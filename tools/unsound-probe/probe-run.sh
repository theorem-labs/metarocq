#!/usr/bin/env bash
# Private, UNSOUND diagnostic runner for BET-64 slice P.  This script never
# produces SafeCheck verdicts.  It schedules each r188 object once under the
# explicit frac-v12-probe image and records the driver's raw row.
#
# Usage:
#   probe-run.sh manifest <r188b-final.tsv> <manifest.tsv>
#   probe-run.sh run <vm> <manifest.tsv> <cutoff-utc>
#
# The run command is copied to /mnt/frac/work on each probe VM.  It starts the
# three slots assigned to <vm> with setsid+nohup and waits only for those exact
# PIDs.  A slot invokes whole-tree.sh once per object, with lane 0 / lanes 1.
set -euo pipefail

readonly SCRIPT_NAME=${0##*/}
readonly RESULT_DIR=/mnt/frac/work/results
readonly TREE_DIR=/mnt/frac/work/r188/rocq
readonly IMAGE=frac-v12-probe
readonly MEMORY=128g
readonly CPUS=2
readonly OBJECT_LIMIT_SECONDS=4500
readonly LONG_OBJECT_SECONDS=4500
readonly SLOT_COUNT=12

usage() {
  printf 'usage: %s manifest <r188b-final.tsv> <manifest.tsv>\n' "$SCRIPT_NAME" >&2
  printf '       %s run <vm> <manifest.tsv> <cutoff-utc>\n' "$SCRIPT_NAME" >&2
  exit 64
}

vm_for_slot() {
  case "$1" in
    0|1|2) printf '%s\n' frac-metarocq-r188 ;;
    3|4|5) printf '%s\n' frac-metarocq-probe-1 ;;
    6|7|8) printf '%s\n' frac-metarocq-probe-2 ;;
    9|10|11) printf '%s\n' frac-metarocq-probe-3 ;;
    *) printf 'unknown slot index: %s\n' "$1" >&2; return 64 ;;
  esac
}

slot_name() {
  printf 'slot-%02d\n' "$1"
}

utc_epoch() {
  date -u -d "$1" +%s
}

write_incomplete() {
  local manifest=$1 vm=$2 slot=$3 object=$4 reason=$5
  printf '%s\t%s\t%s\t%s\n' "$object" "$vm" "$slot" "$reason" \
    >> "$RESULT_DIR/probe-incomplete.tsv"
}

build_manifest() {
  local prior=$1 manifest=$2 work cap total count scratch_root
  [ -r "$prior" ] || { printf 'missing r188b table: %s\n' "$prior" >&2; return 66; }
  mkdir -p "$(dirname "$manifest")"
  scratch_root=${TMPDIR:-/mnt/nvme/sami/tmp}
  mkdir -p "$scratch_root"
  work=$(mktemp -d "$scratch_root/probe-manifest.XXXXXX")

  count=$(awk -F '\t' '$1 != "object" { n++ } END { print n + 0 }' "$prior")
  [ "$count" -eq 76 ] || { printf 'expected 76 r188b rows, found %s\n' "$count" >&2; return 65; }
  total=$(awk -F '\t' '$1 != "object" && $5 ~ /^[0-9.]+$/ { total += $5 } END { printf "%.3f", total }' "$prior")
  cap=$(awk -v total="$total" 'BEGIN { printf "%.3f", total / 12 }')

  awk -F '\t' '$1 != "object" {
    if ($5 !~ /^[0-9.]+$/) {
      printf "row has no usable wall time: %s\n", $1 > "/dev/stderr"; exit 65
    }
    printf "%.9f\t%s\n", $5, $1
  }' "$prior" | LC_ALL=C sort -rn > "$work/durations.tsv"

  awk -F '\t' -v OFS='\t' -v cap="$cap" -v slots="$SLOT_COUNT" -v long="$LONG_OBJECT_SECONDS" '
    function vm_for(slot_index) {
      if (slot_index < 3) return "frac-metarocq-r188"
      if (slot_index < 6) return "frac-metarocq-probe-1"
      if (slot_index < 9) return "frac-metarocq-probe-2"
      return "frac-metarocq-probe-3"
    }
    {
      duration = $1 + 0
      object = $2
      is_long = duration > long
      placed = 0
      # Seed all twelve named slots with one of the twelve largest objects.
      # Thereafter use first-fit decreasing inside the mean wall-time budget.
      # This guarantees each of the four VMs owns exactly three live slots.
      if (rows < slots) {
        slot = rows + 0
        load[slot] += duration
        long_count[slot] += is_long
        row[++rows] = vm_for(slot) OFS sprintf("slot-%02d", slot) OFS object OFS duration
        placed = 1
      } else {
        for (slot = 0; slot < slots; slot++) {
          if (is_long && long_count[slot] > 0) continue
          # A single object larger than the mean budget stays in its seeded slot.
          if (load[slot] + duration <= cap || load[slot] == 0) {
            load[slot] += duration
            long_count[slot] += is_long
            row[++rows] = vm_for(slot) OFS sprintf("slot-%02d", slot) OFS object OFS duration
            placed = 1
            break
          }
        }
      }
      if (!placed) {
        printf "unable to place %s (%.3f s) into a legal slot\n", object, duration > "/dev/stderr"
        exit 65
      }
    }
    END {
      if (rows != 76) {
        printf "expected 76 manifest rows, found %d\n", rows > "/dev/stderr"
        exit 65
      }
      for (i = 1; i <= rows; i++) print row[i]
    }
  ' "$work/durations.tsv" | LC_ALL=C sort -t $'\t' -k1,1 -k2,2 -k3,3 > "$work/rows.tsv"

  {
    printf '# UNSOUND PROBE — NOT A SAFECHECK VERDICT\n'
    printf '# FFD wall-time budget per slot: %s seconds; an object over %s seconds is alone in its slot.\n' \
      "$cap" "$LONG_OBJECT_SECONDS"
    printf 'vm\tslot\tobject\tpredicted_wall_s\n'
    cat "$work/rows.tsv"
  } > "$manifest"
  printf 'manifest %s: 76 objects, total predicted wall %s s, slot budget %s s\n' \
    "$manifest" "$total" "$cap"
}

run_slot() {
  local vm=$1 slot=$2 manifest=$3 cutoff_utc=$4 cutoff_epoch now object prefix status
  cutoff_epoch=$(utc_epoch "$cutoff_utc")
  mkdir -p "$RESULT_DIR"
  printf 'UNSOUND PROBE — NOT A SAFECHECK VERDICT\n'
  printf 'slot=%s vm=%s pid=%s image=%s memory=%s cpus=%s cutoff=%s\n' \
    "$slot" "$vm" "$$" "$IMAGE" "$MEMORY" "$CPUS" "$cutoff_utc"

  mapfile -t objects < <(awk -F '\t' -v vm="$vm" -v slot="$slot" '
    NR > 1 && $1 == vm && $2 == slot { print $3 }
  ' "$manifest")
  [ "${#objects[@]}" -gt 0 ] || { printf 'no objects assigned to %s/%s\n' "$vm" "$slot" >&2; return 65; }

  local index
  for index in "${!objects[@]}"; do
    object=${objects[$index]}
    now=$(date -u +%s)
    if [ "$now" -ge "$cutoff_epoch" ]; then
      printf 'CUTOFF_REACHED vm=%s slot=%s current=%s\n' "$vm" "$slot" "$object"
      for ((; index < ${#objects[@]}; index++)); do
        write_incomplete "$manifest" "$vm" "$slot" "${objects[$index]}" "cutoff_before_object"
      done
      return 0
    fi

    prefix="probe-${vm}-${slot}-${object}"
    printf 'OBJECT_START vm=%s slot=%s object=%s prefix=%s\n' "$vm" "$slot" "$object" "$prefix"
    # IMAGE is deliberately exported in this detached slot shell.  whole-tree
    # passes it to dock.sh; it must never fall back to frac-v12-mr.
    export IMAGE TREE_DIR
    set +e
    ONLY="$object" /mnt/frac/work/whole-tree.sh "$prefix" "$TREE_DIR" \
      "$OBJECT_LIMIT_SECONDS" "$MEMORY" 0 1
    status=$?
    set -e
    printf 'OBJECT_DONE vm=%s slot=%s object=%s whole_tree_exit=%s\n' \
      "$vm" "$slot" "$object" "$status"

    now=$(date -u +%s)
    if [ "$now" -ge "$cutoff_epoch" ]; then
      printf 'CUTOFF_AFTER_DRIVER_ROW vm=%s slot=%s object=%s\n' "$vm" "$slot" "$object"
      for ((index++; index < ${#objects[@]}; index++)); do
        write_incomplete "$manifest" "$vm" "$slot" "${objects[$index]}" "cutoff_after_driver_row"
      done
      return 0
    fi
  done
}

run_vm() {
  local vm=$1 manifest=$2 cutoff_utc=$3 slot pid pidfile
  [ -r "$manifest" ] || { printf 'missing manifest: %s\n' "$manifest" >&2; return 66; }
  mkdir -p "$RESULT_DIR"
  printf 'UNSOUND PROBE — NOT A SAFECHECK VERDICT\n' > "$RESULT_DIR/probe-${vm}-lifecycle.log"
  printf 'vm\tslot\tpid\tstarted_utc\n' > "$RESULT_DIR/probe-${vm}-pids.tsv"

  mapfile -t slots < <(awk -F '\t' -v vm="$vm" 'NR > 1 && $1 == vm { print $2 }' "$manifest" | LC_ALL=C sort -u)
  [ "${#slots[@]}" -eq 3 ] || { printf 'expected three slots for %s, got %s\n' "$vm" "${#slots[@]}" >&2; return 65; }

  declare -A pids=()
  for slot in "${slots[@]}"; do
    setsid nohup "$0" slot "$vm" "$slot" "$manifest" "$cutoff_utc" \
      >> "$RESULT_DIR/probe-${vm}-${slot}.log" 2>&1 < /dev/null &
    pid=$!
    pids[$slot]=$pid
    printf '%s\t%s\t%s\t%s\n' "$vm" "$slot" "$pid" "$(date -u +%FT%TZ)" \
      >> "$RESULT_DIR/probe-${vm}-pids.tsv"
    printf 'SLOT_STARTED vm=%s slot=%s pid=%s\n' "$vm" "$slot" "$pid" \
      >> "$RESULT_DIR/probe-${vm}-lifecycle.log"
  done

  for slot in "${slots[@]}"; do
    pid=${pids[$slot]}
    if wait "$pid"; then
      printf 'SLOT_EXIT vm=%s slot=%s pid=%s status=0 at=%s\n' \
        "$vm" "$slot" "$pid" "$(date -u +%FT%TZ)" >> "$RESULT_DIR/probe-${vm}-lifecycle.log"
    else
      status=$?
      printf 'SLOT_EXIT vm=%s slot=%s pid=%s status=%s at=%s\n' \
        "$vm" "$slot" "$pid" "$status" "$(date -u +%FT%TZ)" >> "$RESULT_DIR/probe-${vm}-lifecycle.log"
    fi
  done
}

case "${1:-}" in
  manifest)
    [ "$#" -eq 3 ] || usage
    build_manifest "$2" "$3"
    ;;
  run)
    [ "$#" -eq 4 ] || usage
    run_vm "$2" "$3" "$4"
    ;;
  slot)
    [ "$#" -eq 5 ] || usage
    run_slot "$2" "$3" "$4" "$5"
    ;;
  *) usage ;;
esac
