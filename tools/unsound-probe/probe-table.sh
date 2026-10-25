#!/usr/bin/env bash
# Aggregate the private BET-64 nested-positivity diagnostic.  Rows are raw
# whole-tree driver observations, not SafeCheck verdicts.
#
# Usage: probe-table.sh <probe-results-directory> <probe-manifest.tsv>
# It writes probe-final.tsv and probe-final-table.md in the result directory;
# it refuses an r188b destination so historical data cannot be overwritten.
set -euo pipefail

[ "$#" -eq 2 ] || {
  printf 'usage: %s <probe-results-directory> <probe-manifest.tsv>\n' "${0##*/}" >&2
  exit 64
}

result_dir=$1
manifest=$2
case "$result_dir" in
  */r188b|*/r188b/*)
    printf 'refusing to write under r188b: %s\n' "$result_dir" >&2
    exit 64
    ;;
esac
[ -d "$result_dir" ] || { printf 'missing result directory: %s\n' "$result_dir" >&2; exit 66; }
[ -r "$manifest" ] || { printf 'missing manifest: %s\n' "$manifest" >&2; exit 66; }

scratch_root=${TMPDIR:-/mnt/nvme/sami/tmp}
mkdir -p "$scratch_root"
work=$(mktemp -d "$scratch_root/probe-table.XXXXXX")
trap 'rm -rf "$work"' EXIT
final_tsv=$result_dir/probe-final.tsv
final_md=$result_dir/probe-final-table.md
rows=$work/rows.tsv
incomplete=$work/incomplete.tsv
: > "$rows"
: > "$incomplete"

expected=$(awk -F '\t' '$1 != "vm" && $1 !~ /^#/ { n++ } END { print n + 0 }' "$manifest")
[ "$expected" -eq 76 ] || { printf 'manifest must have 76 objects, found %s\n' "$expected" >&2; exit 65; }

# Bring together every exact-PID cutoff record.  These are intentionally
# emitted as incomplete rather than a favorable timing result.
while IFS= read -r incomplete_file; do
  awk -F '\t' 'NF == 4 { print $1 "\t" $2 "\t" $3 "\t" $4 }' "$incomplete_file" >> "$incomplete"
done < <(find "$result_dir" -type f -name 'probe-incomplete.tsv' -print | LC_ALL=C sort)

while IFS=$'\t' read -r vm slot object predicted; do
  case "$vm" in
    vm|\#*|'') continue ;;
  esac
  base="probe-${vm}-${slot}-${object}-tree-0.tsv"
  mapfile -t files < <(find "$result_dir" -type f -name "$base" -print | LC_ALL=C sort)
  if [ "${#files[@]}" -gt 1 ]; then
    printf 'duplicate driver rows for %s: %s\n' "$object" "${files[*]}" >&2
    exit 65
  fi
  if [ "${#files[@]}" -eq 1 ] && awk -F '\t' '$1 != "object" && $1 !~ /^#/ { found = 1 } END { exit !found }' "${files[0]}"; then
    awk -F '\t' -v OFS='\t' -v vm="$vm" -v slot="$slot" '
      $1 != "object" && $1 !~ /^#/ {
        if (NF != 10) {
          printf "driver row for %s has %d columns, expected 10\n", $1, NF > "/dev/stderr"
          exit 65
        }
        print $0, 128, vm, slot
        exit
      }
    ' "${files[0]}" >> "$rows"
  else
    reason=$(awk -F '\t' -v object="$object" -v vm="$vm" -v slot="$slot" '
      $1 == object && $2 == vm && $3 == slot { print $4; exit }
    ' "$incomplete")
    [ -n "$reason" ] || reason=missing_driver_row
    printf '%s\t-\t-\t-\t-\t-\t-\t-\t-\tincomplete: %s\t128\t%s\t%s\n' \
      "$object" "$reason" "$vm" "$slot" >> "$rows"
  fi
done < "$manifest"

actual=$(awk 'END { print NR + 0 }' "$rows")
[ "$actual" -eq 76 ] || { printf 'expected 76 final rows, found %s\n' "$actual" >&2; exit 65; }
if awk -F '\t' 'seen[$1]++ { print $1; bad = 1 } END { exit bad }' "$rows" > "$work/duplicates"; then
  :
else
  printf 'duplicate final objects:\n' >&2
  cat "$work/duplicates" >&2
  exit 65
fi

{
  printf '# UNSOUND PROBE — NOT A SAFECHECK VERDICT\n'
  printf 'object\tconstants\texit\ttimed_out\twall_s\tquote_s\tcheck_s\tquote_peak_rss_kb\tcheck_peak_rss_kb\tverdict\tmemory_limit_gib\tvm\tslot\n'
  LC_ALL=C sort -t $'\t' -k1,1 "$rows"
} > "$final_tsv"

{
  printf '# UNSOUND PROBE — NOT A SAFECHECK VERDICT\n\n'
  printf 'The following are private diagnostic driver observations after an intentionally admitted positivity bypass. They are **not SafeCheck verdicts**.\n\n'
  printf '| object | memory limit GiB | VM | slot | exit | timed out | wall s | quote s | check s | quote peak RSS KB | check peak RSS KB | driver outcome |\n'
  printf '|---|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---|\n'
  awk -F '\t' '
    function cell(x) { return (x == "" || x == "-") ? "—" : x }
    {
      printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s | %s |\n", \
        $1, $11, $12, $13, cell($3), cell($4), cell($5), cell($6), cell($7), cell($8), cell($9), $10
    }
  ' "$rows" | LC_ALL=C sort
  printf '\n## Diagnostic counts\n\n'
  awk -F '\t' '
    function cause(v, ex, timeout) {
      if (v ~ /^incomplete:/) return "incomplete"
      if (ex == "137") return "exit 137 (128-GiB diagnostic failure)"
      if (timeout == "1") return "timed out at 4,500 s (necessary G3 failure)"
      if (v == "accepted") return "accepted by unsound probe"
      if (v ~ /^rejected: /) { sub(/^rejected: /, "", v); return "next rejection: " v }
      return "driver outcome: " v
    }
    {
      n[cause($10, $3, $4)]++
      if ($3 == "137") memory_fail++
      if ($4 == "1") timeout_fail++
      if ($10 ~ /^incomplete:/) incomplete++
    }
    END {
      for (k in n) printf "- %s: %d\n", k, n[k]
      printf "- exit 137 / 128-GiB diagnostic failures: %d\n", memory_fail + 0
      printf "- 4,500-s driver timeouts: %d\n", timeout_fail + 0
      printf "- incomplete rows: %d\n", incomplete + 0
    }
  ' "$rows" | LC_ALL=C sort
} > "$final_md"

printf 'UNSOUND PROBE — NOT A SAFECHECK VERDICT\n'
printf 'wrote %s and %s (%s object rows)\n' "$final_tsv" "$final_md" "$actual"
