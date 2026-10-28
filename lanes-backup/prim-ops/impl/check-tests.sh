#!/usr/bin/env bash
# BET-319 row P (PrimTests): the gate behind lanes/prim-ops/impl/TESTS.md.
#
# Runs test-suite/prim_ops.v and test-suite/prim_ops_spec.v on bet64-mem against a
# built implementation tree, reads ONE VERDICT PER CASE out of the two logs, and
# compares each verdict with the one tests-expected.tsv requires for the set of
# design-opt1.md §8 rows that have landed.  It exits non-zero, naming every case,
# when a case holds before its row has landed or stops holding after it has.
#
# It also runs test-suite/check_fail_messages.sh on prim_ops.v, so every expected
# refusal there ([Fail] preceded by an `(* expect: … *)` comment) must refuse with
# THAT message; a [Fail] alone would pass on any error.
#
# Usage:
#   check-tests.sh <tag> "<rows landed>" [<commit>]
#     check-tests.sh m7 "A B C D E F G H K O"             reuse the built tree
#     check-tests.sh m7 "A B C D E F G H K O" 1a2b3c4d    rebuild the tree first
#
# <commit> is a commit of the clone /mnt/nvme/sami/frac-verify/metarocq-fix/metarocq.
# It is streamed to the VM with `git archive | ssh`, so nothing bulky is written on
# this box.  Logs stay on the VM under /mnt/frac/work/prim-ops/out/tests-<tag>/; only
# the verdict table comes back.
#
# The VM run goes through lanes/bin/lane-lock.sh under the work-name
# prim-ops-composition (dispatch://INFRA-681): if a composition build is already
# running, this prints LOCK_HELD and exits 2 WITHOUT starting a second one.
#
# Exit codes: 0 every case as expected; 1 at least one case off; 2 the run itself
# did not happen or did not finish (lock held, no tree, build failure, no verdicts).
set -u

tag=${1:?usage: check-tests.sh <tag> "<rows landed>" [<commit>]}
landed=${2:?usage: check-tests.sh <tag> "<rows landed>" [<commit>]}
commit=${3:--}

here=$(cd "$(dirname "$0")" && pwd)
expected=$here/tests-expected.tsv
m=$here/../../arity-delta/m.sh
lock=$here/../../bin/lane-lock.sh
clone=/mnt/nvme/sami/frac-verify/metarocq-fix/metarocq
W=/mnt/frac/work/prim-ops
O=$W/out/tests-$tag
runlog=$O/run.log
wait_max=${CHECK_TESTS_WAIT_MAX:-10800}   # seconds to wait for the run to finish

[ -r "$expected" ] || { echo "check-tests: no $expected" >&2; exit 2; }
[ -x "$m" ]        || { echo "check-tests: no $m" >&2; exit 2; }
[ -x "$lock" ]     || { echo "check-tests: no $lock" >&2; exit 2; }

sha=-
if [ "$commit" != "-" ]; then
  sha=$(git -C "$clone" rev-parse --short=8 "$commit")
  rc=$?
  [ $rc -eq 0 ] || { echo "check-tests: no such commit $commit" >&2; exit 2; }
  git -C "$clone" archive --format=tar "$commit" \
    | "$m" "mkdir -p $W/in && cat > $W/in/archive-$sha.tar"
  rc=$?
  [ $rc -eq 0 ] || { echo "check-tests: could not stream the archive to bet64-mem" >&2; exit 2; }
fi

# ---- the VM-side run, written to a file and started under the lock ----
# Everything here runs in the FOREGROUND (`docker run --rm`), so the lock lasts
# exactly as long as the run.  The last line it prints is the CHECK_DONE sentinel.
# The old run.log is deleted first: a CHECK_DONE left by an earlier run with the same
# tag would otherwise end the wait below before this run had started.
"$m" "mkdir -p $W/in $O && rm -f $runlog && cat > $W/in/check-tests-$tag.sh" <<'REMOTE'
set -u
tag=$1; sha=$2
W=/mnt/frac/work/prim-ops
T=$W/trees/tests
O=$W/out/tests-$tag
mkdir -p "$O"
if [ "$sha" != "-" ]; then
  sudo rm -rf "$T"; mkdir -p "$T"; chmod 777 "$T"
  if ! (umask 000; tar --no-same-permissions -C "$T" -xf "$W/in/archive-$sha.tar"); then
    echo "CHECK_DONE rc=2 reason=extract"; exit 2
  fi
  sudo chmod -R a+rwX "$T"
  build="./configure.sh local; echo CONFIGURE_STATUS=\$?; make -j16 all; echo ALL_STATUS=\$?;"
else
  build=""
fi
[ -d "$T/test-suite" ] || { echo "CHECK_DONE rc=2 reason=no-tree"; exit 2; }
sudo docker rm -f "prim-tests-$tag" >/dev/null 2>&1 || true
sudo docker run --rm --name "prim-tests-$tag" --cpus 16 --memory 96g --ulimit stack=-1 \
  -v "$W:/work" --entrypoint bash bet64-base -lc "
set -u; ulimit -s unlimited
export COQBIN=/opt/opam-root/harness/bin/
export PATH=/opt/opam-root/harness/bin:\$PATH
export COQEXTRAFLAGS='-native-compiler no'
cd /work/trees/tests
$build
make install > /work/out/tests-$tag/install.log 2>&1; echo INSTALL_STATUS=\$?
cd test-suite
[ -f _RocqProject ] || : > _RocqProject
rocq repl -q < prim_ops.v      > /work/out/tests-$tag/prim_ops.out 2>&1; echo PRIM_OPS_EXIT=\$?
rocq repl -q < prim_ops_spec.v > /work/out/tests-$tag/prim_ops_spec.out 2>&1; echo PRIM_OPS_SPEC_EXIT=\$?
bash check_fail_messages.sh prim_ops.v > /work/out/tests-$tag/fail_messages.txt 2>&1; echo FAIL_MESSAGES_EXIT=\$?
"
echo "CHECK_DONE rc=$?"
REMOTE
rc=$?
[ $rc -eq 0 ] || { echo "check-tests: could not write the run script to bet64-mem" >&2; exit 2; }

started=$("$lock" run bet64-mem prim-ops-composition "check-tests $tag" "$runlog" \
            -- bash "$W/in/check-tests-$tag.sh" "$tag" "$sha")
rc=$?
printf '%s\n' "$started"
if [ $rc -eq 75 ]; then
  echo "check-tests: a prim-ops-composition run is already in progress (above); not starting a second one" >&2
  exit 2
fi
[ $rc -eq 0 ] || { echo "check-tests: lane-lock run failed ($rc)" >&2; exit 2; }

# ---- wait for this run's own sentinel ----
waited=0
until "$m" "grep -q '^CHECK_DONE' $runlog 2>/dev/null" </dev/null; do
  if [ "$waited" -ge "$wait_max" ]; then
    echo "check-tests: no CHECK_DONE in $runlog after ${wait_max}s; the run may still be going" >&2
    exit 2
  fi
  sleep 30; waited=$((waited + 30))
done

# ---- read the verdicts (read-only, so it needs no lock) ----
observed=$("$m" "bash -s -- '$tag'" <<'PARSE'
set -u
tag=$1
W=/mnt/frac/work/prim-ops; T=$W/trees/tests; O=$W/out/tests-$tag
grep -E '_STATUS=|_EXIT=|^CHECK_DONE' "$O/run.log" | sed 's/^/STATUS\t/'
cd "$T/test-suite"

# prim_ops.v: the case order is the order of the SafeCheck commands in the file;
# the verdicts are the messages the run printed, in the same order.
grep -E '^(Fail )?MetaRocq SafeCheck ' prim_ops.v \
  | sed -E 's/^(Fail )?MetaRocq SafeCheck ([A-Za-z0-9_]+).*/\2/' > "$O/names.txt"
awk '
  /The command has indeed failed with message/ { print "failholds"; skip=1; next }
  /The command has not failed/                 { print "notfailed"; next }
  /Environment is well-formed/                 { if (skip) { skip=0; next } print "accepted"; next }
  /Type error:/                                { if (skip) { skip=0; next } print "refused"; next }
' "$O/prim_ops.out" > "$O/events.txt"
paste "$O/names.txt" "$O/events.txt" | sed 's/^/prim_ops\t/'

# prim_ops_spec.v: each case prints its own named verdict.
sed -nE 's/.*(po_[A-Za-z0-9_]+)_ok = (true|false).*/\1\t\2/p' "$O/prim_ops_spec.out" \
  | sed -e 's/\ttrue$/\tok/' -e 's/\tfalse$/\tnotok/' -e 's/^/prim_ops_spec\t/'

# The expected-message check, as one case.  A missing file or no "ok:" line is
# not a pass: the check did not run.
f=$O/fail_messages.txt
if [ ! -s "$f" ];                   then v=missing
elif grep -q '^MISMATCH' "$f";      then v=mismatch
elif grep -q '^ok:' "$f";           then v=ok
else                                     v=missing
fi
printf 'fail_messages\tprim_ops.v\t%s\n' "$v"
PARSE
)
rc=$?
if [ $rc -ne 0 ]; then
  echo "check-tests: reading the verdicts on bet64-mem failed (exit $rc)" >&2
  printf '%s\n' "$observed" >&2
  exit 2
fi

printf '%s\n' "$observed" | grep '^STATUS' || true

# ---- compare ----
report=$(printf '%s\n' "$observed" | awk -v landed="$landed" -v expfile="$expected" '
function needed_ok(rows,   n, i, a) {
  if (rows == "-") return 1
  n = split(rows, a, " ")
  for (i = 1; i <= n; i++) if (index(" " landed " ", " " a[i] " ") == 0) return 0
  return 1
}
BEGIN {
  FS = "\t"
  while ((getline line < expfile) > 0) {
    if (line ~ /^#/ || line ~ /^[ \t]*$/) continue
    split(line, f, "\t")
    key = f[1] "/" f[2]
    order[++nk] = key
    want[key] = needed_ok(f[3]) ? f[5] : f[4]
    rowset[key] = f[3]
    turned[key] = needed_ok(f[3])
  }
  close(expfile)
}
$1 == "STATUS" { next }
NF >= 3 { seen[$1 "/" $2] = ($3 == "" ? "missing" : $3); next }
END {
  bad = 0
  for (i = 1; i <= nk; i++) {
    key = order[i]
    got = (key in seen) ? seen[key] : "missing"
    # a case that produced no verdict did not hold
    norm = got
    if (got == "missing") norm = "notok"
    if (norm != want[key]) {
      bad++
      if (rowset[key] == "-") kind = "MUST-NEVER-TURN"
      else kind = turned[key] ? "STILL-RED-AFTER-ITS-ROW" : "GREEN-BEFORE-ITS-ROW"
      printf "FAIL\t%s\t%s\texpected=%s\tobserved=%s\trows_needed=%s\t%s\n",
             key, (turned[key] ? "row-landed" : "row-pending"), want[key], got, rowset[key], kind
    } else {
      printf "ok\t%s\t%s%s\n", key, norm, (got == "missing" ? "\t(no verdict printed)" : "")
    }
  }
  for (key in seen) if (!(key in want))
    printf "FAIL\t%s\tUNDECLARED-CASE\tobserved=%s\t(add it to tests-expected.tsv)\n", key, seen[key]
  printf "SUMMARY\tcases=%d\tfailures=%d\trows_landed=%s\n", nk, bad, landed
  exit (bad > 0)
}
')
rc=$?
printf '%s\n' "$report"
printf '%s\n' "$report" | grep -q '^ok' || { echo "check-tests: no verdicts came back; see $O/ on bet64-mem" >&2; exit 2; }
exit $rc
