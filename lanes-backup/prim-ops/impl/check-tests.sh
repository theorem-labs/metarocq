#!/usr/bin/env bash
# BET-319 row P (PrimTests): the gate behind lanes/prim-ops/impl/TESTS.md.
#
# Runs test-suite/prim_ops.v and test-suite/prim_ops_spec.v on bet64-mem against a
# built implementation tree, reads ONE VERDICT PER CASE out of the two logs, and
# compares each verdict with the one tests-expected.tsv requires for the set of
# design-opt1.md §8 rows that have landed.  It exits non-zero, naming every case,
# when a case holds before its row has landed or stops holding after it has.
#
# Usage:
#   check-tests.sh <tag> "<rows landed>" [<commit>]
#     check-tests.sh m7 "A B C D E F G H K O"             reuse the built tree
#     check-tests.sh m7 "A B C D E F G H K O" 1a2b3c4d    rebuild the tree first
#
# <commit> is a commit of the clone /mnt/nvme/sami/frac-verify/metarocq-fix/metarocq.
# It is streamed to the VM with `git archive | ssh`, so nothing bulky is written
# on this box.  Logs stay on the VM under /mnt/frac/work/prim-ops/out/tests-<tag>/;
# only the verdict table comes back.
#
# Exit codes: 0 every case as expected; 1 at least one case off; 2 the run itself
# failed (no tree, build failure, no verdicts).
set -u

tag=${1:?usage: check-tests.sh <tag> "<rows landed>" [<commit>]}
landed=${2:?usage: check-tests.sh <tag> "<rows landed>" [<commit>]}
commit=${3:--}

here=$(cd "$(dirname "$0")" && pwd)
expected=$here/tests-expected.tsv
m=$here/../../arity-delta/m.sh
clone=/mnt/nvme/sami/frac-verify/metarocq-fix/metarocq

[ -r "$expected" ] || { echo "check-tests: no $expected" >&2; exit 2; }
[ -x "$m" ] || { echo "check-tests: no $m" >&2; exit 2; }

sha=-
if [ "$commit" != "-" ]; then
  sha=$(git -C "$clone" rev-parse --short=8 "$commit")
  rc=$?
  [ $rc -eq 0 ] || { echo "check-tests: no such commit $commit" >&2; exit 2; }
  git -C "$clone" archive --format=tar "$commit" \
    | "$m" "mkdir -p /mnt/frac/work/prim-ops/in && cat > /mnt/frac/work/prim-ops/in/archive-$sha.tar"
  rc=$?
  [ $rc -eq 0 ] || { echo "check-tests: could not stream the archive to bet64-mem" >&2; exit 2; }
fi

# ---- the VM side: build if asked, run the two files, emit the verdict table ----
observed=$("$m" "bash -s -- '$tag' '$sha'" <<'REMOTE'
set -u
tag=$1; sha=$2
W=/mnt/frac/work/prim-ops
T=$W/trees/tests
O=$W/out/tests-$tag
mkdir -p "$O" "$W/in"

if [ "$sha" != "-" ]; then
  sudo rm -rf "$T"
  mkdir -p "$T"; chmod 777 "$T"
  (umask 000; tar --no-same-permissions -C "$T" -xf "$W/in/archive-$sha.tar")
  rc=$?
  [ $rc -eq 0 ] || { echo "STATUS	EXTRACT=$rc"; exit 2; }
  sudo chmod -R a+rwX "$T"
  build="./configure.sh local; echo CONFIGURE_STATUS=\$?; make -j16 all; echo ALL_STATUS=\$?;"
else
  build=""
fi
[ -d "$T/test-suite" ] || { echo "STATUS	NO_TREE=1"; exit 2; }

sudo docker rm -f "prim-tests-$tag" >/dev/null 2>&1 || true
sudo docker run --rm --name "prim-tests-$tag" --cpus 16 --memory 96g --ulimit stack=-1 \
  -v "$W:/work" --entrypoint bash bet64-base -lc "
set -u; ulimit -s unlimited
export COQBIN=/opt/opam-root/harness/bin/
export PATH=/opt/opam-root/harness/bin:\$PATH
export COQEXTRAFLAGS='-native-compiler no'
cd /work/trees/tests
$build
make install > /tmp/install.log 2>&1; echo INSTALL_STATUS=\$?
cd test-suite
rocq repl -q < prim_ops.v      > /work/out/tests-$tag/prim_ops.out 2>&1; echo PRIM_OPS_EXIT=\$?
rocq repl -q < prim_ops_spec.v > /work/out/tests-$tag/prim_ops_spec.out 2>&1; echo PRIM_OPS_SPEC_EXIT=\$?
" > "$O/run.log" 2>&1 </dev/null
rc=$?
echo "RUN_EXIT=$rc" >> "$O/run.log"
grep -E '_STATUS=|_EXIT=' "$O/run.log" | sed 's/^/STATUS\t/'

# prim_ops.v: the case order is the order of the SafeCheck commands in the file;
# the verdicts are the messages the run printed, in the same order.
cd "$T/test-suite"
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
REMOTE
)
rc=$?
if [ $rc -ne 0 ]; then
  echo "check-tests: the run on bet64-mem failed (ssh/remote exit $rc)" >&2
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
printf '%s\n' "$report" | grep -q '^ok' || { echo "check-tests: no verdicts came back; see /mnt/frac/work/prim-ops/out/tests-$tag/" >&2; exit 2; }
exit $rc
