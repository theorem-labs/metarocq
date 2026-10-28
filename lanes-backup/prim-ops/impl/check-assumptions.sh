#!/usr/bin/env bash
# BET-319 row P (PrimTests): the trusted-base gate, design-opt1.md §10 item 1.
#
# Compares the `Print Assumptions` output of the four checker statements on an
# implementation tip against the integrated baseline, and requires the design's
# acceptance EXACTLY: each of the four blocks differs from the baseline by one
# added axiom, `PrimInt63.leb`, and by nothing else.  The counts 35/35/35/33 ->
# 36/36/36/34 are printed as the consequence, never as the test (gate finding 3:
# state it as a diff, not a count).
#
# Usage: check-assumptions.sh <tip-output> [<baseline>]
#   <tip-output>  the output of running merged/logs/upstream-9.2.0/PrintAssumptions.v
#                 on the implementation tip (4 `Axioms:` blocks, in that order:
#                 infer_and_print_template_program_with_guard, infer_template_program,
#                 typecheck_program, canonical_abstract_env_prop).
#   <baseline>    defaults to lanes/integ-all/results/ia2-a2122448/verify/assumptions.txt
#
# Exit 0 every block differs by exactly +PrimInt63.leb; 1 any other difference
# (each one named); 2 the inputs are not four blocks each.
#
# Entries are compared by AXIOM NAME, not by line, because `Print Assumptions`
# wraps a long type over several indented lines; a name sits at column 0 before
# " :".  That makes the check insensitive to pretty-printing width.
set -u

here=$(cd "$(dirname "$0")" && pwd)
tip=${1:?usage: check-assumptions.sh <tip-output> [<baseline>]}
base=${2:-$here/../../integ-all/results/ia2-a2122448/verify/assumptions.txt}

[ -r "$tip" ]  || { echo "check-assumptions: cannot read tip output $tip" >&2; exit 2; }
[ -r "$base" ] || { echo "check-assumptions: cannot read baseline $base" >&2; exit 2; }

# names_of <file> <block-index>  -> the axiom names of that block, sorted
#
# An entry starts at column 0 and is `Name :` (the type may wrap onto following
# indented lines).  The `Name *:` guard matters: the harness appends its own
# status line (`ASSUMPTIONS_EXIT 0`) after the last block, and without the guard
# it would be counted as a 34th axiom of block 4, contradicting the design's 33.
names_of() {
  awk -v want="$2" '
    /^Axioms:/ { blk++; next }
    blk != want { next }
    /^[^ \t]+[ \t]*:/ {
      line = $0
      sub(/[ \t]*:.*$/, "", line)
      if (line != "") print line
    }
  ' "$1" | sort -u
}

nblocks() { grep -c '^Axioms:' "$1"; }

bt=$(nblocks "$tip"); bb=$(nblocks "$base")
if [ "$bt" -ne 4 ] || [ "$bb" -ne 4 ]; then
  echo "check-assumptions: expected 4 Axioms: blocks in each input, got tip=$bt baseline=$bb" >&2
  echo "  (PrintAssumptions.v prints one block per checker statement; a short file usually" >&2
  echo "   means the run stopped early -- read the run log before trusting this)" >&2
  exit 2
fi

blocknames=(
  "infer_and_print_template_program_with_guard"
  "infer_template_program"
  "typecheck_program"
  "canonical_abstract_env_prop"
)

bad=0
for i in 1 2 3 4; do
  label=${blocknames[$((i-1))]}
  added=$(comm -13 <(names_of "$base" "$i") <(names_of "$tip" "$i"))
  removed=$(comm -23 <(names_of "$base" "$i") <(names_of "$tip" "$i"))
  nbase=$(names_of "$base" "$i" | wc -l)
  ntip=$(names_of "$tip" "$i" | wc -l)

  if [ "$added" = "PrimInt63.leb" ] && [ -z "$removed" ]; then
    printf 'ok\tblock %d (%s)\t%s -> %s\t+PrimInt63.leb\n' "$i" "$label" "$nbase" "$ntip"
  else
    bad=$((bad+1))
    printf 'FAIL\tblock %d (%s)\t%s -> %s\n' "$i" "$label" "$nbase" "$ntip"
    if [ -n "$added" ]; then
      printf '%s\n' "$added" | sed 's/^/\tADDED   /'
    else
      printf '\tADDED   (nothing -- PrimInt63.leb was expected)\n'
    fi
    [ -n "$removed" ] && printf '%s\n' "$removed" | sed 's/^/\tREMOVED /'
  fi
done

# No Uint63Axioms/PrimStringAxioms specification may be added (design §10 item 1).
spec_added=$(comm -13 <(names_of "$base" 1) <(names_of "$tip" 1) \
             | grep -E '^(Uint63Axioms|PrimStringAxioms)\.' || true)
if [ -n "$spec_added" ]; then
  bad=$((bad+1))
  printf 'FAIL\tspecification axiom added (design §10 item 1 forbids it)\n'
  printf '%s\n' "$spec_added" | sed 's/^/\tADDED   /'
fi

if [ "$bad" -eq 0 ]; then
  echo "SUMMARY all 4 blocks differ from the baseline by exactly +PrimInt63.leb"
else
  echo "SUMMARY $bad block(s)/check(s) off -- this stops the gate" >&2
fi
exit $((bad > 0))
