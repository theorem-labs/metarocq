#!/usr/bin/env bash
# Check that every [Print Assumptions] in a test file reports only axioms of the
# primitive-type libraries (the axioms every development using primitive integers,
# strings or floats has).  [Print Assumptions] alone only prints, so an axiom or an
# admitted lemma added later would pass unnoticed without this check.
# Usage: check_assumptions.sh <file.v> [extra]   (run in test-suite/, after `make`)
# [extra] is an optional regex of further allowed axiom names, for an axiom that the
# checked statements themselves name (e.g. Template's [guard_checking]).
# Exit 0 when every reported axiom is allowed; 1 otherwise, naming each other one.
set -u
f=$1
allowed='^(PrimInt63|Uint63Axioms|PrimString|PrimStringAxioms|PrimFloat|FloatAxioms)\.'
[ -n "${2:-}" ] && allowed="$allowed|$2"
flags=$(grep -E '^-(R|Q|I) ' _RocqProject | tr '\n' ' ')
out=$(mktemp)
# rocq repl prefixes the first line of each answer with one "Rocq < " prompt per
# command read since the last output; strip them.
eval rocq repl -q $flags < "$f" 2>&1 | sed -E 's/^(Rocq < )+//' > "$out"
blocks=$(grep -cE '^(Axioms:|Closed under the global context)' "$out")
want=$(grep -cE '^Print Assumptions ' "$f")
status=0
if [ "$blocks" -ne "$want" ]; then
  echo "MISMATCH: $want Print Assumptions commands, $blocks reports"; status=1
fi
bad=$(awk '/^Axioms:/ { inax = 1; next }
           /^[^ ]/ && inax && !/^[A-Za-z_][A-Za-z0-9_.'"'"']* :/ { inax = 0 }
           inax && /^[A-Za-z_][A-Za-z0-9_.'"'"']* :/ { print $1 }' "$out" | grep -vE "$allowed" | sort -u)
if [ -n "$bad" ]; then
  echo "MISMATCH: axioms outside the primitive-type libraries:"; echo "$bad"; status=1
fi
[ "$status" -eq 0 ] && echo "ok: $want Print Assumptions, only primitive-library axioms${2:+ and $2}"
rm -f "$out"
exit $status
