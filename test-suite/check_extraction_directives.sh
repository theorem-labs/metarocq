#!/usr/bin/env bash
# Check that the tree's extraction directives are exactly the allowed ones.
#
# [Print Assumptions] cannot see an extraction directive.  A directive replaces the
# EXTRACTED code of a constant; the Rocq constant it replaces stays closed under the global
# context, so the axiom check (check_assumptions.sh) reports nothing.  That is why
#   Extract Constant TemplateToPCUICShared.memo_trans => "Trans_memo.memo".
# puts 7,206 bytes of hand-written OCaml inside the shipped checker without changing one
# line of a [Print Assumptions] report.  This gate is the instrument for that class.
#
# It scans EVERY tracked .v file, not only the Extraction.v files: a directive in any
# Required file takes effect at extraction, so a gate on Extraction.v alone is bypassed by
# putting the directive one Require away.
#
# Usage: check_extraction_directives.sh [--list] [tree-root]
#   (run from anywhere; the default root is the parent of this script's directory)
#   --list   print the tree's normalized directives instead of checking them; this is how
#            the allowed list is (re)built after a reviewed change.
# Exit 0 when the tree's directives are exactly the allowed list, 1 otherwise, naming each
# difference.
#
# Allowed list: extraction_directives.allowed, beside this script.  Six TAB-separated
# fields (TAB, because an OCaml target may contain "|" and a Rocq target may not contain a
# literal TAB -- the scanner collapses every run of whitespace to one space):
#   FILE <TAB> KIND <TAB> LHS <TAB> RHS <TAB> CLASS <TAB> CONTRACT
# KIND  EXTRACT_CONSTANT | EXTRACT_INLINED_CONSTANT | EXTRACT_INDUCTIVE | IMPORT
#       IMPORT records one Rocq-stdlib extraction library a file Requires, so a new library
#       of directives cannot arrive through an added Require either.
# CLASS repr          the inductive is mapped to an OCaml type, constructor for
#                     constructor; no computation is replaced.
#       repr-proj     a projection of a repr-mapped inductive, mapped to the matching
#                     OCaml projection.
#       inherited     an extraction library of the Rocq distribution, pinned by the Rocq
#                     version; its directives are not in this tree.
#       unreferenced  the directive is in a file that no .v Requires, so it has no effect.
#                     The gate re-checks that: the file must stay unreferenced.
#       trusted       the directive REPLACES A COMPUTATION that the tree also implements in
#                     Rocq.  This is the class the shipping rule is about, and it is
#                     allowed only with a CONTRACT: what the OCaml side must satisfy for
#                     the shipped checker to be correct.  A trusted entry with an empty
#                     contract fails the gate.
set -u

here=$(cd -- "$(dirname -- "$0")" && pwd)
allowed=$here/extraction_directives.allowed
mode=check
if [ "${1-}" = "--list" ]; then mode=list; shift; fi
root=${1-$(dirname -- "$here")}
tab=$(printf '\t')

scan_awk='
# Rocq statement scanner: strips (nestable) comments, keeps strings whole, and splits on a
# "." followed by whitespace or end of input.  A "." inside a qualified name is followed by
# a letter, so it does not end a statement.
function flush(   s) {
  s = buf; buf = ""
  gsub(/[ \t\n\r]+/, " ", s); sub(/^ /, "", s); sub(/ $/, "", s)
  if (s == "") return
  if (s ~ /^Extract Inlined Constant /) { emit("EXTRACT_INLINED_CONSTANT", substr(s, 26)); return }
  if (s ~ /^Extract Constant /)         { emit("EXTRACT_CONSTANT", substr(s, 18)); return }
  if (s ~ /^Extract Inductive /)        { emit("EXTRACT_INDUCTIVE", substr(s, 19)); return }
  if (s ~ /^Extract[ \t]/)              { print FILENAME "\tUNKNOWN_EXTRACT\t" s "\t"; return }
  if (s ~ /(^|[^A-Za-z_])Require([ \t]|$)/) imports(s)
}
# "lhs => rhs": the first token is the Rocq constant, the rest is the OCaml target.
function emit(kind, rest,   lhs, rhs, p) {
  p = index(rest, "=>")
  if (p == 0) { print FILENAME "\tUNKNOWN_EXTRACT\t" kind " " rest "\t"; return }
  lhs = substr(rest, 1, p - 1); rhs = substr(rest, p + 2)
  gsub(/^ +| +$/, "", lhs); gsub(/^ +| +$/, "", rhs)
  print FILENAME "\t" kind "\t" lhs "\t" rhs
}
# Every extraction-directive library the file imports from outside this repository.
function imports(s,   n, i, a) {
  n = split(s, a, /[ \t]+/)
  for (i = 1; i <= n; i++) if (a[i] ~ /^ExtrO[Cc]aml/) print FILENAME "\tIMPORT\t" a[i] "\t-"
}
BEGIN { buf = ""; cdepth = 0; instr = 0 }
{
  line = $0 "\n"
  for (i = 1; i <= length(line); i++) {
    c = substr(line, i, 1); d = substr(line, i + 1, 1)
    if (instr) {
      buf = buf c
      if (c == "\"") { if (d == "\"") { buf = buf d; i++ } else instr = 0 }
      continue
    }
    if (cdepth > 0) {
      if (c == "(" && d == "*") { cdepth++; i++ }
      else if (c == "*" && d == ")") { cdepth--; i++ }
      continue
    }
    if (c == "(" && d == "*") { cdepth = 1; i++; buf = buf " "; continue }
    if (c == "\"") { instr = 1; buf = buf c; continue }
    if (c == "." && (d == "" || d == " " || d == "\t" || d == "\n" || d == "\r")) { flush(); continue }
    buf = buf c
  }
}
END { flush() }
'

cd -- "$root" || { echo "no such tree: $root"; exit 1; }
# A git checkout in CI, an unpacked tarball in a grade image: both must be scannable, and
# the paths must read the same either way, so the allowed list is one list.
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  files=$(git ls-files '*.v')
else
  files=$(find . -name '*.v' -type f | sed 's,^\./,,' | LC_ALL=C sort)
fi
[ -n "$files" ] || { echo "no .v files under $root"; exit 1; }
found=$(printf '%s\n' "$files" | xargs awk "$scan_awk" | LC_ALL=C sort -u)

if [ "$mode" = list ]; then printf '%s\n' "$found"; exit 0; fi

[ -r "$allowed" ] || { echo "missing allowed list: $allowed"; exit 1; }

status=0
bad=$(printf '%s\n' "$found" | grep "${tab}UNKNOWN_EXTRACT${tab}" || true)
if [ -n "$bad" ]; then
  echo "FAIL: extraction statement of an unrecognized form (the gate cannot classify it):"
  printf '%s\n' "$bad"; status=1
fi

records=$(grep -v '^[ 	]*#' "$allowed" | grep -v '^[ 	]*$')
want=$(printf '%s\n' "$records" | cut -f1-4 | LC_ALL=C sort -u)

added=$(comm -23 <(printf '%s\n' "$found") <(printf '%s\n' "$want"))
removed=$(comm -13 <(printf '%s\n' "$found") <(printf '%s\n' "$want"))

if [ -n "$added" ]; then
  echo "FAIL: extraction directive in the tree but not on the allowed list"
  echo "      (an added directive, or an allowed one whose OCaml target changed):"
  printf '%s\n' "$added" | sed 's/^/  + /'
  status=1
fi
if [ -n "$removed" ]; then
  echo "FAIL: extraction directive on the allowed list but not in the tree"
  echo "      (removed, or its OCaml target changed; update the list):"
  printf '%s\n' "$removed" | sed 's/^/  - /'
  status=1
fi

# Every class must be one the gate knows, and a trusted replacement must carry a contract.
badclass=$(printf '%s\n' "$records" | awk -F'\t' '
  $5 != "repr" && $5 != "repr-proj" && $5 != "inherited" && $5 != "unreferenced" && $5 != "trusted" \
    { print $1 "\t" $3 "\t[" $5 "]" }')
if [ -n "$badclass" ]; then
  echo "FAIL: allowed-list entry with no class the gate knows:"
  printf '%s\n' "$badclass" | sed 's/^/  ? /'
  status=1
fi
nocontract=$(printf '%s\n' "$records" | awk -F'\t' '$5 == "trusted" && $6 ~ /^[ \t]*$/ { print $1 "\t" $3 }')
if [ -n "$nocontract" ]; then
  echo "FAIL: trusted replacement with no contract on the allowed list:"
  printf '%s\n' "$nocontract" | sed 's/^/  ! /'
  status=1
fi

# A directive excused as unreferenced must still be unreferenced.  The search is over the
# same file list the scan used, so it works on a checkout and on an unpacked tarball.
for f in $(printf '%s\n' "$records" | awk -F'\t' '$5 == "unreferenced" { print $1 }' | sort -u); do
  m=$(basename -- "$f" .v)
  # A Require statement naming that module.  [^.]* stops the match at the end of the
  # statement, so a later Require on another line cannot be read as part of this one.
  req="Require[^.]*\\<$m\\>"
  hits=$(printf '%s\n' "$files" | xargs grep -n -E "$req" /dev/null)
  if [ -n "$hits" ]; then
    echo "FAIL: $f is Required now, so its directives are live, but they are listed as"
    echo "      unreferenced and carry no contract:"
    printf '%s\n' "$hits" | sed 's/^/  > /'
    status=1
  fi
done

n=$(printf '%s\n' "$found" | grep -c "$tab")
t=$(printf '%s\n' "$records" | awk -F'\t' '$5 == "trusted" { n++ } END { print n + 0 }')
if [ "$status" -eq 0 ]; then
  echo "ok: $n extraction directives and imports, all allowed; $t trusted replacements, each with its contract"
fi
exit $status
