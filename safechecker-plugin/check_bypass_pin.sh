#!/usr/bin/env bash
# SafeCheck's opacity pin (see [quote_safecheck_program] in
# src/g_metarocq_safechecker.mlg).  [Ast_quoter.quote_term_rec ~bypass:false]
# drops the body of every opaque constant, and SafeCheck would then check the
# statement without the proof: a wrong accept.  This check fails the build of
# the plugin when the pin is broken.  In the OCaml sources of src/ (every .mlg,
# and every .ml/.mli that is not generated from a .mlg), outside comments and
# string literals:
#   1. [quote_term_rec] occurs exactly once, in the body of
#      [quote_safecheck_program], so every quotation goes through that function;
#   2. [bypass] occurs exactly once, as [~bypass:true] after that
#      [quote_term_rec];
#   3. [quote_safecheck_program] is defined exactly once, at the top level;
#   4. none of the other quoting entry points that take an opacity switch
#      occurs: quote_constant_body, quote_constant_body_aux and
#      quote_constant_entry (template-rocq/src/quoter.ml), tmQuoteConstant
#      (plugin_core.ml), TmQuoteRecTransp and TmQuoteConst (template_monad.ml).
# The body of [quote_safecheck_program] is its [let] line, which starts in
# column 0, and the indented or blank lines after it, up to the next line that
# starts in column 0.
# Usage: check_bypass_pin.sh [<src dir>]   (default src; the [plugin] target of
# safechecker-plugin/Makefile runs it before it compiles the plugin)
# Exit 0 when the pin holds; 1 otherwise, naming each broken rule.
set -u
src=${1:-src}
words='quote_term_rec|bypass|quote_safecheck_program|quote_constant_(body|entry)|tmQuoteConstant|TmQuoteRecTransp|TmQuoteConst'
cands=()
for f in "$src"/*.mlg "$src"/*.ml "$src"/*.mli; do
  [ -f "$f" ] || continue
  case $f in *.ml) [ -f "${f%.ml}.mlg" ] && continue ;; esac
  grep -qE "$words" "$f" && cands+=("$f")
done
if [ ${#cands[@]} -eq 0 ]; then
  echo "check_bypass_pin: FAILED: no source in $src/ defines quote_safecheck_program"
  exit 1
fi
prog=$(cat <<'AWK'
function fail(msg) { print "check_bypass_pin: " msg; bad = 1 }
# The line with comments and string literals blanked (OCaml lexing: nested
# comments, strings inside comments, and character literals such as '"', so
# that a quote character does not open a string).  [depth] and [instr] carry
# over from line to line.
function strip(line,    out, i, n, c, c2, j) {
  out = ""; n = length(line); i = 1
  while (i <= n) {
    c = substr(line, i, 1); c2 = substr(line, i, 2)
    if (instr) {
      if (c == "\\") { out = out "  "; i += 2; continue }
      if (c == "\"") instr = 0
      out = out " "; i++; continue
    }
    if (c == "'") {
      if (substr(line, i + 2, 1) == "'") { out = out "   "; i += 3; continue }
      if (substr(line, i + 1, 1) == "\\") {
        j = index(substr(line, i + 2), "'")
        if (j > 0) { out = out sprintf("%" (j + 2) "s", ""); i += j + 2; continue }
      }
    }
    if (c2 == "(*") { depth++; out = out "  "; i += 2; continue }
    if (depth > 0 && c2 == "*)") { depth--; out = out "  "; i += 2; continue }
    if (c == "\"") { instr = 1; out = out " "; i++; continue }
    out = out (depth > 0 ? " " : c); i++
  }
  return out
}
function endfile() {
  if (depth > 0 || instr)
    fail(curfile ": unterminated comment or string literal; the check cannot read this file")
}
BEGIN {
  q = sprintf("%c", 39)
  idre = "[A-Za-z_][A-Za-z0-9_" q "]*"
  notid = "([^A-Za-z0-9_" q "]|$)"
  wrapre = "^let[ \t]+quote_safecheck_program" notid
  truere = "^:[ \t]*true" notid
  split("quote_constant_body quote_constant_body_aux quote_constant_entry tmQuoteConstant TmQuoteRecTransp TmQuoteConst", b, " ")
  for (k in b) banned[b[k]] = 1
}
FNR == 1 {
  if (NR > 1) endfile()
  curfile = FILENAME; depth = 0; instr = 0; inwrap = 0; qtr_in_wrap = 0
}
{
  s = strip($0)
  if (s ~ wrapre) { inwrap = 1; nregions++; wrapat = FILENAME ":" FNR }
  else if (inwrap && s ~ /^[^ \t]/) inwrap = 0
  pos = 0; rest = s
  while (match(rest, idre)) {
    tok = substr(rest, RSTART, RLENGTH)
    abs = pos + RSTART
    prevc = abs > 1 ? substr(s, abs - 1, 1) : ""
    after = substr(rest, RSTART + RLENGTH)
    where = FILENAME ":" FNR
    if (tok == "quote_term_rec") {
      nqtr++
      if (inwrap) { qtr_in_wrap = 1; qtrat = where }
      else fail(where ": quote_term_rec outside quote_safecheck_program (the wrapper is bypassed)")
    } else if (tok == "bypass") {
      nbyp++
      if (prevc != "~" || after !~ truere)
        fail(where ": bypass is not passed as ~bypass:true")
      else if (!inwrap)
        fail(where ": ~bypass:true outside quote_safecheck_program")
      else if (!qtr_in_wrap)
        fail(where ": ~bypass:true is not an argument of the quote_term_rec in quote_safecheck_program")
    } else if (tok == "quote_safecheck_program" && (prevtok == "let" || prevtok == "rec" || prevtok == "and")) {
      ndefs++
    } else if (tok in banned) {
      fail(where ": " tok " is used (a quoting entry point with an opacity switch)")
    }
    prevtok = tok
    pos = abs + RLENGTH - 1
    rest = after
  }
}
END {
  endfile()
  if (nqtr != 1)
    fail("quote_term_rec occurs " (nqtr + 0) " times outside comments and strings (expected 1, in quote_safecheck_program)")
  if (nbyp != 1)
    fail("bypass occurs " (nbyp + 0) " times outside comments and strings (expected 1, as ~bypass:true in quote_safecheck_program)")
  if (ndefs != 1 || nregions != 1)
    fail("quote_safecheck_program is defined " (ndefs + 0) " times, " (nregions + 0) " of them at the top level (expected 1, at the top level)")
  if (bad) {
    print "check_bypass_pin: FAILED: SafeCheck must quote only through quote_safecheck_program, which calls quote_term_rec with ~bypass:true (see the comment there)"
    exit 1
  }
  print "check_bypass_pin: ok: quote_term_rec once, with ~bypass:true, in quote_safecheck_program (" wrapat ")"
}
AWK
)
awk "$prog" "${cands[@]}"
