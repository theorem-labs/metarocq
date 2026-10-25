#!/usr/bin/env bash
# Add the required warning to copied private probe evidence without touching r188b.
set -euo pipefail
root=${1:?usage: label-probe-results.sh <probe-result-root>}
label='UNSOUND PROBE — NOT A SAFECHECK VERDICT'
find "$root" -type f -name 'probe-*' ! -name 'probe-final.tsv' ! -name 'probe-final-table.md' -print0 |
while IFS= read -r -d '' file; do
  case "$file" in
    *.tsv) prefix="# $label" ;;
    *.v) prefix="(* $label *)" ;;
    *) prefix="$label" ;;
  esac
  first=$(LC_ALL=C head -c "${#prefix}" "$file" || true)
  [ "$first" = "$prefix" ] && continue
  tmp=$(mktemp "${TMPDIR:-/mnt/nvme/sami/tmp}/probe-label.XXXXXX")
  printf '%s\n' "$prefix" > "$tmp"
  cat "$file" >> "$tmp"
  mv "$tmp" "$file"
done
