#!/usr/bin/env bash
# Check that every "(* expect: TEXT *)" comment in a test file is followed by a
# [Fail MetaRocq SafeCheck] whose failure message contains TEXT.
# [Fail] alone passes on any error, so a refusal for the wrong reason would pass
# unnoticed without this check.
# Usage: check_fail_messages.sh <file.v>   (run in test-suite/, after `make`)
# Exit 0 when every expectation holds; 1 otherwise, naming each one that does not.
# Written for bash 3.2 as well (no mapfile, no expansion of an empty array).
set -u
f=$1
flags=$(grep -E '^-(R|Q|I) ' _RocqProject | tr '\n' ' ')
out=$(mktemp)
# rocq repl prints "The command has indeed failed with message:" and the message
# for each [Fail]; the n-th Fail SafeCheck message is paired with the n-th expect.
eval rocq repl -q $flags < "$f" > "$out" 2>&1
status=0
expects=()
while IFS= read -r line; do expects+=("$line"); done \
  < <(sed -n 's/^(\* expect: \(.*\) \*)$/\1/p' "$f")
# Every [Fail ...] command (Inductive or SafeCheck) prints one block; keep only the
# blocks of [Fail MetaRocq SafeCheck], in order.
kinds=()
while IFS= read -r line; do kinds+=("$line"); done \
  < <(grep -E '^Fail ' "$f" | sed -E 's/^Fail (MetaRocq SafeCheck|[A-Za-z]+).*/\1/')
messages=()
while IFS= read -r line; do messages+=("$line"); done \
  < <(awk '/The command has indeed failed with message:/ { getline; m = $0;
    while ((getline line) > 0 && line !~ /^Rocq </ && line != "") m = m " " line; print m }' "$out")
n=0
i=0
while [ "$i" -lt "${#kinds[@]}" ]; do
  if [ "${kinds[$i]}" = "MetaRocq SafeCheck" ]; then
    want=${expects[$n]:-}
    got=${messages[$i]:-<no failure message>}
    case $got in
      *"$want"*) echo "ok: $want" ;;
      *) echo "MISMATCH: expected \"$want\", got \"$got\""; status=1 ;;
    esac
    n=$((n + 1))
  fi
  i=$((i + 1))
done
[ "$n" -eq "${#expects[@]}" ] || { echo "MISMATCH: ${#expects[@]} expectations, $n Fail SafeCheck commands"; status=1; }
rm -f "$out"
exit $status
