#!/usr/bin/env bash
# Stage frac/probe-nested on frac-metarocq-r188 and build frac-v12-probe.
# This host-side helper performs no build or container operation itself.
#
# Usage: probe-rebuild.sh sync | build
set -euo pipefail

readonly ROOT=/mnt/nvme/sami/frac-verify/metarocq-fix
readonly SOURCE=$ROOT/metarocq-probe
readonly VM=$ROOT/merged/vm188.sh
readonly REMOTE_SOURCE=/mnt/frac/work/metarocq-probe
readonly REMOTE_HELPER=/mnt/frac/work/probe-rebuild-vm.sh

[ "$#" -eq 1 ] || { printf 'usage: %s sync|build\n' "${0##*/}" >&2; exit 64; }
[ -e "$SOURCE/.git" ] || { printf 'not a source worktree: %s\n' "$SOURCE" >&2; exit 66; }
source_sha=$(git -C "$SOURCE" rev-parse HEAD)
source_branch=$(git -C "$SOURCE" branch --show-current)
[ "$source_branch" = frac/probe-nested ] || {
  printf 'expected frac/probe-nested, found %s\n' "$source_branch" >&2
  exit 65
}

sync_source() {
  tar -C "$SOURCE" --exclude=.git -cf - . | "$VM" "
set -euo pipefail
source=$REMOTE_SOURCE
if [ -e \"\$source\" ] && [ ! -f \"\$source/.probe-identity\" ]; then
  printf 'refusing to overwrite unmarked source: %s\\n' \"\$source\" >&2
  exit 65
fi
mkdir -p \"\$source\"
tar -C \"\$source\" -xf -
printf 'source_branch\\t%s\\nsource_sha\\t%s\\n' '$source_branch' '$source_sha' > \"\$source/.probe-identity\"
printf 'PROBE_SOURCE_STAGED %s %s\\n' '$source_branch' '$source_sha'
"
}

case "$1" in
  sync)
    sync_source
    ;;
  build)
    sync_source
    cat "$ROOT/merged/probe-rebuild-vm.sh" | "$VM" "cat > '$REMOTE_HELPER' && chmod 700 '$REMOTE_HELPER'"
    "$VM" "PROBE_SOURCE_SHA='$source_sha' PROBE_BRANCH='$source_branch' '$REMOTE_HELPER'"
    ;;
  *)
    printf 'usage: %s sync|build\n' "${0##*/}" >&2
    exit 64
    ;;
esac
