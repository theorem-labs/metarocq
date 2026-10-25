#!/usr/bin/env bash
# Runs only on frac-metarocq-r188.  It rebuilds the private probe source tree
# into a private image; it never modifies /mnt/frac/work/metarocq.
set -euo pipefail

: "${PROBE_SOURCE_SHA:?PROBE_SOURCE_SHA is required}"
: "${PROBE_BRANCH:?PROBE_BRANCH is required}"
readonly W=/mnt/frac/work
readonly SOURCE=$W/metarocq-probe
readonly FROM=frac-v12-mr2
readonly TO=frac-v12-probe
readonly NAME=frac-v12-probe-rebuild

[ -d "$SOURCE" ] || { printf 'missing probe source: %s\n' "$SOURCE" >&2; exit 66; }
[ -f "$SOURCE/.probe-identity" ] || { printf 'refusing unmarked probe source: %s\n' "$SOURCE" >&2; exit 65; }
if [ "$(awk -F '\t' '$1 == "source_sha" { print $2 }' "$SOURCE/.probe-identity")" != "$PROBE_SOURCE_SHA" ]; then
  printf 'probe source SHA does not match staged identity\n' >&2
  exit 65
fi

sudo docker rm -f "$NAME" >/dev/null 2>&1 || true
cleanup() {
  sudo docker rm -f "$NAME" >/dev/null 2>&1 || true
}
trap cleanup EXIT

sudo docker run --name "$NAME" --ulimit stack=-1 --memory 64g --cpus 24 \
  -v "$W:/work" --entrypoint bash "$FROM" -c '
set -euo pipefail
ulimit -s unlimited
export COQBIN=/opt/opam-root/harness/bin/
export COQEXTRAFLAGS="-native-compiler no"
cd /work/metarocq-probe
[ -f Makefile.conf ] || ./configure.sh local
cd template-rocq
./update_plugin.sh force
cd ..
make -C safechecker-plugin cleanplugin
make -j24 safechecker-plugin
make -C safechecker install
make -C safechecker-plugin install
echo PROBE_REBUILD_OK'

image_id=$(sudo docker image inspect "$TO" --format '{{.Id}}' 2>/dev/null || true)
if [ -n "$image_id" ]; then
  # A stale tag must not be accepted as a new probe image.
  sudo docker image rm -f "$TO" >/dev/null 2>&1 || true
fi
sudo docker commit "$NAME" "$TO" >/dev/null
image_id=$(sudo docker image inspect "$TO" --format '{{.Id}}')
mkdir -p "$W/results"
{
  printf 'UNSOUND PROBE — NOT A SAFECHECK VERDICT\n'
  printf 'source_branch\t%s\n' "$PROBE_BRANCH"
  printf 'source_sha\t%s\n' "$PROBE_SOURCE_SHA"
  printf 'image\t%s\n' "$TO"
  printf 'image_id\t%s\n' "$image_id"
  printf 'built_at_utc\t%s\n' "$(date -u +%FT%TZ)"
} > "$W/results/probe-identity.tsv"
printf 'PROBE_IMAGE_ID %s\n' "$image_id"
