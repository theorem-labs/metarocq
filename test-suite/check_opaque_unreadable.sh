#!/usr/bin/env bash
# SafeCheck on a constant whose opaque body cannot be read must abort with the
# quoter's error, not return a verdict (see [quote_safecheck_program] in
# safechecker-plugin/src/g_metarocq_safechecker.mlg).  Compiles
# opaque_unreadable_lib.v with -vos: its .vos file holds no opaque proof.  Then
# compiles opaque_unreadable.v with -vok, which loads a library from its .vos
# file when that file is not empty, so the library's opaque bodies are
# unreadable there; the [Fail] and [MetaRocq Test SafeCheck Aborts] commands of
# that file are the test, and its controls check that SafeCheck works in this
# mode.  Neither file is in _RocqProject.in: a normal build would give the
# library a .vo, with its proofs.
# Usage: check_opaque_unreadable.sh   (run in test-suite/, after the plugin is
# built; needs _RocqProject; passes $COQEXTRAFLAGS to rocq compile)
# Exit 0 when opaque_unreadable.v compiles; 1 otherwise.
set -u
flags=$(grep -E '^-(R|Q|I) ' _RocqProject | tr '\n' ' ')
rm -f opaque_unreadable_lib.vo opaque_unreadable_lib.vos opaque_unreadable.vok
eval rocq compile "${COQEXTRAFLAGS:-}" $flags -vos opaque_unreadable_lib.v \
  || { echo "MISMATCH: opaque_unreadable_lib.v does not compile with -vos"; exit 1; }
[ -s opaque_unreadable_lib.vos ] \
  || { echo "MISMATCH: opaque_unreadable_lib.vos is missing or empty"; exit 1; }
if eval rocq compile "${COQEXTRAFLAGS:-}" $flags -vok opaque_unreadable.v; then
  echo "ok: SafeCheck aborts with the quoter's error on an unreadable opaque body"
else
  echo "MISMATCH: opaque_unreadable.v failed (the error is above)"; exit 1
fi
