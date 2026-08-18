#!/usr/bin/env bash
# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Nothing from the Lean package may reach a consumer's binary. `check-imports.sh` reads that
# claim off the library's source; this one reads it off what the compiler produced, which is
# the form the claim is actually about.
#
# Three things are checked, and they need both packages built first:
#
#   1. No compiled module of the library refers to the Lean package at all.
#   2. The companion's runtime initialiser starts no Lean module. Its meta initialiser does,
#      which is the whole point of a `meta import`: the elaborator gets the frontend, and a
#      program that merely uses what was derived does not.
#   3. A consumer's own compiled modules, the ones holding the derived instances and the
#      literal syntax, refer to nothing from the Lean package either.

set -euo pipefail

cd "$(dirname "$0")/.."

# Built here rather than assumed, so that the check cannot pass on yesterday's output.
lake build >/dev/null
(cd deriving && lake build >/dev/null)
(cd deriving/test && lake build >/dev/null)

status=0

lean_refs() {
  grep -l 'l_Lean_\|initialize_Lean_' "$@" 2>/dev/null || true
}

library=$(lean_refs .lake/build/ir/*.c .lake/build/ir/Json/*.c)
if [ -n "$library" ]; then
  echo "error: compiled library modules refer to the Lean package:" >&2
  echo "$library" >&2
  status=1
fi

for c in deriving/.lake/build/ir/JsonDeriving.c deriving/.lake/build/ir/JsonDeriving/*.c; do
  [ -f "$c" ] || continue
  if awk '/LEAN_EXPORT lean_object\* runtime_initialize_/,/^}/' "$c" | grep -q 'initialize_Lean'; then
    echo "error: $c starts a Lean module at runtime, not only during elaboration" >&2
    status=1
  fi
done

consumer=$(lean_refs deriving/test/.lake/build/ir/Test/Codecs.c deriving/test/.lake/build/ir/Test/Syntax.c)
if [ -n "$consumer" ]; then
  echo "error: a consumer's modules refer to the Lean package:" >&2
  echo "$consumer" >&2
  status=1
fi

if [ "$status" -eq 0 ]; then
  echo "ok: nothing from the Lean package is reachable at run time"
fi
exit "$status"
