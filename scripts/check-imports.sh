#!/usr/bin/env bash
# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# The library must build against Init and Std alone, so that nothing from the Lean
# package can reach a consumer's binary. The module system already rejects runtime uses
# of a meta import; this is a cheap second line of defence that also rejects the meta
# imports themselves, which the library has no reason to use.
#
# The companion deriving package is exempt: it may use `meta import Lean.*`.

set -euo pipefail

cd "$(dirname "$0")/.."

if matches=$(grep -rnE '^[[:space:]]*(public[[:space:]]+)?(meta[[:space:]]+)?import[[:space:]]+Lean([.[:space:]]|$)' \
    Json.lean Json 2>/dev/null); then
  echo "error: the library must not import from the Lean package:" >&2
  echo "$matches" >&2
  exit 1
fi

echo "ok: no Lean package imports in the library"
