#!/bin/bash -eu

LISZT_PATH="$(cd "$(dirname "$(readlink -f "${BASH_SOURCE[0]}")")" && pwd)"

TERRA_PATH="$LISZT_PATH"/include/?.t "$LEGION_PATH"/language/regent.py "$@" -fparallelize 1
