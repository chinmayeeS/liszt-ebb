#!/bin/bash -eu

LISZT_PATH="$(cd "$(dirname "$(perl -MCwd -le 'print Cwd::abs_path(shift)' "${BASH_SOURCE[0]}")")" && pwd)"

TERRA_PATH="$LISZT_PATH"/include/?.t "$LEGION_PATH"/language/regent.py "$@" -fparallelize 1
