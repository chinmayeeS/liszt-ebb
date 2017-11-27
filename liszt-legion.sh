#!/bin/bash -eu

LISZT_PATH="$(cd "$(dirname "$(perl -MCwd -le 'print Cwd::abs_path(shift)' "${BASH_SOURCE[0]}")")" && pwd)"

gcc -g -O2 -c -o "$LISZT_PATH"/json.o "$LISZT_PATH"/json.c
ar rcs "$LISZT_PATH"/libjsonparser.a "$LISZT_PATH"/json.o

TERRA_PATH="$LISZT_PATH"/include/?.t \
    LIBRARY_PATH="$LIBRARY_PATH:$LISZT_PATH" \
    INCLUDE_PATH="$LISZT_PATH" \
    "$LEGION_PATH"/language/regent.py "$@" -fparallelize 1 -fflow 0 -fdebug 1
