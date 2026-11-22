#!/bin/sh
# Note 14, section 7.1: every exhaustive case of the interleaving check. Builds into $TMPDIR.
set -e
here=$(cd "$(dirname "$0")" && pwd)
out=${TMPDIR:-/tmp}/interleave14.$$
cc -O2 -o "$out" "$here/14_interleave.c"
for a in "3 3 1 3" "3 3 1 4" "3 3 2 4" "3 3 2 5" "3 3 3 4" "3 3 3 5" "3 3 4 5" "3 3 4 6" "3 3 5 6" \
         "4 3 2 4" "4 3 2 5" "4 3 3 4" "4 3 3 5" "4 3 4 5" "4 3 4 6" "4 3 1 3" \
         "4 4 11 13" "4 4 12 14" "4 4 13 15"; do
    set -- $a
    "$out" "$@"
done
rm -f "$out"
