#!/bin/bash
# Build the default targets a few modules at a time. Lake has no job limit, and a parallel build of
# the generated kernel-checked families runs more of them at once than a 16 GB runner holds. Each
# round asks Lake for the modules whose dependencies are built, then builds them WIDTH at a time.
W=${WIDTH:-2}
for round in $(seq 1 5000); do
  frontier=$(lake build --no-build 2>&1 | grep '✖ .*Building ' | sed 's/.*Building //; s/ .*//')
  [ -z "$frontier" ] && break
  echo "round $round: $(echo "$frontier" | wc -l) modules"
  echo "$frontier" | xargs -n "$W" lake build -q || exit 1
done
lake build
