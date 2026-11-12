package leanvmsidecar

import "syscall"

// mapPopulate maps every page at mmap, so no request takes this process's first-touch faults on the arena.
const mapPopulate = syscall.MAP_POPULATE
