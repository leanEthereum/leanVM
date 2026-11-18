#!/bin/sh
# Check that Go platform selection matches the archives produced by stage-static.sh.
set -eu

go_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

assert_file_contains() {
    file=$1
    pattern=$2
    grep -F -- "$pattern" "$go_dir/$file" >/dev/null
}

assert_file_contains native_linux_amd64.go '//go:build cgo && linux && amd64'
assert_file_contains native_linux_amd64.go 'internal/native/linux_amd64'

assert_file_contains native_linux_arm64.go '//go:build cgo && linux && arm64'
assert_file_contains native_linux_arm64.go 'internal/native/linux_arm64'
assert_file_contains native_linux_arm64.go '-lgcc_s'

assert_file_contains native_darwin.go '//go:build cgo && darwin && (amd64 || arm64)'
assert_file_contains native_darwin.go 'internal/native/darwin_universal'

assert_file_contains native_windows_amd64.go '//go:build cgo && windows && amd64'
assert_file_contains native_windows_amd64.go 'internal/native/windows_amd64'
assert_file_contains native_windows_amd64.go '-lntdll -luserenv -lws2_32 -ldbghelp -lsynchronization'
