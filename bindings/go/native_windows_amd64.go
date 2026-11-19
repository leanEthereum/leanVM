//go:build cgo && windows && amd64

package leanpq

// The link libraries are the Rust standard library's imports (from `--print native-static-libs`)
// plus `synchronization`. MinGW ld scans the archive once, and the import stubs Rust embeds for
// WaitOnAddress and WakeByAddressSingle can come before the objects that call them.

// #cgo LDFLAGS: -L${SRCDIR}/internal/native/windows_amd64 -llean_pq_native -lkernel32 -lntdll -luserenv -lws2_32 -ldbghelp -lsynchronization
import "C"
