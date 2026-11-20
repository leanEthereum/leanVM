//go:build cgo && darwin && (amd64 || arm64)

package leanpq

// #cgo LDFLAGS: -L${SRCDIR}/internal/native/darwin_universal -llean_pq_native -lm
import "C"
