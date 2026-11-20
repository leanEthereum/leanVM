//go:build cgo && linux && amd64

package leanpq

// #cgo LDFLAGS: -L${SRCDIR}/internal/native/linux_amd64 -llean_pq_native -ldl -lpthread -lm
import "C"
