//go:build cgo && linux && arm64

package leanpq

// #cgo LDFLAGS: -L${SRCDIR}/internal/native/linux_arm64 -llean_pq_native -ldl -lpthread -lm -lgcc_s
import "C"
