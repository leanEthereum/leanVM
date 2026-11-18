package leanvmsidecar

import (
	"bytes"
	"errors"
	"os"
	"testing"
)

// Against a running sidecar, whose socket LEANVM_SIDECAR_SOCKET names: a blob-only leaf, which needs no keys, a node
// over it, verifying both ways, and a refusal that leaves the connection usable.
func TestSidecar(t *testing.T) {
	socket := os.Getenv("LEANVM_SIDECAR_SOCKET")
	if socket == "" {
		t.Skip("LEANVM_SIDECAR_SOCKET names no sidecar")
	}
	c, err := Dial(socket)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	blob := make([]byte, 8192*16)
	for i := range blob {
		blob[i] = byte(i)
	}
	leaf, err := c.Aggregate(nil, nil, nil, [][]byte{blob}, nil, 2)
	if err != nil {
		t.Fatal(err)
	}
	node, err := c.Aggregate([]Proven{leaf}, nil, nil, nil, nil, 1)
	if err != nil {
		t.Fatal(err)
	}
	if !bytes.Equal(node.Claims, leaf.Claims) {
		t.Fatal("the node publishes other claims than its leaf")
	}
	noClaims := make([]byte, 17)
	for _, check := range []struct {
		claims, proof []byte
		valid         bool
	}{{leaf.Claims, leaf.Proof, true}, {node.Claims, node.Proof, true}, {noClaims, node.Proof, false}, {node.Claims, nil, false}} {
		if valid, err := c.Verify(check.claims, check.proof); err != nil || valid != check.valid {
			t.Fatalf("verify: %v, %v, want %v", valid, err, check.valid)
		}
	}

	var rejection *Rejection
	if _, err := c.Aggregate(nil, nil, nil, [][]byte{blob}, nil, 0); !errors.As(err, &rejection) || rejection.Status != 1 {
		t.Fatalf("rate 0: %v", err)
	}
	if valid, err := c.Verify(leaf.Claims, leaf.Proof); err != nil || !valid {
		t.Fatalf("after a refusal: %v, %v", valid, err)
	}
}
