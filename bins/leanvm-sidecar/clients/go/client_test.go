package leanvmsidecar

import "testing"

// Random sends and in-order frees: a placed block is inside the arena and overlaps no live one.
func TestBlocksNeverOverlap(t *testing.T) {
	const arenaLen = 100
	var live []block
	state, placed := uint64(1), 0
	for id := uint64(0); id < 10000; id++ {
		state = state*6364136223846793005 + 1442695040888963407
		n := (state >> 33) % 40
		if off, ok := place(live, arenaLen, n); ok {
			if off+n > arenaLen {
				t.Fatalf("block [%d, %d) outside the arena", off, off+n)
			}
			for _, b := range live {
				if off+n > b.off && b.end() > off {
					t.Fatalf("block [%d, %d) overlaps [%d, %d)", off, off+n, b.off, b.end())
				}
			}
			live = append(live, block{id: id, off: off, payloadLen: n})
			placed++
		} else {
			live = live[1:]
		}
		if state>>63 == 1 && len(live) > 0 {
			live = live[1:]
		}
	}
	if placed <= 1000 {
		t.Fatal("too few blocks placed")
	}
}
