import { strict as assert } from "node:assert";
import { test } from "node:test";
import { Block, place } from "./client";

// Random sends and in-order frees: a placed block is inside the arena and overlaps no live one.
test("blocks never overlap", () => {
  const arenaLen = 100;
  let live: Block[] = [];
  let state = 1n;
  let placed = 0;
  for (let id = 0n; id < 10000n; id++) {
    state = (state * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n);
    const len = Number((state >> 33n) % 40n);
    const off = place(live, arenaLen, len);
    if (off !== null) {
      assert.ok(off + len <= arenaLen);
      for (const b of live) {
        const bEnd = b.off + b.payloadLen + b.respCap;
        assert.ok(off + len <= b.off || bEnd <= off);
      }
      live.push({ id, off, payloadLen: len, respCap: 0 });
      placed++;
    } else {
      live = live.slice(1);
    }
    if (state >> 63n === 1n) {
      live = live.slice(1);
    }
  }
  assert.ok(placed > 1000);
});
