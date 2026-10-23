import LeanVM.Protocol.Blake2sCircuit

/-!
# BLAKE2s circuit tests

* **The shape.** `14720` product gates at `1280 … 15999`, then the `256` output rows; the
  circuit is bounded (by `decide`, beside the structural proof `bounded_blake2s`).
* **The rows against the deployed walk.** `rowsDigest` digests all `2 ^ 14` rows of `A` and `B`
  (the row table: the recorded gate, else the constant, input or zero row); the value is the same
  digest of the rows the pinned Python verifier's `blake2s_row_values` walks, run on the weights
  `w_j = x^j` of a characteristic-two field held as bitsets, so that row `k` returns the positions
  of row `k` of `A` and of `B` (computed at leanVM `a386121f`; at `127510d1` the function differs
  only in how it initialises the same sixteen state words). The row table agrees with `rowOf`,
  which the theorems are about, on a position of every row kind. This is test evidence of row
  equality, not a theorem.
* **The trace computes `compress`.** On the RFC 7693 Appendix B vector (`BLAKE2s-256("abc")`) and
  on pseudo-random inputs, the output words of the trace are `compress` of the inputs, and the
  trace satisfies every row.
* **What is rejected.** One flipped gate bit of the trace fails a row.

`holdsB` checks every row through the row table, the executable stand-in for the R1CS over
`ZMod 2`, whose naive walks (`2 ^ 28` products per block) do not run. A plain file, so `#guard`
evaluates the compiled definitions.
-/

namespace LeanVMTests.Protocol.Blake2sCircuit

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol ProductCircuit
  LeanVM.Protocol.Blake2sCircuit

/-! ## Executable views -/

/-- The row table: defaults, then the gates in reverse order, so that the first gate at a
position wins, as in `rowOf`. -/
def rowTable (c : ProductCircuit m) : Array (Gate m) :=
  let base : Array (Gate m) := Array.ofFn fun k : Pos m ↦
    if k = c.cpos then ⟨Form.var c.cpos, Form.var c.cpos⟩
    else if c.inputs.getLsbD k then ⟨Form.var k, Form.var c.cpos⟩
    else ⟨0, 0⟩
  c.gates.foldr (fun kg t ↦ t.set! kg.1 kg.2) base

/-- Every row holds at `z`, and the constant position holds `1`. -/
def holdsB (c : ProductCircuit m) (z : Form m) : Bool :=
  let t := rowTable c
  z.getLsbD c.cpos && (List.finRange (2 ^ m)).all fun k ↦
    let g := t[k.val]!
    z.getLsbD k == (g.a.evalB z && g.b.evalB z)

/-- The product gates. -/
def productGates : Array (Pos m × Gate m) := (compressW.run ⟨gateBase, #[]⟩).2.gates

/-- `Σ_k (3 (A_k mod P) + 7 (B_k mod P)) (k + 1) mod P` over the row table, `P = 2 ^ 64 - 59`: a
prime modulo which the powers `2 ^ j`, `j < 2 ^ 14`, are distinct. -/
def rowsDigest (c : ProductCircuit m) : ℕ :=
  let P := 2 ^ 64 - 59
  let t := rowTable c
  (List.range (2 ^ m)).foldl (fun d k ↦
    let g := t[k]!
    (d + ((g.a.toNat % P) * 3 + (g.b.toNat % P) * 7) * (k + 1)) % P) 0

/-- The word `u` at the positions `b, …, b + 31`. -/
def wordAt (b : ℕ) (u : UInt32) : Form m := BitVec.ofNat _ u.toNat <<< b

/-- The input block of one compression. -/
def inputsOf (h : Vector UInt32 8) (msg : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Form m :=
  let cv := (List.finRange 8).foldl (fun z w ↦ z ||| wordAt (32 * w.val) h[w]) 0
  let ms := (List.finRange 16).foldl (fun z w ↦ z ||| wordAt (640 + 32 * w.val) msg[w]) cv
  ms ||| wordAt 1152 t.toUInt32 ||| wordAt 1184 (t >>> 32).toUInt32 ||| wordAt 1216 f0 |||
    wordAt 1248 f1

/-- The output words at `256 … 511`. -/
def outWords (z : Form m) : Vector UInt32 8 :=
  Vector.ofFn fun w : Fin 8 ↦ UInt32.ofNat ((z >>> (256 + 32 * w.val)).toNat % 2 ^ 32)

/-! ## The shape -/

#guard productGates.size == 14720
#guard (productGates[0]?.map (·.1.val), productGates.back?.map (·.1.val)) == (some 1280, some 15999)
#guard blake2sCircuit.gates.size == 14720 + 256
#guard decide blake2sCircuit.Bounded

example : (compressW.run ⟨gateBase, #[]⟩).2.next = 16000 := compressW_next

/-! ## The rows against the deployed walk -/

#guard rowsDigest blake2sCircuit == 4056851438423586957

/-- Positions of every row kind: chaining value, output, the constant, padding, message, counter,
flags, a majority, a ripple and a carry row of the first and last mixing steps, the end padding. -/
def samplePositions : List ℕ :=
  [0, 255, 256, 300, 511, 512, 513, 639, 640, 1151, 1152, 1279, 1280, 1310, 1311, 1340, 1341,
    1371, 1372, 1463, 15815, 15876, 15968, 15999, 16000, 16383]

-- The row table the digest reads is `rowOf`, the rows the theorems are about.
#guard samplePositions.all fun k ↦
  let g := (rowTable blake2sCircuit)[k]!
  let g' := blake2sCircuit.rowOf (pos k)
  g.a == g'.a && g.b == g'.b

/-! ## The trace computes `compress` -/

/-- RFC 7693 §2.8: the unkeyed BLAKE2s-256 parameter block XORed into `iv[0]`. -/
def paramIv : Vector UInt32 8 := iv.set 0 (iv[0] ^^^ 0x01010020)

/-- The zero-padded block of `"abc"`. -/
def abcBlock : Vector UInt32 16 := #v[0x00636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- `BLAKE2s-256("abc")`, RFC 7693 Appendix B. -/
def abcDigest : Vector UInt32 8 :=
  #v[0x8c5e8c50, 0xe2147c32, 0xa32ba7e1, 0x2f45eb4e, 0x208b4537, 0x293ad69e, 0x4c9b994d,
    0x82596786]

/-- The trace of the `"abc"` compression. -/
def abcTrace : Form m := blake2sCircuit.trace (inputsOf paramIv abcBlock 3 0xFFFFFFFF 0)

#guard (outWords abcTrace).toList == abcDigest.toList
#guard holdsB blake2sCircuit abcTrace

/-- Pseudo-random words (a 64-bit linear congruential generator). -/
def lcgWords (seed n : ℕ) : List UInt32 :=
  (List.range n).foldl (fun (acc : ℕ × List UInt32) _ ↦
    let s := (acc.1 * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    (s, UInt32.ofNat (s / 2 ^ 32) :: acc.2)) (seed, []) |>.2

/-- The circuit agrees with `compress` on a pseudo-random input, and its trace holds. -/
def randomCheck (seed : ℕ) : Bool :=
  let ws := lcgWords seed 28
  let h : Vector UInt32 8 := Vector.ofFn fun i ↦ ws.getD i 0
  let msg : Vector UInt32 16 := Vector.ofFn fun i ↦ ws.getD (8 + i) 0
  let t : UInt64 := (ws.getD 24 0).toUInt64 ||| ((ws.getD 25 0).toUInt64 <<< 32)
  let z := blake2sCircuit.trace (inputsOf h msg t (ws.getD 26 0) (ws.getD 27 0))
  (outWords z).toList == (compress h msg t (ws.getD 26 0) (ws.getD 27 0)).toList &&
    holdsB blake2sCircuit z

#guard (List.range 3).all randomCheck

/-! ## What is rejected -/

-- A gate's bit (position `9000`) flipped.
#guard !holdsB blake2sCircuit (abcTrace ^^^ Form.var (pos 9000))

-- An output bit (position `300`) flipped.
#guard !holdsB blake2sCircuit (abcTrace ^^^ Form.var (pos 300))

-- The constant position cleared.
#guard !holdsB blake2sCircuit (abcTrace ^^^ Form.var Flock.constPos)

end LeanVMTests.Protocol.Blake2sCircuit
