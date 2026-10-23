import LeanVM.Arithmetization.Tables.Blake2s
import LeanVM.Protocol.FlockSpec

/-!
# Flock specification tests

* **The relation.** The executor's `BLAKE2S` row (of its test `blake2s_computes_the_compression`
  at leanVM `a386121f`, as in `tests/LeanVMTests/Arithmetization/Tables.lean`) and the RFC 7693
  `"abc"` compression, as limb rows, are compressions; one flipped output bit is not.
* **The slots.** The deployed `SLOTS` of `hash_flock.rs:86-108`, injective; fourteen input limbs.
* **The honest column.** Two blocks, the two rows: the slots of every block read its row back, so
  the circuit's trace computes the executor's and the RFC's outputs; the column's blocks are the
  honest blocks bit for bit.
* **The deployed prover's column.** The honest column of the two rows and six of the prover's
  padding block has the digest of the region the pinned Rust prover commits for the same eight
  compressions: a differential vector for the packing and the whole gate witness. The two-row
  checks above test the packing round trip, not fidelity.
* **What `slots_gen` needs.** The column of a row whose output is wrong carries the true output at
  the output slots, not the row's.
* **The constant position.** The zero column fails the region predicate of the inhabitant.
* **The statements.** `compress_of_region` and `region_holds_gen` at the inhabitant, by type.
* **leanISA's relation.** `Blake2sRelation r` is `LimbsCompress` of `r`'s eighteen value limbs in
  column order: what the adaptor will use.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanVMTests.Protocol.FlockSpec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol ProductCircuit Blake2sFlock
  Blake2sCircuit

/-! ## The relation -/

/-- The executor's row, limbs in the order `m0, m1, m2, m3, out0, out1, cv0, cv1, md`. -/
def rustRow : Fin 18 → K :=
  ![K.ofBits 0x0123456789abcdef, K.ofBits 0xfedcba9876543210,
    K.ofBits 0x1111222233334444, K.ofBits 0x5555666677778888,
    K.ofBits 0xdeadbeefcafebabe, K.ofBits 0x0badf00d0badf00d,
    K.ofBits 0x9999aaaabbbbcccc, K.ofBits 0xddddeeeeffff0000,
    K.ofBits 0x583fffe1350e2137, K.ofBits 0x0de9e32629a5c508,
    K.ofBits 0xf1b0679a15df60bb, K.ofBits 0x0228c8d4ed9b3a24,
    K.ofBits 0x0000000000000007, 0,
    K.ofBits 0x000000000000000b, 0,
    K.ofBits 0x0000000000000040, K.ofBits 0x00000000ffffffff]

/-- The cell of two words, low word first. -/
def limb (lo hi : UInt32) : K := K.ofBits (lo.toNat + 2 ^ 32 * hi.toNat)

/-- RFC 7693 Appendix B, `BLAKE2s-256("abc")`: the parameter block XORed into `iv[0]`, the
zero-padded block, counter `3`, last-block flag set, and the digest. -/
def abcRow : Fin 18 → K :=
  ![limb 0x00636261 0, 0, 0, 0, 0, 0, 0, 0,
    limb 0x8c5e8c50 0xe2147c32, limb 0xa32ba7e1 0x2f45eb4e,
    limb 0x208b4537 0x293ad69e, limb 0x4c9b994d 0x82596786,
    limb (0x6A09E667 ^^^ 0x01010020) 0xBB67AE85, limb 0x3C6EF372 0xA54FF53A,
    limb 0x510E527F 0x9B05688C, limb 0x1F83D9AB 0x5BE0CD19,
    K.ofBits 3, limb 0xFFFFFFFF 0]

/-- The executor's row with bit `0` of `out1`'s low limb flipped. -/
def badRow : Fin 18 → K := Function.update rustRow 10 (K.ofBits 0xf1b0679a15df60ba)

#guard decide (LimbsCompress rustRow)
#guard decide (LimbsCompress abcRow)
#guard !decide (LimbsCompress badRow)

/-! ## The slots -/

#guard (List.finRange 18).map (fun j ↦ (slots j).val) ==
  [10, 11, 12, 13, 14, 15, 16, 17, 4, 5, 6, 7, 0, 1, 2, 3, 18, 19]

example : Function.Injective slots := slots_injective

#guard ((List.finRange 18).filter fun j ↦ decide (IsInputLimb j)).length == 14

/-! ## The honest column -/

/-- Two blocks: the executor's row and the RFC's. -/
def rows : Vector (Fin 18 → K) (2 ^ 1) := #v[rustRow, abcRow]

/-- The slots of every block read its row back. -/
def slotsReadBack {κ : ℕ} (col : Column (8 + κ)) (rs : Vector (Fin 18 → K) (2 ^ κ)) : Bool :=
  (List.finRange (2 ^ κ)).all fun t ↦
    (List.finRange 18).all fun j ↦ slotLimbs slots col t j == rs[t] j

/-- Block `t` of the column is the bitset `hb`, bit for bit. -/
def blockIs {κ : ℕ} (col : Column (8 + κ)) (t : Fin (2 ^ κ)) (hb : Form m) : Bool :=
  (List.range (2 ^ 14)).all fun j ↦ blockBits col t (pos j) == hb.getLsbD j

/-- Every check on one column, so that it is built once (the interpreter does not cache a
column across commands). -/
def honestChecks (col : Column (8 + 1)) : Bool :=
  slotsReadBack col rows && blockIs col 0 (honestBlock rustRow) &&
    blockIs col 1 (honestBlock abcRow)

#guard honestChecks (genColumn rows)

/-! ## The deployed prover's column -/

/-- The prover's padding block, `flock::hash::padding_block`: the compression of the zero block
under the parameter `iv`, counter `64`, last-block flag set. The output limbs are left `0`: the
honest column computes them. -/
def padRow : Fin 18 → K :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    limb 0x6b08e647 0xbb67ae85, limb 0x3c6ef372 0xa54ff53a,
    limb 0x510e527f 0x9b05688c, limb 0x1f83d9ab 0x5be0cd19,
    K.ofBits 64, limb 0xFFFFFFFF 0]

/-- `Σ_u (word_u mod P) (u + 1) mod P`, `P = 2 ^ 64 - 59`, over a column's cells. -/
def columnDigest {n : ℕ} (c : Column n) : ℕ :=
  let P := 2 ^ 64 - 59
  (List.finRange (2 ^ n)).foldl (fun d u ↦
    (d + (c.values[u].toBitVec.toNat % P) * (u.val + 1)) % P) 0

-- The honest column of the executor's row, the RFC's and six padding rows is the region the
-- pinned prover commits for the same compressions (the first output of
-- `flock::hash::generate_witness_with_ab_packed_and_lincheck` at leanVM `a386121f`, which
-- `build_qflock_prepared` copies word for word into `q_flock`): the packing, the gate witness
-- and the output agree cell for cell.
/-- The eight rows. -/
def eightRows : Vector (Fin 18 → K) (2 ^ 3) :=
  Vector.ofFn fun t ↦ if t.val = 0 then rustRow else if t.val = 1 then abcRow else padRow

#guard columnDigest (genColumn (κ := 3) eightRows) == 13489362985207589888

/-! ## What `slots_gen` needs -/

/-- The column of the bad row carries the executor's true output at `out1`'s low slot. -/
def badChecks (col : Column (8 + 0)) : Bool :=
  slotLimbs slots col 0 10 == rustRow 10 && slotLimbs slots col 0 10 != badRow 10

#guard badChecks (genColumn #v[badRow])

/-! ## The constant position -/

/-- The zero column of one block. -/
def zeroCol : Column (8 + 0) := ⟨Vector.replicate _ 0⟩

example : ¬ BlockR1CS.BatchHolds blake2sFlockSpec.r1cs Flock.constPos (bitTable zeroCol) := by
  intro h
  have h1 := (h 0).2
  rw [batchBlock_bitTable] at h1
  simp [liftBlock, ofBool, blockBits, blockCell, zeroCol] at h1

/-! ## The statements -/

example {S : Shape} (r : FlockRegion S) (hA : r.r1cs.A = blake2sFlockSpec.r1cs.A)
    (hB : r.r1cs.B = blake2sFlockSpec.r1cs.B) (c : Column (8 + r.kBatch)) (h : r.Holds c)
    (t : Fin (2 ^ r.kBatch)) : LimbsCompress (slotLimbs slots c t) :=
  blake2sFlockSpec.compress_of_region r hA hB c h t

example {S : Shape} (r : FlockRegion S) (hA : r.r1cs.A = blake2sFlockSpec.r1cs.A)
    (hB : r.r1cs.B = blake2sFlockSpec.r1cs.B) (rs : Vector (Fin 18 → K) (2 ^ r.kBatch)) :
    r.Holds (genColumn rs) :=
  blake2sFlockSpec.region_holds_gen r hA hB rs

/-! ## leanISA's relation -/

/-- The eighteen value limbs of a `BLAKE2S` row, in column order. -/
def limbsOf (r : LeanVM.Arithmetization.Blake2sRow K) : Fin 18 → K :=
  ![r.m0[0], r.m0[1], r.m1[0], r.m1[1], r.m2[0], r.m2[1], r.m3[0], r.m3[1], r.out0[0], r.out0[1],
    r.out1[0], r.out1[1], r.cv0[0], r.cv0[1], r.cv1[0], r.cv1[1], r.md[0], r.md[1]]

theorem vec2_eta (v : Vector K 2) : #v[v[0], v[1]] = v := by
  refine Vector.ext fun i hi ↦ ?_
  interval_cases i <;> rfl

example (r : LeanVM.Arithmetization.Blake2sRow K) :
    LeanVM.Arithmetization.Blake2sRelation r ↔ LimbsCompress (limbsOf r) := by
  simp only [LeanVM.Arithmetization.Blake2sRelation, LimbsCompress, limbsOf, Matrix.cons_val,
    vec2_eta]

end LeanVMTests.Protocol.FlockSpec
