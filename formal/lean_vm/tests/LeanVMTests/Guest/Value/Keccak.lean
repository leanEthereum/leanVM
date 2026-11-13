import LeanVM.Guest.Value.Keccak
import LeanVM.Guest.Core
import LeanVM.Guest.Batch.Def

/-!
# Tests: the Keccak library

* The natural-number evaluator (`KeccakEval`) against the Spec's compiled `keccakF` and
  `keccak256`, and Keccak-256 of the empty string against its published value.
* **The theorems' hypotheses are the compiler's chain.** `chain` runs the `KECCAK`s exactly as
  `keccak_chain` and `keccak_final` describe them (block `k` reading the previous output plus the
  padded cells from `17k / 2`, in the layouts `inLayout k` and `outLayout B k`) on messages of
  every shape the guest hashes: lengths `0`, `48`, `64`, `80`, `128` (one block), `136`, `272`,
  `292` (`SP_ENCODING_BYTES`, ending four bytes into a cell), `1088` (a claim group, whole
  blocks) and `2000`; its digest cells are `digestHalves (keccak256 message)`. A nonzero byte
  past `len` in the last cell breaks it (the hypothesis `hz` is needed).
* `padCells_bytes` on the same shapes; the `state=` continuation after a whole-block prefix.
* The duplex step against the Spec's `duplex`, and a scalar's cells.
* **Templates for B1**: `keccak_one` on a lowered `keccak(a, b, out)` and `keccak_duplex` on a
  lowered `fs_pack` + `fs_perm`, the atoms' cells given as `cells13` lists, discharged by `simp`.
* The axioms of the main theorems.
-/

namespace LeanVMTests.Guest.Value.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value.KeccakEval LeanVM.Guest.Value.Keccak LeanVM.Guest.Value

/-! ## The evaluator -/

/-- A state with every lane different. -/
def s1 : KeccakState := Vector.ofFn fun i ↦ (i.val * 0x9E3779B97F4A7C15 + 7).toUInt64

#guard keccakFN (toNats s1) = toNats (keccakF1600 s1)
#guard keccakFN (toNats zeroState) = toNats keccakFZero

/-- `n` message bytes. -/
def bytes (n : ℕ) : List UInt8 := (List.range n).map fun i ↦ (i * 37 + 11).toUInt8

#guard [0, 1, 135, 136, 137, 271, 272, 500].all fun n ↦
  keccak256N ((bytes n).map UInt8.toNat) = (keccak256 (bytes n)).toList.map UInt64.toNat
-- Keccak-256 of the empty string,
-- `c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`.
#guard (keccak256 []).toList =
  [4333579421379646149, 13836122230913597074, 4262519377828905189, 8116759062988257915]

/-! ## The compiler's chain -/

/-- One `KECCAK`: the cells `KeccakCellsRelation` makes it write (cells as lists, computed once). -/
def perm (I : List E) (inOdd outOdd : Bool) : List E :=
  List.ofFn (cellsOfState (keccakF1600 (stateOfCells (fun c ↦ I.getD c 0) inOdd)) outOdd)

/-- `emit_keccak_message` over the cells `P`, `B` blocks from the cells `st0`: block `k` reads the
previous output plus the cells from `17k / 2`, the capacity unchanged. -/
def chain (P : List E) (st0 : List E) (B : ℕ) : List E :=
  (List.range B).foldl (fun O k ↦
    perm (List.ofFn fun c : Fin 13 ↦
      if c.val < 9 then O.getD c 0 + P.getD (17 * k / 2 + c) 0 else O.getD c 0) (inLayout k)
      (outLayout B k)) st0

/-- The zero cells. -/
def zeroCells : List E := List.replicate 13 0

/-- Canonical message cells whose bytes reach `len` and are zero past it. -/
def msgCells (len : ℕ) : List E :=
  (List.range ((len + 15) / 16)).map fun i ↦
    let full := E.ofLimbs (K.ofBits (i * 0x0123456789abcdef + 1)) (K.ofBits (i * 77 + 5))
    if 16 * (i + 1) ≤ len then full
    else
      -- the last cell: its first `len % 16` bytes only
      let r := len % 16
      if r ≤ 8 then E.ofLimbs (K.ofBits ((i + 0xdeadbeef) % 2 ^ (8 * r))) 0
      else E.ofLimbs (K.ofBits (i + 0xdeadbeef)) (K.ofBits ((i + 3) % 2 ^ (8 * (r - 8))))

/-- The message's bytes. -/
def msg (len : ℕ) : List UInt8 := (cellsBytes (msgCells len)).take len

/-- The lengths the guest hashes. -/
def lens : List ℕ := [0, 48, 64, 80, 128, 136, 272, 292, 1088, 2000]

-- The bytes past `len` are zero, and `len` fits.
#guard lens.all fun len ↦ (cellsBytes (msgCells len)).drop len |>.all (· = 0)
-- `padCells_bytes`.
#guard lens.all fun len ↦
  (cellsBytes (padCells (msgCells len) len)).take (rate * (len / rate + 1)) = padBytes (msg len)
-- `keccak_final_digest` with no prefix: the chain's digest cells are the hash.
#guard lens.all fun len ↦
  let O := chain (padCells (msgCells len) len) zeroCells (len / rate + 1)
  (O.getD 0 0, O.getD 1 0) = digestHalves (keccak256 (msg len))
-- And the chain's whole output is `keccak_final`'s state.
#guard lens.all fun len ↦
  chain (padCells (msgCells len) len) zeroCells (len / rate + 1) =
    List.ofFn (cellsOfState (absorbChunks (len / rate + 1) zeroState (padBytes (msg len))) false)
-- A nonzero byte past `len` in the last cell changes the digest.
#guard
  let cells := msgCells 292 ++ []
  let bad := cells.set 18 (cells.getD 18 0 + E.ofLimbs (K.ofBits (2 ^ 40)) 0)
  let O := chain (padCells bad 292) zeroCells 3
  (O.getD 0 0, O.getD 1 0) ≠ digestHalves (keccak256 (msg 292))

/-! ## `state=` after a whole-block prefix (`claim_list_digest`) -/

-- A claim group of `68` cells (`1088` bytes, eight blocks) absorbed with `final=0`, then the
-- rest with the default `final`: the digest of the concatenation.
#guard
  let pre := msgCells 1088
  let st := chain pre zeroCells 8
  let O := chain (padCells (msgCells 80) 80) st 1
  (O.getD 0 0, O.getD 1 0) = digestHalves (keccak256 (cellsBytes pre ++ msg 80))
-- `keccak_cells([0], digest, state=, len=0)`: the padding alone.
#guard
  let pre := msgCells 1088
  let st := chain pre zeroCells 8
  let O := chain (padCells [0] 0) st 1
  (O.getD 0 0, O.getD 1 0) = digestHalves (keccak256 (cellsBytes pre))

/-! ## The seed and the duplex -/

/-- Two digests. -/
def d1 : Digest := keccak256 (bytes 5)
def d2 : Digest := keccak256 (bytes 9)

#guard toNats (absorbChunks 1 zeroState (cellsBytes [(digestHalves d1).1, (digestHalves d1).2,
  (digestHalves d2).1, (digestHalves d2).2])) = toNats (keccakF1600 (Compile.seedInput d1 d2))

/-- Two waiting scalars, an observed one and a nonce. -/
def pending : List (E × ℕ) :=
  [(E.ofLimbs (K.ofBits 5) (K.ofBits 6), 1),
    (E.ofLimbs (K.ofBits 8) 0, 4)]

-- `keccak_duplex`: the rate cells, then the capacity of `s1`'s cells.
#guard perm (List.ofFn fun c : Fin 13 ↦
    if c.val < 8 then rateCell pending c else cellsOfState s1 false c) false false =
  List.ofFn (cellsOfState (keccakF1600 (Compile.duplexInput ⟨s1, pending, none⟩)) false)
-- `rateCell_scalar`: a scalar's cells are the scalar and its tag in the `y` limb.
#guard (rateCell pending 2, rateCell pending 3) = scalarCells (pending.getD 1 (0, 0)).1 4
#guard scalarCells (pending.getD 0 (0, 0)).1 1 = (E.ofLimbs (K.ofBits 5) (K.ofBits 6), y)
-- `challengeOf`: the state's first cell.
#guard Compile.challengeOf s1 = cellsOfState s1 false 0

/-! ## The baked constants -/

#guard toNats LeanVM.Node.batchSeed = toNats batchSeedValue
#guard (List.range 5).all fun c ↦
  LeanVM.Guest.litField (aggSeed.getD c 0) =
    cellsOfState LeanVM.Node.batchSeed false (Fin.ofNat 13 (8 + c))

/-! ## Templates -/

-- `keccak([a0, a1], [b0, b1], out)`: 64 bytes, the tail the padding run (`0x01`, then zeros),
-- `b8` the constant `0x80 << 56`, the capacity the zero run.
example (a0 a1 b0 b1 : E) (I O : Fin 13 → E)
    (hI : I = LeanVM.Guest.Core.cells13 [a0, a1, b0, b1, LeanVM.Guest.word 1 0, 0, 0, 0,
      LeanVM.Guest.word 9223372036854775808 0, 0, 0, 0, 0])
    (hK : KeccakCellsRelation I false O false .all) :
    (O 0, O 1) = digestHalves (keccak256 (cellsBytes [a0, a1, b0, b1])) := by
  have := (keccak_one (cells := [a0, a1, b0, b1]) (len := 64) (by simp) (by decide)
    (getD_cellsBytes_of_le (by simp))
    (fun c hc ↦ by
      subst hI
      fin_cases c <;> simp_all [padCells, xorByte, padRead, rate, byteCell,
        LeanVM.Guest.Core.cells13])
    (fun c hc ↦ by subst hI; fin_cases c <;> simp_all [LeanVM.Guest.Core.cells13]) hK).2
  rwa [List.take_of_length_le (by simp)] at this

-- `fs_pack(rate, 0, x, DS_OBSERVE)` then `keccak(rate[0:2], [0, 0], nxt, cap=sp)`.
example (S : KeccakState) (x : E) (I O : Fin 13 → E)
    (hI : I = LeanVM.Guest.Core.cells13 [x, E.ofLimbs 0 (K.ofBits 1), 0, 0, 0, 0,
      0, 0, cellsOfState S false 8, cellsOfState S false 9, cellsOfState S false 10,
      cellsOfState S false 11, cellsOfState S false 12])
    (hK : KeccakCellsRelation I false O false .all) :
    O = cellsOfState (keccakF1600 (Compile.duplexInput ⟨S, [(x, 1)], none⟩)) false := by
  have h01 := rateCell_scalar [(x, 1)] 0 (by simp)
  simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero, scalarCells, Prod.mk.injEq] at h01
  refine keccak_duplex (fun c hc ↦ ?_) (fun c hc ↦ ?_) hK
  · subst hI
    fin_cases c <;> simp at hc
    · exact h01.1.symm
    · exact h01.2.symm
    all_goals exact (rateCell_past _ (by simp)).symm
  · subst hI
    fin_cases c <;> simp at hc <;> rfl

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.Value.Keccak.keccak_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccak_chain

/-- info: 'LeanVM.Guest.Value.Keccak.keccak_final_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccak_final_digest

/-- info: 'LeanVM.Guest.Value.Keccak.keccak_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccak_one

/-- info: 'LeanVM.Guest.Value.Keccak.keccak_whole' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccak_whole

/-- info: 'LeanVM.Guest.Value.Keccak.keccak_duplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccak_duplex

/-- info: 'LeanVM.Guest.Value.Keccak.paddingBlobRoot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paddingBlobRoot_eq

/-- info: 'LeanVM.Guest.Value.Keccak.aggSeed_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aggSeed_cells

/-- info: 'LeanVM.Guest.Value.Keccak.keccakF_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms keccakF_zero

end LeanVMTests.Guest.Value.Keccak
