module

public import NativeRustcVmX64.KeccakGkr.Common
public import NativeRustcVmX64.KeccakGkr.SlotWeights.Exec
public import NativeRustcVm.KeccakGkr.Open
public import NativeVm.Math.Keccak.Facts

/-!
# `slot_weights`: the body's context (x86-64)

The arguments (`rowsA` the rows, the stack argument; `wA` the bit weights), the frame's base
`fbA` (160 bytes below the entry's RSP), what the function may change (`Out`: the rows and its
stack), the locals the prologue leaves (`Loc`: `eq_kernel`'s result, `first`, `count`, the weights'
address, the segment kernel's first two elements), the body's context (`Ctx`: the frame, memory
changed only in `Out`, the locals). The segment kernel (`segK`), what the loops leave in the rows
(`prog`: the products of the segments' weights up to a flat index, zero elsewhere), and the rows
at the end (`rows_final`: `keccakSlotWeights`, end to end).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- The rows. -/
abbrev rowsA (m0 : MachineData) : BitVec 64 := slotRows m0
/-- The bit weights. -/
abbrev wA (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The point. -/
abbrev ptA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The frame's base. -/
abbrev fbA (m0 : MachineData) : BitVec 64 := stackBelow m0 160
/-- The stack argument's address. -/
abbrev argA (m0 : MachineData) : BitVec 64 := rspOf m0 + 8#64

/-- The segment kernel. -/
def segK (logSteps : Nat) (c : KeccakClaimW) : Array EW :=
  eqKernel (c.point.extract (logSteps - 4) c.point.size)

/-- The product at flat index `i` of the rows. -/
def V (logSteps : Nat) (c : KeccakClaimW) (first i : Nat) : EW :=
  (segK logSteps c).getD (i / 1600 - first) 0 * c.weights.getD (i % 1600) 0

/-- The rows after the products up to flat index `b`. -/
def prog (logSteps : Nat) (c : KeccakClaimW) (first b i : Nat) : EW :=
  if 1600 * first ≤ i ∧ i < b then V logSteps c first i else 0

/-- What the function may change: the rows and its stack. -/
def Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (rowsA m0) rowsBytes q ∨
    NativeRustcVm.InRange (stackBelow m0 slotWeightsStack) slotWeightsStack q

/-- **The locals** the prologue leaves in the frame. -/
structure Loc (m0 : MachineData) (c : KeccakClaimW) (d : DataMem) : Prop where
  ok : NativeRustcVm.WordAt d (off (fbA m0) 8) 1
  first : NativeRustcVm.WordAt d (off (fbA m0) 16) (UInt64.ofBitVec (reg m0 .r8))
  count : NativeRustcVm.WordAt d (off (fbA m0) 24) (UInt64.ofBitVec (reg m0 .r9))
  wts : NativeRustcVm.WordAt d (off (fbA m0) 40) (UInt64.ofBitVec (wA m0))
  seg : ∀ i < 2, NativeRustcVm.EWAt d (off (fbA m0) (48 + 16 * i))
    ((segK (reg m0 .rdi).toNat c).getD i 0)

/-- **The body's context**: the frame, memory changed only in `Out`, the locals. -/
structure Ctx (m0 : MachineData) (c : KeccakClaimW) (st : MachineData) : Prop where
  frame : Frame m0 160 slots 8 st
  same : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0)
  loc : Loc m0 c st.dmem

end

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide

theorem slots_ge : ∀ p ∈ slots, 112 ≤ p.1 := by decide

theorem prog_succ (logSteps : Nat) (c : KeccakClaimW) {first n : Nat} (h : 1600 * first ≤ n) :
    (fun i ↦ if i = n then V logSteps c first n else prog logSteps c first n i) =
      prog logSteps c first (n + 1) := by
  funext i
  unfold prog
  by_cases hi : i = n
  · subst hi; simp [h]
  · simp only [hi, ite_false]
    congr 1
    apply propext
    omega

theorem prog_start (logSteps : Nat) (c : KeccakClaimW) (first : Nat) :
    prog logSteps c first (1600 * first) = fun _ ↦ 0 := by
  funext i
  unfold prog
  rw [ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)]

/-- **The rows at the end**: `keccakSlotWeights`, end to end. -/
theorem rows_final {logSteps : Nat} {c : KeccakClaimW} {first count : Nat} {d : DataMem}
    {a : BitVec 64} (hc : first + count ≤ 2)
    (h : ElemsAt d a (prog logSteps c first (1600 * (first + count))) 4096) :
    NativeRustcVm.EWsAt d a (rowsFlat (keccakSlotWeights logSteps c first count)) := by
  obtain ⟨hsz, hrow⟩ := NativeVm.Math.Keccak.slotWeights_size logSteps c first count
  apply ElemsAt.ewsAt
  rw [rowsFlat, NativeRustcVm.KeccakGkr.rowsFlat_length _ (fun r hr ↦ hrow r (by omega)), hsz]
  intro i hi
  obtain ⟨r, z, hz, rfl⟩ : ∃ r z, z < 64 ∧ i = 64 * r + z :=
    ⟨i / 64, i % 64, Nat.mod_lt _ (by decide), by omega⟩
  have e : (rowsFlat (keccakSlotWeights logSteps c first count)).getD (64 * r + z) 0 =
      prog logSteps c first (1600 * (first + count)) (64 * r + z) := by
    rw [rowsFlat, List.getD_eq_getElem?_getD, NativeRustcVm.KeccakGkr.rowsFlat_getElem? _
      (fun r hr ↦ hrow r (by omega)) (by omega) hz, Option.getD_some,
      NativeVm.Math.Keccak.slotWeights_getD logSteps c hc (by omega) hz, NativeVm.Math.Keccak.slotRow, prog,
      V, segK]
    have h1 : (64 * r + z) / 1600 = r / 25 := by omega
    have h2 : (64 * r + z) % 1600 = 64 * (r % 25) + z := by omega
    rw [h1, h2]
    congr 1
    apply propext
    omega
  have := h (64 * r + z) (by omega)
  show NativeRustcVm.EWAt d _
    ((rowsFlat (keccakSlotWeights logSteps c first count)).getD (64 * r + z) 0)
  rw [e]
  exact this

/-- The locals kept where memory changed only off them. -/
theorem Loc.keep {m0 : MachineData} {c : KeccakClaimW} {d d' : DataMem} (h : Loc m0 c d)
    {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d d' R)
    (hR : ∀ j, (8 ≤ j ∧ j < 32) ∨ (40 ≤ j ∧ j < 80) → ¬ R (off (fbA m0) j)) : Loc m0 c d' := by
  have hw : ∀ (o : Nat) (bs : List UInt8), NativeRustcVm.BytesAt d (off (fbA m0) o) bs →
      (∀ i < bs.length, (8 ≤ o + i ∧ o + i < 32) ∨ (40 ≤ o + i ∧ o + i < 80)) →
      NativeRustcVm.BytesAt d' (off (fbA m0) o) bs := fun o bs hb hin ↦
    NativeRustcVm.Transcript.bytesAt_congr hb fun i hi ↦ by
      rw [NativeRustcVm.Transcript.off_add]
      exact hs _ (hR _ (hin i hi))
  have h8 : ∀ w : UInt64, (NativeRustcVm.wordBytes w).length = 8 := NativeRustcVm.length_wordBytes
  refine ⟨hw _ _ h.ok fun i hi ↦ ?_, hw _ _ h.first fun i hi ↦ ?_, hw _ _ h.count fun i hi ↦ ?_,
    hw _ _ h.wts fun i hi ↦ ?_, fun i hi ↦ hw _ _ (h.seg i hi) fun t ht ↦ ?_⟩
  · rw [h8] at hi; omega
  · rw [h8] at hi; omega
  · rw [h8] at hi; omega
  · rw [h8] at hi; omega
  · rw [NativeRustcVm.length_ewBytes] at ht; omega

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
