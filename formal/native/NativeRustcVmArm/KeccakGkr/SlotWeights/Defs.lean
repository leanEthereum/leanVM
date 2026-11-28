module

public import NativeRustcVmArm.KeccakGkr.Common
public import NativeRustcVmArm.KeccakGkr.SlotWeights.Exec
public import NativeRustcVm.KeccakGkr.Open
public import NativeRustcVmArm.Spec.Arrays

/-!
# `slot_weights`: the body's context

The body (`Body`: the 176-byte frame, the rows written), the segment kernel (`segK`), what the
loops leave in the rows (`prog`: the products of the segments' weights up to a flat index, zero
elsewhere), and the rows at the end (`rows_final`: `keccakSlotWeights`, end to end).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes)

@[expose] public section

/-- The rows. -/
abbrev rowsA (m0 : MachineData) : BitVec 64 := m0.regs.X6.toBitVec
/-- The bit weights. -/
abbrev wA (m0 : MachineData) : BitVec 64 := m0.regs.X3.toBitVec
/-- The frame's base. -/
abbrev fbA (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 176

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(168, .X19), (160, .X20), (152, .X21), (144, .X22), (136, .X23), (128, .X24), (120, .X25),
    (112, .X26), (104, .X27), (96, .X28), (80, .X29), (88, .X30)]

/-- The body: the 176-byte frame, the rows written. -/
abbrev Body (m0 st : MachineData) : Prop :=
  Frame m0 176 slotWeightsStack slots [⟨rowsA m0, rowsBytes⟩] st

/-- The segment kernel. -/
def segK (logSteps : Nat) (c : KeccakClaimW) : Array EW :=
  eqKernel (c.point.extract (logSteps - 4) c.point.size)

/-- The product at flat index `i` of the rows. -/
def V (logSteps : Nat) (c : KeccakClaimW) (first i : Nat) : EW :=
  (segK logSteps c).getD (i / 1600 - first) 0 * c.weights.getD (i % 1600) 0

/-- The rows after the products up to flat index `b`. -/
def prog (logSteps : Nat) (c : KeccakClaimW) (first b i : Nat) : EW :=
  if 1600 * first ≤ i ∧ i < b then V logSteps c first i else 0

end

public section

theorem slots_le : ∀ p ∈ slots, 80 ≤ p.1 ∧ p.1 + 8 ≤ 176 := by decide

theorem slots_le' : ∀ p ∈ slots, p.1 + 8 ≤ 176 := fun p hp ↦ (slots_le p hp).2

theorem all_slots : ∀ r, calleeSaved r = true → r ∉ slots.map (·.2) → r ∈ ([] : List XReg) := by
  intro r hr hn
  exfalso
  apply hn
  cases r <;> simp_all [calleeSaved, slots]

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

/-- **One element changed**: elements but the `n`th kept, the `n`th the new one. -/
theorem ElemsAt.update {d d' : DataMem} {a : BitVec 64} {f : Nat → EW} {N n : Nat} {v : EW}
    (h : ElemsAt d a f N) (hnw : NoWrap a (16 * N)) (hn : n < N)
    (hs : SameOutside d d' (InRange (a + BitVec.ofNat 64 (16 * n)) 16))
    (hv : NativeRustcVm.EWAt d' (a + BitVec.ofNat 64 (16 * n)) v) :
    ElemsAt d' a (fun i ↦ if i = n then v else f i) N := by
  intro i hi
  by_cases hin : i = n
  · subst hin; simpa using hv
  · simp only [hin, ite_false]
    refine NativeRustcVm.BytesAt.of_sameOutside_apart (h i hi) hs ?_ ?_ ?_
    · rw [NativeRustcVm.length_ewBytes]
      rcases Nat.lt_or_gt_of_ne hin with hlt | hgt
      · exact apart_in hnw (by omega) (by omega)
      · exact NativeRustcVm.Apart.symm (apart_in hnw (by omega) (by omega))
    · rw [NativeRustcVm.length_ewBytes]; exact NativeRustcVm.NoWrap.sub hnw (by omega)
    · exact NativeRustcVm.NoWrap.sub hnw (by omega)

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

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
