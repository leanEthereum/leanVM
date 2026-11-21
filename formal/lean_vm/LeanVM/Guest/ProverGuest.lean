/-
  LeanVM.Guest.ProverGuest

  `Statement/Prover/Guest.lean`'s witness generation is the honest hint generator the proofs use
  (`LeanVM.Guest.Hints`).
-/

module

public import Statement.Prover.Guest
public import LeanVM.Guest.Hints
public import LeanVM.Guest.AcceptableChild
import LeanVM.Wire.ReadWrite
import LeanVM.Protocol.Verifier.Load

/-!
# The statement's witness generation is the proofs' hint generator

`Statement/Prover/Guest.lean` writes the guest's witness generation with the statement's own
definitions; the proofs reason about `LeanVM.Guest.Hints`, the same pushes written with
`lean_vm`'s helpers. They agree function by function (`honestPushes_eq`); `EndExecFinal.lean` takes
the statement's advice to `guestAdvice` (`guestAdvice_eq`). The only differences
are of form: a cell of 16 bytes read lane by lane (`littleEndianLane`) rather than by
`laneOfBytes` (equal for 16 bytes or more, `cellOfBytes_eq`), and the coverage plan's own
structure (`coveragePlan_eq`).
-/

namespace LeanVM.Guest.ProverGuest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

public section

/-! ## Cells -/

theorem lane_eq {b : List UInt8} (h : 8 ≤ b.length) : littleEndianLane b 0 = laneOfBytes b := by
  have hb : b = wordBytes (laneOfBytes b) ++ b.drop 8 := by
    rw [wordBytes_laneOfBytes h, List.take_append_drop]
  conv_lhs => rw [hb]
  exact LeanVM.Wire.littleEndianLane_wordBytes_append _ _

theorem cellOfBytes_eq {b : List UInt8} (h : 16 ≤ b.length) :
    Prover.Guest.cellOfBytes b = Hints.cellOfBytes b := by
  rw [Prover.Guest.cellOfBytes, Hints.cellOfBytes, kOfBytes, kOfBytes, lane_eq (by omega),
    LeanVM.Wire.littleEndianLane_eq_drop b 1, Nat.mul_one, lane_eq (by simp; omega)]

theorem cell128_eq : Prover.Guest.cell128 = Hints.cell128 := by
  funext v
  rw [Prover.Guest.cell128, Hints.cell128, cellOfBytes_eq (by simp [HashSig.littleEndianBytes])]

theorem cellsOfBytes_eq : Prover.Guest.cellsOfBytes = Hints.cellsOfBytes := by
  funext b
  rw [Prover.Guest.cellsOfBytes, Hints.cellsOfBytes]
  refine List.map_congr_left fun i hi ↦ cellOfBytes_eq ?_
  rw [List.mem_range] at hi
  rw [List.length_drop]
  have := Nat.div_mul_le_self b.length 16
  have : 16 * (i + 1) ≤ b.length := by
    calc 16 * (i + 1) ≤ 16 * (b.length / 16) := Nat.mul_le_mul_left _ hi
      _ ≤ b.length := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  omega

theorem ordered_eq : Prover.Guest.ordered = Hints.ordered := by
  funext r a b
  simp only [Prover.Guest.ordered, Hints.ordered, cell128_eq]

/-! ## Coverage -/

theorem takeSlot_eq : @Prover.Guest.takeSlot = @Coverage.takeSlot := rfl

theorem takeSlots_eq : @Prover.Guest.takeSlots = @Coverage.takeSlots := by
  funext α _ d st l
  induction l generalizing st with
  | nil => rfl
  | cons c l ih => simp only [Prover.Guest.takeSlots, Coverage.takeSlots, takeSlot_eq, ih]

theorem takeSlotsAll_eq : @Prover.Guest.takeSlotsAll = @Coverage.takeSlotsAll := by
  funext α _ d st l
  induction l generalizing st with
  | nil => rfl
  | cons c l ih => simp only [Prover.Guest.takeSlotsAll, Coverage.takeSlotsAll, takeSlots_eq, ih]

theorem coveragePlan_eq {α : Type} [BEq α] (d r : List α) (c : List (List α)) :
    Prover.Guest.coveragePlan d r c = ⟨(Coverage.coveragePlan d r c).duplicates,
      (Coverage.coveragePlan d r c).directSlots, (Coverage.coveragePlan d r c).childSlots⟩ := by
  simp only [Prover.Guest.coveragePlan, Coverage.coveragePlan, takeSlots_eq, takeSlotsAll_eq]

/-! ## Signatures -/

theorem xmssLayer_eq : Prover.Guest.xmssLayer = Hints.xmssLayer := by
  funext p lay key m part
  simp only [Prover.Guest.xmssLayer, Hints.xmssLayer, cell128_eq]
  rfl

theorem xmssHints_eq : Prover.Guest.xmssHints = Hints.xmssHints := by
  funext pk m σ
  simp only [Prover.Guest.xmssHints, Hints.xmssHints, xmssLayer_eq]
  rfl

theorem sphincsForsNodes_eq : Prover.Guest.sphincsForsNodes = Hints.sphincsForsNodes := by
  funext p i t l o
  simp only [Prover.Guest.sphincsForsNodes, Hints.sphincsForsNodes, ordered_eq]

theorem sphincsLayer_eq : Prover.Guest.sphincsLayer = Hints.sphincsLayer := by
  funext p i σ lay d
  simp only [Prover.Guest.sphincsLayer, Hints.sphincsLayer, ordered_eq, cell128_eq]
  rfl

theorem sphincsHints_eq : Prover.Guest.sphincsHints = Hints.sphincsHints := by
  funext pk m σ
  simp only [Prover.Guest.sphincsHints, Hints.sphincsHints, sphincsLayer_eq, sphincsForsNodes_eq,
    cell128_eq]
  rfl

/-! ## Children -/

theorem recordQueries_eq : @Prover.Guest.recordQueries = @Hints.recordQueries := by
  funext α p
  induction p with
  | ret => rfl
  | fail => rfl
  | read k ih => simp only [Prover.Guest.recordQueries, Hints.recordQueries, ih]
  | sample k ih => simp only [Prover.Guest.recordQueries, Hints.recordQueries, ih]
  | grind b k ih => simp only [Prover.Guest.recordQueries, Hints.recordQueries, ih]
  | commit h w k ih => simp only [Prover.Guest.recordQueries, Hints.recordQueries, ih]
  | query i ps k ih => simp only [Prover.Guest.recordQueries, Hints.recordQueries, ih]

theorem childQueries_eq : Prover.Guest.childQueries = Hints.childQueries := by
  funext b seed c
  simp only [Prover.Guest.childQueries, Hints.childQueries, recordQueries_eq]
  rfl

theorem climbSteps_eq : Prover.Guest.climbSteps = Hints.climbSteps := by
  funext i n ss
  induction ss generalizing i n with
  | nil => rfl
  | cons s ss ih => simp only [Prover.Guest.climbSteps, Hints.climbSteps, ih]; rfl

theorem levelHints_eq : Prover.Guest.levelHints = Hints.levelHints := by
  funext f d c ph
  simp only [Prover.Guest.levelHints, Hints.levelHints, climbSteps_eq]
  rfl

theorem merkleHints_eq : Prover.Guest.merkleHints = Hints.merkleHints := by
  funext f qs phs
  induction qs generalizing f phs with
  | nil => cases phs <;> rfl
  | cons q qs ih =>
    cases phs with
    | nil => rfl
    | cons ph phs => simp only [Prover.Guest.merkleHints, Hints.merkleHints, levelHints_eq, ih]

theorem runHeads_eq : Prover.Guest.runHeads = Hints.runHeads := by
  funext l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp only [Prover.Guest.runHeads, Hints.runHeads, ← ih]

theorem runGroups_eq : Prover.Guest.runGroups = Hints.runGroups := by
  funext n p l
  induction l generalizing n p with
  | nil => rfl
  | cons k ks ih => simp only [Prover.Guest.runGroups, Hints.runGroups, ih]

theorem blockGroupOrder_eq : Prover.Guest.blockGroupOrder = Hints.blockGroupOrder := by
  funext L
  simp only [Prover.Guest.blockGroupOrder, Hints.blockGroupOrder, runGroups_eq, runHeads_eq]
  rfl

theorem colGroupOrder_eq : Prover.Guest.colGroupOrder = Hints.colGroupOrder := by
  funext L
  simp only [Prover.Guest.colGroupOrder, Hints.colGroupOrder, runGroups_eq, runHeads_eq]
  rfl

theorem childHints_eq : Prover.Guest.childHints = Hints.childHints := by
  funext b seed c
  simp only [Prover.Guest.childHints, Hints.childHints, merkleHints_eq, childQueries_eq,
    colGroupOrder_eq, blockGroupOrder_eq]
  rfl

/-! ## The node -/

theorem increasing_eq : Prover.Guest.increasing = Hints.increasing := by
  funext l
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simp only [Prover.Guest.increasing, Hints.increasing, ← ih]

theorem slotGaps_eq : Prover.Guest.slotGaps = Hints.slotGaps := by
  funext n l
  induction l generalizing n with
  | nil => rfl
  | cons o os ih => simp only [Prover.Guest.slotGaps, Hints.slotGaps, ih]

theorem childSlotPushes_eq : Prover.Guest.childSlotPushes = Hints.childSlotPushes := by
  funext l
  simp only [Prover.Guest.childSlotPushes, Hints.childSlotPushes, increasing_eq, slotGaps_eq]
  rfl

/-- **The statement's honest pushes are the proofs'.** -/
theorem honestPushes_eq (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    Prover.Guest.honestPushes bytecode seed s w = Hints.honestPushes bytecode seed s w := by
  simp only [Prover.Guest.honestPushes, Hints.honestPushes, coveragePlan_eq, cellsOfBytes_eq,
    xmssHints_eq, sphincsHints_eq, childSlotPushes_eq, childHints_eq]
  rfl

end

end LeanVM.Guest.ProverGuest
