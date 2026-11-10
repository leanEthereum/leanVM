import Rv64Verifier.Proofs.Walk.At14

/-!
# `walk`: R13's values, as `placementsRust` computes them

`plc_eq` unfolds `plc A k` over `blk 165` (`blocks`), `stacked` and the scattered offsets `ofl`;
`pf` is one column's placement.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Layout Rv64Verifier.Model.LayoutMirror

theorem outputs_eq : outputsRust = (113, 138) := by decide +kernel

theorem keepB_eq {c : Nat} (hc : c < 165) : ((qkeccakSlotRust c).isNone &&
    !decide (outputsRust.1 ≤ c ∧ c < outputsRust.2)) = keepB c := by
  rw [qkeccakSlotRust_spec, outputs_eq]
  interval_cases c <;> rfl

theorem zipIdx_map_eq {α : Type} (K : List Nat) (F : Nat × Nat → α) {n : Nat} (hl : K.length = n) :
    K.zipIdx.map F = (List.range n).map fun c ↦ F (K.getD c 0, c) := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range, Nat.zero_add]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]
  rfl

/-- `block_kappas`. -/
def bkl (K : List Nat) : List Nat := (blk 165).map fun c ↦ K.getD c 0

/-- `offsets`: the stacked offsets scattered over the `blocks`. -/
def ofl (K : List Nat) : List (BitVec 64) :=
  ((blk 165).zip (stackOffsetsRust (bkl K)).1).foldl (fun o co ↦ o.set co.1 co.2)
    (List.replicate 165 0#64)

/-- Column `c`'s placement. -/
def pf (K : List Nat) (c : Nat) : Option PlacementRust :=
  match slotOf c with
  | some slot => some ⟨K.getD c 0, (ofl K).getD 5 0 + (BitVec.ofNat 64 slot <<< (K.getD c 0 % 64))⟩
  | none => if 113 ≤ c ∧ c < 138 then none else some ⟨K.getD c 0, (ofl K).getD c 0⟩

theorem plc_eq (A : List E) (k : Nat) :
    (plc A k).1 = (List.range 165).map (pf (kapPre A k 6)) ∧
    (plc A k).2.1.index = (ofl (kapPre A k 6)).getD 5 0 ∧
    (plc A k).2.2 = max 15 (stackOffsetsRust (bkl (kapPre A k 6))).2 := by
  have hl : (kapPre A k 6).length = 165 := by rw [kapPre_length A k 6 (le_refl 6)]; decide
  have hb : (List.range (kapPre A k 6).length).filter (fun c ↦ (qkeccakSlotRust c).isNone &&
      !decide (outputsRust.1 ≤ c ∧ c < outputsRust.2)) = blk 165 := by
    rw [hl]; exact List.filter_congr fun c hc ↦ keepB_eq (List.mem_range.mp hc)
  simp only [plc, placementsRust, hb]
  refine ⟨?_, rfl, rfl⟩
  rw [zipIdx_map_eq _ _ hl]
  apply List.map_congr_left
  intro c hc
  simp only [qkeccakSlotRust_spec, outputs_eq, pf, decide_eq_true_eq, hl]
  rfl

theorem kapPre_mem_le {s : MachineState} {A : List E} {k : Nat} (h : HeadOk s A k) :
    ∀ i ≤ 6, ∀ x ∈ kapPre A k i, x ≤ 38
  | 0, _, x, hx => by
    have h1 := h.2.1.2
    have h2 := h.2.2.2.2
    have h3 : (hts A).getD 5 0 ≤ 32 := heightsLe h 5
    simp only [BitVec.le_def] at h1
    have e32 : (32#64).toNat = 32 := rfl
    simp only [busBitsRust] at h2
    simp only [kapPre, List.take_zero, List.foldl_nil, kap0, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  | i + 1, hi, x, hx => by
    have hl : i < tablesRust.length := lt_of_lt_of_le (Nat.lt_succ_self i) hi
    obtain ⟨t, ht⟩ : ∃ t, tablesRust[i]? = some t := ⟨_, List.getElem?_eq_getElem hl⟩
    rw [kapPre_succ A k ht, List.mem_append] at hx
    rcases hx with hx | hx
    · exact kapPre_mem_le h i (by omega) x hx
    · rw [List.eq_of_mem_replicate hx]; have : (hts A).getD i 0 ≤ 32 := heightsLe h i; omega

theorem kapPre_le {s : MachineState} {A : List E} {k : Nat} (h : HeadOk s A k) (j : Nat) :
    (kapPre A k 6).getD j 0 ≤ 38 := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : (kapPre A k 6)[j]? with
  | none => simp
  | some x => exact kapPre_mem_le h 6 (le_refl 6) x (List.mem_of_getElem? hx)

end Rv64Verifier.Proofs.Walk
