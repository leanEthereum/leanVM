/-
  LeanVM.Protocol.Relation.Link.GroupLinksWeights

  The program side's slot weights (`tableSlotWeights`) and sums (`programSums`) in closed form.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksSummand

/-!
# The program side's weights in closed form

`tsw_closed`: slot `s` of table's `omega`, `pc` and `frame` weights is the opcode's challenge at
`s = 3`, each operand equation's first-slot challenge on its slots, and each access's reads of the
instruction (and its framed address) under `η_mem·μ` and `γ_word` (`γ_addr`). `programSums_closed`:
the program side's two sums over the tables and the slots `4 ..< 2^BYTECODE_SLOT_BITS`.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link Finset

@[expose] public section

theorem getD_addAtSlot (l : List E) (s i : ℕ) (c : E) :
    (addAtSlot l s c).getD i 0 = l.getD i 0 + if s = i ∧ i < l.length then c else 0 := by
  unfold addAtSlot
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_set]
    by_cases hs : s = i
    · subst hs; simp [hi]
    · simp [hs, hi]
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega)]
    simp [hi]

/-- A read's weight on slot `s` of `omega` (`Read::Slot`). -/
def lkSlotRead (s : ℕ) : Read → E
  | .slot s' scale => if s' = s then scale else 0
  | _ => 0

/-- A read's weight on slot `s` of `pc` (`Read::Pc`). -/
def lkPcRead (s : ℕ) : Read → E
  | .pc s' scale => if s' = s then scale else 0
  | _ => 0

/-- A read's weight on slot `s` of `frame` (`Read::Frame`). -/
def lkFrameRead (s : ℕ) : Read → E
  | .frame s' scale => if s' = s then scale else 0
  | _ => 0

/-- A framed address's weight on slot `s` of `frame`, `g^e`. -/
def lkFrameAddr (s : ℕ) (a : Access) : E :=
  match a.frame with
  | some (s', e) => if s' = s then gpow e else 0
  | none => 0

/-- One read of the instruction folded into the weights. -/
def lkRdStep (m g2 : E) (acc : List E × List E × List E) (read : Read) : List E × List E × List E :=
  match read with
  | .word _ _ => acc
  | .slot s scale => (addAtSlot acc.1 s (m * g2 * scale), acc.2.1, acc.2.2)
  | .frame s scale => (acc.1, acc.2.1, addAtSlot acc.2.2 s (m * g2 * scale))
  | .pc s scale => (acc.1, addAtSlot acc.2.1 s (m * g2 * scale), acc.2.2)

/-- One access folded into the weights. -/
def lkAccStep (gamma : E × E) (etaMem : E) (acc : List E × List E × List E) (x : Access × E) :
    List E × List E × List E :=
  let m := etaMem * x.2
  let frame := match x.1.frame with
    | some (s, e) => addAtSlot acc.2.2 s (m * gamma.1 * gpow e)
    | none => acc.2.2
  x.1.reads.foldl (lkRdStep m gamma.2) (acc.1, acc.2.1, frame)

/-- One operand equation folded into `omega`. -/
def lkOpStep (etaBc : E) (slot : List E) (omega : List E) (op : List ℕ × Form) : List E :=
  op.1.foldl (fun omega s ↦ addAtSlot omega s (etaBc * slot.getD (op.1.headD 0) 0)) omega

theorem tsw_eq (table : Table) (slot : List E) (gamma : E × E) (mu : List E) (etaMem etaBc : E) :
    tableSlotWeights table slot gamma mu etaMem etaBc =
      (table.links.memory.zip mu).foldl (lkAccStep gamma etaMem)
        (table.links.bytecodeLink.operands.foldl (lkOpStep etaBc slot)
          ((List.replicate (2 ^ bytecodeSlotBits) (0 : E)).set 3 (etaBc * slot.getD 3 0)),
          List.replicate (2 ^ bytecodeSlotBits) 0, List.replicate (2 ^ bytecodeSlotBits) 0) := rfl

theorem lk_rd_fold (m g2 : E) (i : ℕ) : ∀ (R : List Read) (acc : List E × List E × List E),
    i < acc.1.length → i < acc.2.1.length → i < acc.2.2.length →
    let r := R.foldl (lkRdStep m g2) acc
    r.1.getD i 0 = acc.1.getD i 0 + (R.map fun rd ↦ m * g2 * lkSlotRead i rd).sum ∧
    r.2.1.getD i 0 = acc.2.1.getD i 0 + (R.map fun rd ↦ m * g2 * lkPcRead i rd).sum ∧
    r.2.2.getD i 0 = acc.2.2.getD i 0 + (R.map fun rd ↦ m * g2 * lkFrameRead i rd).sum ∧
    r.1.length = acc.1.length ∧ r.2.1.length = acc.2.1.length ∧ r.2.2.length = acc.2.2.length
  | [], acc, _, _, _ => by simp
  | rd :: R, acc, h1, h2, h3 => by
    intro r
    have hr : r = R.foldl (lkRdStep m g2) (lkRdStep m g2 acc rd) := rfl
    cases rd with
    | word p scale =>
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := lk_rd_fold m g2 i R acc h1 h2 h3
      have hs : lkRdStep m g2 acc (.word p scale) = acc := rfl
      rw [hr, hs]
      refine ⟨?_, ?_, ?_, a4, a5, a6⟩
      · rw [a1, List.map_cons, List.sum_cons]; simp [lkSlotRead]
      · rw [a2, List.map_cons, List.sum_cons]; simp [lkPcRead]
      · rw [a3, List.map_cons, List.sum_cons]; simp [lkFrameRead]
    | slot s scale =>
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := lk_rd_fold m g2 i R (addAtSlot acc.1 s (m * g2 * scale), acc.2.1, acc.2.2)
        (by simpa [length_addAtSlot] using h1) h2 h3
      have hs : lkRdStep m g2 acc (.slot s scale) = (addAtSlot acc.1 s (m * g2 * scale), acc.2.1, acc.2.2) := rfl
      rw [hr, hs]
      refine ⟨?_, ?_, ?_, by rw [a4, length_addAtSlot], a5, a6⟩
      · rw [a1, getD_addAtSlot, List.map_cons, List.sum_cons]
        simp only [lkSlotRead, h1, and_true]
        split_ifs <;> ring
      · rw [a2, List.map_cons, List.sum_cons]; simp [lkPcRead]
      · rw [a3, List.map_cons, List.sum_cons]; simp [lkFrameRead]
    | frame s scale =>
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := lk_rd_fold m g2 i R (acc.1, acc.2.1, addAtSlot acc.2.2 s (m * g2 * scale))
        h1 h2 (by simpa [length_addAtSlot] using h3)
      have hs : lkRdStep m g2 acc (.frame s scale) = (acc.1, acc.2.1, addAtSlot acc.2.2 s (m * g2 * scale)) := rfl
      rw [hr, hs]
      refine ⟨?_, ?_, ?_, a4, a5, by rw [a6, length_addAtSlot]⟩
      · rw [a1, List.map_cons, List.sum_cons]; simp [lkSlotRead]
      · rw [a2, List.map_cons, List.sum_cons]; simp [lkPcRead]
      · rw [a3, getD_addAtSlot, List.map_cons, List.sum_cons]
        simp only [lkFrameRead, h3, and_true]
        split_ifs <;> ring
    | pc s scale =>
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := lk_rd_fold m g2 i R (acc.1, addAtSlot acc.2.1 s (m * g2 * scale), acc.2.2)
        h1 (by simpa [length_addAtSlot] using h2) h3
      have hs : lkRdStep m g2 acc (.pc s scale) = (acc.1, addAtSlot acc.2.1 s (m * g2 * scale), acc.2.2) := rfl
      rw [hr, hs]
      refine ⟨?_, ?_, ?_, a4, by rw [a5, length_addAtSlot], a6⟩
      · rw [a1, List.map_cons, List.sum_cons]; simp [lkSlotRead]
      · rw [a2, getD_addAtSlot, List.map_cons, List.sum_cons]
        simp only [lkPcRead, h2, and_true]
        split_ifs <;> ring
      · rw [a3, List.map_cons, List.sum_cons]; simp [lkFrameRead]

theorem lk_acc_fold (gamma : E × E) (etaMem : E) (i : ℕ) : ∀ (L : List (Access × E)) (acc : List E × List E × List E),
    i < acc.1.length → i < acc.2.1.length → i < acc.2.2.length →
    let r := L.foldl (lkAccStep gamma etaMem) acc
    r.1.getD i 0 = acc.1.getD i 0 +
      (L.map fun x ↦ (x.1.reads.map fun rd ↦ etaMem * x.2 * gamma.2 * lkSlotRead i rd).sum).sum ∧
    r.2.1.getD i 0 = acc.2.1.getD i 0 +
      (L.map fun x ↦ (x.1.reads.map fun rd ↦ etaMem * x.2 * gamma.2 * lkPcRead i rd).sum).sum ∧
    r.2.2.getD i 0 = acc.2.2.getD i 0 + (L.map fun x ↦ etaMem * x.2 * gamma.1 * lkFrameAddr i x.1 +
      (x.1.reads.map fun rd ↦ etaMem * x.2 * gamma.2 * lkFrameRead i rd).sum).sum ∧
    r.1.length = acc.1.length ∧ r.2.1.length = acc.2.1.length ∧ r.2.2.length = acc.2.2.length
  | [], acc, _, _, _ => by simp
  | x :: L, acc, h1, h2, h3 => by
    intro r
    set fr := match x.1.frame with
      | some (s, e) => addAtSlot acc.2.2 s (etaMem * x.2 * gamma.1 * gpow e)
      | none => acc.2.2 with hfr
    have hfr1 : fr.getD i 0 = acc.2.2.getD i 0 + etaMem * x.2 * gamma.1 * lkFrameAddr i x.1 ∧
        fr.length = acc.2.2.length := by
      rcases hx : x.1.frame with _ | ⟨s, e⟩
      · simp [hfr, hx, lkFrameAddr]
      · simp only [hfr, hx, lkFrameAddr]
        refine ⟨?_, length_addAtSlot _ _ _⟩
        rw [getD_addAtSlot]
        simp only [h3, and_true]
        split_ifs <;> ring
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := lk_rd_fold (etaMem * x.2) gamma.2 i x.1.reads (acc.1, acc.2.1, fr)
      h1 h2 (by rw [hfr1.2]; exact h3)
    have hstep : lkAccStep gamma etaMem acc x = x.1.reads.foldl (lkRdStep (etaMem * x.2) gamma.2)
        (acc.1, acc.2.1, fr) := rfl
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := lk_acc_fold gamma etaMem i L (lkAccStep gamma etaMem acc x)
      (by rw [hstep, b4]; exact h1) (by rw [hstep, b5]; exact h2) (by rw [hstep, b6, hfr1.2]; exact h3)
    have hr : r = L.foldl (lkAccStep gamma etaMem) (lkAccStep gamma etaMem acc x) := rfl
    rw [hr]
    refine ⟨?_, ?_, ?_, by rw [a4, hstep, b4], by rw [a5, hstep, b5], by rw [a6, hstep, b6, hfr1.2]⟩
    · rw [a1, hstep, b1, List.map_cons, List.sum_cons]; ring
    · rw [a2, hstep, b2, List.map_cons, List.sum_cons]; ring
    · rw [a3, hstep, b3, hfr1.1, List.map_cons, List.sum_cons]; ring

theorem lk_op_fold (etaBc : E) (slot : List E) (i : ℕ) : ∀ (L : List (List ℕ × Form)) (omega : List E),
    i < omega.length →
    (L.foldl (lkOpStep etaBc slot) omega).getD i 0 = omega.getD i 0 +
      (L.map fun op ↦ (op.1.map fun s ↦ if s = i then etaBc * slot.getD (op.1.headD 0) 0 else 0).sum).sum ∧
    (L.foldl (lkOpStep etaBc slot) omega).length = omega.length
  | [], omega, _ => by simp
  | op :: L, omega, hi => by
    have hin : ∀ (S : List ℕ) (w : List E), i < w.length →
        (S.foldl (fun omega s ↦ addAtSlot omega s (etaBc * slot.getD (op.1.headD 0) 0)) w).getD i 0 =
          w.getD i 0 + (S.map fun s ↦ if s = i then etaBc * slot.getD (op.1.headD 0) 0 else 0).sum ∧
        (S.foldl (fun omega s ↦ addAtSlot omega s (etaBc * slot.getD (op.1.headD 0) 0)) w).length =
          w.length := by
      intro S
      induction S with
      | nil => intro w _; simp
      | cons s S ih =>
        intro w hw
        rw [List.foldl_cons]
        obtain ⟨c1, c2⟩ := ih (addAtSlot w s (etaBc * slot.getD (op.1.headD 0) 0)) (by rw [length_addAtSlot]; exact hw)
        refine ⟨?_, by rw [c2, length_addAtSlot]⟩
        rw [c1, getD_addAtSlot, List.map_cons, List.sum_cons]
        simp only [hw, and_true]
        split_ifs <;> ring
    obtain ⟨c1, c2⟩ := hin op.1 omega hi
    obtain ⟨a1, a2⟩ := lk_op_fold etaBc slot i L (lkOpStep etaBc slot omega op) (by rw [lkOpStep, c2]; exact hi)
    rw [List.foldl_cons]
    refine ⟨?_, by rw [a2, lkOpStep, c2]⟩
    rw [a1, lkOpStep, c1, List.map_cons, List.sum_cons]
    ring

/-- **A table's slot weights in closed form**, slot `i < 2^BYTECODE_SLOT_BITS`. -/
theorem tsw_closed (table : Table) (slot : List E) (gamma : E × E) (mu : List E) (etaMem etaBc : E)
    {i : ℕ} (hi : i < 2 ^ bytecodeSlotBits) :
    let w := tableSlotWeights table slot gamma mu etaMem etaBc
    let L := table.links.memory.zip mu
    w.1.getD i 0 = (if i = 3 then etaBc * slot.getD 3 0 else 0) +
      (table.links.bytecodeLink.operands.map fun op ↦
        (op.1.map fun s ↦ if s = i then etaBc * slot.getD (op.1.headD 0) 0 else 0).sum).sum +
      (L.map fun x ↦ (x.1.reads.map fun rd ↦ etaMem * x.2 * gamma.2 * lkSlotRead i rd).sum).sum ∧
    w.2.1.getD i 0 = (L.map fun x ↦ (x.1.reads.map fun rd ↦ etaMem * x.2 * gamma.2 * lkPcRead i rd).sum).sum ∧
    w.2.2.getD i 0 = (L.map fun x ↦ etaMem * x.2 * gamma.1 * lkFrameAddr i x.1 +
      (x.1.reads.map fun rd ↦ etaMem * x.2 * gamma.2 * lkFrameRead i rd).sum).sum := by
  intro w L
  have hz : (List.replicate (2 ^ bytecodeSlotBits) (0 : E)).length = 2 ^ bytecodeSlotBits := by simp
  have hset : ((List.replicate (2 ^ bytecodeSlotBits) (0 : E)).set 3 (etaBc * slot.getD 3 0)).getD i 0 =
      if i = 3 then etaBc * slot.getD 3 0 else 0 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_set]
    split_ifs with h1 h2 h2 <;> first | rfl | omega | simp
  obtain ⟨o1, o2⟩ := lk_op_fold etaBc slot i table.links.bytecodeLink.operands
    ((List.replicate (2 ^ bytecodeSlotBits) (0 : E)).set 3 (etaBc * slot.getD 3 0)) (by simpa using hi)
  obtain ⟨a1, a2, a3, -, -, -⟩ := lk_acc_fold gamma etaMem i L
    (table.links.bytecodeLink.operands.foldl (lkOpStep etaBc slot)
      ((List.replicate (2 ^ bytecodeSlotBits) (0 : E)).set 3 (etaBc * slot.getD 3 0)),
      List.replicate (2 ^ bytecodeSlotBits) 0, List.replicate (2 ^ bytecodeSlotBits) 0)
    (by rw [o2]; simpa using hi) (by simpa using hi) (by simpa using hi)
  have hw : w = L.foldl (lkAccStep gamma etaMem)
      (table.links.bytecodeLink.operands.foldl (lkOpStep etaBc slot)
        ((List.replicate (2 ^ bytecodeSlotBits) (0 : E)).set 3 (etaBc * slot.getD 3 0)),
        List.replicate (2 ^ bytecodeSlotBits) 0, List.replicate (2 ^ bytecodeSlotBits) 0) := tsw_eq _ _ _ _ _ _
  rw [hw]
  refine ⟨?_, ?_, ?_⟩
  · rw [a1, o1, hset]
  · rw [a2]; simp
  · rw [a3]; simp

/-- Table `t`'s rows of `slot_weights`. -/
theorem slotWeights_getD (tables : List Table) (slot : List E) (gamma : E × E) (mu : List (List E))
    (etaMem etaBc : E) {t : ℕ} (ht : t < tables.length) :
    let w := slotWeights tables slot gamma mu etaMem etaBc
    let r := tableSlotWeights (tables.getD t default) slot gamma (mu.getD t []) etaMem etaBc
    w.omega.getD t [] = r.1 ∧ w.pc.getD t [] = r.2.1 ∧ w.frame.getD t [] = r.2.2 := by
  intro w r
  simp only [w, r, slotWeights]
  rw [zipIdx_eq_map]
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact ht)]
    simp only [List.getElem_map, List.getElem_range]

/-- Two sums folded at once. -/
theorem foldl_add_pair {α : Type} (f g : α → E) : ∀ (L : List α) (a b : E),
    L.foldl (fun (acc : E × E) x ↦ (acc.1 + f x, acc.2 + g x)) (a, b) =
      (a + (L.map f).sum, b + (L.map g).sum)
  | [], a, b => by simp
  | x :: L, a, b => by
    rw [List.foldl_cons, foldl_add_pair f g L]
    simp only [List.map_cons, List.sum_cons, Prod.mk.injEq]
    constructor <;> ring

/-- **The program side's sums in closed form**: over the tables, the opcode's weight times
`count`, and over the slots `4 ..< 2^BYTECODE_SLOT_BITS` the weights times the split's sums. -/
theorem programSums_closed (layout : Layout) (ch : LinkCh) (split : Split) :
    let weights := slotWeights layout.tables (eqKernel ch.alpha) (ch.gammaMem.getD 0 0, ch.gammaMem.getD 1 0)
      ch.mu ch.etaMem ch.etaBc
    programSums layout ch split =
      (∑ t ∈ range nTables, ((weights.omega.getD t []).getD 3 0 * gpow t * split.count.getD t 0 +
        ∑ s ∈ range (2 ^ bytecodeSlotBits - 4), ((weights.omega.getD t []).getD (s + 4) 0 *
          (split.slots.getD t []).getD (s + 4) 0 + (weights.pc.getD t []).getD (s + 4) 0 *
          (split.pc.getD t []).getD (s + 4) 0)),
       ∑ t ∈ range nTables, ∑ s ∈ range (2 ^ bytecodeSlotBits - 4),
        (weights.frame.getD t []).getD (s + 4) 0 * (split.slots.getD t []).getD (s + 4) 0) := by
  intro weights
  have key : ∀ n : ℕ, (List.range n).foldl (fun (acc : E × E) t ↦
      let omega := weights.omega.getD t []
      let pc := weights.pc.getD t []
      let frame := weights.frame.getD t []
      let slots := split.slots.getD t []
      let pcs := split.pc.getD t []
      let program := acc.1 + omega.getD 3 0 * gpow t * split.count.getD t 0
      ((List.range (2 ^ bytecodeSlotBits - 4)).map (· + 4)).foldl (fun (acc : E × E) s ↦
        (acc.1 + (omega.getD s 0 * slots.getD s 0 + pc.getD s 0 * pcs.getD s 0),
          acc.2 + frame.getD s 0 * slots.getD s 0)) (program, acc.2)) (0, 0) =
      (∑ t ∈ range n, ((weights.omega.getD t []).getD 3 0 * gpow t * split.count.getD t 0 +
        ∑ s ∈ range (2 ^ bytecodeSlotBits - 4), ((weights.omega.getD t []).getD (s + 4) 0 *
          (split.slots.getD t []).getD (s + 4) 0 + (weights.pc.getD t []).getD (s + 4) 0 *
          (split.pc.getD t []).getD (s + 4) 0)),
       ∑ t ∈ range n, ∑ s ∈ range (2 ^ bytecodeSlotBits - 4),
        (weights.frame.getD t []).getD (s + 4) 0 * (split.slots.getD t []).getD (s + 4) 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
      simp only
      rw [foldl_add_pair, sum_range_succ, sum_range_succ, List.map_map, List.map_map,
        list_sum_range_map, list_sum_range_map]
      simp only [Prod.mk.injEq, Function.comp_def]
      constructor
      · ring
      · trivial
  exact key nTables

end

end LeanVM.Protocol.Relation
