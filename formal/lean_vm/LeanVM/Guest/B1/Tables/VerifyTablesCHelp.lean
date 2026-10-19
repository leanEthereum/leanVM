/-
  LeanVM.Guest.B1.Tables.VerifyTablesCHelp

  `verify_tables`' completeness: the facts the assembly reads off the layout and the run.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCMem
public import LeanVM.Guest.B1.Tables.VerifyTablesCSem

/-!
# Layout and run facts

`vt_consH`: `vt_cons` handing the continuation the first window's statements holding.
`vt_sel_push`, `vt_sel_count`: the bus layout's placements are the selectors' (`vtKs`, `selOff`).
`vt_forms_shaped`: `busVal`'s forms are shaped. `flatten_shape_eq`: lists of lists of one shape
are equal when their flattenings are.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- **Two windows in sequence**, the first's facts kept and its statements holding for the second. -/
theorem vt_consH {C : CallRel} {rd : Reader} {a l1 l2 lo mid hi : ℕ} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) (hnb : NumBelow mid (Stmt.valsList ((vtPre.drop a).take l1)))
    (h1 : Completes C rd lo mid ((vtPre.drop a).take l1) σ P)
    (hP : ∀ σ1 σ2 : Val, (∀ k < mid, σ2 (.n k) = σ1 (.n k)) → P σ1 → P σ2)
    (h2 : ∀ σ', Ext lo mid σ σ' → P σ' → (∀ (next : Prop) (kret : List E → Prop), next →
      Stmt.HoldsList C rd σ' ((vtPre.drop a).take l1) next kret) →
      Completes C rd mid hi ((vtPre.drop (a + l1)).take l2) σ' Q) :
    Completes C rd lo hi ((vtPre.drop a).take (l1 + l2)) σ (fun σ'' => P σ'' ∧ Q σ'') := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  have h1' : Completes C rd lo mid ((vtPre.drop a).take l1) σ (fun σ' => P σ' ∧
      ∀ (next : Prop) (kret : List E → Prop), next →
        Stmt.HoldsList C rd σ' ((vtPre.drop a).take l1) next kret) := ⟨σ1, he1, ⟨hp1, hh1⟩, hh1⟩
  refine (vt_cons hlo hhi hnb h1' (fun σ1 σ2 hag hp => ⟨hP σ1 σ2 hag hp.1, fun next kret hn =>
    (holdsList_frame hnb (fun k hk => (hag k hk).symm) next kret).mp (hp.2 next kret hn)⟩)
    fun σ' he hp => h2 σ' he hp.1 hp.2).mono le_rfl le_rfl fun σ'' h => ⟨h.1.1, h.2⟩

/-- Lists of lists of one shape are equal when their flattenings are. -/
theorem flatten_shape_eq {α : Type} : ∀ (a b : List (List α)), a.map List.length = b.map List.length →
    a.flatten = b.flatten → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hs, hf => by
    simp only [List.map_cons, List.cons.injEq] at hs
    simp only [List.flatten_cons] at hf
    obtain ⟨h1, h2⟩ := List.append_inj hf hs.1
    rw [h1, flatten_shape_eq xs ys hs.2 h2]
  | [], _ :: _, hs, _ => by simp at hs
  | _ :: _, [], hs, _ => by simp at hs

section
variable {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (logMem : ℕ) {rowsN : List ℕ}
  (hrl : rowsN.length = 6)
include hb hrl

/-- The push side's placements are the selectors'. -/
theorem vt_sel_push {i : ℕ} (hi : i < 37) :
    ((busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).framework ++
      (busLayout [0, logMem, 18] (layoutOf bytecode logMem rowsN).push).tables).getD i default =
      ({ vars := vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (selBlk.getD i 0), index := selOff (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) i } : Placement) := by
  obtain ⟨-, -, hpo, -, hpl, -⟩ := layoutOf_blocks bytecode hb logMem rowsN hrl
  have hpl34 : (layoutOf bytecode logMem rowsN).push.length = 34 := by
    have := congrArg List.length hpo; simp only [List.length_map] at this; rw [this]; rfl
  have hszP : [0, logMem, 18] ++ (layoutOf bytecode logMem rowsN).push.map (·.logRows) =
      (List.range 37).map (vtKs logMem fun t => log2Ceil (rowsN.getD t 0)) := by
    rw [vtKs_push, hpl]
  rw [busLayout_all_getD _ _ (by simp only [List.length_cons, List.length_nil, hpl34]; omega), hszP,
    selBlk_facts.1 i hi]
  simp only [selOff, hi, ↓reduceIte, pushOff]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

/-- The count side's placements are the selectors'. -/
theorem vt_sel_count {j : ℕ} (hj : j < 28) :
    (busLayout [] (layoutOf bytecode logMem rowsN).count).tables.getD j default =
      ({ vars := vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (selBlk.getD (37 + j) 0), index := selOff (vtKs logMem (fun t => log2Ceil (rowsN.getD t 0))) (37 + j) } : Placement) := by
  obtain ⟨-, -, -, hco, -, -, hcl, -⟩ := layoutOf_blocks bytecode hb logMem rowsN hrl
  have hcl28 : (layoutOf bytecode logMem rowsN).count.length = 28 := by
    have := congrArg List.length hco; simp only [List.length_map] at this; rw [this]; rfl
  have hszC : (layoutOf bytecode logMem rowsN).count.map (·.logRows) =
      (List.range 28).map (fun i => vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) (74 + i)) := by
    rw [vtKs_count, hcl]
  rw [busLayout_tables_getD _ (by omega), hszC, selBlk_facts.2 j hj]
  simp only [selOff, show ¬ 37 + j < 37 by omega, ↓reduceIte, countOff, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map, List.getElem_range]

end

/-- `busVal`'s forms are shaped. -/
theorem vt_forms_shaped {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (logMem : ℕ) {rows : List ℕ}
    (hr : rows.length = 6) (alphas : List E) (beta : E) (point tv memory : List E) (mF bF bv : E) :
    FormsShaped (busVal (layoutOf bytecode logMem rows) alphas beta point tv memory mF bF bv).forms := by
  obtain ⟨hlb, -, hpo, hco, -, -, -, -, -, -, -, hpp⟩ := layoutOf_blocks bytecode hb logMem rows hr
  set L := layoutOf bytecode logMem rows with hLd
  have hlm : L.logMemory = logMem := rfl
  have hlo : L.pull.map (·.owner) = layoutPushOwners := by
    have := congrArg (List.map fun x : ℕ × ℕ × ℕ => x.1) hpp
    simp only [List.map_map] at this; rw [← hpo]; exact this
  have po6 : ∀ b ∈ L.push, b.owner < 6 := fun b hb => by
    have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hpo] at this
    exact vt_owners_lt.1 _ this
  have lo6 : ∀ b ∈ L.pull, b.owner < 6 := fun b hb => by
    have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hlo] at this
    exact vt_owners_lt.1 _ this
  have co6 : ∀ b ∈ L.count, b.owner < 6 := fun b hb => by
    have := List.mem_map_of_mem (f := (·.owner)) hb; rw [hco] at this
    exact vt_owners_lt.2 _ this
  simp only [busVal_eq, hlb, hlm]
  refine (accSide_forms (side := 2) (by omega) 0 0 (fun _ => 0) ?_ co6 _ _ _ _ _ _).2
  refine (accSide_forms (side := 1) (by omega) 0 0 (fun _ => 0) ?_ lo6 _ _ _ _ _ _).2
  exact (accSide_forms (side := 0) (by omega) 0 0 (fun _ => 0) forms0_shaped po6 _ _ _ _ _ _).2

/-- An entry of a run of constant blocks. -/
theorem flatMap_replicate_getElem? {α : Type} (f : ℕ → α) (cnt : ℕ → ℕ) :
    ∀ (m t j : ℕ), t < m → j < cnt t →
      ((List.range m).flatMap fun s => List.replicate (cnt s) (f s))[(∑ s ∈ Finset.range t, cnt s) + j]? =
        some (f t)
  | 0, _, _, ht, _ => absurd ht (Nat.not_lt_zero _)
  | m + 1, t, j, ht, hj => by
    have hl : ((List.range m).flatMap fun s => List.replicate (cnt s) (f s)).length =
        ∑ s ∈ Finset.range m, cnt s := by
      clear ht hj
      induction m with
      | zero => simp
      | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih, Finset.sum_range_succ]; simp
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h | rfl
    · have hle : (∑ s ∈ Finset.range t, cnt s) + j < ∑ s ∈ Finset.range m, cnt s := by
        have := Finset.sum_le_sum_of_subset (f := cnt) (Finset.range_mono (show t + 1 ≤ m by omega))
        rw [Finset.sum_range_succ] at this; omega
      rw [List.getElem?_append_left (by rw [hl]; exact hle)]
      exact flatMap_replicate_getElem? f cnt m t j h hj
    · rw [List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left,
        List.getElem?_replicate]
      simp [hj]

theorem evFirst_sum : ∀ t < 6, evFirst.getD t 0 = ∑ s ∈ Finset.range t, evCnt.getD s 0 := by decide

theorem vtEvalVars_lengths : vtEvalVars.map List.length = (List.range 6).map fun t => evCnt.getD t 0 := by
  decide

/-- **The tables' claims' values and points**, from the evaluations' shape. -/
theorem vt_claimsT {bytecode : List K} (hb : bytecode.length = 2 ^ 22) (logMem : ℕ) {rowsN : List ℕ}
    (hrl : rowsN.length = 6) (alphas : List E) (beta : E) (point tv memory : List E) (mF bF bv : E)
    (chis : List E) {evss : List (List E)}
    (hshape : evss.map List.length = vtEvalVars.map List.length) :
    ((List.zip (vtRows (layoutOf bytecode logMem rowsN)
        (busVal (layoutOf bytecode logMem rowsN) alphas beta point tv memory mF bF bv) chis) evss).flatMap
        (rowClaims chis)).map (·.value) = evss.flatten ∧
    ((List.zip (vtRows (layoutOf bytecode logMem rowsN)
        (busVal (layoutOf bytecode logMem rowsN) alphas beta point tv memory mF bF bv) chis) evss).flatMap
        (rowClaims chis)).map (·.point) =
      (List.range 6).flatMap fun t => List.replicate (evCnt.getD t 0) (chis.take (log2Ceil (rowsN.getD t 0))) := by
  have hel6 : evss.length = 6 := by have := congrArg List.length hshape; simpa [vt_evalVars_length] using this
  set L := layoutOf bytecode logMem rowsN with hL
  set bus := busVal L alphas beta point tv memory mF bF bv with hbus
  have hfl : bus.forms.length = 6 := (vt_forms_shaped hb logMem hrl alphas beta point tv memory mF bF bv).1
  have hh : L.tableLogHeights = rowsN.map log2Ceil := rfl
  set X := List.zip L.tableLogHeights (List.zip bus.forms (tableWeights L.tableLogHeights bus.point chis)) with hX
  have hXl : X.length = 6 := by simp [hX, hh, hrl, hfl, tableWeights_length]
  have hrows : vtRows L bus chis = List.zip tables X := rfl
  have hrl6 : (vtRows L bus chis).length = 6 := by rw [hrows]; simp [hXl, tables_length']
  constructor
  · rw [List.map_flatMap]
    simp only [rowClaims_value]
    rw [List.flatMap_def, List.map_snd_zip (by rw [hrl6, hel6])]
  · rw [List.map_flatMap]
    simp only [rowClaims_point]
    rw [hrows, vt_rows_flatMap X hXl evss hel6]
    refine List.flatMap_congr fun t ht => ?_
    have ht' := List.mem_range.mp ht
    have e1 : (evss.getD t []).length = evCnt.getD t 0 := by
      have h := congrArg (fun l => l.getD t 0) (hshape.trans vtEvalVars_lengths)
      have h1 : (evss.map List.length).getD t 0 = (evss.getD t []).length := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map,
          List.getD_eq_getElem _ _ (by omega)]
      have h2 : ((List.range 6).map fun t => evCnt.getD t 0).getD t 0 = evCnt.getD t 0 := by
        rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega), List.getElem_map,
          List.getElem_range]
      exact h1.symm.trans (h.trans h2)
    have e2 : (X.getD t default).1 = log2Ceil (rowsN.getD t 0) := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp only [hX, List.getElem_zip, hh, List.getElem_map]
      rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [e1, e2]

end
end LeanVM.Guest.B1.VerifySub
