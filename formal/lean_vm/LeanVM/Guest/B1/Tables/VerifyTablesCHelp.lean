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

end
end LeanVM.Guest.B1.VerifySub
