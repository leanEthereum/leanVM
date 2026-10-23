/-
  LeanVM.Guest.B1.Tables.VtCEv

  `verify_tables`' completeness: a column evaluation, forward (`VtEvComplete`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesC0
public import LeanVM.Guest.B1.Tables.VerifyTablesCIface

/-!
# A column evaluation, forward (G:1748-1752)

`evT j` as items (`vtEvI`): the `fs_next` reading word `j` at the cursor, its copy, its store in
`claim_pool[5 + j]` and its table's `g^τ` in `claim_cplen_g[5 + j]`. `vt_ev_complete`:
`VtEvComplete`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

/-- Column evaluation `j`'s state value. -/
def evS (j : ℕ) : ℕ := if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13

/-- A column evaluation, as items. -/
def vtEvI (j v s τv : ℕ) : List FItem :=
  [.fs (.n s) (.n (s + 1)) (.n 4651) j v, .atom (.copy (.n (v + 15)) (.n v)),
    .atom (.load (.n v) (.n 13) (5 + j)), .atom (.load (.n τv) (.n 14) (5 + j))]

theorem vtEvI_stmts (j : ℕ) : (vtEvI j (evVal.getD j 0) (evS j) (evTau.getD j 0)).flatMap FItem.stmts = evT j := by
  simp [vtEvI, evT, evS, FItem.stmts]

set_option maxRecDepth 100000 in
theorem vtEv_ok : ∀ j < 104, fOkI (evVal.getD j 0) (evVal.getD j 0 + 16) []
    (vtEvI j (evVal.getD j 0) (evS j) (evTau.getD j 0)) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtEv_obsB : ∀ j < 104, listEqb iobEqb (iObs (evVal.getD j 0) [] (vtEvI j (evVal.getD j 0) (evS j) (evTau.getD j 0)))
    [.fs (.n (evS j)) (.n (evS j + 1)) (.n 4651) j,
      .ob (.holds (.load (.n (evVal.getD j 0)) (.n 13) (5 + j))),
      .ob (.holds (.load (.n (evTau.getD j 0)) (.n 14) (5 + j)))] = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vtEv_eqsB : ∀ j < 104,
    [FEq.item (.fs (.n (evS j)) (.n (evS j + 1)) (.n 4651) j (evVal.getD j 0)),
      .def (.copy (.n (evVal.getD j 0 + 15)) (.n (evVal.getD j 0)))].all (fun e =>
      (fEqs (evVal.getD j 0) [] (vtEvI j (evVal.getD j 0) (evS j) (evTau.getD j 0))).any (feqEqb e)) = true := by
  decide +kernel

theorem vtEv_lt : ∀ j < 104, evS j + 1 < evVal.getD j 0 ∧ evTau.getD j 0 < evVal.getD j 0 ∧
    4651 < evVal.getD j 0 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **A column evaluation completes** (G:1748-1752). -/
theorem vt_ev_complete : VtEvComplete := by
  intro j hj rd σ cur pool cplen w g cv h4651 h13 h14 hτ hcv hw hpool hcplen
  have hst := stmtsEqb_sound (ev_blocks j hj)
  have hok := vtEv_ok j hj
  have hobs := listEqb_sound iobEqb_sound (vtEv_obsB j hj)
  have heqs := vtEv_eqsB j hj
  obtain ⟨l1, l2, l3⟩ := vtEv_lt j hj
  rw [← hst, ← vtEvI_stmts]
  change (σ (.n (evS j)), σ (.n (evS j + 1))) = digestScalars cv at hcv
  generalize evVal.getD j 0 = v at *
  generalize evS j = s at *
  generalize evTau.getD j 0 = τv at *
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (fun _ => 0) (vtEvI j v s τv) hok σ
  generalize hσf : fRunI rd v (fun _ => 0) [] σ (vtEvI j v s τv) = σf at Cm
  have hf : ∀ u, fRunI rd v (fun _ => 0) [] σ (vtEvI j v s τv) u = σf u := fun u => by rw [hσf]
  have E := fRunI_eqs rd (fun _ => 0) σf (vtEvI j v s τv) [] σ hok hf
  have FR : ∀ n < v, σf (.n n) = σ (.n n) := fun n hn =>
    fRunI_eq_of_def rd _ hok hf (by simp [fDef, vNum, hn])
  have hB := heqs
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hB
  have dfs := E _ (mem_of_any feqEqb_sound hB.1)
  have dcp : σf (.n (v + 15)) = σf (.n v) := E _ (mem_of_any feqEqb_sound hB.2)
  have hdec : decodeCv (σf (.n s)) (σf (.n (s + 1))) = cv := by
    rw [FR s (by omega), FR (s + 1) (by omega)]
    exact digestScalars_injective ((decodeCv_spec ⟨cv, hcv⟩).symm.trans hcv)
  have e0 : σf (.n v) = w := by
    have := dfs 0 (by simp [FItem.sets]) (by simp [FItem.vals])
    simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range, List.getElem_cons_zero,
      Nat.add_zero] at this
    rw [this, FR 4651 (by omega), h4651, memAt_of_loadHolds hw]
  have ek : ∀ k < 14, σf (.n (v + (k + 1))) = fsVals w cv 1 k := fun k hk => by
    have := dfs (k + 1) (by simp [FItem.sets]; omega) (by simp [FItem.vals]; omega)
    simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range, List.getElem_cons_succ] at this
    rw [this, hdec, FR 4651 (by omega), h4651, memAt_of_loadHolds hw]
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [hobs]
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · simp only [IOb.Holds]
      rw [FR 4651 (by omega), h4651, FR s (by omega), FR (s + 1) (by omega)]
      exact ⟨hw.1, isSome_of_loadHolds hw, cv, hcv⟩
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [FR 13 (by omega), h13, e0]; exact hpool
    · simp only [IOb.Holds, Ob.Holds, Atom.Holds]
      rw [FR 14 (by omega), h14, FR τv (by omega), hτ]; exact hcplen
  · intro σ' h
    rw [h]
    refine ⟨e0, by rw [dcp, e0], ?_⟩
    rw [show v + 13 = v + (12 + 1) by ring, show v + 14 = v + (13 + 1) by ring, ek 12 (by omega),
      ek 13 (by omega)]
    rfl

end
end LeanVM.Guest.B1.VerifySub
