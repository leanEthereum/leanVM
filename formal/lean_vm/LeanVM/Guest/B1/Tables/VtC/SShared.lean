/-
  LeanVM.Guest.B1.Tables.VtC.SShared

  `idxc_tab`, `zeta1` and the six tables' shared selector tables hold on the honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.SBase
public import LeanVM.Guest.B1.Selectors.SharedTablesComplete

/-!
# The index factors, `1 + ζ` and the shared tables (G:2337-2355)

`vtIdxcW`: `idxc_tab`'s words `1 + g^(2^t)`; `idxc_ok`: its stores hold on a memory holding them.
`zeta1_ok`: `plus_one_run` on `g^μ` holds when `zeta1` holds `1 + ζ_k`. `sh_call`: a table's
`shared_selector_tables` call on a run of `μ - τ` coordinates, its nibble tables in place
(`RunTables`); the calls' statements are `SShT`'s.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `idxc_tab`'s words. -/
def vtIdxcW : List E := (List.range 34).map fun t ↦ 1 + gen ^ 2 ^ t

theorem vtIdxc_word {t : ℕ} (ht : t < 34) :
    word (tbGSquaresBits.getD t 0 ^^^ 1) 0 = 1 + gen ^ 2 ^ t := by
  rw [tb_word_eOfNat, eOfNat_xor, eOfNat_one, gen_pow_two_pow_eq ht, add_comm]

theorem vtIdxcT_length : vtIdxcT.length = 68 := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **`idxc_tab`'s stores.** -/
theorem idxc_ok (hl : args.length = 20) (h : TbReadsAt rd (vtσ rd w args (.n 664)) vtIdxcW) :
    ∀ st ∈ vtIdxcT, VSH (coreProgram.Rel rd) rd (vtσ rd w args) st := by
  intro st hst
  have hst' := hst
  simp only [vtIdxcT, List.mem_flatten, List.mem_map, List.mem_range] at hst'
  obtain ⟨_, ⟨t, ht, rfl⟩, hm⟩ := hst'
  have hc : vtσ rd w args (.n (665 + t)) = 1 + gen ^ 2 ^ t := by
    have := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (vtPre_drop 625 ▸ vtIdxc_check)
      (show Stmt.atom (.const (.n (665 + t)) (word (tbGSquaresBits.getD t 0 ^^^ 1) 0)) ∈
        vtIdxcT by
          simp only [vtIdxcT, List.mem_flatten, List.mem_map, List.mem_range]
          exact ⟨_, ⟨t, ht, rfl⟩, List.mem_cons_self⟩))
    simp only [fixNe, GoodS, Good] at this
    rw [this, vtIdxc_word ht]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · show _ = _
    rw [hc, vtIdxc_word ht]
  · show LoadHolds rd _ _ _
    rw [hc]
    have := h t (by simp [vtIdxcW]; exact ht)
    simpa [vtIdxcW] using this

/-- **`zeta1`'s `plus_one_run`.** -/
theorem zeta1_ok (hl : args.length = 20) {point : List E}
    (h9 : vtσ rd w args (.n 9) = gen ^ point.length) (hμ : point.length ≤ 33)
    (hz : TbReadsAt rd (vtσ rd w args (.n 8)) point)
    (hz1 : TbReadsAt rd (vtσ rd w args (.n 699)) (point.map (1 + ·))) (hw : w 700 = 0) :
    VSH (coreProgram.Rel rd) rd (vtσ rd w args)
      (.dispatch (.n 9) plusOneRunNames [.n 699, .n 8] [.n 700]) := by
  have hg := vt_goodS (rd := rd) (w := w) hl (vt_mem_slice (blk := [_]) (vtPre_drop 694 ▸ vtZeta1_check)
    List.mem_cons_self)
  simp only [fixNe, GoodS, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hg
  rw [vsh_dispatch]
  have hj : point.length < plusOneRunNames.length := by simp [plusOneRunNames]; omega
  refine ⟨point.length, hj, by rw [h9, gen_pow_eq_ofK], ?_⟩
  rw [← List.getD_eq_getElem _ ""]
  refine (plus_one_run_holds _ hμ rd _ _).mpr ?_
  simp only [List.map_cons, List.map_nil, MeaningPlusOneRun]
  exact ⟨⟨point, rfl, hz, hz1⟩, by rw [hg]; simp [hw]⟩

theorem sh_call {μ τ : ℕ} {point : List E} (hμ : point.length = μ) (hμ33 : μ < 33)
    (hτμ : τ ≤ μ) {eqt gt z z1 gsq : E}
    (hzv : TbReadsAt rd z (point.drop τ)) (hz1v : TbReadsAt rd z1 ((point.map (1 + ·)).drop τ))
    (hsqv : TbReadsAt rd gsq ((gSquaresList.drop τ).take (μ - τ)))
    (hrun : RunTables rd eqt gt (μ - τ) (point.drop τ) ((point.map (1 + ·)).drop τ)
      ((gSquaresList.drop τ).take (μ - τ))) :
    coreProgram.Rel rd "shared_selector_tables" [eqt, gt, z, z1, gsq, gen ^ (μ - τ)] [] := by
  have hsql : gSquaresList.length = 34 := by simp [gSquaresList]
  exact shared_selector_tables_complete_holds rd eqt gt z z1 gsq (μ - τ) _ _ _ (by omega)
    (by simp; omega) (by simp; omega) (by simp [hsql]; omega) hzv hz1v hsqv hrun

end
end LeanVM.Guest.B1.Tables
