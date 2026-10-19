/-
  LeanVM.Guest.B1.Tables.VerifyTablesVals

  `verify_tables`' straight-line values as expressions: the three bus totals, each table's
  `constraint_eval`, and the table sumcheck's target.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesBus

/-!
# The values by reflection

With `fp_w`'s loads the weights `χ` (`vt_fpw_sound`), and the pull side's loads the index values
and memory claims (`vt_pullTab_sound`), the kernel checks `vt_push_total`, `vt_pull_total`,
`vt_count_total` and `vt_ce0` .. `vt_ce5` give the values (`vt_vals`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

theorem vt_fpw_sound {rd : Reader} {σ : Val} {w : List E} (hw : 16 ≤ w.length)
    (h : ReadsAt rd (σ (.n 11)) w) : LoadTab.Sound rd σ (fun i => w.getD i 0) vtFpwTab := by
  intro q hq v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
  have hi' := List.mem_range.mp hi
  simp only [Ex.eval]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact loadHolds_unique hv (h i (by omega))

theorem vt_pullTab_sound {rd : Reader} {σ : Val} {w : List E} (hw : 16 ≤ w.length)
    (h : ReadsAt rd (σ (.n 11)) w) (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931)))
    (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)]) :
    LoadTab.Sound rd σ (fun i => w.getD i 0) pullLoadTab := by
  intro q hq v hv
  rcases List.mem_append.mp hq with hq | hq
  · exact vt_fpw_sound hw h q hq v hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [Ex.eval] at hv ⊢
    · exact loadHolds_unique hv h1
    · exact loadHolds_unique hv h2
    · exact loadHolds_unique hv (hm 0 (by simp))
    · exact loadHolds_unique hv (hm 1 (by simp))
    · exact loadHolds_unique hv (hm 2 (by simp))

/-- **The values**: the three bus totals and each table's `constraint_eval`, as expressions in the
valuation and the weights `χ`, and the sumcheck's target. -/
theorem vt_vals {rd : Reader} {σ : Val} (h : VtHolds rd σ) {w : List E} (hw : 16 ≤ w.length)
    (hfw : ReadsAt rd (σ (.n 11)) w) (h1 : LoadHolds rd (σ (.n 1852)) 1 (σ (.n 1931)))
    (h2 : LoadHolds rd (σ (.n 1852)) 2 (σ (.n 2035)))
    (hm : ReadsAt rd (σ (.n 13)) [σ (.n 1937), σ (.n 1955), σ (.n 1973)]) :
    σ (.n 3326) = pushTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 3705) = pullTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      σ (.n 4553) = countTotalEx.eval (fun k => σ (.n k)) (fun i => w.getD i 0) ∧
      (∀ t : Fin 6, σ (.n (vtCeVars.getD t 0)) =
        (ceEx t).eval (fun k => σ (.n k)) (fun i => w.getD i 0)) ∧
      σ (.n 4631) = σ (.n 4624) * σ (.n 3326) + σ (.n 4625) * σ (.n 3705) +
        σ (.n 4626) * σ (.n 4553) := by
  have hL := vt_fpw_sound hw hfw
  obtain ⟨kret, hb⟩ := h
  have hE : LoadTab.Sound rd σ (fun i => w.getD i 0) [] := fun _ hq => absurd hq (by simp)
  refine ⟨window_eval vtPre_noRet hb hL 1505 1587 3326 pushTotalEx vt_push_total,
    window_eval vtPre_noRet hb (vt_pullTab_sound hw hfw h1 h2 hm) 1505 1892 3705 pullTotalEx
      vt_pull_total,
    window_eval vtPre_noRet hb hE 3397 876 4553 countTotalEx vt_count_total, fun t => ?_, ?_⟩
  · fin_cases t
    · exact window_eval vtPre_noRet hb hL 4374 481 5140 (ceEx 0) vt_ce0
    · exact window_eval vtPre_noRet hb hL 4862 521 5668 (ceEx 1) vt_ce1
    · exact window_eval vtPre_noRet hb hL 5391 269 5945 (ceEx 2) vt_ce2
    · exact window_eval vtPre_noRet hb hL 5668 515 6468 (ceEx 3) vt_ce3
    · exact window_eval vtPre_noRet hb hL 6191 494 6970 (ceEx 4) vt_ce4
    · exact window_eval vtPre_noRet hb hL 6693 1153 8131 (ceEx 5) vt_ce5
  · have hv : VtHolds rd σ := ⟨kret, hb⟩
    have a0 := hv.atom 4333 (.mul (.n 4627) (.n 4624) (.n 3326)) (by decide +kernel)
    have a1 := hv.atom 4334 (.mul (.n 4628) (.n 4625) (.n 3705)) (by decide +kernel)
    have a2 := hv.atom 4335 (.add (.n 4629) (.n 4627) (.n 4628)) (by decide +kernel)
    have a3 := hv.atom 4336 (.mul (.n 4630) (.n 4626) (.n 4553)) (by decide +kernel)
    have a4 := hv.atom 4337 (.add (.n 4631) (.n 4629) (.n 4630)) (by decide +kernel)
    simp only [Atom.Holds] at a0 a1 a2 a3 a4
    rw [a4, a2, a0, a1, a3]

end
end LeanVM.Guest.B1.VerifySub
