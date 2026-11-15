/-
  LeanVM.Guest.B1.Tables.VtC.FComplete

  `verify_tables`' table evaluations, forms, air terms and final check (statements
  `2690 ..< 5530`) complete: on the honest memory, every one holds of the honest valuation.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FWin
public import LeanVM.Guest.B1.Tables.VtC.FFinal

/-!
# The table phase's evaluations and final check, complete (G:2594-2675)

`vtF_complete`: the window (`vtF_window`) and the final check `assert air_acc == claim`, which
holds since `air_acc` (`σ 5947`) is `termsPure`'s terminal value over the six tables
(`vt_asm_finalF`) and the table sumcheck's final claim `σ 2648` is it (`hfin`, the
specification's check of the honest run). It also gives what follows: the evaluations' values,
the sponge after them (`vt_evals_fsF`), and `VtF`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (blockSel termsPure)

@[expose] public section

theorem vtF_split : tbStmtsEqb ((vtPre.drop vtFLo).take (5530 - vtFLo))
    ((vtPre.drop vtFLo).take (vtFHi - vtFLo) ++ [.atom (.assertEq (.n 5952) (.n 2653))]) =
      true := by
  simp only [vtPre_drop]; decide +kernel

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **Statements `2690 ..< 5530` complete**, and what they leave: `VtF`, the evaluations' values
and the sponge after them. -/
theorem vtF_complete (hl : args.length = 21) (bc : List K) (hbc : bc.length = 2 ^ 23)
    {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hkbt : ∀ t < 6, vtσ rd w args (.n (28 + t)) = gen ^ vtHt rows t)
    (hP : ∀ i < 51, vtσ rd w args (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, vtσ rd w args (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH (vtσ rd w args))
    (hz1 : TbReadsAt rd (vtσ rd w args (.n 700)) (point.map (1 + ·)))
    (hxi : vtσ rd w args (.n 2612) = 1 ∧ vtσ rd w args (.n 2613) = vtσ rd w args (.n 2611) ∧
      vtσ rd w args (.n 2614) = vtσ rd w args (.n 2611) ^ 2 ∧
      vtσ rd w args (.n 2615) = vtσ rd w args (.n 2611) ^ 3 ∧
      vtσ rd w args (.n 2616) = vtσ rd w args (.n 2611) ^ 4)
    {weights : List E} (hwl : weights.length = 16)
    (hW : TbReadsAt rd (vtσ rd w args (.n 13)) weights) {n : ℕ}
    (hgn : vtσ rd w args (.n 2545) = gen ^ n) (hhn : ∀ t < 6, vtHt rows t ≤ n)
    (hnp : n ≤ point.length) {pts : List E} (hpl : pts.length = n)
    (hcp : ∀ j ≤ n, LoadHolds rd (vtσ rd w args (.n 2631)) j (pts.take j).prod)
    (hpe : EqPrefix rd (vtσ rd w args (.n 2656)) 1 (vtσ rd w args (.n 16))
      (vtσ rd w args (.n 700)) n)
    (hchi : ∀ i < n, LoadHolds rd (vtσ rd w args (.n 16)) (n - 1 - i) (pts.getD i 0))
    {evs : List E} (hevl : evs.length = 153)
    (hcur : TbReadsAt rd (vtσ rd w args (.n 2652)) evs)
    (hfin : (termsPure ((powers (vtσ rd w args (.n 2611)) 5).take 2)
      ((powers (vtσ rd w args (.n 2611)) 5).drop 2) pts.reverse
      (List.zip (vtRows (tableHeightsOf rows)
        (vtAcc2 (layoutOf bc lm rows) weights (vtσ rd w args (.n 14)) point
          [vtσ rd w args (.n 813), vtσ rd w args (.n 817)]
          (vtσ rd w args (.n 1303)) (vtσ rd w args (.n 1317)) (vtσ rd w args (.n 1841))
          (vtσ rd w args (.n 2442)) (vtσ rd w args (.n 2488)) (vtσ rd w args (.n 2543))).1
            point pts) (vtEvsT (vtσ rd w args))) 0 0 []).1 = vtσ rd w args (.n 2653)) :
    (∀ s ∈ (vtPre.drop 2690).take (5530 - 2690),
        VSH (coreProgram.Rel rd) rd (vtσ rd w args) s) ∧
      VtF rd (vtσ rd w args) ∧ vtEvs (vtσ rd w args) = evs ∧
      (∀ j < 38, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
          ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
        ⟨vtCapV (vtσ rd w args) j,
          (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
        vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
          (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) ∧
      vtσ rd w args (.n 5952) = vtσ rd w args (.n 2653) := by
  obtain ⟨as, bs, -, -, -, -, hpre⟩ := id hpe
  have hwin := vtF_window (w := w) hl (by omega) hcur hW (by omega) hkbt hgn hhn hcp
    (pe := prefixProd 1 as bs) (fun j hj ↦ hpre j hj)
  have hV := vtF_of_vsh hwin
  have hfinG := vt_asm_finalF hV bc hbc hr hkbt hP hC hpull hz1 hxi hwl hW hgn hhn hnp hpl hcp
    hpe hchi
  have e6817 : vtσ rd w args (.n 5952) = vtσ rd w args (.n 2653) := hfinG.symm.trans hfin
  refine ⟨?_, hV, ?_, vt_evals_fsF hV, e6817⟩
  · rw [tbStmtsEqb_sound vtF_split]
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hwin s hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      show vtσ rd w args (.n 5952) + vtσ rd w args (.n 2653) = 0
      rw [e6817]
      exact CharTwo.add_self_eq_zero _
  · apply List.ext_getElem (by rw [vtEvs_length, hevl])
    intro k h1 _
    have hk : k < 153 := by simpa [vtEvs] using h1
    rw [← List.getD_eq_getElem _ 0 h1, vtEvs_getD _ hk,
      (vtF_evRead (w := w) hl hcur (by omega) hk).2, List.getD_eq_getElem _ _ (by omega)]

end

end
end LeanVM.Guest.B1.Tables
