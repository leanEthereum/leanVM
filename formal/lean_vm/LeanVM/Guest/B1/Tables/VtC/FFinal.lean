/-
  LeanVM.Guest.B1.Tables.VtC.FFinal

  `Vt/AsmForms.lean`'s forms' values and `Vt/AsmFinal.lean`'s final check on the window `VtF`:
  `termsPure`'s terminal value over the six tables is the guest's `air_acc` (`σ 6921`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FForms0
public import LeanVM.Guest.B1.Tables.VtC.FForms1
public import LeanVM.Guest.B1.Tables.VtC.FForms2
public import LeanVM.Guest.B1.Tables.VtC.FForms3
public import LeanVM.Guest.B1.Tables.VtC.FForms4
public import LeanVM.Guest.B1.Tables.VtC.FForms5
public import LeanVM.Guest.B1.Tables.VtC.FAir
public import LeanVM.Guest.B1.Tables.Vt.AsmFinal

/-!
# The forms and the final check, on the window

What the soundness proof read outside the window becomes hypotheses: the push and count blocks'
selectors (`vt_sels`'s), the pull blocks' copies of the push ones (`VtPullSelsH`, `vtPullSels*`'s,
statements `1994 ..< 2070`), the tables' `g^τ` (`kappa_base`'s frame variables `σ (30 + t)`),
`zeta1` (`vt_zeta1`'s) and the batching challenge's powers (`vt_xi_pow`'s, statements
`2636 ..< 2641`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (accFold_spec accumulateSide_fst blockSel termsPure
  length_tableWeights jumpConstraints_eq refNConstraints)

@[expose] public section

/-- The pull blocks' selectors are their push twins' (`vtPullSels0 .. 5`). -/
def VtPullSelsH (σ : Val) : Prop :=
  ([σ (.n 1968), σ (.n 1970), σ (.n 1972), σ (.n 1974), σ (.n 1976)] = [σ (.n 960), σ (.n 965), σ (.n 970), σ (.n 975), σ (.n 980)]) ∧
  ([σ (.n 1978), σ (.n 1980), σ (.n 1982), σ (.n 1984), σ (.n 1986)] = [σ (.n 989), σ (.n 998), σ (.n 1007), σ (.n 1016), σ (.n 1025)]) ∧
  ([σ (.n 1988), σ (.n 1990), σ (.n 1992)] = [σ (.n 1034), σ (.n 1043), σ (.n 1052)]) ∧
  ([σ (.n 1994), σ (.n 1996), σ (.n 1998), σ (.n 2000), σ (.n 2002)] = [σ (.n 1061), σ (.n 1070), σ (.n 1079), σ (.n 1088), σ (.n 1097)]) ∧
  ([σ (.n 2004), σ (.n 2006), σ (.n 2008), σ (.n 2010), σ (.n 2012)] = [σ (.n 1106), σ (.n 1115), σ (.n 1124), σ (.n 1133), σ (.n 1142)]) ∧
  ([σ (.n 2014), σ (.n 2016), σ (.n 2018), σ (.n 2020), σ (.n 2022), σ (.n 2024), σ (.n 2026), σ (.n 2028), σ (.n 2030), σ (.n 2032), σ (.n 2034), σ (.n 2036), σ (.n 2038), σ (.n 2040), σ (.n 2042), σ (.n 2044), σ (.n 2046), σ (.n 2048), σ (.n 2050), σ (.n 2052), σ (.n 2054), σ (.n 2056), σ (.n 2058), σ (.n 2060), σ (.n 2062), σ (.n 2064), σ (.n 2066), σ (.n 2068)] = [σ (.n 1151), σ (.n 1160), σ (.n 1169), σ (.n 1178), σ (.n 1187), σ (.n 1196), σ (.n 1205), σ (.n 1214), σ (.n 1223), σ (.n 1232), σ (.n 1241), σ (.n 1250), σ (.n 1259), σ (.n 1268), σ (.n 1277), σ (.n 1286), σ (.n 1295), σ (.n 1304), σ (.n 1313), σ (.n 1322), σ (.n 1331), σ (.n 1340), σ (.n 1349), σ (.n 1358), σ (.n 1367), σ (.n 1376), σ (.n 1385), σ (.n 1394)])

/-- **The forms' values.** -/
theorem vt_forms_valF {rd : Reader} {σ : Val} (hF : VtF rd σ) (bc : List K)
    (hbc : bc.length = 2 ^ 23) {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ) {alphas : List E} (hal : alphas.length = 4)
    (hW : TbReadsAt rd (σ (.n 13)) (eqKernel alphas)) {t : ℕ} (ht : t < 6) :
    ((vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 14)) point
        [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
        (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1.getD t []).map
        (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hpull
  have hkl : (eqKernel alphas).length = 16 := by
    rw [show (16 : ℕ) = 2 ^ alphas.length by rw [hal]; rfl]
    exact vt_length_eqKernel alphas
  have hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i ((eqKernel alphas).getD i 0) :=
    fun i hi ↦ by
      have := hW i (by omega)
      rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e0, e1, e2⟩ := vt_forms hbc alphas (σ (.n 14)) point
    [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
    (σ (.n 25)) (σ (.n 26)) (σ (.n 27)) (fun c ↦ σ (.n c)) hP hC hr ⟨t, ht⟩ ((vtEvT σ t).getD · 0)
  simp only at e0 e1 e2
  rw [vt_three _ ((vt_forms3_shape bc lm hr _ _ _ _ _ _ _ _ _ _).2 t ht) {}]
  simp only [List.map_cons, List.map_nil, e0, e1, e2]
  have hev : ∀ c < vtW6.getD t 0, σ (.n (vtEvB (vtB6.getD t 0 + c))) = (vtEvT σ t).getD c 0 :=
    fun c hc ↦ (vt_evT_getD σ t c hc).symm
  interval_cases t
  · simp only [vtFV, List.getD_cons_zero, List.map_cons, List.map_nil]
    rw [vtSide00F hF hw hev, vtSide10F hF q0 hw hev, q0, vtSide20F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide01F hF hw hev, vtSide11F hF q1 hw hev, q1, vtSide21F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide02F hF hw hev, vtSide12F hF q2 hw hev, q2, vtSide22F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide03F hF hw hev, vtSide13F hF q3 hw hev, q3, vtSide23F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide04F hF hw hev, vtSide14F hF q4 hw hev, q4, vtSide24F hF hev]
    rfl
  · simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil]
    rw [vtSide05F hF hw hev, vtSide15F hF q5 hw hev, q5, vtSide25F hF hev]
    rfl

/-- **The final check**: `termsPure`'s terminal value over the six tables is the guest's
`air_acc`. -/
theorem vt_asm_finalF {rd : Reader} {σ : Val} (hV : VtF rd σ) (bc : List K)
    (hbc : bc.length = 2 ^ 23) {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hkbt : ∀ t < 6, σ (.n (30 + t)) = gen ^ vtHt rows t)
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ)
    (hz1 : TbReadsAt rd (σ (.n 703)) (point.map (1 + ·)))
    (hxi : σ (.n 2589) = 1 ∧ σ (.n 2590) = σ (.n 2588) ∧ σ (.n 2591) = σ (.n 2588) ^ 2 ∧
      σ (.n 2592) = σ (.n 2588) ^ 3 ∧ σ (.n 2593) = σ (.n 2588) ^ 4)
    {alphas : List E} (hal : alphas.length = 4)
    (hW : TbReadsAt rd (σ (.n 13)) (eqKernel alphas)) {n : ℕ}
    (hgn : σ (.n 2516) = gen ^ n) (hhn : ∀ t < 6, vtHt rows t ≤ n) (hnp : n ≤ point.length)
    {pts : List E} (hpl : pts.length = n)
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 2608)) j (pts.take j).prod)
    (hpe : EqPrefix rd (σ (.n 2629)) 1 (σ (.n 16)) (σ (.n 703)) n)
    (hchi : ∀ i < n, LoadHolds rd (σ (.n 16)) (n - 1 - i) (pts.getD i 0)) :
    (termsPure ((powers (σ (.n 2588)) 5).take 2) ((powers (σ (.n 2588)) 5).drop 2) pts.reverse
      (List.zip (vtRows (tableHeightsOf rows)
        (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 14)) point
          [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
          (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1 point pts) (vtEvsT σ)) 0 0 []).1 =
      σ (.n 6921) := by
  set F := (vtAcc2 (layoutOf bc lm rows) alphas (σ (.n 14)) point
    [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
    (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1 with hF
  have hFv : ∀ t < 6, (F.getD t []).map (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := fun t ht ↦
    vt_forms_valF hV bc hbc hr hP hC hpull hal hW ht
  have hF6 := (vt_forms3_shape bc lm hr alphas (σ (.n 14)) point
    [σ (.n 830), σ (.n 843), σ (.n 856)] (σ (.n 1843)) (σ (.n 1898)) (σ (.n 581))
    (σ (.n 25)) (σ (.n 26)) (σ (.n 27))).1
  have hH6 : (tableHeightsOf rows).length = 6 := vt_tableHeightsOf_length hr
  set Wt := tableWeights (tableHeightsOf rows) point pts.reverse with hWt
  have hW6 : Wt.length = 6 := by rw [hWt, length_tableWeights, hH6]
  -- the weights
  have hwt : ∀ t < 6, ∀ {x cp pe : E}, σ (.n 2516) = x * σ (.n (30 + t)) →
      LoadHolds rd (σ (.n 2608) * x) 0 cp →
      LoadHolds rd (σ (.n 2629) * σ (.n (30 + t))) 0 pe → Wt.getD t 0 = cp * pe := by
    intro t ht x cp pe hx hcpL hpeL
    exact vt_weight_guest hpl hnp hcp hpe hchi hz1 hgn (by rw [hH6]; exact ht) (hhn t ht) hx
      (hkbt t ht) hcpL hpeL
  obtain ⟨x0, c0, p0, v0⟩ := vtAir0F hV
  obtain ⟨x1, c1, p1, v1⟩ := vtAir1F hV
  obtain ⟨x2, c2, p2, v2⟩ := vtAir2F hV
  obtain ⟨x3, c3, p3, v3⟩ := vtAir3F hV
  have hev4 : ∀ c < 14, σ (.n (vtEvB (53 + c))) = (vtEvT σ 4).getD c 0 :=
    fun c hc ↦ (vt_evT_getD σ 4 c hc).symm
  obtain ⟨x4, c4, p4, v4⟩ := vtAir4F hV hev4
  obtain ⟨x5, c5, p5, v5⟩ := vtAir5F hV
  have w0 := hwt 0 (by norm_num) x0 c0 p0
  have w1 := hwt 1 (by norm_num) x1 c1 p1
  have w2 := hwt 2 (by norm_num) x2 c2 p2
  have w3 := hwt 3 (by norm_num) x3 c3 p3
  have w4 := hwt 4 (by norm_num) x4 c4 p4
  have w5 := hwt 5 (by norm_num) x5 c5 p5
  have f0 := hFv 0 (by norm_num)
  have f1 := hFv 1 (by norm_num)
  have f2 := hFv 2 (by norm_num)
  have f3 := hFv 3 (by norm_num)
  have f4 := hFv 4 (by norm_num)
  have f5 := hFv 5 (by norm_num)
  simp only [vtFV, List.getD_cons_zero, List.getD_cons_succ, List.map_cons,
    List.map_nil] at f0 f1 f2 f3 f4 f5
  obtain ⟨n0, n1, n2, n3, n4, n5⟩ := vt_nConstraints_each
  obtain ⟨xp0, xp1, xp2, xp3, xp4⟩ := hxi
  rw [vtRows, ← hWt, vt_six Wt hW6 0, vt_tables_six, vt_six (tableHeightsOf rows) hH6 0,
    vt_six F hF6 [], vtEvsT]
  simp only [List.zip_cons_cons, List.zip_nil_left, termsPure, f0, f1, f2, f3, f4, f5,
    w0, w1, w2, w3, w4, w5, n0, n1, n2, n3, n4, n5, (vt_constraints _).1, (vt_constraints _).2.1,
    (vt_constraints _).2.2.1, (vt_constraints _).2.2.2.1, (vt_constraints _).2.2.2.2.1,
    (vt_constraints _).2.2.2.2.2, jumpConstraints_eq]
  rw [vt_air_totalF hV, v0, v1, v2, v3, v4, v5, xp0, xp1, xp2, xp3, xp4, tb_word_one]
  simp only [powers, powersFrom, dot, List.take, List.drop, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.foldl_cons, List.foldl_nil]
  ring

end
end LeanVM.Guest.B1.Tables
