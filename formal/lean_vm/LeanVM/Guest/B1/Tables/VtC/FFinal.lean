/-
  LeanVM.Guest.B1.Tables.VtC.FFinal

  `Vt/AsmForms.lean`'s forms' values and `Vt/AsmFinal.lean`'s final check on the window `VtF`:
  `termsPure`'s terminal value over the six tables is the guest's `air_acc` (`σ 5947`).
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
selectors (`vt_sels`'s), the pull blocks' copies of the push ones (`VtPullSelsH`, `vtPullSels*`'s),
the tables' `g^τ` (`kappa_base`'s frame variables `σ (27 + t)`), `zeta1` (`vt_zeta1`'s) and the
batching challenge's powers (`vt_xi_pow`'s, statements `2633 ..< 2638`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (accFold_spec accumulateSide_fst blockSel termsPure
  length_tableWeights jumpConstraints_eq refNConstraints)

@[expose] public section

/-- The pull blocks' selectors are their push twins' (`vtPullSels0 .. 5`). -/
def VtPullSelsH (σ : Val) : Prop :=
  ([σ (.n 1335), σ (.n 1337), σ (.n 1339), σ (.n 1341), σ (.n 1343)] = [σ (.n 858), σ (.n 863), σ (.n 868), σ (.n 873), σ (.n 878)]) ∧
  ([σ (.n 1345), σ (.n 1347), σ (.n 1349), σ (.n 1351), σ (.n 1353)] = [σ (.n 887), σ (.n 896), σ (.n 905), σ (.n 914), σ (.n 923)]) ∧
  ([σ (.n 1355), σ (.n 1357), σ (.n 1359)] = [σ (.n 932), σ (.n 941), σ (.n 950)]) ∧
  ([σ (.n 1361), σ (.n 1363), σ (.n 1365), σ (.n 1367), σ (.n 1369)] = [σ (.n 959), σ (.n 968), σ (.n 977), σ (.n 986), σ (.n 995)]) ∧
  ([σ (.n 1371), σ (.n 1373), σ (.n 1375), σ (.n 1377), σ (.n 1379)] = [σ (.n 1004), σ (.n 1013), σ (.n 1022), σ (.n 1031), σ (.n 1040)]) ∧
  ([σ (.n 1381), σ (.n 1383), σ (.n 1385), σ (.n 1387), σ (.n 1389), σ (.n 1391), σ (.n 1393), σ (.n 1395), σ (.n 1397), σ (.n 1399), σ (.n 1401), σ (.n 1403), σ (.n 1405), σ (.n 1407), σ (.n 1409), σ (.n 1411), σ (.n 1413), σ (.n 1415), σ (.n 1417), σ (.n 1419), σ (.n 1421), σ (.n 1423), σ (.n 1425), σ (.n 1427), σ (.n 1429), σ (.n 1431), σ (.n 1433), σ (.n 1435)] = [σ (.n 1049), σ (.n 1058), σ (.n 1067), σ (.n 1076), σ (.n 1085), σ (.n 1094), σ (.n 1103), σ (.n 1112), σ (.n 1121), σ (.n 1130), σ (.n 1139), σ (.n 1148), σ (.n 1157), σ (.n 1166), σ (.n 1175), σ (.n 1184), σ (.n 1193), σ (.n 1202), σ (.n 1211), σ (.n 1220), σ (.n 1229), σ (.n 1238), σ (.n 1247), σ (.n 1256), σ (.n 1265), σ (.n 1274), σ (.n 1283), σ (.n 1292)])

/-- **The forms' values.** -/
theorem vt_forms_valF {rd : Reader} {σ : Val} (hF : VtF rd σ) (bc : List K)
    (hbc : bc.length = 2 ^ 23) {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ) {weights : List E} (hwl : weights.length = 16)
    (hW : TbReadsAt rd (σ (.n 13)) weights) {t : ℕ} (ht : t < 6) :
    ((vtAcc2 (layoutOf bc lm rows) weights (σ (.n 14)) point
        [σ (.n 813), σ (.n 817)] (σ (.n 1303)) (σ (.n 1317)) (σ (.n 1841))
        (σ (.n 2442)) (σ (.n 2488)) (σ (.n 2543))).1.getD t []).map
        (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hpull
  have hw : ∀ i < 16, LoadHolds rd (σ (.n 13)) i (weights.getD i 0) :=
    fun i hi ↦ by
      have := hW i (by omega)
      rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e0, e1, e2⟩ := vt_forms hbc weights (σ (.n 14)) point
    [σ (.n 813), σ (.n 817)] (σ (.n 1303)) (σ (.n 1317)) (σ (.n 1841))
        (σ (.n 2442)) (σ (.n 2488)) (σ (.n 2543)) (fun c ↦ σ (.n c)) hP hC hr ⟨t, ht⟩ ((vtEvT σ t).getD · 0)
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
    (hkbt : ∀ t < 6, σ (.n (28 + t)) = gen ^ vtHt rows t)
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ)
    (hz1 : TbReadsAt rd (σ (.n 700)) (point.map (1 + ·)))
    (hxi : σ (.n 2612) = 1 ∧ σ (.n 2613) = σ (.n 2611) ∧ σ (.n 2614) = σ (.n 2611) ^ 2 ∧
      σ (.n 2615) = σ (.n 2611) ^ 3 ∧ σ (.n 2616) = σ (.n 2611) ^ 4)
    {weights : List E} (hwl : weights.length = 16)
    (hW : TbReadsAt rd (σ (.n 13)) weights) {n : ℕ}
    (hgn : σ (.n 2545) = gen ^ n) (hhn : ∀ t < 6, vtHt rows t ≤ n) (hnp : n ≤ point.length)
    {pts : List E} (hpl : pts.length = n)
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n 2631)) j (pts.take j).prod)
    (hpe : EqPrefix rd (σ (.n 2656)) 1 (σ (.n 16)) (σ (.n 700)) n)
    (hchi : ∀ i < n, LoadHolds rd (σ (.n 16)) (n - 1 - i) (pts.getD i 0)) :
    (termsPure ((powers (σ (.n 2611)) 5).take 2) ((powers (σ (.n 2611)) 5).drop 2) pts.reverse
      (List.zip (vtRows (tableHeightsOf rows)
        (vtAcc2 (layoutOf bc lm rows) weights (σ (.n 14)) point
          [σ (.n 813), σ (.n 817)] (σ (.n 1303)) (σ (.n 1317)) (σ (.n 1841))
        (σ (.n 2442)) (σ (.n 2488)) (σ (.n 2543))).1 point pts) (vtEvsT σ)) 0 0 []).1 =
      σ (.n 5952) := by
  set F := (vtAcc2 (layoutOf bc lm rows) weights (σ (.n 14)) point
    [σ (.n 813), σ (.n 817)] (σ (.n 1303)) (σ (.n 1317)) (σ (.n 1841))
        (σ (.n 2442)) (σ (.n 2488)) (σ (.n 2543))).1 with hF
  have hFv : ∀ t < 6, (F.getD t []).map (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := fun t ht ↦
    vt_forms_valF hV bc hbc hr hP hC hpull hwl hW ht
  have hF6 := (vt_forms3_shape bc lm hr weights (σ (.n 14)) point
    [σ (.n 813), σ (.n 817)] (σ (.n 1303)) (σ (.n 1317)) (σ (.n 1841))
        (σ (.n 2442)) (σ (.n 2488)) (σ (.n 2543))).1
  have hH6 : (tableHeightsOf rows).length = 6 := vt_tableHeightsOf_length hr
  set Wt := tableWeights (tableHeightsOf rows) point pts.reverse with hWt
  have hW6 : Wt.length = 6 := by rw [hWt, length_tableWeights, hH6]
  -- the weights
  have hwt : ∀ t < 6, ∀ {x cp pe : E}, σ (.n 2545) = x * σ (.n (28 + t)) →
      LoadHolds rd (σ (.n 2631) * x) 0 cp →
      LoadHolds rd (σ (.n 2656) * σ (.n (28 + t))) 0 pe → Wt.getD t 0 = cp * pe := by
    intro t ht x cp pe hx hcpL hpeL
    exact vt_weight_guest hpl hnp hcp hpe hchi hz1 hgn (by rw [hH6]; exact ht) (hhn t ht) hx
      (hkbt t ht) hcpL hpeL
  obtain ⟨x0, c0, p0, v0⟩ := vtAir0F hV
  obtain ⟨x1, c1, p1, v1⟩ := vtAir1F hV
  obtain ⟨x2, c2, p2, v2⟩ := vtAir2F hV
  obtain ⟨x3, c3, p3, v3⟩ := vtAir3F hV
  have hev4 : ∀ c < 14, σ (.n (vtEvB (47 + c))) = (vtEvT σ 4).getD c 0 :=
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
