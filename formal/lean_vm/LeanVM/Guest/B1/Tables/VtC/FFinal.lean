/-
  LeanVM.Guest.B1.Tables.VtC.FFinal

  `Vt/AsmForms.lean`'s forms' values and `Vt/AsmFinal.lean`'s final check on the window `VtF`:
  `termsPure`'s terminal value over the six tables is the guest's `air_acc` (`σ 5627`).
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
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_tables»

/-!
# The forms and the final check, on the window

What the soundness proof read outside the window becomes hypotheses: the push and count blocks'
selectors (`vt_sels`'s), the pull blocks' copies of the push ones (`VtPullSelsH`, `vtPullSels*`'s),
the tables' `g^τ` (`kappa_base`'s frame variables `σ (27 + t)`), `zeta1` (`vt_zeta1`'s) and the
batching challenge's powers (`vt_xi_pow`'s, statements `zc_xi_pows[0] ..< bus_target@1`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (accFold_spec accumulateSide_fst blockSel termsPure
  length_tableWeights jumpConstraints_eq refNConstraints)

@[expose] public section

/-- The pull blocks' selectors are their push twins' (`vtPullSels0 .. 5`). -/
def VtPullSelsH (σ : Val) : Prop :=
  ([σ (.n (val% «verify_tables» "block_eq_hi[57]")), σ (.n (val% «verify_tables» "block_eq_hi[58]")), σ (.n (val% «verify_tables» "block_eq_hi[59]")), σ (.n (val% «verify_tables» "block_eq_hi[60]")), σ (.n (val% «verify_tables» "block_eq_hi[61]"))] = [σ (.n (val% «verify_tables» "block_eq_hi[3]")), σ (.n (val% «verify_tables» "block_eq_hi[4]")), σ (.n (val% «verify_tables» "block_eq_hi[5]")), σ (.n (val% «verify_tables» "block_eq_hi[6]")), σ (.n (val% «verify_tables» "block_eq_hi[7]"))]) ∧
  ([σ (.n (val% «verify_tables» "block_eq_hi[62]")), σ (.n (val% «verify_tables» "block_eq_hi[63]")), σ (.n (val% «verify_tables» "block_eq_hi[64]")), σ (.n (val% «verify_tables» "block_eq_hi[65]")), σ (.n (val% «verify_tables» "block_eq_hi[66]"))] = [σ (.n (val% «verify_tables» "block_eq_hi[8]")), σ (.n (val% «verify_tables» "block_eq_hi[9]")), σ (.n (val% «verify_tables» "block_eq_hi[10]")), σ (.n (val% «verify_tables» "block_eq_hi[11]")), σ (.n (val% «verify_tables» "block_eq_hi[12]"))]) ∧
  ([σ (.n (val% «verify_tables» "block_eq_hi[67]")), σ (.n (val% «verify_tables» "block_eq_hi[68]")), σ (.n (val% «verify_tables» "block_eq_hi[69]"))] = [σ (.n (val% «verify_tables» "block_eq_hi[13]")), σ (.n (val% «verify_tables» "block_eq_hi[14]")), σ (.n (val% «verify_tables» "block_eq_hi[15]"))]) ∧
  ([σ (.n (val% «verify_tables» "block_eq_hi[70]")), σ (.n (val% «verify_tables» "block_eq_hi[71]")), σ (.n (val% «verify_tables» "block_eq_hi[72]")), σ (.n (val% «verify_tables» "block_eq_hi[73]")), σ (.n (val% «verify_tables» "block_eq_hi[74]"))] = [σ (.n (val% «verify_tables» "block_eq_hi[16]")), σ (.n (val% «verify_tables» "block_eq_hi[17]")), σ (.n (val% «verify_tables» "block_eq_hi[18]")), σ (.n (val% «verify_tables» "block_eq_hi[19]")), σ (.n (val% «verify_tables» "block_eq_hi[20]"))]) ∧
  ([σ (.n (val% «verify_tables» "block_eq_hi[75]")), σ (.n (val% «verify_tables» "block_eq_hi[76]")), σ (.n (val% «verify_tables» "block_eq_hi[77]")), σ (.n (val% «verify_tables» "block_eq_hi[78]")), σ (.n (val% «verify_tables» "block_eq_hi[79]"))] = [σ (.n (val% «verify_tables» "block_eq_hi[21]")), σ (.n (val% «verify_tables» "block_eq_hi[22]")), σ (.n (val% «verify_tables» "block_eq_hi[23]")), σ (.n (val% «verify_tables» "block_eq_hi[24]")), σ (.n (val% «verify_tables» "block_eq_hi[25]"))]) ∧
  ([σ (.n (val% «verify_tables» "block_eq_hi[80]")), σ (.n (val% «verify_tables» "block_eq_hi[81]")), σ (.n (val% «verify_tables» "block_eq_hi[82]")), σ (.n (val% «verify_tables» "block_eq_hi[83]")), σ (.n (val% «verify_tables» "block_eq_hi[84]")), σ (.n (val% «verify_tables» "block_eq_hi[85]")), σ (.n (val% «verify_tables» "block_eq_hi[86]")), σ (.n (val% «verify_tables» "block_eq_hi[87]")), σ (.n (val% «verify_tables» "block_eq_hi[88]")), σ (.n (val% «verify_tables» "block_eq_hi[89]")), σ (.n (val% «verify_tables» "block_eq_hi[90]")), σ (.n (val% «verify_tables» "block_eq_hi[91]")), σ (.n (val% «verify_tables» "block_eq_hi[92]")), σ (.n (val% «verify_tables» "block_eq_hi[93]")), σ (.n (val% «verify_tables» "block_eq_hi[94]")), σ (.n (val% «verify_tables» "block_eq_hi[95]")), σ (.n (val% «verify_tables» "block_eq_hi[96]")), σ (.n (val% «verify_tables» "block_eq_hi[97]")), σ (.n (val% «verify_tables» "block_eq_hi[98]")), σ (.n (val% «verify_tables» "block_eq_hi[99]")), σ (.n (val% «verify_tables» "block_eq_hi[100]")), σ (.n (val% «verify_tables» "block_eq_hi[101]")), σ (.n (val% «verify_tables» "block_eq_hi[102]")), σ (.n (val% «verify_tables» "block_eq_hi[103]")), σ (.n (val% «verify_tables» "block_eq_hi[104]")), σ (.n (val% «verify_tables» "block_eq_hi[105]")), σ (.n (val% «verify_tables» "block_eq_hi[106]")), σ (.n (val% «verify_tables» "block_eq_hi[107]"))] = [σ (.n (val% «verify_tables» "block_eq_hi[26]")), σ (.n (val% «verify_tables» "block_eq_hi[27]")), σ (.n (val% «verify_tables» "block_eq_hi[28]")), σ (.n (val% «verify_tables» "block_eq_hi[29]")), σ (.n (val% «verify_tables» "block_eq_hi[30]")), σ (.n (val% «verify_tables» "block_eq_hi[31]")), σ (.n (val% «verify_tables» "block_eq_hi[32]")), σ (.n (val% «verify_tables» "block_eq_hi[33]")), σ (.n (val% «verify_tables» "block_eq_hi[34]")), σ (.n (val% «verify_tables» "block_eq_hi[35]")), σ (.n (val% «verify_tables» "block_eq_hi[36]")), σ (.n (val% «verify_tables» "block_eq_hi[37]")), σ (.n (val% «verify_tables» "block_eq_hi[38]")), σ (.n (val% «verify_tables» "block_eq_hi[39]")), σ (.n (val% «verify_tables» "block_eq_hi[40]")), σ (.n (val% «verify_tables» "block_eq_hi[41]")), σ (.n (val% «verify_tables» "block_eq_hi[42]")), σ (.n (val% «verify_tables» "block_eq_hi[43]")), σ (.n (val% «verify_tables» "block_eq_hi[44]")), σ (.n (val% «verify_tables» "block_eq_hi[45]")), σ (.n (val% «verify_tables» "block_eq_hi[46]")), σ (.n (val% «verify_tables» "block_eq_hi[47]")), σ (.n (val% «verify_tables» "block_eq_hi[48]")), σ (.n (val% «verify_tables» "block_eq_hi[49]")), σ (.n (val% «verify_tables» "block_eq_hi[50]")), σ (.n (val% «verify_tables» "block_eq_hi[51]")), σ (.n (val% «verify_tables» "block_eq_hi[52]")), σ (.n (val% «verify_tables» "block_eq_hi[53]"))])

/-- **The forms' values.** -/
theorem vt_forms_valF {rd : Reader} {σ : Val} (hF : VtF rd σ) (bc : List K)
    (hbc : bc.length = 2 ^ 23) {point : List E} {lm : ℕ} {rows : List ℕ} (hr : rows.length = 6)
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ) {weights : List E} (hwl : weights.length = 16)
    (hW : TbReadsAt rd (σ (.n (val% «verify_tables» "fp_w"))) weights) {t : ℕ} (ht : t < 6) :
    ((vtAcc2 (layoutOf bc lm rows) weights (σ (.n (val% «verify_tables» "beta"))) point
        [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
        (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) (σ (.n (val% «verify_tables» "s53.u2.s5#0")))).1.getD t []).map
        (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := by
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := hpull
  have hw : ∀ i < 16, LoadHolds rd (σ (.n (val% «verify_tables» "fp_w"))) i (weights.getD i 0) :=
    fun i hi ↦ by
      have := hW i (by omega)
      rwa [← List.getD_eq_getElem _ 0] at this
  obtain ⟨e0, e1, e2⟩ := vt_forms hbc weights (σ (.n (val% «verify_tables» "beta"))) point
    [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
        (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) (σ (.n (val% «verify_tables» "s53.u2.s5#0"))) (fun c ↦ σ (.n c)) hP hC hr ⟨t, ht⟩ ((vtEvT σ t).getD · 0)
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
    (hkbt : ∀ t < 6, σ (.n ((val% «verify_tables» "kb[2]") + t)) = gen ^ vtHt rows t)
    (hP : ∀ i < 51, σ (.n (vtPushPadData.getD i default).2.2.1) =
      blockSel (vtSizesP lm (vtHt rows)) point.length (3 + i) point)
    (hC : ∀ i < 45, σ (.n (vtCountPadData.getD i default).2.2.1) =
      blockSel (vtSizesC (vtHt rows)) point.length i point)
    (hpull : VtPullSelsH σ)
    (hz1 : TbReadsAt rd (σ (.n (val% «verify_tables» "zeta1"))) (point.map (1 + ·)))
    (hxi : σ (.n (val% «verify_tables» "zc_xi_pows[0]")) = 1 ∧ σ (.n (val% «verify_tables» "zc_xi_pows[1]")) = σ (.n (val% «verify_tables» "nxt[0]@3")) ∧ σ (.n (val% «verify_tables» "zc_xi_pows[2]")) = σ (.n (val% «verify_tables» "nxt[0]@3")) ^ 2 ∧
      σ (.n (val% «verify_tables» "zc_xi_pows[3]")) = σ (.n (val% «verify_tables» "nxt[0]@3")) ^ 3 ∧ σ (.n (val% «verify_tables» "zc_xi_pows[4]")) = σ (.n (val% «verify_tables» "nxt[0]@3")) ^ 4)
    {weights : List E} (hwl : weights.length = 16)
    (hW : TbReadsAt rd (σ (.n (val% «verify_tables» "fp_w"))) weights) {n : ℕ}
    (hgn : σ (.n (val% «verify_tables» "g_zc_n")) = gen ^ n) (hhn : ∀ t < 6, vtHt rows t ≤ n) (hnp : n ≤ point.length)
    {pts : List E} (hpl : pts.length = n)
    (hcp : ∀ j ≤ n, LoadHolds rd (σ (.n (val% «verify_tables» "zc_cprod"))) j (pts.take j).prod)
    (hpe : EqPrefix rd (σ (.n (val% «verify_tables» "zc_peq"))) 1 (σ (.n (val% «verify_tables» "chi"))) (σ (.n (val% «verify_tables» "zeta1"))) n)
    (hchi : ∀ i < n, LoadHolds rd (σ (.n (val% «verify_tables» "chi"))) (n - 1 - i) (pts.getD i 0)) :
    (termsPure ((powers (σ (.n (val% «verify_tables» "nxt[0]@3"))) 5).take 2) ((powers (σ (.n (val% «verify_tables» "nxt[0]@3"))) 5).drop 2) pts.reverse
      (List.zip (vtRows (tableHeightsOf rows)
        (vtAcc2 (layoutOf bc lm rows) weights (σ (.n (val% «verify_tables» "beta"))) point
          [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
        (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) (σ (.n (val% «verify_tables» "s53.u2.s5#0")))).1 point pts) (vtEvsT σ)) 0 0 []).1 =
      σ (.n (val% «verify_tables» "air_acc@6")) := by
  set F := (vtAcc2 (layoutOf bc lm rows) weights (σ (.n (val% «verify_tables» "beta"))) point
    [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
        (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) (σ (.n (val% «verify_tables» "s53.u2.s5#0")))).1 with hF
  have hFv : ∀ t < 6, (F.getD t []).map (·.evaluate ((vtEvT σ t).getD · 0)) =
      (vtFV.getD t []).map fun v ↦ σ (.n v) := fun t ht ↦
    vt_forms_valF hV bc hbc hr hP hC hpull hwl hW ht
  have hF6 := (vt_forms3_shape bc lm hr weights (σ (.n (val% «verify_tables» "beta"))) point
    [σ (.n (val% «verify_tables» "x@1")), σ (.n (val% «verify_tables» "x@2"))] (σ (.n (val% «verify_tables» "x@3"))) (σ (.n (val% «verify_tables» "x@4"))) (σ (.n (val% «verify_tables» "x@5")))
        (σ (.n (val% «verify_tables» "s53.u0.s5#0"))) (σ (.n (val% «verify_tables» "s53.u1.s5#0"))) (σ (.n (val% «verify_tables» "s53.u2.s5#0")))).1
  have hH6 : (tableHeightsOf rows).length = 6 := vt_tableHeightsOf_length hr
  set Wt := tableWeights (tableHeightsOf rows) point pts.reverse with hWt
  have hW6 : Wt.length = 6 := by rw [hWt, length_tableWeights, hH6]
  -- the weights
  have hwt : ∀ t < 6, ∀ {x cp pe : E}, σ (.n (val% «verify_tables» "g_zc_n")) = x * σ (.n ((val% «verify_tables» "kb[2]") + t)) →
      LoadHolds rd (σ (.n (val% «verify_tables» "zc_cprod")) * x) 0 cp →
      LoadHolds rd (σ (.n (val% «verify_tables» "zc_peq")) * σ (.n ((val% «verify_tables» "kb[2]") + t))) 0 pe → Wt.getD t 0 = cp * pe := by
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
