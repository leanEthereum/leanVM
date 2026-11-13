/-
  LeanVM.Guest.B1.VerifySub.H.Vt

  `verify_tables`' honest data on an honest child (`ChildSegs.H`): the specification accepts it
  (`VtHonest.Ok`), it fits the deployed shapes (`VtShape`), and the tables' segment ends where the
  honest run does.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Runs
public import LeanVM.Guest.B1.VerifySub.H.VtRun

/-!
# `verify_tables`' honest data

`vtH_rowsT_length`, `rowsT_fst`: the table loop's six rows. On an honest child (`ChildSegs`, the
guest's bytecode of `2^23` words):

* `H_run`: `S.H` is `Ok`, the tables' words are its words (`curW`: four, ten, `3 n`, `153`), and
  the segment ends with nothing waiting;
* `H_spec`: the bus result and the claims are the honest ones (`vt_spec`), and the segment ends on
  `S.H.s3.squeeze.2`;
* `H_shape`: `S.H` fits the deployed shapes (`VtShape`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace VtHonest

theorem busH_forms_length {H : VtHonest} (hr : H.rows.length = 6) : H.busH.forms.length = 6 :=
  (vt_forms3_shape H.bc H.lm hr H.weights H.beta H.point (H.xs4.take 2) (H.xs4.getD 2 0)
    (H.xs4.getD 3 0) H.share (H.values.getD 0 0) (H.values.getD 1 0) (H.values.getD 2 0)).1

theorem vtH_rowsT_length {H : VtHonest} (hr : H.rows.length = 6) : H.rowsT.length = 6 := by
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  simp only [VtHonest.rowsT, vtRows, List.length_zip, hh, busH_forms_length hr,
    LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
  rfl

theorem rowsT_fst (H : VtHonest) (hr : H.rows.length = 6) : H.rowsT.map (·.1) = tables := by
  have hh : H.L.tableLogHeights.length = 6 := vt_tableHeights_length hr
  simp only [VtHonest.rowsT, vtRows]
  refine List.map_fst_zip ?_
  simp only [List.length_zip, hh, busH_forms_length hr,
    LeanVM.Protocol.EndToEnd.Complete.length_tableWeights]
  decide

end VtHonest

end
end LeanVM.Guest.B1.Tables

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem vsChunks_eq : ∀ (ns : List ℕ) (xs : List E), vsChunks ns xs = Tables.chunks ns xs
  | [], _ => rfl
  | n :: ns, xs => by rw [vsChunks, Tables.chunks, vsChunks_eq ns]

theorem tables_widths : tables.map (·.width) = Tables.vtW6 := by decide

theorem vtPushPad_tabs : Tables.vtPushPadData.map (·.2.1) =
    List.replicate 5 0 ++ List.replicate 5 1 ++ List.replicate 3 2 ++ List.replicate 5 3 ++
      List.replicate 5 4 ++ List.replicate 28 5 := by decide

theorem vtCountPad_tabs : Tables.vtCountPadData.map (·.2.1) =
    List.replicate 4 0 ++ List.replicate 4 1 ++ List.replicate 2 2 ++ List.replicate 4 3 ++
      List.replicate 4 4 ++ List.replicate 27 5 := by decide

/-- The push side's sizes total the push total. -/
theorem vtSizesP_sum (lm : ℕ) (rows : List ℕ) (hr : rows.length = 6) :
    ((Tables.vtSizesP lm (Tables.vtHt rows)).map (2 ^ ·)).sum =
      pushTot lm (Tables.tableHeightsOf rows) := by
  have hsl := heights_length6 rows hr
  have e : Tables.vtSizesP lm (Tables.vtHt rows) = [0, lm, 19] ++
      (Tables.vtPushPadData.map (·.2.1)).map (Tables.vtHt rows) := by
    simp only [Tables.vtSizesP, List.map_map]; rfl
  rw [e, vtPushPad_tabs]
  match hh : Tables.tableHeightsOf rows, hsl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTot_eq]
    simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, smul_eq_mul, Tables.vtHt, hh,
      List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The count side's sizes total at most the push total. -/
theorem vtSizesC_sum (lm : ℕ) (rows : List ℕ) (hr : rows.length = 6) :
    ((Tables.vtSizesC (Tables.vtHt rows)).map (2 ^ ·)).sum ≤
      pushTot lm (Tables.tableHeightsOf rows) := by
  have hsl := heights_length6 rows hr
  have e : Tables.vtSizesC (Tables.vtHt rows) =
      (Tables.vtCountPadData.map (·.2.1)).map (Tables.vtHt rows) := by
    simp only [Tables.vtSizesC, List.map_map]; rfl
  rw [e, vtCountPad_tabs]
  match hh : Tables.tableHeightsOf rows, hsl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTot_eq]
    simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
      smul_eq_mul, Tables.vtHt, hh, List.getD_cons_succ, List.getD_cons_zero]
    have := Nat.two_pow_pos lm
    omega

/-- Each height is at most the push side's depth. -/
theorem height_le_depth (lm : ℕ) {hs : List ℕ} (hl : hs.length = 6) {t : ℕ} (ht : t < 6) :
    hs.getD t 0 ≤ log2Ceil (pushTot lm hs) := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    have hp := pushTot_eq lm h0 h1 h2 h3 h4 h5
    have := Nat.two_pow_pos lm
    refine Tables.tb_le_log2Ceil_of_two_pow_le ?_
    interval_cases t <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- **`verify_tables`' honest data is accepted**: `S.H` is `Ok`, the tables' words are its words,
and the segment ends with nothing waiting. -/
theorem H_run (hbl : bytecode.length = 2 ^ 23) :
    S.H.Ok ∧ S.xsT = S.H.curW ∧ S.s5 = ⟨S.H.cap', []⟩ ∧
      S.xsT.length = 14 + 3 * S.nT + 153 := by
  obtain ⟨-, h4, -, -, -, -⟩ := S.gkr_inv hbl
  have hc4 : ∃ sp, (⟨S.s4.cap, []⟩ : Fs).Carries sp := by rw [← h4]; exact S.c4
  have hrun : RunsTo (Tables.tablesSeg (claimedBytecodeValue c.freshClaim)
      (Tables.layoutOf bytecode S.logMem S.rowsN) (Node.statementDigest seed c.statement) S.wb.1
      S.wb.2 S.rG.2.1 S.rG.2.2) ⟨S.s4.cap, []⟩ S.xsT (S.bus, S.claims) S.s5 := by
    rw [← h4, ← S.hlayout]; exact S.runT
  obtain ⟨x4, bcW, xR, evs, hxs, l4, l10, lR, l153, hpend, hbv⟩ :=
    Tables.vt_inv S.hrowsL hrun hc4
  have hn : S.H.n = S.nT := rfl
  have lR' : xR.length = 3 * S.nT := lR
  have e4 : S.H.xs4 = x4 := by
    show S.xsT.take 4 = x4
    rw [hxs, List.append_assoc, List.append_assoc, List.take_left' l4]
  have e10 : S.H.bcW = bcW := by
    show (S.xsT.drop 4).take 10 = bcW
    rw [hxs, List.append_assoc, List.append_assoc, List.drop_left' l4, List.take_left' l10]
  have eR : S.H.xsR = xR := by
    show (S.xsT.drop 14).take (3 * S.nT) = xR
    rw [hxs, List.append_assoc, List.append_assoc, show 14 = 4 + 10 from rfl, ← List.drop_drop,
      List.drop_left' l4, List.drop_left' l10, List.take_left' lR']
  have eE : S.H.evsT = Tables.chunks Tables.vtW6 evs := by
    show vsChunks (tables.map (·.width)) (S.xsT.drop (14 + 3 * S.nT)) = _
    rw [vsChunks_eq, tables_widths, hxs, List.append_assoc, List.append_assoc,
      show 14 + 3 * S.nT = 4 + (10 + 3 * S.nT) by omega, ← List.drop_drop, List.drop_left' l4,
      ← List.drop_drop, List.drop_left' l10, List.drop_left' lR']
  have hfl : S.H.evsT.flatten = evs := by
    rw [eE, Tables.chunks_flatten _ _ (by rw [l153]; rfl)]
  have hcur : S.xsT = S.H.curW := by
    show S.xsT = S.H.xs4 ++ S.H.bcW ++ S.H.xsR ++ S.H.evsT.flatten
    rw [e4, e10, eR, hfl]
    exact hxs
  have h5 : S.s5 = ⟨S.H.cap', []⟩ := fs_eta hpend
  have hr6 : S.H.rows.length = 6 := S.hrowsL
  refine ⟨⟨?_, hc4, by rw [e4, l4], by rw [e10, l10], by rw [eR, lR']; rfl, ?_, ?_, ?_⟩, hcur, h5, ?_⟩
  · show RunsTo _ _ (S.H.xs4 ++ S.H.bcW ++ S.H.xsR ++ S.H.evsT.flatten) _ _
    rw [← h5, show S.H.xs4 ++ S.H.bcW ++ S.H.xsR ++ S.H.evsT.flatten = S.xsT from hcur.symm]
    exact hrun
  · rw [eE, Tables.chunks_length, Tables.VtHonest.vtH_rowsT_length hr6]; rfl
  · intro p hp
    rw [eE] at hp
    exact (Tables.zip_chunks S.H.rowsT (Tables.VtHonest.rowsT_fst S.H hr6) evs l153).2.2 p hp
  · show Tables.BytecodeAt _ _ (_ ++ Tables.bcSlots (S.H.s0.absorbAll S.H.xs4 dsObserve) S.H.bcW)
      (S.H.bcW.getD 9 0)
    rw [e4, e10]
    exact hbv
  · rw [hxs]
    simp only [List.length_append, l4, l10, lR', l153]

/-- **The tables' segment is the honest one**: its bus result and claims (`vt_spec`), and it
ends on `S.H.s3.squeeze.2`. -/
theorem H_spec (hbl : bytecode.length = 2 ^ 23) :
    S.bus = S.H.busH ∧ S.claims = S.H.busH.claims ++ S.H.terms.2 ++ S.H.pclaims ∧
      S.s5 = ⟨S.H.s3.squeeze.2.cap, []⟩ := by
  obtain ⟨h, -, h5, -⟩ := S.H_run hbl
  obtain ⟨-, -, hb, hc, hcap⟩ := Tables.vt_spec h
  exact ⟨hb, hc, h5.trans (by rw [hcap])⟩

/-- **`verify_tables`' honest data fits the deployed shapes.** -/
theorem H_shape (hbl : bytecode.length = 2 ^ 23) : Tables.VtShape S.H := by
  obtain ⟨-, -, hf5, -, hpl, hvl⟩ := S.gkr_inv hbl
  have hd := S.d_bounds hbl
  have hdE := S.d_eq hbl
  have hh := heights_length6 S.rowsN S.hrowsL
  have hpT : S.pushT = pushTot S.logMem (Tables.tableHeightsOf S.rowsN) := rfl
  have hpl' : S.H.point.length = log2Ceil (pushTot S.logMem (Tables.tableHeightsOf S.rowsN)) := by
    show S.rG.2.1.length = _
    rw [hpl, hdE, hpT]
  have h29 := (S.hs_bounds hbl).1
  have hht : ∀ t < 6, Tables.vtHt S.rowsN t ∈ S.hs := fun t ht ↦ by
    show (Tables.tableHeightsOf S.rowsN).getD t 0 ∈ Tables.tableHeightsOf S.rowsN
    rw [List.getD_eq_getElem _ _ (by rw [hh]; exact ht)]
    exact List.getElem_mem _
  have hfit : pushTot S.logMem (Tables.tableHeightsOf S.rowsN) ≤ 2 ^ S.H.point.length := by
    rw [hpl']; exact le_two_pow_log2Ceil _
  refine ⟨(S.h30.trans (by norm_num)), ?_, ?_, ?_, S.hrowsL, fun t ht ↦ h29 _ (hht t ht), fun t ht ↦ ?_,
    S.wb_length hbl, hvl, hf5, ?_, ?_, hbl⟩
  · rw [hpl']
    refine Tables.tb_le_log2Ceil_of_two_pow_le ?_
    have := pushTot_ge S.logMem hh
    show 2 ^ S.logMem ≤ _
    omega
  · show 19 ≤ S.rG.2.1.length
    omega
  · show S.rG.2.1.length < 33
    omega
  · rw [hpl']
    exact height_le_depth S.logMem hh ht
  · show ((Tables.vtSizesP S.logMem (Tables.vtHt S.rowsN)).map (2 ^ ·)).sum ≤ _
    rw [vtSizesP_sum _ _ S.hrowsL]
    exact hfit
  · exact (vtSizesC_sum S.logMem _ S.hrowsL).trans hfit

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
