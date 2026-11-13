/-
  LeanVM.Guest.B1.Tables.VtC.BMain

  **`verify_tables`' bus sides complete** (statements `765 ..< 2593`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BAll

/-!
# The bus sides, complete

`vtB_complete`: under `VtBHyp`, every statement of `765 ..< 2593` holds on the honest valuation,
every load reads inside `vtBufsB`, the framework words and the bytecode share's are the cursor's,
the share's last capacity and cursor are the honest ones (`vtBcR3`), the selectors are the blocks'
`blockSel`, and the three bus totals are `vtAcc0/1/2`'s at the honest words and GKR leaves (as
`vt_asm_totals`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd.Complete (blockSel)

@[expose] public section

theorem vtB_flatP : tbStmtsEqb ((List.range 51).flatMap fun i ↦ vtSelT
    (vtPushSel.getD i default).2.2.1 (vtPushSel.getD i default).1
    (vtPushSel.getD i default).2.2.2.1 (vtPushSel.getD i default).2.2.2.2.1
    (vtPushSel.getD i default).2.2.2.2.2.1 (vtPushSel.getD i default).2.2.2.2.2.2.1
    (vtPushSel.getD i default).2.2.2.2.2.2.2)
    ((vtPre.drop 842).take 490) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtB_flatC : tbStmtsEqb ((List.range 45).flatMap fun i ↦ vtSelT
    (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
    (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2.1
    (vtCountSel.getD i default).2.2.2.2.2.1 (vtCountSel.getD i default).2.2.2.2.2.2.1
    (vtCountSel.getD i default).2.2.2.2.2.2.2)
    ((vtPre.drop 1479).take 433) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtB_index_stmts :
    tbStmtsEqb [.dispatch (.n 26) vtImNames [.n 8] [.n 809]] ((vtPre.drop 795).take 1) = true ∧
    tbStmtsEqb [.dispatch (.n 821) vtImNames [.n 8] [.n 837]] ((vtPre.drop 825).take 1) = true :=
  by simp only [vtPre_drop]; decide +kernel

/-- A slice is a checked block's statements. -/
theorem vtB_tmpl {P : Stmt → Prop} {blk : List Stmt} {pos : ℕ}
    (hc : tbStmtsEqb blk ((vtPre.drop pos).take blk.length) = true) (h : ∀ s ∈ blk, P s) :
    ∀ s ∈ (vtPre.drop pos).take blk.length, P s := by
  rw [← tbStmtsEqb_sound hc]; exact h

/-- A slice is a checked block's statements, checked at `vtAt`. -/
theorem vtB_tmplAt {P : Stmt → Prop} {blk : List Stmt} {pos : ℕ}
    (hc : tbStmtsEqb blk ((vtAt pos).take blk.length) = true) (h : ∀ s ∈ blk, P s) :
    ∀ s ∈ (vtPre.drop pos).take blk.length, P s :=
  vtB_tmpl (vtPre_drop pos ▸ hc) h

/-- Slices in a row. -/
theorem vtB_cover {P : Stmt → Prop} : ∀ (cuts : List ℕ) (a : ℕ),
    (∀ i < cuts.length, ∀ s ∈ (vtPre.drop (a + (cuts.take i).sum)).take (cuts.getD i 0), P s) →
      ∀ s ∈ (vtPre.drop a).take cuts.sum, P s
  | [], _, _ => by simp
  | c :: cuts, a, h => by
    rw [List.sum_cons]
    refine forall_slice_join (a := a) (l1 := c) (l2 := cuts.sum) (by simpa using h 0 (by simp)) ?_
    refine vtB_cover cuts (a + c) fun i hi ↦ ?_
    have := h (i + 1) (by simp; omega)
    simpa [List.take_succ_cons, Nat.add_assoc] using this

/-- The framework blocks' copies the totals read (the soundness's `vt_fw_copies`, on `VtP`). -/
theorem vtP_fw_copies {rd : Reader} {σ : Val} (h : VtP rd σ) :
    σ (.n 810) = σ (.n 809) ∧ σ (.n 815) = σ (.n 812) ∧ σ (.n 819) = σ (.n 816) ∧
      σ (.n 838) = σ (.n 837) ∧ σ (.n 1293) = σ (.n 832) ∧ σ (.n 1294) = σ (.n 790) ∧
      σ (.n 1299) = σ (.n 807) ∧ σ (.n 1313) = σ (.n 835) ∧ σ (.n 1436) = σ (.n 835) ∧
      σ (.n 1305) = σ (.n 1302) ∧ σ (.n 1307) = σ (.n 1306) ∧ σ (.n 1309) = σ (.n 1308) ∧
      σ (.n 1319) = σ (.n 1316) := by
  have a1 := h.atomAt 796 (.copy (.n 810) (.n 809)) (by decide +kernel)
  have a2 := h.atomAt 803 (.copy (.n 815) (.n 812)) (by decide +kernel)
  have a3 := h.atomAt 808 (.copy (.n 819) (.n 816)) (by decide +kernel)
  have a4 := h.atomAt 826 (.copy (.n 838) (.n 837)) (by decide +kernel)
  have a5 := h.atomAt 1333 (.copy (.n 1293) (.n 832)) (by decide +kernel)
  have a6 := h.atomAt 1334 (.copy (.n 1294) (.n 790)) (by decide +kernel)
  have a7 := h.atomAt 1339 (.copy (.n 1299) (.n 807)) (by decide +kernel)
  have a8 := h.atomAt 1354 (.copy (.n 1313) (.n 835)) (by decide +kernel)
  have a9 := h.atomAt 1478 (.copy (.n 1436) (.n 835)) (by decide +kernel)
  have a10 := h.atomAt 1346 (.copy (.n 1305) (.n 1302)) (by decide +kernel)
  have a11 := h.atomAt 1348 (.copy (.n 1307) (.n 1306)) (by decide +kernel)
  have a12 := h.atomAt 1350 (.copy (.n 1309) (.n 1308)) (by decide +kernel)
  have a13 := h.atomAt 1361 (.copy (.n 1319) (.n 1316)) (by decide +kernel)
  simp only [Atom.Holds] at a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

/-- `beta + 1` (the soundness's `vt_beta1`, on `VtP`). -/
theorem vtP_beta1 {rd : Reader} {σ : Val} (h : VtP rd σ) : σ (.n 1975) = σ (.n 14) + 1 := by
  have a1 := h.atomAt 2021 (.const (.n 1974) (word 1 0)) (by decide +kernel)
  have a2 := h.atomAt 2022 (.add (.n 1975) (.n 14) (.n 1974)) (by decide +kernel)
  simp only [Atom.Holds] at a1 a2
  rw [a2, a1, tb_word_one]

section
variable {rd : Reader} {wo : ℕ → E} {args : List E}

local notation "σv" => vtσ rd wo args

/-- **`index_mle`'s arm, complete.** -/
theorem vtB_indexArm (hl : args.length = 20) {x r : V} {point : List E} {κ : ℕ}
    (hm : Stmt.dispatch x vtImNames [.n 8] [r] ∈ vtPre) (hx : σv x = gen ^ κ)
    (hκ : κ < 34) (hκμ : κ ≤ point.length) (hz : TbReadsAt rd (σv (.n 8)) point)
    (hr : wo r.idx = indexMle (point.take κ)) :
    VSH (coreProgram.Rel rd) rd σv (.dispatch x vtImNames [.n 8] [r]) ∧
      σv r = indexMle (point.take κ) := by
  have er : σv r = indexMle (point.take κ) := by
    rw [vtB_retsM (rd := rd) (w := wo) hl hm r (by simp), hr]
  refine ⟨vshB_dispatch (j := κ) (by simp [vtImNames]; omega) hx ?_, er⟩
  simp only [vtImNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
  rw [er]
  exact index_mle_complete_holds κ hκ rd _ _
    ⟨point.take κ, by simp; omega, tbReadsAt_take hz κ, rfl⟩

set_option maxRecDepth 100000 in
/-- **`verify_tables`' bus sides complete** (statements `765 ..< 2593`). -/
theorem vtB_complete {D : VtBIn} (H : VtBHyp rd wo args D) :
    (∀ s ∈ (vtPre.drop 765).take 1828, VSH (coreProgram.Rel rd) rd σv s) ∧
      LoadsInBuf σv (vtBufsB σv) ((vtPre.drop 765).take 1828) ∧
      [σv (.n 812), σv (.n 816), σv (.n 1302), σv (.n 1316)] = D.xs ∧
      σv (.n 1840) = D.w.getD 0 0 ∧ σv (.n 1905) = D.w.getD 9 0 ∧
      [σv (.n 1892), σv (.n 1893), σv (.n 1894), σv (.n 1895), σv (.n 1896)] =
        (vtBcR3 (vtF0 args D.xs) D.w).1 ∧
      σv (.n 1897) = args.getD 5 0 * gen ^ 13 ∧
      σv (.n 2442) = (vtAcc0 (layoutOf D.bc D.lm D.rows) D.weights (args.getD 14 0) D.point
        [D.xs.getD 0 0, D.xs.getD 1 0] (D.w.getD 0 0) (D.leaves.getD 0 0)).2 ∧
      σv (.n 2488) = (vtAcc1 (layoutOf D.bc D.lm D.rows) D.weights (args.getD 14 0) D.point
        [D.xs.getD 0 0, D.xs.getD 1 0] (D.xs.getD 2 0) (D.xs.getD 3 0) (D.w.getD 0 0)
        (D.leaves.getD 0 0) (D.leaves.getD 1 0)).2 ∧
      σv (.n 2543) = (vtAcc2 (layoutOf D.bc D.lm D.rows) D.weights (args.getD 14 0) D.point
        [D.xs.getD 0 0, D.xs.getD 1 0] (D.xs.getD 2 0) (D.xs.getD 3 0) (D.w.getD 0 0)
        (D.leaves.getD 0 0) (D.leaves.getD 1 0) (D.leaves.getD 2 0)).2 ∧
      σv (.n 788) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 0 D.point ∧
      σv (.n 804) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 1 D.point ∧
      σv (.n 832) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 2 D.point ∧
      σv (.n 790) = σv (.n 788) ∧ σv (.n 807) = σv (.n 804) ∧ σv (.n 835) = σv (.n 832) ∧
      (∀ i < 51, σv (.n (vtPushPadData.getD i default).2.2.1) =
        blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length (3 + i) D.point) ∧
      (∀ i < 45, σv (.n (vtCountPadData.getD i default).2.2.1) =
        blockSel (vtSizesC (vtHt D.rows)) D.point.length i D.point) := by
  obtain ⟨hl, hlow, hml, hlmμ, h19, hr, hτμ, hmu, hz, hwl, hW, hxl, hbl, hcur, hpool, hll,
    hleaves, hpt, ekb, eoP, eoC, eSh, e664, e699, e701, e702, hpw, hidxc, hz1, hrun, hidxB, hfitP,
    hfitC, hbitsF, hdigP, hdigC, hwF, hwP, hwC, hwI, hw1, hw2, hw3, hacc, hbc⟩ := H
  have p : ∀ i < 20, σv (.n i) = args.getD i 0 := fun i hi ↦ vt_param hl hi
  -- the weights
  set W : ℕ → E := fun i ↦ D.weights.getD i 0 with hWd
  have hw : ∀ i < 16, LoadHolds rd (σv (.n 13)) i (W i) := fun i hi ↦ by
    rw [p 13 (by norm_num), hWd]
    simp only
    rw [List.getD_eq_getElem D.weights 0 (by omega)]
    exact hW i (by omega)
  have hWσ : TbReadsAt rd (σv (.n 13)) D.weights := by
    rw [p 13 (by norm_num)]; exact hW
  have hP := vtP_honest hl (by omega) hWσ
  -- the selectors
  obtain ⟨vF0, vF1, vF2, vP, vC, s0, s1, s2, c0, c1, c2, hS, hsum, hSC, hsumC⟩ :=
    vtc_sels (wo := wo) (lm := D.lm) (τ := vtHt D.rows) hl hlow (point := D.point)
      (by rw [p 9 (by norm_num)]; exact hmu) hml (by rw [e699]; exact hz1)
      (by rw [e664]; exact hidxc) hlmμ h19 hτμ ekb hfitP hfitC eoP eoC eSh
      (by rw [e701, e702]; exact hrun) hbitsF hdigP hdigC hwF hwP hwC
  -- the stream's words, the share
  have hlen : (D.xs ++ D.w).length = 14 := by simp [hxl, hbl]
  have hc7 : ∀ i < 7, LoadHolds rd (σv (.n 5)) i ((D.xs ++ D.w).getD i 0) := fun i hi ↦ by
    rw [p 5 (by norm_num), List.getD_eq_getElem (D.xs ++ D.w) 0 (by omega)]
    exact hcur i (by omega)
  obtain ⟨hxs, -, -, -, -, -, d1843, -, -⟩ := vtB_fresh (wo := wo) hl hxl hbl hcur
  obtain ⟨b1931, b1940, b1941, b1942, b1943, b1944, b1945, b1951, b2020, e1840, e1905, ecap3,
    e1897⟩ := vtB_bc (wo := wo) hl hxl hbl hcur hwl hW hpt hw1 hw2 hw3 hacc
  have x0 : σv (.n 812) = D.xs.getD 0 0 := by rw [← hxs, List.getD_cons_zero]
  have x1 : σv (.n 816) = D.xs.getD 1 0 := by rw [← hxs, List.getD_cons_succ, List.getD_cons_zero]
  have x2 : σv (.n 1302) = D.xs.getD 2 0 := by
    rw [← hxs, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
  have x3 : σv (.n 1316) = D.xs.getD 3 0 := by
    rw [← hxs, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero]
  -- the index MLEs
  have k1 : σv (.n 26) = gen ^ D.lm := by simpa using ekb 1 (by norm_num)
  have k2 : σv (.n 821) = gen ^ 19 := by
    have e0 : σv (.n 25) = 1 := by simpa using ekb 0 (by norm_num)
    rw [vt_mulAt hl 810 (d := 821) (x := 25) (y := 820) (by norm_num) (by norm_num)
        (by decide +kernel), vt_constAt hl 809 (d := .n 820) (e := word 524288 0)
        (by decide +kernel), show (524288 : ℕ) = 2 ^ 19 by norm_num,
      tb_word_two_pow (by norm_num), e0, one_mul]
  have hz8 : TbReadsAt rd (σv (.n 8)) D.point := by rw [p 8 (by norm_num)]; exact hz
  obtain ⟨I1, i1⟩ := vtB_indexArm hl (vt_memAt 795 _ (vtAt_eqb vtB_index_stmts.1)) k1 (by omega)
    hlmμ hz8 hwI.1
  obtain ⟨I2, i2⟩ := vtB_indexArm hl (vt_memAt 825 _ (vtAt_eqb vtB_index_stmts.2)) k2
    (by norm_num) h19 hz8 hwI.2
  -- the buffers
  have e777 : σv (.n 777) = wo 777 := vt_allocAt hl 765 (k := 153) (by decide +kernel)
  have hidxσ : ∀ i < 3, LoadHolds rd (σv (.n 777)) i ((vtIdxBufW D.point D.lm).getD i 0) :=
    fun i hi ↦ by
      rw [e777, List.getD_eq_getElem _ _ (by simp [vtIdxBufW]; omega)]
      exact hidxB i (by simp [vtIdxBufW]; omega)
  have hpoolσ : ∀ i < 4, LoadHolds rd (σv (.n 15)) i (D.xs.getD i 0) := fun i hi ↦ by
    rw [p 15 (by norm_num)]; exact hpool i hi
  have hleavesσ : ∀ i < 3, LoadHolds rd (σv (.n 17)) i (D.leaves.getD i 0) := fun i hi ↦ by
    rw [p 17 (by norm_num), List.getD_eq_getElem D.leaves 0 (by omega)]
    exact hleaves i (by omega)
  have hptσ : ∀ i < 4, LoadHolds rd (σv (.n 19)) i
      ((vtBcPoint (vtF0 args D.xs) D.w).getD i 0) := fun i hi ↦ by
    have h4 : (vtBcPoint (vtF0 args D.xs) D.w).length = 4 := rfl
    rw [p 19 (by norm_num), List.getD_eq_getElem (vtBcPoint (vtF0 args D.xs) D.w) 0 (by omega)]
    exact hpt i (by omega)
  have q1 : (vtIdxBufW D.point D.lm).getD 1 0 = indexMle (D.point.take D.lm) := by
    simp [vtIdxBufW]
  have q2 : (vtIdxBufW D.point D.lm).getD 2 0 = indexMle (D.point.take 19) := by
    simp [vtIdxBufW]
  -- the stores
  have h797 : VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 809) (.n 777) 1)) :=
    vsh_store (hidxσ 1 (by norm_num)) (by rw [i1, q1])
  have h827 : VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 837) (.n 777) 2)) :=
    vsh_store (hidxσ 2 (by norm_num)) (by rw [i2, q2])
  have h802 := vsh_store (d := .n 812) (hpoolσ 0 (by norm_num)) x0
  have h807 := vsh_store (d := .n 816) (hpoolσ 1 (by norm_num)) x1
  have h1345 := vsh_store (d := .n 1302) (hpoolσ 2 (by norm_num)) x2
  have h1360 := vsh_store (d := .n 1316) (hpoolσ 3 (by norm_num)) x3
  -- the glue
  have g765 := vtB_glue_765 (rd := rd) (wo := wo) hl
  have g778 := vtB_glue_778 (rd := rd) (wo := wo) hl
  have g794 := vtB_glue_794 hl hc7 I1 h797 h802 h807
  have g824 := vtB_glue_824 hl I2 h827
  have g1332 := vtB_glue_1332 hl hpoolσ hidxσ hc7 h1345 h1360
  have g1912 := vtB_glue_1912 hl hc7
  have g1926 := vtB_glue_1926 hl hw hptσ b1931 b1940 b1941 b1942 b1943 b1944 b1945 b1951 b2020
  have g2021 := vtB_glue_2021 hl hw hleavesσ
  -- every statement
  have hall : ∀ s ∈ (vtPre.drop 765).take 1828, VSH (coreProgram.Rel rd) rd σv s := by
    refine vtB_cover [1, 12, 3, 13, 17, 13, 18, 490, 147, 433, 14, 95, 572] 765 fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact g765
    · exact vtB_tmplAt vtFw0_check vF0
    · exact g778
    · exact vtB_tmplAt vtFw1_check vF1
    · exact g794
    · exact vtB_tmplAt vtFw2_check vF2
    · exact g824
    · intro s hs
      change s ∈ (vtPre.drop 842).take 490 at hs
      rw [← tbStmtsEqb_sound vtB_flatP] at hs
      obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hs
      exact vP j (List.mem_range.mp hj) s hs
    · exact g1332
    · intro s hs
      change s ∈ (vtPre.drop 1479).take 433 at hs
      rw [← tbStmtsEqb_sound vtB_flatC] at hs
      obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hs
      exact vC j (List.mem_range.mp hj) s hs
    · exact g1912
    · exact g1926
    · exact g2021
  -- the totals
  have i1' : σv (.n 1301) = σv (.n 809) := by
    rw [(vt_readAt hl 1341 (d := .n 1301) (by decide +kernel) (by decide +kernel)
      (hidxσ 1 (by norm_num))).1, q1, i1]
  have i2' : σv (.n 1315) = σv (.n 837) := by
    rw [(vt_readAt hl 1356 (d := .n 1315) (by decide +kernel) (by decide +kernel)
      (hidxσ 2 (by norm_num))).1, q2, i2]
  have m0 : σv (.n 1306) = σv (.n 812) := by
    rw [(vt_readAt hl 1347 (d := .n 1306) (by decide +kernel) (by decide +kernel)
      (hpoolσ 0 (by norm_num))).1, x0]
  have m1 : σv (.n 1308) = σv (.n 816) := by
    rw [(vt_readAt hl 1349 (d := .n 1308) (by decide +kernel) (by decide +kernel)
      (hpoolσ 1 (by norm_num))).1, x1]
  have t0 : σv (.n 2441) = D.leaves.getD 0 0 :=
    (vt_readAt hl 2488 (d := .n 2441) (by decide +kernel) (by decide +kernel)
      (hleavesσ 0 (by norm_num))).1
  have t1 : σv (.n 2487) = D.leaves.getD 1 0 :=
    (vt_readAt hl 2534 (d := .n 2487) (by decide +kernel) (by decide +kernel)
      (hleavesσ 1 (by norm_num))).1
  have t2 : σv (.n 2542) = D.leaves.getD 2 0 :=
    (vt_readAt hl 2589 (d := .n 2542) (by decide +kernel) (by decide +kernel)
      (hleavesσ 2 (by norm_num))).1
  obtain ⟨d810, d815, d819, d838, d1293, d1294, d1299, d1313, d1436, d1305, d1307, d1309,
    d1319⟩ := vtP_fw_copies hP
  have hpw' : ∀ t < 6, paddingWeight (D.point.take (vtHt D.rows t)) (vtRw D.rows t) =
      σv (.n (vtPadV t)) := fun t ht ↦ (hpw t ht).symm
  have e0 := vt_total0 hbc D.weights (σv (.n 14)) D.point [σv (.n 812), σv (.n 816)]
    (σv (.n 1840)) (σv (.n 2441)) _ _ _ (fun c ↦ σv (.n c)) (fun t ↦ σv (.n (vtPadV t)))
    s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi) hpw' hr
  have e1 := vt_total1 hbc D.weights (σv (.n 14)) D.point [σv (.n 812), σv (.n 816)]
    (σv (.n 1302)) (σv (.n 1316)) (σv (.n 1840)) (σv (.n 2441)) (σv (.n 2487)) _ _ _
    (fun c ↦ σv (.n c)) (fun t ↦ σv (.n (vtPadV t))) s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi)
    hpw' hr
  have e2 := vt_total2 (bc := D.bc) (lm := D.lm) D.weights (σv (.n 14)) D.point
    [σv (.n 812), σv (.n 816)] (σv (.n 1302)) (σv (.n 1316)) (σv (.n 1840))
    (σv (.n 2441)) (σv (.n 2487)) (σv (.n 2542)) (fun c ↦ σv (.n c)) (fun t ↦ σv (.n (vtPadV t))) W
    (fun i hi ↦ hSC i hi) hpw' hr
  have hpad := vtP_push_pad hP hw
  rw [vtP_beta1 hP] at hpad
  have hfp : ∀ (L : Layout), L.logMemory = D.lm → L.logBytecode = 19 →
      vtFpPush L D.weights D.point [σv (.n 812), σv (.n 816)] (σv (.n 1840)) =
        [W 0 + W 1 + W 2, W 0 * gen + W 1 * σv (.n 809) + W 2 + W 3 * σv (.n 812) +
          W 4 * σv (.n 816), W 0 * gen ^ 2 + W 1 * σv (.n 837) + W 2 + σv (.n 1840)] ∧
      vtFpPull L D.weights D.point [σv (.n 812), σv (.n 816)] (σv (.n 1302)) (σv (.n 1316))
          (σv (.n 1840)) =
        [W 0 + W 1 * vtWFinalPc + W 2, W 0 * gen + W 1 * σv (.n 809) + W 2 * σv (.n 1302) +
          W 3 * σv (.n 812) + W 4 * σv (.n 816),
          W 0 * gen ^ 2 + W 1 * σv (.n 837) + W 2 * σv (.n 1316) + σv (.n 1840)] := by
    intro L hL1 hL2
    simp only [vtFpPush, vtFpPull, fingerprints, hL1, hL2, vt_take3 D.weights (by omega),
      vt_take5 D.weights (by omega), ← i1, ← i2, vtWFinalPc_eq, dot, List.zipWith_cons_cons,
      List.zipWith_nil_left, List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append,
      sepState, sepMem, sepBytecode, Verifier.gpow, pow_zero, hWd]
    refine ⟨?_, ?_⟩ <;> simp only [List.cons.injEq, and_true] <;> refine ⟨?_, ?_, ?_⟩ <;> ring
  obtain ⟨fP, fQ⟩ := hfp (layoutOf D.bc D.lm D.rows) (vt_layout_logMemory D.bc D.lm D.rows)
    (vt_layout_logBytecode D.bc D.lm D.rows hbc)
  have T0 : σv (.n 2442) = (vtAcc0 (layoutOf D.bc D.lm D.rows) D.weights (σv (.n 14)) D.point
      [σv (.n 812), σv (.n 816)] (σv (.n 1840)) (σv (.n 2441))).2 := by
    rw [e0, fP, vtP_push_total hP, vtP_push_fw hP hw, hpad, vtP_push_sel hP, hsum, d810, d815,
      d819, d838, d1293, d1843, c0, c1, c2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  have T1 : σv (.n 2488) = (vtAcc1 (layoutOf D.bc D.lm D.rows) D.weights (σv (.n 14)) D.point
      [σv (.n 812), σv (.n 816)] (σv (.n 1302)) (σv (.n 1316)) (σv (.n 1840))
      (σv (.n 2441)) (σv (.n 2487))).2 := by
    rw [e1, fQ, vtP_pull_total hP, vtP_pull_fw hP hw, hpad, vtP_pull_sel hP, d1294, d1299, d1313,
      d1436, d1305, d1307, d1309, d1319, i1', i2', m0, m1, d1843, c0, c1, c2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  have T2 : σv (.n 2543) = (vtAcc2 (layoutOf D.bc D.lm D.rows) D.weights (σv (.n 14)) D.point
      [σv (.n 812), σv (.n 816)] (σv (.n 1302)) (σv (.n 1316)) (σv (.n 1840))
      (σv (.n 2441)) (σv (.n 2487)) (σv (.n 2542))).2 := by
    rw [e2, vtP_count_total hP, vtP_count_pad hP W, vtP_count_sel hP, hsumC]
    ring
  simp only [x0, x1, x2, x3, e1840, t0, t1, t2, p 14 (by norm_num)] at T0 T1 T2
  have h1897 : σv (.n 1897) = σv (.n 5) * gen ^ 13 := by rw [e1897, p 5 (by norm_num)]
  exact ⟨hall, vtB_loadsInBuf _ h1897, hxs, e1840, e1905, ecap3, e1897, T0, T1, T2, s0, s1, s2,
    c0, c1, c2, hS, hSC⟩

end

end
end LeanVM.Guest.B1.Tables
