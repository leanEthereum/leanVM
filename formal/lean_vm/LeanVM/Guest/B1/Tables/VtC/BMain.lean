/-
  LeanVM.Guest.B1.Tables.VtC.BMain

  **`verify_tables`' bus sides complete** (statements `769 ..< 2589`).
-/

module

public import LeanVM.Guest.B1.Tables.VtC.BAll

/-!
# The bus sides, complete

`vtB_complete`: under `VtBHyp`, every statement of `769 ..< 2589` holds on the honest valuation,
every load reads inside `vtBufsB`, the framework words are the cursor's, the selectors are the
blocks' `blockSel`, and the three bus totals are `vtAcc0/1/2`'s (as `vt_asm_totals`).
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
    ((vtPre.drop 943).take 490) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtB_flatC : tbStmtsEqb ((List.range 45).flatMap fun i ↦ vtSelT
    (vtCountSel.getD i default).2.2.1 (vtCountSel.getD i default).1
    (vtCountSel.getD i default).2.2.2.1 (vtCountSel.getD i default).2.2.2.2.1
    (vtCountSel.getD i default).2.2.2.2.2.1 (vtCountSel.getD i default).2.2.2.2.2.2.1
    (vtCountSel.getD i default).2.2.2.2.2.2.2)
    ((vtPre.drop 2100).take 433) = true := by simp only [vtPre_drop]; decide +kernel

theorem vtB_fs_checks :
    tbStmtsEqb (fsNextT (.n 5) 0 830) ((vtPre.drop 817).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 1 843) ((vtPre.drop 830).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 2 856) ((vtPre.drop 843).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 3 1843) ((vtPre.drop 1881).take 9) = true ∧
    tbStmtsEqb (fsNextT (.n 5) 4 1898) ((vtPre.drop 1924).take 9) = true := by
      simp only [vtPre_drop]; decide +kernel

theorem vtB_fs_reads : Atom.load (.n 830) (.n 5) 0 ∉ vtSL ∧ Atom.load (.n 843) (.n 5) 1 ∉ vtSL ∧
    Atom.load (.n 856) (.n 5) 2 ∉ vtSL ∧ Atom.load (.n 1843) (.n 5) 3 ∉ vtSL ∧
    Atom.load (.n 1898) (.n 5) 4 ∉ vtSL := by decide +kernel

theorem vtB_index_stmts :
    tbStmtsEqb [.dispatch (.n 29) vtImNames [.n 8] [.n 824]] ((vtPre.drop 810).take 1) = true ∧
    tbStmtsEqb [.dispatch (.n 876) vtImNames [.n 8] [.n 894]] ((vtPre.drop 880).take 1) = true :=
  by simp only [vtPre_drop]; decide +kernel

theorem vtB_list5 (l : List E) (h : l.length = 5) :
    [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0] = l := by
  match l, h with
  | [_, _, _, _, _], _ => rfl

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
/-- **`verify_tables`' bus sides complete** (statements `769 ..< 2589`). -/
theorem vtB_complete {D : VtBIn} (H : VtBHyp rd wo args D) :
    (∀ s ∈ (vtPre.drop 769).take 1820, VSH (coreProgram.Rel rd) rd σv s) ∧
      LoadsInBuf σv (vtBufsB σv) ((vtPre.drop 769).take 1820) ∧
      vtFreshWords σv = D.xs ∧
      σv (.n 1820) = (vtAcc0 (layoutOf D.bc D.lm D.rows) D.alphas (σv (.n 14)) D.point
        [σv (.n 830), σv (.n 843), σv (.n 856)] (σv (.n 581)) (σv (.n 25))).2 ∧
      σv (.n 2073) = (vtAcc1 (layoutOf D.bc D.lm D.rows) D.alphas (σv (.n 14)) D.point
        [σv (.n 830), σv (.n 843), σv (.n 856)] (σv (.n 1843)) (σv (.n 1898)) (σv (.n 581))
        (σv (.n 25)) (σv (.n 26))).2 ∧
      σv (.n 2515) = (vtAcc2 (layoutOf D.bc D.lm D.rows) D.alphas (σv (.n 14)) D.point
        [σv (.n 830), σv (.n 843), σv (.n 856)] (σv (.n 1843)) (σv (.n 1898)) (σv (.n 581))
        (σv (.n 25)) (σv (.n 26)) (σv (.n 27))).2 ∧
      σv (.n 794) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 0 D.point ∧
      σv (.n 817) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 1 D.point ∧
      σv (.n 887) = blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length 2 D.point ∧
      σv (.n 796) = σv (.n 794) ∧ σv (.n 820) = σv (.n 817) ∧ σv (.n 890) = σv (.n 887) ∧
      (∀ i < 51, σv (.n (vtPushPadData.getD i default).2.2.1) =
        blockSel (vtSizesP D.lm (vtHt D.rows)) D.point.length (3 + i) D.point) ∧
      (∀ i < 45, σv (.n (vtCountPadData.getD i default).2.2.1) =
        blockSel (vtSizesC (vtHt D.rows)) D.point.length i D.point) := by
  obtain ⟨hl, hlow, hml, hlmμ, h19, hr, hτμ, hmu, hz, hal, hW, hxl, hcur, hpool, hcan, e20, ekb,
    eoP, eoC, eSh, e668, e703, e705, e706, hpw, hidxc, hz1, hrun, hidxB, hfitP, hfitC, hbitsF,
    hdigP, hdigC, hwF, hwP, hwC, hwI, hbc⟩ := H
  have p : ∀ i < 20, σv (.n i) = args.getD i 0 := fun i hi ↦ vt_param hl hi
  -- the weights
  have hWl : (eqKernel D.alphas).length = 16 := by rw [vt_length_eqKernel, hal]; rfl
  set W : ℕ → E := fun i ↦ (eqKernel D.alphas).getD i 0 with hWd
  have hw : ∀ i < 16, LoadHolds rd (σv (.n 13)) i (W i) := fun i hi ↦ by
    rw [p 13 (by norm_num)]
    have := hW i (by omega)
    rwa [← List.getD_eq_getElem _ 0] at this
  have hWσ : TbReadsAt rd (σv (.n 13)) (eqKernel D.alphas) := by
    rw [p 13 (by norm_num)]; exact hW
  have hP := vtP_honest hl (by omega) hWσ
  -- the selectors
  obtain ⟨vF0, vF1, vF2, vP, vC, s0, s1, s2, c0, c1, c2, hS, hsum, hSC, hsumC⟩ :=
    vtc_sels (wo := wo) (lm := D.lm) (τ := vtHt D.rows) hl hlow (point := D.point)
      (by rw [p 9 (by norm_num)]; exact hmu) hml (by rw [e703]; exact hz1)
      (by rw [e668]; exact hidxc) hlmμ h19 hτμ ekb hfitP hfitC eoP eoC eSh
      (by rw [e705, e706]; exact hrun) hbitsF hdigP hdigC hwF hwP hwC
  -- the stream reads
  have hx : ∀ i < 5, LoadHolds rd (σv (.n 5)) i (D.xs.getD i 0) := fun i hi ↦ by
    rw [p 5 (by norm_num), List.getD_eq_getElem D.xs 0 (by omega : i < D.xs.length)]
    exact hcur i (by omega)
  obtain ⟨cF0, cF1, cF2, cF3, cF4⟩ := vtB_fs_checks
  obtain ⟨rF0, rF1, rF2, rF3, rF4⟩ := vtB_fs_reads
  obtain ⟨f0, x0, v0⟩ := vtc_fsNext hl cF0 rF0 (hx 0 (by norm_num))
  obtain ⟨f1, x1, v1⟩ := vtc_fsNext hl cF1 rF1 (hx 1 (by norm_num))
  obtain ⟨f2, x2, v2⟩ := vtc_fsNext hl cF2 rF2 (hx 2 (by norm_num))
  obtain ⟨f3, x3, v3⟩ := vtc_fsNext hl cF3 rF3 (hx 3 (by norm_num))
  obtain ⟨f4, x4, v4⟩ := vtc_fsNext hl cF4 rF4 (hx 4 (by norm_num))
  -- the index MLEs
  have k1 : σv (.n 29) = gen ^ D.lm := by simpa using ekb 1 (by norm_num)
  have k2 : σv (.n 876) = gen ^ 19 := by
    have e0 : σv (.n 28) = 1 := by simpa using ekb 0 (by norm_num)
    rw [vt_mulAt hl 863 (d := 876) (x := 28) (y := 875) (by norm_num) (by norm_num)
        (by decide +kernel), vt_constAt hl 862 (d := .n 875) (e := word 524288 0 0)
        (by decide +kernel), show (524288 : ℕ) = 2 ^ 19 by norm_num,
      tb_word_two_pow (by norm_num), e0, one_mul]
  have hz8 : TbReadsAt rd (σv (.n 8)) D.point := by rw [p 8 (by norm_num)]; exact hz
  obtain ⟨I1, i1⟩ := vtB_indexArm hl (vt_memAt 810 _ (vtAt_eqb vtB_index_stmts.1)) k1 (by omega)
    hlmμ hz8 hwI.1
  obtain ⟨I2, i2⟩ := vtB_indexArm hl (vt_memAt 880 _ (vtAt_eqb vtB_index_stmts.2)) k2
    (by norm_num) h19 hz8 hwI.2
  -- the buffers
  have e781 : σv (.n 781) = wo 781 := vt_allocAt hl 769 (k := 153) (by decide +kernel)
  have hidxσ : ∀ i < 3, LoadHolds rd (σv (.n 781)) i ((vtIdxBufW D.point D.lm).getD i 0) :=
    fun i hi ↦ by
      rw [e781, List.getD_eq_getElem _ _ (by simp [vtIdxBufW]; omega)]
      exact hidxB i (by simp [vtIdxBufW]; omega)
  have hpoolσ : ∀ i < 5, LoadHolds rd (σv (.n 15)) i (D.xs.getD i 0) := fun i hi ↦ by
    rw [p 15 (by norm_num)]; exact hpool i hi
  have q1 : (vtIdxBufW D.point D.lm).getD 1 0 = indexMle (D.point.take D.lm) := by
    simp [vtIdxBufW]
  have q2 : (vtIdxBufW D.point D.lm).getD 2 0 = indexMle (D.point.take 19) := by
    simp [vtIdxBufW]
  -- the stores
  have h811 : VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 824) (.n 781) 1)) :=
    vsh_store (hidxσ 1 (by norm_num)) (by rw [i1, q1])
  have h881 : VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n 894) (.n 781) 2)) :=
    vsh_store (hidxσ 2 (by norm_num)) (by rw [i2, q2])
  have hpS : ∀ (i b : ℕ), i < 5 → σv (.n b) = D.xs.getD i 0 →
      VSH (coreProgram.Rel rd) rd σv (.atom (.load (.n b) (.n 15) i)) :=
    fun i b hi he ↦ vsh_store (hpoolσ i hi) he
  -- the permutation
  have h1915 : VSH (coreProgram.Rel rd) rd σv (.atom (.keccak [.n 837, .n 839, .n 850, .n 852,
      .n 863, .n 865, .n 1850, .n 1852, .n 20, .n 21, .n 22, .n 23, .n 24] [.n 1885, .n 1886,
      .n 1887, .n 1888, .n 1889, .n 1890, .n 1891, .n 1892, .n 1893, .n 1894, .n 1895, .n 1896,
      .n 1897] false false)) := by
    have hg := vt_goodS (rd := rd) (w := wo) hl (vt_memAt 1923 (.atom (.keccak [.n 837, .n 839,
      .n 850, .n 852, .n 863, .n 865, .n 1850, .n 1852, .n 20, .n 21, .n 22, .n 23, .n 24]
      [.n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890, .n 1891, .n 1892, .n 1893, .n 1894,
      .n 1895, .n 1896, .n 1897] false false)) (by decide +kernel))
    rw [fixNe_atom] at hg
    refine holds_of_good (rd := rd) (σ := σv) (S := vtSL) (w := wo)
      (a := .keccak [.n 837, .n 839, .n 850, .n 852, .n 863, .n 865, .n 1850, .n 1852, .n 20,
        .n 21, .n 22, .n 23, .n 24] [.n 1885, .n 1886, .n 1887, .n 1888, .n 1889, .n 1890,
        .n 1891, .n 1892, .n 1893, .n 1894, .n 1895, .n 1896, .n 1897] false false) hg ?_
    show ∀ c : Fin 13, _
    intro c
    have k0 := fsPackVals_canonical (D.xs.getD 0 0) dsObserve
    have k1' := fsPackVals_canonical (D.xs.getD 1 0) dsObserve
    have k2' := fsPackVals_canonical (D.xs.getD 2 0) dsObserve
    have k3 := fsPackVals_canonical (D.xs.getD 3 0) dsObserve
    have hc : ∀ i < 5, IsCanonical128 (σv (.n (20 + i))) := fun i hi ↦ by
      rw [e20 i hi, p i (by omega)]; exact hcan i hi
    fin_cases c <;> simp [cells13]
    · rw [show 837 = 830 + 1 + 6 by rfl, v0 6 (by norm_num)]; exact k0.1
    · rw [show 839 = 830 + 1 + 8 by rfl, v0 8 (by norm_num)]; exact k0.2
    · rw [show 850 = 843 + 1 + 6 by rfl, v1 6 (by norm_num)]; exact k1'.1
    · rw [show 852 = 843 + 1 + 8 by rfl, v1 8 (by norm_num)]; exact k1'.2
    · rw [show 863 = 856 + 1 + 6 by rfl, v2 6 (by norm_num)]; exact k2'.1
    · rw [show 865 = 856 + 1 + 8 by rfl, v2 8 (by norm_num)]; exact k2'.2
    · rw [show 1850 = 1843 + 1 + 6 by rfl, v3 6 (by norm_num)]; exact k3.1
    · rw [show 1852 = 1843 + 1 + 8 by rfl, v3 8 (by norm_num)]; exact k3.2
    · exact hc 0 (by norm_num)
    · exact hc 1 (by norm_num)
    · exact hc 2 (by norm_num)
    · exact hc 3 (by norm_num)
    · exact hc 4 (by norm_num)
  -- the glue
  have g769 := vtB_glue_769 (rd := rd) (wo := wo) hl
  have g784 := vtB_glue_784 hl hw
  have g807 := vtB_glue_807 hl hw I1 h811
  have g826 := vtB_glue_826 hl hw (hpS 0 830 (by norm_num) x0)
  have g839 := vtB_glue_839 hl hw (hpS 1 843 (by norm_num) x1)
  have g852 := vtB_glue_852 hl hw (hpS 2 856 (by norm_num) x2)
  have g877 := vtB_glue_877 hl hw I2 h881
  have g1425 := vtB_glue_1433 hl hw hidxσ
  have g1882 := vtB_glue_1890 hl hw hpoolσ hidxσ (hpS 3 1843 (by norm_num) x3) h1915
  have g1925 := vtB_glue_1933 hl hw (hpS 4 1898 (by norm_num) x4)
  have g2517 := vtB_glue_2533 (rd := rd) (wo := wo) hl
  -- every statement
  have hall : ∀ s ∈ (vtPre.drop 769).take 1820, VSH (coreProgram.Rel rd) rd σv s := by
    refine vtB_cover [3, 12, 10, 13, 10, 9, 4, 9, 4, 9, 12, 13, 66, 490, 448, 9, 34, 9, 167, 433,
      56] 769 fun i hi ↦ ?_
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · exact g769
    · exact vtB_tmplAt vtFw0_check vF0
    · exact g784
    · exact vtB_tmplAt vtFw1_check vF1
    · exact g807
    · exact vtB_tmpl cF0 f0
    · exact g826
    · exact vtB_tmpl cF1 f1
    · exact g839
    · exact vtB_tmpl cF2 f2
    · exact g852
    · exact vtB_tmplAt vtFw2_check vF2
    · exact g877
    · intro s hs
      change s ∈ (vtPre.drop 943).take 490 at hs
      rw [← tbStmtsEqb_sound vtB_flatP] at hs
      obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hs
      exact vP j (List.mem_range.mp hj) s hs
    · exact g1425
    · exact vtB_tmpl cF3 f3
    · exact g1882
    · exact vtB_tmpl cF4 f4
    · exact g1925
    · intro s hs
      change s ∈ (vtPre.drop 2100).take 433 at hs
      rw [← tbStmtsEqb_sound vtB_flatC] at hs
      obtain ⟨j, hj, hs⟩ := List.mem_flatMap.mp hs
      exact vC j (List.mem_range.mp hj) s hs
    · exact g2517
  -- the totals
  have i1' : σv (.n 1839) = σv (.n 824) := by
    rw [(vt_readAt hl 1877 (d := .n 1839) (by decide +kernel) (by decide +kernel)
      (hidxσ 1 (by norm_num))).1, q1, i1]
  have i2' : σv (.n 1881) = σv (.n 894) := by
    rw [(vt_readAt hl 1919 (d := .n 1881) (by decide +kernel) (by decide +kernel)
      (hidxσ 2 (by norm_num))).1, q2, i2]
  have m0 : σv (.n 1856) = σv (.n 830) := by
    rw [(vt_readAt hl 1894 (d := .n 1856) (by decide +kernel) (by decide +kernel)
      (hpoolσ 0 (by norm_num))).1, x0]
  have m1 : σv (.n 1860) = σv (.n 843) := by
    rw [(vt_readAt hl 1898 (d := .n 1860) (by decide +kernel) (by decide +kernel)
      (hpoolσ 1 (by norm_num))).1, x1]
  have m2 : σv (.n 1864) = σv (.n 856) := by
    rw [(vt_readAt hl 1902 (d := .n 1864) (by decide +kernel) (by decide +kernel)
      (hpoolσ 2 (by norm_num))).1, x2]
  have hb1 : σv (.n 783) = σv (.n 14) + 1 := by
    rw [vt_addAt hl 771 (d := .n 783) (x := .n 14) (y := .n 782) (by decide +kernel),
      vt_constAt hl 770 (d := .n 782) (e := word 1 0 0) (by decide +kernel), tb_word_one]
  have hpv : σv (.n 1820) = σv (.n 955) + σv (.n 1815) + (1 + σv (.n 1393)) + σv (.n 25) := by
    rw [vt_addAt hl 1858 (d := .n 1820) (x := .n 1819) (y := .n 25) (by decide +kernel),
      vt_addAt hl 1857 (d := .n 1819) (x := .n 1816) (y := .n 1818) (by decide +kernel),
      vt_addAt hl 1856 (d := .n 1818) (x := .n 1817) (y := .n 1393) (by decide +kernel),
      vt_constAt hl 1855 (d := .n 1817) (e := word 1 0 0) (by decide +kernel),
      vt_addAt hl 1854 (d := .n 1816) (x := .n 955) (y := .n 1815) (by decide +kernel),
      tb_word_one]
  have hpw' : ∀ t < 6, paddingWeight (D.point.take (vtHt D.rows t)) (vtRw D.rows t) =
      σv (.n (vtPadV t)) := fun t ht ↦ (hpw t ht).symm
  have e0 := vt_total0 hbc D.alphas (σv (.n 14)) D.point [σv (.n 830), σv (.n 843), σv (.n 856)]
    (σv (.n 581)) (σv (.n 25)) _ _ _ (fun c ↦ σv (.n c)) (fun t ↦ σv (.n (vtPadV t)))
    s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi) hpw' hr
  have e1 := vt_total1 hbc D.alphas (σv (.n 14)) D.point [σv (.n 830), σv (.n 843), σv (.n 856)]
    (σv (.n 1843)) (σv (.n 1898)) (σv (.n 581)) (σv (.n 25)) (σv (.n 26)) _ _ _
    (fun c ↦ σv (.n c)) (fun t ↦ σv (.n (vtPadV t))) s0.symm s1.symm s2.symm (fun i hi ↦ hS i hi)
    hpw' hr
  have e2 := vt_total2 (bc := D.bc) (lm := D.lm) D.alphas (σv (.n 14)) D.point
    [σv (.n 830), σv (.n 843), σv (.n 856)] (σv (.n 1843)) (σv (.n 1898)) (σv (.n 581))
    (σv (.n 25)) (σv (.n 26)) (σv (.n 27)) (fun c ↦ σv (.n c)) (fun t ↦ σv (.n (vtPadV t))) W
    (fun i hi ↦ hSC i hi) hpw' hr
  have hpush := vtP_push_total hP hw
  have hfw := vtP_push_fw hP hw
  rw [hb1] at hpush
  have hpad : σv (.n 1815) = vtPadSum (fun c ↦ σv (.n c)) (fun t ↦ σv (.n (vtPadV t))) W
      (σv (.n 14) + 1) vtPushPadData := by
    have := hpv.symm.trans hpush
    linear_combination this
  have hfp : ∀ (L : Layout), L.logMemory = D.lm → L.logBytecode = 19 →
      vtFpPush L D.alphas D.point [σv (.n 830), σv (.n 843), σv (.n 856)] (σv (.n 581)) =
        [W 0 + W 1 + W 2, W 0 * gen + W 1 * σv (.n 824) + W 2 + W 3 * σv (.n 830) +
          W 4 * σv (.n 843) + W 5 * σv (.n 856), W 0 * gen ^ 2 + W 1 * σv (.n 894) + W 2 +
          σv (.n 581)] ∧
      vtFpPull L D.alphas D.point [σv (.n 830), σv (.n 843), σv (.n 856)] (σv (.n 1843))
          (σv (.n 1898)) (σv (.n 581)) =
        [W 0 + W 1 * vtWFinalPc + W 2, W 0 * gen + W 1 * σv (.n 824) + W 2 * σv (.n 1843) +
          W 3 * σv (.n 830) + W 4 * σv (.n 843) + W 5 * σv (.n 856),
          W 0 * gen ^ 2 + W 1 * σv (.n 894) + W 2 * σv (.n 1898) + σv (.n 581)] := by
    intro L hL1 hL2
    simp only [vtFpPush, vtFpPull, fingerprints, hL1, hL2, vt_take3 (eqKernel D.alphas) (by omega),
      vt_take6 (eqKernel D.alphas) (by omega), ← i1, ← i2, vtWFinalPc_eq, dot,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
      List.cons_append, List.nil_append, sepState, sepMem, sepBytecode, Verifier.gpow, pow_zero]
    refine ⟨?_, ?_⟩ <;> simp only [List.cons.injEq, and_true] <;> refine ⟨?_, ?_, ?_⟩ <;> ring
  obtain ⟨fP, fQ⟩ := hfp (layoutOf D.bc D.lm D.rows) (vt_layout_logMemory D.bc D.lm D.rows)
    (vt_layout_logBytecode D.bc D.lm D.rows hbc)
  have hfresh : vtFreshWords σv = D.xs := by
    show [σv (.n 830), σv (.n 843), σv (.n 856), σv (.n 1843), σv (.n 1898)] = D.xs
    rw [x0, x1, x2, x3, x4]
    exact vtB_list5 D.xs hxl
  refine ⟨hall, vtB_loadsInBuf _, hfresh, ?_, ?_, ?_, s0, s1, s2, c0, c1, c2, hS, hSC⟩
  · rw [e0, fP, hpush, hfw, hsum]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e1, fQ, vtP_pull_total hP hw, hpad, c0, c1, c2, i1', i2', m0, m1, m2]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring
  · rw [e2, vtP_count_total hP W, hsumC]
    ring

end

end
end LeanVM.Guest.B1.Tables
