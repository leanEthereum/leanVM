/-
  LeanVM.Guest.B1.VsC.VsNatIr

  The link section's reads at the honest context are the native link's values, and the evaluation memory holds the
  node's own words, both without `Hon`.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatHid

/-!
# The link section's reads, natively

* **`VsCtx.holdsWords_rd0B`**: `rd0` holds the node's own words `Wo`, from the placement and the buffers' sizes
  (`holdsWords_rd0` without `Hon`).
* **`VsCtx.irReads_nat`**: `Link.Arith.IRReads x.rd0 x.σ0 (tailIn …)` at the native link's values, from the placement,
  the sizes, a causal return rule, the front's facts (`VsFsChecks1`, `Bw1`, `Num6`), the honest buffers (`BwNat`,
  buffer `8` the fresh claim's values) and returns (`honRet`, `Ret3`). Each read is a buffer's word (`.n 10`, `.n 11`,
  `.n 14`, `.n 17`, `.n 13`, `.n 18`), the stream's (`.n 1076`, `.n 772`), a callee's return (`state_ends`,
  `index_side`, the six `table_point`s, `tablePoint_forms`) or the fresh permutation's cell (window `13`'s `KECCAK`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link.Arith (tailRowSide tailLets tailIn layoutOf rdw IRReads omegaVn cornerVn)

@[expose] public section

/-! ## The evaluation memory holds the own words, from the sizes -/

namespace VsCtx

variable {x : VsCtx}

theorem top_ltB (hok : x.Ok) : x.cur + (vsAllocSz x.p).sum < 2 ^ 60 + 2 ^ 14 := by
  have := VsCtx.p_le32 hok; have := hok.hcur; rw [vsAllocSz_sum]; omega

theorem base_ltB (j : ℕ) (hj : j < 24) :
    x.cur ≤ x.base j ∧ x.base j + (vsAllocSz x.p).getD j 0 ≤ x.cur + (vsAllocSz x.p).sum :=
  bases_getD_in x.cur (vsAllocSz x.p) j (by rw [vsAllocSz_length]; exact hj)

theorem Lw_getDB (hbw : x.bw.map List.length = vsAllocSz x.p) {j : ℕ} (hj : j < 24) :
    x.Lw.getD j [] = if j = 13 then x.cells19.map Prod.snd else x.bw.getD j [] := by
  have hl := VsCtx.bwlen hbw
  by_cases e : j = 13
  · subst e
    simp [Lw, List.getD_eq_getElem?_getD, hl]
  · simp only [e, ↓reduceIte]
    rw [Lw, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm e), ← List.getD_eq_getElem?_getD]

theorem Lw_sizesB (hbw : x.bw.map List.length = vsAllocSz x.p) : x.Lw.map List.length = vsAllocSz x.p := by
  rw [Lw, List.map_set, hbw, List.length_map, cells19_length]
  rfl

theorem rd0_run13B (hok : x.Ok) {k : ℕ} (hk' : k < 12) :
    x.rd0 (addressOfIndex (x.base 13 + k)) = some ((x.cells19.map Prod.snd).getD k 0) := by
  have ht := top_ltB hok
  have h13 := vsAllocSz_13 x.p
  have hb13 := base_ltB (x := x) 13 (by omega)
  have hb : ∀ q ∈ vsCells19 (x.base 13) (vsVal x.rd1 x.w x.args), q.1 < 2 ^ 64 - 1 :=
    vsCells19_lt (by omega)
  have hv := vsCells19_getD (x.base 13) (vsVal x.rd1 x.w x.args) hk'
  rw [cells19, hv]
  exact rdSet_of_mem (rd := x.rd1) (vsCells19_nodup _ _) hb (vsCells19_mem _ _ hk')

theorem rd0_runNeB (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) {j : ℕ} (hj : j < 24) (e13 : j ≠ 13)
    {k : ℕ} (hk : k < (vsAllocSz x.p).getD j 0) :
    x.rd0 (addressOfIndex (x.base j + k)) = some ((x.bw.getD j []).getD k 0) := by
  have ht := top_ltB hok
  have hl := VsCtx.bwlen hbw
  have h13 := vsAllocSz_13 x.p
  have hbj := base_ltB (x := x) j hj
  have hb13 := base_ltB (x := x) 13 (by omega)
  have hjl : j < (bases x.cur (vsAllocSz x.p)).length := by rw [bases_length, vsAllocSz_length]; exact hj
  have hmem : (x.base j, x.bw.getD j []) ∈ vsRuns x.cur x.bw := by
    rw [vsRuns, hbw]
    have := List.getElem_mem (l := (bases x.cur (vsAllocSz x.p)).zip x.bw)
      (by rw [List.length_zip, bases_length, vsAllocSz_length, hl]; omega : j < _)
    rw [List.getElem_zip] at this
    rwa [base, List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ (by omega)]
  have hsz : (x.bw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
    rw [← hbw, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
      List.getElem_map]
  have hW := holdsWords_rdW (bases_zip_pairwise x.cur x.bw) (fun q hq => by
    have := bases_zip_in x.cur x.bw q hq; rw [hbw] at this; omega) _ hmem k (by rw [hsz]; exact hk)
  have h2 := hW.2
  rw [Main.addr_ofK] at h2
  have e1 : x.rd1 (addressOfIndex (x.base j + k)) = some ((x.bw.getD j []).getD k 0) := by
    rw [List.getD_eq_getElem _ _ (by rw [hsz]; exact hk)]
    exact rd1_of_rdW h2
  rw [← e1]
  refine rdSet_of_not fun q hq he => ?_
  simp only [cells19, vsCells19, List.mem_map, List.mem_range] at hq
  obtain ⟨t, ht', rfl⟩ := hq
  simp only at he
  have := addr_inj (by omega) (by omega) he
  rcases Nat.lt_or_gt_of_ne e13 with hlt | hlt
  · have := bases_getD_lt x.cur (vsAllocSz x.p) j 13 hlt (by rw [vsAllocSz_length]; omega)
    simp only [base] at *
    omega
  · have := bases_getD_lt x.cur (vsAllocSz x.p) 13 j hlt (by rw [vsAllocSz_length]; omega)
    simp only [base] at *
    omega

theorem rd0_runB (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) {j : ℕ} (hj : j < 24) {k : ℕ}
    (hk : k < (vsAllocSz x.p).getD j 0) :
    x.rd0 (addressOfIndex (x.base j + k)) = some ((x.Lw.getD j []).getD k 0) := by
  rw [Lw_getDB hbw hj]
  by_cases e13 : j = 13
  · subst e13
    simp only [↓reduceIte]
    exact rd0_run13B hok (by rw [vsAllocSz_13] at hk; exact hk)
  · simp only [e13, ↓reduceIte]
    exact rd0_runNeB hok hbw hj e13 hk

/-- **The evaluation memory holds the own words**, from the placement and the buffers' sizes. -/
theorem holdsWords_rd0B (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) : HoldsWords x.rd0 x.Wo := by
  have hbl : (bases x.cur (vsAllocSz x.p)).length = 24 := by rw [bases_length, vsAllocSz_length]
  have hLl : x.Lw.length = 24 := by rw [Lw, List.length_set, VsCtx.bwlen hbw]
  rintro ⟨b, l⟩ hq k hk
  have hWo : x.Wo = (bases x.cur (vsAllocSz x.p)).zip x.Lw := rfl
  rw [hWo, List.mem_iff_getElem] at hq
  obtain ⟨j, hj, hq⟩ := hq
  rw [List.getElem_zip, Prod.mk.injEq] at hq
  have hj' : j < 24 := by rw [List.length_zip, hbl, hLl] at hj; omega
  obtain ⟨e1, e2⟩ := hq
  have eb : b = x.base j := by rw [← e1, base, List.getD_eq_getElem _ _ (by omega)]
  have el : l = x.Lw.getD j [] := by rw [← e2, List.getD_eq_getElem _ _ (by omega)]
  subst eb el
  simp only at hk ⊢
  have hsz : (x.Lw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
    rw [← Lw_sizesB hbw, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
      List.getElem_map]
  refine ⟨Value.ofK_isInK _, ?_⟩
  rw [Main.addr_ofK, rd0_runB hok hbw hj' (by rw [← hsz]; exact hk), List.getD_eq_getElem _ _ hk]

end VsCtx

/-! ## Lists -/

theorem rdw_reads {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ} (hk : k < xs.length) :
    rdw rd p k = xs.getD k 0 := by
  rw [Link.Arith.rdw_of_load (h k hk), List.getD_eq_getElem _ _ hk]

theorem padTo_getD {n i : ℕ} {l : List E} (hi : i < l.length) : (padTo n l).getD i 0 = l.getD i 0 := by
  rw [padTo, List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

theorem padTo_take_le {n k : ℕ} {l : List E} (h : k ≤ l.length) : (padTo n l).take k = l.take k := by
  rw [padTo, List.take_append_of_le_length h]

theorem rangeMap_getD (f : ℕ → E) {n i : ℕ} (hi : i < n) : ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

/-! ## `tailLets`' slices at any layout of `tables()` -/

section
variable {layout : Layout} {chunks : Chunks} {theta0 : E} {drawn r : List E} {m1 : E} {fresh : List E}
  {split : Split} {qPoint : List E}

theorem lets_theta' (htab : layout.tables = tables) (hd : 88 ≤ drawn.length) :
    (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).theta =
      theta0 :: (List.range 5).map (drawn.getD · 0) := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  exact Link.Arith.lets_theta hd

theorem lets_slot' (htab : layout.tables = tables) (hd : 88 ≤ drawn.length) :
    (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).slot =
      eqKernel ((List.range 4).map fun i ↦ drawn.getD (49 + i) 0) := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  exact Link.Arith.lets_slot hd

theorem lets_tau' (htab : layout.tables = tables) (hd : 88 ≤ drawn.length) :
    (tailLets layout chunks theta0 drawn r m1 fresh split qPoint).tau =
      (drawn.drop 88).take (layout.tableLogHeights.foldl max 0) := by
  obtain ⟨lm, lb, bc, tbls, rows, pl, sl, hts⟩ := layout
  simp only at htab
  subst htab
  exact Link.Arith.lets_tau hd

end

/-! ## The section's atoms on the forward valuation -/

set_option maxRecDepth 200000 in
theorem vsC_irMuls : ([.mul (.n 801) (.n 13) (.n 101), .mul (.n 1299) (.n 18) (.n 115),
    .mul (.n 1411) (.n 18) (.n 116), .mul (.n 1532) (.n 18) (.n 117), .mul (.n 1615) (.n 18) (.n 118),
    .mul (.n 1742) (.n 18) (.n 119), .mul (.n 1888) (.n 18) (.n 120)] : List Atom).all
      (fun a => (atomsOf ((vsC.drop 270).take 1200)).contains a) = true := by
  decide +kernel

section
variable {x : VsCtx} {L : LinkNat}

theorem VsCtx.irMul {d a b : ℕ} (hm : Atom.mul (.n d) (.n a) (.n b) ∈ ([.mul (.n 801) (.n 13) (.n 101),
    .mul (.n 1299) (.n 18) (.n 115), .mul (.n 1411) (.n 18) (.n 116), .mul (.n 1532) (.n 18) (.n 117),
    .mul (.n 1615) (.n 18) (.n 118), .mul (.n 1742) (.n 18) (.n 119), .mul (.n 1888) (.n 18) (.n 120)] : List Atom))
    (ha : a < d) (hb : b < d) : x.σ0 (.n d) = x.σ0 (.n a) * x.σ0 (.n b) := by
  have hc := List.all_eq_true.mp vsC_irMuls _ hm
  have hg := vsC_atoms_good (rd0 := x.rd0) (w := x.w) (rfl : x.args.length = 6) 270 1200 _
    (by simpa using hc)
  exact good_mulF hg ha hb

/-- Buffer `j`'s pointer `.n (j + 6)`. -/
theorem VsCtx.ptrBuf (hret : CausalRule x.ret) {j i : ℕ} (hi : j + 6 = i) (hj : j < 18) :
    x.σ0 (.n i) = ptrAt (x.base j) := by
  subst hi
  have e := vsW_alloc (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) rfl hret (j := j) (by omega)
  rw [vsAllocIdx_getD hj] at e
  have hm : Atom.hint (.alloc (.n (j + 6)) (vsSz0.getD j 0)) ∈ vsW0 := by
    interval_cases j <;> simp [vsW0, vsW0a, vsSz0]
  exact (vsW0_good (rd0 := x.rd0) (w := x.w) (rfl : x.args.length = 6) hm).trans e

/-- **A buffer's word through its pointer**, on `rd0`. -/
theorem VsCtx.rdBuf (hret : CausalRule x.ret) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hW : HoldsWords x.rd0 x.Wo) {j i : ℕ} (hi : j + 6 = i) (hj : j < 18) (h13 : j ≠ 13) {k : ℕ}
    (hk : k < (x.bw.getD j []).length) : rdw x.rd0 (x.σ0 (.n i)) k = (x.bw.getD j []).getD k 0 := by
  rw [x.ptrBuf hret hi hj]
  exact rdw_reads (hW _ (VsCtx.memWo hbw (by omega) h13)) hk

/-- A return of `verify_sub`'s callees: the oracle's word, `ret`'s constant. -/
theorem VsCtx.wRet (hret : CausalRule x.ret) {i : ℕ} (hi : vsPlain i) {c : E} (hc : ∀ σ, x.ret i σ = c) : x.w i = c :=
  vsW_retC (rfl : x.args.length = 6) hret hi hc

/-- Table `t ≥ 1`'s `table_point` returns, its statement's values `d + 5 …` (`d = tpD t`). -/
theorem VsCtx.tpRetK (hret : CausalRule x.ret) (h3 : x.Ret3) {t d : ℕ} (h1 : 1 ≤ t) (h5 : t ≤ 5) (hd : tpD t = d)
    (hr : ∀ v ∈ [V.n (d + 5), .n (d + 6), .n (d + 7)], x.σ0 v = x.w v.idx)
    (p5 : vsPlain (d + 5)) (p6 : vsPlain (d + 6)) (p7 : vsPlain (d + 7)) :
    x.σ0 (.n (d + 5)) = (x.bw.getD 4 []).getD t 0 * Link.tpTotalG (((x.bw.getD 4 []).drop 89).take (x.hgS t))
      ((x.bw.getD 9 []).take (x.hgS t)) (((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t))
      ((x.bw.getD 1 []).getD (26 * t + x.hgS t) 0) (x.hgS t) ∧
    x.σ0 (.n (d + 6)) = 1 + (1 + (x.bw.getD 1 []).getD (26 * t + x.hgS t) 0) *
      Link.tpPad (((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t)) ((x.bw.getD 9 []).take (x.hgS t)) ∧
    x.σ0 (.n (d + 7)) = Link.tpFullAt (((x.bw.getD 4 []).drop 89).take (x.hgS t))
      ((x.bw.getD 9 []).take (x.hgS t)) (x.hgS t) := by
  subst hd
  have w5 := x.wRet hret p5 (fun σ => (h3.rtp t h1 h5 σ).1)
  have w6 := x.wRet hret p6 (fun σ => (h3.rtp t h1 h5 σ).2.1)
  have w7 := x.wRet hret p7 (fun σ => (h3.rtp t h1 h5 σ).2.2)
  exact ⟨(hr _ (by simp)).trans w5, (hr _ (by simp)).trans w6, (hr _ (by simp)).trans w7⟩

/-- **The six `table_point`s' returns**, as `ret` gives them (`Ret2`'s table `0`, `Ret3`'s tables `1 ..= 5`). -/
theorem VsCtx.tpRet (hret : CausalRule x.ret) (h2 : x.Ret2) (h3 : x.Ret3) {t : ℕ} (ht : t < 6) :
    x.σ0 (.n (omegaVn.getD t 0)) = (x.bw.getD 4 []).getD t 0 * Link.tpTotalG (((x.bw.getD 4 []).drop 89).take (x.hgS t))
      ((x.bw.getD 9 []).take (x.hgS t)) (((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t))
      ((x.bw.getD 1 []).getD (26 * t + x.hgS t) 0) (x.hgS t) ∧
    x.σ0 (.n (omegaVn.getD t 0 + 1)) = 1 + (1 + (x.bw.getD 1 []).getD (26 * t + x.hgS t) 0) *
      Link.tpPad (((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t)) ((x.bw.getD 9 []).take (x.hgS t)) ∧
    x.σ0 (.n (omegaVn.getD t 0 + 2)) = Link.tpFullAt (((x.bw.getD 4 []).drop 89).take (x.hgS t))
      ((x.bw.getD 9 []).take (x.hgS t)) (x.hgS t) := by
  have ha : x.args.length = 6 := rfl
  interval_cases t
  · have hr : ∀ v ∈ [V.n 1296, .n 1297, .n 1298], x.σ0 v = x.w v.idx :=
      vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC21_eq
    have w5 : x.w 1296 = _ := x.wRet hret (by decide) h2.r1296
    have w6 : x.w 1297 = _ := x.wRet hret (by decide) h2.r1297
    have w7 : x.w 1298 = _ := x.wRet hret (by decide) h2.r1298
    refine ⟨(hr (.n 1296) (by simp)).trans (w5.trans ?_), (hr (.n 1297) (by simp)).trans (w6.trans ?_),
      (hr (.n 1298) (by simp)).trans (w7.trans ?_)⟩
    all_goals (try simp only [Nat.mul_zero, Nat.zero_add, List.drop_zero])
    all_goals rfl
  · exact x.tpRetK hret h3 (d := 1403) (by norm_num) (by norm_num) rfl
      (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC23_eq) (by decide) (by decide) (by decide)
  · exact x.tpRetK hret h3 (d := 1524) (by norm_num) (by norm_num) rfl
      (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC25_eq) (by decide) (by decide) (by decide)
  · exact x.tpRetK hret h3 (d := 1607) (by norm_num) (by norm_num) rfl
      (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC27_eq) (by decide) (by decide) (by decide)
  · exact x.tpRetK hret h3 (d := 1734) (by norm_num) (by norm_num) rfl
      (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC29_eq) (by decide) (by decide) (by decide)
  · exact x.tpRetK hret h3 (d := 1880) (by norm_num) (by norm_num) rfl
      (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC31_eq) (by decide) (by decide) (by decide)

/-! ## The link section's reads -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **Window `13`'s cells** (vsnat2's `g2_of`, all thirteen): `.n 772` is `m1`'s cursor in the stream, and the
`KECCAK`'s first five outputs `782 ..= 786` are the native fresh coefficients. -/
theorem VsCtx.g2_cells {rest : List E} (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest)
    (hbits : L.bits x.lay ≠ 0) (hwd : L.chunks.width ≠ 0) (hlI : L.wsI.length = L.chunks.width * natRoundLen 1 0)
    (hret : CausalRule x.ret) (hb18 : x.bw.getD 18 [] = padStream x.c.proof.stream)
    (hrd0 : ReadsAt x.rd0 (ptrAt (x.base 18)) (x.bw.getD 18 []))
    (r767 : ∀ j < 7, ∀ σ, x.ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0) :
    x.σ0 (.n 772) = ptrAt (x.natB772 L) ∧ ReadsAt x.rd0 (ptrAt (x.natB772 L)) [L.m1] ∧
      ∀ k < 5, x.σ0 (.n (782 + k)) = (L.fresh x.lay x.nF).getD k 0 := by
  have ha : x.args.length = 6 := rfl
  have hσ : x.σ0 = vsVal x.rd0 x.w x.args := rfl
  rw [hσ]
  have hg := vsC_atoms_good (rd0 := x.rd0) (w := x.w) ha 259 11
  have hm : ∀ a ∈ ([.copy (.n 774) (.n 767), .copy (.n 775) (.n 768), .copy (.n 776) (.n 769),
      .copy (.n 777) (.n 770), .copy (.n 778) (.n 771), .load (.n 779) (.n 772) 0, .copy (.n 780) (.n 779),
      .const (.n 781) (word 0 1),
      .keccak [.n 780, .n 781, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 774, .n 775, .n 776, .n 777, .n 778]
        [.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792, .n 793, .n 794]
        false false] : List Atom), Good x.rd0 vsSL x.w (vsVal x.rd0 x.w x.args) a := fun a h =>
    hg a (by simpa using List.all_eq_true.mp vsC13_kAtoms a h)
  set σ := vsVal x.rd0 x.w x.args with hσσ
  have i3 : σ (.n 774) = σ (.n 767) := hm (.copy (.n 774) (.n 767)) (by simp)
  have i4 : σ (.n 775) = σ (.n 768) := hm (.copy (.n 775) (.n 768)) (by simp)
  have i5 : σ (.n 776) = σ (.n 769) := hm (.copy (.n 776) (.n 769)) (by simp)
  have i6 : σ (.n 777) = σ (.n 770) := hm (.copy (.n 777) (.n 770)) (by simp)
  have i7 : σ (.n 778) = σ (.n 771) := hm (.copy (.n 778) (.n 771)) (by simp)
  have i9 : σ (.n 780) = σ (.n 779) := hm (.copy (.n 780) (.n 779)) (by simp)
  have i10 : σ (.n 781) = word 0 1 := hm (.const (.n 781) (word 0 1)) (by simp)
  have z25 : σ (.n 25) = word 0 0 := vsW0_good (a := .const (.n 25) (word 0 0)) ha (by simp [vsW0, vsW0a])
  have z26 : σ (.n 26) = word 0 0 := vsW0_good (a := .const (.n 26) (word 0 0)) ha (by simp [vsW0, vsW0a])
  have z27 : σ (.n 27) = word 0 0 := vsW0_good (a := .const (.n 27) (word 0 0)) ha (by simp [vsW0, vsW0a])
  have z28 : σ (.n 28) = word 0 0 := vsW0_good (a := .const (.n 28) (word 0 0)) ha (by simp [vsW0, vsW0a])
  have hne : x.natLI L ≠ [] := natChain_ne hwd _ _
  have hcap : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cap.length = 5 := natChain_last_cap hwd _ _ _
  have hr : ∀ j < 7, σ (.n (767 + j)) = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cells.getD j 0 := fun j hj => by
    have e1 : σ (.n (767 + j)) = x.w (767 + j) :=
      vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC12_eq (.n (767 + j)) (by interval_cases j <;> simp)
    rw [e1]
    exact vsW_retC ha hret (by interval_cases j <;> decide) (r767 j hj)
  have hcur : (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cur = ptrAt (x.natB772 L) := by
    rw [chainLast_ne hne _ ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩, VsCtx.natLI, LinkNat.chainI, natChain_cur, ← hlI,
      ptrAt_add]
    rfl
  have e772 : σ (.n 772) = ptrAt (x.natB772 L) := by
    rw [show (772 : ℕ) = 767 + 5 from rfl, hr 5 (by norm_num), cells_getD_5 hcap, hcur]
  obtain ⟨tl, htl⟩ := padStream_drop13 hbits hw
  have hT0 : ReadsAt x.rd0 (ptrAt x.sI) (L.wsI ++ L.m1 :: (L.wsR ++ (L.wsC ++ (L.msg ++ tl)))) := by
    have := VsC.readsAt_drop (m := 13) hrd0
    rwa [hb18, htl] at this
  have hm1 : ReadsAt x.rd0 (ptrAt (x.natB772 L)) [L.m1] := by
    have := readsAt_slice hT0 L.wsI.length 1
    rwa [List.drop_left' rfl, List.take_succ_cons, List.take_zero] at this
  have i8 : σ (.n 779) = L.m1 :=
    good_load_get? (by intro h; have fr := vsC13_fresh; rw [List.contains_iff_mem.mpr h] at fr; exact absurd fr (by decide))
      (hm (.load (.n 779) (.n 772) 0) (by simp)) e772 hm1 rfl
  clear_value σ
  set s1 : Fs := ⟨[σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)], [(σ (.n 779), dsObserve)]⟩ with hs1
  have hK := keccakA_fs (s := s1) (VerifySub.KL.keccakA_complete (hm (.keccak [.n 780, .n 781, .n 25, .n 25, .n 25, .n 26, .n 27, .n 28, .n 774, .n 775,
      .n 776, .n 777, .n 778] [.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792,
      .n 793, .n 794] false false) (by simp))) (by simp [s1]) (by
    simp only [List.map_cons, List.map_nil, s1, i3, i4, i5, i6, i7, i9, i10, z25, z26, z27, z28]
    rfl)
  have hc : ∀ k : Fin 13, ∀ hk : k.val < 13,
      σ ([.n 782, .n 783, .n 784, .n 785, .n 786, .n 787, .n 788, .n 789, .n 790, .n 791, .n 792,
        .n 793, .n 794] : List Core.V)[k.val] = cellsOfState s1.perm false k :=
    fun k hk ↦ outs_eq hK k (by simp)
  have hendI : (L.endI x.lay x.nF).cap = [σ (.n 767), σ (.n 768), σ (.n 769), σ (.n 770), σ (.n 771)] := by
    have e : (L.endI x.lay x.nF).cap = (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cap := by
      rw [chainLast_ne hne _ ⟨L.cap2 x.lay x.nF, ptrAt x.sI, x.clI⟩]
      exact (natChain_fst_cap _ _ _ _ _ _ _ _ _).2
    rw [e, list5 hcap, ← cells_getD_cap hcap (by norm_num), ← cells_getD_cap hcap (by norm_num),
      ← cells_getD_cap hcap (by norm_num), ← cells_getD_cap hcap (by norm_num), ← cells_getD_cap hcap (by norm_num),
      ← hr 0 (by norm_num), ← hr 1 (by norm_num), ← hr 2 (by norm_num), ← hr 3 (by norm_num), ← hr 4 (by norm_num)]
  have hF : L.freshFs x.lay x.nF = s1 := by
    rw [LinkNat.freshFs, hendI, hs1, i8]
    simp [Fs.absorb, rateScalars]
  refine ⟨e772, hm1, fun k hk => ?_⟩
  have e : (L.fresh x.lay x.nF).getD k 0 = Link.cellAt s1.perm k := by
    rw [LinkNat.fresh, rangeMap_getD _ hk, hF]
  rw [e]
  simp only [Link.cellAt, (by omega : k < 13), ↓reduceDIte]
  have h := hc ⟨k, by omega⟩ (by show k < 13; omega)
  interval_cases k <;> exact h

/-- The pointer columns' last cursor is the packed message's. -/
theorem VsCtx.natLC_cur {link : LinkEnd} (hL : L.Ok x.lay x.nF x.c.freshClaim link) (hR0 : linkRows x.lay ≠ 0)
    (hq0 : linkQVars x.lay ≠ 0) : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cur = ptrAt (x.natBm L) := by
  have hne2 : x.natLR L ≠ [] := natChain_ne hR0 _ _
  have hcR : (chainLast ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩
      (x.natLR L)).cur = ptrAt (x.natB772 L + 1 + L.wsR.length) := by
    rw [VsCtx.natLR, LinkNat.chainR, natChain_cur, ← hL.lenR, ptrAt_add]
  have eR0 : chainLast ⟨[], 0, 0⟩ (x.natLR L) =
      chainLast ⟨L.cap4 x.lay x.nF, ptrAt (x.natB772 L + 1), (chainLast ⟨[], 0, 0⟩ (x.natLI L)).cl⟩ (x.natLR L) :=
    chainLast_ne hne2 _ _
  rw [VsCtx.natLC, LinkNat.chainC, chainLast_ne (natChain_ne hq0 _ _) _
    ⟨(L.endR x.lay x.nF).cap, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cur, (chainLast ⟨[], 0, 0⟩ (x.natLR L)).cl⟩,
    natChain_cur, ← hL.lenC]
  rw [eR0, hcR, ptrAt_add]
  rfl

theorem getD_drop1 (l : List E) (k : ℕ) : (l.drop 1).getD k 0 = l.getD (k + 1) 0 := by
  cases l <;> rfl

set_option maxHeartbeats 4000000 in
/-- **The link section's reads at the honest context are the native link's values** (`IRReads` at `tailIn`), from
the placement, the buffers' sizes, a causal return rule, the front's facts (`VsFsChecks1`, `Bw1`, `Num6`), the native
link `L`, the honest buffers (`BwNat`, buffer `8` the fresh claim's values) and returns (`honRet`, `Ret3`). -/
theorem VsCtx.irReads_nat {link : LinkEnd} {rest : List E}
    (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hfs : VsFsChecks1 x) (hb1 : x.Bw1) (h6 : x.Num6)
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hlb : x.lay.logBytecode = 19)
    (hB : BwNat x L) (hb8 : x.bw.getD 8 [] = x.c.freshClaim.values)
    (hR : ∀ i v, honRet x L i = some v → ∀ σ, x.ret i σ = v) (h3 : x.Ret3) :
    IRReads x.rd0 x.σ0 (tailIn x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF) L.m1
      (L.fresh x.lay x.nF) x.c.freshClaim.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg) := by
  obtain ⟨layout, r0, hann, S, hN⟩ := frontNum_of_child hok.child
  have hlay : x.lay = layout := VsCtx.lay_of hann
  have htab : x.lay.tables = tables := by rw [hlay]; exact announced_tables hann
  have hrl : x.lay.tableRows.length = 6 := by rw [hlay]; exact S.rows_length
  have hW := VsCtx.holdsWords_rd0B hok hbw
  have hwd : L.chunks.width = x.wdS := VerifySub.chunks_width hL.chunks
  have hw19 : 19 ≤ x.wdS := by rw [VsCtx.wdS, hlay]; exact hN.hw19
  have hw24 : x.wdS ≤ 24 := by rw [VsCtx.wdS, hlay]; exact hN.hw24
  have hmw : x.lay.logMemory ≤ x.wdS := by rw [VsCtx.wdS, hlay]; exact hN.hmw
  have hht : ∀ t < 6, x.hgS t ≤ x.nS := fun t ht => by
    show x.lay.tableLogHeights.getD t 0 ≤ hMax x.lay
    rw [hlay]; exact hN.hht t ht
  have hnS : x.nS ≤ 24 := by
    obtain ⟨t, ht, he⟩ := hN.hn
    show hMax x.lay ≤ 24
    rw [hlay, ← he]; exact hN.h24 t ht
  have hRr : ∀ t < 6, x.rows t ≤ 2 ^ x.hgS t := fun t ht => by
    show x.lay.tableRows.getD t 0 ≤ 2 ^ x.lay.tableLogHeights.getD t 0
    rw [hlay]; exact hN.hR t ht
  have hq6 : linkQVars x.lay = 6 := VerifySub.linkQVars_tables htab
  have hq0 : linkQVars x.lay ≠ 0 := by rw [hq6]; norm_num
  have hrn : linkRows x.lay = x.nS := rfl
  have hR0 : linkRows x.lay ≠ 0 := by
    have h5 : 9 ≤ layout.tableLogHeights.getD 5 0 := hN.h9
    have h55 : layout.tableLogHeights.getD 5 0 ≤ hMax layout := hN.hht 5 (by norm_num)
    rw [hlay, ← hMax_eq_linkRows]; omega
  have hbits : L.bits x.lay ≠ 0 :=
    grindingBits_ne (le_trans (by omega : 9 ≤ L.chunks.width + 1) (le_max_right _ _))
  have hood := VsCtx.hood_of hok hbw hret hb1.front.b18
  obtain ⟨e573, ecap, hpk⟩ := x.front_nat hw htab hL.chunks hbits hfs hood
  obtain ⟨h40, h4⟩ := x.bw4_nat hb1 e573 ecap hpk
  obtain ⟨h2, r767, r1071, -⟩ := ret_of_honRet hR
  have hD := linkDrawn_eq' htab (hwd ▸ hL.chunks : Chunks.new L.chunks.width = some L.chunks)
  have hnD : L.nDrawn x.lay = 88 + x.nS + x.wdS + L.chunks.d := by
    unfold LinkNat.nDrawn; rw [hD, hrn, hwd]
  have hdl : (L.drawn x.lay x.nF).length = L.nDrawn x.lay := drawn_length x.lay x.nF
  have hl4 : (x.bw.getD 4 []).length = 153 := by rw [VsCtx.lenbw hbw (by norm_num)]; rfl
  have hl5 : (x.bw.getD 5 []).length = 30 := by rw [VsCtx.lenbw hbw (by norm_num)]; rfl
  have hl7 : (x.bw.getD 7 []).length = 25 := by rw [VsCtx.lenbw hbw (by norm_num)]; rfl
  have hl8 : (x.bw.getD 8 []).length = 36 := by rw [VsCtx.lenbw hbw (by norm_num)]; rfl
  have hl11 : (x.bw.getD 11 []).length = 126 := by rw [VsCtx.lenbw hbw (by norm_num)]; rfl
  have hl12 : (x.bw.getD 12 []).length = 25 := by rw [VsCtx.lenbw hbw (by norm_num)]; rfl
  have hrL := natR_length hL
  have hcL := natChi_length (x := x) (L := L)
  have hqL := natQ_length (x := x) (L := L) htab
  -- `.n 10`: `θ_0`, then the draws
  have hchal : ∀ k < 89, rdw x.rd0 (x.σ0 (.n 10)) k = (L.theta0 x.lay x.nF :: L.drawn x.lay x.nF).getD k 0 := by
    intro k hk
    rw [x.rdBuf hret hbw hW (j := 4) rfl (by norm_num) (by norm_num) (by omega)]
    rcases k with _ | j
    · rw [List.getD_eq_getElem?_getD, h40]; rfl
    · rw [x.bw4_getD h4 (by omega)]; rfl
  -- `.n 11`: `eq(α, ·)`
  have hslot : ∀ s < 16, rdw x.rd0 (x.σ0 (.n 11)) (14 + s) = (natLets x L).slot.getD s 0 := by
    intro s hs
    rw [x.rdBuf hret hbw hW (j := 5) rfl (by norm_num) (by norm_num) (by omega), hB.b5]
    have hr4 : (ph7Rs (x.bw.getD 4 [])).length = 4 := by
      simp only [ph7Rs, List.length_take, List.length_drop]; omega
    have e := eqLevels_lev (rs := ph7Rs (x.bw.getD 4 [])) (n := 4) (by omega) 4 (by norm_num) le_rfl s
      (by norm_num; omega)
    have hA : (ph7Rs (x.bw.getD 4 [])).take 4 = (List.range 4).map fun i ↦ (L.drawn x.lay x.nF).getD (49 + i) 0 := by
      rw [List.take_of_length_le (by omega), ph7Rs,
        show ((x.bw.getD 4 []).drop 50).take 4 = ((x.bw.getD 4 []).drop (49 + 1)).take 4 from rfl,
        x.bw4_slice h4 (a := 49) (n := 4) (by omega)]
      exact Link.Arith.dt_eq _ 49 4 (by omega)
    rw [List.getD_eq_getElem?_getD, show 14 + s = 2 ^ 4 - 2 + s by norm_num, e, Option.getD_some, hA, natLets,
      lets_slot' htab (by omega)]
  -- `.n 1076`: the packed message
  have hcLC := x.natLC_cur hL hR0 hq0
  have hs1076 : x.σ0 (.n 1076) = ptrAt (x.natBm L) := by
    have e1 := vsVal_retC (rd0 := x.rd0) (w := x.w) (rfl : x.args.length = 6) vsC16_eq (.n 1076) (by simp)
    have e2 : x.w 1076 = _ := x.wRet hret (by decide) (r1071 5 (by norm_num))
    have hcap : (chainLast ⟨[], 0, 0⟩ (x.natLC L)).cap.length = 5 := natChain_last_cap hq0 _ _ _
    exact e1.trans (e2.trans ((cells_getD_5 hcap).trans hcLC))
  have hmsg : ReadsAt x.rd0 (ptrAt (x.natBm L)) L.msg := by
    have h0 := VsCtx.reads18 hok hbw
    have hbm : x.base 18 ≤ x.natBm L := by simp only [VsCtx.natBm, VsCtx.natB772, VsCtx.sI]; omega
    have r := readsAt_slice h0 (x.natBm L - x.base 18) 144
    rw [(x.sw_nat hbits hw hb1.front.b18 hL.lenM).1, show x.base 18 + (x.natBm L - x.base 18) = x.natBm L by omega]
      at r
    exact r
  -- `.n 17`: `eq(q_point, ·)`
  have heqQ : ∀ q < 64, rdw x.rd0 (x.σ0 (.n 17)) (62 + q) = (eqKernel (L.qPoint x.lay x.nF)).getD q 0 := by
    intro q hq
    rw [x.rdBuf hret hbw hW (j := 11) rfl (by norm_num) (by norm_num) (by omega), hB.b11]
    have e := eqLevels_lev (rs := (L.qPoint x.lay x.nF).take 6) (n := 6) (by simp; omega) 6 (by norm_num) le_rfl q
      (by norm_num; omega)
    rw [List.getD_eq_getElem?_getD, show 62 + q = 2 ^ 6 - 2 + q by norm_num, e, Option.getD_some]
    have e6 : ((L.qPoint x.lay x.nF).take 6).take 6 = L.qPoint x.lay x.nF := by
      rw [List.take_take, Nat.min_self, List.take_of_length_le (le_of_eq hqL)]
    rw [e6]
  -- the six `table_point`s
  have htp : ∀ t < 6,
      x.σ0 (.n (omegaVn.getD t 0)) = omegaAt ((natLets x L).theta.getD t 0) ((natLets x L).tau.take (x.hgS t))
        ((L.chi x.lay x.nF).take (x.hgS t)) (x.rows t) ∧
      x.σ0 (.n (omegaVn.getD t 0 + 1)) = lessThan ((L.chi x.lay x.nF).take (x.hgS t)) (x.rows t) ∧
      x.σ0 (.n (omegaVn.getD t 0 + 2)) = eqEval ((natLets x L).tau.take (x.hgS t))
        ((L.chi x.lay x.nF).take (x.hgS t)) := by
    intro t ht
    have hh := hht t ht
    obtain ⟨e1, e2, e3⟩ := x.tpRet hret h2 h3 ht
    have hθ : (x.bw.getD 4 []).getD t 0 = (natLets x L).theta.getD t 0 := by
      rw [natLets, lets_theta' htab (by omega)]
      rcases t with _ | j
      · rw [List.getD_eq_getElem?_getD, h40]; rfl
      · rw [x.bw4_getD h4 (by omega), show ∀ l : List E, (L.theta0 x.lay x.nF :: l).getD (j + 1) 0 = l.getD j 0 from
          fun _ => rfl, rangeMap_getD _ (by omega)]
    have hts : ((x.bw.getD 4 []).drop 89).take (x.hgS t) = (natLets x L).tau.take (x.hgS t) := by
      have hh' : x.hgS t ≤ x.lay.tableLogHeights.foldl max 0 := hh
      rw [natLets, lets_tau' htab (by omega), List.take_take, Nat.min_eq_left hh']
      exact x.bw4_slice h4 (a := 88) (n := x.hgS t) (by omega)
    have hxs : (x.bw.getD 9 []).take (x.hgS t) = (L.chi x.lay x.nF).take (x.hgS t) := by
      rw [hB.b9]; exact padTo_take_le (by omega)
    have hb1t := hb1.front.b1 t ht
    have hlts : (tsBitsW (x.rows t) (x.hg t)).length = x.hgS t + 1 := by
      simp only [tsBitsW, List.length_append, cbitsE_length, List.length_singleton]; rfl
    have hcs : ((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t) = cbitsE (x.rows t) (x.hgS t) := by
      refine List.ext_getElem? fun i => ?_
      rw [List.getElem?_take, List.getElem?_drop]
      split_ifs with hi
      · rw [hb1t i (by rw [hlts]; omega)]
        show (cbitsE (x.rows t) (x.hgS t) ++ [Link.bitE (x.rows t) (x.hgS t)])[i]? = _
        rw [List.getElem?_append_left (by rw [cbitsE_length]; exact hi)]
      · rw [List.getElem?_eq_none (by rw [cbitsE_length]; omega)]
    have htop : (x.bw.getD 1 []).getD (26 * t + x.hgS t) 0 = Link.bitE (x.rows t) (x.hgS t) := by
      rw [List.getD_eq_getElem?_getD, hb1t (x.hgS t) (by rw [hlts]; omega)]
      show ((cbitsE (x.rows t) (x.hgS t) ++ [Link.bitE (x.rows t) (x.hgS t)])[x.hgS t]?).getD 0 = _
      rw [List.getElem?_append_right (by rw [cbitsE_length]), cbitsE_length, Nat.sub_self]
      rfl
    have hlen1 : ((natLets x L).tau.take (x.hgS t)).length = x.hgS t := by
      rw [← hts, List.length_take, List.length_drop, hl4]; omega
    have hlen2 : ((L.chi x.lay x.nF).take (x.hgS t)).length = x.hgS t := by
      rw [List.length_take, hcL]; omega
    obtain ⟨f1, f2, f3⟩ := tablePoint_forms ((natLets x L).theta.getD t 0) _ _ (x.rows t) (x.hgS t) hlen1 hlen2
      (hRr t ht)
    rw [hθ, hts, hxs, hcs, htop] at e1
    rw [htop, hcs, hxs] at e2
    rw [hts, hxs] at e3
    exact ⟨e1.trans f1, e2.trans f2, e3.trans f3⟩
  -- the corners: `.n 18`'s `belowE` at each height
  have hcorner : ∀ t < 6, rdw x.rd0 (x.σ0 (.n (cornerVn.getD t 0))) 0 =
      prodE (((L.chi x.lay x.nF).drop (x.hgS t)).map (1 + ·)) := by
    intro t ht
    have hh := hht t ht
    have hsel : x.σ0 (.n (115 + t)) = gen ^ x.hgS t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0; exact h6.n115
      · exact h6.sel t h0 (by omega)
    have hcv : x.σ0 (.n (cornerVn.getD t 0)) = x.σ0 (.n 18) * x.σ0 (.n (115 + t)) := by
      interval_cases t
      · show x.σ0 (.n 1299) = x.σ0 (.n 18) * x.σ0 (.n 115)
        exact x.irMul (by simp) (by norm_num) (by norm_num)
      · show x.σ0 (.n 1411) = x.σ0 (.n 18) * x.σ0 (.n 116)
        exact x.irMul (by simp) (by norm_num) (by norm_num)
      · show x.σ0 (.n 1532) = x.σ0 (.n 18) * x.σ0 (.n 117)
        exact x.irMul (by simp) (by norm_num) (by norm_num)
      · show x.σ0 (.n 1615) = x.σ0 (.n 18) * x.σ0 (.n 118)
        exact x.irMul (by simp) (by norm_num) (by norm_num)
      · show x.σ0 (.n 1742) = x.σ0 (.n 18) * x.σ0 (.n 119)
        exact x.irMul (by simp) (by norm_num) (by norm_num)
      · show x.σ0 (.n 1888) = x.σ0 (.n 18) * x.σ0 (.n 120)
        exact x.irMul (by simp) (by norm_num) (by norm_num)
    rw [hcv, hsel, x.ptrBuf hret (j := 12) rfl (by norm_num), Link.Arith.rdw_mul_gen_pow, Nat.add_zero,
      rdw_reads (hW _ (VsCtx.memWo hbw (j := 12) (by norm_num) (by norm_num))) (by rw [hl12]; omega), hB.b12,
      padTo_getD (by simp; omega), rangeMap_getD _ (by omega)]
    rfl
  -- `.n 13`: `belowE r`
  have hbelow : ∀ k ≤ x.wdS, rdw x.rd0 (x.σ0 (.n 13)) k = prodE (((L.r x.lay x.nF).drop k).map (1 + ·)) := by
    intro k hk
    rw [x.rdBuf hret hbw hW (j := 7) rfl (by norm_num) (by norm_num) (by omega), hB.b7,
      padTo_getD (by simp; omega), rangeMap_getD _ (by omega)]
    rfl
  -- window `13`
  have hlI : L.wsI.length = L.chunks.width * natRoundLen 1 0 := hL.lenI
  obtain ⟨e772, hm1, hfr⟩ := x.g2_cells hw hbits (by omega) hlI hret hb1.front.b18 (VsCtx.reads18 hok hbw) r767
  -- `state_ends`, `index_side`
  have hzs : x.zsS = (natLets x L).zeta := x.zsS_nat hL htab h4
  have hzl : (natLets x L).zeta.length = x.wdS := by
    rw [natLets, lets_zeta' htab (by omega), List.length_take, List.length_drop, List.length_drop, hdl, hwd, hnD]
    omega
  have hrs : x.rsS = L.r x.lay x.nF := by rw [VsCtx.rsS, hB.b6]; exact padTo_take hrL
  have hcyc : (x.bw.getD 2 []).take x.wdS = bitsE (linkCycles x.lay) x.wdS := by
    rw [hb1.front.b2, cbL, bitsE, ← List.map_take, List.take_range, Nat.min_eq_left hw24, linkCycles,
      foldl_add6 hrl]
    rfl
  have r10 : ∀ v ∈ [V.n 752, .n 753], x.σ0 v = x.w v.idx := vsVal_retC (rd0 := x.rd0) (w := x.w) rfl vsC10_eq
  have r14 : ∀ v ∈ [V.n 797, .n 798, .n 799], x.σ0 v = x.w v.idx := vsVal_retC (rd0 := x.rd0) (w := x.w) rfl vsC14_eq
  have e752 : x.σ0 (.n 752) = linkEqAt (natLets x L).zeta 0 := by
    rw [r10 (.n 752) (by simp), x.wRet hret (by decide) h2.r752, hzs, ← linkEqAt_zero_eq]
  have e753 : x.σ0 (.n 753) = linkEqAt (natLets x L).zeta (linkCycles x.lay) := by
    rw [r10 (.n 753) (by simp), x.wRet hret (by decide) h2.r753, hcyc, hzs, ← hzl, ← linkEqAt_eq_endsProd]
  have e797 : x.σ0 (.n 797) = indexMle (L.r x.lay x.nF) := by
    rw [r14 (.n 797) (by simp), x.wRet hret (by decide) h2.r797, hrs]
  have e798 : x.σ0 (.n 798) = eqEval (natLets x L).zeta (L.r x.lay x.nF) := by
    rw [r14 (.n 798) (by simp), x.wRet hret (by decide) h2.r798, hzs, hrs]
    exact (sideFold_eq _ _).1
  have e799 : x.σ0 (.n 799) = linkShiftEq (natLets x L).zeta (L.r x.lay x.nF) := by
    rw [r14 (.n 799) (by simp), x.wRet hret (by decide) h2.r799, hzs, hrs]
    exact (sideFold_eq _ _).2
  refine
    { chal := hchal
      slot := hslot
      sent := fun k hk => by rw [hs1076]; exact rdw_reads hmsg (by rw [hL.lenM]; omega)
      splitv := fun k hk => by
        rw [x.rdBuf hret hbw hW (j := 8) rfl (by norm_num) (by norm_num) (by omega), hb8]
        rfl
      eqQ := heqQ
      omega := fun t ht => (htp t ht).1
      act := fun t ht => (htp t ht).2.1
      eqTau := fun t ht => (htp t ht).2.2
      corner := hcorner
      jump := fun k hk => ?_
      e0 := e752
      ec := e753
      idx := e797
      eqzr := e798
      shz := e799
      belowMem := ?_
      belowBc := ?_
      eq0R := ?_
      m1 := by rw [e772]; exact (rdw_reads hm1 (by simp)).trans rfl
      cert := hfr 0 (by norm_num) }
  · show x.σ0 (.n (783 + k)) = ((L.fresh x.lay x.nF).drop 1).getD k 0
    rw [getD_drop1, ← hfr (k + 1) (by omega), show 782 + (k + 1) = 783 + k by omega]
  · show rdw x.rd0 (x.σ0 (.n 801)) 0 = prodE (((L.r x.lay x.nF).drop (min x.lay.logMemory L.chunks.width)).map (1 + ·))
    rw [x.irMul (d := 801) (a := 13) (b := 101) (by simp) (by norm_num) (by norm_num), h6.n101,
      Link.Arith.rdw_mul_gen_pow, Nat.add_zero, hbelow x.mS hmw]
    rw [hwd, Nat.min_eq_left hmw]
    rfl
  · show rdw x.rd0 (x.σ0 (.n 13)) 19 = prodE (((L.r x.lay x.nF).drop (min x.lay.logBytecode L.chunks.width)).map (1 + ·))
    rw [hbelow 19 hw19, hlb, hwd, Nat.min_eq_left hw19]
  · show rdw x.rd0 (x.σ0 (.n 13)) 0 = prodE (((L.r x.lay x.nF).drop (min 0 L.chunks.width)).map (1 + ·))
    rw [hbelow 0 (Nat.zero_le _), Nat.zero_min]

/-! ## The link section's values and `D3.Ok.hid`, from the section's atoms alone -/

/-- **`LinkSecVals` at the honest context from the link section's atoms**: `linkSecVals_of` with its reads
(`irReads_nat`) and `rd0`'s own words (`holdsWords_rd0B`) discharged. -/
theorem VsCtx.linkSecVals_nat {link : LinkEnd} {rest : List E}
    (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hfs : VsFsChecks1 x) (hb1 : x.Bw1) (h6 : x.Num6)
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hlb : x.lay.logBytecode = 19)
    (hB : BwNat x L) (hb8 : x.bw.getD 8 [] = x.c.freshClaim.values)
    (hR : ∀ i v, honRet x L i = some v → ∀ σ, x.ret i σ = v) (h3 : x.Ret3)
    (hA : ∀ a, Stmt.atom a ∈ Link.Arith.linkSec → a.Holds x.rd0 x.σ0) :
    LinkSecVals x L := by
  obtain ⟨layout, r0, hann, -, -⟩ := frontNum_of_child hok.child
  have htab : x.lay.tables = tables := by rw [VsCtx.lay_of hann]; exact announced_tables hann
  exact x.linkSecVals_of hL hret hbw (VsCtx.holdsWords_rd0B hok hbw) htab hlb hA
    (x.irReads_nat hok hbw hret hfs hb1 h6 hw hL hlb hB hb8 hR h3)

/-- **`D3.Ok.hid` at the honest context from the link section's atoms** (`hid_nat` with `linkSecVals_nat`). -/
theorem VsCtx.hid_of_atoms {link : LinkEnd} {rest : List E} {D : D3}
    (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) (hret : CausalRule x.ret)
    (hfs : VsFsChecks1 x) (hb1 : x.Bw1) (h6 : x.Num6)
    (hw : x.c.proof.stream.drop 12 = L.words x.lay ++ rest) (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (hlb : x.lay.logBytecode = 19)
    (hB : BwNat x L) (hb8 : x.bw.getD 8 [] = x.c.freshClaim.values)
    (hR : ∀ i v, honRet x L i = some v → ∀ σ, x.ret i σ = v) (h3 : x.Ret3)
    (hch : Chunks.new x.wdS = some D.ch) (hbm : D.bm = x.natBm L)
    (hA : ∀ a, Stmt.atom a ∈ Link.Arith.linkSec → a.Holds x.rd0 x.σ0) :
    LtIdentity D.ch x.σ0 (x.w 1077) ((x.bw.getD 6 []).take D.ch.width) (x.sw D.bm 80 64)
      (x.cells19.map Prod.snd) (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take D.ch.d) := by
  obtain ⟨layout, r0, hann, S, hN⟩ := frontNum_of_child hok.child
  have hlay : x.lay = layout := VsCtx.lay_of hann
  have htab : x.lay.tables = tables := by rw [hlay]; exact announced_tables hann
  have hrl : x.lay.tableRows.length = 6 := by rw [hlay]; exact S.rows_length
  have hw19 : 19 ≤ x.wdS := by rw [VsCtx.wdS, hlay]; exact hN.hw19
  have hw24 : x.wdS ≤ 24 := by rw [VsCtx.wdS, hlay]; exact hN.hw24
  have hR0 : linkRows x.lay ≠ 0 := by
    have h5 : 9 ≤ layout.tableLogHeights.getD 5 0 := hN.h9
    have h55 : layout.tableLogHeights.getD 5 0 ≤ hMax layout := hN.hht 5 (by norm_num)
    rw [hlay, ← hMax_eq_linkRows]; omega
  obtain ⟨-, -, r1071, -⟩ := ret_of_honRet hR
  exact x.hid_nat hret hb1 hfs (VsCtx.hood_of hok hbw hret hb1.front.b18) hw hL htab hlb hrl hw19 hw24 hR0
    hb1.front.b18 hB.b6 r1071 hch hbm (x.linkSecVals_nat hok hbw hret hfs hb1 h6 hw hL hlb hB hb8 hR h3 hA)

end

end
end LeanVM.Guest.B1.VsC
