/-
  LeanVM.Guest.B1.VsC.VsOrcPh711

  `Ph7to11S`: `wC`'s phases 7 to 11 at the honest context, from `Bw2`, `Ret2` and `Carry6`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh1011
public import LeanVM.Guest.B1.VsC.VsOrcBnd
public import LeanVM.Guest.B1.VsC.VsOrcMem

/-!
# `Ph7` to `Ph11` at the honest context

Each phase's `PhNIn` at `x.rd0`, `x.rd1`, `x.args`, `x.cur`, `x.p`, `x.ret`, `x.R`, `x.Pre`, for every
`Own ⊇ x.OwnB`, at any state with `Bnd`: the buffers' pointers from the `HeapBuf` atoms and `vsW_alloc`
(`VsCtx.ptr`), their words on `x.rd0` and on every memory holding `x.Wo` (`VsCtx.bufAt`, `VsCtx.readsW`), their
cells own (`VsCtx.own`), the arrays below the callees' frames (`Bnd.hkc`), the front's numbers from `Carry6`
(`Num6`), the link's values from `Bw2` (`Lk2.Ok`) and `Ret2`. Each phase lemma (`ph7_of` … `ph11_of`) ends in
`Bnd` by `Bnd.quiet` with the posts' count; **`ph7to11S`** chains them.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-! ## Lists and reads -/

theorem readsAt_takeV {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) (n : ℕ) : ReadsAt rd p (l.take n) :=
  fun k hk => by
    rw [List.getElem_take]
    exact h k (by simp only [List.length_take] at hk; omega)

theorem readsAt_slice {rd : Reader} {b : ℕ} {xs : List E} (h : ReadsAt rd (ptrAt b) xs) (o t : ℕ) :
    ReadsAt rd (ptrAt (b + o)) ((xs.drop o).take t) :=
  readsAt_takeV (VsC.readsAt_drop h) t

theorem take_one_drop {l : List E} {o : ℕ} (h : o < l.length) : (l.drop o).take 1 = [l.getD o 0] := by
  rw [List.getD_eq_getElem _ _ h]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have : i = 0 := by simpa using h2
  subst this
  simp

theorem take_succ_getD {l : List E} {h : ℕ} (hl : h < l.length) : l.take h ++ [l.getD h 0] = l.take (h + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hl, List.getD_eq_getElem _ _ hl]
  rfl

theorem basesGetD : ∀ (b : ℕ) (L : List ℕ) (j : ℕ), j < L.length → (bases b L).getD j 0 = b + (L.take j).sum
  | _, [], _, h => absurd h (by simp)
  | b, n :: L, 0, _ => by simp [bases]
  | b, n :: L, j + 1, h => by
    have ih := basesGetD (b + n) L j (by simpa using h)
    simp only [bases, List.getD_cons_succ, List.take_succ_cons, List.sum_cons] at ih ⊢
    omega

theorem vsAllocIdx_getD {j : ℕ} (hj : j < 18) : vsAllocIdx.getD j 0 = j + 6 := by
  interval_cases j <;> rfl

theorem chunkCount_bounds {w : ℕ} (h1 : 19 ≤ w) (h2 : w ≤ 24) : 6 ≤ chunkCount w ∧ chunkCount w ≤ 9 := by
  interval_cases w <;> decide +kernel

/-! ## The honest context's buffers -/

namespace VsCtx

variable {x : VsCtx}

theorem base_c (j c : ℕ) (hj : j ≤ 18) (hc : (vsSz0.take j).sum = c) : x.base j = x.cur + c := by
  rw [base, basesGetD _ _ _ (by rw [vsAllocSz_length]; omega), vsAllocSz,
    List.take_append_of_le_length (by simp [vsSz0]; omega), hc]

theorem bw_len (hx : x.Hon) {j : ℕ} (hj : j < 24) : (x.bw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
  have hl : j < x.bw.length := by rw [bw_length hx]; exact hj
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ (by rw [vsAllocSz_length]; exact hj)]
  have := List.getElem_of_eq hx.hbw (by simpa using hl)
  simpa using this

/-- Buffer `j`'s run among the node's words, off `.n 19`. -/
theorem mem_Wo2 (hx : x.Hon) {j : ℕ} (hj : j < 24) (h13 : j ≠ 13) : (x.base j, x.bw.getD j []) ∈ x.Wo := by
  have hbl : (bases x.cur (vsAllocSz x.p)).length = 24 := by rw [bases_length, vsAllocSz_length]
  have hLl : x.Lw.length = 24 := by rw [Lw, List.length_set, bw_length hx]
  have hWo : x.Wo = (bases x.cur (vsAllocSz x.p)).zip x.Lw := rfl
  have e1 : x.base j = (bases x.cur (vsAllocSz x.p))[j]'(by omega) := by
    rw [base, List.getD_eq_getElem _ _ (by omega)]
  have e2 : x.bw.getD j [] = x.Lw[j]'(by omega) := by
    rw [← List.getD_eq_getElem x.Lw [] (by omega), Lw_getD hx hj]
    simp [h13]
  rw [hWo, e1, e2]
  exact List.mem_iff_getElem.mpr ⟨j, by simp [hbl, hLl]; omega, by rw [List.getElem_zip]⟩

/-- A memory holding the node's words reads buffer `j`, off `.n 19`. -/
theorem readsW (hx : x.Hon) {rd : Reader} (hW : HoldsWords rd x.Wo) {j : ℕ} (hj : j < 24) (h13 : j ≠ 13) :
    ReadsAt rd (ptrAt (x.base j)) (x.bw.getD j []) :=
  hW _ (mem_Wo2 hx hj h13)

/-- The buffers' cells are own. -/
theorem own {Own : ℕ → Prop} (hO : ∀ i, x.OwnB i → Own i) {i : ℕ} (h1 : x.cur ≤ i)
    (h2 : i < x.cur + 982 + 256 * x.p) : Own i := by
  have := vsAllocSz_sum x.p
  exact hO i ⟨h1, by omega⟩

/-- **A fixed buffer's pointer**: `.n (j + 6)`, allocated in window `0`, is the oracle's base. -/
theorem ptr (hx : x.Hon) {j sz : ℕ} (hj : j < 18) (hm : Atom.hint (.alloc (.n (j + 6)) sz) ∈ vsW0) :
    vsVal x.rd0 x.w x.args (.n (j + 6)) = ptrAt (x.base j) := by
  have e := vsW_alloc (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) rfl hx.hret (j := j) (by omega)
  rw [vsAllocIdx_getD hj] at e
  exact (vsW0_good (rd0 := x.rd0) (w := x.w) rfl hm).trans e

/-- **A fixed buffer**: its pointer, its words on `x.rd0` and on every memory with the state's `O`, its cells own. -/
theorem bufAt (hx : x.Hon) {Own : ℕ → Prop} (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st)
    {j sz n : ℕ} (hj : j < 18) (h13 : j ≠ 13) (hm : Atom.hint (.alloc (.n (j + 6)) sz) ∈ vsW0)
    (hn : n ≤ (vsAllocSz x.p).getD j 0) :
    BufAt x.rd0 (vsVal x.rd0 x.w x.args) x.Pre st.O Own (j + 6) (x.base j) n (x.bw.getD j []) := by
  have hmem := mem_Wo2 hx (by omega) h13
  refine ⟨x.ptr hx hj hm, by rw [bw_len hx (by omega)]; exact hn, holdsWords_rd0 hx _ hmem,
    fun rd _ ho => hb.hO rd ho _ hmem, fun t ht => hO _ ?_⟩
  have := base_lt hx j (by omega)
  exact ⟨by omega, by omega⟩

/-- A constant return of the honest oracle. -/
theorem w_retC (hx : x.Hon) {i : ℕ} (hi : vsPlain i) {c : E} (hc : ∀ σ, x.ret i σ = c) : x.w i = c :=
  vsW_retC rfl hx.hret hi hc

/-- **The front's numbers** at the announced layout. -/
theorem nums (hx : x.Hon) :
    19 ≤ x.wdS ∧ x.wdS ≤ 24 ∧ x.nS ≤ 24 ∧ x.mS ≤ x.wdS ∧ x.h0S ≤ 24 := by
  obtain ⟨layout, r, hann, -, hN⟩ := frontNum_of_child hx.ok.child
  have hl : x.lay = layout := by simp [VsCtx.lay, hann]
  obtain ⟨t, ht, he⟩ := hN.hn
  simp only [wdS, nS, mS, h0S, hl]
  refine ⟨hN.hw19, hN.hw24, ?_, hN.hmw, hN.h24 0 (by norm_num)⟩
  rw [← he]
  exact hN.h24 t ht

/-- The precondition's window tables. -/
theorem pre_win (rd : Reader) (h : x.Pre rd) : WinTabs rd (ptrAt x.qt * word 365917469723852800 0) := by
  have hE : ExpWinTab rd (ptrAt x.qt) := by obtain ⟨⟨_, h2⟩, _⟩ := h; exact h2
  rw [word_g178']
  exact winTabs_of_expWinTab hE

theorem R_tab {j : ℕ} (hj : j < 2 ^ 11) : x.R (x.qt + (j + 178)) := by
  have : expTabLen = 2226 := rfl
  exact Or.inl ⟨by omega, by omega⟩

end VsCtx

/-! ## The phases -/

section
variable {al : String → Bool} {x : VsCtx}

theorem vsW0_10 : Atom.hint (.alloc (.n (4 + 6)) 153) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_11 : Atom.hint (.alloc (.n (5 + 6)) 30) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_8 : Atom.hint (.alloc (.n (2 + 6)) 24) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_7 : Atom.hint (.alloc (.n (1 + 6)) 156) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_12 : Atom.hint (.alloc (.n (6 + 6)) 24) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_13 : Atom.hint (.alloc (.n (7 + 6)) 25) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_14 : Atom.hint (.alloc (.n (8 + 6)) 36) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_15 : Atom.hint (.alloc (.n (9 + 6)) 24) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_16 : Atom.hint (.alloc (.n (10 + 6)) 6) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_17 : Atom.hint (.alloc (.n (11 + 6)) 126) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_18 : Atom.hint (.alloc (.n (12 + 6)) 25) ∈ vsW0 := by simp [vsW0, vsW0a]

/-- The bases `Ph7 … Ph11` name. -/
structure Bases (x : VsCtx) : Prop where
  b1 : x.base 1 = x.cur + 6
  b2 : x.base 2 = x.cur + 162
  b4 : x.base 4 = x.cur + 190
  b5 : x.base 5 = x.cur + 343
  b6 : x.base 6 = x.cur + 373
  b7 : x.base 7 = x.cur + 397
  b8 : x.base 8 = x.cur + 422
  b9 : x.base 9 = x.cur + 458
  b10 : x.base 10 = x.cur + 482
  b11 : x.base 11 = x.cur + 488
  b12 : x.base 12 = x.cur + 614
  b18 : x.base 18 = x.cur + 824

theorem bases_of : Bases x :=
  ⟨VsCtx.base_c 1 6 (by norm_num) (by decide), VsCtx.base_c 2 162 (by norm_num) (by decide), VsCtx.base_c 4 190 (by norm_num) (by decide),
    VsCtx.base_c 5 343 (by norm_num) (by decide), VsCtx.base_c 6 373 (by norm_num) (by decide),
    VsCtx.base_c 7 397 (by norm_num) (by decide), VsCtx.base_c 8 422 (by norm_num) (by decide),
    VsCtx.base_c 9 458 (by norm_num) (by decide), VsCtx.base_c 10 482 (by norm_num) (by decide),
    VsCtx.base_c 11 488 (by norm_num) (by decide), VsCtx.base_c 12 614 (by norm_num) (by decide),
    VsCtx.base_c 18 824 (by norm_num) (by decide)⟩

/-- The front's region lies below the buffers. -/
theorem VsCtx.qt_lt (hx : x.Hon) : x.qt + 2226 ≤ x.cur := by
  have h1 := hx.ok.ht
  have h2 := hx.ok.hfc
  have : expTabLen = 2226 := rfl
  omega

/-- **`Ph7` at the honest context**, `link_rounds__L1_L0`'s call at the end `e`. -/
theorem ph7_of (hx : x.Hon) {Own : ℕ → Prop}
    (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st) (h6 : x.Num6) {L : VsCtx.Lk2} (hL : L.Ok x)
    {e : ℕ} (hcall : LrCall B2C.fs al B2C.cert 17 (x.w 680) (x.w 681) (x.w 682) (x.w 683) (x.w 684) (x.w 580)
      (lrClaim (x.w 752) (x.w 753) ((x.bw.getD 4 []).getD 6 0) ((x.bw.getD 4 []).getD 7 0)) (ptrAt (x.base 6))
      (ptrAt x.qt * word 365917469723852800 0) L.l L.nw (ph7Fp B2C.fs al x.wdS st.kc) e)
    (hq1 : 13 ≤ st.Qs.length) (hq2 : st.Qs.length + 2 ≤ 30) {K : St → Prop}
    (hK : ∀ s, x.Bnd s → s.Qs.length = st.Qs.length + 2 → s.kc = e →
      (∀ rd, s.O rd → st.O rd) → (∀ i, st.D i → s.D i) → K s) :
    Ph7Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st K := by
  obtain ⟨hw19, hw24, hn24, -, -⟩ := VsCtx.nums hx
  have hp := VsCtx.p_le hx
  have hcur := hx.ok.hcur
  have hqt := VsCtx.qt_lt hx
  obtain ⟨B1, B2, B4, B5, B6, B7, B8, B9, B10, B11, B12, B18⟩ := bases_of (x := x)
  have ha : x.args.length = 6 := rfl
  have hkc := hb.hkc
  rw [VsCtx.vsAllocSz_sum] at hkc
  have hl4 : (x.bw.getD 4 []).length = 153 := VsCtx.bw_len hx (j := 4) (by norm_num)
  have hl2 : (x.bw.getD 2 []).length = 24 := VsCtx.bw_len hx (j := 2) (by norm_num)
  have hl6 : (x.bw.getD 6 []).length = 24 := VsCtx.bw_len hx (j := 6) (by norm_num)
  obtain ⟨hs1, hs2⟩ := hL.hsIn
  have hfk : st.kc ≤ ph7Fp B2C.fs al x.wdS st.kc := by
    have h1 := le_allocBase (al (seNames.getD (x.wdS - 19) "")) st.kc
    have h2 := le_allocBase (al "link_rounds__L1_L0") (leafEnd B2C.fs al (seNames.getD (x.wdS - 19) "") st.kc)
    simp only [ph7Fp, leafEnd] at h2 ⊢
    omega
  refine ph7Ok_at ha hx.hret (rd0 := x.rd0) (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p)
    (ret := x.ret) (Own := Own) (R := x.R) (Pre := x.Pre) (st := st) (b8 := x.base 2) (b10 := x.base 4) (b11 := x.base 5) (b12 := x.base 6)
    (qt := x.qt) (n := x.nS) (wd := x.wdS) (s := L.s) (nw := L.nw) (xs10 := x.bw.getD 4 []) (zs := x.zsS)
    (cs := (x.bw.getD 2 []).take x.wdS) (l := L.l) ⟨hw19, hw24,
      VsCtx.bufAt hx hO hb (j := 4) (by norm_num) (by norm_num) vsW0_10 (by show 56 ≤ 153; norm_num),
      by rw [← hx.bw2.b11]; exact VsCtx.bufAt hx hO hb (j := 5) (by norm_num) (by norm_num) vsW0_11 le_rfl,
      h6.n408, h6.n409, VsCtx.ptr hx (j := 2) (by norm_num) vsW0_8,
      by simp only [VsCtx.zsS, List.length_take, List.length_drop, hl4]; omega,
      by simp only [List.length_take, hl2]; omega,
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun rd h => ⟨by
          have := readsAt_slice (VsCtx.readsW hx (hb.hO rd h.2) (j := 4) (by norm_num) (by norm_num)) (89 + x.nS)
            x.wdS
          rw [← Nat.add_assoc] at this
          exact this,
        readsAt_takeV (VsCtx.readsW hx (hb.hO rd h.2) (j := 2) (by norm_num) (by norm_num)) _⟩,
      hx.ret2.r752, hx.ret2.r753, VsCtx.ptr hx (j := 6) (by norm_num) vsW0_12,
      vsVal_param ha (i := 4) (by norm_num), hL.hw580, hL.hl, hL.hcur, hL.hcells, hL.r767, ?_,
      fun t ht => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.R_tab hj,
      fun rd h => ⟨hL.hc rd (hb.hO rd h.2) h.1, by
        rw [hL.hch]
        exact readsAt_takeV (VsCtx.readsW hx (hb.hO rd h.2) (j := 6) (by norm_num) (by norm_num)) _⟩⟩
    hcall fun hec => hK _ (hb.quiet hec (fun rd h => h.1) hq1 (by simp; omega) (by simp)) (by simp) rfl
      (by intro rd h; exact h.1) (by intro i h; exact Or.inl h)
  intro q hq
  have h11 : (2 : ℕ) ^ winTabBits = 2048 := rfl
  simp only [ph7Arrs, List.mem_cons, List.not_mem_nil, or_false, h11] at hq
  rcases hq with rfl | rfl | rfl <;> dsimp only <;> omega

set_option maxHeartbeats 3000000 in
/-- **`Ph8` at the honest context.** -/
theorem ph8_of (hx : x.Hon) {Own : ℕ → Prop}
    (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st) (h6 : x.Num6) {L : VsCtx.Lk2} (hL : L.Ok x)
    (hq1 : 13 ≤ st.Qs.length) (hq2 : st.Qs.length + 1 ≤ 30) {K : St → Prop}
    (hK : ∀ s, x.Bnd s → s.Qs.length = st.Qs.length + 1 → s.kc = ph8End B2C.fs al x.wdS st.kc →
      (∀ rd, s.O rd → st.O rd) → (∀ i, st.D i → s.D i) → K s) :
    Ph8Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st K := by
  obtain ⟨hw19, hw24, hn24, -, -⟩ := VsCtx.nums hx
  have hp := VsCtx.p_le hx
  have hcur := hx.ok.hcur
  obtain ⟨B1, B2, B4, B5, B6, B7, B8, B9, B10, B11, B12, B18⟩ := bases_of (x := x)
  have ha : x.args.length = 6 := rfl
  have hl4 : (x.bw.getD 4 []).length = 153 := VsCtx.bw_len hx (j := 4) (by norm_num)
  have hl6 : (x.bw.getD 6 []).length = 24 := VsCtx.bw_len hx (j := 6) (by norm_num)
  have hl18 : (x.bw.getD 18 []).length = 256 * x.p := VsCtx.bw_len hx (j := 18) (by norm_num)
  obtain ⟨hb1, hb2⟩ := hL.hbIn
  have hv : ∀ rd, HoldsWords rd x.Wo →
      ReadsAt rd (ptrAt L.b772) [(x.bw.getD 18 []).getD (L.b772 - x.base 18) 0] := fun rd hW => by
    have := readsAt_slice (VsCtx.readsW hx hW (j := 18) (by norm_num) (by norm_num)) (L.b772 - x.base 18) 1
    rwa [take_one_drop (by omega), Nat.add_sub_cancel' hb1] at this
  have h772 : x.w 772 = ptrAt L.b772 := (VsCtx.w_retC hx (i := 772) (by decide) (hL.r767 5 (by norm_num))).trans hL.h772
  refine ph8Ok_in ha hx.hret (rd0 := x.rd0) (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p)
    (ret := x.ret) (Own := Own) (R := x.R) (Pre := x.Pre) (st := st) (b772 := L.b772) (b12 := x.base 6) (bz := x.base 4 + 89 + x.nS) (b13 := x.base 7)
    (wd := x.wdS) (v := (x.bw.getD 18 []).getD (L.b772 - x.base 18) 0) (rs := x.rsS) (zs := x.zsS)
    ⟨hw19, hw24, h772, hv _ (VsCtx.holdsWords_rd0 hx), fun rd _ ho => hv rd (hb.hO rd ho),
      Or.inl (VsCtx.own hO (by omega) (by omega)), h6.n409, VsCtx.ptr hx (j := 6) (by norm_num) vsW0_12,
      h6.n694, VsCtx.ptr hx (j := 7) (by norm_num) vsW0_13,
      by simp only [VsCtx.rsS, List.length_take, hl6]; omega,
      by simp only [VsCtx.zsS, List.length_take, List.length_drop, hl4]; omega,
      ⟨by omega, by omega, by omega⟩, by unfold IvApart; omega,
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun rd h => by
        have hW := hb.hO rd h.2
        refine ⟨fun q hq => ?_, fun q hq => ?_⟩
        · simp only [isIns, List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl
          · exact readsAt_takeV (VsCtx.readsW hx hW (j := 6) (by norm_num) (by norm_num)) _
          · have := readsAt_slice (VsCtx.readsW hx hW (j := 4) (by norm_num) (by norm_num)) (89 + x.nS) x.wdS
            rw [← Nat.add_assoc] at this
            exact this
        · simp only [isOuts, List.mem_cons, List.not_mem_nil, or_false] at hq
          subst hq
          show ReadsAt rd (ptrAt (x.base 7)) ((List.range (x.wdS + 1)).map (belowE x.rsS))
          rw [← hx.bw2.b13]
          exact readsAt_takeV (VsCtx.readsW hx hW (j := 7) (by norm_num) (by norm_num)) _,
      hx.ret2.r797, hx.ret2.r798, hx.ret2.r799⟩
    (hK _ (hb.quiet ?_ (fun rd h => h) hq1 (by simp; omega) (by simp)) (by simp) rfl
      (by intro rd h; exact h) (by intro i h; exact h))
  have h1 := le_allocBase (al (isNames.getD (x.wdS - 19) "")) st.kc
  have h2 := le_allocBase (al (imNames.getD (x.wdS - 19) ""))
    (allocBase (al (isNames.getD (x.wdS - 19) "")) st.kc + B2C.fs (isNames.getD (x.wdS - 19) ""))
  omega

set_option maxHeartbeats 3000000 in
/-- **`Ph9` at the honest context**, `link_row_side__L{cc}`'s call at the end `e`. -/
theorem ph9_of (hx : x.Hon) {Own : ℕ → Prop}
    (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st) (h6 : x.Num6) {L : VsCtx.Lk2} (hL : L.Ok x)
    {e : ℕ} (hcall : LrsCall B2C.fs al B2C.cert 17 (chunkCount x.wdS) (x.σ0 (.n 790)) (x.σ0 (.n 791))
      (x.σ0 (.n 792)) (x.σ0 (.n 793)) (x.σ0 (.n 794)) (ptrAt (L.b772 + 1)) (x.w 773) (ptrAt (x.base 9))
      (ptrAt (x.base 10)) (ptrAt x.qt * word 365917469723852800 0) L.l1 L.l2 L.nw1 L.nw2
      (allocBase (al (lrsNames.getD (chunkCount x.wdS - 6) "")) st.kc) e)
    (hq1 : 13 ≤ st.Qs.length) (hq2 : st.Qs.length + 1 ≤ 30) {K : St → Prop}
    (hK : ∀ s, x.Bnd s → s.Qs.length = st.Qs.length + 1 → s.kc = e →
      (∀ rd, s.O rd → st.O rd) → (∀ i, st.D i → s.D i) → K s) :
    Ph9Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st K := by
  obtain ⟨hw19, hw24, hn24, hmw, -⟩ := VsCtx.nums hx
  have hp := VsCtx.p_le hx
  have hcur := hx.ok.hcur
  have hqt := VsCtx.qt_lt hx
  obtain ⟨B1, B2, B4, B5, B6, B7, B8, B9, B10, B11, B12, B18⟩ := bases_of (x := x)
  have ha : x.args.length = 6 := rfl
  have hkc := hb.hkc
  rw [VsCtx.vsAllocSz_sum] at hkc
  have hl7 : (x.bw.getD 7 []).length = 25 := VsCtx.bw_len hx (j := 7) (by norm_num)
  obtain ⟨hb1, hb2⟩ := hL.hbIn
  obtain ⟨hc6, hc9⟩ := chunkCount_bounds hw19 hw24
  have h772 : x.w 772 = ptrAt L.b772 := (VsCtx.w_retC hx (i := 772) (by decide) (hL.r767 5 (by norm_num))).trans hL.h772
  have hfk : st.kc ≤ allocBase (al (lrsNames.getD (chunkCount x.wdS - 6) "")) st.kc := le_allocBase _ _
  refine ph9Ok_at ha hx.hret (rd0 := x.rd0) (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p)
    (ret := x.ret) (Own := Own) (R := x.R) (Pre := x.Pre) (st := st) (b10 := x.base 4) (b11 := x.base 5) (b13 := x.base 7) (b14 := x.base 8)
    (b15 := x.base 9) (b16 := x.base 10) (b772 := L.b772) (m := x.mS) (n := x.nS) (cc := chunkCount x.wdS)
    (qt := x.qt) (nw1 := L.nw1) (nw2 := L.nw2) (xs10 := x.bw.getD 4 []) (xs11 := x.bw.getD 5 [])
    (xs13 := x.bw.getD 7 []) (xs14 := x.bw.getD 8 []) (l1 := L.l1) (l2 := L.l2)
    ⟨VsCtx.ptr hx (j := 7) (by norm_num) vsW0_13, by omega,
      VsCtx.readsW hx (VsCtx.holdsWords_rd0 hx) (j := 7) (by norm_num) (by norm_num),
      fun rd _ ho => VsCtx.readsW hx (hb.hO rd ho) (j := 7) (by norm_num) (by norm_num),
      fun j hj => VsCtx.own hO (by omega) (by omega), h6.n101, by omega,
      VsCtx.bufAt hx hO hb (j := 8) (by norm_num) (by norm_num) vsW0_14 le_rfl,
      VsCtx.bufAt hx hO hb (j := 5) (by norm_num) (by norm_num) vsW0_11 le_rfl,
      VsCtx.bufAt hx hO hb (j := 4) (by norm_num) (by norm_num) vsW0_10 (by show 37 ≤ 153; norm_num),
      hc6, hc9, h6.w484, h772, VsCtx.ptr hx (j := 9) (by norm_num) vsW0_15,
      VsCtx.ptr hx (j := 10) (by norm_num) vsW0_16, h6.n408, vsVal_param ha (i := 4) (by norm_num),
      by omega, hL.hl1, hL.hl2, hL.hcur1, hL.hcur2, hL.hcells2, hL.r1071, ?_,
      fun t ht => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.R_tab hj,
      fun rd h => by
        have hW := hb.hO rd h.2
        obtain ⟨c1, c2⟩ := hL.hc12 rd hW h.1
        refine ⟨VsCtx.pre_win rd h.1, c1, c2, ?_, ?_⟩
        · rw [hL.hch1]
          exact readsAt_takeV (VsCtx.readsW hx hW (j := 9) (by norm_num) (by norm_num)) _
        · rw [hL.hch2]
          exact VsCtx.readsW hx hW (j := 10) (by norm_num) (by norm_num)⟩
    hcall fun hec => hK _ (hb.quiet hec (fun rd h => h.1) hq1 (by simp; omega) (by simp)) (by simp) rfl
      (by intro rd h; exact h.1) (by intro i h; exact Or.inl h)
  intro q hq
  have h11 : (2 : ℕ) ^ winTabBits = 2048 := rfl
  simp only [ph9Arrs, List.mem_cons, List.not_mem_nil, or_false, h11] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

/-- `packed_message`'s inputs: the row side's returns as the chain's cells. -/
theorem w1071 (hx : x.Hon) {L : VsCtx.Lk2} (hL : L.Ok x) :
    (List.range 5).map (fun i => vsW x.rd1 x.args x.cur x.p x.ret (1071 + i)) =
      (chainLast ⟨[], 0, 0⟩ L.l2).cells.take 5 := by
  apply List.ext_getElem (by simp [hL.hcells2])
  intro i h1 h2
  have hi : i < 5 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  rw [vsW_retC rfl hx.hret (i := 1071 + i) (by interval_cases i <;> decide) (hL.r1071 i (by omega)),
    List.getD_eq_getElem _ _ (by rw [hL.hcells2]; omega)]

/-- **`Ph10` at the honest context.** -/
theorem ph10_of (hx : x.Hon) {Own : ℕ → Prop}
    (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st) (h6 : x.Num6) {L : VsCtx.Lk2} (hL : L.Ok x)
    (hq1 : 13 ≤ st.Qs.length) (hq2 : st.Qs.length + 2 ≤ 30) {K : St → Prop}
    (hK : ∀ s, x.Bnd s → s.Qs.length = st.Qs.length + 2 →
      s.kc = leafEnd B2C.fs al "packed_message__L144" (leafEnd B2C.fs al (opsNames.getD x.nS "") st.kc) →
      (∀ rd, s.O rd → st.O rd) → (∀ i, st.D i → s.D i) → K s) :
    Ph10Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st K := by
  obtain ⟨hw19, hw24, hn24, -, -⟩ := VsCtx.nums hx
  have hp := VsCtx.p_le hx
  have hcur := hx.ok.hcur
  obtain ⟨B1, B2, B4, B5, B6, B7, B8, B9, B10, B11, B12, B18⟩ := bases_of (x := x)
  have ha : x.args.length = 6 := rfl
  have hl9 : (x.bw.getD 9 []).length = 24 := VsCtx.bw_len hx (j := 9) (by norm_num)
  have hl18 : (x.bw.getD 18 []).length = 256 * x.p := VsCtx.bw_len hx (j := 18) (by norm_num)
  obtain ⟨hm1, hm2⟩ := hL.hbmIn
  have hwm : x.w 1076 = ptrAt L.bm := (VsCtx.w_retC hx (i := 1076) (by decide) (hL.r1071 5 (by norm_num))).trans hL.hbm
  have e5 := w1071 hx hL
  refine ph10Ok_in ha hx.hret (rd0 := x.rd0) (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p)
    (ret := x.ret) (Own := Own) (R := x.R) (Pre := x.Pre) (st := st) (b15 := x.base 9) (b16 := x.base 10) (b17 := x.base 11) (b18 := x.base 12)
    (bm := L.bm) (n := x.nS) (xs16 := x.bw.getD 10 []) (as15 := x.as15S)
    (xm := ((x.bw.getD 18 []).drop (L.bm - x.base 18)).take 144)
    ⟨VsCtx.bufAt hx hO hb (j := 10) (by norm_num) (by norm_num) vsW0_16 le_rfl,
      by rw [← hx.bw2.b17]; exact VsCtx.bufAt hx hO hb (j := 11) (by norm_num) (by norm_num) vsW0_17 le_rfl,
      h6.n408, by omega, VsCtx.ptr hx (j := 12) (by norm_num) vsW0_18, VsCtx.ptr hx (j := 9) (by norm_num) vsW0_15,
      by simp only [VsCtx.as15S, List.length_take, hl9]; omega,
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun rd h => by
        have hW := hb.hO rd h.2
        refine ⟨readsAt_takeV (VsCtx.readsW hx hW (j := 9) (by norm_num) (by norm_num)) _, ?_⟩
        rw [← hx.bw2.b18]
        exact readsAt_takeV (VsCtx.readsW hx hW (j := 12) (by norm_num) (by norm_num)) _,
      hx.ret2.r1286, hwm, by simp only [List.length_take, List.length_drop, hl18]; omega,
      fun j hj => Or.inl (Or.inr (VsCtx.own hO (by omega) (by omega))),
      fun rd h => by
        have := readsAt_slice (VsCtx.readsW hx (hb.hO rd h.2) (j := 18) (by norm_num) (by norm_num))
          (L.bm - x.base 18) 144
        rwa [Nat.add_sub_cancel' hm1] at this,
      by rw [e5]; exact hL.rpm, by rw [e5]; exact hL.hpm6⟩
    (hK _ (hb.quiet ?_ (fun rd h => h) hq1 (by simp; omega) (by simp)) (by simp) rfl
      (by intro rd h; exact h) (by intro i h; exact h))
  have h1 := le_allocBase (al (opsNames.getD x.nS "")) st.kc
  have h2 := le_allocBase (al "packed_message__L144") (leafEnd B2C.fs al (opsNames.getD x.nS "") st.kc)
  simp only [leafEnd] at h2 ⊢
  omega

/-- **`Ph11` at the honest context.** -/
theorem ph11_of (hx : x.Hon) {Own : ℕ → Prop}
    (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st) (h6 : x.Num6)
    (hq1 : 13 ≤ st.Qs.length) (hq2 : st.Qs.length + 1 ≤ 30) {K : St → Prop}
    (hK : ∀ s, x.Bnd s → s.Qs.length = st.Qs.length + 1 → s.kc = leafEnd B2C.fs al (tpNames.getD x.h0S "") st.kc →
      (∀ rd, s.O rd → st.O rd) → (∀ i, st.D i → s.D i) → K s) :
    Ph11Ok B2C.fs al B2C.cert 17 x.rd0 x.w x.args Own x.R x.Pre st K := by
  obtain ⟨-, -, -, -, hh⟩ := VsCtx.nums hx
  have hp := VsCtx.p_le hx
  have hcur := hx.ok.hcur
  obtain ⟨B1, B2, B4, B5, B6, B7, B8, B9, B10, B11, B12, B18⟩ := bases_of (x := x)
  have ha : x.args.length = 6 := rfl
  have hl1 : (x.bw.getD 1 []).length = 156 := VsCtx.bw_len hx (j := 1) (by norm_num)
  have hl4 : (x.bw.getD 4 []).length = 153 := VsCtx.bw_len hx (j := 4) (by norm_num)
  have hl9 : (x.bw.getD 9 []).length = 24 := VsCtx.bw_len hx (j := 9) (by norm_num)
  refine ph11Ok_in ha hx.hret (rd0 := x.rd0) (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p)
    (ret := x.ret) (Own := Own) (R := x.R) (Pre := x.Pre) (st := st) (b7 := x.base 1) (b10 := x.base 4) (b15 := x.base 9) (h := x.h0S)
    (xs10 := x.bw.getD 4 []) (ts := ((x.bw.getD 4 []).drop 89).take x.h0S) (xs := (x.bw.getD 9 []).take x.h0S)
    (cs := (x.bw.getD 1 []).take x.h0S) (top := (x.bw.getD 1 []).getD x.h0S 0)
    ⟨VsCtx.bufAt hx hO hb (j := 4) (by norm_num) (by norm_num) vsW0_10 (by show 1 ≤ 153; norm_num),
      h6.n115, hh, VsCtx.ptr hx (j := 9) (by norm_num) vsW0_15, VsCtx.ptr hx (j := 1) (by norm_num) vsW0_7,
      by simp only [List.length_take, List.length_drop, hl4]; omega,
      by simp only [List.length_take, hl9]; omega,
      by simp only [List.length_take, hl1]; omega,
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun j hj => VsCtx.own hO (by omega) (by omega),
      fun rd h => by
        have hW := hb.hO rd h.2
        refine ⟨readsAt_slice (VsCtx.readsW hx hW (j := 4) (by norm_num) (by norm_num)) 89 _,
          readsAt_takeV (VsCtx.readsW hx hW (j := 9) (by norm_num) (by norm_num)) _, ?_⟩
        rw [take_succ_getD (by omega)]
        exact readsAt_takeV (VsCtx.readsW hx hW (j := 1) (by norm_num) (by norm_num)) _,
      hx.ret2.r1296, hx.ret2.r1297, hx.ret2.r1298⟩
    (hK _ (hb.quiet ?_ (fun rd h => h) hq1 (by simp; omega) (by simp)) (by simp) rfl
      (by intro rd h; exact h) (by intro i h; exact h))
  have h1 := le_allocBase (al (tpNames.getD x.h0S "")) st.kc
  simp only [leafEnd]
  omega

/-- **`wC`'s phases 7 to 11 at the honest context** (vsph2, vspin): from `Bw2` (the link's data, its two calls
at the pinned ends `x.ec 7`, `x.ec 9`, and `x.ec 12`), `Ret2` and `Carry6` (the posts' count, the front's numbers,
the cursor `x.ec 6`, `StkAt`, which each phase keeps: its memory conditions only added, its data only claimed). -/
theorem ph7to11S (al : String → Bool) : Ph7to11S al := by
  intro x hal hx _ Own hO st K hb h6 hK
  subst hal
  obtain ⟨L, hL⟩ := hx.bw2.lk
  obtain ⟨hq, h6, hk6, hS6⟩ := h6
  have hq6 : 15 ≤ x.qs6 ∧ x.qs6 ≤ 16 := by unfold VsCtx.qs6; split_ifs <;> omega
  refine ph7_of hx hO hb h6 hL (e := x.ec 7) (by rw [hk6]; exact hL.crd) (by omega) (by omega)
    fun s7 hb7 hl7 hk7 hO7 hD7 => ?_
  refine ph8_of hx hO hb7 h6 hL (by omega) (by omega) fun s8 hb8 hl8 hk8 hO8 hD8 => ?_
  refine ph9_of hx hO hb8 h6 hL (e := x.ec 9) (by rw [hk8, hk7]; exact hL.crs) (by omega) (by omega)
    fun s9 hb9 hl9 hk9 hO9 hD9 => ?_
  refine ph10_of hx hO hb9 h6 hL (by omega) (by omega) fun s10 hb10 hl10 hk10 hO10 hD10 => ?_
  exact ph11_of hx hO hb10 h6 (by omega) (by omega) fun s11 hb11 hl11 hk11 hO11 hD11 =>
    hK s11 hb11 ⟨show s11.Qs.length = x.qs6 + 7 by omega, h6, by rw [hk11, hk10, hk9, hx.bw2.e12, ph11End],
      hS6.mono (fun rd h => hO7 rd (hO8 rd (hO9 rd (hO10 rd (hO11 rd h)))))
        (fun i h => hD11 i (hD10 i (hD9 i (hD8 i (hD7 i h)))))⟩

end

end
end LeanVM.Guest.B1.VsC
