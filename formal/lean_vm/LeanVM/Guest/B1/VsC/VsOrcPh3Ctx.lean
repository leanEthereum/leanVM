/-
  LeanVM.Guest.B1.VsC.VsOrcPh3Ctx

  `Ph12EndP` at the honest context, from `Bw3`'s `D3`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh3Spec
public import LeanVM.Guest.B1.VsC.VsOrcPh711
public import LeanVM.Guest.B1.VsC.CstA
public import LeanVM.Guest.Complete.FsSmall

/-!
# `Ph12` to the end on an honest context

The phases' honest inputs at the context's values: the own buffers from `bufAtL` (`bufC`), their cells own
(`VsCtx.own`), the stream's words at the packed message's cursor `bm` (`sw_reads`), the overlay's stores
(`hst19`), `.n 695` from window `9`'s product, the arrays below the callees' cursor (`Bnd.hkc` and the pinned
calls' ends, `ecChain`), the ring buffers (`Bw3`'s `b21`, `b22`, `D3`'s `b23`), the selectors and bits pointers
(`Num6`), the native facts and the pinned calls (`D3`). **`ph1213In_ctx`**, **`ph35In_ctx`**, **`phOpenIn_ctx`**,
**`ph12EndP_ctx`**: `Ph12EndP` at every honest boundary state with `Carry11` (its cursor `x.ec 12`, `StkAt`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Stack LeanVM.Guest.B1.Whir LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (wordNat bitWord allocBase)
open LeanVM.Guest.B1.Link (ltNames)
open LeanVM.Guest.B1.VerifySub

@[expose] public section

namespace VsCtx

variable {x : VsCtx}

theorem vsAllocSz_18 (p : ℕ) : (vsAllocSz p).getD 18 0 = 256 * p := rfl

/-- A fixed own buffer at a boundary, for every cell predicate containing `Own`, with its words `bw`. -/
theorem bufC (hx : x.Hon) {Own : ℕ → Prop} (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st) {j n : ℕ}
    (hj : j < 18) (h13 : j ≠ 13) (hn : n ≤ (vsAllocSz x.p).getD j 0) {C : ℕ → Prop} (hC : ∀ i, Own i → C i) :
    BufAt x.rd0 (vsVal x.rd0 x.w x.args) x.Pre st.O C (j + 6) (x.base j) n (x.bw.getD j []) := by
  have h := bufAtL hx hb.hO hj (C := C) (fun i h => hC i (hO i h)) hn
  simp only [Lw_getD hx (show j < 24 by omega), h13, ↓reduceIte] at h
  exact h

/-- The stream's words' count. -/
theorem sw_len (hx : x.Hon) {bm o n : ℕ} (h1 : x.base 18 ≤ bm) (h2 : bm + o + n ≤ x.base 18 + 256 * x.p) :
    (x.sw bm o n).length = n := by
  have hl : (x.bw.getD 18 []).length = 256 * x.p := bw_len hx (j := 18) (by norm_num)
  simp only [sw, List.length_take, List.length_drop, hl]
  omega

/-- A memory holding the node's words reads the stream from `bm + o`. -/
theorem sw_reads (hx : x.Hon) {rd : Reader} (hW : HoldsWords rd x.Wo) {bm : ℕ} (h1 : x.base 18 ≤ bm) (o n : ℕ) :
    ReadsAt rd (ptrAt (bm + o)) (x.sw bm o n) := by
  have h := readsAt_slice (readsW hx hW (j := 18) (by norm_num) (by norm_num)) (bm - x.base 18 + o) n
  rwa [show x.base 18 + (bm - x.base 18 + o) = bm + o by omega] at h

theorem sw_zero (bm n : ℕ) : x.sw bm 0 n = ((x.bw.getD 18 []).drop (bm - x.base 18)).take n := by
  simp only [sw, Nat.add_zero]

theorem base_13 : x.base 13 = x.cur + 639 := base_c 13 639 (by norm_num) (by decide)
theorem base_14 : x.base 14 = x.cur + 651 := base_c 14 651 (by norm_num) (by decide)
theorem base_15 : x.base 15 = x.cur + 729 := base_c 15 729 (by norm_num) (by decide)
theorem base_17 : x.base 17 = x.cur + 823 := base_c 17 823 (by norm_num) (by decide)

theorem base_wc : x.base 21 = x.a1 ∧ x.base 22 = x.a1 + 16 ∧ x.base 23 = x.a1 + 80 := by
  obtain ⟨h1, h2, h3⟩ := vsBase_wc x.cur x.p
  rw [base, vsBases_getD x.cur x.p (by norm_num), base, vsBases_getD x.cur x.p (by norm_num), base,
    vsBases_getD x.cur x.p (by norm_num), h1, h2, h3, a1]
  omega

/-- Buffer `j ≥ 18`'s words on a memory holding the node's words, off `.n 19`. -/
theorem readsHi (hx : x.Hon) {rd : Reader} (hW : HoldsWords rd x.Wo) {j : ℕ} (hj : j < 24) (h13 : j ≠ 13) :
    ReadsAt rd (ptrAt (x.base j)) (x.bw.getD j []) := readsW hx hW hj h13

/-- The table heights the guest reads are at most `24`. -/
theorem hgS_le (hx : x.Hon) {t : ℕ} (ht : t < 6) : x.hgS t ≤ 24 := by
  obtain ⟨layout, r, hann, -, hN⟩ := frontNum_of_child hx.ok.child
  have hl : x.lay = layout := by simp [VsCtx.lay, hann]
  simp only [hgS, hl]
  exact hN.h24 t ht

/-- **The overlay's stores** hold on the evaluation memory. -/
theorem hst19 (hx : x.Hon) : ∀ a ∈ stC32, MemF x.rd0 (vsVal x.rd0 x.w x.args) a := by
  have ha : x.args.length = 6 := rfl
  have hf := hx.bw3.fresh
  have h19 : vsVal x.rd0 x.w x.args (.n 19) = ptrAt (x.base 13) := ptrL hx (j := 13) (by norm_num)
  have key : ∀ k < 12, LoadHolds x.rd0 (ptrAt (x.base 13)) k
      (vsVal x.rd0 x.w x.args (.n (vs19Src.getD k 0))) := by
    intro k hk
    have hv : tIdx vsRcs (vs19Src.getD k 0) = false := by interval_cases k <;> decide +kernel
    have e := vsVal_congr (v := .n (vs19Src.getD k 0)) ha hf hv
    refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
    have r := rd0_run13 hx hk
    rw [cells19, vsCells19_getD _ _ hk, e] at r
    rw [show (ptrAt (x.base 13)).limb 0 * addressOfIndex k = addressOfIndex (x.base 13 + k) by
      simp [ptrAt, addressOfIndex, pow_add]]
    exact r
  intro a hm
  have hs : stC32 = (List.range 12).map fun k => Atom.load (.n (vs19Src.getD k 0)) (.n 19) k := rfl
  rw [hs, List.mem_map] at hm
  obtain ⟨k, hk, rfl⟩ := hm
  rw [List.mem_range] at hk
  show LoadHolds x.rd0 (vsVal x.rd0 x.w x.args (.n 19)) k (vsVal x.rd0 x.w x.args (.n (vs19Src.getD k 0)))
  rw [h19]
  exact key k hk

/-- `.n 695`, the chunks' `ν`: `.n 694 · .n 409`. -/
theorem n695 (h6 : x.Num6) : vsVal x.rd0 x.w x.args (.n 695) = ptrAt (x.base 4 + 89 + x.nS + x.wdS) := by
  have ha : x.args.length = 6 := rfl
  have hg := vsC_atoms_good (rd0 := x.rd0) (w := x.w) ha 147 97 (.mul (.n 695) (.n 694) (.n 409))
    (by rw [as9_eq]; simp [vsC9a])
  rw [good_mulF hg (by omega) (by omega)]
  show x.σ0 (.n 694) * x.σ0 (.n 409) = _
  rw [h6.n694, h6.n409, ptrAt_mul_pow]

theorem loadHolds_shift {rd : Reader} {b o j : ℕ} {v : E} (h : LoadHolds rd (ptrAt (b + o)) j v) :
    LoadHolds rd (ptrAt b) (o + j) v := by
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  have e : ∀ a t : ℕ, (ptrAt a).limb 0 * addressOfIndex t = addressOfIndex (a + t) := fun a t => by
    simp [ptrAt, addressOfIndex, pow_add]
  have h2 := h.2
  rw [e] at h2 ⊢
  rwa [← Nat.add_assoc]

theorem getD_drop' (l : List E) (n m : ℕ) : (l.drop n).getD m 0 = l.getD (n + m) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The ends the pinned calls leave, in order. -/
theorem ecChain {D : D3} (hD : D.Ok x) :
    x.ec 12 ≤ x.ec 13 ∧ x.ec 13 ≤ x.ec 14 ∧ x.ec 14 ≤ x.ec 15 ∧ x.ec 15 ≤ x.ec 16 := by
  have hlt := hD.hlt
  have hvk := hD.hvk
  have hrt := hD.hrt
  have hos := hD.hos
  unfold LtCall at hlt
  unfold VkCall at hvk
  unfold RtCall at hrt
  obtain ⟨_, _, h1, _⟩ := hlt
  obtain ⟨_, _, h2, _⟩ := hvk
  obtain ⟨_, _, h3, _⟩ := hrt
  obtain ⟨_, _, h4, _⟩ := hos
  have := tpKc_ge B2C.fs x.al x.hgS 5 (x.ec 12)
  have := le_allocBase (x.al (ltNames.getD (x.wdS - 19) "")) (tpKc B2C.fs x.al x.hgS 5 (x.ec 12))
  have := le_allocBase (x.al "verify_keccak") (x.ec 13)
  have := le_allocBase (x.al "ring_switch_target") (x.ec 14)
  have := le_allocBase (x.al (openName D.sl)) (x.ec 15)
  omega

end VsCtx

section
variable {x : VsCtx}

/-- **`Ph1213`'s honest inputs on an honest context.** -/
theorem ph1213In_ctx (hx : x.Hon) {Own : ℕ → Prop} (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st)
    (h6 : x.Num6) {D : VsCtx.D3} (hD : D.Ok x) :
    Ph1213In B2C.fs x.al B2C.cert 17 x.rd0 x.rd1 x.args x.cur x.p x.ret Own x.R x.Pre st (x.base 12) D.bm (x.base 5)
      (x.base 4) (x.base 11) (x.base 9) (x.base 13) (x.base 6) (x.base 4 + 89 + x.nS + x.wdS) x.wdS
      (x.bw.getD 12 []) (x.sw D.bm 0 144) (x.bw.getD 5 []) (x.bw.getD 4 []) (x.bw.getD 11 []) (x.cells19.map Prod.snd)
      x.hgS (fun t => x.base 1 + 26 * (t - 1)) (fun t => ((x.bw.getD 4 []).drop 89).take (x.hgS t))
      (fun t => (x.bw.getD 9 []).take (x.hgS t)) (fun t => ((x.bw.getD 1 []).drop (26 * t)).take (x.hgS t))
      (fun t => (x.bw.getD 1 []).getD (26 * t + x.hgS t) 0) D.ch ((x.bw.getD 6 []).take D.ch.width)
      (x.sw D.bm 80 64) (x.cells19.map Prod.snd) (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take D.ch.d) := by
  have ha : x.args.length = 6 := rfl
  obtain ⟨hw19, hw24, hn24, -, -⟩ := VsCtx.nums hx
  have hp := VsCtx.p_le hx
  have hkc := hb.hkc
  rw [VsCtx.vsAllocSz_sum] at hkc
  obtain ⟨B1, -, B4, B5, B6, -, -, B9, -, B11, B12, B18⟩ := bases_of (x := x)
  have B13 := VsCtx.base_13 (x := x)
  obtain ⟨hm1, hm2⟩ := hD.hbmIn
  have hl1 : (x.bw.getD 1 []).length = 156 := VsCtx.bw_len hx (j := 1) (by norm_num)
  have hl4 : (x.bw.getD 4 []).length = 153 := VsCtx.bw_len hx (j := 4) (by norm_num)
  have hl6 : (x.bw.getD 6 []).length = 24 := VsCtx.bw_len hx (j := 6) (by norm_num)
  have hl9 : (x.bw.getD 9 []).length = 24 := VsCtx.bw_len hx (j := 9) (by norm_num)
  have hhg : ∀ t ≤ 5, x.hgS t ≤ 24 := fun t ht => VsCtx.hgS_le hx (by omega)
  have hchw := hD.hchw
  have hchd := hD.hchd
  have e1076 : vsVal x.rd0 x.w x.args (.n 1076) = ptrAt D.bm :=
    (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC16_eq (.n 1076) (by simp)).trans hD.hbm
  have hC : ∀ i, Own i → Own i ∨ x.R i ∨ st.D i := fun i h => Or.inl h
  have own : ∀ i, x.cur ≤ i → i < x.cur + 982 + 256 * x.p → Own i := fun i h1 h2 => VsCtx.own hO h1 h2
  have rsw : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt D.bm) (x.sw D.bm 0 144) := fun rd hW => by
    have h := VsCtx.sw_reads hx hW hm1 0 144
    rwa [Nat.add_zero] at h
  have r19 : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt (x.base 13)) (x.cells19.map Prod.snd) := fun rd hW => by
    have h := hW _ (VsCtx.mem_Wo hx (j := 13) (by norm_num))
    simp only [VsCtx.Lw_getD hx (show 13 < 24 by omega), ↓reduceIte] at h
    exact h
  have hfk : st.kc ≤ allocBase (x.al (ltNames.getD (x.wdS - 19) "")) (tpKc B2C.fs x.al x.hgS 5 st.kc) :=
    le_trans (tpKc_ge B2C.fs x.al x.hgS 5 st.kc) (le_allocBase _ _)
  have hB19 := VsCtx.bufAtL hx hb.hO (j := 13) (by norm_num) (C := fun i => Own i ∨ x.R i ∨ st.D i)
    (fun i h => Or.inl (hO i h)) (n := 12) (by simp [vsAllocSz, vsSz0])
  simp only [VsCtx.Lw_getD hx (show 13 < 24 by omega), ↓reduceIte] at hB19
  exact {
    B18 := VsCtx.bufC hx hO hb (j := 12) (by norm_num) (by norm_num) (by simp [vsAllocSz, vsSz0]) hC
    B1076 := ⟨e1076, by rw [VsCtx.sw_len hx hm1 (by omega)]; norm_num, rsw _ (VsCtx.holdsWords_rd0 hx),
      fun rd _ ho => rsw rd (hb.hO rd ho), fun j hj => Or.inl (own _ (by omega) (by omega))⟩
    B11 := VsCtx.bufC hx hO hb (j := 5) (by norm_num) (by norm_num) (by simp [vsAllocSz, vsSz0]) hC
    B10 := VsCtx.bufC hx hO hb (j := 4) (by norm_num) (by norm_num) (by simp [vsAllocSz, vsSz0]) hC
    B17 := VsCtx.bufC hx hO hb (j := 11) (by norm_num) (by norm_num) (by simp [vsAllocSz, vsSz0]) hC
    B19 := hB19
    hsel := fun t ht => by
      rcases Nat.eq_zero_or_pos t with rfl | h1
      · exact h6.n115
      · exact h6.sel t h1 ht
    hh := hhg
    h15 := VsCtx.ptr hx (j := 9) (by norm_num) vsW0_15
    hbv := h6.bv
    hts := fun t h1 h5 => by
      have := hhg t h5
      simp only [List.length_take, List.length_drop, hl4, hl9, hl1]
      omega
    hOt := fun j hj => Or.inl (own _ (by omega) (by omega))
    hO15 := fun j hj => Or.inl (own _ (by omega) (by omega))
    hOb := fun t h1 h5 j hj => by
      have := hhg t h5
      exact Or.inl (own _ (by omega) (by omega))
    hPtp := fun t h1 h5 rd h => by
      have hW := hb.hO rd h.2
      have hg := hhg t h5
      refine ⟨readsAt_slice (VsCtx.readsW hx hW (j := 4) (by norm_num) (by norm_num)) 89 _,
        readsAt_takeV (VsCtx.readsW hx hW (j := 9) (by norm_num) (by norm_num)) _, ?_⟩
      have r := readsAt_slice (VsCtx.readsW hx hW (j := 1) (by norm_num) (by norm_num)) (26 * t) (x.hgS t + 1)
      have hdl : x.hgS t < ((x.bw.getD 1 []).drop (26 * t)).length := by
        simp only [List.length_drop, hl1]; omega
      rw [← take_succ_getD hdl, VsCtx.getD_drop'] at r
      rwa [show x.base 1 + 26 * (t - 1) + 26 = x.base 1 + 26 * t by omega]
    rtp := hx.ret3.rtp
    hst := VsCtx.hst19 hx
    h409 := h6.n409
    hw19 := hw19
    hw24 := hw24
    hch := hD.hch
    h12 := VsCtx.ptr hx (j := 6) (by norm_num) vsW0_12
    h695 := VsCtx.n695 h6
    hrs := by simp only [List.length_take, hl6]; omega
    hsl := VsCtx.sw_len hx hm1 (by omega)
    hshs := by simp [VsCtx.cells19_length]
    hnus := by simp only [List.length_take, List.length_drop, hl4]; omega
    hid := hD.hid
    r2894 := hx.ret3.r2894
    hfp := fun q hq => by
      have hrs : ((x.bw.getD 6 []).take D.ch.width).length ≤ 24 := by simp only [List.length_take, hl6]; omega
      have hnu : (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take D.ch.d).length ≤ D.ch.d := by
        simp only [List.length_take]; omega
      simp only [ltIdx, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega
    hcl := fun q hq t ht => by
      have hrs : ((x.bw.getD 6 []).take D.ch.width).length ≤ 24 := by simp only [List.length_take, hl6]; omega
      have hnu : (((x.bw.getD 4 []).drop (89 + x.nS + x.wdS)).take D.ch.d).length ≤ D.ch.d := by
        simp only [List.length_take]; omega
      simp only [ltIdx, List.mem_cons, List.not_mem_nil, or_false] at hq
      refine Or.inl (Or.inr (own _ ?_ ?_)) <;>
        rcases hq with rfl | rfl | rfl | rfl <;> dsimp only at ht ⊢ <;> omega
    hPt := fun rd h => by
      have hW := hb.hO rd h.2
      refine ⟨readsAt_takeV (VsCtx.readsW hx hW (j := 6) (by norm_num) (by norm_num)) _, fun j hj => ?_, r19 rd hW, ?_⟩
      · have r := VsCtx.sw_reads hx hW hm1 80 64
        have hl : (x.sw D.bm 80 64).length = 64 := VsCtx.sw_len hx hm1 (by omega)
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact VsCtx.loadHolds_shift (r j (by omega))
      · have r := readsAt_slice (VsCtx.readsW hx hW (j := 4) (by norm_num) (by norm_num)) (89 + x.nS + x.wdS) D.ch.d
        rwa [show x.base 4 + (89 + x.nS + x.wdS) = x.base 4 + 89 + x.nS + x.wdS by omega] at r }

end

section
variable {x : VsCtx}

theorem vsW0_20 : Atom.hint (.alloc (.n (14 + 6)) 78) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_21 : Atom.hint (.alloc (.n (15 + 6)) 64) ∈ vsW0 := by simp [vsW0, vsW0a]
theorem vsW0_23 : Atom.hint (.alloc (.n (17 + 6)) 1) ∈ vsW0 := by simp [vsW0, vsW0a]

/-- `wC`'s three ring buffers' pointers. -/
theorem VsCtx.w_ring (hx : x.Hon) : x.w 3039 = ptrAt x.a1 ∧ x.w 3040 = ptrAt (x.a1 + 16) ∧ x.w 3553 = ptrAt (x.a1 + 80) := by
  have ha : x.args.length = 6 := rfl
  obtain ⟨h1, h2, h3⟩ := vsBase_wc x.cur x.p
  have e1 := vsW_ptr (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) (ret := x.ret) ha hx.hret (j := 21) (by norm_num)
  have e2 := vsW_ptr (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) (ret := x.ret) ha hx.hret (j := 22) (by norm_num)
  have e3 := vsW_ptr (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) (ret := x.ret) ha hx.hret (j := 23) (by norm_num)
  rw [h1] at e1
  rw [h2] at e2
  rw [h3] at e3
  exact ⟨e1, e2, e3⟩

/-- **`Ph35`'s honest inputs on an honest context**, at a state past the buffers whose memories hold the node's
words. -/
theorem ph35In_ctx (hx : x.Hon) {Own : ℕ → Prop} (hO : ∀ i, x.OwnB i → Own i) {s1 : St} (hs1a : s1.a = x.a1)
    (hs1O : ∀ rd, s1.O rd → HoldsWords rd x.Wo) (hs1k : x.cur + (vsAllocSz x.p).sum ≤ s1.kc)
    (h6 : x.Num6) {D : VsCtx.D3} (hD : D.Ok x) :
    Ph35In B2C.fs x.al B2C.cert 17 x.rd0 x.rd1 x.args x.cur x.p x.ret Own x.R x.Pre s1 x.qt (x.base 9) (x.base 14)
      (x.base 15) D.bm (D.bm + 144 + D.nx) (x.hgS 5) ((x.bw.getD 18 []).getD (D.bm - x.base 18 + (144 + D.nx)) 0)
      (x.bw.getD 15 []) (x.sw D.bm 0 144) (x.bw.getD 9 []) (x.sw D.bm 55 25) (x.sw D.bm 144 D.nx) D.op D.point
      ((x.bw.getD 15 []).take 64) D.kw D.s' := by
  have ha : x.args.length = 6 := rfl
  have hp := VsCtx.p_le hx
  have hkc := hs1k
  rw [VsCtx.vsAllocSz_sum] at hkc
  have hqt := VsCtx.qt_lt hx
  obtain ⟨-, -, -, -, -, -, -, B9, -, -, -, B18⟩ := bases_of (x := x)
  have B14 := VsCtx.base_14 (x := x)
  have B15 := VsCtx.base_15 (x := x)
  obtain ⟨hm1, hm2⟩ := hD.hbmIn
  have hl9 : (x.bw.getD 9 []).length = 24 := VsCtx.bw_len hx (j := 9) (by norm_num)
  have hl15 : (x.bw.getD 15 []).length = 64 := VsCtx.bw_len hx (j := 15) (by norm_num)
  have hl18 : (x.bw.getD 18 []).length = 256 * x.p := VsCtx.bw_len hx (j := 18) (by norm_num)
  have h5 : x.hgS 5 ≤ 24 := VsCtx.hgS_le hx (by norm_num)
  have hopl := hD.hopl
  have hptl := hD.hptl
  have h14 : (vsAllocSz x.p).getD 14 0 = 78 := rfl
  have hcap : qkeccakVarsCap = 39 := rfl
  have h11 : (2 : ℕ) ^ winTabBits = 2048 := rfl
  have a1e : x.a1 = x.cur + (824 + 256 * x.p) + 14 := rfl
  obtain ⟨w39, w40, w53⟩ := VsCtx.w_ring hx
  obtain ⟨b21, b22, b23⟩ := VsCtx.base_wc (x := x)
  have own : ∀ i, x.cur ≤ i → i < x.cur + 982 + 256 * x.p → Own i := fun i h1 h2 => VsCtx.own hO h1 h2
  have hnx : (x.sw D.bm 144 D.nx).length = D.nx := VsCtx.sw_len hx hm1 (by omega)
  have rsw : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt D.bm) (x.sw D.bm 0 144) := fun rd hW => by
    have h := VsCtx.sw_reads hx hW hm1 0 144
    rwa [Nat.add_zero] at h
  have rnz : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt (D.bm + 144 + D.nx))
      [(x.bw.getD 18 []).getD (D.bm - x.base 18 + (144 + D.nx)) 0] := fun rd hW => by
    have h := VsCtx.sw_reads hx hW hm1 (144 + D.nx) 1
    rw [VsCtx.sw, take_one_drop (by omega), ← Nat.add_assoc] at h
    exact h
  have rbuf : ∀ rd, HoldsWords rd x.Wo → ∀ j, j < 24 → j ≠ 13 → ReadsAt rd (ptrAt (x.base j)) (x.bw.getD j []) :=
    fun rd hW j hj h13 => VsCtx.readsW hx hW hj h13
  have hW0 := VsCtx.holdsWords_rd0 hx
  have hpre : ∀ rd, x.Pre rd → ExpWinTab rd (ptrAt x.qt) := fun rd h => by obtain ⟨⟨_, h2⟩, _⟩ := h; exact h2
  exact {
    h120 := h6.sel 5 (by norm_num) le_rfl
    h15 := VsCtx.ptr hx (j := 9) (by norm_num) vsW0_15
    h20 := VsCtx.ptr hx (j := 14) (by norm_num) vsW0_20
    h21 := VsCtx.ptr hx (j := 15) (by norm_num) vsW0_21
    h4 := vsVal_param ha (i := 4) (by norm_num)
    hτ0 := hD.hτ0
    hτ1 := hD.hτ1
    hτc := by omega
    houts := VsCtx.sw_len hx hm1 (by omega)
    hcar := hD.hcar
    hrun := hD.hrun
    hpend := hD.hpend
    hsl := by simp only [List.length_take, hl15]; omega
    rvk := fun j hj σ => by rw [hnx]; exact hD.rvk j hj σ
    hfv := fun q hq => by
      simp only [vkIdx, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try rw [h11]) <;> omega
    hcv := fun q hq t ht => by
      simp only [vkIdx, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at ht ⊢
      all_goals first
        | exact Or.inl (Or.inr (own _ (by omega) (by omega)))
        | exact Or.inl (Or.inl (by
            rw [show x.qt + 178 + t = x.qt + (t + 178) by omega]
            exact VsCtx.R_tab (lt_of_lt_of_le ht (le_of_eq rfl))))
    hPk := fun rd h => by
      have hW := hs1O rd h.2
      refine ⟨VsCtx.pre_win rd h.1, rbuf rd hW 9 (by norm_num) (by norm_num), VsCtx.sw_reads hx hW hm1 55 25,
        VsCtx.sw_reads hx hW hm1 144 D.nx, ?_, ?_, readsAt_takeV (rbuf rd hW 15 (by norm_num) (by norm_num)) 64⟩
      · have r := readsAt_takeV (rbuf rd hW 14 (by norm_num) (by norm_num)) D.op.length
        rwa [← hD.hop] at r
      · have r := readsAt_slice (rbuf rd hW 14 (by norm_num) (by norm_num)) qkeccakVarsCap D.point.length
        rwa [← hD.hpt] at r
    hw2920 := VsCtx.w_retC hx (i := 2920) (by decide) fun σ => by
      rw [hD.rvk 5 (by norm_num) σ]
      show ptrAt (D.bm + 144) * gen ^ D.nx = _
      rw [ptrAt_mul_pow]
    r0cs := rnz _ hW0
    hOcs := fun rd _ ho => rnz rd (hs1O rd ho)
    hOwncs := own _ (by omega) (by omega)
    hl0 := VsCtx.lowDef_rd0 (x := x) 17
    rt := hpre _ (VsCtx.pre_rd0 hx)
    hPt := hpre
    hRq := fun j hj => VsCtx.R_tab hj
    hwin := (vsW_gcWin ha hx.hret hx.bw3.fresh).2.2
    hlow := hx.bw3.hlow
    hw3039 := by rw [hs1a]; exact w39
    hw3040 := by rw [hs1a]; exact w40
    hw3553 := by rw [hs1a]; exact w53
    hOwn := fun j hj => own _ (by omega) (by omega)
    hak := by omega
    r39 := by
      rw [hs1a, ← b21]
      have h := rbuf _ hW0 21 (by norm_num) (by norm_num)
      rw [hx.bw3.b21] at h
      exact h
    hO39 := fun rd _ ho => by
      rw [hs1a, ← b21]
      have h := rbuf _ (hs1O rd ho) 21 (by norm_num) (by norm_num)
      rw [hx.bw3.b21] at h
      exact h
    r40 := by
      rw [hs1a, ← b22]
      have h := rbuf _ hW0 22 (by norm_num) (by norm_num)
      rw [hx.bw3.b22] at h
      exact h
    hO40 := fun rd _ ho => by
      rw [hs1a, ← b22]
      have h := rbuf _ (hs1O rd ho) 22 (by norm_num) (by norm_num)
      rw [hx.bw3.b22] at h
      exact h
    hl21 := by omega
    r21 := rbuf _ hW0 15 (by norm_num) (by norm_num)
    hO21 := fun rd _ ho => rbuf _ (hs1O rd ho) 15 (by norm_num) (by norm_num)
    hOwn21 := fun j hj => own _ (by omega) (by omega)
    hwm := hD.hbm
    hlm := by rw [VsCtx.sw_len hx hm1 (by omega)]
    rm := rsw _ hW0
    hOm := fun rd _ ho => rsw rd (hs1O rd ho)
    hcm := fun j hj => Or.inl (Or.inr (own _ (by omega) (by omega)))
    r53 := by
      rw [hs1a, ← b23]
      have h := rbuf _ hW0 23 (by norm_num) (by norm_num)
      rw [hD.b23] at h
      exact h
    hO53 := fun rd _ ho => by
      rw [hs1a, ← b23]
      have h := rbuf _ (hs1O rd ho) 23 (by norm_num) (by norm_num)
      rw [hD.b23] at h
      exact h
    r3810 := hD.r3810 }

end

section
variable {x : VsCtx}

/-- `.n 42`, the stream's chunk count, and `.n 55`, the stream's buffer. -/
theorem VsCtx.v42_55 (hx : x.Hon) :
    vsVal x.rd0 x.w x.args (.n 42) = gen ^ x.p ∧ vsVal x.rd0 x.w x.args (.n 55) = ptrAt (x.base 18) := by
  have ha : x.args.length = 6 := rfl
  have g42 := vsW0_good (rd0 := x.rd0) (w := x.w) ha (a := .hint (.witness "stream_chunks" (.stack [.n 42])))
    (by simp [vsW0, vsW0a])
  have g55 := vsW0_good (rd0 := x.rd0) (w := x.w) ha (a := .hint (.allocDyn (.n 55) (.n 54)))
    (by simp [vsW0, vsW0a, vsW0b])
  simp only [Good, List.mem_singleton, forall_eq] at g42 g55
  refine ⟨g42.trans (vsW_42 (rd1 := x.rd1) (cur := x.cur) (ret := x.ret) ha hx.hret), g55.trans ?_⟩
  rw [VsCtx.base, vsBases_getD x.cur x.p (by norm_num)]
  exact vsW_ptr (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) (ret := x.ret) ha hx.hret (j := 18)
    (by norm_num)

/-- **`PhOpen`'s honest inputs on an honest context**, at a state at `x.ec 15` whose memories hold the node's words
and `certify_stack`'s placed stack, its buffers claimed. -/
theorem phOpenIn_ctx (hx : x.Hon) {Own : ℕ → Prop} (hO : ∀ i, x.OwnB i → Own i) {s2 : St}
    (hs2O : ∀ rd, s2.O rd → HoldsWords rd x.Wo) (hs2k : s2.kc = x.ec 15) (hs2D : ∀ i, x.StkCells i → s2.D i)
    (hs2P : ∀ rd, x.Pre rd → s2.O rd →
      Stack.StackPlaced rd x.lay (x.σ0 (.n 485)) (x.σ0 (.n 486)) (x.σ0 (.n 487)))
    {D : VsCtx.D3} (hD : D.Ok x) :
    PhOpenIn B2C.fs x.al B2C.cert 17 x.rd0 x.rd1 x.args x.cur x.p x.ret Own x.R x.Pre s2 (x.base 17) D.bm
      (x.bw.getD 17 []) (x.sw D.bm 0 144) D.sl (D.bm + 144 + D.nx) x.qt (x.σ0 (.n 96)) (x.σ0 (.n 134))
      (x.σ0 (.n 137)) [x.σ0 (.n 3033), x.σ0 (.n 3034), x.σ0 (.n 3035), x.σ0 (.n 3036), x.σ0 (.n 3037)]
      D.Ro D.Do D.Oo D.Po D.Qo (B2C.fs (openName D.sl)) (x.ec 16) (x.base 18)
      (D.bm + 144 + D.nx + 1 + D.nxo - x.base 18) x.p D.wE D.bp D.bp1 D.nxo D.layout D.link D.chi D.r D.qPoint D.kOut
      D.kIn D.f D.g D.xq D.z D.rho D.lam D.rm D.outputs D.keccakSlices D.oodValue D.v0 D.v1 D.claims D.carr := by
  have ha : x.args.length = 6 := rfl
  have hp := VsCtx.p_le hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, B18⟩ := bases_of (x := x)
  have B17 := VsCtx.base_17 (x := x)
  obtain ⟨hm1, hm2⟩ := hD.hbmIn
  have hl17 : (x.bw.getD 17 []).length = 1 := VsCtx.bw_len hx (j := 17) (by norm_num)
  have own : ∀ i, x.cur ≤ i → i < x.cur + 982 + 256 * x.p → Own i := fun i h1 h2 => VsCtx.own hO h1 h2
  have rsw : ∀ rd, HoldsWords rd x.Wo → ReadsAt rd (ptrAt D.bm) (x.sw D.bm 0 144) := fun rd hW => by
    have h := VsCtx.sw_reads hx hW hm1 0 144
    rwa [Nat.add_zero] at h
  have hW0 := VsCtx.holdsWords_rd0 hx
  have w2920 : x.w 2920 = ptrAt (D.bm + 144 + D.nx) := VsCtx.w_retC hx (i := 2920) (by decide) fun σ => by
    rw [hD.rvk 5 (by norm_num) σ]
    show ptrAt (D.bm + 144) * gen ^ D.nx = _
    rw [ptrAt_mul_pow]
  obtain ⟨v42, v55⟩ := VsCtx.v42_55 hx
  exact {
    h23 := VsCtx.ptr hx (j := 17) (by norm_num) vsW0_23
    hl23 := by omega
    r23 := VsCtx.readsW hx hW0 (j := 17) (by norm_num) (by norm_num)
    hO23 := fun rd _ ho => VsCtx.readsW hx (hs2O rd ho) (j := 17) (by norm_num) (by norm_num)
    hc23 := Or.inl (own _ (by omega) (by omega))
    h1076 := (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC16_eq (.n 1076) (by simp)).trans hD.hbm
    hlm := by rw [VsCtx.sw_len hx hm1 (by omega)]; norm_num
    rm' := rsw _ hW0
    hOm := fun rd _ ho => rsw rd (hs2O rd ho)
    hcm := fun j hj => Or.inl (own _ (by omega) (by omega))
    h16 := hD.h16
    h30 := hD.h30
    h489 := hD.h489
    h96 := rfl
    hfsv := rfl
    h134 := rfl
    h137 := rfl
    h2920 := (vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC35_eq (.n 2920) (by simp)).trans w2920
    h4 := vsVal_param ha (i := 4) (by norm_num)
    hos := by rw [hs2k]; exact hD.hos
    ro := hD.ro
    hRo := fun i h => (hD.hRo i h).elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inl (Or.inr (hO i h)))
    hPo := fun rd h => hD.hPo rd h.1 (hs2O rd h.2)
    hc := by omega
    hpk := by norm_num; omega
    hie := by omega
    h55 := v55
    h42 := v42
    hcl := hD.hcl
    hsl := hD.hsl
    hid := hD.hsid
    hcarr := hD.hcarr
    hfc := hD.hfc
    hcc := fun q hq t ht => by
      rcases hD.hcc q hq t ht with (h | h) | (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (hO _ h))
      · exact Or.inr (Or.inl (hs2D _ h))
      · exact Or.inr (Or.inr h)
    hPc := fun rd h => hD.hPc rd h.1 (hs2O rd h.2.1) (by rw [hD.hlay]; exact hs2P rd h.1 h.2.1) h.2.2 }

/-- **The export's and the end's facts on an honest context.** -/
theorem endOk_ctx (hx : x.Hon) {O : Reader → Prop} {D : VsCtx.D3} (hD : D.Ok x) (hOo : ∀ rd, O rd → D.Oo rd) :
    EndOk x O D.Qo := by
  obtain ⟨layout, r, hann, -, -⟩ := frontNum_of_child hx.ok.child
  have hl : x.lay = layout := by simp [VsCtx.lay, hann]
  have b0 := hx.bw3.b0
  have b3 := hx.bw3.b3
  rw [hl] at b0 b3
  exact ⟨hx.bw3.fresh, hx.bw3.hpt, fun rd hl0 hp ho t hq => hD.hQo rd hl0 hp (hOo rd ho) t hq, layout, r, hann,
    b0, b3, hx.bw3.b8, hx.bw3.b2⟩

/-- **`Ph12EndP` on an honest context** at a boundary state with `Carry11` (so `st.kc = x.ec 12` and
`certify_stack`'s stack, `StkAt`). -/
theorem ph12EndP_ctx {al : String → Bool} (hal : x.al = al) (hx : x.Hon) {Own : ℕ → Prop}
    (hO : ∀ i, x.OwnB i → Own i) {st : St} (hb : x.Bnd st) (h11 : x.Carry11 st) :
    Ph12EndP al x Own st (x.ec 13) (x.ec 14) (x.ec 15) := by
  subst hal
  obtain ⟨-, h6, hk, hS⟩ := h11
  obtain ⟨D, hD⟩ := hx.bw3.d3
  obtain ⟨c12, c13, c14, -⟩ := VsCtx.ecChain hD
  have hkc := hb.hkc
  have hlt := hD.hlt
  rw [← hk] at hlt
  have hrt := hD.hrt
  rw [← hb.ha] at hrt
  unfold Ph12EndP
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ph1213In_ctx hx hO hb h6 hD, hlt, ?_⟩
  unfold KecEndP
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ph35In_ctx hx hO (s1 := ⟨st.a, x.ec 13, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet]⟩) hb.ha (fun rd h => hb.hO rd h.1) (by dsimp only; omega)
      h6 hD, hD.hvk, hrt, ?_⟩
  unfold OpenEnd
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    phOpenIn_ctx hx hO ?_ ?_ ?_ ?_ hD, rfl, endOk_ctx hx hD ?_⟩
  · intro rd h; exact hb.hO rd h.1.1.1
  · rfl
  · intro i h; exact Or.inl (Or.inl (Or.inl (hS.1 i h)))
  · intro rd hp h; exact hS.2 rd hp h.1.1.1
  · intro rd h; exact h.1.2

/-- **`check_stack_terminal` within `2^24` of its cursor** at the compiled frames, unconditionally. -/
theorem cstE_b2c {al : String → Bool} :
    CheckStackTerminalCompleteAE B2C.fs al B2C.cert 17 fun c e => e ≤ c + 2 ^ 24 :=
  (cst_completeAE (by norm_num)).mono fun _ _ h => h LeanVM.Guest.Complete.fs_lt16

/-- **`Ph12toEndP`** at every alignment: `Carry11` carries `certify_stack`'s stack, `check_stack_terminal`'s end
bounded by `cstE_b2c`. -/
theorem ph12toEndP_ctx (al : String → Bool) : Ph12toEndP al :=
  ph12toEndP_of cstE_b2c fun _ hal hx _ _ hO _ hb h11 _ => ph12EndP_ctx hal hx hO hb h11

end

end
end LeanVM.Guest.B1.VsC
