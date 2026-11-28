/-
  LeanVM.Guest.B1.VsC.VsOrcPh7

  `Ph7Hyp` at the honest oracle: the packed point's eq tensor, `state_ends`, `link_rounds__L1_L0`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPhC

/-!
# `Ph7` at the honest values

`Ph7In`: what the honest values give `wC`'s windows `9 ..< 13`, on the honest oracle `vsW rd1 args cur p ret`:
the opening's buffer `.n 10` (its words `xs10`), the eq buffer `.n 11` holding `eqLevels` of the packed
point (`.n 10`'s words `50 ..< 54`), `state_ends`' inputs and its returns as `ret`'s constants, and the
index side's chain of rounds `l` (the rounds' challenges at `.n 12`, the stream's words from `w 580`),
`ret`'s constants on `link_rounds`' returns. **`ph7Ok_at`**: `Ph7Ok` from it and `link_rounds__L1_L0`'s call at
a given end (`LrCall`, its region narrowed to the arrays' indices), the continuation there. **`ph7Ok_in`**: the
call from `VsLinkCalleesA.rounds_L1_L0`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- The index arrays `link_rounds__L1_L0` reads: the stream's words, the challenges, the window tables. -/
def ph7Arrs (s nw b12 wd qt : ℕ) : List (ℕ × ℕ) := [(s, nw), (b12, wd), (qt + 178, 2 ^ winTabBits)]

/-- **`Ph7`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure Ph7In (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b8 b10 b11 b12 qt n wd s nw : ℕ) (xs10 zs cs : List E) (l : List (E × RSt)) : Prop where
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  B10 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 10 b10 56 xs10
  B11 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 11 b11 30 (eqLevels (ph7Rs xs10) 4)
  h408 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 408) = gen ^ n
  h409 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 409) = gen ^ wd
  h8 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 8) = ptrAt b8
  hz : zs.length = wd
  hcs : cs.length = wd
  hOz : ∀ j < wd, Own (b10 + 89 + n + j)
  hO8 : ∀ j < wd, Own (b8 + j)
  hPse : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89 + n)) zs ∧ ReadsAt rd (ptrAt b8) cs
  r752 : ∀ σ, ret 752 σ = prodE (zs.map (1 + ·))
  r753 : ∀ σ, ret 753 σ = endsProd cs zs
  h12 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 12) = ptrAt b12
  h4 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 4) = ptrAt qt
  hw580 : vsW rd1 args cur p ret 580 = ptrAt s
  hl : l.length = wd
  hcur : (chainLast (ph7St0 (vsW rd1 args cur p ret) xs10) l).cur = vsW rd1 args cur p ret 580 * gen ^ nw
  hcells : (chainLast ⟨[], 0, 0⟩ l).cells.length = 7
  rl : ∀ j < 7, ∀ σ, ret (767 + j) σ = (chainLast ⟨[], 0, 0⟩ l).cells.getD j 0
  hfp : ∀ q ∈ ph7Arrs s nw b12 wd qt, q.1 + q.2 ≤ ph7Fp fs al wd st.kc
  hOs : ∀ t < nw, Own (s + t)
  hO12 : ∀ j < wd, Own (b12 + j)
  hRq : ∀ j < 2 ^ 11, R (qt + (j + 178))
  hPc : ∀ rd, Pre rd ∧ st.O rd → RoundChain rd 1 0 (ph7St0 (vsW rd1 args cur p ret) xs10) l ∧
    ReadsAt rd (ptrAt b12) (l.map Prod.fst)

theorem winTabBits_eq : winTabBits = 11 := rfl

theorem tabs_ptr (qt : ℕ) : ptrAt qt * word 365917469723852800 0 = ptrAt (qt + 178) := by
  rw [word_g178', ptrAt_mul_pow]

/-- The returns `[w (i0 + j)]` of a list of `ret`'s constants. -/
theorem vsW_rets {rd1 : Reader} {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} (ha : args.length = 6)
    (hr : CausalRule ret) {i0 : ℕ} {cs : List E} (hp : ∀ j < cs.length, vsPlain (i0 + j))
    (hc : ∀ j < cs.length, ∀ σ, ret (i0 + j) σ = cs.getD j 0) :
    (List.range cs.length).map (fun j => vsW rd1 args cur p ret (i0 + j)) = cs := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [vsW_retC ha hr (hp j h2) (hc j h2), List.getD_eq_getElem _ _ h2]

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`Ph7` at the honest values, at a given end**: `Ph7Ok` from `Ph7In` and `link_rounds__L1_L0`'s call at
the end `ec`, the continuation at `ec`. -/
theorem ph7Ok_at (ha : args.length = 6) (hr : CausalRule ret) {st : St}
    {K : St → Prop} {b8 b10 b11 b12 qt n wd s nw : ℕ} {xs10 zs cs : List E} {l : List (E × RSt)}
    (H : Ph7In fs al cert k rd0 rd1 args cur p ret Own R Pre st b8 b10 b11 b12 qt n wd s nw xs10 zs cs l) {ec : ℕ}
    (hc : LrCall fs al cert k (vsW rd1 args cur p ret 680) (vsW rd1 args cur p ret 681)
      (vsW rd1 args cur p ret 682) (vsW rd1 args cur p ret 683) (vsW rd1 args cur p ret 684)
      (vsW rd1 args cur p ret 580) (lrClaim (vsW rd1 args cur p ret 752) (vsW rd1 args cur p ret 753)
        (xs10.getD 6 0) (xs10.getD 7 0)) (ptrAt b12) (ptrAt qt * word 365917469723852800 0) l nw
      (ph7Fp fs al wd st.kc) ec)
    (hK : st.kc ≤ ec → K ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ [PostQuiet, PostQuiet]⟩) :
    Ph7Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  set w := vsW rd1 args cur p ret with hw
  have hl10 := H.B10.len
  have hrsl : (ph7Rs xs10).length = 4 := by simp [ph7Rs]; omega
  have hne : l ≠ [] := fun h => by have := H.hl; rw [h] at this; simp at this; have := H.hw19; omega
  -- the callee
  have harr : lrArrays (w 580) (ptrAt b12) (ptrAt qt * word 365917469723852800 0) nw l.length =
      (ph7Arrs s nw b12 wd qt).map fun q => (ptrAt q.1, q.2) := by
    rw [show w 580 = ptrAt s from H.hw580, tabs_ptr, H.hl]; rfl
  unfold LrCall at hc
  have hkc : st.kc ≤ ec := by
    have hc0 := hc
    obtain ⟨_, _, hce, _⟩ := hc0
    have h1 := le_allocBase (al (seNames.getD (wd - 19) "")) st.kc
    have h2 := le_allocBase (al "link_rounds__L1_L0") (leafEnd fs al (seNames.getD (wd - 19) "") st.kc)
    simp only [ph7Fp, leafEnd] at hce h2 ⊢
    omega
  rw [harr, H.hl] at hc
  have hc := CallAtA.idxR hc
  have hrets : (chainLast ⟨[w 680, w 681, w 682, w 683, w 684], w 580,
      lrClaim (w 752) (w 753) (xs10.getD 6 0) (xs10.getD 7 0)⟩ l).cells =
      [w 767, w 768, w 769, w 770, w 771, w 772, w 773] := by
    rw [chainLast_ne hne _ ⟨[], 0, 0⟩]
    have e := vsW_rets (rd1 := rd1) (cur := cur) (p := p) ha hr (i0 := 767) (cs := (chainLast ⟨[], 0, 0⟩ l).cells)
      (fun j hj => by rw [H.hcells] at hj; interval_cases j <;> decide) (fun j hj σ => H.rl j (by rw [H.hcells] at hj; exact hj) σ)
    rw [← e, H.hcells]; rfl
  rw [hrets] at hc
  refine ⟨b8, b10, b11, b12, qt, n, wd, xs10, eqLevels (ph7Rs xs10) 4, ph7Rs xs10, zs, cs, xs10.getD 6 0,
    xs10.getD 7 0, _, _, _, _, _, _, ec, ⟨H.hw19, H.hw24, H.B10.ptr, H.B10.len, H.B10.r0, H.B10.rO, H.B10.cell,
    hrsl, fun t ht => ?_, H.B10.getD (by omega), H.B10.getD (by omega), H.B11.ptr, H.B11.len, H.B11.r0, H.B11.rO,
    H.B11.cell, eqLevels_lev (by omega), H.h408, H.h409, H.h8, H.hz, H.hcs, H.hOz, H.hO8, H.hPse,
    ⟨vsW_retC ha hr (by decide) H.r752, vsW_retC ha hr (by decide) H.r753⟩, H.h12, H.h4, hc, ?_, ?_⟩, hK hkc⟩
  · rw [ph7Rs, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_take, List.getElem_drop,
      List.getElem?_eq_getElem (by omega)]
  · rintro i ⟨q, hq, t, ht, rfl⟩
    simp only [ph7Arrs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact Or.inl (Or.inr (H.hOs t ht))
    · exact Or.inl (Or.inr (H.hO12 t ht))
    · refine Or.inl (Or.inl ?_)
      show R (qt + 178 + t)
      rw [show qt + 178 + t = qt + (t + 178) by omega]
      exact H.hRq t (by rw [winTabBits_eq] at ht; exact ht)
  · intro rd hrd
    obtain ⟨h1, h2⟩ := H.hPc rd hrd
    exact ⟨fun h => absurd rfl h, h1, h2⟩

/-- **`Ph7` at the honest values**: `Ph7Ok` from `Ph7In`, `link_rounds__L1_L0` from the link callees. -/
theorem ph7Ok_in (hL : VsLinkCalleesA fs al cert k) (ha : args.length = 6) (hr : CausalRule ret) {st : St}
    {K : St → Prop} {b8 b10 b11 b12 qt n wd s nw : ℕ} {xs10 zs cs : List E} {l : List (E × RSt)}
    (H : Ph7In fs al cert k rd0 rd1 args cur p ret Own R Pre st b8 b10 b11 b12 qt n wd s nw xs10 zs cs l)
    (hK : ∀ ec, st.kc ≤ ec → K ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ [PostQuiet, PostQuiet]⟩) :
    Ph7Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  set w := vsW rd1 args cur p ret with hw
  have harr : lrArrays (w 580) (ptrAt b12) (ptrAt qt * word 365917469723852800 0) nw l.length =
      (ph7Arrs s nw b12 wd qt).map fun q => (ptrAt q.1, q.2) := by
    rw [show w 580 = ptrAt s from H.hw580, tabs_ptr, H.hl]; rfl
  obtain ⟨ec, hc⟩ := lrCall_of hL.rounds_L1_L0 (f0 := w 680) (f1 := w 681) (f2 := w 682) (f3 := w 683)
    (f4 := w 684) (cur := w 580) (cl := lrClaim (w 752) (w 753) (xs10.getD 6 0) (xs10.getD 7 0))
    (point := ptrAt b12) (tabs := ptrAt qt * word 365917469723852800 0) (l := l) (nw := nw)
    (fp := ph7Fp fs al wd st.kc) (by rw [H.hl]; have := H.hw24; omega)
    (by rw [show w 580 = ptrAt s from H.hw580, ptrAt_eq_pow]; exact pow_ne_zero _ Value.gen_ne_zero) H.hcur
    (by rw [harr]; exact ptrsBelow_idx H.hfp)
  exact ph7Ok_at ha hr H hc (hK ec)

end

end
end LeanVM.Guest.B1.VsC
