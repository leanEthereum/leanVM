/-
  LeanVM.Guest.B1.VsC.VsOrcPh1213

  `Ph1213Hyp` at the honest oracle: the five table points, `link_terminal__L{w}`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh1011

/-!
# `Ph1213` at the honest values

`Ph1213In`: `Ph1213Hyp`'s buffer facts, the table points' returns as `ret`'s constants, and for
`link_terminal__L{w}` its inputs (the point `rs` at `.n 12`, the slices `sl` past the cursor `.n 1076`'s word `80`,
the shift coefficients `shs` at `.n 19`, the chunks' `ν` at `.n 695`) with the terminal identity
`w 1077 = summand + rest` on `w32`'s values `.n 2846` (`coef`), `.n 2891` (`cert_w`), `.n 2890` (`rest`).
**`ph1213Ok_in`**: `Ph1213Ok` from it, the callee from `VsLinkCalleesA.terminal` (its region narrowed to the
indices), its return `w 2894 = 0` a constant of `ret`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- **`Ph1213`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure Ph1213In (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b18 b1076 b11 b10 b17 b15 b19 b12 bnu wd : ℕ) (xs18 xs1076 xs11 xs10 xs17 xs19 : List E) (hg bb : ℕ → ℕ)
    (ts xs cs : ℕ → List E) (top : ℕ → E) (ch : Chunks) (rs sl shs nus : List E) : Prop where
  B18 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 18 b18 25 xs18
  B1076 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 1076 b1076 80
    xs1076
  B11 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 11 b11 30 xs11
  B10 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 10 b10 89 xs10
  B17 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 17 b17 95 xs17
  B19 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O (fun i => Own i ∨ R i ∨ st.D i) 19 b19 12 xs19
  hsel : ∀ t ≤ 5, vsVal rd0 (vsW rd1 args cur p ret) args (.n (115 + t)) = gen ^ hg t
  hh : ∀ t ≤ 5, hg t ≤ 24
  h15 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 15) = ptrAt b15
  hbv : ∀ t, 1 ≤ t → t ≤ 5 → vsVal rd0 (vsW rd1 args cur p ret) args (.n (tpBv t)) = ptrAt (bb t)
  hts : ∀ t, 1 ≤ t → t ≤ 5 → (ts t).length = hg t ∧ (xs t).length = hg t ∧ (cs t).length = hg t
  hOt : ∀ j < 24, Own (b10 + 89 + j) ∨ R (b10 + 89 + j) ∨ st.D (b10 + 89 + j)
  hO15 : ∀ j < 24, Own (b15 + j) ∨ R (b15 + j) ∨ st.D (b15 + j)
  hOb : ∀ t, 1 ≤ t → t ≤ 5 → ∀ j < hg t + 1, Own (bb t + 26 + j) ∨ R (bb t + 26 + j) ∨ st.D (bb t + 26 + j)
  hPtp : ∀ t, 1 ≤ t → t ≤ 5 → ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt (b10 + 89)) (ts t) ∧
    ReadsAt rd (ptrAt b15) (xs t) ∧ ReadsAt rd (ptrAt (bb t + 26)) (cs t ++ [top t])
  rtp : ∀ t, 1 ≤ t → t ≤ 5 → ∀ σ,
    ret (tpD t + 5) σ = xs10.getD t 0 * tpTotalG (ts t) (xs t) (cs t) (top t) (hg t) ∧
    ret (tpD t + 6) σ = 1 + (1 + top t) * tpPad (cs t) (xs t) ∧
    ret (tpD t + 7) σ = tpFullAt (ts t) (xs t) (hg t)
  hst : ∀ x ∈ stC32, MemF rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) x
  h409 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 409) = gen ^ wd
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  hch : Chunks.new wd = some ch
  h12 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 12) = ptrAt b12
  h695 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 695) = ptrAt bnu
  hrs : rs.length = ch.width
  hsl : sl.length = 64
  hshs : shs.length = 12
  hnus : nus.length = ch.d
  hid : LtIdentity ch (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret 1077) rs sl shs nus
  r2894 : ∀ σ, ret 2894 σ = 0
  hfp : ∀ q ∈ ltIdx b12 b1076 b19 bnu rs.length nus.length,
    q.1 + q.2 ≤ allocBase (al (ltNames.getD (wd - 19) "")) (tpKc fs al hg 5 st.kc)
  hcl : ∀ q ∈ ltIdx b12 b1076 b19 bnu rs.length nus.length, ∀ t < q.2,
    (R (q.1 + t) ∨ Own (q.1 + t)) ∨ st.D (q.1 + t)
  hPt : ∀ rd, Pre rd ∧ st.O rd → ReadsAt rd (ptrAt b12) rs ∧
    (∀ j < 64, LoadHolds rd (ptrAt b1076) (80 + j) (sl.getD j 0)) ∧ ReadsAt rd (ptrAt b19) shs ∧
    ReadsAt rd (ptrAt bnu) nus

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- A call's one return, rewritten. -/
theorem CallAtA.ret1 {f : String} {args : List E} {a b : E} {Rc Dc : ℕ → Prop} {Oc Pc : Reader → Prop}
    {Qc : Reader → Tree → Prop} {B fp c e : ℕ} (h : CallAtA fs al cert k f args [a] Rc Dc Oc Pc Qc B fp c e)
    (hb : b = a) : CallAtA fs al cert k f args [b] Rc Dc Oc Pc Qc B fp c e := hb ▸ h

theorem tpKc_ge (fs : String → ℕ) (al : String → Bool) (hg : ℕ → ℕ) : ∀ t kc, kc ≤ tpKc fs al hg t kc
  | 0, _ => le_rfl
  | t + 1, kc => le_trans (tpKc_ge fs al hg t kc) (le_trans (le_allocBase _ _) (Nat.le_add_right _ _))

theorem tpD_plain {t : ℕ} (h1 : 1 ≤ t) (h5 : t ≤ 5) {j : ℕ} (hj : 5 ≤ j) (hj' : j ≤ 7) : vsPlain (tpD t + j) := by
  interval_cases t <;> interval_cases j <;> decide

theorem ltIdx_ptr (b12 b1076 b19 bnu nr nnu : ℕ) :
    ltArrays (ptrAt b12) (ptrAt b1076) (ptrAt b19) (ptrAt bnu) nr nnu =
      (ltIdx b12 b1076 b19 bnu nr nnu).map fun q => (ptrAt q.1, q.2) := by
  simp only [ltArrays, ltIdx, List.map, ptrAt_mul_pow]

/-- **`Ph1213` at the honest values, at a given end**: `Ph1213Ok` from `Ph1213In` and `link_terminal__L{w}`'s call
at the end `ec`, the continuation at `ec`. -/
theorem ph1213Ok_at (ha : args.length = 6) (hr : CausalRule ret) {st : St}
    {K : St → Prop} {b18 b1076 b11 b10 b17 b15 b19 b12 bnu wd : ℕ} {xs18 xs1076 xs11 xs10 xs17 xs19 : List E}
    {hg bb : ℕ → ℕ} {ts xs cs : ℕ → List E} {top : ℕ → E} {ch : Chunks} {rs sl shs nus : List E}
    (H : Ph1213In fs al cert k rd0 rd1 args cur p ret Own R Pre st b18 b1076 b11 b10 b17 b15 b19 b12 bnu wd xs18
      xs1076 xs11 xs10 xs17 xs19 hg bb ts xs cs top ch rs sl shs nus) {ec : ℕ}
    (hc : LtCall fs al cert k wd (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret 1077) b12 b1076 b19
      bnu rs sl shs nus (allocBase (al (ltNames.getD (wd - 19) "")) (tpKc fs al hg 5 st.kc)) ec)
    (hK : K ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet]⟩) :
    Ph1213Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  unfold LtCall at hc
  rw [ltIdx_ptr] at hc
  have hc := CallAtA.idxR hc
  have hc := CallAtA.ret1 hc (vsW_retC (rd1 := rd1) (cur := cur) (p := p) ha hr (i := 2894) (by decide) H.r2894)
  refine ⟨b18, b1076, b11, b10, b17, b15, b19, wd, xs18, xs1076, xs11, xs10, xs17, xs19, hg, bb, ts, xs, cs, top,
    ptrAt b12, _, _, ptrAt bnu, _, _, _, _, _, _, _, ec, ⟨H.B18, H.B1076, H.B11, H.B10, H.B17, H.B19, H.hsel,
    H.hh, H.h15, H.hbv, H.hts, H.hOt, H.hO15, H.hOb, H.hPtp, fun t h1 h5 d hd => ?_, H.hst, H.h409, H.hw19,
    H.hw24, H.h12, rfl, rfl, H.h695, rfl, hc, ?_, fun rd hrd => H.hPt rd hrd⟩, hK⟩
  · subst hd
    exact ⟨vsW_retC ha hr (tpD_plain h1 h5 le_rfl (by omega)) fun σ => (H.rtp t h1 h5 σ).1,
      vsW_retC ha hr (tpD_plain h1 h5 (by omega) (by omega)) fun σ => (H.rtp t h1 h5 σ).2.1,
      vsW_retC ha hr (tpD_plain h1 h5 (by omega) le_rfl) fun σ => (H.rtp t h1 h5 σ).2.2⟩
  · rintro i ⟨q, hq, t, ht, rfl⟩
    exact H.hcl q hq t ht

/-- **`Ph1213` at the honest values**: `Ph1213Ok` from `Ph1213In`, `link_terminal__L{w}` from the link callees. -/
theorem ph1213Ok_in (hL : VsLinkCalleesA fs al cert k) (ha : args.length = 6) (hr : CausalRule ret) {st : St}
    {K : St → Prop} {b18 b1076 b11 b10 b17 b15 b19 b12 bnu wd : ℕ} {xs18 xs1076 xs11 xs10 xs17 xs19 : List E}
    {hg bb : ℕ → ℕ} {ts xs cs : ℕ → List E} {top : ℕ → E} {ch : Chunks} {rs sl shs nus : List E}
    (H : Ph1213In fs al cert k rd0 rd1 args cur p ret Own R Pre st b18 b1076 b11 b10 b17 b15 b19 b12 bnu wd xs18
      xs1076 xs11 xs10 xs17 xs19 hg bb ts xs cs top ch rs sl shs nus)
    (hK : ∀ ec, st.kc ≤ ec → K ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ List.replicate 5 PostQuiet ++ [PostQuiet]⟩) :
    Ph1213Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  obtain ⟨ec, hc⟩ := hL.terminal wd H.hw19 H.hw24 ch H.hch (ptrAt b12) (ptrAt b1076)
    (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2846)) (ptrAt b19)
    (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2891)) (ptrAt bnu)
    (vsVal rd0 (vsW rd1 args cur p ret) args (.n 2890)) (vsW rd1 args cur p ret 1077) rs sl shs nus
    (allocBase (al (ltNames.getD (wd - 19) "")) (tpKc fs al hg 5 st.kc)) H.hrs H.hsl H.hshs H.hnus H.hid
    (by rw [ltIdx_ptr]; exact ptrsBelow_idx H.hfp)
  obtain ⟨_, _, hce, _⟩ := id hc
  exact ph1213Ok_at ha hr H hc (hK ec (le_trans (tpKc_ge fs al hg 5 st.kc)
    (le_trans (le_allocBase _ _) (le_trans (Nat.le_add_right _ _) hce))))
end

end
end LeanVM.Guest.B1.VsC
