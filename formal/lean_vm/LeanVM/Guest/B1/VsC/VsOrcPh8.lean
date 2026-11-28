/-
  LeanVM.Guest.B1.VsC.VsOrcPh8

  `Ph8Hyp` at the honest oracle: `index_side`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh7

/-!
# `Ph8` at the honest values

`Ph8In`: `index_side__L{w}`'s inputs at the honest oracle `vsW rd1 args cur p ret`, its returns as `ret`'s
constants, its three arrays at disjoint index intervals below `2^63` (`arraysApart3`: `ArraysApart` from
the indices). **`ph8Ok_in`**: `Ph8Ok` from it.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Two index intervals apart. -/
def IvApart (a n b m : ℕ) : Prop := a + n ≤ b ∨ b + m ≤ a

/-- **Three pointer arrays at disjoint index intervals below `2^63` are apart.** -/
theorem arraysApart3 {a0 a1 a2 n0 n1 n2 : ℕ} (h0 : a0 + n0 ≤ 2 ^ 63) (h1 : a1 + n1 ≤ 2 ^ 63)
    (h2 : a2 + n2 ≤ 2 ^ 63) (d01 : IvApart a0 n0 a1 n1) (d02 : IvApart a0 n0 a2 n2) (d12 : IvApart a1 n1 a2 n2) :
    ArraysApart [ptrAt a0, ptrAt a1, ptrAt a2] [(0, n0), (1, n1), (2, n2)] := by
  unfold IvApart at d01 d02 d12
  intro q hq q' hq' a ha b hb he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq hq'
  have inj : ∀ {u v : ℕ}, u < 2 ^ 63 → v < 2 ^ 63 → addressOfIndex u = addressOfIndex v → u = v :=
    fun hu hv h => gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega) h
  rcases hq with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ, Main.addr_ofK] at he ha hb <;>
    have := inj (by omega) (by omega) he <;> first | exact ⟨rfl, by omega⟩ | omega

/-- **`Ph8`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure Ph8In (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b772 b12 bz b13 wd : ℕ) (v : E) (rs zs : List E) : Prop where
  hw19 : 19 ≤ wd
  hw24 : wd ≤ 24
  hw772 : vsW rd1 args cur p ret 772 = ptrAt b772
  r772 : ReadsAt rd0 (ptrAt b772) [v]
  hO772 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b772) [v]
  hc772 : Own b772 ∨ R b772 ∨ st.D b772
  h409 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 409) = gen ^ wd
  h12 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 12) = ptrAt b12
  h694 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 694) = ptrAt bz
  h13 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 13) = ptrAt b13
  hrs : rs.length = wd
  hzs : zs.length = wd
  hb : b12 + wd ≤ 2 ^ 63 ∧ bz + wd ≤ 2 ^ 63 ∧ b13 + (wd + 1) ≤ 2 ^ 63
  hd : IvApart b12 wd bz wd ∧ IvApart b12 wd b13 (wd + 1) ∧ IvApart bz wd b13 (wd + 1)
  hO12 : ∀ j < wd, Own (b12 + j)
  hOz : ∀ j < wd, Own (bz + j)
  hO13 : ∀ j < wd + 1, Own (b13 + j)
  hPis : ∀ rd, Pre rd ∧ st.O rd → HoldsArrays rd [ptrAt b12, ptrAt bz, ptrAt b13] (isIns rs zs) ∧
    HoldsArrays rd [ptrAt b12, ptrAt bz, ptrAt b13] (isOuts rs wd)
  r797 : ∀ σ, ret 797 σ = indexMle rs
  r798 : ∀ σ, ret 798 σ = (sideFold zs rs).1
  r799 : ∀ σ, ret 799 σ = (sideFold zs rs).2.1

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`Ph8` at the honest values.** -/
theorem ph8Ok_in (ha : args.length = 6) (hr : CausalRule ret) {st : St} {K : St → Prop}
    {b772 b12 bz b13 wd : ℕ} {v : E} {rs zs : List E}
    (H : Ph8In fs al cert k rd0 rd1 args cur p ret Own R Pre st b772 b12 bz b13 wd v rs zs)
    (hK : K ⟨st.a, allocBase (al (imNames.getD (wd - 19) "")) (allocBase (al (isNames.getD (wd - 19) "")) st.kc +
      fs (isNames.getD (wd - 19) "")) + fs (imNames.getD (wd - 19) ""), st.O, st.D, st.Qs ++ [PostQuiet]⟩) :
    Ph8Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K :=
  ⟨b772, b12, bz, b13, wd, v, rs, zs, ⟨H.hw19, H.hw24, H.hw772, H.r772, H.hO772, H.hc772, H.h409, H.h12, H.h694,
    H.h13, H.hrs, H.hzs, arraysApart3 H.hb.1 H.hb.2.1 H.hb.2.2 H.hd.1 H.hd.2.1 H.hd.2.2, H.hO12, H.hOz, H.hO13,
    H.hPis, vsW_retC ha hr (by decide) H.r797, vsW_retC ha hr (by decide) H.r798,
    vsW_retC ha hr (by decide) H.r799⟩, hK⟩

end

end
end LeanVM.Guest.B1.VsC
