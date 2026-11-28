/-
  LeanVM.Guest.B1.VsC.VsOrcPh9

  `Ph9Hyp` at the honest oracle: the split values, `link_row_side__L{c}`.
-/

module

public import LeanVM.Guest.B1.VsC.VsOrcPh8
public import LeanVM.Guest.B1.VsC.RowSideA

/-!
# `Ph9` at the honest values

`Ph9In`: `Ph9Hyp`'s buffer facts, and for `link_row_side__L{c}` the rows' chain `l1` (`n` rounds, its
challenges at `.n 15`) and the pointer columns' chain `l2` (`6` rounds, at `.n 16`) from the state after the
index side's rounds (`vsC_w13`'s permutation outputs `.n 790 … .n 794`, the cursor past the index side's
word, the claim `w 773`), `ret`'s constants on its returns. **`ph9Ok_at`**: `Ph9Ok` from it, the permutation's
outputs taken as `vsVal`'s, and the callee's call at a given end (`LrsCall`, its region narrowed to the
indices), the continuation there. **`ph9Ok_in`**: the call from `VsLinkCalleesA.row_side`.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- The index arrays `link_row_side__L{c}` reads: both chains' stream words, both points, the window tables. -/
def ph9Arrs (b772 nw1 nw2 b15 n b16 qt : ℕ) : List (ℕ × ℕ) :=
  [(b772 + 1, nw1), (b772 + 1 + nw1, nw2), (b15, n), (b16, 6), (qt + 178, 2 ^ winTabBits)]

/-- **`Ph9`'s honest inputs**, on the honest oracle `vsW rd1 args cur p ret`. -/
structure Ph9In (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ) (rd0 rd1 : Reader)
    (args : List E) (cur p : ℕ) (ret : ℕ → (ℕ → E) → E) (Own R : ℕ → Prop) (Pre : Reader → Prop) (st : St)
    (b10 b11 b13 b14 b15 b16 b772 m n cc qt nw1 nw2 : ℕ) (xs10 xs11 xs13 xs14 : List E)
    (l1 l2 : List (E × RSt)) : Prop where
  h13 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 13) = ptrAt b13
  hl13 : 20 ≤ xs13.length
  r13 : ReadsAt rd0 (ptrAt b13) xs13
  hO13 : ∀ rd, Pre rd → st.O rd → ReadsAt rd (ptrAt b13) xs13
  hOwn13 : ∀ j < xs13.length, Own (b13 + j)
  h101 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 101) = gen ^ m
  hm : m < xs13.length
  B14 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 14 b14 36 xs14
  B11 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 11 b11 30 xs11
  B10 : BufAt rd0 (vsVal rd0 (vsW rd1 args cur p ret) args) Pre st.O Own 10 b10 37 xs10
  hc6 : 6 ≤ cc
  hc9 : cc ≤ 9
  hw484 : vsW rd1 args cur p ret 484 = gen ^ cc
  hw772 : vsW rd1 args cur p ret 772 = ptrAt b772
  h15 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 15) = ptrAt b15
  h16 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 16) = ptrAt b16
  h408 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 408) = gen ^ n
  h4 : vsVal rd0 (vsW rd1 args cur p ret) args (.n 4) = ptrAt qt
  hn : n < 64
  hl1 : l1.length = n
  hl2 : l2.length = 6
  hcur1 : (chainLast (ph9St0 (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret) b772) l1).cur =
    ptrAt (b772 + 1) * gen ^ nw1
  hcur2 : (chainLast (chainLast (ph9St0 (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret) b772)
    l1) l2).cur = (chainLast (ph9St0 (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret) b772) l1).cur *
      gen ^ nw2
  hcells : (chainLast ⟨[], 0, 0⟩ l2).cells.length = 7
  rl : ∀ j < 7, ∀ σ, ret (1071 + j) σ = (chainLast ⟨[], 0, 0⟩ l2).cells.getD j 0
  hfp : ∀ q ∈ ph9Arrs b772 nw1 nw2 b15 n b16 qt, q.1 + q.2 ≤ allocBase (al (lrsNames.getD (cc - 6) "")) st.kc
  hOs : ∀ t < nw1 + nw2, Own (b772 + 1 + t)
  hO15 : ∀ j < n, Own (b15 + j)
  hO16 : ∀ j < 6, Own (b16 + j)
  hRq : ∀ j < 2 ^ 11, R (qt + (j + 178))
  hPc : ∀ rd, Pre rd ∧ st.O rd →
    WinTabs rd (ptrAt qt * word 365917469723852800 0) ∧
    RoundChain rd (cc + 1) (lrsGrind cc).1
      (ph9St0 (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret) b772) l1 ∧
    RoundChain rd cc (lrsGrind cc).2
      (chainLast (ph9St0 (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret) b772) l1) l2 ∧
    ReadsAt rd (ptrAt b15) (l1.map Prod.fst) ∧ ReadsAt rd (ptrAt b16) (l2.map Prod.fst)

section
variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k : ℕ} {rd0 rd1 : Reader}
  {args : List E} {cur p : ℕ} {ret : ℕ → (ℕ → E) → E} {Own R : ℕ → Prop} {Pre : Reader → Prop}

/-- **`Ph9` at the honest values, at a given end**: `Ph9Ok` from `Ph9In` and `link_row_side__L{c}`'s call at
the end `ec`, the continuation at `ec`. -/
theorem ph9Ok_at (ha : args.length = 6) (hr : CausalRule ret) {st : St}
    {K : St → Prop} {b10 b11 b13 b14 b15 b16 b772 m n cc qt nw1 nw2 : ℕ} {xs10 xs11 xs13 xs14 : List E}
    {l1 l2 : List (E × RSt)}
    (H : Ph9In fs al cert k rd0 rd1 args cur p ret Own R Pre st b10 b11 b13 b14 b15 b16 b772 m n cc qt nw1 nw2
      xs10 xs11 xs13 xs14 l1 l2) {ec : ℕ}
    (hc : LrsCall fs al cert k cc ((vsVal rd0 (vsW rd1 args cur p ret) args) (.n 790))
      ((vsVal rd0 (vsW rd1 args cur p ret) args) (.n 791)) ((vsVal rd0 (vsW rd1 args cur p ret) args) (.n 792))
      ((vsVal rd0 (vsW rd1 args cur p ret) args) (.n 793)) ((vsVal rd0 (vsW rd1 args cur p ret) args) (.n 794))
      (ptrAt (b772 + 1)) ((vsW rd1 args cur p ret) 773) (ptrAt b15) (ptrAt b16)
      (ptrAt qt * word 365917469723852800 0) l1 l2 nw1 nw2 (allocBase (al (lrsNames.getD (cc - 6) "")) st.kc) ec)
    (hK : st.kc ≤ ec → K ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ [PostQuiet]⟩) :
    Ph9Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  have hne : l2 ≠ [] := fun h => by have := H.hl2; rw [h] at this; simp at this
  have harr : lrsArrays (ptrAt (b772 + 1)) (chainLast (ph9St0 (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret) b772) l1).cur (ptrAt b15) (ptrAt b16)
      (ptrAt qt * word 365917469723852800 0) nw1 nw2 l1.length =
      (ph9Arrs b772 nw1 nw2 b15 n b16 qt).map fun q => (ptrAt q.1, q.2) := by
    rw [H.hcur1, ptrAt_mul_pow, tabs_ptr, H.hl1]; rfl
  unfold ph9St0 at harr
  unfold LrsCall at hc
  have hkc : st.kc ≤ ec := by
    have hc0 := hc
    obtain ⟨_, _, hce, _⟩ := hc0
    have h1 := le_allocBase (al (lrsNames.getD (cc - 6) "")) st.kc
    omega
  rw [harr, H.hl1] at hc
  have hc := CallAtA.idxR hc
  have hrets : (chainLast (chainLast ⟨[(vsVal rd0 (vsW rd1 args cur p ret) args) (.n 790), (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 791), (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 792), (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 793), (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 794)],
      ptrAt (b772 + 1), (vsW rd1 args cur p ret) 773⟩ l1) l2).cells = [(vsW rd1 args cur p ret) 1071, (vsW rd1 args cur p ret) 1072, (vsW rd1 args cur p ret) 1073, (vsW rd1 args cur p ret) 1074, (vsW rd1 args cur p ret) 1075, (vsW rd1 args cur p ret) 1076, (vsW rd1 args cur p ret) 1077] := by
    rw [chainLast_ne hne _ ⟨[], 0, 0⟩]
    have e := vsW_rets (rd1 := rd1) (cur := cur) (p := p) ha hr (i0 := 1071) (cs := (chainLast ⟨[], 0, 0⟩ l2).cells)
      (fun j hj => by rw [H.hcells] at hj; interval_cases j <;> decide)
      (fun j hj σ => H.rl j (by rw [H.hcells] at hj; exact hj) σ)
    rw [← e, H.hcells]; rfl
  rw [hrets] at hc
  refine ⟨b10, b11, b13, b14, b15, b16, b772, m, n, cc, qt, xs10, xs11, xs13, xs14, (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 790), (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 791),
    (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 792), (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 793), (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 794), _, _, _, _, _, _, ec, ⟨H.h13, H.hl13, H.r13, H.hO13, H.hOwn13, H.h101, H.hm,
    H.B14.ptr, H.B14.len, H.B14.r0, H.B14.rO, H.B14.cell, H.B11.ptr, H.B11.len, H.B11.r0, H.B11.rO, H.B11.cell,
    H.B10.ptr, H.B10.len, H.B10.r0, H.B10.rO, H.B10.cell, H.hc6, H.hc9, H.hw484, H.hw772,
    ⟨rfl, rfl, rfl, rfl, rfl⟩, H.h15, H.h16, H.h408, H.h4, hc, ?_, fun rd hrd => H.hPc rd hrd⟩, hK hkc⟩
  rintro i ⟨q, hq, t, ht, rfl⟩
  simp only [ph9Arrs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inr (H.hOs t (by simp only at ht; omega)))
  · refine Or.inl (Or.inr ?_)
    show Own (b772 + 1 + nw1 + t)
    rw [Nat.add_assoc (b772 + 1)]
    exact H.hOs (nw1 + t) (by simp only at ht; omega)
  · exact Or.inl (Or.inr (H.hO15 t ht))
  · exact Or.inl (Or.inr (H.hO16 t ht))
  · refine Or.inl (Or.inl ?_)
    show R (qt + 178 + t)
    rw [show qt + 178 + t = qt + (t + 178) by omega]
    exact H.hRq t (by rw [winTabBits_eq] at ht; exact ht)

/-- **`Ph9` at the honest values**: `Ph9Ok` from `Ph9In`, `link_row_side__L{c}` from the link callees. -/
theorem ph9Ok_in (hL : VsLinkCalleesA fs al cert k) (ha : args.length = 6) (hr : CausalRule ret) {st : St}
    {K : St → Prop} {b10 b11 b13 b14 b15 b16 b772 m n cc qt nw1 nw2 : ℕ} {xs10 xs11 xs13 xs14 : List E}
    {l1 l2 : List (E × RSt)}
    (H : Ph9In fs al cert k rd0 rd1 args cur p ret Own R Pre st b10 b11 b13 b14 b15 b16 b772 m n cc qt nw1 nw2
      xs10 xs11 xs13 xs14 l1 l2)
    (hK : ∀ ec, st.kc ≤ ec → K ⟨st.a, ec, fun rd => st.O rd ∧ True, fun i => st.D i ∨ False,
      st.Qs ++ [PostQuiet]⟩) :
    Ph9Ok fs al cert k rd0 (vsW rd1 args cur p ret) args Own R Pre st K := by
  have harr : lrsArrays (ptrAt (b772 + 1)) (chainLast (ph9St0 (vsVal rd0 (vsW rd1 args cur p ret) args) (vsW rd1 args cur p ret) b772) l1).cur (ptrAt b15) (ptrAt b16)
      (ptrAt qt * word 365917469723852800 0) nw1 nw2 l1.length =
      (ph9Arrs b772 nw1 nw2 b15 n b16 qt).map fun q => (ptrAt q.1, q.2) := by
    rw [H.hcur1, ptrAt_mul_pow, tabs_ptr, H.hl1]; rfl
  unfold ph9St0 at harr
  obtain ⟨ec, hc⟩ := lrsCall_of hL H.hc6 H.hc9 (f0 := (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 790))
    (f1 := (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 791)) (f2 := (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 792))
    (f3 := (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 793)) (f4 := (vsVal rd0 (vsW rd1 args cur p ret) args) (.n 794))
    (cur := ptrAt (b772 + 1)) (cl := (vsW rd1 args cur p ret) 773) (chi := ptrAt b15) (qp := ptrAt b16)
    (tabs := ptrAt qt * word 365917469723852800 0) (l1 := l1) (l2 := l2) (nw1 := nw1) (nw2 := nw2)
    (fp := allocBase (al (lrsNames.getD (cc - 6) "")) st.kc) (by rw [H.hl1]; exact H.hn) H.hl2
    (by rw [ptrAt_eq_pow]; exact pow_ne_zero _ Value.gen_ne_zero) H.hcur1 H.hcur2
    (by rw [harr]; exact ptrsBelow_idx H.hfp)
  exact ph9Ok_at ha hr H hc (hK ec)

end

end
end LeanVM.Guest.B1.VsC
