module

public import LeanVM.Cost.Bounds.Sizes.RootFinder
import all CompPoly.Univariate.Raw.Core
import all CompPoly.Univariate.Raw.Ops
import all CompPoly.Univariate.Raw.Division
import all CompPoly.Univariate.Basic

/-!
# Sizes along the decoder: the splitter's factors and the Euclidean remainders

* **The splitter's factors** (Shoup's splitter, `splitCandidatesFast`, on a nonzero `p` of degree
  `d`): at every stage the factors are nonconstant, pairwise coprime divisors of the monic
  normalization of `p` (`FacInv`). A factor `u` is replaced by `gcd(u, T)` and `gcd(u, T − 1)`
  (the base constants `0, 1`), coprime as `T − (T − 1) = 1`, each a divisor of `u`
  (`refineFactorFast_facInv`); children of distinct factors are coprime as the factors are
  (`refineFactorsFast_facInv`). So the factors' degrees sum to at most `d`, and they are at most
  `d` (`facInv_sum_natDegree_le`, `facInv_size_le`): **`splitCandidatesFast_size_le`**, at most
  `d` factors at the end, at most `d` at every stage (`splitStage_facInv`), so each basis
  element processes at most `d` factors and the cache holds at most `64·d` entries.
* **The Euclidean remainders** (`rawGcdMonicFast`): a product by a constant keeps the size
  (`raw_C_mul_size_le`), a remainder-only division returns at most its dividend's size
  (`modByMonicRemainderOnly_size_le`), so `rawModFast p q` has at most `|p|` coefficients
  (`rawModFast_size_le`); every pair of the chain stays within the inputs' larger size
  (`rawGcdStep_size_le`), and so does the result (`rawGcdMonicWithFuelFast_size_le`).
-/

namespace LeanVM.Cost.Bounds

open CompPoly CompPoly.GuruswamiSudan LeanVM.Extraction.Fast LeanVM.Extraction LeanVM.Parameters
open CompPoly.CPolynomial.Roots.FiniteField

public section

/-! ## Pairwise coprime divisors -/

theorem isCoprime_list_prod {f : Polynomial K} :
    ∀ L : List (Polynomial K), (∀ g ∈ L, IsCoprime f g) → IsCoprime f L.prod
  | [], _ => by rw [List.prod_nil]; exact isCoprime_one_right
  | a :: L, h => by
    rw [List.prod_cons]
    exact (h a (by simp)).mul_right (isCoprime_list_prod L fun x hx ↦ h x (by simp [hx]))

/-- **Pairwise coprime nonzero divisors of `P`: their degrees sum to at most `deg P`.** -/
theorem list_prod_dvd_and_sum_le {P : Polynomial K} (hP : P ≠ 0) :
    ∀ L : List (Polynomial K), L.Pairwise IsCoprime → (∀ f ∈ L, f ∣ P) → (∀ f ∈ L, f ≠ 0) →
      L.prod ∣ P ∧ (L.map Polynomial.natDegree).sum ≤ P.natDegree := by
  have key : ∀ L : List (Polynomial K), L.Pairwise IsCoprime → (∀ f ∈ L, f ∣ P) →
      (∀ f ∈ L, f ≠ 0) → L.prod ∣ P ∧ L.prod.natDegree = (L.map Polynomial.natDegree).sum := by
    intro L
    induction L with
    | nil => intro _ _ _; simp
    | cons f L ih =>
      intro hpw hd hz
      rw [List.pairwise_cons] at hpw
      obtain ⟨h1, h2⟩ := ih hpw.2 (fun g hg ↦ hd g (by simp [hg])) (fun g hg ↦ hz g (by simp [hg]))
      have hc := isCoprime_list_prod L hpw.1
      have hLz : L.prod ≠ 0 := List.prod_ne_zero fun h0 ↦ hz 0 (by simp [h0]) rfl
      refine ⟨by rw [List.prod_cons]; exact hc.mul_dvd (hd f (by simp)) h1, ?_⟩
      rw [List.prod_cons, Polynomial.natDegree_mul (hz f (by simp)) hLz, h2, List.map_cons,
        List.sum_cons]
  intro L hpw hd hz
  obtain ⟨h1, h2⟩ := key L hpw hd hz
  exact ⟨h1, h2 ▸ Polynomial.natDegree_le_of_dvd h1 hP⟩

/-- **The splitter's invariant**: nonconstant, pairwise coprime divisors of `P`. -/
@[expose] def FacInv (P : Polynomial K) (F : List (CPolynomial K)) : Prop :=
  (F.map CPolynomial.toPoly).Pairwise IsCoprime ∧ ∀ f ∈ F, f.toPoly ∣ P ∧ 1 ≤ f.natDegree

theorem facInv_sum_natDegree_le {P : Polynomial K} (hP : P ≠ 0) {F : List (CPolynomial K)}
    (h : FacInv P F) : (F.map CPolynomial.natDegree).sum ≤ P.natDegree := by
  have := (list_prod_dvd_and_sum_le hP (F.map CPolynomial.toPoly) h.1
    (fun f hf ↦ by obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf; exact (h.2 g hg).1)
    (fun f hf ↦ by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
      intro h0
      have := (h.2 g hg).2
      rw [CPolynomial.natDegree_toPoly, h0] at this
      simp at this)).2
  rw [List.map_map] at this
  rwa [show (Polynomial.natDegree ∘ CPolynomial.toPoly) = CPolynomial.natDegree from
    funext fun f ↦ (CPolynomial.natDegree_toPoly f).symm] at this

/-- **At most `deg P` factors.** -/
theorem facInv_length_le {P : Polynomial K} (hP : P ≠ 0) {F : List (CPolynomial K)}
    (h : FacInv P F) : F.length ≤ P.natDegree := by
  refine le_trans ?_ (facInv_sum_natDegree_le hP h)
  have : ∀ L : List (CPolynomial K), (∀ f ∈ L, 1 ≤ f.natDegree) →
      L.length ≤ (L.map CPolynomial.natDegree).sum := by
    intro L
    induction L with
    | nil => simp
    | cons f L ih =>
      intro hL
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have := hL f (by simp)
      have := ih fun g hg ↦ hL g (by simp [hg])
      omega
  exact this F fun f hf ↦ (h.2 f hf).2

/-! ## One factor -/

theorem toPoly_monicNormalize (p : CPolynomial K) :
    (CPolynomial.monicNormalize p).toPoly = normalize p.toPoly :=
  CPolynomial.monicNormalize_toPoly_eq_normalize p

theorem monicNormalize_dvd (p : CPolynomial K) :
    (CPolynomial.monicNormalize p).toPoly ∣ p.toPoly := by
  rw [toPoly_monicNormalize]; exact normalize_dvd_iff.2 dvd_rfl

/-- A monic normalization that is neither `0` nor `1` is nonconstant. -/
theorem one_le_natDegree_monicNormalize {p : CPolynomial K} (h0 : CPolynomial.monicNormalize p ≠ 0)
    (h1 : CPolynomial.monicNormalize p ≠ 1) : 1 ≤ (CPolynomial.monicNormalize p).natDegree := by
  by_contra hd
  apply h1
  have hp : p.toPoly ≠ 0 := by
    intro h; apply h0; rw [← CPolynomial.toPoly_inj, toPoly_monicNormalize, h, normalize_zero,
      CPolynomial.toPoly_zero]
  have hm := Polynomial.monic_normalize hp
  rw [← toPoly_monicNormalize] at hm
  rw [← CPolynomial.toPoly_inj, CPolynomial.toPoly_one]
  rw [CPolynomial.natDegree_toPoly] at hd
  exact Polynomial.eq_one_of_monic_natDegree_zero hm (by omega)

theorem gcdMonicFast_toPoly (u v : CPolynomial K) :
    (gcdMonicFast u v).toPoly = normalize (EuclideanDomain.gcd u.toPoly v.toPoly) := by
  rw [gcdMonicFast_eq, CPolynomial.gcdMonic_toPoly_eq_normalize_gcd]

/-- The child of `u` at the constant `c`: a divisor of `u` and of `T − c`. -/
theorem child_dvd (u T : CPolynomial K) (c : K) :
    (CPolynomial.monicNormalize (gcdMonicFast u (T - CPolynomial.C c))).toPoly ∣ u.toPoly ∧
      (CPolynomial.monicNormalize (gcdMonicFast u (T - CPolynomial.C c))).toPoly ∣
        T.toPoly - Polynomial.C c := by
  have h := monicNormalize_dvd (gcdMonicFast u (T - CPolynomial.C c))
  rw [gcdMonicFast_toPoly] at h
  have h' := h.trans (normalize_dvd_iff.2 dvd_rfl)
  refine ⟨h'.trans (EuclideanDomain.gcd_dvd_left _ _), h'.trans ?_⟩
  have := EuclideanDomain.gcd_dvd_right u.toPoly (T - CPolynomial.C c).toPoly
  rw [CPolynomial.toPoly_sub, CPolynomial.C_toPoly] at this ⊢
  exact this

/-- `T` and `T − 1` are coprime, so are their divisors. -/
theorem isCoprime_sub_C (T : Polynomial K) : IsCoprime (T - Polynomial.C 0) (T - Polynomial.C 1) :=
  ⟨1, -1, by rw [Polynomial.C_0, Polynomial.C_1]; ring⟩

theorem pushNontrivialChild_toList (children : Array (CPolynomial K)) (child : CPolynomial K) :
    (pushNontrivialChild children child).toList = children.toList ∨
      ((pushNontrivialChild children child).toList = children.toList ++ [child] ∧ child ≠ 0 ∧
        child ≠ 1) := by
  unfold pushNontrivialChild
  split
  · left; rfl
  · rename_i h
    right
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h
    exact ⟨by simp, h.1, h.2⟩

/-- **A factor's children**: nonconstant, pairwise coprime divisors of the factor. -/
theorem refineFactorFast_facInv (beta : K) (cache : ShoupTracePowerCache K) (u0 : CPolynomial K) :
    FacInv u0.toPoly (refineFactorFast beta cache u0).2.toList := by
  unfold refineFactorFast
  dsimp only
  split
  · simp [FacInv]
  · rename_i h0
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h0
    split
    · simp only [List.map_cons, List.map_nil, List.pairwise_singleton, List.mem_singleton,
        forall_eq, true_and, FacInv]
      exact ⟨monicNormalize_dvd u0, one_le_natDegree_monicNormalize h0.1 h0.2⟩
    · set u := CPolynomial.monicNormalize u0
      set T := traceCoordFast beta (tracePowersFast u cache).1
      set g : K → CPolynomial K := fun c ↦
        CPolynomial.monicNormalize (gcdMonicFast u (T - CPolynomial.C c))
      have hfold : traceCtx.baseConstants.foldl (fun children c ↦ pushNontrivialChild children (g c))
          #[] = pushNontrivialChild (pushNontrivialChild #[] (g 0)) (g 1) := rfl
      show FacInv u0.toPoly
        (traceCtx.baseConstants.foldl (fun children c ↦ pushNontrivialChild children (g c))
          #[]).toList
      rw [hfold]
      have hdv : ∀ c, (g c).toPoly ∣ u0.toPoly := fun c ↦ (child_dvd u T c).1.trans
        (monicNormalize_dvd u0)
      have hco : IsCoprime (g 0).toPoly (g 1).toPoly :=
        ((isCoprime_sub_C T.toPoly).of_isCoprime_of_dvd_left (child_dvd u T 0).2).of_isCoprime_of_dvd_right
          (child_dvd u T 1).2
      have hnc : ∀ c, g c ≠ 0 → g c ≠ 1 → 1 ≤ (g c).natDegree := fun c h0 h1 ↦
        one_le_natDegree_monicNormalize h0 h1
      rcases pushNontrivialChild_toList #[] (g 0) with e0 | ⟨e0, a0, b0⟩ <;>
        rcases pushNontrivialChild_toList (pushNontrivialChild #[] (g 0)) (g 1) with
          e1 | ⟨e1, a1, b1⟩ <;> rw [e0] at e1 <;> rw [e1] <;> simp [FacInv]
      · exact ⟨hdv 1, hnc 1 a1 b1⟩
      · exact ⟨hdv 0, hnc 0 a0 b0⟩
      · exact ⟨hco, ⟨hdv 0, hnc 0 a0 b0⟩, hdv 1, hnc 1 a1 b1⟩

/-! ## One stage, and the splitter -/

/-- **A stage keeps the invariant**: the children of pairwise coprime divisors of `P`. -/
theorem refineFactorsFast_facInv {P : Polynomial K} (beta : K) (cache : ShoupTracePowerCache K)
    (factors : Array (CPolynomial K)) (h : FacInv P factors.toList) :
    FacInv P (refineFactorsFast beta cache factors).2.toList := by
  have e : refineFactorsFast beta cache factors = factors.toList.foldl
      (fun st f ↦ ((refineFactorFast beta st.1 f).1, st.2 ++ (refineFactorFast beta st.1 f).2))
      (cache, #[]) := by
    rw [refineFactorsFast, ← Array.foldl_toList]
  rw [e]
  have hgen : ∀ (l : List (CPolynomial K)) (st : ShoupTracePowerCache K × Array (CPolynomial K)),
      FacInv P l → FacInv P st.2.toList →
      (∀ o ∈ st.2.toList, ∀ g ∈ l, IsCoprime o.toPoly g.toPoly) →
      FacInv P (l.foldl (fun st f ↦ ((refineFactorFast beta st.1 f).1,
          st.2 ++ (refineFactorFast beta st.1 f).2)) st).2.toList := by
    intro l
    induction l with
    | nil => intro st _ h2 _; exact h2
    | cons x l ih =>
      intro st hl hst hcross
      rw [List.foldl_cons]
      obtain ⟨hpw, hl'⟩ := hl
      rw [List.map_cons, List.pairwise_cons] at hpw
      have hc := refineFactorFast_facInv beta st.1 x
      set C := (refineFactorFast beta st.1 x).2
      have hCx : ∀ c ∈ C.toList, c.toPoly ∣ x.toPoly := fun c hc' ↦ (hc.2 c hc').1
      refine ih _ ⟨hpw.2, fun g hg ↦ hl' g (by simp [hg])⟩ ?_ ?_
      · refine ⟨?_, ?_⟩
        · show ((st.2 ++ C).toList.map CPolynomial.toPoly).Pairwise IsCoprime
          rw [Array.toList_append, List.map_append, List.pairwise_append]
          refine ⟨hst.1, hc.1, fun a ha b hb ↦ ?_⟩
          obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
          obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hb
          exact (hcross o ho x (by simp)).of_isCoprime_of_dvd_right (hCx c hc')
        · intro f hf
          change f ∈ (st.2 ++ C).toList at hf
          rw [Array.toList_append, List.mem_append] at hf
          rcases hf with hf | hf
          · exact hst.2 f hf
          · exact ⟨(hc.2 f hf).1.trans (hl' x (by simp)).1, (hc.2 f hf).2⟩
      · intro o ho g hg
        change o ∈ (st.2 ++ C).toList at ho
        rw [Array.toList_append, List.mem_append] at ho
        rcases ho with ho | ho
        · exact hcross o ho g (by simp [hg])
        · exact (hpw.1 g.toPoly (List.mem_map_of_mem hg)).of_isCoprime_of_dvd_left (hCx o ho)
  exact hgen factors.toList (cache, #[]) h (by simp [FacInv]) (by simp)

/-- The splitter's stages over the basis elements keep the invariant. -/
theorem splitStage_facInv {P : Polynomial K} (betas : List K) :
    ∀ st : ShoupTracePowerCache K × Array (CPolynomial K), FacInv P st.2.toList →
      FacInv P (betas.foldl (fun state beta ↦
        refineFactorsFast beta state.1 state.2) st).2.toList := by
  induction betas with
  | nil => intro st h; exact h
  | cons b betas ih =>
    intro st h
    rw [List.foldl_cons]
    exact ih _ (refineFactorsFast_facInv b st.1 st.2 h)

/-- **The splitter returns at most `deg p` factors** (`p ≠ 0`). -/
theorem splitCandidatesFast_size_le {p : CPolynomial K} (hp : p ≠ 0) :
    (splitCandidatesFast p).size ≤ p.natDegree := by
  have hp' : (CPolynomial.monicNormalize p).toPoly ≠ 0 := by
    rw [toPoly_monicNormalize]; exact (normalize_eq_zero.not).2 (toPoly_ne_zero hp)
  have hdeg : (CPolynomial.monicNormalize p).toPoly.natDegree = p.natDegree := by
    rw [← CPolynomial.natDegree_toPoly, monicNormalize_natDegree]
  unfold splitCandidatesFast
  dsimp only
  split
  · simp
  · rename_i h0
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h0
    split
    · simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add]
      have := one_le_natDegree_monicNormalize h0.1 h0.2
      rw [monicNormalize_natDegree] at this
      exact this
    · rw [← hdeg, ← Array.length_toList]
      generalize traceCtx.basis.toList = betas
      refine facInv_length_le hp' (splitStage_facInv _ _ ?_)
      exact ⟨by simp, by
        intro f hf
        simp only [List.mem_singleton] at hf
        subst hf
        exact ⟨dvd_rfl, one_le_natDegree_monicNormalize h0.1 h0.2⟩⟩

/-! ## The Euclidean remainders -/

section Raw

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

omit [LawfulBEq F] in
/-- **A product by a constant has at most the factor's size.** -/
theorem raw_C_mul_size_le (c : F) (p : CPolynomial.Raw F) :
    (CPolynomial.Raw.C c * p).size ≤ p.size := by
  show (CPolynomial.Raw.mul (CPolynomial.Raw.C c) p).size ≤ p.size
  unfold CPolynomial.Raw.mul CPolynomial.Raw.mulRaw
  refine (CPolynomial.Raw.Trim.size_le_size _).trans ?_
  simp [CPolynomial.Raw.C, CPolynomial.Raw.size_addRaw, CPolynomial.Raw.mulPowX,
    CPolynomial.Raw.smul, CPolynomial.Raw.mk]

omit [LawfulBEq F] in
theorem subScaledShift_size_le (p q : CPolynomial.Raw F) (s : F) (k : ℕ) :
    (CPolynomial.Raw.subScaledShift p q s k).size ≤ p.size := by
  unfold CPolynomial.Raw.subScaledShift
  exact (CPolynomial.Raw.Trim.size_le_size _).trans (by simp [CPolynomial.Raw.mk])

omit [LawfulBEq F] in
/-- **A remainder-only division returns at most its dividend's size.** -/
theorem modByMonicRemainderOnly_size_le (p q : CPolynomial.Raw F) :
    (CPolynomial.Raw.modByMonicRemainderOnly p q).size ≤ p.size := by
  have : ∀ n (a : CPolynomial.Raw F), (CPolynomial.Raw.modByMonicRemainderOnly.go n a q).size ≤
      a.size := by
    intro n
    induction n with
    | zero => intro a; rw [CPolynomial.Raw.modByMonicRemainderOnly.go]
    | succ n ih =>
      intro a
      rw [CPolynomial.Raw.modByMonicRemainderOnly.go]
      split
      · exact le_rfl
      · exact (ih _).trans (subScaledShift_size_le _ _ _ _)
  exact this _ _

omit [LawfulBEq F] in
/-- **`p mod q` has at most `|p|` coefficients.** -/
theorem rawModFast_size_le (p q : CPolynomial.Raw F) : (rawModFast p q).size ≤ p.size :=
  (modByMonicRemainderOnly_size_le _ _).trans (raw_C_mul_size_le _ _)

omit [LawfulBEq F] in
/-- **A step of the Euclidean chain stays within a bound on both arguments.** -/
theorem rawGcdStep_size_le {p q : CPolynomial.Raw F} {B : ℕ} (hp : p.size ≤ B) (hq : q.size ≤ B) :
    q.trim.size ≤ B ∧ (rawModFast p.trim q.trim).size ≤ B :=
  ⟨(CPolynomial.Raw.Trim.size_le_size _).trans hq,
    (rawModFast_size_le _ _).trans ((CPolynomial.Raw.Trim.size_le_size _).trans hp)⟩

omit [LawfulBEq F] in
theorem raw_monicNormalize_size_le (u : CPolynomial.Raw F) :
    (CPolynomial.Raw.monicNormalize u).size ≤ u.size := by
  unfold CPolynomial.Raw.monicNormalize
  dsimp only
  split
  · exact Nat.zero_le _
  · show (Array.map _ u.trim).size ≤ _
    rw [Array.size_map]
    exact CPolynomial.Raw.Trim.size_le_size _

omit [LawfulBEq F] in
/-- **The Euclidean chain's result stays within a bound on both arguments.** -/
theorem rawGcdMonicWithFuelFast_size_le (fuel : ℕ) :
    ∀ {p q : CPolynomial.Raw F} {B : ℕ}, p.size ≤ B → q.size ≤ B →
      (rawGcdMonicWithFuelFast fuel p q).size ≤ B := by
  induction fuel with
  | zero => intro p q B hp _; exact (raw_monicNormalize_size_le p).trans hp
  | succ fuel ih =>
    intro p q B hp hq
    rw [rawGcdMonicWithFuelFast]
    split
    · exact (raw_monicNormalize_size_le _).trans ((CPolynomial.Raw.Trim.size_le_size _).trans hp)
    · obtain ⟨h1, h2⟩ := rawGcdStep_size_le hp hq
      exact ih h1 h2

end Raw

end

end LeanVM.Cost.Bounds
