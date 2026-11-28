module

public import LeanVM.Protocol.Extraction.Defs
public import CompPoly.Fields.Binary.AdditiveNTT.Coset

/-!
# The inverse novel-basis transform is correct (proofs)

For `κ ≤ 64`, with `X_j = novelBasis j` and `x_v = K.ofBits v`: if `y_v = Σ_{j<2^κ} c_j·X_j(x_v)`
for `v < 2^κ`, then `novelInv κ y = c` (`novelInv_eval`).

The transform is CompPoly's inverse butterfly network (`AdditiveNTT.Coset.inetwork`) on the basis
`β_i = x_{2^i}`, whose span's points are the words (`point_wordBasis`), whose subspace polynomials
are the extractor's (`normalized_wordBasis`, `novel_wordBasis`) and which is independent below
`64` (`independent_wordBasis`): a stage of `novelInv` is CompPoly's `istage` at the twiddles
`twiddle β 0` (`novelInvStage_getD`), so `novelInv` is `inetwork` (`foldl_novelInvStage_getD`),
which inverts the additive NTT (`inetwork_ntt`).

Credits: the transform is the inverse additive NTT of Lin, Chung and Han (FOCS 2014), as in
Diamond and Posen, *Polylogarithmic proofs for multilinears over binary towers* (2024),
Algorithm 2. Its correctness is CompPoly's `AdditiveNTT.Coset`
(`CompPoly/Fields/Binary/AdditiveNTT/Coset.lean`, github.com/Verified-zkEVM/CompPoly at
`afb9b1363984a70f10e24bd597f6ff40ebc8afbb`, Apache-2.0, Thomas Coratger), used, not copied.
-/

namespace LeanVM.Extraction.NovelProofs

open LeanVM.Parameters LeanVM.Extraction LeanVM.Extraction.Words AdditiveNTT.Coset

public section

/-! ## The basis `x_{2^i}` -/

/-- The basis `β_i = x_{2^i}` of `K` over `F₂`. -/
def wordBasis (i : ℕ) : K := K.ofBits (2 ^ i)

/-- The points of its span are the words. -/
theorem point_wordBasis (v : ℕ) : point wordBasis v = K.ofBits v :=
  (ofBits_eq_sum Nat.lt_two_pow_self).symm

/-- No basis word below `64` is in the span of the earlier ones. -/
theorem independent_wordBasis : Independent wordBasis 64 := by
  intro i hi m hm h
  rw [point_wordBasis, wordBasis] at h
  have h2 : 2 ^ i < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hi
  exact absurd (ofBits_injOn (show m < 2 ^ 64 by omega) h2 h) (by omega)

/-- Its subspace polynomials are the extractor's, in characteristic two. -/
theorem vanishing_wordBasis (i : ℕ) (x : K) : vanishing wordBasis i x = subspacePoly i x := by
  rw [vanishing, subspacePoly]
  exact Finset.prod_congr rfl fun v _ ↦ by rw [point_wordBasis, sub_eq_add_neg, CharTwo.neg_eq]

theorem normalized_wordBasis (i : ℕ) (x : K) :
    normalized wordBasis i x = normSubspacePoly i x := by
  rw [normalized, vanishing_wordBasis, vanishing_wordBasis, normSubspacePoly, wordBasis,
    div_eq_mul_inv]

/-- Its novel basis on `κ ≤ 64` coordinates is the extractor's, below `2^κ`. -/
theorem novel_wordBasis {κ j : ℕ} (hκ : κ ≤ 64) (hj : j < 2 ^ κ) (x : K) :
    novel wordBasis κ j x = novelBasis j x := by
  rw [novel, novelBasis, ← Finset.prod_range_mul_prod_Ico _ hκ,
    Finset.prod_eq_one (s := Finset.Ico κ 64) fun i hi ↦ ?_, mul_one]
  · exact Finset.prod_congr rfl fun i _ ↦ by rw [normalized_wordBasis]
  · simp [Nat.testBit_lt_two_pow
      (hj.trans_le (Nat.pow_le_pow_right two_pos (Finset.mem_Ico.mp hi).1))]

/-! ## The stages -/

theorem getD_ofFn {n p : ℕ} (f : Fin n → K) (hp : p < n) : (Array.ofFn f).getD p 0 = f ⟨p, hp⟩ := by
  simp [Array.getD, hp]

/-- Twiddle `q` of stage `i` is `Ŵ_i` at the first point of block `q`. -/
theorem novelTwiddles_getD {m i q : ℕ} (hq : q < 2 ^ (m - (i + 1))) :
    (novelTwiddles m i).getD q 0 = twiddle wordBasis 0 i q := by
  rw [novelTwiddles, getD_ofFn _ hq, twiddle, zero_add, point_wordBasis, normalized_wordBasis,
    normSubspacePoly]

/-- Bit `i` of `p` is set exactly when `p` is in the upper half of its block of `2^(i+1)`. -/
theorem testBit_eq_not_lt (p i : ℕ) : p.testBit i = !decide (p % 2 ^ (i + 1) < 2 ^ i) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_lt p (Nat.two_pow_pos i)
  rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ i) with h | h <;> simp [h, this]

/-- **A stage of the inverse transform** is CompPoly's inverse stage. -/
theorem novelInvStage_getD {m i : ℕ} (him : i < m) (b : Array K) {p : ℕ} (hp : p < 2 ^ m) :
    (novelInvStage m i b).getD p 0 = istage (twiddle wordBasis 0 i) i (fun q ↦ b.getD q 0) p := by
  have hq : p / 2 ^ (i + 1) < 2 ^ (m - (i + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel him]
    exact hp
  rw [novelInvStage, getD_ofFn _ hp]
  simp only [istage, ibutterfly, smul_eq_mul, novelTwiddles_getD hq, testBit_eq_not_lt]
  split_ifs <;> simp_all

theorem size_novelInvStage (m i : ℕ) (b : Array K) : (novelInvStage m i b).size = 2 ^ m :=
  Array.size_ofFn

/-- The first `l` stages of the inverse transform are CompPoly's inverse network. -/
theorem foldl_novelInvStage_getD {m : ℕ} (y : Array K) :
    ∀ l ≤ m, ∀ p < 2 ^ m, ((List.range l).foldl (fun b i ↦ novelInvStage m i b) y).getD p 0 =
      inetwork (twiddle wordBasis 0) l (fun q ↦ y.getD q 0) p
  | 0, _, _, _ => rfl
  | l + 1, hl, p, hp => by
    have hm : 2 ^ (m - (l + 1)) * 2 ^ (l + 1) = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hl]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      novelInvStage_getD (by omega) _ hp, inetwork]
    exact istage_congr (c := 2 ^ (m - (l + 1))) (fun _ _ ↦ rfl)
      (fun q hq ↦ foldl_novelInvStage_getD y l (by omega) q (by rwa [hm] at hq)) (by rwa [hm])

/-! ## The transform -/

theorem size_novelInv {κ : ℕ} (y : Array K) (hy : y.size = 2 ^ κ) : (novelInv κ y).size = 2 ^ κ := by
  unfold novelInv
  cases κ with
  | zero => simpa using hy
  | succ κ => rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      size_novelInvStage]

theorem array_ext_getD {a b : Array K} (h : a.size = b.size)
    (hg : ∀ p < a.size, a.getD p 0 = b.getD p 0) : a = b := by
  apply Array.ext h
  intro p h1 h2
  have := hg p h1
  simp only [Array.getD, h1, h2, dite_true] at this
  exact this

/-- **The inverse transform recovers the coefficients**, as an equation of arrays. -/
theorem novelInv_eval {κ : ℕ} (hκ : κ ≤ 64) (c : ℕ → K) (y : Array K) (hsize : y.size = 2 ^ κ)
    (hy : ∀ v < 2 ^ κ, y.getD v 0 = ∑ j ∈ Finset.range (2 ^ κ), c j * novelBasis j (K.ofBits v)) :
    novelInv κ y = Array.ofFn fun j : Fin (2 ^ κ) ↦ c j := by
  apply array_ext_getD (by rw [size_novelInv y hsize, Array.size_ofFn])
  intro p hp
  rw [size_novelInv y hsize] at hp
  rw [getD_ofFn _ hp, novelInv, foldl_novelInvStage_getD y κ le_rfl p hp]
  refine inetwork_ntt wordBasis independent_wordBasis hκ 0 c _ (fun v hv ↦ ?_) hp
  simp only [hy v hv, ntt, novelEval, zero_add, point_wordBasis]
  exact Finset.sum_congr rfl fun j hj ↦ by
    rw [novel_wordBasis hκ (Finset.mem_range.mp hj), smul_eq_mul, mul_comm]

end
end LeanVM.Extraction.NovelProofs
