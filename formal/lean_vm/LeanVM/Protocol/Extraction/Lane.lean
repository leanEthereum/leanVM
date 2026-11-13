module

public import LeanVM.Protocol.Extraction.Defs
public import LeanVM.Protocol.Extraction.Params
public import LeanVM.Protocol.Extraction.Novel

/-!
# The lane decoder is complete (proofs)

For `κ + R ≤ 64`, `n = 2^(κ+R)`, the message length `k = 2^κ + 6` (level 0's degree is
`2^κ − 1 + 6`) and an agreement `A ≤ n` with `(k − 1)·n < A²`:

* `mem_gsLaneAt`: every polynomial `p` of degree `< k` whose values at `x_v = K.ofBits v` agree
  with lane `u` of the word on at least `A` columns `v < n` is in the lane decoder's output (up to
  `toPoly`). This is ArkLib's `decodeWithParams_complete` for `gsContext`, with the certificate
  `gsParamCert_gsParamsFor`, the points `x_v` as an embedding `Fin n ↪ K` (`domainEmb`: `K.ofBits`
  is injective below `2^64`), the decoder's input as `RepresentsArkInput` (by `rfl`), and agreement
  `≥ A` as Hamming distance `≤ n − A` (`hammingDist_le_of_agree`).
* `lanePoly q u = Σ_{j<2^κ} q[j + 2^κ·u]·X_j` is lane `u` of a stack as a polynomial: its values
  are the encoding (`eval_lanePoly`) and its degree is `< 2^κ` (`degree_lanePoly_lt`, from
  `deg X_j ≤ j`, `natDegree_novelPoly_lt`); `fullLanePoly q H u = lanePoly q u + W_κ·H`, level 0's
  polynomial with low part lane `u` and high part `H` (`eval_fullLanePoly`), of degree `< k` when
  `deg H < 6` (`degree_fullLanePoly_lt`).
* `toNovel_succ_getD`: the first `2^κ` of a polynomial's `2^(κ+1)` novel coefficients are its novel
  coefficients over `U_κ` (`X_{2^κ + r} = Ŵ_κ·X_r` vanishes there), so its low part.
* **`exists_mem_laneListAt`**: for a candidate (`Candidates`: some high parts `H_u`, `deg H_u < 6`,
  with `fullLanePoly q H_u u` agreeing with the word on at least `A` columns), lane `u`'s list
  holds an array whose low part is lane `u` of `q` and whose encoding (`novelFwd (κ+1) (R−1)`) is
  the polynomial's values: the decoder returns the polynomial, and `toNovel (κ+1)` its
  coefficients (`novelFwd_toNovel_succ`).

For the running time only (the size of each lane's list): `gsLaneAt_sound` (ArkLib's
`mem_decodeWithParams_iff_spec`: the output has degree `< k` and agreement `≥ A`),
`novelFwd_toNovel` (for a polynomial of degree `< 2^κ`, the encoding of its `toNovel`
coefficients is its values on all `n` columns, since two polynomials of degree `< 2^κ` that agree
on `U_κ` are equal), and `laneListAt_sound`: every element of a lane's list has size `2^(κ+1)` and
an encoding that is the values of a polynomial of degree `< k` agreeing with the lane on at least
`A` columns.

**The `DecidableEq K` instance.** `gsContext` elaborates at `instBEqBF64`, `BF64.instLawfulBEq`
and the statement's `instDecidableEqK` (the instance declared last; `#check` with `pp.explicit`).
ArkLib's theorems are generic in the three instances, so they unify with `gsContext`'s; the
Hamming distance in `GSSpecSet` is then taken at `instDecidableEqK`, and nothing here mentions
the derived `BF64` instance. No rewriting between instances is needed.

Credits: `decodeWithParams_complete`, `GSSpecSet`, `RepresentsArkInput`, `GSParamCert` are
ArkLib's (github.com/Verified-zkEVM/ArkLib at `4dae3acff846125521b7b3998010885071746f16`,
Apache-2.0; `Data/CodingTheory/GuruswamiSudan/{Correctness,Executable}.lean`, Valerii Huhnin); the
decoder is CompPoly's (github.com/Verified-zkEVM/CompPoly at
`572f997390aa4fc131ef30b1186fa1dcf292ca10`, Apache-2.0; Valerii Huhnin).
-/

namespace LeanVM.Extraction.LaneProofs

open LeanVM.Parameters LeanVM.Parameters.Whir LeanVM.Extraction LeanVM.Extraction.Words
open LeanVM.Extraction.Subspace LeanVM.Extraction.NovelProofs CompPoly Polynomial
open _root_.GuruswamiSudan

public section

attribute [local simp] LeanVM.Extraction.Words.ofBits_zero

/-! ## The decoder's input -/

/-- The domain points `x_v = K.ofBits v`, `v < n ≤ 2^64`, as an embedding. -/
@[expose] def domainEmb (n : ℕ) (hn : n ≤ 2 ^ 64) : Fin n ↪ K :=
  ⟨fun v ↦ K.ofBits v.val, fun a b h ↦
    Fin.ext (ofBits_injOn (show a.val < 2 ^ 64 by omega) (show b.val < 2 ^ 64 by omega) h)⟩

/-- The lane decoder's input represents lane `u` on the domain points. -/
theorem representsArkInput_lanePoints (n : ℕ) (hn : n ≤ 2 ^ 64) (W : ℕ → List K) (u : ℕ) :
    RepresentsArkInput (⟨lanePoints n W u⟩ : GuruswamiSudan.GSReceivedWord K) (domainEmb n hn)
      (fun v ↦ laneSymbol W u v.val) := rfl

/-- A filter of `Fin n` counts as the same filter of `range n`. -/
theorem card_filter_fin (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun v : Fin n ↦ p v.val).card = ((Finset.range n).filter p).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  change ((Finset.univ.filter (p ∘ Fin.valEmbedding)).map Fin.valEmbedding).card = _
  rw [← Finset.filter_map, Fin.map_valEmbedding_univ, Nat.Iio_eq_range]

/-- Agreeing and disagreeing columns add up to `n`. -/
theorem card_agree_add_hammingDist (n : ℕ) (f g : ℕ → K) :
    ((Finset.range n).filter fun v ↦ g v = f v).card +
      hammingDist (fun v : Fin n ↦ f v.val) (fun v : Fin n ↦ g v.val) = n := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun v ↦ g v.val = f v.val)
  rw [Finset.card_univ, Fintype.card_fin, card_filter_fin n (fun v ↦ g v = f v)] at hsplit
  have hd : hammingDist (fun v : Fin n ↦ f v.val) (fun v : Fin n ↦ g v.val) =
      (Finset.univ.filter fun v : Fin n ↦ ¬ g v.val = f v.val).card := by
    rw [hammingDist]
    congr 1
    ext v
    simp [eq_comm]
  omega

/-- Agreement on at least `A` of `n` columns is Hamming distance at most `n − A`. -/
theorem hammingDist_le_of_agree {n A : ℕ} (f g : ℕ → K)
    (h : A ≤ ((Finset.range n).filter fun v ↦ g v = f v).card) :
    hammingDist (fun v : Fin n ↦ f v.val) (fun v : Fin n ↦ g v.val) ≤ n - A := by
  have := card_agree_add_hammingDist n f g
  omega

/-- Hamming distance at most `n − A ≤ n` is agreement on at least `A` columns. -/
theorem agree_of_hammingDist_le {n A : ℕ} (hA : A ≤ n) (f g : ℕ → K)
    (h : hammingDist (fun v : Fin n ↦ f v.val) (fun v : Fin n ↦ g v.val) ≤ n - A) :
    A ≤ ((Finset.range n).filter fun v ↦ g v = f v).card := by
  have := card_agree_add_hammingDist n f g
  omega

/-! ## Completeness of the lane decoder -/

/-- **The lane decoder is complete**: a polynomial of degree `< 2^κ + 6` that agrees with lane `u`
on at least `A` of the `2^(κ+R)` columns is in the decoder's output. -/
theorem mem_gsLaneAt {κ R A : ℕ} (hn : κ + R ≤ 64) (hA : A ≤ 2 ^ (κ + R))
    (hcap : (2 ^ κ + initialFold - 1) * 2 ^ (κ + R) < A * A) (W : ℕ → List K) (u : ℕ) {p : K[X]}
    (hp : p.degree < ((2 ^ κ + initialFold : ℕ) : WithBot ℕ))
    (hagree : A ≤ ((Finset.range (2 ^ (κ + R))).filter fun v ↦
      p.eval (K.ofBits v) = laneSymbol W u v).card) :
    ∃ cp ∈ (gsLaneAt κ R A W u).toList, cp.toPoly = p := by
  have hn' : 2 ^ (κ + R) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hn
  have hk : 1 < 2 ^ κ + initialFold := by
    have := Nat.one_le_two_pow (n := κ); simp only [initialFold]; omega
  refine decodeWithParams_complete gsContext _ (gsParamCert_gsParamsFor hk hA hcap)
    (representsArkInput_lanePoints _ hn' W u) ⟨hp, ?_⟩
  exact hammingDist_le_of_agree (fun v ↦ laneSymbol W u v) (fun v ↦ p.eval (K.ofBits v)) hagree

/-! ## Lane `u` of a stack as a polynomial -/

/-- `W_i` as a polynomial has degree at most `2^i`. -/
theorem natDegree_vanishing_le (i : ℕ) : (vanishing i).natDegree ≤ 2 ^ i := by
  rw [vanishing]
  refine (natDegree_prod_le _ _).trans ?_
  have h1 : ∀ v ∈ Finset.range (2 ^ i), (X + C (K.ofBits v)).natDegree ≤ 1 := fun v _ ↦
    (natDegree_add_le _ _).trans (by simp)
  exact (Finset.sum_le_sum h1).trans (by simp)

/-- `Σ_{i<κ} 2^i < 2^κ`. -/
theorem sum_two_pow_lt (κ : ℕ) : ∑ i ∈ Finset.range κ, 2 ^ i < 2 ^ κ := by
  induction κ with
  | zero => simp
  | succ κ ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- `deg X_j < 2^κ` for `j < 2^κ`, `κ ≤ 64`. -/
theorem natDegree_novelPoly_lt {κ j : ℕ} (hκ : κ ≤ 64) (hj : j < 2 ^ κ) :
    (novelPoly j).natDegree < 2 ^ κ := by
  rw [novelPoly]
  refine (natDegree_prod_le _ _).trans_lt ?_
  have hterm : ∀ i ∈ Finset.range 64,
      (if j.testBit i then C (subspacePoly i (K.ofBits (2 ^ i)))⁻¹ * vanishing i else 1).natDegree
        ≤ if i < κ then 2 ^ i else 0 := by
    intro i _
    split
    · rename_i hb
      have hi : i < κ := by
        by_contra hi
        have : j < 2 ^ i := hj.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [Nat.testBit_lt_two_pow this] at hb
        exact absurd hb (by simp)
      rw [ite_eq_left hi]
      exact (natDegree_C_mul_le _ _).trans (natDegree_vanishing_le i)
    · simp
  refine (Finset.sum_le_sum hterm).trans_lt ?_
  rw [← Finset.sum_range_add_sum_Ico _ hκ]
  have hzero : ∑ i ∈ Finset.Ico κ 64, (if i < κ then 2 ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by rw [ite_eq_right (by simp [Finset.mem_Ico] at hi; omega)]
  rw [hzero, add_zero, Finset.sum_congr rfl fun i hi ↦ ite_eq_left (Finset.mem_range.mp hi)]
  exact sum_two_pow_lt κ

/-- A novel-basis sum of `2^κ` terms has degree `< 2^κ`. -/
theorem degree_novelSum_lt {κ : ℕ} (hκ : κ ≤ 64) (a : ℕ → K) :
    (∑ j ∈ Finset.range (2 ^ κ), C (a j) * novelPoly j).degree < ((2 ^ κ : ℕ) : WithBot ℕ) := by
  have h : (∑ j ∈ Finset.range (2 ^ κ), C (a j) * novelPoly j).natDegree ≤ 2 ^ κ - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ ?_
    have := natDegree_novelPoly_lt hκ (Finset.mem_range.mp hj)
    exact (natDegree_C_mul_le _ _).trans (by omega)
  have hpos : 0 < 2 ^ κ := Nat.two_pow_pos _
  refine degree_le_natDegree.trans_lt ?_
  exact_mod_cast (show (∑ j ∈ Finset.range (2 ^ κ), C (a j) * novelPoly j).natDegree < 2 ^ κ by
    omega)

/-- **Lane `u` of a stack as a polynomial**: `Σ_{j<2^κ} q[j + 2^κ·u]·X_j`, `κ = μ − 6`. -/
noncomputable def lanePoly {μ : ℕ} (q : Vector K (2 ^ μ)) (u : ℕ) : K[X] :=
  ∑ j ∈ Finset.range (2 ^ (μ - initialFold)),
    C (q.getD (j + 2 ^ (μ - initialFold) * u) 0) * novelPoly j

/-- The values of lane `u`'s polynomial are the stack's encoding. -/
theorem eval_lanePoly {μ : ℕ} (q : Vector K (2 ^ μ)) (u v : ℕ) :
    (lanePoly q u).eval (K.ofBits v) = encode q u v := by
  simp [lanePoly, encode, eval_finsetSum, eval_novelPoly]

/-- Lane `u`'s polynomial has degree `< 2^κ`. -/
theorem degree_lanePoly_lt {μ : ℕ} (hκ : μ - initialFold ≤ 64) (q : Vector K (2 ^ μ)) (u : ℕ) :
    (lanePoly q u).degree < ((2 ^ (μ - initialFold) : ℕ) : WithBot ℕ) :=
  degree_novelSum_lt hκ _

/-! ## Level 0's polynomial of a candidate -/

/-- Lane `u` of level 0's polynomial with high part `H`: `lanePoly q u + W_κ·H`, `κ = μ − 6`. -/
noncomputable def fullLanePoly {μ : ℕ} (q : Vector K (2 ^ μ)) (H : K[X]) (u : ℕ) : K[X] :=
  lanePoly q u + vanishing (μ - initialFold) * H

theorem eval_fullLanePoly {μ : ℕ} (q : Vector K (2 ^ μ)) (H : K[X]) (u v : ℕ) :
    (fullLanePoly q H u).eval (K.ofBits v) =
      encode q u v + subspacePoly (μ - initialFold) (K.ofBits v) * H.eval (K.ofBits v) := by
  rw [fullLanePoly, eval_add, eval_mul, eval_lanePoly, eval_vanishing]

/-- `W_i` vanishes on `U_i`. -/
theorem subspacePoly_of_lt {i v : ℕ} (hv : v < 2 ^ i) : subspacePoly i (K.ofBits v) = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hv) (CharTwo.add_self_eq_zero (K.ofBits v))

/-- Level 0's polynomial has degree `< 2^κ + 6` when its high part's is `< 6`. -/
theorem degree_fullLanePoly_lt {μ : ℕ} (hκ : μ - initialFold ≤ 64) (q : Vector K (2 ^ μ))
    {H : K[X]} (hH : H.degree < initialFold) (u : ℕ) :
    (fullLanePoly q H u).degree < ((2 ^ (μ - initialFold) + initialFold : ℕ) : WithBot ℕ) := by
  have hl : (lanePoly q u).natDegree ≤ 2 ^ (μ - initialFold) - 1 := by
    rcases eq_or_ne (lanePoly q u) 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · have := (natDegree_lt_iff_degree_lt h0).mpr (degree_lanePoly_lt hκ q u); omega
  have hHn : H.natDegree ≤ initialFold - 1 := by
    rcases eq_or_ne H 0 with h0 | h0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · have := (natDegree_lt_iff_degree_lt h0).mpr hH; omega
  have hm : (vanishing (μ - initialFold) * H).natDegree ≤
      2 ^ (μ - initialFold) + (initialFold - 1) :=
    natDegree_mul_le.trans (Nat.add_le_add (natDegree_vanishing_le _) hHn)
  have hsum : (fullLanePoly q H u).natDegree < 2 ^ (μ - initialFold) + initialFold := by
    have := (natDegree_add_le (lanePoly q u) (vanishing (μ - initialFold) * H)).trans
      (max_le_max hl hm)
    have h1 := Nat.one_le_two_pow (n := μ - initialFold)
    rw [fullLanePoly]
    simp only [initialFold] at this h1 ⊢
    omega
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hsum)

/-! ## The low part -/

/-- **The low part**: the first `2^κ` novel coefficients over `U_{κ+1}` are the novel coefficients
over `U_κ`, as the coefficients from `2^κ` on multiply `Ŵ_κ`, which vanishes on `U_κ`. -/
theorem toNovel_succ_getD {κ : ℕ} (hκ : κ < 64) (cp : CPolynomial K) {j : ℕ} (hj : j < 2 ^ κ) :
    (toNovel (κ + 1) cp).getD j 0 = (toNovel κ cp).getD j 0 := by
  obtain ⟨c, hc⟩ : ∃ c, c = toNovel (κ + 1) cp := ⟨_, rfl⟩
  rw [← hc]
  have hev : ∀ v < 2 ^ (κ + 1), cp.eval (K.ofBits v) =
      ∑ i ∈ Finset.range (2 ^ (κ + 1)), c.getD i 0 * novelBasis i (K.ofBits v) := by
    intro v hv
    have hround := novelFwd_novelInv (κ := κ + 1)
      (Array.ofFn fun v : Fin (2 ^ (κ + 1)) ↦ cp.eval (K.ofBits v.val)) Array.size_ofFn
    have h1 : (novelFwd (κ + 1) 0 c).getD v 0 =
        (Array.ofFn fun v : Fin (2 ^ (κ + 1)) ↦ cp.eval (K.ofBits v.val)).getD v 0 := by
      rw [hc]; exact congrArg (fun a : Array K ↦ a.getD v 0) hround
    rw [novelFwd_getD (by omega) _ (by simpa using hv), getD_ofFn _ hv] at h1
    exact h1.symm
  have hlow : ∀ v < 2 ^ κ, cp.eval (K.ofBits v) =
      ∑ i ∈ Finset.range (2 ^ κ), c.getD i 0 * novelBasis i (K.ofBits v) := by
    intro v hv
    have hle : 2 ^ κ ≤ 2 ^ (κ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hz : ∑ r ∈ Finset.range (2 ^ κ),
        c.getD (2 ^ κ + r) 0 * novelBasis (2 ^ κ + r) (K.ofBits v) = 0 := by
      refine Finset.sum_eq_zero fun r hr ↦ ?_
      have hr' := Finset.mem_range.mp hr
      rw [show 2 ^ κ + r = 2 ^ κ * 1 + r by ring, novelBasis_mul_two_pow_add hr', mul_one,
        novelBasis_two_pow hκ, normSubspacePoly_of_lt hv, zero_mul, mul_zero]
    rw [hev v (by omega), pow_succ, mul_two, Finset.sum_range_add, hz, add_zero]
  rw [toNovel_eq (by omega) cp (fun i ↦ c.getD i 0) hlow, getD_ofFn _ hj]

/-- The novel-basis coefficients `toNovel` returns encode the polynomial on every column, for a
polynomial of degree `< 2^κ`. -/
theorem novelFwd_toNovel {κ R : ℕ} (hκ : κ + R ≤ 64) {cp : CPolynomial K}
    (hdeg : cp.toPoly.degree < ((2 ^ κ : ℕ) : WithBot ℕ)) {v : ℕ} (hv : v < 2 ^ (κ + R)) :
    (novelFwd κ R (toNovel κ cp)).getD v 0 = cp.toPoly.eval (K.ofBits v) := by
  have hκ' : κ ≤ 64 := by omega
  set c := toNovel κ cp
  set P := ∑ j ∈ Finset.range (2 ^ κ), C (c.getD j 0) * novelPoly j
  have hevalP : ∀ v < 2 ^ (κ + R), P.eval (K.ofBits v) = (novelFwd κ R c).getD v 0 := by
    intro v hv
    rw [novelFwd_getD hκ' _ hv]
    simp [P, eval_finsetSum, eval_novelPoly]
  have hU : ∀ v < 2 ^ κ, P.eval (K.ofBits v) = cp.toPoly.eval (K.ofBits v) := by
    intro v hv
    have hround := novelFwd_novelInv (κ := κ)
      (Array.ofFn fun v : Fin (2 ^ κ) ↦ cp.eval (K.ofBits v.val)) Array.size_ofFn
    have h1 := congrArg (fun a : Array K ↦ a.getD v 0) hround
    rw [novelFwd_getD hκ' _ (by simpa using hv), getD_ofFn _ hv] at h1
    rw [← CompPoly.CPolynomial.eval_toPoly, ← h1]
    simp [P, eval_finsetSum, eval_novelPoly, c, toNovel]
  have hinj : Set.InjOn K.ofBits (Finset.range (2 ^ κ) : Set ℕ) := fun a ha b hb h ↦
    ofBits_injOn (show a < 2 ^ 64 from (Finset.mem_range.mp ha).trans_le
      (Nat.pow_le_pow_right (by norm_num) hκ'))
      (show b < 2 ^ 64 from (Finset.mem_range.mp hb).trans_le
      (Nat.pow_le_pow_right (by norm_num) hκ')) h
  have hPeq : P = cp.toPoly := by
    refine Polynomial.eq_of_degrees_lt_of_eval_index_eq _ hinj ?_ ?_ fun i hi ↦
      hU i (Finset.mem_range.mp hi)
    · rw [Finset.card_range]; exact degree_novelSum_lt hκ' _
    · rw [Finset.card_range]; exact hdeg
  rw [← hevalP v hv, hPeq]

/-- At `κ + 1` and rate `2^-(R−1)`: the encoding of the `2^(κ+1)` coefficients of a polynomial of
degree `< 2^(κ+1)` is its values on the `2^(κ+R)` columns. -/
theorem novelFwd_toNovel_succ {κ R : ℕ} (hR : 1 ≤ R) (hn : κ + R ≤ 64) {cp : CPolynomial K}
    (hdeg : cp.toPoly.degree < ((2 ^ (κ + 1) : ℕ) : WithBot ℕ)) {v : ℕ} (hv : v < 2 ^ (κ + R)) :
    (novelFwd (κ + 1) (R - 1) (toNovel (κ + 1) cp)).getD v 0 = cp.toPoly.eval (K.ofBits v) :=
  novelFwd_toNovel (by omega) hdeg (by rwa [show κ + 1 + (R - 1) = κ + R by omega])

/-- `2^κ + 6 ≤ 2^(κ+1)` for `κ ≥ 3`. -/
theorem two_pow_add_initialFold_le {κ : ℕ} (hκ : 3 ≤ κ) : 2 ^ κ + initialFold ≤ 2 ^ (κ + 1) := by
  have h8 : 2 ^ 3 ≤ 2 ^ κ := Nat.pow_le_pow_right (by norm_num) hκ
  rw [pow_succ]
  simp only [initialFold]
  omega

/-! ## Lanes of candidates -/

/-- **A lane of level 0's polynomial is in the lane's list**: if `fullLanePoly q H u` (degree
`< 2^κ + 6`) agrees with lane `u` on at least `A` columns, the lane's list holds an array whose
low part is lane `u` of `q` and whose encoding is the polynomial's values. -/
theorem exists_mem_laneListAt {μ R A : ℕ} (hμ : 9 ≤ μ) (hR : 1 ≤ R)
    (hn : μ - initialFold + R ≤ 64) (hA : A ≤ 2 ^ (μ - initialFold + R))
    (hcap : (2 ^ (μ - initialFold) + initialFold - 1) * 2 ^ (μ - initialFold + R) < A * A)
    (W : ℕ → List K) (q : Vector K (2 ^ μ)) {H : K[X]} (hH : H.degree < initialFold) (u : ℕ)
    (hagree : A ≤ ((Finset.range (2 ^ (μ - initialFold + R))).filter fun v ↦
      (fullLanePoly q H u).eval (K.ofBits v) = laneSymbol W u v).card) :
    ∃ c ∈ laneListAt (μ - initialFold) R A W u,
      (∀ j < 2 ^ (μ - initialFold), c.getD j 0 = (laneCoeffs q u).getD j 0) ∧
      ∀ v < 2 ^ (μ - initialFold + R), (novelFwd (μ - initialFold + 1) (R - 1) c).getD v 0 =
        (fullLanePoly q H u).eval (K.ofBits v) := by
  have hκ : μ - initialFold < 64 := by omega
  obtain ⟨cp, hcp, hcpq⟩ :=
    mem_gsLaneAt hn hA hcap W u (degree_fullLanePoly_lt (by omega) q hH u) hagree
  have hdeg : cp.toPoly.degree < ((2 ^ (μ - initialFold + 1) : ℕ) : WithBot ℕ) := by
    rw [hcpq]
    refine (degree_fullLanePoly_lt (by omega) q hH u).trans_le ?_
    exact_mod_cast two_pow_add_initialFold_le (by simp only [initialFold]; omega)
  refine ⟨toNovel (μ - initialFold + 1) cp, ?_, fun j hj ↦ ?_, fun v hv ↦ ?_⟩
  · rw [laneListAt, List.mem_mergeSort, List.mem_dedup, List.mem_map]
    exact ⟨cp, hcp, rfl⟩
  · rw [toNovel_succ_getD hκ cp hj,
      toNovel_eq (by omega) cp (fun j ↦ (laneCoeffs q u).getD j 0) ?_, getD_ofFn _ hj]
    intro v hv
    rw [CompPoly.CPolynomial.eval_toPoly, hcpq, eval_fullLanePoly, subspacePoly_of_lt hv,
      zero_mul, add_zero, encode]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [laneCoeffs, getD_ofFn _ (Finset.mem_range.mp hj)]
  · rw [novelFwd_toNovel_succ hR hn hdeg hv, hcpq]

/-! ## The lane lists are sound (for the running time) -/

/-- **The lane decoder is sound**: everything it returns has degree `< 2^κ + 6` and agrees with
lane `u` on at least `A` columns. -/
theorem gsLaneAt_sound {κ R A : ℕ} (hn : κ + R ≤ 64) (hA : A ≤ 2 ^ (κ + R))
    (hcap : (2 ^ κ + initialFold - 1) * 2 ^ (κ + R) < A * A) (W : ℕ → List K) (u : ℕ)
    {cp : CPolynomial K} (hcp : cp ∈ (gsLaneAt κ R A W u).toList) :
    cp.toPoly.degree < ((2 ^ κ + initialFold : ℕ) : WithBot ℕ) ∧
      A ≤ ((Finset.range (2 ^ (κ + R))).filter fun v ↦
        cp.toPoly.eval (K.ofBits v) = laneSymbol W u v).card := by
  have hn' : 2 ^ (κ + R) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hn
  have hk : 1 < 2 ^ κ + initialFold := by
    have := Nat.one_le_two_pow (n := κ); simp only [initialFold]; omega
  have hspec := (mem_decodeWithParams_iff_spec gsContext _ (gsParamCert_gsParamsFor hk hA hcap)
    (representsArkInput_lanePoints _ hn' W u)).mp ⟨cp, hcp, rfl⟩
  exact ⟨hspec.1, agree_of_hammingDist_le hA (fun v ↦ laneSymbol W u v)
    (fun v ↦ cp.toPoly.eval (K.ofBits v)) hspec.2⟩

/-- **The lane lists are sound**: every element has size `2^(κ+1)`, and its encoding is the values
of a polynomial of degree `< 2^κ + 6` that agree with lane `u` on at least `A` columns. -/
theorem laneListAt_sound {κ R A : ℕ} (hκ : 3 ≤ κ) (hR : 1 ≤ R) (hn : κ + R ≤ 64)
    (hA : A ≤ 2 ^ (κ + R)) (hcap : (2 ^ κ + initialFold - 1) * 2 ^ (κ + R) < A * A)
    (W : ℕ → List K) (u : ℕ) {c : Array K} (hc : c ∈ laneListAt κ R A W u) :
    c.size = 2 ^ (κ + 1) ∧ ∃ p : K[X], p.degree < ((2 ^ κ + initialFold : ℕ) : WithBot ℕ) ∧
      (∀ v < 2 ^ (κ + R), (novelFwd (κ + 1) (R - 1) c).getD v 0 = p.eval (K.ofBits v)) ∧
      A ≤ ((Finset.range (2 ^ (κ + R))).filter fun v ↦
        (novelFwd (κ + 1) (R - 1) c).getD v 0 = laneSymbol W u v).card := by
  rw [laneListAt, List.mem_mergeSort, List.mem_dedup, List.mem_map] at hc
  obtain ⟨cp, hcp, rfl⟩ := hc
  obtain ⟨hdeg, hagree⟩ := gsLaneAt_sound hn hA hcap W u hcp
  have hdeg' : cp.toPoly.degree < ((2 ^ (κ + 1) : ℕ) : WithBot ℕ) :=
    hdeg.trans_le (by exact_mod_cast two_pow_add_initialFold_le hκ)
  refine ⟨size_novelInv _ Array.size_ofFn, cp.toPoly, hdeg,
    fun v hv ↦ novelFwd_toNovel_succ hR hn hdeg' hv, hagree.trans_eq ?_⟩
  congr 1
  refine Finset.filter_congr fun v hv ↦ ?_
  rw [novelFwd_toNovel_succ hR hn hdeg' (Finset.mem_range.mp hv)]

end
end LeanVM.Extraction.LaneProofs
