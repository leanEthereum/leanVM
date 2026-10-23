/-
  LeanVM.Protocol.Whir.Sound.Weights

  The weights of the deployed WHIR verifier as multiaffine functions with known cube values: the
  out-of-domain weight `eq_eval(z, ·)`, the batched consistency weight `_induced_weight`, the
  rotated opening weight, and the lane fold `dot(row, eq_kernel(folds))`.
-/

module

public import LeanVM.Protocol.Whir.Sound.Code
public import LeanVM.Protocol.Whir.ColumnWeight
public import LeanVM.Protocol.EndToEnd.Claims
public import LeanVM.Protocol.Verifier

/-!
# The verifier's weights

The deployed verifier (`LeanVM.Protocol.Verifier`, transcribing `verify_whir` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, `python-verifier/verifier.py:956-1086`) evaluates
three kinds of weights at the terminal point and computes one kind of value from opened rows.
This module proves what the round-by-round analysis needs of each:

* **products of affine factors** are multiaffine (`isMultiaffine_prod`);
* `eqEval z` (the out-of-domain claim's weight) is multiaffine (`isMultiaffine_eqEval`), and its
  inner product with a message is the message's multilinear extension at `z`
  (`sum_eqEval_mul_eq_evalMle`);
* the verifier's `inducedWeight` (`_induced_weight`) is the column-weight sum of Annex D
  `lem:colweight` (`inducedWeight_eq_sum`, through `LeanVM.Protocol.Whir.inducedWeight_eq`; the
  verifier's own `subspaceRoots` is the Annex's roots, `subspaceRoots_eq_closed`), hence
  multiaffine (`isMultiaffine_inducedWeight`), and its inner product with a message is the batched
  codeword entries, `Σ_q w_q Enc(G)[x_q]` (`sum_inducedWeight_mul`);
* the opening weight read at the rotated point, `w(p[ℓ₀:] ++ p[:ℓ₀])`, is multiaffine when `w` is
  the multilinear extension of its cube values (`IsMultilinearFn`,
  `isMultiaffine_of_isMultilinearFn`, `isMultiaffine_rotL`);
* `dot(row, eq_kernel(folds))`, the lane fold of an opened row (`_enforced_sum`), is the row folded
  by `foldsN` (`dot_eqKernel`).

`joinMsg` regroups a message split into lanes and message bits into one message on the full
cube, `sum_joinMsg` relating the two inner products: the level interface, where the next
oracle's lanes are the first variables of the current level's message.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd Finset CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Products of affine factors -/

/-- A function of one variable is affine. -/
def IsAffine1 (f : E → E) : Prop := ∀ X, f X = (1 - X) * f 0 + X * f 1

theorem getD_set (l : List E) {k : ℕ} (hk : k < l.length) (i : ℕ) (X : E) :
    (l.set k X).getD i 0 = if i = k then X else l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

/-- **Products of affine factors are multiaffine.** -/
theorem isMultiaffine_prod (n : ℕ) (f : ℕ → E → E) (hf : ∀ i, IsAffine1 (f i)) :
    IsMultiaffine n fun l ↦ ∏ i : Fin n, f i (l.getD i 0) := by
  intro l hl k hk X
  have key : ∀ Y, ∏ i : Fin n, f i ((l.set k Y).getD i 0) =
      f k Y * ∏ i ∈ univ.erase (⟨k, hk⟩ : Fin n), f i (l.getD i 0) := by
    intro Y
    rw [← Finset.mul_prod_erase univ _ (mem_univ (⟨k, hk⟩ : Fin n))]
    congr 1
    · rw [getD_set l (hl ▸ hk)]; simp
    · refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [getD_set l (hl ▸ hk)]
      have : (i : ℕ) ≠ k := fun h ↦ (Finset.mem_erase.mp hi).1 (Fin.ext h)
      simp [this]
  simp only [key]
  rw [hf k X]
  ring

/-- `foldl (*)` from `a` is `a` times the product. -/
theorem foldl_mul_eq (l : List E) (a : E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

/-- `foldl (+)` from `a` is `a` plus the sum. -/
theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-! ## The out-of-domain weight -/

/-- `eq_eval(z, x)` is the product of its coordinate factors. -/
theorem eqEval_eq_prod (z x : List E) (h : x.length = z.length) :
    eqEval z x = ∏ i : Fin z.length, (1 + z.getD i 0 + x.getD i 0) := by
  rw [eqEval, foldl_mul_eq, one_mul]
  induction z generalizing x with
  | nil => simp
  | cons a z ih =>
    cases x with
    | nil => simp at h
    | cons b x =>
      simp only [List.zipWith_cons_cons, List.prod_cons, List.length_cons, Fin.prod_univ_succ,
        Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
      rw [ih x (by simpa using h)]

/-- `eq_eval(z, ·)` is multiaffine on `|z|` coordinates. -/
theorem isMultiaffine_eqEval (z : List E) : IsMultiaffine z.length (eqEval z) := by
  have hp := isMultiaffine_prod z.length (fun i X ↦ 1 + z.getD i 0 + X) fun i X ↦ by ring
  intro l hl k hk X
  rw [eqEval_eq_prod z _ (by simp [hl]), eqEval_eq_prod z _ (by simp [hl]),
    eqEval_eq_prod z _ (by simp [hl])]
  exact hp l hl k hk X

/-- At a cube point, `eq_eval(z, p)` is the Lagrange weight `Π (p_b ? z_b : 1 − z_b)`. -/
theorem eqEval_bitsL {n : ℕ} (z : List E) (hz : z.length = n) (p : Fin n → Bool) :
    eqEval z (bitsL p) = ∏ b : Fin n, if p b then z.getD b 0 else 1 - z.getD b 0 := by
  subst hz
  rw [eqEval_eq_prod z _ (by simp)]
  refine Finset.prod_congr rfl fun b _ ↦ ?_
  have : (bitsL p).getD b 0 = bitE (p b) := by simp [bitsL, List.getD_eq_getElem?_getD]
  rw [this]
  cases p b
  · simp [bitE, CharTwo.sub_eq_add]
  · simp only [bitE, ite_true]
    rw [add_comm, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The table of a message on the cube, in CompPoly's indexing. -/
def tableOf {n : ℕ} (G : (Fin n → Bool) → E) : CMlPolynomialEval E n :=
  Vector.ofFn fun j ↦ G ((bitsEquiv n).symm j)

/-- A point as a vector. -/
def vecOf (z : List E) : Vector E z.length := ⟨z.toArray, by simp⟩

/-- **The out-of-domain claim reads the extension.** The inner product of `eq_eval(z, ·)` with a
message is the message's multilinear extension at `z`. -/
theorem sum_eqEval_mul_eq_evalMle (z : List E) (G : (Fin z.length → Bool) → E) :
    ∑ p, eqEval z (bitsL p) * G p = evalMle (tableOf G) (vecOf z) := by
  rw [evalMle_eq_sum, ← Equiv.sum_comp (bitsEquiv z.length)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  have ht : (tableOf G)[bitsEquiv z.length p] = G p := by
    simp [tableOf, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  have hl : (lagrangeBasis (vecOf z))[bitsEquiv z.length p] = eqEval z (bitsL p) := by
    rw [Fin.getElem_fin, lagrangeBasis_getElem_nat _ (bitsEquiv z.length p).isLt,
      eqEval_bitsL z rfl]
    refine Finset.prod_congr rfl fun b _ ↦ ?_
    rw [bitsEquiv_val, testBit_bitsToNat]
    simp [vecOf, List.getD_eq_getElem?_getD]
  rw [ht, hl, mul_comm]

/-! ## The rotated opening weight -/

/-- `p[j:] ++ p[:j]`, the verifier's rotation of the terminal point. -/
def rotL (j : ℕ) (l : List E) : List E := l.drop j ++ l.take j

theorem length_rotL (j : ℕ) (l : List E) : (rotL j l).length = l.length := by
  simp only [rotL, List.length_append, List.length_drop, List.length_take]
  omega

theorem rotL_set (j : ℕ) (l : List E) (hj : j ≤ l.length) {k : ℕ} (hk : k < l.length) (X : E) :
    rotL j (l.set k X) = (rotL j l).set (if k < j then l.length - j + k else k - j) X := by
  simp only [rotL, List.drop_set, List.take_set]
  split_ifs with h
  · rw [List.set_append_right _ _ (by simp)]
    congr 2
    simp
  · rw [List.set_eq_of_length_le (l := l.take j) (by simp; omega),
      List.set_append_left _ _ (by simp; omega)]

/-- Rotating the point keeps a weight multiaffine. -/
theorem isMultiaffine_rotL {n j : ℕ} {w : List E → E} (hw : IsMultiaffine n w) (hj : j ≤ n) :
    IsMultiaffine n fun l ↦ w (rotL j l) := by
  intro l hl k hk X
  simp only [rotL_set j l (hl ▸ hj) (hl ▸ hk)]
  exact hw _ (by rw [length_rotL, hl]) _ (by split_ifs <;> omega) X

/-- A multilinear extension of its cube values is multiaffine. -/
theorem isMultiaffine_of_isMultilinearFn {μ : ℕ} {w : List E → E} (hw : IsMultilinearFn μ w) :
    IsMultiaffine μ w := by
  have hb : ∀ x, (boolPoint μ x).length = μ := fun x ↦ by simp [boolPoint]
  have hsum : IsMultiaffine μ fun l ↦ ∑ x : Fin (2 ^ μ), w (boolPoint μ x) *
      eqEval (boolPoint μ x) l :=
    IsMultiaffine.sum _ _ fun x _ ↦ by
      have := (isMultiaffine_eqEval (boolPoint μ x)).const_mul (w (boolPoint μ x))
      rwa [hb] at this
  intro l hl k hk X
  have hlen : ∀ Y, (l.set k Y).length = μ := fun Y ↦ by simp [hl]
  rw [hw _ (hlen X), hw _ (hlen 0), hw _ (hlen 1)]
  exact hsum l hl k hk X

/-! ## The induced weight -/

/-- The root `W_i(e_i)`, in `E`. -/
abbrev rootE (i : ℕ) : E := ofK (vanishingAt i (basisVec i))

private theorem ofK_pow' (a : K) (m : ℕ) : ofK (a ^ m) = ofK a ^ m :=
  map_pow (algebraMap K E) a m

private theorem vanishingAt_zero' (a : K) : vanishingAt 0 a = a := by
  simp [vanishingAt]

private theorem subspaceRootsAux_eq (k j : ℕ) :
    subspaceRootsAux k (rootE j)
        ((List.range' (j + 1) k).map fun c ↦ ofK (vanishingAt j (basisVec c))) =
      (List.range' (j + 1) k).map rootE := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    have hstep : ∀ c, ofK (vanishingAt j (basisVec c)) ^ 2 +
        rootE j * ofK (vanishingAt j (basisVec c)) = ofK (vanishingAt (j + 1) (basisVec c)) := by
      intro c
      rw [vanishingAt_succ, ofK_add, ofK_mul, ofK_pow']
    rw [List.range'_succ]
    simp only [subspaceRootsAux, List.map_cons, List.map_map, Function.comp_def, hstep]
    have := ih (j + 1)
    simp only [show j + 1 + 1 = j + 2 by omega] at this ⊢
    rw [this]

/-- The verifier's `_subspace_roots(n)` is `[W_0(e_0), …, W_n(e_n)]`. -/
theorem subspaceRoots_eq_closed (n : ℕ) :
    Verifier.subspaceRoots n = (List.range (n + 1)).map rootE := by
  have h1 : rootE 0 = 1 := by simp [rootE, vanishingAt_zero', basisVec_zero]
  have hl : (List.range n).map (fun i ↦ eOfNat (2 ^ (i + 1))) =
      (List.range' (0 + 1) n).map fun c ↦ ofK (vanishingAt 0 (basisVec c)) := by
    refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
    simp [eOfNat, vanishingAt_zero', basisVec, add_comm]
  rw [Verifier.subspaceRoots, hl, ← h1, subspaceRootsAux_eq n 0, List.range_eq_range',
    List.range'_succ, List.map_cons]

/-- The verifier's `_subspace_roots` is the Annex transcription's. -/
theorem subspaceRoots_eq_whir (n : ℕ) : Verifier.subspaceRoots n = Whir.subspaceRoots n := by
  rw [subspaceRoots_eq_closed, Whir.subspaceRoots_eq]

/-- The verifier's `_induced_weight` is the Annex transcription's on well-formed input. -/
theorem inducedWeight_eq_whir (n : ℕ) (qs : List ℕ) (ws p : List E) (hp : p.length = n)
    (hw : ws.length = qs.length) :
    Verifier.inducedWeight n qs ws p = (Whir.inducedWeight n qs ws p).getD 0 := by
  simp only [Verifier.inducedWeight, Whir.inducedWeight, hp, hw, and_self, ite_true,
    Option.getD_some, subspaceRoots_eq_whir]
  rfl

/-- The per-query factor of the induced weight at coordinate `i`: `(1 + r) + r·Ŵ_i(x_q)`. -/
def colFactor (q i : ℕ) (r : E) : E := (1 + r) + r * ofK (normVanishingAt i (K.ofBits q))

/-- **The induced weight in closed form**: `Σ_q w_q Π_i ((1 + r_i) + r_i Ŵ_i(x_q))`. -/
theorem inducedWeight_eq_sum (n : ℕ) (qs : List ℕ) (ws l : List E) (hl : l.length = n)
    (hw : ws.length = qs.length) :
    Verifier.inducedWeight n qs ws l =
      ((ws.zip qs).map fun wq ↦ wq.1 * ∏ i : Fin n, colFactor wq.2 i (l.getD i 0)).sum := by
  rw [inducedWeight_eq_whir n qs ws l hl hw]
  have hv : (⟨l.toArray, by simp [hl]⟩ : Vector E n).toList = l := by simp
  have := Whir.inducedWeight_eq n qs ws ⟨l.toArray, by simp [hl]⟩ hw
  rw [hv] at this
  rw [this, Option.getD_some]
  refine congrArg List.sum (List.map_congr_left fun wq _ ↦ ?_)
  rw [eval₂Mle_colWeightTable]
  refine congrArg (wq.1 * ·) (Finset.prod_congr rfl fun i _ ↦ ?_)
  simp [colFactor, List.getD_eq_getElem?_getD, hl, Vector.getElem_mk]

/-- A list-indexed linear combination of multiaffine weights is multiaffine. -/
theorem isMultiaffine_listSum {n : ℕ} {α : Type*} (xs : List α) (c : α → E)
    (F : α → List E → E) (hF : ∀ a, IsMultiaffine n (F a)) :
    IsMultiaffine n fun l ↦ (xs.map fun a ↦ c a * F a l).sum := by
  induction xs with
  | nil => simpa using (IsMultiaffine.zero (n := n))
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hF a).const_mul (c a)).add ih

/-- The verifier's induced weight is multiaffine on `n` coordinates. -/
theorem isMultiaffine_inducedWeight (n : ℕ) (qs : List ℕ) (ws : List E)
    (hw : ws.length = qs.length) : IsMultiaffine n (Verifier.inducedWeight n qs ws) := by
  have h := isMultiaffine_listSum (n := n) (ws.zip qs) (fun wq ↦ wq.1)
    (fun wq l ↦ ∏ i : Fin n, colFactor wq.2 i (l.getD i 0))
    fun wq ↦ isMultiaffine_prod n _ fun i X ↦ by simp only [colFactor]; ring
  intro l hl k hk X
  have hlen : ∀ Y, (l.set k Y).length = n := fun Y ↦ by simp [hl]
  rw [inducedWeight_eq_sum n qs ws _ (hlen X) hw, inducedWeight_eq_sum n qs ws _ (hlen 0) hw,
    inducedWeight_eq_sum n qs ws _ (hlen 1) hw]
  exact h l hl k hk X

/-- At a cube point the column factors multiply to the column weight. -/
theorem prod_colFactor_bitsL {n : ℕ} (q : ℕ) (p : Fin n → Bool) :
    ∏ i : Fin n, colFactor q i ((bitsL p).getD i 0) = ofK (colWeight (K.ofBits q) p) := by
  rw [colWeight]
  change _ = algebraMap K E _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have : (bitsL p).getD i 0 = bitE (p i) := by simp [bitsL, List.getD_eq_getElem?_getD]
  rw [this, colFactor]
  cases p i
  · simp [bitE]
  · simp only [bitE, ite_true, one_mul]
    rw [CharTwo.add_self_eq_zero, zero_add]
    rfl

/-- A codeword entry at an integer position (`0` outside the domain). -/
noncomputable def encAt (n R : ℕ) (G : (Fin n → Bool) → E) (q : ℕ) : E :=
  if h : q < 2 ^ (n + R) then enc n R G ⟨q, h⟩ else 0

/-- Exchange a cube sum with a list sum of scaled terms. -/
theorem sum_listSum_mul {n : ℕ} {α : Type*} (L : List α) (c : α → E)
    (F : α → (Fin n → Bool) → E) (G : (Fin n → Bool) → E) :
    ∑ p, (L.map fun a ↦ c a * F a p).sum * G p = (L.map fun a ↦ c a * ∑ p, F a p * G p).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, ih, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun p _ ↦ by ring) rfl

/-- **The consistency claims read the codeword.** The inner product of the verifier's induced
weight with a message is the batched codeword entries `Σ_q w_q Enc(G)[x_q]`, for queries in the
domain. -/
theorem sum_inducedWeight_mul {n : ℕ} (R : ℕ) (hn : n ≤ 64) (qs : List ℕ) (ws : List E)
    (hw : ws.length = qs.length) (hq : ∀ q ∈ qs, q < 2 ^ (n + R)) (G : (Fin n → Bool) → E) :
    ∑ p, Verifier.inducedWeight n qs ws (bitsL p) * G p =
      ((ws.zip qs).map fun wq ↦ wq.1 * encAt n R G wq.2).sum := by
  simp_rw [inducedWeight_eq_sum n qs ws _ (length_bitsL _) hw, prod_colFactor_bitsL]
  rw [sum_listSum_mul (ws.zip qs) (fun wq ↦ wq.1) (fun wq p ↦ ofK (colWeight (K.ofBits wq.2) p))]
  refine congrArg List.sum (List.map_congr_left fun wq hwq ↦ ?_)
  have hlt := hq wq.2 (List.of_mem_zip hwq).2
  simp only [encAt, hlt, ↓reduceDIte, enc_eq_sum_colWeight R hn G ⟨wq.2, hlt⟩]

end
end LeanVM.Protocol.Whir.Sound
