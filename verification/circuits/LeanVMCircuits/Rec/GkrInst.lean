module

public import LeanVMCircuits.Rec.TableSum

@[expose] public section

/-!
The bus GKR's layers as `Sumcheck.Inst`s, and its root as the product of its leaves.

`Sumcheck.eqInst n p P` is the honest instance of `Σ_x eq(p, x) · P(x)` on the Boolean cube with each round's eq weight
`p_i` factored out, binding variable `0` first: each round's polynomial is `P` summed over the cube in the variables
after it, weighted by their `eq` (`eqv`), and its final value is `P` at the challenges. `eqInst_sum`, `eqInst_ok`,
`eqInst_final`, `eqInst_weight`: its sum is that eq-weighted sum, it has degree `d` when `P` has degree at most `d` in
each variable, its final value is `P(r)` and round `i` factors out `p_i`, as `v.read_round(5, claim,
Some(eq_point))` reads it.

A product tree (`gkr::prove_products`, leaves padded with ones to `2^μ`): node `x` of the level `k` above the leaves is
the product of its `2^k` leaves (`level`), so a node is the product of its four children two levels down (`level_four`)
or its two children one level down (`level_two`), and the root is the product of all leaves (`level_root`).
`pullRoot_eq_level` and `pushRoot_eq_level`: the bus's honest roots are the roots of the trees over the slots' pulls
and pushes at the draw.

`gkr::verify_products`' radix-four layer at a point `p` of `ℓ` variables and a challenge `λ` runs one sumcheck of
`Σ_t λ^t Ṽ_t(p)`, `Ṽ_t` tree `t`'s level at `p` (`mleAt`), each round's eq weight the point's coordinate, ending at
`Σ_t λ^t Π_c a_{t,c}`, `a_{t,c}` the four children's values at the challenges. `layerInst` is its honest instance:
`layerInst_sum` (its sum is the claim at the honest level values), `layerInst_ok` (degree `4`), `layerInst_weight`
(round `i` factors out `p_i`) and `layerInst_final` (its final value is the claim on the children's honest values at the
challenges, `childMle`). `next_claim`: the layer's next claim, `interp(interp(a, b, low), interp(c, d, low), high)` of
the children's honest values, is the level below's value at `[low, high] ++ r`, the next layer's point, so the honest
values carry from the root to the leaves layer by layer.
-/

namespace LeanVMCircuits.Rec.Sumcheck

open MvPolynomial Finset Classical

variable {F : Type} [Field F]

/-- `eq(p, x) = Π_i ((1 - p_i)(1 - x_i) + p_i x_i)`. -/
def eqv {n : ℕ} (p x : Fin n → F) : F := ∏ i, ((1 - p i) * (1 - x i) + p i * x i)

theorem eqv_cons {n : ℕ} (p : Fin (n + 1) → F) (a : F) (x : Fin n → F) :
    eqv p (Fin.cons a x) = ((1 - p 0) * (1 - a) + p 0 * a) * eqv (Fin.tail p) x := by
  simp only [eqv, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

/-- The honest instance of `Σ_x eq(p, x) · P(x)` on the cube, binding variable `0` first, each round's eq weight
`p_i` factored out. -/
noncomputable def eqInst : (n : ℕ) → (Fin n → F) → MvPolynomial (Fin n) F → Inst F n
  | 0, _, P => .leaf (eval Fin.elim0 P)
  | n + 1, p, P => .node (some (p 0))
      (∑ x ∈ cube n, Polynomial.C (eqv (Fin.tail p) x) * (finSuccEquiv F n P).map (eval x))
      fun r => eqInst n (Fin.tail p) (Polynomial.eval (C r) (finSuccEquiv F n P))

theorem eqRound_eval {n : ℕ} (p : Fin (n + 1) → F) (P : MvPolynomial (Fin (n + 1)) F) (r : F) :
    (∑ x ∈ cube n, Polynomial.C (eqv (Fin.tail p) x) * (finSuccEquiv F n P).map (eval x)).eval r =
      ∑ x ∈ cube n, eqv (Fin.tail p) x * eval (Fin.cons r x) P := by
  rw [Polynomial.eval_finsetSum]
  refine sum_congr rfl fun x _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_eq_eval_mv_eval']

/-- The instance's sum is the eq-weighted sum over the cube. -/
theorem eqInst_sum : ∀ {n : ℕ} (p : Fin n → F) (P : MvPolynomial (Fin n) F),
    (eqInst n p P).sum = ∑ x ∈ cube n, eqv p x * eval x P
  | 0, p, P => by simp [eqInst, Inst.sum, sum_cube_zero, eqv]
  | n + 1, p, P => by
    simp only [eqInst, Inst.sum, lin]
    rw [eqRound_eval, eqRound_eval, sum_cube_succ, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [eqv_cons, eqv_cons]
    ring

/-- The instance has degree `d` when `P` has degree at most `d` in each variable. -/
theorem eqInst_ok (d : ℕ) : ∀ {n : ℕ} (p : Fin n → F) (P : MvPolynomial (Fin n) F), (∀ i, degreeOf i P ≤ d) →
    (eqInst n p P).ok d
  | 0, _, _, _ => trivial
  | n + 1, p, P, h => by
    refine ⟨?_, fun r => ⟨?_, eqInst_ok d _ _ fun i => (degreeOf_bind P r i).trans (h i.succ)⟩⟩
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_map_le).trans ((natDegree_finSuccEquiv P).le.trans (h 0)))
    · rw [eqInst_sum, eqRound_eval]
      exact sum_congr rfl fun x _ => by rw [eval_bind]

/-- The instance's final value along `r` is `P(r)`. -/
theorem eqInst_final : ∀ {n : ℕ} (p : Fin n → F) (P : MvPolynomial (Fin n) F) (r : Fin n → F),
    (eqInst n p P).final r = eval r P
  | 0, _, P, r => by simp only [eqInst, Inst.final]; rw [Subsingleton.elim r Fin.elim0]
  | n + 1, p, P, r => by
    simp only [eqInst, Inst.final]
    rw [eqInst_final, eval_bind, Fin.cons_self_tail]

/-- Round `i` factors out the eq weight `p_i`. -/
theorem eqInst_weight : ∀ {n : ℕ} (p : Fin n → F) (P : MvPolynomial (Fin n) F) (r : Fin n → F) (i : Fin n),
    (eqInst n p P).weight r i = some (p i)
  | 0, _, _, _, i => i.elim0
  | n + 1, p, P, r, i => by
    simp only [eqInst, Inst.weight]
    refine Fin.cases rfl (fun j => ?_) i
    simp only [Fin.cases_succ]
    rw [eqInst_weight]
    rfl

end LeanVMCircuits.Rec.Sumcheck

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model MvPolynomial Finset Classical Sumcheck

/-! The product tree. -/

/-- Node `x` of the level `k` above the leaves: the product of its `2^k` leaves. -/
noncomputable def level (leaf : ℕ → E) (k x : ℕ) : E := ∏ j ∈ range (2 ^ k), leaf (2 ^ k * x + j)

theorem prod_range_mul (f : ℕ → E) (b : ℕ) : ∀ a, ∏ j ∈ range (a * b), f j = ∏ c ∈ range a, ∏ j ∈ range b, f (b * c + j)
  | 0 => by simp
  | a + 1 => by
    rw [Nat.succ_mul, prod_range_add, prod_range_mul f b a, prod_range_succ]
    congr 1
    exact prod_congr rfl fun j _ => by rw [mul_comm a b]

theorem level_zero (leaf : ℕ → E) (x : ℕ) : level leaf 0 x = leaf x := by simp [level]

/-- A node is the product of its two children one level down. -/
theorem level_two (leaf : ℕ → E) (k x : ℕ) : level leaf (k + 1) x = level leaf k (2 * x) * level leaf k (2 * x + 1) := by
  unfold level
  rw [pow_succ', prod_range_mul _ (2 ^ k) 2]
  simp only [prod_range_succ, prod_range_zero, one_mul]
  congr 1 <;> refine prod_congr rfl fun j _ => congrArg leaf (by ring)

/-- A node is the product of its four children two levels down. -/
theorem level_four (leaf : ℕ → E) (k x : ℕ) :
    level leaf (k + 2) x = ∏ c ∈ range 4, level leaf k (4 * x + c) := by
  unfold level
  rw [show 2 ^ (k + 2) = 4 * 2 ^ k by ring, prod_range_mul _ (2 ^ k) 4]
  refine prod_congr rfl fun c _ => prod_congr rfl fun j _ => congrArg leaf (by ring)

/-- The root is the product of all leaves. -/
theorem level_root (leaf : ℕ → E) (μ : ℕ) : level leaf μ 0 = ∏ j ∈ range (2 ^ μ), leaf j := by
  simp [level]

/-- A tree's leaves: the slots' tuples at the draw `f = (β, A)`, `β + fp_A(t)`, padded with ones. -/
noncomputable def treeLeaf (n : ℕ) (t : Fin n → UnionSound.Tuple) (f : Fin 5 → E) (j : ℕ) : E :=
  if h : j < n then f 0 + UnionSound.fpAt (Fin.tail f) (t ⟨j, h⟩) else 1

theorem root_eq_level (n : ℕ) (t : Fin n → UnionSound.Tuple) (f : Fin 5 → E) {μ : ℕ} (hμ : n ≤ 2 ^ μ) :
    UnionSound.prodAt ((univ.val : Multiset (Fin n)).map t) (f 0) (Fin.tail f) = level (treeLeaf n t f) μ 0 := by
  rw [level_root, UnionSound.prodAt, Multiset.map_map]
  have hsplit : ∏ j ∈ range (2 ^ μ), treeLeaf n t f j = ∏ j ∈ range n, treeLeaf n t f j := by
    rw [← Nat.add_sub_cancel' hμ, prod_range_add]
    rw [prod_eq_one (s := range (2 ^ μ - n)) fun j _ => by simp [treeLeaf]]
    rw [mul_one]
  rw [hsplit, ← Fin.prod_univ_eq_prod_range]
  simp only [treeLeaf, Fin.is_lt, dif_pos, Fin.eta]
  rfl

/-- The bus's honest root over the pulls is its tree's root, `μ` levels up. -/
theorem pullRoot_eq_level (s : State) (w : Witness) (f : Fin 5 → E) {μ : ℕ} (hμ : (slots w).length ≤ 2 ^ μ) :
    pullRoot s w f = level (treeLeaf (slots w).length
      (fun i => busTuple (key (slots w)[i], carried w (slots w)[i])) f) μ 0 :=
  root_eq_level _ _ f hμ

/-- The bus's honest root over the pushes is its tree's root. -/
theorem pushRoot_eq_level (s : State) (w : Witness) (f : Fin 5 → E) {μ : ℕ} (hμ : (slots w).length ≤ 2 ^ μ) :
    pushRoot s w f = level (treeLeaf (slots w).length
      (fun i => busTuple (key (slots w)[classNext (fun i : Fin (slots w).length => slotClass s (slots w)[i]) i],
        carried w (slots w)[i])) f) μ 0 :=
  root_eq_level _ _ f hμ

/-! A radix-four layer's honest instance. -/

/-- A level's value at a point `p` of its `ℓ` variables: its multilinear extension. -/
noncomputable def mleAt (ℓ : ℕ) (p : Fin ℓ → E) (W : ℕ → E) : E := ∑ z ∈ range (2 ^ ℓ), eqv p (bitPoint ℓ z) * W z

/-- Child `c` of a level's nodes as a multilinear polynomial in its `ℓ` variables: node `z`'s child `4z + c` of the
level below, `V`. -/
noncomputable def childMle (ℓ : ℕ) (V : ℕ → E) (c : ℕ) : MvPolynomial (Fin ℓ) E :=
  ∑ z ∈ range (2 ^ ℓ), eqPoly ℓ ℓ z * C (V (4 * z + c))

/-- The radix-four layer's honest instance at the level's point `p` and `λ`: both trees' (their levels below, `V t`)
eq-weighted sums of each node's four children's product, combined at `λ`. -/
noncomputable def layerInst (ℓ : ℕ) (p : Fin ℓ → E) (lam : E) (V : Fin 2 → ℕ → E) : Inst E ℓ :=
  eqInst ℓ p (∑ t : Fin 2, C (lam ^ (t : ℕ)) * ∏ c ∈ range 4, childMle ℓ (V t) c)

theorem eval_childMle {ℓ : ℕ} (V : ℕ → E) (c : ℕ) {Z : ℕ} (hZ : Z < 2 ^ ℓ) :
    MvPolynomial.eval (bitPoint ℓ Z) (childMle ℓ V c) = V (4 * Z + c) := by
  simp only [childMle, map_sum, map_mul, eval_C]
  rw [sum_congr rfl fun z hz => by rw [eval_eqPoly le_rfl (mem_range.mp hz) hZ]]
  simp [hZ]

/-- The layer's instance sums to the claim `Σ_t λ^t Ṽ_t(p)` at the honest level values, each node its four children's
product. -/
theorem layerInst_sum (ℓ : ℕ) (p : Fin ℓ → E) (lam : E) (V : Fin 2 → ℕ → E) :
    (layerInst ℓ p lam V).sum = ∑ t : Fin 2, lam ^ (t : ℕ) * mleAt ℓ p fun z => ∏ c ∈ range 4, V t (4 * z + c) := by
  rw [layerInst, eqInst_sum, sum_cube_bits]
  simp only [mleAt, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun Z hZ => ?_
  simp only [map_sum, map_mul, eval_C, map_prod, eval_childMle _ _ (mem_range.mp hZ), mul_sum]
  refine sum_congr rfl fun t _ => by ring

theorem degreeOf_childMle (ℓ : ℕ) (V : ℕ → E) (c : ℕ) (i : Fin ℓ) : degreeOf i (childMle ℓ V c) ≤ 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun z _ => ?_)
  exact (degreeOf_mul_C_le _ _ _).trans (degreeOf_eqPoly i)

/-- The layer's instance has degree `d` for every `d ≥ 4`. -/
theorem layerInst_ok (ℓ : ℕ) (p : Fin ℓ → E) (lam : E) (V : Fin 2 → ℕ → E) {d : ℕ} (hd : 4 ≤ d) :
    (layerInst ℓ p lam V).ok d := by
  refine eqInst_ok d p _ fun i => (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun t _ => ?_)
  refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_prod_le _ _ _).trans ?_)
  calc ∑ c ∈ range 4, degreeOf i (childMle ℓ (V t) c) ≤ ∑ _c ∈ range 4, 1 :=
        sum_le_sum fun c _ => degreeOf_childMle ℓ (V t) c i
    _ ≤ d := by simp; omega

/-- Round `i` factors out the point's coordinate `p_i`. -/
theorem layerInst_weight (ℓ : ℕ) (p : Fin ℓ → E) (lam : E) (V : Fin 2 → ℕ → E) (r : Fin ℓ → E) (i : Fin ℓ) :
    (layerInst ℓ p lam V).weight r i = some (p i) :=
  eqInst_weight _ _ r i

/-- The layer's final value along `r`: the claim on the children's honest values at `r`, as the verifier's
`poly_eval(products, λ)` reads the children it receives. -/
theorem layerInst_final (ℓ : ℕ) (p : Fin ℓ → E) (lam : E) (V : Fin 2 → ℕ → E) (r : Fin ℓ → E) :
    (layerInst ℓ p lam V).final r =
      ∑ t : Fin 2, lam ^ (t : ℕ) * ∏ c ∈ range 4, MvPolynomial.eval r (childMle ℓ (V t) c) := by
  rw [layerInst, eqInst_final]
  simp only [map_sum, map_mul, eval_C, map_prod]

/-! The next claim. -/

theorem one_sub_eq_one_add (a : E) : 1 - a = 1 + a := by
  have h : a + a = 0 := by rw [← two_mul, two_E, zero_mul]
  linear_combination (-1 : E) * h

/-- In characteristic two the boolean Lagrange polynomial at a point is `eq` of the point and the row's bits. -/
theorem eval_eqPoly_eqv {ℓ : ℕ} (r : Fin ℓ → E) (z : ℕ) :
    MvPolynomial.eval r (eqPoly ℓ ℓ z : MvPolynomial (Fin ℓ) E) = eqv r (bitPoint ℓ z) := by
  simp only [eqPoly, eqv, map_prod]
  refine prod_congr rfl fun j _ => ?_
  by_cases hb : z.testBit j = true <;> simp [j.isLt, hb, bitPoint, one_sub_eq_one_add]

theorem eval_childMle_eq {ℓ : ℕ} (r : Fin ℓ → E) (V : ℕ → E) (c : ℕ) :
    MvPolynomial.eval r (childMle ℓ V c) = mleAt ℓ r fun z => V (4 * z + c) := by
  simp only [childMle, mleAt, map_sum, map_mul, eval_C, eval_eqPoly_eqv]

theorem sum_range_mul (f : ℕ → E) (b : ℕ) : ∀ a, ∑ j ∈ range (a * b), f j = ∑ c ∈ range a, ∑ j ∈ range b, f (b * c + j)
  | 0 => by simp
  | a + 1 => by
    rw [Nat.succ_mul, sum_range_add, sum_range_mul f b a, sum_range_succ]
    congr 1
    exact sum_congr rfl fun j _ => by rw [mul_comm a b]

/-- Row `4z + c`'s bits: `c`'s two, then `z`'s. -/
theorem bitPoint_four (ℓ z : ℕ) {c : ℕ} (hc : c < 4) :
    bitPoint (ℓ + 2) (4 * z + c) =
      Fin.cons (bitPoint 2 c 0) (Fin.cons (bitPoint 2 c 1) (bitPoint ℓ z) : Fin (ℓ + 1) → E) := by
  have h4 : 4 * z + c = 2 ^ 2 * z + c := by norm_num
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) i
  · simp only [bitPoint, h4, Nat.testBit_two_pow_mul_add z (show c < 2 ^ 2 by omega), Fin.cons_zero]
    simp
  · simp only [bitPoint, h4, Nat.testBit_two_pow_mul_add z (show c < 2 ^ 2 by omega), Fin.cons_succ, Fin.cons_zero]
    simp
  · simp only [bitPoint, h4, Nat.testBit_two_pow_mul_add z (show c < 2 ^ 2 by omega), Fin.cons_succ]
    simp

/-- The layer's next claim: the line at `high` through the lines at `low` of the four children's values at the
challenges (`interp(interp(a, b, low), interp(c, d, low), high)`), is the level below's value at `[low, high] ++ r`. -/
theorem next_claim (ℓ : ℕ) (V : ℕ → E) (low high : E) (r : Fin ℓ → E) :
    mleAt (ℓ + 2) (Fin.cons low (Fin.cons high r)) V =
      Bind.lineE (Bind.lineE (MvPolynomial.eval r (childMle ℓ V 0)) (MvPolynomial.eval r (childMle ℓ V 1)) low)
        (Bind.lineE (MvPolynomial.eval r (childMle ℓ V 2)) (MvPolynomial.eval r (childMle ℓ V 3)) low) high := by
  simp only [eval_childMle_eq, mleAt, Bind.lineE]
  rw [show 2 ^ (ℓ + 2) = 2 ^ ℓ * 4 by ring, sum_range_mul _ 4 (2 ^ ℓ)]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  rw [sum_congr rfl fun z _ => by
    rw [bitPoint_four ℓ z (by norm_num : 0 < 4), bitPoint_four ℓ z (by norm_num : 1 < 4),
      bitPoint_four ℓ z (by norm_num : 2 < 4), bitPoint_four ℓ z (by norm_num : 3 < 4)]]
  simp only [eqv_cons, Fin.tail_cons, Fin.cons_zero, bitPoint, one_sub_eq_one_add]
  simp only [Fin.val_zero, Fin.val_one, show Nat.testBit 0 0 = false by decide, show Nat.testBit 0 1 = false by decide,
    show Nat.testBit 1 0 = true by decide, show Nat.testBit 1 1 = false by decide,
    show Nat.testBit 2 0 = false by decide, show Nat.testBit 2 1 = true by decide,
    show Nat.testBit 3 0 = true by decide, show Nat.testBit 3 1 = true by decide, Bool.false_eq_true, ↓reduceIte,
    add_zero, mul_one, mul_zero, one_add_one, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun z _ => ?_
  ring

/-- On a product tree, the layer `k + 2` levels above the leaves sums to the claim at the honest level values: each
node of its level is its four children's product (`level_four`). -/
theorem layerInst_sum_level (ℓ k : ℕ) (p : Fin ℓ → E) (lam : E) (leaf : Fin 2 → ℕ → E) :
    (layerInst ℓ p lam fun t => level (leaf t) k).sum = ∑ t : Fin 2, lam ^ (t : ℕ) * mleAt ℓ p (level (leaf t) (k + 2)) := by
  rw [layerInst_sum]
  refine sum_congr rfl fun t _ => ?_
  congr 2
  funext z
  rw [level_four]

/-- With no variables a level's value is its one node, the root at the top. -/
theorem mleAt_zero (p : Fin 0 → E) (W : ℕ → E) : mleAt 0 p W = W 0 := by
  simp [mleAt, eqv]

/-- The odd layer's next claim: the line at `r` through the two children is the level below's value at `[r]`. -/
theorem odd_next (r : E) (W : ℕ → E) : mleAt 1 (Fin.cons r Fin.elim0) W = Bind.lineE (W 0) (W 1) r := by
  simp only [mleAt, pow_one, sum_range_succ, sum_range_zero, zero_add, eqv, Fin.prod_univ_one, Fin.cons_zero, bitPoint,
    Bind.lineE, Fin.val_zero, show Nat.testBit 0 0 = false by decide, show Nat.testBit 1 0 = true by decide,
    Bool.false_eq_true, ↓reduceIte, one_sub_eq_one_add, mul_zero, mul_one, add_zero, zero_add]
  linear_combination (r * W 1 + W 1) * two_E

end LeanVMCircuits.Rec.AirLink

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model

/-! The bus GKR as the certificate names it. -/

/-- A passing link: the layer's sumcheck has no residual, its values are the previous next claims, its claim and expected are the sumcheck's input claim and final side, its rounds' eq weights are the previous point, and its input claim reads no hints. -/
theorem LayerCert.link_sem {lc : LayerCert} {sc : SumcheckCert} {os : Array (List ℕ)} {outs pt : List ℕ}
    (h : lc.linkOk sc os outs pt = true) :
    sc.resid = [] ∧ lc.layer.values = outs ∧ lc.layer.claim os = sc.claim0 ∧ lc.layer.expected os = sc.final ∧
      sc.rounds.map (·.weight) = pt.map some ∧ sc.hints = [] := by
  simp only [LayerCert.linkOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A chain's first layer is linked to the next claims and point it starts from, and the rest chains from its own. -/
theorem LayerCert.chain_cons {scs : Array SumcheckCert} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)}
    {lc : LayerCert} {rest : List LayerCert} {outs pt last : List ℕ}
    (h : LayerCert.chain scs cs rl os (lc :: rest) outs pt = some last) :
    ∃ sc, scs[lc.sc]? = some sc ∧ lc.linkOk sc os outs pt = true ∧ lc.layer.ok os cs rl = true ∧ lc.layer.m = 2 ∧
      LayerCert.chain scs cs rl os rest ((List.range 2).map (lc.layer.out os))
        ([lc.layer.low.chal, lc.layer.high.chal] ++ sc.rounds.map (·.chal)) = some last := by
  simp only [LayerCert.chain] at h
  split at h
  · rename_i sc hsc
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨sc, hsc, hc.1.1, hc.1.2, hc.2, h⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- What a passing `GkrCert` gives where the calls hold: its first layer reads the table's root as both trees' value,
its layers chain from the first layer's next claims and point to two last next claims, and the table's totals are a
framework share plus each. -/
theorem GkrCert.sem {g : GkrCert} {tc : TableCert} {scs : Array SumcheckCert} {tops : Array TopCert}
    {odds : Array OddCert} {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}
    (hF : Facts cs rl os st val) (h : g.okIn tc scs tops odds cs rl os = true) :
    (g.start tops odds os).1 = [tc.root, tc.root] ∧ ∃ v0 v1,
      LayerCert.chain scs cs rl os g.layers (g.start tops odds os).2.1 (g.start tops odds os).2.2 = some [v0, v1] ∧
      Model.ev val tc.tot0 = Model.ev val g.fw.1 + Model.ev val v0 ∧
      Model.ev val tc.tot1 = Model.ev val g.fw.2 + Model.ev val v1 := by
  unfold GkrCert.okIn at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨-, hroot⟩, hrest⟩ := h
  refine ⟨hroot, ?_⟩
  split at hrest
  · rename_i v0 v1 hch
    simp only [Bool.and_eq_true, beq_iff_eq] at hrest
    obtain ⟨⟨hcalls, h0⟩, h1⟩ := hrest
    have e0 : Model.ev val (o os g.totAt.1) = Model.ev val g.fw.1 + Model.ev val v0 :=
      holds_of_mem hF hcalls List.mem_cons_self
    have e1 : Model.ev val (o os g.totAt.2) = Model.ev val g.fw.2 + Model.ev val v1 :=
      holds_of_mem hF hcalls (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨v0, v1, hch, h0 ▸ e0, h1 ▸ e1⟩
  · exact absurd hrest (by simp)

/-- A linked layer's wires where the calls hold, in `AirLink.layerInst`'s form: its sumcheck has no residual and its
rounds' eq weights are the previous point; its input claim is the previous next claims combined at `λ` (the claim
`layerInst_sum` names); its final side is the children's products combined at `λ` (`layerInst_final`'s form); and its
next claims are the lines through its children at `low` and `high` (`AirLink.next_claim`'s form). -/
theorem LayerCert.layer_sem {lc : LayerCert} {sc : SumcheckCert} {cs : Array Call} {rl : Array Bool}
    {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val} {outs pt : List ℕ} (hF : Facts cs rl os st val)
    (hlink : lc.linkOk sc os outs pt = true) (hok : lc.layer.ok os cs rl = true) :
    sc.resid = [] ∧ sc.rounds.map (·.weight) = pt.map some ∧
      Model.ev val sc.claim0 = (Sumcheck.polyOf (outs.map (Model.ev val))).eval (Model.ev val lc.layer.lam.chal) ∧
      Model.ev val sc.final = (Sumcheck.polyOf ((List.range lc.layer.m).map fun k =>
        Model.ev val (lc.layer.kid k 0) * Model.ev val (lc.layer.kid k 1) * Model.ev val (lc.layer.kid k 2) *
          Model.ev val (lc.layer.kid k 3))).eval (Model.ev val lc.layer.lam.chal) ∧
      ∀ k < lc.layer.m, Model.ev val (lc.layer.out os k) =
        lineE (lineE (Model.ev val (lc.layer.kid k 0)) (Model.ev val (lc.layer.kid k 1)) (Model.ev val lc.layer.low.chal))
          (lineE (Model.ev val (lc.layer.kid k 2)) (Model.ev val (lc.layer.kid k 3)) (Model.ev val lc.layer.low.chal))
          (Model.ev val lc.layer.high.chal) := by
  obtain ⟨hres, hv, hc, he, hw, -⟩ := LayerCert.link_sem hlink
  obtain ⟨tc, te, tl⟩ := top_sem hF hok
  exact ⟨hres, hw, hc ▸ hv ▸ tc, he ▸ te, tl⟩

/-- Mutation tests of `GkrCert.okIn` with no layer past a top layer: the totals adding the top layer's next claims
pass; totals reading another wire, or a first layer reading two roots, fail. -/
example : ({ odd := false, first := 0, layers := [], totAt := (1, 2), fw := (3, 4) } : GkrCert).okIn
    { (default : TableCert) with root := 7, tot0 := 8, tot1 := 9 } #[]
    #[{ (default : TopCert) with values := [7, 7] }] #[] #[.zero, .add 3 5, .add 4 5] #[] #[[5], [8], [9]] = true := by
  decide +kernel

example : ({ odd := false, first := 0, layers := [], totAt := (1, 2), fw := (3, 4) } : GkrCert).okIn
    { (default : TableCert) with root := 7, tot0 := 8, tot1 := 9 } #[]
    #[{ (default : TopCert) with values := [7, 7] }] #[] #[.zero, .add 3 6, .add 4 5] #[] #[[5], [8], [9]] = false := by
  decide +kernel

example : ({ odd := false, first := 0, layers := [], totAt := (1, 2), fw := (3, 4) } : GkrCert).okIn
    { (default : TableCert) with root := 7, tot0 := 8, tot1 := 9 } #[]
    #[{ (default : TopCert) with values := [7, 6] }] #[] #[.zero, .add 3 5, .add 4 5] #[] #[[5], [8], [9]] = false := by
  decide +kernel

/-- Mutation tests of `LayerCert.linkOk`: a layer linked to the previous next claims and point passes; one whose round reads another eq weight, whose values are not the previous next claims, or whose input claim reads a hint, fails. -/
example : ({ sc := 0, layer := { (default : TopCert) with values := [5, 5] } } : LayerCert).linkOk
    { (default : SumcheckCert) with rounds := [{ (default : RoundCert) with weight := some 3 }] } #[] [5, 5] [3] =
      true := by
  decide +kernel

example : ({ sc := 0, layer := { (default : TopCert) with values := [5, 5] } } : LayerCert).linkOk
    { (default : SumcheckCert) with rounds := [{ (default : RoundCert) with weight := some 4 }] } #[] [5, 5] [3] =
      false := by
  decide +kernel

example : ({ sc := 0, layer := { (default : TopCert) with values := [5, 6] } } : LayerCert).linkOk
    { (default : SumcheckCert) with rounds := [{ (default : RoundCert) with weight := some 3 }] } #[] [5, 5] [3] =
      false := by
  decide +kernel

example : ({ sc := 0, layer := { (default : TopCert) with values := [5, 5] } } : LayerCert).linkOk
    { (default : SumcheckCert) with rounds := [{ (default : RoundCert) with weight := some 3 }], hints := [5] } #[]
      [5, 5] [3] = false := by
  decide +kernel

end LeanVMCircuits.Rec.Bind
