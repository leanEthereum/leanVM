/-
  LeanVM.Guest.B1.Whir.InnerAlg

  The Spec's glued weights at the terminal point against the guest's residual sums, scales and
  out-of-domain weights.
-/

module

public import LeanVM.Guest.B1.Whir.Residuals
public import LeanVM.Guest.B1.Whir.OodW
public import LeanVM.Guest.B1.Whir.Bases
public import LeanVM.Guest.B1.Whir.Level
public import LeanVM.Guest.B1.Opening.NovelEval
public import LeanVM.Protocol.Whir.SubspaceAt

/-!
# The glued weights, algebraically

* `inducedWeight_sum`: `inducedWeight` with the weights `powers λ Q` is
  `Σ_k λ^k Π_t (1 + p_t·(1 + Ŵ_t(x_k)))`;
* `what_factor`: `1 + Ŵ_t(x)` is `1 + W_t(x)·inv_t`, the guest's chain times the vanishing
  inverse;
* `level_inner`: a level's scale times its product chain is `λ³` times its induced weight;
* `level_high`: `β·after` times its high chain is `λ³·recH` times the challenges after it;
* `eqEval_prod`: an out-of-domain weight is `Π (1 + z_t + p_t)`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

theorem foldl_zip_mul {α β : Type} (f : α → β → E) :
    ∀ (a : List α) (b : List β) (w : E) (da : α) (db : β),
      (List.zip a b).foldl (fun prod (p : α × β) ↦ prod * f p.1 p.2) w =
        w * ∏ t ∈ Finset.range (min a.length b.length), f (a.getD t da) (b.getD t db)
  | [], _, w, _, _ => by simp
  | _ :: _, [], w, _, _ => by simp
  | x :: a, y :: b, w, da, db => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_mul f a b _ da db, List.length_cons,
      List.length_cons, Nat.add_min_add_right, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem foldl_zip_sum {α β : Type} (g : α → β → E) :
    ∀ (a : List α) (b : List β) (w : E) (da : α) (db : β),
      (List.zip a b).foldl (fun tot (p : α × β) ↦ tot + g p.1 p.2) w =
        w + ∑ k ∈ Finset.range (min a.length b.length), g (a.getD k da) (b.getD k db)
  | [], _, w, _, _ => by simp
  | _ :: _, [], w, _, _ => by simp
  | x :: a, y :: b, w, da, db => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_sum g a b _ da db, List.length_cons,
      List.length_cons, Nat.add_min_add_right, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem length_subspaceAt (mu : ℕ) (x : K) : (subspaceAt mu x).length = mu + 1 := by
  rw [LeanVM.Protocol.Whir.subspaceAt_eq]; simp

/-- **`inducedWeight` at the weights `powers λ Q`.** -/
theorem inducedWeight_sum (mu : ℕ) (qs : List ℕ) (lam : E) (x : List E) :
    inducedWeight mu qs (powers lam qs.length) x =
      ∑ k ∈ Finset.range qs.length, lam ^ k * ∏ t ∈ Finset.range (min x.length (mu + 1)),
        (1 + x.getD t 0 * ofK (1 + (subspaceAt mu (K.ofBits (qs.getD k 0))).getD t 0)) := by
  unfold inducedWeight
  have e := foldl_zip_sum (fun (w : E) (q : ℕ) ↦ (List.zip x (subspaceAt mu (K.ofBits q))).foldl
      (fun product (p : E × K) ↦ product * (1 + p.1 * ofK (1 + p.2))) w)
    (powers lam qs.length) qs 0 0 0
  rw [e, zero_add, powers, length_powersFrom, min_self]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [foldl_zip_mul (fun (a : E) (b : K) ↦ 1 + a * ofK (1 + b)) x _ _ 0 0, length_subspaceAt,
    getD_powersFrom _ _ _ _ (Finset.mem_range.mp hk), one_mul]

theorem ofK_add' (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_mul' (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem ofK_one' : ofK 1 = 1 := map_one (algebraMap K E)

/-- **`1 + Ŵ_t(x)` is `1 + W_t(x)·inv_t`**, the guest's chain over the roots times the
vanishing inverse. -/
theorem what_factor {mu t : ℕ} (ht : t ≤ mu) (x : K) (vals : List E)
    (hv : ∀ i < mu, vals.getD i 0 = ofK ((subspaceRoots mu).getD i 0)) (inv : E)
    (hinv : inv = ofK ((subspaceRoots mu).getD t 0)⁻¹) :
    ofK (1 + (subspaceAt mu x).getD t 0) = 1 + residualChain vals (ofK x) t * inv := by
  rw [residualChain_vanishing x vals hv t ht, hinv, subspaceRoots_getD ht,
    LeanVM.Protocol.Whir.subspaceAt_eq,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega), Option.map_some,
    Option.getD_some, LeanVM.Protocol.Whir.normVanishingAt, ofK_add', ofK_mul', ofK_one']

theorem getD_map_eOfNat (qs : List ℕ) (k : ℕ) (hk : k < qs.length) :
    (qs.map eOfNat).getD k 0 = ofK (K.ofBits (qs.getD k 0)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getD_eq_getElem _ _ hk]
  rfl

/-- **A level's scale times its product chain** (`μ = 1/λ`) is its induced weight, times
`λ^Q`'s share already in the scale. -/
theorem level_inner {lam li : E} (hli : lam * li = 1) (qs : List ℕ) {mu vo : ℕ} (x : List E)
    (hx : x.length = mu)
    (hval : ∀ i < mu, (osVals vo mu).getD i 0 = ofK ((subspaceRoots mu).getD i 0))
    (hinv : ∀ t < mu, word (vanishInv (vo + t)) 0 = ofK ((subspaceRoots mu).getD t 0)⁻¹)
    (hne : ∀ t < mu, x.getD t 0 * word (vanishInv (vo + t)) 0 ≠ 0) :
    lam ^ qs.length * (∏ t ∈ Finset.range mu, (x.getD t 0 * word (vanishInv (vo + t)) 0)) *
        (qs.map eOfNat).foldl (fun a p ↦ (a + residualProd (osVals vo mu) p
          (fun t ↦ (1 + x.getD t 0) / (x.getD t 0 * word (vanishInv (vo + t)) 0)) mu) * li) 0 =
      inducedWeight mu qs (powers lam qs.length) x := by
  have h := chain_mul_pow hli (fun p ↦ residualProd (osVals vo mu) p
    (fun t ↦ (1 + x.getD t 0) / (x.getD t 0 * word (vanishInv (vo + t)) 0)) mu) (qs.map eOfNat) 0
  rw [List.length_map] at h
  rw [mul_comm (lam ^ _), mul_assoc, h, zero_add, Finset.mul_sum, inducedWeight_sum, hx,
    min_eq_left (by omega)]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' := Finset.mem_range.mp hk
  have e1 : ∏ t ∈ Finset.range mu, (1 + x.getD t 0 *
      ofK (1 + (subspaceAt mu (K.ofBits (qs.getD k 0))).getD t 0)) =
      ∏ t ∈ Finset.range mu, (1 + x.getD t 0 * (1 + residualChain (osVals vo mu)
        (ofK (K.ofBits (qs.getD k 0))) t * word (vanishInv (vo + t)) 0)) :=
    Finset.prod_congr rfl fun t ht ↦ by
      rw [what_factor (by have := Finset.mem_range.mp ht; omega) _ _ hval _
        (hinv t (Finset.mem_range.mp ht))]
  rw [e1, residual_prod _ _ (fun t ↦ x.getD t 0) (fun t ↦ word (vanishInv (vo + t)) 0) mu hne,
    getD_map_eOfNat qs k hk']
  ring

/-- **A level's high chain** (`μ = 1/λ`) times `λ^Q` is its high part's share `recH`. -/
theorem level_high {lam li : E} (hli : lam * li = 1) (qs : List ℕ) {mu bits vo : ℕ}
    (hmu : mu < 64) (hb : bits ≤ mu + 1) (high hsv : List E) (hn : high.length ≤ 2 ^ bits)
    (hlen : hsv.length = high.length)
    (hval : ∀ i < mu, (osVals vo mu).getD i 0 = ofK ((subspaceRoots mu).getD i 0))
    (hhs : ∀ c < high.length, hsv.getD c 0 =
      high.getD c 0 * ofK ((subspaceRoots mu).getD mu 0)⁻¹ * ofK (hsNorm mu bits c)) :
    lam ^ qs.length * (qs.map eOfNat).foldl (fun a p ↦ (a + residualChain (osVals vo mu) p mu *
        novelSum hsv (residualChain (osVals vo mu) p) high.length bits) * li) 0 =
      ∑ k ∈ Finset.range qs.length, lam ^ k * highTerm mu high (qs.getD k 0) := by
  have h := chain_mul_pow hli (fun p ↦ residualChain (osVals vo mu) p mu *
    novelSum hsv (residualChain (osVals vo mu) p) high.length bits) (qs.map eOfNat) 0
  rw [List.length_map] at h
  rw [h, zero_add]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [getD_map_eOfNat qs k (Finset.mem_range.mp hk), highTerm,
    residual_high_eq hmu hb _ _ hval high hsv hn hlen hhs]

/-- **`eqEval`, as a product.** -/
theorem eqEval_prod : ∀ (z x : List E),
    eqEval z x = ∏ t ∈ Finset.range (min z.length x.length), (1 + z.getD t 0 + x.getD t 0) := by
  have key : ∀ (z x : List E) (a : E),
      (List.zipWith (fun x z ↦ 1 + x + z) z x).foldl (· * ·) a =
        a * ∏ t ∈ Finset.range (min z.length x.length), (1 + z.getD t 0 + x.getD t 0) := by
    intro z
    induction z with
    | nil => intro x a; simp
    | cons b z ih =>
      intro x a
      rcases x with _ | ⟨y, x⟩
      · simp
      · rw [List.zipWith_cons_cons, List.foldl_cons, ih]
        simp only [List.length_cons, Nat.add_min_add_right, Finset.prod_range_succ',
          List.getD_cons_succ, List.getD_cons_zero]
        ring
  intro z x
  rw [eqEval, key, one_mul]

end
end LeanVM.Guest.B1.Whir
