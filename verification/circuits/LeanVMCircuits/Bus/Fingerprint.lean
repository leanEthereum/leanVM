module

public import LeanVMCircuits.Bus.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-!
# The product check as a polynomial identity

Lemma `lem:gp` of `doc/leanvm/body/05-arithmetization.tex`: with the challenges kept formal, `A = (A_0, ..., A_3)` and
`X`, the product of `X - π_A(t)` over a multiset of tuples determines the multiset, in any characteristic. So the
bus balances exactly when the pushed and pulled products agree as polynomials (`balanced_iff_product_eq`).
A lookup producer's bit leaves multiply to its entry's factor raised to the multiplicity (`lem:prodbits`,
`producer_leaves_eq`), so the producer counts as its entries pushed with their multiplicities
(`balanced_of_product_check`).

That the polynomials agree is what the verifier tests at one random point `(α, β)`; the Schwartz-Zippel step that
makes the test sound with high probability, and the GKR and sumcheck arguments and the PCS that make the products
the committed tables' ones, are outside this file.
-/

namespace LeanVMCircuits.Bus

open LeanVMCircuits.Rec Polynomial

/-- The ring of the formal fingerprint challenges `A_0, ..., A_3`, an integral domain. -/
abbrev Challenges := MvPolynomial (Fin 4) K

/-- `eq(A, ι)` for slot `ι`, its bits low first. -/
noncomputable def eqWeight (ι : Fin 16) : Challenges :=
  ∏ j : Fin 4, if (ι : ℕ).testBit j then MvPolynomial.X j else 1 - MvPolynomial.X j

/-- The fingerprint `π_A(t) = ∑_ι eq(A, ι) t_ι` of a tuple, a polynomial in the formal `A`. -/
noncomputable def fingerprint (t : Tuple) : Challenges :=
  ∑ ι : Fin 16, eqWeight ι * MvPolynomial.C t[ι]

/-- The Boolean point naming slot `ι`. -/
noncomputable def point (ι : Fin 16) (j : Fin 4) : K := if (ι : ℕ).testBit j then 1 else 0

theorem testBit_eq_iff : ∀ ι ι' : Fin 16, (∀ j : Fin 4, (ι' : ℕ).testBit j = (ι : ℕ).testBit j) ↔ ι' = ι := by
  decide

theorem eval_eqWeight (ι ι' : Fin 16) :
    MvPolynomial.eval (point ι) (eqWeight ι') = if ι' = ι then 1 else 0 := by
  have factor : ∀ j : Fin 4,
      MvPolynomial.eval (point ι) (if (ι' : ℕ).testBit j then MvPolynomial.X j else 1 - MvPolynomial.X j) =
        if (ι' : ℕ).testBit j = (ι : ℕ).testBit j then 1 else 0 := by
    intro j
    by_cases h' : (ι' : ℕ).testBit j <;> by_cases h : (ι : ℕ).testBit j <;> simp [point, h, h']
  simp only [eqWeight, map_prod, factor, Finset.prod_boole, Finset.mem_univ, true_implies]
  simp only [testBit_eq_iff]

/-- Substituting the Boolean point of slot `ι` in the fingerprint returns the slot. -/
theorem eval_fingerprint (t : Tuple) (ι : Fin 16) : MvPolynomial.eval (point ι) (fingerprint t) = t[ι] := by
  simp only [fingerprint, map_sum, map_mul, eval_eqWeight, MvPolynomial.eval_C, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A tuple is recoverable from its fingerprint. -/
theorem fingerprint_injective : Function.Injective fingerprint := by
  intro s t h
  apply Vector.ext
  intro i hi
  have := congrArg (MvPolynomial.eval (point ⟨ i, hi ⟩)) h
  rwa [eval_fingerprint, eval_fingerprint] at this

/-- The fingerprint product `Π_P(A, X)` of a multiset of tuples. -/
noncomputable def product (P : Multiset Tuple) : Challenges[X] := fingerprintProduct fingerprint P

/-- Lemma `lem:gp`: `Π_P = Π_Q` if and only if `P = Q`. -/
theorem product_eq_iff (P Q : Multiset Tuple) : product P = product Q ↔ P = Q :=
  ⟨ eq_of_fingerprintProduct_eq (fingerprint_injective.injOn), congrArg product ⟩

/-- The bus balances exactly when the pushed and pulled fingerprint products agree as polynomials. -/
theorem balanced_iff_product_eq (f : Flushes) : f.Balanced ↔ product f.pushed = product f.pulled := by
  rw [Flushes.balanced_iff, product_eq_iff]

/-- A producer's multiplicity read from its bit columns: `m = ∑_k b_k 2^k`. -/
noncomputable def bitsValue (bits : ℕ → K) (nbit : ℕ) : ℕ :=
  ∑ k ∈ Finset.range nbit, (if bits k = 1 then 1 else 0) * 2 ^ k

/-- The leaf of bit `k` of a producer's entry `e`: `1 + b_k ((X - π_A(e))^(2^k) - 1)`. -/
noncomputable def leaf (e : Tuple) (b : K) (k : ℕ) : Challenges[X] :=
  1 + C (MvPolynomial.C b) * ((X - C (fingerprint e)) ^ 2 ^ k - 1)

/-- Lemma `lem:prodbits`: an entry's leaves multiply to its factor raised to its multiplicity. -/
theorem producer_leaves_eq (e : Tuple) (bits : ℕ → K) (nbit : ℕ) (boolean : ∀ k < nbit, bits k = 0 ∨ bits k = 1) :
    ∏ k ∈ Finset.range nbit, leaf e (bits k) k = (X - C (fingerprint e)) ^ bitsValue bits nbit := by
  have cast : ∀ k < nbit, C (MvPolynomial.C (bits k)) = (((if bits k = 1 then 1 else 0 : ℕ)) : Challenges[X]) := by
    intro k hk
    rcases boolean k hk with h | h <;> simp [h]
  rw [bitsValue, ← prod_one_add_bit_mul_pow_two_pow_sub_one _ nbit (fun k => if bits k = 1 then 1 else 0)
    (fun k _ => by split <;> omega)]
  apply Finset.prod_congr rfl
  intro k hk
  rw [leaf, cast k (Finset.mem_range.mp hk)]

/-- A lookup producer: entries with the bit columns of their multiplicities. -/
structure Producer where
  entries : List (Tuple × (ℕ → K))
  nbit : ℕ
  boolean : ∀ p ∈ entries, ∀ k < nbit, p.2 k = 0 ∨ p.2 k = 1

/-- The producer counted as its entries pushed with their multiplicities. -/
noncomputable def Producer.flushes (prod : Producer) : Flushes where
  produced := prod.entries.map fun p => (p.1, bitsValue p.2 prod.nbit)

/-- The product of all of the producer's leaves. -/
noncomputable def Producer.leaves (prod : Producer) : Challenges[X] :=
  (prod.entries.map fun p => ∏ k ∈ Finset.range prod.nbit, leaf p.1 (p.2 k) k).prod

theorem Producer.leaves_eq (prod : Producer) : prod.leaves = product prod.flushes.pushed := by
  rcases prod with ⟨ entries, nbit, boolean ⟩
  simp only [leaves, flushes, Flushes.pushed, product, fingerprintProduct]
  induction entries with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Multiset.coe_nil, zero_add] at ih ⊢
    rw [producer_leaves_eq p.1 p.2 nbit (boolean p (List.mem_cons_self ..)),
      ih (fun q hq => boolean q (List.mem_cons_of_mem _ hq)), Multiset.map_add, Multiset.prod_add,
      Multiset.map_replicate, Multiset.prod_replicate]

theorem product_add (P Q : Multiset Tuple) : product (P + Q) = product P * product Q := by
  simp [product, fingerprintProduct, Multiset.map_add, Multiset.prod_add]

/--
The product check with a producer's leaves: if the pushed tuples' factors times the producer's leaves equal the
pulled tuples' factors as polynomials, the bus balances with the producer counted as its entries pushed with
their multiplicities.
-/
theorem balanced_of_product_check (f : Flushes) (prod : Producer)
    (check : product f.pushed * prod.leaves = product f.pulled) : (f ++ prod.flushes).Balanced := by
  have pulled_zero : prod.flushes.pulled = 0 := by simp [Producer.flushes, Flushes.pulled]
  rw [balanced_iff_product_eq, Flushes.pushed_append, Flushes.pulled_append, pulled_zero, add_zero, product_add,
    ← prod.leaves_eq, check]

end LeanVMCircuits.Bus
