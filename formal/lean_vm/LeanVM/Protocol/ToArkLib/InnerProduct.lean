/-
  LeanVM.Protocol.ToArkLib.InnerProduct

  The inner-product interface on a hypercube table: a query is a weight on the cube, the answer
  is the weighted sum of the table. Candidate for ArkLib.
-/

module

public import ArkLib.OracleReduction.OracleInterface
public import CompPoly.Multilinear.Basic

/-!
# The inner-product oracle

A table `t : CMlPolynomialEval R n` holds `2 ^ n` values, and `evalMle t r` is its multilinear
extension at a point `r`. ArkLib's interface on such a table answers a position with the entry
there. An interface built on `Weight.pair` answers a *weight*: a table `W` over a ring `S` into
which `R` maps, given with an evaluator of `W`'s own extension that the party asking can run (a
weight given by its cube values alone would cost the asker `2 ^ n` to extend). The answer is the
inner product `⟨W, t⟩ = Σ_x W(x)·φ(t(x))`. A table is a vector, on which ArkLib registers the
position-query interface, so a consumer wraps its tables in a type of its own and declares the
instance there (`LeanVM.Protocol.Field` does, on `Column`).

An evaluation `t̃(p)` is the answer to the equality kernel at `p` (`Weight.pair_eqWeight`), so
the interface subsumes the evaluation interface; a weight that is no equality kernel is what a
sum against the table, such as a batch of claims, asks for.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

/-- A weight on the cube: its values, and an evaluator of its multilinear extension, with the
proof that the two agree. -/
structure Weight (S : Type*) [CommRing S] (n : ℕ) where
  /-- The values on the cube. -/
  onCube : CMlPolynomialEval S n
  /-- The extension, as the asker evaluates it. -/
  mle : Vector S n → S
  /-- The evaluator computes the extension of the cube values. -/
  mle_eq : ∀ r, mle r = evalMle onCube r

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The inner product `Σ_x W(x)·φ(t(x))` of a weight over `S` with a table over `R`. -/
def Weight.pair {n : ℕ} (φ : R →+* S) (W : Weight S n) (t : CMlPolynomialEval R n) : S :=
  ∑ i : Fin (2 ^ n), W.onCube[i] * φ t[i]

/-- The equality kernel at `p` as a weight: its values are the Lagrange basis at `p`, its
extension the product of the coordinatewise factors. -/
def eqWeight {n : ℕ} (p : Vector S n) : Weight S n where
  onCube := lagrangeBasis p
  mle := fun r ↦ ∏ k : Fin n, (p[k] * r[k] + (1 - p[k]) * (1 - r[k]))
  mle_eq := fun r ↦ by rw [← eqTilde_eq_prod, eqTilde, eval_mle_eq_eval]

/-- Pairing the equality kernel at `p` with a table evaluates the table's extension at `p`. -/
theorem Weight.pair_eqWeight {n : ℕ} (φ : R →+* S) (p : Vector S n)
    (t : CMlPolynomialEval R n) : (eqWeight p).pair φ t = eval₂Mle t φ p := by
  unfold Weight.pair eqWeight eval₂Mle
  rw [eval_mle_eq_eval, CMlPolynomialEval.eval, Vector.dotProduct_eq_root_dotProduct]
  simp only [dotProduct, CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map,
    Vector.get_eq_getElem]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

end
end LeanVM.Protocol
