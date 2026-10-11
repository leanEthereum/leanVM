import Whir.PublicCompressionCouplingMixed

/-! Operational postconditions for the pinned public simulator. Certificates
are proved for every adaptive continuation, not supplied by a cryptographic
hypothesis. They permit bounded private inspection after the public game. -/
namespace Whir.PublicCompressionCouplingMixed
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame TypedOracleCompiler

namespace Computation
variable {Q n : Nat} {R S : Type}

theorem every_of_forall (p : Computation Q R n) (P : R → Prop)
    (h : ∀ r, P r) : Sampling.Every P p := by
  induction p with
  | ret r => exact h r
  | draw k next ih => exact fun d => ih d

@[simp] theorem every_map (p : Computation Q R n) (f : R → S) (P : S → Prop) :
    Sampling.Every P (map f p) ↔ Sampling.Every (fun r => P (f r)) p := by
  induction p with
  | ret r => rfl
  | draw k next ih => simp only [map,Sampling.Every]; exact forall_congr' ih

def certify {P : R → Prop} {n : Nat} : (p : Computation Q R n) → Sampling.Every P p →
    Computation Q {r // P r} n
  | .ret r, h => .ret ⟨r,h⟩
  | .draw k next, h => .draw k (fun d => certify (next d) (h d))

@[simp] theorem eval_certify (table : Key Q → Digest32) (p : Computation Q R n)
    {P : R → Prop} (h : Sampling.Every P p) :
    (Sampling.eval table (certify p h)).val = Sampling.eval table p := by
  induction p with
  | ret => rfl
  | draw k next ih => exact ih (table k) _
end Computation

/-- The source call meter bounds every possible public view, including all
choices of replies at every adaptive continuation. -/
theorem compile_every_viewCost {R : Type} (Q : Nat) (iv : Digest32)
    (log : DuplexPublicSimulator.PublicLog) (p : Program R) (remaining : Nat)
    (cap : remaining ≤ Q) (counted : Counts remaining p) :
    Sampling.Every (fun view => viewCost view ≤ remaining)
      (compile Q iv log p remaining cap counted) := by
  induction p generalizing log remaining with
  | done r => simp [compile,Sampling.Every,viewCost]
  | ask query next ih =>
    cases query with
    | primitive purpose input =>
      simp only [compile,Sampling.every_pad,Sampling.every_bind]
      apply Computation.every_of_forall
      intro result
      apply (Computation.every_map _ _ _).mpr
      apply (ih result.2 result.1 (remaining-1) (by omega) (counted.2 _)).mono
      intro tail bound
      have hc : 1 ≤ remaining := counted.1
      simpa only [DuplexRawProgram.observe,viewCost,List.map_cons,List.sum_cons,Query.cost]
        using (show 1 + viewCost tail ≤ remaining by omega)
    | construction coordinate valid =>
      simp only [compile,Sampling.every_pad,Sampling.Every]
      intro answer
      apply (Computation.every_map _ _ _).mpr
      apply (ih answer log (remaining-pathCost coordinate) (by omega) (counted.2 _)).mono
      intro tail bound
      have hc : pathCost coordinate ≤ remaining := counted.1
      simpa only [DuplexRawProgram.observe,viewCost,List.map_cons,List.sum_cons,Query.cost]
        using (show pathCost coordinate + viewCost tail ≤ remaining by omega)

#print axioms compile_every_viewCost
#print axioms Computation.eval_certify
end Whir.PublicCompressionCouplingMixed
