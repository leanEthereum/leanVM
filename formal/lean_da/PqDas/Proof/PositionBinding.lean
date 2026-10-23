/-
# Position-binding of the scheme

Position-binding of the erasure code commitment scheme reduces directly to
position-binding of the underlying vector commitment (Foundations of Data
Availability Sampling, eprint 2023/1079, Lemma 13). The reduction receives a
vector-commitment key, samples the argument system's crs itself, simulates the
random-oracle world for the adversary, and forwards the adversary's output
with the proof component stripped: the scheme's verification is the argument
verification *and* the vector-commitment verification, so any pair of openings
breaking position-binding of the scheme in particular breaks position-binding
of the vector commitment.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Target.Scheme
import PqDas.VcvioExtras

open OracleComp OracleSpec ENNReal

namespace PqDas

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L Crs Proof : Type}

/-- Reduction (an explicit PPT algorithm): a position-binding adversary
against the scheme becomes one against the vector commitment. It samples the
crs itself, simulates the random oracle lazily, and strips the proof from the
commitment. -/
noncomputable def posBindingReduction [DecidableEq ComVC] [SampleableType L]
    {vc : VectorCommitment Λ n CkVC ComVC Opn} {chk : CodeChecker Λ n L}
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (A : ErasureCodeCommitment.PosBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    VectorCommitment.PosBindingAdv Λ n CkVC ComVC Opn := fun ckVC => do
  let crs ← ps.setup
  let (com, i, x, τ, x', τ') ← simulateRom (A (ckVC, crs))
  return (com.1, i, x, τ, x', τ')

/-- **Position-binding of the scheme**, by reduction to position-binding of
the vector commitment via `posBindingReduction`. -/
theorem scheme_positionBinding [DecidableEq Λ] [DecidableEq ComVC] [SampleableType L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L)
    (ps : Nark (CkVC × ComVC × L) (Fin n → Λ) Crs Proof (schemeRel vc chk))
    (A : ErasureCodeCommitment.PosBindingAdv (OracleComp (unifSpec + (ComVC →ₒ L)))
      Λ n (CkVC × Crs) (ComVC × Proof) Opn) :
    (scheme (m := OracleComp (unifSpec + (ComVC →ₒ L)))
        C vc chk ps).posBindingExp (roRuntime ComVC L) A {true} ≤
      Pr{let x ← vc.posBindingExp (posBindingReduction ps A)}[x = true] := by
  unfold ErasureCodeCommitment.posBindingExp VectorCommitment.posBindingExp
    posBindingReduction
  rw [← evalDist_simulateRom, evalDist_singleton_eq_prEvent]
  dsimp only [scheme]
  simp only [monad_norm, simulateRom]
  -- Peel the two lifted setup samplings on both sides.
  rw [simulateRomWithCache_liftM_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun ckVC _ => ?_
  rw [simulateRomWithCache_liftM_bind]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun crs _ => ?_
  -- Split off the adversary's simulated run on both sides: the game threads
  -- the adversary's final oracle cache into verification, the reduction
  -- discards it.
  rw [simulateRomWithCache_bind, bind_simulateRomWithCache]
  simp only [bind_assoc]
  refine OracleComp.prEvent_bind_mono_of_support (spec := unifSpec) _ _ _ fun out _ => ?_
  obtain ⟨⟨com, i, x, τ, x', τ'⟩, cache⟩ := out
  -- Evaluate the two verification queries; their answers `l`, `l'` are
  -- irrelevant to the vector-commitment part of the win condition.
  simp only [monad_norm, simulateRomWithCache_query_bind, simulateRomWithCache_pure]
  refine OracleComp.prEvent_le_prEvent_pure_of_forall_mem_support fun b hb hb' => ?_
  simp only [mem_support_bind_iff] at hb
  obtain ⟨y, _, y', _, hb⟩ := hb
  grind

end PqDas
