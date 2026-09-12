import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Slot
/-!
# Adaptive probes into a sampled secret table

A hash input names one structural coordinate and carries one candidate value. Up to the first
correct candidate, an adaptive strategy sees only misses. Its coordinate and candidate at every
such step are therefore fixed by the all-miss history, so a table with per-cell mass at most
`epsilon` is hit with probability at most `q * epsilon`. There is no union over table coordinates.
-/

namespace SphincsSecurity

open OracleComp ENNReal

variable {D R : Type} [DecidableEq R]

namespace Concrete

noncomputable local instance secretProbeSampleableOfFintype {T : Type} [Fintype T] [Nonempty T] : SampleableType T :=
  SampleableType.ofFintype T

structure FtsSecretProbe where
  index : Index
  tree : FtsTree
  leafIdx : FtsLeaf
  candidate : Digest
def FtsSecretProbe.input (parameter : PublicParameter) (probe : FtsSecretProbe) : HashInput :=
  tweakableHashInput parameter (.ftsLeaf probe.index probe.tree probe.leafIdx)
    (digestBytes probe.candidate)

theorem FtsSecretProbe.input_injective (parameter : PublicParameter) :
    Function.Injective (FtsSecretProbe.input parameter) := by
  intro left right heq
  have hparts := tweakableHashInput_injective parameter (by trivial) (by trivial) heq
  have hdomain : left.index = right.index ∧ left.tree = right.tree ∧
      left.leafIdx = right.leafIdx := by
    simpa only [HashDomain.ftsLeaf.injEq] using hparts.1
  have hcandidate : left.candidate = right.candidate := digestBytes_injective hparts.2
  cases left
  cases right
  simp only [FtsSecretProbe.mk.injEq] at hdomain hcandidate ⊢
  exact ⟨hdomain.1, hdomain.2.1, hdomain.2.2, hcandidate⟩

end Concrete

end SphincsSecurity
