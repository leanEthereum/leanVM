import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeProbability
/-!
# Padding adaptive few-time view sequences

A run may make fewer than the allowed number of signing queries. Extending its view sequence with
independent unused coordinates embeds every coverage pattern into the fixed signature-limit space.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity_1 {α : Type} [Fintype α] [Nonempty α] : SampleableType α :=
  SampleableType.ofFintype α

theorem evalDist_independent_uniform_pair
    {α β : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] :
    𝒟[(do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right))] =
      𝒟[($ᵗ (α × β) : ProbComp (α × β))] := by
  apply SPMF.ext
  intro target
  rw [show (do
      let left ← $ᵗ α
      let right ← $ᵗ β
      pure (left, right)) = Prod.mk <$> ($ᵗ α) <*> ($ᵗ β) by
    simp [monad_norm]]
  change Pr[= target | Prod.mk <$> ($ᵗ α) <*> ($ᵗ β)] =
    Pr[= target | $ᵗ (α × β)]
  rw [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    probOutput_uniformSample, probOutput_uniformSample, Fintype.card_prod,
    Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]

def listToFunction (count : Nat) (values : List FewTimeView) : Fin count → FewTimeView :=
  fun position => values.getD position.val default

@[simp]
theorem listToFunction_ofFn (values : Fin count → FewTimeView) :
    listToFunction count (List.ofFn values) = values := by
  funext position
  simp [listToFunction, List.getD]

end SphincsSecurity.Concrete
