import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeWitness
/-!
# Probability of a fixed few-time coverage pattern

The relevant part of an admissible digest is its 26-bit index and its fourteen opened 10-bit leaf
coordinates.  For a fixed assignment of trees to distinct signing results, the successful tuples
are in bijection with one free index and one free leaf vector per signing result.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev FewTimeView := Index × (FtsTree → FtsLeaf)

theorem fewTimeView_card : Fintype.card FewTimeView =
    2 ^ (totalHeight + ftsTreeHeight * (ftsTrees - 1)) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, ← pow_mul, ← pow_add]

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R

end SphincsSecurity.Concrete
