/-
  LeanVM.Guest.B1.Main.Consts

  The compile-time constants of `aggregate_claims`: the skip domain's nodes, the barycentric
  denominator, the batching transcript's seed.
-/

module

public import LeanVM.Guest.B1.Lag64
public import LeanVM.Guest.B1.Main.AggLoops
public import LeanVM.Spec.Node

/-!
# The batching constants

`phiWords_eq`: the data's 64 nodes are `φ_8(i)` (`PHI8_NODES`, V:282); `lagInv_mul`: the word
`LAGRANGE_INV_S` times the product of the nonzero nodes is `1`, so it is `windowDenominator 64`
(V:745); `aggSeed_eq`: `AGG_SEED_0`, `AGG_SEED_1` are the cells of `blake2sBytes batchLabel`
(N:271).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

theorem phiWords_eq : ∀ i < 64, K.ofBits (phiWords.getD i 0) = Flock.phi8 i := fun i hi => by
  rw [show phiWords.getD i 0 = phi8Words.getD i 0 from
    (by decide +kernel : ∀ i < 64, phiWords.getD i 0 = phi8Words.getD i 0) i hi]
  exact ofBits_phi8Words i (by omega)

theorem lagInv_mul : K.ofBits 11666641484232641359 *
    ((List.range 63).map fun k => Flock.phi8 (k + 1)).foldl (· * ·) 1 = 1 := by decide +kernel

/-- The batching transcript's label, as bytes. -/
theorem batchLabel_eq : batchLabel = [108, 101, 97, 110, 118, 109, 47, 114, 101, 99, 117, 114, 115,
    105, 111, 110, 45, 97, 103, 103, 114, 101, 103, 97, 116, 105, 111, 110, 47, 118, 49] := by
  rw [batchLabel, String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList]
  decide +kernel

theorem aggSeed_eq : (word 13601591990776631179 14393745058652752134 0,
    word 10115303172019694088 4136606974476857268 0) = digestScalars (blake2sBytes batchLabel) := by
  refine pair_eq_digestScalars_iff.mpr ⟨rfl, rfl, Vector.toList_inj.mp ?_⟩
  rw [batchLabel_eq]
  decide +kernel

end
end LeanVM.Guest.B1.Main
