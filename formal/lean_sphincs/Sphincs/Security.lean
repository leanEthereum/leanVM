module

public import FORS.Main
public import Sphincs.Bridge
public import Sphincs.AdvRpm

@[expose] public section

/-!
# leanSPHINCS in the random-permutation model

**The end theorem.** `Sphincs.leanSphincsStronglyUnforgeable` proves
`Sphincs.LeanSphincsStronglyUnforgeable` (`Statement/LeanSphincs.lean`): an adversary that itself
makes at most `q` calls of `π` and `π⁻¹` and at most `1,182,000,000` signing requests forges with
probability at most `(q + 2^19) · 2^-127`; the signer's hashing, its WOTS+C counter search
included, key generation and the forgery's verification are not charged to `q`. The route: the
random-oracle theorem at the adversary's own count, `FORS.Lifetimes.h26_layered_adversary`
(`(q + 265072) / 2^127` for upstream's model `FORS.Scheme` at the deployed configuration, leanVM
main `40f877dc`: key generation's `264193` hash calls and the verification's `879` are the
constant), moved to the crate's key generation and signer in the model's hash monad (`FORS.Crate`,
by `Common.SufCma.StaticSwap.romBoundAdv`), to the random-permutation model by
`Common.SufCma.stronglyUnforgeable_of_romBoundAdv` (the indifferentiability term one unit more),
and to the statement's scheme through the maps (`Sphincs.Model.stronglyUnforgeableAdv_of_model`).
-/

namespace Sphincs

/-- The proof's constant fits the statement's. -/
example : 265072 + 1 ≤ securitySlack := by decide

/-- **leanSPHINCS is strongly unforgeable in the random-permutation model**: `(q + 2^19) · 2^-127`
for an adversary making `q` calls of `π` and `π⁻¹` itself, up to `1,182,000,000` signing requests. -/
theorem leanSphincsStronglyUnforgeable : LeanSphincsStronglyUnforgeable :=
  Model.stronglyUnforgeable_mono_slack
    (Model.stronglyUnforgeableAdv_of_model
      (fun adversary q hq ↦ FORS.Lifetimes.h26_layered_adversary adversary q hq))
    (by decide)

end Sphincs
