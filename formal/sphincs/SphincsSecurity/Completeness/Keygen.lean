import SphincsSecurity.Completeness.Digest

/-!
# What key generation leaves uncached

Key generation derives the public parameter and builds the top tree: derivation inputs and chain,
leaf and node tweaks. The searches that follow hash under the randomizer, message and encoding
tweaks, which none of those produce, so their inputs are all still missing from the cache when
signing begins.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Completeness

open Concrete

/-- Key generation avoids any input that none of its hash calls can produce. -/
theorem Avoids.keygen_of (seed : MasterSeed) (target : HashInput)
    (hkey : ∀ (parameter : PublicParameter) (domain : KeygenDomain),
      keygenHashInput parameter domain seed ≠ target)
    (hchain : ∀ (parameter : PublicParameter) (tree : TreeIndex) (leaf : LeafIndex)
      (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain topLayer tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (parameter : PublicParameter) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf topLayer tree leaf) payload ≠ target)
    (hnode : ∀ (parameter : PublicParameter) (tree : TreeIndex) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node topLayer tree level nodeIdx) payload ≠ target)
    (f : QueryImpl HashSpec Id) : Avoids f target (Seeded.keygenFromSeed seed) :=
  Avoids.keygenFromSeed f target seed (hkey _ _) (fun _ _ _ _ => hchain _ _ _ _ _ _)
    (fun _ _ => hleaf _ _ _ _) (fun _ _ _ => hnode _ _ _ _ _) (fun _ _ => hkey _ _)

theorem keygenDomain_tag_ne (domain : KeygenDomain) (tag : Nat) (htag : tag = 4 ∨ tag = 7 ∨ tag = 12) :
    (keygenDomainFields domain).tag ≠ BitVec.ofNat 8 tag := by
  rcases htag with rfl | rfl | rfl <;> cases domain <;> simp [keygenDomainFields, tweakFields, ftsTweakFields]

/-- After key generation, nothing the randomizer search, the message digest or a counter search hashes is cached. -/
theorem keygen_fresh (seed : MasterSeed) (r : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.keygenFromSeed seed)).run ∅))
    (message : Message) :
    (∀ s, r.2 (randInput r.1.2 message s) = none)
      ∧ (∀ ρ, r.2 (msgInput r.1.2 message ρ) = none)
      ∧ EncodingFresh r.1.2.parameter (fun _ => True) r.2 := by
  refine ⟨fun s => cache_none_of_avoids _ ∅ r hr _ rfl (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_),
    fun ρ => cache_none_of_avoids _ ∅ r hr _ rfl (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_),
    fun lay _ tree leaf payload => cache_none_of_avoids _ ∅ r hr _ rfl
      (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_)⟩
  · intro parameter domain h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.parameter
      (fields1 := keygenDomainFields domain) (fields2 := ⟨7#8, 0#8, 0#8, 0#32, BitVec.ofNat 32 s, 0#32⟩)
      (keygenDomain_tag_ne domain 7 (by simp)) _ _
      (by simpa only [keygenHashInput, randInput, randomizerHashInput, List.append_assoc] using h)
  · intro parameter tree leaf chainIdx step payload h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.parameter
      (fields1 := hashDomainFields (.chain topLayer tree leaf chainIdx step))
      (fields2 := ⟨7#8, 0#8, 0#8, 0#32, BitVec.ofNat 32 s, 0#32⟩)
      (by simp [hashDomainFields, tweakFields]) _ _
      (by simpa only [tweakableHashInput, tweakBytes, randInput, randomizerHashInput,
        List.append_assoc] using h)
  · intro parameter tree leaf payload h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.parameter
      (fields1 := hashDomainFields (.leaf topLayer tree leaf))
      (fields2 := ⟨7#8, 0#8, 0#8, 0#32, BitVec.ofNat 32 s, 0#32⟩)
      (by simp [hashDomainFields, tweakFields]) _ _
      (by simpa only [tweakableHashInput, tweakBytes, randInput, randomizerHashInput,
        List.append_assoc] using h)
  · intro parameter tree level nodeIdx payload h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.parameter
      (fields1 := hashDomainFields (.node topLayer tree level nodeIdx))
      (fields2 := ⟨7#8, 0#8, 0#8, 0#32, BitVec.ofNat 32 s, 0#32⟩)
      (by simp [hashDomainFields, tweakFields]) _ _
      (by simpa only [tweakableHashInput, tweakBytes, randInput, randomizerHashInput,
        List.append_assoc] using h)
  · intro parameter domain
    exact keygenHashInput_ne_tweakableHashInput parameter _ domain _ seed _
  · intro parameter tree leaf chainIdx step payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree leaf payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree level nodeIdx payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter domain
    exact keygenHashInput_ne_tweakableHashInput parameter _ domain _ seed _
  · intro parameter tree' leaf' chainIdx step payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree' leaf' payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree' level nodeIdx payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _

end SphincsSecurity.Completeness
