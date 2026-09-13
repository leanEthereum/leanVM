import SphincsSecurity.Proof.IdealStatement
import SphincsSecurity.Proof.Scheme.Bytes

namespace SphincsSecurity

theorem keygenDomainFields_injective : Function.Injective keygenDomainFields := by
  intro left right h
  cases left <;> cases right <;>
    simp_all only [keygenDomainFields, TweakFields.mk.injEq, BitVec.reduceEq, false_and,
      true_and, KeygenDomain.ots.injEq, KeygenDomain.fts.injEq]
  · obtain ⟨hlay, htree, hchain, hleaf⟩ := h
    exact ⟨fin_of_ofNat_eq (by decide) hlay, fin_of_ofNat_eq (by decide) htree,
      fin_of_ofNat_eq (by decide) hleaf, fin_of_ofNat_eq (by decide) hchain⟩
  · obtain ⟨htree, hindex, hleaf⟩ := h
    exact ⟨fin_of_ofNat_eq (by decide) hindex, fin_of_ofNat_eq (by decide) htree,
      fin_of_ofNat_eq (by decide) hleaf⟩

theorem keygenHashInput_injective {p₁ p₂ : PublicParameter} {d₁ d₂ : KeygenDomain}
    {s₁ s₂ : MasterSeed} (h : keygenHashInput p₁ d₁ s₁ = keygenHashInput p₂ d₂ s₂) :
    p₁ = p₂ ∧ d₁ = d₂ ∧ s₁ = s₂ := by
  unfold keygenHashInput at h
  obtain ⟨hprefix, hseed⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨htweak, hparameter⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hparameter,
    keygenDomainFields_injective (fieldBytes_injective htweak), bytesLE_injective hseed⟩

/-- Derivation hashes and verification hashes have disjoint input sets, for all parameters and payloads. -/
theorem keygenHashInput_ne_tweakableHashInput (p₁ p₂ : PublicParameter)
    (d₁ : KeygenDomain) (d₂ : HashDomain) (seed : MasterSeed) (payload : HashInput) :
    keygenHashInput p₁ d₁ seed ≠ tweakableHashInput p₂ d₂ payload := by
  intro h
  unfold keygenHashInput tweakableHashInput tweakBytes at h
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  have htag := congrArg TweakFields.tag (fieldBytes_injective htweak)
  cases d₁ <;> cases d₂ <;> simp [keygenDomainFields, hashDomainFields] at htag

/-- One raw oracle query can name at most one master seed. -/
theorem keygenHashInput_seed_unique (input : HashInput) {s₁ s₂ : MasterSeed}
    (h₁ : ∃ p d, keygenHashInput p d s₁ = input)
    (h₂ : ∃ p d, keygenHashInput p d s₂ = input) : s₁ = s₂ := by
  obtain ⟨p₁, d₁, h₁⟩ := h₁
  obtain ⟨p₂, d₂, h₂⟩ := h₂
  exact (keygenHashInput_injective (h₁.trans h₂.symm)).2.2

end SphincsSecurity
