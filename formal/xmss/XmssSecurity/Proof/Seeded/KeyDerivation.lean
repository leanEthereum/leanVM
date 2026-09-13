import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.HashInputLemmas

namespace XmssSecurity

private theorem fin_of_ofNat32_eq {n : Nat} {a b : Fin n} (hn : n ≤ 2 ^ 32)
    (h : BitVec.ofNat 32 a.val = BitVec.ofNat 32 b.val) : a = b := by
  apply Fin.ext
  have ha := a.isLt.trans_le hn
  have hb := b.isLt.trans_le hn
  have heq := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using heq

theorem keygenDomainFields_injective : Function.Injective keygenDomainFields := by
  intro left right h
  cases left <;> cases right <;>
    simp_all only [keygenDomainFields, TweakFields.mk.injEq, BitVec.reduceEq, false_and,
      true_and, KeygenDomain.chain.injEq]
  obtain ⟨hchain, hepoch⟩ := h
  exact ⟨fin_of_ofNat32_eq (by decide) hepoch, fin_of_ofNat32_eq (by decide) hchain⟩

theorem keygenHashInput_injective {p₁ p₂ : PublicParameter} {d₁ d₂ : KeygenDomain}
    {s₁ s₂ : MasterSeed} (h : keygenHashInput p₁ d₁ s₁ = keygenHashInput p₂ d₂ s₂) :
    p₁ = p₂ ∧ d₁ = d₂ ∧ s₁ = s₂ := by
  unfold keygenHashInput at h
  obtain ⟨hprefix, hseed⟩ := List.append_inj' h (by simp)
  obtain ⟨htweak, hparameter⟩ := List.append_inj' hprefix (by simp)
  exact ⟨bytesLE_injective 16 hparameter,
    keygenDomainFields_injective (fieldBytes_injective htweak), bytesLE_injective 32 hseed⟩

/-- Derivation hashes and verification hashes have disjoint input sets, for all parameters and payloads. -/
theorem keygenHashInput_ne_tweakableHashInput (p₁ p₂ : PublicParameter)
    (d₁ : KeygenDomain) (d₂ : HashDomain) (seed : MasterSeed) (payload : HashInput) :
    keygenHashInput p₁ d₁ seed ≠ tweakableHashInput p₂ d₂ payload := by
  intro h
  unfold keygenHashInput tweakableHashInput tweakBytes at h
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp)
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp)
  have htag := congrArg TweakFields.tag (fieldBytes_injective htweak)
  cases d₁ <;> cases d₂ <;> simp [keygenDomainFields, hashDomainFields] at htag

/-- One raw oracle query can name at most one master seed. -/
theorem keygenHashInput_seed_unique (input : HashInput) {s₁ s₂ : MasterSeed}
    (h₁ : ∃ p d, keygenHashInput p d s₁ = input)
    (h₂ : ∃ p d, keygenHashInput p d s₂ = input) : s₁ = s₂ := by
  obtain ⟨p₁, d₁, h₁⟩ := h₁
  obtain ⟨p₂, d₂, h₂⟩ := h₂
  exact (keygenHashInput_injective (h₁.trans h₂.symm)).2.2

end XmssSecurity
