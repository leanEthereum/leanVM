import SphincsFors.Bytes
import SphincsFors.Fresh

/-! Injectivity and separation of the candidate's exact byte inputs. These facts keep the
derivation and verification addresses distinct in later random-oracle reductions. -/

namespace SphincsFors.Security

/-- The fixed-width prefix determines its parameter and fields, with no restriction on payload. -/
theorem fieldInput_injective {fields fields' : TweakFields}
    {parameter parameter' : PublicParameter} {payload payload' : HashInput}
    (h : bytesLE 16 parameter ++ fieldBytes fields ++ payload =
      bytesLE 16 parameter' ++ fieldBytes fields' ++ payload') :
    fields = fields' ∧ parameter = parameter' ∧ payload = payload' := by
  obtain ⟨hprefix, hpayload⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  obtain ⟨hparameter, hfields⟩ := List.append_inj hprefix (by simp [bytesLE_length])
  exact ⟨fieldBytes_injective hfields, bytesLE_injective hparameter, hpayload⟩

theorem tweakableInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : HashDomain} {payload payload' : HashInput}
    (h : tweakableHashInput parameter domain payload =
      tweakableHashInput parameter' domain' payload') :
    hashDomainFields domain = hashDomainFields domain' ∧
      parameter = parameter' ∧ payload = payload' :=
  fieldInput_injective h

/-- The first of the two derived values that share the hash of `domain`: the even chain start, the
even FORS secret. Every other value has its own hash. -/
def pairDomain : KeygenDomain → KeygenDomain
  | .ots lay tree leaf chain =>
      .ots lay tree leaf ⟨2 * (chain.val / 2), Nat.lt_of_le_of_lt (Nat.mul_div_le _ 2) chain.isLt⟩
  | .fts index tree leaf =>
      .fts index tree ⟨2 * (leaf.val / 2), Nat.lt_of_le_of_lt (Nat.mul_div_le _ 2) leaf.isLt⟩
  | domain => domain

theorem pairDomain_fields (domain : KeygenDomain) :
    keygenDomainFields (pairDomain domain) = keygenDomainFields domain := by
  cases domain with
  | parameter => rfl
  | surrogate level => rfl
  | ots lay tree leaf chain =>
      simp only [pairDomain, keygenDomainFields]
      rw [show 2 * (chain.val / 2) / 2 = chain.val / 2 by omega]
  | fts index tree leaf =>
      simp only [pairDomain, keygenDomainFields]
      rw [show 2 * (leaf.val / 2) / 2 = leaf.val / 2 by omega]

/-- Two derived values have the same address only if they are the two halves of one hash. -/
theorem deriveFields_pair {left right : KeygenDomain}
    (h : keygenDomainFields left = keygenDomainFields right) : pairDomain left = pairDomain right := by
  cases left <;> cases right <;>
    simp only [keygenDomainFields, tweakFields, TweakFields.mk.injEq] at h
  all_goals try { simp at h; done }
  · rfl
  · rename_i lay tree leaf chain lay' tree' leaf' chain'
    obtain ⟨_, _, hchain, hleaf⟩ := h
    have hl : lay = lay' := layer_eq _ _
    have ht : tree = tree' := treeIndex_eq _ _
    have hc := chain.isLt
    have hc' := chain'.isLt
    simp only [numChains] at hc hc'
    have hnat := ofNat_inj_of_lt (w := 24) (a := chain.val / 2) (b := chain'.val / 2)
      (by omega) (by omega) hchain
    have he : leaf = leaf' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (leaf.isLt.trans_le (by decide))
        (leaf'.isLt.trans_le (by decide)) hleaf
    cases hl; cases ht; cases he
    simp only [pairDomain, hnat]
  · rename_i index tree leaf index' tree' leaf'
    obtain ⟨_, _, hpacked, hindex⟩ := h
    have hi : index = index' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (index.isLt.trans_le (by decide))
        (index'.isLt.trans_le (by decide)) hindex
    have ht := tree.isLt
    have ht' := tree'.isLt
    have hl := leaf.isLt
    have hl' := leaf'.isLt
    simp only [ftsTrees, ftsTreeHeight] at ht ht' hl hl'
    have hnat := ofNat_inj_of_lt (w := 24) (a := tree.val + 512 * (leaf.val / 2))
      (b := tree'.val + 512 * (leaf'.val / 2)) (by omega) (by omega) hpacked
    have htree : tree = tree' := Fin.ext (by omega)
    have hleaf : leaf.val / 2 = leaf'.val / 2 := by omega
    cases hi; cases htree
    simp only [pairDomain, hleaf]
  · rename_i level level'
    obtain ⟨_, _, hlevel, _⟩ := h
    have hl : level = level' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (level.isLt.trans_le (by decide))
        (level'.isLt.trans_le (by decide)) hlevel
    cases hl; rfl

/-- Two seed-derivation queries have the same input only if their parameters and seeds agree and
they derive the same value or the two halves of one hash. -/
theorem keygenInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : KeygenDomain} {seed seed' : MasterSeed}
    (h : keygenHashInput parameter domain seed = keygenHashInput parameter' domain' seed') :
    parameter = parameter' ∧ pairDomain domain = pairDomain domain' ∧ seed = seed' := by
  obtain ⟨hfields, hp, hs⟩ := fieldInput_injective h
  exact ⟨hp, deriveFields_pair hfields, bytesLE_injective hs⟩

/-- The two halves of one hash have the same input. -/
theorem keygenHashInput_pairDomain (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    keygenHashInput parameter (pairDomain domain) seed = keygenHashInput parameter domain seed := by
  simp only [keygenHashInput, pairDomain_fields]

/-- Every verification-domain tag is distinct from every seed-derivation tag. -/
theorem derive_tag_ne_hash_tag (derive : KeygenDomain) (hash : HashDomain) :
    (keygenDomainFields derive).tag ≠ (hashDomainFields hash).tag := by
  cases derive <;> cases hash <;> simp [keygenDomainFields, hashDomainFields, tweakFields]

/-- Seed derivation cannot be confused with any verifier hash input, even across parameters. -/
theorem keygenInput_ne_hashInput (parameter parameter' : PublicParameter)
    (derive : KeygenDomain) (hash : HashDomain) (seed : MasterSeed) (payload : HashInput) :
    keygenHashInput parameter derive seed ≠ tweakableHashInput parameter' hash payload :=
  Completeness.fieldInput_ne_of_tag_ne_across parameter parameter'
    (derive_tag_ne_hash_tag derive hash) _ _

end SphincsFors.Security
