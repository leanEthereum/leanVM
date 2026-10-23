import Sphincs.Bytes
import Sphincs.Fresh

set_option backward.isDefEq.respectTransparency false

/-! Injectivity and separation of the candidate's exact byte inputs. These facts keep the
derivation and verification addresses distinct in later random-oracle reductions. -/

namespace Sphincs.Security

/-- The fixed-width prefix `P || A` determines its fields and parameter, with no restriction on
payload. -/
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

/-! ### Forest addresses -/

theorem subSlot_lt (c : Coord) (s : SuperIdx) (j : SubIdx) : subSlot c s j < 256 := by
  have := c.isLt; have := s.isLt; have := j.isLt
  simp only [subSlot, forestCoords, topHeight] at *
  omega

theorem childSlot_lt (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) : childSlot c s j a < 2048 := by
  have := subSlot_lt c s j; have := a.isLt
  simp only [childSlot, subHeight] at *
  omega

theorem chainSlot_lt (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) :
    chainSlot c s j a i < 12288 := by
  have := childSlot_lt c s j a; have := i.isLt
  simp only [chainSlot, childChains] at *
  omega

theorem subSlot_inj {c c' : Coord} {s s' : SuperIdx} {j j' : SubIdx}
    (h : subSlot c s j = subSlot c' s' j') : c = c' ∧ s = s' ∧ j = j' := by
  have := c.isLt; have := s.isLt; have := j.isLt; have := c'.isLt; have := s'.isLt; have := j'.isLt
  simp only [subSlot, forestCoords, topHeight] at *
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega

theorem childSlot_inj {c c' : Coord} {s s' : SuperIdx} {j j' : SubIdx} {a a' : ChildIdx}
    (h : childSlot c s j a = childSlot c' s' j' a') : subSlot c s j = subSlot c' s' j' ∧ a = a' := by
  have := a.isLt; have := a'.isLt
  have := subSlot_lt c s j; have := subSlot_lt c' s' j'
  simp only [childSlot, subHeight] at *
  refine ⟨?_, Fin.ext ?_⟩ <;> omega

theorem chainSlot_inj {c c' : Coord} {s s' : SuperIdx} {j j' : SubIdx} {a a' : ChildIdx} {i i' : FChain}
    (h : chainSlot c s j a i = chainSlot c' s' j' a' i') : childSlot c s j a = childSlot c' s' j' a' ∧ i = i' := by
  have := i.isLt; have := i'.isLt
  have := childSlot_lt c s j a; have := childSlot_lt c' s' j' a'
  simp only [chainSlot, childChains] at *
  refine ⟨?_, Fin.ext ?_⟩ <;> omega

/-- A chain slot determines the coordinate, super-child, sub-tree, child and chain. -/
theorem chainSlot_injective {c c' : Coord} {s s' : SuperIdx} {j j' : SubIdx} {a a' : ChildIdx}
    {i i' : FChain} (h : chainSlot c s j a i = chainSlot c' s' j' a' i') :
    c = c' ∧ s = s' ∧ j = j' ∧ a = a' ∧ i = i' := by
  obtain ⟨hchild, hi⟩ := chainSlot_inj h
  obtain ⟨hsub, ha⟩ := childSlot_inj hchild
  obtain ⟨hc, hs, hj⟩ := subSlot_inj hsub
  exact ⟨hc, hs, hj, ha, hi⟩

theorem pairSlot_lt (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (pair : FPair) :
    pairSlot c s j a pair < 12288 := by
  have := childSlot_lt c s j a; have := pair.isLt
  simp only [pairSlot] at *
  omega

/-- A pair slot determines the coordinate, super-child, sub-tree, child and pair of chains. -/
theorem pairSlot_injective {c c' : Coord} {s s' : SuperIdx} {j j' : SubIdx} {a a' : ChildIdx}
    {pair pair' : FPair} (h : pairSlot c s j a pair = pairSlot c' s' j' a' pair') :
    c = c' ∧ s = s' ∧ j = j' ∧ a = a' ∧ pair = pair' := by
  have hsplit : childSlot c s j a = childSlot c' s' j' a' ∧ pair = pair' := by
    have := childSlot_lt c s j a; have := childSlot_lt c' s' j' a'
    simp only [pairSlot] at h
    refine ⟨?_, Fin.ext ?_⟩ <;> omega
  obtain ⟨hsub, ha⟩ := childSlot_inj hsplit.1
  obtain ⟨hc, hs, hj⟩ := subSlot_inj hsub
  exact ⟨hc, hs, hj, ha, hsplit.2⟩

theorem deriveFields_injective : Function.Injective keygenDomainFields := by
  intro left right h
  cases left <;> cases right <;>
    simp only [keygenDomainFields, tweakFields, TweakFields.mk.injEq] at h
  all_goals try { simp at h; done }
  · rfl
  · rename_i lay tree leaf chain lay' tree' leaf' chain'
    obtain ⟨_, _, hchain, hleaf⟩ := h
    have hl : lay = lay' := Subsingleton.elim (α := Fin 1) _ _
    have ht : tree = tree' := Subsingleton.elim (α := Fin 1) _ _
    have hc : chain = chain' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (chain.isLt.trans_le (by decide))
        (chain'.isLt.trans_le (by decide)) hchain
    have he : leaf = leaf' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (leaf.isLt.trans_le (by decide))
        (leaf'.isLt.trans_le (by decide)) hleaf
    cases hl; cases ht; cases he; cases hc; rfl
  · rename_i index c s j a i index' c' s' j' a' i'
    obtain ⟨_, _, hpos, hindex⟩ := h
    have hidx : index = index' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (index.isLt.trans_le (by decide))
        (index'.isLt.trans_le (by decide)) hindex
    have hp := ofNat_inj_of_lt ((pairSlot_lt c s j a i).trans_le (by decide))
      ((pairSlot_lt c' s' j' a' i').trans_le (by decide)) hpos
    obtain ⟨hc, hs, hj, ha, hi⟩ := pairSlot_injective hp
    subst hidx hc hs hj ha hi; rfl
  · rename_i level level'
    obtain ⟨_, _, hlevel, _⟩ := h
    have hl : level = level' := by
      apply Fin.ext
      exact ofNat_inj_of_lt (level.isLt.trans_le (by decide))
        (level'.isLt.trans_le (by decide)) hlevel
    cases hl; rfl

/-- No two seed-derivation queries have the same input unless their full arguments agree. -/
theorem keygenInput_injective {parameter parameter' : PublicParameter}
    {domain domain' : KeygenDomain} {seed seed' : MasterSeed}
    (h : keygenHashInput parameter domain seed = keygenHashInput parameter' domain' seed') :
    parameter = parameter' ∧ domain = domain' ∧ seed = seed' := by
  obtain ⟨hfields, hp, hs⟩ := fieldInput_injective h
  exact ⟨hp, deriveFields_injective hfields, bytesLE_injective hs⟩

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

end Sphincs.Security
