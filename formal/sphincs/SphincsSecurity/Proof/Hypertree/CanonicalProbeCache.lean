import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalProbeRouting
import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete.CanonicalProbeRouting

open _root_.OracleComp HiddenLabelObservation RetainedObservation
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev ExternalCache := HashInput → Option HashOutput

def CacheClean (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (cache : ExternalCache) : Prop :=
  ∀ input answer, cache input = some answer → ¬Bad parameter words disclosed actual input answer

theorem hidden_mono (words : OtsReferenceWords) (before after : Index → FtsTree → FtsLeaf → Prop)
    (hdisclosed : ∀ index tree leaf, before index tree leaf → after index tree leaf) (coordinate : CanonicalCoordinate) :
    CanonicalCoordinate.Hidden words after coordinate → CanonicalCoordinate.Hidden words before coordinate := by
  cases coordinate with
  | otsStart => exact id
  | graph position => cases position <;> exact id
  | ftsStart index tree leaf =>
      intro hhidden hbefore
      exact hhidden (hdisclosed index tree leaf hbefore)

theorem bad_mono (parameter : PublicParameter) (words : OtsReferenceWords)
    (before after : Index → FtsTree → FtsLeaf → Prop)
    (hdisclosed : ∀ index tree leaf, before index tree leaf → after index tree leaf)
    (actual : Labels) (input : HashInput) (answer : HashOutput) :
    Bad parameter words after actual input answer → Bad parameter words before actual input answer := by
  rintro ⟨position, hat, hbad⟩
  refine ⟨position, hat, ?_⟩
  rcases hbad with ⟨⟨coordinate, hslot, hhidden⟩, hinput⟩ | houtput
  · exact Or.inl ⟨⟨coordinate, hslot, hidden_mono words before after hdisclosed coordinate hhidden⟩, hinput⟩
  · exact Or.inr houtput

theorem cacheClean_disclose (parameter : PublicParameter) (words : OtsReferenceWords)
    (before after : Index → FtsTree → FtsLeaf → Prop)
    (hdisclosed : ∀ index tree leaf, before index tree leaf → after index tree leaf)
    (actual : Labels) (cache : ExternalCache) (hclean : CacheClean parameter words before actual cache) :
    CacheClean parameter words after actual cache := by
  intro input answer hcache hbad
  exact hclean input answer hcache (bad_mono parameter words before after hdisclosed actual input answer hbad)

theorem cacheClean_store (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels) (cache : ExternalCache)
    (hclean : CacheClean parameter words disclosed actual cache) (input : HashInput) (answer : HashOutput)
    (hsafe : ¬Bad parameter words disclosed actual input answer) :
    CacheClean parameter words disclosed actual (Function.update cache input (some answer)) := by
  intro other output hcache
  by_cases heq : other = input
  · subst other
    rw [Function.update_self] at hcache
    have heq := Option.some.inj hcache
    exact heq ▸ hsafe
  · rw [Function.update_of_ne heq] at hcache
    exact hclean other output hcache

structure ExternalMemory where
  cache : ExternalCache
  hashCalls : Nat
  probes : Nat

noncomputable def charge (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (input : HashInput)
    (memory : ExternalMemory) : ExternalMemory :=
  { memory with
    hashCalls := memory.hashCalls + 1
    probes := memory.probes + match memory.cache input with
      | some _ => 0
      | none => match route parameter words disclosed known input with
        | .probe _ => 1
        | _ => 0 }

noncomputable def storeReply (memory : ExternalMemory) (input : HashInput) (answer : HashOutput) : ExternalMemory :=
  { memory with cache := Function.update memory.cache input (some answer) }

theorem charge_probes_le (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (input : HashInput) (memory : ExternalMemory) :
    (charge parameter words disclosed known input memory).probes ≤ memory.probes + 1 := by
  unfold charge
  cases hcache : memory.cache input with
  | some answer => exact Nat.le_add_right _ _
  | none => cases route parameter words disclosed known input <;> simp

end SphincsSecurity.Concrete.CanonicalProbeRouting
