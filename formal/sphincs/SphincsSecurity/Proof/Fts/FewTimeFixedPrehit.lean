import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeRace
/-!
# Reusing one fixed cached message entry

Once an origin configuration fixes a direct source, the later signer has to select that source's
one exact message-digest input. Restricting the reference cache to this input turns the cached-entry
factor in the digest race into one.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

def onlyInputCache (cache : QueryCache HashSpec) (target : HashInput) :
    QueryCache HashSpec :=
  fun input => if input = target then cache input else none

theorem onlyInputCache_le (cache : QueryCache HashSpec) (target : HashInput) :
    onlyInputCache cache target ≤ cache := by
  intro input output hcached
  by_cases hinput : input = target
  · simpa [onlyInputCache, hinput] using hcached
  · simp [onlyInputCache, hinput] at hcached

theorem cachedMessageEntryCountWhere_onlyInput_le_one
    (cache : QueryCache HashSpec) (target : HashInput)
    (parameter : PublicParameter) (root : Digest) (message : Message)
    (P : Concrete.FewTimeView → Prop) :
    cachedMessageEntryCountWhere (onlyInputCache cache target) parameter root message P ≤ 1 := by
  have hsubsingleton :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).Subsingleton := by
    rintro ⟨leftInput, leftOutput⟩ hleft ⟨rightInput, rightOutput⟩ hright
    have hleftInput : leftInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hleft
    have hrightInput : rightInput = target := by
      by_contra hne
      simp [cachedMessageInputSetWhere, cachedMessageInputSet, onlyInputCache, hne]
        at hright
    subst leftInput
    subst rightInput
    have houtputs : leftOutput = rightOutput := by
      apply Option.some.inj
      exact hleft.1.1.symm.trans hright.1.1
    subst rightOutput
    rfl
  have hencard :
      (cachedMessageInputSetWhere (onlyInputCache cache target) parameter root message P).encard ≤ 1 :=
    Set.encard_le_one_iff_subsingleton.2 hsubsingleton
  simpa only [cachedMessageEntryCountWhere, ENat.toENNReal_one] using
    ENat.toENNReal_mono hencard

end SphincsSecurity
