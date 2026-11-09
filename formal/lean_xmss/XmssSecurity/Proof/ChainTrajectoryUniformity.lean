module

public import XmssSecurity.Proof.ConcreteQueryBound
public import XmssSecurity.Proof.ChainKey

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

noncomputable local instance chainTrajectorySampleableDigest : SampleableType Digest :=
  SampleableType.ofFintype Digest

@[simp]
theorem Vector.back_push {n : Nat} (values : Vector α n) (value : α) :
    (values.push value).back = value := by
  symm
  exact Vector.back_eq_of_push_eq (Vector.push_pop_back (values.push value)).symm

def Concrete.chainTrajectory
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position : Nat) : (steps : Nat) → Digest →
      OracleComp HashSpec (Vector Digest (steps + 1))
  | 0, value => pure (Vector.ofFn fun _ => value)
  | steps + 1, value => do
      let values ← chainTrajectory parameter key chain position steps value
      if hvalid : position + steps < chainLength - 1 then
        let next ← Concrete.keyChainHash parameter key chain
          ⟨position + steps, hvalid⟩ values.back
        return values.push next
      else
        return values.push 0

@[simp]
theorem Concrete.chainTrajectory_zero
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position : Nat) (value : Digest) :
    Concrete.chainTrajectory parameter key chain position 0 value =
      pure (Vector.ofFn fun _ => value) := rfl

theorem Concrete.chainTrajectory_succ
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    Concrete.chainTrajectory parameter key chain position (steps + 1) value = (do
      let values ← Concrete.chainTrajectory parameter key chain position steps value
      if hvalid : position + steps < chainLength - 1 then
        let next ← Concrete.keyChainHash parameter key chain
          ⟨position + steps, hvalid⟩ values.back
        return values.push next
      else
        return values.push 0) := rfl

@[simp]
theorem Concrete.chainTrajectory_back
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : ChainKey) (chain : ChainIndex) (position steps : Nat)
    (value : Digest) :
    (evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.chainTrajectory parameter key chain position steps value)).back =
      Wots.walk (Concrete.CacheView.keyChainStep cache parameter key chain)
        position steps value := by
  induction steps with
  | zero =>
      rw [Concrete.chainTrajectory_zero, evalWithAnswerFn_pure]
      simp [Wots.walk, Vector.back]
  | succ steps ih =>
      rw [Concrete.chainTrajectory_succ]
      simp only [evalWithAnswerFn_bind, ih, Wots.walk]
      split <;> simp_all [Concrete.keyChainHash, Concrete.CacheView.keyChainStep,
        Concrete.CacheView.keyChainInput, Concrete.CacheView.tweakableHash]

theorem Concrete.chainTrajectory_getElem
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (key : ChainKey) (chain : ChainIndex) (position steps offset : Nat)
    (value : Digest) (hoffset : offset < steps + 1) :
    (evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.chainTrajectory parameter key chain position steps value))[offset] =
      Wots.walk (Concrete.CacheView.keyChainStep cache parameter key chain)
        position offset value := by
  induction steps generalizing offset with
  | zero =>
      have : offset = 0 := by omega
      subst offset
      rw [Concrete.chainTrajectory_zero, evalWithAnswerFn_pure]
      simp [Wots.walk]
  | succ steps ih =>
      rw [Concrete.chainTrajectory_succ]
      simp only [evalWithAnswerFn_bind]
      split <;> rename_i hvalid
      · simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
        by_cases hlower : offset < steps + 1
        · rw [Vector.getElem_push_lt]
          exact ih offset hlower
        · have hlast : offset = steps + 1 := by omega
          subst offset
          rw [Vector.getElem_push_eq, Concrete.chainTrajectory_back]
          simp [Wots.walk, hvalid, Concrete.keyChainHash,
            Concrete.CacheView.keyChainStep, Concrete.CacheView.keyChainInput,
            Concrete.CacheView.tweakableHash]
      · simp only [evalWithAnswerFn_pure]
        by_cases hlower : offset < steps + 1
        · rw [Vector.getElem_push_lt]
          exact ih offset hlower
        · have hlast : offset = steps + 1 := by omega
          subst offset
          rw [Vector.getElem_push_eq]
          simp [Wots.walk, Concrete.CacheView.keyChainStep, hvalid]

theorem Concrete.chainTrajectory_queryBound_zero_of_avoids
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain)
    (havoid : ∀ offset, offset < steps →
      ∀ hvalid : position + offset < chainLength - 1,
        key.chainDomain chain ⟨position + offset, hvalid⟩ ≠ targetDomain) :
    (Concrete.chainTrajectory parameter key chain position steps value).IsQueryBoundP
      (AtHashAddress parameter targetDomain) 0 := by
  induction steps with
  | zero => simp [Concrete.chainTrajectory]
  | succ steps ih =>
      rw [Concrete.chainTrajectory_succ]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih fun offset hoffset => havoid offset (by omega)) ?_
      intro values _
      split
      · exact OracleComp.isQueryBoundP_bind (m := 0)
          (Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
            (key.chainDomain chain ⟨position + steps, by assumption⟩)
            (Concrete.digestBytes values.back) (havoid steps (by omega) _))
          (fun next _ => OracleComp.isQueryBoundP_pure
            (p := AtHashAddress parameter targetDomain) (values.push next) 0)
      · exact OracleComp.isQueryBoundP_pure
          (p := AtHashAddress parameter targetDomain) (values.push 0) 0


end XmssSecurity
