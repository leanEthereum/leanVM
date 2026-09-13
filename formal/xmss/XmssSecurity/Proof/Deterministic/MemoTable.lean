import XmssSecurity.Proof.Deterministic.MemoGame
import XmssSecurity.Proof.Deterministic.GameComparison

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem hashQueryBound_bind_replace {α β γ : Type} (first : OracleComp OracleWorld α)
    (left : α → OracleComp OracleWorld β) (right : α → OracleComp OracleWorld γ)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= left) cache q)
    (hnext : ∀ value cache q, HashQueryBound (left value) cache q → HashQueryBound (right value) cache q) :
    HashQueryBound (first >>= right) cache q := by
  rw [hashQueryBound_iff_run]
  intro result hresult
  simp only [countHashQueries_bind, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨headResult, hheadResult, tail, htail, rfl⟩ := hresult
  have h := hashQueryBound_bind first left cache q hbound headResult hheadResult
  have ht := hnext headResult.1.1 headResult.2 (q - headResult.1.2) h.2
  rw [hashQueryBound_iff_run] at ht
  have := ht tail htail
  change headResult.1.2 + tail.1.2 ≤ q
  have := h.1
  omega

theorem prob_tableGameAfterSecrets_le_memo (adversary : Adversary) (parameter : PublicParameter)
    (outputs : ChainSecrets) (randomizers : RandomizerOutputs) (cache : QueryCache HashSpec) :
    Pr[= true | (simulateQ romImpl (tableGameAfterSecrets adversary parameter outputs randomizers)).run' cache] ≤
      Pr[= true | (simulateQ romImpl (tableGameAfterSecrets (memoAdversary adversary) parameter outputs randomizers)).run' cache] := by
  unfold tableGameAfterSecrets
  rw [run'_lift_hash_bind, run'_lift_hash_bind]
  apply probOutput_bind_mono
  intro result _
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact prob_sourceGame_le_memo _ _ _ _

theorem tableBudget_memo (adversary : Adversary) (q : Nat) (hbound : HasTableBudget adversary q) :
    HasTableBudget (memoAdversary adversary) q := by
  intro parameter outputs randomizers
  have h := hbound parameter outputs randomizers
  unfold tableGameAfterSecrets at h ⊢
  apply hashQueryBound_bind_replace _ _ _ ∅ q h
  intro root cache q hrest
  rw [← runSigning_sourceGame] at hrest ⊢
  exact hashQueryBound_sourceGame_memo _ _ _ cache q hrest

theorem prob_independentTableGame_le_memo (adversary : Adversary) :
    Pr[= true | independentTableGame adversary] ≤ Pr[= true | independentTableGame (memoAdversary adversary)] := by
  unfold independentTableGame
  apply probOutput_bind_mono
  intro material _
  exact prob_tableGameAfterSecrets_le_memo _ _ _ _ ∅

end XmssSecurity.Seeded
