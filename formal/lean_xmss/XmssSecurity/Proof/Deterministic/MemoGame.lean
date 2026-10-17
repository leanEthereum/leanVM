import XmssSecurity.Proof.Deterministic.TranscriptReduction

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

noncomputable def evaluateSource {α : Type} (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) : ProbComp α :=
  (simulateQ romImpl (runSigning sign computation)).run' cache

theorem evaluateSource_map {α β : Type} (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) (f : α → β) :
    evaluateSource sign (f <$> computation) cache = f <$> evaluateSource sign computation cache := by
  simp only [evaluateSource, runSigning, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

theorem evaluateSource_support {α : Type} (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    support (evaluateSource sign computation cache) ⊆ support computation := by
  unfold evaluateSource runSigning
  rw [← QueryImpl.simulateQ_compose]
  exact support_simulateQ_run'_subset _ _ _

theorem prob_sourceGame_le_memo (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) :
    Pr[= true | evaluateSource sign (sourceGame publicKey adversary) cache] ≤
      Pr[= true | evaluateSource sign (sourceGame publicKey (memoAdversary adversary)) cache] := by
  unfold evaluateSource
  rw [probOutput_congr rfl (evalDist_runSigning_memoize sign (sourceGame publicKey adversary) cache)]
  change Pr[= true | evaluateSource sign (memoize (sourceGame publicKey adversary) ∅) cache] ≤
    Pr[= true | evaluateSource sign (sourceGame publicKey (memoAdversary adversary)) cache]
  rw [← fst_transcriptReduction, ← snd_transcriptReduction, evaluateSource_map, evaluateSource_map]
  simp only [← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro result hresult hwin
  exact transcriptReduction_win publicKey adversary result (evaluateSource_support sign _ cache hresult) hwin

theorem hashQueryBound_sourceGame_memo (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (runSigning sign (sourceGame publicKey adversary)) cache q) :
    HashQueryBound (runSigning sign (sourceGame publicKey (memoAdversary adversary))) cache q := by
  have h := hashQueryBound_runSigning_memoize sign (sourceGame publicKey adversary) cache q hbound
  rw [← fst_transcriptReduction, runSigning, simulateQ_map, hashQueryBound_map_iff] at h
  rw [← snd_transcriptReduction, runSigning, simulateQ_map, hashQueryBound_map_iff]
  exact h

end XmssSecurity.Seeded
