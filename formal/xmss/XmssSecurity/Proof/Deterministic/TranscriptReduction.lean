import XmssSecurity.Proof.Deterministic.LoggedSigning
import XmssSecurity.Proof.Deterministic.GameExpansion
import XmssSecurity.Proof.Deterministic.TableSigner

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

noncomputable def memoAdversary (adversary : Adversary) : Adversary where
  main := fun publicKey => memoize (adversary.main publicKey) ∅

def transcriptWin (forgery : Forgery) (log : QueryLog SigningSpec) (verified : Bool) : Bool :=
  decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

theorem transcriptWin_mono (forgery : Forgery) (original forwarded : QueryLog SigningSpec)
    (h : forwarded.Sublist original) (verified : Bool) (hwin : transcriptWin forgery original verified = true) :
    transcriptWin forgery forwarded verified = true := by
  simp only [transcriptWin, Bool.and_eq_true, decide_eq_true_eq] at hwin ⊢
  refine ⟨⟨List.Nodup.sublist (h.map _) hwin.1.1, ?_⟩, hwin.2⟩
  rintro ⟨entry, hentry, heq⟩
  exact hwin.1.2 ⟨entry, h.subset hentry, heq⟩

noncomputable def finishGame (publicKey : PublicKey) (result : Forgery × QueryLog SigningSpec) :
    OracleComp OracleWorld Bool := do
  let verified ← liftM (Concrete.verify publicKey result.1.epoch result.1.message result.1.signature : OracleComp HashSpec Bool)
  return transcriptWin result.1 result.2 verified

noncomputable def sourceGame (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) Bool :=
  withRequestLog (adversary.main publicKey) >>= fun result => baseLift (finishGame publicKey result)

noncomputable def transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    OracleComp (OracleWorld + SigningSpec) (Bool × Bool) := do
  let result ← withRequestLog (memoize (withRequestLog (adversary.main publicKey)) ∅)
  let verified ← baseLift (liftM
    (Concrete.verify publicKey result.1.1.epoch result.1.1.message result.1.1.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool)
  return (transcriptWin result.1.1 result.1.2 verified, transcriptWin result.1.1 result.2 verified)

theorem runSigning_baseLift {α : Type} (sign : SignRequest → OracleComp HashSpec (Option Signature))
    (computation : OracleComp OracleWorld α) : runSigning sign (baseLift computation) = computation := by
  rw [runSigning, simulateQ_baseLift, simulateQ_ofLift_eq_self]

theorem runSigning_sourceGame (randomizers : RandomizerOutputs) (secretKey : XmssSecurity.SecretKey)
    (publicKey : PublicKey) (adversary : Adversary) :
    runSigning (fun (request : SignRequest) => tableSign randomizers secretKey request.epoch request.message) (sourceGame publicKey adversary) =
      gameRest (tableScheme randomizers) adversary publicKey secretKey := by
  simp only [sourceGame, runSigning, simulateQ_bind, simulateQ_baseLift, simulateQ_ofLift_eq_self]
  rw [show simulateQ (QueryImpl.ofLift OracleWorld (OracleComp OracleWorld) +
      fun (request : SignRequest) => liftM (tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Signature)))
      (withRequestLog (adversary.main publicKey)) =
        loggedRun (fun (request : SignRequest) => liftM (tableSign randomizers secretKey request.epoch request.message : OracleComp HashSpec (Option Signature)))
          (adversary.main publicKey) from runSigning_withRequestLog _ _]
  unfold loggedRun gameRest finishGame transcriptWin
  rfl

theorem fst_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.fst <$> transcriptReduction publicKey adversary = memoize (sourceGame publicKey adversary) ∅ := by
  unfold transcriptReduction sourceGame
  rw [memoize_baseLift_bind]
  conv_rhs => rw [← fst_withRequestLog (memoize (withRequestLog (adversary.main publicKey)) ∅)]
  simp only [map_bind, bind_map_left, map_pure, finishGame, baseLift, simulateQ_bind, simulateQ_pure]

theorem snd_transcriptReduction (publicKey : PublicKey) (adversary : Adversary) :
    Prod.snd <$> transcriptReduction publicKey adversary = sourceGame publicKey (memoAdversary adversary) := by
  unfold transcriptReduction sourceGame memoAdversary
  rw [← withRequestLog_memoize_forget (adversary.main publicKey) ∅]
  simp only [map_bind, bind_map_left, map_pure, finishGame, baseLift, simulateQ_bind, simulateQ_pure]

theorem transcriptReduction_win (publicKey : PublicKey) (adversary : Adversary)
    (result : Bool × Bool) (hresult : result ∈ support (transcriptReduction publicKey adversary)) :
    result.1 = true → result.2 = true := by
  simp only [transcriptReduction, mem_support_bind_iff, mem_support_pure_iff] at hresult
  obtain ⟨logs, hlogs, verified, _, rfl⟩ := hresult
  exact transcriptWin_mono _ _ _ (memoize_log_sublist _ ∅ logs hlogs) verified

end XmssSecurity.Seeded
