import XmssSecurity.Proof.Bridge.Signer
import XmssSecurity.Proof.Deterministic.TranscriptReduction

/-!
# The real game as the model's

The statement's adversary is a model adversary whose signing requests and answers are translated.
Under the prepared cache, the real game after key generation erases to the model's game with the
table signer: the transcripts correspond entry by entry, and the forgery wins in one exactly when its
translation wins in the other.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-! ## Logged simulations with translated logs -/

theorem Erases.simulateQ_writer_map {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    {α L L' : Type} (known : QueryCache target)
    (left : QueryImpl source (WriterT (List L) (OracleComp target)))
    (right : QueryImpl source (WriterT (List L') (OracleComp target))) (g : L' → L)
    (h : ∀ input, Erases known (left input).run
      ((fun p => (p.1, p.2.map g)) <$> (right input).run))
    (computation : OracleComp source α) :
    Erases known (simulateQ left computation).run
      ((fun p => (p.1, p.2.map g)) <$> (simulateQ right computation).run) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', map_pure]
      exact .pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind', map_bind]
      show Erases known ((left input).run >>= fun x =>
          Prod.map id (x.2 ++ ·) <$> (simulateQ left (next x.1)).run)
        ((right input).run >>= fun a => (fun p => (p.1, p.2.map g)) <$>
          (Prod.map id (a.2 ++ ·) <$> (simulateQ right (next a.1)).run))
      have hright : ((right input).run >>= fun a => (fun p => (p.1, p.2.map g)) <$>
            (Prod.map id (a.2 ++ ·) <$> (simulateQ right (next a.1)).run)) =
          ((fun p => (p.1, p.2.map g)) <$> (right input).run) >>= fun a =>
            Prod.map id (a.2 ++ ·) <$> ((fun p => (p.1, p.2.map g)) <$>
              (simulateQ right (next a.1)).run) := by
        rw [bind_map_left]
        apply bind_congr
        intro a
        simp only [Functor.map_map]
        congr 1
        funext q
        simp [List.map_append]
      rw [hright]
      exact (h input).bind _ _ fun a => (ih a.1).map _


theorem Erases.of_eq {ι : Type} {spec : OracleSpec ι} {α : Type} {known : QueryCache spec}
    {left right : OracleComp spec α} (h : left = right) : Erases known left right :=
  h ▸ .refl known left

theorem liftM_hash_map {α β : Type} (f : α → β) (c : OracleComp HashSpec α) :
    (liftM (f <$> c) : OracleComp OracleWorld β) = f <$> (liftM c : OracleComp OracleWorld α) := by
  rw [map_eq_bind_pure_comp, liftM_bind, map_eq_bind_pure_comp]
  simp only [Function.comp_def, liftM_pure]

/-! ## The adversary -/

def toModelReq (request : LeanXmss.SignRequest) : SignRequest := ⟨request.leafIndex, request.message⟩

def toRealReq (request : SignRequest) : LeanXmss.SignRequest := ⟨request.leafIndex, request.message⟩

/-- A real forgery as the model's: its signature's leaf index moves to the claim. -/
def toModelForgery (forgery : LeanXmss.Forgery) : Forgery :=
  ⟨forgery.signature.leafIndex, forgery.message, toModelSig forgery.signature⟩

/-- Answer the statement adversary's queries with the model's oracles, translating each signature. -/
def adversaryImpl :
    QueryImpl (LeanXmss.OracleWorld + LeanXmss.SigningSpec) (OracleComp (OracleWorld + SigningSpec))
  | .inl input => liftM ((OracleWorld + SigningSpec).query (.inl input))
  | .inr request => Option.map (toRealSig request.leafIndex) <$>
      liftM ((OracleWorld + SigningSpec).query (.inr (toModelReq request)))

/-- The statement's adversary as a model adversary. -/
noncomputable def toModelAdversary (adversary : LeanXmss.Security.Adversary) : Adversary where
  main publicKey := toModelForgery <$> simulateQ adversaryImpl (adversary.main (toRealPk publicKey))

/-- A model transcript entry as the real one. -/
def toRealEntry (entry : (_ : SignRequest) × Option Signature) :
    (_ : LeanXmss.SignRequest) × Option LeanXmss.Signature :=
  ⟨toRealReq entry.1, entry.2.map (toRealSig entry.1.leafIndex)⟩

theorem valid_map (log : QueryLog SigningSpec) :
    LeanXmss.SigningTranscript.Valid (log.map toRealEntry) ↔ SigningTranscript.Valid log := by
  simp only [LeanXmss.SigningTranscript.Valid, SigningTranscript.Valid, List.map_map]
  rfl

theorem contains_map (log : QueryLog SigningSpec) (forgery : LeanXmss.Forgery) :
    LeanXmss.SigningTranscript.Contains (log.map toRealEntry) forgery ↔
      SigningTranscript.Contains log (toModelForgery forgery) := by
  rcases forgery with ⟨fmessage, fsignature⟩
  simp only [LeanXmss.SigningTranscript.Contains, SigningTranscript.Contains, List.mem_map]
  constructor
  · rintro ⟨_, ⟨entry, hentry, rfl⟩, hmessage, hsignature⟩
    obtain ⟨request, answer⟩ := entry
    cases answer with
    | none => simp [toRealEntry] at hsignature
    | some signature =>
        simp only [toRealEntry, Option.map_some, Option.some.injEq] at hsignature
        refine ⟨⟨request, some signature⟩, hentry, ?_, ?_⟩
        · subst hsignature
          simp only [toModelForgery, Forgery.request, toRealSig_leafIndex]
          rw [← hmessage]
          rfl
        · subst hsignature
          simp [toModelForgery]
  · rintro ⟨entry, hentry, hrequest, hsignature⟩
    refine ⟨toRealEntry entry, ⟨entry, hentry, rfl⟩, ?_, ?_⟩
    · simp only [toRealEntry, toRealReq]
      rw [hrequest]
      rfl
    · simp only [toRealEntry, hsignature, Option.map_some]
      rw [hrequest]
      simp [Forgery.request, toModelForgery]

/-! ## The real game -/

/-- The real game after key generation. -/
noncomputable def realRest (adversary : LeanXmss.Security.Adversary) (publicKey : LeanXmss.PublicKey)
    (secretKey : LeanXmss.Seeded.SecretKey) : OracleComp LeanXmss.OracleWorld Bool := do
  let ((forgery, log) : LeanXmss.Forgery × QueryLog LeanXmss.SigningSpec) ←
    (simulateQ (QueryImpl.ofLift LeanXmss.OracleWorld
      (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp LeanXmss.OracleWorld)) +
        LeanXmss.Security.signingOracle secretKey) (adversary.main publicKey)).run
  let verified ← liftM (LeanXmss.Concrete.verify publicKey forgery.message forgery.signature :
    OracleComp LeanXmss.HashSpec Bool)
  return decide (LeanXmss.SigningTranscript.Valid log ∧ ¬LeanXmss.SigningTranscript.Contains log forgery) &&
    verified

theorem gameCore_eq (adversary : LeanXmss.Security.Adversary) :
    LeanXmss.Security.gameCore adversary = (do
      let seed ← liftM LeanXmss.sampleMasterSeed
      let keys ← liftM (LeanXmss.Seeded.keygenFromSeed seed)
      realRest adversary keys.1 keys.2) := rfl

namespace Prepared

variable {seed : MasterSeed} {d : Derivations}
  {result : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryLog HashSpec}
  {cache : QueryCache HashSpec}

theorem erases_oracles (h : Prepared seed d result cache) (input : (LeanXmss.OracleWorld + LeanXmss.SigningSpec).Domain) :
    Erases (worldKnown cache)
      ((QueryImpl.ofLift LeanXmss.OracleWorld
        (WriterT (QueryLog LeanXmss.SigningSpec) (OracleComp LeanXmss.OracleWorld)) +
          LeanXmss.Security.signingOracle ⟨seed, d.parameter, result.1.1⟩) input).run
      ((fun p => (p.1, p.2.map toRealEntry)) <$>
        (((forwardOracles + signingOracle (tableScheme d.rnd) (modelSecretKey d result)) ∘ₛ adversaryImpl)
          input).run) := by
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl, QueryImpl.apply_compose, adversaryImpl, simulateQ_spec_query,
        forwardOracles, QueryImpl.ofLift_apply]
      show Erases _ ((fun a => (a, ([] : QueryLog LeanXmss.SigningSpec))) <$>
          (liftM (OracleWorld.query input) : OracleComp OracleWorld _))
        ((fun p => (p.1, p.2.map toRealEntry)) <$> ((fun a => (a, ([] : QueryLog SigningSpec))) <$>
          (liftM (OracleWorld.query input) : OracleComp OracleWorld _)))
      rw [Functor.map_map]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, QueryImpl.apply_compose, adversaryImpl, simulateQ_map,
        simulateQ_spec_query, WriterT.run_map', LeanXmss.Security.signingOracle, signingOracle,
        QueryImpl.run_withLogging_apply, tableScheme]
      have key := (h.erases_sign request.leafIndex request.message).lift_hash.bind
        (fun u => (pure (u, [(⟨request, u⟩ : (r : LeanXmss.SignRequest) × Option LeanXmss.Signature)]) :
          OracleComp OracleWorld _))
        (fun u => (pure (u, [(⟨request, u⟩ : (r : LeanXmss.SignRequest) × Option LeanXmss.Signature)]) :
          OracleComp OracleWorld _)) fun u => .pure _
      convert key using 1 <;> try rfl
      simp only [liftM_hash_map, map_bind, bind_map_left, map_pure, Prod.map_apply, id_eq, List.map_cons,
        List.map_nil]
      rfl



theorem erases_rest (h : Prepared seed d result cache) (adversary : LeanXmss.Security.Adversary) :
    Erases (worldKnown cache)
      (realRest adversary ⟨result.1.1, d.parameter⟩ ⟨seed, d.parameter, result.1.1⟩)
      (Seeded.gameRest (tableScheme d.rnd) (toModelAdversary adversary) (modelPublicKey d result)
        (modelSecretKey d result)) := by
  unfold realRest Seeded.gameRest toModelAdversary
  simp only [simulateQ_map, WriterT.run_map', ← QueryImpl.simulateQ_compose]
  have hsim := Erases.simulateQ_writer_map (worldKnown cache) _ _ toRealEntry h.erases_oracles
    (adversary.main (toRealPk (modelPublicKey d result)))
  refine Erases.trans (hsim.bind _ _ fun _ => Erases.refl _ _) (Erases.of_eq ?_)
  rw [bind_map_left, bind_map_left]
  apply bind_congr
  intro p
  simp only [tableScheme, Concrete.scheme, valid_map, contains_map]
  rw [verify_real]
  rfl

end Prepared

end XmssSecurity.Bridge
