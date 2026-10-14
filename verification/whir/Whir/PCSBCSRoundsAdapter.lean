import Whir.PCSBCSRounds
import Whir.AnchoredPhysicalAnchor
import Whir.AnchoredSourceFreshCaller

/-! Operative regrouping of the actual PCS coin tape and native anchored opening
verifier. The original record is a fixed prior input. Neither its original anchor
sample nor commitment is a new verifier round here. Original commit-time IOP and
whole-system Flock/bus/GKR caller randomness are deliberately outside this module.
Canonical full histories and their byte cursor are preserved; this does not
identify them with the book's hash-chain compiler or invoke its theorem. -/
namespace Whir.PCSBCSRounds
open Concrete Protocol CausalGame CausalProbability WHIRHistory

abbrev BookTape (c : Config) := ∀ q : Coordinate c, Raw q
abbrev SourceTape (c : Config) := (E × (Fin 6 → E)) × Tape c

/-- Lossless regrouping of source chronological draws. First eight scalars are
one dependent verifier message; the other coordinates are untouched. -/
def tapeAdapter (c : Config) : SourceTape c ≃ BookTape c where
  toFun t q := match q with
    | .initial => (t.1,t.2.1)
    | .fold i j => get (.fold i j) t.2
    | .ood i j => get (.ood i j) t.2
    | .query i => get (.query i) t.2
    | .tail j => get (.tail j) t.2
  invFun f := ((f .initial).1, (coordinates c).symm (fun q => match q with
    | .initial => (f .initial).2
    | .fold i j => f (.fold i j)
    | .ood i j => f (.ood i j)
    | .query i => f (.query i)
    | .tail j => f (.tail j)))
  left_inv t := rfl
  right_inv f := by funext q; cases q <;> rfl

noncomputable instance (c : Config) : Fintype (BookTape c) := by
  unfold BookTape
  infer_instance

private def concatenate (a b : Nat) :
    ((Fin a → E) × (Fin b → E)) ≃ (Fin (a+b) → E) :=
  (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) E).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl E))

/-- Literal eight-coordinate alphabet, without padding or a stretched seed. -/
def initialEight {c : Config} : Raw (c := c) .initial ≃ (Fin 8 → E) :=
  (Equiv.prodCongr
    ((Equiv.prodCongr (Equiv.funUnique (Fin 1) E).symm (Equiv.refl (Fin 6 → E))).trans
      (concatenate 1 6))
    (Equiv.funUnique (Fin 1) E).symm).trans (concatenate 7 1)

/-- The complete joint uniform law is preserved, not merely its raw cardinality. -/
theorem tape_uniform (c : Config) (event : BookTape c → Prop) :
    SamplingProbability.probability (fun t : SourceTape c => event (tapeAdapter c t)) =
      SamplingProbability.probability event :=
  SamplingProbability.probability_equiv (tapeAdapter c) event

/-- The actual causal strategy is called only at completed grouped messages.
The ring prefix may affect every reply, but no future WHIR coin is disclosed. -/
def bookReplies (c : Config) (inputFor : (E × (Fin 6 → E)) → Public)
    (strategy : (E × (Fin 6 → E)) → Strategy) (t : BookTape c) : List Reply :=
  let source := (tapeAdapter c).symm t
  run (strategy source.1) (inputFor source.1) []
    (visibleBatches c source.2.1 (challenges c source.2))

theorem causal_replies_preserved (c : Config) (inputFor : (E × (Fin 6 → E)) → Public)
    (strategy : (E × (Fin 6 → E)) → Strategy) (t : SourceTape c) :
    bookReplies c inputFor strategy (tapeAdapter c t) =
      run (strategy t.1) (inputFor t.1) [] (visibleBatches c t.2.1 (challenges c t.2)) := by
  simp only [bookReplies, Equiv.symm_apply_apply]

/-- Native acceptance including tag/length failures. Replies here are the
actual source-shaped messages, retaining authenticated rows as side data. -/
def sourceOpening {m : Nat} (c : Config) (record : AnchoredHeaderCodec.Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (t : SourceTape c) (replies : Array Reply) : Except String Unit := do
  let proof ← CausalGame.opening c (challenges c t.2) replies
  AnchoredPhysicalAnchor.sourceVerify record family points t.1 t.2.1 c
    (challenges c t.2) proof

def bookOpening {m : Nat} (c : Config) (record : AnchoredHeaderCodec.Record)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (t : BookTape c) (replies : Array Reply) : Except String Unit :=
  sourceOpening c record family points ((tapeAdapter c).symm t) replies

/-- Equality of the entire Except result: accepting and rejecting branches are
both preserved. No algebraic validity, grinding success, or honest proof premise. -/
theorem same_acceptance_and_rejection {m : Nat} (c : Config)
    (record : AnchoredHeaderCodec.Record) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (t : SourceTape c) (replies : Array Reply) :
    bookOpening c record family points (tapeAdapter c t) replies =
      sourceOpening c record family points t replies := by
  simp only [bookOpening, Equiv.symm_apply_apply]

/-- A model/source precondition is literal equality of the prior record and
parsed/authenticated causal messages at the audited PCS entry, not a statement
that all Rust versions refine this model. The adapter then transports the native
result for arbitrary rejecting messages as well. -/
theorem source_model_transport {m : Nat} (c : Config)
    (saved received : AnchoredHeaderCodec.Record) (family : Fin m → RingPCSGame.FamilyClaim)
    (points : Array RingPCSGame.PointClaim) (t : SourceTape c)
    (sourceReplies modeledReplies : Array Reply)
    (recordFixed : received = saved) (parsed : sourceReplies = modeledReplies) :
    bookOpening c saved family points (tapeAdapter c t) modeledReplies =
      sourceOpening c received family points t sourceReplies := by
  subst received
  subst sourceReplies
  exact same_acceptance_and_rejection c saved family points t modeledReplies

/-- Byte-history adapter at a live caller continuation; source normalized entry
frames are retained instead of resetting to a freshly seeded PCS statement. -/
theorem byte_history_message_roundtrip (p : ParameterBounds.Profile)
    (entry : FiatShamirGame.FramedHistory) (messages : List Pending)
    (normal : WHIRHistoryKey.Normal messages) (block : Nat) :
    WHIRHistoryKey.parseSteps
      ((WHIRCallerPrefix.outputKeyFrom (WHIRHistoryKey.stackWidth (ParameterBounds.config p))
        entry messages block).history.frames.drop entry.frames.length) =
      some messages.dropLast.reverse :=
  WHIRCallerPrefix.parse_outputKeyFrom _ (WHIRHistoryKey.stackWidth_positive p)
    entry normal block

/-- Every serialized prover string, including a nonce, is recovered exactly.
This is a prover-message codec, not disclosure of the verifier coin tape to an
extractor (the book's extractor input contains IOP strings only). -/
theorem prover_message_roundtrip (message : Pending) :
    decodePending message.scalars.length (encodePending message) = some message :=
  pending_roundtrip message

/-- The original fresh-opening parser retains the actual prior original record;
verifier coins embedded in transformed claims do not become a new commit IOP. -/
theorem fresh_record_fixed (layout : WHIRCallerClaims.CallerLayout)
    (saved : AnchoredHeaderCodec.Record) (entry : FiatShamirGame.FramedHistory)
    (answers : FiatShamirGame.Coordinate → FiatShamirGame.Digest32)
    (claims : AnchoredSourceCaller.Claims)
    (parsed : AnchoredSourceFreshCaller.decode layout saved entry answers = some claims) :
    claims.record = saved ∧ claims.caller.root = saved.root :=
  AnchoredSourceFreshCaller.decode_retained layout saved entry answers claims parsed

/-- Fresh entry binds the entire original record before gamma/maps/lambda.
This actual nonempty prover frame resets the modeled output cursor; an
initial group may not silently inherit the caller's cached output tail. -/
theorem initial_record_binding_nonempty (saved : AnchoredHeaderCodec.Record) :
    scalarBytes (AnchoredHeaderCodec.openingScalars saved) ≠ [] := by
  intro empty
  have size := congrArg List.length empty
  rw [scalarBytes_length, AnchoredHeaderCodec.openingScalars_length,
    List.length_nil] at size
  omega

theorem initial_record_binding_cursor_zero (m : DuplexRefinement.Model)
    (saved : AnchoredHeaderCodec.Record) :
    (DuplexRefinement.modelAbsorb m
      (scalarBytes (AnchoredHeaderCodec.openingScalars saved))).consumed = 0 := by
  simp [DuplexRefinement.modelAbsorb, initial_record_binding_nonempty saved]

#print axioms tape_uniform
#print axioms same_acceptance_and_rejection
#print axioms byte_history_message_roundtrip
end Whir.PCSBCSRounds
