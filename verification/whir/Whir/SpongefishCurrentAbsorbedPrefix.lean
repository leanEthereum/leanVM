import Whir.SpongefishCurrentInitializedMode
import Whir.SpongefishCurrentRoundSeparation

/-! Literal full-prefix transport for the current source construction domain.
The source key contains the observed session domain, zero statement seed,
EVERY completed absorb body and its consumed-count tag, and the output block.
It does not contain earlier verifier coin values. This is the ancestry shape
of the basic full-prefix BCS variant, not its hash-chain variant.

Recovering this prefix is not yet an adapter for the book's public instance,
IOP messages, source acceptance or state-restoration extractor. In particular,
caller points derived from earlier output coordinates still need the actual
public-output getter and original-statement join. -/
namespace Whir.SpongefishCurrentAbsorbedPrefix
open Concrete FiatShamirGame DuplexRefinement SpongefishPCSRoundFrames
set_option autoImplicit false

structure Prefix where
  session : Digest32
  frames : List ByteFrame
  deriving DecidableEq

def Prefix.history (p : Prefix) : FramedHistory :=
  ⟨p.session,zeroDigest,p.frames.map ByteFrame.historicalCore⟩

def Prefix.bytes (p : Prefix) : List Byte :=
  p.frames.flatMap fun frame => match frame with | .absorb _ bytes => bytes

def ofPending (m : Pending) : Prefix := ⟨(close m).domain,(close m).frames⟩

def frames : List Frame → Option (List ByteFrame)
  | [] => some []
  | .absorb previous bytes :: rest =>
      (frames rest).map (ByteFrame.absorb previous bytes :: ·)
  | .nonce _ _ _ :: _ => none

def parse (history : FramedHistory) : Option Prefix :=
  if history.statement = zeroDigest then
    (frames history.frames).map (fun fs => ⟨history.domain,fs⟩)
  else none

/-- Full bounded raw encoding is checked before source ancestry is exposed.
Historical nonce, commitment and powBase coordinates are not current source
rounds and do not become a forged current prefix. -/
def rawPrefix {Q : Nat} (parameter : Digest32) (raw : DuplexModeGame.RawKey Q) :
    Option (Prefix × Nat) := do
  let q ← WHIRHeaderRoots.decodeRaw parameter raw
  match q.terminal with
  | .output block => (parse q.history).map (fun p => (p,block))
  | _ => none

@[simp] theorem frames_encoded (fs : List ByteFrame) :
    frames (fs.map ByteFrame.historicalCore) = some fs := by
  induction fs with
  | nil => rfl
  | cons frame fs ih => cases frame; simp [frames,ByteFrame.historicalCore,ih]

@[simp] theorem frames_recovered (source : List Frame) (decoded : List ByteFrame)
    (ok : frames source = some decoded) :
    decoded.map ByteFrame.historicalCore = source := by
  induction source generalizing decoded with
  | nil => simp only [frames,Option.some.injEq] at ok; subst decoded; rfl
  | cons frame rest ih =>
    cases frame with
    | nonce previous difficulty nonce => simp [frames] at ok
    | absorb previous bytes =>
      simp only [frames,Option.map_eq_some_iff] at ok
      obtain ⟨tail,parsed,equal⟩ := ok
      subst decoded
      simpa only [List.map_cons,ByteFrame.historicalCore] using
        congrArg (Frame.absorb previous bytes :: ·) (ih tail parsed)

@[simp] theorem parse_history (p : Prefix) : parse p.history = some p := by
  simp [parse,Prefix.history]

theorem parse_sound (history : FramedHistory) (p : Prefix) (ok : parse history = some p) :
    p.history = history := by
  unfold parse at ok
  split at ok
  · rename_i statement
    obtain ⟨fs,decoded,equal⟩ := Option.map_eq_some_iff.mp ok
    subst p
    cases history
    simp only [Prefix.history]
    simp only [FramedHistory.mk.injEq] at statement ⊢
    exact ⟨trivial,statement.symm,frames_recovered _ _ decoded⟩
  · cases ok

@[simp] theorem pending_history (m : Pending) :
    (ofPending m).history = (close m).core.history := rfl

theorem complete_prover_bytes (m : Pending) :
    (ofPending m).bytes = retainedBytes m := by
  have empty : (close m).run = [] := by
    by_cases run : m.run = [] <;> simp [close,run]
  simpa only [Prefix.bytes,ofPending,retainedBytes,empty,List.append_nil] using close_retains m

/-- No flattening or truncated-root equality is used for key equality. -/
theorem raw_roundtrip {Q : Nat} (parameter : Digest32) (m : Pending) (block : Nat)
    (valid : DuplexEncoding.Admissible (SpongefishCurrentModeQueries.coordinate m block))
    (bound : DuplexFraming.pathCost (SpongefishCurrentModeQueries.coordinate m block) ≤ Q) :
    rawPrefix parameter (DuplexModeGame.constructionKey Q parameter
      (SpongefishCurrentModeQueries.coordinate m block) bound) = some (ofPending m,block) := by
  rw [rawPrefix,WHIRHeaderRoots.decodeRaw_construction parameter _ valid bound]
  change (parse (ofPending m).history).map (fun p => (p,block)) = _
  rw [parse_history]
  rfl

theorem rawPrefix_sound {Q : Nat} (parameter : Digest32) (raw : DuplexModeGame.RawKey Q)
    (p : Prefix) (block : Nat) (ok : rawPrefix parameter raw = some (p,block)) :
    ∃ bound : DuplexFraming.pathCost (⟨p.history,.output block⟩ : Coordinate) ≤ Q,
      DuplexEncoding.Admissible ⟨p.history,.output block⟩ ∧
        DuplexModeGame.constructionKey Q parameter ⟨p.history,.output block⟩ bound = raw := by
  unfold rawPrefix at ok
  obtain ⟨q,decoded,rest⟩ := Option.bind_eq_some_iff.mp ok
  cases q with
  | mk history terminal =>
    cases terminal with
    | commitment consumed => simp at rest
    | powBase consumed difficulty => simp at rest
    | output outputBlock =>
      obtain ⟨prefixValue,parsed,equal⟩ := Option.map_eq_some_iff.mp rest
      obtain ⟨samePrefix,sameBlock⟩ := Prod.mk.inj equal
      subst prefixValue
      subst outputBlock
      have sameHistory := parse_sound history p parsed
      subst history
      exact WHIRHeaderRoots.decodeRaw_sound parameter raw ⟨p.history,.output block⟩ decoded

theorem raw_source_prefix_injective {Q : Nat} (parameter : Digest32)
    (m₁ m₂ : Pending) (block₁ block₂ : Nat)
    (valid₁ : DuplexEncoding.Admissible (SpongefishCurrentModeQueries.coordinate m₁ block₁))
    (valid₂ : DuplexEncoding.Admissible (SpongefishCurrentModeQueries.coordinate m₂ block₂))
    (bound₁ : DuplexFraming.pathCost (SpongefishCurrentModeQueries.coordinate m₁ block₁) ≤ Q)
    (bound₂ : DuplexFraming.pathCost (SpongefishCurrentModeQueries.coordinate m₂ block₂) ≤ Q)
    (same : DuplexModeGame.constructionKey Q parameter
      (SpongefishCurrentModeQueries.coordinate m₁ block₁) bound₁ =
        DuplexModeGame.constructionKey Q parameter
          (SpongefishCurrentModeQueries.coordinate m₂ block₂) bound₂) :
    ofPending m₁ = ofPending m₂ ∧ block₁ = block₂ := by
  have decoded := congrArg (rawPrefix parameter) same
  rw [raw_roundtrip parameter m₁ block₁ valid₁ bound₁,
    raw_roundtrip parameter m₂ block₂ valid₂ bound₂] at decoded
  exact Prod.mk.inj (Option.some.inj decoded)

#print axioms parse_sound
#print axioms complete_prover_bytes
#print axioms raw_roundtrip
#print axioms raw_source_prefix_injective
#print axioms rawPrefix_sound
end Whir.SpongefishCurrentAbsorbedPrefix
