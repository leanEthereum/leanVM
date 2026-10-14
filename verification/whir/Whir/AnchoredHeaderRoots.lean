import Whir.AnchoredHeaderCodec
import Whir.WHIRHeaderRoots

/-! Original-anchor keys have an arbitrary prior history. Their last completed absorb run ends with the five commitment-header scalars. Looking only at the first absorb frame would misparse real fresh-session commitments. Exact raw reconstruction remains the existing bounded DMV decoder. -/
namespace Whir.AnchoredHeaderRoots
open Concrete FiatShamirGame DuplexModeGame AnchoredHeaderCodec

structure Public where
  iv : Digest32
  domain : Digest32
  shapes : Digest32 → Option Shape

structure Header where
  statement : Digest32
  shape : Shape
  root : Digest32
  deriving DecidableEq

/-- Shape selection and native shape validation occur before scalar decoding. Root padding is checked by scalarsToHash, not discarded. -/
def fromHistory (registry : Public) (history : FramedHistory) : Option Header :=
  if history.domain = registry.domain then
    match registry.shapes history.statement with
    | none => none
    | some shape =>
      if shape.Valid then
        match history.frames.getLast? with
        | some (.absorb _ bytes) =>
          if 120 ≤ bytes.length then
            (WHIRHistory.parseExact 5 (bytes.drop (bytes.length-120))).bind fun scalars =>
              (parseHeader shape scalars).map (fun root => ⟨history.statement,shape,root⟩)
          else none
        | _ => none
      else none
  else none

def rawHeader (registry : Public) {Q : Nat} (raw : RawKey Q) : Option Header :=
  (WHIRHeaderRoots.decodeRaw registry.iv raw).bind fun q =>
    match q.terminal with
    | .output _ => fromHistory registry q.history
    | _ => none

theorem rawHeader_construction (registry : Public) {Q : Nat} (history : FramedHistory) (block : Nat)
    (valid : DuplexEncoding.Admissible (⟨history,.output block⟩ : Coordinate))
    (bound : DuplexFraming.pathCost (⟨history,.output block⟩ : Coordinate) ≤ Q) :
    rawHeader registry (constructionKey Q registry.iv ⟨history,.output block⟩ bound) =
      fromHistory registry history := by
  simp [rawHeader,WHIRHeaderRoots.decodeRaw_construction registry.iv _ valid bound]

/-- A raw header is read from the query alone, before its oracle answer, even for caller-output garbage keys. No output bytes or advertised value are parser arguments. -/
theorem rawHeader_exact (registry : Public) {Q : Nat} (raw : RawKey Q) (header : Header)
    (parsed : rawHeader registry raw = some header) :
    ∃ q, WHIRHeaderRoots.decodeRaw registry.iv raw = some q ∧
      (∃ block, q.terminal = .output block) ∧
      (∃ bound : DuplexFraming.pathCost q ≤ Q,
        DuplexEncoding.Admissible q ∧ DuplexModeGame.constructionKey Q registry.iv q bound = raw) ∧
      fromHistory registry q.history = some header := by
  cases decoded : WHIRHeaderRoots.decodeRaw registry.iv raw with
  | none => simp [rawHeader,decoded] at parsed
  | some q =>
    cases terminal : q.terminal with
    | commitment cursor => simp [rawHeader,decoded,terminal] at parsed
    | powBase cursor bits => simp [rawHeader,decoded,terminal] at parsed
    | output block =>
      exact ⟨q,rfl,⟨block,terminal⟩,WHIRHeaderRoots.decodeRaw_sound registry.iv raw q decoded,
        by simpa [rawHeader,decoded,terminal] using parsed⟩

theorem fromHistory_valid (registry : Public) (history : FramedHistory) (header : Header)
    (parsed : fromHistory registry history = some header) :
    history.domain = registry.domain ∧ header.statement = history.statement ∧
      registry.shapes history.statement = some header.shape ∧ header.shape.Valid := by
  unfold fromHistory at parsed
  split at parsed
  next domain =>
    cases selected : registry.shapes history.statement with
    | none => simp [selected] at parsed
    | some shape =>
      simp only [selected] at parsed
      split at parsed
      next valid =>
        cases last : history.frames.getLast? with
        | none => simp [last] at parsed
        | some frame =>
          cases frame with
          | nonce previous bits value => simp [last] at parsed
          | absorb previous bytes =>
            simp only [last] at parsed
            split at parsed
            next enough =>
              cases decoded : WHIRHistory.parseExact 5 (bytes.drop (bytes.length-120)) with
              | none => simp [decoded] at parsed
              | some scalars =>
                cases root : parseHeader shape scalars with
                | none => simp [decoded,root] at parsed
                | some digest =>
                  simp only [decoded,root,Option.bind_some,Option.map_some,Option.some.injEq] at parsed
                  subst header
                  exact ⟨domain,rfl,rfl,valid⟩
            next => contradiction
      next => contradiction
  next => contradiction

/-- The actual five-scalar header is recognized after any earlier absorb bytes and any earlier frame history. The point output and advertised value are not needed to decode it. -/
theorem fromHistory_header (registry : Public) (statement root : Digest32) (shape : Shape)
    (selected : registry.shapes statement = some shape) (valid : shape.Valid)
    (earlier : List Frame) (previous : Nat) (pending : List Byte) :
    fromHistory registry ⟨registry.domain,statement,
      earlier ++ [.absorb previous (pending ++ WHIRHistory.scalarBytes (headerScalars shape root))]⟩ =
      some ⟨statement,shape,root⟩ := by
  have encoded : (WHIRHistory.scalarBytes (headerScalars shape root)).length = 120 := by
    rw [WHIRHistory.scalarBytes_length,headerScalars_length]
  have parsed := WHIRHistory.parseExact_roundtrip (headerScalars shape root)
  rw [headerScalars_length] at parsed
  simp [fromHistory,selected,valid,encoded,parsed,List.getLast?_append,List.getLast?_singleton]

end Whir.AnchoredHeaderRoots
