import Whir.SpongefishCurrentSourceCallerOriginal

/-! The current replay retains exactly its consumed prover bytes. This proves
source transport from the literal codec reads rather than asking the caller to
supply equality between a decoded query history and the original proof. -/
namespace Whir.SpongefishCurrentByteTransport
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open SpongefishPCSRoundFrames SpongefishCurrentMixedModeCompiler
set_option autoImplicit false

 def resultData : Result → Data
  | .ok cur => cur.data
  | .error (cur,_) => cur.data

 def Conserves (whole : List Byte) (data : Data) : Prop :=
  retainedBytes data.pending ++ data.narg = whole

 theorem read_conserves (whole : List Byte) (cur : SemanticCursor) (kind : WireKind)
    (value : kind.Value) (rest : List Byte) (before : Conserves whole cur.data)
    (parsed : kind.codec.parse cur.data.narg = some (value,rest)) :
    Conserves whole (readNext cur kind value rest).data := by
  have bytes := Codec.canonical_read kind.codec cur.data.narg rest value parsed
  simp only [Conserves,readNext,boundData,bind_retains]
  rw [List.append_assoc,← bytes]
  exact before

 theorem hint_conserves (whole : List Byte) (cur : SemanticCursor)
    (bytes : List Byte) (rest : List (List Byte)) (before : Conserves whole cur.data) :
    Conserves whole (hintNext cur bytes rest).data := before

 theorem drawn_conserves (whole : List Byte) (cur : SemanticCursor) (n : Nat)
    (guard : cur.data.pending.consumed+n ≤ maxCursor) (cache : Cache) (bytes : List Byte)
    (before : Conserves whole cur.data) : Conserves whole (drawn cur n guard cache bytes).data := by
  simpa only [Conserves,drawn,draw_retains] using before

 theorem replay_conserves (C : PrimitiveOracle) (iv : Digest32) (whole : List Byte)
    (cur : SemanticCursor) (calls : List Call) (before : Conserves whole cur.data) :
    Conserves whole (resultData (runReal C iv (replayProgram cur calls)).view.result) := by
  induction calls generalizing cur with
  | nil => exact before
  | cons call calls ih =>
    cases call with
    | read kind =>
      cases parsed : kind.codec.parse cur.data.narg with
      | none => simpa only [replayProgram,parsed,runReal,resultData] using before
      | some pair =>
        obtain ⟨value,rest⟩ := pair
        simp only [replayProgram,parsed]
        exact ih _ (read_conserves whole cur kind value rest before parsed)
    | hint =>
      cases hintEq : cur.data.hints with
      | nil => simpa only [replayProgram,hintEq,runReal,resultData] using before
      | cons bytes rest =>
        simp only [replayProgram,hintEq]
        exact ih _ (hint_conserves whole cur bytes rest before)
    | draw group =>
      by_cases zero : group.bytes = 0
      · simp only [replayProgram,zero,↓reduceDIte]
        exact ih _ before
      · by_cases guard : cur.data.pending.consumed+group.bytes ≤ maxCursor
        · simp only [replayProgram,zero,↓reduceDIte,guard,seq,
            WHIRModeFinal.bind_real_result]
          exact ih _ (drawn_conserves whole cur group.bytes guard _ _ before)
        · simpa only [replayProgram,zero,↓reduceDIte,guard,runReal,resultData] using before

 theorem initial_conserves (session : Digest32) (instanceBytes narg : List Byte)
    (hints : List (List Byte)) :
    Conserves (instanceBytes ++ narg)
      (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints).data := by
  change retainedBytes (SpongefishPCSRoundFrames.bind {domain := session} instanceBytes) ++ narg =
    instanceBytes ++ narg
  rw [bind_retains]
  rfl

 theorem coordinate_bytes (m : Pending) (block : Nat) :
    SpongefishCurrentSourceCallerOriginal.historyBytes
      (SpongefishCurrentModeQueries.coordinate m block) = retainedBytes m := by
  simp only [SpongefishCurrentSourceCallerOriginal.historyBytes,
    SpongefishCurrentModeQueries.coordinate,
    ← SpongefishCurrentAbsorbedPrefix.pending_history,
    SpongefishCurrentAbsorbedPrefix.parse_history,Option.map_some,Option.getD_some,
    SpongefishCurrentAbsorbedPrefix.complete_prover_bytes]

 theorem initialized_consumed_transport (C : PrimitiveOracle) (iv session : Digest32)
    (instanceBytes narg : List Byte) (hints : List (List Byte)) (calls : List Call)
    (block : Nat)
    (consumed : (resultData (runReal C iv (replayProgram
      (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints) calls)).view.result).narg = []) :
    let data := resultData (runReal C iv (replayProgram
      (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints) calls)).view.result
    (SpongefishCurrentSourceCallerOriginal.historyBytes
      (SpongefishCurrentModeQueries.coordinate data.pending block)).drop instanceBytes.length = narg := by
  dsimp only
  rw [coordinate_bytes]
  have saved := replay_conserves C iv (instanceBytes ++ narg)
    (SpongefishCurrentInitializedMode.initial session instanceBytes narg hints) calls
    (initial_conserves session instanceBytes narg hints)
  simp only [Conserves,consumed,List.append_nil] at saved
  rw [saved]
  simp

#print axioms replay_conserves
#print axioms initialized_consumed_transport
end Whir.SpongefishCurrentByteTransport
