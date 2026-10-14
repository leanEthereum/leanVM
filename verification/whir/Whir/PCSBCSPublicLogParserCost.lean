import Whir.PCSBCSSourceRootReferences

/-! Concrete list/byte/scalar parser instrumentation. Fixed 24-byte scalar
loads and extension-field decoding are charged by a bounded fixed-size unit;
list length, suffix traversal, result constructors, and failure paths are
charged explicitly. This module performs no fresh challenge or hash query. -/
set_option autoImplicit false
namespace Whir.PCSBCSPublicLogParserCost
open Concrete FiatShamirGame WHIRHistory WHIRHistoryKey

def parseScalarsCount : Nat → List Byte → Option (List E × List Byte) × Nat
  | 0,bs => (some ([],bs),1)
  | n+1,bs =>
    if h : 24 ≤ bs.length then
      let x := ByteCodec.decodeE (fun i => bs[i.val]'(by omega))
      let later := parseScalarsCount n (bs.drop 24)
      (later.1.map (fun p => (x::p.1,p.2)),bs.length+1024+later.2)
    else (none,bs.length+1)

theorem parseScalarsCount_value (n : Nat) (bs : List Byte) :
    (parseScalarsCount n bs).1 = parseScalars n bs := by
  induction n generalizing bs with
  | zero => rfl
  | succ n ih => simp only [parseScalarsCount,parseScalars]; split <;> simp [ih]

theorem parseScalarsCount_bound (n : Nat) (bs : List Byte) :
    (parseScalarsCount n bs).2 ≤ (n+1)*(bs.length+1024)+1 := by
  induction n generalizing bs with
  | zero => simp [parseScalarsCount]
  | succ n ih =>
    simp only [parseScalarsCount]
    split
    · have later := ih (bs.drop 24)
      simp only [List.length_drop] at later
      simp only []
      have smaller : bs.length-24 ≤ bs.length := Nat.sub_le _ _
      nlinarith
    · simp only []; nlinarith

def parseExactCount (n : Nat) (bs : List Byte) : Option (List E) × Nat :=
  let parsed := parseScalarsCount n bs
  (parsed.1.bind (fun p => if p.2 = [] then some p.1 else none),parsed.2+1)

theorem parseExactCount_value (n : Nat) (bs : List Byte) :
    (parseExactCount n bs).1 = parseExact n bs := by
  simp only [parseExactCount,parseScalarsCount_value,parseExact]
  rfl

theorem parseExactCount_bound (n : Nat) (bs : List Byte) :
    (parseExactCount n bs).2 ≤ (n+1)*(bs.length+1024)+2 := by
  have bound := parseScalarsCount_bound n bs
  simpa only [parseExactCount] using Nat.add_le_add_right bound 1

/-- Public size includes frame slots, payload bytes and consumed-output byte
counts. The latter need not be bounded by the compression-chain length. -/
def frameSize : Frame → Nat
  | .absorb consumed bytes => consumed+bytes.length+1
  | .nonce consumed _ _ => consumed+25

def framesSize (frames : List Frame) : Nat := (frames.map frameSize).sum

def parseStepsCount : List Frame → Option (List Pending) × Nat
  | [] => (some [],1)
  | .absorb _ bytes :: .nonce _ bits nonce :: rest =>
    let xs := parseExactCount (bytes.length/24) bytes
    match xs.1 with
    | none => (none,bytes.length+xs.2+1)
    | some scalars =>
      let later := parseStepsCount rest
      (later.1.map (⟨scalars,some (bits,ByteCodec.decodeE nonce)⟩::·),
        bytes.length+xs.2+later.2+1024)
  | .absorb _ bytes :: rest =>
    let xs := parseExactCount (bytes.length/24) bytes
    match xs.1 with
    | none => (none,bytes.length+xs.2+1)
    | some scalars =>
      let later := parseStepsCount rest
      (later.1.map (⟨scalars,none⟩::·),bytes.length+xs.2+later.2+1)
  | _ => (none,1)

theorem parseStepsCount_value (frames : List Frame) :
    (parseStepsCount frames).1 = parseSteps frames := by
  induction frames using (measure List.length).wf.induction with
  | h frames ih =>
    cases frames with
    | nil => rfl
    | cons f rest =>
      have restEq := ih rest (by exact Nat.lt_succ_self _)
      cases f with
      | nonce consumed bits nonce => rfl
      | absorb consumed bytes =>
        cases rest with
        | nil =>
          simp only [parseStepsCount,parseSteps,parseExactCount_value]
          cases parseExact (bytes.length/24) bytes <;> rfl
        | cons next tail =>
          have tailEq := ih tail (by exact Nat.lt_add_of_pos_right (by decide : 0 < 2))
          cases next <;>
            simp only [parseStepsCount,parseSteps,parseExactCount_value] <;>
            cases parseExact (bytes.length/24) bytes <;>
            simp_all <;> exact Option.map_eq_bind

/-- A sum of literal per-frame scalar-input charges, independent of successful
parse depth. All failures pay only the actually visited stopping prefix. -/
def stepsBudget : List Frame → Nat
  | [] => 1
  | .absorb _ bytes :: rest =>
    bytes.length+(bytes.length/24+1)*(bytes.length+1024)+1026+stepsBudget rest
  | .nonce _ _ _ :: rest => 1026+stepsBudget rest

theorem parseStepsCount_bound (frames : List Frame) :
    (parseStepsCount frames).2 ≤ stepsBudget frames := by
  induction frames using (measure List.length).wf.induction with
  | h frames ih =>
    cases frames with
    | nil => rfl
    | cons f rest =>
      have restCap := ih rest (by exact Nat.lt_succ_self _)
      cases f with
      | nonce consumed bits nonce => simp only [parseStepsCount,stepsBudget]; omega
      | absorb consumed bytes =>
        have scalar := parseExactCount_bound (bytes.length/24) bytes
        cases rest with
        | nil =>
          simp only [parseStepsCount]
          cases (parseExactCount (bytes.length/24) bytes).1 <;>
            simp only [stepsBudget] <;> omega
        | cons next tail =>
          have tailCap := ih tail (by exact Nat.lt_add_of_pos_right (by decide : 0 < 2))
          cases next <;> simp only [parseStepsCount] <;>
            cases (parseExactCount (bytes.length/24) bytes).1 <;>
            simp only [stepsBudget] <;> simp only [stepsBudget] at restCap <;> omega

theorem stepsBudget_polynomial (frames : List Frame) :
    stepsBudget frames ≤ (framesSize frames+1)*(framesSize frames+2050)+1 := by
  induction frames with
  | nil => simp [stepsBudget,framesSize]
  | cons f rest ih =>
    have nonnegative : 0 ≤ framesSize rest := Nat.zero_le _
    cases f with
    | absorb consumed bytes =>
      have divBound : bytes.length/24 ≤ bytes.length := Nat.div_le_self _ _
      simp only [stepsBudget,framesSize,List.map_cons,List.sum_cons,frameSize] at *
      nlinarith
    | nonce consumed bits nonce =>
      simp only [stepsBudget,framesSize,List.map_cons,List.sum_cons,frameSize] at *
      nlinarith

open DuplexRefinement WHIRCallerClaims WHIRCallerShape

def modelMass (m : Model) : Nat := m.run.length+m.history.frames.length

def closeRunCount (m : Model) : Model × Nat :=
  if m.run = [] then (m,1)
  else (closeRun m,m.history.frames.length+3)

theorem closeRunCount_value (m : Model) : (closeRunCount m).1 = closeRun m := by
  unfold closeRunCount closeRun
  split <;> rfl

theorem closeRun_mass (m : Model) : modelMass (closeRun m) ≤ modelMass m := by
  unfold closeRun modelMass
  split
  · rfl
  · simp only [List.length_nil,List.length_append,List.length_singleton]
    have nonempty : 0 < m.run.length := by
      cases h : m.run with
      | nil => contradiction
      | cons b bs => simp
    omega

theorem closeRunCount_bound (m : Model) : (closeRunCount m).2 ≤ modelMass m+3 := by
  unfold closeRunCount modelMass
  split <;> dsimp only <;> omega

def operationCount (m : Model) : Operation → Model × Nat
  | .absorb bs => (modelAbsorb m bs,m.run.length+bs.length+8)
  | .squeeze n =>
    if n = 0 then (m,1) else
      let closed := closeRunCount m
      ({closed.1 with consumed := m.consumed+n},closed.2+3)
  | .nonce bits value =>
    let closed := closeRunCount m
    ({history := {closed.1.history with frames :=
      closed.1.history.frames++[.nonce closed.1.consumed bits value]}},
      closed.2+closed.1.history.frames.length+3)

theorem operationCount_value (m : Model) (op : Operation) :
    (operationCount m op).1 = applyOperation m op := by
  cases op with
  | absorb bs => rfl
  | squeeze n => simp only [operationCount,applyOperation,modelSqueeze,closeRunCount_value]; split <;> rfl
  | nonce bits value => simp only [operationCount,applyOperation,modelNonce,closeRunCount_value]

def tokenModelCount (m : Model) (t : CallerToken) : Model × Nat :=
  let stepped := operationCount m (tokenOperation t)
  (stepped.1,stepped.2+900)

theorem tokenModelCount_mass (m : Model) (t : CallerToken) :
    modelMass (tokenModelCount m t).1 ≤ modelMass m+24 := by
  have closed := closeRun_mass m
  cases t with
  | sent value =>
    simp only [tokenModelCount,tokenOperation,operationCount,modelAbsorb]
    split
    · omega
    · simp only [modelMass,List.length_append,scalarBytes_length,List.length_cons,List.length_nil]
      omega
  | draw value =>
    simp only [tokenModelCount,tokenOperation,operationCount]
    rw [closeRunCount_value]
    exact closed.trans (by omega)
  | nonce bits value =>
    simp only [tokenModelCount,tokenOperation,operationCount,closeRunCount_value,modelMass,
      List.length_nil,List.length_append,List.length_singleton] at *
    omega

theorem tokenModelCount_bound (m : Model) (t : CallerToken) :
    (tokenModelCount m t).2 ≤ 2*modelMass m+950 := by
  have closeCost := closeRunCount_bound m
  have closed := closeRun_mass m
  have frames : (closeRun m).history.frames.length ≤ modelMass m := by
    exact (Nat.le_add_left _ _).trans closed
  cases t with
  | sent value =>
    have runCap : m.run.length ≤ modelMass m := Nat.le_add_right _ _
    simp only [tokenModelCount,tokenOperation,operationCount,WHIRHistory.scalarBytes_length,List.length_cons,List.length_nil]
    omega
  | draw value =>
    simp only [tokenModelCount,tokenOperation,operationCount]
    norm_num only at *
    simp only [ite_false]
    omega
  | nonce bits value =>
    simp only [tokenModelCount,tokenOperation,operationCount]
    rw [closeRunCount_value]
    omega

def tokenModelsCount : Model → List CallerToken → Model × Nat
  | m,[] => (m,1)
  | m,t::rest =>
    let step := tokenModelCount m t
    let later := tokenModelsCount step.1 rest
    (later.1,step.2+later.2+1)

theorem tokenModelsCount_value (m : Model) (ts : List CallerToken) :
    (tokenModelsCount m ts).1 = runOperations m (ts.map tokenOperation) := by
  induction ts generalizing m with
  | nil => rfl
  | cons t ts ih =>
    simp only [tokenModelsCount,runOperations,List.map_cons,List.foldl_cons,ih,tokenModelCount,operationCount_value]

theorem tokenModelsCount_mass (m : Model) (ts : List CallerToken) :
    modelMass (tokenModelsCount m ts).1 ≤ modelMass m+24*ts.length := by
  induction ts generalizing m with
  | nil => simp [tokenModelsCount]
  | cons t ts ih =>
    have first := tokenModelCount_mass m t
    have later := ih (tokenModelCount m t).1
    simp only [tokenModelsCount,List.length_cons]
    omega

theorem tokenModelsCount_bound (m : Model) (ts : List CallerToken) :
    (tokenModelsCount m ts).2 ≤ (ts.length+1)*(2*modelMass m+48*ts.length+952) := by
  induction ts generalizing m with
  | nil => simp [tokenModelsCount]
  | cons t ts ih =>
    have first := tokenModelCount_bound m t
    have mass := tokenModelCount_mass m t
    have later := ih (tokenModelCount m t).1
    simp only [tokenModelsCount,List.length_cons]
    nlinarith

def tokenHistoryCount (domain statement : Digest32) (ts : List CallerToken) : FramedHistory × Nat :=
  let built := tokenModelsCount (seedModel domain statement) ts
  let closed := closeRunCount built.1
  (closed.1.history,built.2+closed.2)

theorem tokenHistoryCount_value (domain statement : Digest32) (ts : List CallerToken) :
    (tokenHistoryCount domain statement ts).1 = tokenHistory domain statement ts := by
  simp only [tokenHistoryCount,tokenHistory,closeRunCount_value,tokenModelsCount_value]

theorem tokenHistoryCount_bound (domain statement : Digest32) (ts : List CallerToken) :
    (tokenHistoryCount domain statement ts).2 ≤ (ts.length+1)*(48*ts.length+1000) := by
  have build := tokenModelsCount_bound (seedModel domain statement) ts
  have mass := tokenModelsCount_mass (seedModel domain statement) ts
  have closeCost := closeRunCount_bound (tokenModelsCount (seedModel domain statement) ts).1
  simp only [modelMass,seedModel,List.length_nil] at build mass closeCost
  unfold tokenHistoryCount
  dsimp only
  simp only [seedModel]
  nlinarith

local instance : DecidableEq Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq Coordinate := by
  intro a b
  cases a
  cases b
  simp only [Coordinate.mk.injEq]
  infer_instance

open WHIRCallerOutputs

def outputsFromCount (e : FramedHistory) (pre : List Frame) :
    List Frame → List Coordinate × Nat
  | [] => ([],1)
  | f::rest =>
    let blocks := (List.range (outputBlocks (previousConsumed f))).map
      (fun block => (⟨{e with frames := pre},.output block⟩ : Coordinate))
    let later := outputsFromCount e (pre++[f]) rest
    (blocks++later.1,later.2+pre.length+8*blocks.length+8)

theorem outputsFromCount_value (e : FramedHistory) (pre fs : List Frame) :
    (outputsFromCount e pre fs).1 = outputsFrom e pre fs := by
  induction fs generalizing pre with
  | nil => rfl
  | cons f fs ih => simp only [outputsFromCount,outputsFrom,ih]

/-- Whole compared history volumes conservatively charge equality even when
lengths differ. The domain and statement occupy 64 fixed bytes. -/
def coordinateEqWork (a b : Coordinate) : Nat :=
  1024+framesSize a.history.frames+framesSize b.history.frames

def memberCount (q : Coordinate) : List Coordinate → Bool × Nat
  | [] => (false,1)
  | x::xs =>
    if q = x then (true,coordinateEqWork q x+1)
    else
      let later := memberCount q xs
      (later.1,coordinateEqWork q x+later.2+1)

theorem memberCount_value (q : Coordinate) (xs : List Coordinate) :
    (memberCount q xs).1 = decide (q ∈ xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [memberCount,List.mem_cons]; split <;> simp_all

/-- The answer callback is called ONCE PER BYTE, as in the real source; no
unit-cost or block-cache assumption is introduced. Tuple counts are invocation
counts, whereas membership/work counters are separate concrete operations. -/
def byteReplyCount (e : FramedHistory) (answers : Coordinate → Digest32)
    (history : FramedHistory) (j : Nat) : Byte × Nat × Nat :=
  let q : Coordinate := ⟨history,.output (j/32)⟩
  let outputs := outputsFromCount e [] e.frames
  let admitted := memberCount q outputs.1
  (if admitted.1 then
    (answers q ⟨j%32,Nat.mod_lt _ (by decide)⟩,1,outputs.2+admitted.2+8)
  else (zeroDigest ⟨j%32,Nat.mod_lt _ (by decide)⟩,0,outputs.2+admitted.2+8))

def recoveredBytesCount (e : FramedHistory) (answers : Coordinate → Digest32)
    (history : FramedHistory) (n : Nat) : List Byte × Nat × Nat :=
  let entries := List.ofFn fun i : Fin n => byteReplyCount e answers history i.val
  (entries.map Prod.fst,(entries.map (fun x => x.2.1)).sum,
    (entries.map (fun x => x.2.2)).sum+3*n+1)

theorem recoveredBytesCount_value (e : FramedHistory) (answers : Coordinate → Digest32)
    (history : FramedHistory) (n : Nat) :
    (recoveredBytesCount e answers history n).1 =
      recoveredBytes (priorAnswers e answers) history 0 n := by
  simp only [recoveredBytesCount,byteReplyCount,recoveredBytes,List.map_ofFn,Nat.zero_add]
  congr 1
  funext i
  simp only [outputsFromCount_value,callerOutputs,memberCount_value,priorAnswers]
  dsimp only [Function.comp_apply]
  split <;> simp_all

/-- Scalar decoding executes only after the real divisibility guard. -/
def tokensFromFrameCount (f : Frame) (output : List Byte) : Option (List CallerToken) × Nat :=
  let n := previousConsumed f
  if n%24 ≠ 0 then (none,2) else
  let draws := parseExactCount (n/24) output
  match draws.1 with
  | none => (none,draws.2+2)
  | some xs =>
    match f with
    | .absorb _ bytes =>
      let sent := parseExactCount (bytes.length/24) bytes
      (sent.1.map (fun ys => xs.map CallerToken.draw++ys.map CallerToken.sent),
        draws.2+sent.2+3*xs.length+3*(bytes.length/24)+4)
    | .nonce _ bits value =>
      (some (xs.map CallerToken.draw++[.nonce bits value]),draws.2+3*xs.length+4)

theorem tokensFromFrameCount_value (f : Frame) (output : List Byte) :
    (tokensFromFrameCount f output).1 = tokensFromFrame f output := by
  simp only [tokensFromFrameCount,tokensFromFrame]
  split
  · rfl
  · rw [parseExactCount_value]
    cases parseExact (previousConsumed f/24) output with
    | none => rfl
    | some xs =>
      cases f with
      | absorb consumed bytes =>
        simp only [parseExactCount_value]
        cases parseExact (bytes.length/24) bytes <;> rfl
      | nonce consumed bits value => rfl

def frameTokensCount (e : FramedHistory) (answers : Coordinate → Digest32) (i : Nat) (f : Frame) :
    Option (List CallerToken) × Nat × Nat :=
  let bytes := recoveredBytesCount e answers {e with frames := e.frames.take i} (previousConsumed f)
  let tokens := tokensFromFrameCount f bytes.1
  (tokens.1,bytes.2.1,bytes.2.2+tokens.2+min i e.frames.length+3)

theorem frameTokensCount_value (e : FramedHistory) (answers : Coordinate → Digest32)
    (i : Nat) (f : Frame) : (frameTokensCount e answers i f).1 = frameTokens e answers i f := by
  simp only [frameTokensCount,tokensFromFrameCount_value,recoveredBytesCount_value,frameTokens]

theorem frameSize_positive (f : Frame) : 1 ≤ frameSize f := by
  cases f <;> simp [frameSize]

theorem framesSize_length (fs : List Frame) : fs.length ≤ framesSize fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have first := frameSize_positive f
    simp only [framesSize,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

theorem framesSize_take (fs : List Frame) (n : Nat) :
    framesSize (fs.take n) ≤ framesSize fs := by
  induction fs generalizing n with
  | nil => simp [framesSize]
  | cons f fs ih =>
    cases n with
    | zero => simp [framesSize]
    | succ n =>
      simpa only [List.take_succ_cons,framesSize,List.map_cons,List.sum_cons] using
        Nat.add_le_add_left (ih n) (frameSize f)

theorem outputBlocks_frameSize (f : Frame) :
    outputBlocks (previousConsumed f) ≤ frameSize f := by
  cases f <;> simp only [outputBlocks,previousConsumed,frameSize] <;> omega

theorem callerOutputCount_bound (fs : List Frame) : callerOutputCount fs ≤ framesSize fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have first := outputBlocks_frameSize f
    simp only [callerOutputCount,framesSize,List.map_cons,List.sum_cons] at *
    omega

theorem outputsFromCount_bound (e : FramedHistory) (pre fs : List Frame) :
    (outputsFromCount e pre fs).2 ≤ 32*(pre.length+framesSize fs+fs.length+1)*(pre.length+framesSize fs+fs.length+1) := by
  induction fs generalizing pre with
  | nil => simp only [outputsFromCount,framesSize,List.map_nil,List.sum_nil,List.length_nil]; nlinarith
  | cons f fs ih =>
    have later := ih (pre++[f])
    have blocks := outputBlocks_frameSize f
    have positive := frameSize_positive f
    let S := pre.length+framesSize fs+fs.length+2
    have cross : S ≤ frameSize f*S := Nat.le_mul_of_pos_left _ positive
    have widthCross : frameSize f ≤ frameSize f*S :=
      Nat.le_mul_of_pos_right _ (by unfold S; omega)
    have prefixCap : pre.length+8 ≤ S+8 := by unfold S; omega
    have stepCap : pre.length+8*outputBlocks (previousConsumed f)+8 ≤ 32*frameSize f*S := by
      nlinarith
    have laterCap : (outputsFromCount e (pre++[f]) fs).2 ≤ 32*S*S := by
      convert later using 1
      simp only [S,List.length_append,List.length_cons,List.length_nil]
      ring
    have sumCap := Nat.add_le_add laterCap stepCap
    have expansion : 32*S*S+32*frameSize f*S ≤ 32*(S+frameSize f)*(S+frameSize f) := by
      nlinarith
    have combined := sumCap.trans expansion
    simp only [outputsFromCount,List.length_map,List.length_range]
    calc
      _ = (outputsFromCount e (pre++[f]) fs).2 +
          (pre.length+8*outputBlocks (previousConsumed f)+8) := by ring
      _ ≤ 32*(S+frameSize f)*(S+frameSize f) := combined
      _ = _ := by simp only [S,framesSize,List.map_cons,List.sum_cons,List.length_cons]; ring

theorem memberCount_bound (q : Coordinate) (xs : List Coordinate) (P : Nat)
    (qCap : framesSize q.history.frames ≤ P)
    (xsCap : ∀ x ∈ xs, framesSize x.history.frames ≤ P) :
    (memberCount q xs).2 ≤ xs.length*(1025+2*P)+1 := by
  induction xs with
  | nil => simp [memberCount]
  | cons x xs ih =>
    have xCap := xsCap x (by simp)
    have later := ih (fun y hy => xsCap y (by simp [hy]))
    have eqCap : coordinateEqWork q x ≤ 1024+2*P := by unfold coordinateEqWork; omega
    simp only [memberCount,List.length_cons]
    split <;> dsimp only <;> nlinarith

theorem callerOutputs_frame_bound (e : FramedHistory) (q : Coordinate)
    (member : q ∈ callerOutputs e) : framesSize q.history.frames ≤ framesSize e.frames := by
  obtain ⟨pre,f,suffix,block,split,bound,rfl⟩ := callerOutputs_mem e q member
  rw [split]
  unfold framesSize
  simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons]
  omega

theorem recoveredBytesCount_length (e : FramedHistory) (answers : Coordinate → Digest32)
    (history : FramedHistory) (n : Nat) : (recoveredBytesCount e answers history n).1.length = n := by
  simp [recoveredBytesCount]

theorem parseScalars_length (n : Nat) (bs : List Byte) (xs : List E) (tail : List Byte)
    (parsed : parseScalars n bs = some (xs,tail)) : xs.length = n := by
  induction n generalizing bs xs tail with
  | zero => cases parsed; rfl
  | succ n ih =>
    simp only [parseScalars] at parsed
    split at parsed
    · cases h : parseScalars n (bs.drop 24) with
      | none => simp [h] at parsed
      | some value =>
        rcases value with ⟨ys,rest⟩
        simp only [h,Option.map_some,Option.some.injEq] at parsed
        obtain ⟨rfl,rfl⟩ := parsed
        simp only [List.length_cons,ih _ _ _ h]
    · contradiction

theorem parseExact_length (n : Nat) (bs : List Byte) (xs : List E)
    (parsed : parseExact n bs = some xs) : xs.length = n := by
  unfold parseExact at parsed
  cases h : parseScalars n bs with
  | none => simp [h] at parsed
  | some value =>
    rcases value with ⟨ys,rest⟩
    simp only [h] at parsed
    change (if rest = [] then some ys else none) = some xs at parsed
    split at parsed
    · cases parsed; exact parseScalars_length _ _ _ _ h
    · contradiction

def byteLookupPolynomial (P : Nat) : Nat :=
  32*(2*P+1)*(2*P+1)+P*(1025+2*P)+9

theorem byteReplyCount_bound (e : FramedHistory) (answers : Coordinate → Digest32)
    (history : FramedHistory) (j P : Nat)
    (entryCap : framesSize e.frames ≤ P) (historyCap : framesSize history.frames ≤ P) :
    (byteReplyCount e answers history j).2.1 ≤ 1 ∧
      (byteReplyCount e answers history j).2.2 ≤ byteLookupPolynomial P := by
  have outputCount := callerOutputCount_bound e.frames
  have outputWork := outputsFromCount_bound e [] e.frames
  have frameCount := framesSize_length e.frames
  have members := memberCount_bound (⟨history,.output (j/32)⟩ : Coordinate)
      (outputsFromCount e [] e.frames).1 P historyCap (by
        intro q member
        rw [outputsFromCount_value] at member
        exact (callerOutputs_frame_bound e q member).trans entryCap)
  have membersCap :
      (memberCount (⟨history,.output (j/32)⟩ : Coordinate) (outputsFromCount e [] e.frames).1).2 ≤
        P*(1025+2*P)+1 := by
    apply members.trans
    rw [outputsFromCount_value,outputsFrom_length]
    gcongr
    exact outputCount.trans entryCap
  have construction :
      (outputsFromCount e [] e.frames).2 ≤ 32*(2*P+1)*(2*P+1) := by
    apply outputWork.trans
    simp only [List.length_nil]
    gcongr
    all_goals omega
  unfold byteReplyCount
  dsimp only
  split <;> dsimp only <;> constructor
  · omega
  · unfold byteLookupPolynomial; nlinarith
  · omega
  · unfold byteLookupPolynomial; nlinarith

theorem recoveredBytesCount_bound (e : FramedHistory) (answers : Coordinate → Digest32)
    (history : FramedHistory) (n P : Nat)
    (entryCap : framesSize e.frames ≤ P) (historyCap : framesSize history.frames ≤ P) :
    (recoveredBytesCount e answers history n).2.1 ≤ n ∧
      (recoveredBytesCount e answers history n).2.2 ≤ n*(byteLookupPolynomial P+3)+1 := by
  have callCap := List.sum_le_length_nsmul
    ((List.ofFn (fun i : Fin n => byteReplyCount e answers history i.val)).map (fun x => x.2.1)) 1 (by
      intro value member
      obtain ⟨x,inside,rfl⟩ := List.mem_map.mp member
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp inside
      exact (byteReplyCount_bound e answers history i.val P entryCap historyCap).1)
  have workCap := List.sum_le_length_nsmul
    ((List.ofFn (fun i : Fin n => byteReplyCount e answers history i.val)).map (fun x => x.2.2))
    (byteLookupPolynomial P) (by
      intro value member
      obtain ⟨x,inside,rfl⟩ := List.mem_map.mp member
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp inside
      exact (byteReplyCount_bound e answers history i.val P entryCap historyCap).2)
  simp only [List.length_map,List.length_ofFn,smul_eq_mul,Nat.mul_one] at callCap workCap
  unfold recoveredBytesCount
  dsimp only
  constructor
  · exact callCap
  · nlinarith

theorem tokensFromFrameCount_bound (f : Frame) (output : List Byte) (P : Nat)
    (frameCap : frameSize f ≤ P) (outputCap : output.length ≤ P) :
    (tokensFromFrameCount f output).2 ≤ 2*(P+1)*(P+1024)+6*P+8 := by
  have consumed : previousConsumed f ≤ P := by cases f <;> simp only [previousConsumed,frameSize] at * <;> omega
  have division : previousConsumed f/24 ≤ P := (Nat.div_le_self _ _).trans consumed
  have draws := parseExactCount_bound (previousConsumed f/24) output
  have drawsCap : (parseExactCount (previousConsumed f/24) output).2 ≤ (P+1)*(P+1024)+2 := by
    apply draws.trans
    gcongr
  unfold tokensFromFrameCount
  dsimp only
  split
  · omega
  · cases h : (parseExactCount (previousConsumed f/24) output).1 with
    | none => nlinarith
    | some xs =>
      have xsSize := parseExact_length _ _ _ (parseExactCount_value _ _ ▸ h)
      cases f with
      | nonce consumed bits value => simp only []; simp only [previousConsumed] at *; nlinarith
      | absorb consumed bytes =>
        have bytesCap : bytes.length ≤ P := by simp only [frameSize] at frameCap; omega
        have sent := parseExactCount_bound (bytes.length/24) bytes
        have sentCap : (parseExactCount (bytes.length/24) bytes).2 ≤ (P+1)*(P+1024)+2 := by
          apply sent.trans
          gcongr
          exact (Nat.div_le_self _ _).trans bytesCap
        simp only []
        simp only [previousConsumed] at *
        have sentCount : bytes.length/24 ≤ P := (Nat.div_le_self _ _).trans bytesCap
        nlinarith

def frameParserPolynomial (P : Nat) : Nat :=
  P*(byteLookupPolynomial P+3)+2*(P+1)*(P+1024)+7*P+12

theorem frameTokensCount_bound (e : FramedHistory) (answers : Coordinate → Digest32)
    (i : Nat) (f : Frame) (P : Nat)
    (entryCap : framesSize e.frames ≤ P) (frameCap : frameSize f ≤ P) :
    (frameTokensCount e answers i f).2.1 ≤ P ∧
      (frameTokensCount e answers i f).2.2 ≤ frameParserPolynomial P := by
  have historyCap : framesSize (e.frames.take i) ≤ P := (framesSize_take _ _).trans entryCap
  have bytes := recoveredBytesCount_bound e answers {e with frames := e.frames.take i}
    (previousConsumed f) P entryCap historyCap
  have consumed : previousConsumed f ≤ P := by cases f <;> simp only [previousConsumed,frameSize] at * <;> omega
  have scalar := tokensFromFrameCount_bound f
      (recoveredBytesCount e answers {e with frames := e.frames.take i} (previousConsumed f)).1 P
      frameCap (by rw [recoveredBytesCount_length]; exact consumed)
  have prefixCap : min i e.frames.length ≤ P := (Nat.min_le_right _ _).trans
    ((framesSize_length _).trans entryCap)
  unfold frameTokensCount frameParserPolynomial
  dsimp only
  constructor
  · omega
  · nlinarith

def tokenFramesCount (e : FramedHistory) (answers : Coordinate → Digest32) :
    List (Frame × Nat) → Option (List (List CallerToken)) × Nat × Nat
  | [] => (some [],0,1)
  | (f,i)::rest =>
    let first := frameTokensCount e answers i f
    match first.1 with
    | none => (none,first.2.1,first.2.2+2)
    | some tokens =>
      let later := tokenFramesCount e answers rest
      (later.1.map (tokens::·),first.2.1+later.2.1,first.2.2+later.2.2+3)

theorem tokenFramesCount_value (e : FramedHistory) (answers : Coordinate → Digest32)
    (fs : List (Frame × Nat)) :
    (tokenFramesCount e answers fs).1 =
      fs.mapM (fun (f,i) => frameTokens e answers i f) := by
  induction fs with
  | nil => rfl
  | cons pair fs ih =>
    rcases pair with ⟨f,i⟩
    simp only [tokenFramesCount,List.mapM_cons,frameTokensCount_value]
    cases frameTokens e answers i f <;> simp [ih,Option.map_eq_bind]

def entryTokensCount (e : FramedHistory) (answers : Coordinate → Digest32) :
    Option (List CallerToken) × Nat × Nat :=
  let frames := tokenFramesCount e answers e.frames.zipIdx
  match frames.1 with
  | none => (none,frames.2.1,frames.2.2+2*e.frames.length+2)
  | some blocks =>
    let tokens := blocks.flatten
    let rebuilt := tokenHistoryCount e.domain e.statement tokens
    (if rebuilt.1 = e then some tokens else none,
      frames.2.1,frames.2.2+2*e.frames.length+blocks.length+tokens.length+
        rebuilt.2+1024+framesSize rebuilt.1.frames+framesSize e.frames+4)

theorem entryTokensCount_value (e : FramedHistory) (answers : Coordinate → Digest32) :
    (entryTokensCount e answers).1 = entryTokens e answers := by
  simp only [entryTokensCount,entryTokens,tokenFramesCount_value]
  cases e.frames.zipIdx.mapM (fun (f,i) => frameTokens e answers i f) with
  | none => rfl
  | some blocks => simp only [tokenHistoryCount_value]; rfl

/-- Include historical payloads and encoded consumed cursors, not only frame
slots. This bounds the complete rejected reconstruction as well as successes. -/
def modelWireSize (m : Model) : Nat :=
  framesSize m.history.frames+m.run.length+m.previous+m.consumed

theorem closeRun_wire (m : Model) :
    modelWireSize (closeRun m) ≤ modelWireSize m+1 := by
  unfold closeRun modelWireSize
  split
  · omega
  · simp only [framesSize,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,frameSize,List.length_nil]
    omega

theorem tokenModelCount_wire (m : Model) (t : CallerToken) :
    modelWireSize (tokenModelCount m t).1 ≤ modelWireSize m+26 := by
  have closed := closeRun_wire m
  have cursor : (closeRun m).consumed = m.consumed := by
    unfold closeRun
    split <;> rfl
  cases t with
  | sent value =>
    simp only [tokenModelCount,tokenOperation,operationCount,modelAbsorb]
    split
    · omega
    · unfold modelWireSize
      simp only [List.length_append,scalarBytes_length,List.length_cons,List.length_nil]
      split <;> omega
  | draw value =>
    simp only [tokenModelCount,tokenOperation,operationCount]
    norm_num only
    simp only [ite_false,closeRunCount_value,modelWireSize] at *
    omega
  | nonce bits value =>
    simp only [tokenModelCount,tokenOperation,operationCount,closeRunCount_value,modelWireSize,
      framesSize,List.map_append,List.sum_append,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,frameSize,List.length_nil] at *
    omega

theorem tokenModelsCount_wire (m : Model) (ts : List CallerToken) :
    modelWireSize (tokenModelsCount m ts).1 ≤ modelWireSize m+26*ts.length := by
  induction ts generalizing m with
  | nil => simp [tokenModelsCount]
  | cons t ts ih =>
    have first := tokenModelCount_wire m t
    have later := ih (tokenModelCount m t).1
    simp only [tokenModelsCount,List.length_cons]
    omega

theorem tokenHistoryCount_size (domain statement : Digest32) (ts : List CallerToken) :
    framesSize (tokenHistoryCount domain statement ts).1.frames ≤ 26*ts.length+1 := by
  have built := tokenModelsCount_wire (seedModel domain statement) ts
  have closed := closeRun_wire (tokenModelsCount (seedModel domain statement) ts).1
  unfold tokenHistoryCount
  dsimp only
  rw [closeRunCount_value]
  simp only [modelWireSize] at closed
  have emptySize : framesSize ([] : List Frame) = 0 := rfl
  simp only [modelWireSize,seedModel,emptySize,List.length_nil] at built
  simp only [seedModel] at closed ⊢
  omega

theorem tokensFromFrame_length (f : Frame) (output : List Byte) (ts : List CallerToken)
    (returned : tokensFromFrame f output = some ts) : ts.length ≤ frameSize f := by
  cases f with
  | nonce consumed bits value =>
    simp only [tokensFromFrame,previousConsumed] at returned
    by_cases guard : consumed%24 ≠ 0
    · simp [guard] at returned
    · simp only [guard,↓reduceIte] at returned
      cases h : parseExact (consumed/24) output with
      | none => simp [h] at returned
      | some xs =>
        have size := parseExact_length _ _ _ h
        simp only [h] at returned
        change some (xs.map CallerToken.draw++[.nonce bits value]) = some ts at returned
        cases returned
        simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,frameSize]
        omega
  | absorb consumed bytes =>
    simp only [tokensFromFrame,previousConsumed] at returned
    by_cases guard : consumed%24 ≠ 0
    · simp [guard] at returned
    · simp only [guard,↓reduceIte] at returned
      cases h : parseExact (consumed/24) output with
      | none => simp [h] at returned
      | some xs =>
        have drawSize := parseExact_length _ _ _ h
        simp only [h] at returned
        cases hs : parseExact (bytes.length/24) bytes with
        | none => simp [hs] at returned
        | some ys =>
          have sentSize := parseExact_length _ _ _ hs
          simp only [hs] at returned
          change some (xs.map CallerToken.draw++ys.map CallerToken.sent) = some ts at returned
          cases returned
          simp only [List.length_append,List.length_map,frameSize]
          omega

theorem tokenFramesCount_bounds (e : FramedHistory) (answers : Coordinate → Digest32)
    (fs : List (Frame × Nat)) (P : Nat) (entryCap : framesSize e.frames ≤ P)
    (frameCaps : ∀ fi ∈ fs, frameSize fi.1 ≤ P) :
    (tokenFramesCount e answers fs).2.1 ≤ fs.length*P ∧
      (tokenFramesCount e answers fs).2.2 ≤ fs.length*(frameParserPolynomial P+3)+1 := by
  induction fs with
  | nil => simp [tokenFramesCount]
  | cons fi fs ih =>
    rcases fi with ⟨f,i⟩
    have first := frameTokensCount_bound e answers i f P entryCap (frameCaps (f,i) (by simp))
    have later := ih (fun fi hi => frameCaps fi (by simp [hi]))
    simp only [tokenFramesCount,List.length_cons]
    cases (frameTokensCount e answers i f).1 <;> dsimp only <;> constructor <;> nlinarith

theorem tokenFramesCount_lengths (e : FramedHistory) (answers : Coordinate → Digest32)
    (fs : List (Frame × Nat)) (P : Nat)
    (frameCaps : ∀ fi ∈ fs, frameSize fi.1 ≤ P)
    (blocks : List (List CallerToken)) (returned : (tokenFramesCount e answers fs).1 = some blocks) :
    blocks.length = fs.length ∧ blocks.flatten.length ≤ fs.length*P := by
  induction fs generalizing blocks with
  | nil => cases returned; simp
  | cons fi fs ih =>
    rcases fi with ⟨f,i⟩
    simp only [tokenFramesCount] at returned
    cases h : (frameTokensCount e answers i f).1 with
    | none => simp [h] at returned
    | some ts =>
      have first := (tokensFromFrame_length f _ ts (by
        have r : tokensFromFrame f
            (recoveredBytesCount e answers {e with frames := e.frames.take i} (previousConsumed f)).1 = some ts := by
          simpa only [frameTokensCount,tokensFromFrameCount_value] using h
        exact r)).trans (frameCaps (f,i) (by simp))
      simp only [h] at returned
      cases hb : (tokenFramesCount e answers fs).1 with
      | none => simp [hb] at returned
      | some rest =>
        simp only [hb,Option.map_some,Option.some.injEq] at returned
        subst blocks
        have later := ih (fun fi hi => frameCaps fi (by simp [hi])) rest hb
        simp only [List.length_cons,List.flatten_cons,List.length_append]
        constructor <;> nlinarith

def entryParserPolynomial (P : Nat) : Nat :=
  P*(frameParserPolynomial P+3)+(P*P+1)*(48*(P*P)+1000)+28*P*P+4*P+1030

theorem entryTokensCount_bound (e : FramedHistory) (answers : Coordinate → Digest32) (P : Nat)
    (entryCap : framesSize e.frames ≤ P) :
    (entryTokensCount e answers).2.1 ≤ P*P ∧
      (entryTokensCount e answers).2.2 ≤ entryParserPolynomial P := by
  have count := (framesSize_length e.frames).trans entryCap
  have caps : ∀ fi ∈ e.frames.zipIdx, frameSize fi.1 ≤ P := by
    intro fi member
    have atFrame := List.mem_zipIdx_iff_getElem?.mp member
    have inside : fi.1 ∈ e.frames := List.mem_of_getElem? atFrame
    have sumCap : frameSize fi.1 ≤ framesSize e.frames := by
      unfold framesSize
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨fi.1,inside,rfl⟩)
    exact sumCap.trans entryCap
  have frames := tokenFramesCount_bounds e answers e.frames.zipIdx P entryCap caps
  simp only [List.length_zipIdx] at frames
  unfold entryTokensCount
  dsimp only
  cases h : (tokenFramesCount e answers e.frames.zipIdx).1 with
  | none => unfold entryParserPolynomial; constructor <;> nlinarith
  | some blocks =>
    have sizes := tokenFramesCount_lengths e answers e.frames.zipIdx P caps blocks h
    simp only [List.length_zipIdx] at sizes
    have tokenCap : blocks.flatten.length ≤ P*P := sizes.2.trans (Nat.mul_le_mul_right _ count)
    have rebuilding := tokenHistoryCount_bound e.domain e.statement blocks.flatten
    have rebuildCap : (tokenHistoryCount e.domain e.statement blocks.flatten).2 ≤
        (P*P+1)*(48*(P*P)+1000) := by apply rebuilding.trans; gcongr
    have wireCap := tokenHistoryCount_size e.domain e.statement blocks.flatten
    unfold entryParserPolynomial
    constructor <;> nlinarith

theorem entryTokensCount_length (e : FramedHistory) (answers : Coordinate → Digest32)
    (P : Nat) (entryCap : framesSize e.frames ≤ P) (tokens : List CallerToken)
    (returned : (entryTokensCount e answers).1 = some tokens) : tokens.length ≤ P*P := by
  have count := (framesSize_length e.frames).trans entryCap
  have caps : ∀ fi ∈ e.frames.zipIdx, frameSize fi.1 ≤ P := by
    intro fi member
    have atFrame := List.mem_zipIdx_iff_getElem?.mp member
    have inside : fi.1 ∈ e.frames := List.mem_of_getElem? atFrame
    have sumCap : frameSize fi.1 ≤ framesSize e.frames := by
      unfold framesSize
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨fi.1,inside,rfl⟩)
    exact sumCap.trans entryCap
  unfold entryTokensCount at returned
  dsimp only at returned
  cases frames : (tokenFramesCount e answers e.frames.zipIdx).1 with
  | none => simp only [frames] at returned; cases returned
  | some blocks =>
    have sizes := tokenFramesCount_lengths e answers e.frames.zipIdx P caps blocks frames
    simp only [List.length_zipIdx] at sizes
    have tokenCap := sizes.2.trans (Nat.mul_le_mul_right P count)
    simp only [frames] at returned
    split at returned
    · cases returned
      exact tokenCap
    · cases returned

#print axioms entryTokensCount_length

#print axioms entryTokensCount_bound

#print axioms entryTokensCount_value

#print axioms frameTokensCount_value

#print axioms tokenHistoryCount_value
#print axioms tokenHistoryCount_bound

#print axioms parseScalarsCount_value
#print axioms parseStepsCount_value
#print axioms parseStepsCount_bound
#print axioms stepsBudget_polynomial
end Whir.PCSBCSPublicLogParserCost
