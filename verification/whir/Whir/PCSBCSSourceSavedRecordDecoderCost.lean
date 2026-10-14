import Whir.PCSBCSSourceSavedRecordDecoder
import Whir.PCSBCSRecoveredSourceVolume

/-! Structural work of the literal saved-record decoder. Units are list cells,
word/guard operations, and bounded fixed-width byte codecs, not CPU cycles or
allocator guarantees. The scalar byte loader is the existing checked counter.
The frame parser below is `WHIRHistory.parseFrames`, not `parseSteps` (which
merges nonce frames). Failed branches do not pay for later frames/candidates.
Digest codecs use a fixed 1024-unit charge. Equality inspects precisely the
reached scalar prefix. Pending closures are charged when forced, including
rebuilding `words tail` on each live access; no arbitrary closure certificate
or caller-word reserve is assumed. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace Whir.PCSBCSSourceSavedRecordDecoderCost
open Concrete FiatShamirGame AnchoredHeaderCodec PCSBCSSourceSavedRecordDecoder
open PCSBCSPublicLogParserCost PCSBCSCoordinateCodecCost
open DuplexFraming DuplexPublicSimulator

/-- Physical frame slots and payload bytes; numeric consumed cursors are not
expanded by this decoder. Nonces contribute their actual fixed 24-byte payload. -/
def physicalSize (entry : FramedHistory) : Nat := bodyUnits entry.frames

def parseFrameCount : Frame → Option WHIRHistory.SemanticFrame × Nat
  | .absorb previous bytes =>
    let parsed := parseExactCount (bytes.length/24) bytes
    (parsed.1.map (.absorb previous),bytes.length+parsed.2+1)
  | .nonce previous bits bytes =>
    (some (.nonce previous bits (ByteCodec.decodeE bytes)),1024)

theorem parseFrameCount_value (f : Frame) :
    (parseFrameCount f).1 = WHIRHistory.parseFrame f := by
  cases f <;> simp [parseFrameCount,WHIRHistory.parseFrame,parseExactCount_value]

def parseFramesCount : List Frame → Option (List WHIRHistory.SemanticFrame) × Nat
  | [] => (some [],1)
  | f::fs =>
    let first := parseFrameCount f
    match first.1 with
    | none => (none,first.2+1)
    | some x =>
      let later := parseFramesCount fs
      (later.1.map (x::·),first.2+later.2+1)

theorem parseFramesCount_value (fs : List Frame) :
    (parseFramesCount fs).1 = WHIRHistory.parseFrames fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [parseFramesCount,WHIRHistory.parseFrames,parseFrameCount_value]
    cases WHIRHistory.parseFrame f <;> simp [ih,Option.map_eq_bind]

theorem parseFrameCount_bound (f : Frame) :
    (parseFrameCount f).2 ≤ frameUnits f*(frameUnits f+2050) := by
  cases f with
  | absorb previous bytes =>
    have h := parseExactCount_bound (bytes.length/24) bytes
    have d := Nat.div_le_self bytes.length 24
    simp only [parseFrameCount,frameUnits]
    nlinarith
  | nonce previous bits bytes => simp [parseFrameCount,frameUnits]

theorem parseFramesCount_bound (fs : List Frame) :
    (parseFramesCount fs).2 ≤ (bodyUnits fs+1)*(bodyUnits fs+2052) := by
  induction fs with
  | nil => simp [parseFramesCount,bodyUnits]
  | cons f fs ih =>
    have hf := parseFrameCount_bound f
    have positive : 1 ≤ frameUnits f := by cases f <;> simp [frameUnits]
    have cross := Nat.zero_le (frameUnits f*bodyUnits fs)
    simp only [parseFramesCount]
    cases (parseFrameCount f).1 <;> dsimp only <;>
      simp only [bodyUnits,List.map_cons,List.sum_cons] at * <;> nlinarith

def semanticUnits : WHIRHistory.SemanticFrame → Nat
  | .absorb _ xs => xs.length+1
  | .nonce _ _ _ => 1

def semanticSize (fs : List WHIRHistory.SemanticFrame) : Nat :=
  (fs.map semanticUnits).sum

theorem parseScalars_length (n : Nat) (bs : List Byte) (xs : List E) (rest : List Byte)
    (h : WHIRHistory.parseScalars n bs = some (xs,rest)) : xs.length = n := by
  induction n generalizing bs xs rest with
  | zero => simp only [WHIRHistory.parseScalars,Option.some.injEq,Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl⟩; rfl
  | succ n ih =>
    simp only [WHIRHistory.parseScalars] at h
    split at h
    · cases he : WHIRHistory.parseScalars n (bs.drop 24) with
      | none => simp [he] at h
      | some pair =>
        rcases pair with ⟨ys,tail⟩
        simp [he] at h
        rcases h with ⟨rfl,rfl⟩
        simp only [List.length_cons,ih _ _ _ he]
    · contradiction

theorem parseExact_length (n : Nat) (bs : List Byte) (xs : List E)
    (h : WHIRHistory.parseExact n bs = some xs) : xs.length = n := by
  unfold WHIRHistory.parseExact at h
  cases he : WHIRHistory.parseScalars n bs with
  | none => simp [he] at h
  | some pair =>
    rcases pair with ⟨ys,tail⟩
    simp only [he,bind,Option.bind] at h
    split at h
    · cases h; exact parseScalars_length n bs xs tail he
    · contradiction

theorem parseFrame_units (f : Frame) (x : WHIRHistory.SemanticFrame)
    (h : WHIRHistory.parseFrame f = some x) : semanticUnits x ≤ frameUnits f := by
  cases f with
  | nonce previous bits bytes => cases h; simp [semanticUnits,frameUnits]
  | absorb previous bytes =>
    simp only [WHIRHistory.parseFrame] at h
    cases he : WHIRHistory.parseExact (bytes.length/24) bytes with
    | none => simp [he] at h
    | some xs =>
      simp only [he,Option.map_some,Option.some.injEq] at h
      subst x
      have len := parseExact_length _ _ _ he
      simp only [semanticUnits,frameUnits,len]
      omega

theorem parseFrames_units (fs : List Frame) (xs : List WHIRHistory.SemanticFrame)
    (h : WHIRHistory.parseFrames fs = some xs) : semanticSize xs ≤ bodyUnits fs := by
  induction fs generalizing xs with
  | nil => cases h; simp [semanticSize,bodyUnits]
  | cons f fs ih =>
    simp only [WHIRHistory.parseFrames] at h
    cases hf : WHIRHistory.parseFrame f with
    | none => simp [hf] at h
    | some x =>
      cases ht : WHIRHistory.parseFrames fs with
      | none => simp [hf,ht] at h
      | some tail =>
        simp [hf,ht] at h
        subst xs
        have first := parseFrame_units f x hf
        have later := ih tail ht
        simp only [semanticSize,bodyUnits,List.map_cons,List.sum_cons] at *
        omega

def extendRunCount (run : List E) : WHIRHistory.SemanticFrame → List E × Nat
  | .absorb previous xs =>
    if previous = 0 then (run++xs,run.length+2) else (xs,2)
  | .nonce _ _ _ => ([],1)

theorem extendRunCount_value (run : List E) (f : WHIRHistory.SemanticFrame) :
    (extendRunCount run f).1 = extendRun run f := by
  cases f <;> simp only [extendRunCount,extendRun]; split <;> rfl

def runCount : List E → List WHIRHistory.SemanticFrame → List E × Nat
  | run,[] => (run,1)
  | run,f::fs =>
    let first := extendRunCount run f
    let later := runCount first.1 fs
    (later.1,first.2+later.2+1)

theorem runCount_value (run : List E) (fs : List WHIRHistory.SemanticFrame) :
    (runCount run fs).1 = fs.foldl extendRun run := by
  induction fs generalizing run with
  | nil => rfl
  | cons f fs ih => simp only [runCount,List.foldl_cons,ih,extendRunCount_value]

theorem extendRunCount_size (run : List E) (f : WHIRHistory.SemanticFrame) :
    (extendRunCount run f).1.length ≤ run.length+semanticUnits f ∧
    (extendRunCount run f).2 ≤ run.length+2 := by
  cases f <;> simp only [extendRunCount,semanticUnits]
  · split <;> simp only [List.length_append] <;> constructor <;> omega
  · simp

theorem runCount_bound (run : List E) (fs : List WHIRHistory.SemanticFrame) :
    (runCount run fs).1.length ≤ run.length+semanticSize fs ∧
    (runCount run fs).2 ≤ (semanticSize fs+1)*(run.length+semanticSize fs+4) := by
  induction fs generalizing run with
  | nil => simp [runCount,semanticSize]
  | cons f fs ih =>
    have first := extendRunCount_size run f
    have later := ih (extendRunCount run f).1
    have positive : 1 ≤ semanticUnits f := by cases f <;> simp [semanticUnits]
    simp only [runCount,semanticSize,List.map_cons,List.sum_cons] at *
    constructor
    · omega
    · have monotone : ((List.map semanticUnits fs).sum+1) *
          ((extendRunCount run f).1.length+(List.map semanticUnits fs).sum+4) ≤
          ((List.map semanticUnits fs).sum+1) *
          (run.length+semanticUnits f+(List.map semanticUnits fs).sum+4) :=
        Nat.mul_le_mul_left _ (by omega)
      have mulRun : run.length ≤ semanticUnits f*run.length := by
        simpa using Nat.mul_le_mul_right run.length positive
      nlinarith [first.2,later.2,Nat.mul_self_le_mul_self positive]

/-- Equality charges one scalar comparison and one constructor test per
visited cell, and stops at the first unequal scalar or list constructor. -/
def equalCount : List E → List E → Bool × Nat
  | [],[] => (true,1)
  | x::xs,y::ys =>
    if x = y then
      let later := equalCount xs ys
      (later.1,later.2+2)
    else (false,2)
  | _,_ => (false,1)

theorem equalCount_value (xs ys : List E) :
    (equalCount xs ys).1 = decide (xs = ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [equalCount]
      split <;> simp_all

theorem equalCount_bound (xs ys : List E) :
    (equalCount xs ys).2 ≤ 2*xs.length+1 := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equalCount]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equalCount]
    | cons y ys =>
      have later := ih ys
      simp only [equalCount,List.length_cons]
      split <;> dsimp only <;> omega

/-- Cost of evaluating a reconstructed pending word. A live word rebuilds
all of `words tail`, then traverses at most eight words; a dead word only
checks its index. The full flatMap is deliberately not treated as cached. -/
def pendingAccessCharge (n tailLength index : Nat) : Nat :=
  if index < (n+7)/8 then 6*tailLength+index+4 else 1

def contextCharge (n tailLength : Nat) : Nat :=
  if n ≤ 64 then
    1 + ((List.range 8).map (fun i => pendingAccessCharge n tailLength i+2)).sum
  else 1

theorem pendingAccessCharge_bound (n t i : Nat) (hi : i < 8) :
    pendingAccessCharge n t i ≤ 6*t+12 := by
  unfold pendingAccessCharge; split <;> omega

theorem contextCharge_bound (n t : Nat) : contextCharge n t ≤ 48*t+113 := by
  unfold contextCharge
  split
  · have sumBound : ((List.range 8).map (fun i => pendingAccessCharge n t i+2)).sum ≤ 8*(6*t+14) := by
      apply List.sum_le_length_nsmul
      intro x hx
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
      have bound := pendingAccessCharge_bound n t i (List.mem_range.mp hi)
      omega
    omega
  · omega

/-- Short-circuit shape guards; exponentiation is reached only after
logBatch < logN < 64, so at most 63 multiplications. -/
def shapeCharge (s : Shape) : Nat :=
  if s.logBatch < s.logN then
    if s.logN < 64 then
      if 1 ≤ s.logRate then
        if s.logN-s.logBatch+s.logRate < 64 then
          if 1 ≤ s.lanes then 6+s.logBatch else 5
        else 4
      else 3
    else 2
  else 1

theorem shapeCharge_bound (s : Shape) : shapeCharge s ≤ 69 := by
  unfold shapeCharge
  repeat' first | omega | split

def validCharge (r : Record) (tailLength : Nat) : Nat :=
  shapeCharge r.shape +
    if r.shape.Valid then
      contextCharge r.context.pendingBytes tailLength +
        if r.context.Valid then r.point.length+1 else 0
    else 0

def compatibleCharge (p : ParameterBounds.Profile) (r : Record) : Nat :=
  if r.shape.logN = (ParameterBounds.config p).logN then
    if r.shape.logBatch = (ParameterBounds.config p).folds[0]! then 3 else 2
  else 1

theorem compatibleCharge_bound (p : ParameterBounds.Profile) (r : Record) :
    compatibleCharge p r ≤ 3 := by
  unfold compatibleCharge
  repeat' first | omega | split

/-- Reconstruct pays its nine constructor tests, both fixed digest codecs,
point drop/dropLast and last-element scan. It does not force pending words. -/
def reconstructCharge : List E → Nat
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: metadata :: _ :: tail =>
    2058 + min ((metadata.c0.toNat+23)/24) tail.length +
      (tail.drop ((metadata.c0.toNat+23)/24)).length + tail.length
  | xs => xs.length+1

theorem reconstructCharge_bound (xs : List E) :
    reconstructCharge xs ≤ 2058+3*xs.length := by
  unfold reconstructCharge
  split
  · rename_i marker shape lanes a b cv0 cv1 metadata squeezed tail
    simp only [List.length_cons,List.length_drop]
    have bound := Nat.min_le_right ((metadata.c0.toNat+23)/24) tail.length
    omega
  · omega

/-- Opening construction is reached only after Valid: ≤3 packs, ≤8 live
words, each possibly rebuilding the literal tail; digest/metadata work is
fixed-width, and the point is copied by the actual concatenations. -/
def packCharge (n t i : Nat) : Nat :=
  6 + pendingAccessCharge n t (3*i%8) +
    (if 3*i+1 < (n+7)/8 then pendingAccessCharge n t ((3*i+1)%8) else 0) +
    (if 3*i+2 < (n+7)/8 then pendingAccessCharge n t ((3*i+2)%8) else 0)

theorem packCharge_bound (n t i : Nat) : packCharge n t i ≤ 18*t+42 := by
  have a := pendingAccessCharge_bound n t (3*i%8) (Nat.mod_lt _ (by decide))
  have b := pendingAccessCharge_bound n t ((3*i+1)%8) (Nat.mod_lt _ (by decide))
  have c := pendingAccessCharge_bound n t ((3*i+2)%8) (Nat.mod_lt _ (by decide))
  unfold packCharge
  split <;> split <;> omega

def openingCharge (r : Record) (tailLength : Nat) : Nat :=
  4096 + ((List.range ((r.context.pendingBytes+23)/24)).map
    (packCharge r.context.pendingBytes tailLength)).sum + 2*r.point.length

theorem openingCharge_bound (r : Record) (t : Nat) (valid : r.Valid) :
    openingCharge r t ≤ 4222+54*t+2*r.point.length := by
  have count : (r.context.pendingBytes+23)/24 ≤ 3 := by
    have := valid.2.1.1
    omega
  have sumBound : ((List.range ((r.context.pendingBytes+23)/24)).map
      (packCharge r.context.pendingBytes t)).sum ≤
      ((r.context.pendingBytes+23)/24)*(18*t+42) := by
    have h := List.sum_le_length_nsmul
      ((List.range ((r.context.pendingBytes+23)/24)).map
        (packCharge r.context.pendingBytes t)) (18*t+42) (by
          intro x hx
          obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
          exact packCharge_bound _ _ _)
    simpa only [List.length_map,List.length_range,smul_eq_mul] using h
  have cap := Nat.mul_le_mul_right (18*t+42) count
  unfold openingCharge
  omega

def parseCount (p : ParameterBounds.Profile) (xs : List E) : Option Record × Nat :=
  let initial := reconstructCharge xs
  match reconstruct xs with
  | none => (none,initial+1)
  | some r =>
    let metadata := initial+validCharge r (xs.length-9)+1
    if r.Valid then
      let profile := metadata+compatibleCharge p r+1
      if Compatible p r then
        let opening := openingScalars r
        let compared := equalCount opening xs
        (if compared.1 then some r else none,
          profile+openingCharge r (xs.length-9)+compared.2+1)
      else (none,profile)
    else (none,metadata)

theorem parseCount_value (p : ParameterBounds.Profile) (xs : List E) :
    (parseCount p xs).1 = parse p xs := by
  simp only [parseCount,parse]
  cases reconstruct xs with
  | none => rfl
  | some r =>
    simp only [Option.bind_some]
    by_cases hv : r.Valid <;> by_cases hp : Compatible p r <;>
      simp [hv,hp,equalCount_value]

theorem reconstruct_point_bound (xs : List E) (r : Record)
    (h : reconstruct xs = some r) : r.point.length ≤ xs.length := by
  unfold reconstruct at h
  split at h
  · cases h
    simp only [List.length_dropLast,List.length_drop,List.length_cons]
    omega
  · contradiction

theorem parseCount_bound (p : ParameterBounds.Profile) (xs : List E) :
    (parseCount p xs).2 ≤ 120*xs.length+7000 := by
  have initial := reconstructCharge_bound xs
  unfold parseCount
  cases hr : reconstruct xs with
  | none => dsimp only; omega
  | some r =>
    have point := reconstruct_point_bound xs r hr
    have shape := shapeCharge_bound r.shape
    have context := contextCharge_bound r.context.pendingBytes (xs.length-9)
    have vc : validCharge r (xs.length-9) ≤ 49*xs.length+183 := by
      unfold validCharge
      split
      · split <;> omega
      · omega
    have profile := compatibleCharge_bound p r
    dsimp only
    split
    · rename_i hv
      split
      · have pendingBound := hv.2.1.1
        have pointLength := hv.2.2
        have openingLength := openingScalars_valid_length r hv
        have eqCost := equalCount_bound (openingScalars r) xs
        have openingCost := openingCharge_bound r (xs.length-9) hv
        omega
      · dsimp only; omega
    · dsimp only; omega

/-- Same four candidates and same early successful exit as findSome?. Each
reached candidate separately pays the real full `xs.length` scan and drop. -/
def candidatesCount (p : ParameterBounds.Profile) (xs : List E) :
    List Nat → Option Record × Nat
  | [] => (none,1)
  | i::is =>
    let dropped := xs.drop (xs.length-(10+(ParameterBounds.config p).logN+i))
    let tried := parseCount p dropped
    let traversal := xs.length + (xs.length-(10+(ParameterBounds.config p).logN+i)) + 4
    match tried.1 with
    | some r => (some r,traversal+tried.2+1)
    | none =>
      let later := candidatesCount p xs is
      (later.1,traversal+tried.2+later.2+1)

theorem candidatesCount_value (p : ParameterBounds.Profile) (xs : List E) (is : List Nat) :
    (candidatesCount p xs is).1 = is.findSome? (fun i =>
      parse p (xs.drop (xs.length-(10+(ParameterBounds.config p).logN+i)))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [candidatesCount,List.findSome?_cons,parseCount_value]
    cases parse p (xs.drop (xs.length-(10+(ParameterBounds.config p).logN+i))) <;> simp [ih]

theorem candidatesCount_bound (p : ParameterBounds.Profile) (xs : List E) (is : List Nat) :
    (candidatesCount p xs is).2 ≤ is.length*(122*xs.length+7005)+1 := by
  induction is with
  | nil => simp [candidatesCount]
  | cons i is ih =>
    have tried := parseCount_bound p (xs.drop (xs.length-(10+(ParameterBounds.config p).logN+i)))
    have dropBound : (xs.drop (xs.length-(10+(ParameterBounds.config p).logN+i))).length ≤ xs.length :=
      by simp only [List.length_drop]; omega
    have triedCap : (parseCount p (xs.drop (xs.length-(10+(ParameterBounds.config p).logN+i)))).2 ≤
        120*xs.length+7000 := tried.trans (by omega)
    have traversalCap := Nat.sub_le xs.length (10+(ParameterBounds.config p).logN+i)
    simp only [candidatesCount,List.length_cons]
    cases (parseCount p (xs.drop (xs.length-(10+(ParameterBounds.config p).logN+i)))).1 <;>
      dsimp only <;> nlinarith

def decodeCount (p : ParameterBounds.Profile) (entry : FramedHistory) : Option Record × Nat :=
  let parsed := parseFramesCount entry.frames
  match parsed.1 with
  | none => (none,parsed.2+1)
  | some fs =>
    let run := runCount [] fs
    let decoded := candidatesCount p run.1 (List.range 4)
    (decoded.1,parsed.2+run.2+decoded.2+2)

theorem decodeCount_value (p : ParameterBounds.Profile) (entry : FramedHistory) :
    (decodeCount p entry).1 = decode p entry := by
  simp only [decodeCount,decode,literalRun,parseFramesCount_value]
  cases WHIRHistory.parseFrames entry.frames <;>
    simp [runCount_value,candidatesCount_value,decodeScalars]

/-- Polynomial in actual physical input volume, including all rejecting inputs. -/
def physicalPolynomial (n : Nat) : Nat := 2*n*n+2550*n+30100

theorem decodeCount_bound (p : ParameterBounds.Profile) (entry : FramedHistory) :
    (decodeCount p entry).2 ≤ physicalPolynomial (physicalSize entry) := by
  have parser := parseFramesCount_bound entry.frames
  unfold decodeCount
  cases hp : (parseFramesCount entry.frames).1 with
  | none => simp only [hp]; unfold physicalPolynomial physicalSize; nlinarith
  | some fs =>
    have parsed : WHIRHistory.parseFrames entry.frames = some fs := by
      rw [← parseFramesCount_value,hp]
    have volume := parseFrames_units entry.frames fs parsed
    have run := runCount_bound [] fs
    have candidate := candidatesCount_bound p (runCount [] fs).1 (List.range 4)
    simp only [List.length_nil,List.length_range,zero_add] at run candidate
    simp only [hp]
    unfold physicalPolynomial physicalSize
    nlinarith

/-- Standard three axioms only; exact value erasure and resource bound together. -/
theorem erasure_resource (p : ParameterBounds.Profile) (entry : FramedHistory) :
    (decodeCount p entry).1 = decode p entry ∧
    (decodeCount p entry).2 ≤ physicalPolynomial (physicalSize entry) :=
  ⟨decodeCount_value p entry,decodeCount_bound p entry⟩

/-- A genuine coordinate-path charge bounds bytes/frames via the checked
canonical parser volume lemma; cursor magnitudes are not needed here. -/
theorem coordinate_physical (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (Q : Nat) (bound : pathCost q ≤ Q) :
    physicalSize q.history ≤ 65*Q := by
  have volume := parse_units (DuplexEncoding.plan q) q (DuplexEncoding.parse_plan q valid)
  change (DuplexEncoding.plan q).length ≤ Q at bound
  unfold physicalSize
  omega

def queryPolynomial (Q : Nat) : Nat := physicalPolynomial (65*Q)

theorem decodeCount_query_bound (p : ParameterBounds.Profile)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (Q : Nat) (bound : pathCost q ≤ Q) :
    (decodeCount p q.history).2 ≤ queryPolynomial Q := by
  have physical := decodeCount_bound p q.history
  have volume := coordinate_physical q valid Q bound
  unfold queryPolynomial physicalPolynomial at *
  nlinarith

theorem decodeCount_recovered_bound {Q : Nat} {iv : Digest32}
    {log : PublicLog} {input : Node} {q : Coordinate}
    (p : ParameterBounds.Profile)
    (recovered : PCSBCSSourceCoordinateDecoder.recover Q iv log input = some q) :
    (decodeCount p q.history).2 ≤ queryPolynomial Q := by
  obtain ⟨_,_,_,_,_,_,valid,physical⟩ := PCSBCSSourceCoordinateDecoder.recover_sound recovered
  exact decodeCount_query_bound p q valid Q physical
theorem supported_logN : ∀ p : ParameterBounds.Profile,
    (ParameterBounds.config p).logN ≤ 28 := by
  decide +kernel

/-- Supported accepted records fit the physical metadata caps used above. -/
theorem accepted_shape_caps (p : ParameterBounds.Profile) (entry : FramedHistory)
    (r : Record) (accepted : decode p entry = some r) :
    r.shape.logN ≤ 28 ∧ r.context.pendingBytes ≤ 64 ∧
    (pendingPacks r.context).length ≤ 3 ∧ (r.context.pendingBytes+7)/8 ≤ 8 := by
  have sound := decode_sound p entry r accepted
  have logCap := supported_logN p
  have bytes := sound.1.2.1.1
  rw [← sound.2.1.1] at logCap
  simp only [pendingPacks,List.length_map,List.length_range]
  omega

#print axioms erasure_resource
#print axioms decodeCount_query_bound
#print axioms decodeCount_recovered_bound
end Whir.PCSBCSSourceSavedRecordDecoderCost
