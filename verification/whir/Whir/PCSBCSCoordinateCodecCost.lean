import Whir.PCSBCSSourceCoordinateDecoder

/-! Concrete canonical coordinate codec resource instrumentation. Read-run
recognition, block loads, list reconstruction and exact equalities are charged
as fixed-byte/list operations; no compression or metadata oracle is invoked. -/
set_option autoImplicit false
namespace Whir.PCSBCSCoordinateCodecCost
open Concrete FiatShamirGame DuplexRefinement DuplexEncoding DuplexModeGame

/-- Number of frames plus payload bytes. Nonce payloads occupy 24 bytes. -/
def frameUnits : Frame → Nat
  | .absorb _ bytes => bytes.length+1
  | .nonce _ _ _ => 25

def bodyUnits (frames : List Frame) : Nat := (frames.map frameUnits).sum

def readRunCount (first : Bool) : List Instruction → Option (Nat × List Byte × List Instruction) × Nat
  | [] => (none,1)
  | (b,t)::rest =>
    if readRole t = role first true then
      (some (readPrevious t,takeBytes b (readLength t),rest),1024)
    else if readRole t = role first false then
      let prior := readRunCount false rest
      (prior.1.map (fun p => (readPrevious t,takeBytes b (readLength t) ++ p.2.1,p.2.2)),prior.2+1024)
    else (none,16)

theorem readRunCount_value (first : Bool) (xs : List Instruction) :
    (readRunCount first xs).1 = readRun first xs := by
  induction xs generalizing first with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨b,t⟩
    simp only [readRunCount,readRun]
    split
    · rfl
    · split
      · rw [ih]
        cases readRun false rest <;> rfl
      · rfl

theorem readRunCount_bound (first : Bool) (xs : List Instruction) :
    (readRunCount first xs).2 ≤ 1024*(xs.length+1) := by
  induction xs generalizing first with
  | nil => simp [readRunCount]
  | cons pair rest ih =>
    rcases pair with ⟨b,t⟩
    have prior := ih false
    simp only [readRunCount,List.length_cons]
    split
    · omega
    · split <;> dsimp only <;> omega

theorem readRun_bytes (first : Bool) (xs : List Instruction) (p : Nat) (bs : List Byte)
    (tail : List Instruction) (parsed : readRun first xs = some (p,bs,tail)) :
    bs.length ≤ 64*(xs.length-tail.length) := by
  induction xs generalizing first p bs tail with
  | nil => simp [readRun] at parsed
  | cons pair rest ih =>
    rcases pair with ⟨b,t⟩
    have takeBound : (takeBytes b (readLength t)).length ≤ 64 := by
      simp [takeBytes,blockBytes]
    simp only [readRun] at parsed
    split at parsed
    · cases parsed; simpa using takeBound
    · split at parsed
      · cases h : readRun false rest with
        | none => simp [h] at parsed
        | some value =>
          rcases value with ⟨old,bytes,remaining⟩
          have prior := ih false old bytes remaining h
          have shorter := readRun_shorter false rest old bytes remaining h
          simp only [h,Option.some.injEq] at parsed
          obtain ⟨rfl,rfl,rfl⟩ := parsed
          simp only [List.length_append,List.length_cons]
          omega
      · contradiction

def readBodyCount : List Instruction → Option (List Frame × Terminal) × Nat
  | [] => (none,1)
  | [(b,t)] => (readBody [(b,t)],2048)
  | (b,t)::next::rest =>
    if readRole t = 9 then
      let later := readBodyCount (next::rest)
      (later.1.map (fun p => (.nonce (wordAt b 24) (wordAt b 32)
        (fun i => b ⟨i.val,by omega⟩)::p.1,p.2)),later.2+2048)
    else
      let run := readRunCount true ((b,t)::next::rest)
      match h : run.1 with
      | none => (none,run.2+16)
      | some (previous,bytes,tail) =>
        let later := readBodyCount tail
        (later.1.map (fun p => (.absorb previous bytes::p.1,p.2)),run.2+later.2+16)
termination_by xs => xs.length
decreasing_by
  · simp_wf
  · have hs := readRun_shorter true _ _ _ _ (readRunCount_value _ _ ▸ h)
    simp_all only [List.length_cons]

theorem readBodyCount_value (xs : List Instruction) :
    (readBodyCount xs).1 = readBody xs := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => simp only [readBodyCount,readBody]
    | cons pair rest =>
      rcases pair with ⟨b,t⟩
      cases rest with
      | nil => simp only [readBodyCount]
      | cons next rest =>
        rw [readBodyCount,readBody]
        split
        · dsimp only
          rw [ih (next::rest) (by exact Nat.lt_succ_self _)]
          cases readBody (next::rest) <;> rfl
        · dsimp only
          rw [readRunCount_value]
          cases h : readRun true ((b,t)::next::rest) with
          | none => rfl
          | some value =>
            rcases value with ⟨previous,bytes,tail⟩
            have shorter := readRun_shorter true _ _ _ _ h
            dsimp only
            rw [ih tail shorter]
            cases readBody tail <;> rfl

theorem readBodyCount_bound (xs : List Instruction) :
    (readBodyCount xs).2 ≤ 4096*(xs.length+1)*(xs.length+1) := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => simp [readBodyCount]
    | cons pair rest =>
      rcases pair with ⟨b,t⟩
      cases rest with
      | nil => simp [readBodyCount]
      | cons next rest =>
        have prior := ih (next::rest) (by exact Nat.lt_succ_self _)
        have runCap := readRunCount_bound true ((b,t)::next::rest)
        rw [readBodyCount]
        split
        · dsimp only; simp only [List.length_cons] at *; nlinarith
        · dsimp only
          cases h : (readRunCount true ((b,t)::next::rest)).1 with
          | none => simp only [List.length_cons] at *; nlinarith
          | some value =>
            rcases value with ⟨previous,bytes,tail⟩
            have shorter := readRun_shorter true _ _ _ _ (readRunCount_value _ _ ▸ h)
            have later := ih tail shorter
            simp only [List.length_cons] at *
            have smaller : tail.length+1 ≤ rest.length+2 := by omega
            nlinarith

theorem readBody_units (xs : List Instruction) (fs : List Frame) (terminal : Terminal)
    (parsed : readBody xs = some (fs,terminal)) : bodyUnits fs ≤ 65*xs.length := by
  induction xs using (measure List.length).wf.induction generalizing fs terminal with
  | h xs ih =>
    cases xs with
    | nil => simp [readBody] at parsed
    | cons pair rest =>
      rcases pair with ⟨b,t⟩
      cases rest with
      | nil =>
        simp only [readBody] at parsed
        split at parsed
        · cases parsed; simp [bodyUnits]
        · split at parsed
          · cases parsed; simp [bodyUnits]
          · split at parsed
            · cases parsed; simp [bodyUnits]
            · contradiction
      | cons next rest =>
        rw [readBody] at parsed
        split at parsed
        · cases h : readBody (next::rest) with
          | none => simp [h] at parsed
          | some value =>
            rcases value with ⟨frames,ending⟩
            have prior := ih (next::rest) (by exact Nat.lt_succ_self _) frames ending h
            simp only [h,Option.some.injEq] at parsed
            obtain ⟨rfl,rfl⟩ := parsed
            simp only [bodyUnits,List.map_cons,List.sum_cons,frameUnits,List.length_cons] at *
            omega
        · split at parsed
          · rename_i previous bytes tail hr
            cases hb : readBody tail with
            | none => simp [hb] at parsed
            | some value =>
              rcases value with ⟨frames,ending⟩
              have shorter := readRun_shorter true _ _ _ _ hr
              have prior := ih tail shorter frames ending hb
              have bytesCap := readRun_bytes true _ _ _ _ hr
              simp only [hb,Option.some.injEq] at parsed
              obtain ⟨rfl,rfl⟩ := parsed
              simp only [bodyUnits,List.map_cons,List.sum_cons,frameUnits,List.length_cons] at *
              omega
          · contradiction

def chunksCount (first : Bool) (previous : Nat) (pending : List Byte) :
    List Byte → List Instruction × Nat
  | [] => (if pending = [] then [] else [chunk first true previous pending],pending.length+1024)
  | b::bs =>
    if pending.length = 64 then
      let later := chunksCount false 0 [b] bs
      (chunk first false previous pending::later.1,pending.length+1024+later.2)
    else
      let later := chunksCount first previous (pending++[b]) bs
      (later.1,2*pending.length+4+later.2)

theorem chunksCount_value (first : Bool) (previous : Nat) (pending bs : List Byte) :
    (chunksCount first previous pending bs).1 = chunks first previous pending bs := by
  induction bs generalizing first previous pending with
  | nil => rfl
  | cons b bs ih =>
    simp only [chunksCount,chunks]
    split <;> simp [ih]

theorem chunksCount_bound (first : Bool) (previous : Nat) (pending bs : List Byte)
    (small : pending.length ≤ 64) :
    (chunksCount first previous pending bs).2 ≤ 2048*(bs.length+1) := by
  induction bs generalizing first previous pending with
  | nil => simp only [chunksCount,List.length_nil]; omega
  | cons b bs ih =>
    simp only [chunksCount,List.length_cons]
    split
    · have later := ih false 0 [b] (by simp); dsimp only; omega
    · have nextSmall : (pending++[b]).length ≤ 64 := by simp; omega
      have later := ih first previous (pending++[b]) nextSmall
      dsimp only
      omega

theorem chunks_length (first : Bool) (previous : Nat) (pending bs : List Byte) :
    (chunks first previous pending bs).length ≤ bs.length+1 := by
  induction bs generalizing first previous pending with
  | nil => simp only [chunks,List.length_nil]; split <;> simp
  | cons b bs ih =>
    simp only [chunks,List.length_cons]
    split
    · have later := ih false 0 [b]; simp only [List.length_cons]; omega
    · exact (ih first previous (pending++[b])).trans (by omega)

def framePlanCount : Frame → List Instruction × Nat
  | .absorb previous bytes => chunksCount true previous [] bytes
  | .nonce previous bits nonce => ([(nonceBlock nonce previous bits,UInt64.ofNat (9*2^56))],2048)

theorem framePlanCount_value (f : Frame) : (framePlanCount f).1 = framePlan f := by
  cases f <;> simp [framePlanCount,framePlan,chunksCount_value]

def framesPlanCount : List Frame → List Instruction × Nat
  | [] => ([],1)
  | f::rest =>
    let first := framePlanCount f
    let later := framesPlanCount rest
    (first.1++later.1,first.2+later.2+first.1.length+2)

theorem framesPlanCount_value (fs : List Frame) :
    (framesPlanCount fs).1 = fs.flatMap framePlan := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [framesPlanCount,List.flatMap_cons,framePlanCount_value,ih]

theorem framePlan_length (f : Frame) : (framePlan f).length ≤ frameUnits f := by
  cases f with
  | absorb previous bytes => exact chunks_length true previous [] bytes
  | nonce previous bits nonce => simp [framePlan,frameUnits]

theorem framesPlanCount_bound (fs : List Frame) :
    (framesPlanCount fs).2 ≤ 4096*(bodyUnits fs+1) := by
  induction fs with
  | nil => simp [framesPlanCount,bodyUnits]
  | cons f fs ih =>
    have positive : 1 ≤ frameUnits f := by cases f <;> simp [frameUnits]
    have size := framePlan_length f
    have first : (framePlanCount f).2 ≤ 2048*frameUnits f := by
      cases f with
      | absorb previous bytes => exact chunksCount_bound true previous [] bytes (by simp)
      | nonce previous bits nonce => simp [framePlanCount,frameUnits]
    simp only [framesPlanCount,framePlanCount_value,bodyUnits,List.map_cons,List.sum_cons] at *
    nlinarith

theorem framesPlan_length (fs : List Frame) :
    (fs.flatMap framePlan).length ≤ bodyUnits fs := by
  induction fs with
  | nil => simp [bodyUnits]
  | cons f fs ih =>
    have first := framePlan_length f
    simp only [List.flatMap_cons,List.length_append,bodyUnits,List.map_cons,List.sum_cons] at *
    omega

def planCount (q : Coordinate) : List Instruction × Nat :=
  let frames := framesPlanCount q.history.frames
  ((ByteCodec.pairBytes (q.history.domain,q.history.statement),UInt64.ofNat (2^56))::
    frames.1++[terminalPlan q.terminal],frames.2+frames.1.length+4096)

theorem planCount_value (q : Coordinate) : (planCount q).1 = plan q := by
  simp [planCount,plan,framesPlanCount_value]

theorem planCount_bound (q : Coordinate) :
    (planCount q).2 ≤ 8192*(bodyUnits q.history.frames+1) := by
  have frames := framesPlanCount_bound q.history.frames
  have size := framesPlan_length q.history.frames
  unfold planCount
  dsimp only
  rw [framesPlanCount_value]
  nlinarith

def parseCount : List Instruction → Option Coordinate × Nat
  | [] => (none,1)
  | (b,t)::rest =>
    if readRole t = 1 then
      let body := readBodyCount rest
      (body.1.map (fun p => ⟨⟨(fun i => b ⟨i.val,by omega⟩),
        (fun i => b ⟨i.val+32,by omega⟩),p.1⟩,p.2⟩),body.2+16)
    else (none,16)

theorem parseCount_value (xs : List Instruction) : (parseCount xs).1 = parse xs := by
  cases xs with
  | nil => rfl
  | cons pair rest =>
    rcases pair with ⟨b,t⟩
    simp only [parseCount,parse]
    split
    · rw [readBodyCount_value]
      cases readBody rest <;> rfl
    · rfl

theorem parseCount_bound (xs : List Instruction) :
    (parseCount xs).2 ≤ 8192*(xs.length+1)*(xs.length+1) := by
  cases xs with
  | nil => simp [parseCount]
  | cons pair rest =>
    rcases pair with ⟨b,t⟩
    have bound := readBodyCount_bound rest
    simp only [parseCount,List.length_cons]
    split <;> dsimp only <;> nlinarith

theorem parse_units (xs : List Instruction) (q : Coordinate) (parsed : parse xs = some q) :
    bodyUnits q.history.frames ≤ 65*xs.length := by
  cases xs with
  | nil => simp [parse] at parsed
  | cons pair rest =>
    rcases pair with ⟨b,t⟩
    simp only [parse] at parsed
    split at parsed
    · cases h : readBody rest with
      | none => simp [h] at parsed
      | some value =>
        rcases value with ⟨frames,terminal⟩
        simp only [h,Option.some.injEq] at parsed
        subst q
        have bound := readBody_units rest frames terminal h
        simp only [List.length_cons]
        exact bound.trans (by omega)
    · contradiction

/-- Each list equality pays the full inspected input-volume upper charge,
including unequal lengths; success never trusts a truncating zip. -/
def decodeCount (xs : List Instruction) : Option Coordinate × Nat :=
  let parsed := parseCount xs
  match parsed.1 with
  | none => (none,parsed.2)
  | some q =>
    let reconstructed := planCount q
    (if Admissible q ∧ reconstructed.1 = xs then some q else none,
      parsed.2+reconstructed.2+65536*(xs.length+reconstructed.1.length+1))

theorem decodeCount_value (xs : List Instruction) :
    (decodeCount xs).1 = decode xs := by
  simp only [decodeCount,decode,parseCount_value]
  cases parse xs <;> simp only [planCount_value]

def codecPolynomial (n : Nat) : Nat := 2000000*(n+2)*(n+2)

theorem decodeCount_bound (xs : List Instruction) :
    (decodeCount xs).2 ≤ codecPolynomial xs.length := by
  have parsing := parseCount_bound xs
  unfold decodeCount
  dsimp only
  cases h : (parseCount xs).1 with
  | none => unfold codecPolynomial; nlinarith
  | some q =>
    have units := parse_units xs q (parseCount_value xs ▸ h)
    have reconstruction := planCount_bound q
    have size := framesPlan_length q.history.frames
    have planSize : (planCount q).1.length ≤ bodyUnits q.history.frames+2 := by
      rw [planCount_value]
      simp only [plan,List.length_cons,List.length_append,List.length_nil]
      omega
    unfold codecPolynomial
    nlinarith

open DuplexFraming

def modeKeyCount (iv : Digest32) (q : Coordinate) : Extracted × Nat :=
  let encoded := planCount q
  (keyFromPlan iv encoded.1,encoded.2+16*encoded.1.length+4)

theorem modeKeyCount_value (iv : Digest32) (q : Coordinate) :
    (modeKeyCount iv q).1 = modeKey iv q := by
  simp [modeKeyCount,modeKey,planCount_value]

/-- Two exact raw-key comparisons share one reconstructed mode key. -/
def decodeExtractedCount (iv : Digest32) (key : Extracted) : Option Coordinate × Nat :=
  let xs := extractedPlan key
  let parsed := decodeCount xs
  match parsed.1 with
  | none => (none,parsed.2+8*(key.message.length+key.template.length)+1)
  | some q =>
    let rebuilt := modeKeyCount iv q
    (if key.message = rebuilt.1.message ∧ key.template = rebuilt.1.template then some q else none,
      parsed.2+rebuilt.2+8*(key.message.length+key.template.length)+
        65536*(key.message.length+key.template.length+
          rebuilt.1.message.length+rebuilt.1.template.length+1))

theorem decodeExtractedCount_value (iv : Digest32) (key : Extracted) :
    (decodeExtractedCount iv key).1 = PCSBCSSourceCoordinateDecoder.decodeExtracted iv key := by
  simp only [decodeExtractedCount,PCSBCSSourceCoordinateDecoder.decodeExtracted,decodeCount_value]
  cases decode (extractedPlan key) <;> simp only [modeKeyCount_value]

def extractedPolynomial (n : Nat) : Nat := 8000000*(n+2)*(n+2)

theorem decodeExtractedCount_bound (iv : Digest32) (key : Extracted) (n : Nat)
    (messageCap : key.message.length ≤ n) (templateCap : key.template.length ≤ n) :
    (decodeExtractedCount iv key).2 ≤ extractedPolynomial n := by
  have xsCap : (extractedPlan key).length ≤ n := by
    simp only [extractedPlan,List.length_reverse,List.length_map,List.length_zip]
    omega
  have parsing := decodeCount_bound (extractedPlan key)
  unfold decodeExtractedCount
  dsimp only
  cases h : (decodeCount (extractedPlan key)).1 with
  | none => unfold codecPolynomial at parsing; unfold extractedPolynomial; nlinarith
  | some q =>
    have decoded : decode (extractedPlan key) = some q := decodeCount_value _ ▸ h
    have exactPlan := (decode_sound decoded).2
    have parsed : parse (extractedPlan key) = some q := by
      unfold decode at decoded
      cases hp : parse (extractedPlan key) with
      | none => simp [hp] at decoded
      | some candidate =>
        simp only [hp] at decoded
        split at decoded
        · cases decoded; rfl
        · contradiction
    have units := parse_units _ _ parsed
    have rebuild := planCount_bound q
    have planSize : (planCount q).1.length ≤ n := by
      rw [planCount_value,exactPlan]
      exact xsCap
    have lengths : (modeKeyCount iv q).1.message.length ≤ n ∧
        (modeKeyCount iv q).1.template.length ≤ n := by
      simp only [modeKeyCount_value,modeKey,keyFromPlan,List.length_map,List.length_reverse,exactPlan]
      exact ⟨xsCap,xsCap⟩
    change (decodeCount (extractedPlan key)).2 + (modeKeyCount iv q).2 +
      8*(key.message.length+key.template.length) +
      65536*(key.message.length+key.template.length+
        (modeKeyCount iv q).1.message.length+(modeKeyCount iv q).1.template.length+1) ≤ _
    have rebuildingCost : (modeKeyCount iv q).2 ≤ 8192*(bodyUnits q.history.frames+1)+16*n+4 := by
      unfold modeKeyCount
      dsimp only
      omega
    unfold codecPolynomial at parsing
    unfold extractedPolynomial
    nlinarith

#print axioms chunksCount_value
#print axioms decodeCount_value
#print axioms decodeCount_bound
#print axioms decodeExtractedCount_value
#print axioms decodeExtractedCount_bound

#print axioms readRunCount_value
#print axioms readBodyCount_value
#print axioms readBodyCount_bound
#print axioms readBody_units
end Whir.PCSBCSCoordinateCodecCost
