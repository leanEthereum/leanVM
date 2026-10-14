import Whir.DuplexPublicSimulator

/-! Executable inverse of the literal duplex message/template key. The byte
parser only proposes a coordinate: the final comparison checks every message
byte, seed CV, tweak and final flag, including unequal list lengths. This is a
modeled source codec, not a theorem equating arbitrary Rust executions to Lean. -/
namespace Whir.PCSBCSSourceCoordinateDecoder
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame DuplexPublicSimulator

/-- The source's `PARAM_IV`, not the domain digest passed to `Duplex::new`. -/
def seedIV : Digest32 := DuplexCompression.parameterIV

/-- Recover a candidate using the existing frame decoder, then validate the
entire raw key. `zip` in `extractedPlan` is never trusted to validate shape. -/
def decodeExtracted (iv : Digest32) (key : Extracted) : Option Coordinate :=
  match DuplexEncoding.decode (extractedPlan key) with
  | none => none
  | some q =>
    if key.message = (modeKey iv q).message ∧ key.template = (modeKey iv q).template
    then some q else none

def decode {Q : Nat} (iv : Digest32) (key : RawKey Q) : Option Coordinate :=
  decodeExtracted iv (expandKey key)

theorem extractedPlan_modeKey (iv : Digest32) (q : Coordinate) :
    extractedPlan (modeKey iv q) = DuplexEncoding.plan q := by
  have step : ∀ p : List DuplexEncoding.Instruction,
      ((p.map (fun i => (if DuplexEncoding.readRole i.2 = 1 then some iv else none, i.1))).zip
        (p.map (fun i => (i.2,true)))).map (fun p => (p.1.2,p.2.1)) = p := by
    intro p
    induction p with
    | nil => rfl
    | cons i p ih => simp [ih]
  unfold modeKey keyFromPlan extractedPlan
  rw [step, List.reverse_reverse]

theorem decodeExtracted_modeKey (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) : decodeExtracted iv (modeKey iv q) = some q := by
  simp [decodeExtracted, extractedPlan_modeKey, DuplexEncoding.decode_plan q valid]

theorem decodeExtracted_iff (iv : Digest32) (key : Extracted) (q : Coordinate) :
    decodeExtracted iv key = some q ↔ DuplexEncoding.Admissible q ∧ key = modeKey iv q := by
  constructor
  · intro h
    unfold decodeExtracted at h
    cases parsed : DuplexEncoding.decode (extractedPlan key) with
    | none => simp [parsed] at h
    | some candidate =>
      simp only [parsed] at h
      split at h
      · have equal := Option.some.inj h
        subst candidate
        have fields : key.message = (modeKey iv q).message ∧
            key.template = (modeKey iv q).template := by assumption
        exact ⟨(DuplexEncoding.decode_sound parsed).1,
          by cases key; exact congrArg₂ Extracted.mk fields.1 fields.2⟩
      · cases h
  · rintro ⟨valid, rfl⟩
    exact decodeExtracted_modeKey iv q valid

theorem decode_iff {Q : Nat} (iv : Digest32) (key : RawKey Q) (q : Coordinate) :
    decode iv key = some q ↔ DuplexEncoding.Admissible q ∧ expandKey key = modeKey iv q :=
  decodeExtracted_iff iv (expandKey key) q

/-- Exact left inverse, uniformly over all data-valued domains, statements,
caller frames, nonce values and all three terminal constructors. -/
theorem decode_constructionKey (Q : Nat) (iv : Digest32) (q : Coordinate)
    (valid : DuplexEncoding.Admissible q) (bound : pathCost q ≤ Q) :
    decode iv (constructionKey Q iv q bound) = some q := by
  simp only [decode, expand_constructionKey]
  exact decodeExtracted_modeKey iv q valid

theorem decode_pathBound {Q : Nat} {iv : Digest32} {key : RawKey Q} {q : Coordinate}
    (decoded : decode iv key = some q) : pathCost q ≤ Q := by
  have same := (decode_iff iv key q).mp decoded |>.2
  have lengths := congrArg (fun e : Extracted => e.message.length) same
  simp only [expandKey, expandShort, List.length_ofFn, (modeKey_lengths iv q).1] at lengths
  have bound := key.1.1.isLt
  omega

/-- Public compression-chain recovery, with no reconstruction oracle. -/
def recover (Q : Nat) (iv : Digest32) (log : PublicLog) (input : Node) : Option Coordinate :=
  (privateKey Q log input).bind (decode iv)

theorem recover_of_modeKey {Q : Nat} {iv : Digest32} {log : PublicLog} {input : Node}
    {key : RawKey Q} {q : Coordinate} (found : privateKey Q log input = some key)
    (valid : DuplexEncoding.Admissible q) (same : expandKey key = modeKey iv q) :
    recover Q iv log input = some q := by
  simp only [recover, found, Option.bind_some]
  exact (decode_iff iv key q).mpr ⟨valid,same⟩

/-- Source shape is supplied by the actual recognized coordinate tree; key
recovery itself remains the existing executable public-log algorithm. -/
theorem recover_of_coordinateTree {Q : Nat} {iv : Digest32} {log : PublicLog} {input : Node}
    (c : Compression) (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (fresh : lookup log input = none)
    (recognizedTree : recognized log input = some (coordinateTree c iv q))
    (budget : log.length+1 ≤ Q) : recover Q iv log input = some q := by
  obtain ⟨key,found,extracted⟩ := privateKey_of_recognized fresh recognizedTree budget
  have same : expandKey key = modeKey iv q :=
    Option.some.inj (extracted.symm.trans (coordinateTree_key c iv q valid))
  exact recover_of_modeKey found valid same

theorem recover_sound {Q : Nat} {iv : Digest32} {log : PublicLog} {input : Node} {q : Coordinate}
    (recovered : recover Q iv log input = some q) :
    ∃ key ns, privateKey Q log input = some key ∧ recognized log input = some ns ∧
      Complete ns ∧ extract ns = some (modeKey iv q) ∧ DuplexEncoding.Admissible q ∧
      pathCost q ≤ Q := by
  unfold recover at recovered
  cases found : privateKey Q log input with
  | none => simp [found] at recovered
  | some key =>
    simp only [found, Option.bind_some] at recovered
    obtain ⟨ns,tree,complete,extracted⟩ := privateKey_sound found
    obtain ⟨valid,same⟩ := (decode_iff iv key q).mp recovered
    exact ⟨key,ns,rfl,tree,complete,by simpa only [same] using extracted,valid,
      decode_pathBound recovered⟩

#print axioms decode_constructionKey
#print axioms decode_iff
#print axioms recover_of_coordinateTree
#print axioms recover_sound
end Whir.PCSBCSSourceCoordinateDecoder
