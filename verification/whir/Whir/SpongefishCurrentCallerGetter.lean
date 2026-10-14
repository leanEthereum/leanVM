import Whir.SpongefishCurrentInitializedMode
import Whir.SpongefishCurrentCommitmentReceive

/-! Current public-answer transport. Only literal construction observations are
used; missing or over-budget answers reject, and all 32 reply bytes are retained.
This interpreter is deterministic and does not run an oracle or Mixed.compile. -/
namespace Whir.SpongefishCurrentCallerGetter
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
set_option autoImplicit false

 def lookup (q : Coordinate) : List Observation → Option Digest32
  | [] => none
  | o :: os => match o.query with
    | .construction other _ => if other = q then some o.answer else lookup q os
    | .primitive _ _ => lookup q os

 def bounded {Q : Nat} (observations : List Observation) (q : Coordinate) : Option Digest32 :=
  if pathCost q ≤ Q then lookup q observations else none

 def raw {Q : Nat} (iv : Digest32) (observations : List Observation)
    (key : RawKey Q) : Option Digest32 := do
  let q ← WHIRHeaderRoots.decodeRaw iv key
  bounded (Q := Q) observations q

 theorem raw_construction {Q : Nat} (iv : Digest32) (observations : List Observation)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (work : pathCost q ≤ Q) :
    raw iv observations (constructionKey Q iv q work) = lookup q observations := by
  simp [raw,WHIRHeaderRoots.decodeRaw_construction iv q valid work,bounded,work]

 def answer {Q : Nat} (observations : List Observation) : Query → Option Digest32
  | .construction q _ => bounded (Q := Q) observations q
  | .primitive _ _ => none

 def run {A : Type} (get : Query → Option Digest32) : Program A → Option A
  | .done a => some a
  | .ask q next => (get q).bind (fun d => run get (next d))

/-- Unlike runReal, this interpreter accepts an arbitrary getter. Close any
computed reply before the adaptive continuation can retain or reuse it. -/
private def runStored {A : Type} (get : Query → Option Digest32) :
    Program A → Option A
  | .done a => some a
  | .ask q next => (get q).bind (fun d =>
      withDigest d (fun stored => runStored get (next stored)))

@[csimp] private theorem run_stored : @run = @runStored := by
  funext A get p
  induction p with
  | done => rfl
  | ask q next ih =>
    simp only [run,runStored,withDigest_eq,ih]

 theorem run_congr {A : Type} (p : Program A) (a b : Query → Option Digest32)
    (equal : a = b) : run a p = run b p := by rw [equal]

 theorem run_real {A : Type} (C : PrimitiveOracle) (iv : Digest32) (p : Program A)
    (get : Query → Option Digest32)
    (observed : ∀ o ∈ (runReal C iv p).view.observations,
      get o.query = some o.answer) :
    run get p = some (runReal C iv p).view.result := by
  induction p with
  | done a => rfl
  | ask query next ih =>
    have first := observed ⟨query,realAnswer C iv query⟩ (by simp [runReal,prepend])
    have tail := ih (realAnswer C iv query) (fun o h => observed o (by
      simp only [runReal,prepend]; exact List.mem_cons_of_mem _ h))
    simp only [run,first,Option.bind_some,tail,runReal,prepend]

 theorem lookup_real (C : PrimitiveOracle) (iv : Digest32) (observations : List Observation)
    (consistent : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q)
    (present : ∃ o ∈ observations, o.query = .construction q valid) :
    lookup q observations = some (evalCoordinate (compressionOf C) iv q) := by
  induction observations with
  | nil => simp at present
  | cons o os ih =>
    have head := consistent o List.mem_cons_self
    have tail := ih (fun x h => consistent x (List.mem_cons_of_mem _ h))
    cases query : o.query with
    | primitive purpose input =>
      simp only [lookup,query]
      apply tail
      obtain ⟨x,h,e⟩ := present
      rcases List.mem_cons.mp h with rfl | h
      · rw [query] at e; cases e
      · exact ⟨x,h,e⟩
    | construction other proof =>
      simp only [lookup,query]
      split
      · rename_i equal
        subst other
        simpa [query,realAnswer] using congrArg some head
      · rename_i different
        apply tail
        obtain ⟨x,h,e⟩ := present
        rcases List.mem_cons.mp h with rfl | h
        · rw [query] at e
          cases e
          exact False.elim (different rfl)
        · exact ⟨x,h,e⟩

 theorem bounded_real {Q : Nat} (C : PrimitiveOracle) (iv : Digest32)
    (observations : List Observation)
    (consistent : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (q : Coordinate) (valid : DuplexEncoding.Admissible q) (work : pathCost q ≤ Q)
    (present : ∃ o ∈ observations, o.query = .construction q valid) :
    bounded (Q := Q) observations q = some (evalCoordinate (compressionOf C) iv q) := by
  simp only [bounded,work,↓reduceIte]
  exact lookup_real C iv observations consistent q valid present

 theorem real_consistent {A : Type} (C : PrimitiveOracle) (iv : Digest32) (p : Program A) :
    ∀ o ∈ (runReal C iv p).view.observations, o.answer = realAnswer C iv o.query := by
  induction p with
  | done a => simp [runReal]
  | ask q next ih =>
    intro o h
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · exact ih (realAnswer C iv q) o h

/-- The actual byte cursor fixes both the block floor and byte remainder. No
sampled coordinate or independent E192 answer is supplied to this theorem. -/
 theorem squeezed_raw_byte {Q : Nat} (C : PrimitiveOracle) (iv : Digest32)
    (m : SpongefishPCSRoundFrames.Pending) (s t : State)
    (represented : SpongefishPCSRoundFrames.RepresentsCurrent (compressionOf C) iv m s)
    (framed : SpongefishCurrentModeQueries.FrameDomain m)
    (n : Nat) (positive : n ≠ 0) (bytes : List Byte)
    (squeezed : squeeze (compressionOf C) s n = .ok (t,bytes)) (j : Nat) (within : j < n)
    (work : pathCost (SpongefishCurrentModeQueries.coordinate m ((m.consumed+j)/32)) ≤ Q)
    (observations : List Observation)
    (consistent : ∀ o ∈ observations, o.answer = realAnswer C iv o.query)
    (present : ∃ o ∈ observations, ∃ valid,
      o.query = .construction (SpongefishCurrentModeQueries.coordinate m ((m.consumed+j)/32)) valid) :
    (raw iv observations (constructionKey Q iv
      (SpongefishCurrentModeQueries.coordinate m ((m.consumed+j)/32)) work)).map
        (fun digest => digest ⟨(m.consumed+j)%32,Nat.mod_lt _ (by decide)⟩) =
      some (bytes[j]'(by
        obtain ⟨_,len⟩ := squeeze_exact_cursor (compressionOf C) s t n bytes squeezed
        omega)) := by
  have valid := SpongefishCurrentModeQueries.squeezed_coordinate_admissible
    (compressionOf C) iv m s t represented framed n positive bytes squeezed j within
  obtain ⟨o,member,proof,equal⟩ := present
  rw [raw_construction iv observations _ valid work,
    lookup_real C iv observations consistent _ valid ⟨o,member,equal⟩]
  simp only [Option.map_some]
  rw [SpongefishCurrentModeQueries.squeezed_byte
    (compressionOf C) iv m s t represented n positive bytes squeezed j within]

#print axioms run_stored

#print axioms raw_construction
#print axioms run_real
#print axioms lookup_real
#print axioms bounded_real
#print axioms real_consistent
#print axioms squeezed_raw_byte
end Whir.SpongefishCurrentCallerGetter
