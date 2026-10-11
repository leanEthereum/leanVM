import Whir.PrunedMerkleProgram
import Whir.PrunedMerkleCoverage
import Whir.PublicMerkleBinding
import Whir.WHIRPhysicalRows
import Whir.WHIRModeReplay
import Whir.WHIRSourceChronology
import Whir.WHIRPowProgram
import Whir.WHIRCallerSupport
import Whir.WHIRNativeArithmetic

namespace Whir.WHIRPhysicalVerifier
open Concrete Protocol FiatShamirGame DuplexModeGame
open MerkleTransport MerkleTransport.Commitments
open WHIRPhysicalRows
set_option maxHeartbeats 800000

structure Opened where
  paths : List RawPath
  rows : Oracle

/-- Native `open_rows` removes absent base lanes. The later WHIR base-row
fold, not this decoder, reverses them. Extension limbs are grouped once. -/
def decodeRows (base : Bool) (rowWords leafWords : Nat) (paths : List RawPath) : Option Oracle :=
  if base then
    some ((paths.map (fun p => ((p.leafData.drop (leafWords-rowWords)).map E.ofK).toArray)).toArray)
  else
    (collect (fun p => ByteCodec.wordsToFields p.leafData) paths).map
      (fun rows => (rows.map List.toArray).toArray)

def finishRows (base : Bool) (rowWords leafWords : Nat) (result : Option (List RawPath)) : Option Opened :=
  result.bind fun paths => (decodeRows base rowWords leafWords paths).map (fun rows => ⟨paths,rows⟩)

/-- Every hash is an ordinary verification-purpose public primitive program.
The returned rows originate in the untrusted pruned proof, never in an ideal oracle. -/
def openRows (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) : Program (Option Opened) :=
  WHIRModeFinal.bind (PrunedMerkleProgram.verify proof root numLeaves queries rowWords leafWords)
    (fun result => .done (finishRows base rowWords leafWords result))

theorem openRows_counted (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) :
    Counts (PrunedMerkleProgram.budget proof numLeaves leafWords)
      (openRows proof root numLeaves queries rowWords leafWords base) := by
  unfold openRows
  rw [← Nat.add_zero (PrunedMerkleProgram.budget proof numLeaves leafWords)]
  apply WHIRModeFinal.bind_counted
  · exact PrunedMerkleProgram.verify_counted proof root numLeaves queries rowWords leafWords
  · intro; trivial

theorem openRows_real (C : PrimitiveOracle) (iv : Digest32)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) :
    (runReal C iv (openRows proof root numLeaves queries rowWords leafWords base)).view.result =
      (proof.open (PublicMerkleLog.hash C) root numLeaves queries rowWords leafWords).bind
        (fun paths => (decodeRows base rowWords leafWords paths).map (fun rows => ⟨paths,rows⟩)) := by
  rw [openRows,WHIRModeFinal.bind_real_result,PrunedMerkleProgram.verify_real_result]
  rfl

theorem openRows_real_accepted (C : PrimitiveOracle) (iv : Digest32)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) (out : Opened)
    (accepted : (runReal C iv (openRows proof root numLeaves queries rowWords leafWords base)).view.result = some out) :
    proof.open (PublicMerkleLog.hash C) root numLeaves queries rowWords leafWords = some out.paths ∧
      decodeRows base rowWords leafWords out.paths = some out.rows := by
  rw [openRows_real] at accepted
  cases opened : proof.open (PublicMerkleLog.hash C) root numLeaves queries rowWords leafWords with
  | none => simp [opened] at accepted
  | some paths =>
    cases decoded : decodeRows base rowWords leafWords paths with
    | none => simp [opened,decoded] at accepted
    | some rows =>
      simp only [opened,Option.bind_some,decoded,Option.map_some,Option.some.injEq] at accepted
      subst out
      exact ⟨rfl,decoded⟩

private theorem wordsBytes_length (words : List K) : (ByteCodec.wordsBytes words).length = 8 * words.length := by
  induction words with
  | nil => rfl
  | cons x xs ih =>
    simp only [ByteCodec.wordsBytes,List.flatMap_cons,List.length_append,List.length_ofFn,List.length_cons] at *
    omega

private theorem opening_input_bounds (C : PrimitiveOracle) {address : List Bool}
    (path : MerkleBinding.Opening (List K) Digest32 address) (leafWords limit : Nat)
    (rowLength : path.row.length = leafWords) (size : 8 * leafWords < limit) (pairSize : 64 < limit) :
    ∀ bytes ∈ path.inputs (hashing (PublicMerkleLog.hash C)), bytes.length < limit := by
  induction path with
  | leaf words =>
    intro bytes h
    simp only [MerkleBinding.Opening.inputs,Finset.mem_singleton] at h
    subst bytes
    change words.length = leafWords at rowLength
    simpa only [hashing,wordsBytes_length,rowLength] using size
  | node right sibling child ih =>
    intro bytes h
    simp only [MerkleBinding.Opening.inputs,Finset.mem_insert] at h
    rcases h with equal | member
    · subst bytes
      simpa [hashing] using pairSize
    · exact ih rowLength bytes member

theorem path_input_bounds_lt (C : PrimitiveOracle) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat) (rowWords leafWords limit : Nat)
    (paths : List RawPath)
    (accepted : proof.open (PublicMerkleLog.hash C) root numLeaves queries rowWords leafWords = some paths)
    (size : 8 * leafWords < limit) (pairSize : 64 < limit) :
    ∀ p ∈ paths, ∀ bytes ∈ p.opening.inputs (hashing (PublicMerkleLog.hash C)), bytes.length < limit := by
  have refined := open_refines _ _ _ _ _ _ _ _ accepted
  intro p member
  obtain ⟨q,_,hp⟩ := forall₂_mem_right refined member
  obtain ⟨stored,_,_,_,_,length,_,_⟩ := hp
  have rowLength : p.opening.row.length = leafWords := by simpa only [RawPath.opening_row] using length
  exact opening_input_bounds C p.opening leafWords limit rowLength size pairSize

theorem path_input_bounds (C : PrimitiveOracle) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves : Nat) (queries : List Nat) (rowWords leafWords : Nat)
    (paths : List RawPath)
    (accepted : proof.open (PublicMerkleLog.hash C) root numLeaves queries rowWords leafWords = some paths)
    (size : 8 * leafWords < 2^64) :
    ∀ p ∈ paths, ∀ bytes ∈ p.opening.inputs (hashing (PublicMerkleLog.hash C)), bytes.length < 2^64 :=
  path_input_bounds_lt C proof root numLeaves queries rowWords leafWords (2^64) paths accepted size (by decide)

private theorem maps_of_forall₂ {A B D : Type} (left : A → D) (right : B → D)
    {xs : List A} {ys : List B} (same : List.Forall₂ (fun x y => left x = right y) xs ys) :
    xs.map left = ys.map right := by
  induction same with
  | nil => rfl
  | cons equal rest ih => simp only [List.map_cons,equal,ih]

def atQueries (oracle : Oracle) (queries : List Nat) : Oracle :=
  (queries.map (fun q => oracle[q]!)).toArray

private theorem liftRoot_get (root : CausalGame.BaseOracle) (q : Nat) (h : q < root.size) :
    (CausalGame.liftRoot root)[q]! = root[q]!.map E.ofK := by
  simp [CausalGame.liftRoot,getElem!_pos,h]

theorem decode_base_bound (hash : Primitive) (snapshot : Snapshot)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (lanes leafWords : Nat) (paths : List RawPath)
    (accepted : proof.open hash root numLeaves queries lanes leafWords = some paths)
    (bound : ∀ p ∈ paths, p.leafData = row hash snapshot root numLeaves.log2 p.leafIndex) :
    decodeRows true lanes leafWords paths = some (atQueries
      (CausalGame.liftRoot (compactBaseOracle hash snapshot root numLeaves.log2 numLeaves leafWords lanes)) queries) := by
  have good := open_compact_rows hash snapshot proof root numLeaves queries lanes leafWords paths accepted bound
  have conditions := ((open_spec _ _ _ _ _ _ _ _).mp accepted).1
  let oracle := CausalGame.liftRoot (compactBaseOracle hash snapshot root numLeaves.log2 numLeaves leafWords lanes)
  have mapped : List.Forall₂ (fun q p =>
      oracle[q]! = ((p.leafData.drop (leafWords-lanes)).map E.ofK).toArray) queries paths := by
    apply List.forall₂_of_length_eq_of_get good.length_eq
    intro i hi hp
    have hq := conditions.range (queries.get ⟨i,hi⟩) (List.get_mem _ _)
    rw [show oracle = CausalGame.liftRoot (compactBaseOracle hash snapshot root numLeaves.log2 numLeaves leafWords lanes) from rfl,
      liftRoot_get _ _ (by simpa only [compactBaseOracle_size] using hq)]
    simpa using (congrArg (fun a : Array K => a.map E.ofK) (good.get hi hp)).symm
  have same := maps_of_forall₂ (fun q => oracle[q]!)
    (fun p : RawPath => ((p.leafData.drop (leafWords-lanes)).map E.ofK).toArray) mapped
  simpa [decodeRows,atQueries,oracle] using congrArg (fun xs => some xs.toArray) same.symm

/-- A real accepted physical base opening either supplies exactly the frozen
occupied lanes, or supplies a concrete ordinary-compression bad witness. -/
theorem openRows_base_binding (C : PrimitiveOracle) (iv : Digest32)
    (oldLog : PublicMerkleLog.PublicLog) (auth : PublicMerkleLog.AuthenticLog C oldLog)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain (PublicMerkleLog.records oldLog))
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (lanes leafWords : Nat) (size : 8 * leafWords < 2^64) (out : Opened)
    (accepted : (runReal C iv (openRows proof root numLeaves queries lanes leafWords true)).view.result = some out) :
    out.rows = atQueries (CausalGame.liftRoot
      (compactBaseOracle (PublicMerkleLog.hash C) snapshot root numLeaves.log2 numLeaves leafWords lanes)) queries ∨
      PublicMerkleBinding.OpenPrimitiveBad C oldLog root out.paths := by
  obtain ⟨opened,decoded⟩ := openRows_real_accepted C iv proof root numLeaves queries lanes leafWords true out accepted
  have frozen := (PublicMerkleBinding.open_frozen_public C oldLog auth [(root,snapshot)] []
    root snapshot table (by simp [Commitments.lookup]) proof numLeaves queries lanes leafWords out.paths
    (path_input_bounds C proof root numLeaves queries lanes leafWords out.paths opened size) opened).2
  rcases frozen with good | bad
  · exact Or.inl (Option.some.inj (decoded.symm.trans
      (decode_base_bound _ snapshot proof root numLeaves queries lanes leafWords out.paths opened good)))
  · exact Or.inr bad

private theorem collect_right {A B D : Type} (f : B → Option D) (g : A → D)
    {qs : List A} {ps : List B} (same : List.Forall₂ (fun q p => f p = some (g q)) qs ps) :
    collect f ps = some (qs.map g) := by
  induction same with
  | nil => rfl
  | cons equal rest ih => simp [collect,equal,ih]

theorem openRows_extension_binding (C : PrimitiveOracle) (iv : Digest32)
    (oldLog : PublicMerkleLog.PublicLog) (auth : PublicMerkleLog.AuthenticLog C oldLog)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain (PublicMerkleLog.records oldLog))
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (width : Nat) (size : 8 * (3*width) < 2^64) (out : Opened)
    (accepted : (runReal C iv (openRows proof root numLeaves queries (3*width) (3*width) false)).view.result = some out) :
    out.rows = atQueries
      (intermediateOracle (PublicMerkleLog.hash C) snapshot root numLeaves.log2 numLeaves width) queries ∨
      PublicMerkleBinding.OpenPrimitiveBad C oldLog root out.paths := by
  obtain ⟨opened,decoded⟩ := openRows_real_accepted C iv proof root numLeaves queries (3*width) (3*width) false out accepted
  rcases open_intermediate_rows (PublicMerkleLog.hash C) snapshot proof root numLeaves queries width out.paths opened with good | bad
  · have collected := collect_right _ _ good
    have rows : decodeRows false (3*width) (3*width) out.paths = some (atQueries
        (intermediateOracle (PublicMerkleLog.hash C) snapshot root numLeaves.log2 numLeaves width) queries) := by
      simp [decodeRows,collected,atQueries,List.map_map,Function.comp_def]
    exact Or.inl (Option.some.inj (decoded.symm.trans rows))
  · exact Or.inr (PublicMerkleBinding.openBad_primitive C oldLog auth snapshot table root out.paths
      (path_input_bounds C proof root numLeaves queries (3*width) (3*width) out.paths opened size) bad)

/-- Historical first-record tables may retain entries reconstructed at earlier
public prefixes. No decoder coverage assumption is needed: absence of an
observed primitive collision makes their saturated domain exact. -/
theorem openRows_base_retained (C : PrimitiveOracle) (iv : Digest32)
    (oldLog : PublicMerkleLog.PublicLog) (auth : PublicMerkleLog.AuthenticLog C oldLog)
    (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicMerkleLog.PublicLog,
      (∀ q ∈ earlier, q ∈ oldLog) ∧ e ∈ PublicMerkleLog.records earlier)
    (saturated : ∀ bytes d, (bytes,d) ∈ PublicMerkleLog.records oldLog → ∃ first, (bytes,first) ∈ retained)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain retained)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (lanes leafWords : Nat) (size : 8 * leafWords < 2^64) (out : Opened)
    (accepted : (runReal C iv (openRows proof root numLeaves queries lanes leafWords true)).view.result = some out) :
    out.rows = atQueries (CausalGame.liftRoot
      (compactBaseOracle (PublicMerkleLog.hash C) snapshot root numLeaves.log2 numLeaves leafWords lanes)) queries ∨
      PublicMerkleBinding.OpenPrimitiveBad C oldLog root out.paths := by
  classical
  by_cases collision : PublicMerkleLog.OutputCollision oldLog
  · exact Or.inr (Or.inl collision)
  · exact openRows_base_binding C iv oldLog auth snapshot
      (table.trans (PublicMerkleBinding.historical_domain_eq C oldLog auth collision retained history saturated))
      proof root numLeaves queries lanes leafWords size out accepted

theorem openRows_extension_retained (C : PrimitiveOracle) (iv : Digest32)
    (oldLog : PublicMerkleLog.PublicLog) (auth : PublicMerkleLog.AuthenticLog C oldLog)
    (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicMerkleLog.PublicLog,
      (∀ q ∈ earlier, q ∈ oldLog) ∧ e ∈ PublicMerkleLog.records earlier)
    (saturated : ∀ bytes d, (bytes,d) ∈ PublicMerkleLog.records oldLog → ∃ first, (bytes,first) ∈ retained)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain retained)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat) (queries : List Nat)
    (width : Nat) (size : 8 * (3*width) < 2^64) (out : Opened)
    (accepted : (runReal C iv (openRows proof root numLeaves queries (3*width) (3*width) false)).view.result = some out) :
    out.rows = atQueries
      (intermediateOracle (PublicMerkleLog.hash C) snapshot root numLeaves.log2 numLeaves width) queries ∨
      PublicMerkleBinding.OpenPrimitiveBad C oldLog root out.paths := by
  classical
  by_cases collision : PublicMerkleLog.OutputCollision oldLog
  · exact Or.inr (Or.inl collision)
  · exact openRows_extension_binding C iv oldLog auth snapshot
      (table.trans (PublicMerkleBinding.historical_domain_eq C oldLog auth collision retained history saturated))
      proof root numLeaves queries width size out accepted

/-- The public geometry, not adversarially sized proof buffers, bounds all
real and arbitrary ideal branches, including hashes preceding rejection. -/
theorem openRows_counted_uniform (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) :
    Counts (PrunedMerkleProgram.uniformBudget numLeaves queries leafWords)
      (openRows proof root numLeaves queries rowWords leafWords base) := by
  unfold openRows
  rw [← Nat.add_zero (PrunedMerkleProgram.uniformBudget numLeaves queries leafWords)]
  apply WHIRModeFinal.bind_counted
  · exact PrunedMerkleProgram.verify_counted_uniform proof root numLeaves queries rowWords leafWords
  · intro; trivial

def replayOpenRows (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool) (trace : List Observation) :
    Option (Option Opened × List Observation) :=
  ((PrunedMerkleProgram.plan proof root numLeaves queries rowWords leafWords).replay trace).map
    (fun result => (finishRows base rowWords leafWords result.1,result.2))

/-- Public chronological reconstruction is valid even when a stateful ideal
simulator gives different replies to repeated identical primitive inputs. -/
theorem openRows_replay (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool)
    (trace suffix : List Observation) (result : Option Opened)
    (runs : PublicMerkleProgram.Runs (openRows proof root numLeaves queries rowWords leafWords base) trace result) :
    replayOpenRows proof root numLeaves queries rowWords leafWords base (trace++suffix) = some (result,suffix) := by
  obtain ⟨before,value,after,joined,prior,last⟩ :=
    (PublicMerkleProgram.Runs.bind_iff _ _).mp runs
  cases last
  simp only [List.append_nil] at joined
  subst trace
  simp only [replayOpenRows,PrunedMerkleProgram.verify_replay _ _ _ _ _ _ _ _ _ prior,Option.map_some]

theorem openRows_ideal_replay {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (base : Bool)
    (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (openRows proof root numLeaves queries rowWords leafWords base))
    (suffix : List Observation) :
    replayOpenRows proof root numLeaves queries rowWords leafWords base
      ((runIdeal sim ro iv state _ remaining cap counted).view.observations++suffix) =
        some ((runIdeal sim ro iv state _ remaining cap counted).view.result,suffix) :=
  openRows_replay proof root numLeaves queries rowWords leafWords base _ suffix _
    (PublicMerkleProgram.runIdeal_runs sim ro iv state _ remaining cap counted)

/-- Embed the physical queries in source chronology without adding hashes,
preimages, root announcements, or logical catalog metadata. -/
def sourceLift {cap : Nat} {R S : Type} :
    Program R → (R → WHIRSourceChronology.Source cap S) → WHIRSourceChronology.Source cap S
  | .done r, next => next r
  | .ask q cont, next => .ask q (fun answer => sourceLift (cont answer) next)

theorem sourceLift_erase {cap : Nat} {R S : Type} (p : Program R)
    (next : R → WHIRSourceChronology.Source cap S) :
    WHIRSourceChronology.erase (sourceLift p next) =
      WHIRModeFinal.bind p (fun r => WHIRSourceChronology.erase (next r)) := by
  induction p with
  | done => rfl
  | ask q cont ih =>
    simp only [sourceLift,WHIRSourceChronology.erase,WHIRModeFinal.bind]
    congr 1
    funext answer
    exact ih answer

theorem sourceLift_counted {cap : Nat} {R S : Type} (p : Program R)
    (next : R → WHIRSourceChronology.Source cap S) (a b : Nat)
    (before : Counts a p) (after : ∀ r, WHIRSourceChronology.Counts b (next r)) :
    WHIRSourceChronology.Counts (a+b) (sourceLift p next) := by
  have eraseCounts (s : WHIRSourceChronology.Source cap S) (n : Nat) :
      Counts n (WHIRSourceChronology.erase s) ↔ WHIRSourceChronology.Counts n s := by
    induction s generalizing n with
    | done => rfl
    | ask q cont ih => simp only [WHIRSourceChronology.erase,Counts,WHIRSourceChronology.Counts,ih]
    | commit _ _ ih => exact ih n
    | claims _ _ _ _ ih => exact ih n
  apply (eraseCounts _ _).mp
  rw [sourceLift_erase]
  exact WHIRModeFinal.bind_counted p _ a b before (fun r => (eraseCounts _ _).mpr (after r))

def leafWords (p : ParameterBounds.Profile) (i : Nat) : Nat :=
  if i = 0 then 2^(ParameterBounds.config p).folds[0]!
  else 3 * 2^(ParameterBounds.config p).folds[i]!

def queryIndices (p : ParameterBounds.Profile) (i : Fin (ParameterBounds.config p).folds.size)
    (x : CausalProbability.Sample (.query i)) : List Nat :=
  (QueryBatchSoundness.queries
    (CausalGame.remaining (ParameterBounds.config p) i.val + (ParameterBounds.config p).rates[i.val]!)
    (ParameterBounds.config p).queries[i.val]! x.1).toList

def openQuery (p : ParameterBounds.Profile) (i : Fin (ParameterBounds.config p).folds.size)
    (lanes : Nat) (proof : PrunedMerklePaths) (root : Digest32)
    (x : CausalProbability.Sample (.query i)) : Program (Option Opened) :=
  openRows proof root (ParameterBounds.length (ParameterBounds.config p) i.val)
    (queryIndices p i x) (if i.val = 0 then lanes else leafWords p i.val)
    (leafWords p i.val) (i.val == 0)

def queryBudget (p : ParameterBounds.Profile) (i : Nat) : Nat :=
  (PrunedMerkleProgram.leafChunkCost (leafWords p i) +
    (ParameterBounds.length (ParameterBounds.config p) i).log2) *
      (ParameterBounds.config p).queries[i]!

theorem openQuery_counted (p : ParameterBounds.Profile) (i : Fin (ParameterBounds.config p).folds.size)
    (lanes : Nat) (proof : PrunedMerklePaths) (root : Digest32)
    (x : CausalProbability.Sample (.query i)) :
    Counts (queryBudget p i.val) (openQuery p i lanes proof root x) := by
  have size : (queryIndices p i x).length = (ParameterBounds.config p).queries[i.val]! := by
    unfold queryIndices
    rw [Array.length_toList]
    exact QueryBatchSoundness.queries_size _ _ _
  simpa only [openQuery,queryBudget,PrunedMerkleProgram.uniformBudget,size] using
      openRows_counted_uniform proof root (ParameterBounds.length (ParameterBounds.config p) i.val)
        (queryIndices p i x) (if i.val = 0 then lanes else leafWords p i.val)
        (leafWords p i.val) (i.val == 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem production_leaf_byte_tag_zero : ∀ p : ParameterBounds.Profile,
    ∀ i : Fin (ParameterBounds.config p).folds.size, 8 * leafWords p i.val < 2^56 := by
  decide +kernel

theorem production_leaf_byte_limit (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) : 8 * leafWords p i.val < 2^64 :=
  lt_trans (production_leaf_byte_tag_zero p i) (by decide)

structure QueryOpening (p : ParameterBounds.Profile) where
  level : Fin (ParameterBounds.config p).folds.size
  root : Digest32
  sample : CausalProbability.Sample (.query level)
  result : Opened

/-- Scalar state carries only physical proof rows and raw roots. No extracted
oracle occurs in the executable source state. Root fields in `Reply` are
shape markers; the actual digest is retained separately at its read point. -/
structure WireState (p : ParameterBounds.Profile) where
  tape : CausalGame.Tape (ParameterBounds.config p)
  previous : Option (CausalProbability.Coordinate (ParameterBounds.config p))
  replies : Array CausalGame.Reply
  rows : Array Oracle
  roots : Array Digest32
  openings : List (QueryOpening p)
  outputCache : Option Digest32
  lastNonceState : Option DuplexRefinement.State
  initial : Option (RingPCSGame.Prefix × E)

def initialWireState (p : ParameterBounds.Profile) (root : Digest32) : WireState p :=
  ⟨WHIRReplay.zeroTape p,none,#[],#[],#[root],[],none,none,none⟩

def absorbedRoot {c : Config} (q : CausalProbability.Coordinate c) (xs : List E) : Option Digest32 :=
  match q with
  | .fold i j =>
    if j.val+1 = c.folds[i.val]! ∧ i.val+1 < c.folds.size then
      match xs with | [_,_,a,b] => ByteCodec.scalarsToHash (a,b) | _ => none
    else none
  | _ => none

/-- Read the transmitted scalar response before issuing its following squeeze.
Only an actually parsed final-fold root generates a commitment instruction. -/
def absorbResponse {p : ParameterBounds.Profile} (state : WireState p) (pending : WHIRHistory.Pending) :
    Option (WireState p × Option Digest32) :=
  match state.previous with
  | none => if pending.scalars.isEmpty then some (state,none) else none
  | some q => do
    let rows := match q with | .query i => state.rows[i.val]! | _ => #[]
    let response ← WHIRHistory.decodeReplyScalars q (fun _ => #[]) rows pending.scalars
    let root := absorbedRoot q pending.scalars
    let roots := match root with | none => state.roots | some d => state.roots.push d
    some ({state with replies := state.replies.push response, roots},root)

def recordSample {p : ParameterBounds.Profile} (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q) : WireState p :=
  let sampled := {state with
    previous := some q
    tape := CausalProbability.set q state.tape (StackWHIRReplay.projectSample q x)}
  match q, x with
  | .initial, x => {sampled with initial := some x}
  | _, _ => sampled

theorem absorbedRoot_nonfold {c : Config} (q : CausalProbability.Coordinate c)
    (xs : List E) (notFold : ∀ i j, q ≠ .fold i j) : absorbedRoot q xs = none := by
  cases q with
  | fold i j => exact False.elim (notFold i j rfl)
  | _ => rfl

def sampleBudget (p : ParameterBounds.Profile) : CausalProbability.Coordinate (ParameterBounds.config p) → Nat
  | .query i => queryBudget p i.val
  | _ => 0

/-- A query sample immediately consumes its actual flat proof, before the
following intro coefficients are read. Other samples do not inspect Merkle data. -/
def takeSample {p : ParameterBounds.Profile} (lanes : Nat) (proofs : Array PrunedMerklePaths)
    (state : WireState p) (q : CausalProbability.Coordinate (ParameterBounds.config p))
    (x : StackWHIRReplay.Sample q) : Program (Option (WireState p)) :=
  match q, x with
  | .query i, x =>
    if i.val = state.rows.size then
      match proofs[i.val]?, state.roots[i.val]? with
      | some proof, some root =>
        WHIRModeFinal.bind (openQuery p i lanes proof root x) fun opened =>
          .done (opened.map fun out =>
            {recordSample state (.query i) x with
              rows := state.rows.push out.rows,
              openings := ⟨i,root,x,out⟩ :: state.openings})
      | _, _ => .done none
    else .done none
  | q, x => .done (some (recordSample state q x))

theorem takeSample_counted {p : ParameterBounds.Profile} (lanes : Nat)
    (proofs : Array PrunedMerklePaths) (state : WireState p)
    (q : CausalProbability.Coordinate (ParameterBounds.config p)) (x : StackWHIRReplay.Sample q) :
    Counts (sampleBudget p q) (takeSample lanes proofs state q x) := by
  cases q with
  | query i =>
    simp only [takeSample,sampleBudget]
    split
    · cases hp : proofs[i.val]? <;> cases hr : state.roots[i.val]?
      · trivial
      · trivial
      · trivial
      · rw [← Nat.add_zero (queryBudget p i.val)]
        apply WHIRModeFinal.bind_counted
        · exact openQuery_counted p i lanes _ _ x
        · intro; trivial
    · trivial
  | _ => trivial

theorem takeSample_query_accepted {p : ParameterBounds.Profile} (C : PrimitiveOracle) (iv : Digest32)
    (lanes : Nat) (proofs : Array PrunedMerklePaths) (state out : WireState p)
    (i : Fin (ParameterBounds.config p).folds.size) (x : CausalProbability.Sample (.query i))
    (accepted : (runReal C iv (takeSample lanes proofs state (.query i) x)).view.result = some out) :
    ∃ proof root opened, proofs[i.val]? = some proof ∧ state.roots[i.val]? = some root ∧
      i.val = state.rows.size ∧
      (runReal C iv (openQuery p i lanes proof root x)).view.result = some opened ∧
      out = {recordSample state (.query i) x with
        rows := state.rows.push opened.rows
        openings := ⟨i,root,x,opened⟩ :: state.openings} := by
  simp only [takeSample] at accepted
  split at accepted
  next shape =>
    cases hp : proofs[i.val]? with
    | none => simp [hp,runReal] at accepted
    | some proof =>
      cases hr : state.roots[i.val]? with
      | none => simp [hp,hr,runReal] at accepted
      | some root =>
        simp only [hp,hr] at accepted
        rw [WHIRModeFinal.bind_real_result] at accepted
        change ((runReal C iv (openQuery p i lanes proof root x)).view.result.map _) = some out at accepted
        cases result : (runReal C iv (openQuery p i lanes proof root x)).view.result with
        | none => simp [result] at accepted
        | some opened =>
          simp only [result,Option.map_some,Option.some.injEq] at accepted
          exact ⟨proof,root,opened,rfl,rfl,shape,result,accepted.symm⟩
  next => cases accepted

noncomputable def frozenQueryOracle (hash : Primitive) (snapshot : Snapshot)
    (root : Digest32) (p : ParameterBounds.Profile) (level lanes : Nat) : Oracle :=
  let rows := ParameterBounds.length (ParameterBounds.config p) level
  if level = 0 then
    CausalGame.liftRoot (compactBaseOracle hash snapshot root rows.log2 rows (leafWords p level) lanes)
  else
    intermediateOracle hash snapshot root rows.log2 rows (2^(ParameterBounds.config p).folds[level]!)

theorem compactBaseOracle_valid (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows leafWords lanes : Nat) (fits : lanes ≤ leafWords) :
    oracleValid (CausalGame.liftRoot
      (compactBaseOracle hash snapshot root height numRows leafWords lanes)) numRows lanes = true := by
  simp only [oracleValid,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true]
  constructor
  · simp only [CausalGame.liftRoot,Array.size_map,compactBaseOracle_size]
  · intro j hj
    have bound : j < (compactBaseOracle hash snapshot root height numRows leafWords lanes).size := by
      simpa only [CausalGame.liftRoot,Array.size_map] using hj
    have index : j < numRows := by simpa only [compactBaseOracle_size] using bound
    have size := compactBaseOracle_row_size hash snapshot root height numRows leafWords lanes j fits index
    simpa only [getElem!_pos (compactBaseOracle hash snapshot root height numRows leafWords lanes) j bound,
      CausalGame.liftRoot,Array.getElem_map,Array.size_map] using size

theorem intermediateOracle_valid (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (height numRows width : Nat) :
    oracleValid (intermediateOracle hash snapshot root height numRows width) numRows width = true := by
  simp only [oracleValid,Bool.and_eq_true,beq_iff_eq,Array.all_eq_true]
  constructor
  · exact intermediateOracle_size hash snapshot root height numRows width
  · intro j hj
    have index : j < numRows := by simpa only [intermediateOracle_size] using hj
    simpa only [getElem!_pos (intermediateOracle hash snapshot root height numRows width) j hj] using
      intermediateOracle_row_size hash snapshot root height numRows width j index

/-- Geometry is fixed by the extractor, including its missing-preimage branch;
it is not a shape assumption on a virtual commitment supplied by a caller. -/
theorem frozenQueryOracle_valid (hash : Primitive) (snapshot : Snapshot) (root : Digest32)
    (p : ParameterBounds.Profile) (level lanes : Nat)
    (fits : lanes ≤ 2^(ParameterBounds.config p).folds[0]!) :
    oracleValid (frozenQueryOracle hash snapshot root p level lanes)
      (ParameterBounds.length (ParameterBounds.config p) level)
      (if level = 0 then lanes else 2^(ParameterBounds.config p).folds[level]!) = true := by
  by_cases base : level = 0
  · subst level
    simpa only [frozenQueryOracle,leafWords,ite_true] using
      compactBaseOracle_valid hash snapshot root
        (ParameterBounds.length (ParameterBounds.config p) 0).log2
        (ParameterBounds.length (ParameterBounds.config p) 0)
        (2^(ParameterBounds.config p).folds[0]!) lanes fits
  · simpa only [frozenQueryOracle,ite_eq_right base] using
      intermediateOracle_valid hash snapshot root
        (ParameterBounds.length (ParameterBounds.config p) level).log2
        (ParameterBounds.length (ParameterBounds.config p) level)
        (2^(ParameterBounds.config p).folds[level]!)

theorem openQuery_binding (C : PrimitiveOracle) (iv : Digest32)
    (oldLog : PublicMerkleLog.PublicLog) (auth : PublicMerkleLog.AuthenticLog C oldLog)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain (PublicMerkleLog.records oldLog))
    (p : ParameterBounds.Profile) (i : Fin (ParameterBounds.config p).folds.size)
    (lanes : Nat) (proof : PrunedMerklePaths) (root : Digest32)
    (x : CausalProbability.Sample (.query i)) (out : Opened)
    (accepted : (runReal C iv (openQuery p i lanes proof root x)).view.result = some out) :
    out.rows = atQueries (frozenQueryOracle (PublicMerkleLog.hash C) snapshot root p i.val lanes)
      (queryIndices p i x) ∨ PublicMerkleBinding.OpenPrimitiveBad C oldLog root out.paths := by
  by_cases base : i.val = 0
  · have phase : (i.val == 0) = true := by simp [base]
    have opened := openRows_base_binding C iv oldLog auth snapshot table proof root
      (ParameterBounds.length (ParameterBounds.config p) i.val) (queryIndices p i x)
      lanes (leafWords p i.val) (production_leaf_byte_limit p i) out
      (by simpa only [openQuery,ite_eq_left base,phase] using accepted)
    simpa only [frozenQueryOracle,ite_eq_left base] using opened
  · have phase : (i.val == 0) = false := by simp [base]
    have words : leafWords p i.val = 3 * 2^(ParameterBounds.config p).folds[i.val]! := by
      rw [leafWords,ite_eq_right base]
    have opened := openRows_extension_binding C iv oldLog auth snapshot table proof root
      (ParameterBounds.length (ParameterBounds.config p) i.val) (queryIndices p i x)
      (2^(ParameterBounds.config p).folds[i.val]!)
      (by simpa only [words] using production_leaf_byte_limit p i) out
      (by simpa only [openQuery,ite_eq_right base,phase,words] using accepted)
    simpa only [frozenQueryOracle,ite_eq_right base] using opened

theorem openQuery_retained (C : PrimitiveOracle) (iv : Digest32)
    (oldLog : PublicMerkleLog.PublicLog) (auth : PublicMerkleLog.AuthenticLog C oldLog)
    (retained : Records)
    (history : ∀ e ∈ retained, ∃ earlier : PublicMerkleLog.PublicLog,
      (∀ q ∈ earlier, q ∈ oldLog) ∧ e ∈ PublicMerkleLog.records earlier)
    (saturated : ∀ bytes d, (bytes,d) ∈ PublicMerkleLog.records oldLog → ∃ first, (bytes,first) ∈ retained)
    (snapshot : Snapshot) (table : snapshot.table = recordDomain retained)
    (p : ParameterBounds.Profile) (i : Fin (ParameterBounds.config p).folds.size)
    (lanes : Nat) (proof : PrunedMerklePaths) (root : Digest32)
    (x : CausalProbability.Sample (.query i)) (out : Opened)
    (accepted : (runReal C iv (openQuery p i lanes proof root x)).view.result = some out) :
    out.rows = atQueries (frozenQueryOracle (PublicMerkleLog.hash C) snapshot root p i.val lanes)
      (queryIndices p i x) ∨ PublicMerkleBinding.OpenPrimitiveBad C oldLog root out.paths := by
  classical
  by_cases collision : PublicMerkleLog.OutputCollision oldLog
  · exact Or.inr (Or.inl collision)
  · exact openQuery_binding C iv oldLog auth snapshot
      (table.trans (PublicMerkleBinding.historical_domain_eq C oldLog auth collision retained history saturated))
      p i lanes proof root x out accepted

def packetQuery (ctx : RawWHIRKeys.Context) (Q : Nat) (p : ParameterBounds.Profile)
    (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p) :
    CausalProbability.Coordinate (ParameterBounds.config p) :=
  profile ▸ WHIRReplay.query packet.val.profile (packet.val.statement,packet.val.messages)

def packetSample (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q : Nat)
    (p : ParameterBounds.Profile) (packet : RawWHIRKeys.Packet ctx Q)
    (profile : packet.val.profile = p) (raw : RawOracleCoupling.Concrete.GroupAnswer ctx Q (.inl packet)) :
    StackWHIRReplay.Sample (packetQuery ctx Q p packet profile) := by
  subst p
  exact WHIRRawReplay.decodePacket ctx stack Q packet raw

/-- All requested output coordinates are the nonce interpreter's returned
normalized history, whose equality and admissibility are carried by the result. -/
def readPacket (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (nonce : WHIRPowProgram.Outcome ctx Q packet) :
    Program (RawOracleCoupling.Concrete.GroupAnswer ctx Q (.inl packet)) :=
  WHIRModeProgram.readPacket (RawWHIRKeys.blocks ctx packet.val)
    (fun i => .construction (nonce.coordinate i.val) (nonce.coordinate_admissible i)) Program.done

theorem readPacket_eq (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (nonce : WHIRPowProgram.Outcome ctx Q packet) :
    readPacket ctx Q packet nonce =
      WHIRModeProgram.readPacket (RawWHIRKeys.blocks ctx packet.val)
        (WHIRModeFinal.request ctx Q packet) Program.done := by
  unfold readPacket
  congr 1
  funext i
  simp only [WHIRModeFinal.request,WHIRPowProgram.Outcome.coordinate_eq]

theorem readPacket_counted (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (nonce : WHIRPowProgram.Outcome ctx Q packet) :
    Counts (WHIRModeFinal.packetCost ctx Q packet) (readPacket ctx Q packet nonce) := by
  rw [readPacket_eq]
  simpa only [Nat.add_zero,WHIRModeFinal.packetCost,WHIRModeFinal.request,Query.cost] using
    WHIRModeProgram.readPacket_counted (RawWHIRKeys.blocks ctx packet.val)
      (WHIRModeFinal.request ctx Q packet) Program.done 0 (fun _ => True.intro)

/-- #552 production query phases use the public constant17. Difficulty is
not an adversarial scalar field and earns no soundness amplification here. -/
def nonceMatches {c : Config} (q : CausalProbability.Coordinate c) (pending : WHIRHistory.Pending) : Bool :=
  match q, pending.nonce with
  | .query _, some (bits,_) => bits == 17
  | .query _, none => false
  | _, nonce => nonce.isNone

def afterNonce {p : ParameterBounds.Profile} {ctx Q packet}
    (state : WireState p) (nonce : WHIRPowProgram.Outcome ctx Q packet) : Option (WireState p) :=
  match nonce.boundCV with
  | none => some state
  | some _ => state.outputCache.map (fun old =>
      {state with lastNonceState := nonce.state old})

def withOutput {p : ParameterBounds.Profile} (ctx : RawWHIRKeys.Context) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (raw : RawOracleCoupling.Concrete.GroupAnswer ctx Q (.inl packet))
    (state : WireState p) : WireState p :=
  {state with outputCache := some (raw ⟨RawWHIRKeys.blocks ctx packet.val-1,by
    have := RawWHIRKeys.blocks_positive ctx packet.val
    omega⟩)}

def announce {cap : Nat} {R : Type} (root : Option Digest32)
    (next : WHIRSourceChronology.Source cap R) : WHIRSourceChronology.Source cap R :=
  match root with | none => next | some d => .commit d next

def packetBudget (ctx : RawWHIRKeys.Context) (Q : Nat) (p : ParameterBounds.Profile)
    (packet : RawWHIRKeys.Packet ctx Q) (profile : packet.val.profile = p) : Nat :=
  WHIRPowProgram.packetCost ctx packet.val + WHIRModeFinal.packetCost ctx Q packet +
    sampleBudget p (packetQuery ctx Q p packet profile)

def packetsBudget (ctx : RawWHIRKeys.Context) (Q : Nat) (p : ParameterBounds.Profile)
    (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ packet ∈ packets, packet.val.profile = p) : Nat :=
  (packets.attach.map (fun packet => packetBudget ctx Q p packet.val (profiles _ packet.property))).sum

/-- Native final replay interleaves scalar reads, root announcements, complete
nonce verification/binding, output reads and actual pruned openings. Rejection
stops at its source boundary; no future row or message is consulted. -/
def readPhysicalPackets {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (p : ParameterBounds.Profile)
    (lanes : Nat) (proofs : Array PrunedMerklePaths) (reject : R) :
    (packets : List (RawWHIRKeys.Packet ctx Q)) →
    (∀ packet ∈ packets, packet.val.profile = p) → WireState p →
    (WireState p → List (Sigma (RawOracleCoupling.Concrete.GroupAnswer ctx Q)) →
      WHIRSourceChronology.Source cap R) → WHIRSourceChronology.Source cap R
  | [], _, state, next => next state []
  | packet :: packets, profiles, state, next =>
    let profile := profiles packet (by simp)
    let pending := packet.val.messages.headD ⟨[],none⟩
    match absorbResponse state pending with
    | none => .done reject
    | some (absorbed,root) =>
      if packet.val.messages.length = absorbed.replies.size+1 ∧
          nonceMatches (packetQuery ctx Q p packet profile) pending then
        announce root (sourceLift (WHIRPowProgram.verifyPacket ctx Q packet) fun nonce =>
          match afterNonce absorbed nonce with
          | none => .done reject
          | some bound =>
            if nonce.accepted then
              sourceLift (readPacket ctx Q packet nonce) fun raw =>
                sourceLift (takeSample lanes proofs bound (packetQuery ctx Q p packet profile)
                  (packetSample ctx stack Q p packet profile raw)) fun result =>
                  match result with
                  | none => .done reject
                  | some checked =>
                    readPhysicalPackets ctx stack Q p lanes proofs reject packets
                      (fun a ha => profiles a (by simp [ha])) (withOutput ctx Q packet raw checked)
                      (fun final history => next final (⟨.inl packet,raw⟩ :: history))
            else .done reject)
      else .done reject

theorem announce_counted {cap : Nat} {R : Type} (root : Option Digest32)
    (next : WHIRSourceChronology.Source cap R) (budget : Nat) :
    WHIRSourceChronology.Counts budget (announce root next) ↔ WHIRSourceChronology.Counts budget next := by
  cases root <;> rfl

theorem packetsBudget_cons (ctx : RawWHIRKeys.Context) (Q : Nat) (p : ParameterBounds.Profile)
    (packet : RawWHIRKeys.Packet ctx Q) (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ a ∈ packet::packets, a.val.profile = p) :
    packetsBudget ctx Q p (packet::packets) profiles =
      packetBudget ctx Q p packet (profiles packet (by simp)) +
        packetsBudget ctx Q p packets (fun a ha => profiles a (by simp [ha])) := by
  simp [packetsBudget,List.attach_cons,List.map_map,Function.comp_def]

/-- One public bound covers every arbitrary primitive/construction answer,
all malformed proof arrays, failed nonce predicates, and early-reject paths. -/
theorem readPhysicalPackets_counted {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context)
    (stack : ctx.mode = .stack) (Q : Nat) (p : ParameterBounds.Profile)
    (lanes : Nat) (proofs : Array PrunedMerklePaths) (reject : R)
    (packets : List (RawWHIRKeys.Packet ctx Q))
    (profiles : ∀ packet ∈ packets, packet.val.profile = p) (state : WireState p)
    (next : WireState p → List (Sigma (RawOracleCoupling.Concrete.GroupAnswer ctx Q)) →
      WHIRSourceChronology.Source cap R) (budget : Nat)
    (after : ∀ state history, WHIRSourceChronology.Counts budget (next state history)) :
    WHIRSourceChronology.Counts (packetsBudget ctx Q p packets profiles + budget)
      (readPhysicalPackets ctx stack Q p lanes proofs reject packets profiles state next) := by
  induction packets generalizing state next with
  | nil => simpa only [packetsBudget,List.attach_nil,List.map_nil,List.sum_nil,Nat.zero_add,readPhysicalPackets] using after state []
  | cons packet packets ih =>
    rw [packetsBudget_cons]
    simp only [packetBudget,Nat.add_assoc,readPhysicalPackets]
    cases ha : absorbResponse state (packet.val.messages.headD ⟨[],none⟩) with
    | none => trivial
    | some pair =>
      rcases pair with ⟨absorbed,root⟩
      dsimp only
      split
      · rw [announce_counted]
        apply sourceLift_counted
        · exact WHIRPowProgram.verifyPacket_counted ctx Q packet
        · intro nonce
          cases hn : afterNonce absorbed nonce with
          | none => trivial
          | some bound =>
            dsimp only
            split
            · apply sourceLift_counted
              · exact readPacket_counted ctx Q packet nonce
              · intro raw
                apply sourceLift_counted
                · exact takeSample_counted lanes proofs bound _ _
                · intro result
                  cases result with
                  | none => trivial
                  | some checked =>
                    exact ih _ _ _ (fun final history => after final (⟨.inl packet,raw⟩ :: history))
            · trivial
      · trivial

local instance : DecidableEq FiatShamirGame.Terminal := by
  intro a b
  cases a <;> cases b <;> simp <;> infer_instance

local instance : DecidableEq FiatShamirGame.Coordinate := by
  intro a b
  cases a
  cases b
  simp only [FiatShamirGame.Coordinate.mk.injEq]
  infer_instance

/-- Prior caller outputs are read from their exact physical coordinates. The
decoder receives only replies already returned by those public requests. -/
def readCallerInputs {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) :
    List (WHIRModeFinal.CallerPosition ctx Q packet) →
    (FiatShamirGame.Coordinate → Option Digest32) →
    ((FiatShamirGame.Coordinate → Option Digest32) → WHIRSourceChronology.Source cap R) →
    WHIRSourceChronology.Source cap R
  | [], answers, next => next answers
  | q :: qs, answers, next =>
    .ask (.construction q.val (RawWHIRKeys.callerOutput_admissible ctx Q packet q.val q.property))
      (fun answer => readCallerInputs ctx Q packet qs
        (fun key => if key = q.val then some answer else answers key) next)

theorem readCallerInputs_counted {cap : Nat} {R : Type} (ctx : RawWHIRKeys.Context) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (qs : List (WHIRModeFinal.CallerPosition ctx Q packet))
    (answers : FiatShamirGame.Coordinate → Option Digest32)
    (next : (FiatShamirGame.Coordinate → Option Digest32) → WHIRSourceChronology.Source cap R)
    (budget : Nat) (after : ∀ answers, WHIRSourceChronology.Counts budget (next answers)) :
    WHIRSourceChronology.Counts (WHIRModeFinal.callerCost qs + budget)
      (readCallerInputs ctx Q packet qs answers next) := by
  induction qs generalizing answers with
  | nil => simpa only [WHIRModeFinal.callerCost,List.map_nil,List.sum_nil,Nat.zero_add,readCallerInputs] using after answers
  | cons q qs ih =>
    simp only [readCallerInputs,WHIRSourceChronology.Counts,WHIRModeFinal.callerCost,List.map_cons,List.sum_cons,Query.cost]
    refine ⟨by omega,fun answer => ?_⟩
    simpa only [WHIRModeFinal.callerCost,Nat.add_assoc,Nat.add_sub_cancel_left] using
      ih (fun key => if key = q.val then some answer else answers key)

theorem completion_profiles (ctx : RawWHIRKeys.Context) (Q : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) :
    ∀ a ∈ RawOracleCoupling.Concrete.completion ctx Q packet, a.val.profile = packet.val.profile := by
  intro a member
  simp only [RawOracleCoupling.Concrete.completion,List.mem_append,List.mem_singleton] at member
  rcases member with prior | same
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp prior
    rfl
  · subst a
    rfl

structure Verified (ctx : RawWHIRKeys.Context) (Q cap : Nat) (packet : RawWHIRKeys.Packet ctx Q) where
  request : CausalBindingState.ClaimRequest cap packet.val.profile
  wire : WireState packet.val.profile
  history : List (Sigma (RawOracleCoupling.Concrete.GroupAnswer ctx Q))
  nativeShapes : SuccinctRingWeight.FamilyShape (ParameterBounds.config packet.val.profile).logN request.claims.family ∧
    ∀ point ∈ request.claims.points.toList, SuccinctPointWeight.Shape (ParameterBounds.config packet.val.profile).logN point
  acceptance : ∃ (seedBatch : RingPCSGame.Prefix × E) (proof : Opening),
    wire.initial = some seedBatch ∧
    CausalGame.opening (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) wire.tape) wire.replies = .ok proof ∧
    WHIRNativeArithmetic.sourceVerify request.claims.family request.claims.points seedBatch.1 seedBatch.2
      (ParameterBounds.config packet.val.profile)
      (CausalGame.challenges (ParameterBounds.config packet.val.profile) wire.tape) request.lanes proof = .ok () ∧
    let c := ParameterBounds.config packet.val.profile
    let claims := RingPCSGame.transformedClaims (2^c.logN) request.claims.family request.claims.points seedBatch.1
    (claims.all (fun claim => Protocol.shapeValid c request.lanes claim.weight) = true) ∧
      Protocol.shapeValid c request.lanes (CausalGame.batchClaims (2^c.logN) claims seedBatch.2).weight = true

theorem Verified.replies_nonempty {ctx : RawWHIRKeys.Context} {Q cap : Nat}
    {packet : RawWHIRKeys.Packet ctx Q} (v : Verified ctx Q cap packet) : v.wire.replies ≠ #[] := by
  intro empty
  obtain ⟨_,_,_,parsed,_⟩ := v.acceptance
  rw [empty] at parsed
  simp [CausalGame.opening,CausalGame.visibleBatches,CausalGame.checkReplies] at parsed

/-- The only acceptance computation: actual parsed rows, literal transmitted
sumcheck coefficients, native caller weight/target and native saved contexts.
No extracted oracle, dense weight table, or unmetered hash is evaluated here. -/
def finish (ctx : RawWHIRKeys.Context) (Q cap : Nat) (packet : RawWHIRKeys.Packet ctx Q)
    (request : CausalBindingState.ClaimRequest cap packet.val.profile) (state : WireState packet.val.profile)
    (history : List (Sigma (RawOracleCoupling.Concrete.GroupAnswer ctx Q)))
    (nativeShapes : SuccinctRingWeight.FamilyShape (ParameterBounds.config packet.val.profile).logN request.claims.family ∧
      ∀ point ∈ request.claims.points.toList, SuccinctPointWeight.Shape (ParameterBounds.config packet.val.profile).logN point)
    (claimShapes : ∀ (seed : RingPCSGame.Prefix) (lambda : E),
      let c := ParameterBounds.config packet.val.profile
      let claims := RingPCSGame.transformedClaims (2^c.logN) request.claims.family request.claims.points seed
      (claims.all (fun claim => Protocol.shapeValid c request.lanes claim.weight) = true) ∧
        Protocol.shapeValid c request.lanes (CausalGame.batchClaims (2^c.logN) claims lambda).weight = true) :
    Option (Verified ctx Q cap packet) :=
  match initial : state.initial with
  | none => none
  | some (seed,lambda) =>
    let c := ParameterBounds.config packet.val.profile
    let ch := CausalGame.challenges c state.tape
    match parsed : CausalGame.opening c ch state.replies with
    | .error _ => none
    | .ok proof =>
      match accepted : WHIRNativeArithmetic.sourceVerify request.claims.family request.claims.points seed lambda
          c ch request.lanes proof with
      | .error _ => none
      | .ok () => some ⟨request,state,history,nativeShapes,
          ⟨(seed,lambda),proof,initial,parsed,accepted,claimShapes seed lambda⟩⟩

def sourceBudget (ctx : RawWHIRKeys.Context) (Q : Nat) (packet : RawWHIRKeys.Packet ctx Q) : Nat :=
  WHIRModeFinal.callerCost (WHIRModeFinal.callerPositions ctx Q packet) +
    packetsBudget ctx Q packet.val.profile (RawOracleCoupling.Concrete.completion ctx Q packet)
      (completion_profiles ctx Q packet)

/-- One complete honest PCS verification. The base root is announced before
caller outputs; original claims are decoded only after those outputs; each
later commitment is announced at its scalar read. Merkle and nonce calls are
part of this same interaction and this same all-path resource certificate. -/
def verifySource (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q lanes : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (proofs : Array PrunedMerklePaths) :
    WHIRSourceChronology.Source cap (Option (Verified ctx Q cap packet)) :=
  let entry := RawWHIRKeys.entry ctx packet.val
  match WHIRCallerClaims.initialRoot model.layout entry with
  | none => .done none
  | some root =>
    .commit root (readCallerInputs ctx Q packet (WHIRModeFinal.callerPositions ctx Q packet) (fun _ => none)
      (fun answers =>
        match decoded : WHIRCallerClaims.decodeAvailableRequest cap packet.val.profile lanes model.layout entry answers with
        | none => .done none
        | some request =>
          .claims packet.val.profile entry request
            (readPhysicalPackets ctx stack Q packet.val.profile request.lanes proofs none
              (RawOracleCoupling.Concrete.completion ctx Q packet) (completion_profiles ctx Q packet)
              (initialWireState packet.val.profile root)
              (fun state history => .done (finish ctx Q cap packet request state history
                (WHIRCallerSupport.decodeAvailableRequest_nativeShapes model cap packet.val.profile lanes entry answers request decoded)
                (WHIRCallerSupport.decodeAvailableRequest_shapes model cap packet.val.profile lanes entry answers request decoded))))))

theorem verifySource_counted (cap : Nat) (model : WHIRCallerSupport.ProductionLayout)
    (ctx : RawWHIRKeys.Context) (stack : ctx.mode = .stack) (Q lanes : Nat)
    (packet : RawWHIRKeys.Packet ctx Q) (proofs : Array PrunedMerklePaths) :
    WHIRSourceChronology.Counts (sourceBudget ctx Q packet)
      (verifySource cap model ctx stack Q lanes packet proofs) := by
  unfold verifySource
  dsimp only
  split
  · trivial
  · change WHIRSourceChronology.Counts _ (readCallerInputs _ _ _ _ _ _)
    apply readCallerInputs_counted
    intro answers
    split
    · trivial
    · change WHIRSourceChronology.Counts _ (readPhysicalPackets _ _ _ _ _ _ _ _ _ _ _)
      apply readPhysicalPackets_counted ctx stack Q packet.val.profile
        _ proofs none _ (completion_profiles ctx Q packet) _ _ 0
      intro state history
      trivial

end Whir.WHIRPhysicalVerifier
