import Whir.PublicMerkleProgram
import Whir.MerkleTransport

/-! Physical baseline octopus verification. Whole-hash requests below lower to
ordinary BLAKE2s compression requests, not a second hash oracle. Leaf rows are
checked/hashed one at a time; parent hashes precede the next adjacent group.
Rejected continuations therefore retain every primitive call already made.
No independent-path rehashing is performed. -/
namespace Whir.PrunedMerkleProgram
open FiatShamirGame Concrete MerkleBinding MerkleLevels
open DuplexModeGame MerkleTransport

/-- An internal syntax for sequencing whole-hash computations. Its only
interpreter into the physical game is `lower`, which expands every chunk. -/
inductive HashProgram (R : Type) where
  | done (result : R)
  | hash (bytes : List Byte) (next : Digest32 → HashProgram R)

namespace HashProgram
variable {R S : Type}

def bind : HashProgram R → (R → HashProgram S) → HashProgram S
  | .done r, next => next r
  | .hash bytes next, after => .hash bytes (fun d => bind (next d) after)

def map (f : R → S) (p : HashProgram R) : HashProgram S := bind p (.done ∘ f)

def lower : HashProgram R → Program R
  | .done r => .done r
  | .hash bytes next => WHIRModeFinal.bind (PublicMerkleProgram.hash bytes)
      (fun d => lower (next d))

def eval (H : Primitive) : HashProgram R → R
  | .done r => r
  | .hash bytes next => eval H (next (H bytes))

theorem eval_bind (H : Primitive) (p : HashProgram R) (next : R → HashProgram S) :
    eval H (bind p next) = eval H (next (eval H p)) := by
  induction p with
  | done => rfl
  | hash bytes next ih => exact ih (H bytes)

theorem eval_map (H : Primitive) (f : R → S) (p : HashProgram R) :
    eval H (map f p) = f (eval H p) := eval_bind H p _

theorem lower_real (C : PrimitiveOracle) (iv : Digest32) (p : HashProgram R) :
    (runReal C iv (lower p)).view.result = eval (PublicMerkleLog.hash C) p := by
  induction p with
  | done => rfl
  | hash bytes next ih =>
    rw [lower, PublicMerkleProgram.hash_bind_real_result]
    exact ih _

/-- Exact chronological replay through arbitrary observed replies. -/
def replay : HashProgram R → List Observation → Option (R × List Observation)
  | .done r, trace => some (r,trace)
  | .hash bytes next, trace => do
    let (digest,rest) ← PublicMerkleProgram.replay bytes trace
    replay (next digest) rest

theorem lower_replay (p : HashProgram R) (trace : List Observation) (result : R)
    (run : PublicMerkleProgram.Runs (lower p) trace result) (suffix : List Observation) :
    replay p (trace ++ suffix) = some (result,suffix) := by
  induction p generalizing trace result with
  | done r => cases run; rfl
  | hash bytes next ih =>
    obtain ⟨before,digest,after,he,hb,ha⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp run
    subst trace
    simp only [replay,List.append_assoc,PublicMerkleProgram.hash_replay hb]
    exact ih digest after result ha

/-- Whole-hash provenance is a chronological segmentation of the public
primitive trace, not a first/last-answer map or a consistency premise. -/
inductive PublicRun : HashProgram R → List Observation → R → Prop where
  | done (r : R) : PublicRun (.done r) [] r
  | hash {bytes : List Byte} {next : Digest32 → HashProgram R}
      {before after : List Observation} {digest : Digest32} {result : R} :
      PublicMerkleProgram.Runs (PublicMerkleProgram.hash bytes) before digest →
      PublicRun (next digest) after result →
      PublicRun (.hash bytes next) (before ++ after) result

theorem lower_runs_iff (p : HashProgram R) (trace : List Observation) (result : R) :
    PublicMerkleProgram.Runs (lower p) trace result ↔ PublicRun p trace result := by
  induction p generalizing trace result with
  | done r =>
    constructor
    · intro h; cases h; exact .done r
    · intro h; cases h; exact .done r
  | hash bytes next ih =>
    constructor
    · intro h
      obtain ⟨before,digest,after,he,hb,ha⟩ := (PublicMerkleProgram.Runs.bind_iff _ _).mp h
      subst trace
      exact .hash hb ((ih digest after result).mp ha)
    · intro h
      cases h with
      | hash hb ha =>
        exact (PublicMerkleProgram.Runs.bind_iff _ _).mpr
          ⟨_,_,_,rfl,hb,(ih _ _ _).mpr ha⟩

theorem PublicRun.verification {p : HashProgram R} {trace : List Observation} {result : R}
    (h : PublicRun p trace result) :
    ∀ o ∈ trace, ∃ n, o.query = .primitive .verification n := by
  induction h with
  | done => simp
  | hash hb _ ih =>
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact (PublicMerkleProgram.hash_trace hb).2 o ho
    · exact ih o ho

/-- Real execution's whole-hash requests, in order, including rejecting prefixes. -/
def calls (H : Primitive) : HashProgram R → List (List Byte)
  | .done _ => []
  | .hash bytes next => bytes :: calls H (next (H bytes))

theorem bind_real_observations (C : PrimitiveOracle) (iv : Digest32)
    (p : Program R) (next : R → Program S) :
    (runReal C iv (WHIRModeFinal.bind p next)).view.observations =
      (runReal C iv p).view.observations ++
        (runReal C iv (next (runReal C iv p).view.result)).view.observations := by
  induction p with
  | done => rfl
  | ask q cont ih =>
    simpa only [WHIRModeFinal.bind,runReal,prepend,List.cons_append] using
      congrArg (List.cons (⟨q,realAnswer C iv q⟩ : Observation)) (ih (realAnswer C iv q))

theorem real_observations (C : PrimitiveOracle) (iv : Digest32) (p : HashProgram R) :
    (runReal C iv (lower p)).view.observations =
      (calls (PublicMerkleLog.hash C) p).flatMap (fun bytes =>
        (PublicMerkleLog.plan C bytes).map (fun e => (⟨.primitive .verification e.1,e.2⟩ : Observation))) := by
  induction p with
  | done => rfl
  | hash bytes next ih =>
    rw [lower, bind_real_observations, PublicMerkleProgram.hash_real_observations,
      PublicMerkleProgram.hash_real_result, ih]
    rfl

/-- A compositional all-reply cost/return invariant. The postcondition is
proved by the program, never supplied as a decoder-correctness hypothesis. -/
def Certified (budget : Nat) (post : R → Prop) : HashProgram R → Prop
  | .done r => post r
  | .hash bytes next =>
    (PublicMerkleLog.chunks bytes).length ≤ budget ∧
      ∀ d, Certified (budget - (PublicMerkleLog.chunks bytes).length) post (next d)

theorem Certified.mono {p : HashProgram R} {a b : Nat} {P Q : R → Prop}
    (h : Certified a P p) (budget : a ≤ b) (post : ∀ r, P r → Q r) : Certified b Q p := by
  induction p generalizing a b with
  | done r => exact post r h
  | hash bytes next ih =>
    exact ⟨h.1.trans budget,fun d => ih d (h.2 d) (Nat.sub_le_sub_right budget _)⟩

theorem Certified.bind {p : HashProgram R} {next : R → HashProgram S} {a b : Nat}
    {P : R → Prop} {Q : S → Prop} (before : Certified a P p)
    (after : ∀ r, P r → Certified b Q (next r)) : Certified (a+b) Q (bind p next) := by
  induction p generalizing a with
  | done r => exact (after r before).mono (by omega) (fun _ h => h)
  | hash bytes cont ih =>
    refine ⟨by have := before.1; omega,fun d => ?_⟩
    have h := ih d (before.2 d)
    have he : a+b-(PublicMerkleLog.chunks bytes).length =
        (a-(PublicMerkleLog.chunks bytes).length)+b := by have := before.1; omega
    simpa only [he] using h

theorem Certified.counts {p : HashProgram R} {budget : Nat} {post : R → Prop}
    (h : Certified budget post p) : Counts budget (lower p) := by
  induction p generalizing budget with
  | done => trivial
  | hash bytes next ih =>
    have hh := PublicMerkleProgram.hash_bind_counted bytes (fun d => lower (next d))
      (budget-(PublicMerkleLog.chunks bytes).length) (fun d => ih d (h.2 d))
    exact WHIRModeFinal.counts_mono hh (by have := h.1; omega)

end HashProgram

abbrev LevelResult := Option (Level Digest32 × Level Digest32 × List Digest32)
abbrev LevelsResult := Option (Level Digest32 × List (Level Digest32) × List Digest32)

def pairBytes (left right : Digest32) : List Byte := List.ofFn (ByteCodec.pairBytes (left,right))

theorem pair_cost (left right : Digest32) : (PublicMerkleLog.chunks (pairBytes left right)).length = 1 := by
  rw [PublicMerkleLog.chunks]
  simp [pairBytes]

def leafHashes (rowWords leafWords : Nat) : List (List K) → HashProgram (Option (List Digest32))
  | [] => .done (some [])
  | row :: rows =>
    if row.length = rowWords then
      .hash (ByteCodec.wordsBytes (leafImage 0 leafWords row)) fun digest =>
        (leafHashes rowWords leafWords rows).map (Option.map (digest :: ·))
    else .done none

/-- Hash this adjacent group BEFORE executing the remaining groups. -/
def emit (index : Nat) (left right : Digest32) (tail : HashProgram LevelResult) : HashProgram LevelResult :=
  .hash (pairBytes left right) fun digest => tail.map (Option.map fun (parents,known,rest) =>
    ((index/2,digest)::parents,(2*(index/2),left)::(2*(index/2)+1,right)::known,rest))

def foldLevel : Level Digest32 → List Digest32 → HashProgram LevelResult
  | [], supplied => .done (some ([],[],supplied))
  | (i,d) :: nodes, supplied =>
    if i % 2 = 0 then
      match nodes with
      | (j,e) :: tail =>
        if j = i+1 then emit i d e (foldLevel tail supplied)
        else match supplied with
          | [] => .done none
          | s::ss => emit i d s (foldLevel ((j,e)::tail) ss)
      | [] => match supplied with
        | [] => .done none
        | s::ss => emit i d s (foldLevel [] ss)
    else match supplied with
      | [] => .done none
      | s::ss => emit i s d (foldLevel nodes ss)
termination_by nodes => nodes.length

def levels : Nat → Level Digest32 → List Digest32 → HashProgram LevelsResult
  | 0, nodes, supplied => .done (some (nodes,[],supplied))
  | n+1, nodes, supplied => (foldLevel nodes supplied).bind fun result =>
    match result with
    | none => .done none
    | some (parents,known,rest) => (levels n parents rest).map (Option.map fun (final,ls,tail) =>
        (final,known::ls,tail))

def finish (root : Digest32) (queries : List Nat) (leafWords : Nat)
    (table : Level (List K)) (result : LevelsResult) : Option (List RawPath) := do
  let (final,known,rest) ← result
  if rest ≠ [] then none
  else do
    let (_,computed) ← final.head?
    if computed ≠ root then none
    else do
      let distinct ← distinctPaths leafWords known table
      collect (fun q => MerkleLevels.binaryLookup q distinct) queries

/-- Source order differs from the pure model's equivalent early guards:
`leaf_hashes` may emit a valid prefix before a wrong-width row, and every leaf
is hashed before the sorted-last out-of-range test. -/
def plan (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) : HashProgram (Option (List RawPath)) :=
  if numLeaves = 0 ∨ 2 ^ numLeaves.log2 ≠ numLeaves ∨ queries = [] then .done none
  else if (sortedUnique queries).length ≠ proof.leafData.length ∨ rowWords > leafWords then .done none
  else (leafHashes rowWords leafWords proof.leafData).bind fun hashes =>
    match hashes with
    | none => .done none
    | some hashes =>
      if ∃ q ∈ queries, numLeaves ≤ q then .done none
      else (levels numLeaves.log2 ((sortedUnique queries).zip hashes) proof.siblingHashes).map
        (finish root queries leafWords (leafTable queries proof.leafData))

def verify (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) : Program (Option (List RawPath)) :=
  (plan proof root numLeaves queries rowWords leafWords).lower

theorem leafHashes_eval (H : Primitive) (rowWords leafWords : Nat) (rows : List (List K)) :
    (leafHashes rowWords leafWords rows).eval H =
      if ∀ row ∈ rows, row.length = rowWords then
        some (rows.map fun row => H (ByteCodec.wordsBytes (leafImage 0 leafWords row))) else none := by
  induction rows with
  | nil => simp [leafHashes,HashProgram.eval]
  | cons row rows ih =>
    by_cases hw : row.length = rowWords
    · simp [leafHashes,hw,HashProgram.eval,HashProgram.eval_map,ih]
    · simp [leafHashes,hw,HashProgram.eval]

theorem emit_eval (H : Primitive) (i : Nat) (left right : Digest32) (tail : HashProgram LevelResult) :
    (emit i left right tail).eval H =
      MerkleLevels.emit (fun p => H (List.ofFn (ByteCodec.pairBytes p))) i left right (tail.eval H) := by
  simp [emit,HashProgram.eval,HashProgram.eval_map,MerkleLevels.emit,pairBytes]

theorem foldLevel_eval (H : Primitive) (nodes : Level Digest32) (supplied : List Digest32) :
    (foldLevel nodes supplied).eval H =
      MerkleLevels.foldLevel (fun p => H (List.ofFn (ByteCodec.pairBytes p))) nodes supplied := by
  induction nodes using (measure List.length).wf.induction generalizing supplied with
  | _ nodes ih =>
    cases nodes with
    | nil => simp [foldLevel,MerkleLevels.foldLevel,HashProgram.eval]
    | cons x nodes =>
      rcases x with ⟨i,d⟩
      rw [foldLevel.eq_def,MerkleLevels.foldLevel.eq_def]
      dsimp only
      split
      · cases nodes with
        | nil => cases supplied <;> simp [HashProgram.eval,emit_eval,
            ih [] (by change 0 < 1; omega)]
        | cons y tail =>
          rcases y with ⟨j,e⟩
          dsimp only
          split
          · rw [emit_eval,ih tail (by change tail.length < tail.length+1+1; omega)]
          · cases supplied with
            | nil => rfl
            | cons s ss =>
              rw [emit_eval,ih ((j,e)::tail) (by change tail.length+1 < tail.length+1+1; omega)]
      · cases supplied with
        | nil => rfl
        | cons s ss => rw [emit_eval,ih nodes (by change nodes.length < nodes.length+1; omega)]

theorem levels_eval (H : Primitive) (n : Nat) (nodes : Level Digest32) (supplied : List Digest32) :
    (levels n nodes supplied).eval H =
      runLevels (fun p => H (List.ofFn (ByteCodec.pairBytes p))) n nodes supplied := by
  induction n generalizing nodes supplied with
  | zero => rfl
  | succ n ih =>
    simp only [levels,HashProgram.eval_bind,foldLevel_eval,runLevels]
    cases hf : MerkleLevels.foldLevel (fun p => H (List.ofFn (ByteCodec.pairBytes p))) nodes supplied with
    | none => rfl
    | some triple =>
      rcases triple with ⟨parents,known,rest⟩
      simp [HashProgram.eval_map,ih,Option.map_eq_bind]

theorem zip_hashes (H : Primitive) (leafWords : Nat) (indices : List Nat) (rows : List (List K)) :
    indices.zip (rows.map fun row => H (ByteCodec.wordsBytes (leafImage 0 leafWords row))) =
      leafNodes H leafWords (indices.zip rows) := by
  induction indices generalizing rows with
  | nil => simp [leafNodes]
  | cons i indices ih =>
    cases rows with
    | nil => simp [leafNodes]
    | cons row rows =>
      simpa [leafNodes] using congrArg (List.cons (i,H (ByteCodec.wordsBytes (leafImage 0 leafWords row))))
        (ih rows)

theorem plan_eval (H : Primitive) (proof : PrunedMerklePaths) (root : Digest32)
    (numLeaves : Nat) (queries : List Nat) (rowWords leafWords : Nat) :
    (plan proof root numLeaves queries rowWords leafWords).eval H =
      proof.open H root numLeaves queries rowWords leafWords := by
  by_cases hs : numLeaves = 0 ∨ 2 ^ numLeaves.log2 ≠ numLeaves ∨ queries = []
  · simp [plan,PrunedMerklePaths.open,hs,HashProgram.eval]
  by_cases hc : (sortedUnique queries).length ≠ proof.leafData.length ∨ rowWords > leafWords
  · simp [plan,PrunedMerklePaths.open,hs,hc,HashProgram.eval]
  simp only [plan,PrunedMerklePaths.open,ite_eq_right hs,ite_eq_right hc,HashProgram.eval_bind,leafHashes_eval]
  by_cases hw : ∀ row ∈ proof.leafData, row.length = rowWords
  · simp only [ite_eq_left hw,ite_eq_right (not_not_intro hw)]
    by_cases hr : ∃ q ∈ queries, numLeaves ≤ q
    · simp only [ite_eq_left hr,HashProgram.eval]
    · simp only [ite_eq_right hr,HashProgram.eval_map,levels_eval,zip_hashes]
      rfl
  · simp only [ite_eq_right hw,ite_eq_left hw,HashProgram.eval]

theorem verify_real_result (C : PrimitiveOracle) (iv : Digest32)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) :
    (runReal C iv (verify proof root numLeaves queries rowWords leafWords)).view.result =
      proof.open (PublicMerkleLog.hash C) root numLeaves queries rowWords leafWords := by
  rw [verify,HashProgram.lower_real,plan_eval]

theorem verify_replay (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (trace suffix : List Observation)
    (result : Option (List RawPath))
    (run : PublicMerkleProgram.Runs (verify proof root numLeaves queries rowWords leafWords) trace result) :
    (plan proof root numLeaves queries rowWords leafWords).replay (trace ++ suffix) = some (result,suffix) :=
  HashProgram.lower_replay _ trace result run suffix

theorem verify_real_observations (C : PrimitiveOracle) (iv : Digest32)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) :
    (runReal C iv (verify proof root numLeaves queries rowWords leafWords)).view.observations =
      ((plan proof root numLeaves queries rowWords leafWords).calls (PublicMerkleLog.hash C)).flatMap
        (fun bytes => (PublicMerkleLog.plan C bytes).map
          (fun e => (⟨.primitive .verification e.1,e.2⟩ : Observation))) :=
  HashProgram.real_observations C iv _

theorem HashProgram.Certified.map {R S : Type} {p : HashProgram R} {budget : Nat}
    {P : R → Prop} {Q : S → Prop} (h : HashProgram.Certified budget P p)
    (f : R → S) (post : ∀ r, P r → Q (f r)) :
    HashProgram.Certified budget Q (p.map f) := by
  have hb := h.bind (b := 0) (next := fun r => .done (f r))
    (fun r hr => show HashProgram.Certified 0 Q (.done (f r)) from post r hr)
  simpa only [Nat.add_zero,HashProgram.map,Function.comp_def] using hb

def leafBudget (leafWords : Nat) (rows : List (List K)) : Nat :=
  (rows.map fun row => (PublicMerkleLog.chunks (ByteCodec.wordsBytes (leafImage 0 leafWords row))).length).sum

def Sized {A B : Type} (bound : Nat) (result : Option (List A × B)) : Prop :=
  ∀ value, result = some value → value.1.length ≤ bound

theorem Sized.mono {A B : Type} {a b : Nat} {result : Option (List A × B)}
    (h : Sized a result) (bound : a ≤ b) : Sized b result :=
  fun value hv => (h value hv).trans bound

theorem leafHashes_certified (rowWords leafWords : Nat) (rows : List (List K)) :
    HashProgram.Certified (leafBudget leafWords rows)
      (fun result => ∀ hashes, result = some hashes → hashes.length = rows.length)
      (leafHashes rowWords leafWords rows) := by
  induction rows with
  | nil => simp [leafBudget,leafHashes,HashProgram.Certified]
  | cons row rows ih =>
    by_cases hw : row.length = rowWords
    · simp only [leafHashes,hw,↓reduceIte,HashProgram.Certified,leafBudget,List.map_cons,List.sum_cons]
      refine ⟨by omega,fun digest => ?_⟩
      have h := ih.map (Q := fun result => ∀ hashes, result = some hashes → hashes.length = (row::rows).length)
        (Option.map (digest :: ·)) (by
        intro result hr hashes he
        cases result with
        | none => simp at he
        | some tail =>
          simp only [Option.map_some,Option.some.injEq] at he
          subst hashes
          simp [hr tail rfl])
      simpa [leafBudget] using h
    · simp [leafHashes,hw,HashProgram.Certified]

theorem emit_certified (i : Nat) (left right : Digest32)
    (tail : HashProgram LevelResult) (budget bound : Nat)
    (h : HashProgram.Certified budget (Sized bound) tail) :
    HashProgram.Certified (budget+1) (Sized (bound+1)) (emit i left right tail) := by
  simp only [emit,HashProgram.Certified,pair_cost]
  refine ⟨by omega,fun digest => ?_⟩
  have hm := h.map (Q := Sized (bound+1)) (Option.map fun (parents,known,rest) =>
      ((i/2,digest)::parents,(2*(i/2),left)::(2*(i/2)+1,right)::known,rest)) (by
    intro result hr value he
    cases result with
    | none => simp at he
    | some triple =>
      rcases triple with ⟨parents,known,rest⟩
      simp only [Option.map_some,Option.some.injEq] at he
      subst value
      have hb := hr (parents,known,rest) rfl
      change parents.length ≤ bound at hb
      simp only [List.length_cons]
      omega)
  simpa using hm

theorem foldLevel_certified (nodes : Level Digest32) (supplied : List Digest32) :
    HashProgram.Certified nodes.length (Sized nodes.length) (foldLevel nodes supplied) := by
  induction nodes using (measure List.length).wf.induction generalizing supplied with
  | _ nodes ih =>
    cases nodes with
    | nil => simp [foldLevel,HashProgram.Certified,Sized]
    | cons x nodes =>
      rcases x with ⟨i,d⟩
      rw [foldLevel.eq_def]
      dsimp only
      split
      · cases nodes with
        | nil =>
          cases supplied with
          | nil => simp [HashProgram.Certified,Sized]
          | cons s ss => exact emit_certified i d s _ 0 0 (ih [] (by change 0<1; omega) ss)
        | cons y tail =>
          rcases y with ⟨j,e⟩
          dsimp only
          split
          · have h := emit_certified i d e _ tail.length tail.length
              (ih tail (by change tail.length < tail.length+1+1; omega) supplied)
            exact h.mono (by simp) (fun _ hr => hr.mono (by simp))
          · cases supplied with
            | nil => simp [HashProgram.Certified,Sized]
            | cons s ss =>
              exact emit_certified i d s _ _ _
                (ih ((j,e)::tail) (by change tail.length+1 < tail.length+1+1; omega) ss)
      · cases supplied with
        | nil => simp [HashProgram.Certified,Sized]
        | cons s ss =>
          exact emit_certified i s d _ _ _ (ih nodes (by change nodes.length < nodes.length+1; omega) ss)

theorem levels_certified (n : Nat) (nodes : Level Digest32) (supplied : List Digest32) :
    HashProgram.Certified (n * nodes.length) (Sized nodes.length) (levels n nodes supplied) := by
  induction n generalizing nodes supplied with
  | zero => simp [levels,HashProgram.Certified,Sized]
  | succ n ih =>
    rw [levels,Nat.succ_mul,Nat.add_comm]
    apply (foldLevel_certified nodes supplied).bind (b := n*nodes.length)
    intro result hr
    cases result with
    | none => simp [HashProgram.Certified,Sized]
    | some triple =>
      rcases triple with ⟨parents,known,rest⟩
      have hp := hr (parents,known,rest) rfl
      have hm := (ih parents rest).map (Q := Sized nodes.length)
        (Option.map fun (final,ls,tail) => (final,known::ls,tail)) (by
          intro result hs value he
          cases result with
          | none => simp at he
          | some v =>
            simp only [Option.map_some,Option.some.injEq] at he
            subst value
            exact (hs v rfl).trans hp)
      exact hm.mono (Nat.mul_le_mul_left n hp) (fun _ hs => hs)

/-- Full uncached cost: every declared leaf image's chunk count plus at most
one 64-byte parent compression per active node per level. This bound covers
every reply and rejected continuation, not merely successful paths. -/
def budget (proof : PrunedMerklePaths) (numLeaves leafWords : Nat) : Nat :=
  leafBudget leafWords proof.leafData + numLeaves.log2 * proof.leafData.length

theorem plan_certified (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) :
    HashProgram.Certified (budget proof numLeaves leafWords) (fun _ => True)
      (plan proof root numLeaves queries rowWords leafWords) := by
  unfold plan budget
  split
  · trivial
  · split
    · trivial
    · apply (leafHashes_certified rowWords leafWords proof.leafData).bind
        (b := numLeaves.log2 * proof.leafData.length)
      intro hashes hh
      cases hashes with
      | none => trivial
      | some hashes =>
        dsimp only
        split
        · trivial
        · have hlen := hh hashes rfl
          have h := (levels_certified numLeaves.log2 ((sortedUnique queries).zip hashes)
            proof.siblingHashes).map (Q := fun _ => True)
              (finish root queries leafWords (leafTable queries proof.leafData))
              (fun _ _ => True.intro)
          exact h.mono (Nat.mul_le_mul_left numLeaves.log2
            (by simpa only [List.length_zip,hlen] using Nat.min_le_right (sortedUnique queries).length proof.leafData.length))
            (fun _ _ => True.intro)

theorem verify_counted (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) :
    Counts (budget proof numLeaves leafWords) (verify proof root numLeaves queries rowWords leafWords) :=
  (plan_certified proof root numLeaves queries rowWords leafWords).counts

theorem verify_ideal_replay {Q : Nat} {Seed State : Type} (sim : Simulator Q Seed State)
    (ro : RawKey Q → Digest32) (iv : Digest32) (state : State)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (remaining : Nat) (cap : remaining ≤ Q)
    (counted : Counts remaining (verify proof root numLeaves queries rowWords leafWords))
    (suffix : List Observation) :
    (plan proof root numLeaves queries rowWords leafWords).replay
      ((runIdeal sim ro iv state _ remaining cap counted).view.observations ++ suffix) =
        some ((runIdeal sim ro iv state _ remaining cap counted).view.result,suffix) :=
  verify_replay proof root numLeaves queries rowWords leafWords _ suffix _
    (PublicMerkleProgram.runIdeal_runs sim ro iv state _ remaining cap counted)

theorem verify_public_run (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (trace : List Observation)
    (result : Option (List RawPath))
    (run : PublicMerkleProgram.Runs (verify proof root numLeaves queries rowWords leafWords) trace result) :
    HashProgram.PublicRun (plan proof root numLeaves queries rowWords leafWords) trace result :=
  (HashProgram.lower_runs_iff _ trace result).mp run

theorem verify_verification_queries (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (trace : List Observation)
    (result : Option (List RawPath))
    (run : PublicMerkleProgram.Runs (verify proof root numLeaves queries rowWords leafWords) trace result) :
    ∀ o ∈ trace, ∃ node, o.query = .primitive .verification node :=
  (verify_public_run proof root numLeaves queries rowWords leafWords trace result run).verification

theorem chunks_length_congr (a b : List Byte) (same : a.length = b.length) :
    (PublicMerkleLog.chunks a).length = (PublicMerkleLog.chunks b).length := by
  induction a using (measure List.length).wf.induction generalizing b with
  | _ a ih =>
    conv_lhs => rw [PublicMerkleLog.chunks]
    conv_rhs => rw [PublicMerkleLog.chunks]
    by_cases small : a.length ≤ 64
    · simp only [ite_eq_left small,ite_eq_left (show b.length ≤ 64 by omega),List.length_cons,List.length_nil]
    · simp only [ite_eq_right small,ite_eq_right (show ¬ b.length ≤ 64 by omega),List.length_cons]
      rw [ih (a.drop 64) (by change (a.drop 64).length < a.length; simp; omega)
        (b.drop 64) (by simp [List.length_drop,same])]

theorem wordsBytes_length (words : List K) : (ByteCodec.wordsBytes words).length = words.length * 8 := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp only [ByteCodec.wordsBytes,List.flatMap_cons,List.length_append,List.length_ofFn]
    change 8 + (ByteCodec.wordsBytes words).length = (words.length+1)*8
    rw [ih]
    omega

def leafChunkCost (leafWords : Nat) : Nat :=
  (PublicMerkleLog.chunks (List.replicate (8*leafWords) (0 : Byte))).length

theorem leaf_chunk_cost (leafWords : Nat) (row : List K) (fits : row.length ≤ leafWords) :
    (PublicMerkleLog.chunks (ByteCodec.wordsBytes (leafImage 0 leafWords row))).length = leafChunkCost leafWords := by
  apply chunks_length_congr
  rw [wordsBytes_length,leafImage_length 0 leafWords row fits,List.length_replicate]
  omega

theorem leafHashes_certified_uniform (rowWords leafWords : Nat) (rows : List (List K))
    (fits : rowWords ≤ leafWords) :
    HashProgram.Certified (rows.length * leafChunkCost leafWords)
      (fun result => ∀ hashes, result = some hashes → hashes.length = rows.length)
      (leafHashes rowWords leafWords rows) := by
  induction rows with
  | nil => simp [leafHashes,HashProgram.Certified]
  | cons row rows ih =>
    by_cases hw : row.length = rowWords
    · simp only [leafHashes,hw,↓reduceIte,HashProgram.Certified,
        leaf_chunk_cost leafWords row (by omega),List.length_cons,Nat.add_mul,Nat.one_mul]
      refine ⟨by omega,fun digest => ?_⟩
      have h := ih.map (Q := fun result => ∀ hashes, result = some hashes → hashes.length = (row::rows).length)
        (Option.map (digest :: ·)) (by
          intro result hr hashes he
          cases result with
          | none => simp at he
          | some tail =>
            simp only [Option.map_some,Option.some.injEq] at he
            subst hashes
            simp [hr tail rfl])
      simpa only [Nat.add_sub_cancel,List.length_cons] using h
    · simp [leafHashes,hw,HashProgram.Certified]

/-- Public geometry only: adversarial row count, row widths and sibling count
cannot inflate this all-reply cap because their guards precede offending work. -/
def uniformBudget (numLeaves : Nat) (queries : List Nat) (leafWords : Nat) : Nat :=
  (leafChunkCost leafWords + numLeaves.log2) * queries.length

theorem plan_certified_uniform (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) :
    HashProgram.Certified (uniformBudget numLeaves queries leafWords) (fun _ => True)
      (plan proof root numLeaves queries rowWords leafWords) := by
  unfold plan
  split
  · trivial
  · split
    · trivial
    · rename_i hs hc
      have fits : rowWords ≤ leafWords := by omega
      have count : proof.leafData.length ≤ queries.length := by
        have he : proof.leafData.length = (sortedUnique queries).length := by omega
        rw [he]
        simpa [sortedUnique] using queries.toFinset_card_le
      have h : HashProgram.Certified
          (proof.leafData.length * leafChunkCost leafWords + numLeaves.log2 * proof.leafData.length)
          (fun _ => True)
          ((leafHashes rowWords leafWords proof.leafData).bind fun hashes =>
            match hashes with
            | none => .done none
            | some hashes =>
              if ∃ q ∈ queries, numLeaves ≤ q then .done none
              else (levels numLeaves.log2 ((sortedUnique queries).zip hashes) proof.siblingHashes).map
                (finish root queries leafWords (leafTable queries proof.leafData))) := by
        apply (leafHashes_certified_uniform rowWords leafWords proof.leafData fits).bind
          (b := numLeaves.log2 * proof.leafData.length)
        intro hashes hh
        cases hashes with
        | none => trivial
        | some hashes =>
          dsimp only
          split
          · trivial
          · have hlen := hh hashes rfl
            have h := (levels_certified numLeaves.log2 ((sortedUnique queries).zip hashes)
              proof.siblingHashes).map (Q := fun _ => True)
                (finish root queries leafWords (leafTable queries proof.leafData)) (fun _ _ => True.intro)
            exact h.mono (Nat.mul_le_mul_left numLeaves.log2
              (by simpa only [List.length_zip,hlen] using Nat.min_le_right (sortedUnique queries).length proof.leafData.length))
              (fun _ _ => True.intro)
      apply h.mono ?_ (fun _ _ => True.intro)
      unfold uniformBudget
      nlinarith [Nat.mul_le_mul_left (leafChunkCost leafWords + numLeaves.log2) count]

theorem verify_counted_uniform (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) :
    Counts (uniformBudget numLeaves queries leafWords) (verify proof root numLeaves queries rowWords leafWords) :=
  (plan_certified_uniform proof root numLeaves queries rowWords leafWords).counts

end Whir.PrunedMerkleProgram
