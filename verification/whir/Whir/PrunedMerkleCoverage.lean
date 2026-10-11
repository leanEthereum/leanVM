import Whir.PrunedMerkleProgram

namespace Whir.PrunedMerkleProgram
open FiatShamirGame Concrete MerkleBinding MerkleLevels
open DuplexModeGame MerkleTransport

theorem HashProgram.calls_bind {R S : Type} (H : Primitive) (p : HashProgram R) (next : R → HashProgram S) :
    (p.bind next).calls H = p.calls H ++ (next (p.eval H)).calls H := by
  induction p with
  | done => rfl
  | hash bytes cont ih => simp only [HashProgram.bind,HashProgram.calls,HashProgram.eval,ih,List.cons_append]

theorem HashProgram.calls_map {R S : Type} (H : Primitive) (p : HashProgram R) (f : R → S) :
    (p.map f).calls H = p.calls H := by
  simp [HashProgram.map,HashProgram.calls_bind,HashProgram.calls]

/-- Every even/odd pair retained by the level walk was actually hashed.
This states provenance, not just equality of recomputed root values. -/
def PairedCoverage (known : Level Digest32) (calls : List (List Byte)) : Prop :=
  ∀ index left right,
    lookup (2*index) known = some left →
    lookup (2*index+1) known = some right →
    pairBytes left right ∈ calls

theorem PairedCoverage.prepend (known : Level Digest32) (calls : List (List Byte))
    (index : Nat) (left right : Digest32) (covered : PairedCoverage known calls) :
    PairedCoverage ((2*index,left)::(2*index+1,right)::known) (pairBytes left right::calls) := by
  intro j l r hl hr
  by_cases same : j = index
  · subst j
    simp only [lookup,ite_true,Option.some.injEq] at hl
    have hn : 2*index+1 ≠ 2*index := by omega
    simp only [lookup,ite_eq_right hn,ite_true,Option.some.injEq] at hr
    subst l
    subst r
    simp
  · have hll : 2*j ≠ 2*index := by omega
    have hlr : 2*j ≠ 2*index+1 := by omega
    have hrl : 2*j+1 ≠ 2*index := by omega
    have hrr : 2*j+1 ≠ 2*index+1 := by omega
    simp only [lookup,ite_eq_right hll,ite_eq_right hlr] at hl
    simp only [lookup,ite_eq_right hrl,ite_eq_right hrr] at hr
    exact List.mem_cons_of_mem _ (covered j l r hl hr)

theorem PairedCoverage.edge {known : Level Digest32} {calls : List (List Byte)}
    (covered : PairedCoverage known calls) {index : Nat} {current other : Digest32}
    (hc : lookup index known = some current)
    (hs : lookup (MerkleLevels.sibling index) known = some other) :
    List.ofFn (ByteCodec.pairBytes (MerkleLevels.orient index current other)) ∈ calls := by
  by_cases even : index % 2 = 0
  · have he : 2*(index/2) = index := by omega
    simpa only [MerkleLevels.orient,ite_eq_left even,pairBytes] using
      covered (index/2) current other (by simpa [he] using hc)
        (by simpa [he,MerkleLevels.sibling,even] using hs)
  · have he : 2*(index/2) = index-1 := by omega
    have ho : 2*(index/2)+1 = index := by omega
    simpa only [MerkleLevels.orient,ite_eq_right even,pairBytes] using
      covered (index/2) other current
        (by simpa [he,MerkleLevels.sibling,even] using hs) (by simpa [ho] using hc)

theorem foldLevel_calls_paired (H : Primitive) (i : Nat) (d e : Digest32)
    (nodes : Level Digest32) (supplied : List Digest32) (even : i%2=0) :
    (foldLevel ((i,d)::(i+1,e)::nodes) supplied).calls H =
      pairBytes d e :: (foldLevel nodes supplied).calls H := by
  rw [foldLevel.eq_def]
  simp only [even,↓reduceIte,emit,HashProgram.calls,HashProgram.calls_map]

theorem foldLevel_calls_even (H : Primitive) (i : Nat) (d s : Digest32)
    (nodes : Level Digest32) (supplied : List Digest32) (even : i%2=0)
    (unpaired : nodes.head?.map Prod.fst ≠ some (i+1)) :
    (foldLevel ((i,d)::nodes) (s::supplied)).calls H =
      pairBytes d s :: (foldLevel nodes supplied).calls H := by
  rw [foldLevel.eq_def]
  cases nodes with
  | nil => simp [even,emit,HashProgram.calls,HashProgram.calls_map]
  | cons x nodes =>
    rcases x with ⟨j,e⟩
    have hn : j ≠ i+1 := by simpa using unpaired
    simp only [even,hn,↓reduceIte,emit,HashProgram.calls,HashProgram.calls_map]

theorem foldLevel_calls_odd (H : Primitive) (i : Nat) (d s : Digest32)
    (nodes : Level Digest32) (supplied : List Digest32) (odd : i%2≠0) :
    (foldLevel ((i,d)::nodes) (s::supplied)).calls H =
      pairBytes s d :: (foldLevel nodes supplied).calls H := by
  rw [foldLevel.eq_def]
  simp only [odd,↓reduceIte,emit,HashProgram.calls,HashProgram.calls_map]

theorem foldLevel_coverage (H : Primitive) (nodes : Level Digest32) (supplied : List Digest32)
    (parents known : Level Digest32) (rest : List Digest32)
    (run : MerkleLevels.foldLevel (fun p => H (List.ofFn (ByteCodec.pairBytes p))) nodes supplied = some (parents,known,rest)) :
    PairedCoverage known ((foldLevel nodes supplied).calls H) := by
  have trace := foldLevel_spec _ _ _ run
  clear run
  induction trace with
  | nil supplied => intro _ _ _ h; simp [lookup] at h
  | paired i d e nodes supplied parents known rest even _ ih =>
    rw [foldLevel_calls_paired H i d e nodes supplied even]
    have he : 2*(i/2) = i := by omega
    simpa only [he] using PairedCoverage.prepend known _ (i/2) d e ih
  | even i d s nodes supplied parents known rest even unpaired _ ih =>
    rw [foldLevel_calls_even H i d s nodes supplied even unpaired]
    have he : 2*(i/2) = i := by omega
    simpa only [he] using PairedCoverage.prepend known _ (i/2) d s ih
  | odd i d s nodes supplied parents known rest odd _ ih =>
    rw [foldLevel_calls_odd H i d s nodes supplied odd]
    have he : 2*(i/2) = i-1 := by omega
    have ho : 2*(i/2)+1 = i := by omega
    have h := PairedCoverage.prepend known _ (i/2) s d ih
    rw [ho,he] at h
    exact h

def ascentInputs (H : Primitive) (index : Nat) (current : Digest32) : List Digest32 → List (List Byte)
  | [] => []
  | other::rest =>
    let bytes := List.ofFn (ByteCodec.pairBytes (MerkleLevels.orient index current other))
    bytes :: ascentInputs H (index/2) (H bytes) rest

theorem node_digest (H : Primitive) (index : Nat) (other : Digest32)
    {below : List Bool} (p : Opening (List K) Digest32 below) :
    (Opening.node (MerkleLevels.right index) other p).digest (hashing H) =
      H (List.ofFn (ByteCodec.pairBytes (MerkleLevels.orient index (p.digest (hashing H)) other))) := by
  simp only [Opening.digest,hashing,MerkleLevels.orient,MerkleLevels.right]
  by_cases even : index%2=0
  · simp [even]
  · have odd : index%2=1 := by omega
    simp [odd]

theorem node_inputs (H : Primitive) (index : Nat) (other : Digest32)
    {below : List Bool} (p : Opening (List K) Digest32 below) :
    (Opening.node (MerkleLevels.right index) other p).inputs (hashing H) =
      insert (List.ofFn (ByteCodec.pairBytes (MerkleLevels.orient index (p.digest (hashing H)) other))) (p.inputs (hashing H)) := by
  simp only [Opening.inputs,hashing,MerkleLevels.orient,MerkleLevels.right]
  by_cases even : index%2=0
  · simp [even]
  · have odd : index%2=1 := by omega
    simp [odd]

theorem wrap_inputs_coverage (H : Primitive) (index : Nat) (siblings : List Digest32)
    {below : List Bool} (p : Opening (List K) Digest32 below)
    (bytes : List Byte) (member : bytes ∈ (wrap index siblings p).inputs (hashing H)) :
    bytes ∈ p.inputs (hashing H) ∨ bytes ∈ ascentInputs H index (p.digest (hashing H)) siblings := by
  induction siblings generalizing index below with
  | nil => exact Or.inl member
  | cons other rest ih =>
    have h := ih (index/2) (.node (MerkleLevels.right index) other p) member
    rw [node_inputs,node_digest] at h
    rcases h with h | h
    · rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem levels_path_coverage (H : Primitive) (n : Nat) (nodes : Level Digest32)
    (supplied : List Digest32) (final : Level Digest32) (known : List (Level Digest32)) (rest : List Digest32)
    (run : runLevels (fun p => H (List.ofFn (ByteCodec.pairBytes p))) n nodes supplied = some (final,known,rest))
    (sorted : Sorted nodes) (index : Nat) (digest : Digest32)
    (start : lookup index nodes = some digest) (path : List Digest32)
    (reconstructed : reconstruct index known = some path) :
    ∀ bytes ∈ ascentInputs H index digest path, bytes ∈ (levels n nodes supplied).calls H := by
  induction n generalizing nodes supplied final known rest index digest path with
  | zero =>
    simp [runLevels] at run
    rcases run with ⟨rfl,rfl,rfl⟩
    simp [reconstruct] at reconstructed
    subst path
    simp [ascentInputs]
  | succ n ih =>
    simp [runLevels,Option.bind_eq_some_iff,-List.ofFn_succ] at run
    obtain ⟨parents,current,remain,hfold,later,hrun,rfl⟩ := run
    have facts := foldLevel_invariant _ sorted hfold
    obtain ⟨other,hs,hparent⟩ := facts.edge start
    have hs' : binaryLookup (MerkleTransport.sibling index) current = some other :=
      (binaryLookup_eq_lookup _ _ facts.known_sorted).trans hs
    simp [reconstruct,hs',Option.bind_eq_some_iff] at reconstructed
    obtain ⟨tail,htail,rfl⟩ := reconstructed
    have htailCoverage := ih parents remain final later rest hrun facts.parents_sorted
      (index/2) _ hparent tail htail
    have hpair := (foldLevel_coverage H nodes supplied parents current remain hfold).edge
      (facts.preserved start) hs
    intro bytes member
    rw [levels,HashProgram.calls_bind,foldLevel_eval,hfold]
    simp only [HashProgram.calls_map,List.mem_append]
    rcases List.mem_cons.mp member with rfl | member
    · exact Or.inl hpair
    · exact Or.inr (htailCoverage bytes member)

theorem leafHashes_calls (H : Primitive) (rowWords leafWords : Nat) (rows : List (List K))
    (widths : ∀ row ∈ rows, row.length = rowWords) :
    (leafHashes rowWords leafWords rows).calls H =
      rows.map (fun row => ByteCodec.wordsBytes (leafImage 0 leafWords row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hw := widths row (by simp)
    have ht : ∀ r ∈ rows, r.length = rowWords := fun r hr => widths r (by simp [hr])
    simp only [leafHashes,hw,↓reduceIte,HashProgram.calls,HashProgram.calls_map,List.map_cons,ih ht]

theorem plan_calls (H : Primitive) (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat)
    (conditions : OpenConditions proof numLeaves queries rowWords leafWords) :
    (plan proof root numLeaves queries rowWords leafWords).calls H =
      proof.leafData.map (fun row => ByteCodec.wordsBytes (leafImage 0 leafWords row)) ++
        (levels numLeaves.log2 (leafNodes H leafWords (leafTable queries proof.leafData))
          proof.siblingHashes).calls H := by
  have hs : ¬(numLeaves=0 ∨ 2^numLeaves.log2≠numLeaves ∨ queries=[]) := by
    simp [conditions.positive,conditions.power,conditions.queries_nonempty]
  have hc : ¬((sortedUnique queries).length ≠ proof.leafData.length ∨ rowWords>leafWords) := by
    simp [conditions.count,Nat.not_lt.mpr conditions.fits]
  have hr : ¬∃ q ∈ queries, numLeaves ≤ q := by
    rintro ⟨q,hq,hn⟩
    have := conditions.range q hq
    omega
  simp only [plan,ite_eq_right hs,ite_eq_right hc,HashProgram.calls_bind,
    leafHashes_calls H rowWords leafWords proof.leafData conditions.widths,leafHashes_eval,
    ite_eq_left conditions.widths,ite_eq_right hr,HashProgram.calls_map,zip_hashes,leafTable]

theorem plan_opening_inputs (H : Primitive) (proof : PrunedMerklePaths) (root : Digest32)
    (numLeaves : Nat) (queries : List Nat) (rowWords leafWords : Nat) (paths : List RawPath)
    (accepted : proof.open H root numLeaves queries rowWords leafWords = some paths)
    (p : RawPath) (member : p ∈ paths) (bytes : List Byte)
    (input : bytes ∈ p.opening.inputs (hashing H)) :
    bytes ∈ (plan proof root numLeaves queries rowWords leafWords).calls H := by
  obtain ⟨conditions,final,known,index,distinct,hrun,hroot,hdistinct,hpaths⟩ :=
    (open_spec H proof root numLeaves queries rowWords leafWords paths).mp accepted
  have hsorted := leafTable_sorted queries proof.leafData conditions.count
  have hdSorted := distinctPaths_sorted leafWords known _ distinct hdistinct hsorted
  obtain ⟨q,hq,hlookup⟩ := collect_mem _ queries paths hpaths member
  rw [binaryLookup_eq_lookup _ _ hdSorted] at hlookup
  obtain ⟨row,hrow,hindex,hdata,hpath⟩ :=
    distinctPaths_mem leafWords known _ distinct hdistinct q p (lookup_mem hlookup)
  have hstart := leafNodes_lookup H leafWords _ q row (lookup_of_mem hsorted hrow)
  have hcoverage := levels_path_coverage H numLeaves.log2 _ proof.siblingHashes final known [] hrun
    (leafNodes_sorted H leafWords _ hsorted) q _ hstart p.path hpath
  rw [plan_calls H proof root numLeaves queries rowWords leafWords conditions]
  apply List.mem_append.mpr
  rcases wrap_inputs_coverage H p.leafIndex p.path (.leaf p.leafData) bytes input with base | above
  · left
    simp only [Opening.inputs,hashing,Finset.mem_singleton] at base
    rw [base,hdata]
    exact List.mem_map.mpr ⟨row,(leafTable_mem hrow).2,rfl⟩
  · right
    apply hcoverage bytes
    simpa only [Opening.digest,hashing,hindex,hdata] using above

/-- Every primitive invocation needed by any accepted reconstructed opening
is already present in the actual metered flat decoder trace. No independent
path hashing or assumed decoder-coverage bridge is used in this reduction. -/
theorem verify_opening_primitive_coverage (C : PrimitiveOracle) (iv : Digest32)
    (proof : PrunedMerklePaths) (root : Digest32) (numLeaves : Nat)
    (queries : List Nat) (rowWords leafWords : Nat) (paths : List RawPath)
    (accepted : (runReal C iv (verify proof root numLeaves queries rowWords leafWords)).view.result = some paths)
    (p : RawPath) (member : p ∈ paths) (bytes : List Byte)
    (input : bytes ∈ p.opening.inputs (hashing (PublicMerkleLog.hash C)))
    (event : DuplexFraming.Node × Digest32) (present : event ∈ PublicMerkleLog.plan C bytes) :
    (⟨.primitive .verification event.1,event.2⟩ : Observation) ∈
      (runReal C iv (verify proof root numLeaves queries rowWords leafWords)).view.observations := by
  rw [verify_real_result] at accepted
  have hb := plan_opening_inputs (PublicMerkleLog.hash C) proof root numLeaves queries rowWords leafWords
    paths accepted p member bytes input
  rw [verify_real_observations]
  exact List.mem_flatMap.mpr ⟨bytes,hb,List.mem_map.mpr ⟨event,present,rfl⟩⟩

end Whir.PrunedMerkleProgram

namespace Whir.PublicMerkleProgram
open FiatShamirGame DuplexModeGame

theorem runReal_answers {R : Type} (C : PrimitiveOracle) (iv : Digest32) (p : Program R) :
    ∀ o ∈ (runReal C iv p).view.observations, o.answer = realAnswer C iv o.query := by
  induction p with
  | done => simp [runReal]
  | ask q next ih =>
    intro o member
    simp only [runReal,prepend,List.mem_cons] at member
    rcases member with rfl | member
    · rfl
    · exact ih (realAnswer C iv q) o member

/-- An operational subtrace identifies the real result only after each
observed answer has been justified against the real query semantics. -/
theorem Runs.real_view {R : Type} {p : Program R} {trace : List Observation} {result : R}
    (run : Runs p trace result) (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ trace, o.answer = realAnswer C iv o.query) :
    (runReal C iv p).view = ⟨trace,result⟩ := by
  induction run with
  | done r => rfl
  | @ask q next trace result answer run ih =>
    have ha : answer = realAnswer C iv q := answers ⟨q,answer⟩ (by simp)
    have ht : ∀ o ∈ trace, o.answer = realAnswer C iv o.query :=
      fun o ho => answers o (List.mem_cons_of_mem _ ho)
    simp only [runReal,←ha,prepend,ih ht]

theorem Runs.real_result_trace {R : Type} {p : Program R} {trace : List Observation} {result : R}
    (run : Runs p trace result) (C : PrimitiveOracle) (iv : Digest32)
    (answers : ∀ o ∈ trace, o.answer = realAnswer C iv o.query) :
    (runReal C iv p).view.result = result ∧ (runReal C iv p).view.observations = trace := by
  have h := run.real_view C iv answers
  exact ⟨congrArg View.result h,congrArg View.observations h⟩

end Whir.PublicMerkleProgram
