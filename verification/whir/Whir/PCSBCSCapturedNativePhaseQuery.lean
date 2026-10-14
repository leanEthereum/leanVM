import Whir.PCSBCSCapturedIdealNativeAcceptance
import Whir.PCSBCSMerkleRootCacheTransport

/-! Exact historical phase/query crosswalk at ONE captured prefix. No theorem
identifies this table with a later physical registry. Initial occupied lanes may
be any admitted suffix of the full zero-prefixed leaf; extension lanes use all
three limbs, in wire order. Primitive bad alternatives are not discharged.

The next-root projection below concerns the parsed root's captured prefix only.
To apply it to an actual native fold reply one must still establish that reply's
full next table uses this prefix; queried-row binding alone cannot establish that
fact, especially when raw construction prequeries preceded announcement. -/
set_option autoImplicit false
namespace Whir.PCSBCSCapturedNativePhaseQuery
open Concrete Protocol CausalGame CausalProbability FiatShamirGame WHIRHistory
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache PCSBCSMerkleLeafImages
open PCSBCSSourceFrozenAccessor PCSBCSFrozenOracleRows PCSBCSCapturedNativeReplyBridge
open PublicMerkleLog MerkleTransport MerkleTransport.Commitments WHIRPhysicalRows

private theorem fieldWords_lanes (fields : List E) (i : Nat) (inside : i < fields.length) :
    (ByteCodec.fieldWords fields)[3*i]! = fields[i]!.c0 ∧
    (ByteCodec.fieldWords fields)[3*i+1]! = fields[i]!.c1 ∧
    (ByteCodec.fieldWords fields)[3*i+2]! = fields[i]!.c2 := by
  induction fields generalizing i with
  | nil => simp at inside
  | cons x xs ih =>
    cases i with
    | zero => simp [ByteCodec.fieldWords]
    | succ i =>
      have hi : i < xs.length := by simpa using inside
      have index0 : 3*(i+1) = Nat.succ (Nat.succ (Nat.succ (3*i))) := by omega
      have index1 : 3*(i+1)+1 = Nat.succ (Nat.succ (Nat.succ (3*i+1))) := by omega
      have index2 : 3*(i+1)+2 = Nat.succ (Nat.succ (Nat.succ (3*i+2))) := by omega
      simpa only [ByteCodec.fieldWords,List.flatMap_cons,List.append_assoc,
        List.cons_append,List.nil_append,index0,index1,index2,List.getElem!_cons_succ]
        using ih i hi

/-- The array codec and the actual native list codec agree on every limb;
there is no zero-c2 restriction and no reversal or discarded remainder. -/
theorem extensionRow_wordsToFields (words : List K) (fields : List E)
    (decoded : ByteCodec.wordsToFields words = some fields) :
    extensionRow words.toArray = some fields.toArray := by
  have wordsEq := (ByteCodec.fieldWords_wordsToFields words fields decoded).symm
  have size := ByteCodec.wordsToFields_length words fields decoded
  unfold extensionRow
  simp only [List.size_toArray, size, Nat.mul_mod_right, ↓reduceIte]
  congr 1
  apply Array.ext
  · simp only [Array.size_ofFn,List.size_toArray]
    omega
  · intro i hi hj
    have inside : i < fields.length := by simpa using hj
    have limbs := fieldWords_lanes fields i inside
    simp only [Array.getElem_ofFn, List.getElem_toArray]
    rw [wordsEq]
    simp only [List.getElem!_toArray]
    rw [limbs.1, limbs.2.1, limbs.2.2, getElem!_pos fields i inside]

private theorem mapM_of_rows {α β : Type} [Inhabited β]
    (xs : Array α) (f : α → Option β) (ys : Array β)
    (size : ys.size = xs.size)
    (rows : ∀ i : Fin xs.size, f xs[i] = some ys[i.val]!) : xs.mapM f = some ys := by
  rw [Array.mapM_eq_mapM_toList]
  have related : List.Forall₂ (fun x y => f x = some y) xs.toList ys.toList := by
    apply List.forall₂_of_length_eq_of_get (by simpa using size.symm)
    intro i hi hy
    simpa [getElem!_pos, show i < ys.size by simpa using hy] using
      rows ⟨i,by simpa using hi⟩
  have traversal (as : List α) (bs : List β)
      (h : List.Forall₂ (fun x y => f x = some y) as bs) : as.mapM f = some bs := by
    induction h with
    | nil => rfl
    | cons equal _ ih => simp only [List.mapM_cons,equal,ih]; rfl
  rw [traversal _ _ related]
  simp

/-- Full later leaves are consecutive three-word E lanes, including ghost
zero rows. This equation uses exactly the same snapshot, never a later one. -/
theorem extensionOracle_compact_full (hash : Primitive) (snapshot : Snapshot)
    (root : Digest32) (height numRows width : Nat) :
    extensionOracle (compactBaseOracle hash snapshot root height numRows (3*width) (3*width)) =
      some (intermediateOracle hash snapshot root height numRows width) := by
  unfold extensionOracle
  apply mapM_of_rows
  · simp [compactBaseOracle_size,intermediateOracle_size]
  · intro i
    have inside : i.val < numRows := by
      simpa only [compactBaseOracle_size] using i.isLt
    simp only [Fin.getElem_fin]
    rw [← getElem!_pos (compactBaseOracle hash snapshot root height numRows (3*width) (3*width))
      i.val i.isLt]
    rw [compactBaseOracle_get _ _ _ _ _ _ _ _ inside,
      intermediateOracle_get _ _ _ _ _ _ _ inside]
    simp only [compactBaseRow,Nat.sub_self,List.drop_zero]
    exact extensionRow_wordsToFields _ _ (intermediateRow_decoded hash snapshot root height i.val width).1

/-- Exact initial/full-later source/native phase codec at an authentic capture.
For phase zero `occupied` is arbitrary; only later phases are fully occupied. -/
theorem frozenOracle_native (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (p : ParameterBounds.Profile) (root : Digest32) (phase lanes : Nat)
    (auth : AuthenticLog C log) (clean : ¬ OutputCollision log) :
    frozenOracle phase (freeze log root
      ⟨(ParameterBounds.length (ParameterBounds.config p) phase).log2,
        WHIRPhysicalVerifier.leafWords p phase,
        if phase = 0 then lanes else WHIRPhysicalVerifier.leafWords p phase⟩) =
      some (WHIRPhysicalVerifier.frozenQueryOracle (hash C)
        ⟨recordDomain (records log),[]⟩ root p phase lanes) := by
  let ref : Reference := ⟨root,
    ⟨(ParameterBounds.length (ParameterBounds.config p) phase).log2,
      WHIRPhysicalVerifier.leafWords p phase,
      if phase = 0 then lanes else WHIRPhysicalVerifier.leafWords p phase⟩⟩
  have raw := (next_image_provenance C log ref auth clean).2
  change (freeze log root ref.shape).raw = _ at raw
  unfold frozenOracle
  rw [raw]
  have count : 2^(ParameterBounds.length (ParameterBounds.config p) phase).log2 =
      ParameterBounds.length (ParameterBounds.config p) phase := by
    simp [ParameterBounds.length]
  by_cases base : phase = 0
  · simp [ref,base,WHIRPhysicalVerifier.frozenQueryOracle,ParameterBounds.length]
  · simp only [base,↓reduceIte,WHIRPhysicalVerifier.frozenQueryOracle]
    simp only [ref,count,WHIRPhysicalVerifier.leafWords,base,↓reduceIte]
    exact extensionOracle_compact_full _ _ _ _ _ _

/-- Actual typed native samples use the same strided query extraction as the
source parser, including repetitions and the original ordering. -/
theorem queryIndices_derived (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) (x : Sample (.query i)) :
    deriveQueries (remaining (ParameterBounds.config p) i.val + (ParameterBounds.config p).rates[i.val]!)
      (ParameterBounds.config p).queries[i.val]! (Array.ofFn x.1) =
      some (WHIRPhysicalVerifier.queryIndices p i x).toArray := by
  have depth := TapeValidity.config_query_depth (ParameterBounds.config p)
    (ParameterBounds.production_config_valid p).1 i.val i.isLt
  unfold WHIRPhysicalVerifier.queryIndices
  rw [Array.toArray_toList]
  exact QueryBatchSoundness.queries_actual _ _ x.1 (by omega) depth.2

private theorem queryRows_list (oracle : Oracle) (qs : List Nat)
    (bound : ∀ q ∈ qs, q < oracle.size) :
    queryRows oracle qs.toArray = some (WHIRPhysicalVerifier.atQueries oracle qs) := by
  unfold queryRows WHIRPhysicalVerifier.atQueries
  apply mapM_of_rows
  · simp
  · intro i
    have inside : i.val < qs.length := by simpa using i.isLt
    have rowBound := bound qs[i.val] (List.getElem_mem inside)
    change oracle[qs[i.val]]? = some ((qs.map (fun q => oracle[q]!)).toArray)[i.val]!
    rw [getElem!_pos ((qs.map (fun q => oracle[q]!)).toArray) i.val (by simp [inside])]
    simp [rowBound]

/-- Checked source lookup is exactly native read-at-indices, with bounds proved
from the actual typed sampler rather than supplied selected-row equality. -/
theorem queryRows_atQueries (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) (x : Sample (.query i))
    (oracle : Oracle) (size : oracle.size = ParameterBounds.length (ParameterBounds.config p) i.val) :
    queryRows oracle (WHIRPhysicalVerifier.queryIndices p i x).toArray =
      some (WHIRPhysicalVerifier.atQueries oracle (WHIRPhysicalVerifier.queryIndices p i x)) := by
  apply queryRows_list
  intro q member
  have nativeMember : q ∈ QueryBatchSoundness.queries
      (remaining (ParameterBounds.config p) i.val + (ParameterBounds.config p).rates[i.val]!)
      (ParameterBounds.config p).queries[i.val]! x.1 := by
    simpa only [WHIRPhysicalVerifier.queryIndices,Array.mem_def] using member
  obtain ⟨j,hj,same⟩ := Array.mem_iff_getElem.mp nativeMember
  have count : j < (ParameterBounds.config p).queries[i.val]! := by
    rw [← QueryBatchSoundness.queries_size _ _ x.1]
    exact hj
  have queryBound := QueryBatchSoundness.queries_bound
    (remaining (ParameterBounds.config p) i.val + (ParameterBounds.config p).rates[i.val]!)
    (ParameterBounds.config p).queries[i.val]! x.1 j count
  rw [size,← same]
  rw [getElem!_pos (QueryBatchSoundness.queries
    (remaining (ParameterBounds.config p) i.val + (ParameterBounds.config p).rates[i.val]!)
    (ParameterBounds.config p).queries[i.val]! x.1) j hj] at queryBound
  exact queryBound

/-- Exact semantic selected rows whenever the source's padding/status guard
admits them. Authentication of that guard is derived below from native opening
acceptance, not assumed by this pure codec equation. -/
theorem selectPhase_rows (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (p : ParameterBounds.Profile) (root : Digest32) (i : Fin (ParameterBounds.config p).folds.size)
    (lanes : Nat) (x : Sample (.query i))
    (auth : AuthenticLog C log) (clean : ¬ OutputCollision log)
    (selected : Selected)
    (selection : selectPhase i.val (freeze log root
      ⟨(ParameterBounds.length (ParameterBounds.config p) i.val).log2,
        WHIRPhysicalVerifier.leafWords p i.val,
        if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val⟩)
      (WHIRPhysicalVerifier.queryIndices p i x).toArray = some selected) :
    selected.rows = WHIRPhysicalVerifier.atQueries
      (WHIRPhysicalVerifier.frozenQueryOracle (hash C) ⟨recordDomain (records log),[]⟩ root p i.val lanes)
      (WHIRPhysicalVerifier.queryIndices p i x) := by
  obtain ⟨_,oracle,decoded,size,rows⟩ := selectPhase_order _ _ _ _ selection
  have equal := Option.some.inj (decoded.symm.trans
    (frozenOracle_native C log p root i.val lanes auth clean))
  subst oracle
  apply Array.ext
  · simpa [WHIRPhysicalVerifier.atQueries] using size
  · intro j hj hn
    have inside : j < (WHIRPhysicalVerifier.queryIndices p i x).toArray.size := by
      simpa [size] using hj
    have row := rows ⟨j,inside⟩
    simpa [WHIRPhysicalVerifier.atQueries,getElem!_pos,hj] using row

theorem decodeRows_projection (phase rowWords leafWords : Nat)
    (paths : List RawPath) (native : Oracle)
    (later : phase ≠ 0 → rowWords = leafWords)
    (decoded : WHIRPhysicalVerifier.decodeRows (phase == 0) rowWords leafWords paths = some native) :
    List.Forall₂ (fun path row =>
      rowCodec phase (path.leafData.drop (leafWords-rowWords)).toArray = some row)
      paths native.toList := by
  by_cases base : phase = 0
  · simp only [WHIRPhysicalVerifier.decodeRows,base,beq_self_eq_true,↓reduceIte,
      Option.some.injEq] at decoded
    subst native
    induction paths with
    | nil => exact .nil
    | cons path paths ih => exact .cons (by simp [rowCodec,base]) ih
  · simp only [WHIRPhysicalVerifier.decodeRows,show (phase == 0) = false by simp [base],
      Bool.false_eq_true,↓reduceIte] at decoded
    obtain ⟨fields,collected,equal⟩ := Option.map_eq_some_iff.mp decoded
    subst native
    have related := (collect_spec _ _ _).mp collected
    clear collected decoded
    induction related with
    | nil => exact .nil
    | cons h _ ih =>
      apply List.Forall₂.cons _ ih
      simpa [rowCodec,base,later base] using extensionRow_wordsToFields _ _ h

/-- Native accepted openings authenticate the full initial zero prefix before
selecting its occupied suffix. No selected-row equality or source replay is an
input. Later openings authenticate all three limbs of every occupied E lane.
The existing primitive bad branch, including output collision, remains literal. -/
theorem openQuery_selectPhase (C : DuplexModeGame.PrimitiveOracle) (iv : Digest32)
    (log : PublicLog) (auth : AuthenticLog C log) (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) (lanes : Nat)
    (fits : lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (proof : PrunedMerklePaths) (root : Digest32) (x : Sample (.query i))
    (out : WHIRPhysicalVerifier.Opened)
    (accepted : (DuplexModeGame.runReal C iv (WHIRPhysicalVerifier.openQuery p i lanes proof root x)).view.result =
      some out) :
    (∃ selected, selectPhase i.val (freeze log root
      ⟨(ParameterBounds.length (ParameterBounds.config p) i.val).log2,
        WHIRPhysicalVerifier.leafWords p i.val,
        if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val⟩)
      (WHIRPhysicalVerifier.queryIndices p i x).toArray = some selected ∧
      selected.rows = out.rows ∧ selected.queries = (WHIRPhysicalVerifier.queryIndices p i x).toArray ∧
      ∀ cell ∈ selected.cells, cell.available = true ∧ cell.paddingValid = true) ∨
      PublicMerkleBinding.OpenPrimitiveBad C log root out.paths := by
  let shape : Shape := ⟨(ParameterBounds.length (ParameterBounds.config p) i.val).log2,
    WHIRPhysicalVerifier.leafWords p i.val,
    if i.val = 0 then lanes else WHIRPhysicalVerifier.leafWords p i.val⟩
  have shapeFits : shape.occupied ≤ shape.leafWords := by
    dsimp [shape]
    split
    next base => simpa [WHIRPhysicalVerifier.leafWords,base] using fits
    next => exact Nat.le_refl _
  obtain ⟨opened,decoded⟩ := WHIRPhysicalVerifier.openRows_real_accepted C iv proof root
    (ParameterBounds.length (ParameterBounds.config p) i.val)
    (WHIRPhysicalVerifier.queryIndices p i x) shape.occupied shape.leafWords (i.val == 0) out accepted
  have bounds := WHIRPhysicalVerifier.path_input_bounds C proof root
    (ParameterBounds.length (ParameterBounds.config p) i.val)
    (WHIRPhysicalVerifier.queryIndices p i x) shape.occupied shape.leafWords out.paths opened
    (WHIRPhysicalVerifier.production_leaf_byte_limit p i)
  rcases PCSBCSMerkleSourceRows.pruned_opened_compact C log auth root proof
    (ParameterBounds.length (ParameterBounds.config p) i.val) shape.leafWords shape.occupied
    (WHIRPhysicalVerifier.queryIndices p i x) out.paths opened bounds with transport | bad
  · obtain ⟨oracle,oracleDecoded,_⟩ := PCSBCSSourceFrozenAccessorStructural.frozenOracle_freeze
      log root shape shapeFits i.val (by
        by_cases base : i.val = 0
        · exact Or.inl base
        · right; simp [shape,base,WHIRPhysicalVerifier.leafWords])
    have projection := decodeRows_projection i.val shape.occupied shape.leafWords out.paths out.rows
      (by intro later; simp [shape,later]) decoded
    left
    exact select_accepted i.val (freeze log root shape)
      (WHIRPhysicalVerifier.queryIndices p i x).toArray out.paths shape.leafWords shape.occupied
      out.rows oracle oracleDecoded
      (PCSBCSSourceFrozenAccessorStructural.freeze_shape_exact log root shape shapeFits).2.1
      (by simpa [freeze,shape] using transport) projection
  · exact Or.inr bad

/-- Parsed historical next-root roles fix the full later shape. This is the
exact projection required by NativeEvidence.next for the *captured-prefix*
native table, not an identification with the native driver's later table. -/
theorem parsed_next_projection (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (p : ParameterBounds.Profile) (i : Fin (ParameterBounds.config p).folds.size)
    (j : Fin (ParameterBounds.config p).folds[i.val]!) (m : Pending) (ref : Reference)
    (parsed : parsePhase (ParameterBounds.config p) (.fold i j) m (i.val+1) 2 = some ref)
    (auth : AuthenticLog C log) (clean : ¬ OutputCollision log) :
    extensionOracle (compactBaseOracle (hash C) ⟨recordDomain (records log),[]⟩
      ref.root ref.shape.height (2^ref.shape.height) ref.shape.leafWords ref.shape.occupied) =
      some (WHIRPhysicalVerifier.frozenQueryOracle (hash C) ⟨recordDomain (records log),[]⟩
        ref.root p (i.val+1) 0) ∧
    frozenOracle (i.val+1) (freeze log ref.root ref.shape) =
      some (WHIRPhysicalVerifier.frozenQueryOracle (hash C) ⟨recordDomain (records log),[]⟩
        ref.root p (i.val+1) 0) := by
  have shape := (parsePhase_admitted _ _ _ _ _ _ parsed).2.2.2
  have geometry : ref.shape =
      ⟨(ParameterBounds.length (ParameterBounds.config p) (i.val+1)).log2,
        WHIRPhysicalVerifier.leafWords p (i.val+1),
        if i.val+1 = 0 then 0 else WHIRPhysicalVerifier.leafWords p (i.val+1)⟩ := by
    rw [shape]
    simp [phaseShape,ParameterBounds.length,WHIRPhysicalVerifier.leafWords]
  have decoded := frozenOracle_native C log p ref.root (i.val+1) 0 auth clean
  rw [← geometry] at decoded
  refine ⟨?_,decoded⟩
  have raw := (next_image_provenance C log ref auth clean).2
  simpa only [frozenOracle,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,raw] using decoded


private theorem remaining_initial (c : Config) : remaining c 0 = c.logN-c.folds[0]! := by
  have first (xs : List Nat) : (xs.take 1).sum = xs.toArray[0]! := by
    cases xs <;> simp
  change c.logN-(c.folds.toList.take 1).sum = c.logN-c.folds[0]!
  rw [first]

private theorem sameShape_exact (a b : Shape) (same : sameShape a b = true) : a = b := by
  cases a
  cases b
  simp only [sameShape,Bool.and_eq_true,beq_iff_eq] at same
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := same
  rfl

/-- The actual source phase parser admits exactly the native geometry. Initial
lane occupancy is copied from the saved record, not replaced by the full cube. -/
theorem phaseReference_geometry (p : ParameterBounds.Profile) (saved : AnchoredHeaderCodec.Record)
    (messages : List Pending) (phase : Nat) (ref : Reference)
    (reference : phaseReference (ParameterBounds.config p) saved messages phase = some ref) :
    ref.shape = ⟨(ParameterBounds.length (ParameterBounds.config p) phase).log2,
      WHIRPhysicalVerifier.leafWords p phase,
      if phase = 0 then saved.shape.lanes else WHIRPhysicalVerifier.leafWords p phase⟩ := by
  unfold phaseReference at reference
  by_cases base : phase = 0
  · simp only [base,↓reduceIte] at reference
    split at reference
    next compatible =>
      have initial := (parseInitial_admitted saved _ _ ref reference).2.2.2
      rw [initial]
      obtain ⟨logN,batch,rate⟩ := compatible
      simp [initialShape,base,ParameterBounds.length,WHIRPhysicalVerifier.leafWords,
        remaining_initial,logN,batch,rate]
    next => contradiction
  · simp only [base,↓reduceIte] at reference
    split at reference
    next admitted =>
      cases found : (phaseReferences (ParameterBounds.config p) messages)[phase-1]? with
      | none => simp [found] at reference
      | some other =>
        simp only [found,Bind.bind,Option.bind] at reference
        split at reference
        next same =>
          have shape := sameShape_exact other.shape _ same
          cases Option.some.inj reference
          rw [shape]
          simp [phaseShape,ParameterBounds.length,WHIRPhysicalVerifier.leafWords,base]
        next => contradiction
    next => contradiction

/-- Parser-admitted Reference crosswalk; both sides consult its actual captured
log, including earlier raw construction prequeries. -/
theorem phaseReference_frozenOracle (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (p : ParameterBounds.Profile) (saved : AnchoredHeaderCodec.Record)
    (messages : List Pending) (phase : Nat) (ref : Reference)
    (reference : phaseReference (ParameterBounds.config p) saved messages phase = some ref)
    (auth : AuthenticLog C log) (clean : ¬ OutputCollision log) :
    frozenOracle phase (freeze log ref.root ref.shape) =
      some (WHIRPhysicalVerifier.frozenQueryOracle (hash C)
        ⟨recordDomain (records log),[]⟩ ref.root p phase saved.shape.lanes) := by
  rw [phaseReference_geometry p saved messages phase ref reference]
  exact frozenOracle_native C log p ref.root phase saved.shape.lanes auth clean

/-- The full image needed by the source opening is the exact native leaf image,
not a fully-occupied substitute. Compacting it returns the actual native proof. -/
theorem native_openSource_fullImage (hash : Primitive) (proof : PrunedMerklePaths)
    (root : Digest32) (numLeaves rowWords leafWords : Nat) (qs : List Nat)
    (paths : List RawPath)
    (opened : proof.open hash root numLeaves qs rowWords leafWords = some paths) :
    PCSBCSMerkleFullSourceTransport.openSource hash
      ⟨proof.leafData.map (MerkleBinding.leafImage 0 leafWords),proof.siblingHashes⟩
      root numLeaves qs leafWords rowWords = some paths := by
  have conditions := ((open_spec _ _ _ _ _ _ _ _).mp opened).1
  have compact : collect (PCSBCSMerkleFullSourceTransport.compactLeaf leafWords rowWords)
      (proof.leafData.map (MerkleBinding.leafImage 0 leafWords)) = some proof.leafData := by
    apply (collect_spec _ _ _).mpr
    apply List.forall₂_map_left_iff.mpr
    have each : ∀ row ∈ proof.leafData,
        PCSBCSMerkleFullSourceTransport.compactLeaf leafWords rowWords
          (MerkleBinding.leafImage 0 leafWords row) = some row := by
      intro row member
      have width := conditions.widths row member
      simp [PCSBCSMerkleFullSourceTransport.compactLeaf,conditions.fits,
        MerkleBinding.leafImage,width,zeroPrefix_replicate]
    apply List.forall₂_of_length_eq_of_get rfl
    intro n hn hm
    exact each _ (List.getElem_mem hn)
  unfold PCSBCSMerkleFullSourceTransport.openSource PCSBCSMerkleFullSourceTransport.compactProof
  rw [compact]
  exact opened

section SourceQuery
open TypedOracleCompiler PCSStateRestoration.Latent
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
    {R : Type} {count : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Exact query constructor for the parent's ReplyTransport. The source log is
computed by firstMention, and the same-tape sample is read directly from past.
Only real native opening acceptance, literal source reference admission and
authentic captured-prefix evidence remain inputs; neither selected-row equality,
accepted replay nor ReaderTransport is assumed. This local theorem does not
eliminate any enclosing FrozenExtractionBad alternative. -/
theorem source_query_of_native
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R count)
    (table : Table Keys Answers) (C : DuplexModeGame.PrimitiveOracle)
    (current : Coordinate (ParameterBounds.config p)) (saved : AnchoredHeaderCodec.Record)
    (messages : List Pending) (past : WHIRFiatShamir.Prefix current)
    (m : Pending) (digest : Digest32)
    (i : Fin (ParameterBounds.config p).folds.size) (a : Message E)
    (earlier : position (.query i : Coordinate (ParameterBounds.config p)) < position current)
    (ref : Reference)
    (reference : phaseReference (ParameterBounds.config p) saved
      (messages.reverse.take (position (.query i : Coordinate (ParameterBounds.config p))+1)).reverse
      i.val = some ref)
    (auth : AuthenticLog C (sourceLog addresses ref program table))
    (fits : saved.shape.lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (proof : PrunedMerklePaths) (out : WHIRPhysicalVerifier.Opened)
    (accepted : (DuplexModeGame.runReal C iv
      (WHIRPhysicalVerifier.openQuery p i saved.shape.lanes proof ref.root (past (.query i) earlier))).view.result =
      some out) :
    SourceEvidence addresses program table C current saved messages past m digest
      (.query i) (.query out.rows a) ∨
      PublicMerkleBinding.OpenPrimitiveBad C (sourceLog addresses ref program table) ref.root out.paths := by
  let log := sourceLog addresses ref program table
  let x := past (.query i) earlier
  let qs := (WHIRPhysicalVerifier.queryIndices p i x).toArray
  have geometry := phaseReference_geometry p saved _ i.val ref reference
  have shapeFits : ref.shape.occupied ≤ ref.shape.leafWords := by
    rw [geometry]
    dsimp only
    split
    next base => simpa [WHIRPhysicalVerifier.leafWords,base] using fits
    next => exact Nat.le_refl _
  have codec : i.val = 0 ∨ ref.shape.occupied % 3 = 0 := by
    by_cases base : i.val = 0
    · exact Or.inl base
    · right; simp [geometry,base,WHIRPhysicalVerifier.leafWords]
  obtain ⟨opened,decoded⟩ := WHIRPhysicalVerifier.openRows_real_accepted C iv proof ref.root
    (ParameterBounds.length (ParameterBounds.config p) i.val) qs.toList
    ref.shape.occupied ref.shape.leafWords (i.val == 0) out
    (by simpa [qs,geometry,WHIRPhysicalVerifier.openQuery,x] using accepted)
  have full := native_openSource_fullImage (hash C) proof ref.root
    (ParameterBounds.length (ParameterBounds.config p) i.val)
    ref.shape.occupied ref.shape.leafWords qs.toList out.paths opened
  have bounds := WHIRPhysicalVerifier.path_input_bounds C proof ref.root
    (ParameterBounds.length (ParameterBounds.config p) i.val) qs.toList
    ref.shape.occupied ref.shape.leafWords out.paths opened
    (by rw [geometry]; exact WHIRPhysicalVerifier.production_leaf_byte_limit p i)
  have projected := decodeRows_projection i.val ref.shape.occupied ref.shape.leafWords
    out.paths out.rows (by intro later; simp [geometry,later]) decoded
  by_cases bad : PublicMerkleBinding.OpenPrimitiveBad C log ref.root out.paths
  · exact Or.inr bad
  · left
    exact .query i a out.rows earlier ref log reference rfl shapeFits codec qs
      (queryIndices_derived p i x)
      (ParameterBounds.length (ParameterBounds.config p) i.val)
      ⟨proof.leafData.map (MerkleBinding.leafImage 0 ref.shape.leafWords),proof.siblingHashes⟩
      out.paths (by rw [geometry]) auth full bounds bad projected
/-- Actual capture provenance gives the phase codec at the literal stored
prefix, not at a later root announcement or a supplied frozen-oracle callback. -/
theorem captured_phase_oracle
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R count)
    (table : Table Keys Answers) (C : DuplexModeGame.PrimitiveOracle)
    (saved : AnchoredHeaderCodec.Record) (messages : List Pending)
    (phase : Nat) (ref : Reference) (f : Frozen)
    (reference : phaseReference (ParameterBounds.config p) saved messages phase = some ref)
    (captured : PCSBCSSourceRootCapture.capture addresses ref program table = some f)
    (auth : AuthenticLog C f.queryPrefix) (clean : ¬ OutputCollision f.queryPrefix) :
    frozenOracle phase f = some (WHIRPhysicalVerifier.frozenQueryOracle (hash C)
      ⟨recordDomain (records f.queryPrefix),[]⟩ ref.root p phase saved.shape.lanes) := by
  obtain ⟨events,_,frozen,_⟩ := PCSBCSSourceRootCapture.capture_provenance
    addresses ref program table f captured
  have literal : f = freeze f.queryPrefix ref.root ref.shape := by
    rw [frozen]
    rfl
  nth_rw 1 [literal]
  exact phaseReference_frozenOracle C f.queryPrefix p saved messages phase ref reference auth clean

/-- Actual native opening at an actually captured, parser-admitted Reference:
all selected cells authenticate full leaf images, all padded initial shapes are
supported, and query order/repetitions are preserved. The bad case is unchanged. -/
theorem captured_query_selection
    (addresses : Keys → List Reference) (program : Sampling Keys Answers R count)
    (table : Table Keys Answers) (C : DuplexModeGame.PrimitiveOracle)
    (saved : AnchoredHeaderCodec.Record) (messages : List Pending)
    (i : Fin (ParameterBounds.config p).folds.size) (ref : Reference) (f : Frozen)
    (reference : phaseReference (ParameterBounds.config p) saved messages i.val = some ref)
    (captured : PCSBCSSourceRootCapture.capture addresses ref program table = some f)
    (auth : AuthenticLog C f.queryPrefix)
    (fits : saved.shape.lanes ≤ 2^(ParameterBounds.config p).folds[0]!)
    (proof : PrunedMerklePaths) (x : Sample (.query i)) (out : WHIRPhysicalVerifier.Opened)
    (accepted : (DuplexModeGame.runReal C iv
      (WHIRPhysicalVerifier.openQuery p i saved.shape.lanes proof ref.root x)).view.result = some out) :
    (∃ selected, selectPhase i.val f (WHIRPhysicalVerifier.queryIndices p i x).toArray = some selected ∧
      selected.rows = out.rows ∧ selected.queries = (WHIRPhysicalVerifier.queryIndices p i x).toArray ∧
      ∀ cell ∈ selected.cells, cell.available = true ∧ cell.paddingValid = true) ∨
      PublicMerkleBinding.OpenPrimitiveBad C f.queryPrefix ref.root out.paths := by
  obtain ⟨events,_,frozen,_⟩ := PCSBCSSourceRootCapture.capture_provenance
    addresses ref program table f captured
  have literal : f = freeze f.queryPrefix ref.root ref.shape := by
    rw [frozen]
    rfl
  have geometry := phaseReference_geometry p saved messages i.val ref reference
  have good := openQuery_selectPhase C iv f.queryPrefix auth p i saved.shape.lanes fits proof ref.root x out accepted
  rw [← geometry] at good
  nth_rw 1 [literal]
  exact good

end SourceQuery

#print axioms extensionRow_wordsToFields
#print axioms extensionOracle_compact_full
#print axioms frozenOracle_native
#print axioms queryIndices_derived
#print axioms queryRows_atQueries
#print axioms selectPhase_rows
#print axioms openQuery_selectPhase
#print axioms parsed_next_projection
#print axioms decodeRows_projection
#print axioms phaseReference_geometry
#print axioms phaseReference_frozenOracle
#print axioms native_openSource_fullImage
#print axioms source_query_of_native
#print axioms captured_phase_oracle
#print axioms captured_query_selection
end Whir.PCSBCSCapturedNativePhaseQuery
