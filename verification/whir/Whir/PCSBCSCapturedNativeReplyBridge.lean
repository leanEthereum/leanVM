import Whir.PCSBCSCapturedSourceTransport

/-! Native formal-model reply transport. Source tags and erased-field normal
forms are explicit. Accepted full padded openings authenticate query suffixes
outside OpenPrimitiveBad; a phase codec then transports the actual semantic
rows, in derived order, without deduplication. Next tables come from the
primitive-prefix snapshot, not a digest-to-oracle callback. -/
set_option autoImplicit false
namespace Whir.PCSBCSCapturedNativeReplyBridge
open Concrete Protocol CausalGame CausalProbability FiatShamirGame WHIRHistory
open PCSBCSSourceRootReferences PCSBCSMerkleRootCache PCSBCSMerkleLeafImages
open PCSBCSSourceFrozenAccessor PCSBCSSourceReplyInversion PCSBCSFrozenOracleRows
open PublicMerkleLog MerkleTransport
open MerkleTransport.Commitments

/-- The native phase codec, preserving wire lane order. -/
def rowCodec (phase : Nat) (words : Array K) : Option (Array E) :=
  if phase = 0 then some (words.map E.ofK) else extensionRow words

private theorem mapM_some {α β : Type} [Inhabited β] (xs : Array α) (f : α → Option β)
    (ys : Array β) (size : ys.size = xs.size)
    (each : ∀ i : Fin xs.size, f xs[i] = some ys[i.val]!) : xs.mapM f = some ys := by
  rw [Array.mapM_eq_mapM_toList]
  have rel : List.Forall₂ (fun x y => f x = some y) xs.toList ys.toList := by
    apply List.forall₂_of_length_eq_of_get (by simpa using size.symm)
    intro i hi hy
    simpa [getElem!_pos,show i < ys.size by simpa using hy] using each ⟨i,by simpa using hi⟩
  have go (as : List α) (bs : List β)
      (h : List.Forall₂ (fun x y => f x = some y) as bs) : as.mapM f = some bs := by
    induction h with
    | nil => rfl
    | cons h _ ih => simp only [List.mapM_cons,h,ih]; rfl
  rw [go _ _ rel]
  simp

/-- Checked full-table decoding gives precisely the same per-row codec. -/
theorem frozenOracle_row (phase : Nat) (f : Frozen) (oracle : Oracle)
    (decoded : frozenOracle phase f = some oracle) :
    oracle.size = f.raw.size ∧ ∀ i : Fin f.raw.size,
      rowCodec phase f.raw[i] = some oracle[i.val]! := by
  by_cases base : phase = 0
  · simp only [frozenOracle,base,↓reduceIte,Option.some.injEq] at decoded
    subst oracle
    refine ⟨by simp [liftRoot],?_⟩
    intro i
    simp [rowCodec,base,liftRoot,getElem!_pos]
  · have parsed : f.raw.mapM extensionRow = some oracle := by
      simpa only [frozenOracle,base,↓reduceIte,extensionOracle] using decoded
    rw [Array.mapM_eq_mapM_toList] at parsed
    obtain ⟨rows,hr,heq⟩ := Option.map_eq_some_iff.mp parsed
    have rel := WHIRCallerGeometry.option_mapM_rel extensionRow f.raw.toList rows hr
    have same : rows.toArray = oracle := heq
    subst oracle
    refine ⟨by simpa using rel.length_eq.symm,?_⟩
    intro i
    have hi : i.val < rows.length := by rw [← rel.length_eq]; simp
    have row := rel.get (i := i.val) (by simp) hi
    simpa [rowCodec,base,getElem!_pos,hi] using row

/-- Accepted source openings imply both status bits. Thus even an all-zero
unavailable ghost cannot serve as an authenticated source row. -/
theorem accepted_rows (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (ref : Reference) (numLeaves : Nat) (queries : List Nat)
    (proof : PrunedMerklePaths) (output : List RawPath)
    (height : ref.shape.height = numLeaves.log2) (auth : AuthenticLog C log)
    (accepted : PCSBCSMerkleFullSourceTransport.openSource (hash C) proof ref.root
      numLeaves queries ref.shape.leafWords ref.shape.occupied = some output)
    (bounds : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (hashing (hash C)), bytes.length < 2^64)
    (quiet : ¬ PublicMerkleBinding.OpenPrimitiveBad C log ref.root output) :
    List.Forall₂ (fun q path => (freeze log ref.root ref.shape).raw[q]! =
      (path.leafData.drop (ref.shape.leafWords-ref.shape.occupied)).toArray ∧
      ((freeze log ref.root ref.shape).cells[q]?).map
        (fun cell => (cell.available,cell.paddingValid)) = some (true,true)) queries output := by
  obtain ⟨compact,_,opened⟩ := PCSBCSMerkleFullSourceTransport.openSource_refines
    (hash C) proof ref.root numLeaves queries ref.shape.leafWords ref.shape.occupied output accepted
  rcases PCSBCSMerkleSourceRows.pruned_opened_compact C log auth ref.root compact
    numLeaves ref.shape.leafWords ref.shape.occupied queries output opened bounds with good | bad
  · simpa only [freeze,height] using good
  · exact (quiet bad).elim

/-- Semantic query rows are decoded from the accepted full opening suffixes,
not equated to captured rows as a premise. Repeated queries remain repeated. -/
theorem select_accepted (phase : Nat) (f : Frozen) (qs : Array Nat)
    (output : List RawPath) (leafWords occupied : Nat) (native : Oracle)
    (oracle : Oracle) (decoded : frozenOracle phase f = some oracle)
    (shape : f.raw.size = f.cells.size)
    (transport : List.Forall₂ (fun q path => f.raw[q]! =
      (path.leafData.drop (leafWords-occupied)).toArray ∧
      (f.cells[q]?).map (fun cell => (cell.available,cell.paddingValid)) = some (true,true)) qs.toList output)
    (projection : List.Forall₂ (fun path row =>
      rowCodec phase (path.leafData.drop (leafWords-occupied)).toArray = some row) output native.toList) :
    ∃ selected, selectPhase phase f qs = some selected ∧ selected.rows = native ∧
      selected.queries = qs ∧ ∀ cell ∈ selected.cells, cell.available = true ∧ cell.paddingValid = true := by
  have nativeSize : native.size = qs.size := by
    have h := transport.length_eq.trans projection.length_eq
    simpa using h.symm
  have cellAt (i : Fin qs.size) : ∃ cell, f.cells[qs[i]]? = some cell ∧
      cell.available = true ∧ cell.paddingValid = true := by
    have ho : i.val < output.length := by rw [← transport.length_eq]; simp
    have status := (transport.get (i := i.val) (by simp) ho).2
    obtain ⟨cell,hc,hflags⟩ := Option.map_eq_some_iff.mp status
    exact ⟨cell,hc,(Prod.mk.inj hflags).1,(Prod.mk.inj hflags).2⟩
  let cells := qs.map (fun q => f.cells[q]!)
  have cellsParsed : qs.mapM (fun q => f.cells[q]?) = some cells := by
    apply mapM_some _ _ _ (by simp [cells])
    intro i
    obtain ⟨cell,hc,_,_⟩ := cellAt i
    change f.cells[qs[i]]? = some cells[i.val]!
    have same : cells[i.val]! = cell := by
      rw [getElem!_pos cells i.val (by simp [cells])]
      simp only [cells,Array.getElem_map]
      change f.cells[qs[i]]! = cell
      rw [getElem!_def,hc]
    rw [same]
    exact hc
  have rowsParsed : queryRows oracle qs = some native := by
    apply mapM_some _ _ _ nativeSize
    intro i
    obtain ⟨cell,hc,_,_⟩ := cellAt i
    have inside : qs[i] < f.cells.size := (Array.getElem?_eq_some_iff.mp hc).1
    have rawInside : qs[i] < f.raw.size := by rw [shape]; exact inside
    have ho : i.val < output.length := by rw [← transport.length_eq]; simp
    have hn : i.val < native.size := by rw [nativeSize]; exact i.isLt
    have suffix := (transport.get (i := i.val) (by simp) ho).1
    have projected := projection.get (i := i.val) ho (by simpa using hn)
    have codec := (frozenOracle_row phase f oracle decoded).2 ⟨qs[i],rawInside⟩
    simp only [List.get_eq_getElem,Array.getElem_toList] at suffix projected
    simp only [Fin.getElem_fin] at codec rawInside ⊢
    rw [getElem!_pos f.raw (qs[i.val]) rawInside] at suffix
    rw [suffix] at codec
    have equal : oracle[qs[i]]! = native[i.val]! := by
      rw [projected] at codec
      simpa [getElem!_pos native i.val hn] using (Option.some.inj codec).symm
    have bound : qs[i] < oracle.size := by rw [(frozenOracle_row phase f oracle decoded).1]; exact rawInside
    simp only [Fin.getElem_fin] at equal bound
    rw [Array.getElem?_eq_getElem bound,← getElem!_pos oracle (qs[i.val]) bound,equal]
  have flags : cells.all (fun cell => !cell.available || cell.paddingValid) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have iq : i < qs.size := by simpa [cells] using hi
    obtain ⟨cell,hc,ha,hp⟩ := cellAt ⟨i,iq⟩
    change f.cells[qs[i]]? = some cell at hc
    simp only [cells,Array.getElem_map]
    change (!f.cells[qs[i]]!.available || f.cells[qs[i]]!.paddingValid) = true
    rw [getElem!_def,hc]
    simp only [ha,hp,Bool.not_true,Bool.false_or]
  refine ⟨⟨qs,native,cells⟩,?_,rfl,rfl,?_⟩
  · unfold selectPhase
    rw [decoded]
    dsimp only [Bind.bind,Option.bind]
    rw [rowsParsed]
    dsimp only [Bind.bind,Option.bind]
    rw [cellsParsed]
    dsimp only [Bind.bind,Option.bind]
    rw [flags]
    rfl
  · intro cell member
    obtain ⟨q,hq,rfl⟩ := Array.mem_map.mp member
    obtain ⟨i,hi,heq⟩ := Array.mem_iff_getElem.mp hq
    obtain ⟨actual,hc,ha,hp⟩ := cellAt ⟨i,hi⟩
    change f.cells[qs[i]]? = some actual at hc
    rw [← heq,getElem!_def,hc]
    exact ⟨ha,hp⟩

/-- Full next-image provenance includes all rows, including unavailable defaults
and invalid padding. It is not just a quotient equality at queried indexes. -/
theorem next_image_provenance (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (ref : Reference) (auth : AuthenticLog C log) (clean : ¬ OutputCollision log) :
    imageTable (freeze log ref.root ref.shape).cells =
      MerkleTransport.Commitments.baseOracle (hash C)
        ⟨recordDomain (records log),[]⟩ ref.root ref.shape.height (2^ref.shape.height) ref.shape.leafWords ∧
    (freeze log ref.root ref.shape).raw = WHIRPhysicalRows.compactBaseOracle (hash C)
      ⟨recordDomain (records log),[]⟩ ref.root ref.shape.height (2^ref.shape.height)
        ref.shape.leafWords ref.shape.occupied := by
  exact ⟨PCSBCSMerkleSourceRows.imageRoot0_eq_baseOracle C log auth clean ref.root
      ref.shape.height ref.shape.leafWords ref.shape.occupied,
    PCSBCSMerkleSourceRows.compactRoot0_eq_compactBaseOracle C log auth clean ref.root
      ref.shape.height ref.shape.leafWords ref.shape.occupied⟩

/-- Opening the full index range transports a genuine native full table and
authenticates every cell. This stronger statement is needed if the native model
uses a fully available table rather than the total primitive snapshot view. -/
theorem accepted_full_table (C : DuplexModeGame.PrimitiveOracle) (log : PublicLog)
    (ref : Reference) (numLeaves : Nat) (proof : PrunedMerklePaths) (output : List RawPath)
    (height : ref.shape.height = numLeaves.log2) (auth : AuthenticLog C log)
    (accepted : PCSBCSMerkleFullSourceTransport.openSource (hash C) proof ref.root numLeaves
      (List.range (2^ref.shape.height)) ref.shape.leafWords ref.shape.occupied = some output)
    (bounds : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (hashing (hash C)), bytes.length < 2^64)
    (quiet : ¬ PublicMerkleBinding.OpenPrimitiveBad C log ref.root output) :
    (freeze log ref.root ref.shape).raw =
      (output.map (fun path => (path.leafData.drop (ref.shape.leafWords-ref.shape.occupied)).toArray)).toArray ∧
    ∀ i < 2^ref.shape.height,
      ((freeze log ref.root ref.shape).cells[i]?).map
        (fun cell => (cell.available,cell.paddingValid)) = some (true,true) := by
  have transport := accepted_rows C log ref numLeaves (List.range (2^ref.shape.height))
    proof output height auth accepted bounds quiet
  have length : output.length = 2^ref.shape.height := by simpa using transport.length_eq.symm
  constructor
  · apply Array.ext
    · simp [freeze,compactTable,sourceCells_size,length]
    · intro i hi ho
      have inside : i < 2^ref.shape.height := by
        simpa only [freeze,compactTable,Array.size_map,sourceCells_size] using hi
      have related := (transport.get (i := i) (by simpa using inside) (by omega)).1
      simpa only [List.get_eq_getElem,List.getElem_range,
        getElem!_pos (freeze log ref.root ref.shape).raw i hi,
        List.getElem_toArray,List.getElem_map] using related
  · intro i hi
    have related := (transport.get (i := i) (by simpa using hi) (by omega)).2
    simpa only [List.get_eq_getElem,List.getElem_range] using related

/-- The capture field of NativeEvidence on the production registry is supplied
by actual first-mention execution, not by a supplied frozen oracle callback. -/
theorem captured_freeze_provenance {p : ParameterBounds.Profile} {Q : Nat}
    {iv : Digest32} {boundary : Nat} {R : Type} {n : Nat}
    (addresses : PCSBCSSourceRootCapture.Key (p := p) (Q := Q) (iv := iv)
      (boundary := boundary) → List Reference)
    (program : TypedOracleCompiler.Sampling _ (PCSBCSSourceRootCapture.Answer
      (p := p) (Q := Q) (iv := iv) (boundary := boundary)) R n)
    (table : PCSStateRestoration.Latent.Table _ _) (current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (ref : Reference) (mentioned : ref ∈ addresses (.inl current))
    (visited : (.inl current : PCSBCSSourceRootCapture.Key) ∈
      ((TypedOracleCompiler.Sampling.execute table program).2.map Sigma.fst)) :
    ∃ events, PCSBCSFirstRootDisclosure.firstMention addresses ref program table = some events ∧
      PCSBCSSourceCallerSnapshot.capturedRegistry addresses program current (fun key => table key.val) ref =
        some (freeze (PCSBCSSourceRootCapture.ordinaryPrefix events) ref.root ref.shape) := by
  obtain ⟨f,captured⟩ := PCSBCSSourceRootCapture.capture_exists addresses ref
    (.inl current) mentioned program table visited
  obtain ⟨events,first,frozen,_⟩ := PCSBCSSourceRootCapture.capture_provenance
    addresses ref program table f captured
  refine ⟨events,first,?_⟩
  rw [PCSBCSSourceCallerSnapshot.capturedRegistry_enabled addresses program current table ref mentioned,
    captured,frozen]

/-- Local native-model input contract. No constructor takes canonicalReply
compatibility or a constructed accessor. Capture storage must be the literal
freeze of the identified ordinary primitive prefix. Source admission, scalar
projection, and chronological message index are supplied separately. -/
inductive NativeEvidence {c : Config} (current : Coordinate c)
    (saved : AnchoredHeaderCodec.Record) (registry : Captures) (messages : List Pending)
    (past : WHIRFiatShamir.Prefix current) (m : Pending) (digest : Digest32)
    (C : DuplexModeGame.PrimitiveOracle) :
    Coordinate c → Reply → Prop where
  | initial (a : Message E) : NativeEvidence current saved registry messages past m digest C .initial (.initial a)
  | ood (i : Fin c.folds.size) (j : Fin (oodCount c i.val)) (a : OodClaim) :
      NativeEvidence current saved registry messages past m digest C (.ood i j) (.ood a)
  | tail (j : Fin (c.logN-c.folds.toList.sum)) (a : Message E) :
      NativeEvidence current saved registry messages past m digest C (.tail j) (.tail a)
  | middle (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) (a : Message E)
      (notLast : j.val+1 ≠ c.folds[i.val]!) :
      NativeEvidence current saved registry messages past m digest C (.fold i j) (.fold a none #[])
  | terminal (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) (a : Message E) (residual : Array E)
      (last : j.val+1 = c.folds[i.val]!) (terminal : ¬ i.val+1 < c.folds.size)
      (width : residual.size = 2^remaining c i.val) :
      NativeEvidence current saved registry messages past m digest C (.fold i j) (.fold a none residual)
  | next (i : Fin c.folds.size) (j : Fin c.folds[i.val]!) (a : Message E) (native : Oracle)
      (last : j.val+1 = c.folds[i.val]!) (later : i.val+1 < c.folds.size)
      (ref : Reference) (log : PublicLog)
      (reference : parsePhase c (.fold i j) m (i.val+1) 2 = some ref)
      (captured : registry ref = some (freeze log ref.root ref.shape))
      (fits : ref.shape.occupied ≤ ref.shape.leafWords)
      (auth : AuthenticLog C log) (clean : ¬ OutputCollision log)
      (projection : extensionOracle (WHIRPhysicalRows.compactBaseOracle (hash C)
        ⟨recordDomain (records log),[]⟩ ref.root ref.shape.height (2^ref.shape.height)
        ref.shape.leafWords ref.shape.occupied) = some native) :
      NativeEvidence current saved registry messages past m digest C (.fold i j) (.fold a (some native) #[])
  | query (i : Fin c.folds.size) (a : Message E) (native : Oracle)
      (earlier : position (.query i : Coordinate c) < position current)
      (ref : Reference) (log : PublicLog)
      (reference : phaseReference c saved
        (messages.reverse.take (position (.query i : Coordinate c)+1)).reverse i.val = some ref)
      (captured : registry ref = some (freeze log ref.root ref.shape))
      (fits : ref.shape.occupied ≤ ref.shape.leafWords)
      (codec : i.val = 0 ∨ ref.shape.occupied % 3 = 0)
      (qs : Array Nat)
      (derived : deriveQueries (remaining c i.val+c.rates[i.val]!) c.queries[i.val]!
        (Array.ofFn (past (.query i) earlier).1) = some qs)
      (numLeaves : Nat) (proof : PrunedMerklePaths) (output : List RawPath)
      (height : ref.shape.height = numLeaves.log2) (auth : AuthenticLog C log)
      (accepted : PCSBCSMerkleFullSourceTransport.openSource (hash C) proof ref.root
        numLeaves qs.toList ref.shape.leafWords ref.shape.occupied = some output)
      (bounds : ∀ path ∈ output, ∀ bytes ∈ path.opening.inputs (hashing (hash C)), bytes.length < 2^64)
      (quiet : ¬ PublicMerkleBinding.OpenPrimitiveBad C log ref.root output)
      (projection : List.Forall₂ (fun path row =>
        rowCodec i.val (path.leafData.drop (ref.shape.leafWords-ref.shape.occupied)).toArray = some row)
        output native.toList) :
      NativeEvidence current saved registry messages past m digest C (.query i) (.query native a)

/-- Compatibility is a conclusion of accepted opening/full-table transport and
the native normal-form contract, never an acceptance-to-compatibility premise. -/
theorem native_compatible {c : Config} {C : DuplexModeGame.PrimitiveOracle} (current q : Coordinate c)
    (saved : AnchoredHeaderCodec.Record) (registry : Captures) (messages : List Pending)
    (past : WHIRFiatShamir.Prefix current) (m : Pending) (digest : Digest32) (native : Reply)
    (earlier : position q < position current)
    (evidence : NativeEvidence current saved registry messages past m digest C q native) :
    ∃ access, build current saved registry messages past q m = some access ∧
      canonicalReply q digest ((oracles access).next q) ((oracles access).rows q) native = some native := by
  cases evidence with
  | initial a =>
    refine ⟨{},?_,rfl⟩
    simp only [build,dite_eq_left earlier]
  | ood i j a => exact ⟨{},by simp [build,earlier],rfl⟩
  | tail j a => exact ⟨{},by simp [build,earlier],rfl⟩
  | middle i j a notLast =>
    have notLast' : j.val+1 ≠ c.folds[i.val] := by simpa using notLast
    exact ⟨{},by simp [build,earlier,notLast'],by simp [canonicalReply,notLast']⟩
  | terminal i j a residual last terminal width =>
    exact ⟨{},by simp [build,earlier,last,terminal],by simp [canonicalReply,last,terminal,width]⟩
  | next i j a native last later ref log reference captured fits auth clean projection =>
    have raw := (next_image_provenance C log ref auth clean).2
    have decoded : frozenOracle (i.val+1) (freeze log ref.root ref.shape) = some native := by
      simp only [frozenOracle,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
      rw [raw]
      exact projection
    refine ⟨⟨#[],native,#[],#[],(freeze log ref.root ref.shape).cells.map status⟩,?_,?_⟩
    · exact build_fold_next current saved registry messages past i j m earlier last later ref _
        native reference (PCSBCSSourceFrozenAccessorStructural.lookup_freeze registry log ref fits captured) decoded
    · simp [canonicalReply,last,later,oracles]
  | query i a native queryEarlier ref log reference captured fits codec qs derived
      numLeaves proof output height auth accepted bounds quiet projection =>
    obtain ⟨oracle,decoded,_⟩ := PCSBCSSourceFrozenAccessorStructural.frozenOracle_freeze
      log ref.root ref.shape fits i.val codec
    have transport := accepted_rows C log ref numLeaves qs.toList proof output height auth accepted bounds quiet
    obtain ⟨selected,hs,rows,_,_⟩ := select_accepted i.val (freeze log ref.root ref.shape) qs
      output ref.shape.leafWords ref.shape.occupied native oracle decoded
      (PCSBCSSourceFrozenAccessorStructural.freeze_shape_exact log ref.root ref.shape fits).2.1
      transport projection
    refine ⟨⟨selected.rows,#[],qs,selected.cells.map status,#[]⟩,?_,?_⟩
    · exact build_query current saved registry messages past i m queryEarlier ref _ qs selected
        reference (PCSBCSSourceFrozenAccessorStructural.lookup_freeze registry log ref fits captured) derived hs
    · simp [canonicalReply,oracles,rows]

/-- Exact chronological inverse of the actual native earlier reply. -/
theorem inverseAt_native {c : Config} {C : DuplexModeGame.PrimitiveOracle} (current : Coordinate c)
    (saved : AnchoredHeaderCodec.Record) (registry : Captures) (messages : List Pending)
    (past : WHIRFiatShamir.Prefix current) (n : Nat) (q : Coordinate c)
    (m : Pending) (digest : Digest32) (native : Reply)
    (coordinate : (schedule c)[n]? = some q) (message : messages.reverse[n+1]? = some m)
    (earlier : position q < position current)
    (scalars : replyScalars q digest native = some m.scalars)
    (evidence : NativeEvidence current saved registry messages past m digest C q native) :
    PCSBCSSourceFrozenAccessor.inverseAt current saved registry messages past n = some ⟨native,m.nonce⟩ := by
  obtain ⟨access,built,compatible⟩ := native_compatible current q saved registry messages past
    m digest native earlier evidence
  rw [inverseAt_integration current saved registry messages past n q m access coordinate message built]
  have roundtrip := scalar_roundtrip (oracles access) q digest native m.nonce
  rw [scalars,Option.bind_some,compatible] at roundtrip
  exact roundtrip

open TypedOracleCompiler PCSStateRestoration.Latent
variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)

/-- Literal ordinary records before the first mention. The empty default does
not grant authentication: accepted transport still requires AuthenticLog and
absence of OpenPrimitiveBad, and the production address gate proves existence. -/
noncomputable def sourceLog {R : Type} {n : Nat} (addresses : Keys → List Reference)
    (ref : Reference) (program : Sampling Keys Answers R n) (table : Table Keys Answers) : PublicLog :=
  PCSBCSSourceRootCapture.ordinaryPrefix
    ((PCSBCSFirstRootDisclosure.firstMention addresses ref program table).getD [])

/-- A fixed source projection, not a supplied oracle. Only mentioned roles are
used; their actual captures are proved equal to this literal first-mention view. -/
noncomputable def sourceRegistry {R : Type} {n : Nat} (addresses : Keys → List Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) : Captures :=
  fun ref => some (freeze (sourceLog addresses ref program table) ref.root ref.shape)

/-- The log field in source evidence cannot choose a different primitive prefix:
the frozen record retains the actual prefix, not just its extracted table. -/
theorem sourceRegistry_log_exact {R : Type} {n : Nat} (addresses : Keys → List Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers) (ref : Reference)
    (log : PublicLog)
    (projected : sourceRegistry addresses program table ref = some (freeze log ref.root ref.shape)) :
    log = sourceLog addresses ref program table := by
  have same := Option.some.inj projected
  exact (congrArg Frozen.queryPrefix same).symm

/-- Native source evidence fixes logs/tables by actual program execution.
The NativeEvidence capture field now concerns the computed source projection;
the actual capturedRegistry success is a theorem, not an input. -/
abbrev SourceEvidence {R : Type} {n : Nat} {c : Config} (addresses : Keys → List Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (C : DuplexModeGame.PrimitiveOracle)
    (current : Coordinate c) (saved : AnchoredHeaderCodec.Record) (messages : List Pending)
    (past : WHIRFiatShamir.Prefix current) (m : Pending) (digest : Digest32)
    (q : Coordinate c) (native : Reply) : Prop :=
  NativeEvidence current saved (sourceRegistry addresses program table) messages past m digest C q native

theorem source_registry_enabled {R : Type} {n : Nat} (addresses : Keys → List Reference)
    (program : Sampling Keys Answers R n) (table : Table Keys Answers)
    (current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary) (ref : Reference)
    (mentioned : ref ∈ addresses (.inl current))
    (visited : (.inl current : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst)) :
    PCSBCSSourceCallerSnapshot.capturedRegistry addresses program current (fun key => table key.val) ref =
      sourceRegistry addresses program table ref := by
  obtain ⟨events,first,captured⟩ := captured_freeze_provenance addresses program table current ref mentioned visited
  simpa only [sourceRegistry,sourceLog,first,Option.getD_some] using captured

/-- Every needed role is obtained from the literal current packet's admitted
root-address list, including the next root announced by this exact message. -/
theorem source_nativeEvidence {R : Type} {count : Nat} (addresses : Keys → List Reference)
    (program : Sampling Keys Answers R count) (table : Table Keys Answers)
    (C : DuplexModeGame.PrimitiveOracle)
    (current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (saved : AnchoredHeaderCodec.Record) (past : WHIRFiatShamir.Prefix current.2.coord)
    (n : Nat) (q : Coordinate (ParameterBounds.config p)) (m : Pending) (digest : Digest32)
    (native : Reply) (coordinate : (schedule (ParameterBounds.config p))[n]? = some q)
    (message : current.2.messages.reverse[n+1]? = some m)
    (addressRoles : addresses (.inl current) =
      ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) current.2.messages)
    (visited : (.inl current : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst))
    (evidence : SourceEvidence addresses program table C current.2.coord saved current.2.messages
      past m digest q native) :
    NativeEvidence current.2.coord saved
      (PCSBCSSourceCallerSnapshot.capturedRegistry addresses program current (fun key => table key.val))
      current.2.messages past m digest C q native := by
  cases evidence with
  | initial a => exact .initial a
  | ood i j a => exact .ood i j a
  | tail j a => exact .tail j a
  | middle i j a notLast => exact .middle i j a notLast
  | terminal i j a residual last terminal width => exact .terminal i j a residual last terminal width
  | next i j a native last later ref log reference captured fits auth clean projection =>
    have member := PCSBCSCapturedSourceTransport.foldReference_member (ParameterBounds.config p)
      current.2.messages n i j m ref coordinate message reference
    have mentioned : ref ∈ addresses (.inl current) := by
      rw [addressRoles]
      exact List.mem_cons_of_mem _ member
    have actual := (source_registry_enabled addresses program table current ref mentioned visited).trans captured
    exact .next i j a native last later ref log reference actual fits auth clean projection
  | query i a native earlier ref log reference captured fits codec qs derived
      numLeaves proof output height auth accepted bounds quiet projection =>
    have member := PCSBCSCapturedSourceTransport.phaseReference_member (ParameterBounds.config p)
      saved current.2.messages i.val (position (.query i : Coordinate (ParameterBounds.config p))+1) ref reference
    have mentioned : ref ∈ addresses (.inl current) := by rw [addressRoles]; exact member
    have actual := (source_registry_enabled addresses program table current ref mentioned visited).trans captured
    exact .query i a native earlier ref log reference actual fits codec qs derived numLeaves proof
      output height auth accepted bounds quiet projection

/-- Production captured-registry native inverse. Neither capture availability
nor semantic compatibility is a free premise; visited address membership and
first-mention source provenance supply the former, accepted transport the latter. -/
theorem inverseAt_source_native {R : Type} {count : Nat} (addresses : Keys → List Reference)
    (program : Sampling Keys Answers R count) (table : Table Keys Answers)
    (C : DuplexModeGame.PrimitiveOracle)
    (current : PCSBCSChallengeOracle.EnteredPacket p Q iv boundary)
    (saved : AnchoredHeaderCodec.Record) (past : WHIRFiatShamir.Prefix current.2.coord)
    (n : Nat) (q : Coordinate (ParameterBounds.config p)) (m : Pending) (digest : Digest32)
    (native : Reply) (coordinate : (schedule (ParameterBounds.config p))[n]? = some q)
    (message : current.2.messages.reverse[n+1]? = some m)
    (earlier : position q < position current.2.coord)
    (scalars : replyScalars q digest native = some m.scalars)
    (addressRoles : addresses (.inl current) =
      ⟨saved.root,initialShape saved.shape⟩ :: phaseReferences (ParameterBounds.config p) current.2.messages)
    (visited : (.inl current : Keys) ∈ ((Sampling.execute table program).2.map Sigma.fst))
    (evidence : SourceEvidence addresses program table C current.2.coord saved current.2.messages
      past m digest q native) :
    PCSBCSSourceFrozenAccessor.inverseAt current.2.coord saved
      (PCSBCSSourceCallerSnapshot.capturedRegistry addresses program current (fun key => table key.val))
      current.2.messages past n = some ⟨native,m.nonce⟩ := by
  exact inverseAt_native current.2.coord saved _ current.2.messages past n q m digest native
    coordinate message earlier scalars
    (source_nativeEvidence addresses program table C current saved past n q m digest native
      coordinate message addressRoles visited evidence)

#print axioms source_registry_enabled
#print axioms sourceRegistry_log_exact
#print axioms source_nativeEvidence
#print axioms inverseAt_source_native

#print axioms accepted_rows
#print axioms select_accepted
#print axioms next_image_provenance
#print axioms accepted_full_table
#print axioms captured_freeze_provenance
#print axioms native_compatible
#print axioms inverseAt_native

end Whir.PCSBCSCapturedNativeReplyBridge
