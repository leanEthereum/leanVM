/-
  LeanVM.Guest.Backend.Guest.Cpl.Inst

  The completeness instance through the back end: the cells of each value (the back end's
  places), the frame words of each instance (the frame family `FrameConsistentStmt` gives), the
  frames' cells and the callees' headers, and the checker's facts about them (`KFactsAll`).
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Placed
public import LeanVM.Guest.Backend.Guest.Cpl.Insts
public import LeanVM.Guest.Backend.Complete.InFrameFn
public import LeanVM.Guest.EndComplete

/-!
# The instance

`certG f v` is the cell the back end places value `v` of function `f` at. `FSG i fp kfps hdr` is a
frame family of entry `i` at frame `fp` with callee frames `kfps` and header `hdr` as
`FrameConsistentStmt` gives one (`FSOk`), chosen once for every memory; it is blind to the
temporaries' words whether or not one exists (`FSG_congr`). An instance of entry `i` that runs
has the cells `nodeG`: its temporaries' and its frame runs' cells with the values' words first,
then every cell of its frame off the temporaries' cells with the frame words, then (`main`) the
jump table; a phantom has its parameters' cells and a registered loop helper's self pointer. A
callee's header is the frame family's, if it is of `K`.

The checker's facts (`kFactsAll`) need only the static test of every entry (`CplOkAll`): the
temporaries' cells are distinct and in the frame, the frame runs' cells are consecutive, apart
from the temporaries' and one value each, and the frame family does not see the temporaries.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory GuestPiece
open LeanVM.Guest.Deployed

@[expose] public section

/-! ## The cells and the frame words -/

/-- Entry `i` of the back end's input. -/
noncomputable abbrev tfG (i : ℕ) : TracedFn := guestTraced.getD i default

/-- **The back end's cell** of each value of each function. -/
noncomputable def certG (f : String) (v : V) : ℕ :=
  match coreProgram.indexOf? f with
  | some i => (Complete.cellP (placedG i).locs v).getD 0
  | none => 0

/-- **What `FrameConsistentStmt` gives entry `i`** at frame `fp`, callee frames `kfps` and header
`hdr`: a frame family `FS`. -/
def FSOk (i fp : ℕ) (kfps : List ℕ) (hdr : E × E) (FS : Val → Complete.FrameSpec) : Prop :=
  Complete.FrameCongr (tfG i) (placedG i) FS ∧
    ∀ (σ : Val) (es : List Ev) (vs : List V), walk σ (tfG i).core.body = .ret es vs →
      (∀ q ∈ addrs es, σ q.1 = ofK (addressOfIndex (fp + (Complete.cellP (placedG i).locs q.2).getD 0))) →
      (∀ rd : Reader, (∀ e ∈ es, e.Holds rd σ) →
        Complete.FrameClauses (loopTable W0.p) (tfG i) (placedG i) fp σ es vs hdr (FS σ)) ∧
      ∀ {κ : ℕ} (L : MemoryImage κ) (ck : List (Opcode → ℕ)),
        Complete.FrameOK L (loopTable W0.p) (tfG i) (placedG i).fn.frameSize fp (FS σ) σ es kfps hdr →
        (∀ e ∈ es, e.Holds L.read σ) → JTHolds L W0.layout W0.slots →
        Complete.World.KidsRunP (Complete.World.withL W0 L) σ es kfps ck →
        Complete.World.CplBody (Complete.World.withL W0 L) (tfG i) (placedG i) fp σ (kfps.zip ck)

open Classical in
/-- **The frame family of entry `i`** at frame `fp`, callee frames `kfps`, header `hdr`. -/
noncomputable def FSG (i fp : ℕ) (kfps : List ℕ) (hdr : E × E) : Val → Complete.FrameSpec :=
  if h : ∃ FS, FSOk i fp kfps hdr FS then Classical.choose h else fun _ => ⟨fun _ => 0, fun _ => (0, 0)⟩

/-- The frame family does not see the temporaries. -/
theorem FSG_congr (i fp : ℕ) (kfps : List ℕ) (hdr : E × E) :
    Complete.FrameCongr (tfG i) (placedG i) (FSG i fp kfps hdr) := by
  unfold FSG
  split
  · next h => exact (Classical.choose_spec h).1
  · intro σ σ' _
    exact ⟨fun _ _ => rfl, rfl⟩

/-- The frame words of an instance of entry `i`. -/
noncomputable def FSI (i : ℕ) (I : Inst) (σ : Val) : Complete.FrameSpec := FSG i I.fp I.kidFps I.hdr σ

/-- The cells of values, at the back end's cells. -/
noncomputable def valG (f : String) (σ : Val) (vs : List V) : List (ℕ × E) :=
  vs.map fun v => (certG f v, σ v)

/-- The cells of the frame runs of a path, at the back end's cells. -/
noncomputable def runsG (f : String) (σ : Val) (es : List Ev) : List (ℕ × E) :=
  es.flatMap fun
    | .atom (.frameAddr _ (r :: rs)) => (r :: rs).mapIdx fun k v => (certG f r + k, σ v)
    | _ => []

open Classical in
/-- The cells of the frame of an instance of entry `i` off its temporaries' cells, with the frame
words. -/
noncomputable def ownG (i : ℕ) (f : String) (σ : Val) (I : Inst) : List (ℕ × E) :=
  (List.range (placedG i).fn.frameSize).filterMap fun n =>
    if ∃ t ∈ coreProgram.temps f, certG f t = n then none else some (n, (FSI i I σ).Ψ n)

/-- The candidate cells of an instance of entry `i` after its temporaries'. -/
noncomputable def restG (i : ℕ) (f : String) (σ : Val) (I : Inst) : List (ℕ × E) :=
  runsG f σ (I.t.events coreProgram) ++ (ownG i f σ I ++ (if i = 0 then tableCells else []))

/-- **The candidate cells of an instance of entry `i` that runs.** -/
noncomputable def nodeG (i : ℕ) (f : String) (σ : Val) (I : Inst) : List (ℕ × E) :=
  valG f σ (coreProgram.temps f) ++ restG i f σ I

/-- The candidate cells of a phantom of entry `i`: what its caller writes. -/
noncomputable def phantomG (i : ℕ) (f : String) (σ : Val) (I : Inst) : List (ℕ × E) :=
  valG f σ (coreOf (i + 1)).params ++
    (if (loopsG[f]?).any (·.registered) then
      [(2 + (coreOf (i + 1)).params.length, ofK (addressOfIndex I.fp))] else [])

/-- **The cells of each frame of the honest memory.** -/
noncomputable def CG (I : Inst) : List (ℕ × E) :=
  match I.t, coreProgram.indexOf? I.t.name with
  | .node f σ _ _, some i => frameE (fs f) (nodeG i f σ I)
  | .phantom f σ, some i => frameE (fs f) (phantomG i f σ I)
  | _, _ => []

open Classical in
/-- **The header of each callee**: the frame family's, if it is of `K`. -/
noncomputable def HG (I : Inst) (k : ℕ) : E × E :=
  match I.t, coreProgram.indexOf? I.t.name with
  | .node _ σ _ _, some i =>
      if IsInK ((FSI i I σ).kh k).1 ∧ IsInK ((FSI i I σ).kh k).2 then (FSI i I σ).kh k else (0, 0)
  | _, _ => (0, 0)

theorem CG_node {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {i : ℕ}
    (ht : I.t = .node f σ bufs kids) (hi : coreProgram.indexOf? f = some i) :
    CG I = frameE (fs f) (nodeG i f σ I) := by
  unfold CG
  rw [ht]
  simp only [Tree.name, hi]

theorem CG_phantom {I : Inst} {f : String} {σ : Val} {i : ℕ} (ht : I.t = .phantom f σ)
    (hi : coreProgram.indexOf? f = some i) : CG I = frameE (fs f) (phantomG i f σ I) := by
  unfold CG
  rw [ht]
  simp only [Tree.name, hi]

theorem HG_node {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} {i : ℕ}
    (ht : I.t = .node f σ bufs kids) (hi : coreProgram.indexOf? f = some i) (k : ℕ)
    (hK : IsInK ((FSI i I σ).kh k).1 ∧ IsInK ((FSI i I σ).kh k).2) : HG I k = (FSI i I σ).kh k := by
  unfold HG
  rw [ht]
  simp only [Tree.name, hi]
  simp only [hK.1, hK.2, and_self, ↓reduceIte]

theorem CG_shape (I : Inst) : ∃ L, CG I = frameE (fs I.t.name) L ∨ CG I = [] := by
  unfold CG
  cases ht : I.t with
  | node f σ bufs kids =>
    cases hj : coreProgram.indexOf? f with
    | none => exact ⟨[], Or.inr (by simp [Tree.name, hj])⟩
    | some j => exact ⟨nodeG j f σ I, Or.inl (by simp [Tree.name, hj])⟩
  | phantom f σ =>
    cases hj : coreProgram.indexOf? f with
    | none => exact ⟨[], Or.inr (by simp [Tree.name, hj])⟩
    | some j => exact ⟨phantomG j f σ I, Or.inl (by simp [Tree.name, hj])⟩
theorem isInK_zeroG : IsInK (0 : E) := by
  simpa [Value.ofK_zero] using Value.ofK_isInK (0 : K)


/-- Every callee header is of `K`. -/
theorem HG_K (I : Inst) (k : ℕ) : KHdr (HG I k) := by
  unfold HG
  split
  · split
    · next h => exact h
    · exact ⟨isInK_zeroG, isInK_zeroG⟩
  · exact ⟨isInK_zeroG, isInK_zeroG⟩

/-! ## The functions -/

/-- **Function `f`, entry `i`**: its core function, frame size, temporaries and cells. -/
structure FnAt (f : String) (i : ℕ) : Prop where
  lt : i < coreProgram.length
  find : coreProgram.find? f = some (coreOf (i + 1))
  core : (tfG i).core = coreOf (i + 1)
  name : (coreOf (i + 1)).name = f
  fs_eq : fs f = fsN (i + 1)
  temps : coreProgram.temps f = Stmt.tmpsList (coreOf (i + 1)).body
  cert : ∀ v, certG f v = (Complete.cellP (placedG i).locs v).getD 0
  nfns : i + 1 < nFns

theorem fnAt {f : String} {i : ℕ} (hix : coreProgram.indexOf? f = some i) : FnAt f i := by
  have hj : idxOf f = some (i + 1) := by unfold idxOf; rw [hix]; rfl
  obtain ⟨i', he, hi, hn, hf, hc, hfs, -, h2⟩ := fn_of_idx hj
  obtain rfl : i = i' := by omega
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi guestTraced_length.symm
  have hcore : (tfG i).core = coreOf (i + 1) := by
    show (guestTraced.getD i default).core = _
    rw [List.getD_eq_getElem _ _ hi', guestTraced_getElem hi']
  exact ⟨hi, by rw [hc]; exact hf, hcore, by rw [hc]; exact hn, hfs,
    by rw [Program.temps, hf, hc], fun v => by unfold certG; rw [hix], h2⟩

theorem ix_of_idx {f : String} {j : ℕ} (hj : idxOf f = some j) :
    ∃ i, j = i + 1 ∧ coreProgram.indexOf? f = some i := by
  unfold idxOf at hj
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hj
  exact ⟨i, rfl, hi⟩

theorem ix_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn) :
    ∃ i, coreProgram.indexOf? f = some i := by
  cases hj : coreProgram.indexOf? f with
  | none => rw [find?_none hj] at h; cases h
  | some i => exact ⟨i, rfl⟩

theorem tmps_tfG {f : String} {i : ℕ} (F : FnAt f i) :
    coreProgram.temps f = Stmt.tmpsList (tfG i).core.body := by
  rw [F.temps, F.core]

theorem fsWant_le (i : ℕ) : fsWant i ≤ fsN (i + 1) := by
  rcases i with _ | i
  · show Deployed.Data.mainCells ≤ mainFrame
    unfold mainFrame; omega
  · show max 2 (fsAt (i + 1 + 1)) ≤ (bif Nat.beq (i + 1 + 1) 1 then mainFrame else max 2 (fsAt (i + 1 + 1)))
    simp

theorem fsWant_eq {i : ℕ} (h : i ≠ 0) : fsWant i = fsN (i + 1) := by
  rcases i with _ | i
  · exact absurd rfl h
  · show max 2 (fsAt (i + 1 + 1)) = (bif Nat.beq (i + 1 + 1) 1 then mainFrame else max 2 (fsAt (i + 1 + 1)))
    simp


/-- **What the per-function test gives entry `i`**, placed. -/
structure EntryOk (i : ℕ) : Prop where
  facts : CplFacts i (placedG i)
  placed : ∃ t', placeFn loopsG sigsG (tablesAt outsG i) (tfG i) = .ok (placedG i, t')
  placedAs : Complete.World.PlacedAs W0 (tfG i) (placedG i)
  inFrame : ∀ v n, Complete.cellP (placedG i).locs v = some n → 2 ≤ n ∧ n < fsWant i

theorem entryOk (hok : CplOkAll) {i : ℕ} (hi : i < coreProgram.length) : EntryOk i := by
  have hi' : i < guestTraced.length := lt_of_lt_of_eq hi guestTraced_length.symm
  obtain ⟨hat, hpa, t', hpf⟩ := guest_placed hi'
  have hF := cplOkWith_spec (cplOkWith_of hat (hok i (coreProgram_length ▸ hi)))
  refine ⟨hF, ⟨t', hpf⟩, hpa, fun v n hv => ?_⟩
  have := Complete.placeFn_inFrame _ _ _ _ _ _ hpf hF.isScoped v n hv
  rw [hF.sfacts.frame] at this
  exact this

/-! ## Frame runs -/

theorem mem_runsG {f : String} {σ : Val} {es : List Ev} {x : ℕ × E} (h : x ∈ runsG f σ es) :
    ∃ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ es ∧ ∃ k, ∃ hk : k < (r :: rs).length,
      x = (certG f r + k, σ (r :: rs)[k]) := by
  simp only [runsG, List.mem_flatMap] at h
  obtain ⟨e, he, hx⟩ := h
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨p, _ | ⟨r, rs⟩⟩ | _ | _⟩ | _ | _ | _ <;>
    simp only [List.not_mem_nil] at hx
  obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hx
  exact ⟨p, r, rs, he, k, hk, rfl⟩

/-- An atom of a node's path is an atom of its function's body. -/
theorem events_atomG {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {a : Atom} (ha : Ev.atom a ∈ I.t.events coreProgram) :
    ∃ i, coreProgram.indexOf? f = some i ∧ a ∈ Lift.blockAtoms (tfG i).core.body := by
  rw [ht] at ha
  unfold Tree.events at ha
  simp only [Tree.name, Tree.val] at ha
  cases hix : coreProgram.indexOf? f with
  | none => rw [find?_none hix] at ha; cases ha
  | some i =>
    have F := fnAt hix
    rw [F.find] at ha
    simp only at ha
    cases hw : walk σ (coreOf (i + 1)).body with
    | ret es vs =>
      rw [hw] at ha
      refine ⟨i, rfl, ?_⟩
      rw [F.core]
      exact walk_blockAtoms (σ := σ) _ (by rw [hw]; exact ha)
    | fall es => rw [hw] at ha; cases ha
    | stuck => rw [hw] at ha; cases ha

/-- **A frame run's cells**: consecutive from its first, in the frame, at no temporary's cell. -/
theorem run_cells (hok : CplOkAll) {f : String} {i : ℕ} (hix : coreProgram.indexOf? f = some i) {p r : V} {rs : List V}
    (ha : Atom.frameAddr p (r :: rs) ∈ Lift.blockAtoms (tfG i).core.body) (k : ℕ)
    (hk : k < (r :: rs).length) :
    Complete.cellP (placedG i).locs (r :: rs)[k] = some (certG f r + k) ∧ 2 ≤ certG f r + k ∧
      certG f r + k < fsWant i ∧ ∀ t ∈ coreProgram.temps f, certG f r + k ≠ certG f t := by
  have F := fnAt hix
  have E := entryOk hok F.lt
  have S := E.facts.sfacts
  obtain ⟨c, hc, hle, hrun⟩ := S.run p r rs ha
  have hcr : certG f r = c := by rw [F.cert, hc]; rfl
  obtain ⟨hck, hnt⟩ := hrun k hk
  rw [hcr]
  have hin := E.inFrame _ _ hck
  refine ⟨hck, hin.1, hin.2, fun t ht he => ?_⟩
  rw [tmps_tfG F] at ht
  obtain ⟨c', hc', -⟩ := S.tmpIn t ht
  rw [F.cert, hc'] at he
  exact hnt t ht (by rw [hc']; exact congrArg some he.symm)

/-- **A frame run's cells hold its values**, at no temporary's cell, in every tree. -/
theorem run_kfactG (hok : CplOkAll) {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {p r : V} {rs : List V}
    (he : Ev.atom (.frameAddr p (r :: rs)) ∈ I.t.events coreProgram) (k : ℕ) (hk : k < (r :: rs).length) :
    (certG f r + k, σ (r :: rs)[k]) ∈ CG I ∧ ∀ t ∈ coreProgram.temps f, certG f r + k ≠ certG f t := by
  obtain ⟨i, hix, ha⟩ := events_atomG ht he
  have F := fnAt hix
  have E := entryOk hok F.lt
  obtain ⟨hck, h2, hlt, hnt⟩ := run_cells hok hix ha k hk
  refine ⟨?_, hnt⟩
  have hfs : certG f r + k < fs f := by
    rw [F.fs_eq]; exact lt_of_lt_of_le hlt (fsWant_le i)
  rw [CG_node ht hix, nodeG, restG, ← List.append_assoc, frameE_append]
  refine dedupC_mem ?_ fun x hx hxe => ?_
  · simp only [List.mem_filter, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
    refine ⟨List.mem_append_right _ ?_, h2, hfs⟩
    simp only [runsG, List.mem_flatMap]
    exact ⟨_, he, List.mem_mapIdx.mpr ⟨k, hk, rfl⟩⟩
  · simp only [List.mem_filter, List.mem_append] at hx
    rcases hx.1 with hx | hx
    · simp only [valG, List.mem_map] at hx
      obtain ⟨t, ht', rfl⟩ := hx
      exact absurd hxe.symm (hnt t ht')
    · obtain ⟨p', r', rs', he', k', hk', rfl⟩ := mem_runsG hx
      obtain ⟨i', hix', ha'⟩ := events_atomG ht he'
      rw [hix] at hix'; cases hix'
      obtain ⟨hck', -, -, -⟩ := run_cells hok hix ha' k' hk'
      simp only at hxe
      rw [hxe] at hck'
      have S := E.facts.sfacts
      have := S.runsFun _ (mem_runVals ha (List.getElem_mem hk)) _
        (mem_runVals ha' (List.getElem_mem hk')) _ hck hck'
      rw [this, hxe]

/-! ## The checker's facts -/

theorem temps_none {f : String} (h : coreProgram.indexOf? f = none) : coreProgram.temps f = [] := by
  rw [Program.temps, find?_none h]

/-- **The temporaries' cells lie in the frame past the header.** -/
theorem certG_lt (hok : CplOkAll) : ∀ f, ∀ t ∈ coreProgram.temps f, 2 ≤ certG f t ∧ certG f t < fs f := by
  intro f t ht
  cases hix : coreProgram.indexOf? f with
  | none => rw [temps_none hix] at ht; cases ht
  | some i =>
    have F := fnAt hix
    have E := entryOk hok F.lt
    rw [tmps_tfG F] at ht
    obtain ⟨c, hc, h2, hn⟩ := E.facts.sfacts.tmpIn t ht
    rw [F.cert, hc, F.fs_eq]
    exact ⟨h2, lt_of_lt_of_le hn (fsWant_le i)⟩

/-- **Distinct temporaries have distinct cells.** -/
theorem certG_inj (hok : CplOkAll) : ∀ f, ∀ t ∈ coreProgram.temps f, ∀ t' ∈ coreProgram.temps f,
    certG f t = certG f t' → t = t' := by
  intro f t ht t' ht' he
  cases hix : coreProgram.indexOf? f with
  | none => rw [temps_none hix] at ht; cases ht
  | some i =>
    have F := fnAt hix
    have S := (entryOk hok F.lt).facts.sfacts
    rw [tmps_tfG F] at ht ht'
    obtain ⟨c, hc, -⟩ := S.tmpIn t ht
    obtain ⟨c', hc', -⟩ := S.tmpIn t' ht'
    rw [F.cert, F.cert, hc, hc'] at he
    exact S.tmpInj t ht t' ht' (by rw [hc, hc']; exact congrArg some he)

/-- **A temporary's cell holds only it**, in every instance of every tree. -/
theorem tmp_kfactG (hok : CplOkAll) {I : Inst} {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node f σ bufs kids) {t : V} (htm : t ∈ coreProgram.temps f) {q : ℕ × E}
    (hq : q ∈ CG I) (hqt : q.1 = certG f t) : q.2 = σ t := by
  cases hix : coreProgram.indexOf? f with
  | none => rw [temps_none hix] at htm; cases htm
  | some i =>
    rw [CG_node ht hix, nodeG, frameE_append] at hq
    have hlt := certG_lt hok f t htm
    have hmem := dedupC_first hq ⟨(certG f t, σ t), List.mem_filter.mpr
      ⟨List.mem_map_of_mem (f := fun v => (certG f v, σ v)) htm, by
        simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact hlt⟩, hqt.symm⟩
    obtain ⟨hq1, -⟩ := List.mem_filter.mp hmem
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hq1
    obtain rfl := certG_inj hok f t' ht' t htm hqt
    rfl

/-! ## Re-chosen temporaries -/

theorem HG_reInst {ν : ℕ → String → Val → V → E} (J : Inst) (k : ℕ) : HG (reInst ν J) k = HG J k := by
  obtain ⟨t, fp, hdr, kf, bb⟩ := J
  cases t with
  | node f σ bufs kids =>
    simp only [reInst]
    rw [retemp_node]
    unfold HG
    simp only [Tree.name]
    cases hix : coreProgram.indexOf? f with
    | none => rfl
    | some i =>
      have hkh : (FSI i ⟨.node f (retempVal coreProgram ν fp f σ) bufs
          (Tree.retempKids coreProgram fs ν (kidPos fs coreProgram.loop fp f bufs (kids.map (Tree.total fs)))
            kids), fp, hdr, kf, bb⟩ (retempVal coreProgram ν fp f σ)).kh =
          (FSI i ⟨.node f σ bufs kids, fp, hdr, kf, bb⟩ σ).kh :=
        (FSG_congr i fp kf hdr σ (retempVal coreProgram ν fp f σ) fun v hv => by
          rw [← tmps_tfG (fnAt hix)] at hv
          simp only [retempVal, hv, ↓reduceIte]).2
      simp only [hkh]
  | phantom f σ =>
    simp only [reInst]
    rw [retemp_phantom]

theorem runsG_congr {f : String} {σ σ' : Val} {es : List Ev}
    (h : ∀ p r rs, Ev.atom (.frameAddr p (r :: rs)) ∈ es → ∀ v ∈ r :: rs, σ' v = σ v) :
    runsG f σ' es = runsG f σ es := by
  unfold runsG
  refine List.flatMap_congr fun e he => ?_
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨p, _ | ⟨r, rs⟩⟩ | _ | _⟩ | _ | _ | _ <;> try rfl
  refine List.ext_getElem (by simp) fun k h1 h2 => ?_
  simp only [List.getElem_mapIdx]
  rw [h p r rs he _ (List.getElem_mem _)]

/-- **The candidates after the temporaries' do not see them.** -/
theorem restG_reInst (hok : CplOkAll) {ν : ℕ → String → Val → V → E} {I : Inst} {f : String} {σ : Val}
    {bufs : List ℕ} {kids : List Tree} {i : ℕ} (ht : I.t = .node f σ bufs kids)
    (hix : coreProgram.indexOf? f = some i) :
    restG i f (retempVal coreProgram ν I.fp f σ) (reInst ν I) = restG i f σ I := by
  have F := fnAt hix
  have hev : (reInst ν I).t.events coreProgram = I.t.events coreProgram := by
    simp only [reInst]
    rw [ht, retemp_node, events_retemp coreProgram_fresh]
  have hoff : ∀ v, v ∉ coreProgram.temps f → retempVal coreProgram ν I.fp f σ v = σ v :=
    fun v hv => by simp only [retempVal, hv, ↓reduceIte]
  unfold restG ownG
  rw [hev]
  congr 1
  · refine runsG_congr fun p r rs he v hv => hoff v fun htv => ?_
    obtain ⟨i', hix', ha⟩ := events_atomG ht he
    rw [hix] at hix'; cases hix'
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    obtain ⟨hck, -, -, hnt⟩ := run_cells hok hix ha k hk
    exact hnt _ htv (by rw [F.cert (r :: rs)[k], hck]; rfl)
  · congr 1
    refine List.filterMap_congr fun n _ => ?_
    split
    · rfl
    · next hn =>
      have hc := FSG_congr i I.fp I.kidFps I.hdr σ (retempVal coreProgram ν I.fp f σ) fun v hv =>
        hoff v (by rw [tmps_tfG F]; exact hv)
      congr 2
      refine hc.1 n fun t ht he => hn ⟨t, by rw [tmps_tfG F]; exact ht, ?_⟩
      rw [F.cert, he]; rfl

private theorem keys_valG {f : String} (σ σ' : Val) (vs : List V) (p : ℕ × E → Bool)
    (hp : ∀ a b c, p (a, b) = p (a, c)) :
    ((valG f σ vs).filter p).map Prod.fst = ((valG f σ' vs).filter p).map Prod.fst := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [valG, List.map_cons, List.filter_cons] at ih ⊢
    rw [hp _ (σ v) (σ' v)]
    split
    · simp only [List.map_cons, ih]
    · exact ih

/-- **A re-chosen instance's cells off its temporaries are its old ones.** -/
theorem CG_reInst (hok : CplOkAll) {ν : ℕ → String → Val → V → E} (I : Inst) {q : ℕ × E} (hq : q ∈ CG (reInst ν I))
    (hn : ¬ TmpOff coreProgram certG I.t q.1) : q ∈ CG I := by
  obtain ⟨t, fp, hdr, kf, bb⟩ := I
  cases t with
  | phantom f σ =>
    simp only [reInst] at hq
    rw [retemp_phantom] at hq
    exact hq
  | node f σ bufs kids =>
    cases hix : coreProgram.indexOf? f with
    | none =>
      simp only [reInst] at hq
      rw [retemp_node] at hq
      simp [CG, Tree.name, hix] at hq
    | some i =>
      have ht' : (reInst ν ⟨.node f σ bufs kids, fp, hdr, kf, bb⟩).t =
          .node f (retempVal coreProgram ν fp f σ) bufs
            (Tree.retempKids coreProgram fs ν (kidPos fs coreProgram.loop fp f bufs (kids.map (Tree.total fs)))
              kids) := by
        simp only [reInst]
        rw [retemp_node]
      rw [CG_node ht' hix, nodeG, restG_reInst hok (I := ⟨.node f σ bufs kids, fp, hdr, kf, bb⟩) rfl hix,
        frameE_append] at hq
      rw [CG_node rfl hix, nodeG, frameE_append]
      refine dedupC_swap (keys_valG _ _ _ _ fun _ _ _ => rfl) hq fun hm => hn ?_
      obtain ⟨⟨k, w⟩, hkw, hk⟩ := List.mem_map.mp hm
      obtain ⟨hkw, -⟩ := List.mem_filter.mp hkw
      obtain ⟨v, hv, hve⟩ := List.mem_map.mp hkw
      simp only [Prod.mk.injEq] at hve
      exact ⟨f, σ, bufs, kids, rfl, v, hv, by rw [← hk, ← hve.1]⟩

/-- **`main`'s cells hold its jump table.** -/
theorem tableG (hok : CplOkAll) {I : Inst} {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node "main" σ bufs kids) : tableCells ⊆ CG I := by
  intro q hq
  have hix : coreProgram.indexOf? "main" = some 0 := by
    obtain ⟨i, he, hi⟩ := ix_of_idx main_idx
    obtain rfl : i = 0 := by omega
    exact hi
  have F := fnAt hix
  have E := entryOk hok F.lt
  have hlo : Deployed.Data.mainCells ≤ q.1 := by
    have := tableCells_offsets ▸ List.mem_map_of_mem (f := Prod.fst) hq
    rw [List.mem_range'_1] at this
    exact this.1
  have hoff := tableCells_off hq
  have hpre : ∀ x ∈ valG "main" σ (coreProgram.temps "main") ++
      (runsG "main" σ (I.t.events coreProgram) ++ ownG 0 "main" σ I), x.1 < Deployed.Data.mainCells := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨t, htm, rfl⟩ := List.mem_map.mp hx
      rw [tmps_tfG F] at htm
      obtain ⟨c, hc, -, hn⟩ := E.facts.sfacts.tmpIn t htm
      dsimp only
      rw [F.cert, hc]
      simpa [fsWant] using hn
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p, r, rs, he, k, hk, rfl⟩ := mem_runsG hx
      obtain ⟨i', hix', ha⟩ := events_atomG ht he
      rw [hix] at hix'; cases hix'
      exact (run_cells hok hix ha k hk).2.2.1
    · obtain ⟨n, hn, hx⟩ := List.mem_filterMap.mp hx
      split at hx
      · cases hx
      · cases hx
        rw [E.facts.sfacts.frame] at hn
        exact List.mem_range.mp hn
  have hfs : fs "main" = mainFrame := by rw [F.fs_eq]; rfl
  simp only [CG_node ht hix, nodeG, restG, ↓reduceIte]
  rw [← List.append_assoc, ← List.append_assoc, hfs, frameE,
    ← List.append_nil (List.filter _ _)]
  refine dedupC_mem (List.mem_filter.mpr ⟨List.mem_append_right _ hq, ?_⟩) fun x hx he => ?_
  · simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]
    exact ⟨hoff.1, hoff.2⟩
  · obtain ⟨hx, -⟩ := List.mem_filter.mp hx
    rcases List.mem_append.mp hx with hx | hx
    · have := hpre x (by simpa only [List.append_assoc] using hx)
      omega
    · exact Prod.ext he (tableCells_agree hx hq he)

/-- **The checker's facts for every tree of `main`.** -/
theorem kFactsAllG (hok : CplOkAll) : End.KFactsAll fs HG CG certG := fun hdr T _ =>
  { cells := cellsOk_frameE CG_shape _
    cells' := fun _ => cellsOk_frameE CG_shape _
    cert_lt := certG_lt hok
    cert_inj := certG_inj hok
    run := fun _ _ _ _ _ _ ht _ _ _ he k hk => run_kfactG hok ht he k hk
    tmp := fun _ _ _ _ _ _ _ ht _ htm _ hq hqt => tmp_kfactG hok ht htm hq hqt
    keep := fun ν I hI I' hI' hfp _ q hq hn => by
      obtain rfl := reInst_of_honest coreProgram_fresh (fun J k => HG_reInst J k) hI hI' hfp
      simp only [Inst.cells, List.mem_cons] at hq ⊢
      rcases hq with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (CG_reInst hok I h hn)) }

end
end LeanVM.Guest.Backend.Cpl
