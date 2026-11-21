/-
  LeanVM.Guest.EndExecA

  The bump pointer's track: past the prologue, the executor's next free cell is the top frame's
  cursor, and each frame below resumes where the frame above ends.
-/

module

public import LeanVM.Guest.EndExecCAlign
public import LeanVM.Guest.Bridge.AllocLink
public import LeanVM.Guest.Bridge.AllocSound
public import LeanVM.Guest.Bridge.AllocCur
public import LeanVM.Guest.Memory.Cursor
public import LeanVM.Guest.Memory.HeapPops
public import LeanVM.Guest.Bridge.AllocAdv

/-!
# The bump pointer's track

`cursorAt A e off`: frame `e`'s cursor (`Inst.curAt`) at offset `off` of its function, past the
buffers the function reserves before `off` (`Bridge.nbAt`) and the calls the frame has made, plus
the next callee's block while its frame is reserved and not entered (`Bridge.pendAt`). `ChainA`:
each frame below the top resumes, at the return pc the header of the frame above holds, at the
cursor where that frame's subtree ends (`Inst.endCur`), and a loop iteration past all its calls has
a phantom last callee (`TailA`). `NcTop A e off`: at an offset at or before a buffer hint the frame has made no call (the
check puts every call after the buffer hints). `YAlloc A r s`: in the prologue the next
free cell is past `main`'s frame and nothing is popped from `heap_sizes`; past it, a state of the
tree track at the state's pc and frame whose top frame's cursor is the next free cell, its frames
chained, `NcTop` at its offset, and whose advised sizes still to pop are the rest of the stream
(`HeapAt`).

The advised sizes (`heap_sizes`, popped by `allocAdvice`, each a buffer hint before its function's
first jump, `Bridge.advChk`): `slotsOf F`, the buffer indices a function's advice stands for;
`advBefore F off`, those it pops before offset `off`; `restH A st off`, the entries the frames `st`
still pop, the top frame at offset `off`: its own past `advBefore`, then each frame's callees not yet
called (`Memory.Tree.heapPopsKids`); `ChainH`: each frame below resumes past its function's first
jump, its advice all popped. `HeapAt A r s e st`: the stream (`heapStream`) past the executor's
cursor is `restH`, the frames `ChainH`, and the advised pointer cells whose buffers exist written
(`AdvWr`: the top frame's before its offset, every frame's below). `HeapPops`: the honest pushes of `heap_sizes` are the
reference tree's advised sizes (`Memory.Tree.heapPops advSlots`).

Proved here: the track holds initially (`initY_alloc`), and the reference holds a buffer's base at
its hint's pointer cell (`bufBase_ref`: the `k`-th buffer hint of a function passing the allocation
check compiles the `k`-th allocation atom of every path, `Bridge.allocShape_walk`, whose pointer the
placement puts at the instance's cursor past the buffers before it, `Bridge.EntOk.alloc_at`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-- **Frame `e`'s cursor at offset `off`**: past the buffers its function reserves before `off`
and its calls made, and the next callee's block while that callee's frame is reserved and not
entered. -/
noncomputable def cursorAt (A : String → FnAl) (e : Ent) (off : ℕ) : ℕ :=
  e.I.curAt B2C.fs coreProgram.loop (nbAt (A e.I.t.name).X (A e.I.t.name).d off) e.nc +
    bif pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off then
      (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0
    else 0

/-- The indices, from `k`, of the advised buffers' hints among buffer hints. -/
def advIdx : ℕ → List (ℕ × Hint) → List ℕ
  | _, [] => []
  | k, q :: l => if isAdv q.2 then k :: advIdx (k + 1) l else advIdx (k + 1) l

/-- **The buffer indices a function's `allocAdvice` hints stand for**, in order. -/
noncomputable def slotsOf (F : FnAl) : List ℕ := advIdx 0 (bufsOf F.X F.d)

/-- The advised sizes the deployed functions pop, by name. -/
noncomputable def advSlots (f : String) : List ℕ := slotsOf (alignA f)

/-- **The advised sizes a frame of `F` pops before offset `off`.** -/
noncomputable def advBefore (F : FnAl) (off : ℕ) : ℕ :=
  (allocHints F.d).countP fun q ↦ decide (q.1 < off) && isAdv q.2

/-- The advised sizes frame `e`'s callees not yet called pop. -/
noncomputable def kidsH (A : String → FnAl) (e : Ent) : List (List E) :=
  Tree.heapPopsKids (fun f ↦ slotsOf (A f)) (e.I.t.kids.drop e.nc)

/-- **The advised sizes the frames still pop**, the top one at offset `off`. -/
noncomputable def restH (A : String → FnAl) : List Ent → ℕ → List (List E)
  | [], _ => []
  | e :: st, off => ((slotsOf (A e.I.t.name)).map (advEntry e.I.t.bufs)).drop (advBefore (A e.I.t.name) off) ++
      kidsH A e ++ st.flatMap (kidsH A)

/-- **Each frame below resumes past its function's first jump**, at the return pc the header of the
frame above holds. -/
def ChainH (A : String → FnAl) (M : ℕ → E) : List Ent → Prop
  | e :: e' :: st => (∃ r, M (e.I.fp + 0) = ofK (addressOfIndex r) ∧ r < 2 ^ 63 ∧
      nextJump (A e'.I.t.name).code 0 ≤ r - entOf A e'.I.t.name) ∧ ChainH A M (e' :: st)
  | _ => True

/-- **The honest pushes of `heap_sizes`**, their entries in order. -/
noncomputable def heapStream (r : Ref) : List (List E) :=
  ((Hints.honestPushes End.bytecode r.seed r.s r.w).filter (·.1 == Hints.heapSizeStream)).map (·.2)

/-- **Frame `e`'s advised pointer cells written** before offset `off`: each `allocAdvice` there whose
buffer exists. -/
def AdvWrTop (A : String → FnAl) (m : Mem) (e : Ent) (off : ℕ) : Prop :=
  ∀ k o p S, (bufsOf (A e.I.t.name).X (A e.I.t.name).d)[k]? = some (o, .allocAdvice p S) → o < off →
    k < e.I.t.bufs.length → m.written (e.I.fp + p) = true

/-- **The advised pointer cells written**: the top frame's before offset `off`, every frame's below. -/
def AdvWr (A : String → FnAl) (m : Mem) : List Ent → ℕ → Prop
  | [], _ => True
  | e :: st, off => AdvWrTop A m e off ∧ ∀ e' ∈ st, ∀ o, AdvWrTop A m e' o

/-- **The advised sizes' track at a state**: the stream past the cursor is what the frames still pop,
the frames below resume past their advice, whose pointer cells are written. -/
abbrev HeapAt (A : String → FnAl) (r : Ref) (s : St) (e : Ent) (st : List Ent) : Prop :=
  (heapStream r).drop (s.cursor.getD Hints.heapSizeStream 0) = restH A (e :: st) (s.pc - entOf A e.I.t.name) ∧
    ChainH A (memOf r.img) (e :: st) ∧ AdvWr A s.mem (e :: st) (s.pc - entOf A e.I.t.name)

/-- **The honest pushes of `heap_sizes` are the reference tree's advised sizes.** -/
def HeapPops : Prop := ∀ r : Ref, r.Ok → heapStream r = r.T.heapPops advSlots

/-- **A loop iteration past all its calls ended its loop**: its last callee, past which the frame's
cursor would go, is a phantom (`total = block`). -/
def TailA (e : Ent) : Prop :=
  coreProgram.loop e.I.t.name = true → e.I.t.kids.length ≤ e.nc → ∀ hk : e.I.t.kids ≠ [],
    (e.I.t.kids.getLast hk).total B2C.fs = (e.I.t.kids.getLast hk).block B2C.fs coreProgram.loop

/-- **No call before the buffers**: at an offset at or before a buffer hint of its function, the
frame has made no call. -/
def NcTop (A : String → FnAl) (e : Ent) (off : ℕ) : Prop :=
  (∃ q ∈ bufsOf (A e.I.t.name).X (A e.I.t.name).d, off ≤ q.1) → e.nc = 0

/-- **Each frame below resumes where the frame above ends**: at the return pc the header of the
frame above holds in `M`, its cursor that frame's end, no call made there before the buffers
(`NcTop`); and each frame `TailA`. -/
def ChainA (A : String → FnAl) (M : ℕ → E) : List Ent → Prop
  | [] => True
  | [e] => TailA e
  | e :: e' :: st => TailA e ∧ (∃ r, M (e.I.fp + 0) = ofK (addressOfIndex r) ∧ r < 2 ^ 63 ∧
      e.I.endCur B2C.fs coreProgram.loop = cursorAt A e' (r - entOf A e'.I.t.name) ∧
      NcTop A e' (r - entOf A e'.I.t.name)) ∧ ChainA A M (e' :: st)

/-- **The bump pointer's track**: in the prologue the next free cell is past `main`'s frame; past
it, a state of the tree track at the state's pc and frame whose top frame's cursor is the next free
cell, its frames chained. -/
def YAlloc (A : String → FnAl) (r : Ref) (s : St) : Prop :=
  (s.steps < proLen → s.nextFree = r.adv.mainFrame ∧ s.cursor.getD Hints.heapSizeStream 0 = 0) ∧
    (proLen ≤ s.steps → s.steps < r.n → ∃ done e st, RefTrack A r s.pc s.fp (done, e :: st) ∧
      s.nextFree = cursorAt A e (s.pc - entOf A e.I.t.name) ∧ ChainA A (memOf r.img) (e :: st) ∧
      NcTop A e (s.pc - entOf A e.I.t.name) ∧ HeapAt A r s e st)

end

public section

/-- **The bump pointer's track holds initially.** -/
theorem initY_alloc (A : String → FnAl) : InitY (YAlloc A) := by
  intro r hr C m hC hm
  refine ⟨fun _ ↦ ⟨rfl, Std.HashMap.getD_empty⟩, fun h ↦ ?_⟩
  exact absurd h (by show ¬ proLen ≤ 0; rw [proLen_eq]; norm_num)

theorem compilesA_ptr {X : AlignCtx} {fs : ℕ} {a : Core.Hint} {h : Prover.Exec.Hint} (hc : compilesA X fs a h = true)
    {p : ℕ} (hp : allocPtr h = some p) :
    allocCellOk X fs (allocDstOf a) = true ∧ X.locAt (allocDstOf a).idx = p := by
  cases a <;> cases h <;> simp_all [compilesA, allocPtr, allocDstOf, Bool.and_eq_true, Nat.beq_eq]

theorem allocDst_mem {es : List Ev} {d : V} (h : d ∈ allocDsts es) : ∃ a, Ev.atom a ∈ es ∧ d ∈ atomUses a := by
  obtain ⟨e, he, hd⟩ := List.mem_filterMap.mp h
  rcases e with ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ | _⟩ | _ | _ | _ <;>
    simp only [Ev.allocDst?, reduceCtorEq, Option.some.injEq] at hd <;> subst hd <;>
    exact ⟨_, he, by simp [atomUses, hintUses]⟩

/-- **A value's cell holds it on the reference**: at a frame of the tree track of function `j`, a
value an atom of its path uses, whose cell the allocation check admits (`allocCellOk`), is at that
cell of the frame, below `maxCells`. -/
theorem cellRef {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (hT : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} (hj : B2C.idxOf e.I.t.name = some j) {v : V}
    (hv : ∃ a, Ev.atom a ∈ e.pre ++ e.es ∧ v ∈ atomUses a) (hcell : allocCellOk (ctxOf j) (B2C.fsN j) v = true) :
    e.I.fp + (ctxOf j).locAt v.idx < maxCells ∧ refMem r.img (e.I.fp + (ctxOf j).locAt v.idx) = e.σ v := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, hFH⟩ :=
    (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := hT.track.ents e List.mem_cons_self
  obtain ⟨at', hat, hdu⟩ := hv
  have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
  have hA2 : alignA e.I.t.name = fnAl j := alignA_of hj
  rcases hx : (ctxOf j).extra.lookup v.idx with _ | c
  · simp only [allocCellOk, hx, Option.isSome_none, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hcell
    obtain ⟨-, hlocC⟩ := pairOk_alignA _ _ j hE.find hj
    have hx' : (alignA e.I.t.name).X.extra.lookup v.idx = none := by rw [hA2]; exact hx
    have hlc : (ctxOf j).locAt v.idx = (certOf j).locs.getD v.idx 0 := by
      have := hlocC v.idx hx' hcell.1.1
      rwa [hA2] at this
    have hcj : B2C.cellJ j v = (ctxOf j).locAt v.idx := hlc.symm
    rw [← hcj] at hcell ⊢
    have hrd := hFH.val v (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hat, hdu⟩)))
      hcell.1.2 hcell.2
    obtain ⟨i, -, -, -, -, -, hfs, -⟩ := B2C.fn_of_idx hj
    have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ r.T.total B2C.fs :=
      honest_within hI (by have := hHon.cells.two_le e.I hI; omega)
    have h28 : r.T.total B2C.fs ≤ 2 ^ r.κ := le_two_pow_logMem _
    have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
    exact refRd_img hκ r.img _ _ (by rw [hfs] at hwithin; omega) hrd
  · have hx' : (alignA e.I.t.name).X.extra.lookup v.idx = some c := by rw [hA2]; exact hx
    obtain ⟨hlt, hrd⟩ := hr.extra e.I hI _ _ bufs kids hIt v (by rw [hevs]; exact List.mem_flatMap.mpr ⟨_, hat, hdu⟩) c hx'
    have hlc : (ctxOf j).locAt v.idx = c := by
      unfold Bridge.AlignCtx.locAt; rw [hx]; rfl
    rw [hlc]
    have := refRd_img hκ r.img (e.I.fp + c) _ (by omega) hrd
    exact this

/-- **The reference holds a buffer's base at its hint's pointer cell**: at a frame of the tree track
whose function passes the allocation check, the `k`-th buffer hint's pointer cell holds
`g^(cur + bufs[0] + … + bufs[k-1])`, the instance's cursor past the buffers before it. -/
theorem bufBase_ref {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent}
    {st : List Ent} (hT : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} (hj : B2C.idxOf e.I.t.name = some j)
    (hA : AllocJ j) {k : ℕ} {h : Prover.Exec.Hint}
    (hk : (((allocHints (adviceOf j)).filter fun q ↦ isBuf (ctxOf j) q.2).map (·.2))[k]? = some h)
    {p : ℕ} (hp : allocPtr h = some p) :
    k < e.I.t.bufs.length ∧ e.I.fp + p < maxCells ∧
      refMem r.img (e.I.fp + p) = ofK (addressOfIndex (e.I.cur + (e.I.t.bufs.take k).sum)) := by
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, hFH⟩ :=
    (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := hT.track.ents e List.mem_cons_self
  -- the check
  have hA' := hA
  simp only [AllocJ, allocChk, allocRest, Bool.and_eq_true] at hA'
  obtain ⟨⟨hshape, -⟩, hpairs, -⟩ := hA'
  obtain ⟨a, ha, hca⟩ := pairsA_get hpairs k h hk
  obtain ⟨hcell, hloc⟩ := compilesA_ptr hca hp
  -- the path allocates the atoms in order
  have hw0 := hw
  rw [← hfn] at hw
  have hds := allocDsts_of_shape hshape hw
  have hdk : (allocDsts (e.pre ++ e.es))[k]? = some (allocDstOf a) := by
    rw [hds, List.getElem?_map, ha]; rfl
  -- the placement
  obtain ⟨t, ν, hv, -, hpl, -, -, -, hTt⟩ := hr.tree
  have hTp : r.T.Placed coreProgram B2C.fs B2C.cert (0, r.T.block B2C.fs coreProgram.loop) := by
    rw [hTt, block_retemp]
    exact placed_retemp coreProgram_fresh t _ hv hpl
  have hI' : e.I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
  have hIp := insts_placedAt r.T _ r.hdr hTp e.I hI'
  have hIP := insts_placed r.T _ r.hdr (by omega) e.I hI'
  have hE' : EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) { e with nb := k } :=
    ⟨hE.mem, hE.node, hE.find, hE.path, hE.kids⟩
  obtain ⟨hσ, hlt⟩ := hE'.alloc_at (cert := B2C.cert) hIp hIP hdk
  refine ⟨hlt, ?_⟩
  -- the pointer's cell
  have hdmem : allocDstOf a ∈ allocDsts (e.pre ++ e.es) := List.mem_of_getElem? hdk
  obtain ⟨hc1, hc2⟩ := cellRef hr hT hj (allocDst_mem hdmem) hcell
  rw [hloc] at hc1 hc2
  exact ⟨hc1, hc2.trans hσ⟩

end

end LeanVM.Guest.EndExec
