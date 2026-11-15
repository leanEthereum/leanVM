/-
  LeanVM.Guest.EndExecAReady

  Each allocation hint has what it needs where the tree puts the bump pointer: `AllocReady` on the
  deployed alignment, from the facts the static checks do not give, each named.
-/

module

public import LeanVM.Guest.EndExecACur
public import LeanVM.Guest.Bridge.AllocIdx

/-!
# The allocation hints ready

`allocReady_alignA : DynPow → AdvNext alignA → LateReady alignA → FrameReady alignA → ExclReady alignA →
AllocReady alignA`, `sizesAt_alignA` likewise for `SizesAt alignA`, `frameReady_of : FrameSize alignA →
FramePtr alignA → FrameReady alignA`; `AllocGaps` gathers what is named. At the `i`-th hint of a
frame's offset (`HintAt`), the bump pointer the frame's cursor moved by the words the hints before it
reserve:

* a buffer hint of a function the allocation check admits is the buffer hint of index `bufIdx`
  (`Bridge.bufsOf_idx`); no frame hint before it (`Bridge.buf_noFrame`), no call made
  (`NcTop`), so the bump pointer is the instance's cursor past the buffers before it, where the
  reference puts its base (`bufBase_ref`); its size is the path's (`Tree.BufsOk`, `allocs_of_shape`),
  a constant's (`JumpCells.pcw`), a dynamic size's (`DynPow`), or the stream's (`AdvNext`); the
  buffer ends within the instance's subtree, which ends within the tree (`endCur_chain`);
* a callee frame's hint: nothing pending and no frame hint before it at its offset (`FrUniq`),
  every buffer hint before it (`Bridge.frame_allBufs`), so the bump pointer is the instance's cursor
  past its buffers and callees so far, the next callee's block within the subtree;
* a cell's address, at a fixed cell of the frame (`FrameHolds.stat`), the cell below the frame size
  (`Bridge.addrOk`); a next frame's address, in a loop helper whose tail callee's frame follows its
  own (`Memory.tail_pos`), within the tree.

The words each hint reserves (`SizesAt`) follow the same way: a buffer's from its atom, a late hint's
none, a frame's from its size (`rsz_of_sizeOk`).

What is named here, proved elsewhere: `DynPow`, every dynamic `HeapBuf`'s size is a power of `g`
(what the path computes; `dynPow_guest`, `EndExecADyn.lean`), `FrameSize` and `FramePtr`
(`EndExecAFrSize.lean`, `EndExecAFrame.lean`): a callee frame's hint reserves the next callee's
block (`SizeOk`: a constant, a dispatch arm's by its selector, a loop chain's by its bound), its
pointer cell the next callee's frame (the next call, reached by the straight code to the call site's
jump, `FrameHolds.site`); `AdvNext`, an `allocAdvice` pops the `heap_sizes` entry of its buffer's
size, empty when the path allocates none (`advNext_alignA`, `EndExecAHeap.lean`, from the advised
sizes' track `HeapAt`). Named, not proved:

* `LateReady`: a late hint finds its buffer reserved, its size cell a power;
* `ExclReady`: the buffer hints of the function the allocation check excludes (`claim_list_digest`,
  its one buffer in a branch).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec

@[expose] public section

/-- **The `i`-th hint `h` at a state `s` of the tree track** on the reference run, top frame `e`, its
frames chained, no call before its buffers, run from the state `sx` the hints before it reach, whose written cells hold
the reference's words. -/
structure HintAt (A : String → FnAl) (r : Ref) (C : Ctx) (e : Ent) (s sx : St) (i : ℕ) (h : Hint) : Prop where
  ok : r.Ok
  ctx : Ctx.of guestProgram r.adv = .ok C
  track : ∃ done st, RefTrack A r s.pc s.fp (done, e :: st) ∧ ChainA A (memOf r.img) (e :: st) ∧ HeapAt A r s e st
  nc : NcTop A e (s.pc - entOf A e.I.t.name)
  fine : Fine (refMem r.img) s
  onref : OnRef guestProgram r.img r.n s
  get : ((C.hints[s.pc]?).getD [])[i]? = some h
  pre : (((C.hints[s.pc]?).getD []).take i).foldlM (runHint C) s = .ok sx
  agree : ∀ c v, sx.mem.get c = some v → refMem r.img c = v

/-- The buffer index of the `i`-th hint at offset `off` of frame `e`: the buffer hints before it. -/
noncomputable def bufIdx (A : String → FnAl) (e : Ent) (off i : ℕ) : ℕ :=
  nbAt (A e.I.t.name).X (A e.I.t.name).d off + ((hintsAtOff (A e.I.t.name) off).take i).countP (isBuf (A e.I.t.name).X)

/-- **Every dynamic `HeapBuf`'s size is a power of `g`**, at each entered instance of every reference
tree. -/
def DynPow : Prop :=
  ∀ r : Ref, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ f σ bufs kids,
    I.t = .node f σ bufs kids → ∀ d s,
    Ev.atom (.hint (.allocDyn d s)) ∈ I.t.events coreProgram → I.t.val s = ofK (addressOfIndex (logG (I.t.val s)))

/-- **An `allocAdvice` pops its buffer's size**: the next entry of its stream is the size of the
buffer of its index, empty when the path allocates none. -/
def AdvNext (A : String → FnAl) : Prop :=
  ∀ r C e s sx i p S, HintAt A r C e s sx i (.allocAdvice p S) →
    StreamNext C sx S (match e.I.t.bufs[bufIdx A e (s.pc - entOf A e.I.t.name) i]? with
      | some n => [ofK (addressOfIndex n)]
      | none => [])

/-- **A late hint finds its buffer reserved**, its size a power below `maxCells`. -/
def LateReady (A : String → FnAl) : Prop :=
  ∀ r C e s sx i p b, HintAt A r C e s sx i (.allocLate p b) → sx.mem.written (sx.fp + p) = true ∧ ∃ n, BufOk sx b n

/-- **A callee frame's hint reserves the next callee's block**, and has what it needs where the tree
puts the bump pointer, the cells it reads written. -/
def FrameReady (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h, HintAt A r C e s sx i h → isFrame (A e.I.t.name).X h = true →
    rsz C (refMem r.img) sx h =
        (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0 ∧
      (Mode.HintIn sx h → sx.nextFree = cursorAt A e (s.pc - entOf A e.I.t.name) +
          ((treeSizes A e (s.pc - entOf A e.I.t.name)).take i).sum → HintOk C (refMem r.img) sx h)

/-- **A callee frame's hint reserves `B` words**, its size read off `M` at frame `fp`: a constant, a
dispatch arm's by its selector, or a loop chain's by its bound. -/
def SizeOk (M : ℕ → E) (fp : ℕ) : Hint → ℕ → Prop
  | .alloc _ n, B => n = B
  | .allocArm _ sel sizes, B => ∃ k, M (fp + sel) = ofK (Parameters.g ^ k) ∧ k < maxCells ∧ sizes[k]? = some B
  | .allocFrames _ size stop si tail, B => ∃ v n, M (fp + stop) = ofK v ∧ v * si = Parameters.g ^ n ∧ n < maxCells ∧
      size * n + tail = B
  | _, _ => False

/-- **A callee frame's hint reserves the next callee's block**, its sizes read off the reference. -/
def FrameSize (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h, HintAt A r C e s sx i h → isFrame (A e.I.t.name).X h = true →
    SizeOk (refMem r.img) sx.fp h ((((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0)

/-- **A callee frame's pointer cell holds the next callee's frame**: the instance's cursor past its
buffers and its callees so far. -/
def FramePtr (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h p, HintAt A r C e s sx i h → isFrame (A e.I.t.name).X h = true → allocPtr h = some p →
    e.I.fp + p < maxCells ∧
      refMem r.img (e.I.fp + p) = ofK (addressOfIndex (e.I.curAt B2C.fs coreProgram.loop e.I.t.bufs.length e.nc))

/-- **The buffer hints of the functions the allocation check excludes** reserve the buffers of
their index, and have what they need where the tree puts the bump pointer. -/
def ExclReady (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h j, HintAt A r C e s sx i h → B2C.idxOf e.I.t.name = some j → j ∈ AllocChk.allocExcl →
    isBuf (A e.I.t.name).X h = true →
    rsz C (refMem r.img) sx h = e.I.t.bufs.getD (bufIdx A e (s.pc - entOf A e.I.t.name) i) 0 ∧
    (sx.nextFree = cursorAt A e (s.pc - entOf A e.I.t.name) +
        ((treeSizes A e (s.pc - entOf A e.I.t.name)).take i).sum → HintOk C (refMem r.img) sx h)

end

public section

/-! ## The tree -/

mutual
/-- **Every instance of a tree whose buffers are its paths' has its path's buffers.** -/
theorem insts_bufsOk {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E} {P : Core.Program} :
    ∀ (t : Tree) (p : ℕ × ℕ) (hdr : E × E), t.BufsOk P → ∀ I ∈ t.insts fs lp H p hdr, I.t.BufsOk P
  | .node f σ bufs kids, p, hdr, hb, I, hI => by
      rw [insts_node, List.mem_cons] at hI
      rcases hI with rfl | hI
      · exact hb
      · simp only [Tree.BufsOk] at hb
        exact instsKids_bufsOk kids _ _ 0 hb.2 I hI
  | .phantom .., p, hdr, _, I, hI => by
      rw [insts_phantom, List.mem_singleton] at hI
      subst hI
      simp [Tree.BufsOk]

/-- `insts_bufsOk` for the callees. -/
theorem instsKids_bufsOk {fs : String → ℕ} {lp : String → Bool} {H : Inst → ℕ → E × E} {P : Core.Program} :
    ∀ (ks : List Tree) (ps : List (ℕ × ℕ)) (J : Inst) (j : ℕ), Tree.BufsOkKids P ks →
      ∀ I ∈ Tree.instsKids fs lp H J j ps ks, I.t.BufsOk P
  | [], _, _, _, _, I, hI => by rw [instsKids_nil] at hI; exact (List.not_mem_nil hI).elim
  | _ :: _, [], _, _, _, I, hI => by
      rw [instsKids_nil_left] at hI; exact (List.not_mem_nil hI).elim
  | k :: ks, p :: ps, J, j, hb, I, hI => by
      simp only [Tree.BufsOkKids] at hb
      rw [instsKids_cons, List.mem_append] at hI
      rcases hI with hI | hI
      · exact insts_bufsOk k p _ hb.1 I hI
      · exact instsKids_bufsOk ks ps J (j + 1) hb.2 I hI
end

/-- **The cursor stays within the frame's subtree.** -/
theorem cursorAt_le_endCur (A : String → FnAl) {e : Ent} (hn : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids)
    (off : ℕ) : cursorAt A e off ≤ e.I.endCur B2C.fs coreProgram.loop := by
  unfold cursorAt
  cases pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off
  · simp only [Bool.cond_false, Nat.add_zero]; exact curAt_le_endCur hn _ _
  · simp only [Bool.cond_true]
    rcases hk : (e.I.t.kidsC coreProgram.loop)[e.nc]? with _ | k
    · simp only [Option.map_none, Option.getD_none, Nat.add_zero]; exact curAt_le_endCur hn _ _
    · have hlt := (List.getElem?_eq_some_iff.mp hk).1
      have hk' : (e.I.t.kidsC coreProgram.loop)[e.nc] = k := (List.getElem?_eq_some_iff.mp hk).2
      have := curAt_block_le (fs := B2C.fs) (nb := nbAt (A e.I.t.name).X (A e.I.t.name).d off) hn hlt
      rw [hk'] at this
      simpa only [Option.map_some, Option.getD_some] using this

/-- **Each frame's subtree ends within the tree**: the bottom frame is the root's, at frame `0`, its
subtree the tree; each frame above ends where the one below resumes. -/
theorem endCur_chain {A : String → FnAl} {r : Ref} (hr : r.Ok) :
    ∀ (st : List Ent) (e : Ent) (pc fp : ℕ),
      (∀ x ∈ e :: st, EntOk coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) x) →
      Linked (memOf r.img) (entOf A) (alOf A) pc fp (e :: st) → ChainA A (memOf r.img) (e :: st) →
      e.I.endCur B2C.fs coreProgram.loop ≤ r.T.total B2C.fs
  | [], e, pc, fp, hE, hL, _ => by
    obtain ⟨rd, hHon, -⟩ := hr.honest
    obtain ⟨hfp, h0, -⟩ := hL
    obtain ⟨I, rest, he, hIt, hIfp, hcur, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H)
      r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr
    have hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T := by rw [honestInsts, he]; exact List.mem_cons_self
    have heI := (hE e List.mem_cons_self).mem
    have hpw := insts_pairwise (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H) r.T
      (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega)
    have hEq : e.I = I := inst_eq_of_fp hpw heI hI (by rw [hfp, h0, hIfp])
      (by have := hHon.cells.two_le e.I heI; omega) (by have := hHon.cells.two_le I hI; omega)
    rw [hEq, Inst.endCur, hIt, hcur]
    have := block_le_total (fs := B2C.fs) (lp := coreProgram.loop) r.T
    omega
  | e' :: st, e, pc, fp, hE, hL, hC => by
    obtain ⟨-, -, r0, -, -, hL'⟩ := hL
    obtain ⟨-, ⟨r1, -, -, hend, -⟩, hrest⟩ := hC
    have ih := endCur_chain hr st e' r0 e'.I.fp (fun x hx ↦ hE x (List.mem_cons_of_mem _ hx)) hL' hrest
    have hn := (hE e' (List.mem_cons_of_mem _ List.mem_cons_self)).node
    have := cursorAt_le_endCur A (e := e') ⟨_, _, _, _, hn.choose_spec.choose_spec.choose_spec⟩
      (r1 - entOf A e'.I.t.name)
    omega

/-! ## Sizes in order -/

theorem tsz_take {α : Type} (p q : α → Bool) (g : ℕ → ℕ) (B : ℕ) :
    ∀ (hs : List α) (n i : ℕ), tsz p q g B (hs.take i) n = (tsz p q g B hs n).take i
  | [], n, i => by simp [tsz]
  | a :: hs, n, 0 => by simp [tsz]
  | a :: hs, n, i + 1 => by
    rw [List.take_succ_cons, tsz_cons, tsz_cons, List.take_succ_cons, tsz_take p q g B hs]

theorem treeSizes_eq (A : String → FnAl) (e : Ent) (off : ℕ) :
    treeSizes A e off = tsz (isBuf (A e.I.t.name).X) (isFrame (A e.I.t.name).X) (fun k ↦ e.I.t.bufs.getD k 0)
      ((((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0)
      (hintsAtOff (A e.I.t.name) off) (nbAt (A e.I.t.name).X (A e.I.t.name).d off) := by
  simp only [treeSizes, tsz]
  refine List.map_congr_left fun i _ ↦ ?_
  cases (hintsAtOff (A e.I.t.name) off)[i]? <;> rfl

/-- **The words the hints before a buffer hint reserve**: the buffers before it, no frame hint
being before it. -/
theorem treeSizes_take_buf (A : String → FnAl) (e : Ent) (off i : ℕ)
    (h0 : ((hintsAtOff (A e.I.t.name) off).take i).countP (isFrame (A e.I.t.name).X) = 0) :
    (e.I.t.bufs.take (nbAt (A e.I.t.name).X (A e.I.t.name).d off)).sum + ((treeSizes A e off).take i).sum =
      (e.I.t.bufs.take (bufIdx A e off i)).sum := by
  rw [treeSizes_eq, ← tsz_take, tsz_sum]
  have : ((hintsAtOff (A e.I.t.name) off).take i).countP
      (fun h ↦ !isBuf (A e.I.t.name).X h && isFrame (A e.I.t.name).X h) = 0 := by
    have := List.countP_mono_left (l := (hintsAtOff (A e.I.t.name) off).take i)
      (p := fun h ↦ !isBuf (A e.I.t.name).X h && isFrame (A e.I.t.name).X h) (q := isFrame (A e.I.t.name).X)
      (fun x _ hx ↦ by simp only [Bool.and_eq_true] at hx; exact hx.2)
    omega
  rw [this, Nat.zero_mul, Nat.add_zero, take_sum_range]
  rfl

/-! ## A hint at a frame -/

/-- **The hints at a frame's pc are its function's at the offset.** -/
theorem hint_off {r : Ref} {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s : St}
    {done : List Pop} {e : Ent} {st : List Ent} (htr : RefTrack alignA r s.pc s.fp (done, e :: st)) {i : ℕ}
    {h : Hint} (hget : ((C.hints[s.pc]?).getD [])[i]? = some h) :
    ∃ off, s.pc = entOf alignA e.I.t.name + off ∧ (C.hints[s.pc]?).getD [] = hintsAtOff (alignA e.I.t.name) off := by
  have hpcS : s.pc < C.ops.size := by
    by_contra hge
    have hsz := (ctx_hints_size hC).trans (ctx_of_spec hC).1.symm
    rw [Array.getElem?_eq_none (by omega)] at hget
    simp at hget
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨-, hat⟩ := htr.linked.top
  obtain ⟨off, hpc, p, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (progAl.ok _ _ hE.find) hal'
  have hsize := (ctx_of_spec hC).1
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (by rw [← hsize]; exact hpcS)
  refine ⟨off, hpc, ?_⟩
  rw [hh, hintsAtOff, advAl_alignA _ _ hE.find off ins hins]
  rw [hpc]
  rfl

theorem hintsAtOff_eq (F : FnAl) (off : ℕ) : hintsAtOff F off = hintsAtD F.d F.X.entry off := rfl

theorem bufs_of_ok {t : Tree} {P : Core.Program} (h : t.BufsOk P) {f : String} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} (ht : t = .node f σ bufs kids) : bufs = allocs σ (t.events P) := by
  subst ht; simp only [Tree.BufsOk] at h; exact h.1

theorem allocH_eq {ev : Ev} {a : Core.Hint} (h : Ev.allocH? ev = some a) : ev = .atom (.hint a) := by
  cases ev with
  | atom aa =>
    cases aa with
    | hint hh =>
      simp only [Ev.allocH?] at h
      cases hc : coreFlow hh <;> simp only [hc, Bool.cond_true, Bool.cond_false, reduceCtorEq, Option.some.injEq] at h
      rw [h]
    | _ => simp [Ev.allocH?] at h
  | _ => simp [Ev.allocH?] at h

/-- **A buffer hint's atom**: the `k`-th buffer hint of a function the allocation check admits compiles
an allocation atom of the frame's path, of the `k`-th buffer's size. -/
theorem bufAtom {r : Ref} (hr : r.Ok) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (hT : RefTrack alignA r pc fp (done, e :: st)) {j : ℕ} (hj : B2C.idxOf e.I.t.name = some j) (hA : AllocJ j)
    {k : ℕ} {h : Hint} (hk : (((allocHints (adviceOf j)).filter fun q ↦ isBuf (ctxOf j) q.2).map (·.2))[k]? = some h) :
    ∃ a, compilesA (ctxOf j) (B2C.fsN j) a h = true ∧ Ev.atom (.hint a) ∈ e.pre ++ e.es ∧
      e.I.t.bufs[k]? = some (allocSizeOf e.σ a) := by
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j', bufs, kids, vs, hj', hIt, hfn, hw, -⟩ := (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain rfl : j = j' := Option.some.inj (hj.symm.trans hj')
  have hE := hT.track.ents e List.mem_cons_self
  have hA' := hA
  simp only [AllocJ, allocChk, allocRest, Bool.and_eq_true] at hA'
  obtain ⟨⟨hshape, -⟩, hpairs, -⟩ := hA'
  obtain ⟨a, ha, hca⟩ := pairsA_get hpairs k h hk
  have hw0 := hw
  rw [← hfn] at hw
  refine ⟨a, hca, ?_, ?_⟩
  · have hmem : a ∈ (e.pre ++ e.es).filterMap Ev.allocH? := by
      rw [allocShape_walk _ hshape _ (Or.inr ⟨vs, hw⟩)]; exact List.mem_of_getElem? ha
    obtain ⟨ev, hev, hev'⟩ := List.mem_filterMap.mp hmem
    rw [← allocH_eq hev']; exact hev
  · have hb1 := bufs_of_ok (insts_bufsOk r.T _ r.hdr hHon.bufsOk e.I hI) hIt
    have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw0
    have hbufs : e.I.t.bufs = bufs := congrArg Memory.Tree.bufs hIt
    rw [hevs, allocs_of_shape hshape hw] at hb1
    rw [hbufs, hb1, List.getElem?_map, ha]
    rfl

/-- What a buffer hint compiles, by kind. -/
theorem compilesA_cases {X : AlignCtx} {fs : ℕ} {a : Core.Hint} {h : Hint} (hc : compilesA X fs a h = true) :
    (∃ d n, a = .alloc d n ∧ h = .alloc (X.locAt d.idx) n) ∨
    (∃ d nv n, a = .allocDyn d nv ∧ h = .alloc (X.locAt d.idx) n ∧ allocCellOk X fs nv = true ∧
      X.pcAt (X.locAt nv.idx) = some n ∧ n < 2 ^ 28) ∨
    (∃ d nv, a = .allocDyn d nv ∧ h = .allocDyn (X.locAt d.idx) (X.locAt nv.idx) ∧ allocCellOk X fs nv = true) ∨
    (∃ d nv S, a = .allocDyn d nv ∧ h = .allocAdvice (X.locAt d.idx) S) := by
  cases a <;> cases h <;> simp only [compilesA, Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, Nat.blt_eq,
    Bool.false_eq_true] at hc
  · obtain ⟨⟨-, rfl⟩, rfl⟩ := hc
    exact Or.inl ⟨_, _, rfl, rfl⟩
  · obtain ⟨⟨⟨⟨-, hn⟩, rfl⟩, hpc⟩, hlt⟩ := hc
    exact Or.inr (Or.inl ⟨_, _, _, rfl, rfl, hn, hpc, hlt⟩)
  · obtain ⟨⟨⟨-, hn⟩, rfl⟩, rfl⟩ := hc
    exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, hn⟩))
  · obtain ⟨-, rfl⟩ := hc
    exact Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, rfl⟩))

/-- **A loop helper's path makes a call**, its last statements its conditional call and `ret []`. -/
theorem loop_calls_ne {fn : Fn} {p : B2C.Plumb} (h : loopChk fn p = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) : calls es ≠ [] := by
  unfold loopChk at h
  split at h
  case h_2 => cases h
  rename_i cc g args rpre hrev
  simp only [Bool.and_eq_true] at h
  obtain ⟨hnr, -⟩ := h
  have hbody : fn.body = rpre.reverse ++ [.callIf cc g args, .ret []] := by
    rw [← List.reverse_reverse fn.body, hrev]; simp
  rw [hbody, Bridge.walk_append] at hw
  rcases walk_noRet (σ := σ) _ (noRetB_spec _ hnr) with ⟨es1, he1⟩ | he1
  · rw [he1] at hw
    have hw2 : walk σ [Stmt.callIf cc g args, Stmt.ret []] =
        .ret [.inK cc, if σ cc = 0 then .skip g args else .call g args []] [] := by
      rw [walk_callIf_cons, walk_ret_cons]; rfl
    rw [hw2] at hw
    simp only [Out.seq, Out.pre] at hw
    obtain ⟨rfl, -⟩ := Out.ret.inj hw
    rw [Memory.calls_append']
    by_cases h0 : σ cc = 0 <;> simp [calls, h0, Ev.call?]
  · rw [he1] at hw; cases hw

/-! ## The allocation hints -/

/-- **Each allocation hint is ready where the tree puts the bump pointer**, on the deployed
alignment, given the facts named. -/
theorem allocReady_alignA (hD : DynPow) (hA : AdvNext alignA) (hL : LateReady alignA) (hF : FrameReady alignA)
    (hX : ExclReady alignA) : AllocReady alignA := by
  intro r hr C hC done e st s htr hch hnc hha hfine hon i h sx hget hpre hm halloc hin hnf
  have hat : HintAt alignA r C e s sx i h :=
    ⟨hr, hC, ⟨done, st, htr, hch, hha⟩, hnc, hfine, hon, hget, hpre, hm.fine.agree.get⟩
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hFH⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨off, hpcE, hhs⟩ := hint_off hC htr hget
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  rw [hoff] at hnf hnc
  have hget' : (hintsAtD (alignA e.I.t.name).d (alignA e.I.t.name).X.entry off)[i]? = some h := by
    rw [← hintsAtOff_eq, ← hhs]; exact hget
  have hfpe : e.I.fp = s.fp := htr.linked.top.1
  have hsxfp : sx.fp = e.I.fp := hm.fp.trans hfpe.symm
  have hU := hintsUp_frame hE.find
  have hCF := curFacts_frame hj
  obtain ⟨i0, rfl, hi0, -, hfind, hcore, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hA2 : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  by_cases hp : (allocPtr h).isSome = true
  · by_cases hfr : isFrame (alignA e.I.t.name).X h = true
    · exact (hF r C e s sx i h hat hfr).2 hin (by rw [hoff]; exact hnf)
    · by_cases hlt : isLate h = true
      · cases h <;> simp only [isLate, Bool.false_eq_true] at hlt
        rename_i p b
        obtain ⟨hwr, n, hb⟩ := hL r C e s sx i p b hat
        exact ⟨n, hb, Or.inl hwr⟩
      · have hb : isBuf (alignA e.I.t.name).X h = true := by
          unfold isBuf; simp only [hp, hfr, hlt, Bool.not_false, Bool.and_self]
        by_cases hex : i0 + 1 ∈ AllocChk.allocExcl
        · exact (hX r C e s sx i h (i0 + 1) hat hj hex hb).2 (by rw [hoff]; exact hnf)
        · have hAJ : AllocJ (i0 + 1) := AllocChk.allocJ_all _ h1 (by have : nFns = 1602 := rfl; omega) hex
          have hidx := bufsOf_idx hU hget' hb
          have hbo : bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d =
              (allocHints (adviceOf (i0 + 1))).filter fun q ↦ isBuf (ctxOf (i0 + 1)) q.2 := by rw [hA2]; rfl
          have hk : (((allocHints (adviceOf (i0 + 1))).filter fun q ↦ isBuf (ctxOf (i0 + 1)) q.2).map (·.2))[
              bufIdx alignA e off i]? = some h := by
            rw [List.getElem?_map, ← hbo]; unfold bufIdx; rw [hintsAtOff_eq, hidx]; rfl
          obtain ⟨p, hpp⟩ := Option.isSome_iff_exists.mp hp
          obtain ⟨hklt, hfpp, hptr⟩ := bufBase_ref hr htr hj hAJ hk hpp
          have hnc0 : e.nc = 0 := hnc ⟨(off, h), List.mem_of_getElem? hidx, le_refl _⟩
          obtain ⟨hfq, hcf⟩ := buf_noFrame hU hCF.first hget' hb
          have hpend : pendAt (alignA e.I.t.name).X (alignA e.I.t.name).code (alignA e.I.t.name).d off = false := by
            unfold pendAt pendIn
            rw [List.any_eq_false]
            intro q hq
            have := hfq q hq
            simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
            omega
          have hnfx : sx.nextFree = e.I.cur + (e.I.t.bufs.take (bufIdx alignA e off i)).sum := by
            rw [hnf, cursorAt_unfold, hnc0, hpend, ← treeSizes_take_buf alignA e off i hcf]
            simp only [List.take_zero, List.map_nil, List.sum_nil, Bool.cond_false, Nat.zero_mul, Nat.add_zero]
            omega
          obtain ⟨a, hca, hev, hbk⟩ := bufAtom hr htr hj hAJ hk
          set k := bufIdx alignA e off i with hkdef
          -- the buffer ends within the tree
          have hn : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
          have he1 := curAt_le_endCur (fs := B2C.fs) (lp := coreProgram.loop) hn e.I.t.bufs.length 0
          simp only [Inst.curAt, List.take_length, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero] at he1
          have he2 := endCur_chain (A := alignA) hr st e s.pc s.fp htr.track.ents htr.linked hch
          have he3 := le_two_pow_logMem (r.T.total B2C.fs)
          have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
          have hIP := insts_placed r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega) e.I hI
          have hcur2 : 2 ≤ e.I.cur := by
            have h2 := hHon.cells.two_le e.I hI
            have hb2 : B2C.fs e.I.t.name ≤ e.I.t.block B2C.fs coreProgram.loop := by
              rw [hIt]; simp only [Tree.block, Tree.name]; omega
            have := hIP.2.2
            omega
          obtain ⟨n, hbn⟩ : ∃ n, e.I.t.bufs[k]? = some n := ⟨_, hbk⟩
          have htk : (e.I.t.bufs.take (k + 1)).sum = (e.I.t.bufs.take k).sum + n := by
            rw [List.take_add_one, List.sum_append, hbn]; simp
          have hle : (e.I.t.bufs.take (k + 1)).sum ≤ e.I.t.bufs.sum :=
            List.Sublist.sum_le_sum (List.take_sublist _ _) (fun _ _ ↦ Nat.zero_le _)
          have hbound : sx.nextFree + n ≤ maxCells := by
            rw [hnfx]; unfold maxCells; unfold Ref.κ at he3 h2k; omega
          have hnlt : n < maxCells := by
            rw [hnfx] at hbound; omega
          rw [hbk] at hbn
          obtain rfl := Option.some.inj hbn
          rcases compilesA_cases hca with ⟨d, n', rfl, rfl⟩ | ⟨d, nv, n', rfl, rfl, hcn, hpc, hlt'⟩ |
            ⟨d, nv, rfl, rfl, hcn⟩ | ⟨d, nv, S, rfl, rfl⟩
          · simp only [allocPtr, Option.some.injEq] at hpp
            subst hpp
            exact ⟨by rw [hsxfp]; exact hfpp, hbound, by rw [hsxfp, hptr, hnfx]⟩
          · simp only [allocPtr, Option.some.injEq] at hpp
            subst hpp
            have hval := cellRef hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hcn
            have hJ := (jumpCells_at r hr _ _ _ _ _ htr).pcw ((ctxOf (i0 + 1)).locAt nv.idx) n' (by rw [hA2]; exact hpc)
            have hw' := (refRd_img hκ r.img _ _ (by unfold maxCells at hval; omega) hJ).2
            rw [hval.2] at hw'
            have hsz : allocSizeOf e.σ (.allocDyn d nv) = n' := by
              simp only [allocSizeOf]; rw [hw', logG_spec (by omega)]
            rw [hsz] at hbound
            exact ⟨by rw [hsxfp]; exact hfpp, hbound, by rw [hsxfp, hptr, hnfx]⟩
          · simp only [allocPtr, Option.some.injEq] at hpp
            subst hpp
            have hval := cellRef hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hcn
            have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
            have hpow := hD r hr e.I hI _ _ _ _ hIt d nv (by rw [hevs]; exact hev)
            refine ⟨allocSizeOf e.σ (.allocDyn d nv), ⟨?_, hnlt⟩, ⟨by rw [hsxfp]; exact hfpp, hbound,
              by rw [hsxfp, hptr, hnfx]⟩⟩
            obtain ⟨v, hv⟩ := Mem.get_of_written (show sx.mem.written (sx.fp + (ctxOf (i0 + 1)).locAt nv.idx) = true from hin)
            have hMv := hm.fine.agree.get _ _ hv
            unfold Mem.peek
            rw [hv, Option.getD_some, ← hMv, hsxfp, hval.2]
            exact hpow
          · simp only [allocPtr, Option.some.injEq] at hpp
            subst hpp
            have hnx := hA r C e s sx i _ S hat
            rw [hoff, ← hkdef, hbk] at hnx
            exact Or.inr ⟨_, hnx, hnlt, by rw [hsxfp]; exact hfpp, hbound, by rw [hsxfp, hptr, hnfx]⟩
  · cases h <;> simp only [isAllocHint, allocPtr, Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      not_false_eq_true, not_true_eq_false] at halloc hp
    all_goals
      have hpos : ((alignA e.I.t.name).d.2.2.lookup ((alignA e.I.t.name).X.entry + off)).isSome = true := by
        unfold hintsAtD at hget'
        cases hlk : (alignA e.I.t.name).d.2.2.lookup ((alignA e.I.t.name).X.entry + off) with
        | none => rw [hlk] at hget'; simp at hget'
        | some _ => rfl
      obtain ⟨hs', hlk⟩ := Option.isSome_iff_exists.mp hpos
      have hmem := mem_of_lookupN hlk
      have hget'' := hget'
      unfold hintsAtD at hget''
      rw [hlk, Option.getD_some] at hget''
      have haddr := hCF.addr _ hmem _ (List.mem_of_getElem? hget'')
      have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ r.T.total B2C.fs :=
        honest_within hI (by have := hHon.cells.two_le e.I hI; omega)
      have h28 : r.T.total B2C.fs ≤ 2 ^ r.κ := le_two_pow_logMem _
      have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
      rw [hfs] at hwithin
    · -- a next frame's address: in a loop helper, its tail callee's frame right after its own
      rename_i o
      simp only [addrOk, Bool.and_eq_true, Nat.beq_eq] at haddr
      obtain ⟨rfl, hloop⟩ := haddr
      show sx.fp + B2C.fsN (i0 + 1) < maxCells
      have hd := JumpCells.jcData_all _ h1 (by have : nFns = 1602 := rfl; omega)
      unfold jcData jcDataD at hd
      simp only [Bool.and_eq_true] at hd
      obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hlc⟩, -⟩ := hd
      simp only [hloop, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hlc
      have hw' : walk e.σ (coreOf (i0 + 1)).body = .ret (e.pre ++ e.es) vs := by rw [hfn]; exact hw
      have hne := loop_calls_ne hlc.2 hw'
      have hkl : (calls (e.pre ++ e.es)).length = e.I.t.kids.length := by
        obtain ⟨rv, hkv⟩ := hE.kids; exact kidsValid_len hkv
      have hk : e.I.t.kids ≠ [] := fun h0 ↦ hne (List.eq_nil_of_length_eq_zero (by rw [hkl, h0]; rfl))
      have hlp : coreProgram.loop e.I.t.name = true := by
        rw [Program.loop_of_find? hfind, ← hcore]; exact hloop
      have hpos := tail_pos (fs := B2C.fs) hlp hk
      have hlast : e.I.t.kids[e.I.t.kids.length - 1]? = some (e.I.t.kids.getLast hk) := by
        rw [← List.getLast?_eq_getElem?, List.getLast?_eq_some_getLast hk]
      obtain ⟨J, hJ, hJt, hJfp⟩ := honest_closed e.I hI _ _ hlast
      have hIP := insts_placed r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr (by omega) e.I hI
      rw [hIP.1, List.getElem?_map, hpos] at hJfp
      have hJfp' : J.fp = e.I.fp + B2C.fs e.I.t.name := (Option.some.inj hJfp).symm
      have hJw : J.fp + B2C.fs J.t.name ≤ r.T.total B2C.fs :=
        honest_within hJ (by have := hHon.cells.two_le J hJ; omega)
      have := hHon.cells.two_le J hJ
      rw [hsxfp]; unfold maxCells; rw [hfs] at hJfp'; omega
    · -- a cell's address: a fixed cell of the frame holding it
      rename_i q o
      simp only [addrOk, Bool.and_eq_true, Nat.blt_eq] at haddr
      obtain ⟨hst, hofs⟩ := haddr
      split at hst
      · rename_i o' hso
        simp only [Nat.beq_eq] at hst
        subst hst
        have hd := JumpCells.jcData_all _ h1 (by have : nFns = 1602 := rfl; omega)
        unfold jcData jcDataD at hd
        simp only [Bool.and_eq_true] at hd
        obtain ⟨⟨⟨⟨⟨⟨⟨hstat, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hd
        rw [hA2] at hso
        have hsm := statOf_ofData hso
        have hb := List.all_eq_true.mp hstat _ hsm
        simp only [cellIn, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hb
        have hrd := hFH.stat _ hsm hb.1.1 hb.1.2
        obtain ⟨hq, hv⟩ := refRd_img hκ r.img _ _ (by omega) hrd
        refine ⟨by rw [hsxfp]; unfold maxCells; omega, by rw [hsxfp]; exact hq, ?_⟩
        rw [hsxfp, hv]
        rfl
      · cases hst

/-! ## The words each hint reserves -/

theorem treeSizes_getD (A : String → FnAl) (e : Ent) {off i : ℕ} {h : Hint}
    (hi : (hintsAtOff (A e.I.t.name) off)[i]? = some h) :
    (treeSizes A e off).getD i 0 = if isBuf (A e.I.t.name).X h then e.I.t.bufs.getD (bufIdx A e off i) 0
      else if isFrame (A e.I.t.name).X h then
        (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0
      else 0 := by
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  rw [List.getD_eq_getElem?_getD, treeSizes, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some, hi, bufIdx, List.countP_eq_length_filter]

/-- **Each hint reserves its `treeSizes` entry**, on the deployed alignment, given the facts named. -/
theorem sizesAt_alignA (hA : AdvNext alignA) (hL : LateReady alignA) (hF : FrameReady alignA) (hX : ExclReady alignA) :
    SizesAt alignA := by
  intro r hr C hC done e st s htr hch hnc hha hfine hon i h sx hget hpre hag
  have hat : HintAt alignA r C e s sx i h := ⟨hr, hC, ⟨done, st, htr, hch, hha⟩, hnc, hfine, hon, hget, hpre, hag⟩
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hFH⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨off, hpcE, hhs⟩ := hint_off hC htr hget
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  rw [hoff]
  have hgetO : (hintsAtOff (alignA e.I.t.name) off)[i]? = some h := by rw [← hhs]; exact hget
  have hget' : (hintsAtD (alignA e.I.t.name).d (alignA e.I.t.name).X.entry off)[i]? = some h := hgetO
  rw [treeSizes_getD alignA e hgetO]
  have hfpe : e.I.fp = s.fp := htr.linked.top.1
  have hfol := hints_follows _ s sx ⟨hfine.agree.wf, hfine.dl⟩ hpre
  have hsxfp : sx.fp = e.I.fp := hfol.fp.trans hfpe.symm
  have hU := hintsUp_frame hE.find
  have hCF := curFacts_frame hj
  obtain ⟨i0, rfl, hi0, -, hfind, hcore, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hA2 : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  by_cases hfr : isFrame (alignA e.I.t.name).X h = true
  · simp only [isFrame_notBuf hfr, hfr, Bool.false_eq_true, ↓reduceIte]
    exact (hF r C e s sx i h hat hfr).1
  by_cases hp : (allocPtr h).isSome = true
  · by_cases hlt : isLate h = true
    · have hnb : isBuf (alignA e.I.t.name).X h = false := by unfold isBuf; simp [hlt]
      simp only [hnb, hfr, Bool.false_eq_true, ↓reduceIte]
      cases h <;> simp only [isLate, Bool.false_eq_true] at hlt
      rename_i p b
      obtain ⟨hwr, -⟩ := hL r C e s sx i p b hat
      cases b <;> simp [rsz, hwr]
    · have hb : isBuf (alignA e.I.t.name).X h = true := by
        unfold isBuf; simp only [hp, hfr, hlt, Bool.not_false, Bool.and_self]
      simp only [hb, ↓reduceIte]
      have hidx := bufsOf_idx hU hget' hb
      have hadv : ∀ p S, h = .allocAdvice p S →
          rsz C (refMem r.img) sx h = e.I.t.bufs.getD (bufIdx alignA e off i) 0 := by
        rintro p S rfl
        have hnx := hA r C e s sx i p S hat
        rw [hoff] at hnx
        simp only [rsz, advSize]
        rw [List.getD_eq_getElem?_getD]
        obtain ⟨es, h1', h2'⟩ := hnx
        rw [h1', Option.bind_some, h2']
        rcases hbk : e.I.t.bufs[bufIdx alignA e off i]? with _ | n
        · rfl
        · have hn : n ≤ r.T.total B2C.fs := by
            have hle : n ≤ e.I.t.bufs.sum := List.le_sum_of_mem (List.mem_of_getElem? hbk)
            have hn : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
            have he1 := curAt_le_endCur (fs := B2C.fs) (lp := coreProgram.loop) hn e.I.t.bufs.length 0
            simp only [Inst.curAt, List.take_length, List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero] at he1
            have he2 := endCur_chain (A := alignA) hr st e s.pc s.fp htr.track.ents htr.linked hch
            omega
          have := hHon.size
          simp only [Option.getD_some]
          exact logG_spec (by omega)
      by_cases hex : i0 + 1 ∈ AllocChk.allocExcl
      · have := (hX r C e s sx i h (i0 + 1) hat hj hex hb).1
        rw [hoff] at this
        exact this
      · have hAJ : AllocJ (i0 + 1) := AllocChk.allocJ_all _ h1 (by have : nFns = 1602 := rfl; omega) hex
        have hbo : bufsOf (alignA e.I.t.name).X (alignA e.I.t.name).d =
            (allocHints (adviceOf (i0 + 1))).filter fun q ↦ isBuf (ctxOf (i0 + 1)) q.2 := by rw [hA2]; rfl
        have hk : (((allocHints (adviceOf (i0 + 1))).filter fun q ↦ isBuf (ctxOf (i0 + 1)) q.2).map (·.2))[
            bufIdx alignA e off i]? = some h := by
          rw [List.getElem?_map, ← hbo]; unfold bufIdx; rw [hintsAtOff_eq, hidx]; rfl
        obtain ⟨a, hca, hev, hbk⟩ := bufAtom hr htr hj hAJ hk
        rw [List.getD_eq_getElem?_getD, hbk, Option.getD_some]
        rcases compilesA_cases hca with ⟨d, n', rfl, rfl⟩ | ⟨d, nv, n', rfl, rfl, hcn, hpc, hlt'⟩ |
          ⟨d, nv, rfl, rfl, hcn⟩ | ⟨d, nv, S, rfl, rfl⟩
        · rfl
        · have hval := cellRef hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hcn
          have hJ := (jumpCells_at r hr _ _ _ _ _ htr).pcw ((ctxOf (i0 + 1)).locAt nv.idx) n' (by rw [hA2]; exact hpc)
          have hw' := (refRd_img hκ r.img _ _ (by unfold maxCells at hval; omega) hJ).2
          rw [hval.2] at hw'
          simp only [rsz, allocSizeOf]
          rw [hw', logG_spec (by omega)]
        · have hval := cellRef hr htr hj ⟨_, hev, by simp [atomUses, hintUses]⟩ hcn
          simp only [rsz, allocSizeOf]
          rw [hsxfp, hval.2]
        · have := hadv _ S rfl
          rw [List.getD_eq_getElem?_getD, hbk, Option.getD_some] at this
          exact this
  · have hnb : isBuf (alignA e.I.t.name).X h = false := by unfold isBuf; simp [hp]
    simp only [hnb, hfr, Bool.false_eq_true, ↓reduceIte]
    cases h <;> first | rfl | (simp only [allocPtr, Option.isSome_some, not_true_eq_false] at hp)

/-! ## The callee frames -/

/-- **A frame hint's size read off `M` is its reserved words.** -/
theorem rsz_of_sizeOk {C : Ctx} {M : ℕ → E} {s : St} {h : Hint} {B : ℕ} (hS : SizeOk M s.fp h B) :
    rsz C M s h = B := by
  cases h <;> simp only [SizeOk] at hS
  · rename_i p size stop si tail
    obtain ⟨v, n, hp, hvn, hn, hB⟩ := hS
    simp only [rsz]
    rw [hp, limb_ofK]
    simp only [Fin.isValue, Fin.val_zero, ↓reduceIte]
    rw [hvn, logG_spec (by unfold maxCells at hn; omega), hB]
  · exact hS
  · rename_i p sel sizes
    obtain ⟨k, hp, hk, hsz⟩ := hS
    simp only [rsz]
    rw [hp, logG_spec (by unfold maxCells at hk; omega), List.getD_eq_getElem?_getD, hsz, Option.getD_some]

/-- A written cell's word is `M`'s, where `M` agrees with the state. -/
theorem peek_of_written {M : ℕ → E} {s : St} (hag : ∀ c v, s.mem.get c = some v → M c = v) {c : ℕ}
    (hw : s.mem.written c = true) : s.mem.peek c = M c := by
  obtain ⟨v, hv⟩ := Mem.get_of_written hw
  unfold Mem.peek
  rw [hv, Option.getD_some, hag c v hv]

/-- **The callee frames' hints**, from their sizes and pointers. -/
theorem frameReady_of (hS : FrameSize alignA) (hP : FramePtr alignA) : FrameReady alignA := by
  intro r C e s sx i h hat hfr
  obtain ⟨hr, hC, ⟨done, st, htr, hch, hha⟩, hnc, hfine, hon, hget, hpre, hag⟩ := hat
  have hat : HintAt alignA r C e s sx i h := ⟨hr, hC, ⟨done, st, htr, hch, hha⟩, hnc, hfine, hon, hget, hpre, hag⟩
  have hSz := hS r C e s sx i h hat hfr
  refine ⟨rsz_of_sizeOk hSz, fun hin hnf ↦ ?_⟩
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, hfn, hw, hFH⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨off, hpcE, hhs⟩ := hint_off hC htr hget
  have hoff : s.pc - entOf alignA e.I.t.name = off := by omega
  rw [hoff] at hnf
  have hgetO : (hintsAtOff (alignA e.I.t.name) off)[i]? = some h := by rw [← hhs]; exact hget
  have hget' : (hintsAtD (alignA e.I.t.name).d (alignA e.I.t.name).X.entry off)[i]? = some h := hgetO
  have hfpe : e.I.fp = s.fp := htr.linked.top.1
  have hfol := hints_follows _ s sx ⟨hfine.agree.wf, hfine.dl⟩ hpre
  have hsxfp : sx.fp = e.I.fp := hfol.fp.trans hfpe.symm
  have hU := hintsUp_frame hE.find
  have hCF := curFacts_frame hj
  set X := (alignA e.I.t.name).X
  set d := (alignA e.I.t.name).d
  set code := (alignA e.I.t.name).code
  -- the hint among the frame hints
  have hpos : (d.2.2.lookup (X.entry + off)).isSome = true := by
    unfold hintsAtD at hget'
    cases hlk : d.2.2.lookup (X.entry + off) with
    | none => rw [hlk] at hget'; simp at hget'
    | some _ => rfl
  obtain ⟨hs', hlk⟩ := Option.isSome_iff_exists.mp hpos
  have hget'' := hget'
  unfold hintsAtD at hget''
  rw [hlk, Option.getD_some] at hget''
  have hqm : (off, h) ∈ frames X d := by
    unfold frames allocHints hintsOff
    refine List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨_, mem_of_lookupN hlk,
      List.mem_map.mpr ⟨h, List.mem_of_getElem? hget'', ?_⟩⟩, isFrame_ptr hfr⟩, hfr⟩
    rw [hU.1]; simp
  obtain ⟨ins, hins⟩ := frJump_of hCF (off, h) hqm
  -- nothing pending, no frame hint before it at its offset
  set J := nextJump code off
  have hle1 : (frames X d).countP (fun q ↦ Nat.beq (nextJump code q.1) J) ≤ 1 :=
    countP_uniq hCF.uniq hins (nextJump_jump hins) fun q _ hq ↦ by simpa using hq
  have hdis : ∀ q : ℕ × Hint, ¬((decide (q.1 < off) && decide (off ≤ nextJump code q.1)) = true ∧
      decide (q.1 = off) = true) := fun q ⟨h1, h2⟩ ↦ by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 h2; omega
  have hsub : (frames X d).countP (fun q ↦ (decide (q.1 < off) && decide (off ≤ nextJump code q.1)) ||
      decide (q.1 = off)) ≤ (frames X d).countP (fun q ↦ Nat.beq (nextJump code q.1) J) := by
    refine List.countP_mono_left fun q hq hpq ↦ ?_
    obtain ⟨insq, hinsq⟩ := frJump_of hCF q hq
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hpq
    rcases hpq with ⟨h1, h2⟩ | h1
    · have := nextJump_eq hinsq h1.le h2
      simp [J, ← this]
    · simp [J, h1]
  rw [countP_or hdis] at hsub
  have hat_off : (frames X d).countP (fun q ↦ decide (q.1 = off)) =
      (hintsAtD d X.entry off).countP (isFrame X) :=
    countP_at hU (fun _ ↦ isFrame_ptr (X := X)) off
  have hsplit : (hintsAtD d X.entry off).countP (isFrame X) =
      ((hintsAtD d X.entry off).take i).countP (isFrame X) + 1 +
        ((hintsAtD d X.entry off).drop (i + 1)).countP (isFrame X) := by
    have hlt := (List.getElem?_eq_some_iff.mp hget').1
    conv_lhs => rw [← List.take_append_drop i (hintsAtD d X.entry off),
      List.drop_eq_getElem_cons hlt]
    rw [(List.getElem?_eq_some_iff.mp hget').2]
    simp only [List.countP_append, List.countP_cons, hfr, ↓reduceIte]
    omega
  have hpend0 : (frames X d).countP (fun q ↦ decide (q.1 < off) && decide (off ≤ nextJump code q.1)) = 0 := by omega
  have hcf : ((hintsAtD d X.entry off).take i).countP (isFrame X) = 0 := by omega
  have hpend : pendAt X code d off = false := by
    unfold pendAt
    rw [pendIn_eq, hpend0]
    rfl
  -- the bump pointer: past every buffer and the callees so far
  have hbl := bufs_le hr htr List.mem_cons_self
  have hall := frame_allBufs hU hCF.first hget' hfr
  have hnfx : sx.nextFree = e.I.curAt B2C.fs coreProgram.loop e.I.t.bufs.length e.nc := by
    have h' := treeSizes_take_buf alignA e off i hcf
    have hk : bufIdx alignA e off i = (bufsOf X d).length := hall
    rw [hk, take_sum_le hbl] at h'
    rw [hnf, cursorAt_unfold, hpend]
    simp only [Inst.curAt, List.take_length, Bool.cond_false, Nat.zero_mul, Nat.add_zero]
    omega
  set B := (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0
  have hn : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids := ⟨_, _, _, _, hIt⟩
  have hend : e.I.curAt B2C.fs coreProgram.loop e.I.t.bufs.length e.nc + B ≤ e.I.endCur B2C.fs coreProgram.loop := by
    rcases hk : (e.I.t.kidsC coreProgram.loop)[e.nc]? with _ | k
    · simp only [B, hk, Option.map_none, Option.getD_none, Nat.add_zero]
      exact curAt_le_endCur hn _ _
    · have hlt := (List.getElem?_eq_some_iff.mp hk).1
      have hk' : (e.I.t.kidsC coreProgram.loop)[e.nc] = k := (List.getElem?_eq_some_iff.mp hk).2
      have := curAt_block_le (fs := B2C.fs) (nb := e.I.t.bufs.length) hn hlt
      simp only [B, hk, Option.map_some, Option.getD_some]
      rw [hk'] at this
      exact this
  have he2 := endCur_chain (A := alignA) hr st e s.pc s.fp htr.track.ents htr.linked hch
  have he3 := le_two_pow_logMem (r.T.total B2C.fs)
  have h2k : 2 ^ r.κ ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hκ
  have hbound : sx.nextFree + B ≤ maxCells := by
    rw [hnfx]; unfold maxCells; unfold Ref.κ at he3 h2k; omega
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (isFrame_ptr hfr)
  obtain ⟨hpl, hpv⟩ := hP r C e s sx i h p hat hfr hp
  have hA : AllocOk (refMem r.img) sx p B :=
    ⟨by rw [hsxfp]; exact hpl, hbound, by rw [hsxfp, hpv, hnfx]⟩
  cases h <;> simp only [SizeOk] at hSz <;> simp only [allocPtr, Option.some.injEq] at hp
  · subst hp
    obtain ⟨v, n, h1, h2, h3, h4⟩ := hSz
    exact ⟨v, n, by rw [peek_of_written hag hin, h1], h2, h3, h4 ▸ hA⟩
  · subst hp hSz; exact hA
  · subst hp
    obtain ⟨k, hk, hk', hsz⟩ := hSz
    exact ⟨k, B, ⟨by rw [peek_of_written hag hin, hk], hk'⟩, hsz, hA⟩

/-! ## Together -/

/-- **What the allocation track rests on and does not prove**, on the deployed alignment. -/
structure AllocGaps : Prop where
  dynPow : DynPow
  advNext : AdvNext alignA
  late : LateReady alignA
  frameSize : FrameSize alignA
  framePtr : FramePtr alignA
  excl : ExclReady alignA

theorem AllocGaps.allocReady (G : AllocGaps) : AllocReady alignA :=
  allocReady_alignA G.dynPow G.advNext G.late (frameReady_of G.frameSize G.framePtr) G.excl

theorem AllocGaps.sizesAt (G : AllocGaps) : SizesAt alignA :=
  sizesAt_alignA G.advNext G.late (frameReady_of G.frameSize G.framePtr) G.excl

end

end LeanVM.Guest.EndExec
