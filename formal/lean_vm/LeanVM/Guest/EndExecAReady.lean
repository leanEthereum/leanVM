/-
  LeanVM.Guest.EndExecAReady

  Each allocation hint has what it needs where the tree puts the bump pointer, and takes the step
  the tree reserves there: `SizesAt` and `AllocReady` from the facts by hint kind.
-/

module

public import LeanVM.Guest.EndExecACurArith

/-!
# The allocation hints ready, aligned

The bus era's `EndExecAReady.lean` on Hotwire's aligned allocator, its glue: at the `i`-th hint of a
frame's offset (`HintAtA`), the hints before it, in their order (`ordHints`), have bumped the cursor
to the frame's cursor past its buffers before the hint (`bufIdxA`) and its calls made, nothing
pending (`cursor_take`, `ordHints_at`). So `SizesAt` and `AllocReady` follow from three facts by hint
kind, the bus era's:

* `BufReady L D A`: a buffer hint takes its buffer's cells, unaligned, and, at the cursor past the
  buffers before it, has what it needs (`HintOk`: its pointer cell the buffer's base, the reservation
  below `maxCells`) and its reservation within `2^κ` (the bus era's `bufBase_ref`, `Tree.BufsOk`,
  `allocs_of_shape`, `DynPow`, `endCur_chain`);
* `FrameReadyA L D A`: a callee frame's hint takes the next callee's block, aligned as `L.al`
  allocates that callee, and has what it needs there (the bus era's `FrameSize`, `FramePtr`, `kid_pos`);
* `AddrReady L D A`: an address hint has what it needs (`addrOk`, the cell below the frame size).

A hint neither a buffer's nor a frame's is no allocation (`allocPtr` none) and takes no step.
`allocTrack_ofReady`: `AllocTrack R (YAlloc L D A)` from the bridge's premises, `MainA L`, `CurHyps`
and the three facts.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Guest.Mode (HintIn)
open LeanVM.Prover.Exec

@[expose] public section

/-- **The `i`-th hint `h` at a state `s` of the tree track** on a reference of the honest tree, top
frame `e`, its frames chained, no call before its buffers, run from the state `sx` the hints before
it reach, in `s`'s frame, whose written cells hold the reference's words. -/
structure HintAtA (L : Lay) (D : Ref → RefD) (A : String → FnAl) (r : Ref) (C : Ctx) (e : Ent) (s sx : St)
    (i : ℕ) (h : Hint) : Prop where
  ref : RefH L (D r) r
  ok : r.Ok
  ctx : Ctx.of guestProgram r.adv = .ok C
  track : ∃ done st, RefTrack L D A r s.pc s.fp (done, e :: st) ∧ ChainA L A (memOf r.img) (e :: st)
  nc : NcTop A e (s.pc - entOf A e.I.t.name)
  fine : Fine (refMem r.img) s
  onref : OnRef guestProgram r.img r.n s
  get : ((C.hints[s.pc]?).getD [])[i]? = some h
  pre : (((C.hints[s.pc]?).getD []).take i).foldlM (runHint C) s = .ok sx
  fp : sx.fp = s.fp
  agree : ∀ c v, sx.mem.get c = some v → refMem r.img c = v

/-- The buffer index of the `i`-th hint at offset `off` of frame `e`: the buffer hints before it. -/
noncomputable def bufIdxA (A : String → FnAl) (e : Ent) (off i : ℕ) : ℕ :=
  nbAt (A e.I.t.name).X (A e.I.t.name).d off + ((hintsAtOff (A e.I.t.name) off).take i).countP (isBuf (A e.I.t.name).X)

/-- The step a callee frame's hint of frame `e` takes on the honest tree: the next callee's block,
aligned as the layout allocates it. -/
noncomputable def frameStep (L : Lay) (e : Ent) : Bool × ℕ :=
  (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map fun k ↦ (L.al k.name, k.block L.fs coreProgram.loop)).getD (false, 0)

/-- **A buffer hint takes its buffer's cells and is ready at the cursor past the buffers before
it.** -/
def BufReady (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h, HintAtA L D A r C e s sx i h → isBuf (A e.I.t.name).X h = true →
    rszA (refMem r.img) sx h = (false, e.I.t.bufs.getD (bufIdxA A e (s.pc - entOf A e.I.t.name) i) 0) ∧
    (HintIn sx h → sx.nextFree = e.I.curA L.fs coreProgram.loop L.al (bufIdxA A e (s.pc - entOf A e.I.t.name) i) e.nc →
      HintOk C (refMem r.img) sx h ∧ AllocB (2 ^ r.κ) sx h)

/-- **A callee frame's hint takes the next callee's block, aligned as the layout allocates it, and
is ready at the cursor past the buffers before it and the calls made.** -/
def FrameReadyA (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h, HintAtA L D A r C e s sx i h → isFrame (A e.I.t.name).X h = true →
    rszA (refMem r.img) sx h = frameStep L e ∧
    (HintIn sx h → sx.nextFree = e.I.curA L.fs coreProgram.loop L.al (bufIdxA A e (s.pc - entOf A e.I.t.name) i) e.nc →
      HintOk C (refMem r.img) sx h ∧ AllocB (2 ^ r.κ) sx h)

/-- **An address hint has what it needs.** -/
def AddrReady (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h, HintAtA L D A r C e s sx i h → (∃ o, h = .frameAddress o) ∨ (∃ p c, h = .cellAddress p c) →
    HintIn sx h → HintOk C (refMem r.img) sx h

end

public section

/-! ## Steps in order -/

theorem stepsOf_take (isB isF : Hint → Bool) (buf : ℕ → ℕ) (fr : Bool × ℕ) :
    ∀ (hs : List Hint) (n i : ℕ), (stepsOf isB isF buf fr hs n).take i = stepsOf isB isF buf fr (hs.take i) n
  | [], _, i => by simp [stepsOf]
  | _ :: _, _, 0 => by simp [stepsOf]
  | h :: hs, n, i + 1 => by rw [stepsOf, List.take_succ_cons, List.take_succ_cons, stepsOf, stepsOf_take _ _ _ _ hs]

theorem stepsOf_getD (isB isF : Hint → Bool) (buf : ℕ → ℕ) (fr : Bool × ℕ) :
    ∀ (hs : List Hint) (n i : ℕ) (h : Hint), hs[i]? = some h →
      (stepsOf isB isF buf fr hs n).getD i (false, 0) =
        (bif isB h then (false, buf (n + (hs.take i).countP isB)) else bif isF h then fr else (false, 0))
  | [], _, _, _, hi => by simp at hi
  | h0 :: hs, n, 0, h, hi => by
      obtain rfl : h0 = h := by simpa using hi
      simp [stepsOf]
  | h0 :: hs, n, i + 1, h, hi => by
      rw [stepsOf, List.getD_cons_succ, stepsOf_getD _ _ _ _ hs _ i h (by simpa using hi), List.take_succ_cons,
        List.countP_cons]
      have : (bif isB h0 then n + 1 else n) + (hs.take i).countP isB =
          n + ((hs.take i).countP isB + if isB h0 = true then 1 else 0) := by
        cases isB h0 <;> simp
        omega
      rw [this]

theorem ordHints_take {isB isF : Hint → Bool} :
    ∀ (p : Bool) (hs : List Hint) (i : ℕ), ordHints isB isF p hs = true → ordHints isB isF p (hs.take i) = true
  | _, [], _, _ => by simp [ordHints]
  | _, _ :: _, 0, _ => by simp [ordHints]
  | p, h :: hs, i + 1, ho => by
      simp only [ordHints, Bool.and_eq_true] at ho
      rw [List.take_succ_cons, ordHints, Bool.and_eq_true]
      exact ⟨ho.1, ordHints_take _ hs i ho.2⟩

/-- **At a buffer or frame hint nothing is pending**: neither a frame before the offset nor one
before it at the offset. -/
theorem ordHints_at {isB isF : Hint → Bool} :
    ∀ (p : Bool) (hs : List Hint) (i : ℕ) (h : Hint), ordHints isB isF p hs = true → hs[i]? = some h →
      (isB h = true ∨ isF h = true) → (p || (hs.take i).any isF) = false
  | _, [], _, _, _, hi, _ => by simp at hi
  | p, h0 :: hs, 0, h, ho, hi, hk => by
      obtain rfl : h0 = h := by simpa using hi
      simp only [ordHints, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ho
      rcases ho.1 with h1 | ⟨h1, h2⟩
      · simp [h1]
      · rcases hk with hk | hk <;> simp_all
  | p, h0 :: hs, i + 1, h, ho, hi, hk => by
      simp only [ordHints, Bool.and_eq_true] at ho
      have := ordHints_at _ hs i h ho.2 (by simpa using hi) hk
      simp only [Bool.or_eq_false_iff] at this
      rw [List.take_succ_cons, List.any_cons]
      simp only [Bool.or_eq_false_iff] at this ⊢
      exact ⟨this.1.1, this.1.2, this.2⟩

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **The hints at a frame's pc are its function's at the offset.** -/
theorem hints_off (hP : ProgAl guestProgram coreProgram A) (hAd : AdvAl A) {r : Ref} {C : Ctx}
    (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack L D A r s.pc s.fp (done, e :: st)) (hne : (C.hints[s.pc]?).getD [] ≠ []) :
    (C.hints[s.pc]?).getD [] = hintsAtOff (A e.I.t.name) (s.pc - entOf A e.I.t.name) := by
  have hpc2 := pc_lt_of_hints hC hne
  have hsize := (ctx_of_spec hC).1
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨-, hat⟩ := htr.linked.top
  obtain ⟨off, hpc, p, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal'
  have hpcE : s.pc = (A e.I.t.name).X.entry + off := hpc
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr hpc2
  have hoff : s.pc - entOf A e.I.t.name = off := by
    show s.pc - (A e.I.t.name).X.entry = off
    omega
  rw [hoff, hh, hintsAtOff, hAd _ _ hE.find off ins hins, ← hpcE]

/-- **A buffer at the offset means no call made.** -/
theorem bufStep {e : Ent} {off : ℕ} (hU : HintsUp (A e.I.t.name).d (A e.I.t.name).X.entry) (hnc : NcTop A e off)
    (hc : 0 < (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X)) :
    ∀ n, bump (curForm L e n false) (false, e.I.t.bufs.getD n 0) = curForm L e (n + 1) false := by
  intro n
  have hq : 0 < (bufsOf (A e.I.t.name).X (A e.I.t.name).d).countP (fun q ↦ decide (q.1 = off)) := by
    rw [show bufsOf (A e.I.t.name).X (A e.I.t.name).d =
      (allocHints (A e.I.t.name).d).filter fun q ↦ isBuf (A e.I.t.name).X q.2 from rfl,
      countP_at hU (fun _ ↦ isBuf_ptr) off]
    exact hc
  obtain ⟨q, hqm, hq1⟩ := List.countP_pos_iff.mp hq
  have h0 : e.nc = 0 := hnc ⟨q, hqm, by simp only [decide_eq_true_eq] at hq1; omega⟩
  rw [curForm_false, curForm_false, Inst.curA, Inst.curA, h0, List.take_zero, curF_nil, curF_nil, bump,
    allocBase_false, take_succ_sum]
  simp only
  omega

/-- **The hints before the `i`-th at an offset bump the cursor** to the cursor past their buffers,
a frame pending when one was or is reserved. -/
theorem cursor_take {e : Ent} {off : ℕ} (hU : HintsUp (A e.I.t.name).d (A e.I.t.name).X.entry)
    (hF : CurFactsX (A e.I.t.name).X (A e.I.t.name).body (A e.I.t.name).code (A e.I.t.name).d)
    (hnc : NcTop A e off) (i : ℕ) :
    bumpL (cursorAt L A e off) ((treeSteps L A e off).take i) =
      curForm L e (nbAt (A e.I.t.name).X (A e.I.t.name).d off +
          ((hintsAtOff (A e.I.t.name) off).take i).countP (isBuf (A e.I.t.name).X))
        (pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off ||
          ((hintsAtOff (A e.I.t.name) off).take i).any (isFrame (A e.I.t.name).X)) := by
  rw [cursorAt_eq, treeSteps, stepsOf_take]
  refine bump_stepsOf (cf := curForm L e) (fun n ↦ ?_) (fun _ ↦ isBuf_notFrame) _ _ _
    (ordHints_take _ _ i (ord_at hF off)) fun hc ↦ bufStep hU hnc ?_
  · cases hk : (e.I.t.kidsC coreProgram.loop)[e.nc]? with
    | none =>
      unfold curForm
      rw [hk]
      exact bump_zero _
    | some k => rw [curForm_true hk, curForm_false]; rfl
  · exact lt_of_lt_of_le hc (List.take_sublist _ _).countP_le

theorem rszA_none {M : ℕ → E} {s : St} {h : Hint} (hp : allocPtr h = none) : rszA M s h = (false, 0) := by
  cases h <;> simp_all [allocPtr, rszA]

theorem allocPtr_none {X : AlignCtx} {h : Hint} (hb : isBuf X h = false) (hf : isFrame X h = false) :
    allocPtr h = none := by
  unfold isBuf at hb
  rw [hf] at hb
  simpa using hb

/-! ## `SizesAt` and `AllocReady` -/

/-- **Each hint takes its `treeSteps` entry**, from the facts by hint kind. -/
theorem sizesAt_of (hH : HintHyps L D A) (hB : BufReady L D A) (hFr : FrameReadyA L D A) :
    SizesAt L D A := by
  intro r hR hr C hCtx done e st s htr hch hnc hs hon i h sx hi hx hag
  have hne : (C.hints[s.pc]?).getD [] ≠ [] := fun h0 ↦ by rw [h0] at hi; simp at hi
  have hoff := hints_off hH.progAl hH.advAl hCtx htr hne
  have hfx := hints_follows _ s sx ⟨hs.agree.wf, hs.dl⟩ hx
  have hat : HintAtA L D A r C e s sx i h :=
    ⟨hR, hr, hCtx, ⟨done, st, htr, hch⟩, hnc, hs, hon, hi, hx, hfx.fp, hag⟩
  have hi' := hi
  rw [hoff] at hi'
  rw [treeSteps, stepsOf_getD _ _ _ _ _ _ _ h hi']
  cases hb : isBuf (A e.I.t.name).X h
  · cases hf : isFrame (A e.I.t.name).X h
    · simp only [Bool.cond_false]
      exact rszA_none (allocPtr_none hb hf)
    · simp only [Bool.cond_false, Bool.cond_true]
      exact (hFr r C e s sx i h hat hf).1
  · simp only [Bool.cond_true]
    exact (hB r C e s sx i h hat hb).1

/-- **Each allocation hint is ready where the tree puts the bump pointer**, from the facts by hint
kind. -/
theorem allocReady_of (hH : HintHyps L D A) (hC : CurHyps L D A) (hB : BufReady L D A) (hFr : FrameReadyA L D A)
    (hAr : AddrReady L D A) : AllocReady L D A := by
  intro r hR hr C hCtx done e st s htr hch hnc hs hon i h sx hi hx hm ha hin hnf
  have hne : (C.hints[s.pc]?).getD [] ≠ [] := fun h0 ↦ by rw [h0] at hi; simp at hi
  have hoff := hints_off hH.progAl hH.advAl hCtx htr hne
  have hat : HintAtA L D A r C e s sx i h :=
    ⟨hR, hr, hCtx, ⟨done, st, htr, hch⟩, hnc, hs, hon, hi, hx, hm.1, hm.2⟩
  have hE := htr.track.ents e List.mem_cons_self
  have hF := hC.facts _ _ hE.find
  have hU := hintsUp_of hH.progAl hE.find
  have hi' := hi
  rw [hoff] at hi'
  rw [cursor_take hU hF hnc i] at hnf
  have hkind : ∀ hk : isBuf (A e.I.t.name).X h = true ∨ isFrame (A e.I.t.name).X h = true,
      sx.nextFree = e.I.curA L.fs coreProgram.loop L.al (bufIdxA A e (s.pc - entOf A e.I.t.name) i) e.nc := by
    intro hk
    have h0 := ordHints_at _ _ i h (ord_at hF (s.pc - entOf A e.I.t.name)) hi' hk
    rw [hnf, show (pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d (s.pc - entOf A e.I.t.name) ||
      ((hintsAtOff (A e.I.t.name) (s.pc - entOf A e.I.t.name)).take i).any (isFrame (A e.I.t.name).X)) = false from h0]
    rfl
  cases hb : isBuf (A e.I.t.name).X h
  · cases hf : isFrame (A e.I.t.name).X h
    · have hp := allocPtr_none hb hf
      have haddr : (∃ o, h = .frameAddress o) ∨ (∃ p c, h = .cellAddress p c) := by
        cases h <;> simp_all [isAllocHint, allocPtr]
      refine ⟨hAr r C e s sx i h hat haddr hin, ?_⟩
      rcases haddr with ⟨o, rfl⟩ | ⟨p, c, rfl⟩ <;> trivial
    · exact (hFr r C e s sx i h hat hf).2 hin (hkind (.inr hf))
  · exact (hB r C e s sx i h hat hb).2 hin (hkind (.inl hb))

/-- **The allocation track's obligations** from the bridge's premises, `main`'s frame in the layout,
the guest's cursor facts and the facts by hint kind. -/
theorem allocTrack_ofReady {R : Ref → Prop} {Km : Mode.Cert} {E0 : Mode.Env} (hH : HintHyps L D A)
    (hRH : ∀ r, R r → RefH L (D r) r) (hMain : MainOk Km E0) (hM : MainA L) (hC : CurHyps L D A)
    (hB : BufReady L D A) (hFr : FrameReadyA L D A) (hAr : AddrReady L D A) : AllocTrack R (YAlloc L D A) :=
  allocTrack_ofCur hH hRH hMain hM (sizesAt_of hH hB hFr) hC (allocReady_of hH hC hB hFr hAr)

end

end LeanVM.Guest.EndExec
