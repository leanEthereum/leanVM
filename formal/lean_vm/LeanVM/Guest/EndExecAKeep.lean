/-
  LeanVM.Guest.EndExecAKeep

  The bump pointer's track along the run, aligned: each step keeps `YAlloc`, and the allocation
  track's obligations follow from the steps each hint takes on the honest tree, the cursor following
  each step of the tree track, and each allocation hint ready at the bump pointer.
-/

module

public import LeanVM.Guest.EndExecA
public import LeanVM.Guest.EndExecH
import all Statement.Data.AdviceHints

/-!
# The bump pointer's track along the run, aligned

The bus era's `EndExecAKeep.lean` on Hotwire's aligned allocator: a hint moves the bump pointer by
a step `(a, n)` (`Memory.bump`: `c ↦ allocBase a c + n`), not by a size.

`treeSteps L A e off`: the steps the hints at offset `off` of frame `e` take on the honest tree, in
order: a buffer hint its function's buffer of its index (`Bridge.nbAt` before it), never aligned; a
callee frame's hint the block of the frame's next callee, aligned as the layout allocates that
callee (`L.al`); any other hint none.

What is left, three named facts on the references of the honest tree (`RefH`), the bus era's:

* `SizesAt L D A`: each hint at a frame's pc, run from the state the hints before it reach, takes its
  `treeSteps` entry (`Memory.rszA`: its alignment and its size read off the reference memory);
* `CurArith L D A`: the reference step from a state of the tree track, its frames chained, lands at
  a state of the track whose top frame's cursor is the old one bumped by the offset's `treeSteps`,
  its frames chained;
* `AllocReady L D A`: each allocation hint, run from the state the hints before it reach, whose bump
  pointer is the frame's cursor bumped by the steps those hints take, has what it needs (`HintOk`)
  and its reservation within the reference's `2^κ` (`AllocB`).

Proved here: `keepY_alloc` (each step keeps `YAlloc`, from `SizesAt` and `CurArith`: the hints move
the bump pointer by their steps, `Memory.hints_nextFreeA`, the instruction keeps it,
`runOp_nextFree`; in the prologue there are no hints and `nextFree` is `main`'s frame, at its last
step the run enters `main`, whose cursor is past its frame, `refTrack_mainA`), `hintAllocW_of`
(`AllocReady` at the bump pointer the hints before it reach), and `allocTrack_of`: `AllocTrack R
(YAlloc L D A)` from the bridge's premises, `MainA L`, `SizesAt`, `CurArith` and `AllocReady`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec
open LeanVM.Guest.Mode (HintIn)

@[expose] public section

/-- The hints at offset `off` of function `F`. -/
def hintsAtOff (F : FnAl) (off : ℕ) : List Hint := (F.d.2.2.lookup (F.X.entry + off)).getD []

/-- **The steps the hints at offset `off` of frame `e` take on the honest tree**, in order. -/
noncomputable def treeSteps (L : Lay) (A : String → FnAl) (e : Ent) (off : ℕ) : List (Bool × ℕ) :=
  stepsOf (isBuf (A e.I.t.name).X) (isFrame (A e.I.t.name).X) (fun k ↦ e.I.t.bufs.getD k 0)
    ((((e.I.t.kidsC coreProgram.loop)[e.nc]?).map fun k ↦ (L.al k.name, k.block L.fs coreProgram.loop)).getD
      (false, 0))
    (hintsAtOff (A e.I.t.name) off) (nbAt (A e.I.t.name).X (A e.I.t.name).d off)

/-- **Each hint takes its `treeSteps` entry**: at a state of the tree track on a reference of the
honest tree, its frames chained, no call before its buffers, the `i`-th hint at its pc, run from
the state the hints before it reach, whose written cells hold the reference's words. -/
def SizesAt (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r : Ref, RefH L (D r) r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ done e st (s : St),
    RefTrack L D A r s.pc s.fp (done, e :: st) → ChainA L A (memOf r.img) (e :: st) →
    NcTop A e (s.pc - entOf A e.I.t.name) → Fine (refMem r.img) s → OnRef guestProgram r.img r.n s →
    ∀ (i : ℕ) (h : Hint) (sx : St), ((C.hints[s.pc]?).getD [])[i]? = some h →
      (((C.hints[s.pc]?).getD []).take i).foldlM (runHint C) s = .ok sx →
      (∀ c v, sx.mem.get c = some v → refMem r.img c = v) →
      rszA (refMem r.img) sx h = (treeSteps L A e (s.pc - entOf A e.I.t.name)).getD i (false, 0)

/-- **Each allocation hint is ready where the tree puts the bump pointer**: at a state of the tree
track on a reference of the honest tree, its frames chained, no call before its buffers, the `i`-th
hint at its pc, an allocation whose cells it reads are written, run from the state the hints before
it reach, whose bump pointer is the frame's cursor bumped by the steps those hints take, has what
it needs, its reservation within the reference's `2^κ`. -/
def AllocReady (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r : Ref, RefH L (D r) r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ done e st (s : St),
    RefTrack L D A r s.pc s.fp (done, e :: st) → ChainA L A (memOf r.img) (e :: st) →
    NcTop A e (s.pc - entOf A e.I.t.name) → Fine (refMem r.img) s → OnRef guestProgram r.img r.n s →
    ∀ (i : ℕ) (h : Hint) (sx : St), ((C.hints[s.pc]?).getD [])[i]? = some h →
      (((C.hints[s.pc]?).getD []).take i).foldlM (runHint C) s = .ok sx → MovesW (refMem r.img) s sx →
      isAllocHint h = true → HintIn sx h →
      sx.nextFree = bumpL (cursorAt L A e (s.pc - entOf A e.I.t.name))
        ((treeSteps L A e (s.pc - entOf A e.I.t.name)).take i) →
      HintOk C (refMem r.img) sx h ∧ AllocB (2 ^ r.κ) sx h

/-- **The cursor follows each step of the tree track**: from a state of the track at `(pc, fp)` on a
reference of the honest tree, its frames chained, no call before its buffers, the reference step to
registers short of the final ones lands at a state of the track whose top frame's cursor is the old
one bumped by the steps the hints at `pc` take, its frames chained, no call before its buffers. -/
def CurArith (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r : Ref, RefH L (D r) r → r.Ok → ∀ pc fp done e st r', RefTrack L D A r pc fp (done, e :: st) →
    ChainA L A (memOf r.img) (e :: st) → NcTop A e (pc - entOf A e.I.t.name) →
    step guestProgram r.img (regs pc fp) = some r' → r' ≠ Registers.final guestProgram →
    ∃ pc' fp' done' e' st', r' = regs pc' fp' ∧ RefTrack L D A r pc' fp' (done', e' :: st') ∧
      cursorAt L A e' (pc' - entOf A e'.I.t.name) =
        bumpL (cursorAt L A e (pc - entOf A e.I.t.name)) (treeSteps L A e (pc - entOf A e.I.t.name)) ∧
      ChainA L A (memOf r.img) (e' :: st') ∧ NcTop A e' (pc' - entOf A e'.I.t.name)

end

public section

/-! ## An instruction keeps the bump pointer -/

theorem nf_logOr {s s' : St} {x : K} {b k : ℕ} {f : Fault} (h : s.logOr x b f = .ok (k, s')) :
    s'.nextFree = s.nextFree := by
  unfold St.logOr at h
  rw [St.log_eq] at h
  split at h
  · rename_i k' s1 hp
    simp only [pure_ok, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    rfl
  · simp at h

/-- **An instruction keeps `nextFree`.** -/
theorem runOp_nextFree {C : Ctx} {s s' : St} {op : Op} (e : runOp C s op = .ok s') : s'.nextFree = s.nextFree := by
  cases op with
  | xor a b c =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, _, -, _, -, _, -, _, -, s1, h1, rfl⟩ := e
    exact (withMem_nextFree h1).1
  | mul a b c =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, _, -, _, -, s1, h1, rfl⟩ := e
    exact (withMem_nextFree h1).1
  | set o k =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, s1, h1, rfl⟩ := e
    exact (withMem_nextFree h1).1
  | deref o1 o2 o3 mode =>
    simp only [runOp, bind_ok] at e
    obtain ⟨_, -, p, -, e⟩ := e
    split_ifs at e
    · exact absurd e (by intro h; cases h)
    obtain ⟨⟨a2, s1⟩, h1, e⟩ := bind_ok.mp e
    simp only [bind_ok, pure_ok] at e
    obtain ⟨_, -, s2, h2, rfl⟩ := e
    obtain ⟨D, rfl⟩ := St.derefCell_dl h1
    exact (withMem_nextFree h2).1
  | jump c d f =>
    simp only [runOp, bind_ok] at e
    obtain ⟨_, -, _, -, _, -, _, -, vc, -, _, -, vd, -, _, -, vf, -, s1, h1, e⟩ := e
    split_ifs at e
    · simp only [pure_ok] at e; subst e; exact (withMem_nextFree h1).1
    · rw [bind_ok] at e
      obtain ⟨⟨pc, s2⟩, h2, e⟩ := e
      rw [bind_ok] at e
      obtain ⟨⟨fp, s3⟩, h3, e⟩ := e
      simp only [pure_ok] at e
      subst e
      exact (nf_logOr h3).trans ((nf_logOr h2).trans (withMem_nextFree h1).1)
  | keccak ins out inOdd outOdd count =>
    simp only [runOp, bind_ok, pure_ok] at e
    obtain ⟨_, -, _, -, _, -, _, -, s1, h1, rfl⟩ := e
    exact (withMem_nextFree h1).1

/-! ## The hints' steps -/

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **The hints' list at a frame of the track has its `treeSteps`' length**, and is the advice's at
the frame's offset. -/
theorem hints_len (hP : ProgAl guestProgram coreProgram A) (hAd : AdvAl A) {r : Ref}
    {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack L D A r s.pc s.fp (done, e :: st)) (hpcS : s.pc < C.ops.size) :
    ((C.hints[s.pc]?).getD []).length = (treeSteps L A e (s.pc - entOf A e.I.t.name)).length := by
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨-, hat⟩ := htr.linked.top
  obtain ⟨off, hpc, p, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal'
  have hsize := (ctx_of_spec hC).1
  have hpcE : s.pc = (A e.I.t.name).X.entry + off := hpc
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (by rw [← hsize]; exact hpcS)
  have hoff : s.pc - entOf A e.I.t.name = off := by
    show s.pc - (A e.I.t.name).X.entry = off
    omega
  rw [hoff, treeSteps, length_stepsOf, hh, hintsAtOff, hAd _ _ hE.find off ins hins, ← hpcE]

/-! ## The step -/

/-- **Each step keeps the bump pointer's track**, from `SizesAt` and `CurArith`. -/
theorem keepY_alloc {Km : Mode.Cert} {E0 : Mode.Env} (hMain : MainOk Km E0)
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen) (hL : AlLayout A)
    (hAd : AdvAl A) (hM : MainA L) (hS : SizesAt L D A) (hCA : CurArith L D A)
    {Y : Ref → St → Prop} (hY : ∀ r s, Y r s → YAlloc L D A r s) {r : Ref} (hR : RefH L (D r) r)
    (hr : r.Ok) {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {op : Op} {s1 s' : St}
    (hon : OnRun (XOf Y) r s) (hop : C.ops[s.pc]? = some op)
    (e1 : ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1) (hm : Moves (refMem r.img) s s1)
    (hmo : OpModed (refMem r.img) s1 op) (e : runOp C s1 op = .ok s') :
    YAlloc L D A r { s' with steps := s'.steps + 1 } := by
  have hκ : r.κ ≤ 28 := hr.log
  have hYs := hY r s hon.1.2
  obtain ⟨r1, k, hk, hstep, hrun1, hd⟩ :=
    step_done hκ hC hm.fine (Mode.onRef_moves hm hon.2.2) (by rw [hm.pc]; exact hop) hmo e
  have hst : s'.steps = s.steps := hd.steps.trans hm.steps
  rw [hm.steps] at hk
  rw [hm.pc, hm.fp] at hstep
  have hpcS : s.pc < C.ops.size := (Array.getElem?_eq_some_iff.mp hop).1
  have hsize := (ctx_of_spec hC).1
  have hpc62 : s.pc < 2 ^ 62 := by rw [hsize, guest_logSize] at hpcS; omega
  have hpos := posAt hR hon.1.1 hpc62 hon.2.1.fp
  have hnf' : s'.nextFree = s1.nextFree := runOp_nextFree e
  refine ⟨fun hlt ↦ ?_, fun hge hn ↦ ?_⟩
  · have hs : s.steps < proLen := by dsimp only at hlt; omega
    have hpc : s.pc < proLen := by rw [(hpos.1 hs).1]; exact hs
    show s'.nextFree = _
    rw [hnf', ← hYs.1 hs]
    rw [hints_pro hC rfl hpc] at e1
    simp only [List.foldlM_nil, pure_ok] at e1
    rw [e1]
  dsimp only at hge hn ⊢
  have hne1 : r1 ≠ Registers.final guestProgram := by
    rintro rfl
    cases k with
    | zero => omega
    | succ k' =>
      rw [run_succ_of_eq rfl] at hrun1
      cases hrun1
  by_cases hpro : s.steps < proLen
  · obtain ⟨hpc, hfp⟩ := hpos.1 hpro
    obtain ⟨o0, k0, k1, hins0⟩ := pro_set hMain (show s.pc < proLen by omega)
    have hset := op_pro hC (show s.pc < proLen by omega) hins0
    rw [hop] at hset
    cases hset
    obtain ⟨hpc', hfp', -⟩ := Mode.runOp_next (⟨hm.fine.agree.wf, hm.fine.dl⟩ : s1.Good) hm.fine.fp
      (by rw [hm.pc]; exact hpcS) e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    obtain ⟨e0, htr, hcur, hch, hnc0⟩ := refTrack_mainA hP hmain hM hR
    have h2 : s'.pc = proLen := by rw [hpc', hm.pc]; omega
    have hnf1 : s1.nextFree = s.nextFree := by
      rw [hints_pro hC rfl (show s.pc < proLen by omega)] at e1
      simp only [List.foldlM_nil, pure_ok] at e1
      rw [e1]
    refine ⟨[], e0, [], ?_, ?_, hch, by rw [h2]; exact hnc0⟩
    · rw [h2, hfp', hm.fp, hfp]; exact htr
    · rw [hnf', hnf1, hYs.1 hpro, h2, hcur]
  obtain ⟨done, e0, st0, htr, hcur, hch, hnc⟩ := hYs.2 (by omega) hon.2.2.1
  obtain ⟨pc', fp', done', e', st', hr', hts', hcur', hch', hnc'⟩ :=
    hCA r hR hr _ _ _ _ _ _ htr hch hnc (by rw [regs_eq]; exact hstep) hne1
  rw [← hd.regs] at hr'
  have hE3 := hts'.track.ents e' List.mem_cons_self
  obtain ⟨hfp3, hat3⟩ := hts'.linked.top
  have hpc2 := (entry_of_atPc hP hL hE3 hat3).1
  have hfpl := inst_fp_lt hR hr hE3.mem
  have hspc := hd.pc
  have hsfp := hd.fine.fp
  rw [hsize, guest_logSize] at hspc
  rw [guest_logSize] at hpc2
  rw [hfp3] at hfpl
  unfold maxCells at hfpl hsfp
  rw [regs_eq] at hr'
  have e_pc : s'.pc = pc' := gpow_inj (by omega) (by omega) (congrArg Registers.pc hr')
  have e_fp : s'.fp = fp' := gpow_inj (by omega) (by omega) (congrArg Registers.fp hr')
  refine ⟨done', e', st', by rw [e_pc, e_fp]; exact hts', ?_, hch', by rw [e_pc]; exact hnc'⟩
  have hlen := hints_len hP hAd hC htr hpcS
  have hs1 := hints_nextFreeA _ _ s s1 ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ e1 hm.fine.agree.get hlen
    fun i h sx hi hx ↦ hS r hR hr C hC done e0 st0 s htr hch hnc hon.2.1 hon.2.2 i h sx hi hx fun c v hv ↦
      hm.fine.agree.get c v ((hints_follows _ sx s1 (hints_follows _ s sx ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ hx).good
        (by
          have := e1
          rw [← List.take_append_drop i ((C.hints[s.pc]?).getD []), List.foldlM_append, hx, ok_bind] at this
          exact this)).le.get _ _ hv)
  show s'.nextFree = _
  rw [e_pc, hcur', hnf', hs1, hcur]

/-! ## The allocation hints -/

/-- **An allocation hint's needs from `YAlloc`**, `SizesAt` and `AllocReady`: the hints before it
move the bump pointer by the steps they take on the tree. -/
theorem hintAllocW_of (hP : ProgAl guestProgram coreProgram A) (hAd : AdvAl A)
    (hS : SizesAt L D A) (hR : AllocReady L D A) {Y : Ref → St → Prop} (hY : ∀ r s, Y r s → YAlloc L D A r s)
    {r : Ref} (hRH : RefH L (D r) r) (hr : r.Ok) {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s : St}
    (hon : OnRun (XOf Y) r s) {pre : List Hint} {h : Hint} {post : List Hint}
    (hl : (C.hints[s.pc]?).getD [] = pre ++ h :: post) {s1 : St} (e1 : pre.foldlM (runHint C) s = .ok s1)
    (hm : MovesW (refMem r.img) s s1) (ha : isAllocHint h = true) (hin : HintIn s1 h) :
    HintOk C (refMem r.img) s1 h ∧ AllocB (2 ^ r.κ) s1 h := by
  have hYs := hY r s hon.1.2
  have hne : (C.hints[s.pc]?).getD [] ≠ [] := by rw [hl]; simp
  have hpc2 : s.pc < 2 ^ guestProgram.logSize := pc_lt_of_hints hC hne
  have hpcS : s.pc < C.ops.size := by rw [(ctx_of_spec hC).1]; exact hpc2
  by_cases hpro : s.steps < proLen
  · have hpc : s.pc < proLen := by
      rw [((posAt hRH hon.1.1 (by rw [guest_logSize] at hpc2; omega) hon.2.1.fp).1 hpro).1]; exact hpro
    exact absurd (hints_pro hC rfl hpc) hne
  obtain ⟨done, e, st, htr, hcur, hch, hnc⟩ := hYs.2 (by omega) hon.2.2.1
  have hlen := hints_len hP hAd hC htr hpcS
  have hi : ((C.hints[s.pc]?).getD [])[pre.length]? = some h := by rw [hl]; simp
  have htake : ((C.hints[s.pc]?).getD []).take pre.length = pre := by rw [hl]; simp
  refine hR r hRH hr C hC done e st s htr hch hnc hon.2.1 hon.2.2 pre.length h s1 hi (by rw [htake]; exact e1) hm ha
    hin ?_
  have hs1 := hints_nextFreeA pre ((treeSteps L A e (s.pc - entOf A e.I.t.name)).take pre.length) s s1
    ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ e1 hm.2 (by
      rw [List.length_take]
      have : pre.length ≤ ((C.hints[s.pc]?).getD []).length := by rw [hl]; simp
      omega)
    fun j h' sx hj hx ↦ by
      have hjl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
      have h1 := hS r hRH hr C hC done e st s htr hch hnc hon.2.1 hon.2.2 j h' sx
        (by rw [hl, List.getElem?_append_left hjl]; exact hj)
        (by rw [hl, List.take_append_of_le_length hjl.le]; exact hx) fun c v hv ↦
        hm.2 c v ((hints_follows _ sx s1 (hints_follows _ s sx ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ hx).good
          (by
            have := e1
            rw [← List.take_append_drop j pre, List.foldlM_append, hx, ok_bind] at this
            exact this)).le.get _ _ hv)
      rw [h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hjl]
  rw [hs1, hcur]

/-- **The allocation track's obligations**, for the bump pointer's track `YAlloc L D A`, on the
references of the honest tree, from the bridge's premises, `main`'s frame in the layout, `SizesAt`,
`CurArith` and `AllocReady`. -/
theorem allocTrack_of {R : Ref → Prop} {Km : Mode.Cert} {E0 : Mode.Env} (hH : HintHyps L D A)
    (hRH : ∀ r, R r → RefH L (D r) r) (hMain : MainOk Km E0) (hM : MainA L) (hS : SizesAt L D A)
    (hCA : CurArith L D A) (hR : AllocReady L D A) : AllocTrack R (YAlloc L D A) where
  init := fun _ _ _ _ _ _ _ ↦ initY_alloc
  keep := fun _ hY r hR0 hr _ hC _ _ _ _ hon hop e1 hm hmo e ↦
    keepY_alloc hMain hH.progAl hH.mainAt hH.layout hH.advAl hM hS hCA hY (hRH r hR0) hr hC hon hop e1 hm hmo e
  hint := fun _ hY r hR0 hr _ hC _ hon _ _ _ hl _ e1 hm ha hin ↦
    (hintAllocW_of hH.progAl hH.advAl hS hR hY (hRH r hR0) hr hC hon hl e1 hm.w ha hin).1
  used := fun _ hY r hR0 hr _ hC _ hon _ _ _ hl _ e1 hm ha hin ↦
    (hintAllocW_of hH.progAl hH.advAl hS hR hY (hRH r hR0) hr hC hon hl e1 hm ha hin).2

/-- **`ExecGaps` from the hint bridge, the allocation track the bump pointer's**: `ExecGaps.ofHints`
at `YAlloc L D A`, its obligations from `MainA L`, `SizesAt`, `CurArith` and `AllocReady`. -/
theorem ExecGaps.ofHintsA {R : Ref → Prop} {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env}
    {Ct : Ref → Mode.Cts} {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D A)
    (hRH : ∀ r, R r → RefH L (D r) r) (hM : MainA L) (hS : SizesAt L D A) (hCA : CurArith L D A)
    (hR : AllocReady L D A) (certs : ModeCerts Ks Km E0) (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D A (YAlloc L D A))) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok → Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D A (YAlloc L D A)) r s))
    (term : TermRef R Ks (XOf (YH L D A (YAlloc L D A)))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D A (YAlloc L D A)) :=
  ExecGaps.ofHints hH (allocTrack_of hH hRH main hM hS hCA hR) hRH certs main frame ctMain res term

end

end LeanVM.Guest.EndExec
