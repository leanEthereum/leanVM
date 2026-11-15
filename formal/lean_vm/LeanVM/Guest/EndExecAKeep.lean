/-
  LeanVM.Guest.EndExecAKeep

  The bump pointer's track along the run: each step keeps `YAlloc`, from the words each hint
  reserves on the honest tree and the cursor following each step of the tree track.
-/

module

public import LeanVM.Guest.EndExecA
public import LeanVM.Guest.EndExecYKeep
public import LeanVM.Guest.EndExecYAl
public import LeanVM.Guest.Memory.Bump
public import LeanVM.Guest.Bridge.StepOff

/-!
# The bump pointer's track along the run

`treeSizes A e off`: the words each hint at offset `off` of frame `e` reserves on the honest tree,
in order: a buffer hint its function's buffer of its index (`Bridge.nbAt` before it), a callee
frame's hint the block of the frame's next callee, any other hint nothing.

`keepY_alloc`: each step keeps `YAlloc`, its advised sizes' track (`HeapAt`) by `HeapArith` (each step
of the tree track pops what the hints at its offset pop, `heapArith_alignA` in `EndExecAHeap.lean`)
from the honest pushes of `heap_sizes` at `main`'s entry (`HeapPopsA`), and the rest from two facts:

* `SizesAt`: each hint at a frame's pc, run from the state the hints before it reach, reserves its
  `treeSizes` entry (`Memory.rsz`: its size read off the reference memory and the streams);
* `CurArith`: the reference step from a state of the tree track, its frames chained, lands at a
  state of the track whose top frame's cursor is the old one moved by the offset's `treeSizes`, its
  frames chained (`Bridge.stepRule_at` with the allocation check's static facts).

In the prologue there are no hints and `nextFree` is past `main`'s frame; at its last step the run
enters `main`, whose frame's cursor is past its frame (`refTrack_mainA`).

`hintAlloc_of`: `ExecGaps.hintAlloc` from `YAlloc`, `SizesAt` and `AllocReady` (each allocation hint has
what it needs once the bump pointer is the frame's cursor moved by the words the hints before it
reserve): the hints before it move the bump pointer by their `treeSizes` (`Memory.hints_nextFree`).
`keepY_allocA`, `hintAlloc_alignA`: both on the deployed alignment. `CurArith alignA` is proved in
`EndExecACur.lean` (`curArith_alignA`); `SizesAt alignA` and `AllocReady alignA` in `EndExecAReady.lean`
from the facts it names (`AllocGaps`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec
open LeanVM.Guest.End (mainEntry)

@[expose] public section

/-- The hints at offset `off` of function `F`. -/
def hintsAtOff (F : FnAl) (off : ℕ) : List Hint := (F.d.2.2.lookup (F.X.entry + off)).getD []

/-- **The words the hints at offset `off` of frame `e` reserve on the honest tree**, in order. -/
noncomputable def treeSizes (A : String → FnAl) (e : Ent) (off : ℕ) : List ℕ :=
  let F := A e.I.t.name
  let hs := hintsAtOff F off
  (List.range hs.length).map fun i ↦ match hs[i]? with
    | some h =>
      if isBuf F.X h then e.I.t.bufs.getD (nbAt F.X F.d off + ((hs.take i).filter (isBuf F.X)).length) 0
      else if isFrame F.X h then
        (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map (Tree.block B2C.fs coreProgram.loop)).getD 0
      else 0
    | none => 0

/-- **Each hint reserves its `treeSizes` entry**: at a state of the tree track on the reference run, its
frames chained, no call before its buffers, the `i`-th hint at its pc, run from the state the hints before it reach,
whose written cells hold the reference's words. -/
def SizesAt (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ done e st (s : St),
    RefTrack A r s.pc s.fp (done, e :: st) → ChainA A (memOf r.img) (e :: st) →
    NcTop A e (s.pc - entOf A e.I.t.name) → HeapAt A r s e st → Fine (refMem r.img) s → OnRef guestProgram r.img r.n s →
    ∀ (i : ℕ) (h : Hint) (sx : St), ((C.hints[s.pc]?).getD [])[i]? = some h →
      (((C.hints[s.pc]?).getD []).take i).foldlM (runHint C) s = .ok sx →
      (∀ c v, sx.mem.get c = some v → refMem r.img c = v) →
      rsz C (refMem r.img) sx h = (treeSizes A e (s.pc - entOf A e.I.t.name)).getD i 0

/-- **Each allocation hint is ready where the tree puts the bump pointer**: at a state of the tree
track on the reference run, its frames chained, no call before its buffers, the `i`-th hint at its pc, an allocation whose cells it reads are written,
run from the state the hints before it reach, whose bump pointer is the frame's cursor moved by the
words those hints reserve, has what it needs. -/
def AllocReady (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ done e st (s : St),
    RefTrack A r s.pc s.fp (done, e :: st) → ChainA A (memOf r.img) (e :: st) →
    NcTop A e (s.pc - entOf A e.I.t.name) → HeapAt A r s e st → Fine (refMem r.img) s → OnRef guestProgram r.img r.n s →
    ∀ (i : ℕ) (h : Hint) (sx : St), ((C.hints[s.pc]?).getD [])[i]? = some h →
      (((C.hints[s.pc]?).getD []).take i).foldlM (runHint C) s = .ok sx → Moves (refMem r.img) s sx →
      isAllocHint h = true → Mode.HintIn sx h →
      sx.nextFree = cursorAt A e (s.pc - entOf A e.I.t.name) + ((treeSizes A e (s.pc - entOf A e.I.t.name)).take i).sum →
      HintOk C (refMem r.img) sx h

/-- **The cursor follows each step of the tree track**: from a state of the track at `(pc, fp)`, its
frames chained, no call before its buffers, the reference step to registers short of the final ones
lands at a state of the track whose top frame's cursor is the old one moved by the words the hints at
`pc` reserve, its frames chained, no call before its buffers. -/
def CurArith (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ pc fp done e st r', RefTrack A r pc fp (done, e :: st) →
    ChainA A (memOf r.img) (e :: st) → NcTop A e (pc - entOf A e.I.t.name) →
    step guestProgram r.img (regs pc fp) = some r' → r' ≠ Registers.final guestProgram →
    ∃ pc' fp' done' e' st', r' = regs pc' fp' ∧ RefTrack A r pc' fp' (done', e' :: st') ∧
      cursorAt A e' (pc' - entOf A e'.I.t.name) =
        cursorAt A e (pc - entOf A e.I.t.name) + (treeSizes A e (pc - entOf A e.I.t.name)).sum ∧
      ChainA A (memOf r.img) (e' :: st') ∧ NcTop A e' (pc' - entOf A e'.I.t.name) ∧
      ∃ off, pc = entOf A e.I.t.name + off ∧
        StepOff coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) r.img A e off st pc' fp' (e' :: st')

/-- **What the advised sizes' track becomes past a step**: the frames still chained, the entries they
still pop those before less the advised sizes the hints at the step's offset pop. -/
def HeapNext (A : String → FnAl) (M : ℕ → E) (e : Ent) (st : List Ent) (off : ℕ) (pc' : ℕ) : List Ent → Prop
  | [] => False
  | e' :: st' => ChainH A M (e' :: st') ∧ restH A (e' :: st') (pc' - entOf A e'.I.t.name) =
      (restH A (e :: st) off).drop ((hintsAtOff (A e.I.t.name) off).countP isAdv)

/-- **The advised sizes follow each step of the tree track.** -/
def HeapArith (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ pc fp done e st off pc' fp' st'' done', RefTrack A r pc fp (done, e :: st) →
    pc = entOf A e.I.t.name + off →
    StepOff coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) r.img A e off st pc' fp' st'' →
    RefTrack A r pc' fp' (done', st'') → ChainH A (memOf r.img) (e :: st) → HeapNext A (memOf r.img) e st off pc' st''

/-- **The hints at a frame's offset write its advised pointer cells there**, those whose buffers exist:
at a state of the tree track as in `SizesAt`, past the offset's hints. -/
def AdvWrites (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ done e st (s : St),
    RefTrack A r s.pc s.fp (done, e :: st) → ChainA A (memOf r.img) (e :: st) →
    NcTop A e (s.pc - entOf A e.I.t.name) → HeapAt A r s e st → Fine (refMem r.img) s → OnRef guestProgram r.img r.n s →
    s.pc < C.ops.size → ∀ s1, ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 → Moves (refMem r.img) s s1 →
    ∀ k p S, (bufsOf (A e.I.t.name).X (A e.I.t.name).d)[k]? = some (s.pc - entOf A e.I.t.name, .allocAdvice p S) →
      k < e.I.t.bufs.length → s1.mem.written (e.I.fp + p) = true

/-- The advised pointer cells written at frames `st` whose top is at `pc`. -/
def WrNext (A : String → FnAl) (m : Mem) (pc : ℕ) : List Ent → Prop
  | [] => True
  | e :: st => AdvWr A m (e :: st) (pc - entOf A e.I.t.name)

/-- **The advised pointer cells stay written past each step of the tree track**, given those at the
step's offset. -/
def WrArith (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ pc fp done e st off pc' fp' st'' done' (m : Mem), RefTrack A r pc fp (done, e :: st) →
    pc = entOf A e.I.t.name + off →
    StepOff coreProgram (honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) r.img A e off st pc' fp' st'' →
    RefTrack A r pc' fp' (done', st'') → AdvWr A m (e :: st) off →
    (∀ k p S, (bufsOf (A e.I.t.name).X (A e.I.t.name).d)[k]? = some (off, .allocAdvice p S) →
      k < e.I.t.bufs.length → m.written (e.I.fp + p) = true) →
    WrNext A m pc' st''

/-- **The honest pushes of `heap_sizes` are the reference tree's advised sizes**, on alignment `A`. -/
def HeapPopsA (A : String → FnAl) : Prop := ∀ r : Ref, r.Ok → heapStream r = r.T.heapPops fun f ↦ slotsOf (A f)

/-- The advice's hints pop `heap_sizes` exactly when they are advised sizes. -/
def heapHintOk (h : Hint) : Bool := popsOn Hints.heapSizeStream h == isAdv h

end

public section

theorem adviceHints_heap : Data.adviceHints.all (fun p ↦ p.2.all heapHintOk) = true := by decide +kernel

/-- **The executor's hints pop `heap_sizes` exactly at the advised sizes.** -/
theorem hints_heap {adv : Advice} {C : Ctx} (hC : Ctx.of guestProgram adv = .ok C) (ha : adv.hints = Data.adviceHints)
    (pc : ℕ) : ∀ h ∈ (C.hints[pc]?).getD [], popsOn Hints.heapSizeStream h = isAdv h := by
  intro h hh
  by_cases hpc : pc < 2 ^ guestProgram.logSize
  · rw [Mode.ctx_hints hC (ha ▸ Mode.adviceHints_incr) hpc, ha] at hh
    unfold Mode.hintsAt at hh
    split at hh
    · rename_i p hp
      have := List.all_eq_true.mp (List.all_eq_true.mp adviceHints_heap p (List.mem_of_find?_eq_some hp)) h hh
      simpa [heapHintOk] using this
    · cases hh
  · have hsz : C.hints.size = 2 ^ guestProgram.logSize := by
      simp only [Ctx.of, bind_ok, pure_ok] at hC
      obtain ⟨ops, -, rfl⟩ := hC
      exact (foldl_set_size _ _).trans (Array.size_replicate ..)
    rw [Array.getElem?_eq_none (by omega)] at hh
    cases hh

theorem advWrTop_mono {A : String → FnAl} {m m' : Mem} (h : m ≤ m') {e : Ent} {off : ℕ}
    (hw : AdvWrTop A m e off) : AdvWrTop A m' e off :=
  fun k o p S hk ho hb ↦ Mode.written_mono h (hw k o p S hk ho hb)

/-- **Memory growing keeps the advised pointer cells written.** -/
theorem advWr_mono {A : String → FnAl} {m m' : Mem} (h : m ≤ m') :
    ∀ {st : List Ent} {off : ℕ}, AdvWr A m st off → AdvWr A m' st off
  | [], _, _ => trivial
  | _ :: _, _, ⟨h1, h2⟩ => ⟨advWrTop_mono h h1, fun e' he' o ↦ advWrTop_mono h (h2 e' he' o)⟩

theorem filter_heap {l : List Hint} (h : ∀ x ∈ l, popsOn Hints.heapSizeStream x = isAdv x) :
    (l.filter (popsOn Hints.heapSizeStream)).length = l.countP isAdv := by
  rw [← List.countP_eq_length_filter]
  exact List.countP_congr fun x hx ↦ by rw [h x hx]

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
    obtain ⟨_, -, _, -, _, -, s1, h1, rfl⟩ := e
    exact (withMem_nextFree h1).1

/-! ## `main`'s entry -/

/-- **The root's block is `main`'s frame.** -/
theorem block_main {r : Ref} (hr : r.Ok) : r.T.block B2C.fs coreProgram.loop = r.adv.mainFrame := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  have hv := hH.valid
  have hn := hr.name
  rcases hT : r.T with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
  · rw [hT] at hn
    simp only [Tree.name] at hn
    subst hn
    rw [Tree.block, ite_eq_right (by rw [B2C.main_not_loop]; decide), Nat.add_zero, B2C.fs_main]
    show B2C.mainFrame = Data.adviceMainFrame
    simp [B2C.mainFrame, Data.mainCells, Data.jtSlots, Data.adviceMainFrame]
  · rw [hT] at hv; exact hv.elim

/-- **The track at `main`'s entry, its cursor past `main`'s frame**: `main`'s frame at its body, at
frame `0`, nothing done. -/
theorem refTrack_mainA {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) {r : Ref} (hr : r.Ok) :
    ∃ e, RefTrack A r mainEntry 0 ([], [e]) ∧ cursorAt A e (mainEntry - entOf A e.I.t.name) = r.adv.mainFrame ∧
      ChainA A (memOf r.img) [e] ∧ NcTop A e (mainEntry - entOf A e.I.t.name) ∧ e.I.t = r.T ∧ e.nc = 0 ∧
      mainEntry - entOf A e.I.t.name = 0 := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  obtain ⟨I, rest, he, hIt, hfp, hcur, -⟩ := head_insts (fs := B2C.fs) (lp := coreProgram.loop) (H := B2C.H)
    r.T (0, r.T.block B2C.fs coreProgram.loop) r.hdr
  have hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T := by
    rw [honestInsts, he]; exact List.mem_cons_self
  have hv := hH.valid
  rw [← hIt] at hv
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? I.t.name = some fn := by
    rcases hIt' : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hIt'] at hv
      obtain ⟨fn, hf, -⟩ := hv
      exact ⟨fn, hf⟩
    · rw [hIt'] at hv; exact hv.elim
  have htr := trackOk_init (rd := r.rd0) hI hf hv
  rw [hIt] at htr
  have hname : I.t.name = "main" := by rw [hIt]; exact hr.name
  have hal0 : alOf A "main" 0 = some fn.body := by
    rw [hname] at hf
    change alignAt (A "main").X (A "main").body (A "main").code (A "main").d 0 = some fn.body
    rw [alignAt_zero (hP.ok _ _ hf), hP.body _ _ hf]
  have h0 := refOk_init (M := memOf r.img) (ent := entOf A) (al := alOf A) htr hfp (by rw [hname]; exact hal0)
  rw [hname, hmain] at h0
  have hen : entOf A (Ent.enter coreProgram I fn).I.t.name = mainEntry := by
    show entOf A I.t.name = mainEntry
    rw [hname, hmain]
  refine ⟨_, h0, ?_, fun _ hl hk ↦ absurd (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)) hk, fun _ ↦ rfl, hIt, rfl,
    by rw [hen, Nat.sub_self]⟩
  rw [hen, Nat.sub_self, cursorAt]
  have hnb : nbAt (A I.t.name).X (A I.t.name).d 0 = 0 := by
    unfold nbAt
    simp
  have hpe : pendAt (A I.t.name).X (A I.t.name).code (A I.t.name).d 0 = false := by
    unfold pendAt pendIn
    simp
  show I.curAt B2C.fs coreProgram.loop (nbAt (A I.t.name).X (A I.t.name).d 0) (calls ([] : List Ev)).length +
    (bif pendAt (A I.t.name).X (A I.t.name).code (A I.t.name).d 0 then _ else 0) = _
  rw [hnb, hpe, Inst.curAt, hcur, ← block_main hr]
  simp [calls]

/-! ## The step -/

/-- **Each step keeps the bump pointer's track**, from `SizesAt`, `CurArith` and `HeapArith`, the
advised sizes' stream the tree's (`HeapPopsA`). -/
theorem keepY_alloc {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) (hJ : JumpCellsAt A) (hL : AlLayout A) (hAd : AdvAl A)
    (hS : SizesAt A) (hCA : CurArith A) (hHA : HeapArith A) (hHP : HeapPopsA A) (hAW : AdvWrites A)
    (hWA : WrArith A) {Y : Ref → St → Prop} (hD : DerefPow Y) (hY : ∀ r s, Y r s → YAlloc A r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s1 s', OnRun (XOf Y) r s →
      C.ops[s.pc]? = some op → ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → runOp C s1 op = .ok s' → YAlloc A r { s' with steps := s'.steps + 1 } := by
  intro r hr C hC s op s1 s' hon hop e1 hm e
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hYs := hY r s hon.1.2.2
  have hmo : OpModed (refMem r.img) s1 op :=
    Mode.opModed_of hm.fine.agree (reads_of_runOp e) ((refOk_X hP hmain hJ hD hr hC hon hop).congr hm.fp)
  obtain ⟨r1, k, hk, hstep, hrun1, hd⟩ :=
    step_done hκ hC hm.fine (Mode.onRef_moves hm hon.2.2) (by rw [hm.pc]; exact hop) hmo e
  have hst : s'.steps = s.steps := hd.steps.trans hm.steps
  rw [hm.steps] at hk
  rw [hm.pc, hm.fp] at hstep
  have hpcS : s.pc < C.ops.size := (Array.getElem?_eq_some_iff.mp hop).1
  have hsize := (ctx_of_spec hC).1
  have hnf' : s'.nextFree = s1.nextFree := runOp_nextFree e
  have hhc : s'.cursor.getD Hints.heapSizeStream 0 =
      s.cursor.getD Hints.heapSizeStream 0 + ((C.hints[s.pc]?).getD []).countP isAdv := by
    rw [runOp_cursor e, hints_cursor _ _ s s1 e1, filter_heap (hints_heap hC rfl s.pc)]
  refine ⟨fun hlt ↦ ?_, fun hge hn ↦ ?_⟩
  · have hs : s.steps < proLen := by dsimp only at hlt; omega
    have hpc : s.pc < proLen := by
      rcases hon.1.1 with ⟨-, hpc, -⟩ | ⟨h, -⟩
      · omega
      · omega
    show s'.nextFree = _ ∧ s'.cursor.getD Hints.heapSizeStream 0 = 0
    rw [hhc, hints_pro hC rfl hpc, hnf', ← (hYs.1 hs).1, (hYs.1 hs).2]
    rw [hints_pro hC rfl hpc] at e1
    simp only [List.foldlM_nil, pure_ok] at e1
    rw [e1]
    exact ⟨rfl, rfl⟩
  dsimp only at hge hn ⊢
  have hne1 : r1 ≠ Registers.final guestProgram := by
    rintro rfl
    cases k with
    | zero => omega
    | succ k' =>
      rw [run_succ_of_eq rfl] at hrun1
      cases hrun1
  by_cases hpro : s.steps < proLen
  · obtain ⟨hpc, hfp⟩ : s.pc = s.steps ∧ s.fp = 0 := by
      rcases hon.1.1 with ⟨-, hpc, hfp⟩ | ⟨h, -⟩
      · exact ⟨hpc, hfp⟩
      · omega
    obtain ⟨k0, t, hset, -⟩ := op_pro hC (show s.pc < proLen by omega)
    rw [hop] at hset
    cases hset
    obtain ⟨hpc', hfp', -⟩ := Mode.runOp_next (⟨hm.fine.agree.wf, hm.fine.dl⟩ : s1.Good) hm.fine.fp
      (by rw [hm.pc]; exact hpcS) e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    obtain ⟨e0, htr, hcur, hch, hnc0, hIt0, hnc0', hoff0⟩ := refTrack_mainA hP hmain hr
    have h2 : s'.pc = mainEntry := by show s'.pc = proLen; rw [hpc', hm.pc]; omega
    have hnf1 : s1.nextFree = s.nextFree := by
      rw [hints_pro hC rfl (show s.pc < proLen by omega)] at e1
      simp only [List.foldlM_nil, pure_ok] at e1
      rw [e1]
    refine ⟨[], e0, [], ?_, ?_, hch, by rw [h2]; exact hnc0, ?_, trivial,
      ⟨fun _ _ _ _ _ ho _ ↦ absurd ho (by rw [h2, hoff0]; exact Nat.not_lt_zero _), fun _ h ↦ absurd h List.not_mem_nil⟩⟩
    · rw [h2, hfp', hm.fp, hfp]; exact htr
    · rw [hnf', hnf1, (hYs.1 hpro).1, h2, hcur]
    · rw [hhc, hints_pro hC rfl (show s.pc < proLen by omega), (hYs.1 hpro).2, h2, hoff0, hHP r hr]
      obtain ⟨rd, hH, -⟩ := hr.honest
      have hv := hH.valid
      rcases hT : r.T with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
      · rw [hT] at hIt0
        have hb : advBefore (A f) 0 = 0 := by simp [advBefore]
        simp only [List.countP_nil, Nat.add_zero, List.drop_zero]
        simp only [restH, kidsH, List.flatMap_nil, List.append_nil]
        rw [hIt0, hnc0']
        simp only [Tree.name, Tree.bufs, Tree.kids, List.drop_zero, hb,
          Tree.heapPops]
      · rw [hT] at hv; exact hv.elim
  obtain ⟨done, e0, st0, htr, hcur, hch, hnc, hha, hchH, hwr⟩ := hYs.2 (by omega) hon.2.2.1
  have hE := htr.track.ents e0 List.mem_cons_self
  obtain ⟨-, hat⟩ := htr.linked.top
  obtain ⟨off, hpc, p, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal'
  obtain ⟨pc', fp', done', e', st', hr', hts', hcur', hch', hnc', off', hpc0, hk'⟩ :=
    hCA r hr _ _ _ _ _ _ htr hch hnc hstep hne1
  rw [← hd.regs] at hr'
  have hE3 := hts'.track.ents e' List.mem_cons_self
  obtain ⟨hfp3, hat3⟩ := hts'.linked.top
  have hpc2 := (entry_of_atPc hP hL hE3 hat3).1
  have hfpl := inst_fp_lt hr hE3.mem
  have hspc := hd.pc
  have hsfp := hd.fine.fp
  rw [hsize, guest_logSize] at hspc
  rw [guest_logSize] at hpc2
  rw [hfp3] at hfpl
  unfold maxCells at hfpl hsfp
  have e_pc : s'.pc = pc' := gpow_inj (by omega) (by omega) (congrArg Registers.pc hr')
  have e_fp : s'.fp = fp' := gpow_inj (by omega) (by omega) (congrArg Registers.fp hr')
  -- the hints' words
  have hpcE : s.pc = (A e0.I.t.name).X.entry + off := hpc
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (by rw [← hsize]; exact hpcS)
  have hhs : (C.hints[s.pc]?).getD [] = hintsAtOff (A e0.I.t.name) off := by
    rw [hh, hintsAtOff, hAd _ _ hE.find off ins hins, ← hpcE]
  have hoff : s.pc - entOf A e0.I.t.name = off := by
    show s.pc - (A e0.I.t.name).X.entry = off
    omega
  have hoff' : off' = off := by
    have : s.pc = entOf A e0.I.t.name + off' := hpc0
    show off' = off
    have h2 : entOf A e0.I.t.name = (A e0.I.t.name).X.entry := rfl
    omega
  subst hoff'
  have hHN := hHA r hr _ _ _ _ _ _ _ _ _ _ htr hpc0 hk' hts' hchH
  obtain ⟨hchH', hrest⟩ := hHN
  refine ⟨done', e', st', by rw [e_pc, e_fp]; exact hts', ?_, hch', by rw [e_pc]; exact hnc', ?_, hchH', ?_⟩
  · have hlen : ((C.hints[s.pc]?).getD []).length = (treeSizes A e0 (s.pc - entOf A e0.I.t.name)).length := by
      rw [hoff, treeSizes, List.length_map, List.length_range, hhs]
    have hs1 := hints_nextFree _ _ s s1 ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ e1 hm.fine.agree.get hlen
      fun i h sx hi hx ↦ hS r hr C hC done e0 st0 s htr hch hnc ⟨hha, hchH, hwr⟩ hon.2.1 hon.2.2 i h sx hi hx fun c v hv ↦
        hm.fine.agree.get c v ((hints_follows _ sx s1 (hints_follows _ s sx ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ hx).good
          (by
            have := e1
            rw [← List.take_append_drop i ((C.hints[s.pc]?).getD []), List.foldlM_append, hx, ok_bind] at this
            exact this)).le.get _ _ hv)
    rw [e_pc, hcur', hnf', hs1, hcur]
  · rw [hhc, ← List.drop_drop, hha, hoff, hhs, e_pc, hrest]
  · have hle : s.mem ≤ s'.mem := Mem.le_trans hm.le hd.le
    have hw1 := hAW r hr C hC done e0 st0 s htr hch hnc ⟨hha, hchH, hwr⟩ hon.2.1 hon.2.2 hpcS s1 e1 hm
    rw [hoff] at hw1 hwr
    rw [e_pc]
    exact hWA r hr _ _ _ _ _ _ _ _ _ _ _ htr hpc0 hk' hts' (advWr_mono hle hwr)
      fun k p S hk hb ↦ Mode.written_mono hd.le (hw1 k p S hk hb)

/-! ## The allocation hints -/

/-- **The hints' list at a frame of the track has its `treeSizes`' length.** -/
theorem hints_len {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A) (hAd : AdvAl A) {r : Ref}
    {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack A r s.pc s.fp (done, e :: st)) (hpcS : s.pc < C.ops.size) :
    ((C.hints[s.pc]?).getD []).length = (treeSizes A e (s.pc - entOf A e.I.t.name)).length := by
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
  rw [hoff, treeSizes, List.length_map, List.length_range, hh, hintsAtOff, hAd _ _ hE.find off ins hins, ← hpcE]

/-- **`hintAlloc` from `YAlloc`**, `SizesAt` and `AllocReady`: the hints before an allocation hint
move the bump pointer by the words they reserve on the tree. -/
theorem hintAlloc_of {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A) (hAd : AdvAl A)
    (hS : SizesAt A) (hR : AllocReady A) {Y : Ref → St → Prop} (hY : ∀ r s, Y r s → YAlloc A r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isAllocHint h = true → Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h := by
  intro r hr C hC s hon pre h post hl s1 e1 hm ha hin
  have hYs := hY r s hon.1.2.2
  by_cases hpro : s.steps < proLen
  · have hpc : s.pc < proLen := by
      rcases hon.1.1 with ⟨-, hpc, -⟩ | ⟨hge, -⟩
      · omega
      · omega
    rw [hints_pro hC rfl hpc] at hl
    simp at hl
  obtain ⟨done, e, st, htr, hcur, hch, hnc, hha⟩ := hYs.2 (by omega) hon.2.2.1
  have hpcS : s.pc < C.ops.size := by
    by_contra hge
    have hsz := (ctx_hints_size hC).trans (ctx_of_spec hC).1.symm
    rw [Array.getElem?_eq_none (by omega)] at hl
    simp at hl
  have hlen := hints_len hP hAd hC htr hpcS
  have hi : ((C.hints[s.pc]?).getD [])[pre.length]? = some h := by rw [hl]; simp
  have htake : ((C.hints[s.pc]?).getD []).take pre.length = pre := by rw [hl]; simp
  refine hR r hr C hC done e st s htr hch hnc hha hon.2.1 hon.2.2 pre.length h s1 hi (by rw [htake]; exact e1) hm ha hin ?_
  have hs1 := hints_nextFree pre ((treeSizes A e (s.pc - entOf A e.I.t.name)).take pre.length) s s1
    ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ e1 hm.fine.agree.get (by
      rw [List.length_take]
      have : pre.length ≤ ((C.hints[s.pc]?).getD []).length := by rw [hl]; simp
      omega)
    fun j h' sx hj hx ↦ by
      have hjl : j < pre.length := (List.getElem?_eq_some_iff.mp hj).1
      have h1 := hS r hr C hC done e st s htr hch hnc hha hon.2.1 hon.2.2 j h' sx (by rw [hl, List.getElem?_append_left hjl]; exact hj)
        (by rw [hl, List.take_append_of_le_length hjl.le]; exact hx) fun c v hv ↦
        hm.fine.agree.get c v ((hints_follows _ sx s1 (hints_follows _ s sx ⟨hon.2.1.agree.wf, hon.2.1.dl⟩ hx).good
          (by
            have := e1
            rw [← List.take_append_drop j pre, List.foldlM_append, hx, ok_bind] at this
            exact this)).le.get _ _ hv)
      rw [h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hjl]
  rw [hs1, hcur]

/-! ## On the deployed alignment -/

/-- **Each step keeps `YAlloc alignA`**, from `SizesAt` and `CurArith` on the deployed alignment. -/
theorem keepY_allocA (hS : SizesAt alignA) (hCA : CurArith alignA) (hHA : HeapArith alignA)
    (hHP : HeapPopsA alignA) (hAW : AdvWrites alignA) (hWA : WrArith alignA) : KeepY (YAlloc alignA) :=
  keepY_alloc progAl alignA_main jumpCells_at alLayout_alignA advAl_alignA hS hCA hHA hHP hAW hWA (derefPow_all _)
    fun _ _ h ↦ h

/-- **`hintAlloc` on the deployed alignment**, from `SizesAt` and `AllocReady`. -/
theorem hintAlloc_alignA (hS : SizesAt alignA) (hR : AllocReady alignA) {Y : Ref → St → Prop}
    (hY : ∀ r s, Y r s → YAlloc alignA r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
      (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → isAllocHint h = true → Mode.HintIn s1 h → HintOk C (refMem r.img) s1 h :=
  hintAlloc_of progAl advAl_alignA hS hR hY

end

end LeanVM.Guest.EndExec
