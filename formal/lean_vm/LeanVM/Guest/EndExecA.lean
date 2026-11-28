/-
  LeanVM.Guest.EndExecA

  The bump pointer's track, aligned: past the prologue, the executor's next free cell is the top
  frame's cursor on the aligned layout, and each frame below resumes where the frame above ends.
-/

module

public import LeanVM.Guest.EndExecX
public import LeanVM.Guest.Bridge.AllocDefs
public import LeanVM.Guest.Memory.CursorA
public import LeanVM.Guest.Memory.BumpA

/-!
# The bump pointer's track, aligned

The bus era's `EndExecA.lean` on Hotwire's aligned allocator (b2c's `Memory/AllocA`, `CursorA`).

`cursorAt L A e off`: frame `e`'s cursor (`Inst.curA`) at offset `off` of its function, past the
buffers the function reserves before `off` (`Bridge.nbAt`) and the calls the frame has made, moved
by the next callee's reservation (its block at `allocBase (al k)` of the cursor) while its frame is
reserved and not entered (`Bridge.pendAt`). `ChainA`: each frame below the top resumes, at the
return pc the header of the frame above holds, at the cursor where that frame's subtree ends
(`Inst.endCurA`), and a loop iteration past all its calls has a phantom last callee (`TailA`).
`NcTop A e off`: at an offset at or before a buffer hint the frame has made no call. `YAlloc L D A r
s`: in the prologue the next free cell is past `main`'s frame; past it, a state of the tree track
at the state's pc and frame whose top frame's cursor is the next free cell, its frames chained,
`NcTop` at its offset.

`MainA L`: `main` is no loop helper and its frame is the advice's `mainFrame` (the layout's facts
the prologue's end reads). Proved here: the track holds initially (`initY_alloc`), and at `main`'s
entry the track's cursor is `main`'s frame's end (`refTrack_mainA`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-- **Frame `e`'s cursor at offset `off`**: past the buffers its function reserves before `off`
and its calls made, moved by the next callee's reservation while that callee's frame is reserved and
not entered. -/
noncomputable def cursorAt (L : Lay) (A : String → FnAl) (e : Ent) (off : ℕ) : ℕ :=
  bif pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off then
    (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map fun k ↦
      allocBase (L.al k.name) (e.I.curA L.fs coreProgram.loop L.al (nbAt (A e.I.t.name).X (A e.I.t.name).d off) e.nc)
        + k.block L.fs coreProgram.loop).getD
      (e.I.curA L.fs coreProgram.loop L.al (nbAt (A e.I.t.name).X (A e.I.t.name).d off) e.nc)
  else e.I.curA L.fs coreProgram.loop L.al (nbAt (A e.I.t.name).X (A e.I.t.name).d off) e.nc

/-- **A loop iteration past all its calls ended its loop**: its last callee is a phantom, its tail
call not taken. -/
def TailA (e : Ent) : Prop :=
  coreProgram.loop e.I.t.name = true → e.I.t.kids.length ≤ e.nc → ∀ hk : e.I.t.kids ≠ [],
    ∃ f σ, e.I.t.kids.getLast hk = .phantom f σ

/-- **No call before the buffers**: at an offset at or before a buffer hint of its function, the
frame has made no call. -/
def NcTop (A : String → FnAl) (e : Ent) (off : ℕ) : Prop :=
  (∃ q ∈ bufsOf (A e.I.t.name).X (A e.I.t.name).d, off ≤ q.1) → e.nc = 0

/-- **Each frame below resumes where the frame above ends**: at the return pc the header of the
frame above holds in `M`, its cursor that frame's end, no call made there before the buffers
(`NcTop`); and each frame `TailA`. -/
def ChainA (L : Lay) (A : String → FnAl) (M : ℕ → E) : List Ent → Prop
  | [] => True
  | [e] => TailA e
  | e :: e' :: st => TailA e ∧ (∃ r, M (e.I.fp + 0) = ofK (addressOfIndex r) ∧ r < 2 ^ 63 ∧
      e.I.endCurA L.fs coreProgram.loop L.al = cursorAt L A e' (r - entOf A e'.I.t.name) ∧
      NcTop A e' (r - entOf A e'.I.t.name)) ∧ ChainA L A M (e' :: st)

/-- **The bump pointer's track**: in the prologue the next free cell is past `main`'s frame; past
it, a state of the tree track at the state's pc and frame whose top frame's cursor is the next free
cell, its frames chained. -/
def YAlloc (L : Lay) (D : Ref → RefD) (A : String → FnAl) (r : Ref) (s : St) : Prop :=
  (s.steps < proLen → s.nextFree = r.adv.mainFrame) ∧
    (proLen ≤ s.steps → s.steps < r.n → ∃ done e st, RefTrack L D A r s.pc s.fp (done, e :: st) ∧
      s.nextFree = cursorAt L A e (s.pc - entOf A e.I.t.name) ∧ ChainA L A (memOf r.img) (e :: st) ∧
      NcTop A e (s.pc - entOf A e.I.t.name))

/-- **`main`'s frame in the layout**: `main` is no loop helper, its frame the advice's
`mainFrame`. -/
structure MainA (L : Lay) : Prop where
  loop : coreProgram.loop "main" = false
  frame : L.fs "main" = Data.adviceMainFrame

end

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **The bump pointer's track holds initially.** -/
theorem initY_alloc {r : Ref} {C : Ctx} {m : Mem} : YAlloc L D A r (initSt C r.adv m) := by
  refine ⟨fun _ ↦ rfl, fun h ↦ ?_⟩
  exact absurd h (by show ¬ proLen ≤ 0; have := proLen_pos; omega)

/-- **The root's block is `main`'s frame.** -/
theorem block_mainA (hM : MainA L) {r : Ref} (hR : RefH L (D r) r) :
    (D r).T.block L.fs coreProgram.loop = r.adv.mainFrame := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  have hv := hH.valid
  have hn := hR.name
  rcases hT : (D r).T with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
  · rw [hT] at hn
    simp only [Tree.name] at hn
    subst hn
    rw [block_node, nodeBlock, hM.loop, hM.frame]
    rfl
  · rw [hT] at hv; exact hv.elim

/-- **The track at `main`'s entry, its cursor past `main`'s frame**: `main`'s frame at its body, at
frame `0`, nothing done, no call made, its offset `0`. -/
theorem refTrack_mainA (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen)
    (hM : MainA L) {r : Ref} (hR : RefH L (D r) r) :
    ∃ e, RefTrack L D A r proLen 0 ([], [e]) ∧ cursorAt L A e (proLen - entOf A e.I.t.name) = r.adv.mainFrame ∧
      ChainA L A (memOf r.img) [e] ∧ NcTop A e (proLen - entOf A e.I.t.name) := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  obtain ⟨I, rest, he, hIt, hfp, hcur, -⟩ := head_instsA (fs := L.fs) (lp := coreProgram.loop) (al := L.al)
    (H := L.H) (D r).T (0, (D r).T.block L.fs coreProgram.loop) r.hdr
  have hI : I ∈ instsOf L (D r) r := by
    show I ∈ (D r).T.instsA L.fs coreProgram.loop L.al L.H (0, (D r).T.block L.fs coreProgram.loop) r.hdr
    rw [he]; exact List.mem_cons_self
  have hv := hH.valid
  rw [← hIt] at hv
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? I.t.name = some fn := by
    rcases hIt' : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hIt'] at hv
      obtain ⟨fn, hf, -⟩ := hv
      exact ⟨fn, hf⟩
    · rw [hIt'] at hv; exact hv.elim
  have htr := trackOk_init (rd := (D r).rd0) hI hf hv
  rw [hIt] at htr
  have hname : I.t.name = "main" := by rw [hIt]; exact hR.name
  have hal0 : alOf A "main" 0 = some fn.body := by
    rw [hname] at hf
    change alignAt (A "main").X (A "main").body (A "main").code (A "main").d 0 = some fn.body
    rw [alignAt_zero (hP.ok _ _ hf), hP.body _ _ hf]
  have h0 := refOk_init (M := memOf r.img) (ent := entOf A) (al := alOf A) htr hfp (by rw [hname]; exact hal0)
  rw [hname, hmain] at h0
  have hen : entOf A (Ent.enter coreProgram I fn).I.t.name = proLen := by
    show entOf A I.t.name = proLen
    rw [hname, hmain]
  refine ⟨_, h0, ?_, fun _ hl hk ↦ absurd (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)) hk,
    fun _ ↦ rfl⟩
  rw [hen, Nat.sub_self, cursorAt]
  show (bif pendAt (A I.t.name).X (A I.t.name).code (A I.t.name).d 0 then _ else
    I.curA L.fs coreProgram.loop L.al (nbAt (A I.t.name).X (A I.t.name).d 0) (calls ([] : List Ev)).length) = _
  rw [pendAt_zero, Bool.cond_false, Inst.curA, hcur, ← block_mainA hM hR]
  simp [calls, curF_nil, nbAt_zero]

end

end LeanVM.Guest.EndExec
