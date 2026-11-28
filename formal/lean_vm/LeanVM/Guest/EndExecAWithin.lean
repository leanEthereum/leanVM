/-
  LeanVM.Guest.EndExecAWithin

  The reservations within the reference's words: each frame's subtree ends within the tree, so an
  allocation hint's reservation at the frame's cursor ends within `2^κ` (`AllocB`).
-/

module

public import LeanVM.Guest.EndExecAReady

/-!
# The reservations within the tree

The bus era's `endCur_chain` (`EndExecAReady`) on the aligned cursor: the bottom frame of the tree
track is the root's, its subtree's end the tree's words (`Tree.wordsA`); each frame above ends
where the one below resumes, at most that one's end (`cursorAt_le_endCurA`). The words are at most
`2^κ` (`RefH.κ`). `allocB_of_bump`: an allocation hint whose step, its sizes read off the
reference, ends within `B` has its reservation within `B`.

So the facts by hint kind need not state `AllocB`: `BufHint` and `FrameHint` (a hint's step and
`HintOk`) give `BufReady` and `FrameReadyA` (`bufReady_of`, `frameReady_of`), and
`allocTrack_ofHint` leaves `MainA L`, `CurHyps`, `BufHint`, `FrameHint` and `AddrReady`.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Mode (HintIn)
open LeanVM.Prover.Exec

@[expose] public section

/-- **A buffer hint takes its buffer's cells and has what it needs at the cursor past the buffers
before it.** -/
def BufHint (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h, HintAtA L D A r C e s sx i h → isBuf (A e.I.t.name).X h = true →
    rszA (refMem r.img) sx h = (false, e.I.t.bufs.getD (bufIdxA A e (s.pc - entOf A e.I.t.name) i) 0) ∧
    (HintIn sx h → sx.nextFree = e.I.curA L.fs coreProgram.loop L.al (bufIdxA A e (s.pc - entOf A e.I.t.name) i) e.nc →
      HintOk C (refMem r.img) sx h)

/-- **A callee frame's hint takes the next callee's block, aligned as the layout allocates it, and
has what it needs at the cursor past the buffers before it and the calls made.** -/
def FrameHint (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r C e s sx i h, HintAtA L D A r C e s sx i h → isFrame (A e.I.t.name).X h = true →
    rszA (refMem r.img) sx h = frameStep L e ∧
    (HintIn sx h → sx.nextFree = e.I.curA L.fs coreProgram.loop L.al (bufIdxA A e (s.pc - entOf A e.I.t.name) i) e.nc →
      HintOk C (refMem r.img) sx h)

end

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-! ## The frames' ends -/

/-- **The cursor stays within the frame's subtree.** -/
theorem cursorAt_le_endCurA {e : Ent} (hn : ∃ f σ bufs kids, e.I.t = .node f σ bufs kids) (off : ℕ) :
    cursorAt L A e off ≤ e.I.endCurA L.fs coreProgram.loop L.al := by
  rw [cursorAt_eq]
  cases pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off
  · rw [curForm_false]; exact curA_le_endCurA hn _ _
  · cases hk : (e.I.t.kidsC coreProgram.loop)[e.nc]? with
    | none =>
      unfold curForm
      rw [hk]
      exact curA_le_endCurA hn _ _
    | some k => rw [curForm_true hk]; exact curA_block_le hn hk

/-- **Each frame's subtree ends within the tree**: the bottom frame is the root's, at frame `0`, its
subtree the tree; each frame above ends where the one below resumes. -/
theorem endCurA_chain {r : Ref} (hR : RefH L (D r) r) :
    ∀ (st : List Ent) (e : Ent) (pc fp : ℕ),
      (∀ x ∈ e :: st, EntOk coreProgram (instsOf L (D r) r) x) →
      Linked (memOf r.img) (entOf A) (alOf A) pc fp (e :: st) → ChainA L A (memOf r.img) (e :: st) →
      e.I.endCurA L.fs coreProgram.loop L.al ≤ (D r).T.wordsA L.fs coreProgram.loop L.al
  | [], e, pc, fp, hE, hL, _ => by
    obtain ⟨rd, hH, -⟩ := hR.honest
    obtain ⟨hfp, h0, -⟩ := hL
    obtain ⟨I, rest, he, hIt, hIfp, hcur, -⟩ := head_instsA (fs := L.fs) (lp := coreProgram.loop) (al := L.al)
      (H := L.H) (D r).T (0, (D r).T.block L.fs coreProgram.loop) r.hdr
    have hI : I ∈ instsOf L (D r) r := by
      show I ∈ (D r).T.instsA L.fs coreProgram.loop L.al L.H (0, (D r).T.block L.fs coreProgram.loop) r.hdr
      rw [he]; exact List.mem_cons_self
    have heI := (hE e List.mem_cons_self).mem
    have hpw := instsA_pairwise (fs := L.fs) (lp := coreProgram.loop) (al := L.al) (H := L.H) (D r).T
      (0, (D r).T.block L.fs coreProgram.loop) r.hdr (by simp)
    have hEq : e.I = I := inst_eq_of_fp hpw heI hI (by rw [hfp, h0, hIfp])
      (by have := hH.cells.two_le e.I heI; omega) (by have := hH.cells.two_le I hI; omega)
    rw [hEq, Inst.endCurA, hIt, hcur]
    exact le_rfl
  | e' :: st, e, pc, fp, hE, hL, hC => by
    obtain ⟨-, -, r0, -, -, hL'⟩ := hL
    obtain ⟨-, ⟨r1, -, -, hend, -⟩, hrest⟩ := hC
    have ih := endCurA_chain hR st e' r0 e'.I.fp (fun x hx ↦ hE x (List.mem_cons_of_mem _ hx)) hL' hrest
    obtain ⟨f, bufs, kids, hn⟩ := (hE e' (List.mem_cons_of_mem _ List.mem_cons_self)).node
    have := cursorAt_le_endCurA (L := L) (A := A) (e := e') ⟨_, _, _, _, hn⟩ (r1 - entOf A e'.I.t.name)
    omega

/-- **A frame of the tree track ends within the reference's `2^κ`.** -/
theorem endCurA_le_pow {r : Ref} (hR : RefH L (D r) r) {pc fp : ℕ} {done : List Pop} {e : Ent} {st : List Ent}
    (htr : RefTrack L D A r pc fp (done, e :: st)) (hch : ChainA L A (memOf r.img) (e :: st)) :
    e.I.endCurA L.fs coreProgram.loop L.al ≤ 2 ^ r.κ := by
  have h := endCurA_chain hR st e pc fp htr.track.ents htr.linked hch
  have := le_two_pow_logMem ((D r).T.wordsA L.fs coreProgram.loop L.al)
  rw [hR.κ]
  omega

/-! ## The reservation within `B` -/

theorem logG_gpow {n : ℕ} (hn : n < maxCells) : logG (ofK (g ^ n)) = n :=
  logG_spec (by unfold maxCells at hn; omega)

/-- **An allocation hint whose step ends within `B` has its reservation within `B`**, its sizes read
off a memory whose written cells hold `M`'s words. -/
theorem allocB_of_bump {B : ℕ} {M : ℕ → E} {s : St} {h : Hint} (hag : ∀ c v, s.mem.get c = some v → M c = v)
    (hb : bump s.nextFree (rszA M s h) ≤ B) : AllocB B s h := by
  cases h with
  | alloc p n a => exact hb
  | allocDyn p c =>
    intro n hn
    obtain ⟨v, hv, rfl⟩ := get_of_ptrAt hn
    simp only [rszA, bump, allocBase_false, hag _ _ hv, logG_gpow hn.2] at hb
    exact hb
  | allocArm p sel sizes a =>
    intro k n hk hn
    obtain ⟨v, hv, rfl⟩ := get_of_ptrAt hk
    simp only [rszA, bump, hag _ _ hv, logG_gpow hk.2, List.getD_eq_getElem?_getD, hn, Option.getD_some] at hb
    exact hb
  | allocFrames p size stop si tail a =>
    intro v n hn hv hvn
    have hne : s.mem.peek (s.fp + stop) ≠ 0 := by
      intro h0
      rw [h0] at hv
      have : v = 0 := by simpa [limb_zero] using (congrArg (fun x : E ↦ x.limb 0) hv).symm
      subst this
      rw [zero_mul] at hvn
      exact pow_ne_zero n g_ne_zero hvn.symm
    have hM : M (s.fp + stop) = ofK v := by
      cases hg : s.mem.get (s.fp + stop) with
      | none => exact absurd (by rw [Mem.peek, hg]; rfl) hne
      | some w => rw [hag _ w hg, ← hv, Mem.peek, hg]; rfl
    have hl : (M (s.fp + stop)).limb 0 * si = g ^ n := by rw [hM]; simpa using hvn
    simp only [rszA, bump, hl, logG_gpow hn] at hb
    exact hb
  | _ => trivial

/-! ## The facts by hint kind, `AllocB` apart -/

/-- **`BufReady` from `BufHint`**: a buffer's step from the cursor past the buffers before it ends
at the cursor past it, within the frame's subtree. -/
theorem bufReady_of (hH : HintHyps L D A) (hB : BufHint L D A) : BufReady L D A := by
  intro r C e s sx i h hat hb
  obtain ⟨h1, h2⟩ := hB r C e s sx i h hat hb
  refine ⟨h1, fun hin hnf ↦ ⟨h2 hin hnf, allocB_of_bump hat.agree ?_⟩⟩
  obtain ⟨done, st, htr, hch⟩ := hat.track
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨f, bufs, kids, hn⟩ := hE.node
  have hU := hintsUp_of hH.progAl hE.find
  have hne : (C.hints[s.pc]?).getD [] ≠ [] := fun h0 ↦ by have := hat.get; rw [h0] at this; simp at this
  have hoff := hints_off hH.progAl hH.advAl hat.ctx htr hne
  have hget := hat.get
  rw [hoff] at hget
  have hc : 0 < (hintsAtOff (A e.I.t.name) (s.pc - entOf A e.I.t.name)).countP (isBuf (A e.I.t.name).X) :=
    List.countP_pos_iff.mpr ⟨h, List.mem_of_getElem? hget, hb⟩
  have hstep := bufStep (L := L) hU hat.nc hc (bufIdxA A e (s.pc - entOf A e.I.t.name) i)
  rw [curForm_false, curForm_false] at hstep
  rw [h1, hnf, hstep]
  exact (curA_le_endCurA ⟨_, _, _, _, hn⟩ _ _).trans (endCurA_le_pow hat.ref htr hch)

/-- **`FrameReadyA` from `FrameHint`**: the next callee's block, reserved at its aligned base, ends
within the frame's subtree. -/
theorem frameReady_of (hF : FrameHint L D A) : FrameReadyA L D A := by
  intro r C e s sx i h hat hf
  obtain ⟨h1, h2⟩ := hF r C e s sx i h hat hf
  refine ⟨h1, fun hin hnf ↦ ⟨h2 hin hnf, allocB_of_bump hat.agree ?_⟩⟩
  obtain ⟨done, st, htr, hch⟩ := hat.track
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨f, bufs, kids, hn⟩ := hE.node
  refine le_trans ?_ (endCurA_le_pow hat.ref htr hch)
  rw [h1, hnf, frameStep]
  cases hk : (e.I.t.kidsC coreProgram.loop)[e.nc]? with
  | none =>
    simp only [Option.map_none, Option.getD_none, bump_zero]
    exact curA_le_endCurA ⟨_, _, _, _, hn⟩ _ _
  | some k => exact curA_block_le ⟨_, _, _, _, hn⟩ hk

/-- **The allocation track's obligations** from the bridge's premises, `main`'s frame in the layout,
the guest's cursor facts and the facts by hint kind, `AllocB` proved. -/
theorem allocTrack_ofHint {R : Ref → Prop} {Km : Mode.Cert} {E0 : Mode.Env} (hH : HintHyps L D A)
    (hRH : ∀ r, R r → RefH L (D r) r) (hMain : MainOk Km E0) (hM : MainA L) (hC : CurHyps L D A)
    (hB : BufHint L D A) (hF : FrameHint L D A) (hAr : AddrReady L D A) : AllocTrack R (YAlloc L D A) :=
  allocTrack_ofReady hH hRH hMain hM hC (bufReady_of hH hB) (frameReady_of hF) hAr

end

end LeanVM.Guest.EndExec
