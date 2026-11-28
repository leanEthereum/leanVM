/-
  LeanVM.Guest.EndExecACur

  The cursor follows each step of the tree track, aligned: `CurArith` from the step rule's offsets
  (`Bridge.stepRule_off`) and the bump pointer check's facts (`Bridge.CurFactsX`).
-/

module

public import LeanVM.Guest.EndExecAKeep
public import LeanVM.Guest.Bridge.StepOff
public import LeanVM.Guest.Bridge.AllocCur

/-!
# The cursor along the run, aligned

The bus era's `EndExecACur.lean` on Hotwire's aligned allocator. `curForm L e nb p`: frame `e`'s
cursor past `nb` buffers and its calls made, bumped by the next callee's reservation when `p`
(`cursorAt` is it at the offset's `nbAt` and `pendAt`). At an offset whose hints are in their order
(`ordHints`: buffers, then at most one frame hint, none once a frame is pending), the hints' steps
bump the cursor to the cursor past the offset's buffers, a frame pending when one was or is reserved
(`cursor_stepA`, from `Memory.bump_stepsOf`; a buffer at the offset means no call made, `NcTop`).

`curArith_of : CurHyps L D A → … → CurArith L D A`. A step from a state of the tree track is one of
`StepOff`'s kinds:

* within the frame (`fall`, `fwd`, `skip`): the buffer hints counted past the offset, a frame hint
  pending past it, or consumed by a call not taken (a phantom's region is its block, `endA` of a
  phantom the cursor);
* a call (`push`): the callee at the aligned base of the cursor past every buffer and the earlier
  callees, its block the reservation the pending frame hint made (`Memory.kid_posA`), its subtree
  ending where the caller resumes at the site's return pc (`Memory.endCurA_kid`);
* a loop's tail call (`tail`): the next iteration at the cursor past everything (`Memory.tail_posA`),
  ending where the iteration does (`Memory.endCurA_tail`);
* a return (`ret`): the frame ends at its cursor past everything (`Memory.endCurA_ret`, a loop's last
  callee a phantom by `TailA`), where the frame below resumes (`ChainA`).

`CurHyps L D A`, the guest's facts it reads: each function's `CurFactsX` (the generated check's), a
jump through a next frame a loop helper's, a loop helper's call through a call site not its last
(`jcData`'s `loopChk`), and an honest instance's buffers at most its function's buffer hints.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Guest.Check (getF)
open LeanVM.Prover.Exec

@[expose] public section

/-- **Frame `e`'s cursor past `nb` buffers and its calls made**, bumped by the next callee's
reservation when `p`. -/
noncomputable def curForm (L : Lay) (e : Ent) (nb : ℕ) (p : Bool) : ℕ :=
  bif p then (((e.I.t.kidsC coreProgram.loop)[e.nc]?).map fun k ↦
      allocBase (L.al k.name) (e.I.curA L.fs coreProgram.loop L.al nb e.nc) + k.block L.fs coreProgram.loop).getD
      (e.I.curA L.fs coreProgram.loop L.al nb e.nc)
  else e.I.curA L.fs coreProgram.loop L.al nb e.nc

/-- **The guest's facts the cursor's arithmetic reads**: each function's bump pointer check, a jump
through a next frame a loop helper's, a loop helper's call through a call site not its last, and an
honest instance's buffers at most its function's buffer hints. -/
structure CurHyps (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop where
  facts : ∀ f fn, coreProgram.find? f = some fn → CurFactsX (A f).X (A f).body (A f).code (A f).d
  loopNext : ∀ f fn, coreProgram.find? f = some fn → ∀ off oc od of : ℕ, (A f).code[off]? = some (OffsetInstruction.jump oc od of) →
    (A f).X.nextAt of = true → coreProgram.loop f = true
  notLast : ∀ f fn, coreProgram.find? f = some fn → coreProgram.loop f = true → ∀ σ es vs,
    walk σ fn.body = .ret es vs → ∀ i c, (calls es)[i]? = some c → ∀ q s,
      (A f).X.siteAt q c.args c.rets = some s → i + 1 < (calls es).length
  bufsLe : ∀ r, RefH L (D r) r → r.Ok → ∀ I ∈ instsOf L (D r) r,
    I.t.bufs.length ≤ (bufsOf (A I.t.name).X (A I.t.name).d).length

end

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-! ## The cursor form -/

theorem cursorAt_eq (e : Ent) (off : ℕ) :
    cursorAt L A e off = curForm L e (nbAt (A e.I.t.name).X (A e.I.t.name).d off)
      (pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off) := rfl

theorem curForm_congr {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc) : curForm L e' = curForm L e := by
  funext nb p; unfold curForm; rw [hI, hnc]

theorem cursorAt_congr {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc) : cursorAt L A e' = cursorAt L A e := by
  funext off; rw [cursorAt_eq, cursorAt_eq, curForm_congr hI hnc, hI]

theorem curForm_false (e : Ent) (nb : ℕ) : curForm L e nb false = e.I.curA L.fs coreProgram.loop L.al nb e.nc := rfl

theorem curForm_true {e : Ent} {nb : ℕ} {k : Tree} (hk : (e.I.t.kidsC coreProgram.loop)[e.nc]? = some k) :
    curForm L e nb true =
      allocBase (L.al k.name) (e.I.curA L.fs coreProgram.loop L.al nb e.nc) + k.block L.fs coreProgram.loop := by
  unfold curForm; rw [hk]; rfl

theorem take_succ_sum (l : List ℕ) (n : ℕ) : (l.take (n + 1)).sum = (l.take n).sum + l.getD n 0 := by
  rw [List.take_add_one, List.sum_append, List.getD_eq_getElem?_getD]
  cases l[n]? <;> simp

theorem take_sum_of_le {l : List ℕ} {n : ℕ} (h : l.length ≤ n) : (l.take n).sum = l.sum := by
  rw [List.take_of_length_le h]

theorem any_eq_decide {α : Type} (l : List α) (p : α → Bool) : l.any p = decide (0 < l.countP p) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, List.countP_pos_iff]

theorem isBuf_notFrame {X : AlignCtx} {h : Hint} (hb : isBuf X h = true) : isFrame X h = false := by
  unfold isBuf at hb; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb; exact hb.2

theorem isFrame_notBuf {X : AlignCtx} {h : Hint} (hf : isFrame X h = true) : isBuf X h = false := by
  unfold isBuf; simp [hf]

theorem bif_add {p p' : Bool} {c : ℕ} (h : (bif p' then 1 else 0) = (bif p then 1 else 0) + c) :
    p' = (p || decide (0 < c)) := by
  cases p <;> cases p' <;> simp at h ⊢ <;> omega

/-- The hints at an offset, when there are some, are an entry of the advice there. -/
theorem lookup_mem {l : List (ℕ × List Hint)} {a : ℕ} {hs : List Hint} (h : l.lookup a = some hs) :
    (a, hs) ∈ l := by
  induction l with
  | nil => cases h
  | cons p l ih =>
    rw [List.lookup_cons] at h
    split at h
    · rename_i he
      obtain rfl := Option.some.inj h
      have : a = p.1 := by simpa using he
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- **The hints at an offset in their order**, from the check. -/
theorem ord_at {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hF : CurFactsX X body code d) (off : ℕ) :
    ordHints (isBuf X) (isFrame X) (pendIn code (frames X d) off) ((d.2.2.lookup (X.entry + off)).getD []) = true := by
  cases hl : d.2.2.lookup (X.entry + off) with
  | none => rfl
  | some hs =>
    have := hF.ord _ (lookup_mem hl)
    simpa [Nat.add_sub_cancel_left] using this

/-- **The hints at an offset bump the cursor** to the cursor past their buffers, a frame pending when
one was or is reserved. -/
theorem cursor_stepA {e : Ent} {off : ℕ} (hU : HintsUp (A e.I.t.name).d (A e.I.t.name).X.entry)
    (hF : CurFactsX (A e.I.t.name).X (A e.I.t.name).body (A e.I.t.name).code (A e.I.t.name).d)
    (hnc : NcTop A e off) :
    bumpL (cursorAt L A e off) (treeSteps L A e off) =
      curForm L e (nbAt (A e.I.t.name).X (A e.I.t.name).d off +
          (hintsAtOff (A e.I.t.name) off).countP (isBuf (A e.I.t.name).X))
        (pendAt (A e.I.t.name).X (A e.I.t.name).code (A e.I.t.name).d off ||
          (hintsAtOff (A e.I.t.name) off).any (isFrame (A e.I.t.name).X)) := by
  rw [cursorAt_eq, treeSteps]
  refine bump_stepsOf (cf := curForm L e) (fun n ↦ ?_) (fun _ ↦ isBuf_notFrame) _ _ _ (ord_at hF off) fun hc n ↦ ?_
  · cases hk : (e.I.t.kidsC coreProgram.loop)[e.nc]? with
    | none =>
      unfold curForm
      rw [hk]
      exact bump_zero _
    | some k => rw [curForm_true hk, curForm_false]; rfl
  · have hq : 0 < (bufsOf (A e.I.t.name).X (A e.I.t.name).d).countP (fun q ↦ decide (q.1 = off)) := by
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

/-! ## The check's facts -/

theorem frameOk_spec {X : AlignCtx} {code : List OffsetInstruction} {a : ℕ} {h : Prover.Exec.Hint}
    (hf : frameOk X code a h = true) :
    ∃ oc od q, code[nextJump code a]? = some (.jump oc od q) ∧ allocPtr h = some q ∧ X.zeroAt oc = false ∧
      X.selfAt q = false ∧ X.nextAt q = false ∧ ¬(od = 0 ∧ q = 1) := by
  unfold frameOk at hf
  rw [Bool.and_eq_true] at hf
  obtain ⟨-, h2⟩ := hf
  split at h2
  · rename_i oc od q p hc hp
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.beq_eq] at h2
    obtain ⟨⟨⟨⟨rfl, h3⟩, h4⟩, h5⟩, h6⟩ := h2
    refine ⟨oc, od, q, hc, hp, h3, h4, h5, fun ⟨h0, h1⟩ ↦ ?_⟩
    subst h0 h1
    simp at h6
  · cases h2

/-- **A jump through the own frame, on a constant `0`, through a next frame or a return** is no frame
hint's. -/
theorem noFrame_of {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hF : CurFactsX X body code d) {off oc od of : ℕ}
    (hi : code[off]? = some (.jump oc od of))
    (hk : X.zeroAt oc = true ∨ X.selfAt of = true ∨ X.nextAt of = true ∨ (od = 0 ∧ of = 1)) :
    ∀ q ∈ frames X d, nextJump code q.1 ≠ off := fun q hq he ↦ by
  obtain ⟨oc', od', q', hc, -, h1, h2, h3, h4⟩ := frameOk_spec (hF.frame q hq)
  rw [he, hi] at hc
  cases hc
  rcases hk with h | h | h | h
  · rw [h] at h1; cases h1
  · rw [h] at h2; cases h2
  · rw [h] at h3; cases h3
  · exact h4 h

theorem frJump_of {X : AlignCtx} {body : List Stmt} {code : List OffsetInstruction}
    {d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)} (hF : CurFactsX X body code d) : FrJump code (frames X d) :=
  fun q hq ↦ let ⟨_, _, _, hc, _⟩ := frameOk_spec (hF.frame q hq); ⟨_, hc⟩

theorem nextAt_selfAt {X : AlignCtx} {o : ℕ} (h : X.nextAt o = true) : X.selfAt o = false := by
  unfold AlignCtx.nextAt at h
  unfold AlignCtx.selfAt
  split at h
  · rename_i S hS
    rw [hS]
    cases S with
    | zero => simp at h
    | succ S => rfl
  · cases h
  · rename_i hn
    rw [hn]

theorem siteAt_some {X : AlignCtx} {q : ℕ} {args rets : List V} {s : B2C.Site} (h : X.siteAt q args rets = some s) :
    (getF X.sites q).isSome = true := by
  unfold AlignCtx.siteAt at h
  split at h
  · rename_i s' hs'; rw [hs']; rfl
  · cases h

/-- **A jump through a call site's frame cell or a next frame is past every buffer hint.** -/
theorem bufs_le_of_call {X : AlignCtx} {bs : List (ℕ × Prover.Exec.Hint)} {i oc od of : ℕ}
    (h : (∀ q ∈ bs, q.1 ≤ i) ∨ bufJumpOk X bs i oc od of = true)
    (hc : X.nextAt of = true ∨ (getF X.sites of).isSome = true) : ∀ q ∈ bs, q.1 ≤ i := by
  rcases h with h | h
  · exact h
  · unfold bufJumpOk at h
    rcases hc with hc | hc
    · simp [hc, nextAt_selfAt hc] at h
    · rw [Option.isSome_iff_ne_none] at hc
      cases hs : getF X.sites of with
      | none => exact absurd hs hc
      | some _ => simp [hs] at h

/-- A frame's function's advice by increasing pcs from its entry. -/
theorem hintsUp_of (hP : ProgAl guestProgram coreProgram A) {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) : HintsUp (A f).d (A f).X.entry := by
  have hok := hP.ok _ _ hf
  rw [alignOk, AlignCtx.seq_eq] at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.ble_eq] at hok
  exact ⟨hok.1.1.1.2, hok.1.1.2, hok.1.2⟩

/-! ## The chain by frame -/

theorem tailA_congr {e e' : Ent} (hI : e'.I = e.I) (hnc : e'.nc = e.nc) (h : TailA e) : TailA e' := by
  unfold TailA at *; rw [hI, hnc]; exact h

/-- The chain with a new top frame of the same instance, `TailA`. -/
theorem chainA_top {M : ℕ → E} {e e' : Ent} {st : List Ent} (hI : e'.I = e.I)
    (ht : TailA e') (h : ChainA L A M (e :: st)) : ChainA L A M (e' :: st) := by
  cases st with
  | nil => exact ht
  | cons e2 st2 => exact ⟨ht, hI ▸ h.2.1, h.2.2⟩

theorem chainA_tail {M : ℕ → E} {e : Ent} {st : List Ent} (h : ChainA L A M (e :: st)) : TailA e := by
  cases st with
  | nil => exact h
  | cons _ _ => exact h.1

theorem tailA_enter {P : Core.Program} (J : Inst) (fn : Fn) : TailA (Ent.enter P J fn) :=
  fun _ hl hk ↦ absurd (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)) hk

/-- **A callee's cursor at its entry** is its instance's. -/
theorem cursorAt_enter {P : Core.Program} (J : Inst) (fn : Fn) :
    cursorAt L A (Ent.enter P J fn) 0 = J.cur := by
  rw [cursorAt_eq, pendAt_zero, nbAt_zero, curForm_false, Inst.curA]
  simp [Ent.enter, Ent.nc, calls, curF_nil]

/-- `NcTop` past a step within the frame, the same calls made, forward. -/
theorem ncTop_same {e e' : Ent} {off off' : ℕ} (hI : e'.I = e.I) (hnc : e'.nc = e.nc)
    (h : NcTop A e off) (hle : off ≤ off') : NcTop A e' off' := fun ⟨q, hq, hq'⟩ ↦ by
  rw [hnc]; exact h ⟨q, by rw [← hI]; exact hq, by omega⟩

/-- `NcTop` past every buffer hint. -/
theorem ncTop_past {e : Ent} {off : ℕ}
    (h : ∀ q ∈ bufsOf (A e.I.t.name).X (A e.I.t.name).d, q.1 < off) : NcTop A e off :=
  fun ⟨q, hq, hq'⟩ ↦ absurd (h q hq) (by omega)

theorem ncTop_enter {P : Core.Program} (J : Inst) (fn : Fn) (off : ℕ) :
    NcTop A (Ent.enter P J fn) off := fun _ ↦ rfl

/-! ## The honest instances -/

/-- **Two instances at one frame are one**, among instances pairwise apart, frames nonempty. -/
theorem inst_eq_of_fp {fs : String → ℕ} {Is : List Inst} (hp : Is.Pairwise (Inst.Apart fs)) {I J : Inst}
    (hI : I ∈ Is) (hJ : J ∈ Is) (hfp : I.fp = J.fp) (h1 : 0 < I.t.fsz fs) (h2 : 0 < J.t.fsz fs) : I = J := by
  by_contra hne
  have hA : Inst.Apart fs I J := List.Pairwise.forall hp hI hJ hne
  exact hA I.fp (Or.inl ⟨le_rfl, by omega⟩) (Or.inl ⟨by omega, by omega⟩)

/-- **A callee instance at its position** in the caller's `kidPosA`. -/
theorem kid_placeA {r : Ref} (hR : RefH L (D r) r) {I J : Inst} (hI : I ∈ instsOf L (D r) r)
    (hJ : J ∈ instsOf L (D r) r) {i : ℕ} (hk : I.t.kids[i]? = some J.t) (hkf : I.kidFps[i]? = some J.fp) :
    (kidPosA L.fs coreProgram.loop L.al (I.fp, I.cur) I.t.name I.t.bufs I.t.kids)[i]? = some (J.fp, J.cur) := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  have hI' : I ∈ (D r).T.instsA L.fs coreProgram.loop L.al L.H (0, (D r).T.block L.fs coreProgram.loop) r.hdr := hI
  have hJ' : J ∈ (D r).T.instsA L.fs coreProgram.loop L.al L.H (0, (D r).T.block L.fs coreProgram.loop) r.hdr := hJ
  obtain ⟨J', hJ'm, -, hpos⟩ := instsA_kid_pos (D r).T _ r.hdr I hI' i J.t hk
  have hIP := instsA_placed (D r).T (0, (D r).T.block L.fs coreProgram.loop) r.hdr (by simp) I hI'
  have hfp : J'.fp = J.fp := by
    rw [hIP.1, List.getElem?_map, hpos] at hkf
    exact Option.some.inj hkf
  have hpw := instsA_pairwise (fs := L.fs) (lp := coreProgram.loop) (al := L.al) (H := L.H) (D r).T
    (0, (D r).T.block L.fs coreProgram.loop) r.hdr (by simp)
  have hJJ : J' = J := inst_eq_of_fp hpw hJ'm hJ' hfp (by have := hH.cells.two_le J' hJ'm; omega)
    (by have := hH.cells.two_le J hJ; omega)
  rw [hpos, hJJ]

theorem kidsValid_len' {P : Core.Program} {rd : Reader} {σ : Val} :
    ∀ {cs : List Call} {ks : List Tree}, Tree.KidsValid P rd σ cs ks → cs.length = ks.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, kidsValid_len' h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem kidsC_length' (t : Tree) :
    (t.kidsC coreProgram.loop).length = if coreProgram.loop t.name then t.kids.length - 1 else t.kids.length := by
  unfold Tree.kidsC; split <;> simp

theorem kidsC_getElem?_of {t : Tree} {nc : ℕ} (h : nc < (t.kidsC coreProgram.loop).length) :
    (t.kidsC coreProgram.loop)[nc]? = t.kids[nc]? := by
  obtain ⟨k, hk⟩ : ∃ k, (t.kidsC coreProgram.loop)[nc]? = some k := ⟨_, List.getElem?_eq_getElem h⟩
  rw [hk, kidsC_getElem? hk]

theorem curA_take_le {I : Inst} {nb nc : ℕ} (h : (I.t.kidsC coreProgram.loop).length ≤ nc) :
    I.curA L.fs coreProgram.loop L.al nb nc =
      I.curA L.fs coreProgram.loop L.al nb (I.t.kidsC coreProgram.loop).length := by
  unfold Inst.curA; rw [List.take_of_length_le h, List.take_length]

theorem curA_bufs_le {I : Inst} {nb nc : ℕ} (h : I.t.bufs.length ≤ nb) :
    I.curA L.fs coreProgram.loop L.al nb nc = I.curA L.fs coreProgram.loop L.al I.t.bufs.length nc := by
  unfold Inst.curA; rw [List.take_of_length_le h, List.take_length]

end

end LeanVM.Guest.EndExec
