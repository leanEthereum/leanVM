/-
  LeanVM.Guest.EndExecAAddr

  `AddrReady` from the address hints' check (`Bridge.addrFnChk`) and what the reference holds at a
  frame's fixed cells and past a loop helper's frame.
-/

module

public import LeanVM.Guest.EndExecAReady
public import LeanVM.Guest.Bridge.AddrChk

/-!
# The address hints

An address hint of a frame of the honest tree, at its function's offset (`hints_off`), passes its
function's `addrOkX`: a `cellAddress q o` names a fixed cell `q` (`statOf q = .fpg o`) and the cell
`o`, both below the frame size, so within the frame, which ends within `2^κ ≤ 2^28` words
(`honestA_within_node`); a `frameAddress o` is in a loop helper, `o` its frame size. What the
reference holds beyond the check is `AddrFacts`: the fixed cells' words (the bus era's
`FrameHolds.stat`) and, in a loop helper, the next frame's base below `maxCells` (the bus era's
`tail_pos`, the next iteration's frame or phantom following the frame).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B2C

public section

/-- **A loop helper calls**: its final conditional call is on every path, taken or not. -/
theorem loop_calls_ne {fn : Fn} {cc : V} {g : String} {args : List V} {rpre : List Stmt}
    (hrev : fn.body.reverse = .ret [] :: .callIf cc g args :: rpre) (hnr : noRetB rpre.reverse = true) {σ : Val}
    {es : List Ev} {vs : List V} (hw : walk σ fn.body = .ret es vs) : calls es ≠ [] := by
  have hbody : fn.body = rpre.reverse ++ [.callIf cc g args, .ret []] := by
    rw [← List.reverse_reverse fn.body, hrev]; simp
  rw [hbody, walk_append] at hw
  rcases walk_noRet (σ := σ) _ (noRetB_spec _ hnr) with ⟨es1, he1⟩ | he1
  · rw [he1] at hw
    have hw2 : walk σ [Stmt.callIf cc g args, Stmt.ret []] =
        .ret [.inK cc, if σ cc = 0 then .skip g args else .call g args []] [] := by
      rw [walk_callIf_cons, walk_ret_cons]; rfl
    rw [hw2] at hw
    simp only [Out.seq, Out.pre] at hw
    obtain ⟨rfl, -⟩ := Out.ret.inj hw
    have hcalls : calls (es1 ++ [Ev.inK cc, if σ cc = 0 then Ev.skip g args else Ev.call g args []]) =
        calls es1 ++ [⟨g, args, [], !decide (σ cc = 0)⟩] := by
      rw [calls_append']
      congr 1
      by_cases h0 : σ cc = 0
      · simp only [calls, h0, ↓reduceIte, decide_true, Bool.not_true]; rfl
      · simp only [calls, h0, ↓reduceIte, decide_false, Bool.not_false]; rfl
    rw [hcalls]
    simp
  · rw [he1] at hw; cases hw

/-- A loop helper passing `loopChkX` calls on every path. -/
theorem loopX_calls_ne {fn : Fn} {X : AlignCtx} (h : loopChkX fn X = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) : calls es ≠ [] := by
  unfold loopChkX at h
  split at h
  case h_2 => cases h
  rename_i cc g args rpre hrev
  rw [Bool.and_eq_true] at h
  exact loop_calls_ne hrev h.1 hw

end

end LeanVM.Guest.Bridge

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **What the address hints read of the reference**, at every frame of the tree track: each fixed
cell `q` holding the frame's cell `o` (`fpg o`), below the frame size, the address of that cell; in
a loop helper, the frame's end below `maxCells` (`addrFacts_of` proves it from the allocation
check). -/
structure AddrFacts (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop where
  stat : ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) →
    ∀ q o, (A e.I.t.name).X.statOf q = some (.fpg o) → q < L.fs e.I.t.name →
      refMem r.img (e.I.fp + q) = ofK (g ^ (e.I.fp + o))
  tail : ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) →
    coreProgram.loop e.I.t.name = true → e.I.fp + L.fs e.I.t.name < maxCells

theorem mem_of_lookup' {β : Type} : ∀ {l : List (ℕ × β)} {k : ℕ} {v : β}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp at h
  | (a, b) :: l, k, v, h => by
    by_cases hk : k = a
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hne : (k == a) = false := by simpa using hk
      simp only [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup' h)

/-- **Every address hint has what it needs**, from the address hints' check and `AddrFacts`. -/
theorem addrReady_of (hH : HintHyps L D A) (hfs : L.fs = B2C.fs)
    (hchk : ∀ f fn, coreProgram.find? f = some fn → addrFnChk (A f).X (B2C.fs f) fn (A f).d = true)
    (hF : AddrFacts L D A) : AddrReady L D A := by
  intro r C e s sx i h hat haddr _
  obtain ⟨done, st, htr, -⟩ := hat.track
  have hne : (C.hints[s.pc]?).getD [] ≠ [] := fun h0 ↦ by have := hat.get; rw [h0] at this; simp at this
  have hoff := hints_off hH.progAl hH.advAl hat.ctx htr hne
  have hi := hat.get
  rw [hoff] at hi
  have hE := htr.track.ents e List.mem_cons_self
  -- the hint passes its function's `addrOkX`
  have hok : addrOkX (A e.I.t.name).X (B2C.fs e.I.t.name) e.fn.loop h = true := by
    unfold hintsAtOff at hi
    cases hlk : (A e.I.t.name).d.2.2.lookup ((A e.I.t.name).X.entry + (s.pc - entOf A e.I.t.name)) with
    | none => rw [hlk] at hi; simp at hi
    | some l =>
      rw [hlk, Option.getD_some] at hi
      have hp := mem_of_lookup' hlk
      exact List.all_eq_true.mp (List.all_eq_true.mp (hchk _ _ hE.find) _ hp) _ (List.mem_of_getElem? hi)
  -- the frame, within `2^28` words
  have hfp : sx.fp = e.I.fp := by rw [hat.fp]; exact htr.linked.top.1.symm
  obtain ⟨rd, hHon, -⟩ := hat.ref.honest
  have h2 := hHon.cells.two_le e.I hE.mem
  obtain ⟨f', bufs, kids, hnode⟩ := hE.node
  have hw := honestA_within_node hE.mem hnode (by omega)
  have hle := le_two_pow_logMem ((D r).T.wordsA L.fs coreProgram.loop L.al)
  have h28 : 2 ^ logMem ((D r).T.wordsA L.fs coreProgram.loop L.al) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) (hat.ref.log hat.ok)
  rcases haddr with ⟨o, rfl⟩ | ⟨q, o, rfl⟩
  · simp only [addrOkX, Bool.and_eq_true, Nat.beq_eq] at hok
    obtain ⟨rfl, hloop⟩ := hok
    have hlp : coreProgram.loop e.I.t.name = true := by rw [Program.loop_of_find? hE.find]; exact hloop
    have := hF.tail r hat.ref hat.ok s.pc s.fp done e st htr hlp
    show sx.fp + B2C.fs e.I.t.name < maxCells
    rw [hfp, ← hfs]; exact this
  · simp only [addrOkX, Bool.and_eq_true, Nat.blt_eq] at hok
    obtain ⟨⟨hst, ho⟩, hq⟩ := hok
    split at hst
    · rename_i o' hso
      simp only [Nat.beq_eq] at hst
      subst hst
      rw [← hfs] at ho hq
      have hv := hF.stat r hat.ref hat.ok s.pc s.fp done e st htr q o' hso hq
      refine ⟨?_, ?_, ?_⟩
      · rw [hfp]; unfold maxCells; omega
      · rw [hfp]; unfold maxCells; omega
      · rw [hfp]; exact hv
    · cases hst

/-- **A loop helper's frame ends below `maxCells`**: its last callee, the next iteration's frame or
the phantom, is an honest instance at `fp + fs f` (`tail_posA`), the calls nonempty by `loopChkX`. -/
theorem addrTail_of
    (hchk : ∀ f fn, coreProgram.find? f = some fn → allocFnChk (A f).X fn (A f).code (A f).d = true) :
    ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) →
      coreProgram.loop e.I.t.name = true → e.I.fp + L.fs e.I.t.name < maxCells := by
  intro r hR hr pc fp done e st htr hlp
  have hE := htr.track.ents e List.mem_cons_self
  have hloop : e.fn.loop = true := by rw [← Program.loop_of_find? hE.find]; exact hlp
  have hc := hchk _ _ hE.find
  simp only [allocFnChk, Bool.and_eq_true, hloop, Bool.not_true, Bool.false_or] at hc
  obtain ⟨vs, hw, -⟩ := hE.path
  have hne := loopX_calls_ne hc.2 hw
  obtain ⟨rv, hkv⟩ := hE.kids
  have hlen := kidsValid_len' hkv
  have hk : e.I.t.kids ≠ [] := fun h0 ↦ hne (List.eq_nil_of_length_eq_zero (by rw [hlen, h0]; rfl))
  have hlast : e.I.t.kids[e.I.t.kids.length - 1]? = some (e.I.t.kids.getLast hk) := by
    rw [← List.getLast?_eq_getElem?, List.getLast?_eq_some_getLast hk]
  obtain ⟨J, hJ, -, hpos⟩ := instsA_kid_pos (fs := L.fs) (lp := coreProgram.loop) (al := L.al) (H := L.H)
    _ _ _ e.I hE.mem _ _ hlast
  rw [tail_posA hlp hk] at hpos
  have hJfp : J.fp = e.I.fp + L.fs e.I.t.name := (congrArg Prod.fst (Option.some.inj hpos)).symm
  have := inst_fp_lt hR hr hJ
  omega

/-- **`AddrFacts` from the allocation check and the fixed cells' words.** -/
theorem addrFacts_of
    (hchk : ∀ f fn, coreProgram.find? f = some fn → allocFnChk (A f).X fn (A f).code (A f).d = true)
    (hstat : ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) →
      ∀ q o, (A e.I.t.name).X.statOf q = some (.fpg o) → q < L.fs e.I.t.name →
        refMem r.img (e.I.fp + q) = ofK (g ^ (e.I.fp + o))) : AddrFacts L D A :=
  ⟨hstat, addrTail_of hchk⟩

end

end LeanVM.Guest.EndExec
