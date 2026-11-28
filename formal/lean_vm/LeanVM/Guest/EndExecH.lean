module

public import LeanVM.Guest.EndExecC
public import LeanVM.Guest.EndExecYWit
public import LeanVM.Guest.EndExecYKeep
import all Statement.Data.AdviceHints

/-!
# The hint bridge's fields of `ExecGaps`

The hint tracks' invariant `YH L D A Ya r s`: the cells the executor touched within the reference's
`2^κ` (`YU`), the witness streams' cursors (`YCur`), and the bump pointer's track `Ya`.
`ExecGaps.ofHints` assembles `ExecGaps` on the references of the honest tree (`RefH`), its fields
`hintWitness` (`hintWitness_cur`), `hintComputed` (`hintComputed_cur`), `initY`, `keepY` and `usedY`
proved here from the bridge's premises (`HintHyps`) and the allocation track's obligations
(`AllocTrack`), the rest (the core route's) passed through. `hintsUsed_cur`: the hints keep the cells
used within `2^κ`, each hint's frame cells within its frame (`CellsAl`), its buffer runs the
reference's hint words (`witness_core`, `hintComputed_core`), an allocation's reservation the
allocation track's (`AllocTrack.used`).

`AllocTrack L D A R Ya` is what is left of the hint bridge: the bump pointer's track `Ya` started and
kept, each allocation hint's `HintOk` (a reservation at `allocBase` of the bump pointer, aligned for
the frames holding `KECCAK` blocks, of the size the aligned layout `Tree.instsA` allocates there) and
its reservation within `2^κ`. The bus era proved its unaligned form (`EndExecA*`: the cursor along the
tree track, the frames' and buffers' sizes, the generated allocation checks).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Mode (HintIn adviceHints_incr ctx_hints)
open LeanVM.Guest.Bridge (FnAl ProgAl entOf alOf EntOk)
open LeanVM.Prover.Exec

@[expose] public section

/-- **The hint tracks' invariant**: the cells used, the witness streams' cursors and the bump
pointer's track `Ya`. -/
def YH (L : Lay) (D : Ref → RefD) (A : String → FnAl) (Ya : Ref → St → Prop) (r : Ref) (s : St) : Prop :=
  YU r s ∧ YCur L D A r s ∧ Ya r s

/-- **The bridge's premises**: the program's alignments (`main` past the prologue), the jumps'
cells on the tree track, the alignments at the compiled functions, the advice the alignments read,
the witness atoms' and computed hint atoms' cells on the reference, and each hint's frame cells
within its frame. -/
structure HintHyps (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop where
  progAl : ProgAl guestProgram coreProgram A
  mainAt : entOf A "main" = proLen
  jumpCells : JumpCellsAt L D A
  layout : AlLayout A
  advAl : AdvAl A
  witCells : WitCells L D A
  compRef : CompRef L D A
  cellsAl : CellsAl L A

/-- **The allocation track's obligations**, for the references `R` and the bump pointer's track
`Ya`, at any hint tracks `Y` implying it: `Ya` at the initial state and kept by each step, each
allocation hint's needs, and its reservation within the reference's `2^κ`. -/
structure AllocTrack (R : Ref → Prop) (Ya : Ref → St → Prop) : Prop where
  init : ∀ r, R r → r.Ok → ∀ C m, Ctx.of guestProgram r.adv = .ok C → initMem r.adv r.input = .ok m →
    Ya r (initSt C r.adv m)
  keep : ∀ Y : Ref → St → Prop, (∀ r s, Y r s → Ya r s) → ∀ r, R r → r.Ok → ∀ C,
    Ctx.of guestProgram r.adv = .ok C → ∀ s op s1 s', OnRun (XOf Y) r s → C.ops[s.pc]? = some op →
    ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 → Moves (refMem r.img) s s1 →
    OpModed (refMem r.img) s1 op → runOp C s1 op = .ok s' → Ya r { s' with steps := s'.steps + 1 }
  hint : ∀ Y : Ref → St → Prop, (∀ r s, Y r s → Ya r s) → ∀ r, R r → r.Ok → ∀ C,
    Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
    (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
    Moves (refMem r.img) s s1 → isAllocHint h = true → HintIn s1 h → HintOk C (refMem r.img) s1 h
  used : ∀ Y : Ref → St → Prop, (∀ r s, Y r s → Ya r s) → ∀ r, R r → r.Ok → ∀ C,
    Ctx.of guestProgram r.adv = .ok C → ∀ s, OnRun (XOf Y) r s → ∀ pre h post,
    (C.hints[s.pc]?).getD [] = pre ++ h :: post → ∀ s1, pre.foldlM (runHint C) s = .ok s1 →
    MovesW (refMem r.img) s s1 → isAllocHint h = true → HintIn s1 h → AllocB (2 ^ r.κ) s1 h

end

public section

theorem written_of_peek {s : St} {c : ℕ} (h : s.mem.peek c ≠ 0) : s.mem.written c = true := by
  unfold Mem.peek at h
  cases hg : s.mem.get c with
  | none => rw [hg] at h; exact absurd rfl h
  | some v => exact Mode.written_of_get hg

/-- **An allocation hint whose run succeeds found its inputs written.** -/
theorem allocHintIn {C : Ctx} {s s' : St} {h : Hint} (hs : s.Good) (ha : isAllocHint h = true)
    (e : runHint C s h = .ok s') : HintIn s h := by
  cases h with
  | allocDyn p c =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c', hc', sz, hsz, ⟨n, s1⟩, h1, -⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc'
    obtain ⟨-, h2, h3⟩ := logOr_sm hs h1
    obtain ⟨v, hv, -⟩ := get_of_ptrAt (ptrAt_of hsz h2 h3)
    exact Mode.written_of_get hv
  | allocArm p sel sizes a =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c', hc', x, hx, ⟨k, s1⟩, h1, -⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc'
    obtain ⟨-, h2, h3⟩ := logOr_sm hs h1
    obtain ⟨v, hv, -⟩ := get_of_ptrAt (ptrAt_of hx h2 h3)
    exact Mode.written_of_get hv
  | allocFrames p size stop si tail a =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c', hc', sp, hsp, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc'
    split_ifs at e with h0
    · simp [bind_ok] at e
    · refine written_of_peek fun hz ↦ h0 ?_
      obtain ⟨-, rfl⟩ := inK_ok hsp
      rw [hz, Parameters.limb_zero, zero_mul]
  | frameAddress | alloc | cellAddress => trivial
  | _ => simp [isAllocHint] at ha

theorem foldlM_split {C : Ctx} {l : List Hint} {s s1 : St} {i : ℕ} {h : Hint} (hi : l[i]? = some h)
    (e : l.foldlM (runHint C) s = .ok s1) :
    ∃ sx s2, (l.take i).foldlM (runHint C) s = .ok sx ∧ runHint C sx h = .ok s2 ∧
      (l.drop (i + 1)).foldlM (runHint C) s2 = .ok s1 := by
  have hlt := (List.getElem?_eq_some_iff.mp hi).1
  rw [← List.take_append_drop i l, List.foldlM_append, List.drop_eq_getElem_cons hlt,
    (List.getElem?_eq_some_iff.mp hi).2, bind_ok] at e
  obtain ⟨sx, hx, e⟩ := e
  rw [List.foldlM_cons, bind_ok] at e
  obtain ⟨s2, h2, e⟩ := e
  exact ⟨sx, s2, hx, h2, e⟩

theorem heapB_of_alloc {B : ℕ} {s : St} {h : Hint} (ha : isAllocHint h = true) : HeapB B s h := by
  cases h <;> simp_all [isAllocHint, HeapB]

theorem allocB_of_not {B : ℕ} {s : St} {h : Hint} (ha : isAllocHint h = false) : AllocB B s h := by
  cases h <;> simp_all [isAllocHint, AllocB]

section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl} {R : Ref → Prop} {Ya : Ref → St → Prop}

/-- **The hints keep the cells used within the reference's `2^κ`.** -/
theorem hintsUsed_cur (hH : HintHyps L D A) (hA : AllocTrack R Ya) (hRH : ∀ r, R r → RefH L (D r) r) :
    HintsUsed R (YH L D A Ya) := by
  intro r hR0 hr C hC s s1 hon e1 hm
  have hR := hRH r hR0
  have hu0 : s.mem.used ≤ 2 ^ r.κ := hon.1.2.1
  have hs0 : s.Good := ⟨hon.2.1.agree.wf, hon.2.1.dl⟩
  by_cases hne : (C.hints[s.pc]?).getD [] = []
  · rw [hne] at e1
    simp only [List.foldlM_nil, pure_ok] at e1
    subst e1
    exact hu0
  have hpc : s.pc < 2 ^ guestProgram.logSize := pc_lt_of_hints hC hne
  have hge : proLen ≤ s.steps := by
    by_contra hlt
    have hpc19 := hpc
    rw [guest_logSize] at hpc19
    have := ((posAt hR hon.1.1 (by omega) hon.2.1.fp).1 (by omega)).1
    exact hne (hints_pro hC rfl (by omega))
  obtain ⟨done, e, st, htr⟩ :=
    trackAt hH.progAl hH.mainAt hH.jumpCells hH.layout hR hr hon.1.1 hon.2.1 hon.2.2 hge hpc
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨hfpe, hat⟩ := htr.linked.top
  obtain ⟨off, hpce, hoff, -⟩ := pair_flow hH.progAl hE hat
  have hins : (A e.I.t.name).code[off]? = some ((A e.I.t.name).code[off]) := List.getElem?_eq_getElem hoff
  have hcells : ∀ h ∈ (C.hints[s.pc]?).getD [], Bridge.hintCellsOk (L.fs e.I.t.name) h = true := by
    intro h hmem
    rw [ctx_hints (adv := r.adv) hC adviceHints_incr hpc] at hmem
    refine hH.cellsAl _ _ hE.find s.pc h ?_
    rw [hpce, hH.advAl _ _ hE.find off _ hins, ← hpce]
    exact hmem
  have hwithin := frame_within hR hE
  refine hints_used _ s s1 hs0 e1 hu0 fun i h sx hi hx ↦ ?_
  obtain ⟨sx', s2, hx', h2', hrest⟩ := foldlM_split hi e1
  obtain rfl : sx = sx' := by rw [hx'] at hx; cases hx; rfl
  have hfx := hints_follows _ s sx hs0 hx
  have hf1 := hints_follows _ s2 s1 (runHint_follows hfx.good h2').good hrest
  have hmw : MovesW (refMem r.img) s sx :=
    ⟨hfx.fp, fun c v hv ↦ hm.fine.agree.get c v ((Mem.le_trans (runHint_follows hfx.good h2').le hf1.le).get _ _ hv)⟩
  have hmem : h ∈ (C.hints[s.pc]?).getD [] := List.mem_of_getElem? hi
  have hl : (C.hints[s.pc]?).getD [] = ((C.hints[s.pc]?).getD []).take i ++ h ::
      ((C.hints[s.pc]?).getD []).drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i ((C.hints[s.pc]?).getD [])]
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hi).1, (List.getElem?_eq_some_iff.mp hi).2]
  refine usedOk_of (fs := L.fs e.I.t.name) (hcells h hmem) (by rw [hfx.fp, ← hfpe]; exact hwithin) ?_ ?_
  · cases ha : isAllocHint h
    · cases hw : isWitnessHint h
      · exact (hintComputed_core hH.progAl hH.mainAt hH.jumpCells hH.layout hH.advAl hH.cellsAl hH.compRef
          hR hr hC hon hmem ha hw hmw).1
      · exact (witness_core hH.progAl hH.advAl hH.witCells (fun r s h ↦ h.2.1) hR hr hC hon hl hx hmw hw).1
    · exact heapB_of_alloc ha
  · cases ha : isAllocHint h
    · exact allocB_of_not ha
    · exact hA.used _ (fun r s h ↦ h.2.2) r hR0 hr C hC s hon _ h _ hl sx hx hmw ha
        (allocHintIn hfx.good ha h2')

/-- **`ExecGaps` from the hint bridge**: on references of the honest tree, with the hint tracks
`YH L D A Ya`, from the bridge's premises, the allocation track's obligations and the core route's
fields. -/
theorem ExecGaps.ofHints {Ks : List Mode.Cert} {Km : Mode.Cert} {E0 : Mode.Env} {Ct : Ref → Mode.Cts}
    {Q : Ref → Mode.Cert → ℕ → St → Prop} (hH : HintHyps L D A) (hA : AllocTrack R Ya)
    (hRH : ∀ r, R r → RefH L (D r) r) (certs : ModeCerts Ks Km E0) (main : MainOk Km E0)
    (frame : ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ K ∈ Ks,
      Mode.FrameSpec C (refMem r.img) (OnRun (XOf (YH L D A Ya)) r) (Ct r) K (Q r K))
    (ctMain : ∀ r, Ct r Km.F.entry = none)
    (res : ∀ r, R r → r.Ok → Mode.ResRef guestProgram r.img r.n Ks (fun s ↦ XOf (YH L D A Ya) r s))
    (term : TermRef R Ks (XOf (YH L D A Ya))) :
    ExecGaps R Ks Km E0 Ct Q (YH L D A Ya) where
  certs := certs
  main := main
  frame := frame
  ctMain := ctMain
  hintAlloc := hA.hint _ (fun _ _ h ↦ h.2.2)
  hintWitness := fun r hR hr C hC s hon _ _ _ hL s1 e1 hm hw hin ↦
    hintWitness_cur hH.progAl hH.advAl hH.witCells (fun _ _ h ↦ h.2.1) (hRH r hR) hr hC hon hL e1 hm hw hin
  hintComputed := fun r hR hr C hC s h hon hmem hna hnw s1 hm hin ↦
    hintComputed_cur hH.progAl hH.mainAt hH.jumpCells hH.layout hH.advAl hH.cellsAl hH.compRef (hRH r hR) hr
      hC hon hmem hna hnw hm hin
  res := res
  term := term
  initY := fun r hR hr C m hC hm ↦
    ⟨initY_used (by rw [(hRH r hR).κ]; exact twentyThree_le_logMem _) hm, initY_cur L D A,
      hA.init r hR hr C m hC hm⟩
  keepY := fun r hR hr C hC s op s1 s' hon hop e1 hm hmo e ↦
    ⟨keepY_used (hintsUsed_cur hH hA hRH) hR hr hC hon hop e1 hm e,
      keepY_cur main hH.progAl hH.mainAt hH.jumpCells hH.layout hH.advAl (fun _ _ h ↦ h.2.1) (hRH r hR) hr hC
        hon hop e1 hm hmo e,
      hA.keep _ (fun _ _ h ↦ h.2.2) r hR hr C hC s op s1 s' hon hop e1 hm hmo e⟩
  usedY := fun _ _ _ _ h ↦ h.1

end

end

end LeanVM.Guest.EndExec
