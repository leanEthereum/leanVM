/-
  LeanVM.Guest.EndExecAUsed

  The hints keep the cells used within the reference's `2^κ` (`HintsUsed`), on the deployed
  alignment.
-/

module

public import LeanVM.Guest.EndExecAGaps
public import LeanVM.Guest.EndExecYWit
public import LeanVM.Guest.EndExecAExtra
public import LeanVM.Guest.EndExecYShape

/-!
# The cells the hints use

`hintsUsed_alignA : SizesAt alignA → AllocReady alignA → WitCells alignA → HintsUsed Y`: each hint at a
frame's pc writes below `2^κ` (`usedOk_of`, then `hints_used`):

* its frame cells are below the frame's size (`Bridge.cellsChk_all`), the frame within the tree,
  within `2^κ`;
* its runs from a buffer pointer are the reference's hint words there, below `2^κ`: a witness hint's
  (`witness_core`), a computed hint's (`heapComputed_alignA`);
* an allocation's reservation ends within the tree (`hintAllocW_of`), its inputs written since its
  run succeeded (`allocHintIn`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

theorem written_of_peek {s : St} {c : ℕ} (h : s.mem.peek c ≠ 0) : s.mem.written c = true := by
  unfold Mem.peek at h
  cases hg : s.mem.get c with
  | none => rw [hg] at h; exact absurd rfl h
  | some v => exact Mode.written_of_get hg

/-- **An allocation hint whose run succeeds found its inputs written.** -/
theorem allocHintIn {C : Ctx} {s s' : St} {h : Hint} (hs : s.Good) (ha : isAllocHint h = true)
    (e : runHint C s h = .ok s') : Mode.HintIn s h := by
  cases h with
  | allocDyn p c =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c', hc', sz, hsz, ⟨n, s1⟩, h1, -⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc'
    obtain ⟨-, h2, h3⟩ := logOr_sm hs h1
    obtain ⟨v, hv, -⟩ := get_of_ptrAt (ptrAt_of hsz h2 h3)
    exact Mode.written_of_get hv
  | allocArm p sel sizes =>
    simp only [runHint, bind_ok] at e
    obtain ⟨c', hc', x, hx, ⟨k, s1⟩, h1, -⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc'
    obtain ⟨-, h2, h3⟩ := logOr_sm hs h1
    obtain ⟨v, hv, -⟩ := get_of_ptrAt (ptrAt_of hx h2 h3)
    exact Mode.written_of_get hv
  | allocFrames p size stop si tail =>
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

/-- **The hints keep the cells used within the reference's `2^κ`**, on the deployed alignment. -/
theorem hintsUsed_alignA (hS : SizesAt alignA) (hR : AllocReady alignA) (hW : WitCells alignA)
    {Y : Ref → St → Prop} (hY : ∀ r s, Y r s → YCur alignA r s ∧ YAlloc alignA r s) : HintsUsed Y := by
  intro r hr C hC s s1 hon e1 hm
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hu0 : s.mem.used ≤ 2 ^ r.κ := hon.1.2.1
  have hs0 : s.Good := ⟨hon.2.1.agree.wf, hon.2.1.dl⟩
  -- no hints: nothing written
  have hnil : (C.hints[s.pc]?).getD [] = [] → s1.mem.used ≤ 2 ^ r.κ := fun h0 ↦ by
    rw [h0] at e1
    simp only [List.foldlM_nil, pure_ok] at e1
    subst e1; exact hu0
  by_cases hpro : s.steps < proLen
  · have hpc : s.pc < proLen := by
      rcases hon.1.1 with ⟨-, hpc, -⟩ | ⟨hge, -⟩
      · omega
      · omega
    exact hnil (hints_pro hC rfl hpc)
  by_cases hpcS : s.pc < C.ops.size
  swap
  · refine hnil ?_
    have hsz := (ctx_hints_size hC).trans (ctx_of_spec hC).1.symm
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  obtain ⟨done, e, st, htr, -, hch, -⟩ := (hY r s hon.1.2.2).2.2 (by omega) hon.2.2.1
  have hE := htr.track.ents e List.mem_cons_self
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, -⟩ := (htr.frames hr.name hHon hHX.covers) e List.mem_cons_self
  obtain ⟨i0, rfl, -, -, -, -, hfs, -, h1, h2⟩ := B2C.fn_of_idx hj
  have hA2 : alignA e.I.t.name = fnAl (i0 + 1) := alignA_of hj
  -- the frame within `2^κ`
  have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ r.T.total B2C.fs :=
    honest_within_node hI hIt (by have := hHon.cells.two_le e.I hI; omega)
  have htot := le_two_pow_logMem (r.T.total B2C.fs)
  have hfpe : e.I.fp = s.fp := htr.linked.top.1
  -- the hints at the pc are the function's
  obtain ⟨-, hat⟩ := htr.linked.top
  obtain ⟨off, hpc, q, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (progAl.ok _ _ hE.find) hal'
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (by rw [← (ctx_of_spec hC).1]; exact hpcS)
  have hhs : (C.hints[s.pc]?).getD [] = hintsAtOff (alignA e.I.t.name) off := by
    rw [hh, hintsAtOff, advAl_alignA _ _ hE.find off ins hins]
    rw [hpc]
    rfl
  have hcells : ∀ h ∈ (C.hints[s.pc]?).getD [], hintCellsOk (B2C.fsN (i0 + 1)) h = true := by
    intro h hmem
    rw [hhs, hintsAtOff] at hmem
    cases hlk : (alignA e.I.t.name).d.2.2.lookup ((alignA e.I.t.name).X.entry + off) with
    | none => rw [hlk] at hmem; cases hmem
    | some hs =>
      rw [hlk, Option.getD_some] at hmem
      have hp := mem_of_lookupN hlk
      rw [hA2] at hp
      exact List.all_eq_true.mp (List.all_eq_true.mp (cellsChk_all _ h2) _ hp) h hmem
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
  refine usedOk_of (fs := B2C.fsN (i0 + 1)) (hcells h hmem) (by rw [hfx.fp, ← hfpe, ← hfs]; unfold Ref.κ; omega)
    ?_ ?_
  · cases ha : isAllocHint h
    · cases hw : isWitnessHint h
      · exact heapComputed_alignA extraRef_alignA r hr C hC s h hon hmem ha hw sx hmw
      · exact (witness_core progAl advAl_alignA hW pushShape (fun r s h ↦ (hY r s h).1) r hr C hC s hon _ h _ hl
          sx hx hmw hw).1
    · exact heapB_of_alloc ha
  · cases ha : isAllocHint h
    · exact allocB_of_not ha
    · exact (hintAllocW_of progAl advAl_alignA hS hR (fun r s h ↦ (hY r s h).2) r hr C hC s hon _ h _ hl sx hx hmw ha
        (allocHintIn hfx.good ha h2')).2

end

end LeanVM.Guest.EndExec
