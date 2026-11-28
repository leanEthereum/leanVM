module

public import LeanVM.Guest.EndExecY
public import LeanVM.Guest.EndExecCUsed
public import LeanVM.Guest.Bridge.PairDefs
public import LeanVM.Guest.Bridge.PairCells
import all Statement.Data.AdviceHints

/-!
# The computed hints on the reference

At a state of the tracks past the prologue (no hint runs in it, `hints_pro`), the tree track's top
frame is at the state's pc (`trackAt`); its function's advice there is the executor's (`AdvAl`), so a
computed hint there compiles a hint atom on the frame's path (`pair_flow`). What the reference holds
of that atom is `CompRef`: the atom exact on `rd0`, its frame values at their cells, and a buffer it
writes or reads allocated at a power `g^b` with the reference's words over it as `rd0`'s. Then
`HintOk` holds, kind by kind (`Bridge.hintOkR_*`): `hintComputed_cur`.

`CompRef` is the bus era's `RefOk.frames` (each frame of the track an honest instance whose frame
holds the values its path names, `FrameHolds.val`), the data check `PairOk` (`Bridge.pairChk`: the
atom's frame values at certificate cells or hint-only cells), the tree's exactness and the hint-only
cells' values (`ExtraRef`), read at the computed hint atoms: b2c's honest memory and B2's
completeness data discharge it. `CellsAl`: each function's hints write their frame cells within its
frame (the bus era's generated `cellsChk_all`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Mode (HintIn adviceHints_incr ctx_hints)
open LeanVM.Guest.Bridge (FnAl ProgAl entOf alOf compiles destOk AtPc EntOk)
open LeanVM.Prover.Exec

@[expose] public section

/-- **What the reference holds of each computed hint atom**, at each frame of the tree track: the
atom exact on `rd0`, its frame values at their cells, and a buffer it writes or reads at a power
`g^b` with the reference's words over it `rd0`'s. -/
def CompRef (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) →
    ∀ hc, Ev.atom (.hint hc) ∈ e.pre ++ e.es → Bridge.compHint hc = true →
      hc.Exact (D r).rd0 e.σ ∧
      (∀ v ∈ Bridge.hintFrame hc, e.I.fp + (A e.I.t.name).X.locAt v.idx < maxCells ∧
        refMem r.img (e.I.fp + (A e.I.t.name).X.locAt v.idx) = e.σ v) ∧
      ∀ p off len, Bridge.hintBuf hc = some (p, off, len) → off = 0 ∧ ∃ b < maxCells,
        refMem r.img (e.I.fp + (A e.I.t.name).X.locAt p.idx) = ofK (Parameters.g ^ b) ∧
        ∀ k < len, b + k < 2 ^ r.κ ∧
          refMem r.img (b + k) = ((Dest.heap p off len).words (D r).rd0 e.σ).getD k 0

/-- **Each function's hints write their frame cells within its frame.** -/
def CellsAl (L : Lay) (A : String → FnAl) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ pc, ∀ h ∈ ((A f).d.2.2.lookup pc).getD [],
    Bridge.hintCellsOk (L.fs f) h = true

end

public section

theorem foldl_setIfInBounds_size : ∀ (l : List (ℕ × List Prover.Exec.Hint)) (a : Array (List Prover.Exec.Hint)),
    (l.foldl (fun hs (p : ℕ × List Prover.Exec.Hint) ↦ hs.setIfInBounds p.1 p.2) a).size = a.size
  | [], _ => rfl
  | p :: l, a => by
    rw [List.foldl_cons, foldl_setIfInBounds_size l, Array.size_setIfInBounds]

theorem ctx_hints_size {prog : LeanIsaProgram} {adv : Advice} {C : Ctx} (h : Ctx.of prog adv = .ok C) :
    C.hints.size = 2 ^ prog.logSize := by
  simp only [Ctx.of, bind_ok, pure_ok] at h
  obtain ⟨ops, -, rfl⟩ := h
  exact (foldl_setIfInBounds_size _ _).trans (Array.size_replicate ..)

theorem isaFlow_of {h : Prover.Exec.Hint} (h1 : isAllocHint h = false) (h2 : isWitnessHint h = false) :
    Bridge.isaFlowHint h = true := by
  cases h <;> simp_all [isAllocHint, isWitnessHint, Bridge.isaFlowHint]

theorem compHint_of {loc : ℕ → ℕ} {hc : Core.Hint} {h : Prover.Exec.Hint} (hcomp : compiles loc hc h = true)
    (h1 : isAllocHint h = false) (h2 : isWitnessHint h = false) : Bridge.compHint hc = true := by
  cases hc with
  | witness s d => cases d <;> cases h <;> simp_all [compiles, isWitnessHint]
  | alloc d n => cases h <;> simp_all [compiles, isAllocHint]
  | allocDyn d n => cases h <;> simp_all [compiles, isAllocHint]
  | _ => rfl

theorem hintFrame_uses {h : Core.Hint} {v : V} (hv : v ∈ Bridge.hintFrame h) : v ∈ hintUses h := by
  cases h with
  | bits _ _ _ d => cases d <;> simp_all [Bridge.hintFrame, Bridge.stackVals, hintUses, destUses]
  | bitsExp _ _ d => cases d <;> simp_all [Bridge.hintFrame, Bridge.stackVals, hintUses, destUses]
  | digitsExp _ _ _ _ _ sc d =>
    cases d <;> cases sc <;> (simp only [Bridge.hintFrame, Bridge.stackVals, hintUses, destUses, Option.toList,
      List.mem_cons, List.mem_append, List.nil_append, List.not_mem_nil, or_false] at hv ⊢; tauto)
  | windowsExp _ _ _ _ d => cases d <;> simp_all [Bridge.hintFrame, Bridge.stackVals, hintUses, destUses]
  | log2Ceil b _ _ _ => cases b <;> simp_all [Bridge.hintFrame, Bridge.stackVals, hintUses, destUses]
  | _ => simp_all [Bridge.hintFrame, hintUses]

theorem hintBuf_uses {h : Core.Hint} {p : V} {off len : ℕ} (hb : Bridge.hintBuf h = some (p, off, len)) :
    p ∈ hintUses h := by
  cases h with
  | log2Ceil b _ _ _ => cases b <;> simp_all [Bridge.hintBuf, destHeap?, hintUses, destUses]
  | witness _ d => cases d <;> simp_all [Bridge.hintBuf, hintDest?, destHeap?, hintUses, destUses]
  | bits _ _ _ d => cases d <;> simp_all [Bridge.hintBuf, hintDest?, destHeap?, hintUses, destUses]
  | bitsExp _ _ d => cases d <;> simp_all [Bridge.hintBuf, hintDest?, destHeap?, hintUses, destUses]
  | digitsExp _ _ _ _ _ _ d => cases d <;> simp_all [Bridge.hintBuf, hintDest?, destHeap?, hintUses, destUses]
  | windowsExp _ _ _ _ d => cases d <;> simp_all [Bridge.hintBuf, hintDest?, destHeap?, hintUses, destUses]
  | _ => simp_all [Bridge.hintBuf, hintDest?]

theorem words_heap_getD {rd : Reader} {σ : Core.Val} {p : V} {off len k : ℕ} (hk : k < len) :
    ((Dest.heap p off len).words rd σ).getD k 0 = (rd ((σ p).limb 0 * addressOfIndex (off + k))).getD 0 := by
  simp [Dest.words, List.getD_eq_getElem?_getD, hk]

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => (List.not_mem_nil hb).elim
  | a :: _, b' :: _, .cons hab h, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', hr⟩ := forall₂_mem_right h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hr⟩

theorem walk_atoms_pre {σ : Val} : ∀ (bs : List Atom) (ps : List Stmt),
    walk σ (bs.map Stmt.atom ++ ps) = (walk σ ps).pre (bs.map Ev.atom)
  | [], ps => by simp only [List.map_nil, List.nil_append, Bridge.out_pre_nil]
  | b :: bs, ps => by
    rw [List.map_cons, List.cons_append, Bridge.walk_atom_cons, walk_atoms_pre bs ps, Bridge.out_pre_pre]
    rfl

/-- **Atoms heading a position are on its path.** -/
theorem atoms_on_path {σ : Val} {bs : List Atom} {ps : List Stmt} {es : List Ev} {vs : List V}
    (h : walk σ (bs.map Stmt.atom ++ ps) = .ret es vs) : ∀ a ∈ bs, Ev.atom a ∈ es := by
  rw [walk_atoms_pre] at h
  obtain ⟨es', -, rfl⟩ := Bridge.pre_eq_ret h
  intro a ha
  exact List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- **The pairing at a pc**: a frame of the tree track at pc `pc` is at an offset `off` of its
function's code, and each flow hint of its advice at `pc` compiles a hint atom on its path. -/
theorem pair_flow {prog : LeanIsaProgram} {P : Core.Program} {A : String → FnAl} (hP : ProgAl prog P A)
    {Is : List Inst} {e : Bridge.Ent} (hE : EntOk P Is e) {pc : ℕ} (hat : AtPc (entOf A) (alOf A) e pc) :
    ∃ off, pc = (A e.I.t.name).X.entry + off ∧ off < (A e.I.t.name).code.length ∧
      ∀ h ∈ (((A e.I.t.name).d.2.2.lookup pc).getD []), Bridge.isaFlowHint h = true →
        ∃ hc, Ev.atom (.hint hc) ∈ e.pre ++ e.es ∧ compiles (A e.I.t.name).X.locAt hc h = true := by
  obtain ⟨off, hpc, p, hal, as0, -, hpos⟩ := hat
  obtain ⟨ins, z, tabs, r, as, hins, -, hp, hF2, -⟩ := Bridge.alignAt_step (hP.ok _ _ hE.find) hal
  refine ⟨off, hpc, (List.getElem?_eq_some_iff.mp hins).1, fun h hh hfl ↦ ?_⟩
  rw [hpc] at hh
  obtain ⟨a, ha, hc, rfl, hcomp⟩ := forall₂_mem_right hF2 h (List.mem_filter.mpr ⟨hh, hfl⟩)
  obtain ⟨vs, -, hw⟩ := hE.path
  rw [hpos, hp, ← List.append_assoc, ← List.map_append] at hw
  exact ⟨hc, List.mem_append_right _ (atoms_on_path hw _ (List.mem_append_right _ (List.mem_filter.mp ha).1)),
    hcomp⟩

/-- **A frame of the track lies within the reference.** -/
theorem frame_within {L : Lay} {D : Ref → RefD} {r : Ref} (hR : RefH L (D r) r) {e : Bridge.Ent}
    (hE : EntOk coreProgram (instsOf L (D r) r) e) : e.I.fp + L.fs e.I.t.name ≤ 2 ^ r.κ := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  obtain ⟨f, bufs, kids, ht⟩ := hE.node
  have h2 := hH.cells.two_le e.I hE.mem
  have hw := honestA_within hE.mem (by omega)
  rw [fszA_of_node ht] at hw
  rw [hR.κ]
  exact le_trans hw (le_two_pow_logMem _)

/-- **Each computed hint's destination holds, on the reference, its formula of its inputs**, at any
state the pc's hints reach; a buffer destination's run below `2^κ`. -/
theorem hintComputed_core {L : Lay} {D : Ref → RefD} {A : String → FnAl}
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen) (hJ : JumpCellsAt L D A)
    (hL : AlLayout A) (hAd : AdvAl A) (hCl : CellsAl L A) (hCR : CompRef L D A) {Y : Ref → St → Prop}
    {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C)
    {s : St} {h : Prover.Exec.Hint} (hon : OnRun (XOf Y) r s) (hmem : h ∈ (C.hints[s.pc]?).getD [])
    (hna : isAllocHint h = false) (hnw : isWitnessHint h = false) {s1 : St} (hm : MovesW (refMem r.img) s s1) :
    HeapB (2 ^ r.κ) s1 h ∧ (HintIn s1 h → HintOk C (refMem r.img) s1 h) := by
  have hκ : r.κ ≤ 28 := hr.log
  have hpc : s.pc < 2 ^ guestProgram.logSize := by
    have hsz := ctx_hints_size hC
    by_contra hc
    rw [Array.getElem?_eq_none (by rw [hsz]; omega)] at hmem
    cases hmem
  have hge : proLen ≤ s.steps := by
    by_contra hlt
    have hpc19 := hpc
    rw [guest_logSize] at hpc19
    have hpcs := ((posAt hR hon.1.1 (by omega) hon.2.1.fp).1 (by omega)).1
    rw [hints_pro hC rfl (show s.pc < proLen by omega)] at hmem
    cases hmem
  have hposh : posHintOk h = true := hints_pos hC rfl hpc h hmem
  obtain ⟨done, e, st, hT⟩ := trackAt hP hmain hJ hL hR hr hon.1.1 hon.2.1 hon.2.2 hge hpc
  have hE := hT.track.ents e List.mem_cons_self
  obtain ⟨hfp, hat⟩ := hT.linked.top
  obtain ⟨off, hpce, hoff, hpair⟩ := pair_flow hP hE hat
  have hins : (A e.I.t.name).code[off]? = some ((A e.I.t.name).code[off]) := List.getElem?_eq_getElem hoff
  have hmem' : h ∈ (((A e.I.t.name).d.2.2.lookup s.pc).getD []) := by
    rw [ctx_hints (adv := r.adv) hC adviceHints_incr hpc] at hmem
    rw [hpce, hAd _ _ hE.find off _ hins, ← hpce]
    exact hmem
  obtain ⟨hc, hev, hcomp⟩ := hpair h hmem' (isaFlow_of hna hnw)
  obtain ⟨hxc, hFr, hBuf⟩ := hCR r hR hr _ _ _ _ _ hT hc hev (compHint_of hcomp hna hnw)
  have hcells := hCl _ _ hE.find s.pc h hmem'
  have hwithin := frame_within hR hE
  set loc := (A e.I.t.name).X.locAt with hloc
  have hfp1 : s1.fp = e.I.fp := hm.1.trans hfp.symm
  have h2k : 2 ^ r.κ ≤ maxCells := Nat.pow_le_pow_right (by norm_num) hκ
  have hF : ∀ v ∈ Bridge.hintFrame hc, s1.fp + loc v.idx < maxCells ∧
      refMem r.img (s1.fp + loc v.idx) = e.σ v := by
    intro v hv; rw [hfp1]; exact hFr v hv
  -- the executor reads the reference at its written cells
  have hRd : ∀ c v, s1.mem.written c = true → refMem r.img c = v → s1.mem.peek c = v := fun c v hwc hM ↦ by
    obtain ⟨w, hw'⟩ := Mem.get_of_written hwc
    rw [Mem.peek_of_get hw', ← hm.2 c w hw', hM]
  have hIn : ∀ v ∈ Bridge.hintFrame hc, s1.mem.written (s1.fp + loc v.idx) = true →
      s1.mem.peek (s1.fp + loc v.idx) = e.σ v := fun v hv hwv ↦ hRd _ _ hwv (hF v hv).2
  -- a buffer: its pointer and the reference's words over it
  have hB : ∀ p off len, Bridge.hintBuf hc = some (p, off, len) → s1.mem.written (s1.fp + loc p.idx) = true →
      off = 0 ∧ ∃ b, PtrAt s1 (s1.fp + loc p.idx) b ∧ ∀ k < len, b + k < 2 ^ r.κ ∧
        refMem r.img (b + k) = ((Dest.heap p off len).words (D r).rd0 e.σ).getD k 0 := by
    intro p off len hb hwp
    obtain ⟨rfl, b, hb', hM, hrun⟩ := hBuf p off len hb
    exact ⟨rfl, b, ⟨hRd _ _ hwp (by rw [hfp1]; exact hM), hb'⟩, hrun⟩
  -- a destination the hint writes
  have hDest : ∀ (d : Dest) (bd : BitsDest) (pos n : ℕ), destOk loc d bd pos n = true →
      (∀ v ∈ Bridge.stackVals d, v ∈ Bridge.hintFrame hc) → (∀ q, destHeap? d = some q → Bridge.hintBuf hc = some q) →
      Mode.DestIn s1 bd → Bridge.DestR loc (refMem r.img) s1 (D r).rd0 e.σ d := by
    intro d bd pos n hd hsv hhb hdi
    cases d with
    | stack ws => exact fun v hv ↦ hF v (hsv v hv)
    | heap p off len =>
      cases bd with
      | stack _ => simp [destOk] at hd
      | heap ptr =>
        simp only [destOk, Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨⟨hptr, -⟩, -⟩ := hd
        have hwp : s1.mem.written (s1.fp + loc p.idx) = true := by rw [hptr]; exact hdi
        obtain ⟨rfl, b, hpt, hrun⟩ := hB p off len (hhb _ rfl) hwp
        refine ⟨b, hpt, fun k hk ↦ ?_⟩
        have hk' : k < len := by simpa [Dest.words] using hk
        obtain ⟨h1, h2⟩ := hrun k hk'
        refine ⟨by have := h2k; simp; omega, ?_⟩
        rw [Nat.add_zero, h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  -- a buffer destination's run below `2^κ`
  have hHeap : ∀ (d : Dest) (bd : BitsDest) (pos n : ℕ), destOk loc d bd pos n = true →
      (∀ q, destHeap? d = some q → Bridge.hintBuf hc = some q) →
      ∀ ptr, bd = .heap ptr → ∀ b, PtrAt s1 (s1.fp + ptr) b → ∀ k < n, b + pos + k < 2 ^ r.κ := by
    intro d bd pos n hd hhb ptr hbd b hpt k hk
    subst hbd
    cases d with
    | stack _ => simp [destOk] at hd
    | heap p off len =>
      simp only [destOk, Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨⟨hptr, rfl⟩, rfl⟩ := hd
      rw [← hptr] at hpt
      obtain ⟨v, hv, -⟩ := get_of_ptrAt hpt
      obtain ⟨rfl, b0, hpt0, hrun⟩ := hB p off len (hhb _ rfl) (Mode.written_of_get hv)
      obtain rfl := ptrAt_uniq hpt hpt0
      have := (hrun k hk).1
      omega
  have hsv : ∀ (d : Dest) (v : V) (l : List V), v ∈ Bridge.stackVals d → v ∈ l ++ Bridge.stackVals d :=
    fun _ _ _ hv ↦ List.mem_append_right _ hv
  cases hc with
  | witness _ _ => exact absurd (compHint_of hcomp hna hnw) (by simp [Bridge.compHint])
  | alloc _ _ => exact absurd (compHint_of hcomp hna hnw) (by simp [Bridge.compHint])
  | allocDyn _ _ => exact absurd (compHint_of hcomp hna hnw) (by simp [Bridge.compHint])
  | bits v start nbits d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x bd n
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨-, rfl⟩, hnb⟩, hd⟩ := hc'
    refine ⟨?_, fun hin ↦ ?_⟩
    · rw [← hnb]
      cases bd with
      | stack _ => trivial
      | heap ptr => exact hHeap d _ 0 nbits hd (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) ptr rfl
    obtain ⟨hwv, hdi⟩ := hin
    exact Bridge.hintOkR_bits hcomp (hIn v (by simp [Bridge.hintFrame]) hwv)
      (hF v (by simp [Bridge.hintFrame])).1 (by simpa [posHintOk] using hposh)
      (hDest d bd 0 nbits hd (fun w hw ↦ by simp [Bridge.hintFrame, hw])
        (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) hdi) hxc
  | bitsExp v nbits d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x bd n
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨rfl, hnb⟩, -⟩, hd⟩ := hc'
    refine ⟨?_, fun hin ↦ ?_⟩
    · rw [← hnb]
      cases bd with
      | stack _ => trivial
      | heap ptr => exact hHeap d _ 0 nbits hd (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) ptr rfl
    obtain ⟨hwv, hdi⟩ := hin
    exact Bridge.hintOkR_bitsExp hcomp (hIn v (by simp [Bridge.hintFrame]) hwv)
      (by simpa [posHintOk] using hposh)
      (hDest d bd 0 nbits hd (fun w hw ↦ by simp [Bridge.hintFrame, hw])
        (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) hdi) hxc
  | digitsExp v nbits ndigits digitBits start sc d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x bd nbits' ndigits' digitBits' start' sc'
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, -⟩, hnd⟩, -⟩, -⟩, -⟩, hsc⟩, hd⟩ := hc'
    refine ⟨?_, fun hin ↦ ?_⟩
    · rw [← hnd]
      cases bd with
      | stack _ => trivial
      | heap ptr => exact hHeap d _ 0 ndigits hd (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) ptr rfl
    obtain ⟨hwv, hws, hdi⟩ := hin
    refine Bridge.hintOkR_digitsExp hcomp (hIn v (by simp [Bridge.hintFrame]) hwv) (fun c hcs ↦ ?_)
      (fun base hbd ↦ by
        subst hbd
        simp only [Bridge.hintCellsOk, Bridge.dstCellsOk, decide_eq_true_eq] at hcells
        rw [hfp1]
        omega)
      (hDest d bd 0 ndigits hd (fun w hw ↦ by simp [Bridge.hintFrame, hw])
        (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) hdi) hxc
    subst hcs
    cases sc' with
    | none => simp [Bridge.startOk] at hsc
    | some c' =>
      simp only [Bridge.startOk, beq_iff_eq] at hsc
      exact hIn c (by simp [Bridge.hintFrame]) (by rw [hsc]; exact hws c' rfl)
  | windowsExp v start width count d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x bd pos start' width' count'
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨⟨rfl, -⟩, -⟩, hnc⟩, hd⟩ := hc'
    refine ⟨?_, fun hin ↦ ?_⟩
    · rw [← hnc]
      cases bd with
      | stack _ => trivial
      | heap ptr => exact hHeap d _ pos count hd (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) ptr rfl
    obtain ⟨hwv, hdi⟩ := hin
    exact Bridge.hintOkR_windowsExp hcomp (hIn v (by simp [Bridge.hintFrame]) hwv)
      (hF v (by simp [Bridge.hintFrame])).1 (by simpa [posHintOk] using hposh)
      (hDest d bd pos count hd (fun w hw ↦ by simp [Bridge.hintFrame, hw])
        (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) hdi) hxc
  | limbs v ds =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x base len
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨rfl, -⟩, -⟩ := hc'
    refine ⟨trivial, fun hin ↦ ?_⟩
    exact Bridge.hintOkR_limbs hcomp (hIn v (by simp [Bridge.hintFrame]) hin)
      (hF v (by simp [Bridge.hintFrame])).1 (by simpa [posHintOk] using hposh)
      (fun w hw ↦ hF w (by simp [Bridge.hintFrame, hw])) hxc
  | log2Ceil b nbits floor dst =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i bd dst' nbits' floor'
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨hd, -⟩, rfl⟩, -⟩ := hc'
    refine ⟨trivial, fun hin ↦ ?_⟩
    have hdst := hF dst (by simp [Bridge.hintFrame])
    refine Bridge.hintOkR_log2Ceil hcomp ?_ ?_ hdst.1 hdst.2 hxc
    swap
    · -- the bits' run ends below `maxCells`: its last cell is a frame value's, or a buffer's word's
      intro a ha
      have hnp := hposh
      simp only [posHintOk, Nat.blt_eq] at hnp
      cases b with
      | stack ws =>
        cases bd with
        | heap _ => simp [destOk] at hd
        | stack base =>
          simp only [destOk, Bool.and_eq_true, beq_iff_eq] at hd
          obtain ⟨hlen, hcons⟩ := hd
          have ha' : s1.fp + base = a := ha
          subst ha'
          have hk : ws.length - 1 < ws.length := by omega
          have hv : ws[ws.length - 1] ∈ ws := List.getElem_mem hk
          have h1 := (hF ws[ws.length - 1] (by simp [Bridge.hintFrame, Bridge.stackVals, hv])).1
          rw [Bridge.consecutive_get hcons _ hk] at h1
          omega
      | heap p off len =>
        cases bd with
        | stack _ => simp [destOk] at hd
        | heap ptr =>
          simp only [destOk, Bool.and_eq_true, beq_iff_eq] at hd
          obtain ⟨⟨hptr, -⟩, hlen⟩ := hd
          obtain ⟨a', hpa, rfl⟩ := ha
          obtain ⟨hwp, -⟩ := hin
          rw [← hptr] at hwp hpa
          obtain ⟨rfl, b0, hpt, hrun⟩ := hB p off len (by simp [Bridge.hintBuf, destHeap?]) hwp
          obtain rfl := ptrAt_uniq hpa hpt
          have := (hrun (len - 1) (by omega)).1
          omega
    cases b with
    | stack ws =>
      cases bd with
      | heap _ => simp [destOk] at hd
      | stack base =>
        simp only [destOk, Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨rfl, hcons⟩ := hd
        intro v hv
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
        refine hIn _ (by simp [Bridge.hintFrame, Bridge.stackVals, hv]) ?_
        rw [Bridge.consecutive_get hcons k hk, ← Nat.add_assoc]
        exact hin k hk
    | heap p off len =>
      cases bd with
      | stack _ => simp [destOk] at hd
      | heap ptr =>
        simp only [destOk, Bool.and_eq_true, beq_iff_eq] at hd
        obtain ⟨⟨hptr, -⟩, rfl⟩ := hd
        obtain ⟨hwp, hbits⟩ := hin
        rw [← hptr] at hwp hbits
        obtain ⟨rfl, b0, hpt, hrun⟩ := hB p off len (by simp [Bridge.hintBuf, destHeap?]) hwp
        refine ⟨b0, hpt, fun k hk ↦ ?_⟩
        obtain ⟨h1, h2⟩ := hrun k hk
        obtain ⟨w, hw'⟩ := Mem.get_of_written hwp
        have hwv : w = ofK (Parameters.g ^ b0) := (Mem.peek_of_get hw').symm.trans hpt.1
        have hwk := hbits w b0 hw' ⟨by rw [hwv]; simp, hpt.2⟩ k hk (by omega)
        rw [Nat.add_zero]
        exact hRd _ _ hwk h2
  | inverse x d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x' d'
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨rfl, -⟩ := hc'
    refine ⟨trivial, fun hin ↦ ?_⟩
    have hd := hF d (by simp [Bridge.hintFrame])
    exact Bridge.hintOk_inverse hcomp (hIn x (by simp [Bridge.hintFrame]) hin)
      (hF x (by simp [Bridge.hintFrame])).1 hd.2 hd.1 hxc

/-- **Each computed hint's destination holds, on the reference, its formula of its inputs**:
`ExecGaps`' `hintComputed` on a reference of the honest tree. -/
theorem hintComputed_cur {L : Lay} {D : Ref → RefD} {A : String → FnAl}
    (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen) (hJ : JumpCellsAt L D A)
    (hL : AlLayout A) (hAd : AdvAl A) (hCl : CellsAl L A) (hCR : CompRef L D A) {Y : Ref → St → Prop}
    {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C)
    {s : St} {h : Prover.Exec.Hint} (hon : OnRun (XOf Y) r s) (hmem : h ∈ (C.hints[s.pc]?).getD [])
    (hna : isAllocHint h = false) (hnw : isWitnessHint h = false) {s1 : St} (hm : Moves (refMem r.img) s s1)
    (hin : HintIn s1 h) : HintOk C (refMem r.img) s1 h :=
  (hintComputed_core hP hmain hJ hL hAd hCl hCR hR hr hC hon hmem hna hnw hm.w).2 hin

end

end LeanVM.Guest.EndExec
