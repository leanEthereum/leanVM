/-
  LeanVM.Guest.EndExecC

  `ExecGaps.hintComputed` from the tree track: each computed hint the executor runs pairs with a hint atom on the top frame's path, exact on the reference's reader, at its certificate cells.
-/

module

public import LeanVM.Guest.EndExecX
public import LeanVM.Guest.Bridge.Pair
public import LeanVM.Guest.Bridge.PairEvery
public import LeanVM.Guest.Bridge.FrameMap
public import LeanVM.Guest.Bridge.PairCells

/-!
# The computed hints on the reference

At a state of the tracks past the prologue (no hint runs in it, `hints_pro`), the tree track's top frame is at the state's pc (`trackAt_X`); its function's advice there is the executor's (`HintsAl`), so a computed hint there compiles a hint atom on the frame's path (`Bridge.pair_flow`). The frame is an honest instance (`RefOk.frames`): every value its path names holds at its certificate cell (`FrameHolds.val`), and its node of the honest tree is exact on `rd0` (`Ref.Ok.tree`'s `ExactAt`, through the re-choice of temporaries, `Bridge.every_exact_retemp`, at each placed instance, `Bridge.every_insts`). The function's data check (`PairOk`: `Bridge.pairChk`) puts the atom's frame values at those cells; a buffer it writes or reads is allocated on the path (a power `g^base`, `Inst.nodeAt`) and written whole by a heap hint on it, whose words the reference holds as `rd0` does (`Ref.Ok.hintWords`). Then `HintOk` holds, kind by kind (`Bridge.hintOk_*`).

What is assumed beyond `ExecGaps.ofX`'s premises: `HintsAl` (each function's alignment reads the advice's hints), `PairOk` (each function's computed hints pass the data check), and `ExtraRef` (the reference holds a hint-only cell's value, `log2_ceil_in_the_exponent`'s buffer pointer).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Mode (HintIn adviceHints_incr ctx_hints)
open LeanVM.Guest.Bridge (FnAl ProgAl entOf alOf compiles destOk)
open LeanVM.Guest.End (mainEntry)
open LeanVM.Prover.Exec

@[expose] public section

/-- **Each function's alignment reads the advice's hints** at its offsets. -/
def HintsAl (A : String → FnAl) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∀ off < (A f).code.length,
    Mode.hintsAt Data.adviceHints ((A f).X.entry + off) = (((A f).d.2.2.lookup ((A f).X.entry + off)).getD [])

/-- **Each function's computed hints pass the data check**, its alignment's cell map the
certificate's but at its hint-only cells. -/
def PairOk (A : String → FnAl) : Prop :=
  ∀ f fn j, coreProgram.find? f = some fn → B2C.idxOf f = some j →
    Bridge.pairChk (A f).X.extra (certOf j).locs (B2C.fsN j) fn.body = true ∧
      ∀ i, (A f).X.extra.lookup i = none → i < 2 ^ 30 → (A f).X.locAt i = (certOf j).locs.getD i 0

/-- **The reference holds each hint-only cell's value**, at each honest instance. -/
def ExtraRef (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T, ∀ f σ bufs kids,
    I.t = .node f σ bufs kids → ∀ v ∈ (I.t.events coreProgram).flatMap Ev.uses, ∀ c,
      (A f).X.extra.lookup v.idx = some c → refMem r.img (I.fp + c) = σ v

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

/-- **A buffer allocated and written whole by a heap hint on an honest instance's path**: its
pointer is `g^b`, `b < maxCells`, and the reference holds `rd0`'s words over it. -/
theorem buf_ref {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Core.Val} {bufs : List ℕ} {kids : List Memory.Tree} (hIt : I.t = .node f σ bufs kids) {p : V}
    {len : ℕ} (hlen : len < 2 ^ 30) (hlen0 : 0 < len) (hp : p ∈ allocDsts (I.t.events coreProgram)) {a : Atom}
    (ha : Ev.atom a ∈ I.t.events coreProgram) (had : atomHeapDest? a = some (p, 0, len)) :
    ∃ b < maxCells, σ p = ofK (Parameters.g ^ b) ∧ ∀ k < len, b + k < maxCells ∧
      refMem r.img (b + k) = (r.rd0 ((σ p).limb 0 * addressOfIndex (0 + k))).getD 0 := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨t, ν, hv, -, hpl, -, -, -, hTt⟩ := hr.tree
  have hTp : r.T.Placed coreProgram B2C.fs B2C.cert (0, r.T.block B2C.fs coreProgram.loop) := by
    rw [hTt, block_retemp]
    exact placed_retemp coreProgram_fresh t _ hv hpl
  have hI' : I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
  have hIp := insts_placedAt r.T _ r.hdr hTp I hI'
  have hIP := insts_placed r.T _ r.hdr (by omega) I hI'
  -- the pointer: a buffer base
  obtain ⟨base, hbase⟩ : ∃ base, σ p = ofK (addressOfIndex base) := by
    have h1 := (Inst.nodeAt hIp hIP hIt).1
    have h2 : σ p ∈ (allocDsts (I.t.events coreProgram)).map σ := List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [h1] at h2
    obtain ⟨b, -, hb⟩ := List.mem_map.mp h2
    exact ⟨b, hb.symm⟩
  -- its words: hint words, which the reference holds as `rd0` does
  have hwords : ∀ k < len, ∃ v, r.rd0 ((σ p).limb 0 * addressOfIndex (0 + k)) = some v ∧
      r.img.read ((σ p).limb 0 * addressOfIndex (0 + k)) = some v := by
    intro k hk
    refine hr.hintWords _ (List.mem_flatMap.mpr ⟨I, hI, ?_⟩)
    simp only [Inst.hintAddrs, hIt]
    refine List.mem_flatMap.mpr ⟨.atom a, hIt ▸ ha, ?_⟩
    cases a with
    | hint h =>
      simp only [atomHeapDest?] at had
      simp only [Ev.hintAddrs, had]
      exact List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
    | _ => simp [atomHeapDest?] at had
  have hpow : ∀ k, (σ p).limb 0 * addressOfIndex (0 + k) = Parameters.g ^ (base + k) := fun k ↦ by
    rw [hbase]; simp [addressOfIndex, pow_add]
  obtain ⟨v0, -, hr0⟩ := hwords 0 hlen0
  obtain ⟨i0, hi0, -⟩ := (MemoryImage.read_eq_some_iff (by omega) r.img).mp hr0
  rw [hpow, Nat.add_zero] at hi0
  have hi0' : (i0 : ℕ) < 2 ^ 28 := lt_of_lt_of_le i0.isLt (Nat.pow_le_pow_right (by norm_num) hκ)
  have hσp : σ p = ofK (Parameters.g ^ (i0 : ℕ)) := by rw [hbase]; exact congrArg ofK hi0
  refine ⟨i0, by unfold maxCells; omega, hσp, fun k hk ↦ ?_⟩
  obtain ⟨v, hv0, hvi⟩ := hwords k hk
  have ha' : (σ p).limb 0 * addressOfIndex (0 + k) = Parameters.g ^ ((i0 : ℕ) + k) := by
    rw [hσp]; simp [addressOfIndex, pow_add]
  rw [ha'] at hv0 hvi
  obtain ⟨h1, h2⟩ := refRd_img hκ r.img ((i0 : ℕ) + k) v (by omega) hvi
  rw [ha', hv0]
  exact ⟨h1, h2⟩

/-- **`ExecGaps.hintComputed` from the tree track**: under `ExecGaps.ofX`'s alignment premises, each
function's alignment reading the advice's hints, its computed hints passing the data check, and the
reference holding the hint-only cells' values. -/
theorem hintComputed_X {Y : Ref → St → Prop} {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) (hJ : JumpCellsAt A) (hL : AlLayout A) (hH : HintsAl A)
    (hPC : PairOk A) (hXR : ExtraRef A) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s h, OnRun (XOf Y) r s →
      h ∈ (C.hints[s.pc]?).getD [] → isAllocHint h = false → isWitnessHint h = false → ∀ s1,
      Moves (refMem r.img) s s1 → HintIn s1 h → HintOk C (refMem r.img) s1 h := by
  intro r hr C hC s h hon hmem hna hnw s1 hm hin
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hge : proLen ≤ s.steps := by
    rcases hon.1.1 with ⟨hlt, hpc, -⟩ | ⟨hge, -⟩
    · rw [hints_pro hC rfl (show s.pc < proLen by omega)] at hmem; cases hmem
    · exact hge
  have hpc : s.pc < 2 ^ guestProgram.logSize := by
    rw [← ctx_hints_size hC]
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hmem
    cases hmem
  obtain ⟨done, e, st, hT⟩ := trackAt_X hP hmain hJ hL hr hon hge hpc
  have hE := hT.track.ents e List.mem_cons_self
  obtain ⟨hfp, hat⟩ := hT.linked.top
  obtain ⟨off, hpce, hoff, hpair⟩ := Bridge.pair_flow hP hE hat
  have hmem' : h ∈ (((A e.I.t.name).d.2.2.lookup s.pc).getD []) := by
    rw [ctx_hints (adv := r.adv) hC adviceHints_incr hpc] at hmem
    rw [hpce, ← hH _ _ hE.find off hoff, ← hpce]
    exact hmem
  obtain ⟨hc, hev, hcomp⟩ := hpair h hmem' (isaFlow_of hna hnw)
  obtain ⟨rd, hHon, hHX⟩ := hr.honest
  obtain ⟨hI, j, bufs, kids, vs, hj, hIt, -, hw, hFH⟩ :=
    (hT.frames hr.name hHon hHX.covers) e List.mem_cons_self
  -- the atom is exact on `rd0`
  have hxc : hc.Exact r.rd0 e.σ := by
    obtain ⟨t, ν, hv, -, -, -, -, hex, hTt⟩ := hr.tree
    have hexT : r.T.Every (ExactAt coreProgram r.rd0) := by
      rw [hTt]; exact Bridge.every_exact_retemp coreProgram_fresh t _ hex
    have hI' : e.I ∈ r.T.insts B2C.fs coreProgram.loop B2C.H (0, r.T.block B2C.fs coreProgram.loop) r.hdr := hI
    have hexI := Bridge.every_insts r.T _ r.hdr hexT e.I hI' _ _ bufs kids hIt
    have hevs : (Memory.Tree.node e.I.t.name e.σ [] []).events coreProgram = e.pre ++ e.es := events_node hE.find hw
    exact hexI _ (by rw [hevs]; exact hev)
  -- the data check
  obtain ⟨hchk, hlocAt⟩ := hPC _ _ j hE.find hj
  obtain ⟨hframe, hbuf⟩ := Bridge.pairChk_sound hchk hw hev (compHint_of hcomp hna hnw)
  set loc := (A e.I.t.name).X.locAt with hloc
  have hfp1 : s1.fp = e.I.fp := hm.fp.trans hfp.symm
  obtain ⟨i, -, -, -, -, -, hfs, -⟩ := B2C.fn_of_idx hj
  have hwithin : e.I.fp + B2C.fs e.I.t.name ≤ r.T.total B2C.fs :=
    honest_within hI (by have := hHon.cells.two_le e.I hI; omega)
  have h28 : r.T.total B2C.fs ≤ 2 ^ 28 :=
    le_trans (le_two_pow_logMem _) (Nat.pow_le_pow_right (by norm_num) hκ)
  have hnamed : ∀ v ∈ hintUses hc, v ∈ B2C.namedOf (coreOf j).params (e.pre ++ e.es) vs := fun v hv ↦
    List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, hev, hv⟩))
  -- a value at its certificate cell
  have hcell : ∀ v ∈ hintUses hc, loc v.idx = (certOf j).locs.getD v.idx 0 → 2 ≤ (certOf j).locs.getD v.idx 0 →
      (certOf j).locs.getD v.idx 0 < B2C.fsN j →
      s1.fp + loc v.idx < maxCells ∧ refMem r.img (s1.fp + loc v.idx) = e.σ v := by
    intro v hv hl h2 hlt
    have hrd := hFH.val v (hnamed v hv) h2 hlt
    rw [hfp1, hl]
    exact refRd_img hκ r.img _ _ (by rw [hfs] at hwithin; omega) hrd
  have hF : ∀ v ∈ Bridge.hintFrame hc, s1.fp + loc v.idx < maxCells ∧ refMem r.img (s1.fp + loc v.idx) = e.σ v :=
    fun v hv ↦ have hf := hframe v hv; hcell v (hintFrame_uses hv) (hlocAt _ hf.1 hf.2.1) hf.2.2.1 hf.2.2.2
  -- the executor reads the reference at its written cells
  have hRd : ∀ c v, s1.mem.written c = true → refMem r.img c = v → s1.mem.peek c = v := fun c v hwc hM ↦ by
    obtain ⟨w, hw'⟩ := Mem.get_of_written hwc
    rw [Mem.peek_of_get hw', ← hm.fine.agree.get c w hw', hM]
  have hIn : ∀ v ∈ Bridge.hintFrame hc, s1.mem.written (s1.fp + loc v.idx) = true →
      s1.mem.peek (s1.fp + loc v.idx) = e.σ v := fun v hv hwv ↦ hRd _ _ hwv (hF v hv).2
  -- a buffer: its pointer and the reference's words over it
  have hB : ∀ p off len, Bridge.hintBuf hc = some (p, off, len) → s1.mem.written (s1.fp + loc p.idx) = true →
      off = 0 ∧ ∃ b, PtrAt s1 (s1.fp + loc p.idx) b ∧ ∀ k < len, b + k < maxCells ∧
        refMem r.img (b + k) = ((Dest.heap p off len).words r.rd0 e.σ).getD k 0 := by
    intro p off len hb hwp
    obtain ⟨rfl, hl0, hl, hcl, hal, a, ha, had⟩ := hbuf p off len hb
    have hevs : e.I.t.events coreProgram = e.pre ++ e.es := by rw [hIt]; exact events_node hE.find hw
    obtain ⟨b, hb', hσp, hrun⟩ := buf_ref hr hI hIt hl hl0 (by rw [hevs]; exact hal) (by rw [hevs]; exact ha) had
    have hM : refMem r.img (s1.fp + loc p.idx) = e.σ p := by
      rcases hcl with hcl | hx
      · exact (hcell p (hintBuf_uses hb) (hlocAt _ hcl.1 hcl.2.1) hcl.2.2.1 hcl.2.2.2).2
      · obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hx
        have hlc : loc p.idx = c := by rw [hloc]; unfold Bridge.AlignCtx.locAt; rw [hc']; rfl
        rw [hfp1, hlc]
        have := hXR r hr e.I hI _ _ bufs kids hIt p (by rw [hevs]; exact List.mem_flatMap.mpr ⟨_, hev, hintBuf_uses hb⟩) c
          hc'
        exact this
    refine ⟨rfl, b, ⟨hRd _ _ hwp (hM.trans hσp), hb'⟩, fun k hk ↦ ⟨(hrun k hk).1, ?_⟩⟩
    rw [(hrun k hk).2, words_heap_getD hk]
  -- a destination the hint writes
  have hDest : ∀ (d : Dest) (bd : BitsDest) (pos n : ℕ), destOk loc d bd pos n = true →
      (∀ v ∈ Bridge.stackVals d, v ∈ Bridge.hintFrame hc) → (∀ q, destHeap? d = some q → Bridge.hintBuf hc = some q) →
      Mode.DestIn s1 bd → Bridge.DestR loc (refMem r.img) s1 r.rd0 e.σ d := by
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
        refine ⟨by simpa using h1, ?_⟩
        rw [Nat.add_zero, h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
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
    obtain ⟨⟨⟨-, rfl⟩, -⟩, hd⟩ := hc'
    obtain ⟨hwv, hdi⟩ := hin
    exact Bridge.hintOkR_bits hcomp (hIn v (by simp [Bridge.hintFrame]) hwv)
      (hDest d bd 0 nbits hd (fun w hw ↦ by simp [Bridge.hintFrame, hw])
        (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) hdi) hxc
  | bitsExp v nbits d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x bd n
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨rfl, -⟩, -⟩, hd⟩ := hc'
    obtain ⟨hwv, hdi⟩ := hin
    exact Bridge.hintOkR_bitsExp hcomp (hIn v (by simp [Bridge.hintFrame]) hwv)
      (hDest d bd 0 nbits hd (fun w hw ↦ by simp [Bridge.hintFrame, hw])
        (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) hdi) hxc
  | digitsExp v nbits ndigits digitBits start sc d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x bd nbits' ndigits' digitBits' start' sc'
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, -⟩, -⟩, -⟩, -⟩, -⟩, hsc⟩, hd⟩ := hc'
    obtain ⟨hwv, hws, hdi⟩ := hin
    refine Bridge.hintOkR_digitsExp hcomp (hIn v (by simp [Bridge.hintFrame]) hwv) (fun c hcs ↦ ?_)
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
    obtain ⟨⟨⟨⟨rfl, -⟩, -⟩, -⟩, hd⟩ := hc'
    obtain ⟨hwv, hdi⟩ := hin
    exact Bridge.hintOkR_windowsExp hcomp (hIn v (by simp [Bridge.hintFrame]) hwv)
      (hDest d bd pos count hd (fun w hw ↦ by simp [Bridge.hintFrame, hw])
        (fun q hq ↦ by simp [Bridge.hintBuf, hintDest?, hq]) hdi) hxc
  | limbs v ds =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x base len
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨rfl, -⟩, -⟩ := hc'
    exact Bridge.hintOkR_limbs hcomp (hIn v (by simp [Bridge.hintFrame]) hin)
      (fun w hw ↦ hF w (by simp [Bridge.hintFrame, hw])) hxc
  | log2Ceil b nbits floor dst =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i bd dst' nbits' floor'
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨⟨⟨hd, -⟩, rfl⟩, -⟩ := hc'
    have hdst := hF dst (by simp [Bridge.hintFrame])
    refine Bridge.hintOkR_log2Ceil hcomp ?_ hdst.1 hdst.2 hxc
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
        have hwk := hbits w b0 hw' ⟨by rw [hwv]; simp, hpt.2⟩ k hk h1
        rw [Nat.add_zero]
        exact hRd _ _ hwk h2
  | inverse x d =>
    cases h <;> simp only [compiles, Bool.false_eq_true] at hcomp
    rename_i x' d'
    have hc' := hcomp
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨rfl, -⟩ := hc'
    have hd := hF d (by simp [Bridge.hintFrame])
    exact Bridge.hintOk_inverse hcomp (hIn x (by simp [Bridge.hintFrame]) hin) hd.2 hd.1 hxc

end

end LeanVM.Guest.EndExec
