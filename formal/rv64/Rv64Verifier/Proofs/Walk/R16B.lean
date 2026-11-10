import Rv64Verifier.Proofs.Walk.R16A
import Rv64Verifier.Proofs.Walk.Keeps

/-!
# `walk` R16: `verify_bus_balance`'s call, to `AtR17`

The call writes its result at `S - 928`, the sponge, its stack and the heap it allocates
(`busCall`). An `Err` is copied to the result (`0x80003ea0`) and the function returns; an `Ok` is
`AtR17` at `0x800035f0` (`r16`), its bus the result's (one for every transcript:
`BusResultAt.unique`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The memory holds at most one bus result. -/
theorem BusResultAt.unique {s s' t : MachineState} {a : Word} {r r' : BusResultRust}
    (h : BusResultAt s t a r) (h' : BusResultAt s' t a r') : r = r' := by
  obtain ⟨c, bp, p, f, tt⟩ := r
  obtain ⟨c', bp', p', f', tt'⟩ := r'
  simp only [BusResultRust.mk.injEq]
  exact ⟨h.claims.2.2.1.symm.trans h'.claims.2.2.1, h.bytecodePoint.elems.symm.trans
    h'.bytecodePoint.elems, h.point.elems.symm.trans h'.point.elems,
    h.forms.2.symm.trans h'.forms.2, h.totals.elems.symm.trans h'.totals.elems⟩

/-- Some transcript stands for any memory. -/
theorem transcriptAt_ex (u : MachineState) (p : Word) : ∃ T, TranscriptAt u p T :=
  ⟨{ proof := { stream := eListAt u (streamPtr u p) (streamLen u p), openings := [] }
     sponge := spongeAt u (p + 8), streamOffset := (u.getMem (p + 344)).toNat
     openingOffset := (u.getMem (p + 352)).toNat, roots := [] }, rfl, rfl, rfl, rfl⟩

/-- `BusResultAt` from a call's entry `c` holds from `walk`'s. -/
theorem BusResultAt.widen {s c t : MachineState} {a : Word} {r : BusResultRust}
    (h : BusResultAt c t a r) (hm : heapNext s ≤ heapNext c) : BusResultAt s t a r := by
  have wb : ∀ {p : Word} {n : Nat}, BufIn c t p n → BufIn s t p n := fun hb ↦
    ⟨hb.1, hb.2.1, hb.2.2.imp_right fun h' ↦ le_trans hm h'⟩
  have wn : ∀ {p : Word} {n : Nat}, NewBuf c t p n 8 → NewBuf s t p n 8 := fun hb ↦
    ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨le_trans hm h'.1, h'.2⟩⟩
  have wv : ∀ {p : Word} {xs : List E}, NewVecE c t p xs → NewVecE s t p xs := fun hv ↦
    ⟨hv.vec, wn hv.buf, hv.elems⟩
  exact ⟨⟨h.claims.1, wn h.claims.2.1, h.claims.2.2.1, fun i hi ↦
      (h.claims.2.2.2 i hi).imp fun _ hx ↦ wv hx⟩, wv h.bytecodePoint, wv h.point, h.forms,
    wv h.totals, wb h.claimsIn, fun i hi ↦ ⟨wb (h.claimPoints i hi).1, (h.claimPoints i hi).2⟩,
    wb h.pointIn, wb h.formsIn,
    fun i hi ↦ ⟨(h.formRows i hi).1, fun j hj ↦ wb ((h.formRows i hi).2 j hj)⟩, h.formsApart,
    h.formTags⟩

/-- The call's frame as a step: its result, the sponge, its stack, `NEXT` and what it allocates. -/
theorem busCallStep {s c y : MachineState} (hpre : WalkPre s) (I : Inv s c)
    (h10 : c.getReg .x10 = s.getReg .x2 - 928) (h12 : c.getReg .x12 = tp s)
    {bev : MachineState → Word → List E → Option E} (post : BusBalancePost bev c y)
    (sp : y.getReg .x2 = c.getReg .x2) :
    StepW s c y (fun a ↦ Within a (s.getReg .x2 - 928) 120) True := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hs := busStack_le
  refine ⟨post.frame.mono fun a ha ↦ ?_, post.heap, post.mono, sp⟩
  rw [h10, h12, stackLo_callee I] at ha
  rcases ha with ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, by rw [tp] at ha ⊢; addr_omega [ha, hb1]⟩)))
  · exact Or.inr (Or.inl (by addr_omega [ha, hb1, hs]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))

section Same
variable {s y t : MachineState} (hm : ∀ x, t.getMem x = y.getMem x)
include hm

theorem VecOk.same' {a : Word} {sz al : Nat} (h : VecOk y a sz al) : VecOk t a sz al :=
  ⟨by simpa only [RawVecOk, Buf, vecPtr, vecCap, heapNext, hm] using h.raw,
    by simpa only [vecLen, vecCap, hm] using h.len⟩

theorem NewVecE.same' {a : Word} {xs : List E} (h : NewVecE s y a xs) : NewVecE s t a xs :=
  ⟨VecOk.same' hm h.vec, by simpa only [NewBuf, vecPtr, vecCap, heapNext, hm] using h.buf,
    by simpa only [vecEs, eListAt, eAt, vecPtr, vecLen, hm] using h.elems⟩

theorem monoAt_same (a : Word) : monoAt t a = monoAt y a := by
  unfold monoAt
  rw [hm a, hm (a + 8), hm (a + 16)]

theorem formRowsAt_same (a : Word) (n : Nat) : formRowsAt t a n = formRowsAt y a n := by
  simp only [formRowsAt, formVecAt, formAt, termsAt, monoAt_same hm, eAt, vecPtr, vecLen, hm]

/-- `BusResultAt` reads only memory. -/
theorem BusResultAt.same {a : Word} {r : BusResultRust} (h : BusResultAt s y a r) :
    BusResultAt s t a r := by
  obtain ⟨⟨c1, c2, c3, c4⟩, c5, c6, ⟨c7, c8⟩, c9, c10, c11, c12, c13, c14, c15, c16⟩ := h
  refine ⟨⟨VecOk.same' hm c1, by simpa only [NewBuf, vecPtr, vecCap, heapNext, hm] using c2,
      by simpa only [claimAt, vecEs, eListAt, eAt, vecPtr, vecLen, hm] using c3,
      fun i hi ↦ ?_⟩, NewVecE.same' hm c5, NewVecE.same' hm c6, ⟨VecOk.same' hm c7, ?_⟩,
    NewVecE.same' hm c9, by simpa only [BufIn, vecPtr, vecCap, heapNext, hm] using c10, ?_,
    by simpa only [BufIn, vecPtr, vecLen, heapNext, hm] using c12,
    by simpa only [BufIn, vecPtr, vecLen, heapNext, hm] using c13, ?_, ?_, ?_⟩
  · simp only [vecLen, hm] at hi
    obtain ⟨xs, hx⟩ := c4 i (by simpa only [vecLen] using hi)
    exact ⟨xs, by simpa only [vecPtr] using NewVecE.same' hm (by simpa only [vecPtr, hm] using hx)⟩
  · rw [formRowsAt_same hm]
    simpa only [vecPtr, vecLen, hm] using c8
  · simpa only [BufIn, Apart, vecPtr, vecLen, vecCap, heapNext, hm] using c11
  · simpa only [BufIn, formPiece, vecPtr, vecLen, heapNext, hm] using c14
  · simpa only [Apart, formPiece, vecPtr, vecLen, hm] using c15
  · simpa only [vecPtr, vecLen, hm] using c16

end Same

theorem Old.mono {s u t : MachineState} {p : Word} {n : Nat} (h : Old s u p n)
    (hm : heapNext u ≤ heapNext t) : Old s t p n :=
  ⟨h.1, le_trans h.2.1 hm, h.2.2⟩

set_option maxRecDepth 8192 in
/-- The `Layout`'s slots and buffers, kept, hold the same layout. -/
theorem LayoutIn.keep {s u₀ t : MachineState} {L : LayoutMirror.LayoutRust} (hpre : WalkPre s)
    (h : LayoutIn s u₀ L) (hmono : heapNext u₀ ≤ heapNext t)
    (hs : ∀ k : Nat, (1872 + 8 ≤ k ∧ k ≤ 2080) ∨ k = 2456 ∨ k = 2464 →
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 k) = u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k))
    (hh : ∀ x : Word, x.toNat + 8 ≤ heapNext u₀ → t.getMem x = u₀.getMem x) :
    LayoutIn s t L := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have e2456 : t.getMem (s.getReg .x2 - 2456) = u₀.getMem (s.getReg .x2 - 2456) := hs 2456 (by omega)
  have e2464 : t.getMem (s.getReg .x2 - 2464) = u₀.getMem (s.getReg .x2 - 2464) := hs 2464 (by omega)
  have hv (a : Word) (k : Nat) (ha : a = s.getReg .x2 - BitVec.ofNat 64 k) (hk : 1872 + 24 ≤ k ∧ k ≤ 2080) :
      vecPtr t a = vecPtr u₀ a ∧ vecLen t a = vecLen u₀ a := by
    subst ha
    have e8 : s.getReg .x2 - BitVec.ofNat 64 k + 8 = s.getReg .x2 - BitVec.ofNat 64 (k - 8) := by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hk]
    have e16 : s.getReg .x2 - BitVec.ofNat 64 k + 16 = s.getReg .x2 - BitVec.ofNat 64 (k - 16) := by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hk]
    simp only [vecPtr, vecLen, e8, e16]
    exact ⟨hs _ (by omega), hs _ (by omega)⟩
  obtain ⟨tP, tL⟩ := hv (s.getReg .x2 - 2080) 2080 rfl (by omega)
  obtain ⟨pP, pL⟩ := hv (s.getReg .x2 - 1984) 1984 rfl (by omega)
  have ht := h.tables
  have hq := h.heights
  have hp := h.placements
  simp only [Old] at ht hq hp
  exact {
    tables := by rw [e2456]; exact h.tables.mono hmono
    tablesVec := ⟨by rw [e2456, tP]; exact h.tablesVec.1, by rw [tL]; exact h.tablesVec.2⟩
    opcodes := fun i hi ↦ by
      rw [e2456, hh _ (by addr_omega [ht, hi])]; exact h.opcodes i hi
    heights := by rw [e2464]; exact h.heights.mono hmono
    heightsVal := by
      rw [e2464, ← h.heightsVal]
      simp only [Bus.natsAt, readWords_eq_map, List.map_map]
      refine List.map_congr_left fun i hi ↦ ?_
      rw [List.mem_range] at hi
      simp only [Function.comp]
      exact congrArg BitVec.toNat (hh _ (by addr_omega [hq, hi]))
    placements := by rw [pP, pL]; exact h.placements.mono hmono
    placementsVal := by
      rw [pP, pL, placementsAt_congr (fun i hi o ho ↦ hh _ (by addr_omega [hp, hi, ho]))]
      exact h.placementsVal
    logMemory := by rw [show t.getMem (s.getReg .x2 - 1928) = _ from hs 1928 (by omega)]; exact h.logMemory
    qkeccakVars := by
      rw [show t.getMem (s.getReg .x2 - 1912) = _ from hs 1912 (by omega)]; exact h.qkeccakVars
    qkeccakIndex := by
      rw [show t.getMem (s.getReg .x2 - 1904) = _ from hs 1904 (by omega)]; exact h.qkeccakIndex
    stackLog := by rw [show t.getMem (s.getReg .x2 - 1896) = _ from hs 1896 (by omega)]; exact h.stackLog
    keccakLogSteps := by
      rw [show t.getMem (s.getReg .x2 - 1888) = _ from hs 1888 (by omega)]; exact h.keccakLogSteps
    keccakDepth := by
      rw [show t.getMem (s.getReg .x2 - 1880) = _ from hs 1880 (by omega)]; exact h.keccakDepth }

set_option maxRecDepth 8192 in
/-- R16: `verify_bus_balance` from `AtBus` to `AtR17` (`0x800035f0`), or the `Err` return, or a
dead end. -/
theorem r16 {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hBB : BusBalanceSpec BcOk bev)
    (hBW : BcWalk BcOk bev) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ c : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s) (hpc : c.pc = 0x80006428)
    (h : AtBus OI s u₀ c A k R Q B lo lo2) :
    ∃ t, Reaches Image.code c t ∧ ((∃ bus, AtR17 OI s t (layoutOf A k) (rowsOf A) (rateOf A) bus) ∨
      Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := h.inv
  have H := h.at15.keep.at11.base
  obtain ⟨y, hr, ⟨hpcy, hpy, post⟩ | hd⟩ := hBB.call (Reaches.refl c) hpc (busPre hBW hpre h)
  swap
  · exact ⟨y, hr, Or.inr (Or.inr hd)⟩
  have stc := busCallStep hpre I h.x10 h.x12 post (hpy .x2 (by decide))
  have stc' : StepW s c y (W15 s) True := stc.weaken (fun _ ha ↦ Or.inl ha) id
  have st : StepW s u₀ y (W15 s) True :=
    (h.st.trans stc').weaken (fun _ ha ↦ ha.elim id id) fun _ ↦ trivial
  have Iy : Inv s y := I.stepW hpre (fun a ha ↦ W15.inF hpre ha) stc'
  have spy : y.getReg .x2 = s.getReg .x2 - 2656 := Iy.sp
  have pcy : y.pc = 0x800035dc := by rw [hpcy, returnAddress_eq, h.x1]; decide
  obtain ⟨t, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800035dc_spec pcy (by
    rv_eval [spy]; and_intros <;> valid_access hval [hb1])
  have m₁ := b800035dc_mem_same h₁
  have k₁ := b800035dc_keeps h₁
  have e1728 : y.getReg .x2 + 1728 = s.getReg .x2 - 928 := by
    rw [spy]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x21y : y.getReg .x21 = s.getReg .x10 := by rw [hpy .x21 (by decide), h.x21]
  have x21 : t.getReg .x21 = s.getReg .x10 := by rw [k₁ .x21 (by decide), x21y]
  have stt := st.ext15 Iy.heap m₁ (k₁ .x2 (by decide))
  have It : Inv s t := Iy.same m₁ (k₁ .x2 (by decide))
  by_cases he : y.getMem (y.getReg .x2 + 1728) = (0xffffffffffffffff : Word)
  · -- `Err`: copied to the result
    have hR := hpre.out
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80003ea0_spec (b800035dc_pc_taken h₁ he) (by
      rv_eval [x21]
      and_intros <;> exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR])
        (by addr_omega [hR]))
    have fr := b80003ea0_frame h₂ (by rw [x21]; addr_omega [hR])
    rw [x21] at fr
    obtain ⟨t₃, hr₃, ht⟩ := errRes hDL hpre h.at15 It stt fr (b80003ea0_keeps h₂ .x2 (by decide))
      (b80003ea0_pc h₂) (by rw [← x21, b80003ea0_m_x21_0 h₂, b800035dc_x10 h₁]; rfl)
    exact ⟨t₃, hr.trans (hr₁.trans (hr₂.trans hr₃)), Or.inr ht⟩
  -- `Ok`: the bus, one for every transcript
  have hok : vecCap y (s.getReg .x2 - 928) ≠ errNiche := by rw [vecCap, ← e1728]; exact he
  have hargs := busArgs hBW hpre h
  have run : ∀ T, TranscriptAt c (tp s) T → ∃ r T',
      (verifyBusBalanceM (evaluateRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)))
        ((layoutOf A k).toSpec [])).run T = some (r, T') ∧
      BusResultAt c y (s.getReg .x2 - 928) r ∧ TranscriptAt y (tp s) T' := by
    intro T hT
    have hv := post.value T (by rw [h.x12]; exact hT)
    rw [hargs, h.x10, h.x12] at hv
    generalize (verifyBusBalanceM (evaluateRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)))
      ((layoutOf A k).toSpec [])).run T = o at hv ⊢
    rcases o with _ | ⟨r, T'⟩
    · exact absurd hv hok
    · exact ⟨r, T', rfl, hv.2.1, hv.2.2⟩
  obtain ⟨T₀, hT₀⟩ := transcriptAt_ex c (tp s)
  obtain ⟨bus, -, -, hbus, -⟩ := run T₀ hT₀
  have hbt : BusResultAt s t (s.getReg .x2 - 928) bus :=
    BusResultAt.same m₁ (BusResultAt.widen hbus I.mono)
  have sl (k' : Nat) (hk : 104 + 8 ≤ k' ∧ k' ≤ 2656)
      (hn : (k' ≤ 808 ∨ 928 + 8 ≤ k') ∧ (k' ≤ 1768 ∨ 1800 + 8 ≤ k') ∧ (k' ≤ 2088 ∨ 2440 + 8 ≤ k')) :
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 k') = u₀.getMem (s.getReg .x2 - BitVec.ofNat 64 k') :=
    stt.slot15 hpre hk hn
  have hpm := H.spills
  have e856 : s.getReg .x2 - 928 + 72 = s.getReg .x2 - 856 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e880 : s.getReg .x2 - 928 + 48 = s.getReg .x2 - 880 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fI := hbt.formsIn
  have fR := hbt.formRows
  rw [e856] at fI fR
  -- the root, kept through the call
  have hroot : PcsContracts.digestAt t (s.getReg .x2 - 1800) =
      PcsContracts.digestAt c (s.getReg .x2 - 1800) := by
    simp only [PcsContracts.digestAt]
    congr 1
    funext i
    rw [m₁, stc.getF hpre (by have := i.isLt; constructor <;> addr_omega [hb1])
      (fun j hj hw ↦ by have := i.isLt; simp only [Within] at hw; addr_omega [hw, hj, hb1])
      (fun _ ↦ by have := i.isLt; rw [tp]; addr_omega [hb1])]
  have hbtr := h.tracks
  rw [hroot.symm] at hbtr
  refine ⟨t, hr.trans hr₁, Or.inl ⟨bus, {
    pc := b800035dc_pc_not_taken h₁ he
    inv := It
    proofPtr := by
      rw [show tp s = s.getReg .x2 - BitVec.ofNat 64 2448 from rfl, sl 2448 (by omega) (by omega)]
      exact H.proofPtr
    checked := by
      rw [byteAt_congr (by rw [tp]; addr_omega [hb1, hb3])
        (show t.getMem (tp s + 360) = u₀.getMem (tp s + 360) by
          rw [show tp s + 360 = s.getReg .x2 - BitVec.ofNat 64 2088 by
            rw [tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
          exact sl 2088 (by omega) (by omega))]
      exact H.checked
    x21 := x21
    x22 := by rw [k₁ .x22 (by decide), hpy .x22 (by decide), h.x22]
    x23 := by rw [k₁ .x23 (by decide), hpy .x23 (by decide), h.x23]
    x27 := by rw [k₁ .x27 (by decide), hpy .x27 (by decide), h.x27]
    x19 := by rw [b800035dc_x19 h₁, e1728, m₁]
    x11 := by
      rw [b800035dc_x11 h₁, m₁, spy]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x25 := by
      rw [b800035dc_x25 h₁, m₁, spy]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    rate := by rw [show t.getMem (s.getReg .x2 - 2584) = _ from sl 2584 (by omega) (by omega)]; exact hpm.1
    sret := by
      rw [show t.getMem (s.getReg .x2 - 2488) = _ from sl 2488 (by omega) (by omega)]
      exact hpm.2.2.2.2.2.2.2.2
    pi0 := by
      rw [show t.getMem (s.getReg .x2 - 2568) = _ from sl 2568 (by omega) (by omega)]; exact hpm.2.2.1
    pi1 := by
      rw [show t.getMem (s.getReg .x2 - 2552) = _ from sl 2552 (by omega) (by omega)]
      exact hpm.2.2.2.2.1
    pi2 := by
      rw [show t.getMem (s.getReg .x2 - 2576) = _ from sl 2576 (by omega) (by omega)]; exact hpm.2.1
    pi3 := by
      rw [show t.getMem (s.getReg .x2 - 2560) = _ from sl 2560 (by omega) (by omega)]
      exact hpm.2.2.2.1
    busOk := by rw [vecCap, m₁, ← e1728]; exact he
    busAt := hbt
    forms := ⟨fun i hi ↦ by
        have := (fR i hi).2 3 (le_refl _)
        simp only [formPiece, lt_irrefl, ↓reduceIte] at this
        exact this,
      fun i hi j hj ↦ by
        have h3 := (fR i hi).1
        rw [h3] at hj
        have hj3 : j < 3 := by simp at hj; omega
        have := (fR i hi).2 j (by omega)
        simp only [formPiece, hj3, ↓reduceIte] at this
        exact this⟩
    tags := by have := hbt.formTags; rw [e856] at this; exact this
    pointOld := by have := hbt.pointIn; rw [e880] at this; exact this
    claimsOld := hbt.claimsIn
    claimPoints := fun i hi ↦ (hbt.claimPoints i hi).1
    formsBuf := fI
    claimsApart := fun i hi ↦ (hbt.claimPoints i hi).2
    layoutIn := h.at15.layoutIn.keep hpre stt.mono
      (fun k' hk ↦ sl k' (by omega) (by omega)) fun x hx ↦ stt.heapKeep hpre hx
    build := ⟨H.rowsLen, _, _, buildLayout_eq H.ok⟩
    stack := h.at15.stack
    rateOk := by
      have hr := H.rate
      simp only [BitVec.le_def] at hr
      exact hr
    tracks := by
      rw [afterRoot] at hbtr
      refine TracksR.bind hbtr (keeps_verifyBusBalanceM _ _) fun T hT ↦ ?_
      obtain ⟨r, T', e, hrr, hT'⟩ := run T hT
      have er : r = bus := BusResultAt.unique (BusResultAt.widen hrr I.mono) (BusResultAt.widen hbus I.mono)
      subst er
      exact ⟨T', e, TranscriptAt.same hpre Iy (by
        rw [show tp s = s.getReg .x2 - BitVec.ofNat 64 2448 from rfl,
          st.slot15 hpre (by omega) (by omega)]; exact H.proofPtr) m₁ hT'⟩ }⟩⟩

/-- R15 and R16: from `AtR15` (`0x800034c0`) to `AtR17` (`0x800035f0`), or an `Err` return, or a
dead end. -/
theorem r1516 {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hNS : NextScalarsSpec)
    (hBB : BusBalanceSpec BcOk bev) (hBW : BcWalk BcOk bev) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s) (hpc : u₀.pc = 0x800034c0)
    (h : AtR15 OI s u₀ A k R Q B lo lo2) :
    ∃ t, Reaches Image.code u₀ t ∧ ((∃ layout rows lir bus, AtR17 OI s t layout rows lir bus) ∨
      Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨c, hr, hd | hd | ⟨hpc₁, hc⟩⟩ := r15 hNS hDL hpre hpc h
  · exact ⟨c, hr, Or.inr (Or.inl hd)⟩
  · exact ⟨c, hr, Or.inr (Or.inr hd)⟩
  obtain ⟨t, hr', ht | ht | ht⟩ := r16 hBB hBW hDL hpre hpc₁ hc
  · obtain ⟨bus, hb⟩ := ht
    exact ⟨t, hr.trans hr', Or.inl ⟨_, _, _, bus, hb⟩⟩
  · exact ⟨t, hr.trans hr', Or.inr (Or.inl ht)⟩
  · exact ⟨t, hr.trans hr', Or.inr (Or.inr ht)⟩

end Rv64Verifier.Proofs.Walk
