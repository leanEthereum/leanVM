import Rv64Verifier.Proofs.Walk.R15A

/-!
# `walk` R15: the root's bytes, to `verify_bus_balance`'s call

`0x80003514` copies the scalars' words and stores the root's bytes at `S - 1800` byte by byte
(`merge_w`, `merge_ws`, `merge_b`, `merge_b7`: the stores rebuild each doubleword), then calls
`verify_bus_balance` (`AtBus`, at `0x80006428`). The mirror's `TM.commit` is `next_scalars(2)` and
`Digest::from_halves` (`commit_run`); from here the transcript has one root (`TracksR`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.KeccakHash Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem merge_w (old w : Word) :
    replaceWord32 (replaceWord32 old (0 / 4) (BitVec.truncate 32 w)) (4 / 4)
      (BitVec.truncate 32 (w >>> 32)) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceWord32, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem merge_ws (old w : Word) :
    replaceWord32 (replaceWord32 old (0 / 4) (BitVec.truncate 32 w)) (4 / 4)
      (BitVec.truncate 32 (BitVec.signExtend 64 (extractWord32 w (4 / 4)))) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceWord32, extractWord32, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.truncate_eq_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_signExtend]
  interval_cases i <;> simp

theorem merge_b (old w : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
      (replaceByte old 2 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 2))))
      3 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 3))))
      4 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 4))))
      5 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 5))))
      0 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 0))))
      1 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 1))))
      6 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 6))))
      7 (BitVec.truncate 8 (w >>> 56)) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_ushiftRight, getLsbD_extractByte]
  interval_cases i <;> simp

theorem merge_b7 (old w : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
      (replaceByte old 2 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 2))))
      3 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 3))))
      4 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 4))))
      5 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 5))))
      0 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 0))))
      1 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 1))))
      6 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 6))))
      7 (BitVec.truncate 8 (BitVec.zeroExtend 64 (extractByte w 7))) = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.truncate_eq_setWidth,
    getLsbD_extractByte]
  interval_cases i <;> simp

/-- The root `Digest::from_halves` makes of the scalars at `p` and `p + 24`. -/
def rootOf (u : MachineState) (p : Word) : Digest :=
  #v[((eAt u p).limb 0).lane, ((eAt u p).limb 1).lane, ((eAt u (p + 24)).limb 0).lane,
    ((eAt u (p + 24)).limb 1).lane]

theorem fromHalves_root (u : MachineState) (p : Word) (h0 : u.getMem (p + 16) = 0)
    (h1 : u.getMem (p + 40) = 0) :
    digestFromHalves (eAt u p, eAt u (p + 24)) = some (rootOf u p) := by
  have c0 : IsCanonical128 (eAt u p) := by
    show BF64.ofBitVec (u.getMem (p + 16)) = 0
    rw [h0]; rfl
  have c1 : IsCanonical128 (eAt u (p + 24)) := by
    show BF64.ofBitVec (u.getMem (p + 24 + 16)) = 0
    rw [BitVec.add_assoc, show (24 : Word) + 16 = 40 from rfl, h1]; rfl
  simp only [digestFromHalves, c0, c1, and_self, ite_true]
  rfl

/-- The root at `a`, its doublewords the halves' low limbs. -/
theorem digestAt_root {c w : MachineState} {a P : Word} (h0 : c.getMem a = w.getMem P)
    (h1 : c.getMem (a + 8) = w.getMem (P + 8)) (h2 : c.getMem (a + 16) = w.getMem (P + 24))
    (h3 : c.getMem (a + 24) = w.getMem (P + 24 + 8)) : PcsContracts.digestAt c a = rootOf w P := by
  apply Vector.ext
  intro i hi
  simp only [PcsContracts.digestAt, Vector.getElem_ofFn]
  interval_cases i
  · show UInt64.ofBitVec (c.getMem (a + BitVec.ofNat 64 0)) = _
    rw [BitVec.add_zero, h0]; rfl
  · show UInt64.ofBitVec (c.getMem (a + 8)) = _
    rw [h1]; rfl
  · show UInt64.ofBitVec (c.getMem (a + 16)) = _
    rw [h2]; rfl
  · show UInt64.ofBitVec (c.getMem (a + 24)) = _
    rw [h3]; rfl

/-- What `walk` runs once the root is read: the bus, then `tailRust`. -/
def afterRoot (s : MachineState) (A : List E) (k : Nat) : TM SummaryRust :=
  verifyBusBalanceM (evaluateRust (Proofs.Bytecode.readBytecode s (s.getReg .x11)))
    ((layoutOf A k).toSpec []) >>= fun bus ↦
      tailRust (bytesAt s (s.getReg .x12) 32) (layoutOf A k) (rowsOf A) (rateOf A) bus

/-- The root's shape. -/
def shape15 (A : List E) (k : Nat) : ℕ × ℕ :=
  stackShape (layoutOf A k).stackLog (rateOf A).toNat

/-- Past `next_scalars(2)` and the high limbs' check, the mirror has read the root. -/
theorem tracks15 {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} {P : Word}
    (h : AtR15 OI s u₀ A k R Q B lo lo2) (N : NS15 s u₀ w)
    (hP : vecPtr w (s.getReg .x2 - 928) = P) (hcap : vecCap w (s.getReg .x2 - 928) ≠ errNiche)
    (hl : 2 ≤ (vecLen w (s.getReg .x2 - 928)).toNat) (z0 : w.getMem (P + 16) = 0)
    (z1 : w.getMem (P + 40) = 0) :
    TracksR OI s w ((rootOf w P), shape15 A k) (afterRoot s A k) := by
  intro proof hp
  obtain ⟨T, e, er, hT, hr⟩ := h.tracks proof hp
  rw [bodyRest_tail] at hr
  have hv := N.value T hT
  generalize ho : (TM.nextScalars 2).run T = o at hv
  rcases o with _ | ⟨xs, T'⟩
  · exact absurd hv hcap
  obtain ⟨-, hn, hT'⟩ := hv
  have hx := hn.elems
  simp only [vecEs, hP] at hx
  have g0 : xs.getD 0 0 = eAt w P := by
    rw [← hx, eListAt_getD (by omega)]; simp
  have g1 : xs.getD 1 0 = eAt w (P + 24) := by
    rw [← hx, eListAt_getD (by omega)]; rfl
  have hc : (TM.commit (stackShape (layoutOf A k).stackLog (rateOf A).toNat).1
      (stackShape (layoutOf A k).stackLog (rateOf A).toNat).2).run T =
      some (rootOf w P, { T' with roots := T.roots ++ [(rootOf w P, shape15 A k)] }) := by
    rw [commit_run, ho, Option.bind_some, g0, g1, fromHalves_root w P z0 z1]
    rfl
  refine ⟨{ T' with roots := T.roots ++ [(rootOf w P, shape15 A k)] }, ?_, by rw [er]; rfl,
    ⟨hT'.stream, hT'.sponge, hT'.streamOffset, hT'.openingOffset⟩, ?_⟩
  · exact (KeepsProof.nextScalars 2 ho).1.trans e
  · rw [hr, StateT.run_bind, hc]
    rfl

theorem valid4 {a x : Word} {n : Nat} (h : Mapped a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 4 ≤ a.toNat + n) (h3 : x.toNat % 4 = 0) : Sym.validAccess 4 x = true := by
  simp only [Sym.validAccess, isValidMemAccess, isValidMemAddr_eq, isAligned4, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [Mapped] at h
  omega

theorem frameMapped {s : MachineState} (hpre : WalkPre s) : Mapped (s.getReg .x2 - 11392) 11392 := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hm := hpre.stack.mapped (by decide) (by decide)
  rw [stackLo_eq, stack_eq] at hm
  simp only [Mapped]; addr_omega [hm, hb1, hb3]

/-- At `verify_bus_balance`'s call (`0x80006428`): `a0` the result at `S - 928`, `a1` the `Layout`,
`a2` the transcript, the root at `S - 1800`. -/
structure AtBus (OI : MachineState → Word → List (List Opening) → Prop) (s u₀ c : MachineState)
    (A : List E) (k : Nat) (R Q B : Word) (lo lo2 : Nat) : Prop where
  at15 : AtR15 OI s u₀ A k R Q B lo lo2
  inv : Inv s c
  st : StepW s u₀ c (W15 s) True
  x1 : c.getReg .x1 = 0x800035dc
  x10 : c.getReg .x10 = s.getReg .x2 - 928
  x11 : c.getReg .x11 = s.getReg .x2 - 2080
  x12 : c.getReg .x12 = tp s
  x21 : c.getReg .x21 = s.getReg .x10
  x22 : c.getReg .x22 = s.getReg .x2 - 512
  x23 : c.getReg .x23 = tp s + 8
  x27 : c.getReg .x27 = 6
  tracks : TracksR OI s c (PcsContracts.digestAt c (s.getReg .x2 - 1800), shape15 A k)
    (afterRoot s A k)

set_option maxRecDepth 8192 in
/-- `0x80003514`: the root's bytes, then `verify_bus_balance`'s call. -/
theorem r15root {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ w v : MachineState}
    {A : List E} {k : Nat} {R Q B : Word} {lo lo2 : Nat} {P : Word} (hpre : WalkPre s)
    (h : AtR15 OI s u₀ A k R Q B lo lo2) (hpc : v.pc = 0x80003514) (M : Mid15 s u₀ w v P) :
    ∃ c, Reaches Image.code v c ∧ c.pc = 0x80006428 ∧ AtBus OI s u₀ c A k R Q B lo lo2 := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hfm := frameMapped hpre
  have N := M.ns
  have Iv : Inv s v := N.inv.same M.mem M.sp
  have sp : v.getReg .x2 = s.getReg .x2 - 2656 := Iv.sp
  have hP := M.buf
  have hwh := N.inv.heap.hi
  have hul := h.keep.at11.base.inv.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hwh hul hP
  have hreg : Region P 48 := ⟨by simp only [Mapped]; omega, hP.1⟩
  obtain ⟨c, hr, h₁⟩ := Sym.BlockSpec.reaches b80003514_spec hpc (by
    rv_eval [sp, M.x10]
    and_intros <;> first
      | exact Region.valid hreg (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
      | valid_access hval [hb1]
      | exact frameByte hpre (by addr_omega [hb1]) (by addr_omega [hb1])
      | exact valid4 hfm (by addr_omega [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1, hb3])
      | addr_omega [hb1, hb3])
  have k₁ := b80003514_keeps h₁
  have st₁ : StepW s v c (W15 s) False := StepW.ofFrame hpre Iv.heap (h₁.dframe (by
      rv_eval [sp]
      and_intros <;> simp only [W15, Within] <;> first
        | exact Or.inl ⟨by addr_omega [hb1], by addr_omega [hb1]⟩
        | exact Or.inr ⟨by addr_omega [hb1], by addr_omega [hb1]⟩))
    (fun a ha ↦ W15.inF hpre ha) (k₁ .x2 (by decide))
  have stv := N.st.ext15 N.inv.heap M.mem M.sp
  have st : StepW s u₀ c (W15 s) True :=
    (stv.trans st₁).weaken (fun _ ha ↦ ha.elim id id) fun ht ↦ ht.elim id False.elim
  have Ic : Inv s c := Iv.stepW hpre (fun a ha ↦ W15.inF hpre ha) st₁
  -- the root's doublewords
  have m0 : c.getMem (v.getReg .x2 + 880) = (b80003514.mem[0]'(by decide)).2.eval v :=
    h₁.mem_eq 0 (by decide) (by rv_eval []) rfl
  have m1 : c.getMem (v.getReg .x2 + 872) = (b80003514.mem[1]'(by decide)).2.eval v :=
    h₁.mem_eq 1 (by decide) (by rv_eval []) rfl
  have m2 : c.getMem (v.getReg .x2 + 864) = (b80003514.mem[2]'(by decide)).2.eval v :=
    h₁.mem_eq 2 (by decide) (by rv_eval []) rfl
  have m3 : c.getMem (v.getReg .x2 + 856) = (b80003514.mem[3]'(by decide)).2.eval v :=
    h₁.mem_eq 3 (by decide) (by rv_eval []) rfl
  rv_eval [] at m0 m1 m2 m3
  rw [merge_w] at m0
  rw [merge_b] at m1
  rw [merge_b7] at m2
  rw [merge_ws] at m3
  have hroot : PcsContracts.digestAt c (s.getReg .x2 - 1800) = rootOf w P := by
    refine digestAt_root ?_ ?_ ?_ ?_
    · rw [show s.getReg .x2 - 1800 = v.getReg .x2 + 856 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m3, M.x10, M.mem]
    · rw [show s.getReg .x2 - 1800 + 8 = v.getReg .x2 + 864 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m2, M.x10, M.mem]
    · rw [show s.getReg .x2 - 1800 + 16 = v.getReg .x2 + 872 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m1, M.x10, M.mem]
    · rw [show s.getReg .x2 - 1800 + 24 = v.getReg .x2 + 880 by
        rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m0, M.x10, M.mem,
        BitVec.add_assoc]
      rfl
  have etp : tp s = s.getReg .x2 - BitVec.ofNat 64 2448 := rfl
  have ptrv : v.getMem (tp s) = s.getReg .x13 := by
    rw [etp, stv.slot15 hpre (by omega) (by omega)]
    exact h.keep.at11.base.proofPtr
  have ptrw : w.getMem (tp s) = s.getReg .x13 := by rw [← M.mem]; exact ptrv
  have tr := tracks15 h N M.ptr M.cap M.len M.z0 M.z1
  refine ⟨c, hr, b80003514_pc h₁, {
    at15 := h
    inv := Ic
    st := st
    x1 := b80003514_x1 h₁
    x10 := by rw [b80003514_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := by rw [b80003514_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x12 := by rw [b80003514_x12 h₁, sp, tp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x21 := by rw [k₁ .x21 (by decide)]; exact M.x21
    x22 := by rw [k₁ .x22 (by decide)]; exact M.x22
    x23 := by rw [k₁ .x23 (by decide)]; exact M.x23
    x27 := by rw [k₁ .x27 (by decide)]; exact M.x27
    tracks := by
      rw [hroot]
      refine tr.keep fun T hT ↦ StepW.transcript hpre Iv ptrv (fun a ha ↦ ⟨W15.inF hpre ha, ?_⟩) st₁
        (TranscriptAt.same hpre N.inv ptrw M.mem hT)
      simp only [W15, Within, tp] at ha ⊢
      rcases ha with ha | ha <;> addr_omega [ha, hb1] }⟩

/-- R15: from `AtR15` (`0x800034c0`) to `verify_bus_balance`'s call, or an `Err` return, or a
dead end. -/
theorem r15 (hNS : NextScalarsSpec) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ : MachineState} {A : List E}
    {k : Nat} {R Q B : Word} {lo lo2 : Nat} (hpre : WalkPre s) (hpc : u₀.pc = 0x800034c0)
    (h : AtR15 OI s u₀ A k R Q B lo lo2) :
    ∃ c, Reaches Image.code u₀ c ∧ (Done OI s c ∨ Dead Image.code c ∨
      (c.pc = 0x80006428 ∧ AtBus OI s u₀ c A k R Q B lo lo2)) := by
  obtain ⟨w, hr₁, ⟨hpc₁, N⟩ | hd⟩ := r15call hNS hpre hpc h
  swap
  · exact ⟨w, hr₁, Or.inr (Or.inl hd)⟩
  obtain ⟨v, hr₂, hd | hd | ⟨hpc₂, M⟩⟩ := r15branch hDL hpre h hpc₁ N
  · exact ⟨v, hr₁.trans hr₂, Or.inl hd⟩
  · exact ⟨v, hr₁.trans hr₂, Or.inr (Or.inl hd)⟩
  obtain ⟨c, hr₃, hpc₃, hc⟩ := r15root hpre h hpc₂ M
  exact ⟨c, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr ⟨hpc₃, hc⟩)⟩

end Rv64Verifier.Proofs.Walk
