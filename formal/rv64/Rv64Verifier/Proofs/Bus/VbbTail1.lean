import Rv64Verifier.Proofs.Bus.VbbSpine

/-!
# `verify_bus_balance` past the GKR loop: the mirror's rest, the `Err` exit through `s2`, the check

`tailRest` is `vbbTail` past the transcript's last read (`vbbTail_eq`). From `0x80006b60`, a
block that stores `Err` through `s2` jumps to the epilogue at `0x80007114` (`errDoneAt`). In checked
mode a zero count's root exits with `Err` (`12`); the slices `point[..log_memory]` and
`point[..log_bytecode]` trap when the point is shorter (`checkStep`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The mirror past the transcript -/

/-- `vbbTail` from the three scalars on. -/
def tailRest (bytecodeEvaluate : List E → Option E) (layout : Layout) (alphas : List E) (beta : E)
    (state : GkrState) (memory : List E) (memoryFinal bytecodeFinal : E) : TM BusResultRust := do
  let point := state.point
  let treeValues := state.values
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayoutRust frameworkLogRows layout.push
  let pullLayout := busLayoutRust frameworkLogRows layout.pull
  let countLayout := busLayoutRust [] layout.count
  let weights := eqKernelRust alphas
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let claims : List ColumnClaim :=
    [memory0, memory1, memory2].map (fun column ↦ ⟨column, memoryLow, memory.getD column 0⟩) ++
      [⟨memoryFinalCounters, memoryLow, memoryFinal⟩,
        ⟨bytecodeFinalCounters, bytecodeLow, bytecodeFinal⟩]
  let memoryIndex := indexMleRust memoryLow
  let bytecodeIndex := indexMleRust bytecodeLow
  let bytecodePoint := bytecodeLow ++ alphas
  let bytecodeValue ← TM.lift (bytecodeEvaluate bytecodePoint)
  let fingerprints := fun (pc memoryCount bytecodeCount : E) ↦
    [dotRust (weights.take 3) [sepStateRust, pc, gpowRust 0#64],
      dotRust (weights.take 6) [sepMemRust, memoryIndex, memoryCount, memory.getD 0 0,
        memory.getD 1 0, memory.getD 2 0],
      dotRust (weights.take 3) [sepBytecodeRust, bytecodeIndex, bytecodeCount] + bytecodeValue]
  let finalPc := gpowRust ((1#64 <<< (layout.logBytecode % 64)) - 1#64)
  let sides : List (List BusBlock × BusLayoutRust × List E × List E × E) :=
    [(layout.push, pushLayout, fingerprints (gpowRust 0#64) 1 1, weights, beta),
      (layout.pull, pullLayout, fingerprints finalPc memoryFinal bytecodeFinal, weights, beta),
      (layout.count, countLayout, [], [1], 0)]
  let r := sides.zipIdx.foldl (fun (acc : List (List Form) × List E) sd ↦
      let side := sideStepRust point treeValues acc.1 sd.2 sd.1.1 sd.1.2.1 sd.1.2.2.1 sd.1.2.2.2.1
        sd.1.2.2.2.2
      (side.1, acc.2 ++ [side.2]))
    (List.replicate tables.length (List.replicate 3 {}), [])
  pure ⟨claims, bytecodePoint, point, r.1, r.2⟩

theorem vbbTail_eq (bytecodeEvaluate : List E → Option E) (layout : Layout) (alphas : List E)
    (beta count : E) (state : GkrState) :
    vbbTail bytecodeEvaluate layout alphas beta count state =
      (TM.require (count ≠ 0) >>= fun _ ↦ TM.nextScalars 3 >>= fun memory ↦
        TM.nextScalar >>= fun memoryFinal ↦ TM.nextScalar >>= fun bytecodeFinal ↦
          tailRest bytecodeEvaluate layout alphas beta state memory memoryFinal bytecodeFinal) :=
  rfl

/-- What runs from the three scalars on. -/
def rest (bev : MachineState → Word → List E → Option E) (s : MachineState) (k : Start)
    (state : GkrState) (memory : List E) (memoryFinal bytecodeFinal : E) : TM BusResultRust :=
  tailRest (bev s (bytecodeOf s (s.getReg .x11))) (busLayoutAt s (s.getReg .x11)) k.alphas k.beta
    state memory memoryFinal bytecodeFinal

/-! ## Limbs -/

theorem eOf3_eq_zero (a b c : Word) : eOf3 a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  have hl : Model.limbs (eOf3 a b c) = (a, b, c) := by
    rw [eOf3, limbs_ofLimbs]; simp only [BF64.toBitVec_ofBitVec]
  constructor
  · intro h
    have := congrArg Model.limbs h
    rw [hl, Model.limbs_zero] at this
    simp only [Model.lzero, Prod.mk.injEq] at this
    exact this
  · rintro ⟨rfl, rfl, rfl⟩
    exact eq_of_limbs (by rw [hl, Model.limbs_zero]; rfl)

theorem or3_eq_zero (a b c : Word) : (a ||| b) ||| c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [show (0 : Word) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, and_assoc]

/-! ## The `Err` exit through `s2` -/

/-- A block that wrote `errNiche` through `s2` and jumped to the epilogue: the function returns
`Err`, what the mirror gives when it fails. -/
theorem errDoneAt {bev : MachineState → Word → List E → Option E} {s u v : MachineState} {n : Nat}
    (hpre : BusBalancePre s) (h : Inv s u) (hx18 : u.getReg .x18 = s.getReg .x10) (hn : n ≤ 120)
    (fr : MemFrame u v (u.getReg .x18) n) (sp : v.getReg .x2 = u.getReg .x2)
    (hpc : v.pc = 0x80007114) (hcap : v.getMem (u.getReg .x18) = 0xffffffffffffffff)
    (hnone : ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ t, Reaches Image.code v t ∧ Done bev s t := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have ho := hpre.out
  have hos := hpre.outStack
  have hof := hpre.outFree
  rw [stackLo_eq] at hos
  have fr' := DFrame.of_memFrame fr
  rw [hx18] at fr' hcap
  have hn' : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr' nextAddr fun i hi hw ↦ by addr_omega [hof.2, hw, hi, hn])
  have I : Inv s v := h.step hpre fr' (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hn]),
      by addr_omega [ha, hos, hb1, hn]⟩) ⟨hn' ▸ h.heap.lo, hn' ▸ h.heap.hi⟩ hn'.ge sp
  obtain ⟨t, hr, ex, hm⟩ := exit hpre I hpc
  refine ⟨t, hr, ex.pc, ex.preserves, ex.heap, ex.mono, fun T hT ↦ ?_, ex.frame⟩
  rw [show (verifyBusBalanceM (bev s (bytecodeOf s (s.getReg .x11)))
      (busLayoutAt s (s.getReg .x11))).run T = none from hnone T hT]
  show vecCap t (s.getReg .x10) = errNiche
  rw [vecCap, hm, hcap]
  rfl

/-! ## Checked mode, the count's root, the slices -/

/-- The transcript's `checked` byte is not written. -/
theorem Inv.checkedWord {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) :
    u.getMem (s.getReg .x12 + 360) = s.getMem (s.getReg .x12 + 360) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS := hpre.self.self
  have so := hpre.selfOut
  have ss := hpre.selfStack
  have sf := hpre.selfFree
  have hn := h.heap.hi
  rw [stackLo_eq, stack_eq] at ss
  simp only [Outside, heapNext, heapEnd] at sf hn
  refine h.frame _ fun i hi hw ↦ ?_
  simp only [W, Fresh, heapNext, stackLo_eq] at hw
  rcases hw with hw | hw | hw | hw | hw
  · addr_omega [hi, hw, so, hS]
  · addr_omega [hi, hw, hS]
  · addr_omega [hi, hw, ss, hS]
  · addr_omega [hi, hw, sf, hS]
  · addr_omega [hi, hw, sf, hn, hS]

/-- At `0x80006ba0`, the first `next_scalars`' setup: the count's root is not zero and the point
covers both slices; or the function has returned `Err`, or the run trapped. -/
theorem checkStep {bev : MachineState → Word → List E → Option E} {s u : MachineState} {k : Start}
    {cnt : E} {state : GkrState} (hpre : BusBalancePre s) (G : AfterGkr bev s u k cnt state)
    (hpc : u.pc = 0x80006b60) :
    ∃ w, Reaches Image.code u w ∧ (Done bev s w ∨ Dead Image.code w ∨
      (w.pc = 0x80006ba0 ∧ (∀ a, w.getMem a = u.getMem a) ∧
        (∀ r ∈ ([.x1, .x2, .x8, .x9, .x11, .x12, .x13, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
          .x25, .x26, .x27] : List Reg), w.getReg r = u.getReg r) ∧
        cnt ≠ 0 ∧ (logMem s).toNat ≤ (u.getReg .x21).toNat ∧
        (logBc s).toNat ≤ (u.getReg .x21).toNat)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hS := hpre.self.self
  have sp := G.inv.sp
  have hck : extractByte (u.getMem (s.getReg .x12 + 360)) 0 ≠ 0 := by
    have hc := hpre.checked
    rwa [← Transcript.add_ofNat_zero (s.getReg .x12 + 360),
      Runtime.byteAt_add (by addr_omega [hS]) (by decide), ← G.inv.checkedWord hpre] at hc
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006b60_spec hpc (by
    rv_eval [G.x20]
    exact ⟨by addr_omega [hS], Mapped.valid hS.1 (i := 360) (by decide)⟩)
  have k₁ := b80006b60_keeps h₁
  have m₁ := b80006b60_mem_same h₁
  have pc₁ : u₁.pc = 0x80006b68 := Sym.Expect.Holds.pc_eq h₁ (by
    rv_eval [G.x20]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006b68_spec pc₁ trivial
  have k₂ := b80006b68_keeps h₂
  have m₂ := b80006b68_mem_same h₂
  have e11 : u₁.getReg .x11 = k.count0 := (k₁ .x11 (by decide)).trans G.x11
  have e12 : u₁.getReg .x12 = k.count1 := (k₁ .x12 (by decide)).trans G.x12
  have e13 : u₁.getReg .x13 = u.getReg .x13 := k₁ .x13 (by decide)
  have htr := G.tracks
  simp only [tail, vbbTail_eq] at htr
  by_cases hz : (u₁.getReg .x11 ||| u₁.getReg .x12) ||| u₁.getReg .x13 = 0
  · -- the count's root is zero: `Err(BusCountZero)`
    have pc₂ := b80006b68_pc_not_taken h₂ hz
    have hc0 : cnt = 0 := by
      rw [G.cntEq, eOf3_eq_zero, ← e11, ← e12, ← e13]
      exact (or3_eq_zero _ _ _).mp hz
    have x18₂ : u₂.getReg .x18 = s.getReg .x10 := by
      rw [k₂ .x18 (by decide), k₁ .x18 (by decide), G.x18]
    have ho := hpre.out
    obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006b74_spec pc₂ (by
      rv_eval [x18₂]
      and_intros <;> exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho])
        (by addr_omega [ho]))
    have I₂ := (G.inv.same m₁ (k₁ .x2 (by decide))).same m₂ (k₂ .x2 (by decide))
    obtain ⟨t, hrt, hdone⟩ := errDoneAt (bev := bev) hpre I₂ x18₂ (by omega)
      (b80006b74_frame h₃ (by rw [x18₂]; addr_omega [ho])) ((b80006b74_keeps h₃) .x2 (by decide))
      (b80006b74_pc h₃) (b80006b74_m_x18_0 h₃)
      (htr.require_fail (by rw [hc0]; exact fun h ↦ h rfl))
    exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hrt)), Or.inl hdone⟩
  have pc₂ := b80006b68_pc_taken h₂ hz
  have hc : cnt ≠ 0 := by
    rw [G.cntEq, Ne, eOf3_eq_zero, ← e11, ← e12, ← e13]
    exact fun h ↦ hz ((or3_eq_zero _ _ _).mpr h)
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 1344 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide), sp]
  have elm : u₂.getMem (u₂.getReg .x2 + 208) = logMem s := by
    rw [m₂, m₁, sp₂, show s.getReg .x2 - 1344 + 208 = s.getReg .x2 - 1136 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact G.kept.lm
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006b88_spec pc₂ (by
    rv_eval [sp₂]
    valid_access hval [hb1])
  have k₃ := b80006b88_keeps h₃
  have m₃ := b80006b88_mem_same h₃
  have x21₃ : u₂.getReg .x21 = u.getReg .x21 := by
    rw [k₂ .x21 (by decide), k₁ .x21 (by decide)]
  by_cases hl : (logMem s).toNat ≤ (u.getReg .x21).toNat
  swap
  · have pc₃ := b80006b88_pc_not_taken h₃ (by rw [elm, x21₃]; omega)
    obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80006b90_spec pc₃ trivial
    exact ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inl (dead_of_fetch (by
      rw [b80006b90_pc h₄]; exact Option.isNone_iff_eq_none.mp (by decide +kernel))))⟩
  have pc₃ := b80006b88_pc_taken h₃ (by rw [elm, x21₃]; exact hl)
  have sp₃ : u₃.getReg .x2 = s.getReg .x2 - 1344 := by rw [k₃ .x2 (by decide), sp₂]
  have elb : u₃.getMem (u₃.getReg .x2 + 192) = logBc s := by
    rw [m₃, m₂, m₁, sp₃, show s.getReg .x2 - 1344 + 192 = s.getReg .x2 - 1152 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact G.kept.lb
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80006b94_spec pc₃ (by
    rv_eval [sp₃]
    valid_access hval [hb1])
  have k₄ := b80006b94_keeps h₄
  have m₄ := b80006b94_mem_same h₄
  have x21₄ : u₃.getReg .x21 = u.getReg .x21 := by rw [k₃ .x21 (by decide), x21₃]
  by_cases hl' : (logBc s).toNat ≤ (u.getReg .x21).toNat
  swap
  · have pc₄ := b80006b94_pc_not_taken h₄ (by rw [elb, x21₄]; omega)
    obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80006b9c_spec pc₄ trivial
    exact ⟨u₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inl (dead_of_fetch (by
      rw [b80006b9c_pc h₅]; exact Option.isNone_iff_eq_none.mp (by decide +kernel))))⟩
  have pc₄ := b80006b94_pc_taken h₄ (by rw [elb, x21₄]; exact hl')
  refine ⟨u₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr ⟨pc₄, fun a ↦ by
    rw [m₄, m₃, m₂, m₁], fun r hr ↦ ?_, hc, hl, hl'⟩)⟩
  rw [k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
    k₁ r (mem_of_mem hr _)]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
