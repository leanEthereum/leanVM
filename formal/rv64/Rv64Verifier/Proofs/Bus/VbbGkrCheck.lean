import Rv64Verifier.Proofs.Bus.VbbGkrProd

/-!
# `verify_bus_balance`: an iteration's claim check, assembled

From the `checked` test (`0x80006844`, taken: `BusBalancePre.checked`) through the three
products, `memcpy` of the products to `S - 248`, `poly_eval` at the combiner and the comparison
with the sumcheck's claim, to `samples`' setup at `0x80006a14` (`AtSm`), or `Err`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The transcript's `checked` byte is not written. -/
theorem Inv.checkedWordG {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) :
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

/-- `memcpy(S - 248, S - 608, 72)`: the three products copied. -/
theorem memcpyF (hM : Runtime.MemcpySpec 0x800126e4) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x800126e4)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 248)
    (h11 : u.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 608) (h12 : u.getReg .x12 = 72) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepR s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 248) 72) ∧
      eListAt v (s.getReg .x2 - BitVec.ofNat 64 248) 3 =
        eListAt u (s.getReg .x2 - BitVec.ofNat 64 608) 3 ∧
      ∀ T, TranscriptAt u (s.getReg .x12) T → TranscriptAt v (s.getReg .x12) T) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hsl : stackLo u memcpyStack = s.getReg .x2 - BitVec.ofNat 64 1360 := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have h72 : (u.getReg .x12).toNat = 72 := by rw [h12]; rfl
  obtain ⟨d1, -, -⟩ := frameSlot (m := 0) hpre h (k := 248) (n := 72) (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨s1, -, -⟩ := frameSlot (m := 0) hpre h (k := 608) (n := 72) (by omega) (by omega)
    (by omega) (by omega)
  have pre : Runtime.MemcpyPre u := {
    dst := by rw [h72, h10]; exact d1.1
    src := by rw [h72, h11]; exact s1.1
    apart := by rw [h72, h10, h11]; addr_omega [hb1]
    stack := ⟨by
        rw [hsl]
        refine ValidMemRange.sub hpre.stack.valid ?_ ?_ ?_ <;> rw [stackLo_eq] <;>
          addr_omega [hb1],
      by rw [h.sp]; have := hpre.stack.aligned; addr_omega [hb1, this]⟩
    dstStack := by rw [h72, h10, hsl]; addr_omega [hb1]
    srcStack := by rw [h72, h11, hsl]; addr_omega [hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hdd⟩ := hM.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hdd⟩
  have fr := post.frame
  rw [h72, h10, hsl] at fr
  have df : DFrame u v fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 248) 72 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 1360) 16 := fun a ha ↦ fr.getMem ha
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hnx : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (df nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hx, hb1])
  have hv : HeapOk v := ⟨hnx ▸ h.heap.lo, hnx ▸ h.heap.hi⟩
  have hby := post.bytes
  rw [h72, h10, h11] at hby
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, ⟨df.mono fun a ha ↦ ?_, hv, hnx.ge, hp.reg .x2⟩,
    eListAt_eq_of_bytesAt hby (by addr_omega [hb1, hb3]) (by addr_omega [hb1, hb3]),
    fun T hT ↦ h.transcript hpre hv (df.mono fun a ha ↦ Or.inl (by
      rcases ha with ha | ha <;> addr_omega [ha, hb1])) hT⟩⟩
  rcases ha with ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))

/-- At `samples`' setup: the children and `x` as before, the claim checked. -/
structure AtSm (s u w : MachineState) (k : Start) (cnt : E) (P : Word) (n : ℕ) (x : List E)
    (c0 c1 c2 : List E) : Prop where
  ctx : Ctx s w k cnt P
  regs : ∀ r ∈ ([.x20, .x24] : List Reg), w.getReg r = u.getReg r
  x22 : (w.getReg .x22).toNat = n % 2
  layers : (w.getMem (s.getReg .x2 - 1128)).toNat = n
  valuesPtr : w.getMem (s.getReg .x2 - 1280) = P
  hu : heapNext s ≤ heapNext u
  xv : NewVecR u w (w.getMem (s.getReg .x2 - 1120)) (w.getReg .x8) (w.getMem (s.getReg .x2 - 1144)) x
  ch0 : HeapVec u w (w.getReg .x27) (w.getReg .x18) c0
  ch1 : HeapVec u w (w.getReg .x26) (w.getReg .x21) c1
  ch2 : HeapVec u w (w.getMem (s.getReg .x2 - 1112)) (w.getReg .x25) c2
  lens : c0.length = 2 ^ stepOf n ∧ c1.length = 2 ^ stepOf n ∧ c2.length = 2 ^ stepOf n
  step : StepR s u w (Scratch s)

theorem limbs_eOf3 (a b c : Word) : Model.limbs (eOf3 a b c) = (a, b, c) := rfl

/-- The `checked` test to `samples`' setup: the products, `poly_eval` and the comparison. -/
theorem claimCheck (hMul : MulSpec) (hMC : Runtime.MemcpySpec 0x800126e4)
    (hPE : MultilinearContracts.PolyEvalSpec) {bev : MachineState → Word → List E → Option E}
    {s u w₀ : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ} {comb : E} {x : List E}
    {cl : E} {c0 c1 c2 : List E} {K : Unit → TM BusResultRust} (hpre : BusBalancePre s)
    (h : AtCk s u w₀ k cnt P n comb x cl c0 c1 c2) (hpc : w₀.pc = 0x80006844)
    (h20 : u.getReg .x20 = s.getReg .x12) (h24 : u.getReg .x24 = 1)
    (htr : Tracks (prog bev s) (s.getReg .x12) s w₀ (TM.require (cl = polyEvalRust
      ([c0, c1, c2].map fun child ↦ child.foldl (fun acc value ↦ acc * value) 1) comb) >>= K)) :
    ∃ w, Reaches Image.code w₀ w ∧ (Done bev s w ∨ Dead Image.code w ∨
      (w.pc = 0x80006a14 ∧ AtSm s u w k cnt P n x c0 c1 c2 ∧
        Tracks (prog bev s) (s.getReg .x12) s w (K ()))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hS := hpre.self.self
  have C₀ := h.ctx
  have x20₀ : w₀.getReg .x20 = s.getReg .x12 := (h.regs .x20 (by decide)).trans h20
  have hck : extractByte (w₀.getMem (s.getReg .x12 + 360)) 0 ≠ 0 := by
    have hc := hpre.checked
    rwa [← Transcript.add_ofNat_zero (s.getReg .x12 + 360),
      Runtime.byteAt_add (by addr_omega [hS]) (by decide), ← C₀.inv.checkedWordG hpre] at hc
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006844_spec hpc (by
    rv_eval [x20₀]
    exact ⟨by addr_omega [hS], Mapped.valid hS.1 (i := 360) (by decide)⟩)
  have k₁ := b80006844_keeps h₁
  have m₁ := b80006844_mem_same h₁
  have pc₁ : w₁.pc = 0x8000684c := Sym.Expect.Holds.pc_eq h₁ (by
    rv_eval [x20₀]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ hck (by
      have := congrArg BitVec.toNat (beq_iff_eq.mp h)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
      simpa using this)))
  -- the frame the whole check writes
  let Aa : Word → Prop := fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 216 ∨
    Within a (s.getReg .x2 - BitVec.ofNat 64 248) 72
  have fA : FrameW s Aa := fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have sA (a : Word) (ha : Aa a) : Scratch s a := by
    rcases ha with ha | ha <;>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
  have pA {j : Nat} (hj : 528 ≤ j ∧ j ≤ 720) (a : Word) (ha : PhA s j a) : Aa a := by
    rcases ha with ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inl (by addr_omega [ha, hb1, hj])
    · exact Or.inr (by addr_omega [ha, hb1])
  have st₁ : StepR s w₀ w₁ Aa := StepR.same m₁ C₀.inv.heap (k₁ .x2 (by decide))
  have C₁ := C₀.step hpre (st₁.weaken sA)
  have x24₁ : w₁.getReg .x24 = 1 := by rw [k₁ .x24 (by decide), h.regs .x24 (by decide), h24]
  -- the three products
  obtain ⟨y₁, hry₁, hd | ⟨hpcy₁, Ph₁⟩⟩ := phase8000684c hMul hpre C₁ pc₁ x24₁ rfl rfl (by
    rw [k₁ .x27 (by decide), k₁ .x18 (by decide)]; exact (h.ch0.toS h.hu).keepG hpre st₁ fA)
  · exact ⟨y₁, hr₁.trans hry₁, Or.inr (Or.inl hd)⟩
  have s₁ : StepR s w₀ y₁ Aa := st₁.join (Ph₁.step.weaken (pA (by omega)))
  obtain ⟨y₂, hry₂, hd | ⟨hpcy₂, Ph₂, sv₂⟩⟩ := phase800068a8 hMul hpre Ph₁.ctx hpcy₁
    (by rw [Ph₁.regs .x24 (by decide), x24₁]) rfl rfl (by
      rw [Ph₁.regs .x26 (by decide), Ph₁.regs .x21 (by decide), k₁ .x26 (by decide),
        k₁ .x21 (by decide)]
      exact (h.ch1.toS h.hu).keepG hpre s₁ fA)
  · exact ⟨y₂, hr₁.trans (hry₁.trans hry₂), Or.inr (Or.inl hd)⟩
  have s₂ : StepR s w₀ y₂ Aa := s₁.join (Ph₂.step.weaken (pA (by omega)))
  have sp₂ := Ph₂.ctx.inv.sp
  obtain ⟨y₃, hry₃, hd | ⟨hpcy₃, Ph₃, sv₃⟩⟩ := phase8000691c hMul hpre Ph₂.ctx hpcy₂
    (by rw [Ph₂.regs .x24 (by decide), Ph₁.regs .x24 (by decide), x24₁]) rfl rfl (by
      rw [Ph₂.regs .x25 (by decide), Ph₁.regs .x25 (by decide), k₁ .x25 (by decide), sp₂,
        show s.getReg .x2 - 1344 + 232 = s.getReg .x2 - 1112 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
        s₂.word hpre (fun y hy hs ↦ by rcases hs with hs | hs <;> addr_omega [hy, hs, hb1])
          (Or.inl (by addr_omega [hb1]))]
      exact (h.ch2.toS h.hu).keepG hpre s₂ fA)
  · exact ⟨y₃, hr₁.trans (hry₁.trans (hry₂.trans hry₃)), Or.inr (Or.inl hd)⟩
  have s₃ : StepR s w₀ y₃ Aa := s₂.join (Ph₃.step.weaken (pA (by omega)))
  have hr03 := hr₁.trans (hry₁.trans (hry₂.trans hry₃))
  -- the products saved, copied, evaluated
  have sp₃ := Ph₃.ctx.inv.sp
  obtain ⟨y₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800069a0_spec hpcy₃ (by
    rv_eval [sp₃]
    and_intros <;> valid_access hval [hb1])
  have k₄ := b800069a0_keeps h₄
  have fr₄ : DFrame y₃ y₄ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 560) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 248) 24 := fun a ha ↦ h₄.frame a (by
    rv_eval [sp₃]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st₄n : StepR s y₃ y₄ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 560) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 248) 24 := StepR.ofDFrame Ph₃.ctx.inv.heap fr₄
    (fun _ h ↦ h) (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1])
    (k₄ .x2 (by decide))
  have st₄ : StepR s y₃ y₄ Aa := st₄n.weaken fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inr (by addr_omega [ha, hb1])
  have I₄ := Ph₃.ctx.inv.afterR hpre fA st₄
  have p2 : eAt y₄ (s.getReg .x2 - BitVec.ofNat 64 560) = c2.foldl (· * ·) 1 := by
    rw [← Ph₃.acc]
    refine eAt_congr ?_ ?_ ?_
    · have := b800069a0_m_x2_784 h₄
      rw [sp₃, show s.getReg .x2 - 1344 + 784 = s.getReg .x2 - BitVec.ofNat 64 560 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 624 =
          s.getReg .x2 - BitVec.ofNat 64 720 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
      exact this
    · have := b800069a0_m_x2_792 h₄
      rw [sp₃, show s.getReg .x2 - 1344 + 792 = s.getReg .x2 - BitVec.ofNat 64 560 + 8 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 632 =
          s.getReg .x2 - BitVec.ofNat 64 720 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
      exact this
    · have := b800069a0_m_x2_800 h₄
      rw [sp₃, show s.getReg .x2 - 1344 + 800 = s.getReg .x2 - BitVec.ofNat 64 560 + 16 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 640 =
          s.getReg .x2 - BitVec.ofNat 64 720 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
      exact this
  have p1 : eAt y₄ (s.getReg .x2 - BitVec.ofNat 64 584) = c1.foldl (· * ·) 1 := by
    rw [st₄n.eAtFrame hpre (by omega) (by omega) (fun y hy hs ↦ by
      rcases hs with hs | hs <;> addr_omega [hy, hs, hb1]), sv₃, Ph₂.acc]
  have p0 : eAt y₄ (s.getReg .x2 - BitVec.ofNat 64 608) = c0.foldl (· * ·) 1 := by
    rw [st₄n.eAtFrame hpre (by omega) (by omega) (fun y hy hs ↦ by
        rcases hs with hs | hs <;> addr_omega [hy, hs, hb1]),
      Ph₃.step.eAtFrame hpre (by omega) (by omega) (fun y hy hs ↦ by
        simp only [PhA] at hs; rcases hs with hs | hs | hs <;> addr_omega [hy, hs, hb1]),
      sv₂, Ph₁.acc]
  have hl4 : eListAt y₄ (s.getReg .x2 - BitVec.ofNat 64 608) 3 =
      [c0, c1, c2].map fun child ↦ child.foldl (fun acc value ↦ acc * value) 1 := by
    rw [show eListAt y₄ (s.getReg .x2 - BitVec.ofNat 64 608) 3 =
      [eAt y₄ (s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 (24 * 0)),
        eAt y₄ (s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 (24 * 1)),
        eAt y₄ (s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 (24 * 2))] from rfl,
      show s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 (24 * 0) =
        s.getReg .x2 - BitVec.ofNat 64 608 by simp,
      show s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 (24 * 1) =
        s.getReg .x2 - BitVec.ofNat 64 584 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
      show s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 (24 * 2) =
        s.getReg .x2 - BitVec.ofNat 64 560 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
      p0, p1, p2]
    rfl
  have sp₄ := I₄.sp
  obtain ⟨y₅, hr₅, ⟨hpc₅, hp₅, st₅, hc₅, tr₅⟩ | hd⟩ := memcpyF hMC hpre I₄ hr₄ (b800069a0_pc h₄)
    (by rw [b800069a0_x10 h₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b800069a0_x11 h₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (b800069a0_x12 h₄)
  swap
  · exact ⟨y₅, hr03.trans hr₅, Or.inr (Or.inl hd)⟩
  have I₅ := I₄.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₅
  have sp₅ := I₅.sp
  obtain ⟨y₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800069dc_spec
    (by rw [hpc₅, returnAddress_eq, b800069a0_x1 h₄]; decide) trivial
  have k₆ := b800069dc_keeps h₆
  have m₆ := b800069dc_mem_same h₆
  have I₆ := I₅.same m₆ (k₆ .x2 (by decide))
  obtain ⟨y₇, hr₇, ⟨hpc₇, hp₇, st₇, hv₇, tr₇⟩ | hd⟩ :=
    polyEvalCall hPE hpre I₆ (hr₅.trans hr₆) (b800069dc_pc h₆) (k := 608) (j := 128)
      (a := s.getReg .x2 - BitVec.ofNat 64 248)
      (by rw [b800069dc_x10 h₆, sp₅]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      (by rw [b800069dc_x11 h₆, sp₅]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      (b800069dc_x12 h₆)
      (by rw [b800069dc_x13 h₆, sp₅]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by valid_sub hval [hb1]) (by addr_omega [hb1]) (by addr_omega [hb1])
  swap
  · exact ⟨y₇, hr03.trans hr₇, Or.inr (Or.inl hd)⟩
  have I₇ := I₆.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₇
  have sp₇ := I₇.sp
  have s5 : StepR s w₀ y₅ Aa := s₃.join (st₄.join (st₅.weaken fun a ha ↦ Or.inr ha))
  have stAll : StepR s w₀ y₇ Aa := s5.join ((StepR.same m₆ I₅.heap (k₆ .x2 (by decide))).join
    (st₇.weaken fun a ha ↦ Or.inl (by addr_omega [ha, hb1])))
  have C₇ := C₀.step hpre (stAll.weaken sA)
  have hR : eAt y₇ (s.getReg .x2 - BitVec.ofNat 64 608) =
      polyEvalRust ([c0, c1, c2].map fun child ↦ child.foldl (fun acc value ↦ acc * value) 1)
        comb := by
    rw [hv₇, eListAt_congr fun i _ ↦ eAt_congr (m₆ _) (m₆ _) (m₆ _), hc₅, hl4,
      eAt_congr (m₆ _) (m₆ _) (m₆ _), s5.eAtFrame hpre (by omega) (by omega) (fun y hy hs ↦ by
        rcases hs with hs | hs <;> addr_omega [hy, hs, hb1]), h.combAt]
  have rgA (r : Reg) (hr : r ∈ ([.x8, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : y₇.getReg r = w₀.getReg r := by
    rw [hp₇ r (mem_of_mem hr _), k₆ r (mem_of_mem hr _), hp₅ r (mem_of_mem hr _),
      k₄ r (mem_of_mem hr _), Ph₃.regs r hr, Ph₂.regs r hr, Ph₁.regs r hr, k₁ r (mem_of_mem hr _)]
  have wA (j : Nat) (hj : 1000 ≤ j ∧ j ≤ 1336) :
      y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = w₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    stAll.word hpre (fun y hy hs ↦ by rcases hs with hs | hs <;> addr_omega [hy, hs, hb1, hj])
      (Or.inl (by addr_omega [hb1, hj]))
  have e736 : y₇.getReg .x2 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [sp₇]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e744 : y₇.getReg .x2 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 := by
    rw [sp₇]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e752 : y₇.getReg .x2 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + 16 := by
    rw [sp₇]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e136 : y₇.getReg .x2 + 136 = s.getReg .x2 - BitVec.ofNat 64 1208 := by
    rw [sp₇]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e128 : y₇.getReg .x2 + 128 = s.getReg .x2 - BitVec.ofNat 64 1216 := by
    rw [sp₇]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hcl : eOf3 (y₇.getReg .x23) (y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 1208))
      (y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 1216)) = cl := by
    rw [rgA .x23 (by decide), wA 1208 (by omega), wA 1216 (by omega)]; exact h.claimAt
  have hlR := limbs_eAt y₇ (s.getReg .x2 - BitVec.ofNat 64 608)
  rw [hR] at hlR
  have hlC := limbs_eOf3 (y₇.getReg .x23) (y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 1208))
    (y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 1216))
  rw [hcl] at hlC
  -- a mismatch
  have errAt (t : MachineState) (hm : ∀ a, t.getMem a = y₇.getMem a)
      (hsp : t.getReg .x2 = y₇.getReg .x2) (hpct : t.pc = 0x800070f8)
      (hne : ¬ cl = polyEvalRust ([c0, c1, c2].map fun child ↦
        child.foldl (fun acc value ↦ acc * value) 1) comb) :
      ∃ t', Reaches Image.code t t' ∧ Done bev s t' := by
    obtain ⟨t₁, hrt₁, ht₁⟩ := Sym.BlockSpec.reaches b800070f8_spec hpct (by
      rv_eval [hsp, sp₇]
      valid_access hval [hb1])
    have m₁' := b800070f8_mem_same ht₁
    have hm' (a : Word) : t₁.getMem a = y₇.getMem a := (m₁' a).trans (hm a)
    have hsp' : t₁.getReg .x2 = y₇.getReg .x2 := (b800070f8_keeps ht₁ .x2 (by decide)).trans hsp
    obtain ⟨t', hrt', hd⟩ := err7100 (bev := bev) hpre (C₇.inv.same hm' hsp')
      (C₇.kept.step hpre (StepR.same hm' C₇.inv.heap hsp')) (b800070f8_pc ht₁)
      (htr.require_fail hne)
    exact ⟨t', hrt₁.trans hrt', hd⟩
  have hr07 := hr03.trans hr₇
  obtain ⟨y₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b800069f4_spec
    (by rw [hpc₇, returnAddress_eq, b800069dc_x1 h₆]; decide) (by
      rv_eval [sp₇]
      valid_access hval [hb1])
  have m₈ := b800069f4_mem_same h₈
  have k₈ := b800069f4_keeps h₈
  by_cases q0 : y₇.getReg .x23 = y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 608)
  swap
  · obtain ⟨t', hrt', hd⟩ := errAt y₈ m₈ (k₈ .x2 (by decide))
      (b800069f4_pc_taken h₈ (by rw [e736]; exact q0)) fun he ↦ q0 (by
        rw [he] at hlC; rw [hlC] at hlR; exact (Prod.mk.inj hlR).1)
    exact ⟨t', hr07.trans (hr₈.trans hrt'), Or.inl hd⟩
  have pc₈ := b800069f4_pc_not_taken h₈ (by rw [e736]; exact q0)
  have sp₈ : y₈.getReg .x2 = y₇.getReg .x2 := k₈ .x2 (by decide)
  obtain ⟨y₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b800069fc_spec pc₈ (by
    rv_eval [sp₈, sp₇]
    and_intros <;> valid_access hval [hb1])
  have m₉ := b800069fc_mem_same h₉
  have k₉ := b800069fc_keeps h₉
  have m₉₇ (a : Word) : y₉.getMem a = y₇.getMem a := (m₉ a).trans (m₈ a)
  by_cases q1 : y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 1208) =
      y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8)
  swap
  · obtain ⟨t', hrt', hd⟩ := errAt y₉ m₉₇ ((k₉ .x2 (by decide)).trans sp₈)
      (b800069fc_pc_taken h₉ (by rw [sp₈, e136, e744, m₈, m₈]; exact q1)) fun he ↦ q1 (by
        rw [he] at hlC; rw [hlC] at hlR; exact (Prod.mk.inj (Prod.mk.inj hlR).2).1)
    exact ⟨t', hr07.trans (hr₈.trans (hr₉.trans hrt')), Or.inl hd⟩
  have pc₉ := b800069fc_pc_not_taken h₉ (by rw [sp₈, e136, e744, m₈, m₈]; exact q1)
  have sp₉ : y₉.getReg .x2 = y₇.getReg .x2 := (k₉ .x2 (by decide)).trans sp₈
  obtain ⟨y₁₀, hr₁₀, h₁₀⟩ := Sym.BlockSpec.reaches b80006a08_spec pc₉ (by
    rv_eval [sp₉, sp₇]
    and_intros <;> valid_access hval [hb1])
  have m₁₀ := b80006a08_mem_same h₁₀
  have k₁₀ := b80006a08_keeps h₁₀
  have m₁₀₇ (a : Word) : y₁₀.getMem a = y₇.getMem a := (m₁₀ a).trans (m₉₇ a)
  by_cases q2 : y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 1216) =
      y₇.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 16)
  swap
  · obtain ⟨t', hrt', hd⟩ := errAt y₁₀ m₁₀₇ ((k₁₀ .x2 (by decide)).trans sp₉)
      (b80006a08_pc_taken h₁₀ (by rw [sp₉, e128, e752, m₉₇, m₉₇]; exact q2)) fun he ↦ q2 (by
        rw [he] at hlC; rw [hlC] at hlR; exact (Prod.mk.inj (Prod.mk.inj hlR).2).2)
    exact ⟨t', hr07.trans (hr₈.trans (hr₉.trans (hr₁₀.trans hrt'))), Or.inl hd⟩
  have pc₁₀ := b80006a08_pc_not_taken h₁₀ (by rw [sp₉, e128, e752, m₉₇, m₉₇]; exact q2)
  have heq : cl = polyEvalRust ([c0, c1, c2].map fun child ↦
      child.foldl (fun acc value ↦ acc * value) 1) comb := by
    rw [← hcl, ← hR, eAt_eOf3, q0, q1, q2]
  have stE : StepR s w₀ y₁₀ Aa := stAll.join (StepR.same m₁₀₇ I₇.heap
    ((k₁₀ .x2 (by decide)).trans sp₉))
  have rgE (r : Reg) (hr : r ∈ ([.x8, .x18, .x20, .x21, .x22, .x24, .x25, .x26, .x27] :
      List Reg)) : y₁₀.getReg r = w₀.getReg r := by
    rw [k₁₀ r (mem_of_mem hr _), k₉ r (mem_of_mem hr _), k₈ r (mem_of_mem hr _),
      rgA r (mem_of_mem hr _)]
  have wE (j : Nat) (hj : 1000 ≤ j ∧ j ≤ 1336) :
      y₁₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = w₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    stE.word hpre (fun y hy hs ↦ by rcases hs with hs | hs <;> addr_omega [hy, hs, hb1, hj])
      (Or.inl (by addr_omega [hb1, hj]))
  have xv := h.xv.keepU hpre h.hu stE fA
  refine ⟨y₁₀, hr07.trans (hr₈.trans (hr₉.trans hr₁₀)), Or.inr (Or.inr ⟨pc₁₀, {
    ctx := C₀.step hpre (stE.weaken sA)
    regs := fun r hr ↦ by
      rw [rgE r (mem_of_mem hr _)]; exact h.regs r (mem_of_mem hr _)
    x22 := by rw [rgE .x22 (by decide)]; exact h.x22
    layers := by rw [show s.getReg .x2 - 1128 = s.getReg .x2 - BitVec.ofNat 64 1128 from rfl,
      wE 1128 (by omega)]; exact h.layers
    valuesPtr := by rw [show s.getReg .x2 - 1280 = s.getReg .x2 - BitVec.ofNat 64 1280 from rfl,
      wE 1280 (by omega)]; exact h.valuesPtr
    xv := by
      rw [show s.getReg .x2 - 1120 = s.getReg .x2 - BitVec.ofNat 64 1120 from rfl,
        show s.getReg .x2 - 1144 = s.getReg .x2 - BitVec.ofNat 64 1144 from rfl,
        wE 1120 (by omega), wE 1144 (by omega), rgE .x8 (by decide)]
      exact xv
    ch0 := by rw [rgE .x27 (by decide), rgE .x18 (by decide)]; exact h.ch0.keepU hpre h.hu stE fA
    ch1 := by rw [rgE .x26 (by decide), rgE .x21 (by decide)]; exact h.ch1.keepU hpre h.hu stE fA
    ch2 := by
      rw [show s.getReg .x2 - 1112 = s.getReg .x2 - BitVec.ofNat 64 1112 from rfl,
        wE 1112 (by omega), rgE .x25 (by decide)]
      exact h.ch2.keepU hpre h.hu stE fA
    lens := h.lens
    hu := h.hu
    step := h.step.join (stE.weaken sA) }, ?_⟩)⟩
  refine (htr.require heq).keep fun T hT ↦ ?_
  have t3 := Ph₃.tr T (Ph₂.tr T (Ph₁.tr T (TranscriptAt.same hpre C₀.inv m₁ hT)))
  have t4 := Ph₃.ctx.inv.transcript hpre st₄.heap (fr₄.mono fun a ha ↦ Or.inl (by
    rcases ha with ha | ha <;> addr_omega [ha, hb1])) t3
  exact TranscriptAt.same hpre I₇ m₁₀₇ (tr₇ T (TranscriptAt.same hpre I₅ m₆ (tr₅ T t4)))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
