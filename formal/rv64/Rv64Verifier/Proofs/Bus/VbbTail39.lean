import Rv64Verifier.Proofs.Bus.VbbTail38

/-!
# `verify_bus_balance`'s side loop: the tables' selectors

From `0x800075fc`: `try_allocate_in`, `reserve`, the loop of `eq_above`s on the `BusLayout`'s
tables' placements (`selLoop2`), to `0x800076c4` with the selectors from `P` in `s4` and their
count at `S - 1296` (`SelDone2`, `selTb`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x800076c4`: the `cnt` tables' selectors from `P`. -/
structure SelDone2 (s z h u₁ u : MachineState) (L P pp pl : Word) (point : List E) (cnt : Nat) :
    Prop where
  cur : Cur s z h u
  fr : DFrame u₁ u fun a ↦ SelW s h u a ∨ Within a (s.getReg .x2 - 1296) 8
  regs : ∀ r ∈ ([.x2, .x8, .x18, .x22, .x24, .x25, .x26] : List Reg), u.getReg r = u₁.getReg r
  x20 : u.getReg .x20 = P
  x21 : u.getReg .x21 = pl
  x27 : u.getReg .x27 = pp
  buf : P.toNat % 8 = 0 ∧ (cnt = 0 ∨ heapNext h ≤ P.toNat ∧ P.toNat + 24 * cnt ≤ heapNext u)
  vals : eListAt u P cnt = (placementsAt h L).map (·.eqAbove point)
  m48 : u.getMem (s.getReg .x2 - 1296) = BitVec.ofNat 64 cnt

set_option maxRecDepth 8192 in
theorem selTb (hT : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    (hEA : EqAboveSpec) {s z h u₁ : MachineState} {i : Nat} {pp : Word} {point : List E}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (PA : PointAt z h pp (h.getMem (s.getReg .x2 - 1144)) point)
    (hF : LowBuf (h.getMem (layAt s i + 24 + 8)) (16 * (h.getMem (layAt s i + 24 + 16)).toNat)
      (heapNext z))
    (C₁ : Cur s z h u₁) (x20₁ : u₁.getReg .x20 = layAt s i)
    (x21₁ : u₁.getReg .x21 = h.getMem (s.getReg .x2 - 1144)) (x27₁ : u₁.getReg .x27 = pp)
    (hl32 : u₁.getMem (layAt s i + 32) = h.getMem (layAt s i + 24 + 8))
    (hl40 : u₁.getMem (layAt s i + 40) = h.getMem (layAt s i + 24 + 16))
    (hi : i < 3) (hpc : u₁.pc = 0x800075fc) :
    ∃ u, Reaches Image.code u₁ u ∧ (Dead Image.code u ∨ ∃ P, SelDone2 s z h u₁ u (layAt s i + 24) P
      pp (h.getMem (s.getReg .x2 - 1144)) point (h.getMem (layAt s i + 24 + 16)).toNat ∧
      u.pc = 0x800076c4) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hab hnx
  have I₁ := C₁.inv
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  -- `0x800075fc`
  obtain ⟨u₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b800075fc_spec hpc (by
    rv_eval [x20₁, layAt]; and_intros <;> valid_access hval [hb1, hb3, hi])
  have m₀ := b800075fc_mem_same h₀
  have k₀ := b800075fc_keeps h₀
  have C₀ : Cur s z h u₀ := C₁.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₀ I₁.heap (k₀ .x2 (by decide))) fun _ h ↦ h.elim
  have hn₁ : heapNext h ≤ heapNext u₀ := by
    have := C₁.step.mono; simp only [heapNext, m₀] at this ⊢; exact this
  -- `try_allocate_in`
  obtain ⟨v₁, hr₁, ⟨hpc₁, hp₁, Cv₁, fr₁, hm₁, hok₁⟩ | hd⟩ :=
    tryAllocC hT hpre hsz C₀ (Reaches.refl _) (b800075fc_pc h₀)
      (by rw [b800075fc_x10 h₀, sp₁]; rv_eval []) (b800075fc_x13 h₀) (b800075fc_x14 h₀)
  swap
  · exact ⟨v₁, hr₀.trans hr₁, Or.inl hd⟩
  have hr₁ := hr₀.trans hr₁
  have sp₁' : v₁.getReg .x2 = s.getReg .x2 - 1344 := Cv₁.inv.sp
  -- `0x80007620`
  obtain ⟨v₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007620_spec
    (by rw [hpc₁, returnAddress_eq, b800075fc_x1 h₀]; decide) (by
      rv_eval [sp₁']; valid_access hval [hb1])
  have m₂ := b80007620_mem_same h₂
  have k₂ := b80007620_keeps h₂
  have e1096 : v₁.getMem (v₁.getReg .x2 + 1096) = v₁.getMem (s.getReg .x2 - 248) := by
    rw [sp₁']; rv_eval []
  by_cases h0 : v₁.getMem (s.getReg .x2 - 248) = 0
  swap
  · exact ⟨v₂, hr₁.trans hr₂, Or.inl (dead_of_fetch (by
      rw [b80007620_pc_taken h₂ (by rw [e1096]; exact h0)]
      exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have hpc₂ := b80007620_pc_not_taken h₂ (by rw [e1096]; exact h0)
  obtain ⟨hcap₁, hbuf₁⟩ := hok₁ h0
  have x11₀ : u₀.getReg .x11 = h.getMem (layAt s i + 24 + 16) := by
    rw [b800075fc_x11 h₀, x20₁]; exact hl40
  rw [x11₀] at hcap₁ hbuf₁
  have I₂ : Inv s v₂ := Cv₁.inv.same m₂ (k₂ .x2 (by decide))
  have C₂ : Cur s z h v₂ := Cv₁.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₂ Cv₁.inv.heap (k₂ .x2 (by decide))) fun _ h ↦ h.elim
  have sp₂ : v₂.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  have x19₂ : v₂.getReg .x19 = h.getMem (layAt s i + 24 + 16) := by
    rw [k₂ .x19 (by decide), hp₁.reg .x19, b800075fc_x19 h₀, x20₁]; exact hl40
  -- `0x80007560`
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007628_spec hpc₂ (by
    rv_eval [sp₂]; and_intros <;> valid_access hval [hb1])
  have k₃ := b80007628_keeps h₃
  have fr₃ : DFrame v₂ v₃ (Within · (s.getReg .x2 - 128) 24) := by
    have := DFrame.of_memFrame (b80007628_frame h₃ (by rw [sp₂]; addr_omega [hb1]))
    rw [sp₂] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have st₃ : StepS s v₂ v₃ (Within · (s.getReg .x2 - 128) 24) :=
    StepS.ofDFrame I₂.heap fr₃ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
      (k₃ .x2 (by decide))
  have C₃ : Cur s z h v₃ := C₂.next hpre hsz st₃ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  have sp₃ : v₃.getReg .x2 = s.getReg .x2 - 1344 := C₃.inv.sp
  have c₃ : vecCap v₃ (s.getReg .x2 - BitVec.ofNat 64 128) = h.getMem (layAt s i + 24 + 16) := by
    have e := b80007628_m_x2_1216 h₃
    rw [sp₂, m₂] at e; rv_eval [] at e
    exact e.trans hcap₁
  have p₃ : vecPtr v₃ (s.getReg .x2 - BitVec.ofNat 64 128) = v₁.getMem (s.getReg .x2 - 232) := by
    have e := b80007628_m_x2_1224 h₃
    rw [sp₂, m₂] at e; rv_eval [] at e
    exact (congrArg v₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e
  have l₃ : vecLen v₃ (s.getReg .x2 - BitVec.ofNat 64 128) = 0 := by
    have e := b80007628_m_x2_1232 h₃
    rw [sp₂] at e; rv_eval [] at e
    exact (congrArg v₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e
  have hQ := hbuf₁
  simp only [NewBuf] at hQ
  have hvec₃ : VecOk v₃ (s.getReg .x2 - BitVec.ofNat 64 128) 24 8 := by
    have hlo := C₀.inv.heap.lo
    refine ⟨?_, by rw [l₃]; exact Nat.zero_le _⟩
    show Buf v₃ _ _ 8
    rw [p₃, c₃]
    have hn₃ : heapNext v₃ = heapNext v₁ := by
      simp only [heapNext]; rw [fr₃ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx], m₂]
    simp only [Buf, hn₃]
    exact ⟨hQ.1, hQ.2.imp id fun h' ↦ ⟨by omega, h'.2⟩⟩
  -- `reserve`
  obtain ⟨w₄, hr₄, ⟨hpc₄, hp₄, C₄, fr₄, hm₄, hcap₄, hvec₄, hlen₄, hfr₄⟩ | hd⟩ :=
    reserveC hR hpre hsz C₃ (Reaches.refl _) (b80007628_pc h₃) (k := 128) (by omega) (by omega)
      (by omega) (by rw [b80007628_x10 h₃, sp₂]; rv_eval []) hvec₃
  swap
  · exact ⟨w₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inl hd⟩
  have sp₄ : w₄.getReg .x2 = s.getReg .x2 - 1344 := C₄.inv.sp
  have x19₄ : w₄.getReg .x19 = h.getMem (layAt s i + 24 + 16) := by
    rw [hp₄.reg .x19, k₃ .x19 (by decide), x19₂]
  rw [l₃, b80007628_x11 h₃, x19₂] at hcap₄
  rw [l₃] at hlen₄
  -- `0x80007584`
  obtain ⟨w₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000764c_spec
    (by rw [hpc₄, returnAddress_eq, b80007628_x1 h₃]; decide) (by
      rv_eval [sp₄]; and_intros <;> valid_access hval [hb1])
  have m₅ := b8000764c_mem_same h₅
  have k₅ := b8000764c_keeps h₅
  have C₅ : Cur s z h w₅ := C₄.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₅ C₄.inv.heap (k₅ .x2 (by decide))) fun _ h ↦ h.elim
  have x12₅ : w₅.getReg .x12 = 0 := by
    rw [b8000764c_x12 h₅, sp₄, ← hlen₄]; rv_eval []
    exact congrArg w₄.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have x20₅ : w₅.getReg .x20 = vecPtr w₄ (s.getReg .x2 - BitVec.ofNat 64 128) := by
    rw [b8000764c_x20 h₅, sp₄]; rv_eval []
    exact congrArg w₄.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hn₂₁ : heapNext v₂ = heapNext v₁ := by simp only [heapNext, m₂]
  have hn₃ : heapNext v₃ = heapNext v₂ := by
    simp only [heapNext]; rw [fr₃ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx]]
  have hn₅ : heapNext w₅ = heapNext w₄ := by simp only [heapNext, m₅]
  have hw₄E := C₄.inv.heap.hi
  -- where `P` is
  have hP8 := hvec₄.raw.1
  have hPb : (h.getMem (layAt s i + 24 + 16)).toNat = 0 ∨
      heapNext h ≤ (vecPtr w₄ (s.getReg .x2 - BitVec.ofNat 64 128)).toNat ∧
      (vecPtr w₄ (s.getReg .x2 - BitVec.ofNat 64 128)).toNat +
        24 * (h.getMem (layAt s i + 24 + 16)).toNat ≤ heapNext w₄ := by
    rcases Nat.eq_zero_or_pos (h.getMem (layAt s i + 24 + 16)).toNat with hc0 | hc0
    · exact Or.inl hc0
    right
    rcases hfr₄ with ⟨ep, ec⟩ | nb
    · rw [ep, p₃]
      rcases hQ.2 with hz0 | hQ'
      · rw [Nat.mul_eq_zero] at hz0; omega
      · simp only [heapNext] at hn₁ hn₂₁ hn₃ hm₄ hQ' ⊢; omega
    · simp only [NewBuf] at nb
      rcases nb.2 with hz0 | nb'
      · rw [Nat.mul_eq_zero] at hz0; omega
      · simp only [heapNext] at hn₁ hn₂₁ hn₃ hm₁ nb' ⊢; omega
  -- the frame from `u₁` to `w₅`
  have fr₅ : DFrame u₁ w₅ (SelW s h w₅) := by
    have hsub (a : Word) (ha : SelW s h w₄ a) : SelW s h w₅ a := by
      rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by rw [hn₅]; exact a2⟩)))
    refine DFrame.mono ((((((DFrame.of_same m₀ _).trans (fr₁.mono fun a ha ↦ ?_) fun _ h ↦ h).trans (DFrame.of_same m₂ _) fun _ h ↦ h).trans
      (fr₃.mono fun a ha ↦ Or.inr (Or.inl ha)) fun _ h ↦ h).trans (fr₄.mono fun a ha ↦ ?_)
      fun _ h ↦ h).trans (DFrame.of_same m₅ _) fun _ h ↦ h) hsub
    · rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext] at hn₁ a1 ⊢; omega,
          by simp only [heapNext] at hn₂₁ hn₃ hm₄ a2 ⊢; omega⟩)))
    · rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by
          simp only [heapNext] at hn₁ hn₂₁ hn₃ hm₁ a1 ⊢; omega, a2⟩)))
  have regs₅ : ∀ r ∈ ([.x2, .x8, .x18, .x22, .x24, .x25, .x26] : List Reg),
      w₅.getReg r = u₁.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₅ _ (by decide), hp₄.reg _ (by decide), k₃ _ (by decide), k₂ _ (by decide),
        hp₁.reg _ (by decide), k₀ _ (by decide)]
  have x21₅ : w₅.getReg .x21 = h.getMem (s.getReg .x2 - 1144) := by
    rw [k₅ .x21 (by decide), hp₄.reg .x21, k₃ .x21 (by decide), k₂ .x21 (by decide), hp₁.reg .x21,
      k₀ .x21 (by decide), x21₁]
  have x27₅ : w₅.getReg .x27 = pp := by
    rw [k₅ .x27 (by decide), hp₄.reg .x27, k₃ .x27 (by decide), k₂ .x27 (by decide),
      hp₁.reg .x27, k₀ .x27 (by decide), x27₁]
  have sp₅ : w₅.getReg .x2 = s.getReg .x2 - 1344 := C₅.inv.sp
  have hrA := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅)))
  have hlenP : (placementsAt h (layAt s i + 24)).length = (h.getMem (layAt s i + 24 + 16)).toNat := by
    simp [placementsAt, vecLen]
  by_cases hc : h.getMem (layAt s i + 24 + 16) = 0
  · have hc0 : (h.getMem (layAt s i + 24 + 16)).toNat = 0 := by rw [hc]; rfl
    have pc₅ := b8000764c_pc_taken h₅ (by rw [x19₄, hc])
    obtain ⟨w₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800076c0_spec pc₅ (by
      rv_eval [sp₅]; valid_access hval [hb1])
    have k₆ := b800076c0_keeps h₆
    have fr₆ : DFrame w₅ w₆ (Within · (s.getReg .x2 - 1296) 8) := by
      have := DFrame.of_memFrame (b800076c0_frame h₆ (by rw [sp₅]; addr_omega [hb1]))
      rw [sp₅] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
    have st₆ : StepS s w₅ w₆ (Within · (s.getReg .x2 - 1296) 8) :=
      StepS.ofDFrame C₅.inv.heap fr₆ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
        (k₆ .x2 (by decide))
    have hn₆ : heapNext w₆ = heapNext w₅ := by
      simp only [heapNext]; rw [fr₆ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx]]
    refine ⟨w₆, hrA.trans hr₆, Or.inr ⟨vecPtr w₄ (s.getReg .x2 - BitVec.ofNat 64 128),
      ⟨C₅.next hpre hsz st₆ fun a ha ↦ Or.inl (Or.inl (by addr_omega [ha, hb1])), ?_, ?_, ?_, ?_,
        ?_, ⟨hP8, Or.inl hc0⟩, ?_, ?_⟩, b800076c0_pc h₆⟩⟩
    · refine (fr₅.mono fun a ha ↦ Or.inl ?_).trans (fr₆.mono fun a ha ↦ Or.inr ha) fun _ h ↦ h
      rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by rw [hn₆]; exact a2⟩)))
    · intro r hr; rw [k₆ r (mem_of_mem hr _), regs₅ r hr]
    · rw [k₆ .x20 (by decide), x20₅]
    · rw [k₆ .x21 (by decide), x21₅]
    · rw [k₆ .x27 (by decide), x27₅]
    · simp only [hc0, placementsAt, vecLen, eListAt, List.range_zero, List.map_nil]
    · have e := b800076c0_m_x2_48 h₆
      rw [sp₅, x12₅] at e; rv_eval [] at e
      rw [hc0]; exact e
  have pc₅ := b8000764c_pc_not_taken h₅ (by rw [x19₄]; exact hc)
  have hcpos : 0 < (h.getMem (layAt s i + 24 + 16)).toNat := by
    rcases Nat.eq_zero_or_pos (h.getMem (layAt s i + 24 + 16)).toNat with h0' | h0'
    · exact absurd (BitVec.eq_of_toNat_eq h0') hc
    · exact h0'
  obtain ⟨hPh, hPu⟩ := hPb.resolve_left (by omega)
  obtain ⟨F8, hFb⟩ := hF
  have hFl := hFb.resolve_left (by omega)
  have hzE := hzh.trans (le_trans (C₅.step.mono) (le_refl _))
  simp only [heapNext, heapEnd, heapStart] at hFl hzE hw₄E hPh hPu hn₅
  -- `0x80007590`
  obtain ⟨w₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80007658_spec pc₅ (by
    rv_eval [sp₅]; valid_access hval [hb1])
  have k₆ := b80007658_keeps h₆
  have fr₆ : DFrame w₅ w₆ (Within · (s.getReg .x2 - 1296) 8) := by
    have := DFrame.of_memFrame (b80007658_frame h₆ (by rw [sp₅]; addr_omega [hb1]))
    rw [sp₅] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have st₆ : StepS s w₅ w₆ (Within · (s.getReg .x2 - 1296) 8) :=
    StepS.ofDFrame C₅.inv.heap fr₆ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
      (k₆ .x2 (by decide))
  have hn₆ : heapNext w₆ = heapNext w₅ := by
    simp only [heapNext]; rw [fr₆ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx]]
  have x9₅ : w₅.getReg .x9 = h.getMem (layAt s i + 24 + 8) := by
    rw [k₅ .x9 (by decide), hp₄.reg .x9, k₃ .x9 (by decide), k₂ .x9 (by decide), hp₁.reg .x9,
      b800075fc_x9 h₀, x20₁]; exact hl32
  have x19₅ : w₅.getReg .x19 = h.getMem (layAt s i + 24 + 16) := by rw [k₅ .x19 (by decide), x19₄]
  have S0 : SelI2 s z h u₁ w₆ (layAt s i + 24) (vecPtr w₄ (s.getReg .x2 - BitVec.ofNat 64 128)) pp
      (h.getMem (s.getReg .x2 - 1144)) point (h.getMem (layAt s i + 24 + 16)).toNat 0 := by
    refine ⟨C₅.next hpre hsz st₆ fun a ha ↦ Or.inl (Or.inl (by addr_omega [ha, hb1])), ?_,
      fun r hr ↦ by rw [k₆ r (mem_of_mem hr _), regs₅ r hr], ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨hP8, by simp only [heapNext] at hn₁ ⊢; omega, by simp only [heapNext] at hn₆ ⊢; omega⟩,
      by simp [eListAt], ?_⟩
    · refine (fr₅.mono fun a ha ↦ Or.inl ?_).trans (fr₆.mono fun a ha ↦ Or.inr ha) fun _ h ↦ h
      rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by rw [hn₆]; exact a2⟩)))
    · rw [b80007658_x9 h₆, x9₅]; rfl
    · rw [b80007658_x23 h₆, x9₅, x19₅]
      apply BitVec.eq_of_toNat_eq; addr_omega [hFl, hzE, hw₄E, hPu, hn₅]
    · rw [b80007658_x19 h₆, x20₅, x12₅]; apply BitVec.eq_of_toNat_eq; addr_omega [hPu, hw₄E]
    · rw [k₆ .x20 (by decide), x20₅]
    · rw [k₆ .x21 (by decide), x21₅]
    · rw [k₆ .x27 (by decide), x27₅]
    · have e := b80007658_m_x2_48 h₆
      rw [sp₅, x19₅, x12₅] at e; rv_eval [] at e
      rv_eval []
      rw [e, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  obtain ⟨w₇, hr₇, hd | ⟨S₇, hpc₇⟩⟩ := selLoop2 hEA hpre hsz Ih hzh PA rfl ⟨F8, hFb⟩
    ((h.getMem (layAt s i + 24 + 16)).toNat - 1) 0 w₆ (by omega) S0 (b80007658_pc h₆)
  · exact ⟨w₇, hrA.trans (hr₆.trans hr₇), Or.inl hd⟩
  -- `0x800075f4`
  obtain ⟨w₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b800076bc_spec hpc₇ trivial
  have m₈ := b800076bc_mem_same h₈
  have k₈ := b800076bc_keeps h₈
  have hn₈ : heapNext w₈ = heapNext w₇ := by simp only [heapNext, m₈]
  refine ⟨w₈, hrA.trans (hr₆.trans (hr₇.trans hr₈)), Or.inr ⟨_, ⟨S₇.cur.next hpre hsz
    (A := fun _ ↦ False) (StepS.same m₈ S₇.cur.inv.heap (k₈ .x2 (by decide))) fun _ h ↦ h.elim,
    ?_, fun r hr ↦ by rw [k₈ r (mem_of_mem hr _), S₇.regs r hr], by rw [k₈ .x20 (by decide), S₇.x20],
    by rw [k₈ .x21 (by decide), S₇.x21], by rw [k₈ .x27 (by decide), S₇.x27],
    ⟨S₇.buf.1, Or.inr ⟨S₇.buf.2.1, by rw [hn₈]; exact S₇.buf.2.2⟩⟩, ?_,
    by rw [m₈]; exact S₇.m48⟩, b800076bc_pc h₈⟩⟩
  · refine (S₇.fr.trans (DFrame.of_same m₈ _) fun _ h ↦ h).mono fun a ha ↦ ?_
    rcases ha with (ha | ha | ha | ha | ⟨a1, a2⟩) | ha
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr (Or.inl ha))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by rw [hn₈]; exact a2⟩))))
    · exact Or.inr ha
  · rw [eListAt_congr fun j _ ↦ eAt_congr (m₈ _) (m₈ _) (m₈ _), S₇.vals,
      List.take_of_length_le (le_of_eq hlenP)]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
