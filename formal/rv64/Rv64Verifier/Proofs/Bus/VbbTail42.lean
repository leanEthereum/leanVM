import Rv64Verifier.Proofs.Bus.VbbTail41

/-!
# `verify_bus_balance`'s side loop: the shifted fingerprints

From `0x800076c4` (`Front`): `try_allocate_in` and `reserve` of `n` elements at `S - 248`, the
fingerprints plus `beta` stored from its buffer `q` (`shLoop`), to `dot`'s call at `0x80007788`
(`Shifted`, `sideShift`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.MultilinearContracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- What the shifted fingerprints write from `u` to `w`: `S - 248`, the stack below the frame,
`NEXT`, and the heap from `u`'s `NEXT` on. -/
def ShW (s u w : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 248) 24 ∨ Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨
    (heapNext u ≤ a.toNat ∧ a.toNat < heapNext w)

/-- At `0x80007788`, past `Front` at `u`: `n` (`sideWord s h i 16`) fingerprints plus `beta`
from `q` in `a3`, `n` in `a4`, `beta`'s other limbs in `s1`, `s2`. -/
structure Shifted (s z h u w : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (q : Word) : Prop where
  cur : Cur s z h w
  fr : DFrame u w (ShW s u w)
  mono : heapNext u ≤ heapNext w
  regs : ∀ r ∈ ([.x2, .x8, .x20, .x21, .x24, .x25, .x26, .x27] : List Reg),
    w.getReg r = u.getReg r
  x9 : w.getReg .x9 = sideWord s h i 72
  x18 : w.getReg .x18 = sideWord s h i 80
  x13 : w.getReg .x13 = q
  x14 : w.getReg .x14 = sideWord s h i 16
  buf : NewBuf u w q (24 * (sideWord s h i 16).toNat) 8
  vals : eListAt w q (sideWord s h i 16).toNat = sd.2.2.1.map (sd.2.2.2.2 + ·)

theorem ShW.mono {s u w w' : MachineState} (h : heapNext w ≤ heapNext w') {a : Word}
    (ha : ShW s u w a) : ShW s u w' a := by
  rcases ha with ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨a1, by omega⟩))

theorem CallW.shW {s u v w w' : MachineState} {k n : Nat} (hk : k = 248) (hn : n ≤ 24)
    (huv : heapNext u ≤ heapNext v) (hww : heapNext w ≤ heapNext w') {a : Word}
    (ha : CallW s v w k n a) : ShW s u w' a := by
  subst hk
  rcases ha with ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl (show Within a (s.getReg .x2 - BitVec.ofNat 64 248) 24 from
      ⟨ha.1, by have := ha.2; omega⟩)
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))

set_option maxRecDepth 8192 in
theorem sideShift (hT : TryAllocZeroedSpec) (hR : ReserveFreshSpec 0x80008a10 24 8)
    {s z h u : MachineState} {i : Nat} {sd : List BusBlock × BusLayoutRust × List E × List E × E}
    {point : List E} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (SO : SideOk s z h i sd) (F : Front s z h u i sd point)
    (hpc : u.pc = 0x800076c4) :
    ∃ w, Reaches Image.code u w ∧ (Dead Image.code w ∨
      ∃ q, w.pc = 0x80007788 ∧ Shifted s z h u w i sd q) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have C₀ := F.cur
  have I₀ := C₀.inv
  have sp₀ : u.getReg .x2 = s.getReg .x2 - 1344 := I₀.sp
  have hhu := C₀.step.mono
  -- `0x800076c4`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800076c4_spec hpc trivial
  have m₁ := b800076c4_mem_same h₁
  have k₁ := b800076c4_keeps h₁
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, m₁]
  have C₁ : Cur s z h u₁ := C₀.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₁ I₀.heap (k₁ .x2 (by decide))) fun _ h ↦ h.elim
  -- `try_allocate_in`
  obtain ⟨v₁, hr₂, ⟨hpc₂, hp₂, Cv₁, fr₂, hm₂, hok₂⟩ | hd⟩ := tryAllocC hT hpre hsz C₁
    (Reaches.refl _) (b800076c4_pc h₁) (by rw [b800076c4_x10 h₁, sp₀]; rv_eval [])
    (b800076c4_x13 h₁) (b800076c4_x14 h₁)
  swap
  · exact ⟨v₁, hr₁.trans hr₂, Or.inl hd⟩
  have sp₂ : v₁.getReg .x2 = s.getReg .x2 - 1344 := Cv₁.inv.sp
  -- `0x800076e0`
  obtain ⟨v₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800076e0_spec
    (by rw [hpc₂, returnAddress_eq, b800076c4_x1 h₁]; decide) (by
      rv_eval [sp₂]; valid_access hval [hb1])
  have m₃ := b800076e0_mem_same h₃
  have k₃ := b800076e0_keeps h₃
  have e1096 : v₁.getMem (v₁.getReg .x2 + 1096) = v₁.getMem (s.getReg .x2 - 248) := by
    rw [sp₂]; rv_eval []
  by_cases h0 : v₁.getMem (s.getReg .x2 - 248) = 0
  swap
  · exact ⟨v₂, hr₁.trans (hr₂.trans hr₃), Or.inl (dead_of_fetch (by
      rw [b800076e0_pc_taken h₃ (by rw [e1096]; exact h0)]
      exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have hpc₃ := b800076e0_pc_not_taken h₃ (by rw [e1096]; exact h0)
  obtain ⟨hcap₂, hbuf₂⟩ := hok₂ h0
  have x11₁ : u₁.getReg .x11 = sideWord s h i 16 := by rw [b800076c4_x11 h₁, F.x18]
  rw [x11₁] at hcap₂ hbuf₂
  have C₂ : Cur s z h v₂ := Cv₁.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₃ Cv₁.inv.heap (k₃ .x2 (by decide))) fun _ h ↦ h.elim
  have sp₃ : v₂.getReg .x2 = s.getReg .x2 - 1344 := C₂.inv.sp
  -- `0x800076e8`
  obtain ⟨v₃, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800076e8_spec hpc₃ (by
    rv_eval [sp₃]; and_intros <;> valid_access hval [hb1])
  have k₄ := b800076e8_keeps h₄
  have fr₄ : DFrame v₂ v₃ (Within · (s.getReg .x2 - 248) 24) := by
    have := DFrame.of_memFrame (b800076e8_frame h₄ (by rw [sp₃]; addr_omega [hb1]))
    rw [sp₃] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have st₄ : StepS s v₂ v₃ (Within · (s.getReg .x2 - 248) 24) :=
    StepS.ofDFrame C₂.inv.heap fr₄ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
      (k₄ .x2 (by decide))
  have C₃ : Cur s z h v₃ := C₂.next hpre hsz st₄ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
  have hn₃ : heapNext v₃ = heapNext v₁ := by
    simp only [heapNext]; rw [fr₄ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx], m₃]
  have c₃ : vecCap v₃ (s.getReg .x2 - BitVec.ofNat 64 248) = sideWord s h i 16 := by
    have e := b800076e8_m_x2_1096 h₄
    rw [sp₃, m₃] at e; rv_eval [] at e
    exact e.trans hcap₂
  have p₃ : vecPtr v₃ (s.getReg .x2 - BitVec.ofNat 64 248) = v₁.getMem (s.getReg .x2 - 232) := by
    have e := b800076e8_m_x2_1104 h₄
    rw [sp₃, m₃] at e; rv_eval [] at e
    exact (congrArg v₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e
  have l₃ : vecLen v₃ (s.getReg .x2 - BitVec.ofNat 64 248) = 0 := by
    have e := b800076e8_m_x2_1112 h₄
    rw [sp₃] at e; rv_eval [] at e
    exact (congrArg v₃.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])).trans e
  have hQ := hbuf₂
  simp only [NewBuf] at hQ
  have hlo := I₀.heap.lo
  have hvec₃ : VecOk v₃ (s.getReg .x2 - BitVec.ofNat 64 248) 24 8 := by
    refine ⟨?_, by rw [l₃]; exact Nat.zero_le _⟩
    show Buf v₃ _ _ 8
    rw [p₃, c₃]
    simp only [Buf, hn₃]
    exact ⟨hQ.1, hQ.2.imp id fun h' ↦ ⟨by simp only [heapNext] at hn₁ hhu hlo h' ⊢; omega, h'.2⟩⟩
  -- `reserve`
  obtain ⟨w₄, hr₅, ⟨hpc₅, hp₅, C₄, fr₅, hm₅, hcap₅, hvec₅, hlen₅, hfr₅⟩ | hd⟩ :=
    reserveC hR hpre hsz C₃ (Reaches.refl _) (b800076e8_pc h₄) (k := 248) (by omega) (by omega)
      (by omega) (by rw [b800076e8_x10 h₄, sp₃]; rv_eval []) hvec₃
  swap
  · exact ⟨w₄, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl hd⟩
  have hrA := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅)))
  have sp₄ : w₄.getReg .x2 = s.getReg .x2 - 1344 := C₄.inv.sp
  have x18₄ : w₄.getReg .x18 = sideWord s h i 16 := by
    rw [hp₅.reg .x18, k₄ .x18 (by decide), k₃ .x18 (by decide), hp₂.reg .x18,
      k₁ .x18 (by decide), F.x18]
  have x11₃ : v₃.getReg .x11 = sideWord s h i 16 := by
    rw [b800076e8_x11 h₄, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide), F.x18]
  rw [l₃, x11₃] at hcap₅
  rw [l₃] at hlen₅
  -- `0x8000770c`
  obtain ⟨w₅, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000770c_spec
    (by rw [hpc₅, returnAddress_eq, b800076e8_x1 h₄]; decide) (by
      rv_eval [sp₄]; and_intros <;> valid_access hval [hb1])
  have m₆ := b8000770c_mem_same h₆
  have k₆ := b8000770c_keeps h₆
  have C₅ : Cur s z h w₅ := C₄.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₆ C₄.inv.heap (k₆ .x2 (by decide))) fun _ h ↦ h.elim
  have hn₆ : heapNext w₅ = heapNext w₄ := by simp only [heapNext, m₆]
  set q := vecPtr w₄ (s.getReg .x2 - BitVec.ofNat 64 248) with hq
  have x13₆ : w₅.getReg .x13 = q := by
    rw [b8000770c_x13 h₆, sp₄, hq]; rv_eval []
    exact congrArg w₄.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have x14₆ : w₅.getReg .x14 = 0 := by
    rw [b8000770c_x14 h₆, sp₄, ← hlen₅]; rv_eval []
    exact congrArg w₄.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  -- `q`'s buffer
  have hqb : NewBuf u w₅ q (24 * (sideWord s h i 16).toNat) 8 := by
    refine ⟨hvec₅.raw.1, ?_⟩
    rcases Nat.eq_zero_or_pos (sideWord s h i 16).toNat with hc0 | hc0
    · exact Or.inl (by rw [hc0])
    right
    rcases hfr₅ with ⟨ep, ec⟩ | nb
    · rw [ep, p₃]
      rcases hQ.2 with hz0 | hQ'
      · rw [Nat.mul_eq_zero] at hz0; omega
      · simp only [heapNext] at hn₁ hn₃ hm₅ hn₆ hQ' ⊢; omega
    · simp only [NewBuf] at nb
      rcases nb.2 with hz0 | nb'
      · rw [Nat.mul_eq_zero] at hz0; omega
      · simp only [heapNext] at hn₁ hn₃ hm₂ hm₅ hn₆ nb' hhu ⊢; omega
  -- the frame from `u` to `w₅`
  have hn₁₂ : heapNext u ≤ heapNext v₁ := by rw [← hn₁]; exact hm₂
  have hm₂₅ : heapNext v₁ ≤ heapNext w₅ := by
    rw [hn₆]; simp only [heapNext] at hn₃ hm₅ ⊢; omega
  have huw₅ : heapNext u ≤ heapNext w₅ := le_trans hn₁₂ hm₂₅
  have fr₆ : DFrame u w₅ (ShW s u w₅) := by
    exact (((((DFrame.of_same m₁ (ShW s u w₅)).trans (fr₂.mono fun a ha ↦ CallW.shW rfl
      (le_refl _) (le_of_eq hn₁.symm) hm₂₅ ha) fun _ h ↦ h).trans (DFrame.of_same m₃ _)
      fun _ h ↦ h).trans (fr₄.mono fun a ha ↦ Or.inl ha) fun _ h ↦ h).trans
      (fr₅.mono fun a ha ↦ CallW.shW rfl (by omega)
        (by simp only [heapNext] at hn₃ hn₁₂ ⊢; omega) (le_of_eq hn₆.symm) ha) fun _ h ↦ h).trans
      (DFrame.of_same m₆ _) fun _ h ↦ h
  have regs₆ : ∀ r ∈ ([.x2, .x8, .x20, .x21, .x24, .x25, .x26, .x27] : List Reg),
      w₅.getReg r = u.getReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₆ _ (by decide), hp₅.reg _ (by decide), k₄ _ (by decide), k₃ _ (by decide),
        hp₂.reg _ (by decide), k₁ _ (by decide)]
  have sp₅ : w₅.getReg .x2 = s.getReg .x2 - 1344 := C₅.inv.sp
  have rd (j : Nat) (hj1 : 1144 ≤ j) (hj2 : j ≤ 1304) :
      w₅.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    fr₆ _ fun k hk hw ↦ by
      rcases hw with hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hk, hb1, hj1, hj2]
      · addr_omega [hw, hk, hb1, hj1, hj2]
      · addr_omega [hw, hk, hb1, hj1, hj2, hnx]
      · have := C₅.inv.heap.hi
        simp only [heapNext, heapEnd] at a2 this
        addr_omega [a2, hk, hb1, hj1, hj2, this]
  have hfps := SO.fps
  have hlenF : sd.2.2.1.length = (sideWord s h i 16).toNat := by
    rw [← hfps, eListAt_length]
  by_cases hz : sideWord s h i 16 = 0
  · -- `0x80007780`
    have pc₆ := b8000770c_pc_taken h₆ (by rw [x18₄, hz])
    obtain ⟨w₆, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80007780_spec pc₆ (by
      rv_eval [sp₅]; and_intros <;> valid_access hval [hb1])
    have m₇ := b80007780_mem_same h₇
    have k₇ := b80007780_keeps h₇
    have hn₇ : heapNext w₆ = heapNext w₅ := by simp only [heapNext, m₇]
    have hz0 : (sideWord s h i 16).toNat = 0 := by rw [hz]; rfl
    refine ⟨w₆, hrA.trans (hr₆.trans hr₇), Or.inr ⟨q, b80007780_pc h₇, ⟨C₅.next hpre hsz
      (A := fun _ ↦ False) (StepS.same m₇ C₅.inv.heap (k₇ .x2 (by decide))) fun _ h ↦ h.elim,
      (fr₆.trans (DFrame.of_same m₇ _) fun _ h ↦ h).mono fun a ha ↦ ShW.mono (le_of_eq hn₇.symm) ha,
      by rw [hn₇]; exact huw₅, fun r hr ↦ by rw [k₇ r (mem_of_mem hr _), regs₆ r hr], ?_, ?_,
      by rw [k₇ .x13 (by decide), x13₆], by rw [k₇ .x14 (by decide), x14₆, hz],
      by simp only [NewBuf, hn₇]; exact hqb, ?_⟩⟩⟩
    · rw [b80007780_x9 h₇, sp₅]; rv_eval []
      exact (rd 1160 (by omega) (by omega)).trans F.m1160
    · rw [b80007780_x18 h₇, sp₅]; rv_eval []
      exact (rd 1168 (by omega) (by omega)).trans F.m1168
    · rw [hz0]
      have : sd.2.2.1 = [] := List.eq_nil_of_length_eq_zero (by rw [hlenF, hz0])
      simp [this, eListAt]
  -- `0x80007718`
  have pc₆ := b8000770c_pc_not_taken h₆ (by rw [x18₄]; exact hz)
  obtain ⟨w₆, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80007718_spec pc₆ (by
    rv_eval [sp₅]; and_intros <;> valid_access hval [hb1])
  have m₇ := b80007718_mem_same h₇
  have k₇ := b80007718_keeps h₇
  have hn₇ : heapNext w₆ = heapNext w₅ := by simp only [heapNext, m₇]
  have C₆ : Cur s z h w₆ := C₅.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₇ C₅.inv.heap (k₇ .x2 (by decide))) fun _ h ↦ h.elim
  have hnz : 0 < (sideWord s h i 16).toNat := by
    rcases Nat.eq_zero_or_pos (sideWord s h i 16).toNat with h0' | h0'
    · exact absurd (BitVec.eq_of_toNat_eq h0') hz
    · exact h0'
  obtain ⟨F8, Fb⟩ := SO.fpsBuf
  have hFl := Fb.resolve_left (by omega)
  obtain ⟨Q8, Qb⟩ := hqb
  have hQl := Qb.resolve_left (by omega)
  have hhE := C₅.inv.heap.hi
  simp only [heapNext, heapEnd, heapStart] at hFl hQl hhE hzh hhu hn₇
  have x22₅ : w₅.getReg .x22 = sideWord s h i 8 := by
    rw [k₆ .x22 (by decide), hp₅.reg .x22, k₄ .x22 (by decide), k₃ .x22 (by decide), hp₂.reg .x22,
      k₁ .x22 (by decide), F.x22]
  have x18₅ : w₅.getReg .x18 = sideWord s h i 16 := by rw [k₆ .x18 (by decide), x18₄]
  have S0 : ShI s z h w₆ w₆ (sideWord s h i 8) q (sideWord s h i 16).toNat sd.2.2.1
      sd.2.2.2.2 0 := by
    refine ⟨C₆, DFrame.refl _ _, rfl, fun _ _ ↦ rfl, ?_, ?_, by simp [eListAt]⟩
    · rw [b80007718_x22 h₇, x22₅]; rfl
    · rw [b80007718_x10 h₇, x13₆, x14₆]
      apply BitVec.eq_of_toNat_eq; addr_omega [hQl, hhE]
  have hbeta : eOf3 (w₆.getReg .x26) (w₆.getReg .x9) (w₆.getReg .x18) = sd.2.2.2.2 := by
    rw [k₇ .x26 (by decide), regs₆ .x26 (by decide), F.x26, b80007718_x9 h₇, sp₅,
      b80007718_x18 h₇, sp₅]
    rv_eval []
    rw [show w₅.getMem (s.getReg .x2 - 1160) = sideWord s h i 72 from
        (rd 1160 (by omega) (by omega)).trans F.m1160,
      show w₅.getMem (s.getReg .x2 - 1168) = sideWord s h i 80 from
        (rd 1168 (by omega) (by omega)).trans F.m1168]
    exact SO.beta
  have hx11 : w₆.getReg .x11 = sideWord s h i 8 +
      BitVec.ofNat 64 (24 * (sideWord s h i 16).toNat + 16) := by
    have hn40 : (sideWord s h i 16).toNat < 2 ^ 40 := by omega
    have m16 : (sideWord s h i 16 * 16).toNat = (sideWord s h i 16).toNat * 16 := by
      rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by rw [show (16 : Word).toNat = 16 from rfl]; omega)
    have m8 : (sideWord s h i 16 * 8).toNat = (sideWord s h i 16).toNat * 8 := by
      rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by rw [show (8 : Word).toNat = 8 from rfl]; omega)
    have hh5 := C₅.step.mono
    simp only [heapNext] at hh5
    rw [b80007718_x11 h₇, x22₅, x18₅]
    apply BitVec.eq_of_toNat_eq; addr_omega [hFl, hhE, hzh, hh5, m16, m8]
  obtain ⟨t, hr₈, S₈, hpc₈⟩ := shLoop hpre hsz Ih hzh ⟨F8, hFl⟩
    ⟨Q8, by simp only [heapNext]; omega, by simp only [heapNext]; omega⟩ hfps hbeta hx11
    ((sideWord s h i 16).toNat - 1) 0 w₆ (by omega) S0 (b80007718_pc h₇)
  -- `0x8000777c`
  obtain ⟨t', hr₉, h₉⟩ := Sym.BlockSpec.reaches b8000777c_spec hpc₈ trivial
  have m₉ := b8000777c_mem_same h₉
  have k₉ := b8000777c_keeps h₉
  have hn₉ : heapNext t' = heapNext t := by simp only [heapNext, m₉]
  have hnt := S₈.next
  refine ⟨t', hrA.trans (hr₆.trans (hr₇.trans (hr₈.trans hr₉))), Or.inr ⟨q, b8000777c_pc h₉,
    ⟨S₈.cur.next hpre hsz (A := fun _ ↦ False) (StepS.same m₉ S₈.cur.inv.heap (k₉ .x2 (by decide)))
      fun _ h ↦ h.elim, ?_, ?_, fun r hr ↦ ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  · refine (((fr₆.trans (DFrame.of_same m₇ _) fun _ h ↦ h).trans (S₈.fr.mono fun a ha ↦ ?_)
      fun _ h ↦ h).trans (DFrame.of_same m₉ _) fun _ h ↦ h).mono fun a ha ↦ ?_
    · exact Or.inr (Or.inr (Or.inr ⟨by simp only [Within] at ha; simp only [heapNext]; omega,
        by simp only [Within] at ha; simp only [heapNext]; omega⟩))
    · exact ShW.mono (by simp only [heapNext] at hn₉ hnt ⊢; omega) ha
  · simp only [heapNext] at hn₉ hnt huw₅ ⊢; omega
  · rw [k₉ r (mem_of_mem hr _), S₈.regs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
      k₇ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp), regs₆ r hr]
  · rw [k₉ .x9 (by decide), S₈.regs .x9 (by decide), b80007718_x9 h₇, sp₅]; rv_eval []
    exact (rd 1160 (by omega) (by omega)).trans F.m1160
  · rw [k₉ .x18 (by decide), S₈.regs .x18 (by decide), b80007718_x18 h₇, sp₅]; rv_eval []
    exact (rd 1168 (by omega) (by omega)).trans F.m1168
  · rw [k₉ .x13 (by decide), S₈.regs .x13 (by decide), k₇ .x13 (by decide), x13₆]
  · rw [k₉ .x14 (by decide), S₈.regs .x14 (by decide), b80007718_x14 h₇, x14₆, x18₅]
    exact BitVec.add_zero _
  · exact ⟨Q8, Or.inr ⟨by simp only [heapNext]; omega, by
      simp only [heapNext] at hn₉ hnt ⊢; omega⟩⟩
  · rw [eListAt_congr fun j _ ↦ eAt_congr (m₉ _) (m₉ _) (m₉ _), S₈.vals,
      List.take_of_length_le (le_of_eq hlenF)]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
