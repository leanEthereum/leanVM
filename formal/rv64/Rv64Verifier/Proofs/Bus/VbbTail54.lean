import Rv64Verifier.Proofs.Bus.VbbTail53

/-!
# `verify_bus_balance`'s side loop: the padding weight's loop

The loop at `0x80007a68` computes `padLow` of the block's `rows` over the point's first `log_rows`
coordinates (`PadI`, `padIter`, `padLoop`), each step two `mul`s (`Q.mul`) on the frame's scratch.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem b80007ac0_frame' {s t : MachineState} (h : b80007ac0.Holds s t)
    (hb : (s.getReg .x2).toNat + 1240 ≤ 2 ^ 64) : MemFrame s t (s.getReg .x2 + 1216) 24 :=
  h.memFrame (by rv_eval []; and_intros <;> addr_omega [hb])

/-- A block writing `S - [248, 104)` keeps `Q`. -/
theorem Q.blk {s z h e t₀ t₆ t t' : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (Qt : Q s z h e t₀ t₆ t i sd point P n forms tot k)
    (fr : DFrame t t' (Within · (s.getReg .x2 - 248) 144)) (sp : t'.getReg .x2 = t.getReg .x2)
    (regs : ∀ r ∈ ([.x2, .x19, .x23, .x24, .x26, .x27] : List Reg), t'.getReg r = t.getReg r) :
    Q s z h e t₀ t₆ t' i sd point P n forms tot k := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hN : ∀ q < 8, ¬ Within (nextAddr + BitVec.ofNat 64 q) (s.getReg .x2 - 248) 144 :=
    fun q hq hw ↦ by addr_omega [hw, hq, hb1, hnx]
  have hn : heapNext t' = heapNext t := by simp only [heapNext]; rw [fr nextAddr hN]
  exact Qt.next hpre (Qt.cur.next hpre hsz (StepS.ofDFrame Qt.cur.inv.heap fr (fun _ h ↦ h) hN sp)
    fun a ha ↦ QW.side hpre ha) (fr.mono fun a ha ↦ Or.inl ha) hn regs

/-- `mul` into `S - o`, `o` within the scratch, keeps `Q`. -/
theorem Q.mul (hMul : MulSpec) {s z h e t₀ t₆ u : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (Qu : Q s z h e t₀ t₆ u i sd point P n forms tot k)
    (hpc : u.pc = 0x80008c48) {o a b : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 o)
    (h11 : u.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 a)
    (h12 : u.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 b)
    (ho : 128 ≤ o ∧ o ≤ 248 ∧ o % 8 = 0) (ha : 128 ≤ a ∧ a ≤ 1344 ∧ a % 8 = 0)
    (hb : 128 ≤ b ∧ b ≤ 1344 ∧ b % 8 = 0) (hoa : o + 24 ≤ a ∨ a + 24 ≤ o)
    (hob : o + 24 ≤ b ∨ b + 24 ≤ o) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      Q s z h e t₀ t₆ v i sd point P n forms tot k ∧
      DFrame u v (fun x ↦ Within x (s.getReg .x2 - BitVec.ofNat 64 o) 24 ∨
        Within x (s.getReg .x2 - BitVec.ofNat 64 2368) 1024) ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 o) =
        eAt u (s.getReg .x2 - BitVec.ofNat 64 a) * eAt u (s.getReg .x2 - BitVec.ofNat 64 b)) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨v, hrv, ⟨hpcv, hp, Cv, fr, hn, hval⟩ | hd⟩ := mulCallC hMul hpre hsz Qu.cur
    (Reaches.refl u) hpc h10 h11 h12 ⟨ho.1, by omega, ho.2.2⟩ ha hb hoa hob
  · refine ⟨v, hrv, Or.inl ⟨hpcv, hp, Qu.next hpre Cv (fr.mono fun x hx ↦ ?_) hn fun r hr ↦ ?_, fr,
      hval⟩⟩
    · rcases hx with hx | hx
      · exact Or.inl (by addr_omega [hx, hb1, ho])
      · exact Or.inr (by addr_omega [hx, hb1])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hp.reg _
  · exact ⟨v, hrv, Or.inr hd⟩

/-- At the padding weight's loop's head after `j` coordinates. -/
structure PadI (s z h e t₀ t₆ t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) (forms : List (List Form)) (tot : List E) (k j : Nat) : Prop where
  q : Q s z h e t₀ t₆ t i sd point P n forms tot k
  x8 : t.getReg .x8 = e.getMem (s.getReg .x2 - 1256) + BitVec.ofNat 64 (24 * j)
  x9 : t.getReg .x9 = BitVec.ofNat 64 j
  x18 : t.getReg .x18 = s.getReg .x2 - 144
  pad : eOf3 (t.getReg .x12) (t.getReg .x10) (t.getReg .x11) =
    padLow (s.getMem (blkAddr s i k + 32)) point j

/-- An `E` in the frame from three words. -/
theorem eAt_three {t : MachineState} {S : Word} {o : Nat} (hS : 1344 ≤ S.toNat) (ho : 16 ≤ o)
    (ho2 : o ≤ 1344) {x y w : Word} (h0 : t.getMem (S - BitVec.ofNat 64 o) = x)
    (h8 : t.getMem (S - BitVec.ofNat 64 (o - 8)) = y)
    (h16 : t.getMem (S - BitVec.ofNat 64 (o - 16)) = w) :
    eAt t (S - BitVec.ofNat 64 o) = eOf3 x y w := by
  rw [eAt_eq_eOf3, h0,
    show S - BitVec.ofNat 64 o + 8 = S - BitVec.ofNat 64 (o - 8) by
      apply BitVec.eq_of_toNat_eq; addr_omega [hS, ho, ho2], h8,
    show S - BitVec.ofNat 64 o + 16 = S - BitVec.ofNat 64 (o - 16) by
      apply BitVec.eq_of_toNat_eq; addr_omega [hS, ho, ho2], h16]

theorem eOf3_xor0 (a b c x : Word) : eOf3 (a ^^^ x) b c = eOf3 a 0 0 + eOf3 x b c :=
  eq_of_limbs (by rw [limbs_add, limbs_eOf3', limbs_eOf3', limbs_eOf3']; simp)

theorem sp_slot {t : MachineState} {S : Word} {off : Nat} (hS : 1344 ≤ S.toNat) (ho : off ≤ 1344)
    {x : Word} (m : t.getMem (S - 1344 + BitVec.ofNat 64 off) = x) :
    t.getMem (S - BitVec.ofNat 64 (1344 - off)) = x := by
  rw [← m]; congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hS, ho]

set_option maxRecDepth 8192 in
/-- One coordinate of the padding weight. -/
theorem padIter (hMul : MulSpec) {s z h e t₀ t₆ t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k j : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n)
    (I : PadI s z h e t₀ t₆ t i sd point P n forms tot k j)
    (hj : j < (s.getMem (blkAddr s i k + 24)).toNat) (hpc : t.pc = 0x80007a68) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
      (PadI s z h e t₀ t₆ t' i sd point P n forms tot k (j + 1) ∧
        ((j + 1 < (s.getMem (blkAddr s i k + 24)).toNat ∧ t'.pc = 0x80007a68) ∨
          (j + 1 = (s.getMem (blkAddr s i k + 24)).toNat ∧ t'.pc = 0x80007b14)))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS : 1344 ≤ (s.getReg .x2).toNat := by omega
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have Qt := I.q
  have sp : t.getReg .x2 = s.getReg .x2 - 1344 := Qt.cur.inv.sp
  have hjp : j < point.length := lt_of_lt_of_le hj Qt.lr
  -- the point
  have PA := En.pt
  have hl : (e.getMem (s.getReg .x2 - 1144)).toNat = point.length := by
    rw [← PA.elems, eListAt_length]
  have p8 := PA.p8
  have plo : heapStart ≤ (e.getMem (s.getReg .x2 - 1256)).toNat := PA.lo.resolve_left (by omega)
  have phi := PA.hi
  have hzE := le_trans hzh Ih.heap.hi
  rw [hl] at phi
  simp only [heapNext, heapEnd, heapStart] at phi hzE plo
  have hvP : ValidMemRange (e.getMem (s.getReg .x2 - 1256)) (3 * point.length) :=
    heapRange p8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hr : eAt t (t.getReg .x8) = point.getD j 0 := by
    rw [I.x8, ← PA.at hpre Qt.cur Ih hzh, eListAt_getD _ _ (by rw [hl]; exact hjp)]
  -- `0x80007a68`
  obtain ⟨a₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007a68_spec hpc (by
    rv_eval [sp, I.x8, I.x18]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hvP [phi, hzE, plo, hjp]
      | addr_omega [hb1, phi, hzE, plo, hjp])
  have k₁ := b80007a68_keeps h₁
  have sp₁ : a₁.getReg .x2 = s.getReg .x2 - 1344 := (k₁ .x2 (by decide)).trans sp
  have fr₁ : DFrame t a₁ (Within · (s.getReg .x2 - 248) 144) := by
    have := DFrame.of_memFrame (b80007a68_frame' h₁ (by rw [sp]; addr_omega [hb1])
      (by rw [I.x18, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
    rw [sp] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have Q₁ := Qt.blk hpre hsz fr₁ (k₁ .x2 (by decide)) fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁ _ (by decide)
  have e248 : eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 248) =
      padLow (s.getMem (blkAddr s i k + 32)) point j := by
    rw [← I.pad]
    have m0 := b80007a68_m_x2_1096 h₁
    have m8 := b80007a68_m_x2_1104 h₁
    have m16 := b80007a68_m_x2_1112 h₁
    rw [sp] at m0 m8 m16; rv_eval [] at m0 m8 m16
    exact eAt_three hS (by omega) (by omega) m0 m8 m16
  have e128 : eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 128) = point.getD j 0 := by
    rw [← hr, eAt_eq_eOf3 t]
    have m0 := b80007a68_m_x2_1216 h₁
    have m8 := b80007a68_m_x2_1224 h₁
    have m16 := b80007a68_m_x2_1232 h₁
    rw [sp] at m0 m8 m16; rv_eval [] at m0 m8 m16
    exact eAt_three hS (by omega) (by omega) m0 m8 m16
  have hj64 : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have bw : ((s.getMem (blkAddr s i k + 32) >>> ((t.getReg .x9).toNat % 64)) ^^^
      0xffffffffffffffff) &&& 1 = ((s.getMem (blkAddr s i k + 32) >>> (j % 64)) ^^^
      0xffffffffffffffff) &&& 1 := by rw [I.x9, hj64]
  have e152 : eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 152) =
      1 + bitE (s.getMem (blkAddr s i k + 32)) j := by
    rw [← bit_eq]
    have m0 := b80007a68_m_x2_1192 h₁
    have m8 := b80007a68_m_x18_0 h₁
    have m16 := b80007a68_m_x18_8 h₁
    rw [Qt.x27, bw] at m0
    rw [I.x18] at m8 m16
    rw [sp] at m0; rv_eval [] at m0 m8 m16
    exact eAt_three hS (by omega) (by omega) m0 m8 m16
  -- `mul`: `(1 + b) * r` into `S - 176`
  obtain ⟨v₁, hrv₁, ⟨hpv₁, hp₁, Qv₁, frv₁, val₁⟩ | hd⟩ := Q₁.mul hMul hpre hsz (b80007a68_pc h₁)
    (o := 176) (a := 152) (b := 128)
    (by rw [b80007a68_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80007a68_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80007a68_x12 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by omega) (by omega) (by omega) (by omega) (by omega)
  swap
  · exact ⟨v₁, hr₁.trans hrv₁, Or.inl hd⟩
  have spv₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := (hp₁.reg .x2).trans sp₁
  -- `0x80007ac0`: `(1 + b) + r`
  obtain ⟨a₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80007ac0_spec
    (by rw [hpv₁, returnAddress_eq, b80007a68_x1 h₁]; decide) (by
      rv_eval [spv₁]; and_intros <;> valid_access hval [hb1])
  have k₂ := b80007ac0_keeps h₂
  have fr₂ : DFrame v₁ a₂ (Within · (s.getReg .x2 - 128) 24) := by
    have := DFrame.of_memFrame (b80007ac0_frame' h₂ (by rw [spv₁]; addr_omega [hb1]))
    rw [spv₁] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have Q₂ := Qv₁.blk hpre hsz (fr₂.mono fun a ha ↦ by addr_omega [ha, hb1]) (k₂ .x2 (by decide))
    fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₂ _ (by decide)
  have spa₂ : a₂.getReg .x2 = s.getReg .x2 - 1344 := (k₂ .x2 (by decide)).trans spv₁
  have e128₂ : eAt a₂ (s.getReg .x2 - BitVec.ofNat 64 128) =
      (1 + bitE (s.getMem (blkAddr s i k + 32)) j) + point.getD j 0 := by
    rw [← bit_eq, ← hr, eAt_eq_eOf3 t (t.getReg .x8), ← eOf3_xor0]
    have m0 := b80007ac0_m_x2_1216 h₂
    have m8 := b80007ac0_m_x2_1224 h₂
    have m16 := b80007ac0_m_x2_1232 h₂
    rw [spv₁, hp₁.reg .x25, hp₁.reg .x22, b80007a68_x25' h₁, b80007a68_x22 h₁, Qt.x27, bw] at m0
    rw [spv₁, hp₁.reg .x21, b80007a68_x21 h₁] at m8
    rw [spv₁, hp₁.reg .x20, b80007a68_x20 h₁] at m16
    exact eAt_three hS (by omega) (by omega) (sp_slot (off := 1216) hS (by omega) m0)
      (sp_slot (off := 1224) hS (by omega) m8) (sp_slot (off := 1232) hS (by omega) m16)
  have e248₂ : eAt a₂ (s.getReg .x2 - BitVec.ofNat 64 248) = eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 248) := by
    rw [fr₂.eAt fun q hq hw ↦ by addr_omega [hw, hq, hb1]]
    exact frv₁.eAt fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1]
  have e176₂ : eAt a₂ (s.getReg .x2 - BitVec.ofNat 64 176) = eAt v₁ (s.getReg .x2 - BitVec.ofNat 64 176) :=
    fr₂.eAt fun q hq hw ↦ by addr_omega [hw, hq, hb1]
  -- `mul`: `((1 + b) + r) * pad` into `S - 152`
  obtain ⟨v₂, hrv₂, ⟨hpv₂, hp₂, Qv₂, frv₂, val₂⟩ | hd⟩ := Q₂.mul hMul hpre hsz (b80007ac0_pc h₂)
    (o := 152) (a := 128) (b := 248)
    (by rw [b80007ac0_x10 h₂, spv₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80007ac0_x11 h₂, spv₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80007ac0_x12 h₂, spv₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by omega) (by omega) (by omega) (by omega) (by omega)
  swap
  · exact ⟨v₂, hr₁.trans (hrv₁.trans (hr₂.trans hrv₂)), Or.inl hd⟩
  have spv₂ : v₂.getReg .x2 = s.getReg .x2 - 1344 := (hp₂.reg .x2).trans spa₂
  have e176₃ : eAt v₂ (s.getReg .x2 - BitVec.ofNat 64 176) = eAt v₁ (s.getReg .x2 - BitVec.ofNat 64 176) := by
    rw [← e176₂]
    exact frv₂.eAt fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1]
  -- `0x80007ae4`: the new `pad`
  obtain ⟨t', hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007ae4_spec
    (by rw [hpv₂, returnAddress_eq, b80007ac0_x1 h₂]; decide) (by
      rv_eval [spv₂]; and_intros <;> valid_access hval [hb1])
  have m₃ := b80007ae4_mem_same h₃
  have k₃ := b80007ae4_keeps h₃
  have Q₃ := Qv₂.blk hpre hsz (DFrame.of_same m₃ _) (k₃ .x2 (by decide)) fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₃ _ (by decide)
  have E152 : eOf3 (v₂.getMem (s.getReg .x2 - 1344 + 1192)) (v₂.getMem (s.getReg .x2 - 1344 + 1200))
      (v₂.getMem (s.getReg .x2 - 1344 + 1208)) =
      ((1 + bitE (s.getMem (blkAddr s i k + 32)) j) + point.getD j 0) *
        padLow (s.getMem (blkAddr s i k + 32)) point j := by
    rw [← e248, ← e248₂, ← e128₂, ← val₂]
    exact (eAt_three hS (by omega) (by omega) (sp_slot (off := 1192) hS (by omega) rfl)
      (sp_slot (off := 1200) hS (by omega) rfl) (sp_slot (off := 1208) hS (by omega) rfl)).symm
  have E176 : eOf3 (v₂.getMem (s.getReg .x2 - 1344 + 1168)) (v₂.getMem (s.getReg .x2 - 1344 + 1176))
      (v₂.getMem (s.getReg .x2 - 1344 + 1184)) =
      (1 + bitE (s.getMem (blkAddr s i k + 32)) j) * point.getD j 0 := by
    rw [← e152, ← e128, ← val₁, ← e176₃]
    exact (eAt_three hS (by omega) (by omega) (sp_slot (off := 1168) hS (by omega) rfl)
      (sp_slot (off := 1176) hS (by omega) rfl) (sp_slot (off := 1184) hS (by omega) rfl)).symm
  have pad' : eOf3 (t'.getReg .x12) (t'.getReg .x10) (t'.getReg .x11) =
      padLow (s.getMem (blkAddr s i k + 32)) point (j + 1) := by
    rw [b80007ae4_x12 h₃, b80007ae4_x10 h₃, b80007ae4_x11 h₃, eOf3_xor, spv₂, E152, E176]
    rfl
  have hL64 := (s.getMem (blkAddr s i k + 24)).isLt
  have hj1 : j + 1 < 2 ^ 64 := by omega
  have h24 : 24 * j + 24 < 2 ^ 64 := by omega
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x26] : List Reg)) : v₂.getReg r = t.getReg r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [hp₂.reg _, k₂ _ (by decide), hp₁.reg _, k₁ _ (by decide)]
  have x9₂ : v₂.getReg .x9 + 1 = BitVec.ofNat 64 (j + 1) := by
    rw [rg .x9 (by decide), I.x9]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hj1]
  have x26₂ : v₂.getReg .x26 = s.getMem (blkAddr s i k + 24) := Qv₂.x26
  have I' : PadI s z h e t₀ t₆ t' i sd point P n forms tot k (j + 1) := by
    refine ⟨Q₃, ?_, by rw [b80007ae4_x9 h₃, x9₂], ?_, pad'⟩
    · rw [b80007ae4_x8 h₃, rg .x8 (by decide), I.x8, BitVec.add_assoc]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (24 : Word).toNat = 24 from rfl]
      omega
    · rw [k₃ .x18 (by decide), rg .x18 (by decide), I.x18]
  rcases Nat.lt_or_ge (j + 1) (s.getMem (blkAddr s i k + 24)).toNat with hlt | hge
  · refine ⟨t', hr₁.trans (hrv₁.trans (hr₂.trans (hrv₂.trans hr₃))), Or.inr ⟨I', Or.inl ⟨hlt,
      b80007ae4_pc_taken h₃ ?_⟩⟩⟩
    rw [x26₂, x9₂]; intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj1] at this; omega
  · refine ⟨t', hr₁.trans (hrv₁.trans (hr₂.trans (hrv₂.trans hr₃))), Or.inr ⟨I', Or.inr ⟨by omega,
      b80007ae4_pc_not_taken h₃ ?_⟩⟩⟩
    rw [x26₂, x9₂]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj1]; omega

/-- The loop, from `j` coordinates to the last. -/
theorem padLoop (hMul : MulSpec) {s z h e t₀ t₆ : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n) :
    ∀ d j t, j + d + 1 = (s.getMem (blkAddr s i k + 24)).toNat →
      PadI s z h e t₀ t₆ t i sd point P n forms tot k j → t.pc = 0x80007a68 →
      ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
        (PadI s z h e t₀ t₆ t' i sd point P n forms tot k (s.getMem (blkAddr s i k + 24)).toNat ∧
          t'.pc = 0x80007b14)) := by
  intro d
  induction d with
  | zero =>
    intro j t hd I hpc
    obtain ⟨t', hr, hd' | ⟨I', ⟨hlt, -⟩ | ⟨he, hpc'⟩⟩⟩ :=
      padIter hMul hpre hsz Ih hzh En I (by omega) hpc
    · exact ⟨t', hr, Or.inl hd'⟩
    · omega
    · rw [he] at I'; exact ⟨t', hr, Or.inr ⟨I', hpc'⟩⟩
  | succ d ih =>
    intro j t hd I hpc
    obtain ⟨t', hr, hd' | ⟨I', ⟨-, hpc'⟩ | ⟨he, -⟩⟩⟩ :=
      padIter hMul hpre hsz Ih hzh En I (by omega) hpc
    · exact ⟨t', hr, Or.inl hd'⟩
    · obtain ⟨t'', hr', ht''⟩ := ih (j + 1) t' (by omega) I' hpc'
      exact ⟨t'', hr.trans hr', ht''⟩
    · omega

theorem eOf3_one : eOf3 1 0 0 = 1 := eq_of_limbs (by rw [limbs_eOf3', limbs_one])

/-- From the checks to `0x800077f8`, `pad` in `a2`, `a0`, `a1`. -/
theorem padStage (hMul : MulSpec) {s z h e t₀ t₆ t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ih : Inv s h)
    (hzh : heapNext z ≤ heapNext h) (En : Entry s z h e i sd point P n)
    (Qt : Q s z h e t₀ t₆ t i sd point P n forms tot k)
    (hc : (s.getMem (blkAddr s i k + 24) = 0 ∧ t.pc = 0x800077f4 ∧ t.getReg .x10 = 0 ∧
          t.getReg .x11 = 0) ∨
        (s.getMem (blkAddr s i k + 24) ≠ 0 ∧ t.pc = 0x80007a68 ∧
          t.getReg .x8 = e.getMem (s.getReg .x2 - 1256) ∧ t.getReg .x9 = 0 ∧
          t.getReg .x10 = 0 ∧ t.getReg .x11 = 0 ∧ t.getReg .x12 = 1 ∧
          t.getReg .x18 = s.getReg .x2 - 144)) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
      (Q s z h e t₀ t₆ t' i sd point P n forms tot k ∧ t'.pc = 0x800077f8 ∧
        eOf3 (t'.getReg .x12) (t'.getReg .x10) (t'.getReg .x11) =
          padLow (s.getMem (blkAddr s i k + 32)) point (s.getMem (blkAddr s i k + 24)).toNat)) := by
  rcases hc with ⟨hL, hpc, h10, h11⟩ | ⟨hL, hpc, h8, h9, h10, h11, h12, h18⟩
  · obtain ⟨t', hr, h'⟩ := Sym.BlockSpec.reaches b800077f4_spec hpc trivial
    have m' := b800077f4_mem_same h'
    have k' := b800077f4_keeps h'
    refine ⟨t', hr, Or.inr ⟨Qt.blk hpre hsz (DFrame.of_same m' _) (k' .x2 (by decide)) fun r hr ↦ ?_,
      b800077f4_pc h', ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k' _ (by decide)
    · rw [b800077f4_x12 h', k' .x10 (by decide), k' .x11 (by decide), h10, h11, hL]
      exact eOf3_one
  · have I0 : PadI s z h e t₀ t₆ t i sd point P n forms tot k 0 :=
      ⟨Qt, by rw [h8]; simp, by rw [h9]; rfl, h18, by rw [h12, h10, h11]; exact eOf3_one⟩
    have hL0 : (s.getMem (blkAddr s i k + 24)).toNat ≠ 0 := fun h0 ↦ hL (BitVec.eq_of_toNat_eq h0)
    obtain ⟨t₁, hr₁, hd | ⟨I₁, hpc₁⟩⟩ := padLoop hMul hpre hsz Ih hzh En
      ((s.getMem (blkAddr s i k + 24)).toNat - 1) 0 t (by omega) I0 hpc
    · exact ⟨t₁, hr₁, Or.inl hd⟩
    obtain ⟨t', hr, h'⟩ := Sym.BlockSpec.reaches b80007b14_spec hpc₁ trivial
    have m' := b80007b14_mem_same h'
    have k' := b80007b14_keeps h'
    refine ⟨t', hr₁.trans hr, Or.inr ⟨I₁.q.blk hpre hsz (DFrame.of_same m' _) (k' .x2 (by decide))
      fun r hr ↦ ?_, b80007b14_pc h', ?_⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k' _ (by decide)
    · rw [k' .x12 (by decide), k' .x10 (by decide), k' .x11 (by decide)]; exact I₁.pad

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
