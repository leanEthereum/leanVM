import Rv64Verifier.Proofs.Bus.VbbTail55

/-!
# `verify_bus_balance`'s side loop: the block loop

From `0x8000787c` (`Ev`): the sum gains the selector times the weight times the form's value plus
one (`accB`, `blkFold_acc`), to the next block's head or past the last. One block (`blkIter`) and
all of them (`blkLoop`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem eOf3_xor1 (a b c : Word) : eOf3 (a ^^^ 1) b c = eOf3 a b c + 1 :=
  eq_of_limbs (by rw [limbs_add, limbs_eOf3', limbs_eOf3', limbs_one]; simp)

/-- The fold's sum after block `k`. -/
theorem blkFold_acc {s : MachineState} {point : List E} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {forms : List (List Form)} {k : Nat}
    (hb : blocksAt s (blkVec s i) = sd.1) (hk : k < min sd.2.1.tables.length sd.1.length)
    (hL : (s.getMem (blkAddr s i k + 24)).toNat ≤ point.length) :
    (blkFold point i sd forms (k + 1)).2 = (blkFold point i sd forms k).2 +
      (tbSel sd point).getD k 0 *
        ((1 + bitE (s.getMem (blkAddr s i k + 32)) (s.getMem (blkAddr s i k + 24)).toNat) *
          padLow (s.getMem (blkAddr s i k + 32)) point (s.getMem (blkAddr s i k + 24)).toNat) *
        (formEvaluateRust (blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2)
          (tables.getD (blkOwner s i k) default).padding + 1) := by
  rw [blkFold_succ hk, blocks_get hb]
  simp only [busBlockStepRust, blockAt, blkOwner, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [paddingWeightRust_eq_padLow, List.length_take, min_eq_left hL,
    padLow_take _ _ _ _ (le_refl _)]

set_option maxRecDepth 8192 in
/-- From `0x8000787c` to the next block's head, or past the last block. -/
theorem accB (hMul : MulSpec) {s z h e t₀ t₆ t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} {k : Nat}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (hPb : n = 0 ∨ heapNext z ≤ P.toNat)
    (En : Entry s z h e i sd point P n) (B : Blk s z h e t₀ i sd point P n forms tot k)
    (hk : k < min sd.2.1.tables.length sd.1.length)
    (V : Ev s z h e t₀ t₆ t i sd point P n forms tot k) (hpc : t.pc = 0x8000787c) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
      (Blk s z h e t' i sd point P n forms tot (k + 1) ∧
        ((k + 1 < min sd.2.1.tables.length sd.1.length ∧ t'.pc = 0x800078f0) ∨
          (k + 1 = min sd.2.1.tables.length sd.1.length ∧ t'.pc = 0x80007b24)))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hS : 1344 ≤ (s.getReg .x2).toNat := by omega
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have Qt := V.q
  have D := Qt.cd
  have sp : t.getReg .x2 = s.getReg .x2 - 1344 := Qt.cur.inv.sp
  -- `0x8000787c`: the form's value plus one
  obtain ⟨a₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000787c_spec hpc (by
    rv_eval [sp]; and_intros <;> valid_access hval [hb1])
  have k₁ := b8000787c_keeps h₁
  have fr₁ : DFrame t a₁ (Within · (s.getReg .x2 - 128) 24) := by
    have := DFrame.of_memFrame (b8000787c_frame h₁ (by rw [sp]; addr_omega [hb1]))
    rw [sp] at this; exact this.mono fun a ha ↦ by addr_omega [ha, hb1]
  have Q₁ := Qt.blk hpre hsz (fr₁.mono fun a ha ↦ by addr_omega [ha, hb1]) (k₁ .x2 (by decide))
    fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact k₁ _ (by decide)
  have e128 : eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 128) =
      formEvaluateRust (blockFormRust (blockAt s (blkAddr s i k)) sd.2.2.2.1 sd.2.2.2.2)
        (tables.getD (blkOwner s i k) default).padding + 1 := by
    rw [← V.ev, eAt_eq_eOf3 t, ← eOf3_xor1]
    have m0 := b8000787c_m_x2_1216 h₁
    have m8 := b8000787c_m_x2_1224 h₁
    have m16 := b8000787c_m_x2_1232 h₁
    rw [sp] at m0 m8 m16
    refine eAt_three hS (by omega) (by omega) ((sp_slot (off := 1216) hS (by omega) m0).trans ?_)
      ((sp_slot (off := 1224) hS (by omega) m8).trans ?_)
      ((sp_slot (off := 1232) hS (by omega) m16).trans ?_)
    · congr 2; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    · congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    · congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e152 : eAt a₁ (s.getReg .x2 - BitVec.ofNat 64 152) = eAt t (s.getReg .x2 - BitVec.ofNat 64 152) :=
    fr₁.eAt fun q hq hw ↦ by addr_omega [hw, hq, hb1]
  rw [V.w] at e152
  -- `mul`: the block's term into `S - 248`
  obtain ⟨v₁, hrv₁, ⟨hpv₁, hp₁, Qv₁, frv₁, val₁⟩ | hd⟩ := Q₁.mul hMul hpre hsz (b8000787c_pc h₁)
    (o := 248) (a := 152) (b := 128)
    (by rw [b8000787c_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b8000787c_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b8000787c_x12 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by omega) (by omega) (by omega) (by omega) (by omega)
  swap
  · exact ⟨v₁, hr₁.trans hrv₁, Or.inl hd⟩
  rw [e152, e128] at val₁
  have spv₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := (hp₁.reg .x2).trans ((k₁ .x2 (by decide)).trans sp)
  -- `0x800078ac`
  obtain ⟨t', hr₂, h₂⟩ := Sym.BlockSpec.reaches b800078ac_spec
    (by rw [hpv₁, returnAddress_eq, b8000787c_x1 h₁]; decide) (by
      rv_eval [spv₁]; and_intros <;> valid_access hval [hb1])
  have m₂ := b800078ac_mem_same h₂
  have k₂ := b800078ac_keeps h₂
  have Q₂ := Qv₁.blk hpre hsz (DFrame.of_same m₂ _) (k₂ .x2 (by decide)) fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact k₂ _ (by decide)
  have slotV (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j)
      (h2 : j ≤ 104 ∨ 304 ≤ j) := slot_of_fr hpre D.mm Qv₁.fr hj hj2 h1 h2
  have rd (off j : Nat) (hj : off + j = 1344) (hj1 : 1144 ≤ j) (hj2 : j ≤ 1344) :
      v₁.getMem (v₁.getReg .x2 + BitVec.ofNat 64 off) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) := by
    rw [spv₁, ← slotV j (by omega) hj2 (Or.inr hj1) (Or.inr (by omega))]
    congr 1; apply BitVec.eq_of_toNat_eq; addr_omega [hb1, hj]
  have accT : eAt v₁ (s.getReg .x2 - BitVec.ofNat 64 1128) = (blkFold point i sd forms k).2 := by
    rw [← B.acc, ← D.acc]
    exact Qv₁.fr.eAt fun q hq hw ↦ by rcases hw with (hw | hw) | hw <;> addr_omega [hw, hq, hb1]
  have acc' : eOf3 (t'.getReg .x17) (t'.getReg .x16) (t'.getReg .x15) =
      (blkFold point i sd forms (k + 1)).2 := by
    rw [blkFold_acc En.blocks hk V.lr, b800078ac_x17 h₂, b800078ac_x16 h₂, b800078ac_x15 h₂,
      eOf3_xor, ← val₁, ← accT, add_comm]
    rw [spv₁]
    congr 1
    · exact (eAt_three hS (by omega) (by omega) (sp_slot (off := 216) hS (by omega) rfl)
        (sp_slot (off := 224) hS (by omega) rfl) (sp_slot (off := 232) hS (by omega) rfl)).symm
    · exact (eAt_three hS (by omega) (by omega) (sp_slot (off := 1096) hS (by omega) rfl)
        (sp_slot (off := 1104) hS (by omega) rfl) (sp_slot (off := 1112) hS (by omega) rfl)).symm
  have x24' : t'.getReg .x24 = BitVec.ofNat 64 (k + 1) := by
    rw [k₂ .x24 (by decide), Qv₁.x24, D.regs .x24 (by decide), B.x24]
    apply BitVec.eq_of_toNat_eq
    have hk64 : k + 1 < 2 ^ 64 := by have := En.n64; have := En.m; omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
    omega
  have BB : Blk s z h e t' i sd point P n forms tot (k + 1) := by
    refine Mm.blk (Q₂.mm hpre hsz hPb) (fun r hr ↦ ?_) x24' acc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k₂ .x2 (by decide), spv₁]; exact B.cur.inv.sp.symm.trans (B.regs .x2 (by decide))
    · rw [b800078ac_x9 h₂]; exact (rd 184 1160 rfl (by omega) (by omega)).trans (En.x9.symm)
    · rw [b800078ac_x18 h₂]; exact (rd 176 1168 rfl (by omega) (by omega)).trans (En.x18.symm)
    · rw [b800078ac_x20 h₂]; exact (rd 136 1208 rfl (by omega) (by omega)).trans (En.x20.symm)
    · rw [b800078ac_x21 h₂]; exact (rd 128 1216 rfl (by omega) (by omega)).trans (En.x21.symm)
    · rw [b800078ac_x22 h₂]; exact (rd 192 1152 rfl (by omega) (by omega)).trans (En.i1152.trans En.x22.symm)
    · rw [b800078ac_x25 h₂]; exact (rd 112 1232 rfl (by omega) (by omega)).trans (En.n1232.trans En.x25.symm)
    · rw [b800078ac_x26 h₂]; exact (rd 144 1200 rfl (by omega) (by omega)).trans (En.x26.symm)
  have hx24 : v₁.getReg .x24 = BitVec.ofNat 64 (k + 1) := (k₂ .x24 (by decide)).symm.trans x24'
  have hm := En.m
  have hm128 : v₁.getMem (v₁.getReg .x2 + 128) = e.getMem (s.getReg .x2 - 1216) :=
    rd 128 1216 rfl (by omega) (by omega)
  have hk1 : k + 1 < 2 ^ 64 := by have := En.n64; have := (e.getMem (s.getReg .x2 - 1216)).isLt; omega
  rcases Nat.lt_or_ge (k + 1) (min sd.2.1.tables.length sd.1.length) with hlt | hge
  · refine ⟨t', hr₁.trans (hrv₁.trans hr₂), Or.inr ⟨BB, Or.inl ⟨hlt, b800078ac_pc_not_taken h₂ ?_⟩⟩⟩
    rw [hx24, hm128]; intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1] at this; omega
  · refine ⟨t', hr₁.trans (hrv₁.trans hr₂), Or.inr ⟨BB, Or.inr ⟨by omega,
      b800078ac_pc_taken h₂ ?_⟩⟩⟩
    rw [hx24, hm128]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk1]; omega

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
