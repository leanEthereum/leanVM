import Rv64Verifier.Proofs.Multilinear.EqKernelInv

/-!
# `eq_kernel`: the prologue and the outer loop's head

`prologue` runs from the entry to the outer loop (`OInv`, `k = 0`) or, for an empty point, to the
epilogue (`Exit`); `outer_head` from the outer loop's head through `Scaler::new` to the inner
loop (`IInv`, `j = 0`), or to the trap that ends a point of `64` or more coordinates.
-/

namespace Rv64Verifier.Proofs.Multilinear.EqKernel
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Contracts
  Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.MultilinearWords
  Rv64Verifier.Blocks.F51 Rv64Verifier.Proofs.Multilinear.ScalerFill
  Rv64Verifier.Proofs.Multilinear.EqKernelWin
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The prologue -/

theorem prologue (hF : FromElemSpec) {s : MachineState} (hpc : s.pc = 0x8000cb38)
    (hpre : EqKernelPre s) :
    ∃ u, Reaches Image.code s u ∧ ((∃ C P nx, OInv s u C P nx 0) ∨ (∃ C P nx, Exit s u C P nx) ∨
      Dead Image.code u) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hof := hpre.outFree
  have hos := hpre.outStack
  have hor := hpre.outRodata
  simp only [Outside] at hof
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cb38_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000cb38_keeps h₁
  have hm₁ := b8000cb38_frame h₁ (by addr_omega [hb])
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := {
    sp := b8000cb38_x2 h₁
    slots := by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000cb38_m_x2_n8 h₁, b8000cb38_m_x2_n16 h₁, b8000cb38_m_x2_n24 h₁,
        b8000cb38_m_x2_n32 h₁, b8000cb38_m_x2_n40 h₁, b8000cb38_m_x2_n48 h₁,
        b8000cb38_m_x2_n56 h₁, b8000cb38_m_x2_n64 h₁, b8000cb38_m_x2_n72 h₁,
        b8000cb38_m_x2_n80 h₁, b8000cb38_m_x2_n88 h₁, b8000cb38_m_x2_n96 h₁,
        b8000cb38_m_x2_n104 h₁⟩
    dw := fun a ha _ ↦ hm₁ a fun hw ↦ ha (Or.inr (Or.inl (by addr_omega [hw, hb])))
    next := hm₁ _ (by addr_omega [hb, hnx8])
    mono := Nat.le_refl _
    fits := hheap.hi }
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 208 := b8000cb38_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
  have hx12₁ : t₁.getReg .x12 = BitVec.ofNat 64 (2 ^ nm s) :=
    h₁.reg_eq .x12 rfl (by rv_eval []; simp [nm])
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ fromElemStack = s.getReg .x2 - 320 := by
    simp only [stackLo, fromElemStack, tryAllocStack, hsp₁, Sym.sub_sub_lit]; rfl
  have hrod₁ : RodataOk t₁ := hpre.rodata.frame hm₁ (by addr_omega [hb, hro])
  have hN : 2 ^ nm s < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (nm_lt s)
  have hpre₁ : FromElemPre t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; exact outValid hpre
    elem := by rw [b8000cb38_x11 h₁]; exact ScalerNew.zero_valid
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside, hn₁]
      exact hof
    outStack := by rw [hx10₁, hsl]; addr_omega [hb, hos]
    elemFree := by
      rw [b8000cb38_x11 h₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega []), by addr_omega []⟩
    elemStack := by rw [b8000cb38_x11 h₁, hsl]; addr_omega [hro, hb]
    elemOut := by rw [b8000cb38_x11 h₁, hx10₁]; addr_omega [hor] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hF.call hr₁ (b8000cb38_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr (Or.inr hdead)⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have hfit₂ := hpost₂.heap.hi
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := inv₁.step hpre (DwFrame.of_byte hfr₂)
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr (Or.inr ha)))
    (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · addr_omega [ha, hb, hos]
      · addr_omega [ha, hb]
      · addr_omega [ha, hb, hnx8]
      · simp only [Fresh] at ha; addr_omega [ha, hb, hab, hfit₂])
    rfl (by rw [← heapNext, ← heapNext, ← hn₁]; exact hpost₂.mono) hfit₂ (hpres₂.reg .x2)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 208 := (hpres₂.reg .x2).trans hsp₁
  have hvec := hpost₂.vec
  have hlen₂ := hpost₂.len
  have hel₂ := hpost₂.elems
  have hfresh := hpost₂.fresh
  rw [hx10₁] at hvec hlen₂ hel₂ hfresh
  rw [hx12₁] at hlen₂ hel₂ hfresh
  rw [b8000cb38_x11 h₁] at hel₂
  obtain ⟨C, hC⟩ : ∃ C, C = t₂.getMem (s.getReg .x10) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x10 + 8) := ⟨_, rfl⟩
  have hzero : eAt t₁ 0xa0000068 = 0 := by
    apply eAt_eq_of_limbs
    rv_eval [hrod₁.word (a := 0xa0000068) (v := 0), hrod₁.word (a := 0xa0000070) (v := 0),
      hrod₁.word (a := 0xa0000078) (v := 0)]
    rfl
  rw [hzero] at hel₂
  simp only [NewBuf, hn₁, vecPtr, ← hP] at hfresh
  obtain ⟨⟨hraw1, hraw2⟩, hcap⟩ := hvec
  have hlen' : t₂.getMem (s.getReg .x10 + 16) = BitVec.ofNat 64 (2 ^ nm s) := hlen₂
  simp only [vecPtr, vecCap, vecLen, ← hP, ← hC, hlen'] at hraw1 hraw2 hcap
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN] at hcap hfresh
  have hpos : 0 < 2 ^ nm s := Nat.two_pow_pos _
  have hPlo : heapNext s ≤ P.toNat := by rcases hfresh.2 with h0 | h0 <;> omega
  have hPtop : P.toNat + 24 * C.toNat ≤ (t₂.getMem nextAddr).toNat := by
    rcases hraw2 with h0 | h0
    · omega
    · simp only [heapNext] at h0; omega
  have hlo := hheap.lo
  have hPN : P.toNat + 24 * 2 ^ nm s ≤ heapEnd := by
    simp only [heapNext] at hfit₂; omega
  have res₂ : Res s t₂ C P (t₂.getMem nextAddr) :=
    ⟨inv₂, hC.symm, hP.symm, hlen', hraw1, hPlo, hcap, hPtop⟩
  have hx18₂ : t₂.getReg .x18 = s.getReg .x10 := (hpres₂.reg .x18).trans (b8000cb38_x18 h₁)
  -- `0x8000cb94`: the length to `S - 184`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000cb94_spec
    (by rw [hpc₂, returnAddress_eq, b8000cb38_x1 h₁]; decide) (by
      rv_eval [hsp₂, hx18₂]
      exact ⟨by valid_access hst.valid [hb], by valid_access (outValid hpre) [hb]⟩)
  have k₃ := b8000cb94_keeps h₃
  have hm₃ := b8000cb94_frame h₃ (by rw [hsp₂]; addr_omega [hb])
  rw [hsp₂] at hm₃
  rv_eval [] at hm₃
  have hpc₃ := b8000cb94_pc_not_taken h₃ (by
    rw [hx18₂, hlen']
    intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN] at this
    simp at this)
  have m184 := b8000cb94_m_x2_24 h₃
  rw [hsp₂, hx18₂, hlen'] at m184
  rv_eval [] at m184
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 208 := (k₃ .x2 (by decide)).trans hsp₂
  have hnx₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := hm₃ _ (by addr_omega [hb, hnx8])
  have res₃ := res₂.step hpre (DwFrame.of_mem hm₃) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ by addr_omega [ha, hb]) hnx₃ (Nat.le_refl _) inv₂.fits (k₃ .x2 (by decide))
  have hx18₃ : t₃.getReg .x18 = s.getReg .x10 := (k₃ .x18 (by decide)).trans hx18₂
  have hfit₃ := res₃.inv.fits
  -- `0x8000cba0`: `out[0] = ONE`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000cba0_spec hpc₃ (by
    rv_eval [hx18₃, res₃.ptr]
    and_intros
    · exact heap_valid' (by addr_omega [hPlo, hlo, hPN, hpos])
        (by addr_omega [hPlo, hlo, hPN, hpos]) (by addr_omega [hPlo, hlo, hraw1, hPN, hpos])
    · exact heap_valid' (by addr_omega [hPlo, hlo, hPN, hpos])
        (by addr_omega [hPlo, hlo, hPN, hpos]) (by addr_omega [hPlo, hlo, hraw1, hPN, hpos])
    · exact heap_valid' (by addr_omega [hPlo, hlo, hPN, hpos])
        (by addr_omega [hPlo, hlo, hPN, hpos]) (by addr_omega [hPlo, hlo, hraw1, hPN, hpos])
    · valid_access (outValid hpre) [hb])
  have k₄ := b8000cba0_keeps h₄
  have hfr₄ : ∀ a, ¬ Within a P 24 → t₄.getMem a = t₃.getMem a := by
    intro a ha
    refine h₄.frame a ?_
    rv_eval [hx18₃, res₃.ptr]
    and_intros <;> intro heq <;> apply ha <;> rw [heq] <;> addr_omega [hPN, hpos]
  have hx8₄ : t₄.getReg .x8 = P := by rw [b8000cba0_x8 h₄, hx18₃, res₃.ptr]
  have hone : eAt t₄ P = 1 := by
    apply eAt_eq_of_limbs
    have m0 := b8000cba0_m0 h₄
    have m1 := b8000cba0_m1 h₄
    have m2 := b8000cba0_m2 h₄
    rw [hx18₃, res₃.ptr] at m0 m1 m2
    rw [m0, m1, m2, k₃ .x19 (by decide), hpres₂.reg .x19, b8000cb38_x19 h₁, limbs_one]
  have res₄ := res₃.step hpre (DwFrame.of_mem hfr₄)
    (fun a ha ↦ Or.inr (Or.inr ⟨by addr_omega [ha, hPlo], by addr_omega [ha, hPtop, hcap, hpos]⟩))
    (fun a ha ↦ by addr_omega [ha, hb, hab, hPN, hpos])
    ((hfr₄ _ (by addr_omega [hPN, hpos])).trans hnx₃) (Nat.le_refl _) hfit₃ (k₄ .x2 (by decide))
  have hbuf₄ : eListAt t₄ P (2 ^ nm s) =
      (List.replicate (2 ^ nm s) (0 : E)).set 0 1 := by
    have h1 := eListAt_set1 (u := t₃) (v := t₄) (P := P) hpos (by omega)
      (fun a ha ↦ hfr₄ a (by simpa using ha))
    simp only [Nat.mul_zero, BitVec.add_zero, hone] at h1
    rw [h1]
    congr 1
    have h2 : eListAt t₂ P (2 ^ nm s) = List.replicate (2 ^ nm s) 0 := by
      have := hel₂
      simp only [vecEs, vecPtr, vecLen, ← hP, hlen', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN] at this
      exact this
    rw [← h2]
    exact eListAt_frame hm₃ (by addr_omega [hPlo, hlo, hPN, hb, hab]) (by omega)
  have hx9₃ : t₃.getReg .x9 = s.getReg .x12 := by
    rw [k₃ .x9 (by decide), hpres₂.reg .x9, b8000cb38_x9 h₁]
  by_cases hn0 : s.getReg .x12 = 0
  · have hn0' : (s.getReg .x12).toNat = 0 := by rw [hn0]; rfl
    refine ⟨t₄, hr₂.trans (hr₃.trans hr₄), Or.inr (Or.inl ⟨C, P, _,
      { toRes := res₄
        pc := b8000cba0_pc_taken h₄ (by rw [hx9₃, hn0])
        buf := ?_ }⟩)⟩
    have hnm : nm s = 0 := by simp [nm, hn0']
    rw [hbuf₄, pt, hn0', hnm]
    simp [eListAt, eqKernel]
  have hnpos : 0 < (s.getReg .x12).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) hn0
    · exact h
  have hpb := ValidMemRange.bounds (pointValid hpre hnpos) (by omega)
  -- `0x8000cbb4`: the constants
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000cbb4_spec
    (b8000cba0_pc_not_taken h₄ (by rw [hx9₃]; exact hn0)) (by
      rv_eval [k₄ .x2 (by decide), hsp₃]
      and_intros <;> valid_access hst.valid [hb])
  have k₅ := b8000cbb4_keeps h₅
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 208 := (k₄ .x2 (by decide)).trans hsp₃
  have hm₅ := b8000cbb4_frame h₅ (by rw [hsp₄]; addr_omega [hb])
  rw [hsp₄] at hm₅
  rv_eval [] at hm₅
  have hx20₄ : t₄.getReg .x20 = s.getReg .x11 := by
    rw [k₄ .x20 (by decide), k₃ .x20 (by decide), hpres₂.reg .x20, b8000cb38_x20 h₁]
  have hx9₄ : t₄.getReg .x9 = s.getReg .x12 := (k₄ .x9 (by decide)).trans hx9₃
  have mstop := b8000cbb4_m_x2_16 h₅
  have mmagic := b8000cbb4_m_x2_8 h₅
  rw [hsp₄, hx20₄, hx9₄] at mstop
  rw [hsp₄] at mmagic
  rv_eval [] at mstop mmagic
  have res₅ := res₄.step hpre (DwFrame.of_mem hm₅) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ by addr_omega [ha, hb]) ((hm₅ _ (by addr_omega [hb, hnx8])).trans
      ((hfr₄ _ (by addr_omega [hPN, hpos])).trans hnx₃)) (Nat.le_refl _) res₄.inv.fits
    (k₅ .x2 (by decide))
  refine ⟨t₅, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inl ⟨C, P, _,
    { toRes := res₅
      x8 := (k₅ .x8 (by decide)).trans hx8₄
      x24 := b8000cbb4_x24 h₅
      x26 := b8000cbb4_x26 h₅
      x27 := b8000cbb4_x27 h₅
      magic := mmagic
      stop := by rw [mstop]; addr_omega [hpb]
      nlen := by rw [hm₅ _ (by addr_omega [hb]), hfr₄ _ (by addr_omega [hb, hab, hPN, hpos])]; exact m184
      pc := b8000cbb4_pc h₅
      lt := hnpos
      le := Nat.zero_le _
      x11 := by rw [b8000cbb4_x11 h₅, hx20₄]; simp
      x13 := b8000cbb4_x13 h₅
      buf := ?_ }⟩⟩
  rw [eListAt_frame hm₅ (by addr_omega [hPlo, hlo, hPN, hb, hab]) (by omega), hbuf₄, pow_zero]
  exact replicate_set hpos

theorem outer_head (hS : ScalerSpec) {s : MachineState} (hpre : EqKernelPre s) {C P nx : Word}
    {k : Nat} {u : MachineState} (hu : OInv s u C P nx k) :
    ∃ v, Reaches Image.code u v ∧ ((∃ T nx', IInv s v C P T nx' k 0) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hlo := hpre.heap.lo
  have hk := hu.lt
  have hsp := hu.inv.sp
  have hpb := ValidMemRange.bounds (pointValid hpre (by omega)) (by omega)
  have hfit := hu.inv.fits
  have hmono := hu.inv.mono
  have htop := hu.top
  have hroom := hu.room
  have hPlo := hu.lo
  obtain ⟨hPN, hn27⟩ := hu.small
  have hpk := Nat.two_pow_pos k
  simp only [heapEnd] at hPN
  have hkle := hu.le
  -- `0x8000cc10`, `0x8000cc20`: the bounds checks
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cc10_spec hu.pc (by
    rv_eval [hsp]; valid_access hst.valid [hb])
  have k₁ := b8000cc10_keeps h₁
  have hm₁ := b8000cc10_mem_same h₁
  have hpow' : 2 ^ k ≤ 2 ^ nm s := Nat.pow_le_pow_right (by norm_num) hkle
  have e2 : (2 : Word) * BitVec.ofNat 64 (2 ^ k) = BitVec.ofNat 64 (2 * 2 ^ k) :=
    ofNat_mul_pow (c := 2) (k := k) (by decide) (by omega)
  by_cases hkm : ¬ k < nm s
  · refine ⟨u₁, hr₁, Or.inr (dead_of_fetch ?_)⟩
    have hkeq : k = nm s := by omega
    rw [h₁.pc_eq (v := 0x8000ce60) (by
      rv_eval [hsp, hu.nlen, hu.x13, mod64 (show k < 64 by omega), e2]
      rw [show (BitVec.ofNat 64 (2 ^ nm s)).ult (BitVec.ofNat 64 (2 * 2 ^ k)) = true by
        simp only [BitVec.ult, decide_eq_true_eq]
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega), ← hkeq]
        omega]
      rfl)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  simp only [Decidable.not_not] at hkm
  have hpow : 2 ^ (k + 1) ≤ 2 ^ nm s := Nat.pow_le_pow_right (by norm_num) hkm
  rw [pow_succ] at hpow
  have hpc₁ : u₁.pc = 0x8000cc20 := h₁.pc_eq (by
    rv_eval [hsp, hu.nlen, hu.x13, mod64 (show k < 64 by omega), e2]
    rw [show (BitVec.ofNat 64 (2 ^ nm s)).ult (BitVec.ofNat 64 (2 * 2 ^ k)) =
      false by
        simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega]
    rfl)
  have hx9₁ : u₁.getReg .x9 = BitVec.ofNat 64 (2 * 2 ^ k) :=
    h₁.reg_eq .x9 rfl (by rv_eval [hu.x13, mod64 (show k < 64 by omega), e2])
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000cc20_spec hpc₁ (by rv_eval [])
  have k₂ := b8000cc20_keeps h₂
  have hm₂ := b8000cc20_mem_same h₂
  have hx13₁ : u₁.getReg .x13 = BitVec.ofNat 64 k := (k₁ .x13 (by decide)).trans hu.x13
  have hpc₂ := b8000cc20_pc_not_taken h₂ (by rw [hx13₁]; addr_omega [hkm, hn27])
  -- `0x8000cc28`: `Scaler::new(S - 136, &point[k], 1 << k)`
  have hsp₂ : u₂.getReg .x2 = s.getReg .x2 - 208 := by
    rw [k₂ .x2 (by decide), k₁ .x2 (by decide), hsp]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000cc28_spec hpc₂ (by
    rv_eval [hsp₂]; and_intros <;> valid_access hst.valid [hb])
  have k₃ := b8000cc28_keeps h₃
  have hm₃ := b8000cc28_frame h₃ (by rw [hsp₂]; addr_omega [hb])
  rw [hsp₂] at hm₃
  rv_eval [] at hm₃
  have hx13₂ : u₂.getReg .x13 = BitVec.ofNat 64 k := (k₂ .x13 (by decide)).trans hx13₁
  have hx11₂ : u₂.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := by
    rw [k₂ .x11 (by decide), k₁ .x11 (by decide), hu.x11]
  have m168 := b8000cc28_m_x2_40 h₃
  have m176 := b8000cc28_m_x2_32 h₃
  rw [hsp₂, hx11₂] at m168
  rw [hsp₂, hx13₂] at m176
  rv_eval [] at m168 m176
  have hx12₃ : u₃.getReg .x12 = BitVec.ofNat 64 (2 ^ k) :=
    h₃.reg_eq .x12 rfl (by rv_eval [hx13₂, and63 (show k < 64 by omega)]; simp)
  have hx18₃ : u₃.getReg .x18 = BitVec.ofNat 64 (2 ^ k) :=
    h₃.reg_eq .x18 rfl (by rv_eval [hx13₂, and63 (show k < 64 by omega)]; simp)
  have hx20₃ : u₃.getReg .x20 = BitVec.ofNat 64 (24 * 2 ^ k) :=
    h₃.reg_eq .x20 rfl (by
      rv_eval [hx13₂, and63 (show k < 64 by omega)]
      exact ofNat_mul_pow (c := 24) (k := k) (by decide) (by omega))
  have hx10₃ : u₃.getReg .x10 = s.getReg .x2 - 136 := by
    rw [b8000cc28_x10 h₃, hsp₂]; rv_eval []
  have hx11₃ : u₃.getReg .x11 = s.getReg .x11 + BitVec.ofNat 64 (24 * k) :=
    (k₃ .x11 (by decide)).trans hx11₂
  have hsp₃ : u₃.getReg .x2 = s.getReg .x2 - 208 := (k₃ .x2 (by decide)).trans hsp₂
  have hreg₃ (r : Reg) (hr : r ∈ midRegs) : u₃.getReg r = u.getReg r := by
    rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have mid₃ := hu.toMid.step hpre (DwFrame.of_mem (fun a ha ↦ (hm₃ a ha).trans
      ((hm₂ a).trans (hm₁ a)))) (fun a ha ↦ Or.inl (by addr_omega [ha, hb]))
    (fun a ha ↦ ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩)
    ((hm₃ _ (by addr_omega [hb, hnx8])).trans ((hm₂ _).trans ((hm₁ _).trans hu.inv.next)))
    (Nat.le_refl _) hfit hreg₃
  have hbuf₃ : eListAt u₃ P (2 ^ nm s) = eListAt u P (2 ^ nm s) :=
    eListAt_frame (fun a ha ↦ (hm₃ a ha).trans ((hm₂ a).trans (hm₁ a)))
      (by addr_omega [hPN, hPlo, hlo, hb, hab]) (by omega)
  have hsl : stackLo u₃ scalerStack = s.getReg .x2 - 432 := by
    simp only [stackLo, scalerStack, fromElemStack, tryAllocStack, hsp₃, Sym.sub_sub_lit]; rfl
  have hof := pointOutside hpre (by omega)
  simp only [Outside] at hof
  have hn₃ : heapNext u₃ = nx.toNat := by simp only [heapNext, mid₃.inv.next]
  have hpre₃ : ScalerPre u₃ := {
    heap := ⟨by rw [hn₃]; omega, by rw [hn₃]; exact hfit⟩
    out := by rw [hx10₃]; valid_sub hst.valid [hb]
    r := by rw [hx11₃]; valid_sub (pointValid hpre (by omega)) [hpb, hk]
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₃]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hab, hb], by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₃]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₃, hsl]; addr_omega [hb]
    rFree := by
      rw [hx11₃]
      simp only [Outside, hn₃]
      refine ⟨?_, by addr_omega [hof.2, hk, hpb]⟩
      rcases hof.1 with h | h
      · exact Or.inl (by addr_omega [h, hk, hpb, hmono])
      · exact Or.inr (by addr_omega [h, hk, hpb])
    rStack := by rw [hx11₃, hsl]; addr_omega [hpre.pointStack, hk, hpb, hb]
    rOut := by rw [hx11₃, hx10₃]; addr_omega [hpre.pointStack, hk, hpb, hb]
    rodata := mid₃.inv.rodataOk hpre }
  obtain ⟨w, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ := hS.call hr₃ (b8000cc28_pc h₃) hpre₃
  swap
  · exact ⟨w, hr₁.trans (hr₂.trans hr₄), Or.inr hdead⟩
  have hfr₄ := hpost₄.frame
  rw [hx10₃, hsl] at hfr₄
  have hfit₄ := hpost₄.heap.hi
  have hmono₄ := hpost₄.mono
  rw [hn₃] at hmono₄
  simp only [heapNext] at hfit₄ hmono₄
  have hn₃' : (u₃.getMem nextAddr).toNat = nx.toNat := hn₃
  have hsu : (s.getMem nextAddr).toNat ≤ nx.toNat := hmono
  have hX4 (a : Word) (ha : Within a (s.getReg .x2 - 136) 32 ∨
      Within a (s.getReg .x2 - 432) scalerStack ∨ Within a nextAddr 8 ∨ Fresh u₃ w a) :
      LW s (w.getMem nextAddr) a := by
    simp only [LW]
    rcases ha with ha | ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inl (by addr_omega [ha, hb])
    · exact Or.inr (Or.inl ha)
    · simp only [Fresh, heapNext] at ha
      exact Or.inr (Or.inr ⟨by simp only [heapNext]; omega, ha.2⟩)
  have miss4 (a : Word) (h1 : (s.getReg .x2).toNat - 200 ≤ a.toNat)
      (h2 : a.toNat < (s.getReg .x2).toNat - 136) : ¬ (Within a (s.getReg .x2 - 136) 32 ∨
        Within a (s.getReg .x2 - 432) scalerStack ∨ Within a nextAddr 8 ∨ Fresh u₃ w a) := by
    rintro (ha | ha | ha | ha)
    · addr_omega [ha, hb, h1, h2]
    · addr_omega [ha, hb, h1, h2]
    · addr_omega [ha, hb, h1, h2, hnx8]
    · simp only [Fresh, heapNext] at ha; addr_omega [ha, hb, h1, h2, hab, hfit₄]
  have hdw₄ := DwFrame.of_byte hfr₄
  have mid₄ := mid₃.step hpre hdw₄ hX4 (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩
      · exact ⟨by addr_omega [ha, hb], by addr_omega [ha, hb]⟩
      · exact ⟨by addr_omega [ha, hb, hnx8], by addr_omega [ha, hb, hnx8]⟩
      · simp only [Fresh, heapNext] at ha
        exact ⟨by addr_omega [ha, hb, hab, hfit₄], by addr_omega [ha, hb, hab, hfit₄]⟩)
    rfl hmono₄ hfit₄ fun r hr ↦ hpres₄ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have m168₄ : w.getMem (s.getReg .x2 - 168) = s.getReg .x11 + BitVec.ofNat 64 (24 * k) := by
    rw [DwFrame.keep hdw₄ fun i hi ↦ miss4 _ (by addr_omega [hi, hb]) (by addr_omega [hi, hb])]
    exact m168
  have m176₄ : w.getMem (s.getReg .x2 - 176) = BitVec.ofNat 64 k := by
    rw [DwFrame.keep hdw₄ fun i hi ↦ miss4 _ (by addr_omega [hi, hb]) (by addr_omega [hi, hb])]
    exact m176
  have hbuf₄ : eListAt w P (2 ^ nm s) = eListAt u P (2 ^ nm s) := by
    rw [eListAt_dw hdw₄ (fun a ha hx ↦ by
        rcases hx with hx | hx | hx | hx
        · addr_omega [ha, hx, hb, hab, hPN]
        · addr_omega [ha, hx, hb, hab, hPN]
        · addr_omega [ha, hx, hPN]
        · simp only [Fresh, heapNext] at hx; addr_omega [ha, hx, htop, hroom, hn₃'])
      (by omega), hbuf₃]
  have hsp₄ : w.getReg .x2 = s.getReg .x2 - 208 := (hpres₄.reg .x2).trans hsp₃
  have hx9₄ : w.getReg .x9 = BitVec.ofNat 64 (2 * 2 ^ k) := by
    rw [hpres₄.reg .x9, k₃ .x9 (by decide), k₂ .x9 (by decide), hx9₁]
  have hx20₄ : w.getReg .x20 = BitVec.ofNat 64 (24 * 2 ^ k) := (hpres₄.reg .x20).trans hx20₃
  have hx18₄ : w.getReg .x18 = BitVec.ofNat 64 (2 ^ k) := (hpres₄.reg .x18).trans hx18₃
  -- `0x8000cc54`..`0x8000cc7c`: the inner loop's bounds
  obtain ⟨w₁, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000cc54_spec
    (by rw [hpc₄, returnAddress_eq, b8000cc28_x1 h₃]; decide) (by rv_eval [])
  have k₅ := b8000cc54_keeps h₅
  have hpc₅ := b8000cc54_pc_not_taken h₅ (by rw [hx9₄, hx20₄]; addr_omega [hpow, hpk, hPN])
  have hd : w₁.getReg .x10 - w₁.getReg .x20 = BitVec.ofNat 64 (24 * 2 ^ k) := by
    rw [b8000cc54_x10 h₅, k₅ .x20 (by decide), hx9₄, hx20₄]; addr_omega [hpow, hpk, hPN]
  have hsp₅ : w₁.getReg .x2 = s.getReg .x2 - 208 := (k₅ .x2 (by decide)).trans hsp₄
  have hmg : w₁.getMem (w₁.getReg .x2 + 8) = 0xaaaaaaaaaaaaaaab := by
    rw [hsp₅, b8000cc54_mem_same h₅]; rv_eval [mid₄.magic]
  obtain ⟨w₂, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000cc64_spec hpc₅ (by
    rv_eval [hsp₅]; valid_access hst.valid [hb])
  have k₆ := b8000cc64_keeps h₆
  have hdiv : rv64_mulhu (w₁.getReg .x10 - w₁.getReg .x20) (w₁.getMem (w₁.getReg .x2 + 8)) >>> 4 =
      BitVec.ofNat 64 (2 ^ k) := by
    rw [hd, hmg]; exact div24 (by omega)
  have hx10₆ : w₂.getReg .x10 = BitVec.ofNat 64 (2 ^ k) := h₆.reg_eq .x10 rfl (by rv_eval []; exact hdiv)
  have hx18₅ : w₁.getReg .x18 = BitVec.ofNat 64 (2 ^ k) := (k₅ .x18 (by decide)).trans hx18₄
  have hpc₆ : w₂.pc = 0x8000cc78 := h₆.pc_eq (by
    rv_eval []
    have hf : (w₁.getReg .x18).ult (rv64_mulhu (w₁.getReg .x10 - w₁.getReg .x20)
        (w₁.getMem (w₁.getReg .x2 + 8)) >>> 4) = false := by
      rw [hdiv, hx18₅]
      unfold BitVec.ult
      exact decide_eq_false (Nat.lt_irrefl _)
    simp only [hf, Bool.false_eq_true, ↓reduceIte])
  obtain ⟨w₃, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000cc78_spec hpc₆ (by rv_eval [])
  have k₇ := b8000cc78_keeps h₇
  have hsp₇ : w₃.getReg .x2 = s.getReg .x2 - 208 := by
    rw [k₇ .x2 (by decide), k₆ .x2 (by decide), hsp₅]
  obtain ⟨w₄, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000cc7c_spec (b8000cc78_pc h₇) (by
    rv_eval [hsp₇]; and_intros <;> valid_access hst.valid [hb])
  have k₈ := b8000cc7c_keeps h₈
  have hmw (a : Word) : w₄.getMem a = w.getMem a := by
    rw [b8000cc7c_mem_same h₈, b8000cc78_mem_same h₇, b8000cc64_mem_same h₆,
      b8000cc54_mem_same h₅]
  have hmw₃ (a : Word) : w₃.getMem a = w.getMem a := by
    rw [b8000cc78_mem_same h₇, b8000cc64_mem_same h₆, b8000cc54_mem_same h₅]
  have hreg₈ (r : Reg) (hr : r ∈ midRegs) : w₄.getReg r = w.getReg r := by
    rw [k₈ r (mem_of_mem hr _), k₇ r (mem_of_mem hr _), k₆ r (mem_of_mem hr _),
      k₅ r (mem_of_mem hr _)]
  have hx18₇ : w₃.getReg .x18 = BitVec.ofNat 64 (2 ^ k) := (b8000cc78_x18 h₇).trans hx10₆
  have hr0 : (List.range 0).foldl (Model.eqKernelStep ((pt s).getD k 0) (2 ^ k))
      (eqKernel ((pt s).take k) ++ List.replicate (2 ^ nm s - 2 ^ k) 0) =
      eqKernel ((pt s).take k) ++ List.replicate (2 ^ nm s - 2 ^ k) 0 := rfl
  have hr_eq : eAt u₃ (u₃.getReg .x11) = (pt s).getD k 0 := by
    rw [hx11₃, mid₃.inv.point hpre hk, pt, eListAt_getD' _ _ hk]
  have htag : w₄.getReg .x22 = w.getMem (s.getReg .x2 - 136) := by
    rw [b8000cc7c_x22 h₈, hsp₇, hmw₃]; rv_eval []
  have hx12₃' : (u₃.getReg .x12).toNat = 2 ^ k := by
    rw [hx12₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨w₄, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₇.trans hr₈))))),
    Or.inl ⟨w.getMem (s.getReg .x2 - 120), w.getMem nextAddr,
    { toMid := mid₄.same hpre hmw hreg₈
      pc := b8000cc7c_pc h₈
      lt := hkm
      jlt := hpk
      m168 := (hmw _).trans m168₄
      m176 := (hmw _).trans m176₄
      x9 := h₈.reg_eq .x9 rfl (by
        rv_eval [hx18₇]
        rw [show (BitVec.ofNat 64 (2 ^ k)).ult 1 = false by
          simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_lt]
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          exact hpk]
        simp)
      x20 := by
        rw [b8000cc7c_x20 h₈, k₇ .x8 (by decide), k₆ .x8 (by decide), k₅ .x8 (by decide),
          mid₄.x8, k₇ .x20 (by decide), k₆ .x20 (by decide), k₅ .x20 (by decide), hx20₄]
      x25 := b8000cc7c_x25 h₈
      sc := {
        x19 := by rw [b8000cc7c_x19 h₈, hsp₇, hmw₃]; rv_eval []
        plain := fun hne ↦ by
          by_cases hl : (u₃.getReg .x12).toNat < 256
          · obtain ⟨-, he⟩ := hpost₄.plain hl
            rw [hx10₃] at he
            rv_eval [] at he
            rw [← hr_eq, ← he]
            unfold eAt
            rw [hmw, hmw, hmw]
          · have h0 := (hpost₄.table (by omega)).1
            rw [hx10₃] at h0
            exact absurd (htag.trans h0) hne
        table := fun he ↦ by
          by_cases hl : (u₃.getReg .x12).toNat < 256
          · have := (hpost₄.plain hl).1
            rw [hx10₃, ← htag, he] at this
            exact absurd this (by decide)
          obtain ⟨-, hvok, hvlen, hvmap, hvnew⟩ := hpost₄.table (by omega)
          rw [hx10₃] at hvok hvlen hvmap hvnew
          simp only [vecLen, vecPtr, vecEs] at hvlen hvmap hvnew
          rv_eval [] at hvlen hvmap hvnew
          simp only [NewBuf, hn₃] at hvnew
          rw [hvlen] at hvmap
          have hT := hvnew.2
          simp only [heapNext] at hT
          refine ⟨by rw [b8000cc7c_x23 h₈, hsp₇, hmw₃]; rv_eval [hvlen], ⟨hvnew.1,
            by have := hpre.heap.lo; simp only [heapStart, heapNext] at this hmono ⊢; omega,
            by simp only [tabBytes]; omega⟩, by omega, by simp only [tabBytes]; omega, ?_⟩
          rw [tab_same hmw, ScalerNew.tab_eq_map, show (2112 : Word).toNat = 2112 from rfl] at *
          rw [hvmap, hr_eq] }
      buf := by rw [hr0, eListAt_same hmw, hbuf₄]; exact hu.buf }⟩⟩

end Rv64Verifier.Proofs.Multilinear.EqKernel
