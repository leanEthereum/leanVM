import Rv64Verifier.Proofs.Pcs.VsoGlueProdsBase

/-!
# `verify_stacked_opening`'s final level: one coordinate of a query's product

From `0x8000bf00` (`PrI`): a trap past the inverses' end; `base_mul(basis, inverse)`, `1 +` it,
`E * K` of the challenge (`S - 464`), `1 +` that into `S - 160`, `mul(S - 464, S - 128, S - 160)`;
a trap past the roots' end; the product to `S - 128`; `K::square(basis)`, `base_mul(root, basis)`,
their sum the next basis. Then the next coordinate at `0x8000bf00`, or `0x8000be84` after the last.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  Rv64Verifier.FieldContracts LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem pr_eListAt_getD (s : MachineState) (p : Word) {n c : ℕ} (hc : c < n) :
    (eListAt s p n).getD c 0 = eAt s (p + BitVec.ofNat 64 (24 * c)) := by
  rw [List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hc), eListAt_getElem]

theorem pr_ofNat_sub {a k : ℕ} (h : k ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 k = BitVec.ofNat 64 (a - k) := by
  conv_lhs => rw [show a = (a - k) + k by omega, BitVec.ofNat_add]
  exact BitVec.add_sub_cancel _ _

theorem pr_ofNat_add (p : Word) (k i : ℕ) :
    p + BitVec.ofNat 64 k + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (k + i) :=
  add_ofNat_add p k i

set_option maxHeartbeats 1000000 in
/-- The coordinate's step. -/
theorem prCoord (hBM : BaseMulSpec) (hMK : MulKSpec) (hM : MulSpec) (hSq : KSquareSpec)
    {s v w t : MachineState} {n cnt i c : ℕ} {rs : List K} {xs : List E}
    {qs : List (BitVec 64)} {qw : List E} {total : E} {acc : E × K} (hpre : VsoPre s)
    (hc : QC s v w n rs xs qs qw) (h : PrI s v w t n cnt i c total acc) :
    ∃ t', Reaches Image.code t t' ∧ (Dead Image.code t' ∨
      (c + 1 < n ∧ PrI s v w t' n cnt i (c + 1) total (prG rs acc (xs.getD c 0, c))) ∨
      (c + 1 = n ∧ PrE s v w t' n cnt i total (prG rs acc (xs.getD c 0, c)).1)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  have hab := hst.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have hro := hst.rodata
  rw [stackLo_vso, vso_stack] at hro
  have hhs := hpre.heap.lo
  have hsw := hc.gs.su
  have hhw := hc.gs.heap.hi
  simp only [heapEnd] at hhw
  have hcn := h.clt
  -- the inverses, the challenges and the roots
  obtain ⟨ip8, ip1, ip2⟩ := hc.ip
  obtain ⟨rp8, rp1, rp2⟩ := hc.x21
  obtain ⟨pt8, ptb⟩ := hc.pt
  have ptb' := ptb.resolve_left (by omega)
  have imem := hc.imem
  have rmem := hc.rmem
  have xsm := hc.xs
  have hrl := hc.rlen
  have hx18 := h.x18
  have hx20 := h.x20
  have hx21 := h.x21
  generalize hipd : w.getMem (s.getReg .x2 - 784) = ip at ip8 ip1 ip2 imem hx18
  generalize hPd : w.getMem (s.getReg .x2 - 848) = P at pt8 ptb' xsm hx20
  generalize hrpd : w.getReg .x21 = rp at rp8 rp1 rp2 rmem hx21
  simp only [heapStart, heapNext] at hhs hsw
  have hRi : Region ip (8 * (n + 1)) := heap_region (by simp only [heapNext] at ip1; omega)
    (by simp only [heapEnd]; omega) ip8
  have hRr : Region rp (8 * (n + 1)) := heap_region (by simp only [heapNext] at rp1; omega)
    (by simp only [heapEnd]; omega) rp8
  have hRp : Region P (24 * n) := heap_region (by simp only [heapNext] at ptb'; omega)
    (by simp only [heapEnd]; omega) pt8
  have hinv : BF64.ofBitVec (w.getMem (ip + BitVec.ofNat 64 (8 * c))) = (rs.map (·⁻¹)).getD c 0 := by
    rw [← imem, pr_kListAt_getD _ _ (by omega)]
  have hroot : BF64.ofBitVec (w.getMem (rp + BitVec.ofNat 64 (8 * c))) = rs.getD c 0 := by
    rw [← rmem, pr_kListAt_getD _ _ (by omega)]
  have hchal : eAt w (P + BitVec.ofNat 64 (24 * c)) = xs.getD c 0 := by
    rw [← xsm, pr_eListAt_getD _ _ hcn]
  have kH (y : Word) (hy : y.toNat + 8 ≤ heapEnd) (t' : MachineState) (P' : PrX s v w t' n cnt) :
      t'.getMem y = w.getMem y := P'.keep hpre (Or.inl hy)
  -- `0x8000bf00`: a trap past the inverses
  obtain ⟨t₁, r₁, h₁⟩ := Sym.BlockSpec.reaches b8000bf00_spec h.pc trivial
  have k₁ := b8000bf00_keeps h₁
  by_cases e1 : t.getReg .x22 + t.getReg .x27 = 1
  · exact ⟨t₁, r₁, Or.inl (dead_of_fetch (by rw [b8000bf00_pc_taken h₁ e1]; exact trap))⟩
  have P₁ := h.toPrX.same hpre (b8000bf00_mem_same h₁) (k₁ .x2 (by decide)) (k₁ .x22 (by decide))
  -- `0x8000bf0c`: `base_mul(basis, inverse)`
  obtain ⟨t₂, r₂, h₂⟩ := Sym.BlockSpec.reaches b8000bf0c_spec (b8000bf00_pc_not_taken h₁ e1) (by
    rv_eval [k₁ .x18 (by decide), hx18]
    exact Region.valid hRi (by addr_omega [ip2, hhw, hcn]) (by addr_omega [ip2, hhw, hcn])
      (by addr_omega [ip2, hhw, ip8, hcn]))
  have k₂ := b8000bf0c_keeps h₂
  have P₂ := P₁.same hpre (b8000bf0c_mem_same h₂) (k₂ .x2 (by decide)) (k₂ .x22 (by decide))
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₂.gs.sp
  have sl₂ : stackLo t₂ baseMulStack = s.getReg .x2 - 1152 := by
    simp only [stackLo, sp₂, baseMulStack]; rv_eval []
  obtain ⟨t₃, r₃, ⟨pc₃, ps₃, post₃⟩ | hd⟩ := hBM.call (Reaches.refl t₂) (b8000bf0c_pc h₂)
    ⟨(hst.sub 1040 sp₂ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk,
      poolOk_of_rodata (InvR.rodata' hpre P₂.gs.inv) (by rw [sl₂]; addr_omega [hro, hb])⟩
  swap
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inl hd⟩
  have F₃ := DFrame.of_memFrame post₃.frame
  rw [sl₂] at F₃
  have P₃ := P₂.step hpre F₃ (fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hb])))
    (ps₃.reg .x2) (ps₃.reg .x22)
  have v₃ : t₃.getReg .x10 = (BF64.ofBitVec (t.getReg .x19) * (rs.map (·⁻¹)).getD c 0).toBitVec := by
    rw [post₃.value, b8000bf0c_x10 h₂, b8000bf0c_x11 h₂, k₁ .x19 (by decide), k₁ .x18 (by decide),
      hx18, kH _ (by addr_omega [ip2, hhw, hcn]) t₁ P₁]
    exact congrArg (fun z ↦ (BF64.ofBitVec (t.getReg .x19) * z).toBitVec) hinv
  -- `0x8000bf1c`: `E * K` of the challenge
  obtain ⟨t₄, r₄, h₄⟩ := Sym.BlockSpec.reaches b8000bf1c_spec
    (by rw [pc₃, returnAddress_eq, b8000bf0c_x1 h₂]; decide) trivial
  have k₄ := b8000bf1c_keeps h₄
  have P₄ := P₃.same hpre (b8000bf1c_mem_same h₄) (k₄ .x2 (by decide)) (k₄ .x22 (by decide))
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₄.gs.sp
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 464 := by
    rw [b8000bf1c_x10 h₄, P₃.gs.sp]; rv_eval []
  have x11₄ : t₄.getReg .x11 = P + BitVec.ofNat 64 (24 * c) := by
    rw [b8000bf1c_x11 h₄, ps₃.reg .x20, k₂ .x20 (by decide), k₁ .x20 (by decide), hx20]
  have sl₄ : stackLo t₄ mulKStack = s.getReg .x2 - 1200 := by
    simp only [stackLo, sp₄, mulKStack, baseMulStack, Nat.reduceAdd]; rv_eval []
  have hmk : MulKPre t₄ := {
    out := by rw [x10₄]; valid_sub hst.valid [hb]
    lhs := by
      rw [x11₄]
      exact Region.vrange hRp (by addr_omega [ptb', hhw, hcn]) (by addr_omega [ptb', hhw, hcn])
        (by addr_omega [ptb', hhw, pt8, hcn])
    stack := (hst.sub 1040 sp₄ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk
    pool := poolOk_of_rodata (InvR.rodata' hpre P₄.gs.inv) (by rw [sl₄]; addr_omega [hro, hb])
    outStack := by rw [x10₄, sl₄]; addr_omega [hb]
    lhsStack := by rw [x11₄, sl₄]; addr_omega [hb, ptb', hhw, hab, hcn] }
  obtain ⟨t₅, r₅, ⟨pc₅, ps₅, post₅⟩ | hd⟩ := hMK.call (Reaches.refl t₄) (b8000bf1c_pc h₄) hmk
  swap
  · exact ⟨t₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl hd⟩
  have F₅ := DFrame.of_two post₅.frame
  rw [x10₄, sl₄] at F₅
  have P₅ := P₄.step hpre F₅ (fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (by addr_omega [ha, hb]))) (ps₅.reg .x2) (ps₅.reg .x22)
  have v₅ : eAt t₅ (s.getReg .x2 - 464) = xs.getD c 0 *
      ofK (1 + BF64.ofBitVec (t.getReg .x19) * (rs.map (·⁻¹)).getD c 0) := by
    rw [← x10₄, post₅.value, x11₄, b8000bf1c_x12 h₄, v₃, ← hchal]
    congr 1
    · exact P₄.fr.eAt fun j hj hw ↦ by
        rcases hw with hw | hw | hw | hw | hw <;> addr_omega [hw, hj, ptb', hhw, hab, hb, hcn]
    · exact congrArg ofK (pr_kOf_xor_one _)
  -- `0x8000bf30`: `1 +` it into `S - 160`, `mul(S - 464, S - 128, S - 160)`
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₅.gs.sp
  obtain ⟨t₆, r₆, h₆⟩ := Sym.BlockSpec.reaches b8000bf30_spec
    (by rw [pc₅, returnAddress_eq, b8000bf1c_x1 h₄]; decide) (by
      rv_eval [sp₅]
      and_intros <;> valid_access hst.valid [hb])
  have k₆ := b8000bf30_keeps h₆
  have F₆ : DFrame t₅ t₆ fun y ↦ Within y (s.getReg .x2 - 160) 24 := by
    have := DFrame.of_memFrame (b8000bf30_frame h₆ (by rw [sp₅]; addr_omega [hb]))
    rw [sp₅] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  have P₆ := P₅.step hpre F₆ (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])))
    (k₆ .x2 (by decide)) (k₆ .x22 (by decide))
  have e160 : eAt t₆ (s.getReg .x2 - 160) = 1 + eAt t₅ (s.getReg .x2 - 464) := by
    have m0 := b8000bf30_m_x2_880 h₆
    have m1 := b8000bf30_m_x2_888 h₆
    have m2 := b8000bf30_m_x2_896 h₆
    rw [sp₅] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    exact pr_one_add_eAt m0 (by rv_eval [m1]) (by rv_eval [m2])
  have e128 : eAt t₆ (s.getReg .x2 - 128) = acc.1 := by
    rw [F₆.eAt (fun j hj hw ↦ by addr_omega [hw, hj, hb]),
      F₅.eAt (fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb]),
      (by simp only [eAt, b8000bf1c_mem_same h₄] :
        eAt t₄ (s.getReg .x2 - 128) = eAt t₃ (s.getReg .x2 - 128)),
      F₃.eAt (fun j hj hw ↦ by addr_omega [hw, hj, hb]),
      (by simp only [eAt, b8000bf0c_mem_same h₂] :
        eAt t₂ (s.getReg .x2 - 128) = eAt t₁ (s.getReg .x2 - 128)),
      (by simp only [eAt, b8000bf00_mem_same h₁] :
        eAt t₁ (s.getReg .x2 - 128) = eAt t (s.getReg .x2 - 128)), h.prod]
  have x10₆ : t₆.getReg .x10 = s.getReg .x2 - 464 := by rw [b8000bf30_x10 h₆, sp₅]; rv_eval []
  have x11₆ : t₆.getReg .x11 = s.getReg .x2 - 128 := by rw [b8000bf30_x11 h₆, sp₅]; rv_eval []
  have x12₆ : t₆.getReg .x12 = s.getReg .x2 - 160 := by rw [b8000bf30_x12 h₆, sp₅]; rv_eval []
  obtain ⟨t₇, r₇, hv₇⟩ := callMul hM hpre P₆.gs.inv (b8000bf30_pc h₆) x10₆ x11₆ x12₆
    ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb]⟩
    ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb]⟩
    ⟨by addr_omega [hb], by addr_omega [hb], by addr_omega [hb]⟩ (by addr_omega [hb])
    (by addr_omega [hb])
  have r₁₇ := r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans (r₆.trans r₇)))))
  rcases hv₇ with hd | ⟨pc₇, ps₇, F₇, v₇⟩
  · exact ⟨t₇, r₁₇, Or.inl hd⟩
  have P₇ := P₆.step hpre F₇ (fun a ha ↦ by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (by addr_omega [ha, hb]))) (ps₇.reg .x2) (ps₇.reg .x22)
  rw [e128, e160, v₅] at v₇
  -- `0x8000bf60`: a trap past the roots, the product to `S - 128`
  have sp₇ : t₇.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₇.gs.sp
  obtain ⟨t₈, r₈, h₈⟩ := Sym.BlockSpec.reaches b8000bf60_spec
    (by rw [pc₇, returnAddress_eq, b8000bf30_x1 h₆]; decide) (by
      rv_eval [sp₇]
      and_intros <;> valid_access hst.valid [hb])
  have k₈ := b8000bf60_keeps h₈
  by_cases e8 : t₇.getReg .x27 - 1 = 0
  · exact ⟨t₈, r₁₇.trans r₈, Or.inl (dead_of_fetch (by rw [b8000bf60_pc_taken h₈ e8]; exact trap))⟩
  have F₈ : DFrame t₇ t₈ fun y ↦ Within y (s.getReg .x2 - 128) 24 := by
    have := DFrame.of_memFrame (b8000bf60_frame h₈ (by rw [sp₇]; addr_omega [hb]))
    rw [sp₇] at this
    exact this.mono fun y hy ↦ by addr_omega [hy, hb]
  have P₈ := P₇.step hpre F₈ (fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])))
    (k₈ .x2 (by decide)) (k₈ .x22 (by decide))
  have e128₈ : eAt t₈ (s.getReg .x2 - 128) = (prG rs acc (xs.getD c 0, c)).1 := by
    have m0 := b8000bf60_m_x2_912 h₈
    have m1 := b8000bf60_m_x2_920 h₈
    have m2 := b8000bf60_m_x2_928 h₈
    rw [sp₇] at m0 m1 m2
    rv_eval [] at m0 m1 m2
    rw [eAt_congr m0 (by rv_eval [m1]) (by rv_eval [m2]), v₇, h.basis]
    simp only [prG]
  -- `0x8000bf80`: `K::square(basis)`
  obtain ⟨t₉, r₉, h₉⟩ := Sym.BlockSpec.reaches b8000bf80_spec (b8000bf60_pc_not_taken h₈ e8) trivial
  have k₉ := b8000bf80_keeps h₉
  have P₉ := P₈.same hpre (b8000bf80_mem_same h₉) (k₉ .x2 (by decide)) (k₉ .x22 (by decide))
  obtain ⟨t₁₀, r₁₀, ⟨pc₁₀, ps₁₀, post₁₀⟩ | hd⟩ := hSq.call (Reaches.refl t₉) (b8000bf80_pc h₉) trivial
  swap
  · exact ⟨t₁₀, r₁₇.trans (r₈.trans (r₉.trans r₁₀)), Or.inl hd⟩
  have P₁₀ := P₉.same hpre post₁₀.mem (ps₁₀.reg .x2) (ps₁₀.reg .x22)
  -- `0x8000bf9c`: `base_mul(root, basis)`
  have x21₁₀ : t₁₀.getReg .x21 = rp + BitVec.ofNat 64 (8 * c) := by
    rw [ps₁₀.reg .x21, k₉ .x21 (by decide), k₈ .x21 (by decide), ps₇.reg .x21, k₆ .x21 (by decide),
      ps₅.reg .x21, k₄ .x21 (by decide), ps₃.reg .x21, k₂ .x21 (by decide), k₁ .x21 (by decide), hx21]
  obtain ⟨t₁₁, r₁₁, h₁₁⟩ := Sym.BlockSpec.reaches b8000bf9c_spec
    (by rw [pc₁₀, returnAddress_eq, b8000bf80_x1 h₉]; decide) (by
      rv_eval [x21₁₀]
      exact Region.valid hRr (by addr_omega [rp2, hhw, hcn]) (by addr_omega [rp2, hhw, hcn])
        (by addr_omega [rp2, hhw, rp8, hcn]))
  have k₁₁ := b8000bf9c_keeps h₁₁
  have P₁₁ := P₁₀.same hpre (b8000bf9c_mem_same h₁₁) (k₁₁ .x2 (by decide)) (k₁₁ .x22 (by decide))
  have sp₁₁ : t₁₁.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := P₁₁.gs.sp
  have sl₁₁ : stackLo t₁₁ baseMulStack = s.getReg .x2 - 1152 := by
    simp only [stackLo, sp₁₁, baseMulStack]; rv_eval []
  obtain ⟨t₁₂, r₁₂, ⟨pc₁₂, ps₁₂, post₁₂⟩ | hd⟩ := hBM.call (Reaches.refl t₁₁) (b8000bf9c_pc h₁₁)
    ⟨(hst.sub 1040 sp₁₁ (by decide) (by decide) (by decide) (by decide) (by decide)).toStackOk,
      poolOk_of_rodata (InvR.rodata' hpre P₁₁.gs.inv) (by rw [sl₁₁]; addr_omega [hro, hb])⟩
  swap
  · exact ⟨t₁₂, r₁₇.trans (r₈.trans (r₉.trans (r₁₀.trans (r₁₁.trans r₁₂)))), Or.inl hd⟩
  have F₁₂ := DFrame.of_memFrame post₁₂.frame
  rw [sl₁₁] at F₁₂
  have P₁₂ := P₁₁.step hpre F₁₂ (fun a ha ↦ Or.inr (Or.inr (by addr_omega [ha, hb])))
    (ps₁₂.reg .x2) (ps₁₂.reg .x22)
  -- `0x8000bfb4`: the next basis
  obtain ⟨t₁₃, r₁₃, h₁₃⟩ := Sym.BlockSpec.reaches b8000bfb4_spec
    (by rw [pc₁₂, returnAddress_eq, b8000bf9c_x1 h₁₁]; decide) trivial
  have k₁₃ := b8000bfb4_keeps h₁₃
  have P₁₃ := P₁₂.same hpre (b8000bfb4_mem_same h₁₃) (k₁₃ .x2 (by decide)) (k₁₃ .x22 (by decide))
  have r₁₁₃ : Reaches Image.code t t₁₃ :=
    r₁₇.trans (r₈.trans (r₉.trans (r₁₀.trans (r₁₁.trans (r₁₂.trans r₁₃)))))
  -- the registers
  have x19₈ : t₈.getReg .x19 = t.getReg .x19 := by
    rw [k₈ .x19 (by decide), ps₇.reg .x19, k₆ .x19 (by decide), ps₅.reg .x19, k₄ .x19 (by decide),
      ps₃.reg .x19, k₂ .x19 (by decide), k₁ .x19 (by decide)]
  have hbas : BF64.ofBitVec (t₁₃.getReg .x19) = (prG rs acc (xs.getD c 0, c)).2 := by
    rw [b8000bfb4_x19 h₁₃, post₁₂.value, ps₁₂.reg .x21, b8000bf9c_x21 h₁₁, post₁₀.value,
      b8000bf9c_x10 h₁₁, b8000bf9c_x11 h₁₁, x21₁₀, ps₁₀.reg .x19, b8000bf80_x10 h₉,
      k₉ .x19 (by decide), x19₈, kH _ (by addr_omega [rp2, hhw, hcn]) t₁₀ P₁₀, pr_kOf_xor]
    simp only [prG, kOf, h.basis, hroot]
    exact add_comm _ _
  have hreg (r : Reg) (hc : r ∈ calleeSaved) (h13 : t₁₃.getReg r = t₁₂.getReg r)
      (h11 : t₁₁.getReg r = t₁₀.getReg r) (h9 : t₉.getReg r = t₈.getReg r)
      (h8 : t₈.getReg r = t₇.getReg r) (h6 : t₆.getReg r = t₅.getReg r)
      (h4 : t₄.getReg r = t₃.getReg r) (h2 : t₂.getReg r = t₁.getReg r)
      (h1 : t₁.getReg r = t.getReg r) : t₁₃.getReg r = t.getReg r := by
    rw [h13, ps₁₂ r hc, h11, ps₁₀ r hc, h9, h8, ps₇ r hc, h6, ps₅ r hc, h4, ps₃ r hc, h2, h1]
  have x8₁₃ := hreg .x8 (by decide) (k₁₃ .x8 (by decide)) (k₁₁ .x8 (by decide)) (k₉ .x8 (by decide))
    (k₈ .x8 (by decide)) (k₆ .x8 (by decide)) (k₄ .x8 (by decide)) (k₂ .x8 (by decide))
    (k₁ .x8 (by decide))
  have x23₁₃ := hreg .x23 (by decide) (k₁₃ .x23 (by decide)) (k₁₁ .x23 (by decide))
    (k₉ .x23 (by decide)) (k₈ .x23 (by decide)) (k₆ .x23 (by decide)) (k₄ .x23 (by decide))
    (k₂ .x23 (by decide)) (k₁ .x23 (by decide))
  have x24₁₃ := hreg .x24 (by decide) (k₁₃ .x24 (by decide)) (k₁₁ .x24 (by decide))
    (k₉ .x24 (by decide)) (k₈ .x24 (by decide)) (k₆ .x24 (by decide)) (k₄ .x24 (by decide))
    (k₂ .x24 (by decide)) (k₁ .x24 (by decide))
  have x25₁₃ := hreg .x25 (by decide) (k₁₃ .x25 (by decide)) (k₁₁ .x25 (by decide))
    (k₉ .x25 (by decide)) (k₈ .x25 (by decide)) (k₆ .x25 (by decide)) (k₄ .x25 (by decide))
    (k₂ .x25 (by decide)) (k₁ .x25 (by decide))
  have tot₁₃ : E.ofLimbs (BF64.ofBitVec (t₁₃.getReg .x23)) (BF64.ofBitVec (t₁₃.getReg .x25))
      (BF64.ofBitVec (t₁₃.getReg .x24)) = total := by rw [x23₁₃, x24₁₃, x25₁₃]; exact h.tot
  have x8₇ : t₈.getReg .x9 = t.getReg .x9 := by
    rw [k₈ .x9 (by decide), ps₇.reg .x9, k₆ .x9 (by decide), ps₅.reg .x9, k₄ .x9 (by decide),
      ps₃.reg .x9, k₂ .x9 (by decide), k₁ .x9 (by decide)]
  have x9₁₂ : t₁₂.getReg .x9 = BitVec.ofNat 64 (24 * (n - (c + 1))) := by
    rw [ps₁₂.reg .x9, k₁₁ .x9 (by decide), ps₁₀.reg .x9, b8000bf80_x9 h₉, x8₇, h.x9,
      show (24 : Word) = BitVec.ofNat 64 24 from rfl,
      pr_ofNat_sub (a := 24 * (n - c)) (k := 24) (by omega)]
    congr 1
    omega
  have prod₁₃ : eAt t₁₃ (s.getReg .x2 - 128) = (prG rs acc (xs.getD c 0, c)).1 := by
    rw [← e128₈, (by simp only [eAt, b8000bfb4_mem_same h₁₃] :
        eAt t₁₃ (s.getReg .x2 - 128) = eAt t₁₂ (s.getReg .x2 - 128)),
      F₁₂.eAt (fun j hj hw ↦ by addr_omega [hw, hj, hb])]
    simp only [eAt, b8000bf9c_mem_same h₁₁, post₁₀.mem, b8000bf80_mem_same h₉]
  by_cases e13 : t₁₂.getReg .x9 ≠ 0
  · refine ⟨t₁₃, r₁₁₃, Or.inr (Or.inl ⟨?_, {
      toPrX := P₁₃
      pc := b8000bfb4_pc_taken h₁₃ e13
      ilt := h.ilt
      clt := ?_
      x8 := x8₁₃.trans h.x8
      tot := tot₁₃
      x9 := by rw [k₁₃ .x9 (by decide), x9₁₂]
      x18 := by
        rw [k₁₃ .x18 (by decide), ps₁₂.reg .x18, k₁₁ .x18 (by decide), ps₁₀.reg .x18,
          b8000bf80_x18 h₉, k₈ .x18 (by decide), ps₇.reg .x18, k₆ .x18 (by decide), ps₅.reg .x18,
          k₄ .x18 (by decide), ps₃.reg .x18, k₂ .x18 (by decide), k₁ .x18 (by decide), hx18,
          show (8 : Word) = BitVec.ofNat 64 8 from rfl, pr_ofNat_add, hipd,
          show 8 * c + 8 = 8 * (c + 1) by omega]
      x20 := by
        rw [k₁₃ .x20 (by decide), ps₁₂.reg .x20, k₁₁ .x20 (by decide), ps₁₀.reg .x20,
          b8000bf80_x20 h₉, k₈ .x20 (by decide), ps₇.reg .x20, k₆ .x20 (by decide), ps₅.reg .x20,
          k₄ .x20 (by decide), ps₃.reg .x20, k₂ .x20 (by decide), k₁ .x20 (by decide), hx20,
          show (24 : Word) = BitVec.ofNat 64 24 from rfl, pr_ofNat_add, hPd,
          show 24 * c + 24 = 24 * (c + 1) by omega]
      x21 := by
        rw [b8000bfb4_x21 h₁₃, ps₁₂.reg .x26, k₁₁ .x26 (by decide), ps₁₀.reg .x26,
          b8000bf80_x26 h₉, k₈ .x21 (by decide), ps₇.reg .x21, k₆ .x21 (by decide), ps₅.reg .x21,
          k₄ .x21 (by decide), ps₃.reg .x21, k₂ .x21 (by decide), k₁ .x21 (by decide), hx21,
          show (8 : Word) = BitVec.ofNat 64 8 from rfl, pr_ofNat_add, hrpd,
          show 8 * c + 8 = 8 * (c + 1) by omega]
      x27 := by
        rw [k₁₃ .x27 (by decide), ps₁₂.reg .x27, k₁₁ .x27 (by decide), ps₁₀.reg .x27,
          k₉ .x27 (by decide), b8000bf60_x27 h₈, ps₇.reg .x27, k₆ .x27 (by decide), ps₅.reg .x27,
          k₄ .x27 (by decide), ps₃.reg .x27, k₂ .x27 (by decide), k₁ .x27 (by decide), h.x27,
          show (1 : Word) = BitVec.ofNat 64 1 from rfl,
          pr_ofNat_sub (a := n + 2 - c) (k := 1) (by omega), show n + 2 - c - 1 = n + 2 - (c + 1) by omega]
      prod := prod₁₃
      basis := hbas }⟩)⟩
    all_goals
      by_contra hn
      apply e13
      rw [x9₁₂, show n - (c + 1) = 0 by omega]
      rfl
  · have e0 : t₁₂.getReg .x9 = 0 := by simpa using e13
    have hn : c + 1 = n := by
      rw [x9₁₂] at e0
      have := congrArg BitVec.toNat e0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      have h0 : (0 : Word).toNat = 0 := rfl
      omega
    obtain ⟨t₁₄, r₁₄, h₁₄⟩ := Sym.BlockSpec.reaches b8000bfc0_spec
      (b8000bfb4_pc_not_taken h₁₃ e0) trivial
    have k₁₄ := b8000bfc0_keeps h₁₄
    refine ⟨t₁₄, r₁₁₃.trans r₁₄, Or.inr (Or.inr ⟨hn, {
      toPrX := P₁₃.same hpre (b8000bfc0_mem_same h₁₄) (k₁₄ .x2 (by decide)) (k₁₄ .x22 (by decide))
      pc := b8000bfc0_pc h₁₄
      ilt := h.ilt
      x8 := (k₁₄ .x8 (by decide)).trans (x8₁₃.trans h.x8)
      tot := by rw [k₁₄ .x23 (by decide), k₁₄ .x24 (by decide), k₁₄ .x25 (by decide)]; exact tot₁₃
      prod := by rw [← prod₁₃]; simp only [eAt, b8000bfc0_mem_same h₁₄] }⟩)⟩

end Rv64Verifier.Proofs.Pcs.Vso
