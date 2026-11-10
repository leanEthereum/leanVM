import Rv64Verifier.Proofs.Gkr.LayerR10d

/-!
# `keccak::verify_layer`: the second check

`keccak.rs:171-178` at `0x8000fac0..0x8000fb34`: `(kappa + t[1]) * t[2]` into `f + 264`, the sum
with `kappa * t[0]` into `f + 960`, the product with `scale * at_local` into `f + 216`, compared
with the value: on a mismatch `Err(KeccakLayer)` returned (`0x80010178`), on a match `J11`
(`c2b`); `second_check` from `J8`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

/-- `0x80010178`: `Err(KeccakLayer)`, code `21`, returned. -/
theorem err_21 {s u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hpc : u.pc = 0x80010178) (hout : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10)
    (hf : Fails s) : ∃ t, Reaches Image.code u t ∧ Ret s t := by
  obtain ⟨w, hr, h⟩ := Sym.BlockSpec.reaches b80010178_spec hpc trivial
  have hm := b80010178_mem_same h
  obtain ⟨t, hr', ht⟩ := err_exit hpre (B.same ((b80010178_keeps h .x2 (by decide)).trans B.x2) hm)
    (b80010178_pc h) (by rw [hm]; exact hout) hf
  exact ⟨t, hr.trans hr', ht⟩

set_option maxHeartbeats 16000000 in
/-- `0x8000fac0`: `(kappa + t[1]) * t[2]`; `0x8000fad8`: the sum and the product with
`scale * at_local`; `0x8000fb1c..0x8000fb2c`: the comparison with the value. -/
theorem c2b (hM : MulSpec) {s v : MachineState} {ip : Word} {c : E} {point lp t : List E}
    {scale lv : E} {tp tn : Word} (hpre : VerifyLayerPre s)
    (P : P1 s v ip c point scale lv lp t tp tn) :
    ∃ u, Reaches Image.code v u ∧ (J11 s u (instanceWeightsRust c) point (eqKernelRust (lp.take 6))
      (eqKernelRust (lp.drop 6)) t ∨ Ret s u ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have B := P.base
  have X := P.fx
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hlo := hpre.heap.lo
  simp only [stackLo] at hab hnx
  unfold verifyLayerStack at hb hab hnx
  have tB := X.tB
  rw [P.tn3] at tB
  have ta := tB.1
  have tb : heapNext s ≤ tp.toNat ∧ tp.toNat + 24 * 3 ≤ heapNext v := by
    rcases tB.2 with h | h
    · omega
    · exact h
  have hHv := B.heap.hi
  -- `0x8000fac0`: `mul(f + 264, f + 960, t[2])`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fac0_spec P.pc trivial
  have k₁ := b8000fac0_keeps h₁
  have hm₁ := b8000fac0_mem_same h₁
  have x2₁ : t₁.getReg .x2 = s.getReg .x2 - 1712 := (k₁ .x2 (by decide)).trans B.x2
  have B₁ : Base s t₁ := B.same x2₁ hm₁
  have hN₁ : heapNext t₁ = heapNext v := by simp only [heapNext, hm₁]
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000fac0_x10 h₁, B.x2]; rv_eval []
  have x11₁ : t₁.getReg .x11 = s.getReg .x2 - 752 := by rw [b8000fac0_x11 h₁, B.x2]; rv_eval []
  have x12₁ : t₁.getReg .x12 = tp + 48 := by rw [b8000fac0_x12 h₁, P.x24]
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, B₂, F₂, hN₂, G₂, V₂⟩ | hd⟩ := mulF hM hpre B₁ hr₁ (b8000fac0_pc h₁)
    1448 x10₁ (by decide) (fun a h ↦ Or.inr (Or.inl (by addr_omega [h, hb])))
    (by rw [x11₁]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₁]; addr_omega [hb]) (by rw [x11₁]; addr_omega [hb])
    (by rw [x12₁]; exact heap_vmr (by addr_omega [tb, hlo]) (by addr_omega [tb, hHv]) (by addr_omega [ta, tb, hHv]))
    (by rw [x12₁]; addr_omega [tb, hHv, hab, hb]) (by rw [x12₁]; addr_omega [tb, hHv, hab, hb])
  swap
  · exact ⟨t₂, hr₂, Or.inr (Or.inr hd)⟩
  have tE₁ : eListAt t₁ tp 3 = t := by rw [eListAt_congr hm₁, ← P.tn3]; exact X.tE
  have ht2 : eAt t₁ (tp + 48) = t.getD 2 0 := by
    have := eListAt_getD_lt t₁ tp (by decide : 2 < 3)
    rw [tE₁] at this
    exact this.symm
  have e264 : eAt t₂ (s.getReg .x2 - 1448) =
      (sumE (instanceWeightsRust c) + t.getD 1 0) * t.getD 2 0 := by
    refine V₂.trans ?_
    rw [x11₁, x12₁, ht2, eAt_of_same hm₁, P.e960]
  have e1560₂ : eAt t₂ (s.getReg .x2 - 152) = scale *
      atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) := by
    rw [mulF_keep hpre G₂ (by decide) (by addr_omega [hb]) (by addr_omega [hb])
      (Or.inr (by addr_omega [hb])), eAt_of_same hm₁]
    exact P.e1560
  have e1584₂ : eAt t₂ (s.getReg .x2 - 128) = sumE (instanceWeightsRust c) * t.getD 0 0 := by
    rw [mulF_keep hpre G₂ (by decide) (by addr_omega [hb]) (by addr_omega [hb])
      (Or.inr (by addr_omega [hb])), eAt_of_same hm₁]
    exact P.e1584
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := B₂.x2
  -- `0x8000fad8`: the sum into `f + 960`, `mul(f + 216, f + 1560, f + 960)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fad8_spec
    (by rw [hpc₂, returnAddress_eq, b8000fac0_x1 h₁]; decide) (by
      rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000fad8_keeps h₃
  have f₃ := b8000fad8_frame h₃ (by rw [x2₂]; addr_omega [hb])
  rw [x2₂] at f₃
  rv_eval [] at f₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have B₃ : Base s t₃ := B₂.slots hpre x2₃ f₃ (by addr_omega [hb]) (by addr_omega [hb])
  have hN₃ : heapNext t₃ = heapNext t₂ := by
    simp only [heapNext]; rw [f₃ _ (by addr_omega [hb, hnx])]
  have F₃ : DFrame t₂ t₃ (W10 s) := (DFrame.of_memFrame f₃).mono fun a h ↦
    Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
  have m960 := b8000fad8_m_x2_960 h₃
  have m968 := b8000fad8_m_x2_968 h₃
  have m976 := b8000fad8_m_x2_976 h₃
  rw [x2₂] at m960 m968 m976
  rv_eval [] at m960 m968 m976
  have l264 := limbs_eAt t₂ (s.getReg .x2 - 1448)
  have l1584 := limbs_eAt t₂ (s.getReg .x2 - 128)
  rw [e264] at l264
  rw [e1584₂] at l1584
  rv_eval [] at l264 l1584
  have e960₃ : eAt t₃ (s.getReg .x2 - 752) =
      (sumE (instanceWeightsRust c) + t.getD 1 0) * t.getD 2 0 +
        sumE (instanceWeightsRust c) * t.getD 0 0 := by
    apply eAt_eq_of_limbs
    rw [limbs_add, l264, l1584]
    rv_eval [m960, m968, m976]
  have e1560₃ : eAt t₃ (s.getReg .x2 - 152) = scale *
      atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) := by
    rw [(DFrame.of_memFrame f₃).eAt (fun i hi hw ↦ by addr_omega [hw, hi, hb])]
    exact e1560₂
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 1496 := by rw [b8000fad8_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = s.getReg .x2 - 152 := by rw [b8000fad8_x11 h₃, x2₂]; rv_eval []
  have x12₃ : t₃.getReg .x12 = s.getReg .x2 - 752 := by rw [b8000fad8_x12 h₃, x2₂]; rv_eval []
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, B₄, F₄, hN₄, -, V₄⟩ | hd⟩ := mulF hM hpre B₃ hr₃ (b8000fad8_pc h₃)
    1496 x10₃ (by decide) (fun a h ↦ Or.inl (by addr_omega [h, hb]))
    (by rw [x11₃]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₃]; addr_omega [hb]) (by rw [x11₃]; addr_omega [hb])
    (by rw [x12₃]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₃]; addr_omega [hb]) (by rw [x12₃]; addr_omega [hb])
  swap
  · exact ⟨t₄, hr₂.trans hr₄, Or.inr (Or.inr hd)⟩
  have e216 : eAt t₄ (s.getReg .x2 - 1496) = scale *
      atLocalRust (wOf s) (eqKernelRust (lp.take 6)) (eqKernelRust (lp.drop 6)) *
        (sumE (instanceWeightsRust c) * t.getD 0 0 +
          (sumE (instanceWeightsRust c) + t.getD 1 0) * t.getD 2 0) := by
    refine V₄.trans ?_
    rw [x11₃, x12₃, e1560₃, e960₃, add_comm ((sumE (instanceWeightsRust c) + t.getD 1 0) * t.getD 2 0)]
  have l216 := limbs_eAt t₄ (s.getReg .x2 - 1496)
  rw [e216] at l216
  rv_eval [] at l216
  -- what the products kept
  have Fv4 : DFrame v t₄ (W10 s) :=
    ((((DFrame.of_same hm₁ (W10 s)).trans F₂ fun _ h ↦ h).trans F₃ fun _ h ↦ h).trans F₄ fun _ h ↦ h)
  have hN4v : heapNext t₄ = heapNext v := by rw [hN₄, hN₃, hN₂, hN₁]
  have X₄ := X.keep hpre B.heap B₄.heap (le_of_eq hN4v.symm) Fv4
  have R₄ : Rest s t₄ (rest10 s c point scale lv lp t) :=
    P.rest.body hpre B B₄ (Fv4.mono fun a h ↦ w10_body hpre h)
  have kw (y : Word) (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1520) : t₄.getMem y = v.getMem y :=
    Fv4 y (w10_low hpre h1 h2)
  have r4 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x21, .x22, .x24, .x25, .x26]) :
      t₄.getReg r = v.getReg r := by
    rw [hp₄ r (reg_sub (by decide) hr), k₃ r (reg_sub (by decide) hr),
      hp₂ r (reg_sub (by decide) hr), k₁ r (reg_sub (by decide) hr)]
  have x20₄ : t₄.getReg .x20 = s.getReg .x11 := by
    rw [hp₄.reg .x20, k₃ .x20 (by decide), hp₂.reg .x20, b8000fac0_x20 h₁, P.x22]
  have lv4 : limbs lv = (t₄.getReg .x8, t₄.getReg .x21, t₄.getReg .x9) := by
    rw [r4 .x8 (by decide), r4 .x21 (by decide), r4 .x9 (by decide), P.x8, P.x21, P.x9]
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := B₄.x2
  -- `0x8000fb1c..0x8000fb2c`: the comparison
  obtain ⟨u₁, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000fb1c_spec
    (by rw [hpc₄, returnAddress_eq, b8000fad8_x1 h₃]; decide) (by
      rv_eval [x2₄]; valid_access hpre.stack.valid [hb])
  have k₅ := b8000fb1c_keeps h₅
  have hm₅ := b8000fb1c_mem_same h₅
  have c1 : t₄.getMem (t₄.getReg .x2 + 216) = t₄.getMem (s.getReg .x2 - 1496) := by
    rw [x2₄]; rv_eval []
  have hout : t₄.getMem (s.getReg .x2 - 1664) = s.getReg .x10 := X₄.k8.out
  have hfail (hc : ¬ check2 (wOf s) (sumE (instanceWeightsRust c)) scale lv lp t) : Fails s :=
    R₄.require_fail hc
  have heq (h1 : t₄.getMem (s.getReg .x2 - 1496) = t₄.getReg .x8)
      (h2 : t₄.getMem (s.getReg .x2 - 1488) = t₄.getReg .x21)
      (h3 : t₄.getMem (s.getReg .x2 - 1480) = t₄.getReg .x9) :
      check2 (wOf s) (sumE (instanceWeightsRust c)) scale lv lp t := by
    show _ = lv
    apply eq_of_limbs
    rw [lv4, ← h1, ← h2, ← h3]
    exact l216
  by_cases d1 : t₄.getMem (s.getReg .x2 - 1496) = t₄.getReg .x8
  swap
  · have hc : ¬ check2 (wOf s) (sumE (instanceWeightsRust c)) scale lv lp t := fun hc ↦
      d1 (congrArg Prod.fst (l216.symm.trans ((congrArg limbs hc).trans lv4)))
    obtain ⟨w, hr, hw⟩ := err_21 hpre (B₄.same ((k₅ .x2 (by decide)).trans x2₄) hm₅)
      (b8000fb1c_pc_taken h₅ (by rw [c1]; exact d1)) (by rw [hm₅]; exact hout) (hfail hc)
    exact ⟨w, hr₂.trans (hr₄.trans ( (hr₅.trans hr))), Or.inr (Or.inl hw)⟩
  obtain ⟨u₂, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000fb24_spec
    (b8000fb1c_pc_not_taken h₅ (by rw [c1]; exact d1)) (by
      rv_eval [k₅ .x2 (by decide), x2₄]; valid_access hpre.stack.valid [hb])
  have k₆ := b8000fb24_keeps h₆
  have hm₆ := b8000fb24_mem_same h₆
  have hm46 (a : Word) : u₂.getMem a = t₄.getMem a := by rw [hm₆, hm₅]
  have c2 : u₁.getMem (u₁.getReg .x2 + 224) = t₄.getMem (s.getReg .x2 - 1488) := by
    rw [k₅ .x2 (by decide), x2₄, hm₅]; rv_eval []
  by_cases d2 : t₄.getMem (s.getReg .x2 - 1488) = t₄.getReg .x21
  swap
  · have hc : ¬ check2 (wOf s) (sumE (instanceWeightsRust c)) scale lv lp t := fun hc ↦
      d2 (congrArg (fun p ↦ p.2.1) (l216.symm.trans ((congrArg limbs hc).trans lv4)))
    obtain ⟨w, hr, hw⟩ := err_21 hpre
      (B₄.same ((k₆ .x2 (by decide)).trans ((k₅ .x2 (by decide)).trans x2₄)) hm46)
      (b8000fb24_pc_taken h₆ (by rw [c2, k₅ .x21 (by decide)]; exact d2))
      (by rw [hm46]; exact hout) (hfail hc)
    exact ⟨w, hr₂.trans (hr₄.trans ( (hr₅.trans (hr₆.trans hr)))), Or.inr (Or.inl hw)⟩
  obtain ⟨u₃, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000fb2c_spec
    (b8000fb24_pc_not_taken h₆ (by rw [c2, k₅ .x21 (by decide)]; exact d2)) (by
      rv_eval [k₆ .x2 (by decide), k₅ .x2 (by decide), x2₄]; valid_access hpre.stack.valid [hb])
  have k₇ := b8000fb2c_keeps h₇
  have hm₇ := b8000fb2c_mem_same h₇
  have hm47 (a : Word) : u₃.getMem a = t₄.getMem a := by rw [hm₇, hm46]
  have x2u : u₃.getReg .x2 = s.getReg .x2 - 1712 := by
    rw [k₇ .x2 (by decide), k₆ .x2 (by decide), k₅ .x2 (by decide), x2₄]
  have c3 : u₂.getMem (u₂.getReg .x2 + 232) = t₄.getMem (s.getReg .x2 - 1480) := by
    rw [k₆ .x2 (by decide), k₅ .x2 (by decide), x2₄, hm46]; rv_eval []
  have x9u : u₂.getReg .x9 = t₄.getReg .x9 := by rw [k₆ .x9 (by decide), k₅ .x9 (by decide)]
  by_cases d3 : t₄.getMem (s.getReg .x2 - 1480) = t₄.getReg .x9
  swap
  · have hc : ¬ check2 (wOf s) (sumE (instanceWeightsRust c)) scale lv lp t := fun hc ↦
      d3 (congrArg (fun p ↦ p.2.2) (l216.symm.trans ((congrArg limbs hc).trans lv4)))
    obtain ⟨w, hr, hw⟩ := err_21 hpre (B₄.same x2u hm47)
      (b8000fb2c_pc_taken h₇ (by rw [c3, x9u]; exact d3)) (by rw [hm47]; exact hout) (hfail hc)
    exact ⟨w, hr₂.trans (hr₄.trans ( (hr₅.trans (hr₆.trans (hr₇.trans hr))))),
      Or.inr (Or.inl hw)⟩
  -- the check passed: `J11`
  have hc := heq d1 d2 d3
  have Bu : Base s u₃ := B₄.same x2u hm47
  have hNu : heapNext u₃ = heapNext t₄ := by simp only [heapNext, hm47]
  have Xu := X₄.keep hpre B₄.heap Bu.heap (le_of_eq hNu.symm) (DFrame.of_same hm47 _)
  have ru (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x24, .x25, .x26]) :
      u₃.getReg r = t₄.getReg r := by
    rw [k₇ r (reg_sub (by decide) hr), k₆ r (reg_sub (by decide) hr), k₅ r (reg_sub (by decide) hr)]
  have e1600 : u₃.getMem (s.getReg .x2 - 1600) = v.getMem (s.getReg .x2 - 1600) := by
    rw [hm47, kw _ (by addr_omega [hb]) (by addr_omega [hb])]
  have e1624 : u₃.getMem (s.getReg .x2 - 1624) = v.getMem (s.getReg .x2 - 1624) := by
    rw [hm47, kw _ (by addr_omega [hb]) (by addr_omega [hb])]
  have x25u : u₃.getReg .x25 = u₃.getMem (s.getReg .x2 - 1600) := by
    rw [ru .x25 (by decide), r4 .x25 (by decide), P.x25, e1600]
  have x18u : u₃.getReg .x18 = u₃.getMem (s.getReg .x2 - 1624) := by
    rw [ru .x18 (by decide), r4 .x18 (by decide), P.x18, e1624]
  have x24u : u₃.getReg .x24 = tp := by rw [ru .x24 (by decide), r4 .x24 (by decide), P.x24]
  have x19u : u₃.getReg .x19 = tn := by rw [ru .x19 (by decide), r4 .x19 (by decide), P.x19]
  have x26u : u₃.getReg .x26 = 16 := by rw [ru .x26 (by decide), r4 .x26 (by decide), P.x26]
  refine ⟨u₃, hr₂.trans (hr₄.trans ( (hr₅.trans (hr₆.trans hr₇)))), Or.inl {
    pc := b8000fb2c_pc_not_taken h₇ (by rw [c3, x9u]; exact d3)
    base := Bu
    out := Xu.k8.out
    sponge := Xu.k8.sponge
    x20 := by rw [ru .x20 (by decide), x20₄]
    muLen := by rw [x26u]; exact Xu.k8.icap
    muBuf := by rw [Xu.k8.ipM]; exact Xu.k8.ibuf
    muE := by rw [Xu.k8.ipM, x26u]; exact Xu.k8.iw
    ptV := Xu.k8.ptV
    ezBuf := Xu.ezB
    ezE := Xu.ezE
    x25 := x25u
    x18 := x18u
    elBuf := by rw [x25u, x18u]; exact Xu.elB
    elE := by rw [x25u, x18u]; exact Xu.elE
    t2 := by rw [Xu.t2, x24u]
    tBuf := by rw [x24u, x19u]; exact Xu.tB
    tE := by rw [x24u, x19u]; exact Xu.tE
    rest := (R₄.keep fun T hT ↦ transcriptAt_congr hm47 hT).require_pass hc }⟩

/-- From the pack rounds to the second check: `J11`, a return or a dead end. -/
theorem second_check (hSC : SumcheckSpec) (hNS : NextScalarsSpec) (hEK : EqKernelSpec)
    (hDt : MultilinearContracts.DotSpec) (hM : MulSpec) {s w : MachineState} {ip : Word} {c : E}
    {acc : E × E × List E} (hpre : VerifyLayerPre s) (J : J8 s w ip c acc) :
    ∃ u, Reaches Image.code w u ∧
      ((∃ mu point eqZ eqLane t, J11 s u mu point eqZ eqLane t) ∨ Ret s u ∨ Dead Image.code u) := by
  obtain ⟨v₁, hr₁, ⟨lp, lv, S⟩ | hret | hd⟩ := r9_sc hSC hpre J
  · obtain ⟨v₂, hr₂, ⟨t, S'⟩ | hret | hd⟩ := r9_ns hNS hpre S
    · obtain ⟨v₃, hr₃, S'' | hd⟩ := r9_ek1 hEK hpre S'
      · obtain ⟨v₄, hr₄, J' | hd⟩ := r9_ek2 hEK hpre S''
        · obtain ⟨v₅, hr₅, K | hd⟩ := at_local hDt hM hpre J'
          · have r5 := hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅)))
            obtain ⟨v₆, hr₆, P | hd⟩ := c2a hM hpre K
            · obtain ⟨v₇, hr₇, J'' | hret | hd⟩ := c2b hM hpre P
              · exact ⟨v₇, r5.trans (hr₆.trans hr₇), Or.inl ⟨_, _, _, _, _, J''⟩⟩
              · exact ⟨v₇, r5.trans (hr₆.trans hr₇), Or.inr (Or.inl hret)⟩
              · exact ⟨v₇, r5.trans (hr₆.trans hr₇), Or.inr (Or.inr hd)⟩
            · exact ⟨v₆, r5.trans hr₆, Or.inr (Or.inr hd)⟩
          · exact ⟨v₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr (Or.inr hd)⟩
        · exact ⟨v₄, hr₁.trans (hr₂.trans (hr₃.trans hr₄)), Or.inr (Or.inr hd)⟩
      · exact ⟨v₃, hr₁.trans (hr₂.trans hr₃), Or.inr (Or.inr hd)⟩
    · exact ⟨v₂, hr₁.trans hr₂, Or.inr (Or.inl hret)⟩
    · exact ⟨v₂, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  · exact ⟨v₁, hr₁, Or.inr (Or.inl hret)⟩
  · exact ⟨v₁, hr₁, Or.inr (Or.inr hd)⟩

end Rv64Verifier.Gkr.Layer
