import Rv64Verifier.Proofs.Gkr.LayerR10

/-!
# `keccak::verify_layer`: `at_local`, a lane

`keccak.rs:166-169` at `0x8000f888..0x8000f848`: lane `k`'s chunk of the weights (at most 64 of
them, from `s3`) dotted with `eq_z` into `f + 960` (`at_dot`).
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem elist_take_min (u : MachineState) (p : Word) (k n : Nat) :
    (eListAt u p n).take k = eListAt u p (min k n) := by
  apply List.ext_getElem (by simp [eListAt_length])
  intro i h1 h2
  simp only [List.getElem_take, eListAt_getElem]

/-- Lane `k`'s chunk of the weights. -/
theorem chunk_eq (s : MachineState) (k : Nat) :
    ((wOf s).drop (64 * k)).take 64 = eListAt s (s.getMem (s.getReg .x15 + 56) +
      BitVec.ofNat 64 (1536 * k)) (min 64 ((s.getMem (s.getReg .x15 + 64)).toNat - 64 * k)) := by
  rw [claim_weights, Open.eListAt_drop, elist_take_min, show 24 * (64 * k) = 1536 * k by omega]

theorem newBuf_vmr {s u : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk u) {p : Word}
    {n : Nat} (hB : NewBuf s u p (24 * n) 8) : ValidMemRange p (3 * n) := by
  rcases hB.2 with h0 | ⟨b1, b2⟩
  · intro i hi; omega
  · have := hpre.heap.lo
    have := hH.hi
    exact heap_vmr (by omega) (by omega) hB.1

/-- `dot` into `f + 960`. -/
theorem dotCall (hDt : MultilinearContracts.DotSpec) {s u₀ u : MachineState}
    (hpre : VerifyLayerPre s) (B : Base s u) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x80007f3c) (hx10 : u.getReg .x10 = s.getReg .x2 - 752)
    (hp : MultilinearContracts.DotPre u) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Base s v ∧
      DFrame u v (W10 s) ∧ heapNext v = heapNext u ∧ u.getReg .x12 = u.getReg .x14 ∧
      eAt v (s.getReg .x2 - 752) = dotRust (eListAt u (u.getReg .x11) (u.getReg .x12).toNat)
        (eListAt u (u.getReg .x13) (u.getReg .x12).toNat)) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  simp only [stackLo] at hnx
  unfold verifyLayerStack at hb hnx
  obtain ⟨v, hrv, ⟨hpc', hp', post⟩ | hd⟩ := hDt.call hr hpc hp
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have F := DFrame.of_two post.frame
  rw [hx10] at F
  simp only [stackLo, B.x2] at F
  have F10 : DFrame u v (W10 s) := F.mono fun a h ↦ by
    rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb]))))
  have V := post.value
  rw [hx10] at V
  have x2v : v.getReg .x2 = s.getReg .x2 - 1712 := (hp'.reg .x2).trans B.x2
  have hN : v.getMem nextAddr = u.getMem nextAddr := F _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have hN' : heapNext v = heapNext u := by simp only [heapNext, hN]
  have Bv : Base s v := B.next hpre x2v ⟨by rw [hN']; exact B.heap.lo, by rw [hN']; exact B.heap.hi⟩
    (le_of_eq hN'.symm) F10 fun a h ↦ w10_lw hpre h
  exact ⟨v, hrv, Or.inl ⟨hpc', hp', Bv, F10, hN', post.len, V⟩⟩

/-- `mul` into `f + 1712 - K` of two `E`s read anywhere apart from it and from `mul`'s stack. -/
theorem mulH (hM : MulSpec) {s u₀ u : MachineState} (hpre : VerifyLayerPre s) (B : Base s u)
    (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80008c48) (K : Nat)
    (hx10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 K) (hK : 128 ≤ K ∧ K ≤ 1712 ∧ K % 8 = 0)
    (hKw : ∀ a, Within a (s.getReg .x2 - BitVec.ofNat 64 K) 24 → W10 s a)
    (hl : ValidMemRange (u.getReg .x11) 3)
    (hlS : Apart (u.getReg .x11) 24 (s.getReg .x2 - 2736) 1024)
    (hlo : Apart (s.getReg .x2 - BitVec.ofNat 64 K) 24 (u.getReg .x11) 24)
    (hrr : ValidMemRange (u.getReg .x12) 3)
    (hrS : Apart (u.getReg .x12) 24 (s.getReg .x2 - 2736) 1024)
    (hro : Apart (s.getReg .x2 - BitVec.ofNat 64 K) 24 (u.getReg .x12) 24) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Base s v ∧
      DFrame u v (W10 s) ∧ heapNext v = heapNext u ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 K) = eAt u (u.getReg .x11) * eAt u (u.getReg .x12)) ∨
      Dead Image.code v) := by
  have hb := bounds hpre
  have hnx := hpre.stack.next
  simp only [stackLo] at hnx
  unfold verifyLayerStack at hb hnx
  obtain ⟨hK1, hK2, hK3⟩ := hK
  have hmp : MulPre u := mul_pre hpre B.x2 (B.rodata hpre) K hx10 (by omega) hK2 hK3 hl hlS
    (by rw [hx10]; exact hlo) hrr hrS (by rw [hx10]; exact hro)
  obtain ⟨v, hrv, ⟨hpc', hp, post⟩ | hd⟩ := hM.call hr hpc hmp
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have F := mul_frame B.x2 post
  rw [hx10] at F
  have V := post.value
  rw [hx10] at V
  have x2v : v.getReg .x2 = s.getReg .x2 - 1712 := (hp.reg .x2).trans B.x2
  have F10 : DFrame u v (W10 s) := F.mono fun a h ↦ by
    rcases h with h | h
    · exact hKw a h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb]))))
  have hN : v.getMem nextAddr = u.getMem nextAddr := F _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx, hK1, hK2]
  have hN' : heapNext v = heapNext u := by simp only [heapNext, hN]
  have Bv : Base s v := B.next hpre x2v ⟨by rw [hN']; exact B.heap.lo, by rw [hN']; exact B.heap.hi⟩
    (le_of_eq hN'.symm) F10 fun a h ↦ w10_lw hpre h
  exact ⟨v, hrv, Or.inl ⟨hpc', hp, Bv, F10, hN', V⟩⟩

/-- Lane `k`'s dot product done, at `0x8000f848`. -/
structure QD (s v : MachineState) (ip : Word) (c : E) (point : List E) (scale lv : E)
    (lp t : List E) (tp tn : Word) (k : Nat) : Prop extends
    AC s v ip c point scale lv lp t tp tn k where
  pc : v.pc = 0x8000f848
  dot : eAt v (s.getReg .x2 - 752) =
    dotRust (eqKernelRust (lp.take 6)) (((wOf s).drop (64 * k)).take 64)

set_option maxHeartbeats 16000000 in
/-- `0x8000f888`: the chunk's length `min(64, rest)`; `0x8000f830`: `dot(eq_z, chunk)` into
`f + 960`. -/
theorem at_dot (hDt : MultilinearContracts.DotSpec) {s v : MachineState} {ip : Word} {c : E}
    {point lp t : List E} {scale lv : E} {tp tn : Word} {k : Nat} (hpre : VerifyLayerPre s)
    (L : L10 s v ip c point scale lv lp t tp tn k) :
    ∃ u, Reaches Image.code v u ∧ (QD s u ip c point scale lv lp t tp tn k ∨ Dead Image.code u) := by
  have hb := bounds hpre
  have B := L.base
  have X := L.fx
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hab := hpre.stack.above
  have hrs := hpre.stack.rodata
  have hHv := B.heap.hi
  simp only [stackLo] at hab hrs
  unfold verifyLayerStack at hb hsm hab hrs
  have wR := hpre.weights
  have wS := hpre.weightsStack
  have mw := missVec B.heap hpre.weights hpre.weightsOut hpre.weightsSelf hpre.weightsStack
    hpre.weightsFree
  simp only [VecRegion, VecApart, vecPtr, vecLen, lClaim] at wR wS mw
  rv_eval [] at wR wS mw
  unfold verifyLayerStack at wS
  have hwl : (wOf s).length = (s.getMem (s.getReg .x15 + 64)).toNat := by
    rw [claim_weights, eListAt_length]
  have hm := L.lt
  simp only [mOf] at hm
  rw [hwl] at hm
  have hk64 : 64 * k < (s.getMem (s.getReg .x15 + 64)).toNat := by omega
  have hR : Region (s.getMem (s.getReg .x15 + 56)) (24 * (s.getMem (s.getReg .x15 + 64)).toNat) := by
    rcases wR with h0 | h0
    · omega
    · exact h0
  have h9 : (v.getReg .x9).toNat = (s.getMem (s.getReg .x15 + 64)).toNat - 64 * k := by
    rw [L.x9, hwl, BitVec.toNat_ofNat]
    have := (s.getMem (s.getReg .x15 + 64)).isLt
    omega
  -- `0x8000f888`, `0x8000f894`: the chunk's length in `a4`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000f888_spec L.pc trivial
  have k₁ := b8000f888_keeps h₁
  have hm₁ := b8000f888_mem_same h₁
  have to830 : ∃ t₂, Reaches Image.code v t₂ ∧ t₂.pc = 0x8000f830 ∧ (∀ a, t₂.getMem a = v.getMem a) ∧
      (∀ r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27],
        t₂.getReg r = v.getReg r) ∧
      t₂.getReg .x14 = BitVec.ofNat 64 (min 64 ((s.getMem (s.getReg .x15 + 64)).toNat - 64 * k)) := by
    by_cases h64 : (v.getReg .x9).toNat < 64
    · refine ⟨t₁, hr₁, b8000f888_pc_taken h₁ (by rw [show ((64 : Word)).toNat = 64 from rfl]; exact h64),
        hm₁, fun r hr ↦ k₁ r (reg_sub (by decide) hr), ?_⟩
      rw [b8000f888_x14 h₁, L.x9, hwl]
      congr 1
      omega
    · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000f894_spec
        (b8000f888_pc_not_taken h₁ (by rw [show ((64 : Word)).toNat = 64 from rfl]; omega)) trivial
      refine ⟨t₂, hr₁.trans hr₂, b8000f894_pc h₂, fun a ↦ by rw [b8000f894_mem_same h₂, hm₁],
        fun r hr ↦ by rw [b8000f894_keeps h₂ r (reg_sub (by decide) hr), k₁ r (reg_sub (by decide) hr)],
        ?_⟩
      rw [b8000f894_x14 h₂, show min 64 ((s.getMem (s.getReg .x15 + 64)).toNat - 64 * k) = 64 by omega]
      rfl
  obtain ⟨t₂, hr₂, pc₂, hm₂, rg₂, x14₂⟩ := to830
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := by rw [rg₂ .x2 (by decide), B.x2]
  have B₂ : Base s t₂ := B.same x2₂ hm₂
  have hN₂ : heapNext t₂ = heapNext v := by simp only [heapNext, hm₂]
  -- `0x8000f830`: `dot`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000f830_spec pc₂ (by
    rv_eval [x2₂]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₃ := b8000f830_keeps h₃
  have hm₃ := b8000f830_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := (k₃ .x2 (by decide)).trans x2₂
  have hm13 (a : Word) : t₃.getMem a = v.getMem a := by rw [hm₃, hm₂]
  have B₃ : Base s t₃ := B.same x2₃ hm13
  have hN₃ : heapNext t₃ = heapNext v := by simp only [heapNext, hm13]
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 752 := by rw [b8000f830_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = v.getMem (s.getReg .x2 - 1632) := by
    rw [b8000f830_x11 h₃, x2₂, hm₂]; rv_eval []
  have x12₃ : t₃.getReg .x12 = v.getMem (s.getReg .x2 - 1640) := by
    rw [b8000f830_x12 h₃, x2₂, hm₂]; rv_eval []
  have x13₃ : t₃.getReg .x13 = s.getMem (s.getReg .x15 + 56) + BitVec.ofNat 64 (1536 * k) := by
    rw [b8000f830_x13 h₃, rg₂ .x19 (by decide), L.x19]
  have x14₃ : t₃.getReg .x14 =
      BitVec.ofNat 64 (min 64 ((s.getMem (s.getReg .x15 + 64)).toNat - 64 * k)) := by
    rw [k₃ .x14 (by decide), x14₂]
  have hcl : (BitVec.ofNat 64 (min 64 ((s.getMem (s.getReg .x15 + 64)).toNat - 64 * k))).toNat =
      min 64 ((s.getMem (s.getReg .x15 + 64)).toNat - 64 * k) := by
    rw [BitVec.toNat_ofNat]; omega
  have zv := newBuf_vmr hpre B.heap X.ezB
  have hst : RtStack t₃ MultilinearContracts.dotStack :=
    hpre.stack.sub 1712 x2₃ (by unfold verifyLayerStack; decide) (by decide) (by decide) (by decide)
      (by decide)
  have zB := X.ezB
  simp only [NewBuf] at zB
  have dp : MultilinearContracts.DotPre t₃ := {
    ret := by rw [x10₃]; exact slot_vmr hpre (by decide) (by decide) (by decide)
    left := by rw [x11₃, x12₃]; exact zv
    right := by
      rw [x13₃, x14₃, hcl]
      intro i hi
      exact Region.valid hR (by addr_omega [hR, hk64, hi]) (by addr_omega [hR, hk64, hi])
        (by addr_omega [hR, hk64, hi])
    stack := hst.toStackOk
    retLeft := by
      rw [x10₃, x11₃, x12₃]
      rcases zB.2 with h0 | ⟨b1, b2⟩
      · addr_omega [h0]
      · addr_omega [b1, b2, hHv, hab, hb]
    retRight := by rw [x10₃, x13₃, x14₃, hcl]; addr_omega [wS, hb, hk64, hR]
    retStack := by rw [x10₃]; simp only [stackLo, x2₃]; addr_omega [hb]
    leftStack := by
      rw [x11₃, x12₃]; simp only [stackLo, x2₃]
      rcases zB.2 with h0 | ⟨b1, b2⟩
      · addr_omega [h0]
      · addr_omega [b1, b2, hHv, hab, hb]
    rightStack := by
      rw [x13₃, x14₃, hcl]; simp only [stackLo, x2₃]; addr_omega [wS, hb, hk64, hR]
    rodata := B₃.rodata hpre
    retRodata := by rw [x10₃]; addr_omega [hrs, hb]
    stackRodata := by simp only [stackLo, x2₃]; addr_omega [hrs, hb] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, B₄, F₄, hN₄, hlen, V₄⟩ | hd⟩ :=
    dotCall hDt hpre B₃ (hr₂.trans hr₃) (b8000f830_pc h₃) x10₃ dp
  swap
  · exact ⟨t₄, hr₄, Or.inr hd⟩
  rw [x11₃, x12₃, x13₃, eListAt_congr hm13] at V₄
  rw [eListAt_congr hm13] at V₄
  rw [x12₃, x14₃] at hlen
  rw [X.ezE, hlen, hcl, B.eListAt (fun y hy ↦ mw y (by addr_omega [hy, hR, hk64]))
    (Or.inr (by addr_omega [hR, hk64])), ← chunk_eq] at V₄
  refine ⟨t₄, hr₄, Or.inl {
    pc := by rw [hpc₄, returnAddress_eq, b8000f830_x1 h₃]; decide
    base := B₄
    fx := (X.keep hpre B.heap B₃.heap (le_of_eq hN₃.symm) (DFrame.of_same hm13 _)).keep hpre
      B₃.heap B₄.heap (le_of_eq hN₄.symm) F₄
    x8 := by rw [hp₄.reg .x8, k₃ .x8 (by decide), rg₂ .x8 (by decide), L.x8]
    x22 := by rw [hp₄.reg .x22, k₃ .x22 (by decide), rg₂ .x22 (by decide), L.x22]
    x26 := by rw [hp₄.reg .x26, k₃ .x26 (by decide), rg₂ .x26 (by decide), L.x26]
    x27 := by rw [hp₄.reg .x27, k₃ .x27 (by decide), rg₂ .x27 (by decide), L.x27]
    x24 := by rw [hp₄.reg .x24, k₃ .x24 (by decide), rg₂ .x24 (by decide), L.x24]
    x9 := by rw [hp₄.reg .x9, k₃ .x9 (by decide), rg₂ .x9 (by decide), L.x9]
    x19 := by rw [hp₄.reg .x19, k₃ .x19 (by decide), rg₂ .x19 (by decide), L.x19]
    x25 := by
      rw [hp₄.reg .x25, k₃ .x25 (by decide), rg₂ .x25 (by decide), L.x25,
        F₄ (s.getReg .x2 - 1600) (w10_low hpre (by addr_omega [hb]) (by addr_omega [hb])), hm13]
    x23 := by rw [hp₄.reg .x23, k₃ .x23 (by decide), rg₂ .x23 (by decide), L.x23]
    lt := L.lt
    acc := by
      rw [hp₄.reg .x18, k₃ .x18 (by decide), rg₂ .x18 (by decide), hp₄.reg .x20,
        k₃ .x20 (by decide), rg₂ .x20 (by decide), hp₄.reg .x21, k₃ .x21 (by decide),
        rg₂ .x21 (by decide)]
      exact L.acc
    rest := (L.rest.keep fun T hT ↦ transcriptAt_congr hm13 hT).body hpre B₃ B₄
      (F₄.mono fun a h ↦ w10_body hpre h)
    dot := V₄ }⟩

end Rv64Verifier.Gkr.Layer
