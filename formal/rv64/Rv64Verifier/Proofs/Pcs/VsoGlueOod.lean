import Rv64Verifier.Proofs.Pcs.VsoGlueHead
import Rv64Verifier.Proofs.EqEval

/-!
# `verify_stacked_opening`'s final level: an out-of-domain claim

`0x8000bad0` calls `eq_eval(S - 376, ood point, point + 24 fs, len - fs)`; `0x8000baec` loads the
value's limbs into `s7`, `s9`, `s8` (`GV`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem toNat_add_ofNat {p : Word} {k : ℕ} (h : p.toNat + k < 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt h]

/-- The point's suffix from the fold start `fs`: `n = len - fs` elements from `point + 24 fs`, in
the point's buffer, allocated between `u` and `v`. -/
theorem TB.suffix {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E}
    (h : TB OA s x u v Wl residual tf rt w0) {fs : ℕ}
    (hfs : fs ≤ (vecLen v (s.getReg .x2 - 280)).toNat) :
    Model.Pcs.sliceFrom fs (Wl.folds ++ tf) = some (eListAt v (vecPtr v (s.getReg .x2 - 280) +
      BitVec.ofNat 64 (24 * fs)) ((vecLen v (s.getReg .x2 - 280)).toNat - fs)) ∧
    (vecPtr v (s.getReg .x2 - 280) + BitVec.ofNat 64 (24 * fs)).toNat % 8 = 0 ∧
    ((vecLen v (s.getReg .x2 - 280)).toNat - fs = 0 ∨
      heapNext u ≤ (vecPtr v (s.getReg .x2 - 280) + BitVec.ofNat 64 (24 * fs)).toNat ∧
      (vecPtr v (s.getReg .x2 - 280) + BitVec.ofNat 64 (24 * fs)).toNat +
        24 * ((vecLen v (s.getReg .x2 - 280)).toNat - fs) ≤ heapNext v) := by
  obtain ⟨hPv, hPe, hPn⟩ := h.point
  have hl := hPv.len
  have hr := hPv.raw
  have hhv := h.heap.hi
  simp only [RawVecOk, Buf, heapEnd] at hr hhv
  have hlen : (Wl.folds ++ tf).length = (vecLen v (s.getReg .x2 - 280)).toNat := by
    rw [← hPe]; simp only [vecEs, eListAt_length]
  have hsl : Model.Pcs.sliceFrom fs (Wl.folds ++ tf) = some ((Wl.folds ++ tf).drop fs) := by
    simp only [Model.Pcs.sliceFrom, hlen, hfs, ↓reduceIte]
  rw [hsl, ← hPe, vecEs, pt_drop]
  have hp8 := hPn.1
  rcases hPn.2 with h0 | h0
  · have hc : (vecCap v (s.getReg .x2 - 280)).toNat = 0 := by omega
    have : fs = 0 := by omega
    subst this
    simp only [Nat.mul_zero, add_ofNat_zero]
    exact ⟨by trivial, hp8, Or.inl (by omega)⟩
  · have e : (vecPtr v (s.getReg .x2 - 280) + BitVec.ofNat 64 (24 * fs)).toNat =
        (vecPtr v (s.getReg .x2 - 280)).toNat + 24 * fs := toNat_add_ofNat (by omega)
    rw [e]
    refine ⟨rfl, by omega, ?_⟩
    by_cases hn : (vecLen v (s.getReg .x2 - 280)).toNat - fs = 0
    · exact Or.inl hn
    · exact Or.inr ⟨by omega, by omega⟩

/-- **An out-of-domain claim**: `eq_eval` of its point and the point's suffix. -/
theorem claimOod (hEq : FunSpec Image.code 0x8000da88 Proofs.EqEval.Pre Proofs.EqEval.Post)
    {OA : MachineState → Word → Model.TState → Prop} {s : MachineState} {x : LCtx}
    {u v w : MachineState} {Wl : Model.Pcs.WhirLocals} {residual tf : List E} {rt w0 : E} {j : ℕ}
    {a : Word} {acc : E} (hpre : VsoPre s) (h : GH OA s x u v w Wl residual tf rt w0 j a acc)
    (ht : u.getMem a = 0xffffffffffffffff) :
    ∃ w', Reaches Image.code w w' ∧
      (Dead Image.code w' ∨ ∃ val, GV OA s x u v w' Wl residual tf rt w0 j a acc val) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hsp := h.gs.sp
  have fin := h.tb.toTI.fin
  obtain ⟨ea, ha1, ha2, ha8⟩ := fin.claimAt h.jlt
  rw [h.addr] at ea ha1 ha2 ha8
  have hs := fin.hs
  have hhs := hpre.heap.lo
  have hhu := fin.heap.hi
  simp only [heapEnd] at hhu
  have hab := hpre.stack.above
  rw [stackLo_vso] at hab
  simp only [heapEnd] at hab
  have hro := hst.rodata
  rw [stackLo_vso] at hro
  have hR : Region a 88 := heap_region (by simp only [heapStart, heapNext] at hhs hs ⊢; omega)
    (by simp only [heapEnd]; omega) ha8
  -- the out-of-domain point
  have hfz := fin.frozen j h.jlt
  have hal := fin.aligned j h.jlt
  rw [h.addr] at hfz hal
  simp only [WeightAligned, ht, ↓reduceIte] at hal
  have hob := bufBound (L := x.L) (by simp only [heapEnd]; omega) fun y hy ↦ hfz y (by
    simp only [InBufs, ht, ↓reduceIte]; exact hy)
  have e16 : vecPtr u (a + 8) = u.getMem (a + 16) := by simp only [vecPtr]; rv_eval []
  have e24 : vecLen u (a + 8) = u.getMem (a + 24) := by simp only [vecLen]; rv_eval []
  rw [e16, e24] at hob
  rw [e16] at hal
  -- the point's suffix
  have hfs := h.fsle
  obtain ⟨hsl, hP8, hPb⟩ := h.tb.suffix hfs
  generalize hP : vecPtr v (s.getReg .x2 - 280) +
    BitVec.ofNat 64 (24 * (u.getMem (a + 80)).toNat) = P at hsl hP8 hPb
  generalize hn : (vecLen v (s.getReg .x2 - 280)).toNat - (u.getMem (a + 80)).toNat = n at hsl hPb
  have hm848 := h.m848
  rw [hP] at hm848
  have hx26 := h.x26
  rw [hn] at hx26
  have hum := h.tb.mono
  have hvw := h.gs.mono
  have hhw := h.gs.heap.hi
  simp only [heapEnd] at hhw
  have T := GS.ti hpre h.tb h.gs
  have kw := T.claimWord hpre h.jlt
  rw [h.addr] at kw
  -- `0x8000bad0`
  have hpc : w.pc = 0x8000bad0 := by rw [h.pc]; simp only [ht, ↓reduceIte]
  obtain ⟨t₃, r₃, h₃⟩ := Sym.BlockSpec.reaches b8000bad0_spec hpc (by
    rv_eval [hsp, h.x8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | exact Region.valid hR (by addr_omega [ha2, hhu]) (by addr_omega [ha2, hhu])
          (by addr_omega [ha2, hhu, ha8]))
  have hm₃ := b8000bad0_mem_same h₃
  have k₃ := b8000bad0_keeps h₃
  have G₃ := h.gs.same hpre hm₃ (k₃ .x2 (by decide))
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 1040 := G₃.sp
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 376 := by rw [b8000bad0_x10 h₃, hsp]; rv_eval []
  have x11₃ : t₃.getReg .x11 = u.getMem (a + 16) := by
    rw [b8000bad0_x11 h₃, h.x8]; exact kw 16 (by decide)
  have x12₃ : t₃.getReg .x12 = u.getMem (a + 24) := by
    rw [b8000bad0_x12 h₃, h.x8]; exact kw 24 (by decide)
  have x13₃ : t₃.getReg .x13 = P := by
    rw [b8000bad0_x13 h₃, hsp, ← hm848]; rv_eval []
  have x14₃ : t₃.getReg .x14 = BitVec.ofNat 64 n := by rw [b8000bad0_x14 h₃, hx26]
  have hsl₃ : stackLo t₃ Proofs.EqEval.stackSize = s.getReg .x2 - 2176 := by
    simp only [stackLo, sp₃, Proofs.EqEval.stackSize, mulStack, Nat.reduceAdd]; rv_eval []
  have hn64 : n < 2 ^ 64 := by omega
  have hpreE : Proofs.EqEval.Pre t₃ := {
    ret := by rw [x10₃]; valid_sub hst.valid [hb]
    left := by
      rw [x11₃, x12₃]
      rcases hob with h0 | h0
      · intro i hi; omega
      · exact Region.vrange (heap_region (n := 24 * (u.getMem (a + 24)).toNat)
          (by simp only [heapStart, heapNext] at hhs hs ⊢; omega)
          (by simp only [heapEnd]; omega) hal) (Nat.le_refl _) (by omega) hal
    right := by
      rw [x13₃, x14₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
      rcases hPb with h0 | h0
      · intro i hi; omega
      · exact Region.vrange (heap_region (n := 24 * n)
          (by simp only [heapStart, heapNext] at hhs hs ⊢; omega)
          (by simp only [heapEnd]; omega) hP8) (Nat.le_refl _) (by omega) hP8
    stack := ⟨by rw [hsl₃]; valid_sub hst.valid [hb], by rw [sp₃]; addr_omega [hb]⟩
    retStack := by rw [x10₃, hsl₃]; addr_omega [hb]
    leftStack := by
      rw [x11₃, x12₃, hsl₃]
      rcases hob with h0 | h0
      · exact Or.inl h0
      · addr_omega [h0.2, hhu, hab, hb]
    rightStack := by
      rw [x13₃, x14₃, hsl₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
      rcases hPb with h0 | h0
      · exact Or.inl (by omega)
      · addr_omega [h0.2, hhw, hvw, hab, hb]
    rodata := InvR.rodata' hpre G₃.inv
    stackRodata := by rw [hsl₃]; simp only [vsoStack, basisStack, ringEvalStack, mulStack,
      roundPolyStack, nextScalarsStack, shuntNextStack, nextScalarStack, absorbStack, duplexStack,
      keccakFStack, memStack] at hro; addr_omega [hro, hb] }
  obtain ⟨t₄, r₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ := hEq.call (Reaches.refl t₃) (b8000bad0_pc h₃) hpreE
  swap
  · exact ⟨t₄, r₃.trans r₄, Or.inl hdead⟩
  have F₄ := DFrame.of_two hpost₄.frame
  rw [x10₃, hsl₃] at F₄
  obtain ⟨G₄, n₄⟩ := G₃.stepS hpre F₄ (fun y hy ↦ by
    rcases hy with hy | hy
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [hy, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hy, hb]))))) (hpres₄ .x2 (by decide))
  have hlen := hpost₄.len
  rw [x12₃, x14₃] at hlen
  have hval := hpost₄.value
  simp only [Proofs.EqEval.left, Proofs.EqEval.right, Proofs.EqEval.len] at hval
  rw [x10₃, x11₃, x12₃, x13₃, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at hval
  have eR : eListAt t₃ P n = eListAt v P n := G₃.eListLow hpre (by
    rcases hPb with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨by omega, h0.2⟩)
  have eL : eListAt t₃ (u.getMem (a + 16)) n = vecEs u (a + 8) := by
    rw [vecEs, e16, e24, hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
    rw [hlen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64] at hob
    exact (GS.ti hpre h.tb G₃).eList hpre (by
      rcases hob with h0 | h0
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, h0.2⟩)
  rw [eL, eR] at hval
  -- `0x8000baec`
  obtain ⟨t₅, r₅, h₅⟩ := Sym.BlockSpec.reaches b8000baec_spec
    (by rw [hpc₄, returnAddress_eq, b8000bad0_x1 h₃]; decide) (by
      rv_eval [G₄.sp]
      and_intros <;> valid_access hst.valid [hb])
  have hm₅ := b8000baec_mem_same h₅
  have G₅ := G₄.same hpre hm₅ (b8000baec_keeps h₅ .x2 (by decide))
  have kS (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 376).toNat ∨ (s.getReg .x2 - 352).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2).toNat) : t₅.getMem y = w.getMem y := by
    rw [hm₅, F₄ y fun i hi hw ↦ by rcases hw with hw | hw <;> rcases hy with hy | hy <;>
      addr_omega [hw, hi, hy, hb], hm₃]
  refine ⟨t₅, r₃.trans (r₄.trans r₅), Or.inr ⟨Model.eqEvalRust (vecEs u (a + 8)) (eListAt v P n), {
    tb := h.tb
    gs := G₅
    pc := b8000baec_pc h₅
    jlt := h.jlt
    addr := h.addr
    m880 := by rw [kS _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m880
    m872 := by rw [kS _ (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩)]; exact h.m872
    fold := h.fold
    wt := by
      rw [← h.wt, (DFrame.of_same hm₅ _).eAt (w := fun _ ↦ False) (fun _ _ h ↦ h)]
      rw [F₄.eAt fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb]]
      simp only [eAt, hm₃]
    scalar := by
      rw [← h.scalar, (DFrame.of_same hm₅ _).eAt (w := fun _ ↦ False) (fun _ _ h ↦ h)]
      rw [F₄.eAt fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb]]
      simp only [eAt, hm₃]
    value := by
      rw [b8000baec_x23 h₅, b8000baec_x24 h₅, b8000baec_x25 h₅, G₄.sp, Model.eqEvalRust_eq, ← hval]
      simp only [eAt]
      rv_eval []
    eval := ⟨eListAt v P n, by simp only [gluedAt]; exact hsl, by
      simp only [gluedAt, weightAt, ht, ↓reduceIte, Model.Pcs.GluedWeightRust.evaluate]⟩ }⟩⟩

end Rv64Verifier.Proofs.Pcs.Vso
