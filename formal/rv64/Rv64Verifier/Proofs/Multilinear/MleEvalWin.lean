import Rv64Verifier.Proofs.Multilinear.EqKernelWin
import Rv64Verifier.Blocks.F56

/-!
# `multilinear_eval`: `Scaled::mul`'s window loops

`Scaled::mul` as inlined in `multilinear_eval` (`Blocks/F56.lean`), as in `EqKernelWin.lean`: a loop
per limb at `0x8000d4d4` (limb `a5`), `0x8000d520` (`a4`) and `0x8000d56c` (`a1`), the product in
`a0`, `a2`, `a3`, the table at `s10`, its length in `s11`, the loops' ends in `s4`, `s6`, `s8`.
-/

namespace Rv64Verifier.Proofs.Multilinear.MleEvalWin
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.MultilinearWords Rv64Verifier.Model
  Rv64Verifier.Blocks.F56 Rv64Verifier.Proofs.Multilinear.ScalerFill
  Rv64Verifier.Proofs.Multilinear.EqKernelWin
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The first limb, at `0x8000d4d4` -/

def keep1 : List Reg := [.x1, .x2, .x3, .x4, .x8, .x9, .x11, .x14, .x15, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

structure Inv1 (u₀ u : MachineState) (T : Word) (w : Nat) : Prop where
  pc : u.pc = 0x8000d4d4
  lt : w < 11
  mem : ∀ a, u.getMem a = u₀.getMem a
  keep : ∀ r ∈ keep1, u.getReg r = u₀.getReg r
  sh : u.getReg .x16 = BitVec.ofNat 64 (6 * w)
  base : u.getReg .x17 = BitVec.ofNat 64 (64 * w)
  acc : (u.getReg .x10, u.getReg .x12, u.getReg .x13) =
    (winFold (tab u₀ T) (u₀.getReg .x15) (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 0 w).1

theorem win1 {u₀ : MachineState} {T : Word} (hT : BufP T) (h26 : u₀.getReg .x26 = T)
    (h27 : u₀.getReg .x27 = 2112) (hend : u₀.getReg .x20 = 704) (hpc : u₀.pc = 0x8000d4d4)
    (h15 : u₀.getReg .x16 = 0) (h16 : u₀.getReg .x17 = 0) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x8000d518 ∧ (∀ a, v.getMem a = u₀.getMem a) ∧
      (∀ r ∈ keep1, v.getReg r = u₀.getReg r) ∧
      (v.getReg .x10, v.getReg .x12, v.getReg .x13) = (winFold (tab u₀ T) (u₀.getReg .x15)
        (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 0 11).1 := by
  have hTl := hT.lo
  have hTh := hT.hi
  simp only [tabBytes] at hTh
  refine Reaches.loop (code := Image.code) (fun u ↦ ∃ w, Inv1 u₀ u T w)
    (fun u ↦ 704 - (u.getReg .x17).toNat) _ (fun u ⟨w, hu⟩ ↦ ?_) u₀
    ⟨0, hpc, by decide, fun _ ↦ rfl, fun _ _ ↦ rfl, h15, h16, rfl⟩
  have hw := hu.lt
  have hlimb := hu.keep .x15 (by decide)
  have hbits := bits_lt (u₀.getReg .x15) w
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d4d4_spec hu.pc (by rv_eval [])
  have k₁ := b8000d4d4_keeps h₁
  have hm₁ := b8000d4d4_mem_same h₁
  have hb : (u₀.getReg .x15 >>> (6 * w) &&& (63 : Word)).toNat = bits (u₀.getReg .x15) w := rfl
  have hx5 : v₁.getReg .x5 = BitVec.ofNat 64 (64 * w) + (u₀.getReg .x15 >>> (6 * w) &&& 63) :=
    h₁.reg_eq .x5 rfl (by rv_eval [hu.sh, hu.base, hlimb, shift_eq hw])
  have hi : (v₁.getReg .x5).toNat = 64 * w + bits (u₀.getReg .x15) w := by
    rw [hx5]; addr_omega [hb, hbits, hw]
  have hpc₁ : v₁.pc = 0x8000d4e4 := h₁.pc_eq (by
    rv_eval [hu.sh, hu.base, hlimb, shift_eq hw, hu.keep .x27 (by decide), h27]
    rw [← hx5]
    simp only [BitVec.ult, hi]
    rw [show (2112 : Word).toNat = 2112 from rfl, decide_eq_true (by omega)]
    rfl)
  have haddr := entry_addr (T := T) hi (by omega) (by omega)
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d4e4_spec hpc₁ (by
    rv_eval [k₁ .x26 (by decide), hu.keep .x26 (by decide), h26, haddr]
    exact entry_valid hT (by omega))
  have k₂ := b8000d4e4_keeps h₂
  have hm₂ := b8000d4e4_mem_same h₂
  have hreg (r : Reg) (hr : r ∈ keep1) : v.getReg r = u₀.getReg r :=
    (k₂ r hr).trans ((k₁ r (mem_of_mem hr _)).trans (hu.keep r hr))
  have hmem (a : Word) : v.getMem a = u₀.getMem a := (hm₂ a).trans ((hm₁ a).trans (hu.mem a))
  have hacc : (v.getReg .x10, v.getReg .x12, v.getReg .x13) = (winFold (tab u₀ T) (u₀.getReg .x15)
      (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 0 (w + 1)).1 := by
    rw [winFold_succ, mulStep, winFold_snd, Nat.zero_add, lookup _ (by omega), ← hu.acc,
      b8000d4e4_x10 h₂, b8000d4e4_x12 h₂, b8000d4e4_x13 h₂, k₁ .x26 (by decide),
      hu.keep .x26 (by decide), h26, haddr, hm₁, hm₁, hm₁, hu.mem, hu.mem, hu.mem,
      k₁ .x10 (by decide), k₁ .x12 (by decide), k₁ .x13 (by decide)]
    exact acc_step
  have h16 : v₁.getReg .x17 = BitVec.ofNat 64 (64 * w) := (k₁ .x17 (by decide)).trans hu.base
  have hend' : v₁.getReg .x20 = 704 :=
    (k₁ .x20 (by decide)).trans ((hu.keep .x20 (by decide)).trans hend)
  have hx16 : v.getReg .x17 = BitVec.ofNat 64 (64 * (w + 1)) := by
    rw [b8000d4e4_x17 h₂, h16]; addr_omega [hw]
  by_cases hlast : w + 1 = 11
  · refine Or.inl ⟨v, hr₁.trans hr₂,
      b8000d4e4_pc_not_taken h₂ (by rw [h16, hend']; addr_omega [hlast]), hmem, hreg, ?_⟩
    rw [hacc, hlast]
  · refine Or.inr ⟨v, hr₁.trans hr₂, ⟨w + 1, {
      pc := b8000d4e4_pc_taken h₂ (by rw [h16, hend']; addr_omega [hlast, hw])
      lt := by omega
      mem := hmem
      keep := hreg
      sh := by
        rw [b8000d4e4_x16 h₂, k₁ .x16 (by decide), hu.sh]; addr_omega [hw]
      base := hx16
      acc := hacc }⟩, ?_⟩
    rw [hx16, hu.base]
    addr_omega [hw, hlast]

/-! ## The second limb, at `0x8000d520` -/

def keep2 : List Reg := [.x1, .x2, .x3, .x4, .x7, .x8, .x9, .x11, .x14, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

structure Inv2 (u₀ u : MachineState) (T : Word) (w : Nat) : Prop where
  pc : u.pc = 0x8000d520
  lt : w < 11
  mem : ∀ a, u.getMem a = u₀.getMem a
  keep : ∀ r ∈ keep2, u.getReg r = u₀.getReg r
  sh : u.getReg .x15 = BitVec.ofNat 64 (6 * w)
  base : u.getReg .x16 = BitVec.ofNat 64 (64 * (11 + w))
  acc : (u.getReg .x10, u.getReg .x12, u.getReg .x13) =
    (winFold (tab u₀ T) (u₀.getReg .x14) (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 11 w).1

theorem win2 {u₀ : MachineState} {T : Word} (hT : BufP T) (h26 : u₀.getReg .x26 = T)
    (h27 : u₀.getReg .x27 = 2112) (hend : u₀.getReg .x22 = 1408) (hpc : u₀.pc = 0x8000d520)
    (h15 : u₀.getReg .x15 = 0) (h16 : u₀.getReg .x16 = 704) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x8000d564 ∧ (∀ a, v.getMem a = u₀.getMem a) ∧
      (∀ r ∈ keep2, v.getReg r = u₀.getReg r) ∧
      (v.getReg .x10, v.getReg .x12, v.getReg .x13) = (winFold (tab u₀ T) (u₀.getReg .x14)
        (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 11 11).1 := by
  have hTl := hT.lo
  have hTh := hT.hi
  simp only [tabBytes] at hTh
  refine Reaches.loop (code := Image.code) (fun u ↦ ∃ w, Inv2 u₀ u T w)
    (fun u ↦ 1408 - (u.getReg .x16).toNat) _ (fun u ⟨w, hu⟩ ↦ ?_) u₀
    ⟨0, hpc, by decide, fun _ ↦ rfl, fun _ _ ↦ rfl, h15, h16.trans (by decide), rfl⟩
  have hw := hu.lt
  have hlimb := hu.keep .x14 (by decide)
  have hbits := bits_lt (u₀.getReg .x14) w
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d520_spec hu.pc (by rv_eval [])
  have k₁ := b8000d520_keeps h₁
  have hm₁ := b8000d520_mem_same h₁
  have hb : (u₀.getReg .x14 >>> (6 * w) &&& (63 : Word)).toNat = bits (u₀.getReg .x14) w := rfl
  have hx5 : v₁.getReg .x17 = BitVec.ofNat 64 (64 * (11 + w)) + (u₀.getReg .x14 >>> (6 * w) &&& 63) :=
    h₁.reg_eq .x17 rfl (by rv_eval [hu.sh, hu.base, hlimb, shift_eq hw])
  have hi : (v₁.getReg .x17).toNat = 64 * (11 + w) + bits (u₀.getReg .x14) w := by
    rw [hx5]; addr_omega [hb, hbits, hw]
  have hpc₁ : v₁.pc = 0x8000d530 := h₁.pc_eq (by
    rv_eval [hu.sh, hu.base, hlimb, shift_eq hw, hu.keep .x27 (by decide), h27]
    rw [← hx5]
    simp only [BitVec.ult, hi]
    rw [show (2112 : Word).toNat = 2112 from rfl, decide_eq_true (by omega)]
    rfl)
  have haddr := entry_addr (T := T) hi (by omega) (by omega)
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d530_spec hpc₁ (by
    rv_eval [k₁ .x26 (by decide), hu.keep .x26 (by decide), h26, haddr]
    exact entry_valid hT (by omega))
  have k₂ := b8000d530_keeps h₂
  have hm₂ := b8000d530_mem_same h₂
  have hreg (r : Reg) (hr : r ∈ keep2) : v.getReg r = u₀.getReg r :=
    (k₂ r hr).trans ((k₁ r (mem_of_mem hr _)).trans (hu.keep r hr))
  have hmem (a : Word) : v.getMem a = u₀.getMem a := (hm₂ a).trans ((hm₁ a).trans (hu.mem a))
  have hacc : (v.getReg .x10, v.getReg .x12, v.getReg .x13) = (winFold (tab u₀ T) (u₀.getReg .x14)
      (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 11 (w + 1)).1 := by
    rw [winFold_succ, mulStep, winFold_snd, lookup _ (by omega), ← hu.acc,
      b8000d530_x10 h₂, b8000d530_x12 h₂, b8000d530_x13 h₂, k₁ .x26 (by decide),
      hu.keep .x26 (by decide), h26, haddr, hm₁, hm₁, hm₁, hu.mem, hu.mem, hu.mem,
      k₁ .x10 (by decide), k₁ .x12 (by decide), k₁ .x13 (by decide)]
    exact acc_step
  have h16 : v₁.getReg .x16 = BitVec.ofNat 64 (64 * (11 + w)) := (k₁ .x16 (by decide)).trans hu.base
  have hend' : v₁.getReg .x22 = 1408 :=
    (k₁ .x22 (by decide)).trans ((hu.keep .x22 (by decide)).trans hend)
  have hx16 : v.getReg .x16 = BitVec.ofNat 64 (64 * (11 + (w + 1))) := by
    rw [b8000d530_x16 h₂, h16]; addr_omega [hw]
  by_cases hlast : w + 1 = 11
  · refine Or.inl ⟨v, hr₁.trans hr₂,
      b8000d530_pc_not_taken h₂ (by rw [h16, hend']; addr_omega [hlast]), hmem, hreg, ?_⟩
    rw [hacc, hlast]
  · refine Or.inr ⟨v, hr₁.trans hr₂, ⟨w + 1, {
      pc := b8000d530_pc_taken h₂ (by rw [h16, hend']; addr_omega [hlast, hw])
      lt := by omega
      mem := hmem
      keep := hreg
      sh := by
        rw [b8000d530_x15 h₂, k₁ .x15 (by decide), hu.sh]; addr_omega [hw]
      base := hx16
      acc := hacc }⟩, ?_⟩
    rw [hx16, hu.base]
    addr_omega [hw, hlast]

/-! ## The third limb, at `0x8000d56c` -/

def keep3 : List Reg := [.x1, .x2, .x3, .x4, .x6, .x7, .x8, .x9, .x11, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

structure Inv3 (u₀ u : MachineState) (T : Word) (w : Nat) : Prop where
  pc : u.pc = 0x8000d56c
  lt : w < 11
  mem : ∀ a, u.getMem a = u₀.getMem a
  keep : ∀ r ∈ keep3, u.getReg r = u₀.getReg r
  sh : u.getReg .x14 = BitVec.ofNat 64 (6 * w)
  base : u.getReg .x15 = BitVec.ofNat 64 (64 * (22 + w))
  acc : (u.getReg .x10, u.getReg .x12, u.getReg .x13) =
    (winFold (tab u₀ T) (u₀.getReg .x11) (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 22 w).1

theorem win3 {u₀ : MachineState} {T : Word} (hT : BufP T) (h26 : u₀.getReg .x26 = T)
    (h27 : u₀.getReg .x27 = 2112) (hend : u₀.getReg .x24 = 2112) (hpc : u₀.pc = 0x8000d56c)
    (h15 : u₀.getReg .x14 = 0) (h16 : u₀.getReg .x15 = 1408) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x8000d5b0 ∧ (∀ a, v.getMem a = u₀.getMem a) ∧
      (∀ r ∈ keep3, v.getReg r = u₀.getReg r) ∧
      (v.getReg .x10, v.getReg .x12, v.getReg .x13) = (winFold (tab u₀ T) (u₀.getReg .x11)
        (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 22 11).1 := by
  have hTl := hT.lo
  have hTh := hT.hi
  simp only [tabBytes] at hTh
  refine Reaches.loop (code := Image.code) (fun u ↦ ∃ w, Inv3 u₀ u T w)
    (fun u ↦ 2112 - (u.getReg .x15).toNat) _ (fun u ⟨w, hu⟩ ↦ ?_) u₀
    ⟨0, hpc, by decide, fun _ ↦ rfl, fun _ _ ↦ rfl, h15, h16.trans (by decide), rfl⟩
  have hw := hu.lt
  have hlimb := hu.keep .x11 (by decide)
  have hbits := bits_lt (u₀.getReg .x11) w
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000d56c_spec hu.pc (by rv_eval [])
  have k₁ := b8000d56c_keeps h₁
  have hm₁ := b8000d56c_mem_same h₁
  have hb : (u₀.getReg .x11 >>> (6 * w) &&& (63 : Word)).toNat = bits (u₀.getReg .x11) w := rfl
  have hx5 : v₁.getReg .x16 = BitVec.ofNat 64 (64 * (22 + w)) + (u₀.getReg .x11 >>> (6 * w) &&& 63) :=
    h₁.reg_eq .x16 rfl (by rv_eval [hu.sh, hu.base, hlimb, shift_eq hw])
  have hi : (v₁.getReg .x16).toNat = 64 * (22 + w) + bits (u₀.getReg .x11) w := by
    rw [hx5]; addr_omega [hb, hbits, hw]
  have hpc₁ : v₁.pc = 0x8000d57c := h₁.pc_eq (by
    rv_eval [hu.sh, hu.base, hlimb, shift_eq hw, hu.keep .x27 (by decide), h27]
    rw [← hx5]
    simp only [BitVec.ult, hi]
    rw [show (2112 : Word).toNat = 2112 from rfl, decide_eq_true (by omega)]
    rfl)
  have haddr := entry_addr (T := T) hi (by omega) (by omega)
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d57c_spec hpc₁ (by
    rv_eval [k₁ .x26 (by decide), hu.keep .x26 (by decide), h26, haddr]
    exact entry_valid hT (by omega))
  have k₂ := b8000d57c_keeps h₂
  have hm₂ := b8000d57c_mem_same h₂
  have hreg (r : Reg) (hr : r ∈ keep3) : v.getReg r = u₀.getReg r :=
    (k₂ r hr).trans ((k₁ r (mem_of_mem hr _)).trans (hu.keep r hr))
  have hmem (a : Word) : v.getMem a = u₀.getMem a := (hm₂ a).trans ((hm₁ a).trans (hu.mem a))
  have hacc : (v.getReg .x10, v.getReg .x12, v.getReg .x13) = (winFold (tab u₀ T) (u₀.getReg .x11)
      (u₀.getReg .x10, u₀.getReg .x12, u₀.getReg .x13) 22 (w + 1)).1 := by
    rw [winFold_succ, mulStep, winFold_snd, lookup _ (by omega), ← hu.acc,
      b8000d57c_x10 h₂, b8000d57c_x12 h₂, b8000d57c_x13 h₂, k₁ .x26 (by decide),
      hu.keep .x26 (by decide), h26, haddr, hm₁, hm₁, hm₁, hu.mem, hu.mem, hu.mem,
      k₁ .x10 (by decide), k₁ .x12 (by decide), k₁ .x13 (by decide)]
    exact acc_step
  have h16 : v₁.getReg .x15 = BitVec.ofNat 64 (64 * (22 + w)) := (k₁ .x15 (by decide)).trans hu.base
  have hend' : v₁.getReg .x24 = 2112 :=
    (k₁ .x24 (by decide)).trans ((hu.keep .x24 (by decide)).trans hend)
  have hx16 : v.getReg .x15 = BitVec.ofNat 64 (64 * (22 + (w + 1))) := by
    rw [b8000d57c_x15 h₂, h16]; addr_omega [hw]
  by_cases hlast : w + 1 = 11
  · refine Or.inl ⟨v, hr₁.trans hr₂,
      b8000d57c_pc_not_taken h₂ (by rw [h16, hend']; addr_omega [hlast]), hmem, hreg, ?_⟩
    rw [hacc, hlast]
  · refine Or.inr ⟨v, hr₁.trans hr₂, ⟨w + 1, {
      pc := b8000d57c_pc_taken h₂ (by rw [h16, hend']; addr_omega [hlast, hw])
      lt := by omega
      mem := hmem
      keep := hreg
      sh := by
        rw [b8000d57c_x14 h₂, k₁ .x14 (by decide), hu.sh]; addr_omega [hw]
      base := hx16
      acc := hacc }⟩, ?_⟩
    rw [hx16, hu.base]
    addr_omega [hw, hlast]

/-! ## The product, from `0x8000d4c0` to `0x8000d448` -/

def tmKeep : List Reg := [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
  .x26, .x27, .x28, .x30, .x31]

/-- `Scaled::mul` of the limbs in `a5`, `a4`, `a1` by the table at `T` (`s10`), into `a0`, `a2`,
`a3`. -/
theorem table_mul {u : MachineState} {T : Word} (hT : BufP T) (hpc : u.pc = 0x8000d4c0)
    (h26 : u.getReg .x26 = T) (h27 : u.getReg .x27 = 2112) (h20 : u.getReg .x20 = 704)
    (h22 : u.getReg .x22 = 1408) (h24 : u.getReg .x24 = 2112) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x8000d448 ∧ (∀ r ∈ tmKeep, v.getReg r = u.getReg r) ∧
      (∀ a, v.getMem a = u.getMem a) ∧
      (v.getReg .x10, v.getReg .x12, v.getReg .x13) =
        scaledMul (tab u T) (u.getReg .x15, u.getReg .x14, u.getReg .x11) := by
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000d4c0_spec hpc (by rv_eval [])
  have k₀ := b8000d4c0_keeps h₀
  have hm₀ := b8000d4c0_mem_same h₀
  obtain ⟨w₁, hr₁, pc₁, hm₁, k₁, acc₁⟩ := win1 hT ((k₀ .x26 (by decide)).trans h26)
    ((k₀ .x27 (by decide)).trans h27) ((k₀ .x20 (by decide)).trans h20) (b8000d4c0_pc h₀)
    (b8000d4c0_x16 h₀) (b8000d4c0_x17 h₀)
  obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000d518_spec pc₁ (by rv_eval [])
  have k₂ := b8000d518_keeps h₂
  have hm₂ := b8000d518_mem_same h₂
  have g (r : Reg) (hr : r ∈ tmKeep) : w₂.getReg r = u.getReg r :=
    (k₂ r (mem_of_mem hr _)).trans ((k₁ r (mem_of_mem hr _)).trans (k₀ r (mem_of_mem hr _)))
  obtain ⟨w₃, hr₃, pc₃, hm₃, k₃, acc₂⟩ := win2 hT ((g .x26 (by decide)).trans h26)
    ((g .x27 (by decide)).trans h27) ((g .x22 (by decide)).trans h22)
    (b8000d518_pc h₂) (b8000d518_x15 h₂) (b8000d518_x16 h₂)
  obtain ⟨w₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000d564_spec pc₃ (by rv_eval [])
  have k₄ := b8000d564_keeps h₄
  have hm₄ := b8000d564_mem_same h₄
  have g' (r : Reg) (hr : r ∈ tmKeep) : w₄.getReg r = u.getReg r :=
    (k₄ r (mem_of_mem hr _)).trans ((k₃ r (mem_of_mem hr _)).trans (g r hr))
  obtain ⟨w₅, hr₅, pc₅, hm₅, k₅, acc₃⟩ := win3 hT ((g' .x26 (by decide)).trans h26)
    ((g' .x27 (by decide)).trans h27) ((g' .x24 (by decide)).trans h24)
    (b8000d564_pc h₄) (b8000d564_x14 h₄) (b8000d564_x15 h₄)
  obtain ⟨v, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000d5b0_spec pc₅ (by rv_eval [])
  have k₆ := b8000d5b0_keeps h₆
  refine ⟨v, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))),
    b8000d5b0_pc h₆, fun r hr ↦ (k₆ r (mem_of_mem hr _)).trans
      ((k₅ r (mem_of_mem hr _)).trans (g' r hr)),
    fun a ↦ (b8000d5b0_mem_same h₆ a).trans ((hm₅ a).trans ((hm₄ a).trans ((hm₃ a).trans
      ((hm₂ a).trans ((hm₁ a).trans (hm₀ a)))))), ?_⟩
  have e11 : w₄.getReg .x11 = u.getReg .x11 := by
    rw [k₄ .x11 (by decide), k₃ .x11 (by decide), k₂ .x11 (by decide), k₁ .x11 (by decide),
      k₀ .x11 (by decide)]
  have e14 : w₂.getReg .x14 = u.getReg .x14 := by
    rw [k₂ .x14 (by decide), k₁ .x14 (by decide), k₀ .x14 (by decide)]
  have e0 : (w₀.getReg .x10, w₀.getReg .x12, w₀.getReg .x13) = lzero := by
    rw [b8000d4c0_x10 h₀, b8000d4c0_x12 h₀, b8000d4c0_x13 h₀]; rfl
  rw [k₆ .x10 (by decide), k₆ .x12 (by decide), k₆ .x13 (by decide), acc₃, scaledMul_win, e11,
    k₄ .x10 (by decide), k₄ .x12 (by decide), k₄ .x13 (by decide), acc₂, e14,
    k₂ .x10 (by decide), k₂ .x12 (by decide), k₂ .x13 (by decide), acc₁, k₀ .x15 (by decide), e0,
    tab_same (fun a ↦ (hm₄ a).trans ((hm₃ a).trans ((hm₂ a).trans ((hm₁ a).trans (hm₀ a))))),
    tab_same (fun a ↦ (hm₂ a).trans ((hm₁ a).trans (hm₀ a))), tab_same hm₀]

end Rv64Verifier.Proofs.Multilinear.MleEvalWin
