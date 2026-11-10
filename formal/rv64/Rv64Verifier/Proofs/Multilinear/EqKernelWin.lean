import Rv64Verifier.Proofs.Multilinear.ScalerFill
import Rv64Verifier.Blocks.F51

/-!
# `eq_kernel`: `Scaled::mul`'s window loops

`Scaled::mul` as inlined in `eq_kernel` (`Blocks/F51.lean`): a loop per limb, each of
`WINDOWS_PER_LIMB = 11` lookups `product += table[64·t + (limb >> 6w) % 64]`, at `0x8000cd38`
(limb `a7`, tables `0..11`), `0x8000cd84` (`a4`, `11..22`) and `0x8000cdd0` (`a2`, `22..33`),
the product in `a3`, `a1`, `a0` and the table at `s3`. Each lemma takes its loop from head to exit
and says it computes `winFold`, `Model.scaledMul`'s inner fold; no index reaches the table's
length, so the bounds checks never trap.
-/

namespace Rv64Verifier.Proofs.Multilinear.EqKernelWin
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.MultilinearWords Rv64Verifier.Model
  Rv64Verifier.Blocks.F51 Rv64Verifier.Proofs.Multilinear.ScalerFill
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- One limb's lookups, `w` windows in, from table `t0` and product `acc`. -/
def winFold (tables : List Limbs) (limb : BitVec 64) (acc : Limbs) (t0 w : Nat) : Limbs × Nat :=
  (List.range w).foldl (mulStep tables limb) (acc, t0)

theorem winFold_succ (tables : List Limbs) (limb : BitVec 64) (acc : Limbs) (t0 w : Nat) :
    winFold tables limb acc t0 (w + 1) = mulStep tables limb (winFold tables limb acc t0 w) w := by
  simp only [winFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem winFold_snd (tables : List Limbs) (limb : BitVec 64) (acc : Limbs) (t0 : Nat) :
    ∀ w, (winFold tables limb acc t0 w).2 = t0 + w
  | 0 => rfl
  | w + 1 => by rw [winFold_succ, mulStep, winFold_snd tables limb acc t0 w]; rfl

/-- Window `w`'s six bits. -/
def bits (limb : Word) (w : Nat) : Nat := (limb >>> (6 * w) &&& (63 : Word)).toNat

theorem bits_lt (limb : Word) (w : Nat) : bits limb w < 64 := by
  unfold bits
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem index_eq (limb : Word) (t w : Nat) :
    (t <<< 6 ||| (limb >>> (6 * w)).toNat % (1 <<< 6)) = 64 * t + bits limb w := by
  have h : (limb >>> (6 * w)).toNat % (1 <<< 6) = bits limb w := by
    simp only [bits, BitVec.toNat_and]
    rw [show (63 : Word).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rfl
  rw [h, ← Nat.shiftLeft_add_eq_or_of_lt (bits_lt limb w), Nat.shiftLeft_eq]
  ring

/-- The lookup of window `w` at table `t`: the entry's limbs. -/
theorem lookup {u₀ : MachineState} {T : Word} (limb : Word) {t w : Nat}
    (hi : 64 * t + bits limb w < 2112) :
    (tab u₀ T).getD (t <<< 6 ||| (limb >>> (6 * w)).toNat % (1 <<< 6)) lzero =
      (u₀.getMem (T + BitVec.ofNat 64 (24 * (64 * t + bits limb w))),
        u₀.getMem (T + BitVec.ofNat 64 (24 * (64 * t + bits limb w)) + 8),
        u₀.getMem (T + BitVec.ofNat 64 (24 * (64 * t + bits limb w)) + 16)) := by
  rw [index_eq, tab_getD u₀ T hi, limbs_eAt]

theorem shift_eq {w : Nat} (hw : w < 11) : (BitVec.ofNat 64 (6 * w)).toNat % 64 = 6 * w := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 6 * w) (by omega)]
  omega

/-- The entry's address, `T + 24·idx` as compiled. -/
theorem entry_addr {T x : Word} {i : Nat} (hx : x.toNat = i) (hi : i < 2112)
    (hT : T.toNat + 24 * 2112 ≤ heapEnd) :
    T + (x * 16 + x * 8) = T + BitVec.ofNat 64 (24 * i) := by
  addr_omega [hx, hi, hT]

theorem entry_valid {T : Word} (hT : BufP T) {i : Nat} (hi : i < 2112) :
    Sym.validAccess 8 (T + BitVec.ofNat 64 (24 * i) + 16) = true ∧
      Sym.validAccess 8 (T + BitVec.ofNat 64 (24 * i) + 8) = true ∧
      Sym.validAccess 8 (T + BitVec.ofNat 64 (24 * i)) = true := by
  have h1 := hT.lo
  have h2 := hT.hi
  have h3 := hT.align
  simp only [tabBytes] at h2
  refine ⟨?_, ?_, ?_⟩ <;> exact heap_valid' (by addr_omega [h1, h2, hi]) (by addr_omega [h1, h2, hi])
    (by addr_omega [h1, h2, h3, hi])

/-- The product after a lookup, `ladd` with the operands swapped as compiled. -/
theorem acc_step {a b c x y z : Word} :
    (x ^^^ a, y ^^^ b, z ^^^ c) = ladd (a, b, c) (x, y, z) :=
  Prod.ext (BitVec.xor_comm _ _) (Prod.ext (BitVec.xor_comm _ _) (BitVec.xor_comm _ _))

/-! ## The first limb, at `0x8000cd38` -/

def keep1 : List Reg := [.x1, .x2, .x3, .x4, .x8, .x9, .x12, .x14, .x17, .x18, .x19, .x20, .x21,
  .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

structure Inv1 (u₀ u : MachineState) (T : Word) (w : Nat) : Prop where
  pc : u.pc = 0x8000cd38
  lt : w < 11
  mem : ∀ a, u.getMem a = u₀.getMem a
  keep : ∀ r ∈ keep1, u.getReg r = u₀.getReg r
  x15 : u.getReg .x15 = BitVec.ofNat 64 (6 * w)
  x16 : u.getReg .x16 = BitVec.ofNat 64 (64 * w)
  acc : (u.getReg .x13, u.getReg .x11, u.getReg .x10) =
    (winFold (tab u₀ T) (u₀.getReg .x17) (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 0 w).1

theorem win1 {u₀ : MachineState} {T : Word} (hT : BufP T) (h19 : u₀.getReg .x19 = T)
    (h23 : u₀.getReg .x23 = 2112) (h26 : u₀.getReg .x26 = 704) (hpc : u₀.pc = 0x8000cd38)
    (h15 : u₀.getReg .x15 = 0) (h16 : u₀.getReg .x16 = 0) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x8000cd7c ∧ (∀ a, v.getMem a = u₀.getMem a) ∧
      (∀ r ∈ keep1, v.getReg r = u₀.getReg r) ∧
      (v.getReg .x13, v.getReg .x11, v.getReg .x10) = (winFold (tab u₀ T) (u₀.getReg .x17)
        (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 0 11).1 := by
  have hTl := hT.lo
  have hTh := hT.hi
  simp only [tabBytes] at hTh
  refine Reaches.loop (code := Image.code) (fun u ↦ ∃ w, Inv1 u₀ u T w)
    (fun u ↦ 704 - (u.getReg .x16).toNat) _ (fun u ⟨w, hu⟩ ↦ ?_) u₀
    ⟨0, hpc, by decide, fun _ ↦ rfl, fun _ _ ↦ rfl, h15, h16, rfl⟩
  have hw := hu.lt
  have hlimb := hu.keep .x17 (by decide)
  have hbits := bits_lt (u₀.getReg .x17) w
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cd38_spec hu.pc (by rv_eval [])
  have k₁ := b8000cd38_keeps h₁
  have hm₁ := b8000cd38_mem_same h₁
  have hb : (u₀.getReg .x17 >>> (6 * w) &&& (63 : Word)).toNat = bits (u₀.getReg .x17) w := rfl
  have hx5 : v₁.getReg .x5 = BitVec.ofNat 64 (64 * w) + (u₀.getReg .x17 >>> (6 * w) &&& 63) :=
    h₁.reg_eq .x5 rfl (by rv_eval [hu.x15, hu.x16, hlimb, shift_eq hw])
  have hi : (v₁.getReg .x5).toNat = 64 * w + bits (u₀.getReg .x17) w := by
    rw [hx5]; addr_omega [hb, hbits, hw]
  have hpc₁ : v₁.pc = 0x8000cd48 := h₁.pc_eq (by
    rv_eval [hu.x15, hu.x16, hlimb, shift_eq hw, hu.keep .x23 (by decide), h23]
    rw [← hx5]
    simp only [BitVec.ult, hi]
    rw [show (2112 : Word).toNat = 2112 from rfl, decide_eq_true (by omega)]
    rfl)
  have haddr := entry_addr (T := T) hi (by omega) (by omega)
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000cd48_spec hpc₁ (by
    rv_eval [k₁ .x19 (by decide), hu.keep .x19 (by decide), h19, haddr]
    exact entry_valid hT (by omega))
  have k₂ := b8000cd48_keeps h₂
  have hm₂ := b8000cd48_mem_same h₂
  have hreg (r : Reg) (hr : r ∈ keep1) : v.getReg r = u₀.getReg r :=
    (k₂ r hr).trans ((k₁ r (mem_of_mem hr _)).trans (hu.keep r hr))
  have hmem (a : Word) : v.getMem a = u₀.getMem a := (hm₂ a).trans ((hm₁ a).trans (hu.mem a))
  have hacc : (v.getReg .x13, v.getReg .x11, v.getReg .x10) = (winFold (tab u₀ T) (u₀.getReg .x17)
      (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 0 (w + 1)).1 := by
    rw [winFold_succ, mulStep, winFold_snd, Nat.zero_add, lookup _ (by omega), ← hu.acc,
      b8000cd48_x13 h₂, b8000cd48_x11 h₂, b8000cd48_x10 h₂, k₁ .x19 (by decide),
      hu.keep .x19 (by decide), h19, haddr, hm₁, hm₁, hm₁, hu.mem, hu.mem, hu.mem,
      k₁ .x13 (by decide), k₁ .x11 (by decide), k₁ .x10 (by decide)]
    exact acc_step
  have h16 : v₁.getReg .x16 = BitVec.ofNat 64 (64 * w) := (k₁ .x16 (by decide)).trans hu.x16
  have h26' : v₁.getReg .x26 = 704 := (k₁ .x26 (by decide)).trans ((hu.keep .x26 (by decide)).trans h26)
  have hx16 : v.getReg .x16 = BitVec.ofNat 64 (64 * (w + 1)) := by
    rw [b8000cd48_x16 h₂, h16]; addr_omega [hw]
  by_cases hlast : w + 1 = 11
  · refine Or.inl ⟨v, hr₁.trans hr₂, b8000cd48_pc_not_taken h₂ (by rw [h16, h26']; addr_omega [hlast]),
      hmem, hreg, ?_⟩
    rw [hacc, hlast]
  · refine Or.inr ⟨v, hr₁.trans hr₂, ⟨w + 1, {
      pc := b8000cd48_pc_taken h₂ (by rw [h16, h26']; addr_omega [hlast, hw])
      lt := by omega
      mem := hmem
      keep := hreg
      x15 := by
        rw [b8000cd48_x15 h₂, k₁ .x15 (by decide), hu.x15]; addr_omega [hw]
      x16 := hx16
      acc := hacc }⟩, ?_⟩
    rw [hx16, hu.x16]
    addr_omega [hw, hlast]

/-! ## The second limb, at `0x8000cd84` -/

def keep2 : List Reg := [.x1, .x2, .x3, .x4, .x7, .x8, .x9, .x12, .x14, .x18, .x19, .x20, .x21,
  .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

structure Inv2 (u₀ u : MachineState) (T : Word) (w : Nat) : Prop where
  pc : u.pc = 0x8000cd84
  lt : w < 11
  mem : ∀ a, u.getMem a = u₀.getMem a
  keep : ∀ r ∈ keep2, u.getReg r = u₀.getReg r
  x15 : u.getReg .x15 = BitVec.ofNat 64 (6 * w)
  x16 : u.getReg .x16 = BitVec.ofNat 64 (64 * (11 + w))
  acc : (u.getReg .x13, u.getReg .x11, u.getReg .x10) =
    (winFold (tab u₀ T) (u₀.getReg .x14) (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 11 w).1

theorem win2 {u₀ : MachineState} {T : Word} (hT : BufP T) (h19 : u₀.getReg .x19 = T)
    (h23 : u₀.getReg .x23 = 2112) (hend : u₀.getReg .x27 = 1408) (hpc : u₀.pc = 0x8000cd84)
    (h15 : u₀.getReg .x15 = 0) (h16 : u₀.getReg .x16 = 704) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x8000cdc8 ∧ (∀ a, v.getMem a = u₀.getMem a) ∧
      (∀ r ∈ keep2, v.getReg r = u₀.getReg r) ∧
      (v.getReg .x13, v.getReg .x11, v.getReg .x10) = (winFold (tab u₀ T) (u₀.getReg .x14)
        (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 11 11).1 := by
  have hTl := hT.lo
  have hTh := hT.hi
  simp only [tabBytes] at hTh
  refine Reaches.loop (code := Image.code) (fun u ↦ ∃ w, Inv2 u₀ u T w)
    (fun u ↦ 1408 - (u.getReg .x16).toNat) _ (fun u ⟨w, hu⟩ ↦ ?_) u₀
    ⟨0, hpc, by decide, fun _ ↦ rfl, fun _ _ ↦ rfl, h15, h16.trans (by decide), rfl⟩
  have hw := hu.lt
  have hlimb := hu.keep .x14 (by decide)
  have hbits := bits_lt (u₀.getReg .x14) w
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cd84_spec hu.pc (by rv_eval [])
  have k₁ := b8000cd84_keeps h₁
  have hm₁ := b8000cd84_mem_same h₁
  have hb : (u₀.getReg .x14 >>> (6 * w) &&& (63 : Word)).toNat = bits (u₀.getReg .x14) w := rfl
  have hx5 : v₁.getReg .x17 = BitVec.ofNat 64 (64 * (11 + w)) + (u₀.getReg .x14 >>> (6 * w) &&& 63) :=
    h₁.reg_eq .x17 rfl (by rv_eval [hu.x15, hu.x16, hlimb, shift_eq hw])
  have hi : (v₁.getReg .x17).toNat = 64 * (11 + w) + bits (u₀.getReg .x14) w := by
    rw [hx5]; addr_omega [hb, hbits, hw]
  have hpc₁ : v₁.pc = 0x8000cd94 := h₁.pc_eq (by
    rv_eval [hu.x15, hu.x16, hlimb, shift_eq hw, hu.keep .x23 (by decide), h23]
    rw [← hx5]
    simp only [BitVec.ult, hi]
    rw [show (2112 : Word).toNat = 2112 from rfl, decide_eq_true (by omega)]
    rfl)
  have haddr := entry_addr (T := T) hi (by omega) (by omega)
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000cd94_spec hpc₁ (by
    rv_eval [k₁ .x19 (by decide), hu.keep .x19 (by decide), h19, haddr]
    exact entry_valid hT (by omega))
  have k₂ := b8000cd94_keeps h₂
  have hm₂ := b8000cd94_mem_same h₂
  have hreg (r : Reg) (hr : r ∈ keep2) : v.getReg r = u₀.getReg r :=
    (k₂ r hr).trans ((k₁ r (mem_of_mem hr _)).trans (hu.keep r hr))
  have hmem (a : Word) : v.getMem a = u₀.getMem a := (hm₂ a).trans ((hm₁ a).trans (hu.mem a))
  have hacc : (v.getReg .x13, v.getReg .x11, v.getReg .x10) = (winFold (tab u₀ T) (u₀.getReg .x14)
      (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 11 (w + 1)).1 := by
    rw [winFold_succ, mulStep, winFold_snd, lookup _ (by omega), ← hu.acc,
      b8000cd94_x13 h₂, b8000cd94_x11 h₂, b8000cd94_x10 h₂, k₁ .x19 (by decide),
      hu.keep .x19 (by decide), h19, haddr, hm₁, hm₁, hm₁, hu.mem, hu.mem, hu.mem,
      k₁ .x13 (by decide), k₁ .x11 (by decide), k₁ .x10 (by decide)]
    exact acc_step
  have h16 : v₁.getReg .x16 = BitVec.ofNat 64 (64 * (11 + w)) := (k₁ .x16 (by decide)).trans hu.x16
  have hend' : v₁.getReg .x27 = 1408 := (k₁ .x27 (by decide)).trans ((hu.keep .x27 (by decide)).trans hend)
  have hx16 : v.getReg .x16 = BitVec.ofNat 64 (64 * (11 + (w + 1))) := by
    rw [b8000cd94_x16 h₂, h16]; addr_omega [hw]
  by_cases hlast : w + 1 = 11
  · refine Or.inl ⟨v, hr₁.trans hr₂, b8000cd94_pc_not_taken h₂ (by rw [h16, hend']; addr_omega [hlast]),
      hmem, hreg, ?_⟩
    rw [hacc, hlast]
  · refine Or.inr ⟨v, hr₁.trans hr₂, ⟨w + 1, {
      pc := b8000cd94_pc_taken h₂ (by rw [h16, hend']; addr_omega [hlast, hw])
      lt := by omega
      mem := hmem
      keep := hreg
      x15 := by
        rw [b8000cd94_x15 h₂, k₁ .x15 (by decide), hu.x15]; addr_omega [hw]
      x16 := hx16
      acc := hacc }⟩, ?_⟩
    rw [hx16, hu.x16]
    addr_omega [hw, hlast]

/-! ## The third limb, at `0x8000cdd0` -/

def keep3 : List Reg := [.x1, .x2, .x3, .x4, .x6, .x7, .x8, .x9, .x12, .x18, .x19, .x20, .x21,
  .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

structure Inv3 (u₀ u : MachineState) (T : Word) (w : Nat) : Prop where
  pc : u.pc = 0x8000cdd0
  lt : w < 11
  mem : ∀ a, u.getMem a = u₀.getMem a
  keep : ∀ r ∈ keep3, u.getReg r = u₀.getReg r
  x14 : u.getReg .x14 = BitVec.ofNat 64 (6 * w)
  x15 : u.getReg .x15 = BitVec.ofNat 64 (64 * (22 + w))
  acc : (u.getReg .x13, u.getReg .x11, u.getReg .x10) =
    (winFold (tab u₀ T) (u₀.getReg .x12) (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 22 w).1

theorem win3 {u₀ : MachineState} {T : Word} (hT : BufP T) (h19 : u₀.getReg .x19 = T)
    (h23 : u₀.getReg .x23 = 2112) (hend : u₀.getReg .x24 = 2112) (hpc : u₀.pc = 0x8000cdd0)
    (h15 : u₀.getReg .x14 = 0) (h16 : u₀.getReg .x15 = 1408) :
    ∃ v, Reaches Image.code u₀ v ∧ v.pc = 0x8000ce14 ∧ (∀ a, v.getMem a = u₀.getMem a) ∧
      (∀ r ∈ keep3, v.getReg r = u₀.getReg r) ∧
      (v.getReg .x13, v.getReg .x11, v.getReg .x10) = (winFold (tab u₀ T) (u₀.getReg .x12)
        (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 22 11).1 := by
  have hTl := hT.lo
  have hTh := hT.hi
  simp only [tabBytes] at hTh
  refine Reaches.loop (code := Image.code) (fun u ↦ ∃ w, Inv3 u₀ u T w)
    (fun u ↦ 2112 - (u.getReg .x15).toNat) _ (fun u ⟨w, hu⟩ ↦ ?_) u₀
    ⟨0, hpc, by decide, fun _ ↦ rfl, fun _ _ ↦ rfl, h15, h16.trans (by decide), rfl⟩
  have hw := hu.lt
  have hlimb := hu.keep .x12 (by decide)
  have hbits := bits_lt (u₀.getReg .x12) w
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000cdd0_spec hu.pc (by rv_eval [])
  have k₁ := b8000cdd0_keeps h₁
  have hm₁ := b8000cdd0_mem_same h₁
  have hb : (u₀.getReg .x12 >>> (6 * w) &&& (63 : Word)).toNat = bits (u₀.getReg .x12) w := rfl
  have hx5 : v₁.getReg .x16 = BitVec.ofNat 64 (64 * (22 + w)) + (u₀.getReg .x12 >>> (6 * w) &&& 63) :=
    h₁.reg_eq .x16 rfl (by rv_eval [hu.x14, hu.x15, hlimb, shift_eq hw])
  have hi : (v₁.getReg .x16).toNat = 64 * (22 + w) + bits (u₀.getReg .x12) w := by
    rw [hx5]; addr_omega [hb, hbits, hw]
  have hpc₁ : v₁.pc = 0x8000cde0 := h₁.pc_eq (by
    rv_eval [hu.x14, hu.x15, hlimb, shift_eq hw, hu.keep .x23 (by decide), h23]
    rw [← hx5]
    simp only [BitVec.ult, hi]
    rw [show (2112 : Word).toNat = 2112 from rfl, decide_eq_true (by omega)]
    rfl)
  have haddr := entry_addr (T := T) hi (by omega) (by omega)
  obtain ⟨v, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000cde0_spec hpc₁ (by
    rv_eval [k₁ .x19 (by decide), hu.keep .x19 (by decide), h19, haddr]
    exact entry_valid hT (by omega))
  have k₂ := b8000cde0_keeps h₂
  have hm₂ := b8000cde0_mem_same h₂
  have hreg (r : Reg) (hr : r ∈ keep3) : v.getReg r = u₀.getReg r :=
    (k₂ r hr).trans ((k₁ r (mem_of_mem hr _)).trans (hu.keep r hr))
  have hmem (a : Word) : v.getMem a = u₀.getMem a := (hm₂ a).trans ((hm₁ a).trans (hu.mem a))
  have hacc : (v.getReg .x13, v.getReg .x11, v.getReg .x10) = (winFold (tab u₀ T) (u₀.getReg .x12)
      (u₀.getReg .x13, u₀.getReg .x11, u₀.getReg .x10) 22 (w + 1)).1 := by
    rw [winFold_succ, mulStep, winFold_snd, lookup _ (by omega), ← hu.acc,
      b8000cde0_x13 h₂, b8000cde0_x11 h₂, b8000cde0_x10 h₂, k₁ .x19 (by decide),
      hu.keep .x19 (by decide), h19, haddr, hm₁, hm₁, hm₁, hu.mem, hu.mem, hu.mem,
      k₁ .x13 (by decide), k₁ .x11 (by decide), k₁ .x10 (by decide)]
    exact acc_step
  have h16 : v₁.getReg .x15 = BitVec.ofNat 64 (64 * (22 + w)) := (k₁ .x15 (by decide)).trans hu.x15
  have hend' : v₁.getReg .x24 = 2112 := (k₁ .x24 (by decide)).trans ((hu.keep .x24 (by decide)).trans hend)
  have hx16 : v.getReg .x15 = BitVec.ofNat 64 (64 * (22 + (w + 1))) := by
    rw [b8000cde0_x15 h₂, h16]; addr_omega [hw]
  by_cases hlast : w + 1 = 11
  · refine Or.inl ⟨v, hr₁.trans hr₂, b8000cde0_pc_not_taken h₂ (by rw [h16, hend']; addr_omega [hlast]),
      hmem, hreg, ?_⟩
    rw [hacc, hlast]
  · refine Or.inr ⟨v, hr₁.trans hr₂, ⟨w + 1, {
      pc := b8000cde0_pc_taken h₂ (by rw [h16, hend']; addr_omega [hlast, hw])
      lt := by omega
      mem := hmem
      keep := hreg
      x14 := by
        rw [b8000cde0_x14 h₂, k₁ .x14 (by decide), hu.x14]; addr_omega [hw]
      x15 := hx16
      acc := hacc }⟩, ?_⟩
    rw [hx16, hu.x15]
    addr_omega [hw, hlast]

/-! ## The product, from `0x8000cd18` to `0x8000ccb0` -/

theorem scaledMul_win (tables : List Limbs) (a : Limbs) : scaledMul tables a =
    (winFold tables a.2.2 (winFold tables a.2.1 (winFold tables a.1 lzero 0 11).1 11 11).1 22 11).1 := by
  have e (limb : Word) (st : Limbs × Nat) :
      (List.range 11).foldl (mulStep tables limb) st = winFold tables limb st.1 st.2 11 := rfl
  simp only [scaledMul, List.foldl_cons, List.foldl_nil, e, winFold_snd]

theorem tab_same {u v : MachineState} (h : ∀ a, v.getMem a = u.getMem a) (T : Word) :
    tab v T = tab u T := by
  simp only [tab, eAt, h]

def tmKeep : List Reg := [.x1, .x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
  .x26, .x27]

/-- `Scaled::mul(out[j])` by the table at `T` (`s3`), the product at `sp + 48`. -/
theorem table_mul {u : MachineState} {T : Word} (hT : BufP T) (hpc : u.pc = 0x8000cd18)
    (h19 : u.getReg .x19 = T) (h23 : u.getReg .x23 = 2112) (h24 : u.getReg .x24 = 2112)
    (h26 : u.getReg .x26 = 704) (h27 : u.getReg .x27 = 1408)
    (hv : Sym.validAccess 8 (u.getReg .x18 + 16) = true ∧ Sym.validAccess 8 (u.getReg .x18 + 8) = true ∧
      Sym.validAccess 8 (u.getReg .x18) = true)
    (hs : Sym.validAccess 8 (u.getReg .x2 + 64) = true ∧ Sym.validAccess 8 (u.getReg .x2 + 56) = true ∧
      Sym.validAccess 8 (u.getReg .x2 + 48) = true)
    (hsp : (u.getReg .x2).toNat + 72 ≤ 2 ^ 64) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x8000ccb0 ∧ (∀ r ∈ tmKeep, v.getReg r = u.getReg r) ∧
      MemFrame u v (u.getReg .x2 + 48) 24 ∧
      (v.getMem (u.getReg .x2 + 48), v.getMem (u.getReg .x2 + 56), v.getMem (u.getReg .x2 + 64)) =
        scaledMul (tab u T) (limbs (eAt u (u.getReg .x18))) := by
  obtain ⟨w₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000cd18_spec hpc (by rv_eval []; exact hv)
  have k₀ := b8000cd18_keeps h₀
  have hm₀ := b8000cd18_mem_same h₀
  obtain ⟨w₁, hr₁, pc₁, hm₁, k₁, acc₁⟩ := win1 hT ((k₀ .x19 (by decide)).trans h19)
    ((k₀ .x23 (by decide)).trans h23) ((k₀ .x26 (by decide)).trans h26) (b8000cd18_pc h₀)
    (b8000cd18_x15 h₀) (b8000cd18_x16 h₀)
  obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000cd7c_spec pc₁ (by rv_eval [])
  have k₂ := b8000cd7c_keeps h₂
  have hm₂ := b8000cd7c_mem_same h₂
  have g (r : Reg) (hr : r ∈ tmKeep) : w₂.getReg r = u.getReg r :=
    (k₂ r (mem_of_mem hr _)).trans ((k₁ r (mem_of_mem hr _)).trans (k₀ r (mem_of_mem hr _)))
  obtain ⟨w₃, hr₃, pc₃, hm₃, k₃, acc₂⟩ := win2 hT ((g .x19 (by decide)).trans h19)
    ((g .x23 (by decide)).trans h23) ((g .x27 (by decide)).trans h27)
    (b8000cd7c_pc h₂) (b8000cd7c_x15 h₂) (b8000cd7c_x16 h₂)
  obtain ⟨w₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000cdc8_spec pc₃ (by rv_eval [])
  have k₄ := b8000cdc8_keeps h₄
  have hm₄ := b8000cdc8_mem_same h₄
  have g' (r : Reg) (hr : r ∈ tmKeep) : w₄.getReg r = u.getReg r :=
    (k₄ r (mem_of_mem hr _)).trans ((k₃ r (mem_of_mem hr _)).trans (g r hr))
  obtain ⟨w₅, hr₅, pc₅, hm₅, k₅, acc₃⟩ := win3 hT ((g' .x19 (by decide)).trans h19)
    ((g' .x23 (by decide)).trans h23) ((g' .x24 (by decide)).trans h24)
    (b8000cdc8_pc h₄) (b8000cdc8_x14 h₄) (b8000cdc8_x15 h₄)
  have hsp₅ : w₅.getReg .x2 = u.getReg .x2 := (k₅ .x2 (by decide)).trans (g' .x2 (by decide))
  obtain ⟨v, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000ce14_spec pc₅ (by rv_eval [hsp₅]; exact hs)
  have k₆ := b8000ce14_keeps h₆
  have hmem₅ (a : Word) : w₅.getMem a = u.getMem a :=
    (hm₅ a).trans ((hm₄ a).trans ((hm₃ a).trans ((hm₂ a).trans ((hm₁ a).trans (hm₀ a)))))
  refine ⟨v, hr₀.trans (hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆))))),
    b8000ce14_pc h₆, fun r hr ↦ (k₆ r (mem_of_mem hr _)).trans
      ((k₅ r (mem_of_mem hr _)).trans (g' r hr)),
    fun a ha ↦ ((b8000ce14_frame h₆ (by rw [hsp₅]; exact hsp)) a (by rw [hsp₅]; exact ha)).trans
      (hmem₅ a), ?_⟩
  have m48 := b8000ce14_m_x2_48 h₆
  have m56 := b8000ce14_m_x2_56 h₆
  have m64 := b8000ce14_m_x2_64 h₆
  rw [hsp₅] at m48 m56 m64
  have e12 : w₄.getReg .x12 = u.getMem (u.getReg .x18 + 16) := by
    rw [k₄ .x12 (by decide), k₃ .x12 (by decide), k₂ .x12 (by decide), k₁ .x12 (by decide),
      b8000cd18_x12 h₀]
  have e14 : w₂.getReg .x14 = u.getMem (u.getReg .x18 + 8) := by
    rw [k₂ .x14 (by decide), k₁ .x14 (by decide), b8000cd18_x14 h₀]
  have e0 : (w₀.getReg .x13, w₀.getReg .x11, w₀.getReg .x10) = lzero := by
    rw [b8000cd18_x13 h₀, b8000cd18_x11 h₀, b8000cd18_x10 h₀]; rfl
  rw [m48, m56, m64, acc₃, scaledMul_win, limbs_eAt, e12, k₄ .x13 (by decide), k₄ .x11 (by decide),
    k₄ .x10 (by decide), acc₂, e14, k₂ .x13 (by decide), k₂ .x11 (by decide), k₂ .x10 (by decide),
    acc₁, b8000cd18_x17 h₀, e0, tab_same (fun a ↦ (hm₄ a).trans ((hm₃ a).trans ((hm₂ a).trans
      ((hm₁ a).trans (hm₀ a))))), tab_same (fun a ↦ (hm₂ a).trans ((hm₁ a).trans (hm₀ a))),
    tab_same hm₀]


end Rv64Verifier.Proofs.Multilinear.EqKernelWin
