import Rv64Verifier.Proofs.Gkr.LayerJ11
import Rv64Verifier.Proofs.Gkr.LayerSample
import Rv64Verifier.Proofs.Hash.Arith

/-!
# `keccak::verify_layer`: `beta` and the lane weights

`keccak.rs:183-190`, inlined at `0x8000fb34..0x8000fcbc`: the sponge duplexed and `beta` read
into `f + 936`, then per lane `lane_weights[lane] = eq_lane[lane] + beta * (eq_lane[i1] +
beta * eq_lane[i2])` into `f + 960`, the two neighbours' indices by a `mulhu` division by five
(`idx`), and the 25 weights copied to `f + 264`.
-/

namespace Rv64Verifier.Gkr.Layer
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Model.Gkr Rv64Verifier.Transcript Rv64Verifier.Contracts
  Rv64Verifier.Gkr Rv64Verifier.Blocks.F74
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-! ## The neighbours' indices -/

/-- `eq_lane`'s indices of the lane's θ neighbours, `x + 4` and `x + 3` in its row. -/
def i1 (L : Nat) : Nat := 5 * (L / 5) + (L % 5 + 4) % 5
def i2 (L : Nat) : Nat := 5 * (L / 5) + (L % 5 + 3) % 5

theorem mulhu5 {L : Nat} (hL : L < 2 ^ 32) :
    rv64_mulhu (BitVec.ofNat 64 L) 0x3333333333333334 = BitVec.ofNat 64 (L / 5) := by
  apply BitVec.eq_of_toNat_eq
  rw [Hash.toNat_mulhu, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]
  show L * 3689348814741910324 / 2 ^ 64 = L / 5
  omega

theorem and255 {L : Nat} (hL : L < 256) : BitVec.ofNat 64 L &&& 255 = BitVec.ofNat 64 L := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (255 : Word).toNat = 255 from rfl,
    Nat.mod_eq_of_lt (by omega)]
  exact Nat.and_two_pow_sub_one_of_lt_two_pow (n := 8) hL

theorem i1_eq (L : Nat) :
    BitVec.ofNat 64 ((L % 5 + 4) % 5) + (BitVec.ofNat 64 L + (BitVec.ofNat 64 (L / 5) * 4 +
      (BitVec.ofNat 64 (L / 5) - BitVec.ofNat 64 L))) = BitVec.ofNat 64 (i1 L) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (4 : Word).toNat = 4 from rfl, i1]
  omega

theorem i2_lo {L : Nat} (hL : L < 25) (h : L % 5 < 2) :
    3 + BitVec.ofNat 64 L = BitVec.ofNat 64 (i2 L) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (3 : Word).toNat = 3 from rfl, i2]
  omega

theorem i2_hi {L : Nat} (hL : L < 25) (h : 2 ≤ L % 5) :
    0xfffffffffffffffe + BitVec.ofNat 64 L = BitVec.ofNat 64 (i2 L) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    show (0xfffffffffffffffe : Word).toNat = 0xfffffffffffffffe from rfl, i2]
  omega

theorem ult_ofNat {n : Nat} (hn : n < 2 ^ 64) (y : Word) :
    (BitVec.ofNat 64 n).ult y = decide (n < y.toNat) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

set_option maxHeartbeats 4000000 in
/-- `0x8000fb7c..0x8000fbd8`: `i1` into `a0`, `i2` into `a1`, each checked against `eq_lane`'s
length. -/
theorem idx {w : MachineState} {L : Nat} (hL : L < 25) (hpc : w.pc = 0x8000fb7c)
    (h19 : w.getReg .x19 = BitVec.ofNat 64 L) (h8 : w.getReg .x8 = BitVec.ofNat 64 L)
    (h15 : w.getReg .x15 = 0x3333333333333334) :
    ∃ t, Reaches Image.code w t ∧ (∀ a, t.getMem a = w.getMem a) ∧
      (∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18, .x19, .x20,
        .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31], t.getReg r = w.getReg r) ∧
      ((t.pc = 0x8000fbd8 ∧ t.getReg .x10 = BitVec.ofNat 64 (i1 L) ∧
        t.getReg .x11 = BitVec.ofNat 64 (i2 L) ∧ i1 L < (w.getReg .x18).toNat ∧
        i2 L < (w.getReg .x18).toNat) ∨ Dead Image.code t) := by
  have hq : rv64_mulhu (BitVec.ofNat 64 L) 0x3333333333333334 = BitVec.ofNat 64 (L / 5) :=
    mulhu5 (by omega)
  have hm : BitVec.ofNat 64 L - BitVec.ofNat 64 (L / 5) - BitVec.ofNat 64 (L / 5) * 4 =
      BitVec.ofNat 64 (L % 5) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat,
      show (4 : Word).toNat = 4 from rfl]
    omega
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fb7c_spec hpc trivial
  have k₁ := b8000fb7c_keeps h₁
  have hm₁ := b8000fb7c_mem_same h₁
  have x11₁ : t₁.getReg .x11 = BitVec.ofNat 64 (L % 5) :=
    h₁.reg_eq .x11 rfl (by rv_eval [h19, h15, hq]; exact hm)
  have pc₁ := h₁.pc
  rv_eval [h19, h15, hq, hm] at pc₁
  have hst : ∃ t₂, Reaches Image.code w t₂ ∧ t₂.pc = 0x8000fb9c ∧ (∀ a, t₂.getMem a = w.getMem a) ∧
      (∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x11, .x12, .x13, .x14, .x15, .x16,
        .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31],
        t₂.getReg r = t₁.getReg r) ∧ t₂.getReg .x10 = BitVec.ofNat 64 ((L % 5 + 4) % 5) := by
    by_cases h0 : L % 5 = 0
    · rw [h0, show (BitVec.ofNat 64 0 != (0 : Word)) = false from rfl] at pc₁
      simp only [Bool.false_eq_true, ↓reduceIte] at pc₁
      obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fb90_spec pc₁ trivial
      refine ⟨t₂, hr₁.trans hr₂, b8000fb90_pc h₂, fun a ↦ by rw [b8000fb90_mem_same h₂, hm₁],
        fun r hr ↦ b8000fb90_keeps h₂ r (mem_of_mem hr _), ?_⟩
      rw [b8000fb90_x10 h₂, h0]; rfl
    · rw [ite_bne_of_ne (by
        intro he; apply h0; have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl] at this; omega)] at pc₁
      obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fb98_spec pc₁ trivial
      refine ⟨t₂, hr₁.trans hr₂, b8000fb98_pc h₂, fun a ↦ by rw [b8000fb98_mem_same h₂, hm₁],
        fun r hr ↦ b8000fb98_keeps h₂ r (mem_of_mem hr _), ?_⟩
      rw [b8000fb98_x10 h₂, x11₁]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : Word).toNat = 1 from rfl]
      omega
  obtain ⟨t₂, hr₂, pc₂, hm₂, k₂, x10₂⟩ := hst
  have r₂ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18,
      .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]) :
      t₂.getReg r = w.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x11₂ : t₂.getReg .x11 = BitVec.ofNat 64 (L % 5) := by rw [k₂ .x11 (by decide), x11₁]
  have hq' : rv64_mulhu (BitVec.ofNat 64 L &&& 255) 0x3333333333333334 = BitVec.ofNat 64 (L / 5) := by
    rw [and255 (by omega), hq]
  -- `0x8000fb9c`: `i1`, checked
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fb9c_spec pc₂ trivial
  have k₃ := b8000fb9c_keeps h₃
  have hm₃ := b8000fb9c_mem_same h₃
  have x10₃ : t₃.getReg .x10 = BitVec.ofNat 64 (i1 L) :=
    h₃.reg_eq .x10 rfl (by
      rv_eval [x10₂, r₂ .x19 (by decide), r₂ .x8 (by decide), r₂ .x15 (by decide), h19, h8, h15, hq',
        and255 (by omega : L < 256), hq, i1_eq])
  have pc₃ := h₃.pc
  rv_eval [x10₂, r₂ .x19 (by decide), r₂ .x8 (by decide), r₂ .x15 (by decide), r₂ .x18 (by decide),
    h19, h8, h15, hq', and255 (by omega : L < 256), hq, i1_eq, ult_ofNat (n := i1 L) (by unfold i1; omega)] at pc₃
  have r₃ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18,
      .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]) :
      t₃.getReg r = w.getReg r := by
    rw [k₃ r (mem_of_mem hr _), r₂ r hr]
  have hm3 (a : Word) : t₃.getMem a = w.getMem a := by rw [hm₃, hm₂]
  by_cases hlt1 : i1 L < (w.getReg .x18).toNat
  swap
  · simp only [hlt1, decide_false, Bool.not_false, ↓reduceIte] at pc₃
    exact ⟨t₃, hr₂.trans hr₃, hm3, r₃, Or.inr (dead_of_fetch (by rw [pc₃]; exact trap))⟩
  simp only [hlt1, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at pc₃
  have x11₃ : t₃.getReg .x11 = BitVec.ofNat 64 (L % 5) := by rw [k₃ .x11 (by decide), x11₂]
  -- `0x8000fbbc`: `i2`, checked
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000fbbc_spec pc₃ trivial
  have hst : ∃ t₅, Reaches Image.code t₄ t₅ ∧ t₅.pc = 0x8000fbd0 ∧ (∀ a, t₅.getMem a = w.getMem a) ∧
      (∀ r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x15, .x16, .x17, .x18,
        .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31],
        t₅.getReg r = t₃.getReg r) ∧ t₅.getReg .x11 + t₅.getReg .x19 = BitVec.ofNat 64 (i2 L) := by
    have k₄ := b8000fbbc_keeps h₄
    have hm₄ := b8000fbbc_mem_same h₄
    by_cases hx : L % 5 < 2
    · obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000fbcc_spec (b8000fbbc_pc_taken h₄ (by
        rw [x11₃, BitVec.toNat_ofNat, show (2 : Word).toNat = 2 from rfl]; omega)) trivial
      have k₅ := b8000fbcc_keeps h₅
      refine ⟨t₅, hr₅, b8000fbcc_pc h₅, fun a ↦ by rw [b8000fbcc_mem_same h₅, hm₄, hm3],
        fun r hr ↦ by rw [k₅ r (mem_of_mem hr _), k₄ r (mem_of_mem hr _)], ?_⟩
      rw [b8000fbcc_x11 h₅, k₅ .x19 (by decide), k₄ .x19 (by decide), r₃ .x19 (by decide), h19,
        i2_lo hL hx]
    · obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000fbc4_spec (b8000fbbc_pc_not_taken h₄ (by
        rw [x11₃, BitVec.toNat_ofNat, show (2 : Word).toNat = 2 from rfl]; omega)) trivial
      have k₅ := b8000fbc4_keeps h₅
      refine ⟨t₅, hr₅, b8000fbc4_pc h₅, fun a ↦ by rw [b8000fbc4_mem_same h₅, hm₄, hm3],
        fun r hr ↦ by rw [k₅ r (mem_of_mem hr _), k₄ r (mem_of_mem hr _)], ?_⟩
      rw [b8000fbc4_x11 h₅, k₅ .x19 (by decide), k₄ .x19 (by decide), r₃ .x19 (by decide), h19,
        i2_hi hL (by omega)]
  obtain ⟨t₅, hr₅, pc₅, hm5, k₅, e₅⟩ := hst
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000fbd0_spec pc₅ trivial
  have k₆ := b8000fbd0_keeps h₆
  have r₆ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17, .x18,
      .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]) :
      t₆.getReg r = w.getReg r := by
    rw [k₆ r (mem_of_mem hr _), k₅ r (mem_of_mem hr _), r₃ r hr]
  have hm6 (a : Word) : t₆.getMem a = w.getMem a := by rw [b8000fbd0_mem_same h₆, hm5]
  have x18₅ : t₅.getReg .x18 = w.getReg .x18 := by rw [k₅ .x18 (by decide), r₃ .x18 (by decide)]
  have hr06 := hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans hr₆)))
  by_cases hlt2 : i2 L < (w.getReg .x18).toNat
  swap
  · refine ⟨t₆, hr06, hm6, r₆, Or.inr (dead_of_fetch ?_)⟩
    rw [b8000fbd0_pc_taken h₆ (by rw [e₅, x18₅, BitVec.toNat_ofNat]; unfold i2 at hlt2 ⊢; omega)]
    exact trap
  refine ⟨t₆, hr06, hm6, r₆, Or.inl ⟨b8000fbd0_pc_not_taken h₆ (by
    rw [e₅, x18₅, BitVec.toNat_ofNat]; unfold i2 at hlt2 ⊢; omega), ?_, ?_, hlt1, hlt2⟩⟩
  · rw [k₆ .x10 (by decide), k₅ .x10 (by decide), x10₃]
  · rw [b8000fbd0_x11 h₆, e₅]

/-! ## The lane loop -/

/-- The lane weight as the code computes it. -/
def laneW (eL : List E) (beta : E) (L : Nat) : E :=
  beta * (beta * eL.getD (i2 L) 0 + eL.getD (i1 L) 0) + eL.getD L 0

/-- What the lane loop writes: `mul`'s result and stack, `f + 1584`, the lane weights. -/
@[rv_addr] def LnW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1448) 24 ∨ Within a (s.getReg .x2 - 128) 24 ∨
    Within a (s.getReg .x2 - 2736) 1024 ∨ Within a (s.getReg .x2 - 752) 600

/-- What the lane loop reads, at its start `w₀`. -/
structure LC (s w₀ : MachineState) (eLp eLn : Word) (beta : E) (eL : List E) : Prop where
  p112 : w₀.getMem (s.getReg .x2 - 1600) = eLp
  p88 : w₀.getMem (s.getReg .x2 - 1624) = eLn
  beta : eAt w₀ (s.getReg .x2 - 776) = beta
  buf : NewBuf s w₀ eLp (24 * eLn.toNat) 8
  elems : eListAt w₀ eLp eLn.toNat = eL

/-- The lane loop at its head `0x8000fb78`, `L` lanes done. -/
structure LN (s w₀ w : MachineState) (eLp eLn : Word) (beta : E) (eL : List E) (L : Nat) :
    Prop where
  base : Base s w
  frame : DFrame w₀ w (LnW s)
  x8 : w.getReg .x8 = BitVec.ofNat 64 L
  x19 : w.getReg .x19 = BitVec.ofNat 64 L
  x15 : w.getReg .x15 = 0x3333333333333334
  x18 : w.getReg .x18 = eLn
  x20 : w.getReg .x20 = eLp + BitVec.ofNat 64 (24 * L) + 16
  x25 : w.getReg .x25 = s.getReg .x2 - 736 + BitVec.ofNat 64 (24 * L)
  x26 : w.getReg .x26 = w₀.getReg .x26
  lw : ∀ i < L, eAt w (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = laneW eL beta i
  le : L ≤ eLn.toNat
  lt : L < 25

/-- The lane loop done, at `0x8000fca4`. -/
structure LX (s w₀ w : MachineState) (beta : E) (eL : List E) : Prop where
  base : Base s w
  frame : DFrame w₀ w (LnW s)
  x26 : w.getReg .x26 = w₀.getReg .x26
  x27 : w.getReg .x27 = 0x3333333333333334
  lw : ∀ i < 25, eAt w (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = laneW eL beta i

theorem mul24n (n : Nat) :
    BitVec.ofNat 64 n * 16 + BitVec.ofNat 64 n * 8 = BitVec.ofNat 64 (24 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (16 : Word).toNat = 16 from rfl, show (8 : Word).toNat = 8 from rfl]
  omega

theorem sh16 (b : Word) (k : Nat) : b - 736 + BitVec.ofNat 64 k - 16 = b - 752 + BitVec.ofNat 64 k := by
  bv_omega

theorem sh8 (b : Word) (k : Nat) :
    b - 736 + BitVec.ofNat 64 k - 8 = b - 752 + BitVec.ofNat 64 k + 8 := by
  bv_omega

theorem sh0 (b : Word) (k : Nat) :
    b - 736 + BitVec.ofNat 64 k = b - 752 + BitVec.ofNat 64 k + 16 := by
  bv_omega

theorem st24 (b : Word) (k : Nat) :
    b + BitVec.ofNat 64 (24 * k) + 24 = b + BitVec.ofNat 64 (24 * (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (24 : Word).toNat = 24 from rfl]
  omega

theorem st24' (b : Word) (k : Nat) :
    b + BitVec.ofNat 64 (24 * k) + 16 + 24 = b + BitVec.ofNat 64 (24 * (k + 1)) + 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (24 : Word).toNat = 24 from rfl,
    show (16 : Word).toNat = 16 from rfl]
  omega

set_option maxHeartbeats 16000000 in
theorem lane_step (hM : MulSpec) {s w₀ w : MachineState} {eLp eLn : Word} {beta : E}
    {eL : List E} {L : Nat} (hpre : VerifyLayerPre s) (C : LC s w₀ eLp eLn beta eL)
    (Q : LN s w₀ w eLp eLn beta eL L) (hpc : w.pc = 0x8000fb78) :
    ∃ v, Reaches Image.code w v ∧ ((LN s w₀ v eLp eLn beta eL (L + 1) ∧ v.pc = 0x8000fb78) ∨
      (LX s w₀ v beta eL ∧ v.pc = 0x8000fca4) ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := Q.base
  have hL := Q.lt
  have hnx := hpre.stack.next
  have hA := hpre.stack.above
  have hH0 := hpre.heap.lo
  have hHw := B.heap.hi
  have hbuf := C.buf
  simp only [stackLo] at hA hnx
  unfold verifyLayerStack at hb hnx hA
  simp only [NewBuf] at hbuf
  have lnw (a : Word) (h : LnW s a) : (s.getReg .x2).toNat - 2736 ≤ a.toNat ∧
      a.toNat < (s.getReg .x2).toNat - 104 := by
    simp only [LnW] at h; rcases h with h | h | h | h <;> addr_omega [h, hb]
  have hN : w.getMem nextAddr = w₀.getMem nextAddr := Q.frame _ fun i hi hw ↦ by
    have := lnw _ hw; addr_omega [this, hi, hb, hnx]
  have hNw : heapNext w₀ ≤ heapEnd := by simp only [heapNext, ← hN]; exact hHw
  -- `0x8000fb78`: the lane against `eq_lane`'s length
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000fb78_spec hpc trivial
  by_cases he : eLn = BitVec.ofNat 64 L
  · exact ⟨t₁, hr₁, Or.inr (Or.inr (dead_of_fetch (by
      rw [b8000fb78_pc_taken h₁ (by rw [Q.x18, Q.x19, he])]; exact trap)))⟩
  have hLn : L < eLn.toNat := by
    have := Q.le
    rcases Nat.lt_or_ge L eLn.toNat with h | h
    · exact h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; omega)) he
  have hEb : heapStart ≤ eLp.toNat ∧ eLp.toNat + 24 * eLn.toNat ≤ heapNext w₀ := by
    rcases hbuf.2 with h | h
    · omega
    · exact ⟨by omega, h.2⟩
  have hEV : ValidMemRange eLp (3 * eLn.toNat) :=
    heap_vmr hEb.1 (by omega) hbuf.1
  -- what the loop keeps: `eq_lane`, the slots outside `LnW`
  have eLv (v : MachineState) (F : DFrame w₀ v (LnW s)) (i : Nat) (hi : i < eLn.toNat) :
      eAt v (eLp + BitVec.ofNat 64 (24 * i)) = eL.getD i 0 := by
    rw [F.eAt fun j hj hw ↦ by
        have := lnw _ hw; addr_omega [this, hj, hb, hA, hEb, hNw, hi],
      ← C.elems, getD_eListAt _ _ hi]
  have k₁ := b8000fb78_keeps h₁
  have hm₁ := b8000fb78_mem_same h₁
  obtain ⟨t₂, hr₂, hm₂, k₂, ⟨pc₂, x10₂, x11₂, hi1, hi2⟩ | hd⟩ := idx hL
    (b8000fb78_pc_not_taken h₁ (by rw [Q.x18, Q.x19]; exact he))
    (by rw [k₁ .x19 (by decide), Q.x19]) (by rw [k₁ .x8 (by decide), Q.x8])
    (by rw [k₁ .x15 (by decide), Q.x15])
  swap
  · exact ⟨_, hr₁.trans hr₂, Or.inr (Or.inr hd)⟩
  have x18₁ : t₁.getReg .x18 = eLn := by rw [k₁ .x18 (by decide), Q.x18]
  rw [x18₁] at hi1 hi2
  have hm12 (a : Word) : t₂.getMem a = w.getMem a := by rw [hm₂, hm₁]
  have r₂ (r : Reg) (hr : r ∈ [Reg.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x15, .x16, .x17,
      .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]) :
      t₂.getReg r = w.getReg r := by
    rw [k₂ r hr, k₁ r (mem_of_mem hr _)]
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 1712 := by rw [r₂ .x2 (by decide), B.x2]
  have B₂ : Base s t₂ := B.same x2₂ hm12
  have F₂ : DFrame w₀ t₂ (LnW s) := Q.frame.trans (DFrame.of_same hm12 _) fun _ h ↦ h
  have keepS (v : MachineState) (F : DFrame w₀ v (LnW s)) (y : Word)
      (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat) (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
        (s.getReg .x2).toNat - 1424 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 752 ∨
        (s.getReg .x2).toNat - 152 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 128) :
      v.getMem y = w₀.getMem y :=
    F y fun i hi hw ↦ by simp only [LnW] at hw; rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hi, h1, h2, hb]
  have m112 : t₂.getMem (s.getReg .x2 - 1600) = eLp := by
    rw [keepS t₂ F₂ _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), C.p112]
  have x20₂ : t₂.getReg .x20 = eLp + BitVec.ofNat 64 (24 * L) + 16 := by rw [r₂ .x20 (by decide), Q.x20]
  -- `0x8000fbd8`: `eq_lane[i1]` and `eq_lane[lane]` loaded, `beta * eq_lane[i2]`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000fbd8_spec pc₂ (by
    rv_eval [x2₂, x10₂, x20₂, m112, mul24n]
    and_intros <;> first
      | valid_access hpre.stack.valid [hb]
      | valid_access hEV [hEb, hNw, hi1, hLn, hbuf.1])
  have k₃ := b8000fbd8_keeps h₃
  have hm₃ := b8000fbd8_mem_same h₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 1712 := by rw [k₃ .x2 (by decide), x2₂]
  have B₃ : Base s t₃ := B₂.same x2₃ hm₃
  have F₃ : DFrame w₀ t₃ (LnW s) := F₂.trans (DFrame.of_same hm₃ _) fun _ h ↦ h
  have x10₃ : t₃.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000fbd8_x10 h₃, x2₂]; rv_eval []
  have x11₃ : t₃.getReg .x11 = s.getReg .x2 - 776 := by rw [b8000fbd8_x11 h₃, x2₂]; rv_eval []
  have x12₃ : t₃.getReg .x12 = eLp + BitVec.ofNat 64 (24 * i2 L) := by
    rw [b8000fbd8_x12 h₃, x2₂, x11₂]; rv_eval [m112, mul24n]
  have hmp : MulPre t₃ := mul_pre hpre x2₃ (B₃.rodata hpre) 1448 x10₃ (by decide) (by decide)
    (by decide)
    (by rw [x11₃]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₃]; addr_omega [hb])
    (by rw [x10₃, x11₃]; addr_omega [hb])
    (by rw [x12₃]; valid_sub hEV [hEb, hNw, hi2, hbuf.1])
    (by rw [x12₃]; addr_omega [hb, hA, hEb, hNw, hi2])
    (by rw [x10₃, x12₃]; addr_omega [hb, hA, hEb, hNw, hi2])
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hd⟩ := hM.call (hr₂.trans hr₃) (b8000fbd8_pc h₃) hmp
  swap
  · exact ⟨_, hr₁.trans hr₄, Or.inr (Or.inr hd)⟩
  have G₄ := mul_frame x2₃ hpost₄
  rw [x10₃] at G₄
  have v₄ := hpost₄.value
  rw [x10₃, x11₃, x12₃, eLv t₃ F₃ _ hi2,
    F₃.eAt fun j hj hw ↦ by
      simp only [LnW] at hw; rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hb], C.beta] at v₄
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 1712 := (hpres₄.reg .x2).trans x2₃
  have F₄ : DFrame w₀ t₄ (LnW s) := F₃.trans G₄ fun a h ↦ by
    simp only [LnW]; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  have hN₄ : t₄.getMem nextAddr = t₃.getMem nextAddr := G₄ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have B₄ : Base s t₄ := B₃.next hpre x2₄
    ⟨by simp only [heapNext, hN₄]; exact B₃.heap.lo, by simp only [heapNext, hN₄]; exact B₃.heap.hi⟩
    (by simp only [heapNext, hN₄]; exact le_refl _) G₄ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb]
  -- `0x8000fc28`: `beta * eq_lane[i2] + eq_lane[i1]` into `f + 1584`, times `beta`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000fc28_spec
    (by rw [hpc₄, returnAddress_eq, b8000fbd8_x1 h₃]; decide) (by
      rv_eval [x2₄]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₅ := b8000fc28_keeps h₅
  have f₅ := b8000fc28_frame h₅ (by rw [x2₄]; addr_omega [hb])
  rw [x2₄] at f₅
  rv_eval [] at f₅
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 1712 := (k₅ .x2 (by decide)).trans x2₄
  have B₅ : Base s t₅ := B₄.slots hpre x2₅ f₅ (by addr_omega [hb]) (by addr_omega [hb])
  have F₅ : DFrame w₀ t₅ (LnW s) := F₄.trans (DFrame.of_memFrame f₅) fun a h ↦ by
    simp only [LnW]; exact Or.inr (Or.inl h)
  have e1 : eAt t₅ (s.getReg .x2 - 128) = beta * eL.getD (i2 L) 0 + eL.getD (i1 L) 0 := by
    apply eAt_eq_of_limbs
    rw [limbs_add, ← v₄, ← eLv t₃ F₃ _ hi1, limbs_eAt, limbs_eAt]
    have n0 := b8000fc28_m_x2_1584 h₅
    have n8 := b8000fc28_m_x2_1592 h₅
    have n16 := b8000fc28_m_x2_1600 h₅
    rw [x2₄] at n0 n8 n16
    rv_eval [] at n0 n8 n16
    have y23 : t₄.getReg .x23 = t₃.getReg .x23 := hpres₄.reg .x23
    have y18 : t₄.getReg .x18 = t₃.getReg .x18 := hpres₄.reg .x18
    have y22 : t₄.getReg .x22 = t₃.getReg .x22 := hpres₄.reg .x22
    rw [y23, b8000fbd8_x23 h₃] at n0
    rw [y18, b8000fbd8_x18 h₃] at n8
    rw [y22, b8000fbd8_x22 h₃] at n16
    rw [x2₂, x10₂] at n0 n8 n16
    rv_eval [m112, mul24n] at n0 n8 n16
    rv_eval [n0, n8, n16, hm₃]
  have x10₅ : t₅.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000fc28_x10 h₅, x2₄]; rv_eval []
  have x11₅ : t₅.getReg .x11 = s.getReg .x2 - 776 := by rw [b8000fc28_x11 h₅, x2₄]; rv_eval []
  have x12₅ : t₅.getReg .x12 = s.getReg .x2 - 128 := by rw [b8000fc28_x12 h₅, x2₄]; rv_eval []
  have hmp₅ : MulPre t₅ := mul_pre hpre x2₅ (B₅.rodata hpre) 1448 x10₅ (by decide) (by decide)
    (by decide)
    (by rw [x11₅]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x11₅]; addr_omega [hb])
    (by rw [x10₅, x11₅]; addr_omega [hb])
    (by rw [x12₅]; exact slot_vmr hpre (by decide) (by decide) (by decide))
    (by rw [x12₅]; addr_omega [hb])
    (by rw [x10₅, x12₅]; addr_omega [hb])
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hpost₆⟩ | hd⟩ := hM.call hr₅ (b8000fc28_pc h₅) hmp₅
  swap
  · exact ⟨_, hr₁.trans (hr₄.trans hr₆), Or.inr (Or.inr hd)⟩
  have G₆ := mul_frame x2₅ hpost₆
  rw [x10₅] at G₆
  have v₆ := hpost₆.value
  rw [x10₅, x11₅, x12₅, e1, F₅.eAt fun j hj hw ↦ by
      simp only [LnW] at hw; rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hb],
    C.beta] at v₆
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 1712 := (hpres₆.reg .x2).trans x2₅
  have F₆ : DFrame w₀ t₆ (LnW s) := F₅.trans G₆ fun a h ↦ by
    simp only [LnW]; rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  have hN₆ : t₆.getMem nextAddr = t₅.getMem nextAddr := G₆ _ fun i hi hw ↦ by
    rcases hw with hw | hw <;> addr_omega [hi, hw, hb, hnx]
  have B₆ : Base s t₆ := B₅.next hpre x2₆
    ⟨by simp only [heapNext, hN₆]; exact B₅.heap.lo, by simp only [heapNext, hN₆]; exact B₅.heap.hi⟩
    (by simp only [heapNext, hN₆]; exact le_refl _) G₆ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;> addr_omega [h, hb]
  -- the registers across the two calls
  have cs (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x24, .x25, .x26, .x27]) :
      t₆.getReg r = t₃.getReg r := by
    rw [hpres₆.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      k₅ r (mem_of_mem hr _),
      hpres₄.reg r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have x25₆ : t₆.getReg .x25 = s.getReg .x2 - 736 + BitVec.ofNat 64 (24 * L) := by
    rw [cs .x25 (by decide), k₃ .x25 (by decide), r₂ .x25 (by decide), Q.x25]
  -- `0x8000fc60`: the lane's weight stored, the next lane
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b8000fc60_spec
    (by rw [hpc₆, returnAddress_eq, b8000fc28_x1 h₅]; decide) (by
      rv_eval [x2₆, x25₆]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb, hL]
        | addr_omega [hb, hL])
  have k₇ := b8000fc60_keeps h₇
  have f₇ := b8000fc60_frame h₇ (by rw [x25₆]; constructor <;> addr_omega [hb, hL])
  rw [x25₆, sh16] at f₇
  have x2₇ : t₇.getReg .x2 = s.getReg .x2 - 1712 := (k₇ .x2 (by decide)).trans x2₆
  have B₇ : Base s t₇ := B₆.slots hpre x2₇ f₇ (by addr_omega [hb, hL]) (by addr_omega [hb, hL])
  have F₇ : DFrame w₀ t₇ (LnW s) := F₆.trans (DFrame.of_memFrame f₇) fun a h ↦ by
    simp only [LnW]; exact Or.inr (Or.inr (Or.inr (by addr_omega [h, hb, hL])))
  have eL0 := eLv t₃ F₃ L hLn
  have enew : eAt t₇ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * L)) = laneW eL beta L := by
    apply eAt_eq_of_limbs
    rw [laneW, limbs_add, ← v₆, ← eL0, limbs_eAt, limbs_eAt]
    have n0 := b8000fc60_m_x25_n16 h₇
    have n8 := b8000fc60_m_x25_n8 h₇
    have n16 := b8000fc60_m_x25_0 h₇
    rw [x25₆, x2₆] at n0 n8 n16
    rw [cs .x9 (by decide), b8000fbd8_x9 h₃] at n0
    rw [cs .x24 (by decide), b8000fbd8_x24 h₃] at n8
    rw [cs .x21 (by decide), b8000fbd8_x21 h₃] at n16
    rw [x20₂] at n0 n8 n16
    rw [sh16] at n0
    rw [sh8] at n8
    rw [sh0] at n16
    rv_eval [] at n0 n8 n16
    rv_eval [n0, n8, n16, hm₃]
  have e3 (a : Word) : eAt t₃ a = eAt w a := by unfold Rv64Verifier.eAt; rw [hm₃, hm₃, hm₃, hm12, hm12, hm12]
  have hnot (i : Nat) (hi : i < 25) (hne : i ≠ L) :
      eAt t₇ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) =
        eAt w (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) := by
    rw [f₇.eAt (by addr_omega [hb, hL, hi, hne]) (by addr_omega [hb, hi]),
      G₆.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hi],
      f₅.eAt (by addr_omega [hb, hi]) (by addr_omega [hb, hi]),
      G₄.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb, hi], e3]
  have x19₆ : t₆.getReg .x19 = BitVec.ofNat 64 L := by
    rw [cs .x19 (by decide), k₃ .x19 (by decide), r₂ .x19 (by decide), Q.x19]
  have x8₆ : t₆.getReg .x8 = BitVec.ofNat 64 L := by
    rw [cs .x8 (by decide), k₃ .x8 (by decide), r₂ .x8 (by decide), Q.x8]
  have x27₆ : t₆.getReg .x27 = 0x3333333333333334 := by
    rw [cs .x27 (by decide), b8000fbd8_x27 h₃, r₂ .x15 (by decide), Q.x15]
  have x26₇ : t₇.getReg .x26 = w₀.getReg .x26 := by
    rw [k₇ .x26 (by decide), cs .x26 (by decide), k₃ .x26 (by decide), r₂ .x26 (by decide), Q.x26]
  have lw₇ (i : Nat) (hi : i < L + 1) :
      eAt t₇ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) = laneW eL beta i := by
    by_cases hiL : i = L
    · rw [hiL, enew]
    · rw [hnot i (by omega) hiL, Q.lw i (by omega)]
  have hr07 := hr₁.trans (hr₄.trans (hr₆.trans hr₇))
  by_cases hl : L + 1 < 25
  · refine ⟨t₇, hr07, Or.inl ⟨{
      base := B₇
      frame := F₇
      x8 := by rw [b8000fc60_x8 h₇, x8₆, ofNat_succ]
      x19 := by rw [b8000fc60_x19 h₇, x19₆, ofNat_succ]
      x15 := by rw [b8000fc60_x15 h₇, x27₆]
      x18 := by
        rw [b8000fc60_x18 h₇, x2₆]; rv_eval []
        rw [keepS t₆ F₆ _ (by addr_omega [hb]) (Or.inl (by addr_omega [hb])), C.p88]
      x20 := by
        rw [b8000fc60_x20 h₇, cs .x20 (by decide), k₃ .x20 (by decide), x20₂, st24']
      x25 := by rw [b8000fc60_x25 h₇, x25₆, st24]
      x26 := x26₇
      lw := lw₇
      le := hLn
      lt := hl }, b8000fc60_pc_taken h₇ ?_⟩⟩
    rw [x19₆, ofNat_succ]
    intro h; have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, show (25 : Word).toNat = 25 from rfl] at this; omega
  · refine ⟨t₇, hr07, Or.inr (Or.inl ⟨{
      base := B₇
      frame := F₇
      x26 := x26₇
      x27 := by rw [k₇ .x27 (by decide), x27₆]
      lw := fun i hi ↦ lw₇ i (by omega) }, b8000fc60_pc_not_taken h₇ ?_⟩)⟩
    rw [x19₆, ofNat_succ, show L + 1 = 25 by omega]; rfl

theorem lane_loop (hM : MulSpec) {s w₀ : MachineState} {eLp eLn : Word} {beta : E} {eL : List E}
    (hpre : VerifyLayerPre s) (C : LC s w₀ eLp eLn beta eL) :
    ∀ n L w, L + n = 25 → LN s w₀ w eLp eLn beta eL L → w.pc = 0x8000fb78 →
      ∃ v, Reaches Image.code w v ∧ ((LX s w₀ v beta eL ∧ v.pc = 0x8000fca4) ∨ Dead Image.code v)
  | 0, L, w, hn, Q, _ => absurd Q.lt (by omega)
  | n + 1, L, w, hn, Q, hpc => by
    obtain ⟨v, hr, ⟨Q', hpc'⟩ | ⟨X, hpc'⟩ | hd⟩ := lane_step hM hpre C Q hpc
    · obtain ⟨t, hr', ht⟩ := lane_loop hM hpre C n (L + 1) v (by omega) Q' hpc'
      exact ⟨t, hr.trans hr', ht⟩
    · exact ⟨v, hr, Or.inl ⟨X, hpc'⟩⟩
    · exact ⟨v, hr, Or.inr hd⟩

/-! ## From `J11` to the lane weights copied -/

/-- The lane weight as `nextWeightsRust` states it. -/
def laneModel (eL : List E) (beta : E) (L : Nat) : E :=
  eL.getD L 0 + beta * (eL.getD (keccakAlong (64 * L) 4 / 64) 0 +
    beta * eL.getD (keccakAlong (64 * L) 3 / 64) 0)

theorem laneW_eq (eL : List E) (beta : E) (L : Nat) : laneW eL beta L = laneModel eL beta L := by
  have e4 : keccakAlong (64 * L) 4 / 64 = i1 L := by rw [keccakAlong_def, i1]; omega
  have e3 : keccakAlong (64 * L) 3 / 64 = i2 L := by rw [keccakAlong_def, i2]; omega
  rw [laneW, laneModel, e4, e3]
  ring

/-- What `0x8000fb34..0x8000fcbc` writes: the sponge, the callees' stacks, `f + 24`, `f + 56`,
`f + 264 .. f + 864`, `beta`, the lane weights, `f + 1584`. -/
@[rv_addr] def W11b (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x11 + 8) 336 ∨ Within a (s.getReg .x2 - 2736) 1024 ∨
    Within a (s.getReg .x2 - 1448) 600 ∨ Within a (s.getReg .x2 - 776) 24 ∨
    Within a (s.getReg .x2 - 752) 600 ∨ Within a (s.getReg .x2 - 128) 24

@[rv_addr] def W11 (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1688) 8 ∨ Within a (s.getReg .x2 - 1656) 8 ∨ W11b s a

/-- After the lane weights, at `0x8000fcbc`. -/
structure J12 (s u : MachineState) (mu point eqZ eqLane t : List E) (beta : E) : Prop where
  pc : u.pc = 0x8000fcbc
  base : Base s u
  out : u.getMem (s.getReg .x2 - 1664) = s.getReg .x10
  muLen : (u.getReg .x26).toNat ≤ (u.getMem (s.getReg .x2 - 1672)).toNat
  muBuf : NewBuf s u (u.getMem (s.getReg .x2 - 1648))
    ((u.getMem (s.getReg .x2 - 1672)).toNat * 24) 8
  muE : eListAt u (u.getMem (s.getReg .x2 - 1648)) (u.getReg .x26).toNat = mu
  ptV : NewVecE s u (s.getReg .x2 - 848) point
  ezBuf : NewBuf s u (u.getMem (s.getReg .x2 - 1632)) (24 * (u.getMem (s.getReg .x2 - 1640)).toNat) 8
  ezE : eListAt u (u.getMem (s.getReg .x2 - 1632)) (u.getMem (s.getReg .x2 - 1640)).toNat = eqZ
  t2 : u.getMem (s.getReg .x2 - 1680) = u.getMem (s.getReg .x2 - 1656) + 48
  tBuf : NewBuf s u (u.getMem (s.getReg .x2 - 1656)) (24 * (u.getMem (s.getReg .x2 - 1688)).toNat) 8
  tE : eListAt u (u.getMem (s.getReg .x2 - 1656)) (u.getMem (s.getReg .x2 - 1688)).toNat = t
  bt : eAt u (s.getReg .x2 - 776) = beta
  x9 : u.getReg .x9 = s.getReg .x2 - 1448
  x27 : u.getReg .x27 = 0x3333333333333334
  lw : ∀ i < 25, eAt u (s.getReg .x2 - 1448 + BitVec.ofNat 64 (24 * i)) = laneModel eqLane beta i
  rest : Rest s u (pure ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), mu, point,
    linearTransposeRust (nextWeightsRust eqZ eqLane beta)⟩)

/-- A buffer allocated since the entry, below `NEXT` at `u`, misses `W11`. -/
theorem newBuf_w11 {s u : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk u) {p : Word}
    {n : Nat} (hB : NewBuf s u p n 8) {y : Word} (h1 : p.toNat ≤ y.toNat)
    (h2 : y.toNat < p.toNat + n) : ¬ W11 s y := by
  have hb := bounds hpre
  have hS := hpre.self.self
  have hsf := hpre.selfFree.1
  have hA := hpre.stack.above
  have hH1 := hH.hi
  simp only [stackLo] at hA
  unfold verifyLayerStack at hb hA
  simp only [NewBuf] at hB
  rcases hB.2 with h0 | ⟨b1, b2⟩
  · omega
  intro hw
  simp only [W11, W11b] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;> rcases hsf with h | h <;>
    addr_omega [hw, h, h1, h2, b1, b2, hH1, hS, hb, hA]

theorem newBuf_eList {s u v : MachineState} (hpre : VerifyLayerPre s) (hH : HeapOk u) {p : Word}
    {n k : Nat} (hB : NewBuf s u p n 8) (hk : 24 * k ≤ n) (F : DFrame u v (W11 s)) :
    eListAt v p k = eListAt u p k :=
  F.eListAt fun i hi hw ↦ by
    have hH1 := hH.hi
    have hb := hB
    simp only [NewBuf] at hb
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    exact newBuf_w11 hpre hH hB (by addr_omega [hi, hk, b2, hH1]) (by addr_omega [hi, hk, b2, hH1]) hw

set_option maxHeartbeats 32000000 in
theorem lanes (hD : DuplexSpec) (hM : MulSpec) (hMC : Runtime.MemcpySpec 0x800126e4)
    {s u : MachineState} {mu point eqZ eqLane t : List E} (hpre : VerifyLayerPre s)
    (J : J11 s u mu point eqZ eqLane t) :
    ∃ v beta, Reaches Image.code u v ∧ (J12 s v mu point eqZ eqLane t beta ∨ Dead Image.code v) := by
  have hb := bounds hpre
  have B := J.base
  have hS := hpre.self.self
  have hss := hpre.selfStack
  have hnx := hpre.stack.next
  have hA := hpre.stack.above
  have hsm := hpre.stack.mapped (by decide) (by decide)
  simp only [stackLo] at hA hnx hss
  unfold verifyLayerStack at hb hnx hA hss
  -- `0x8000fb34`: `t` saved, `duplex`
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b8000fb34_spec J.pc (by
    rv_eval [B.x2]; and_intros <;> valid_access hpre.stack.valid [hb])
  have k₀ := b8000fb34_keeps h₀
  have f₀ := b8000fb34_frame h₀ (by rw [B.x2]; addr_omega [hb])
  rw [B.x2] at f₀
  rv_eval [] at f₀
  have x2₀ : t₀.getReg .x2 = s.getReg .x2 - 1712 := (k₀ .x2 (by decide)).trans B.x2
  have B₀ : Base s t₀ := B.slots hpre x2₀ f₀ (by addr_omega [hb]) (by addr_omega [hb])
  have G₀ : DFrame u t₀ fun a ↦ Within a (s.getReg .x2 - 1688) 8 ∨ Within a (s.getReg .x2 - 1656) 8 :=
    Open.dframe_of_writes h₀ (by rv_eval [B.x2]; and_intros <;> addr_omega [hb])
  have m24 := b8000fb34_m_x2_24 h₀
  have m56 := b8000fb34_m_x2_56 h₀
  rw [B.x2] at m24 m56
  rv_eval [] at m24 m56
  obtain ⟨v₁, hr₁, ⟨hpc₁, hpres₁, B₁, F₁, tr₁⟩ | hd⟩ := duplexCall hD hpre B₀ hr₀
    (b8000fb34_pc h₀) (by rw [b8000fb34_x10 h₀, B.x2]; rv_eval [J.sponge])
  swap
  · exact ⟨_, 0, hr₁, Or.inr hd⟩
  have x2v : v₁.getReg .x2 = s.getReg .x2 - 1712 := (hpres₁.reg .x2).trans x2₀
  have x20v : v₁.getReg .x20 = s.getReg .x11 := by
    rw [hpres₁.reg .x20, k₀ .x20 (by decide), J.x20]
  -- `0x8000fb48`: `beta` from the state
  obtain ⟨w₀, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000fb48_spec
    (by rw [hpc₁, returnAddress_eq, b8000fb34_x1 h₀]; decide) (by
      rv_eval [x2v, x20v]
      and_intros <;> first
        | valid_access hpre.stack.valid [hb]
        | (refine Region.valid hS ?_ ?_ ?_ <;> addr_omega [hS]))
  have k₂ := b8000fb48_keeps h₂
  have f₂ := b8000fb48_frame h₂ (by rw [x2v]; addr_omega [hb])
  rw [x2v] at f₂
  rv_eval [] at f₂
  have x2w : w₀.getReg .x2 = s.getReg .x2 - 1712 := (k₂ .x2 (by decide)).trans x2v
  have Bw : Base s w₀ := B₁.slots hpre x2w f₂ (by addr_omega [hb]) (by addr_omega [hb])
  have n936 := b8000fb48_m_x2_936 h₂
  have n944 := b8000fb48_m_x2_944 h₂
  have n952 := b8000fb48_m_x2_952 h₂
  rw [x2v, x20v] at n936 n944 n952
  rv_eval [] at n936 n944 n952
  have Ftw : DFrame t₀ w₀ (W11b s) :=
    (F₁.mono fun a h ↦ by
      simp only [W11b]; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by addr_omega [h, hb]))).trans (DFrame.of_memFrame f₂) fun a h ↦ by
      simp only [W11b]; exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb]))))
  have toW11 {v : MachineState} (F : DFrame t₀ v (W11b s)) : DFrame u v (W11 s) :=
    (G₀.mono fun a h ↦ h.elim Or.inl fun h ↦ Or.inr (Or.inl h)).trans F fun a h ↦ Or.inr (Or.inr h)
  have Fuw := toW11 Ftw
  -- the transcript and the mirror
  have R₀ : Rest s t₀ (TM.sample >>= fun beta ↦ pure ⟨t.getD 0 0 + beta * (t.getD 1 0 +
      beta * t.getD 2 0), mu, point, linearTransposeRust (nextWeightsRust eqZ eqLane beta)⟩) :=
    J.rest.keep fun T hT ↦ B.slots_tat hpre B₀ f₀ (by addr_omega [hb]) (by addr_omega [hb]) hT
  have R₁ : Rest s w₀ (pure ⟨t.getD 0 0 + eAt w₀ (s.getReg .x2 - 776) * (t.getD 1 0 +
      eAt w₀ (s.getReg .x2 - 776) * t.getD 2 0), mu, point,
      linearTransposeRust (nextWeightsRust eqZ eqLane (eAt w₀ (s.getReg .x2 - 776)))⟩) :=
    R₀.step fun T hT ↦ by
      have h1 := tr₁ T hT
      refine ⟨{ T with sponge := spDuplex T.sponge }, ?_,
        B₁.slots_tat hpre Bw f₂ (by addr_omega [hb]) (by addr_omega [hb]) h1⟩
      have hs : spongeAt v₁ (s.getReg .x11 + 8) = spDuplex T.sponge := h1.sponge
      have e1 : (spSqueeze T.sponge).2 = spDuplex T.sponge := rfl
      have e2 : (spSqueeze T.sponge).1 = challengeOf (spDuplex T.sponge).state := rfl
      have hce : challengeOf (spDuplex T.sponge).state = eAt w₀ (s.getReg .x2 - 776) := by
        rw [← hs]
        show challengeOf (stateAt v₁ (s.getReg .x11 + 8 + 128)) = _
        rw [challengeOf_stateAt]
        symm
        apply eAt_congr <;> rv_eval [n936, n944, n952]
      show some ((spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }) = _
      rw [e1, e2, hce]
  have hsf := hpre.selfFree
  have slot {v : MachineState} (F : DFrame u v (W11 s)) (y : Word)
      (h1 : (s.getReg .x2).toNat - 1712 ≤ y.toNat)
      (h3 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1688 ∨
        (s.getReg .x2).toNat - 1680 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1656 ∨
        (s.getReg .x2).toNat - 1648 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448 ∨
        (s.getReg .x2).toNat - 848 ≤ y.toNat ∧ y.toNat + 8 ≤ (s.getReg .x2).toNat - 776) :
      v.getMem y = u.getMem y :=
    F y fun i hi hw ↦ by
      simp only [W11, W11b] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, h1, h3, hb, hS, hss]
  have hNw : w₀.getMem nextAddr = u.getMem nextAddr := Fuw _ fun i hi hw ↦ by
    simp only [W11, W11b] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hnx, hS, hsf.2]
  have hHu := B.heap
  have C : LC s w₀ (u.getReg .x25) (u.getReg .x18) (eAt w₀ (s.getReg .x2 - 776)) eqLane := {
    p112 := by rw [slot Fuw _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))), J.x25]
    p88 := by rw [slot Fuw _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inl ⟨by addr_omega [hb], by addr_omega [hb]⟩))), J.x18]
    beta := rfl
    buf := by have h := J.elBuf; simp only [NewBuf, heapNext, hNw] at h ⊢; exact h
    elems := by rw [newBuf_eList hpre hHu J.elBuf (le_refl _) Fuw, J.elE] }
  have Q₀ : LN s w₀ w₀ (u.getReg .x25) (u.getReg .x18) (eAt w₀ (s.getReg .x2 - 776)) eqLane 0 := {
    base := Bw
    frame := DFrame.refl _ _
    x8 := b8000fb48_x8 h₂
    x19 := b8000fb48_x19 h₂
    x15 := by rw [b8000fb48_x15 h₂]; exact (B₁.rodata hpre).word
    x18 := by rw [k₂ .x18 (by decide), hpres₁.reg .x18, k₀ .x18 (by decide)]
    x20 := by
      rw [b8000fb48_x20 h₂, hpres₁.reg .x25, k₀ .x25 (by decide), Nat.mul_zero, add_ofNat_zero]
    x25 := by rw [b8000fb48_x25 h₂, x2v, Nat.mul_zero, add_ofNat_zero]; rv_eval []
    x26 := rfl
    lw := fun i hi ↦ absurd hi (Nat.not_lt_zero i)
    le := Nat.zero_le _
    lt := by decide }
  obtain ⟨v, hr₃, ⟨X, hpc₃⟩ | hd⟩ := lane_loop hM hpre C 25 0 w₀ rfl Q₀ (b8000fb48_pc h₂)
  swap
  · exact ⟨v, 0, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
  -- `0x8000fca4`: the lane weights copied to `f + 264`
  have x2x : v.getReg .x2 = s.getReg .x2 - 1712 := X.base.x2
  obtain ⟨u₃, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000fca4_spec hpc₃ trivial
  have k₄ := b8000fca4_keeps h₄
  have hm₄ := b8000fca4_mem_same h₄
  have x2₄ : u₃.getReg .x2 = s.getReg .x2 - 1712 := (k₄ .x2 (by decide)).trans x2x
  have x10₄ : u₃.getReg .x10 = s.getReg .x2 - 1448 := by rw [b8000fca4_x10 h₄, x2x]; rv_eval []
  have x11₄ : u₃.getReg .x11 = s.getReg .x2 - 752 := by rw [b8000fca4_x11 h₄, x2x]; rv_eval []
  have x12₄ : u₃.getReg .x12 = 600 := b8000fca4_x12 h₄
  have hmc : Runtime.MemcpyPre u₃ := {
    dst := by rw [x10₄, x12₄]; addr_omega [hb, hsm]
    src := by rw [x11₄, x12₄]; addr_omega [hb, hsm]
    apart := by rw [x10₄, x11₄, x12₄]; addr_omega [hb]
    stack := (hpre.stack.sub 1712 x2₄ (by unfold verifyLayerStack; decide) (by decide) (by decide)
      (by decide) (by decide)).toStackOk
    dstStack := by rw [x10₄, x12₄]; simp only [stackLo, x2₄]; addr_omega [hb]
    srcStack := by rw [x11₄, x12₄]; simp only [stackLo, x2₄]; addr_omega [hb] }
  obtain ⟨u₄, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hd⟩ := hMC.call hr₄ (b8000fca4_pc h₄) hmc
  swap
  · exact ⟨_, 0, hr₁.trans (hr₂.trans (hr₃.trans hr₅)), Or.inr hd⟩
  have bytes := hpost₅.bytes
  have G₅ := DFrame.of_byteFrame hpost₅.frame
  rw [x10₄, x11₄, x12₄] at bytes
  rw [x10₄, x12₄] at G₅
  simp only [stackLo, x2₄] at G₅
  have x2₅ : u₄.getReg .x2 = s.getReg .x2 - 1712 := (hpres₅.reg .x2).trans x2₄
  have Fv5 : DFrame v u₄ (W11b s) := (DFrame.of_same hm₄ _).trans G₅ fun a h ↦ by
    simp only [W11b]; rcases h with h | h
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
    · exact Or.inr (Or.inl (by addr_omega [h, hb]))
  have Fw5 : DFrame w₀ u₄ (W11b s) := (X.frame.mono fun a h ↦ by
    simp only [LnW] at h; simp only [W11b]; rcases h with h | h | h | h
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))).trans Fv5 fun _ h ↦ h
  have Ft5 : DFrame t₀ u₄ (W11b s) := Ftw.trans Fw5 fun _ h ↦ h
  have Fu5 := toW11 Ft5
  have hN5 : u₄.getMem nextAddr = u.getMem nextAddr := Fu5 _ fun i hi hw ↦ by
    simp only [W11, W11b] at hw
    rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hnx, hS, hsf.2]
  have hNv : u₄.getMem nextAddr = v.getMem nextAddr := Fv5 _ fun i hi hw ↦ by
    simp only [W11b] at hw
    rcases hw with hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hnx, hS, hsf.2]
  have B₃ : Base s u₃ := X.base.same x2₄ hm₄
  have hN3 : u₄.getMem nextAddr = u₃.getMem nextAddr := by rw [hNv, hm₄]
  have B₅ : Base s u₄ := B₃.next hpre x2₅
    ⟨by simp only [heapNext, hN3]; exact B₃.heap.lo, by simp only [heapNext, hN3]; exact B₃.heap.hi⟩
    (by simp only [heapNext, hN3]; exact le_refl _) G₅ fun a h ↦ by
      refine ⟨Or.inr (Or.inr (Or.inl ?_)), ?_⟩ <;> rcases h with h | h <;>
        first | (unfold verifyLayerStack; addr_omega [h, hb]) | addr_omega [h, hb]
  have nb {p : Word} {n : Nat} (h : NewBuf s u p n 8) : NewBuf s u₄ p n 8 := by
    simp only [NewBuf, heapNext, hN5] at h ⊢; exact h
  have x26₅ : u₄.getReg .x26 = u.getReg .x26 := by
    rw [hpres₅.reg .x26, k₄ .x26 (by decide), X.x26, k₂ .x26 (by decide), hpres₁.reg .x26,
      k₀ .x26 (by decide)]
  have keep56 : u₄.getMem (s.getReg .x2 - 1656) = u.getReg .x24 := by
    rw [Ft5 _ fun i hi hw ↦ by
      simp only [W11b] at hw
      rcases hw with hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hS, hss], m56]
  have keep24 : u₄.getMem (s.getReg .x2 - 1688) = u.getReg .x19 := by
    rw [Ft5 _ fun i hi hw ↦ by
      simp only [W11b] at hw
      rcases hw with hw | hw | hw | hw | hw | hw <;> addr_omega [hw, hi, hb, hS, hss], m24]
  have hlw (i : Nat) (hi : i < 25) : eAt u₄ (s.getReg .x2 - 1448 + BitVec.ofNat 64 (24 * i)) =
      laneModel eqLane (eAt w₀ (s.getReg .x2 - 776)) i := by
    have e : eListAt u₄ (s.getReg .x2 - 1448) 25 = eListAt u₃ (s.getReg .x2 - 752) 25 :=
      eListAt_eq_of_bytesAt (by rw [show 24 * 25 = ((600 : Word)).toNat from rfl]; exact bytes)
        (by addr_omega [hb]) (by addr_omega [hb])
    rw [← getD_eListAt _ _ hi, e, getD_eListAt _ _ hi,
      show eAt u₃ (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) =
        eAt v (s.getReg .x2 - 752 + BitVec.ofNat 64 (24 * i)) by
          unfold Rv64Verifier.eAt; rw [hm₄, hm₄, hm₄],
      X.lw i hi, laneW_eq]
  have bt5 : eAt u₄ (s.getReg .x2 - 776) = eAt w₀ (s.getReg .x2 - 776) := by
    rw [G₅.eAt fun j hj hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hj, hb],
      show eAt u₃ (s.getReg .x2 - 776) = eAt v (s.getReg .x2 - 776) by
        unfold Rv64Verifier.eAt; rw [hm₄, hm₄, hm₄],
      X.frame.eAt fun j hj hw ↦ by
        simp only [LnW] at hw; rcases hw with hw | hw | hw | hw <;> addr_omega [hw, hj, hb]]
  have Fst : DFrame w₀ u₄ (Within · (s.getReg .x2 - 2736) 2736) :=
    (X.frame.mono fun a h ↦ by
      simp only [LnW] at h; rcases h with h | h | h | h <;> addr_omega [h, hb]).trans
      ((DFrame.of_same hm₄ _).trans G₅ fun a h ↦ by rcases h with h | h <;> addr_omega [h, hb])
      fun _ h ↦ h
  have hc : vecCap u₄ (s.getReg .x2 - 848) = vecCap u (s.getReg .x2 - 848) :=
    slot Fu5 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
  have hp : vecPtr u₄ (s.getReg .x2 - 848) = vecPtr u (s.getReg .x2 - 848) :=
    slot Fu5 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
  have hl : vecLen u₄ (s.getReg .x2 - 848) = vecLen u (s.getReg .x2 - 848) :=
    slot Fu5 _ (by addr_omega [hb]) (Or.inr (Or.inr (Or.inr ⟨by addr_omega [hb], by addr_omega [hb]⟩)))
  have s2 (y : Word) (h1 : (s.getReg .x2).toNat - 1680 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1656) : u₄.getMem y = u.getMem y :=
    slot Fu5 y (by addr_omega [h1, hb]) (Or.inr (Or.inl ⟨h1, h2⟩))
  have s3 (y : Word) (h1 : (s.getReg .x2).toNat - 1648 ≤ y.toNat)
      (h2 : y.toNat + 8 ≤ (s.getReg .x2).toNat - 1448) : u₄.getMem y = u.getMem y :=
    slot Fu5 y (by addr_omega [h1, hb]) (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩)))
  obtain ⟨⟨hraw, hlen⟩, hbuf, hel⟩ := J.ptV
  refine ⟨u₄, eAt w₀ (s.getReg .x2 - 776), hr₁.trans (hr₂.trans (hr₃.trans hr₅)), Or.inl {
    pc := by rw [hpc₅, returnAddress_eq, b8000fca4_x1 h₄]; decide
    base := B₅
    out := by rw [s2 _ (by addr_omega [hb]) (by addr_omega [hb]), J.out]
    muLen := by
      rw [x26₅, s2 _ (by addr_omega [hb]) (by addr_omega [hb])]; exact J.muLen
    muBuf := by
      rw [s2 (s.getReg .x2 - 1672) (by addr_omega [hb]) (by addr_omega [hb]),
        s3 (s.getReg .x2 - 1648) (by addr_omega [hb]) (by addr_omega [hb])]
      exact nb J.muBuf
    muE := by
      rw [x26₅, s3 _ (by addr_omega [hb]) (by addr_omega [hb]),
        newBuf_eList hpre hHu J.muBuf (by have := J.muLen; omega) Fu5, J.muE]
    ptV := by
      refine ⟨⟨?_, by rw [hl, hc]; exact hlen⟩, ?_, ?_⟩
      · have h := hraw
        simp only [RawVecOk, Buf, heapNext] at h ⊢
        rw [hc, hp, hN5]; exact h
      · have h := hbuf
        simp only [NewBuf, heapNext] at h ⊢
        rw [hc, hp, hN5]; exact h
      · simp only [vecEs] at hel ⊢
        rw [hp, hl, newBuf_eList hpre hHu hbuf (by have := hlen; omega) Fu5]; exact hel
    ezBuf := by
      rw [s3 _ (by addr_omega [hb]) (by addr_omega [hb]), s3 _ (by addr_omega [hb]) (by addr_omega [hb])]
      exact nb J.ezBuf
    ezE := by
      rw [s3 _ (by addr_omega [hb]) (by addr_omega [hb]), s3 _ (by addr_omega [hb]) (by addr_omega [hb]),
        newBuf_eList hpre hHu J.ezBuf (le_refl _) Fu5, J.ezE]
    t2 := by rw [s2 _ (by addr_omega [hb]) (by addr_omega [hb]), keep56, J.t2]
    tBuf := by rw [keep56, keep24]; exact nb J.tBuf
    tE := by rw [keep56, keep24, newBuf_eList hpre hHu J.tBuf (le_refl _) Fu5, J.tE]
    bt := bt5
    x9 := by rw [hpres₅.reg .x9, b8000fca4_x9 h₄, x2x]; rv_eval []
    x27 := by rw [hpres₅.reg .x27, k₄ .x27 (by decide), X.x27]
    lw := hlw
    rest := R₁.keep fun T hT ↦
      Bw.tat hpre B₅.heap Fst (fun a ha ↦ bodyW_tat hpre Bw B₅.heap (stk_body hpre ha)) hT }⟩

end Rv64Verifier.Gkr.Layer
