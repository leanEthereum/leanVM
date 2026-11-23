module

public import NativeRustcArm.Hasher.Bytes
public import NativeRustcVm.MemLemmas
public import NativeRustcVmArm.Spec.Keccak

/-!
# Words the executor loads

A word in memory (`NativeRustcVm.WordAt`) at a region's offset is what the environment loads
there (`load_word`); an 8-byte write of a block leaves its value's word (`Match.wordAt_write`).

The stack of a callee below its caller's frame: the caller's `StackOk`, `RcAt` and `Apart … (stackBelow
…)` give the callee's (`StackOk.sub`, `RcAt.sub`, `Apart.stack_sub`), and a range above SP is apart
from the stack below it (`apart_above`).
-/

namespace NativeRustcVmArm.Sumcheck

open NativeRustcArm NativeRustcArm.Sym LeanVM.Protocol.KeccakHash

public section

/-- A word's bytes loaded: the word. -/
theorem ofInt_ofBytes_wordBytes (v : UInt64) :
    BitVec.ofInt 64 (Int.ofBytes (wordBytes v)) = v.toBitVec := by
  have hw := Hasher.wordBytes_ofBitVec v.toBitVec
  have hb := Sym.ofBytes_byteOf v.toBitVec 0 8
  simp only [Nat.zero_add] at hb
  rw [show UInt64.ofBitVec v.toBitVec = v from rfl] at hw
  rw [hw, hb, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have := v.toBitVec.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

/-- **A word at a region's offset** is what the environment loads there. -/
theorem load_word {env : Env} {r off : Nat} {v : UInt64}
    (h : NativeRustcVm.WordAt env.mem0 (env.base r + BitVec.ofNat 64 off) v) :
    env.load r off 8 = v.toBitVec := by
  rw [Env.load_of_bytesAt (NativeRustcVm.length_wordBytes v) h, ofInt_ofBytes_wordBytes]

/-- **A word a block wrote**: an 8-byte write of `v` at offset `o` of region `r`. -/
theorem Match.wordAt_write [Labels] {env : Env} {S : SState} {m : MachineData}
    (hm : Match env S m) {r o : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hle : o + 8 ≤ sz) {v : Sym}
    (hw : ∀ i < 8, findWrite r (o + i) S.mem = some (v, i)) :
    NativeRustcVm.WordAt m.dmem (b + BitVec.ofNat 64 o) (UInt64.ofBitVec (v.eval env)) := by
  have := hm.bytesAt_write hb hle hw
  unfold NativeRustcVm.WordAt NativeRustcVm.wordBytes
  rw [Hasher.wordBytes_ofBitVec]
  exact this

/-- **Where a block wrote**: in region `r`, when every write of the block is there. -/
theorem Written.inRange {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz : Nat}
    (hb : env.regions[r]? = some (b, sz)) (hnw : b.toNat + sz ≤ 2 ^ 64)
    (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz) {p : BitVec 64} (h : Written env S p) :
    InRange b sz p := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hle⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  exact (NativeRustcVm.inRange_iff hnw).mpr ⟨by omega, by omega⟩

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `ubfm x, k, 63` (`lsr x, #k`). -/
theorem evalUBFM_lsr (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (evalUBFM (w := .W64) x k 63 : BitVec 64) = x >>> k := by
  have hb : RegWidth.W64.bits = 64 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [evalUBFM, hb, Nat.mod_eq_of_lt hk, show 63 % 64 = 63 from rfl,
    show 63 ≥ k from by omega, ↓reduceIte, BitVec.toNat_setWidth, toNat_take',
    BitVec.toNat_ushiftRight]
  have h1 : x.toNat >>> k < 2 ^ (63 - k + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 63 - k + 1 + k = 64 by omega]
    exact x.isLt
  have h2 : 2 ^ (63 - k + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

/-- **Where a block wrote**, as numbers: from `lo` to `hi` in region `r`, when every write of the
block is there. -/
theorem Written.toNat {env : Env} {S : SState} {r : Nat} {b : BitVec 64} {sz lo hi : Nat}
    (hb : env.regions[r]? = some (b, sz))
    (hS : ∀ w ∈ S.mem, w.r = r ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) {p : BitVec 64}
    (h : Written env S p) : b.toNat + lo ≤ p.toNat ∧ p.toNat < b.toNat + hi := by
  obtain ⟨w, hw, b', sz', hb', h1, h2⟩ := h
  obtain ⟨hr, hlo, hle⟩ := hS w hw
  rw [hr, hb] at hb'
  cases hb'
  omega

/-- `lsr x, #1` of a word: the word halved. -/
theorem evalUBFM_half (q : UInt64) :
    UInt64.ofBitVec (evalUBFM (w := .W64) q.toBitVec 1 63) = q / 2 := by
  rw [evalUBFM_lsr _ (by decide)]
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_div, Nat.shiftRight_eq_div_pow]

/-- Bit `0` of a word's low half: the word is odd. -/
theorem getLsbD_low_zero (q : UInt64) :
    (Sym.low .W32 q.toBitVec).getLsbD 0 = decide (q % 2 ≠ 0) := by
  simp only [Sym.low, BitVec.take, BitVec.getLsbD_extractLsb']
  simp [BitVec.getLsbD, Nat.testBit]
  have h : q % 2 = 0 ↔ q.toNat % 2 = 0 := by
    constructor
    · intro h; have := congrArg UInt64.toNat h; simpa [UInt64.toNat_mod] using this
    · intro h; apply UInt64.toNat_inj.mp; simpa [UInt64.toNat_mod] using h
  by_cases h' : q.toNat % 2 = 0
  · simp [h', h.mpr h']
  · have : q.toNat % 2 = 1 := by omega
    simp only [this, beq_self_eq_true]
    rw [decide_eq_false fun e ↦ h' (h.mp e)]
    rfl

/-- `subs w8, w0, #3; csel w1, wzr, w8, lo`: the bit count less `3`, saturating. -/
theorem grind_bits [Labels] (env : Env) (hx : (env.regs .X0).toNat ≤ 64) :
    ((Sym.ite (SBool.cmp CmpOp.ult RegWidth.W32 (.reg .X0) (.lit 3)) (.lit 0)
      (.bin BinOp.sub RegWidth.W32 (.reg .X0) (.lit 3))).eval env).toNat =
      (env.regs .X0).toNat - 3 := by
  sym_simp
  have h32 : (BitVec.setWidth 32 (env.regs .X0)).toNat = (env.regs .X0).toNat := by
    rw [BitVec.toNat_setWidth]; omega
  have h3 : (BitVec.setWidth 32 (3#64)).toNat = 3 := by decide
  by_cases h : (env.regs .X0).toNat < 3
  · have : (BitVec.setWidth 32 (env.regs .X0)).ult (BitVec.setWidth 32 3#64) = true := by
      simp only [BitVec.ult, h32, h3]; simp [h]
    rw [ite_eq_left this]; simp; omega
  · have : (BitVec.setWidth 32 (env.regs .X0)).ult (BitVec.setWidth 32 3#64) = false := by
      simp only [BitVec.ult, h32, h3]; simp; omega
    rw [ite_eq_right (by rw [this]; decide)]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, h32, h3]
    omega

/-! ## The stack below a frame -/

variable {m m' : MachineData} {f N N' : Nat}

theorem toNat_stackBelow (h : N ≤ m.regs.SP.toNat) :
    (stackBelow m N).toNat = m.regs.SP.toNat - N :=
  NativeRustcVm.toNat_sub_ofNat h

/-- The SP `f` bytes below. -/
theorem toNat_sp_sub (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f)
    (hf : f ≤ m.regs.SP.toNat) : m'.regs.SP.toNat = m.regs.SP.toNat - f := by
  show m'.regs.SP.toBitVec.toNat = _
  rw [hsp]
  exact NativeRustcVm.toNat_sub_ofNat hf

/-- **A callee's stack is inside its caller's**: a range apart from the caller's stack is apart from
the callee's, `f` bytes of frame further down. -/
theorem Apart.stack_sub {x : BitVec 64} {n : Nat} (h : Apart x n (stackBelow m N) N)
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hfN : f + N' ≤ N)
    (hN : N ≤ m.regs.SP.toNat) : Apart x n (stackBelow m' N') N' := by
  have h1 := toNat_sp_sub hsp (by omega)
  have h2 : (stackBelow m' N').toNat = m'.regs.SP.toNat - N' := toNat_stackBelow (by omega)
  unfold Apart at h ⊢
  rw [toNat_stackBelow hN] at h
  omega

/-- A range above SP is apart from the stack below it. -/
theorem apart_above {x : BitVec 64} {n : Nat} (hx : m.regs.SP.toNat ≤ x.toNat)
    (hN : N ≤ m.regs.SP.toNat) : Apart x n (stackBelow m N) N := by
  unfold Apart
  rw [toNat_stackBelow hN]
  omega

/-- **A callee's `StackOk`** from its caller's, `f` bytes of frame (a multiple of `16`) further
down, every byte of the caller kept. -/
theorem StackOk.sub (h : StackOk m N)
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hf : f % 16 = 0)
    (hfN : f + N' ≤ N) (hk : Kept m.dmem m'.dmem) : StackOk m' N' := by
  obtain ⟨hal, hN, hmap⟩ := h
  have h1 := toNat_sp_sub hsp (by omega)
  have hs : m.regs.SP.toNat = m.regs.SP.toBitVec.toNat := rfl
  have hs' : m'.regs.SP.toNat = m'.regs.SP.toBitVec.toNat := rfl
  have hlt := m.regs.SP.toBitVec.isLt
  refine ⟨by omega, by omega, fun i hi ↦ hk _ ?_⟩
  have : m'.regs.SP.toBitVec - BitVec.ofNat 64 N' + BitVec.ofNat 64 i =
      m.regs.SP.toBitVec - BitVec.ofNat 64 N + BitVec.ofNat 64 (N - f - N' + i) := by
    apply BitVec.eq_of_toNat_eq
    have e1 : (m'.regs.SP.toBitVec - BitVec.ofNat 64 N').toNat = m'.regs.SP.toNat - N' :=
      NativeRustcVm.toNat_sub_ofNat (by omega)
    have e2 : (m.regs.SP.toBitVec - BitVec.ofNat 64 N).toNat = m.regs.SP.toNat - N :=
      NativeRustcVm.toNat_sub_ofNat hN
    rw [NativeRustcVm.toNat_add_ofNat (by rw [e1]; omega),
      NativeRustcVm.toNat_add_ofNat (by rw [e2]; omega), e1, e2]
    omega
  rw [this]
  exact hmap _ (by omega)

/-- **A callee's `RcAt`** from its caller's: the constants' bytes the same, its stack inside the
caller's. -/
theorem RcAt.sub [Labels] (h : RcAt m N)
    (hsp : m'.regs.SP.toBitVec = m.regs.SP.toBitVec - BitVec.ofNat 64 f) (hfN : f + N' ≤ N)
    (hN : N ≤ m.regs.SP.toNat)
    (hsame : ∀ p, InRange rcAddr 192 p → m'.dmem.get? p = m.dmem.get? p) : RcAt m' N' := by
  obtain ⟨hw, hnw, hap⟩ := h
  refine ⟨fun i hi ↦ ?_, hnw, Apart.stack_sub hap hsp hfN hN⟩
  have hl : (LeanVM.Parameters.keccakRC.flatMap NativeRustcVm.wordBytes).length = 192 := by
    rw [NativeRustcVm.length_wordsBytes]; rfl
  rw [hsame _ (NativeRustcVm.inRange_add (by omega) (by omega))]
  exact hw i hi

end

end NativeRustcVmArm.Sumcheck
