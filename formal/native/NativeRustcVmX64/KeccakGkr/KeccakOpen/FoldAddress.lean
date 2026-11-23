module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Entry2

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (off)

public section

theorem shl11 (x : BitVec 64) : x <<< 11 = BitVec.ofNat 64 (2048 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

variable [Labels] {m0 d : MachineData} {sl : Array EW} {t i : Nat}

theorem eval_P3 : P3.eval (envK m0 (varsOf sl t i)) = off (rwA m0) (1024 * i) := by
  simp only [P3, Sym.eval, BinOp.apply, low_W64, ext_W64]
  change (rwA m0 + 0#64) + BitVec.ofNat 64 (1024 * i) = _
  rw [BitVec.add_zero]

theorem eval_srcA (hi : i < 64) :
    srcA0.eval (envK m0 (varsOf sl t i)) = off (rwA m0) (1024 * (2 * i)) := by
  simp only [srcA0, sh2, Sym.eval, BinOp.apply, low_W64, ext_W64]
  change (rwA m0 + 0#64) + (BitVec.ofNat 64 i <<< 11) = _
  rw [BitVec.add_zero, shl11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    show 2048 * i = 1024 * (2 * i) by omega]

theorem eval_srcB (hi : i < 64) :
    srcB0.eval (envK m0 (varsOf sl t i)) = off (rwA m0) (1024 * (2 * i + 1)) := by
  change BinOp.apply .add .W64 1024#64 (srcA0.eval (envK m0 (varsOf sl t i))) = _
  rw [eval_srcA hi]
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.add_comm]
  change (rwA m0 + BitVec.ofNat 64 (1024 * (2 * i))) + BitVec.ofNat 64 1024 = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2

theorem eval_nextI : (Sym.bin .add .W64 (.var 2) (.lit 1)).eval (envK m0 (varsOf sl t i)) =
    BitVec.ofNat 64 (i + 1) := by
  change BinOp.apply .add .W64 (BitVec.ofNat 64 i) 1#64 = _
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.ofNat_add]

theorem eval_nextP : (Sym.bin .add .W64 (.lit 1024) P3).eval (envK m0 (varsOf sl t i)) =
    P3.eval (envK m0 (varsOf sl t (i + 1))) := by
  change BinOp.apply .add .W64 1024#64 (P3.eval (envK m0 (varsOf sl t i))) = _
  rw [eval_P3, eval_P3]
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.add_comm]
  change (rwA m0 + BitVec.ofNat 64 (1024 * i)) + BitVec.ofNat 64 1024 = _
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

theorem next_kR0 (hk : KAt m0 (varsOf sl 0 i) k10 d) :
    KAt m0 (varsOf sl 0 (i + 1)) kR0 d := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · change reg d .r12 = (sl.getD 0 0).c0.toBitVec
    exact hk.1
  · change reg d .r13 = (sl.getD 0 0).c1.toBitVec
    exact hk.2.1
  · change reg d .rbx = BitVec.ofNat 64 (i + 1)
    exact hk.2.2.1.trans (eval_nextI (m0 := m0) (sl := sl) (t := 0) (i := i))
  · exact hk.2.2.2.1.trans (eval_nextP (m0 := m0) (sl := sl) (t := 0) (i := i))

theorem next_kR1 (hk : KAt m0 (varsOf sl 1 i) k17 d) :
    KAt m0 (varsOf sl 1 (i + 1)) kR1 d := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · change reg d .r12 = (sl.getD 1 0).c0.toBitVec
    exact hk.1
  · change reg d .r13 = (sl.getD 1 0).c1.toBitVec
    exact hk.2.1
  · change reg d .rbp = BitVec.ofNat 64 (i + 1)
    exact hk.2.2.1.trans (eval_nextI (m0 := m0) (sl := sl) (t := 1) (i := i))
  · exact hk.2.2.2.1.trans (eval_nextP (m0 := m0) (sl := sl) (t := 1) (i := i))

theorem saved_row {ret : BitVec 64} (hw : Words m0 (varsOf sl t i) w5 d) :
    (E m0 d (varsOf sl t i) ret).load 0 16 8 = BitVec.ofNat 64 i := by
  have hh : NativeRustcVm.WordAt d.dmem (off (fbA m0) 16) (UInt64.ofBitVec (BitVec.ofNat 64 i)) := hw.1
  exact (load_of_wordAt hh).trans (UInt64.toBitVec_ofBitVec _)

theorem row_test {ret : BitVec 64} {n : Nat} (hi : i < n) (hn : n ≤ 64)
    (hw : Words m0 (varsOf sl t i) w5 d) :
    (SBool.not (.cmp .eq .W64 (.bin .add .W64 (.load 0 16 8) (.lit 1)) (.lit n))).eval
      (E m0 d (varsOf sl t i) ret) = decide (i + 1 < n) := by
  simp only [SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64, saved_row hw]
  change (!(BitVec.ofNat 64 i + BitVec.ofNat 64 1 == BitVec.ofNat 64 n)) = _
  rw [← BitVec.ofNat_add]
  by_cases he : i + 1 = n
  · simp [he]
  · have hne : BitVec.ofNat 64 (i + 1) ≠ BitVec.ofNat 64 n := by
      intro hx
      have hx' := congrArg BitVec.toNat hx
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)] at hx'
      exact he hx'
    simp [hne, show i + 1 < n by omega]

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
