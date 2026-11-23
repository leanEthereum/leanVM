module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Exit
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.First
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Run2
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back.Model

/-!
# `verify_keccak`'s back half: common facts (x86-64)

A bounds check `x < c` the code makes before a slice (`eval_ite_ult`), ranges of one region apart
(`sepR2`), the regions' bases as `off` (`ob1`, `ob2`), a claim's point in the frame
(`ClaimAt.pointAt`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.KeccakGkr.SeqZ NativeVm.Model
open NativeRustcVm.Transcript (DecArea TStateAt)
open NativeRustcVm.KeccakGkr (off ClaimAt WeightsAt)

public section

section
variable [Labels] {env : Env}

theorem eval_ult (x : Sym) {c : Nat} (hc : c < 2 ^ 64) :
    (SBool.cmp .ult .W64 x (.lit c)).eval env = decide ((x.eval env).toNat < c) := by
  show CmpOp.apply .ult .W64 (x.eval env) (BitVec.ofNat 64 c) = _
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [CmpOp.apply, low_W64]
  rw [BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

/-- **A bounds check** before a slice. -/
theorem eval_ite_ult (x a b : Sym) {c : Nat} (hc : c < 2 ^ 64) :
    (Sym.ite (.cmp .ult .W64 x (.lit c)) a b).eval env =
      if (x.eval env).toNat < c then a.eval env else b.eval env := by
  show (if (SBool.cmp .ult .W64 x (.lit c)).eval env then a.eval env else b.eval env) = _
  rw [eval_ult x hc]
  simp only [decide_eq_true_eq]

end

theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A bounds check that holds. -/
theorem eval_ite_ult_pos [Labels] {env : Env} (x a b : Sym) {c : Nat} (hc : c < 2 ^ 64)
    (h : (x.eval env).toNat < c) :
    (Sym.ite (.cmp .ult .W64 x (.lit c)) a b).eval env = a.eval env := by
  rw [eval_ite_ult x a b hc]
  simp only [h, ↓reduceIte]

theorem add64 (x y : BitVec 64) : BinOp.apply .add .W64 x y = x + y := by
  simp only [BinOp.apply, low_W64, ext_W64]

section
variable [Labels] {m0 : MachineData} {a : DecArea} {inst : Array EW}

theorem ob1 : off (ob m0 1) 0 = reg m0 .rdi := off0 _

theorem ob2 (o : Nat) : off (ob m0 2) o = off (reg m0 .r9) o := rfl

/-- Two ranges of one region apart. -/
theorem sepR2 (c : Ctx a inst m0) {i o n p l : Nat} (h1 : 1 ≤ i) (h4 : i ≤ 4) (hn : o + n ≤ rsz i)
    (hl : p + l ≤ rsz i) (hn0 : 0 < n) (hl0 : 0 < l) (h : o + n ≤ p ∨ p + l ≤ o) :
    Sep (off (ob m0 i) o).toNat n (off (ob m0 i) p).toNat l := by
  rw [offR c h1 h4 (by omega), offR c h1 h4 (by omega)]
  unfold Sep; omega

end

/-- `off` of `off` (`NativeRustcVm.KeccakGkr.off`). -/
theorem koff (b : BitVec 64) (o i : Nat) : off (off b o) i = off b (o + i) :=
  NativeRustcVm.Transcript.off_off b o i

/-- `NativeRustcVm.Transcript.off` of `off` (`NativeRustcVm.KeccakGkr.off`). -/
theorem toff (b : BitVec 64) (o i : Nat) : NativeRustcVm.Transcript.off (off b o) i = off b (o + i) :=
  NativeRustcVm.Transcript.off_off b o i

/-- **A claim's point**: its count at `pointOff`, its elements from `pointOff + 8`. -/
theorem ClaimAt.pointAt {d : Mem 64} {p : BitVec 64} {c : KeccakClaimW} (h : ClaimAt d p c) :
    c.point.size ≤ 30 ∧ NativeRustcVm.WordAt d (off p 280) c.point.size.toUInt64 ∧
      NativeRustcVm.EWsAt d (off p 288) c.point.toList := by
  obtain ⟨-, -, hl, hw, he⟩ := h
  refine ⟨by simpa [NativeRustcVm.KeccakGkr.claimPointCap] using hl,
    by simpa [NativeRustcVm.KeccakGkr.pointOff] using hw, ?_⟩
  have e : off p 280 + 8#64 = off p 288 := NativeRustcVm.Transcript.off_add _ _ _
  rw [← e]; exact he

/-- **A claim's instance weights**: their count at `muOff`, their elements from `muOff + 8`. -/
theorem ClaimAt.muAt {d : Mem 64} {p : BitVec 64} {c : KeccakClaimW} (h : ClaimAt d p c) :
    c.mu.size ≤ 16 ∧ NativeRustcVm.WordAt d (off p 16) c.mu.size.toUInt64 ∧
      NativeRustcVm.EWsAt d (off p 24) c.mu.toList := by
  obtain ⟨-, ⟨hl, hw, he⟩, -⟩ := h
  refine ⟨by simpa [NativeRustcVm.KeccakGkr.muCap] using hl,
    by simpa [NativeRustcVm.KeccakGkr.muOff] using hw, ?_⟩
  have e : off p 16 + 8#64 = off p 24 := NativeRustcVm.Transcript.off_add _ _ _
  rw [← e]; exact he

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak.Back
