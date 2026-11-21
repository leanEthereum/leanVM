module

public import NativeVm.Field.Basic

/-!
# `K` on the machine

`kmul`: `rax := rax · rbx` in `K = GF(2^64)`, by the bits of `rax` from the lowest, adding `rbx`
masked by each and multiplying `rbx` by `x` (`mulXW`) between them; `ksq`: `rax := rax²`.
Both write `rax`, `rbx`, `rcx`, `r8` and no memory.
-/

@[expose] public section

namespace NativeVm.Field

open Native LeanVM.Parameters

/-- `rax := rax · rbx` in `K`; the sum in `rcx`, `r8` a temporary. -/
def kmul : Stmt := blk [
  I (.movi .rcx 0),
  .loop (.test false .rax (.reg .rax)) (blk [
    I (.mov .r8 .rax), I (.andi .r8 1), I (.neg .r8), I (.and .r8 .rbx), I (.xor .rcx .r8),
    I (.mov .r8 .rbx), I (.sari .r8 63), I (.andi .r8 0x1B), I (.shli .rbx 1), I (.xor .rbx .r8),
    I (.shri .rax 1)]),
  I (.mov .rax .rcx)]

/-- The registers `kmul` and `ksq` write. -/
abbrev kRegs : List Reg64 := [.rax, .rbx, .rcx, .r8]

theorem toNat_shiftRight_one_lt {x : UInt64} (h : x ≠ 0) : (x >>> 1).toNat < x.toNat := by
  have : x.toNat ≠ 0 := fun h0 ↦ h (UInt64.toNat_inj.mp (by simpa using h0))
  rw [UInt64.toNat_shiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  change x.toNat / 2 ^ 1 < _
  omega

theorem mulXW_unfold (t : UInt64) :
    (t <<< 1) ^^^ (UInt64.ofBitVec (t.toBitVec.sshiftRight 63) &&& 0x1B) = mulXW t := (rfl)

/-- **`kmul` multiplies in `K`.** -/
theorem kmul_spec (s : QState) {E : QState → Prop} :
    WP kmul s (fun s' ↦ K.ofLane (s'.reg .rax) = K.ofLane (s.reg .rax) * K.ofLane (s.reg .rbx) ∧
      s'.mem = s.mem ∧ RegsFrame kRegs s s') E := by
  unfold kmul
  fstep
  apply WP.blk_cons
  apply WP.loop (fun t ↦ K.ofLane (t.reg .rcx) + K.ofLane (t.reg .rax) * K.ofLane (t.reg .rbx) =
      K.ofLane (s.reg .rax) * K.ofLane (s.reg .rbx) ∧ t.mem = s.mem ∧ RegsFrame kRegs s t)
    (fun t ↦ (t.reg .rax).toNat)
  · refine ⟨?_, rfl, by rf_tac⟩
    simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, ofLane_zero, zero_add]
  · intro t ⟨hI, hm, hf⟩ hc
    have hne : t.reg .rax ≠ 0 := by simpa [Cond.eval, Rhs.eval] using hc
    fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep; fstep
    fdone
    refine ⟨⟨?_, hm, by rf_tac; exact hf⟩, toNat_shiftRight_one_lt hne⟩
    rw [mulXW_unfold, ← hI, ofLane_xor, ofLane_mask, ofLane_mulXW, ofLane_bit (t.reg .rax)]
    ring
  · intro t ⟨hI, hm, hf⟩ hc
    have h0 : t.reg .rax = 0 := by simpa [Cond.eval, Rhs.eval] using hc
    fstep
    fdone
    refine ⟨?_, hm, by rf_tac; exact hf⟩
    rw [← hI, h0, ofLane_zero, zero_mul, add_zero]

/-- `rax := rax²` in `K`. -/
def ksq : Stmt := blk [I (.mov .rbx .rax), kmul]

/-- **`ksq` squares in `K`.** -/
theorem ksq_spec (s : QState) {E : QState → Prop} :
    WP ksq s (fun s' ↦ K.ofLane (s'.reg .rax) = K.ofLane (s.reg .rax) ^ 2 ∧
      s'.mem = s.mem ∧ RegsFrame kRegs s s') E := by
  unfold ksq
  fstep
  refine WP.then (kmul_spec _) fun t ⟨h1, h2, h3⟩ ↦ ?_
  fdone
  refine ⟨?_, h2, ?_⟩
  · rw [h1, sq]
    simp
  · exact RegsFrame.trans (by rf_tac) h3

end NativeVm.Field
