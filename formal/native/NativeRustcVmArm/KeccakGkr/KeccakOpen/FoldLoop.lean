module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldRowL

/-!
# `keccak_open`'s fold: the looped rounds' tools

The source rows' addresses (`ev_src0`, `ev_src1`); the registers after a row (`kN`), the next
row's (`kO_next`); a round's start (`kS1`, `kO_zero`); the block closing a row (`rowTail`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- After a looped round's row (`b10`, `b17`): the row and its offset advanced. -/
def kN : List (XReg × Sym) :=
  [(.X26, .bin .add .W64 (.var 2) (.lit 1)), (.X25, .bin .add .W64 (.var 3) (.lit 1024)),
    (.X29, P), (.X27, A0), (.X28, B0), (.X22, V0), (.X23, V1)]

/-- After `b11`: round 1's start. -/
def kS1 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X25, .lit 0), (.X26, .lit 0), (.X27, A0), (.X28, B0), (.X29, P)]

/-- A looped round's inner loop's registers. -/
def kLp : List (XReg × Sym) := (.X24, .bin .add .W64 P (.var 3)) :: kOE

/-- A looped round's test: the next row is not `n`. -/
def rowEnd (n : Nat) : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.var 2) (.lit 1)) (.lit n))

end

public section

theorem shl11 (x : BitVec 64) : x <<< 11 = BitVec.ofNat 64 (2048 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem mem_kO {p : XReg × Sym} (hp : p ∈ kO) :
    p = (.X29, P) ∨ p = (.X27, A0) ∨ p = (.X28, B0) ∨ p = (.X22, V0) ∨ p = (.X23, V1) ∨
      p = (.X26, .var 2) ∨ p = (.X25, .var 3) := by
  simpa [kO] using hp

section
variable [Labels] {m0 st : MachineData} {sl : Array EW} {t i : Nat}

theorem ev_src0 (hi : i < 64) :
    src0.eval (Env.ofMachine m0 (envR m0) (varsOf sl t i)) =
      rwA m0 + BitVec.ofNat 64 (1024 * (2 * i)) := by
  show BinOp.apply .add .W64 (rwA m0 + BitVec.ofInt 64 0)
    (UnOp.apply (.shift .LSL 11) .W64 (BitVec.ofNat 64 i)) = _
  simp only [BinOp.apply, UnOp.apply, low_W64, ext_W64, shiftW]
  rw [ofInt0, NativeRustcVm.addr_add_zero, shl11, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), show 2048 * i = 1024 * (2 * i) by omega]

theorem ev_src1 (hi : i < 64) :
    (Sym.bin .add .W64 src0 (.lit 1024)).eval (Env.ofMachine m0 (envR m0) (varsOf sl t i)) =
      rwA m0 + BitVec.ofNat 64 (1024 * (2 * i + 1)) := by
  show BinOp.apply .add .W64 (src0.eval _) (BitVec.ofNat 64 1024) = _
  rw [ev_src0 hi]
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [NativeRustcVm.addr_add_add, show 1024 * (2 * i) + 1024 = 1024 * (2 * i + 1) by omega]

/-- **The next row's registers.** -/
theorem kO_next (hk : KAt m0 (varsOf sl t i) kN st) : KAt m0 (varsOf sl t (i + 1)) kO st := by
  refine KAt.of_reg hk.1 fun p hp ↦ ?_
  rcases mem_kO hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hk.reg (memK (show inK .X29 P kN = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X27 A0 kN = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X28 B0 kN = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X22 V0 kN = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X23 V1 kN = true by decide))).trans rfl
  · refine (hk.reg (memK (show inK .X26 (.bin .add .W64 (.var 2) (.lit 1)) kN = true
      by decide))).trans ?_
    show BinOp.apply .add .W64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 1) = BitVec.ofNat 64 (i + 1)
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.ofNat_add]
  · refine (hk.reg (memK (show inK .X25 (.bin .add .W64 (.var 3) (.lit 1024)) kN = true
      by decide))).trans ?_
    show BinOp.apply .add .W64 (BitVec.ofNat 64 (1024 * i)) (BitVec.ofNat 64 1024) =
      BitVec.ofNat 64 (1024 * (i + 1))
    simp only [BinOp.apply, low_W64, ext_W64]
    rw [← BitVec.ofNat_add, Nat.mul_succ]

/-- **A round's first row's registers.** -/
theorem kO_zero (hk : KAt m0 (varsOf sl t 0) kS1 st) : KAt m0 (varsOf sl t 0) kO st := by
  refine KAt.of_reg hk.1 fun p hp ↦ ?_
  rcases mem_kO hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hk.reg (memK (show inK .X29 P kS1 = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X27 A0 kS1 = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X28 B0 kS1 = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X22 V0 kS1 = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X23 V1 kS1 = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X26 (.lit 0) kS1 = true by decide))).trans rfl
  · exact (hk.reg (memK (show inK .X25 (.lit 0) kS1 = true by decide))).trans rfl

end

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData}

/-- **The block closing a looped round's row**: the next row, or the round done. -/
theorem rowTail (hp : Placed code k) (ok : Ok c.a m0) {t i n : Nat} (ht : t < 6)
    (hi : i < n) (hn : n ≤ 64) {bT : List Directive} {kT kA : Nat}
    (hin : bT.IsInfixAt code kT) (hne : bT ≠ []) {ST : SState} {lbl : Label}
    (hx : exec bT (pS kOE) = some (ST, .cond (rowEnd n) lbl)) (hmem : ST.mem = [])
    (hok : regsOk t ST kN = true) (hlbl : Labels.label lbl = Host.addrOf (k + kA))
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + kT)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl t i) kOE s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      ((i + 1 < n ∧ s'.pc = Host.addrOf (k + kA)) ∨
        (i + 1 = n ∧ s'.pc = Host.addrOf (k + kT + bT.length))) ∧
      Mid c m0 s'.data ∧ KAt m0 (varsOf c.sl t (i + 1)) kO s'.data ∧
      s'.data.dmem = s.data.dmem) s := by
  have hsl : t < c.sl.size := by rw [hmid.sl_size]; exact ht
  refine (zeroBlock hp ok (by decide) hsl rfl rfl hin hne hx hmem hok hpc hmid hk).mono
    fun s' ⟨hpc', hmid', hk', hd'⟩ ↦ ⟨?_, hmid', kO_next hk', hd'⟩
  simp only [PcOk] at hpc'
  have hc : SBool.eval (Env.ofMachine s.data (envR m0) (varsOf c.sl t i)) (rowEnd n) =
      decide (i + 1 ≠ n) := by
    have e2 : (Env.ofMachine s.data (envR m0) (varsOf c.sl t i)).vars 2 = BitVec.ofNat 64 i :=
      rfl
    simp only [rowEnd, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [e2, ← BitVec.ofNat_add]
    by_cases h : i + 1 = n
    · subst h
      simp
    · have : (BitVec.ofNat 64 (i + 1) == BitVec.ofNat 64 n) = false := by
        rw [beq_eq_false_iff_ne]
        intro he
        have := congrArg BitVec.toNat he
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
        omega
      simp [this, h]
  rw [hc] at hpc'
  by_cases h : i + 1 = n
  · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc'
    exact Or.inr ⟨h, hpc'⟩
  · simp only [ne_eq, h, not_false_eq_true, decide_true, ↓reduceIte] at hpc'
    exact Or.inl ⟨by omega, hpc'.trans hlbl⟩

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
