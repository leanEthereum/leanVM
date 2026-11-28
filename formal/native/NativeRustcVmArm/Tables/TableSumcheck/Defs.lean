module

public import NativeRustcVmArm.Tables.TableSumcheck.Facts
public import NativeRustcVmArm.Tables.TableSumcheck.Model
public import NativeRustcVmArm.Tables.Frame

/-!
# `table_sumcheck`: the proofs' shared terms

The outputs (`outs`: the `TState` at X0, the evaluations at X7), the model's result (`res`), what
the function reaches (`Goal`); `lsr #1`, `lsl #4` and a negative offset as numbers.
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables

@[expose] public section

/-- The outputs: the `TState` (X0) and the evaluations (X7). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec tstateBytes q ∨ InRange m0.regs.X7.toBitVec tableEvalsBytes q

/-- The model's result. -/
def res (s : TState) (heights : Array Nat) (bus : BusResultW) (m0 : MachineData) :
    Option (Array (Array EW × Array EW) × TState) :=
  (tableSumcheck heights bus.forms (arrE m0 m0.regs.X3 2) (arrE m0 m0.regs.X4 3) bus.point
    ⟨m0.regs.X5, m0.regs.X6⟩).run s

/-- What `table_sumcheck` reaches. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (heights : Array Nat) (bus : BusResultW)
    (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ TableSumcheckPost a s heights bus m0 st.data

/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := base m0 720

/-- The registers from `b1` on: the arguments in callee-saved registers, `n` in X25. -/
structure Regs (m0 m : MachineData) (n : Nat) : Prop where
  x19 : m.regs.getXReg .X19 = m0.regs.X2
  x20 : m.regs.getXReg .X20 = m0.regs.X4
  x21 : m.regs.getXReg .X21 = m0.regs.X1
  x22 : m.regs.getXReg .X22 = m0.regs.X3
  x23 : m.regs.getXReg .X23 = m0.regs.X0
  x24 : m.regs.getXReg .X24 = m0.regs.X7
  x25 : (m.regs.getXReg .X25).toNat = n

end

public section

theorem N_ge [Labels] : 720 ≤ tableSumcheckStack := by unfold tableSumcheckStack; omega

/-- Registers kept: the same `Regs`. -/
theorem Regs.of {m0 m m' : MachineData} {n : Nat} (h : Regs m0 m n)
    (hk : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25],
      m'.regs.getXReg r = m.regs.getXReg r) : Regs m0 m' n where
  x19 := (hk .X19 (by simp)).trans h.x19
  x20 := (hk .X20 (by simp)).trans h.x20
  x21 := (hk .X21 (by simp)).trans h.x21
  x22 := (hk .X22 (by simp)).trans h.x22
  x23 := (hk .X23 (by simp)).trans h.x23
  x24 := (hk .X24 (by simp)).trans h.x24
  x25 := by rw [hk .X25 (by simp)]; exact h.x25

/-- **The `TState`** across changes in the function's stack. -/
theorem tstate_keep [Labels] {m0 : MachineData} {t : BitVec 64} {a : DecArea} {N F : Nat}
    (c : Sumcheck.Ctx m0 t a N F) {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → InRange (stackBelow m0 N) N q) {d d' : DataMem} {s : TState}
    (hts : TStateAt d t a s) (hk : Kept d d') (hs : SameOutside d d' R) : TStateAt d' t a s := by
  have hnw : NoWrap (stackBelow m0 N) N := by
    unfold NoWrap; rw [c.stk]; have := c.spN; have := Sumcheck.Ctx.sp_lt m0; omega
  exact hts.frame hk (fun q hq ↦ ⟨NativeRustcVm.Apart.not_inRange c.tok.1.symm hnw c.fp.1.2
    (hR q hq), NativeRustcVm.Apart.not_inRange c.tok.2.1.symm hnw c.fp.2.1.2 (hR q hq)⟩) hs

/-- A register a block kept, from the block's list. -/
theorem reg_keep {S : SState} {L : List XReg}
    (h : L.all (fun r ↦ S.reg r == some (.reg r)) = true) {r : XReg} (hr : r ∈ L) :
    S.reg r = some (.reg r) :=
  beq_iff_eq.mp (List.all_eq_true.mp h r hr)

/-- `x - 1 == 0` of a word at least `1`. -/
theorem sub1_beq (x : BitVec 64) (h : 1 ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 1) == BitVec.ofNat 64 0) = decide (x.toNat = 1) := by
  have e := sub_lit x 1 h
  by_cases h1 : x.toNat = 1
  · simp only [h1, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [e, h1]; rfl
  · simp only [h1, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h2
    have := congrArg BitVec.toNat h2
    rw [e] at this
    simp at this
    omega

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `lsr #1`. -/
theorem lsr1 (x : BitVec 64) : (UnOp.apply (.ubfm 1 63) .W64 x).toNat = x.toNat / 2 := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64]
  simp [evalUBFM, toNat_take', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- `lsl #4`. -/
theorem lsl4 (x : BitVec 64) (h : x.toNat < 2 ^ 59) :
    (UnOp.apply (.shift .LSL 4) .W64 x).toNat = 16 * x.toNat := by
  simp only [UnOp.apply, Sym.ext_W64, Sym.low_W64, shiftW]
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- A pointer's negative offset. -/
theorem add_ofInt_neg (a : BitVec 64) {n c : Nat} (h : c ≤ n) :
    a + BitVec.ofNat 64 n + BitVec.ofInt 64 (-(c : Int)) = a + BitVec.ofNat 64 (n - c) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- The frame's base, as a number. -/
theorem fb_toNat {m0 : MachineData} {N : Nat} (hS : StackOk m0 N) (hN : 720 ≤ N) :
    (fb m0).toNat = m0.regs.SP.toNat - 720 :=
  base_toNat (by have := hS.2.1; omega)

/-- The frame's byte `o`, as a number. -/
theorem fb_add {m0 : MachineData} {N : Nat} (hS : StackOk m0 N) (hN : 720 ≤ N) {o : Nat}
    (ho : o ≤ 720) : (fb m0 + BitVec.ofNat 64 o).toNat = (fb m0).toNat + o := by
  have h1 := fb_toNat hS hN
  have h2 := m0.regs.SP.toNat_lt
  have h3 := hS.2.1
  exact NativeRustcVm.toNat_add_ofNat (by omega)

/-- The frame's bytes from `o` do not wrap. -/
theorem noWrap_fb {m0 : MachineData} {N : Nat} (hS : StackOk m0 N) (hN : 720 ≤ N) {o n : Nat}
    (h : o + n ≤ 720) : NoWrap (fb m0 + BitVec.ofNat 64 o) n := by
  unfold NoWrap
  rw [fb_add hS hN (by omega), fb_toNat hS hN]
  have := m0.regs.SP.toNat_lt
  have := hS.2.1
  omega

/-- A byte of the frame's `n` bytes from `o`, in its `n'` bytes from `o' ≤ o`. -/
theorem inRange_fb {m0 : MachineData} {N : Nat} (hS : StackOk m0 N) (hN : 720 ≤ N)
    {o n o' n' : Nat} (h1 : o' ≤ o) (h2 : o + n ≤ o' + n') (h3 : o' + n' ≤ 720) {q : BitVec 64}
    (hq : InRange (fb m0 + BitVec.ofNat 64 o) n q) : InRange (fb m0 + BitVec.ofNat 64 o') n' q := by
  rw [Sym.inRange_iff (noWrap_fb hS hN (by omega)), fb_add hS hN (by omega)] at hq
  rw [Sym.inRange_iff (noWrap_fb hS hN h3), fb_add hS hN (by omega)]
  omega

/-- A byte of the frame is in the function's stack. -/
theorem fb_stack {m0 : MachineData} {N : Nat} (hS : StackOk m0 N) (hN : 720 ≤ N) {o n : Nat}
    (h : o + n ≤ 720) {q : BitVec 64} (hq : InRange (fb m0 + BitVec.ofNat 64 o) n q) :
    InRange (base m0 N) N q := by
  have h0 := inRange_fb hS hN (o' := 0) (n' := 720) (by omega) (by omega) (by omega) hq
  rw [NativeRustcVm.addr_add_zero] at h0
  exact Bus.frame_inRange hS.2.1 hN h0

end

end NativeRustcVmArm.Tables.TableSumcheck
