module

public import NativeRustcVmX64.Whir.BasisWEval.Entry

/-!
# `BasisW::eval`: the loop's states, the values the blocks compute (x86-64)

`Mid i j`: at `NativeRustcVmX64.Vm.BasisWEval.label_6` (`b11`, `j = i`) before column claim `i`, or at `NativeRustcVmX64.Vm.BasisWEval.label_15`
(`b10`, `j = i + 1`) after it: the running sum over the weights met after `j` claims, R12 16 bytes
into claim `i`, RBX the claims' bytes from claim `i` on, RCX the placements' address (kept at the
frame's `104` too). `End`: after the column claims (`NativeRustcVmX64.Vm.BasisWEval.label_10`, `b21`).

The symbolic values of `Exec` evaluated: the counts the blocks clamp to their caps (`rcx4`,
`r84`, `rcx16`, `r816`, `rdi24`, `rsi24`, `rbx7`, `r127`), the branch conditions (`c7`, `c10`,
`c11`, `c12`, `cScale`), the placement entry's address (`placeSym`, `pentSym`).
-/

namespace NativeRustcVmX64.Whir.BasisWEval

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVmX64.Vm.BasisWEval
open NativeRustcVm.Transcript (off off_add off_zero toNat_off)
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- **In the loop**: before column claim `i` (`j = i`) or after it (`j = i + 1`). -/
structure Mid (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (i j : Nat)
    (d : MachineData) : Prop where
  base : Base m0 ba 24 d
  w56 : FW m0 d 56 (reg m0 .rsi)
  w104 : FW m0 d 104 (off ba.layout 120)
  acc : Acc m0 ba b (ws v (xpt m0) j) d
  ilt : i < v.cs.size
  rbx : (reg d .rbx).toNat = 608 * (v.cs.size - i)
  r12 : reg d .r12 = off ba.claims (24 + 608 * i)
  rcx : reg d .rcx = off ba.layout 120

/-- **After the column claims** (`b21`). -/
structure End (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (d : MachineData) :
    Prop where
  base : Base m0 ba 24 d
  w56 : FW m0 d 56 (reg m0 .rsi)
  acc : Acc m0 ba b (ws v (xpt m0) v.cs.size) d

end

public section

/-! ## Counts -/

theorem ult_lit {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) :
    CmpOp.apply .ult .W64 x (BitVec.ofNat 64 n) = decide (x.toNat < n) := by
  simp only [CmpOp.apply, low_W64]
  exact ult_ofNat hn

theorem eq_lit {x : BitVec 64} {n : Nat} (hn : n < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  simp only [CmpOp.apply, low_W64]
  rw [bv_beq_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem eq_reg {x y : BitVec 64} : CmpOp.apply .eq .W64 x y = decide (x.toNat = y.toNat) := by
  simp only [CmpOp.apply, low_W64]
  rw [bv_beq_toNat]

variable [Labels] {env : Env}

/-- A count below `37`: the point's address. -/
theorem rcx4_eval {c K : BitVec 64} (h1 : env.load 2 0 8 = c) (h2 : env.load 1 32 8 = K)
    (hc : c.toNat < 37) : rcx4.eval env = off K 8 := by
  simp only [rcx4, Sym.eval, SBool.eval, BinOp.apply, low_W64, ext_W64, h1, h2,
    ult_lit (show 37 < 2 ^ 64 by decide), decide_eq_true hc, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  exact BitVec.add_comm _ _

theorem r84_eval {c : BitVec 64} (h1 : env.load 2 0 8 = c) (hc : c.toNat < 37) :
    r84.eval env = c := by
  simp only [r84, Sym.eval, SBool.eval, h1, ult_lit (show 37 < 2 ^ 64 by decide),
    decide_eq_true hc, ↓reduceIte]

theorem rcx16_eval (hc : (env.load 1 8 8).toNat < 37) :
    rcx16.eval env = (Sym.ptr 1 16).eval env := by
  simp only [rcx16, Sym.eval, SBool.eval, ult_lit (show 37 < 2 ^ 64 by decide),
    decide_eq_true hc, ↓reduceIte]

theorem r816_eval (hc : (env.load 1 8 8).toNat < 37) : r816.eval env = env.load 1 8 8 := by
  simp only [r816, Sym.eval, SBool.eval, ult_lit (show 37 < 2 ^ 64 by decide),
    decide_eq_true hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem rdi24_eval {c Z : BitVec 64} (h1 : env.load 2 0 8 = c) (h2 : env.load 1 48 8 = Z)
    (hc : c.toNat < 31) : rdi24.eval env = off Z 8 := by
  simp only [rdi24, Sym.eval, SBool.eval, BinOp.apply, low_W64, ext_W64, h1, h2,
    ult_lit (show 31 < 2 ^ 64 by decide), decide_eq_true hc, ↓reduceIte]
  exact BitVec.add_comm _ _

theorem rsi24_eval {c : BitVec 64} (h1 : env.load 2 0 8 = c) (hc : c.toNat < 31) :
    rsi24.eval env = c := by
  simp only [rsi24, Sym.eval, SBool.eval, h1, ult_lit (show 31 < 2 ^ 64 by decide),
    decide_eq_true hc, ↓reduceIte]

omit [Labels] in
theorem mul608 {n : Nat} (hn : n ≤ 160) :
    (BinOp.apply .mul .W64 n.toUInt64.toBitVec (BitVec.ofNat 64 608)).toNat = 608 * n := by
  simp only [BinOp.apply, low_W64, ext_W64]
  rw [BitVec.toNat_mul, toNat_bv_toUInt64 (by omega), BitVec.toNat_ofNat]
  omega

/-- The claims' bytes. -/
theorem rbx7_eval {n : Nat} (h1 : env.load 2 0 8 = n.toUInt64.toBitVec) (hn : n ≤ 160) :
    (rbx7.eval env).toNat = 608 * n := by
  simp only [rbx7, Sym.eval, SBool.eval, h1, ult_lit (show 161 < 2 ^ 64 by decide),
    toNat_bv_toUInt64 (show n < 2 ^ 64 by omega), decide_eq_true (show n < 161 by omega),
    ↓reduceIte]
  exact mul608 hn

theorem r127_eval {n : Nat} {C : BitVec 64} (h1 : env.load 2 0 8 = n.toUInt64.toBitVec)
    (h2 : env.load 1 40 8 = C) (hn : n ≤ 160) : r127.eval env = off C 8 := by
  simp only [r127, Sym.eval, SBool.eval, BinOp.apply, low_W64, ext_W64, h1, h2,
    ult_lit (show 161 < 2 ^ 64 by decide), toNat_bv_toUInt64 (show n < 2 ^ 64 by omega),
    decide_eq_true (show n < 161 by omega), ↓reduceIte]
  exact BitVec.add_comm _ _

theorem c7_eval {n : Nat} (h1 : env.load 2 0 8 = n.toUInt64.toBitVec) (hn : n ≤ 160) :
    c7.eval env = decide (n = 0) := by
  have e := rbx7_eval h1 hn
  simp only [c7, SBool.eval, Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  rw [eq_lit (by decide), e]
  simp only [decide_eq_decide]
  omega

/-- `addq $-608, %rbx; je`. -/
theorem c10_eval {N i : Nat} (hx : (env.regs .rbx).toNat = 608 * (N - i)) (hi : i < N)
    (hN : N ≤ 160) :
    c10.eval env = decide (i + 1 = N) ∧
      ((Sym.bin .add .W64 (.lit 18446744073709551008) (.reg .rbx)).eval env).toNat =
        608 * (N - (i + 1)) := by
  have e : ((Sym.bin .add .W64 (.lit 18446744073709551008) (.reg .rbx)).eval env).toNat =
      608 * (N - (i + 1)) := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat]
    omega
  refine ⟨?_, e⟩
  simp only [c10, SBool.eval]
  rw [show (Sym.lit 0).eval env = BitVec.ofNat 64 0 from rfl, eq_lit (by decide), e]
  simp only [decide_eq_decide]
  omega

/-- `cmpq $158, %rax; jae`. -/
theorem c11_eval {c : Nat} (h1 : env.load 1 0 8 = c.toUInt64.toBitVec) (hc : c < 2 ^ 64) :
    c11.eval env = !decide (c < 158) := by
  simp only [c11, SBool.eval, Sym.eval, h1, ult_lit (show 158 < 2 ^ 64 by decide),
    toNat_bv_toUInt64 hc]

/-- `cmpq $0, (%rcx,%rax,8); je`. -/
theorem c12_eval {w : BitVec 64} (h1 : env.load 1 0 8 = w) :
    c12.eval env = decide (w.toNat = 0) := by
  simp only [c12, SBool.eval, Sym.eval, h1, eq_lit (show 0 < 2 ^ 64 by decide)]

/-- `cmpq %rbp, %r13; je`: the scales run out. -/
theorem cScale_eval {ba : BasisAddrs} {j : Nat} (h13 : env.regs .r13 = sA ba (min j ba.count))
    (hbp : env.regs .rbp = sA ba ba.count) (hnw : NativeRustcVm.NoWrap ba.scales (16 * ba.count))
    (hpos : 0 < ba.scales.toNat ∨ ba.scales.toNat + 16 * ba.count < 2 ^ 64) :
    cScale.eval env = decide (ba.count ≤ j) := by
  simp only [cScale, SBool.eval, Sym.eval, h13, hbp, eq_reg]
  rw [← bv_beq_toNat]
  exact scale_beq hnw hpos

/-- `leaq (%rax,%rax,2), %rax`: three times the column. -/
theorem col3_eval {c : Nat} (h : env.regs .rax = c.toUInt64.toBitVec) (hc : c < 158) :
    (col3.eval env).toNat = 3 * c := by
  simp only [col3, Sym.eval, BinOp.apply, low_W64, ext_W64, h]
  rw [BitVec.toNat_add, BitVec.toNat_mul, toNat_bv_toUInt64 (by omega), BitVec.toNat_ofNat]
  omega

omit [Labels] in
/-- An entry of the placements: `L + 120` plus `8` times three times the column. -/
theorem off_place {L x : BitVec 64} {c : Nat} (hx : x.toNat = 3 * c) :
    off L 120 + x * BitVec.ofNat 64 8 = off L (120 + 24 * c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, hx]
  omega

/-- The placement entry `b12` reads. -/
theorem placeSym_eval {c : Nat} {L : BitVec 64} (h1 : env.regs .rcx = off L 120)
    (h2 : env.regs .rax = c.toUInt64.toBitVec) (hc : c < 158) :
    placeSym.eval env = off L (120 + 24 * c) := by
  simp only [placeSym, Sym.eval, BinOp.apply, low_W64, ext_W64, h1]
  exact off_place (col3_eval h2 hc)

/-- The placement entry `b13` reads. -/
theorem pentSym_eval {c : Nat} {L : BitVec 64} (h1 : env.regs .rcx = off L 120)
    (h2 : (env.regs .rax).toNat = 3 * c) :
    pentSym.eval env = off L (120 + 24 * c) := by
  simp only [pentSym, Sym.eval, BinOp.apply, low_W64, ext_W64, h1]
  exact off_place h2

end

end NativeRustcVmX64.Whir.BasisWEval
