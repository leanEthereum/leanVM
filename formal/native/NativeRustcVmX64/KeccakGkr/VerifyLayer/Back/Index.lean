module

public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Exec
public import NativeRustcVmX64.KeccakGkr.VerifyLayer.Model
import Mathlib.Tactic.FinCases

/-! # Bounded certificates for the weights loop's machine index arithmetic -/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model LeanVM.Protocol.Verifier

@[expose] public section

def alongRow (j n : Nat) : Nat := (j / 64 % 5 + n) % 5 + 5 * (j / 320)

def idxCol (x : BitVec 64) : BitVec 64 :=
  let l := BinOp.apply .shr .W64 x 6#64
  let q := BinOp.apply .mulhi .W64 l (BitVec.ofNat 64 3689348814741910324)
  BinOp.apply .sub .W64 l (BinOp.apply .add .W64 q (BinOp.apply .mul .W64 q 4#64))

def idxRow (x : BitVec 64) : BitVec 64 :=
  let q := BinOp.apply .shr .W64
    (BinOp.apply .mulhi .W64 x (BitVec.ofNat 64 14757395258967641293)) 8#64
  BinOp.apply .add .W64 q (BinOp.apply .mul .W64 q 4#64)

def idx4 (x : BitVec 64) : BitVec 64 :=
  let l := BinOp.apply .shr .W64 x 6#64
  let q := BinOp.apply .mulhi .W64 l (BitVec.ofNat 64 3689348814741910324)
  let f := BinOp.apply .add .W64 q (BinOp.apply .mul .W64 q 4#64)
  let n := if CmpOp.apply .eq .W64 l f then 4#64
    else BinOp.apply .add .W64
      (BinOp.apply .add .W64 (BitVec.ofNat 64 288230376151711742) (idxCol x)) 1#64
  BinOp.apply .shl .W64 (BinOp.apply .add .W64 (idxRow x) n) 6#64

def idx3 (col row : BitVec 64) : BitVec 64 :=
  BinOp.apply .shl .W64 (BinOp.apply .add .W64
    (if CmpOp.apply .ult .W64 col 2#64 then 3#64 else BitVec.ofNat 64 288230376151711742)
    (BinOp.apply .add .W64 col row)) 6#64

def indexCheck (j : Nat) : Bool :=
  idxCol (BitVec.ofNat 64 j) == BitVec.ofNat 64 (j / 64 % 5) &&
  idxRow (BitVec.ofNat 64 j) == BitVec.ofNat 64 (5 * (j / 320)) &&
  idx4 (BitVec.ofNat 64 j) == BitVec.ofNat 64 (64 * alongRow j 4) &&
  idx3 (BitVec.ofNat 64 (j / 64 % 5)) (BitVec.ofNat 64 (5 * (j / 320))) ==
    BitVec.ofNat 64 (64 * alongRow j 3)

def laneS : Sym := .bin .shr .W64 (.reg .rbp) (.lit 6)
def quotS : Sym := .bin .mulhi .W64 laneS (.lit 3689348814741910324)
def fiveS : Sym := .bin .add .W64 quotS (.bin .mul .W64 quotS (.lit 4))
def colS : Sym := .bin .sub .W64 laneS fiveS
def div320S : Sym := .bin .shr .W64
  (.bin .mulhi .W64 (.reg .rbp) (.lit 14757395258967641293)) (.lit 8)
def rowS : Sym := .bin .add .W64 div320S (.bin .mul .W64 div320S (.lit 4))
def fourS : Sym := .bin .shl .W64
  (.bin .add .W64 rowS (.ite (.cmp .eq .W64 laneS fiveS) (.lit 4)
    (.bin .add .W64 (.bin .add .W64 (.reg .r13) colS) (.lit 1)))) (.lit 6)
def threeS : Sym := .bin .shl .W64
  (.bin .add .W64 (.ite (.cmp .ult .W64 (.reg .rcx) (.lit 2)) (.lit 3) (.reg .r13))
    (.bin .add .W64 (.reg .rcx) (.reg .rax))) (.lit 6)

end

public section

theorem index_chunks (b : Fin 16) : (List.range 100).all (fun i ↦ indexCheck (100 * b.val + i)) = true := by
  fin_cases b <;> decide +kernel

theorem index_checked {j : Nat} (hj : j < 1600) : indexCheck j = true := by
  have h := List.all_eq_true.mp (index_chunks ⟨j / 100, by omega⟩) (j % 100)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  simpa only [Nat.div_add_mod] using h

theorem index_values {j : Nat} (hj : j < 1600) :
    idxCol (BitVec.ofNat 64 j) = BitVec.ofNat 64 (j / 64 % 5) ∧
    idxRow (BitVec.ofNat 64 j) = BitVec.ofNat 64 (5 * (j / 320)) ∧
    idx4 (BitVec.ofNat 64 j) = BitVec.ofNat 64 (64 * alongRow j 4) ∧
    idx3 (BitVec.ofNat 64 (j / 64 % 5)) (BitVec.ofNat 64 (5 * (j / 320))) =
      BitVec.ofNat 64 (64 * alongRow j 3) := by
  have h := index_checked hj
  simp only [indexCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem colS_eval [Labels] (env : Env) :
    colS.eval env = idxCol (env.regs .rbp) := by
  simp only [colS, fiveS, quotS, laneS, idxCol, Sym.eval]

theorem rowS_eval [Labels] (env : Env) :
    rowS.eval env = idxRow (env.regs .rbp) := by
  simp only [rowS, div320S, idxRow, Sym.eval]

theorem fourS_eval [Labels] (env : Env)
    (h : env.regs .r13 = BitVec.ofNat 64 288230376151711742) :
    fourS.eval env = idx4 (env.regs .rbp) := by
  simp only [fourS, colS, fiveS, quotS, laneS, rowS, div320S, idx4, idxCol, idxRow,
    Sym.eval, SBool.eval, h]

theorem threeS_eval [Labels] (env : Env)
    (h : env.regs .r13 = BitVec.ofNat 64 288230376151711742) :
    threeS.eval env = idx3 (env.regs .rcx) (env.regs .rax) := by
  simp only [threeS, idx3, Sym.eval, SBool.eval, h]

theorem along_eq (j n : Nat) : keccakAlong j n = 64 * alongRow j n + j % 64 := by
  simp only [keccakAlong, alongRow]
  omega

theorem alongRow_lt (j n : Nat) (hj : j < 1600) : alongRow j n < 25 := by
  unfold alongRow
  omega

end

end NativeRustcVmX64.KeccakGkr.VerifyLayer
