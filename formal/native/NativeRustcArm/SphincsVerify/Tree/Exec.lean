module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The tree region's blocks, run by the symbolic executor

Each run starts from a fresh state of the frame (region 0, SP its base, X29 the saved registers'
address) with the registers the region keeps known: `wotsS` for the one-time leaf's `th` with
calls (`b143` .. `b148`, each ending in a call) and the path's checks (`b149` .. `b152`, run in
one environment: `after ds S` is the state `exec ds S` ends in).
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

/-- The registers every state of the region keeps: the hashers' buffers, `136`, X29. -/
def keptRegs : List (XReg × Sym) :=
  [(.X21, .ptr 0 26968), (.X25, .ptr 0 16600), (.X26, .lit 136), (.X29, .ptr 0 29280)]

/-- The frame (region 0), SP its base, the kept registers. -/
def wotsS : SState := init [(29376, true)] (.ptr 0 0) keptRegs

end

set_option Elab.async false

sym_block run_b143 := exec b143 wotsS
sym_block run_b144 := exec b144 wotsS
sym_block run_b145 := exec b145 wotsS
sym_block run_b146 := exec b146 wotsS
sym_block run_b147 := exec b147 wotsS
sym_block run_b148 := exec b148 wotsS
sym_block run_b149 := exec b149 wotsS
sym_block run_b150 := exec b150 (after b149 wotsS)
sym_block run_b151 := exec b151 (after b150 (after b149 wotsS))
sym_block run_b152 := exec b152 (after b151 (after b150 (after b149 wotsS)))

end NativeRustcArm.SphincsVerifyProof.Tree
