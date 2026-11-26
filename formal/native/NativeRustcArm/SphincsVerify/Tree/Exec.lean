module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Sphincs.SphincsVerify
public meta import NativeRustcArm.Code.Sphincs.SphincsVerify

/-!
# The tree region's blocks, run by the symbolic executor

Each run starts from a fresh state of the frame (region 0, SP its base, X29 the saved registers'
address) with the registers the region keeps known: `wotsS` for the one-time leaf's `th` with
calls (`b134` .. `b139`, each ending in a call) and the path's checks (`b140` .. `b143`, run in
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

/-- The registers every state of the region keeps: `136`, the hashers' buffers, X27, X29. -/
def keptRegs : List (XReg × Sym) :=
  [(.X19, .lit 136), (.X21, .ptr 0 19208), (.X25, .ptr 0 8840), (.X27, .ptr 0 19008),
    (.X29, .ptr 0 21520)]

/-- The frame (region 0), SP its base, the kept registers. -/
def wotsS : SState := init [(21616, true)] (.ptr 0 0) keptRegs

end

set_option Elab.async false

sym_block run_b134 := exec b134 wotsS
sym_block run_b135 := exec b135 wotsS
sym_block run_b136 := exec b136 wotsS
sym_block run_b137 := exec b137 wotsS
sym_block run_b138 := exec b138 wotsS
sym_block run_b139 := exec b139 wotsS
sym_block run_b140 := exec b140 wotsS
sym_block run_b141 := exec b141 (after b140 wotsS)
sym_block run_b142 := exec b142 (after b141 (after b140 wotsS))
sym_block run_b143 := exec b143 (after b142 (after b141 (after b140 wotsS)))

end NativeRustcArm.SphincsVerifyProof.Tree
