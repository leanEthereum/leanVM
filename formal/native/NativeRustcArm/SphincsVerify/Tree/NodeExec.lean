module

public import NativeRustcArm.SphincsVerify.Tree.Exec
public meta import NativeRustcArm.SphincsVerify.Tree.Exec

/-!
# The fold's node, run by the symbolic executor

A node of the fold (`b144` .. `b169`) between its calls, each stretch from a fresh state of the
frame with the kept registers (`keptRegs`): the loop head `b144` (`nodeS p`, spill `432` the
layer's path from node `p`, X24 the height, below 10), then after each call (`postS`):
`b145 b148 b150 b151 b152` (`PK.seed` and the address into hasher A), `b153 b149 b156` (the clone),
`b157 b159 b160 b161` (the children into hasher B), `b162 b158 b165` (B's state into A),
`b166 b167` (the final block), `b168` (its XOR into A), `b169` (the node's value, the loop's test);
and the exit `b170 b172`, `b173`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- At the loop head: spill `432` the layer's path from node `p`, X24 below 10. -/
def nodeS (p : Nat) : SState :=
  { init [(21616, true)] (.ptr 0 0) keptRegs [] [(.reg .X24, 10)] with
    mem := [⟨0, 432, 8, .ptr 0 ((4708 + 16 * p : Nat) : Int)⟩] }

/-- After a call: the kept registers and `known`. -/
def postS (known : List (XReg × Sym)) : SState := init [(21616, true)] (.ptr 0 0) (keptRegs ++ known)

/-- After `memset`. -/
def s2 : SState := postS []
/-- After the address' `memcpy`: X22, X23 the bytes taken and left. -/
def s3 : SState := postS [(.X22, .lit 32), (.X23, .lit 32)]
/-- After the clone. -/
def s4 : SState := postS []
/-- After the children's `memcpy`: X22, X26 the bytes taken and left. -/
def s5 : SState := postS [(.X22, .lit 32), (.X26, .lit 32)]
/-- After the state's `memcpy`: X23 the final block's length. -/
def s6 : SState := postS [(.X23, .lit 80)]
/-- After the final block's `memcpy`: X23 its length. -/
def s7 : SState := postS [(.X23, .lit 80)]
/-- After `keccak_f`. -/
def s8 : SState := postS []

end

set_option Elab.async false

sym_block run_b144_0 := exec b144 (nodeS 0)
sym_block run_b144_8 := exec b144 (nodeS 8)
sym_block run_b144_16 := exec b144 (nodeS 16)
sym_block run_b145 := exec b145 s2
sym_block run_b148 := exec b148 (after b145 s2)
sym_block run_b150 := exec b150 (after b148 (after b145 s2))
sym_block run_b151 := exec b151 (after b150 (after b148 (after b145 s2)))
sym_block run_b152 := exec b152 (after b151 (after b150 (after b148 (after b145 s2))))
sym_block run_b153 := exec b153 s3
sym_block run_b149 := exec b149 (after b153 s3)
sym_block run_b156 := exec b156 (after b149 (after b153 s3))
sym_block run_b157 := exec b157 s4
sym_block run_b159 := exec b159 (after b157 s4)
sym_block run_b160 := exec b160 (after b159 (after b157 s4))
sym_block run_b161 := exec b161 (after b160 (after b159 (after b157 s4)))
sym_block run_b162 := exec b162 s5
sym_block run_b158 := exec b158 (after b162 s5)
sym_block run_b165 := exec b165 (after b158 (after b162 s5))
sym_block run_b166 := exec b166 s6
sym_block run_b167 := exec b167 (after b166 s6)
sym_block run_b168 := exec b168 s7
sym_block run_b169 := exec b169 s8
sym_block run_b170 := exec b170 s8
sym_block run_b172 := exec b172 (after b170 s8)
sym_block run_b173 := exec b173 (after b172 (after b170 s8))

end NativeRustcArm.SphincsVerifyProof.Tree
