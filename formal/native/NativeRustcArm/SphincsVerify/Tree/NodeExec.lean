module

public import NativeRustcArm.SphincsVerify.Tree.Exec
public meta import NativeRustcArm.SphincsVerify.Tree.Exec

/-!
# The fold's node, run by the symbolic executor

A node of the fold (`b153` .. `b178`) between its calls, each stretch from a fresh state of the
frame with the kept registers (`keptRegs`): the loop head `b153` (`nodeS p`, X24 the layer's path
from node `p`, X20 the current value's copy at `21648`, X19 the height, below 10), then after each
call (`postS`, X20 as the stretch needs it): `b154 b157 b159 b160 b161` (`PK.seed` and the address
into hasher A), `b162 b158 b165` (the clone), `b166 b168 b169 b170` (the children into hasher B),
`b171 b167 b174` (B's state into A), `b175 b176` (the final block), `b177` (its XOR into A),
`b178` (the node's value, the loop's test); and the exit `b179 b181`, `b182`.
-/

namespace NativeRustcArm.SphincsVerifyProof.Tree

open NativeRustcArm.Sym NativeRustcArm.Sphincs.SphincsVerify

@[expose] public section

/-- At the loop head: X24 the layer's path from node `p`, X20 `21648`, X19 below 10. -/
def nodeS (p : Nat) : SState :=
  init [(29376, true)] (.ptr 0 0) (keptRegs ++ [(.X24, .ptr 0 ((12468 + 16 * p : Nat) : Int)), (.X20, .ptr 0 21648)])
    [] [(.reg .X19, 10)]

/-- After a call: the kept registers and `known`. -/
def postS (known : List (XReg × Sym)) : SState := init [(29376, true)] (.ptr 0 0) (keptRegs ++ known)

/-- After `memset`. -/
def s2 : SState := postS []
/-- After the address' `memcpy`: X22, X23 the bytes taken and left. -/
def s3 : SState := postS [(.X22, .lit 32), (.X23, .lit 32)]
/-- After the clone. -/
def s4 : SState := postS []
/-- After the children's `memcpy`: X22, X28 the bytes taken and left. -/
def s5 : SState := postS [(.X22, .lit 32), (.X28, .lit 32)]
/-- After the state's `memcpy`: X23 the final block's length. -/
def s6 : SState := postS [(.X23, .lit 80)]
/-- After the final block's `memcpy`: X23 its length. -/
def s7 : SState := postS [(.X23, .lit 80)]
/-- After `keccak_f`. -/
def s8 : SState := postS []

end

set_option Elab.async false

sym_block run_b153_0 := exec b153 (nodeS 0)
sym_block run_b153_8 := exec b153 (nodeS 8)
sym_block run_b153_16 := exec b153 (nodeS 16)
sym_block run_b154 := exec b154 s2
sym_block run_b157 := exec b157 (after b154 s2)
sym_block run_b159 := exec b159 (after b157 (after b154 s2))
sym_block run_b160 := exec b160 (after b159 (after b157 (after b154 s2)))
sym_block run_b161 := exec b161 (after b160 (after b159 (after b157 (after b154 s2))))
sym_block run_b162 := exec b162 s3
sym_block run_b158 := exec b158 (after b162 s3)
sym_block run_b165 := exec b165 (after b158 (after b162 s3))
sym_block run_b166 := exec b166 s4
sym_block run_b168 := exec b168 (after b166 s4)
sym_block run_b169 := exec b169 (after b168 (after b166 s4))
sym_block run_b170 := exec b170 (after b169 (after b168 (after b166 s4)))
sym_block run_b171 := exec b171 s5
sym_block run_b167 := exec b167 (after b171 s5)
sym_block run_b174 := exec b174 (after b167 (after b171 s5))
sym_block run_b175 := exec b175 s6
sym_block run_b176 := exec b176 (after b175 s6)
sym_block run_b177 := exec b177 s7
sym_block run_b178 := exec b178 s8
sym_block run_b179 := exec b179 s8
sym_block run_b181 := exec b181 (after b179 s8)
sym_block run_b182 := exec b182 (after b181 (after b179 s8))

end NativeRustcArm.SphincsVerifyProof.Tree
