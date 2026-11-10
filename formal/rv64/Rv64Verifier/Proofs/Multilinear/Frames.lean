import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Proofs.EqEval

/-!
# Doubleword frames of the leaf contracts

`mul`'s and `eq_eval`'s contracts frame doublewords (`MulPost.frame`, `EqEval.Post.frame`); as
`DwFrame`s they compose with byte frames (`DwFrame.of_byte`) and block frames
(`DwFrame.of_mem`).
-/

namespace Rv64Verifier.MultilinearWords
open RiscvZkvm.Rv64 Rv64Verifier.Contracts

theorem MulPost.dwFrame {u v : MachineState} (h : MulPost u v) :
    DwFrame u v fun a ↦ Within a (u.getReg .x10) 24 ∨ Within a (stackLo u mulStack) mulStack :=
  DwFrame.of_two h.frame

theorem EqEvalPost.dwFrame {u v : MachineState} (h : Proofs.EqEval.Post u v) :
    DwFrame u v fun a ↦ Within a (u.getReg .x10) 24 ∨
      Within a (stackLo u Proofs.EqEval.stackSize) Proofs.EqEval.stackSize :=
  DwFrame.of_two h.frame

end Rv64Verifier.MultilinearWords
