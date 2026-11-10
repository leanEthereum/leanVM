import Rv64Verifier.Proofs.Layout.ReprVec
import Rv64Verifier.Proofs.Bus.Repr

/-!
# The bus proofs' forms are the layout proofs'

`Proofs/Bus/Repr.lean` reads monomials, terms and forms as `Repr.lean` does, under its own names.
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

@[simp] theorem monoAt_eq : Bus.monoAt = monoOf := rfl

@[simp] theorem termsAt_eq : Bus.termsAt = termsOf := rfl

@[simp] theorem formAt_eq : Bus.formAt = formOf := rfl

@[simp] theorem formVecAt_eq (s : MachineState) (a : Word) :
    Bus.formVecAt s a = (formVecOf s a).map FormRust.toSpec := by
  simp only [Bus.formVecAt, formVecOf, formsAt, List.map_map, formAt_eq]
  rfl

@[simp] theorem formRowsAt_eq (s : MachineState) (a : Word) (n : Nat) :
    Bus.formRowsAt s a n =
      (List.range n).map fun i ↦ (formVecOf s (a + BitVec.ofNat 64 (24 * i))).map FormRust.toSpec := by
  simp only [Bus.formRowsAt, formVecAt_eq]

end Rv64Verifier.Layout
