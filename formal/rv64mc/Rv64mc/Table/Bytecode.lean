/-
  Rv64mc.Table.Bytecode

  `bytecode.rs`'s contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index
  (`Rv64mc/Gen/index.tsv`), with the generated link, from the contracts not proved here (`panic_bounds_check`,
  which does not return).
-/

import Rv64mc.Proof.Bytecode.IsValidEncoding
import Rv64mc.Gen.Link.Verifier.Bytecode

namespace Rv64mc.Table.Bytecode

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem isValidEncoding (hpanic : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck 0) :
    Spec.Bytecode.IsValidEncoding.spec env (liftProg fns) Idx.Verifier.Bytecode.IsValidEncodingOfALeanisaProgram :=
  Proof.Bytecode.IsValidEncoding.ok env _ Idx.Verifier.Bytecode.IsValidEncodingOfALeanisaProgram _ Verifier.Bytecode.IsValidEncodingOfALeanisaProgram.tmpl_eq
    Verifier.Bytecode.IsValidEncodingOfALeanisaProgram.wf hpanic

end Rv64mc.Table.Bytecode

/-- info: 'Rv64mc.Table.Bytecode.isValidEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Bytecode.isValidEncoding
