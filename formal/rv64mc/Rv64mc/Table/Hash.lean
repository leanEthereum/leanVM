/-
  Rv64mc.Table.Hash

  The contracts of `hash.rs` and `merkle.rs` at the image (`liftProg Gen.fns`): each `ok` at its function's index,
  with the generated link and the stack each needs (`Gen.Needs`). The indices are the generator's
  (`Rv64mc/Gen/index.tsv`).
-/

import Rv64mc.Proof.Hash.DigestFromHalves
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Hash.Digest.FromHalves
import Rv64mc.Proof.Hash.DigestWords
import Rv64mc.Proof.Hash.DigestHalves
import Rv64mc.Gen.Link.Verifier.Hash.Digest.Words
import Rv64mc.Gen.Link.Verifier.Hash.Digest.Halves
import Rv64mc.Table.Runtime

namespace Rv64mc.Table.Hash

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem digestFromHalves :
    Spec.Hash.DigestFromHalves.spec env (liftProg fns) Idx.Verifier.Hash.Digest.FromHalves Needs.Verifier.Hash.Digest.FromHalves :=
  Proof.Hash.DigestFromHalves.ok env _ Idx.Verifier.Hash.Digest.FromHalves _ Verifier.Hash.Digest.FromHalves.tmpl_eq _

/-- `compiler_builtins`' `memcpy`, a hypothesis of `Table.Runtime` too. -/
abbrev BuiltinMemcpy : Prop :=
  Spec.Runtime.MemcpySpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy

theorem digestWords (hcp : BuiltinMemcpy env) :
    Spec.Hash.DigestWords.spec env (liftProg fns) Idx.Verifier.Hash.Digest.Words Needs.Verifier.Hash.Digest.Words :=
  Proof.Hash.DigestWords.ok env _ Idx.Verifier.Hash.Digest.Words _ Verifier.Hash.Digest.Words.tmpl_eq
    Verifier.Hash.Digest.Words.wf (by decide) (Table.Runtime.memcpy env hcp)

theorem digestHalves (hcp : BuiltinMemcpy env) :
    Spec.Hash.DigestHalves.spec env (liftProg fns) Idx.Verifier.Hash.Digest.Halves Needs.Verifier.Hash.Digest.Halves :=
  Proof.Hash.DigestHalves.ok env _ Idx.Verifier.Hash.Digest.Halves _ Verifier.Hash.Digest.Halves.tmpl_eq
    Verifier.Hash.Digest.Halves.wf (by decide) (digestWords env hcp)

end Rv64mc.Table.Hash

/-- info: 'Rv64mc.Table.Hash.digestFromHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Hash.digestFromHalves
