/-
  Rv64mc.Table.DigestT

  `Digest::from_halves`' and `Digest::words`' total contracts at the image (`liftProg Gen.fns`). Left as a
  hypothesis: `compiler_builtins`' `memcpy` (`MemcpySpecT`, wave 1b's), under the C wrapper `Digest::words`
  tail-calls (`RuntimeT.memcpy`).

  ## Main results

  * `digestFromHalves`, `digestWords`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Hash.DigestFromHalvesT
import Rv64mc.Proof.Hash.DigestWordsT
import Rv64mc.Gen.Link.Verifier.Hash

namespace Rv64mc.Table.DigestT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Hash
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)

variable (env : Env)

theorem digestFromHalves :
    DigestFromHalvesT.specT env (liftProg fns) Idx.Verifier.Hash.Digest.FromHalves
      Needs.Verifier.Hash.Digest.FromHalves :=
  DigestFromHalvesT.total env _ _ _ Verifier.Hash.Digest.FromHalves.tmpl_eq _

theorem digestWords
    (hm : MemcpySpecT env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy) :
    DigestWordsT.specT env (liftProg fns) Idx.Verifier.Hash.Digest.Words Needs.Verifier.Hash.Digest.Words :=
  DigestWordsT.total env _ _ _ Verifier.Hash.Digest.Words.tmpl_eq Verifier.Hash.Digest.Words.wf (by decide)
    (Table.RuntimeT.memcpy env hm)

end Rv64mc.Table.DigestT

/-- info: 'Rv64mc.Table.DigestT.digestFromHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.DigestT.digestFromHalves

/-- info: 'Rv64mc.Table.DigestT.digestWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.DigestT.digestWords
