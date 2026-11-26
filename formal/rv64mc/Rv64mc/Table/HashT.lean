/-
  Rv64mc.Table.HashT

  The total contracts of the hash functions proved total, at the image: `xor_block` (`XorBlockSafeT`), a leaf, and
  `keccak_f` (`KeccakFSafeT`), over the C wrappers `memcpy` and `memset`. Left as a hypothesis: `keccak_f`'s three
  constant tables in the image's static data (`KeccakTables`, `DataRef.InData`), an environment fact.

  ## Main results

  * `xorBlockT`, `keccakFT`
-/

import Rv64mc.Proof.Hash.XorBlockT
import Rv64mc.Proof.Hash.KeccakFT
import Rv64mc.Table.CopyUseT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Hash

namespace Rv64mc.Table.HashT

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

/-- **`xor_block` at the image** (function 123). -/
theorem xorBlockT : Proof.Hash.XorBlockT.XorBlockSafeT env (liftProg fns) Idx.Verifier.Hash.XorBlock
    Needs.Verifier.Hash.XorBlock :=
  HoldsT.mono_need (Proof.Hash.XorBlockT.total Verifier.Hash.XorBlock.tmpl_eq) (by decide)

/-- `keccak_f`'s round constants, `π` and `ρ` tables in the image's static data. -/
abbrev KeccakTables : Prop := DataRef.InData env (Proof.Hash.KeccakFT.tables Verifier.Hash.KeccakF.link)

/-- **`keccak_f` at the image** (function 114), over its tables. -/
theorem keccakFT (hd : KeccakTables env) :
    Proof.Hash.KeccakFT.KeccakFSafeT env (liftProg fns) Idx.Verifier.Hash.KeccakF Needs.Verifier.Hash.KeccakF :=
  HoldsT.mono_need (Proof.Hash.KeccakFT.total (needC := 16) Verifier.Hash.KeccakF.tmpl_eq Verifier.Hash.KeccakF.wf hd
    (CopyUseT.memcpy env) (HoldsT.mono_need (RuntimeT.memset env) (by decide))) (by decide)

end Rv64mc.Table.HashT

/-- info: 'Rv64mc.Table.HashT.xorBlockT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.HashT.xorBlockT

/-- info: 'Rv64mc.Table.HashT.keccakFT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.HashT.keccakFT
