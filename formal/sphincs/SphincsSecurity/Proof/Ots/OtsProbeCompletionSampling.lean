import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FtsProbeSimulation
import SphincsSecurity.Proof.Ots.OtsProbeSimulation
/-!
# Finite boundary of one-time completion

The concrete retained game observes a completed hidden table only through its chain-start values.
Those values form the finite `OtsSecretIndex` table already used by the concrete sampler transport.
Structural positions remain dynamic on the masked side and do not enter the distributional target.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def hashOutputOfDigest (digest : Digest) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (digest, 0)

@[simp] theorem truncateHash_hashOutputOfDigest (digest : Digest) :
    truncateHash (hashOutputOfDigest digest) = digest := by
  change (splitHashOutput digestBits
    ((splitHashOutputEquiv digestBits (by decide)).symm (digest, 0))).1 = digest
  rw [show splitHashOutput digestBits = splitHashOutputEquiv digestBits (by decide) from rfl,
    Equiv.apply_symm_apply]
