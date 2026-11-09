/-
# PqDas

The security framework for erasure code commitments of Benedikt Wagner.

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593.
-/
import PqDas.Assumptions.ErasureCode
import PqDas.Assumptions.VectorCommitment
import PqDas.Assumptions.CodeChecker
import LeanDa.Defs
import PqDas.RomRuntime
import PqDas.VcvioExtras
import PqDas.Target.ErasureCodeCommitment
import PqDas.Target.Scheme
import PqDas.Proof.CommittedSoundness.Defs
import PqDas.Proof.CommittedSoundness.Fork
import PqDas.Proof.CommittedSoundness.Bridge
import PqDas.Proof.CommittedSoundness.Coupling
import PqDas.Proof.CommittedSoundness.Lockstep
import PqDas.Proof.CommittedSoundness.ForkingBound
import PqDas.Proof.PositionBinding
import PqDas.Proof.CodeBinding
import PqDas.Proof.CorollaryCodeBinding
import PqDas.AxiomCheck
