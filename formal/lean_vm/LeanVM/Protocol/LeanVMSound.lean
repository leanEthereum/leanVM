/-
  LeanVM.Protocol.LeanVMSound

  The leanVM verifier in the two-oracle random-oracle model (`LeanVM/Protocol/Rom/Statement.lean`):
  the step of the proof of `LeanVM.KnowledgeSoundness` (`Statement/LeanVm.lean`) before the
  random-permutation model.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Statements
public import LeanVM.Protocol.EndToEnd.Sound.Extractor
import LeanVM.Protocol.Extraction.Sound
public import LeanVM.Protocol.WithHash
import LeanVM.Protocol.Whir.Params.Iface
public import LeanVM.Protocol.Rom.Statement
public import ArkLib.Data.Polynomial.FrobeniusContraction
public import ArkLib.Data.Polynomial.ResultantDegree
public import ArkLib.Data.Polynomial.UniversalHenselNumerator
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# leanVM in the random-oracle model: the verifier and the experiment

The verifier is leanVM's (`crates/verifier`), its Fiat-Shamir sponge a duplex sponge over
Keccak-f[1600] and its Merkle hash Keccak-256, both modelled as independent random oracles
(`HashSpec = (Bytes →ₒ Digest) + (KState →ₒ KState)`, `LeanVM/Protocol/Rom/Statement.lean`).
Here: the deployed verifier (`verify`), the experiment over the ordered log of fresh queries, the
adversary's part first (`experiment_eq`, `expVerifier_eq`), and the bound on level 0's list
(`candidates_ncard_le`). Knowledge soundness in this model, for the agreement-set extractor, is
`knowledgeSoundnessRomAS` (`LeanVM/Protocol/LeanVMSoundAS.lean`); `LeanVM.Protocol.LeanVM` proves
completeness, and `LeanVM.Protocol.LeanVMRpm` moves both to the random-permutation model.

* The stacked opening's specification enters through the interface `Sound.OpeningIface`
  (`EndToEnd/Sound/Assemble.lean`), filled by the deployed WHIR opening
  (`Whir.Params.openingIface`, `LeanVM/Protocol/Whir/Params/Iface.lean`).
* That `verifier` is the Rust verifier is test evidence, not proof.
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd
open LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Rom (cacheOf map_run_simulateQ_loggedRO_nil map_run_simulateQ_loggedRO)
open scoped ENNReal

@[expose] public section

/-- **The deployed verifier**: `verifier` with Keccak-256 and Keccak-f[1600] (moved here from
`Statement/LeanVm.lean`; no end statement names it). -/
def verify (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) : Bool :=
  Id.run (verifierWithHash (m := Id) keccak256 keccakF1600 prog input proof)

/-- The verifier of the experiment, on a statement and a proof. -/
abbrev expVerifier : ProgramAndInput × Proof → OracleComp KeccakCalls Bool :=
  fun z ↦ verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2

/-- The experiment's verifier is the random-oracle theorem's verifier of every statement. -/
theorem expVerifier_eq : expVerifier = Rom.verifierFam Sound.leanVmSeeds Sound.anyProgram := by
  funext z
  rw [Sound.verifierFam_leanVm, verifierComp_leanVm]
  rfl

/-- **The experiment over the ordered log**: the adversary's run from the empty log, then the
verifier's from the log it left (`Sound.logged2`), each log read as a cache. -/
theorem experiment_eq (A : Adversary) :
    experiment A = (fun w ↦ ((w.1.1, w.2.1), cacheOf w.2.2, cacheOf w.1.2)) <$>
      Sound.logged2 A expVerifier := by
  simp only [experiment, Sound.logged2, ← map_run_simulateQ_loggedRO_nil, bind_map_left,
    map_bind, Functor.map_map]
  refine bind_congr fun p ↦ ?_
  rw [← map_run_simulateQ_loggedRO, bind_map_left]
  simp [map_eq_bind_pure_comp]

/-! ## Knowledge soundness -/

end
end LeanVM
