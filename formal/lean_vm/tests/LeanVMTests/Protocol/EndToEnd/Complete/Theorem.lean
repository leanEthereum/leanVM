import LeanVM.Protocol.Verifier.Claims
import LeanVM.Protocol.EndToEnd.Complete.Theorem
import LeanVM.Protocol.WithHash

/-!
# Perfect completeness of the leanVM verifier: statement locks

Locks of the phases' simulations (`follows_verifyBusBalance`, `follows_tablePhase`,
`follows_keccakPhase`, `follows_ringSwitch_leanIsa`, `follows_verifyGkrGrandProducts` is locked in
`Complete/Gkr.lean`'s test) and of the assembled theorems (`leanVm_complete`,
`exists_prove_verifyWith`, `exists_prove_verify`, `leanVm_complete_of_execution`): a change of a
hypothesis or of the conclusion fails here. The fidelity facts the bus and the table phase rest
on are locked too (`refFlush_eval`, `refCountColumns`, `refNConstraints`): they are what makes the
verifier's tables' bus and constraints the instance's.
-/

namespace LeanVMTests.Protocol.EndToEnd.Complete.Theorem

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.Compile
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open LeanVM.Protocol.Whir.Complete LeanVM.Protocol.KeccakHash
open Air.Flat (EnsembleWitness)

-- Matching a statement against a theorem must not unfold the simulation into the scripts.
attribute [local irreducible] Follows

/-! ## The phases -/

example : ∀ {prog : LeanIsaProgram} {s : Sizes} {input : PublicInput} {q : Column (leanIsaμ
    prog s)},
    busDepth prog s < 64 → M3Honest (inst prog s) input q → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ BusGood prog s q b) (hBus prog s q)
      (verifyBusBalance computedBytecodeValue (verifierLayout prog s)) cs :=
  follows_verifyBusBalance

example : ∀ {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)} {input :
    PublicInput},
    M3Holds (inst prog s) input q → ∀ (bus : BusResult), BusGood prog s q bus → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b ∧
        ∃ tc, b = bus.claims ++ tc ∧ tc.length = 153 ∧ ∃ z : Vector E (s.τ 5),
          tc.filter (fun c ↦ c.column ∈ keccakOutputColumns) = honestLanes prog s q z)
      (hTable prog s q bus) (tablePhaseClaims (verifierLayout prog s) bus) cs :=
  follows_tablePhase

example : ∀ (prog : LeanIsaProgram) (s : Sizes) (q : Column (leanIsaμ prog s)) {input :
    PublicInput},
    M3Holds (inst prog s) input q → ∀ {claims : List ColumnClaim}, TrueClaims prog s q claims →
    ∀ (z : Vector E (s.τ 5)), lanesOf claims = honestLanes prog s q z → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        (∀ c ∈ b.1, TrueClaim prog s q c ∧ c.column ∉ keccakOutputColumns) ∧
        KeccakGkr.slicesTrue (s.τ 5) (qkH prog s q) b.2.1 b.2.2 ∧ b.1.length ≤ claims.length + 1)
      (hKeccakPhase prog s q claims) (keccakPhaseClaims (verifierLayout prog s) claims) cs :=
  follows_keccakPhase

example : ∀ {prog : LeanIsaProgram} {s : Sizes} {q : Column (leanIsaμ prog s)} (r : List E ×
    List E),
    KeccakGkr.slicesTrue (s.τ 5) (Front.qkAt ((blocks prog s).offset (keccakBlock prog s)) q)
      r.1 r.2 → ∀ (cs : Commits),
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧
        StackClaim.Holds (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2) q ∧
        IsMultilinearFn (leanIsaμ prog s) (ringSwitchClaim (verifierLayout prog s) b.1 b.2).1)
      (hRing r.1 r.2) (ringSwitch r.1 r.2) cs :=
  follows_ringSwitch_leanIsa

/-! ## The fidelity of the verifier's tables -/

example : ∀ (t : Fin 6) (side : Side) (row : Fin (width (opIdx t)) → K),
    ((refSide t side).map fun coords ↦
        (List.range 16).map fun k ↦ (coords.getD k {}).evaluate (rowFn row)) =
      (((LeanIsa.flushes (opIdx t)).filter fun f ↦ decide (f.1 = side)).map
        fun f ↦ f.2.toList.map fun P ↦ ofK (P.eval row)) :=
  refFlush_eval

example : ∀ t : Fin 6,
    (tables.getD t default).countColumns = (LeanIsa.counts (opIdx t)).map (·.val) :=
  refCountColumns

example : tables.map Table.nConstraints = [0, 0, 0, 0, 2, 0] := refNConstraints

/-! ## The assembled theorems -/

example : ∀ {prog : LeanIsaProgram} {input : PublicInput} {κ : ℕ} {w : EnsembleWitness
    (leanIsaEnsemble prog κ)}
    {s : Sizes} {ρ : ℕ}, SatisfiedBy prog input w → Sizes.ofWitness w = some s →
    s.Admissible prog → validRate ρ →
    ∃ S : Strategy, ∀ chal : List Ev → E,
      runI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S chal =
          some true ∧
        shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S chal :=
  leanVm_complete

example : ∀ (H : Bytes → Digest) (F : LeanVM.Semantics.KeccakState → LeanVM.Semantics.KeccakState)
    {prog : LeanIsaProgram} {input : PublicInput}
    {κ : ℕ} {w : EnsembleWitness (leanIsaEnsemble prog κ)} {s : Sizes} {ρ : ℕ},
    SatisfiedBy prog input w → Sizes.ofWitness w = some s → s.Admissible prog → validRate ρ →
    ∀ (fuel : ℕ),
    (∀ hist bits k sp,
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)).after hist = some
          (.grind bits k) →
        findNonce F bits sp fuel ≠ none) →
    ∃ S π, prove H F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S
        (Id.run (seedWithHash (m := Id) H F (bytecodeWords prog) (publicInputDigest input))) fuel =
          some π ∧
      Id.run (verifyWithHash (m := Id) H F (bytecodeWords prog) (publicInputDigest input) π) =
          true :=
  exists_prove_verifyWith

example : ∀ {prog : LeanIsaProgram} {input : PublicInput} {κ : ℕ} {w : EnsembleWitness
    (leanIsaEnsemble prog κ)}
    {s : Sizes} {ρ : ℕ}, SatisfiedBy prog input w → Sizes.ofWitness w = some s →
    s.Admissible prog → validRate ρ → ∀ (fuel : ℕ),
    (∀ hist bits k sp,
      (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)).after hist = some
          (.grind bits k) →
        findNonce keccakF1600 bits sp fuel ≠ none) →
    ∃ S π, prove keccak256 keccakF1600 (leanVmVerifierProgram (bytecodeWords prog)
        (publicInputDigest input)) S
        (seed (bytecodeWords prog) (publicInputDigest input)) fuel = some π ∧
      verify (bytecodeWords prog) (publicInputDigest input) π = true :=
  exists_prove_verify

example : ∀ {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog},
    ValidExecution prog input t → t.stepCount ≤ 2 ^ maxLogRows →
    ∃ (w : EnsembleWitness (leanIsaEnsemble prog t.logMemorySize))
      (s : Sizes), SatisfiedBy prog input w ∧ AssignmentRepresents w t ∧
      Sizes.ofWitness w = some s ∧
      (s.Admissible prog → ∀ ρ, validRate ρ → ∃ S : Strategy, ∀ chal : List Ev → E,
        runI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S chal =
            some true ∧
          shapedI (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) S chal) :=
  leanVm_complete_of_execution

end LeanVMTests.Protocol.EndToEnd.Complete.Theorem
