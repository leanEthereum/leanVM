/-
  LeanVM.Protocol.EndToEnd.Sound.CutRun

  The ghost verifier cut at the final polynomial: on a prefix of every accepting run's history, it
  returns the run's data.
-/

module

public import LeanVM.Protocol.EndToEnd.Sound.Assemble
public import LeanVM.Protocol.Whir.Sound.Cut

/-!
# The verifier, cut at the final polynomial

`leanVmProgramCut` is `leanVmProgramG` with the opening cut at the final polynomial
(`Whir.Sound.verifyStackedOpeningCut`); `cutRel_leanVmProgramG`: wherever the ghost verifier
returns its verdict and data, the cut returns them after a prefix of the history. The extractor
replays the cut.
-/

namespace LeanVM.Protocol.EndToEnd.Sound

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir.Sound

@[expose] public section

/-- `veBodyG` cut at the final polynomial. -/
def veBodyCut (ev : List K → List E → E → VerifierProgram Unit) (publicInput : Digest)
    (layout : Verifier.Layout) (ρ : ℕ) : VerifierProgram WhirTrace := do
  commitStack layout.stackLog ρ
  let ood ← readOod layout.stackLog
  let (claims, keccakPoint, keccakSlices) ← frontProg ev layout publicInput
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  verifyStackedOpeningCut layout.stackLog ρ
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout) ++ [ood])

theorem cutRel_veBodyG (ev : List K → List E → E → VerifierProgram Unit) (publicInput : Digest)
    (layout : Verifier.Layout) (ρ : ℕ) :
    CutRel (veBodyG ev publicInput layout ρ) (veBodyCut ev publicInput layout ρ) := by
  unfold veBodyG veBodyCut
  simp only [VerifierProgram.bind_eq]
  refine CutRel.bind _ fun _ ↦ CutRel.bind _ fun ood ↦ CutRel.bind _ fun r ↦ ?_
  obtain ⟨cl, kp, ks⟩ := r
  refine CutRel.bind _ fun y ↦ ?_
  obtain ⟨t, w⟩ := y
  exact cutRel_verifyStackedOpeningG _ _ _

/-- `verifyExecutionClaimsG` cut at the final polynomial. -/
def verifyExecutionClaimsCut (ev : List K → List E → E → VerifierProgram Unit) (bytecode : List K)
    (pd : Digest) : VerifierProgram ((Verifier.Layout × ℕ) × WhirTrace) :=
  (readAnnouncedSizes bytecode).bind fun a ↦ (veBodyCut ev pd a.1 a.2).bind fun tr ↦
    VerifierProgram.ret (a, tr)

theorem cutRel_verifyExecutionClaimsG (ev : List K → List E → E → VerifierProgram Unit)
    (bytecode : List K) (pd : Digest) :
    CutRel (verifyExecutionClaimsG ev bytecode pd) (verifyExecutionClaimsCut ev bytecode pd) :=
  CutRel.bind _ fun a ↦ (cutRel_veBodyG ev pd a.1 a.2).mapRet fun tr ↦ (a, tr)

/-- **The leanVM verifier cut at the final polynomial**, returning the verdict and the data. -/
def leanVmProgramCut (bytecode : List K) (pd : Digest) :
    VerifierProgram (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) :=
  (verifyExecutionClaimsCut computedBytecodeValue bytecode pd).bind fun d ↦
    VerifierProgram.ret (true, d)

/-- **The cut returns an accepting run's data**: wherever the ghost verifier returns, the cut
returns the same after a prefix of the history. -/
theorem cutRel_leanVmProgramG (bytecode : List K) (pd : Digest) :
    CutRel (leanVmProgramG bytecode pd) (leanVmProgramCut bytecode pd) :=
  (cutRel_verifyExecutionClaimsG _ bytecode pd).mapRet fun d ↦ (true, d)

end
end LeanVM.Protocol.EndToEnd.Sound
