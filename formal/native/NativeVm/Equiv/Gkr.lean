module

public import NativeVm.Equiv.Transcript
public import NativeVm.Model.Gkr

/-!
# Phase 3a: the bus's GKR walk simulates the statement's

`gkrStep`, `gkrLayers` and `verifyGkrGrandProducts` (`NativeVm/Model/Gkr.lean`) against the
statement's of the same names, the walk's state related through `GkrStateW.toSpec` (the trees'
values and the point under `EW.toE`). Each step composes the transcript's simulations
(`Sim.grind`, `Sim.sampleChallenge`, `Sim.sumcheck`, `Sim.readScalars`, `Sim.require`,
`Sim.sampleChallenges`); the walk is an induction following `gkrLayers`' recursion.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Protocol

/-- The walk's state as the statement's `GkrState`. -/
def GkrStateW.toSpec (s : GkrStateW) : Verifier.GkrState :=
  ⟨s.values.toList.map EW.toE, s.point.toList.map EW.toE⟩

end NativeVm.Model

namespace NativeVm.Equiv

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

theorem Sim.gkrStep (step : ℕ) (last : Bool) (st : GkrStateW) :
    Sim (Model.gkrStep step last st) (Verifier.gkrStep step last st.toSpec)
      fun a b ↦ a.toSpec = b := by
  unfold Model.gkrStep Verifier.gkrStep
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind Sim.sampleChallenge fun c c' hc ↦ ?_
  refine Sim.bind
    (Sim.sumcheck (by rw [toE_polyEval, hc]; rfl) _ (by simp [GkrStateW.toSpec])) ?_
  rintro ⟨x, cl⟩ ⟨x', cl'⟩ ⟨hx, hcl⟩
  refine Sim.bind (Sim.readScalars _) fun c0 c0' ⟨h0, _⟩ ↦ ?_
  refine Sim.bind (Sim.readScalars _) fun c1 c1' ⟨h1, _⟩ ↦ ?_
  refine Sim.bind (Sim.readScalars _) fun c2 c2' ⟨h2, _⟩ ↦ ?_
  refine Sim.bind (Sim.require ?_) fun _ _ _ ↦ ?_
  · rw [EW.beq_iff_toE, toE_polyEval, hcl, hc]
    simp [toE_prodE, h0, h1, h2]
  refine Sim.bind (Sim.grind _) fun _ _ _ ↦ ?_
  refine Sim.bind (Sim.sampleChallenges _) fun y y' ⟨hy, _⟩ ↦ ?_
  refine Sim.pure ?_
  simp [GkrStateW.toSpec, toE_multilinearEval, h0, h1, h2, hy, hx]

theorem Sim.gkrLayers : ∀ (n : ℕ) (st : GkrStateW),
    Sim (Model.gkrLayers n st) (Verifier.gkrLayers n st.toSpec) fun a b ↦ a.toSpec = b
  | 0, st => by
    simp only [Model.gkrLayers, Verifier.gkrLayers]
    exact Sim.pure rfl
  | 1, st => by
    simp only [Model.gkrLayers, Verifier.gkrLayers]
    refine Sim.bind (Sim.gkrStep 1 true st) fun a b hab ↦ ?_
    subst hab
    exact Sim.gkrLayers 0 a
  | n + 2, st => by
    simp only [Model.gkrLayers, Verifier.gkrLayers]
    split
    · refine Sim.bind (Sim.gkrStep 1 false st) fun a b hab ↦ ?_
      subst hab
      exact Sim.gkrLayers (n + 1) a
    · refine Sim.bind (Sim.gkrStep 2 _ st) fun a b hab ↦ ?_
      subst hab
      exact Sim.gkrLayers n a

/-- **`verifyGkrGrandProducts`**: the count roots, the points and the values agree. -/
theorem Sim.verifyGkrGrandProducts (depth : ℕ) :
    Sim (Model.verifyGkrGrandProducts depth) (Verifier.verifyGkrGrandProducts depth)
      fun a b ↦ a.1.toE = b.1 ∧ a.2.1.toList.map EW.toE = b.2.1 ∧
        a.2.2.toList.map EW.toE = b.2.2 := by
  unfold Model.verifyGkrGrandProducts Verifier.verifyGkrGrandProducts
  refine Sim.bind Sim.readScalar fun sh sh' hsh ↦ ?_
  refine Sim.bind Sim.readScalar fun c c' hc ↦ ?_
  have : (⟨[sh', sh', c'], []⟩ : Verifier.GkrState) = GkrStateW.toSpec ⟨#[sh, sh, c], #[]⟩ := by
    simp [GkrStateW.toSpec, hsh, hc]
  rw [this]
  refine Sim.bind (Sim.gkrLayers _ _) fun a b hab ↦ ?_
  subst hab
  exact Sim.pure ⟨hc, rfl, rfl⟩

end NativeVm.Equiv
