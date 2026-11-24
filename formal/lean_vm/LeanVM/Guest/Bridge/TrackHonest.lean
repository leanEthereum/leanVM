/-
  LeanVM.Guest.Bridge.TrackHonest

  The tree track on the honest tree of the deployed guest: `main`'s frame at its body to start, the callees and buffers where the honest memory places them, and the tree's pops agreeing with the honest pushes stream by stream.
-/

module

public import LeanVM.Guest.Bridge.RetempPops
public import LeanVM.Guest.EndComplete
public import LeanVM.Guest.B2C.B2Final
public import LeanVM.Guest.Memory.DischargeX
public import LeanVM.Guest.B1.Main.HintsX
public import LeanVM.Guest.Budget.FinalP

/-!
# The tree track on the honest tree

The honest memory's tree, its temporaries re-chosen, pops the same (`pops_retemp`). `honest_closed`: each instance's callees are instances at its callee frames, what a call's move needs (`EntOk.callee`).
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.End (MainComplete Budget work hdrOf bytecode KFactsAll CntRetemp)
open LeanVM.Guest.Budget (MainCompleteP)
open LeanVM.Guest.B1 (LowDef)
open LeanVM.Guest.B1.Main (KFacts imageOf LConsistent Layout MemL)

public section

variable {fs : String → ℕ} {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)} {cert : String → V → ℕ}
  {cnt : Tree → Opcode → ℕ} {b : Budget}

variable {hdr : E × E} {T : Tree} {rd : Reader}

/-- **The honest instances are closed under callees**, each at its callee frame. -/
theorem honest_closed : ∀ I ∈ honestInsts coreProgram fs H hdr T, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
    ∃ J ∈ honestInsts coreProgram fs H hdr T, J.t = k ∧ I.kidFps[i]? = some J.fp := fun _ hI _ _ hk ↦
  let ⟨J, hJ, h1, h2, _⟩ := honest_kid hI hk
  ⟨J, hJ, h1, h2⟩

end

end LeanVM.Guest.Bridge
