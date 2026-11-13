/-
  LeanVM.Guest.B1.Place.LqBoundP

  `level_queries` with its pops, within every words bound of its trees.
-/

module

public import LeanVM.Guest.B1.Place.LqProofP

/-!
# `level_queries` with its pops, within a words bound

`lqAtOP_of_EP`: `LqAtEP` gives `LqAtOP` at every words bound of its trees, frames below `2^32` (`lq_bound` on `LqAtEP.toE`). `level_queries_completeAtBP`: every entry of `lqTable`; `level_queries_completeAtOP`: at no bound.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **`LqAtEP` gives `LqAtOP` within every words bound of its trees**, frames below `2^32`. -/
theorem lqAtOP_of_EP {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {name : String}
    {q base folds leaf d cd mu nhs hbits fin : ℕ}
    (hE : LqAtEP fs cert κ name q base folds leaf d cd mu nhs hbits fin)
    (hfs : ∀ f, fs f < 2 ^ 32) (hS : LqSmall q base folds leaf d cd mu nhs hbits fin) {B : ℕ}
    (hT : TotalLe coreProgram fs name (fun _ ↦ B)) :
    LqAtOP fs cert κ name q base folds leaf d cd mu nhs hbits fin (some B) := by
  intro Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst
    hcaps hreg hmem
  have hb := lq_bound hE.toE hfs hS hrl hhs hst hcaps hT
  exact (hE Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs
    hst hcaps hreg hmem).toOP fun B' h ↦ by cases h; exact hb

/-- **`level_queries` with its pops within every words bound of its trees**, frames below `2^32`. -/
theorem level_queries_completeAtBP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    (hfs : ∀ f, fs f < 2 ^ 32) :
    ∀ e ∈ lqTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
      LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
        e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 (some B) :=
  fun e he _ hT ↦ lqAtOP_of_EP (level_queries_completeAtEP fs cert κ e he) hfs (lqTable_small e he) hT

/-- **`level_queries` with its pops at no words bound.** -/
theorem level_queries_completeAtOP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) :
    ∀ e ∈ lqTable,
      LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
        e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 none :=
  fun e he Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs capW flW r0 r1 hrl hhs hst hcaps hreg
    hmem ↦ (level_queries_completeAtEP fs cert κ e he Lin lam lamInv ecoefs ehs epos eqp rounds hsv eb qs rows sibs
      capW flW r0 r1 hrl hhs hst hcaps hreg hmem).toOP fun _ h ↦ by cases h

end
end LeanVM.Guest.B1
