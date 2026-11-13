/-
  LeanVM.Guest.B1.Place.LqBoundP

  `level_queries` with its pops, within every words bound of its trees.
-/

module

public import LeanVM.Guest.B1.Place.LqProofP

/-!
# `level_queries` with its pops, within a words bound

`LqAtOP`: `LqAtDP` at an optional words bound (`CompleteAtOP`). `lqAtOP_of_EP`: `LqAtEP` gives it at every words bound
of its trees, frames below `2^32` (`lq_bound` on `LqAtEP.toE`). `level_queries_completeAtBP`: every entry of `lqTable`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **`LqAtDP` at an optional words bound.** -/
def LqAtOP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q base folds leaf d cd mu nhs hbits fin : ℕ) (Bd : Option ℕ) : Prop :=
  let s := lqOqS q base folds leaf d cd mu nhs hbits fin
  ∀ (Lin : Layout) (lam lamInv : E) (ecoefs ehs epos eqp : ℕ) (rounds : List FoldRound)
    (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest)
    (capW flW : List E) (r0 r1 : E),
    rounds.length = s.folds → (s.final = 1 → hsv.length = s.nHs) →
    OqStatic s rounds hsv qs rows sibs q →
    LqCaps s q capW flW r0 r1 qs rows sibs →
    LqReg (RegionL Lin) s q ecoefs ehs epos eqp eb →
    (∀ rd, LowDef κ rd → MemL rd Lin → LqMem rd s q ecoefs ehs epos eqp rounds hsv eb qs) →
    CompleteAtOP fs cert κ name Lin
      [lam, lamInv, ofK (addressOfIndex ecoefs), ofK (addressOfIndex ehs),
        ofK (addressOfIndex epos), ofK (addressOfIndex eqp)]
      (Returns [r0, r1, lqSum s (lqOdd q base folds leaf d cd mu nhs hbits fin) (lqIters q base)
        lamInv rounds qs rows, lam ^ q]) Bd
      (fun _ => lqCapE capW flW ++ oqPops s (oqW qs rows sibs) q)

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

end
end LeanVM.Guest.B1
