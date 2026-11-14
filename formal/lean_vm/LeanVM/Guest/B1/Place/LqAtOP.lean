/-
  LeanVM.Guest.B1.Place.LqAtOP

  `level_queries`' placed statement with its pops at an optional words bound, stated where `open_stacked`'s arm proof can take it.
-/

module

public import LeanVM.Guest.B1.Place.Lq
public import LeanVM.Guest.B1.Opening.QueriesPlacedDP
public import LeanVM.Guest.Budget.Bounded

/-!
# `level_queries` with its pops, stated

* `lqCapE`: the cap's and the flags' entries, the honest words;
* `LqAtOP`: `level_queries` at an entry of `lqTable`, placed at an optional words bound (`CompleteAtOP`), popping `lqCapE` then `oqPops` of its queries;
* `CompleteAtOP.toDTBR`: within a bound, by a tree popping the entries.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout

@[expose] public section

/-- **The cap's and the flags' entries**: the honest words. -/
def lqCapE (capW flW : List E) : List Pop := [("merkle_caps", capW), ("merkle_cap_active", flW)]

/-- **`level_queries` at an entry of `lqTable`, placed at an optional words bound, with its pops.** -/
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

/-- **Within a bound, by a tree popping the entries.** -/
theorem CompleteAtOP.toDTBR {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String} {Lin : Layout}
    {args : List E} {Out : List E → Layout → Prop} {B : ℕ} {ps : Reader → List Pop}
    (h : CompleteAtOP fs cert κ f Lin args Out (some B) ps) :
    CompleteAtDTBR fs cert κ f Lin args Out (fun rd t ↦ t.pops coreProgram rd = ps rd) B := fun fp ↦
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn B rfl, ho, hw, hd, hr⟩

end
end LeanVM.Guest.B1
