/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD0

  `opening_queries` is `CompleteAtB`, from `CompleteAtEP`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedDP

/-!
# `opening_queries`, `CompleteAtB`

`oqMain1_completeAtB`, `oqMain0_completeAtB`: `oqMain1_completeAtEP`, `oqMain0_completeAtEP`
forgetting the pops and bounding the tree by its exact size.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **`opening_queries` at level 0 is `CompleteAtB`.** -/
theorem oqMain1_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb1 : s.base = 1) {cd odd : ℕ} (hcd : 1 ≤ cd)
    (hodd : odd ≤ 1) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT s loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s loop) (hlp : coreProgram.loop loop = true)
    {Lin : Main.Layout} {N : ℕ} (hN : N + 1 < ordG) {ecap eflags ecoefs ehs epos eqp : ℕ}
    {lamInv : E} {rounds : List FoldRound} {hsv : List E} (hrl : rounds.length = s.folds)
    (hhl : s.final = 1 → hsv.length = s.nHs) {eb qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest}
    (hst : OqStatic s cd rounds hsv qs rows sibs (odd + 2 * N))
    (hreg : OqLinReg (RegionL Lin) s cd ecap eflags ecoefs ehs epos eqp eb qs (odd + 2 * N))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s cd (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
        (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
        (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
        qs rows sibs (odd + 2 * N)) :
    CompleteAtB fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N, gen ^ odd]
      (Returns [if s.final = 1 then 0 else
        oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (fs name + (N + 1) + (N * fs loop + fs (tailKey loop))) :=
  (oqMain1_completeAtEP fs cert κ hs hfin hb1 hcd hodd hfm hpm hbm hfl hpl hbl hlp hN hrl hhl hst hreg hmem).toE.toB le_rfl

/-- **`opening_queries` deeper is `CompleteAtB`.** -/
theorem oqMain0_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb0 : s.base = 0) {cd : ℕ} (hcd : 1 ≤ cd)
    {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm) (hpm : fm.params = oqMainParams)
    (hbm : fm.body = oqMainT s loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (hlp : coreProgram.loop loop = true)
    {Lin : Main.Layout} {N : ℕ} (hN : N + 1 < ordG) {ecap eflags ecoefs ehs epos eqp : ℕ}
    {lamInv : E} {rounds : List FoldRound} {hsv : List E} (hrl : rounds.length = s.folds)
    (hhl : s.final = 1 → hsv.length = s.nHs) {eb qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest}
    (hst : OqStatic s cd rounds hsv qs rows sibs N)
    (hreg : OqLinReg (RegionL Lin) s cd ecap eflags ecoefs ehs epos eqp eb qs N)
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s cd (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
        (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
        (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
        qs rows sibs N) :
    CompleteAtB fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N, gen ^ 0]
      (Returns [if s.final = 1 then 0 else
        oqChain 0 s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (fs name + (N + 1) + (N * fs loop + fs (tailKey loop))) :=
  (oqMain0_completeAtEP fs cert κ hs hfin hb0 hcd hfm hpm hbm hfl hpl hbl hlp hN hrl hhl hst hreg hmem).toE.toB le_rfl

end
end LeanVM.Guest.B1
