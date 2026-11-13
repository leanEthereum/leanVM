/-
  LeanVM.Guest.B1.Opening.QueriesPlacedDPAll

  Every deployed specialization of `opening_queries` is `CompleteAtDP`, popping its queries' entries.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedDP
public import LeanVM.Guest.B1.Opening.QueriesPlacedAll

/-!
# `opening_queries`, `CompleteAtDP`, every specialization

`OqCompleteDP`: `OqCompleteD` popping `oqPops` of its `oqCount` queries; `opening_queries_completeAtDP`: every entry of `openingQueriesLoops`, as `opening_queries_completeAtB`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **`opening_queries`, the specialization `name` of the shape `s`, `odd`, is `CompleteAtDP`**: `OqCompleteD`, its
tree popping its queries' rows and walks' children in order. -/
def OqCompleteDP (fs : String → ℕ) (cert : String → V → ℕ) (name : String) (s : Oq) (odd : ℕ) : Prop :=
  ∀ (κ : ℕ) (Lin : Main.Layout) (N : ℕ) (ecap eflags ecoefs ehs epos eqp : ℕ) (lamInv : E)
    (rounds : List FoldRound) (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
    (sibs : ℕ → List Digest), N + 1 < ordG → rounds.length = s.folds →
    (s.final = 1 → hsv.length = s.nHs) →
    OqStatic s rounds hsv qs rows sibs (oqCount odd s.base N) →
    OqLinReg (RegionL Lin) s ecap eflags ecoefs ehs epos eqp eb qs (oqCount odd s.base N) →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
        (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
        (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
        qs rows sibs (oqCount odd s.base N)) →
    CompleteAtDP fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N]
      (Returns [if s.final = 1 then 0 else
        oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (fun _ => oqPops s (oqW qs rows sibs) (oqCount odd s.base N))

/-- **Every deployed `opening_queries` is `CompleteAtDP`.** -/
theorem opening_queries_completeAtDP (fs : String → ℕ) (cert : String → V → ℕ) :
    ∀ p ∈ openingQueriesLoops, OqCompleteDP fs cert p.1 p.2.2.oq p.2.2.odd := by
  intro p hp
  obtain ⟨hW, fm, fl, hfm, hpm, hbm, hfl, hpl, hbl⟩ := oqFns_all p hp
  obtain ⟨hs, hfin, hb, hpd, hcd, -, -, -⟩ := oqSide_all p hp
  intro κ Lin N ecap eflags ecoefs ehs epos eqp lamInv rounds hsv eb qs rows sibs hN hrl hhl hst hreg hmem
  rcases hb with ⟨hb0, hodd⟩ | ⟨hb1, -, hodd⟩
  · have hQ : oqCount p.2.2.odd p.2.2.oq.base N = N := by
      unfold oqCount; rw [show p.2.2.oq.base = 0 from hb0]; rfl
    rw [hQ] at hst hreg hmem ⊢
    rw [hodd] at hbm ⊢
    have hbl' := hbl.trans (oqLoopT_zero hb0 _ _ _)
    exact oqMain0_completeAtDP fs cert κ hs hfin hb0 hpd hcd hW hfm hpm hbm hfl hpl hbl'
      (loop0_true hfl hbl') hN hrl hhl hst hreg hmem
  · have hQ : oqCount p.2.2.odd p.2.2.oq.base N = p.2.2.odd + 2 * N := by
      unfold oqCount; rw [show p.2.2.oq.base = 1 from hb1]; rfl
    rw [hQ] at hst hreg hmem ⊢
    have hbl' := hbl.trans (oqLoopT_one hb1 _ _ _)
    exact oqMain1_completeAtDP fs cert κ hs hfin hb1 hpd hcd hodd hW hfm hpm hbm hfl hpl hbl'
      (loop1_true hfl hbl') hN hrl hhl hst hreg hmem

end
end LeanVM.Guest.B1
