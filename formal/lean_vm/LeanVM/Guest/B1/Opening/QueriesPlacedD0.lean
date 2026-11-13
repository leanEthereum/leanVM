/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD0

  `opening_queries` deeper is `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedD1

/-!
# `opening_queries` deeper, `CompleteAtB`

As at level 0 (`oqMain1_completeAtB`), a deeper specialization (`base = 0`, `odd = 0`, one query an
iteration): `oqMain0_completeAtB`, its own layout its chain buffer.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **`opening_queries` deeper is `CompleteAtB`.** -/
theorem oqMain0_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb0 : s.base = 0) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) {name wlk loop : String} (hW : WalkFn wlk s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s 0 wlk loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s wlk loop) (hlp : coreProgram.loop loop = true)
    {Lin : Main.Layout} {N : ℕ} (hN : N + 1 < ordG) {ecap eflags ecoefs ehs epos eqp : ℕ}
    {lamInv : E} {rounds : List FoldRound} {hsv : List E} (hrl : rounds.length = s.folds)
    (hhl : s.final = 1 → hsv.length = s.nHs) {eb qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest}
    (hst : OqStatic s rounds hsv qs rows sibs N)
    (hreg : OqLinReg (RegionL Lin) s ecap eflags ecoefs ehs epos eqp eb qs N)
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
        (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
        (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
        qs rows sibs N) :
    CompleteAtB fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N]
      (Returns [if s.final = 1 then 0 else
        oqChain 0 s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (fs name + (N + 1) + (N + 1) * fs loop + N * fs wlk) := by
  intro fp
  set W := oqW qs rows sibs with hWd
  set ds : ℕ → E := fun k ↦ oqResV s rounds (W k) with hds
  obtain ⟨chainL, hchainL⟩ : ∃ L : Main.Layout,
      L = [(fp + fs name, oqChainVals 0 s.base lamInv ds N)] := ⟨_, rfl⟩
  have wChain : Within chainL (fp + fs name) (N + 1) := by
    intro x hx
    simp only [hchainL, List.mem_singleton] at hx
    subst hx
    simp [oqChainVals]
  set n := fs name + (N + 1) + 0 * fs wlk + ((N + 1) * fs loop + N * fs wlk) with hn
  have wAll : Within chainL fp n := wChain.mono (by omega) (by omega)
  have dAll : DisjL chainL := by rw [hchainL]; exact List.pairwise_singleton _ _
  refine ⟨n, chainL, _, [], ⟨rfl, rfl⟩, by simpa using wAll,
    by simpa using dAll, le_of_eq (by rw [hn]; ring), fun rd hlow hm ↦ ?_⟩
  rw [List.nil_append, Main.memL_append] at hm
  obtain ⟨hmChain, hmLin⟩ := hm
  have hk := hmem rd hlow hmLin
  have hch : ∀ i ≤ N, LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) i
      (oqChain 0 s.base lamInv ds i) := by
    intro i hi
    have := hmChain (fp + fs name, oqChainVals 0 s.base lamInv ds N) (by rw [hchainL]; simp) i
      (by simp [oqChainVals]; omega)
    simpa [oqChainVals] using this
  refine relAtIn_dmono (D := fun _ ↦ False) ?_ (fun i hi ↦ absurd hi (regionL_nil i))
  rw [← oqRet_eq s 0 lamInv rounds qs rows sibs N]
  refine oqMain0_placed (rounds := rounds) (hsv := hsv) (hNv := oqChain 0 s.base lamInv ds N)
    (w := W) (bp := fun j ↦ ofK (Parameters.addressOfIndex (eb j)))
    (v := fun j ↦ oqChain 0 s.base lamInv ds j)
    coreProgram_wf fs cert hs hfin hpd1 hcd hW hfm hpm hbm hfl hpl hbl hlp hN
    (by simpa [oqChain] using hch 0 (by omega)) (fun _ ↦ hch N le_rfl) (fun j hj ↦ ?_)
  obtain ⟨xa, ba, -⟩ := hk.2.2 j hj
  refine ⟨qdOk_of_lin hrl hhl hst hk hj _ _ _, xa, ba, fun _ ↦ ⟨hch j (by omega), ?_⟩,
    ⟨epos + j, ?_, Or.inl (hreg.2.2 j hj).1⟩, ⟨eqp + j, ?_, Or.inl (hreg.2.2 j hj).2.1⟩,
    (oqQReg_of hreg hj).mono fun i hi ↦ Or.inl hi, fun _ e he ↦ ?_⟩
  · have := hch (j + 1) (by omega)
    rw [oqChain_succ_zero hb0] at this
    exact this
  · rw [addr_gpow, Nat.add_zero]
  · rw [addr_gpow, Nat.add_zero]
  · refine ⟨fp + fs name + (j + e), ?_, Or.inr ⟨by omega, by omega⟩⟩
    rw [addr_gpow, Nat.add_assoc]

end
end LeanVM.Guest.B1
