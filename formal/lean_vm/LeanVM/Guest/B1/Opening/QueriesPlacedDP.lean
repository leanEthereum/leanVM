/-
  LeanVM.Guest.B1.Opening.QueriesPlacedDP

  `opening_queries` is `CompleteAtDP`: its pops are its queries' rows and walks' children, query by query.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedP3
public import LeanVM.Guest.B1.Opening.QueriesPlacedD1
public import LeanVM.Guest.B1.Main.CompleteP

/-!
# `opening_queries`, `CompleteAtDP`

`QueriesPlacedD1`'s and `QueriesPlacedD0`'s proofs with `oqMain1_placedP`, `oqMain0_placedP`.

* `oqQE`: a query's two entries, its row's cells and its walk's children; they read only the shape and the query's witness (`oqQE_eq`);
* `flatMap_range_pairs`: an odd first then pairs is the queries in order;
* `oqPops`: the call's entries, its queries' `oqQE` in order;
* `oqMain1_completeAtDP`, `oqMain0_completeAtDP`: the function pops `oqPops` on every memory.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **A query's entries**: its row's cells, its walk's children. -/
def oqQE (s : Oq) (w : QW) : List Pop :=
  ("merkle_leaf_rows", (oqQD s 0 true 0 0 0 [] [] w).rowVals) :: ((oqQD s 0 true 0 0 0 [] [] w).wd 0).wpPops

theorem oqQE_eq (s : Oq) (b : ℕ) (emit : Bool) (pr : ℕ) (cap flags : E) (rounds : List FoldRound) (hsv : List E)
    (w : QW) (bp : E) :
    ("merkle_leaf_rows", (oqQD s b emit pr cap flags rounds hsv w).rowVals) ::
      ((oqQD s b emit pr cap flags rounds hsv w).wd bp).wpPops = oqQE s w := rfl

/-- **The call's entries**: its `Q` queries' in order. -/
def oqPops (s : Oq) (W : ℕ → QW) (Q : ℕ) : List Pop := (List.range Q).flatMap fun k => oqQE s (W k)

theorem flatMap_range_pairs {α : Type} (f : ℕ → List α) {odd : ℕ} (hodd : odd ≤ 1) : ∀ N : ℕ,
    (List.range (odd + 2 * N)).flatMap f =
      (if odd = 1 then f 0 else []) ++ (List.range N).flatMap fun j => f (odd + 2 * j) ++ f (odd + 2 * j + 1)
  | 0 => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hodd with rfl | rfl
    · rfl
    · simp
  | N + 1 => by
    rw [show odd + 2 * (N + 1) = odd + 2 * N + 1 + 1 by ring, List.range_succ, List.range_succ,
      List.flatMap_append, List.flatMap_append, flatMap_range_pairs f hodd N, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- **`opening_queries` at level 0 is `CompleteAtDP`**: it pops its queries' entries in order. -/
theorem oqMain1_completeAtDP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb1 : s.base = 1) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) {odd : ℕ} (hodd : odd ≤ 1) {name wlk loop : String}
    (hW : WalkFn coreProgram wlk s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7])
    (hbm : fm.body = oqMainT s odd wlk loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {Lin : Main.Layout} {N : ℕ} (hN : N + 1 < ordG) {ecap eflags ecoefs ehs epos eqp : ℕ}
    {lamInv : E} {rounds : List FoldRound} {hsv : List E} (hrl : rounds.length = s.folds)
    (hhl : s.final = 1 → hsv.length = s.nHs) {eb qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest}
    (hst : OqStatic s rounds hsv qs rows sibs (odd + 2 * N))
    (hreg : OqLinReg (RegionL Lin) s ecap eflags ecoefs ehs epos eqp eb qs (odd + 2 * N))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
        (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
        (ofK (Parameters.addressOfIndex epos)) (ofK (Parameters.addressOfIndex eqp)) rounds hsv eb
        qs rows sibs (odd + 2 * N)) :
    CompleteAtDP fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N]
      (Returns [if s.final = 1 then 0 else
        oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (fun _ => oqPops s (oqW qs rows sibs) (odd + 2 * N)) := by
  intro fp
  set W := oqW qs rows sibs with hWd
  set ds : ℕ → E := fun k ↦ oqResV s rounds (W k) with hds
  obtain ⟨chainL, hchainL⟩ : ∃ L : Main.Layout,
      L = [(fp + fs name, oqChainVals odd s.base lamInv ds N)] := ⟨_, rfl⟩
  have wChain : Within chainL (fp + fs name) (N + 1) := by
    intro x hx
    simp only [hchainL, List.mem_singleton] at hx
    subst hx
    simp [oqChainVals]
  set n := fs name + (N + 1) + odd * fs wlk + ((N + 1) * fs loop + N * (2 * fs wlk)) with hn
  have wAll : Within chainL fp n := wChain.mono (by omega) (by omega)
  have dAll : DisjL chainL := by rw [hchainL]; exact List.pairwise_singleton _ _
  refine ⟨n, chainL, _, [], ⟨rfl, rfl⟩, by simpa using wAll, by simpa using dAll, fun rd hlow hm ↦ ?_⟩
  rw [List.nil_append, Main.memL_append] at hm
  obtain ⟨hmChain, hmLin⟩ := hm
  have hk := hmem rd hlow hmLin
  have hch : ∀ i ≤ N, LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) i
      (oqChain odd s.base lamInv ds i) := by
    intro i hi
    have := hmChain (fp + fs name, oqChainVals odd s.base lamInv ds N) (by rw [hchainL]; simp) i
      (by simp [oqChainVals]; omega)
    simpa [oqChainVals] using this
  refine RelAtInP.dmono (D := fun _ ↦ False) ?_ (fun i hi ↦ absurd hi (regionL_nil i))
  rw [← oqRet_eq s odd lamInv rounds qs rows sibs N]
  have hpe : oqMainPops s odd (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
      rounds hsv (W 0) (ofK (Parameters.addressOfIndex (eb 0))) ++
      (List.range N).flatMap (fun j => oqIt1Pops s (ofK (Parameters.addressOfIndex ecap))
        (ofK (Parameters.addressOfIndex eflags)) rounds hsv (W (odd + 2 * j)) (W (odd + 2 * j + 1))
        (ofK (Parameters.addressOfIndex (eb (odd + 2 * j))))
        (ofK (Parameters.addressOfIndex (eb (odd + 2 * j + 1))))) = oqPops s W (odd + 2 * N) := by
    rw [oqPops, flatMap_range_pairs _ hodd N, oqMainPops]
    split <;> rfl
  rw [← hpe]
  refine oqMain1_placedP (rounds := rounds) (hsv := hsv) (w := W 0)
    (bp := ofK (Parameters.addressOfIndex (eb 0))) (hNv := oqChain odd s.base lamInv ds N)
    (w1 := fun j ↦ W (odd + 2 * j)) (w2 := fun j ↦ W (odd + 2 * j + 1))
    (bp1 := fun j ↦ ofK (Parameters.addressOfIndex (eb (odd + 2 * j))))
    (bp2 := fun j ↦ ofK (Parameters.addressOfIndex (eb (odd + 2 * j + 1))))
    (v := fun j ↦ oqChain odd s.base lamInv ds j)
    coreProgram_wf fs cert hs hfin hpd1 hcd hodd hW hfm hpm hbm hfl hpl hbl hlp hN
    (fun ho ↦ ?_) (fun ho ↦ ?_) (fun _ ↦ hch N le_rfl) (fun j hj ↦ ?_)
  · subst ho
    obtain ⟨x0, b0, -⟩ := hk.2.2 0 (by omega)
    refine ⟨x0, b0, qdOk_of_lin hrl hhl hst hk (by omega) _ _ _, ?_,
      ⟨_, limb_addr _ _, (hreg.2.2 0 (by omega)).1⟩,
      ⟨_, limb_addr _ _, (hreg.2.2 0 (by omega)).2.1⟩, oqQReg_of hreg (by omega)⟩
    have := hch 0 (by omega)
    simpa [oqChain] using this
  · have := hch 0 (by omega)
    simpa [oqChain, ho] using this
  · obtain ⟨xa, ba, -⟩ := hk.2.2 (odd + 2 * j) (by omega)
    obtain ⟨xb, bb, -⟩ := hk.2.2 (odd + 2 * j + 1) (by omega)
    refine ⟨qdOk_of_lin hrl hhl hst hk (by omega) _ _ _, qdOk_of_lin hrl hhl hst hk (by omega) _ _ _,
      ?_, ?_, ?_, ?_, fun _ ↦ ⟨hch j (by omega), ?_⟩, fun e he ↦ ?_, fun e he ↦ ?_,
      (oqQReg_of hreg (by omega)).mono fun i hi ↦ Or.inl hi,
      (oqQReg_of hreg (by omega)).mono fun i hi ↦ Or.inl hi, fun _ e he ↦ ?_⟩
    · rw [show 2 * j + odd = odd + 2 * j by omega]; exact xa
    · rw [show 2 * j + odd + 1 = odd + 2 * j + 1 by omega]; exact xb
    · rw [show 2 * j + odd = odd + 2 * j by omega]; exact ba
    · rw [show 2 * j + odd + 1 = odd + 2 * j + 1 by omega]; exact bb
    · have := hch (j + 1) (by omega)
      rw [oqChain_succ_one hb1] at this
      exact this
    · refine ⟨epos + (odd + 2 * j + e), ?_, Or.inl (hreg.2.2 _ (by omega)).1⟩
      rw [mul_assoc, ← pow_add, ← two_mul, addr_gpow]
      congr 1; omega
    · refine ⟨eqp + (odd + 2 * j + e), ?_, Or.inl (hreg.2.2 _ (by omega)).2.1⟩
      rw [mul_assoc, ← pow_add, ← two_mul, addr_gpow]
      congr 1; omega
    · refine ⟨fp + fs name + (j + e), ?_, Or.inr ⟨by omega, by omega⟩⟩
      rw [addr_gpow, Nat.add_assoc]

/-- **`opening_queries` deeper is `CompleteAtDP`**: it pops its queries' entries in order. -/
theorem oqMain0_completeAtDP (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb0 : s.base = 0) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) {name wlk loop : String} (hW : WalkFn coreProgram wlk s.pd s.cd) {fm fl : Fn}
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
    CompleteAtDP fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N]
      (Returns [if s.final = 1 then 0 else
        oqChain 0 s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (fun _ => oqPops s (oqW qs rows sibs) N) := by
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
  refine ⟨n, chainL, _, [], ⟨rfl, rfl⟩, by simpa using wAll, by simpa using dAll, fun rd hlow hm ↦ ?_⟩
  rw [List.nil_append, Main.memL_append] at hm
  obtain ⟨hmChain, hmLin⟩ := hm
  have hk := hmem rd hlow hmLin
  have hch : ∀ i ≤ N, LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) i
      (oqChain 0 s.base lamInv ds i) := by
    intro i hi
    have := hmChain (fp + fs name, oqChainVals 0 s.base lamInv ds N) (by rw [hchainL]; simp) i
      (by simp [oqChainVals]; omega)
    simpa [oqChainVals] using this
  refine RelAtInP.dmono (D := fun _ ↦ False) ?_ (fun i hi ↦ absurd hi (regionL_nil i))
  rw [← oqRet_eq s 0 lamInv rounds qs rows sibs N,
    show oqPops s W N = (List.range N).flatMap (fun j => oqIt0Pops s (ofK (Parameters.addressOfIndex ecap))
      (ofK (Parameters.addressOfIndex eflags)) rounds hsv (W j) (ofK (Parameters.addressOfIndex (eb j)))) from rfl]
  refine oqMain0_placedP (rounds := rounds) (hsv := hsv) (hNv := oqChain 0 s.base lamInv ds N)
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
