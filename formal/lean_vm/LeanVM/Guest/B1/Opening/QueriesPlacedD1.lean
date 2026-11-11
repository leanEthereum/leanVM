/-
  LeanVM.Guest.B1.Opening.QueriesPlacedD1

  `opening_queries` at level 0 is `CompleteAtB`.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlacedL
public import LeanVM.Guest.B1.Opening.QueriesMainW
public import LeanVM.Guest.AcceptableChild

/-!
# `opening_queries` at level 0, `CompleteAtB`

The honest data of the call: the iterations `N`, the rounds' challenges `rounds`, the final
coefficients `hsv` (final level), the queries' positions `qs`, rows `rows` and siblings below the
cap `sibs` (`oqW`), the window runs at `g^(eb k)`; the caller's buffers at `g^ecap` (the cap),
`g^eflags`, `g^ecoefs` (the challenges), `g^ehs` (the final coefficients), `g^epos` (the points),
`g^eqp` (the window pointers).

* `OqLinMem`: what every memory holding the caller's words `Lin` holds: the challenges, the final
  coefficients, the points, the window pointers and windows, each query's cap leaf (its path's
  top) and its flag;
* `OqLinReg`: those words lie in `Lin`'s region;
* `OqStatic`: the opening's facts of each query: the position's range, the lengths, at the final
  level the fold the final polynomial at the point.

`oqMain1_completeAtB`: the function is `CompleteAtB` on `Lin`, returning the chain of the queries'
folds (or `0` at the final level), its own layout its chain buffer (`oqChainVals`), by a tree of
at most `fs name + (N + 1) + (N + 1) * fs loop + (odd + 2N) * fs walk` words (a `walk_path` frame a
query).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- A query's witness from the call's data: its position, its row, its siblings below the cap. -/
def oqW (qs : ℕ → ℕ) (rows : ℕ → List K) (sibs : ℕ → List Digest) (k : ℕ) : QW :=
  (qs k, rows k, sibs k)

/-- **What the memory holds of `opening_queries`' caller's words**: the rounds' challenges at
`coefs`, (final level) the final coefficients at `hs`, and for each query `k < Q` its point
`positions[k] = eOfNat (qs k)`, its window pointer `qptrs[k] = g^(eb k)`, its position's windows
there (`g^qwVal`), its cap leaf (its path's top) and its parent's flag. -/
def OqLinMem (rd : Reader) (s : Oq) (cap flags coefs hs positions qptrs : E)
    (rounds : List FoldRound) (hsv : List E) (eb qs : ℕ → ℕ) (rows : ℕ → List K)
    (sibs : ℕ → List Digest) (Q : ℕ) : Prop :=
  RoundsAt rd coefs rounds ∧ (s.final = 1 → WordsAt rd hs hsv) ∧
    ∀ k < Q, LoadHolds rd positions k (eOfNat (qs k)) ∧
      LoadHolds rd qptrs k (ofK (Parameters.addressOfIndex (eb k))) ∧
      (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd (ofK (Parameters.addressOfIndex (eb k))) i
        (gen ^ qwVal (s.pd + s.cd) s.cd (qs k) i)) ∧
      LoadHolds rd cap (2 * (2 ^ s.cd + qs k / 2 ^ s.pd))
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
      LoadHolds rd cap (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + 1)
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
      LoadHolds rd flags (2 ^ (s.cd - 1) + qs k / 2 ^ (s.pd + 1)) 1

/-- **Where those words lie**: in the region `R`. -/
def OqLinReg (R : ℕ → Prop) (s : Oq) (ecap eflags ecoefs ehs epos eqp : ℕ) (eb qs : ℕ → ℕ)
    (Q : ℕ) : Prop :=
  (∀ l < 2 * s.folds, R (ecoefs + l)) ∧ (s.final = 1 → ∀ l < s.nHs, R (ehs + l)) ∧
    ∀ k < Q, R (epos + k) ∧ R (eqp + k) ∧ (∀ i < qwN (s.pd + s.cd) s.cd, R (eb k + i)) ∧
      R (eflags + (qs k / 2 ^ (s.pd + 1) + 2 ^ (s.cd - 1))) ∧
      ∀ e < 2, R (ecap + (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + e))

/-- **The opening's static facts** of the queries `k < Q`: the position below `2^depth`, the row's
and the siblings' lengths, and (final level) the fold the final polynomial at the point. -/
def OqStatic (s : Oq) (rounds : List FoldRound) (hsv : List E) (qs : ℕ → ℕ) (rows : ℕ → List K)
    (sibs : ℕ → List Digest) (Q : ℕ) : Prop :=
  ∀ k < Q, qs k < 2 ^ (s.pd + s.cd) ∧ (rows k).length = rowLen s.base s.folds ∧
    (sibs k).length = s.pd ∧
    (s.final = 1 → foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds =
      novelSum hsv (wsChain (s.vs.map K.ofBits) (eOfNat (qs k))) s.nHs s.hsBits)

theorem cap_index (q pd cd e : ℕ) :
    4 * (q / 2 ^ (pd + 1)) + (if q.testBit pd then 2 else 0) + (2 ^ (cd + 1) + e) =
      2 * (2 ^ cd + q / 2 ^ pd) + e := by
  have hsplit : q / 2 ^ pd = 2 * (q / 2 ^ (pd + 1)) + (if q.testBit pd then 1 else 0) := by
    rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    by_cases h : q / 2 ^ pd % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  rw [hsplit, pow_succ]
  split <;> ring

theorem limb_addr (b k : ℕ) : (ofK (Parameters.addressOfIndex b)).limb 0 *
    Parameters.addressOfIndex k =
    Parameters.addressOfIndex (b + k) := Main.addr_ofK b k

/-- The query region `OqQReg` from `OqLinReg`. -/
theorem oqQReg_of {R : ℕ → Prop} {s : Oq} {ecap eflags ecoefs ehs epos eqp : ℕ}
    {eb qs : ℕ → ℕ} {Q : ℕ} (h : OqLinReg R s ecap eflags ecoefs ehs epos eqp eb qs Q) {k : ℕ}
    (hk : k < Q) :
    OqQReg R s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
      (ofK (Parameters.addressOfIndex ecoefs)) (ofK (Parameters.addressOfIndex ehs))
      (ofK (Parameters.addressOfIndex (eb k))) (qs k) := by
  obtain ⟨-, -, b, f, c⟩ := h.2.2 k hk
  refine ⟨fun off ho ↦ ⟨_, limb_addr _ _, h.1 off ho⟩,
    fun hf off ho ↦ ⟨_, limb_addr _ _, h.2.1 hf off ho⟩,
    fun off ho ↦ ⟨_, limb_addr _ _, b off (by rw [qwN_eq]; exact ho)⟩,
    ⟨_, by rw [addr_gpow, Nat.add_assoc], f⟩, fun e he ↦ ⟨_, by rw [addr_gpow], ?_⟩⟩
  rw [Nat.add_assoc, cap_index _ _ _ _]
  exact c e he

theorem OqQReg.mono {R R' : ℕ → Prop} {s : Oq} {cap flags coefs hs bp : E} {q : ℕ}
    (h : OqQReg R s cap flags coefs hs bp q) (hR : ∀ i, R i → R' i) :
    OqQReg R' s cap flags coefs hs bp q :=
  ⟨fun o ho ↦ let ⟨i, h1, h2⟩ := h.co o ho; ⟨i, h1, hR i h2⟩,
    fun hf o ho ↦ let ⟨i, h1, h2⟩ := h.h hf o ho; ⟨i, h1, hR i h2⟩,
    fun o ho ↦ let ⟨i, h1, h2⟩ := h.b o ho; ⟨i, h1, hR i h2⟩,
    let ⟨i, h1, h2⟩ := h.f; ⟨i, h1, hR i h2⟩,
    fun e he ↦ let ⟨i, h1, h2⟩ := h.c e he; ⟨i, h1, hR i h2⟩⟩

theorem regionL_nil (i : ℕ) : ¬ RegionL [] i := by simp [RegionL]

/-- Query `k`'s `QD.Ok` from the memory and the static facts. -/
theorem qdOk_of_lin {rd : Reader} {s : Oq} {cap flags coefs hsp positions qptrs : E}
    {rounds : List FoldRound} {hsv : List E} {eb qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest} {Q : ℕ} (hrl : rounds.length = s.folds)
    (hhl : s.final = 1 → hsv.length = s.nHs) (hst : OqStatic s rounds hsv qs rows sibs Q)
    (hm : OqLinMem rd s cap flags coefs hsp positions qptrs rounds hsv eb qs rows sibs Q)
    {k : ℕ} (hk : k < Q) (b : ℕ) (emit : Bool) (pr : ℕ) :
    (oqQD s b emit pr cap flags rounds hsv (oqW qs rows sibs k)).Ok rd coefs hsp
      (ofK (Parameters.addressOfIndex (eb k))) := by
  obtain ⟨hR, hW, hk'⟩ := hm
  obtain ⟨-, -, a2, a3, a4, a5⟩ := hk' k hk
  obtain ⟨qa, ra, sa, fa⟩ := hst k hk
  exact qdOk_of_mem ra sa qa a2 a3 a4 a5 hR hrl fun hf ↦ ⟨hW hf, hhl hf, fa hf⟩

/-- The chain's words: the queries' results. -/
theorem oqResV_W {s : Oq} {rounds : List FoldRound} {qs : ℕ → ℕ} {rows : ℕ → List K}
    {sibs : ℕ → List Digest} (hf : s.final ≠ 1) (k : ℕ) :
    oqResV s rounds (oqW qs rows sibs k) = foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds := by
  simp only [oqResV, hf, ↓reduceIte]
  rfl

/-- The returned word: at a non-final level the chain of the queries' results is that of their
folds. -/
theorem oqRet_eq (s : Oq) (odd : ℕ) (lamInv : E) (rounds : List FoldRound) (qs : ℕ → ℕ)
    (rows : ℕ → List K) (sibs : ℕ → List Digest) (N : ℕ) :
    (if s.final = 1 then 0 else
      oqChain odd s.base lamInv (fun k ↦ oqResV s rounds (oqW qs rows sibs k)) N) =
    (if s.final = 1 then 0 else
      oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N) := by
  by_cases hf : s.final = 1
  · simp only [hf, ↓reduceIte]
  · simp only [hf, ↓reduceIte]
    congr 1
    funext k
    exact oqResV_W hf k

/-- **`opening_queries` at level 0 is `CompleteAtB`.** -/
theorem oqMain1_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hfin : s.FinOk) (hb1 : s.base = 1) (hpd1 : 1 ≤ s.pd)
    (hcd : 2 ≤ s.cd) {odd : ℕ} (hodd : odd ≤ 1) {name wlk loop : String}
    (hW : WalkFn wlk s.pd s.cd) {fm fl : Fn}
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
    CompleteAtB fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lamInv,
        ofK (Parameters.addressOfIndex ecoefs), ofK (Parameters.addressOfIndex ehs),
        ofK (Parameters.addressOfIndex epos), ofK (Parameters.addressOfIndex eqp), gen ^ N]
      (Returns [if s.final = 1 then 0 else
        oqChain odd s.base lamInv (fun k ↦ foldRow (lanesOf s.base (rows k)) (K.ofBits (qs k)) rounds) N])
      (fs name + (N + 1) + (N + 1) * fs loop + (odd + 2 * N) * fs wlk) := by
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
  refine ⟨n, chainL, _, [], ⟨rfl, rfl⟩, by simpa using wAll,
    by simpa using dAll, le_of_eq (by rw [hn]; ring), fun rd hlow hm ↦ ?_⟩
  rw [List.nil_append, Main.memL_append] at hm
  obtain ⟨hmChain, hmLin⟩ := hm
  have hk := hmem rd hlow hmLin
  -- the chain buffer
  have hch : ∀ i ≤ N, LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) i
      (oqChain odd s.base lamInv ds i) := by
    intro i hi
    have := hmChain (fp + fs name, oqChainVals odd s.base lamInv ds N) (by rw [hchainL]; simp) i
      (by simp [oqChainVals]; omega)
    simpa [oqChainVals] using this
  refine relAtIn_dmono (D := fun _ ↦ False) ?_ (fun i hi ↦ absurd hi (regionL_nil i))
  rw [← oqRet_eq s odd lamInv rounds qs rows sibs N]
  refine oqMain1_placed (rounds := rounds) (hsv := hsv) (w := W 0)
    (bp := ofK (Parameters.addressOfIndex (eb 0))) (hNv := oqChain odd s.base lamInv ds N)
    (w1 := fun j ↦ W (odd + 2 * j)) (w2 := fun j ↦ W (odd + 2 * j + 1))
    (bp1 := fun j ↦ ofK (Parameters.addressOfIndex (eb (odd + 2 * j))))
    (bp2 := fun j ↦ ofK (Parameters.addressOfIndex (eb (odd + 2 * j + 1))))
    (v := fun j ↦ oqChain odd s.base lamInv ds j)
    coreProgram_wf fs cert hs hfin hpd1 hcd hodd hW hfm hpm hbm hfl hpl hbl hlp hN
    (fun ho ↦ ?_) (fun ho ↦ ?_) (fun _ ↦ hch N le_rfl) (fun j hj ↦ ?_)
  · -- the odd first query
    subst ho
    obtain ⟨x0, b0, -⟩ := hk.2.2 0 (by omega)
    refine ⟨x0, b0, qdOk_of_lin hrl hhl hst hk (by omega) _ _ _, ?_,
      ⟨_, limb_addr _ _, (hreg.2.2 0 (by omega)).1⟩,
      ⟨_, limb_addr _ _, (hreg.2.2 0 (by omega)).2.1⟩, oqQReg_of hreg (by omega)⟩
    have := hch 0 (by omega)
    simpa [oqChain] using this
  · have := hch 0 (by omega)
    simpa [oqChain, ho] using this
  · -- an iteration
    obtain ⟨xa, ba, -⟩ := hk.2.2 (odd + 2 * j) (by omega)
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

end
end LeanVM.Guest.B1
