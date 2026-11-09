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

The honest data of the call: the iterations `N`, the queries' positions `qs`, rows `rows` and
siblings below the cap `sibs`, the weights `w`, the window runs at `g^(eb k)`; the caller's buffers
at `g^ecap` (the cap), `g^eflags`, `g^eqp` (the window pointers), `g^ewp` (the weights).

* `OqLinMem`: what every memory holding the caller's words `Lin` holds: the weights, the window
  pointers and windows, each query's cap leaf (its path's top) and its flag;
* `OqLinReg`: those words lie in `Lin`'s region.

`oqMain1_completeAtB`: the function is `CompleteAtB` on `Lin`, returning the chain's end times
`λ_n`, its own layout its chain buffer (`oqChainVals`), by a tree of at most
`fs name + (N + 1) + (N + 1) * fs loop + (odd + 2N) * fs walk` words (a `walk_path` frame a query).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- **What the memory holds of `opening_queries`' caller's words**: the weights at `wp`, and for
each query `k < Q` its window pointer `qptrs[k] = g^(eb k)`, its position's windows there
(`g^qwVal`), its cap leaf (its path's top) and its parent's flag. -/
def OqLinMem (rd : Reader) (s : Oq) (cap flags wp qptrs : E) (w : ℕ → E) (eb qs : ℕ → ℕ)
    (rows : ℕ → List K) (sibs : ℕ → List Digest) (Q : ℕ) : Prop :=
  (∀ l < s.lo + s.I / s.lo, LoadHolds rd wp l (w l)) ∧
    ∀ k < Q, LoadHolds rd qptrs k (ofK (Parameters.addressOfIndex (eb k))) ∧
      (∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd (ofK (Parameters.addressOfIndex (eb k))) i
        (gen ^ qwVal (s.pd + s.cd) s.cd (qs k) i)) ∧
      LoadHolds rd cap (2 * (2 ^ s.cd + qs k / 2 ^ s.pd))
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).1 ∧
      LoadHolds rd cap (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + 1)
        (digestHalves (climbD (merkleLeafDigest (rows k)) (qs k) (sibs k))).2 ∧
      LoadHolds rd flags (2 ^ (s.cd - 1) + qs k / 2 ^ (s.pd + 1)) 1

/-- **Where those words lie**: in the region `R`. -/
def OqLinReg (R : ℕ → Prop) (s : Oq) (ecap eflags eqp ewp : ℕ) (eb qs : ℕ → ℕ) (Q : ℕ) : Prop :=
  (∀ l < s.lo + s.I / s.lo, R (ewp + l)) ∧
    ∀ k < Q, R (eqp + k) ∧ (∀ i < qwN (s.pd + s.cd) s.cd, R (eb k + i)) ∧
      R (eflags + (qs k / 2 ^ (s.pd + 1) + 2 ^ (s.cd - 1))) ∧
      ∀ e < 2, R (ecap + (2 * (2 ^ s.cd + qs k / 2 ^ s.pd) + e))

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
theorem oqQReg_of {R : ℕ → Prop} {s : Oq} {ecap eflags eqp ewp : ℕ}
    {eb qs : ℕ → ℕ} {Q : ℕ} (h : OqLinReg R s ecap eflags eqp ewp eb qs Q) {k : ℕ} (hk : k < Q) :
    OqQReg R s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
      (ofK (Parameters.addressOfIndex ewp)) (ofK (Parameters.addressOfIndex (eb k))) (qs k) := by
  obtain ⟨-, b, f, c⟩ := h.2 k hk
  refine ⟨fun off ho ↦ ⟨_, limb_addr _ _, h.1 off ho⟩,
    fun off ho ↦ ⟨_, limb_addr _ _, b off (by rw [qwN_eq]; exact ho)⟩,
    ⟨_, by rw [addr_gpow, Nat.add_assoc], f⟩, fun e he ↦ ⟨_, by rw [addr_gpow], ?_⟩⟩
  rw [Nat.add_assoc, cap_index _ _ _ _]
  exact c e he

theorem OqQReg.mono {R R' : ℕ → Prop} {s : Oq} {cap flags wp bp : E} {q : ℕ}
    (h : OqQReg R s cap flags wp bp q) (hR : ∀ i, R i → R' i) : OqQReg R' s cap flags wp bp q :=
  ⟨fun o ho ↦ let ⟨i, h1, h2⟩ := h.w o ho; ⟨i, h1, hR i h2⟩,
    fun o ho ↦ let ⟨i, h1, h2⟩ := h.b o ho; ⟨i, h1, hR i h2⟩,
    let ⟨i, h1, h2⟩ := h.f; ⟨i, h1, hR i h2⟩,
    fun e he ↦ let ⟨i, h1, h2⟩ := h.c e he; ⟨i, h1, hR i h2⟩⟩

theorem regionL_nil (i : ℕ) : ¬ RegionL [] i := by simp [RegionL]

/-- **`opening_queries` at level 0 is `CompleteAtB`.** -/
theorem oqMain1_completeAtB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ)
    {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1) (hpd1 : 1 ≤ s.pd) (hcd : 2 ≤ s.cd) {odd : ℕ}
    (hodd : odd ≤ 1) {name wlk loop : String} (hW : WalkFn wlk s.pd s.cd) {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd wlk loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd wlk loop) (hlp : coreProgram.loop loop = true)
    {Lin : Main.Layout} {N : ℕ} (hN : N + 1 < ordG) {ecap eflags eqp ewp : ℕ} {lam lamN : E}
    (hlam : lam ≠ 0) {w : ℕ → E} {eb qs : ℕ → ℕ} {rows : ℕ → List K} {sibs : ℕ → List Digest}
    (hst : ∀ k < odd + 2 * N, qs k < 2 ^ (s.pd + s.cd) ∧ (rows k).length = s.R ∧
      (sibs k).length = s.pd)
    (hreg : OqLinReg (RegionL Lin) s ecap eflags eqp ewp eb qs (odd + 2 * N))
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin →
      OqLinMem rd s (ofK (Parameters.addressOfIndex ecap)) (ofK (Parameters.addressOfIndex eflags))
        (ofK (Parameters.addressOfIndex ewp)) (ofK (Parameters.addressOfIndex eqp)) w eb qs rows
            sibs (odd + 2 * N)) :
    CompleteAtB fs cert κ name Lin
      [ofK (Parameters.addressOfIndex ecap), ofK (Parameters.addressOfIndex eflags), lam, lamN,
        ofK (Parameters.addressOfIndex eqp), ofK (Parameters.addressOfIndex ewp), gen ^ N]
      (Returns [oqChain odd s.base lam⁻¹ (fun k ↦ rowDot s.base s.I (rows k) w) N * lamN])
      (fs name + (N + 1) + (N + 1) * fs loop + (odd + 2 * N) * fs wlk) := by
  intro fp
  set ds : ℕ → E := fun k ↦ rowDot s.base s.I (rows k) w with hds
  obtain ⟨chainL, hchainL⟩ : ∃ L : Main.Layout,
      L = [(fp + fs name, oqChainVals odd s.base lam ds N)] := ⟨_, rfl⟩
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
  obtain ⟨hw, hk⟩ := hmem rd hlow hmLin
  -- the chain buffer
  have hch : ∀ i ≤ N, LoadHolds rd (ofK (Parameters.addressOfIndex (fp + fs name))) i
      (oqChain odd s.base lam⁻¹ ds i) := by
    intro i hi
    have := hmChain (fp + fs name, oqChainVals odd s.base lam ds N) (by rw [hchainL]; simp) i
      (by simp [oqChainVals]; omega)
    simpa [oqChainVals] using this
  refine relAtIn_dmono (D := fun _ ↦ False) ?_ (fun i hi ↦ absurd hi (regionL_nil i))
  refine oqMain1_placed (r := rows 0) (w := w) (q := qs 0) (sb := sibs 0)
    (bp := ofK (Parameters.addressOfIndex (eb 0))) (hNv := oqChain odd s.base lam⁻¹ ds N)
    (r1 := fun j ↦ rows (odd + 2 * j)) (r2 := fun j ↦ rows (odd + 2 * j + 1))
    (w1 := fun _ ↦ w) (w2 := fun _ ↦ w) (q1 := fun j ↦ qs (odd + 2 * j))
    (q2 := fun j ↦ qs (odd + 2 * j + 1)) (sb1 := fun j ↦ sibs (odd + 2 * j))
    (sb2 := fun j ↦ sibs (odd + 2 * j + 1)) (bp1 := fun j ↦ ofK (Parameters.addressOfIndex (eb (odd + 2 * j))))
    (bp2 := fun j ↦ ofK (Parameters.addressOfIndex (eb (odd + 2 * j + 1))))
    (v := fun j ↦ oqChain odd s.base lam⁻¹ ds j)
    coreProgram_wf fs cert hs hpd1 hcd hodd hW hfm hpm hbm hfl hpl hbl hlp hN hlam
    (fun ho ↦ ?_) (fun ho ↦ ?_) (hch N le_rfl) (fun j hj ↦ ?_)
  · -- the odd first query
    subst ho
    obtain ⟨b0, win0, c00, c01, f0⟩ := hk 0 (by omega)
    obtain ⟨q0, r0, s0⟩ := hst 0 (by omega)
    refine ⟨b0, qdOk_of_mem r0 s0 q0 win0 hw c00 c01 f0, ?_,
      ⟨_, limb_addr _ _, (hreg.2 0 (by omega)).1⟩, oqQReg_of hreg (by omega)⟩
    have := hch 0 (by omega)
    simpa [oqChain] using this
  · have := hch 0 (by omega)
    simpa [oqChain, ho] using this
  · -- an iteration
    obtain ⟨a1, a2, a3, a4, a5⟩ := hk (odd + 2 * j) (by omega)
    obtain ⟨b1, b2, b3, b4, b5⟩ := hk (odd + 2 * j + 1) (by omega)
    obtain ⟨qa, ra, sa⟩ := hst (odd + 2 * j) (by omega)
    obtain ⟨qb, rb, sb⟩ := hst (odd + 2 * j + 1) (by omega)
    refine ⟨qdOk_of_mem ra sa qa a2 hw a3 a4 a5, qdOk_of_mem rb sb qb b2 hw b3 b4 b5, ?_, ?_,
      hch j (by omega), ?_, fun e he ↦ ?_,
      (oqQReg_of hreg (by omega)).mono fun i hi ↦ Or.inl hi,
      (oqQReg_of hreg (by omega)).mono fun i hi ↦ Or.inl hi, fun e he ↦ ?_⟩
    · rw [show 2 * j + odd = odd + 2 * j by omega]; exact a1
    · rw [show 2 * j + odd + 1 = odd + 2 * j + 1 by omega]; exact b1
    · have := hch (j + 1) (by omega)
      rw [oqChain_succ_one hb1] at this
      exact this
    · refine ⟨eqp + (odd + 2 * j + e), ?_, Or.inl (hreg.2 _ (by omega)).1⟩
      rw [mul_assoc, ← pow_add, ← two_mul, addr_gpow]
      congr 1; omega
    · refine ⟨fp + fs name + (j + e), ?_, Or.inr ⟨by omega, by omega⟩⟩
      rw [addr_gpow, Nat.add_assoc]

end
end LeanVM.Guest.B1
