module

public import Quantum.Qrom.Xmss.Costs.RegrindInv
public import Quantum.Xmss.Assembly.RecBadMass

@[expose] public section

/-!
# Re-grinds: the recorded hits of the selected digests

Without leaf reuse, a recorded trial read cell whose value hits its key's selected digest
(`recSWt`) costs at most `2^-128` per unit of trace: in the decompressed basis the hit has no
weight (`not_hit_of_rgInv`: a selection is a codeword of the trial's own search, the trials
before it no codewords, and the search stops at it), and Persistence converts the recorded
weight of a one-digest content predicate (`re_trace_recH_le_of_dec`, the sharp form of
RecBadMass's `re_trace_recH_wm_le` with no decompressed weight).

## Main statements

* `re_trace_recH_le_of_dec`: recorded weight `≤ κ tr σ` when the decompressed operator has no
  `⊥` at the cell and no weight on the content predicate (`κ` its value fraction).
* `trialW_recSWt_le`: at a trial read presented an operator on the invariant, `recSWt` weighs at
  most `2^-128 tr σ`.
* `recSPre_le`: `recSPre A θ ≤ 2^-128 K` with at most `K` classical calls, against an adversary
  that reuses no leaf.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

/-! ## Recorded weight without decompressed weight -/

namespace Quantum.Sponge

open Quantum

section convert

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {n : Type} [Fintype n] [DecidableEq n] {M : Type} [Fintype M] [DecidableEq M]

open scoped Classical in
/-- **Recorded weight without decompressed weight** (RecBadMass's `re_trace_recH_wm_le`, block by
block, with Persistence's `(√dec + √(κ tr))²` at `dec = 0`): if every `g w` excludes the empty
cell and has value fraction at most `κ`, and the decompressed operator has no `⊥` at `z` and no
weight on `g`, the weight of "cell `z` of `h` is recorded with a content in `g (W, m)`" is at most
`κ tr σ`. -/
theorem re_trace_recH_le_of_dec (z : Z) (g : Hw X Z × M → Option X → Prop) (hg : ∀ w, ¬ g w none)
    {κ : ℝ} (hκ : ∀ w, cellFrac (g w) ≤ κ)
    {σ : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hdec : QuerySupportedOn (fun m : n × HwReg X Z M ↦ m.2)
      {s | (s.1.1 z).isSome ∧ ¬ g s.2 (s.1.1 z)}
      (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) σ)) :
    (∑ a : n × HwReg X Z M, if g a.2.2 (a.2.1.1 z) then (σ a a).re else 0) ≤
      κ * σ.trace.re := by
  set C : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ :=
    (1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M with hC
  have hCh : Cᴴ = C := conjTranspose_one_kron_compressReg
  rw [MatrixMap.conj_apply, hCh] at hdec
  set σ' := C * σ * C with hσ'
  have hnb : QuerySupportedOn (fun m : n × HwReg X Z M ↦ m.2) {s | (s.1.1 z).isSome} σ' :=
    hdec.mono fun _ hs ↦ hs.1
  have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hCP : ∀ w, C * diagonal (rbInd w) = diagonal (rbInd w) * C := fun w ↦
    rb_compress_mul_rbInd w
  have hdecP : ∀ (E : Set (HwReg X Z M)) (inst : DecidablePred (· ∈ E)),
      (1 : Matrix n n ℂ) ⊗ₖ hwDecProj E =
        C * diagonal (fun a : n × HwReg X Z M ↦ if a.2 ∈ E then (1 : ℂ) else 0) * C := by
    intro E _
    rw [hwDecProj, ← rb_one_kron_diagonal (fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0),
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  have hcyc : ∀ D τ : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ,
      (C * D * C * τ).trace = (D * (C * τ * C)).trace := fun D τ ↦ by
    rw [show C * D * C * τ = C * (D * (C * τ)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm C, show D * (C * τ) * C = D * (C * τ * C) by
        simp only [Matrix.mul_assoc]]
  have key : ∀ w, ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ a a).re else 0) else 0) ≤
      κ * ∑ a, (if a.2.2 = w then (σ a a).re else 0) := by
    intro w
    have hσw : (diagonal (rbInd w) * σ * diagonal (rbInd w)).PosSemidef := by
      have h := hσ.mul_mul_conjTranspose_same (diagonal (rbInd w))
      rwa [conjTranspose_diagonal_rbInd] at h
    have hCw : C * (diagonal (rbInd w) * σ * diagonal (rbInd w)) * C =
        diagonal (rbInd w) * σ' * diagonal (rbInd w) := by
      calc C * (diagonal (rbInd w) * σ * diagonal (rbInd w)) * C =
          (C * diagonal (rbInd w)) * σ * (diagonal (rbInd w) * C) := by
            simp only [Matrix.mul_assoc]
        _ = (diagonal (rbInd w) * C) * σ * (C * diagonal (rbInd w)) := by rw [hCP w]
        _ = diagonal (rbInd w) * σ' * diagonal (rbInd w) := by
            rw [hσ']
            simp only [Matrix.mul_assoc]
    have hnbw : QuerySupportedOn (fun m : n × HwReg X Z M ↦ m.2) {s | (s.1.1 z).isSome}
        (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M)
          (diagonal (rbInd w) * σ * diagonal (rbInd w))) := by
      rw [MatrixMap.conj_apply, hCh, hCw]
      intro a b hab
      rw [rb_diagonal_conj_apply] at hab
      exact hnb a b fun h0 ↦ hab (by rw [show σ' a b = 0 from h0, mul_zero, zero_mul])
    have h := re_trace_recH_le z (g w) (hg w) hσw hnbw
    have e1 : (((1 : Matrix n n ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦
        if g w (s.1.1 z) then 1 else 0) * (diagonal (rbInd w) * σ * diagonal (rbInd w))).trace.re =
          ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ a a).re else 0) else 0) := by
      rw [rb_one_kron_diagonal, rb_trace_diagonal_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [rb_diagonal_conj_apply]
      by_cases h1 : a.2.2 = w <;> by_cases h2 : g w (a.2.1.1 z) <;> simp [rbInd, h1, h2]
    have e2 : (((1 : Matrix n n ℂ) ⊗ₖ hwDecProj {s : HwReg X Z M | g w (s.1.1 z)}) *
        (diagonal (rbInd w) * σ * diagonal (rbInd w))).trace.re =
          ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ' a a).re else 0) else 0) := by
      rw [hdecP, hcyc, hCw, rb_trace_diagonal_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [rb_diagonal_conj_apply]
      by_cases h1 : a.2.2 = w <;> by_cases h2 : g w (a.2.1.1 z) <;> simp [rbInd, h1, h2]
    have e3 : (diagonal (rbInd w) * σ * diagonal (rbInd w)).trace.re =
        ∑ a, (if a.2.2 = w then (σ a a).re else 0) := by
      rw [Matrix.trace, Complex.re_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Matrix.diag_apply, rb_diagonal_conj_apply]
      by_cases h1 : a.2.2 = w <;> simp [rbInd, h1]
    rw [e1, e2, e3] at h
    have hT0 : 0 ≤ ∑ a, (if a.2.2 = w then (σ a a).re else 0) :=
      Finset.sum_nonneg fun a _ ↦ by
        split_ifs
        exacts [hre a, le_rfl]
    have hD0 : ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ' a a).re else 0) else 0) =
        0 := Finset.sum_eq_zero fun a _ ↦ by
      split_ifs with h1 h2
      · have h0 : σ' a a = 0 := by
          by_contra hne
          exact (hdec a a hne).1.2 (by rw [h1]; exact h2)
        rw [h0, Complex.zero_re]
      · rfl
      · rfl
    rw [hD0, Real.sqrt_zero, zero_add, Real.sq_sqrt (mul_nonneg (cellFrac_nonneg _) hT0)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hκ w) hT0)
  have hsum : ∀ f : n × HwReg X Z M → Hw X Z × M → ℝ,
      ∑ w, ∑ a, (if a.2.2 = w then f a w else 0) = ∑ a, f a a.2.2 := fun f ↦ by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  have rhs : σ.trace.re = ∑ w, ∑ a, (if a.2.2 = w then (σ a a).re else 0) := by
    rw [hsum (fun a _ ↦ (σ a a).re), Matrix.trace, Complex.re_sum]
    rfl
  calc (∑ a : n × HwReg X Z M, if g a.2.2 (a.2.1.1 z) then (σ a a).re else 0)
      = ∑ w, ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ a a).re else 0) else 0) :=
        (hsum fun a w ↦ if g w (a.2.1.1 z) then (σ a a).re else 0).symm
    _ ≤ ∑ w, κ * ∑ a, (if a.2.2 = w then (σ a a).re else 0) :=
        Finset.sum_le_sum fun w _ ↦ key w
    _ = κ * σ.trace.re := by rw [rhs, Finset.mul_sum]

end convert

end Quantum.Sponge

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid HashSig LeanXmss
open Quantum.Xmss.Assembly (recSpec runtimeR extWeight extCls NoBot
  totalWeight_le_of_forallQueries)
open Quantum.Xmss.Hybrid (totalWeight_const_mul_weight)

attribute [local irreducible] xmssRom

/-! ## A trial read on the invariant -/

section trial

variable {θ : HPos → Digest}

/-- The content of a recorded hit of key `(l, e)` at the cell `z`, read from the hardwired cells
and the memory. -/
def HitG (z : HashDomain) (l : Layer) (e : KeyIndex) (w : Hw HashOutput HashDomain × QMem)
    (o : Option HashOutput) : Prop :=
  ∃ y sel, o = some y ∧ w.2.2 l e = some sel ∧ sel.1 ≠ z ∧ truncateHash y = sel.2

open scoped Classical in
theorem cellFrac_hitG_le (z : HashDomain) (l : Layer) (e : KeyIndex)
    (w : Hw HashOutput HashDomain × QMem) : cellFrac (HitG z l e w) ≤ (2 ^ 128 : ℝ)⁻¹ := by
  unfold cellFrac
  rw [← two_pow_div_card_hashOutput]
  gcongr
  unfold HitG
  rcases hw : w.2.2 l e with _ | sel
  · simp
  · exact_mod_cast (Finset.card_le_card fun y hy ↦ by
      rw [Finset.mem_filter] at hy ⊢
      obtain ⟨y', sel', h1, h2, -, h4⟩ := hy.2
      cases h1
      cases h2
      exact ⟨Finset.mem_univ _, h4⟩).trans (card_fiber_truncateHash_le sel.2)

/-- **No decompressed hit at a trial read**: within a search, the key's selection is a codeword of
the search's own trials, the trials before it no codewords and the search's earlier trials no
codewords, so the read cell's value does not truncate to the selected digest. -/
theorem not_hit_of_rgInv {l : Layer} {e : KeyIndex} {msg : MsgBytes} {base : Randomizer} {j : ℕ}
    {rd : HashDomain → Option HashOutput} {s : RReg SelMem}
    (hs : s ∈ rgInv θ (.srch l e msg base j, rd)) :
    (s.1.1 (trialCell (tabOf θ).param l e msg base j)).isSome ∧
      ¬HitG (trialCell (tabOf θ).param l e msg base j) l e s.2
        (s.1.1 (trialCell (tabOf θ).param l e msg base j)) := by
  obtain ⟨⟨hnb, hmsg, -, -⟩, -, hcur, hpre⟩ := hs
  refine ⟨hnb.1 _, ?_⟩
  rintro ⟨y, sel, hy, hsel, hne, ht⟩
  have hv : hvw s (trialCell (tabOf θ).param l e msg base j) = y := by
    show (((s.2.1.1 _).or (s.1.1 _)).getD 0) = y
    rw [hmsg _ l e (slotOf_trialCell _ l e msg base j), hy]
    rfl
  obtain ⟨j', h1, -, h3, h4, h5⟩ := hcur sel hsel
  rcases lt_trichotomy j' j with hlt | rfl | hgt
  · have h := (hpre j' hlt).2
    rw [← h1, ← h3] at h
    exact h h4
  · exact hne h1
  · have h := (h5 j hgt).2
    rw [hv, ht] at h
    exact h h4

/-- **The recorded hits at a trial read on the invariant** weigh at most `2^-128 tr σ`. -/
theorem trialW_recSWt_le {μ : RgMode} {c : HwRead HashOutput HashDomain QMem}
    (hok : rgRdOk (tabOf θ).param μ.1 c)
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × RReg SelMem ↦ m.2) (rgInv θ μ)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain QMem) σ)) :
    trialW recSWt c σ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
  classical
  obtain ⟨σ₀, rd⟩ := μ
  cases σ₀ with
  | free => exact hok.elim
  | srch l e msg base j =>
    have hc : c = trialRead (trialCell (tabOf θ).param l e msg base j) l e := hok
    subst hc
    rw [trialW_trialRead _ (slotOf_trialCell _ l e msg base j)]
    have hconv := re_trace_recH_le_of_dec (trialCell (tabOf θ).param l e msg base j)
      (HitG (trialCell (tabOf θ).param l e msg base j) l e)
      (fun _ ⟨_, _, h, _⟩ ↦ by cases h) (cellFrac_hitG_le _ l e) hσ
      (hs.mono fun s hs' ↦ not_hit_of_rgInv hs')
    have he : ∑ q, recSWt (trialCell (tabOf θ).param l e msg base j) l e q.2 * (σ q q).re =
        ∑ q : Unit × RReg SelMem, if HitG (trialCell (tabOf θ).param l e msg base j) l e q.2.2
          (q.2.1.1 (trialCell (tabOf θ).param l e msg base j)) then (σ q q).re else 0 := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      unfold recSWt
      by_cases h1 : RecHitQ (trialCell (tabOf θ).param l e msg base j) l e q.2
      · have h2 : HitG (trialCell (tabOf θ).param l e msg base j) l e q.2.2
            (q.2.1.1 (trialCell (tabOf θ).param l e msg base j)) := h1
        rw [ite_eq_left h1, ite_eq_left h2, one_mul]
      · have h2 : ¬HitG (trialCell (tabOf θ).param l e msg base j) l e q.2.2
            (q.2.1.1 (trialCell (tabOf θ).param l e msg base j)) := h1
        rw [ite_eq_right h1, ite_eq_right h2, zero_mul]
    rw [he]
    refine (ENNReal.ofReal_le_ofReal hconv).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

end trial

/-! ## The prefix -/

/-- **The recorded hits of the selected digests along the prefix**: against an adversary that
reuses no leaf, with at most `K` classical calls, `recSPre A θ ≤ 2^-128 K`. -/
theorem recSPre_le (A : Adversary) (hleaf : NoLeafReuse A) (θ : HPos → Digest) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    recSPre A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * K := by
  unfold recSPre preTot
  refine (totalWeight_le_of_forallQueries (runtimeR m0Q) .instruments
    (fun i σ ↦ ∃ μ, rgOkZ θ μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) (rgInv θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpec SelMem).In i) ((RSpec SelMem).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain QMem) σ))
    (fun _ _ _ h ↦ h) (w' := fun i σ ↦ (2 ^ 128 : ℝ≥0∞)⁻¹ * trW i σ) (fun i σ hσ hI ↦ ?_)
    (prefixQ A θ) initQ_posSemidef (forallQueries_rgInv θ hleaf)).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · obtain ⟨μ, hok, hs⟩ := hI
      exact trialW_recSWt_le hok hσ hs
    · exact zero_le
    · exact zero_le
  · exact (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments
      ((2 ^ 128 : ℝ≥0∞)⁻¹) trW (prefixQ A θ) initQ)).trans
      (mul_le_mul_of_nonneg_left (totalWeight_trW_le _ hK) zero_le)

end Quantum.Qrom.Xmss

end
