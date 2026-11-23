module

public import Quantum.Xmss.Assembly.CostRefined
public import Quantum.Xmss.Assembly.CwRec
public import Quantum.Sponge.Oracle.Hardwired.Persistence

@[expose] public section

/-!
# The `RecBad` mass of the randomizer trials

CostRefined's `recBadPre` sums, along the challenge prefix, the weight of the `RecBad` states at the
trials' `h`-reads: the read cell `z` recorded (not hardwired), the state in `BadR`, the state with
the cell emptied not. This file splits it into three parts and moves the re-grind part to the
decompressed basis.

* **What one recorded `h` value can do** (`tgt_eq_of_emptied`, `recBad_cases`): goodness reads only
  `k`, `k'`, so emptying the cell keeps the union good; the event then needs a tail reaching its
  target through `z`. If the trial's own one-block tail reaches `z` in the union with a rate of the
  trial's digest (`TrialOn`; `trialOf` names a trial only up to it), goodness makes it the only
  tail at `z`, so the recorded value `v` hits the target of the trial's tail:
  `xmssTgtHw L W m [x] = some (trunc128 (xi + v))` (`RecHit`; the target of a message-slot tail is
  the selected digest of its key unless the tail is the selected input's). Otherwise the trial's
  own path is missing from the union (`RecOff`).
* **Re-grind or not** (`SameGrind`, `RegrindSel`, `RecHitA`, `RecHitB`): the key's selection was
  made by a trial of the same label (block of the same message, same base: a re-grind of a selected
  key), or not (another label of the same key, e.g. a bottom key signing a second message).
* **The conversion** (`re_trace_recH_wm_le`): Persistence's `re_trace_recH_le` for a content
  predicate that also depends on the hardwired cells and the memory (block by block in `(W, m)`,
  which the compression does not touch): recorded weight `≤ 2 · decompressed weight + 2 κ tr σ`.
  For `RecHitA` the content predicate is a single digest, `κ = 2^-128` (`cellFrac_hitG_le`), so
  `recHitAPre ≤ 2 decHitAPre + recConv` (`recHitAPre_le`), `recConv = 2^-127 clsCap ≤ 2^-60`
  (`recConv_le`).
* **The average** (`recBadAvg_of_parts`): `RecBadAvg A good (2 τA + recConv + τB + τO)` from the
  three remaining averaged bounds `DecHitAvg A good τA`, `RecHitBAvg A good τB`,
  `RecOffAvg A good τO`.

The remaining bounds and their routes:
* `DecHitAvg` (expected `0` up to static table terms): in the decompressed basis the table is a
  fixed function between program calls (DecUniform, Persistence). A re-grind of label `lab` reads
  the cells its first grind measured; trials before the selecting one measured non-codeword
  digests, the selected digest `d` is a codeword, so no re-grind trial value hits `d`, and the
  re-grind stops at the selecting trial (CwRec's search modes `CwMode` carry the trial index).
* `RecHitBAvg`: a trial of a label whose key was selected by another label reads a cell recorded
  before its own `k`-read; the trial blocks carry the label's undisclosed randomizer base, so this
  is CwRecView's hidden-base argument with the hit predicate "the value hits the selected digest"
  (CwRec's generic `HitPred`), `2^-128` per adversary entry times `2^-128` for the digest.
* `RecOffAvg`: right after the trial's `k`- and `k'`-reads with outcomes `a`, `c` the decompressed
  cells hold `a`, `c`; the compressed cell is empty or holds another value with weight at most
  `2 / |Z|` each (the overlap of `C |a⟩` with `|a⟩` is `1 - 1/|Z|`), so about `4 / |Z|` per read.
  `trialOf trialUpd` names the program's trial up to its rate's digest (EncRefined's
  `trialUpd_inj`), which `TrialOn` allows.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

/-! ## What one recorded `h` value can do -/

open Quantum.SufCma

namespace Quantum.Sponge

open Quantum

section classify

/-- **A recorded `h` value that alone puts the register into a target event**: if the state is in
`HwTargetBad`, the state with the cell `z` emptied is not, and the one-block tail `[x]` reaches `z`
with rate `xi` in the union, then the recorded value `v` at `z` makes `[x]` reach its target:
emptying keeps the union good (goodness reads only `k`, `k'`), so the event is a tail reaching its
target through `z`, which goodness makes `[x]`. -/
theorem tgt_eq_of_emptied {X Z Y M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    [AddCommGroup X] [AddCommGroup Z] {π : Equiv.Perm (X × Z)} {out : X → Y}
    {tgt : Hw X Z → M → List X → Option Y} {N : ℕ} {D : DbReg X Z} {W : Hw X Z} {m : M} {z : Z}
    {v x xi : X} (hW : W.1 z = none) (hD : D.1 z = some v)
    (hb : (D, W, m) ∈ HwTargetBad π out tgt N)
    (hnb : ((Function.update D.1 z none, D.2.1, D.2.2), W, m) ∉ HwTargetBad π out tgt N)
    (hon : IsHeadTail π (union W D) [x] z xi) :
    tgt W m [x] = some (out (xi + v)) := by
  obtain ⟨hN, hT⟩ := hb
  have hk : (union W (Function.update D.1 z none, D.2.1, D.2.2)).k = (union W D).k := rfl
  have hk' : (union W (Function.update D.1 z none, D.2.1, D.2.2)).k' = (union W D).k' := rfl
  have hU' : union W (Function.update D.1 z none, D.2.1, D.2.2) ∉ TargetBad π out (tgt W m) :=
    fun h ↦ hnb ⟨hN, h⟩
  rw [not_mem_targetBad_iff] at hU'
  obtain ⟨hG', hR'⟩ := hU'
  have hG : Good π (union W D) := (good_congr hk hk').1 hG'
  rcases hT with hbad | ⟨τ, y, hτ, z', xi', w, hht, hw, rfl⟩
  · exact absurd hG hbad
  · by_cases hz : z' = z
    · subst hz
      have hu : (union W D).h z' = some v := by
        rw [union_h_apply', hW, hD]
        rfl
      obtain rfl := Option.some_injective _ (hw.symm.trans hu)
      obtain ⟨rfl, rfl⟩ := hG.isHeadTail_unique hht hon
      exact hτ
    · exact absurd ⟨z', xi', w, (isHeadTail_congr hk hk').2 hht,
        (union_updH_off W D hz none).trans hw, rfl⟩ (hR' τ _ hτ)

end classify

/-! ## Recorded weight against decompressed weight, for a predicate also on `(W, m)` -/

section wmConvert

theorem rb_trace_diagonal_mul {N : Type} [Fintype N] [DecidableEq N] (d : N → ℂ)
    (τ : Matrix N N ℂ) : (diagonal d * τ).trace = ∑ a, d a * τ a a := by
  simp only [Matrix.trace, Matrix.diag, diagonal_mul]

theorem rb_diagonal_conj_apply {N : Type} [Fintype N] [DecidableEq N] (d : N → ℂ)
    (τ : Matrix N N ℂ) (a b : N) : (diagonal d * τ * diagonal d) a b = d a * τ a b * d b := by
  rw [mul_diagonal, diagonal_mul]

theorem rb_sq_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (√a + √b) ^ 2 ≤ 2 * a + 2 * b := by
  nlinarith [sq_nonneg (√a - √b), Real.sq_sqrt ha, Real.sq_sqrt hb]

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {n : Type} [Fintype n] [DecidableEq n] {M : Type} [Fintype M] [DecidableEq M]

/-- The indicator of the block `w` of the hardwired cells and the memory. -/
def rbInd (w : Hw X Z × M) (a : n × HwReg X Z M) : ℂ :=
  if a.2.2 = w then 1 else 0

omit [AddCommGroup X] [AddCommGroup Z] [Fintype n] [Fintype M] in
theorem rb_one_kron_diagonal (f : HwReg X Z M → ℂ) :
    (1 : Matrix n n ℂ) ⊗ₖ diagonal f = diagonal fun a : n × HwReg X Z M ↦ f a.2 := by
  rw [← diagonal_one, diagonal_kronecker_diagonal]
  congr 1
  funext a
  simp only [one_mul]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The compression commutes with the block indicators of the hardwired cells and the memory. -/
theorem rb_compress_mul_rbInd (w : Hw X Z × M) :
    ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) * diagonal (rbInd w) =
      diagonal (rbInd w) * ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases h : a.2.2 = b.2.2
  · rw [show rbInd w a = rbInd w b by simp only [rbInd, h], mul_comm]
  · have h0 : ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) a b = 0 := by
      rw [kroneckerMap_apply, compressReg, kroneckerMap_apply, Matrix.one_apply_ne h, mul_zero,
        mul_zero]
    rw [h0, zero_mul, mul_zero]

omit [AddCommGroup X] [AddCommGroup Z] [Fintype n] [Fintype M] in
theorem conjTranspose_diagonal_rbInd (w : Hw X Z × M) :
    (diagonal (rbInd (n := n) w))ᴴ = diagonal (rbInd w) := by
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : a.2.2 = w <;> simp [rbInd, h]

open scoped Classical in
/-- **Recorded weight against decompressed weight, for a content predicate depending on `(W, m)`**
(Persistence's `re_trace_recH_le` block by block in the hardwired cells and the memory, which the
compression does not touch): if every `g w` excludes the empty cell and has value fraction at most
`κ`, then on an operator with no decompressed `⊥` at `z` the weight of "cell `z` of `h` is recorded
with a content in `g (W, m)`" is at most twice the decompressed weight plus `2 κ tr σ`. -/
theorem re_trace_recH_wm_le (z : Z) (g : Hw X Z × M → Option X → Prop) (hg : ∀ w, ¬ g w none)
    {κ : ℝ} (hκ : ∀ w, cellFrac (g w) ≤ κ)
    {σ : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : n × HwReg X Z M ↦ m.2) {s | (s.1.1 z).isSome}
      (MatrixMap.conj ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) σ)) :
    (((1 : Matrix n n ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦ if g s.2 (s.1.1 z) then 1 else 0) *
        σ).trace.re ≤
      2 * (((1 : Matrix n n ℂ) ⊗ₖ hwDecProj {s : HwReg X Z M | g s.2 (s.1.1 z)}) * σ).trace.re +
        2 * κ * σ.trace.re := by
  have hdec : ∀ (E : Set (HwReg X Z M)) (inst : DecidablePred (· ∈ E)),
      (1 : Matrix n n ℂ) ⊗ₖ hwDecProj E =
        ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) *
          diagonal (fun a : n × HwReg X Z M ↦ if a.2 ∈ E then (1 : ℂ) else 0) *
            ((1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M) := by
    intro E _
    rw [hwDecProj, ← rb_one_kron_diagonal (fun s : HwReg X Z M ↦ if s ∈ E then (1 : ℂ) else 0),
      ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  set C : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ :=
    (1 : Matrix n n ℂ) ⊗ₖ compressReg X Z M with hC
  have hCh : Cᴴ = C := conjTranspose_one_kron_compressReg
  rw [MatrixMap.conj_apply, hCh] at hnb
  set σ' := C * σ * C with hσ'
  have hσ'psd : σ'.PosSemidef := by
    have h := hσ.mul_mul_conjTranspose_same C
    rw [hCh] at h
    rw [hσ']
    exact h
  have hre : ∀ a, 0 ≤ (σ a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hre' : ∀ a, 0 ≤ (σ' a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ'psd.diag_nonneg).1
  have hCP : ∀ w, C * diagonal (rbInd w) = diagonal (rbInd w) * C := fun w ↦
    rb_compress_mul_rbInd w
  have hcyc : ∀ D τ : Matrix (n × HwReg X Z M) (n × HwReg X Z M) ℂ,
      (C * D * C * τ).trace = (D * (C * τ * C)).trace := fun D τ ↦ by
    rw [show C * D * C * τ = C * (D * (C * τ)) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm C, show D * (C * τ) * C = D * (C * τ * C) by
        simp only [Matrix.mul_assoc]]
  -- The three terms per block `w`.
  have key : ∀ w, ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ a a).re else 0) else 0) ≤
      2 * ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ' a a).re else 0) else 0) +
        2 * κ * ∑ a, (if a.2.2 = w then (σ a a).re else 0) := by
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
      rw [hdec, hcyc, hCw, rb_trace_diagonal_mul, Complex.re_sum]
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
    have hD0 : 0 ≤ ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ' a a).re else 0)
        else 0) := Finset.sum_nonneg fun a _ ↦ by
      split_ifs
      exacts [hre' a, le_rfl, le_rfl]
    have hT0 : 0 ≤ ∑ a, (if a.2.2 = w then (σ a a).re else 0) :=
      Finset.sum_nonneg fun a _ ↦ by
        split_ifs
        exacts [hre a, le_rfl]
    have hcf := mul_le_mul_of_nonneg_right (hκ w) hT0
    refine h.trans ((rb_sq_sqrt_add_le hD0 (mul_nonneg (cellFrac_nonneg _) hT0)).trans ?_)
    linarith
  -- Summing the blocks.
  have hsum : ∀ f : n × HwReg X Z M → Hw X Z × M → ℝ,
      ∑ w, ∑ a, (if a.2.2 = w then f a w else 0) = ∑ a, f a a.2.2 := fun f ↦ by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  have lhs : (((1 : Matrix n n ℂ) ⊗ₖ diagonal fun s : HwReg X Z M ↦
      if g s.2 (s.1.1 z) then 1 else 0) * σ).trace.re =
        ∑ w, ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ a a).re else 0) else 0) := by
    rw [hsum (fun a w ↦ if g w (a.2.1.1 z) then (σ a a).re else 0), rb_one_kron_diagonal,
      rb_trace_diagonal_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases h1 : g a.2.2 (a.2.1.1 z) <;> simp [h1]
  have rhs1 : (((1 : Matrix n n ℂ) ⊗ₖ hwDecProj {s : HwReg X Z M | g s.2 (s.1.1 z)}) *
      σ).trace.re =
        ∑ w, ∑ a, (if a.2.2 = w then (if g w (a.2.1.1 z) then (σ' a a).re else 0) else 0) := by
    rw [hsum (fun a w ↦ if g w (a.2.1.1 z) then (σ' a a).re else 0), hdec, hcyc, ← hσ',
      rb_trace_diagonal_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    by_cases h1 : g a.2.2 (a.2.1.1 z) <;> simp [h1]
  have rhs2 : σ.trace.re = ∑ w, ∑ a, (if a.2.2 = w then (σ a a).re else 0) := by
    rw [hsum (fun a _ ↦ (σ a a).re), Matrix.trace, Complex.re_sum]
    rfl
  rw [lhs, rhs1, rhs2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun w _ ↦ key w

end wmConvert

end Quantum.Sponge

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The split of a `RecBad` state at a trial read -/

section split

attribute [local instance] badRDec

/-- Adding a value keeps the agreement of two rates' digests. -/
private theorem rb_trunc128_add_congr {a b : X} (h : trunc128 a = trunc128 b) (v : X) :
    trunc128 (a + v) = trunc128 (b + v) := by
  rw [trunc128_eq, trunc128_eq] at h
  rw [trunc128_eq, trunc128_eq]
  have h' := (bitsEquiv 128).symm.injective h
  refine congrArg (bitsEquiv 128).symm (funext fun j ↦ ?_)
  rw [Pi.add_apply, Pi.add_apply, congrFun h' j]

/-- The trial's own one-block tail `[t.x]` reaches the read cell `z` in the union of the hardwired
and the database cells, with a rate of the trial's digest (`trialOf` names a trial only up to its
rate's digest). -/
def TrialOn (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z Mem) : Prop :=
  ∃ xi, trunc128 xi = trunc128 t.xi ∧ IsHeadTail L.perm (union s.2.1 s.1) [t.x] z xi

/-- **A recorded value hitting the target of the trial's tail**: the cell `z` not hardwired, recorded
with a value `v` that makes the trial's tail `[t.x]` reach its target. -/
def RecHit (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z Mem) : Prop :=
  s.2.1.1 z = none ∧ ∃ v, s.1.1 z = some v ∧
    xmssTgtHw L s.2.1 s.2.2.2 [t.x] = some (trunc128 (t.xi + v))

/-- **A recorded cell off the trial's path**: the cell `z` recorded, not hardwired, and the trial's
own tail does not reach it in the union. -/
def RecOff (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z Mem) : Prop :=
  s.2.1.1 z = none ∧ s.1.1 z ≠ none ∧ ¬ TrialOn L z t s

/-- **A `RecBad` state at a trial read hits the target of the trial's tail, or is off its path**
(`tgt_eq_of_emptied`). -/
theorem recBad_cases {L : HonestTable} {z : Z} (t : TrialPt) {s : HwReg X Z Mem}
    (h : RecBad L z s) : RecHit L z t s ∨ RecOff L z t s := by
  obtain ⟨hW, hD, hb, hnb⟩ := h
  by_cases hon : TrialOn L z t s
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hD
    have hb' : (s.1, s.2.1, s.2.2.2) ∈ Bad L progCap := hb
    have hnb' : ((Function.update s.1.1 z none, s.1.2.1, s.1.2.2), s.2.1, s.2.2.2) ∉
        Bad L progCap := hnb
    obtain ⟨xi, hxi, hht⟩ := hon
    refine .inl ⟨hW, v, hv, ?_⟩
    rw [tgt_eq_of_emptied hW hv hb' hnb' hht, rb_trunc128_add_congr hxi v]
  · exact .inr ⟨hW, hD, hon⟩

/-- Two blocks of the same randomizer search: the trials `i` and `j` of the label `lab` from the
base `base` (CwRec's `cwBlk`). -/
def SameGrind (P : PublicParameter) (x x' : X) : Prop :=
  ∃ (lab : RLabel) (base : Randomizer) (i j : ℕ), x = cwBlk P lab base i ∧ x' = cwBlk P lab base j

/-- **A re-grind**: the trial's key is selected, by a block of the same search as the trial's. -/
def RegrindSel (L : HonestTable) (t : TrialPt) (m : Selections) : Prop :=
  ∃ sel, m t.l t.e = some sel ∧ SameGrind L.param t.x sel.1

/-- `RecHit` at a re-grind of a selected key. -/
def RecHitA (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z Mem) : Prop :=
  RecHit L z t s ∧ RegrindSel L t s.2.2.2

/-- `RecHit` off the re-grinds: the key selected by another label (or not at all). -/
def RecHitB (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z Mem) : Prop :=
  RecHit L z t s ∧ ¬ RegrindSel L t s.2.2.2

/-- **The content predicate of `RecHitA`**, on the hardwired cells and the memory `w` and the cell
content `o`. -/
def hitG (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem) (o : Option X) : Prop :=
  w.1.1 z = none ∧ RegrindSel L t w.2.2 ∧ ∃ v, o = some v ∧
    xmssTgtHw L w.1 w.2.2 [t.x] = some (trunc128 (t.xi + v))

theorem recHitA_iff (L : HonestTable) (z : Z) (t : TrialPt) (s : HwReg X Z Mem) :
    RecHitA L z t s ↔ hitG L z t s.2 (s.1.1 z) :=
  ⟨fun ⟨⟨h1, v, h2, h3⟩, h4⟩ ↦ ⟨h1, h4, v, h2, h3⟩, fun ⟨h1, h4, v, h2, h3⟩ ↦ ⟨⟨h1, v, h2, h3⟩, h4⟩⟩

theorem hitG_none (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem) :
    ¬ hitG L z t w none := fun ⟨_, _, _, h, _⟩ ↦ Option.some_ne_none _ h.symm

/-- Each digest has `2^960` preimages under `v ↦ trunc128 (xi + v)`. -/
theorem card_fiber_trunc128_add (xi : X) (d : Digest) :
    (Finset.univ.filter fun v : X ↦ trunc128 (xi + v) = d).card ≤ 2 ^ 960 := by
  have h := card_filter_out_add (out := trunc128) (F := 2 ^ 960) (fun d' ↦ card_fiber_trunc128 d')
    (fun d' ↦ d' = d) xi
  rw [h]
  have h1 : (Finset.univ.filter fun d' : Digest ↦ d' = d).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb ↦ (Finset.mem_filter.mp ha).2.trans
      (Finset.mem_filter.mp hb).2.symm
  calc (Finset.univ.filter fun d' : Digest ↦ d' = d).card * 2 ^ 960 ≤ 1 * 2 ^ 960 :=
        Nat.mul_le_mul_right _ h1
    _ = 2 ^ 960 := one_mul _

/-- A value with `hitG` makes the trial's tail reach its target. -/
theorem hitG_some_tgt {L : HonestTable} {z : Z} {t : TrialPt} {w : Hw X Z × Mem} {y : X}
    (h : hitG L z t w (some y)) : xmssTgtHw L w.1 w.2.2 [t.x] = some (trunc128 (t.xi + y)) := by
  obtain ⟨-, -, v, hv, hd⟩ := h
  rw [Option.some_injective _ hv]
  exact hd

/-- At most `2^960` values satisfy `hitG` (one target digest). -/
theorem card_hitG_le (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem)
    [DecidablePred fun y : X ↦ hitG L z t w (some y)] :
    (Finset.univ.filter fun y : X ↦ hitG L z t w (some y)).card ≤ 2 ^ 960 := by
  rcases hT : xmssTgtHw L w.1 w.2.2 [t.x] with _ | d
  · have h0 : (Finset.univ.filter fun y : X ↦ hitG L z t w (some y)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun y _ h ↦ by
        have h' := hitG_some_tgt h
        rw [hT] at h'
        exact Option.some_ne_none _ h'.symm
    rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  · exact card_filter_le_of_imp (card_fiber_trunc128_add t.xi d) fun y hy ↦ by
      have h' := hitG_some_tgt hy
      rw [hT] at h'
      exact (Option.some_injective _ h').symm

open scoped Classical in
/-- **The value fraction of `hitG`**: at most `2^-128` (one target digest). -/
theorem cellFrac_hitG_le (L : HonestTable) (z : Z) (t : TrialPt) (w : Hw X Z × Mem) :
    cellFrac (hitG L z t w) ≤ (2 ^ 128 : ℝ)⁻¹ := by
  unfold cellFrac
  rw [← two_pow_div_card_X]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_hitG_le L z t w) (Nat.cast_nonneg _)

/-- **`RecBad` splits** into `RecHitA`, `RecHitB` and `RecOff`. -/
theorem recBad_cases3 {L : HonestTable} {z : Z} (t : TrialPt) {s : HwReg X Z Mem}
    (h : RecBad L z s) : RecHitA L z t s ∨ RecHitB L z t s ∨ RecOff L z t s := by
  rcases recBad_cases t h with h | h
  · by_cases hr : RegrindSel L t s.2.2.2
    · exact .inl ⟨h, hr⟩
    · exact .inr (.inl ⟨h, hr⟩)
  · exact .inr (.inr h)

end split

/-! ## The weights and their sums along the prefix -/

section weights

open scoped Classical in
/-- The `RecHitA` mass of a trial read port (`0` at the other read ports). -/
noncomputable def recHitAW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if RecHitA L (trialOf trialUpd c).1
    (trialOf trialUpd c).2 q.2 then (σ q q).re else 0) else 0

open scoped Classical in
/-- The `RecHitB` mass of a trial read port. -/
noncomputable def recHitBW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if RecHitB L (trialOf trialUpd c).1
    (trialOf trialUpd c).2 q.2 then (σ q q).re else 0) else 0

open scoped Classical in
/-- The `RecOff` mass of a trial read port. -/
noncomputable def recOffW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal (∑ q, if RecOff L (trialOf trialUpd c).1
    (trialOf trialUpd c).2 q.2 then (σ q q).re else 0) else 0

open scoped Classical in
/-- **The decompressed `RecHitA` weight of a trial read port**: the weight of the decompressed
event "the cell's content satisfies `hitG`". -/
noncomputable def decHitAW (L : HonestTable) (c : HwRead X Z Mem)
    (σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ) : ℝ≥0∞ :=
  if IsTrial trialUpd c then ENNReal.ofReal ((((1 : Matrix Unit Unit ℂ) ⊗ₖ
    hwDecProj {s : HwReg X Z Mem | hitG L (trialOf trialUpd c).1 (trialOf trialUpd c).2 s.2
      (s.1.1 (trialOf trialUpd c).1)}) * σ).trace.re) else 0

/-- `recHitAW` summed along the prefix. -/
noncomputable def recHitAPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (recHitAW L) fun _ _ ↦ 0))
    (prefixR A L) initR

/-- `recHitBW` summed along the prefix. -/
noncomputable def recHitBPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (recHitBW L) fun _ _ ↦ 0))
    (prefixR A L) initR

/-- `recOffW` summed along the prefix. -/
noncomputable def recOffPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (recOffW L) fun _ _ ↦ 0))
    (prefixR A L) initR

/-- **The decompressed re-grind hit weight**, summed along the prefix. -/
noncomputable def decHitAPre (A : Adversary (X × Z)) (L : HonestTable) : ℝ≥0∞ :=
  (runtimeR m0R).totalWeight .instruments (extWeight (hwCost (decHitAW L) fun _ _ ↦ 0))
    (prefixR A L) initR

/-- A real sum over the three parts of `RecBad`. -/
theorem sum_ite_le_three {n : Type} [Fintype n] (P Q R S : n → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred R] [DecidablePred S] (f : n → ℝ) (hf : ∀ a, 0 ≤ f a)
    (h : ∀ a, P a → Q a ∨ R a ∨ S a) :
    ∑ a, (if P a then f a else 0) ≤ ∑ a, (if Q a then f a else 0) +
      ∑ a, (if R a then f a else 0) + ∑ a, (if S a then f a else 0) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  by_cases hP : P a
  · rw [ite_eq_left hP]
    rcases h a hP with hQ | hR | hS
    · rw [ite_eq_left hQ]
      have := hf a
      split_ifs <;> linarith
    · rw [ite_eq_left hR]
      have := hf a
      split_ifs <;> linarith
    · rw [ite_eq_left hS]
      have := hf a
      split_ifs <;> linarith
  · rw [ite_eq_right hP]
    have := hf a
    split_ifs <;> linarith

/-- **The `RecBad` mass of a port splits** into the three parts. -/
theorem recBadW_le (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef) :
    recBadW L c σ ≤ recHitAW L c σ + recHitBW L c σ + recOffW L c σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  unfold recBadW recHitAW recHitBW recOffW
  split_ifs with ht
  · exact (ENNReal.ofReal_le_ofReal (sum_ite_le_three _ _ _ _ _ hre fun q h ↦
      recBad_cases3 (trialOf trialUpd c).2 h)).trans
        (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl))
  · simp

/-- **`recBadPre` splits** into the three parts. -/
theorem recBadPre_le (A : Adversary (X × Z)) (L : HonestTable) :
    recBadPre A L ≤ recHitAPre A L + recHitBPre A L + recOffPre A L := by
  refine (totalWeight_le_totalWeight (runtimeR m0R) .instruments
    (w' := fun i σ ↦ extWeight (hwCost (recHitAW L) fun _ _ ↦ 0) i σ +
      extWeight (hwCost (recHitBW L) fun _ _ ↦ 0) i σ +
        extWeight (hwCost (recOffW L) fun _ _ ↦ 0) i σ) (fun i σ hσ ↦ ?_) (prefixR A L)
    initR_posSemidef).trans_eq ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · exact recBadW_le L c hσ
    · exact zero_le
    · exact zero_le
  · exact (totalWeight_add_weight (runtimeR m0R) .instruments
      (fun i σ ↦ extWeight (hwCost (recHitAW L) fun _ _ ↦ 0) i σ +
        extWeight (hwCost (recHitBW L) fun _ _ ↦ 0) i σ)
      (extWeight (hwCost (recOffW L) fun _ _ ↦ 0)) (prefixR A L) initR).trans
        (congrArg (· + recOffPre A L) (totalWeight_add_weight (runtimeR m0R) .instruments
          (extWeight (hwCost (recHitAW L) fun _ _ ↦ 0))
          (extWeight (hwCost (recHitBW L) fun _ _ ↦ 0)) (prefixR A L) initR))

end weights

/-! ## The conversion of the re-grind part -/

section convert

/-- **The conversion term** of the re-grind part: `2 · 2^-128` per unit of trial-read trace, at
most `clsCap` of it. -/
noncomputable def recConv : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * clsCap

set_option exponentiation.threshold 4096 in
/-- `recConv ≤ 2^-60` (`clsCap < 2^67`). -/
theorem recConv_le : recConv ≤ ENNReal.ofReal (1 / 2 ^ 60) := by
  unfold recConv
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [clsCap, verifyBlocks_eq, signBlocks_eq, progCap_eq]
  norm_num [lifetime, layerCount, layerHeight]

open scoped Classical in
/-- **A trial read port's `RecHitA` mass against its decompressed weight**: on a port input with
no decompressed `⊥`, `recHitAW ≤ 2 decHitAW + 2 · 2^-128 tr σ` (`re_trace_recH_wm_le` with
`hitG`, `cellFrac_hitG_le`). -/
theorem recHitAW_le (L : HonestTable) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hnb : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ)) :
    recHitAW L c σ ≤ 2 * decHitAW L c σ +
      ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * ENNReal.ofReal σ.trace.re := by
  unfold recHitAW decHitAW
  split_ifs with ht
  · generalize trialOf trialUpd c = zt
    obtain ⟨z, t⟩ := zt
    have hnb' : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2) {s | (s.1.1 z).isSome}
        (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z Mem) σ) :=
      fun a b h ↦ ⟨(show NoBotDb a.2.1 from (hnb a b h).1).1 z,
        (show NoBotDb b.2.1 from (hnb a b h).2).1 z⟩
    have h := re_trace_recH_wm_le z (hitG L z t) (hitG_none L z t) (cellFrac_hitG_le L z t) hσ hnb'
    have hl : (((1 : Matrix Unit Unit ℂ) ⊗ₖ diagonal fun s : HwReg X Z Mem ↦
        if hitG L z t s.2 (s.1.1 z) then 1 else 0) * σ).trace.re =
          ∑ q, if RecHitA L z t q.2 then (σ q q).re else 0 := by
      rw [rb_one_kron_diagonal, rb_trace_diagonal_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      by_cases hq : RecHitA L z t q.2
      · rw [ite_eq_left hq, ite_eq_left ((recHitA_iff L z t q.2).1 hq), one_mul]
      · rw [ite_eq_right hq, ite_eq_right fun h ↦ hq ((recHitA_iff L z t q.2).2 h), zero_mul,
          Complex.zero_re]
    rw [hl] at h
    calc ENNReal.ofReal (∑ q, if RecHitA L z t q.2 then (σ q q).re else 0)
        ≤ ENNReal.ofReal (2 * (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj {s : HwReg X Z Mem |
            hitG L z t s.2 (s.1.1 z)}) * σ).trace.re + 2 * (2 ^ 128 : ℝ)⁻¹ * σ.trace.re) :=
          ENNReal.ofReal_le_ofReal h
      _ ≤ ENNReal.ofReal (2 * (((1 : Matrix Unit Unit ℂ) ⊗ₖ hwDecProj {s : HwReg X Z Mem |
            hitG L z t s.2 (s.1.1 z)}) * σ).trace.re) +
            ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹ * σ.trace.re) := ENNReal.ofReal_add_le
      _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_ofNat]
  · exact zero_le

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The re-grind part against its decompressed weight**:
`recHitAPre ≤ 2 decHitAPre + recConv` (EncPorts' `forallQueries_preInv` gives the inputs no
decompressed `⊥`; the trial reads' traces add up to at most `clsCap`). -/
theorem recHitAPre_le (L : HonestTable) : recHitAPre A L ≤ 2 * decHitAPre A L + recConv := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  refine (totalWeight_le_of_forallQueries (runtimeR m0R) .instruments (PreInv q) hP
    (w' := fun i σ ↦ 2 * extWeight (hwCost (decHitAW L) fun _ _ ↦ 0) i σ +
      ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * extWeight (hwCost
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef hx).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · exact recHitAW_le L c hσ hI.2.2
    · exact zero_le
    · exact zero_le
  · refine (le_of_eq (totalWeight_add_weight (runtimeR m0R) .instruments
      (fun i σ ↦ 2 * extWeight (hwCost (decHitAW L) fun _ _ ↦ 0) i σ)
      (fun i σ ↦ ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹) * extWeight (hwCost
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re) i σ)
      (prefixR A L) initR)).trans (add_le_add (le_of_eq (totalWeight_const_mul_weight
        (runtimeR m0R) .instruments 2 (extWeight (hwCost (decHitAW L) fun _ _ ↦ 0))
        (prefixR A L) initR)) ((le_of_eq (totalWeight_const_mul_weight (runtimeR m0R)
          .instruments (ENNReal.ofReal (2 * (2 ^ 128 : ℝ)⁻¹)) (extWeight (hwCost
            (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
          (prefixR A L) initR)).trans ?_))
    unfold recConv
    gcongr
    exact totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L)

end convert

/-! ## The average -/

section avg

/-- **The remaining bound of the re-grind part**: over a good set, the average of the decompressed
re-grind hit weight `decHitAPre` is at most `τ` (expected `0` up to static table terms: in the
decompressed basis a re-grind reads the values its first grind measured). -/
def DecHitAvg (A : Adversary (X × Z)) (good : HonestTable → Prop) [DecidablePred good]
    (τ : ℝ≥0∞) : Prop :=
  uavg (fun L ↦ if good L then decHitAPre A L else 0) ≤ τ

/-- **The remaining bound of the other labels**: over a good set, the average of `recHitBPre` is at
most `τ` (`0` without leaf reuse: Assembly.NoReuse's `recHitBAvg_zero`). -/
def RecHitBAvg (A : Adversary (X × Z)) (good : HonestTable → Prop) [DecidablePred good]
    (τ : ℝ≥0∞) : Prop :=
  uavg (fun L ↦ if good L then recHitBPre A L else 0) ≤ τ

/-- **The remaining bound off the trial's path**: over a good set, the average of `recOffPre` is
at most `τ` (about `4 / |Z|` per trial read). -/
def RecOffAvg (A : Adversary (X × Z)) (good : HonestTable → Prop) [DecidablePred good]
    (τ : ℝ≥0∞) : Prop :=
  uavg (fun L ↦ if good L then recOffPre A L else 0) ≤ τ

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The `RecBad` mass of a table**: `recBadPre ≤ 2 decHitAPre + recConv + recHitBPre + recOffPre`. -/
theorem recBadPre_le_parts (L : HonestTable) :
    recBadPre A L ≤ 2 * decHitAPre A L + recConv + recHitBPre A L + recOffPre A L :=
  (recBadPre_le A L).trans (add_le_add (add_le_add (recHitAPre_le hperm hsign L) le_rfl) le_rfl)

/-- **`RecBadAvg` from the three remaining bounds**:
`RecBadAvg A good (2 τA + recConv + τB + τO)`, `recConv ≤ 2^-60`. -/
theorem recBadAvg_of_parts (good : HonestTable → Prop) [DecidablePred good] {τA τB τO : ℝ≥0∞}
    (hA : DecHitAvg A good τA) (hB : RecHitBAvg A good τB) (hO : RecOffAvg A good τO) :
    RecBadAvg A good (2 * τA + recConv + τB + τO) := by
  unfold RecBadAvg
  calc uavg (fun L ↦ if good L then recBadPre A L else 0)
      ≤ uavg (fun L ↦ 2 * (if good L then decHitAPre A L else 0) + recConv +
          (if good L then recHitBPre A L else 0) + (if good L then recOffPre A L else 0)) :=
        uavg_mono fun L ↦ by
          by_cases hL : good L
          · simp only [hL, ↓reduceIte]
            exact recBadPre_le_parts hperm hsign L
          · simp only [hL, ↓reduceIte, mul_zero, zero_add, add_zero]
            exact zero_le
    _ = 2 * uavg (fun L ↦ if good L then decHitAPre A L else 0) + uavg (fun _ ↦ recConv) +
          uavg (fun L ↦ if good L then recHitBPre A L else 0) +
          uavg (fun L ↦ if good L then recOffPre A L else 0) := by
        rw [uavg_add, uavg_add, uavg_add, uavg_const_mul]
    _ ≤ 2 * τA + recConv + τB + τO :=
        add_le_add (add_le_add (add_le_add (by gcongr; exact hA) (uavg_const_le _)) hB) hO

end avg

end Quantum.Xmss.Assembly

end
