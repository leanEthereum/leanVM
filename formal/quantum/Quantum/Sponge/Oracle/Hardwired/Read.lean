module

public import Quantum.Sponge.Oracle.Hardwired.Event

@[expose] public section

/-!
# The read-port certificate

A classical port with a complete family of Kraus operators `K r` changes the weight of an event
`Q` by the *flip operator* `F = ∑ᵣ K rᴴ Q K r - Q`: `w' = w + tr (F σ)`. For any projector `P`
(below: the projector on the states whose read cell is recorded in the database) and every
`s > 0`, `F ≤ P' F P' + s⁻¹ P' F P F P' + (1 + s) P` with `P' = 1 - P`
(`posSemidef_read_certificate`). Hence, with `ε = tr (P' F P' σ)`, `ε' = tr (P' F P F P' σ)` and
`p = tr (P σ)`, `w' ≤ w + ε + p + 2 √(ε' p)` (`potential_read_le`): the flips from states whose
cell is empty cost `ε`, and their interference with the recorded states costs `2 √(ε' p)`.

For the ports of the hardwired runtime this is `potential_hwReadKraus_le` and
`potential_hwProgKraus_le`, which discharge the classical-port hypotheses of
`eventWeight_spongeHardwiredRuntime_le` with the costs `flipCost`.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder

namespace Quantum.Sponge

open Quantum

/-! ## The operator inequality -/

section operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Splitting an operator along a projector.** For a Hermitian `F`, a projector `P` and `s > 0`,
`F ≤ P' F P' + s⁻¹ P' F P F P' + s P + P F P`, with `P' = 1 - P`: the cross terms between the
ranges of `P'` and `P` cost `s⁻¹ P' F P F P' + s P`. -/
theorem posSemidef_split_sub (F P : Matrix n n ℂ) (hF : Fᴴ = F) (hP : Pᴴ = P) (hPP : P * P = P)
    {s : ℝ} (hs : 0 < s) :
    ((1 - P) * F * (1 - P) + s⁻¹ • ((1 - P) * F * P * F * (1 - P)) + s • P + P * F * P -
      F).PosSemidef := by
  set X := (1 - P) * F * P
  have hXh : Xᴴ = P * F * (1 - P) := by
    simp only [X, conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP, hF,
      Matrix.mul_assoc]
  have hXP : X * P = X := by simp only [X, Matrix.mul_assoc, hPP]
  have hPX : P * Xᴴ = Xᴴ := by rw [hXh, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
  have hXX : X * Xᴴ = (1 - P) * F * P * F * (1 - P) := by
    rw [hXh]
    simp only [X, Matrix.mul_assoc, ← Matrix.mul_assoc P P, hPP]
  have hsplit : F = (1 - P) * F * (1 - P) + X + Xᴴ + P * F * P := by
    rw [hXh]
    simp only [X, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have hsq : (X - s • P) * (X - s • P)ᴴ = X * Xᴴ - s • X - s • Xᴴ + (s * s) • P := by
    simp only [conjTranspose_sub, conjTranspose_smul, hP, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, hXP, hPX, hPP, star_trivial]
    rw [smul_sub, smul_smul]
    abel
  have hpos : (s⁻¹ • ((X - s • P) * (X - s • P)ᴴ)).PosSemidef :=
    (posSemidef_self_mul_conjTranspose _).smul (inv_nonneg.mpr hs.le)
  have heq : (1 - P) * F * (1 - P) + s⁻¹ • ((1 - P) * F * P * F * (1 - P)) + s • P +
      P * F * P - F = s⁻¹ • ((X - s • P) * (X - s • P)ᴴ) := by
    calc _ = (1 - P) * F * (1 - P) + s⁻¹ • (X * Xᴴ) + s • P + P * F * P -
          ((1 - P) * F * (1 - P) + X + Xᴴ + P * F * P) := by rw [← hXX, ← hsplit]
      _ = s⁻¹ • (X * Xᴴ) - X - Xᴴ + s • P := by abel
      _ = _ := by
          rw [hsq, smul_add, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul,
            inv_mul_cancel₀ hs.ne', one_smul, one_smul, ← mul_assoc, inv_mul_cancel₀ hs.ne',
            one_mul]
  rw [heq]
  exact hpos

variable {ι : Type*} [Fintype ι]

/-- **The read-port certificate.** For a complete family of Kraus operators `K r`, a projector `Q`,
any projector `P` and `s > 0`, with the flip operator `F = ∑ᵣ K rᴴ Q K r - Q`,
`∑ᵣ K rᴴ Q K r ≤ Q + P' F P' + s⁻¹ P' F P F P' + (1 + s) P`. -/
theorem posSemidef_read_certificate (K : ι → Matrix n n ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1)
    (Q P : Matrix n n ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (hP : Pᴴ = P) (hPP : P * P = P) {s : ℝ}
    (hs : 0 < s) :
    let F := ∑ r, (K r)ᴴ * Q * K r - Q
    (Q + (1 - P) * F * (1 - P) + s⁻¹ • ((1 - P) * F * P * F * (1 - P)) + (1 + s) • P -
      ∑ r, (K r)ᴴ * Q * K r).PosSemidef := by
  intro F
  have hQc : (1 - Q)ᴴ * (1 - Q) = 1 - Q := by
    rw [conjTranspose_sub, conjTranspose_one, hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hQQ, sub_self, sub_zero]
  have hQpos : Q.PosSemidef := by
    rw [← hQQ]
    nth_rewrite 1 [← hQ]
    exact posSemidef_conjTranspose_mul_self Q
  have hFh : Fᴴ = F := by
    simp only [F, conjTranspose_sub, conjTranspose_sum, conjTranspose_mul,
      conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]
  have h1F : (1 - F).PosSemidef := by
    have h : 1 - F = ∑ r, (K r)ᴴ * ((1 - Q)ᴴ * (1 - Q)) * K r + Q := by
      simp only [F, hQc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Finset.sum_sub_distrib,
        hK]
      abel
    rw [h]
    refine (Matrix.posSemidef_sum _ fun r _ ↦ ?_).add hQpos
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_assoc]
    exact posSemidef_conjTranspose_mul_self _
  have hPFP : (P - P * F * P).PosSemidef := by
    have key : ∀ G : Matrix n n ℂ, P - P * G * P = Pᴴ * (1 - G) * P := fun G ↦ by
      rw [hP, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hPP]
    rw [key F]
    exact h1F.conjTranspose_mul_mul_same P
  have h := (posSemidef_split_sub F P hFh hP hPP hs).add hPFP
  have heq : Q + (1 - P) * F * (1 - P) + s⁻¹ • ((1 - P) * F * P * F * (1 - P)) + (1 + s) • P -
      ∑ r, (K r)ᴴ * Q * K r =
      (1 - P) * F * (1 - P) + s⁻¹ • ((1 - P) * F * P * F * (1 - P)) + s • P + P * F * P - F +
        (P - P * F * P) := by
    simp only [F, add_smul, one_smul]
    abel
  rw [heq]
  exact h

/-- **The read-port bound on weights.** For a complete family of Kraus operators `K r`, a projector
`Q`, any projector `P` and a positive semidefinite `σ`, the weight on `Q` after the measurement
is at most `w + ε + p + 2 √(ε' p)`, with `ε = tr (P' F P' σ)`, `ε' = tr (P' F P F P' σ)` and
`p = tr (P σ)`. -/
theorem ofReal_trace_read_le (K : ι → Matrix n n ℂ) (hK : ∑ r, (K r)ᴴ * K r = 1)
    (Q P : Matrix n n ℂ) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (hP : Pᴴ = P) (hPP : P * P = P)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    let F := ∑ r, (K r)ᴴ * Q * K r - Q
    ∑' r, ENNReal.ofReal (MatrixMap.conj (Q * K r) σ).trace.re ≤
      ENNReal.ofReal (MatrixMap.conj Q σ).trace.re +
        ENNReal.ofReal ((1 - P) * F * (1 - P) * σ).trace.re + ENNReal.ofReal (P * σ).trace.re +
        2 * (ENNReal.ofReal ((1 - P) * F * P * F * (1 - P) * σ).trace.re *
          ENNReal.ofReal (P * σ).trace.re) ^ (2⁻¹ : ℝ) := by
  intro F
  have hterm : ∀ r, (MatrixMap.conj (Q * K r) σ).trace = ((K r)ᴴ * Q * K r * σ).trace :=
    fun r ↦ by
      rw [MatrixMap.trace_conj_apply, conjTranspose_mul, hQ, Matrix.mul_assoc (K r)ᴴ Q,
        ← Matrix.mul_assoc Q Q, hQQ]
      simp only [Matrix.mul_assoc]
  have hnn : ∀ r, 0 ≤ (MatrixMap.conj (Q * K r) σ).trace.re := fun r ↦
    (hσ.mul_mul_conjTranspose_same _).trace_re_nonneg
  set w' := ((∑ r, (K r)ᴴ * Q * K r) * σ).trace.re
  have hw' : ∑' r, ENNReal.ofReal (MatrixMap.conj (Q * K r) σ).trace.re = ENNReal.ofReal w' := by
    rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hnn r]
    congr 1
    simp only [w', hterm, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  set w := (Q * σ).trace.re
  have hw : (MatrixMap.conj Q σ).trace.re = w := by
    rw [MatrixMap.trace_conj_apply, hQ, hQQ]
  set e := ((1 - P) * F * (1 - P) * σ).trace.re
  set e' := ((1 - P) * F * P * F * (1 - P) * σ).trace.re
  set p := (P * σ).trace.re
  have hPpos : P.PosSemidef := by
    rw [← hPP]
    nth_rewrite 1 [← hP]
    exact posSemidef_conjTranspose_mul_self P
  have hp : 0 ≤ p := hPpos.trace_mul_re_nonneg hσ
  have he' : 0 ≤ e' := by
    have hFh : Fᴴ = F := by
      simp only [F, conjTranspose_sub, conjTranspose_sum, conjTranspose_mul,
        conjTranspose_conjTranspose, hQ, Matrix.mul_assoc]
    have h : (1 - P) * F * P * F * (1 - P) = ((1 - P) * F * P) * ((1 - P) * F * P)ᴴ := by
      simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hP, hFh,
        Matrix.mul_assoc, ← Matrix.mul_assoc P P, hPP]
    rw [show e' = ((1 - P) * F * P * F * (1 - P) * σ).trace.re from rfl, h]
    exact (posSemidef_self_mul_conjTranspose _).trace_mul_re_nonneg hσ
  have hle : ∀ s : ℝ, 0 < s → w' - w - e + e' ≤ (1 + s) * p + (1 + s⁻¹) * e' := fun s hs ↦ by
    have h := (posSemidef_read_certificate K hK Q P hQ hQQ hP hPP hs).trace_mul_re_nonneg hσ
    rw [Matrix.sub_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, Complex.sub_re, Complex.add_re, Complex.add_re,
      Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul] at h
    change 0 ≤ w + e + s⁻¹ * e' + (1 + s) * p - w' at h
    nlinarith
  have hopt := Real.le_sq_sqrt_add_sqrt_of_forall hp he' hle
  have hfin : w' ≤ w + e + p + 2 * √(e' * p) := by
    rw [Real.sqrt_mul he']
    rw [add_sq, Real.sq_sqrt hp, Real.sq_sqrt he'] at hopt
    nlinarith [Real.sqrt_nonneg p, Real.sqrt_nonneg e']
  rw [hw', hw]
  refine (ENNReal.ofReal_le_ofReal hfin).trans ?_
  refine ENNReal.ofReal_add_le.trans (add_le_add ?_ ?_)
  · exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  · rw [ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul he', ENNReal.ofReal_rpow_inv_two]
    norm_num

end operator

/-! ## The classical ports of the hardwired runtime -/

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

instance (c : HwRead X Z M) : Fintype c.Result := by
  cases c <;> exact inferInstanceAs (Fintype (Option _ × _))

instance (c : HwProg X Z) : Fintype c.Result := by
  cases c <;> exact inferInstanceAs (Fintype (Option _ × _))

variable [AddCommGroup X] [AddCommGroup Z]

/-- The Kraus operators of every read port form a complete family. -/
theorem sum_hwReadKraus (c : HwRead X Z M) : ∑ r, (hwReadKraus c r)ᴴ * hwReadKraus c r = 1 := by
  cases c with
  | readH z upd => exact sum_readKrausH z upd
  | readK x upd => exact sum_readKrausK x upd
  | readK' x upd => exact sum_readKrausK' x upd

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The Kraus operators of every program port form a complete family. -/
theorem sum_hwProgKraus (c : HwProg X Z) :
    ∑ r, (hwProgKraus (M := M) c r)ᴴ * hwProgKraus c r = 1 := by
  cases c with
  | programH z v => exact sum_programKrausH z v
  | programK x v => exact sum_programKrausK x v
  | programK' x v => exact sum_programKrausK' x v

/-- The cost of a classical step with Kraus operators `K r` for the event `S`, relative to a
projector `P`: `ε + p + 2 √(ε' p)`, with `F` the flip operator of the step. -/
noncomputable def flipCost (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] {ι : Type} [Fintype ι]
    (K : ι → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (P σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  let Q := (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S
  let F := ∑ r, (K r)ᴴ * Q * K r - Q
  ENNReal.ofReal ((1 - P) * F * (1 - P) * σ).trace.re + ENNReal.ofReal (P * σ).trace.re +
    2 * (ENNReal.ofReal ((1 - P) * F * P * F * (1 - P) * σ).trace.re *
      ENNReal.ofReal (P * σ).trace.re) ^ (2⁻¹ : ℝ)

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The event projector next to the trivial register is a projector. -/
theorem one_kronecker_hwProjector_proj (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S)ᴴ = (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S ∧
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) * ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) =
        (1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S := by
  have hq := isStarProjection_labelProjector (α := ℂ) (fun s : HwReg X Z M ↦ decide (s ∈ S)) true
  refine ⟨?_, ?_⟩
  · rw [conjTranspose_kronecker, conjTranspose_one]
    exact congrArg _ hq.isSelfAdjoint
  · rw [← mul_kronecker_mul, Matrix.one_mul]
    exact congrArg _ hq.isIdempotentElem

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **A classical step raises the weight of an event by at most its flip cost.** -/
theorem potential_kraus_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)] {ι : Type}
    [Fintype ι] (K : ι → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (hK : ∑ r, (K r)ᴴ * K r = 1) (P : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (hP : Pᴴ = P) (hPP : P * P = P) (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (K r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ + flipCost S K P σ := by
  obtain ⟨hQ, hQQ⟩ := one_kronecker_hwProjector_proj S
  have h := ofReal_trace_read_le K hK ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) P hQ hQQ hP
    hPP hσ
  have hpot : ∀ τ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ,
      QuantumRuntime.potential (hwProjector S) τ =
        ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector S) τ).trace.re :=
    fun τ ↦ by rw [QuantumRuntime.potential, MatrixMap.amplifyLeft_conj]
  simp only [hpot, ← LinearMap.comp_apply, ← MatrixMap.conj_mul]
  refine h.trans_eq ?_
  simp only [flipCost, add_assoc]

/-- **The read ports discharge the hypothesis of the graded event bound**, with the costs
`flipCost S (hwReadKraus c) (P c)`. -/
theorem potential_hwReadKraus_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (P : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (hP : ∀ c, (P c)ᴴ = P c) (hPP : ∀ c, P c * P c = P c) (c : HwRead X Z M)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ + flipCost S (hwReadKraus c) (P c) σ :=
  potential_kraus_le S _ (sum_hwReadKraus c) (P c) (hP c) (hPP c) σ hσ

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **The program ports discharge the hypothesis of the graded event bound**, with the costs
`flipCost S (hwProgKraus c) (P c)`. -/
theorem potential_hwProgKraus_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (P : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ)
    (hP : ∀ c, (P c)ᴴ = P c) (hPP : ∀ c, P c * P c = P c) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) (hσ : σ.PosSemidef) :
    ∑' r, QuantumRuntime.potential (hwProjector S) (MatrixMap.conj (hwProgKraus c r) σ) ≤
      QuantumRuntime.potential (hwProjector S) σ + flipCost S (hwProgKraus c) (P c) σ :=
  potential_kraus_le S _ (sum_hwProgKraus c) (P c) (hP c) (hPP c) σ hσ

end Quantum.Sponge

end
