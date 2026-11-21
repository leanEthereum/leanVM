module

public import Quantum.Sponge.Oracle.Hardwired.EventPar
public import QuantumFoundations.Pure.Vector

@[expose] public section

/-!
# The event bound with rounds of every sponge port, split by port

Programs over the hardwired runtime extended by classical ports, with rounds of one sponge port
each through the port map `p ↦ .inl (.inl (.inl p))`.

* **One port's fields** (`UpClosedAt`, `FreshAt`): the certificate of port `i` needs only the
  fields of `UpClosed` and `FreshBound` of port `i` (`posSemidef_spongeHardwired_certificate_at`,
  `l2_opNorm_commutator_spongeHardwired_le`, `l2_opNorm_commutator_hRound_le_at`).
* **Rounds slot by slot** (`l2_opNorm_commutator_roundProd_le`): the commutator of a round with
  the event, on grades at most `m`, is at most the sum of its slots' commutators, slot `j` on
  grades at most `m + j`; a round of `w` calls of `k` (or `k'`) raises the square root of the
  event weight by at most `w √(6 ε tr σ)` (`rpow_inv_two_potential_portRound_le`).
* **The event bound** (`rpow_inv_two_eventWeight_extend_split_le`): rounds of `h` are charged by
  depth with the rate `ε_h` of the cell events (Corollary C; a single `h` call is a round of width
  one), rounds of `k` or `k'` and single `k`, `k'` calls sequentially at the capacity rate `ε_c`,
  rounds mixing ports are excluded. With `q_h` calls of `h` in `d_h` rounds, `n_k` calls of `k`
  and `k'`, and `K` classical calls, `√w ≤ √(6 ε_h d_h q_h) + n_k √(6 ε_c) + √(∑ d)`.
-/

open Matrix IPFunctor
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

universe u v w u₁ v₁

namespace Quantum.Sponge

open Quantum QuantumRuntime OracleSpec

/-! ## One port's fields of upward closure and of the fresh bound -/

section port

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- The field of `UpClosed` of port `i`: filling an empty cell of its database stays in `S`. -/
def UpClosedAt (S : Set (Dbs X Z)) : SpongePort → Prop
  | .h => ∀ D ∈ S, ∀ z u, D.h z = none →
      ({ D with h := Function.update D.h z (some u) } : Dbs X Z) ∈ S
  | .k => ∀ D ∈ S, ∀ x u, D.k x = none →
      ({ D with k := Function.update D.k x (some u) } : Dbs X Z) ∈ S
  | .k' => ∀ D ∈ S, ∀ x u, D.k' x = none →
      ({ D with k' := Function.update D.k' x (some u) } : Dbs X Z) ∈ S

/-- The field of `FreshBound S t ε` of port `i`. -/
def FreshAt (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)] (t : ℕ) (ε : ℝ≥0∞) : SpongePort → Prop
  | .h => ∀ D ∉ S, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ z, D.h z = none →
      ((Finset.univ.filter fun u : X ↦
          ({ D with h := Function.update D.h z (some u) } : Dbs X Z) ∈ S).card : ℝ≥0∞) /
        Fintype.card X ≤ ε
  | .k => ∀ D ∉ S, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ x, D.k x = none →
      ((Finset.univ.filter fun u : Z ↦
          ({ D with k := Function.update D.k x (some u) } : Dbs X Z) ∈ S).card : ℝ≥0∞) /
        Fintype.card Z ≤ ε
  | .k' => ∀ D ∉ S, D.h.size < t → D.k.size < t → D.k'.size < t → ∀ x, D.k' x = none →
      ((Finset.univ.filter fun u : Z ↦
          ({ D with k' := Function.update D.k' x (some u) } : Dbs X Z) ∈ S).card : ℝ≥0∞) /
        Fintype.card Z ≤ ε

variable {S : Set (Dbs X Z)}

omit [Fintype X] [Fintype Z] in
theorem UpClosed.port (h : UpClosed S) : ∀ i, UpClosedAt S i
  | .h => h.h
  | .k => h.k
  | .k' => h.k'

variable [DecidablePred (· ∈ S)] {t : ℕ} {ε : ℝ≥0∞}

theorem FreshBound.port (h : FreshBound S t ε) : ∀ i, FreshAt S t ε i
  | .h => h.h
  | .k => h.k
  | .k' => h.k'

/-- A port's fresh bound below `t` holds below any `t' ≤ t`. -/
theorem FreshAt.mono {t' : ℕ} (ht : t' ≤ t) :
    ∀ {i : SpongePort}, FreshAt S t ε i → FreshAt S t' ε i
  | .h, h => fun D hD h₁ h₂ h₃ ↦ h D hD (h₁.trans_le ht) (h₂.trans_le ht) (h₃.trans_le ht)
  | .k, h => fun D hD h₁ h₂ h₃ ↦ h D hD (h₁.trans_le ht) (h₂.trans_le ht) (h₃.trans_le ht)
  | .k', h => fun D hD h₁ h₂ h₃ ↦ h D hD (h₁.trans_le ht) (h₂.trans_le ht) (h₃.trans_le ht)

end port

/-! ## The certificate of one port from its own fields -/

section cert

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {M : Type} [Fintype M] [DecidableEq M]

/-- The certificate of port `i` at the `n`-th call (`posSemidef_spongeCompressed_certificate`)
from the fields of port `i` only. -/
theorem posSemidef_spongeCompressed_certificate_at (S : Set (Dbs X Z)) [DecidablePred (· ∈ S)]
    (i : SpongePort) (hup : UpClosedAt S i) {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : FreshAt S (n + 1) ε i) :
    let U := (spongeCompressed X Z).U i
    let Q := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ dbsProjector S
    let P : Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ :=
      diagonal fun m ↦ if dbGrade m.2 ≤ n then (1 : ℂ) else 0
    ((6 * ε.toReal) • (1 : Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ) -
      ((Q * U - U * Q) * P)ᴴ * ((Q * U - U * Q) * P)).PosSemidef := by
  have hr0 : 0 ≤ 6 * ε.toReal := by positivity
  cases i
  · let _ : UniformAnswerMeasure (Z →ₒ X) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitH (Z × X)) (fun d b ↦ (d, b.1, b.2))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_fresh _ _ _ (fun d hd z u hz ↦ ?_) fun d hd hsize z hz ↦ ?_))
      (by norm_num)
    · simp only [decide_eq_true_eq] at hd ⊢
      exact hup _ hd z u hz
    · simp only [decide_eq_true_eq]
      exact hε ⟨d, b.1, b.2⟩ (fun h ↦ by simp [DbReg.toDbs, h] at hd) hsize
        (Nat.lt_succ_of_le hb.1) (Nat.lt_succ_of_le hb.2) z hz
  · let _ : UniformAnswerMeasure (X →ₒ Z) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitK (X × Z)) (fun d b ↦ (b.1, d, b.2))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]; tauto) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_fresh _ _ _ (fun d hd x u hx ↦ ?_) fun d hd hsize x hx ↦ ?_))
      (by norm_num)
    · simp only [decide_eq_true_eq] at hd ⊢
      exact hup _ hd x u hx
    · simp only [decide_eq_true_eq]
      exact hε ⟨b.1, d, b.2⟩ (fun h ↦ by simp [DbReg.toDbs, h] at hd) (Nat.lt_succ_of_le hb.1)
        hsize (Nat.lt_succ_of_le hb.2) x hx
  · let _ : UniformAnswerMeasure (X →ₒ Z) := UniformAnswerMeasure.ofFiniteNonempty _
    refine posSemidef_port_certificate (splitK' (X × Z)) (fun d b ↦ (b.1, b.2, d))
      (fun _ _ _ ↦ rfl) (fun D : DbReg X Z ↦ decide (D.toDbs ∈ S)) dbGrade
      (fun b ↦ b.1.size ≤ n ∧ b.2.size ≤ n) n
      (fun d b ↦ by simp only [dbGrade, max_le_iff]; tauto) hr0 fun b hb ↦ ?_
    refine mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hεtop
      (instability_le_of_fresh _ _ _ (fun d hd x u hx ↦ ?_) fun d hd hsize x hx ↦ ?_))
      (by norm_num)
    · simp only [decide_eq_true_eq] at hd ⊢
      exact hup _ hd x u hx
    · simp only [decide_eq_true_eq]
      exact hε ⟨b.1, b.2, d⟩ (fun h ↦ by simp [DbReg.toDbs, h] at hd) (Nat.lt_succ_of_le hb.1)
        (Nat.lt_succ_of_le hb.2) hsize x hx

/-- **The certificate of port `i` of the hardwired runtime**
(`posSemidef_spongeHardwired_certificate`) from the fields of port `i` of every slice only. -/
theorem posSemidef_spongeHardwired_certificate_at (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (i : SpongePort) (hup : ∀ W m, UpClosedAt (slice S W m) i) {n : ℕ} {ε : ℝ≥0∞}
    (hεtop : ε ≠ ⊤) (hε : ∀ W m, FreshAt (slice S W m) (n + 1) ε i) (W₀ : Hw X Z) (m₀ : M) :
    let U := (spongeHardwired X Z W₀ m₀).U i
    let Q := (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwProjector S
    let P : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ :=
      diagonal fun q ↦ if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0
    ((6 * ε.toReal) •
        (1 : Matrix (spongeIn X Z i × HwReg X Z M) (spongeIn X Z i × HwReg X Z M) ℂ) -
      ((Q * U - U * Q) * P)ᴴ * ((Q * U - U * Q) * P)).PosSemidef := by
  intro U Q P
  let e := hwSplit X Z M (spongeIn X Z i)
  let Ub : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun b ↦
    labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
        (spongeCompressed X Z).U i +
      hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)
  let Qb : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun b ↦
    (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ dbsProjector (slice S b.1 b.2)
  let Pb : Hw X Z × M →
      Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ := fun _ ↦
    diagonal fun q : spongeIn X Z i × DbReg X Z ↦ if dbGrade q.2 ≤ n then (1 : ℂ) else 0
  have hu : U = liftBlocks e Ub := spongeHardwired_U W₀ m₀ i
  have hq : Q = liftBlocks e Qb := one_kronecker_hwProjector_eq_liftBlocks S _
  have hp : P = liftBlocks e Pb := (liftBlocks_diagonal e _).symm
  have hb (b : Hw X Z × M) :
      ((6 * ε.toReal) • (1 : Matrix (spongeIn X Z i × DbReg X Z) (spongeIn X Z i × DbReg X Z) ℂ) -
        (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ * (((Qb * Ub - Ub * Qb) * Pb) b)).PosSemidef := by
    have hQL : Qb b * labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1)
        false = labelProjector (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1) false *
          Qb b := by
      simp only [Qb, dbsProjector, one_kronecker_labelProjector]
      exact labelProjector_mul_comm _ _ _ _
    have hQN : Qb b * (hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) =
        (hwShift b.1 i ⊗ₖ (1 : Matrix (DbReg X Z) (DbReg X Z) ℂ)) * Qb b := by
      simp only [Qb, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    exact posSemidef_masked_certificate (fun q : spongeIn X Z i × DbReg X Z ↦ hwMaskFn b.1 i q.1)
      ((spongeCompressed X Z).U i) _ (Qb b) (Pb b) hQL hQN
      (posSemidef_spongeCompressed_certificate_at (slice S b.1 b.2) i (hup b.1 b.2) hεtop
        (hε b.1 b.2))
  have hh := posSemidef_liftBlocks e hb
  change (liftBlocks e ((6 * ε.toReal) • 1 -
    (fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) * ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_sub, liftBlocks_smul, liftBlocks_one] at hh
  change (_ - liftBlocks e ((fun b ↦ (((Qb * Ub - Ub * Qb) * Pb) b)ᴴ) *
    ((Qb * Ub - Ub * Qb) * Pb))).PosSemidef at hh
  rw [liftBlocks_mul, liftBlocks_adjoint, liftBlocks_mul, liftBlocks_sub, liftBlocks_mul,
    liftBlocks_mul, ← hq, ← hp, ← hu] at hh
  exact hh

/-- **One call of port `i`**: the commutator with the event, on grades at most `n`, has norm at
most `√(6 ε)`, from the fields of port `i` of every slice. -/
theorem l2_opNorm_commutator_spongeHardwired_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (i : SpongePort) (hup : ∀ W m, UpClosedAt (slice S W m) i) {n : ℕ} {ε : ℝ≥0∞}
    (hεtop : ε ≠ ⊤) (hε : ∀ W m, FreshAt (slice S W m) (n + 1) ε i) (W₀ : Hw X Z) (m₀ : M) :
    ‖(labelProjector (fun q : spongeIn X Z i × HwReg X Z M ↦ decide (q.2 ∈ S)) true *
          (spongeHardwired X Z W₀ m₀).U i -
        (spongeHardwired X Z W₀ m₀).U i *
          labelProjector (fun q : spongeIn X Z i × HwReg X Z M ↦ decide (q.2 ∈ S)) true) *
      labelProjector (fun q : spongeIn X Z i × HwReg X Z M ↦ decide (dbGrade q.2.1 ≤ n)) true‖ ≤
      √(6 * ε.toReal) := by
  have cert := posSemidef_spongeHardwired_certificate_at S i hup hεtop hε W₀ m₀
  have hQ : (1 : Matrix (spongeIn X Z i) (spongeIn X Z i) ℂ) ⊗ₖ hwProjector S =
      labelProjector (fun q : spongeIn X Z i × HwReg X Z M ↦ decide (q.2 ∈ S)) true := by
    rw [hwProjector, one_kronecker_labelProjector]
  have hP : (diagonal fun q : spongeIn X Z i × HwReg X Z M ↦
      if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0) =
      labelProjector (fun q : spongeIn X Z i × HwReg X Z M ↦ decide (dbGrade q.2.1 ≤ n)) true := by
    simp [labelProjector]
  simp only [hQ, hP] at cert
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (Par.l2_opNorm_sq_le_of_posSemidef (by positivity) cert)

end cert

end Quantum.Sponge

namespace Quantum.Par

open Quantum QuantumRuntime Sponge

/-! ## Rounds slot by slot -/

section norm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A matrix raising a grade by at most one maps grades at most `m` to grades at most `m + 1`. -/
theorem mul_labelProjector_grade (g : n → ℕ) (V : Matrix n n ℂ)
    (hV : ∀ x x', V x' x ≠ 0 → g x' ≤ g x + 1) (m : ℕ) :
    V * labelProjector (fun x ↦ decide (g x ≤ m)) true =
      labelProjector (fun x ↦ decide (g x ≤ m + 1)) true * V *
        labelProjector (fun x ↦ decide (g x ≤ m)) true := by
  ext y x
  simp only [labelProjector, mul_diagonal, diagonal_mul]
  by_cases hx : g x ≤ m
  · by_cases hV0 : V y x = 0
    · simp [hV0]
    · have := hV x y hV0
      simp [hx, show g y ≤ m + 1 by omega]
  · simp [hx]

omit [Fintype n] [DecidableEq n] in
/-- The ring identity of one more slot. -/
theorem commutator_mul_mul_eq {R : Type*} [Ring R] {Q T V P P' : R} (h : V * P = P' * V * P) :
    (Q * (T * V) - T * V * Q) * P =
      (Q * T - T * Q) * P' * (V * P) + T * ((Q * V - V * Q) * P) := by
  rw [show (Q * T - T * Q) * P' * (V * P) = (Q * T - T * Q) * (P' * V * P) by
    simp only [mul_assoc], ← h]
  noncomm_ring

/-- **A round, slot by slot**: the commutator of a round of contractions raising a grade by at
most one with a label projector, on grades at most `m`, is at most the sum of its slots'
commutators, each on grades below `m + w`. -/
theorem l2_opNorm_commutator_roundProd_le (q : n → Bool) (g : n → ℕ) {r : ℝ} :
    ∀ {w : ℕ} (V : Fin w → Matrix n n ℂ) (m : ℕ), (∀ j, ‖V j‖ ≤ 1) →
      (∀ j x x', V j x' x ≠ 0 → g x' ≤ g x + 1) →
      (∀ j m', m' < m + w → ‖(labelProjector q true * V j - V j * labelProjector q true) *
        labelProjector (fun x ↦ decide (g x ≤ m')) true‖ ≤ r) →
      ‖(labelProjector q true * roundProd V - roundProd V * labelProjector q true) *
        labelProjector (fun x ↦ decide (g x ≤ m)) true‖ ≤ w * r
  | 0, V, m, _, _, _ => by
      rw [roundProd_zero, Matrix.mul_one, Matrix.one_mul, sub_self, Matrix.zero_mul, norm_zero,
        Nat.cast_zero, zero_mul]
  | w + 1, V, m, hV1, hVg, hr => by
      have ih := l2_opNorm_commutator_roundProd_le q g (fun j ↦ V j.succ) (m + 1)
        (fun j ↦ hV1 j.succ) (fun j ↦ hVg j.succ) fun j m' hm' ↦ hr j.succ m' (by omega)
      have h0 := hr 0 m (by omega)
      have hT := l2_opNorm_roundProd_le_one fun j ↦ hV1 j.succ
      rw [roundProd_succ, commutator_mul_mul_eq (mul_labelProjector_grade g (V 0) (hVg 0) m)]
      refine (norm_add_le _ _).trans ?_
      have h1 := (l2_opNorm_mul _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
        ((l2_opNorm_mul _ _).trans ((mul_le_mul (hV1 0)
          (l2_opNorm_labelProjector_le_one (𝕜 := ℂ) (fun x ↦ decide (g x ≤ m)) true)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)))).trans ih)
      have h2 := (l2_opNorm_mul _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hT).trans h0)
      calc _ ≤ w * r + r := add_le_add h1 h2
        _ = ((w + 1 : ℕ) : ℝ) * r := by push_cast; ring

end norm

/-! ## Calls and rounds of one port -/

section hardwired

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]

omit [AddCommGroup X] [AddCommGroup Z] in
/-- **The potential after a unitary** whose commutator with the event, on grades at most `n`, has
norm at most `√c`: the square root of the event weight rises by at most `√(c tr σ)`. -/
theorem rpow_inv_two_potential_conj_le_of_norm {A : Type} [Fintype A] [DecidableEq A]
    (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    {U : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ}
    (hU : U ∈ unitaryGroup (A × HwReg X Z M) ℂ) {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hn : ‖(labelProjector (fun x : A × HwReg X Z M ↦ decide (x.2 ∈ S)) true * U -
        U * labelProjector (fun x : A × HwReg X Z M ↦ decide (x.2 ∈ S)) true) *
      labelProjector (fun x : A × HwReg X Z M ↦ decide (dbGrade x.2.1 ≤ n)) true‖ ≤ √c)
    {σ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hσg : QuerySupportedOn (fun x : A × HwReg X Z M ↦ dbGrade x.2.1) (Set.Iic n) σ) :
    potential (hwProjector S) (MatrixMap.conj U σ) ^ (2⁻¹ : ℝ) ≤
      potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        (ENNReal.ofReal c * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
  set Q := (1 : Matrix A A ℂ) ⊗ₖ hwProjector S
  have hQ : Q = labelProjector (fun x : A × HwReg X Z M ↦ decide (x.2 ∈ S)) true := by
    simp only [Q, hwProjector, one_kronecker_labelProjector]
  have hpot : ∀ τ : Matrix (A × HwReg X Z M) (A × HwReg X Z M) ℂ,
      potential (hwProjector S) τ = ENNReal.ofReal (MatrixMap.conj Q τ).trace.re :=
    fun τ ↦ by rw [potential, MatrixMap.amplifyLeft_conj]
  rw [hpot, hpot, ← LinearMap.comp_apply, ← MatrixMap.conj_mul,
    show Q * U = U * Q + (Q * U - U * Q) by abel]
  refine (MatrixMap.ofReal_trace_conj_add_rpow_le hσ _ _).trans (add_le_add (le_of_eq ?_) ?_)
  · rw [MatrixMap.conj_mul, LinearMap.comp_apply, trace_conj_of_mem_unitaryGroup hU]
  · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← hQ] at hn
    have hcert := MatrixMap.posSemidef_scalar_sub_gram_of_norm_sq_le _
      ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans_eq (Real.sq_sqrt hc))
    exact ofReal_trace_conj_le_of_certificate _ _ hc hcert hσ
      (hσg.conj_diagonal_eq_self fun q hq ↦ by simp [Set.mem_Iic.mp hq])

/-- **One call of port `p`** on grades at most `n`, from the fields of port `p`: the square root
of the event weight rises by at most `√(6 ε tr σ)`. -/
theorem rpow_inv_two_potential_single_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (p : SpongePort) (hup : ∀ W m, UpClosedAt (slice S W m) p) {n : ℕ} {ε : ℝ≥0∞}
    (hεtop : ε ≠ ⊤) (hε : ∀ W m, FreshAt (slice S W m) (n + 1) ε p) (W₀ : Hw X Z) (m₀ : M)
    {σ : Matrix (spongeIn X Z p × HwReg X Z M) (spongeIn X Z p × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hσg : QuerySupportedOn (fun x : spongeIn X Z p × HwReg X Z M ↦ dbGrade x.2.1)
      (Set.Iic n) σ) :
    potential (hwProjector S) (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ) ^ (2⁻¹ : ℝ) ≤
      potential (hwProjector S) σ ^ (2⁻¹ : ℝ) + (6 * ε * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) :=
  (rpow_inv_two_potential_conj_le_of_norm S ((spongeHardwired X Z W₀ m₀).unitary p)
    (by positivity) (l2_opNorm_commutator_spongeHardwired_le S p hup hεtop hε W₀ m₀) hσ
    hσg).trans_eq (by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hεtop]; norm_num)

/-- A round of one sponge port raises the grade by at most its width. -/
theorem dbGrade_le_of_portRound_ne_zero (W₀ : Hw X Z) (m₀ : M) (p : SpongePort) {w : ℕ}
    (x x' : (Fin w → spongeIn X Z p) × HwReg X Z M)
    (h : roundProd (fun j : Fin w ↦ slotLift j ((spongeHardwired X Z W₀ m₀).U p)) x' x ≠ 0) :
    dbGrade x'.2.1 ≤ dbGrade x.2.1 + w :=
  roundProd_grade_le (fun x : (Fin w → spongeIn X Z p) × HwReg X Z M ↦ dbGrade x.2.1) _
    (fun j x x' hx ↦ by
      rw [slotLift_apply] at hx
      split_ifs at hx
      · exact dbGrade_le_of_spongeHardwired_U_ne_zero W₀ m₀ p (x.1 j) (x'.1 j) x.2 x'.2 hx
      · exact absurd rfl hx) x x' h

/-- **A round of `w` calls of port `p`, slot by slot**: on grades at most `n`, with the fields of
port `p` below `n + w`, the square root of the event weight rises by at most `w √(6 ε tr σ)`. -/
theorem rpow_inv_two_potential_portRound_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (p : SpongePort) (hup : ∀ W m, UpClosedAt (slice S W m) p) {n w : ℕ} {ε : ℝ≥0∞}
    (hεtop : ε ≠ ⊤) (hε : ∀ W m, FreshAt (slice S W m) (n + w) ε p) (W₀ : Hw X Z) (m₀ : M)
    {σ : Matrix ((Fin w → spongeIn X Z p) × HwReg X Z M)
      ((Fin w → spongeIn X Z p) × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hσg : QuerySupportedOn (fun x : (Fin w → spongeIn X Z p) × HwReg X Z M ↦ dbGrade x.2.1)
      (Set.Iic n) σ) :
    potential (hwProjector S) (MatrixMap.conj (roundProd fun j : Fin w ↦
        slotLift j ((spongeHardwired X Z W₀ m₀).U p)) σ) ^ (2⁻¹ : ℝ) ≤
      potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        w * (6 * ε * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
  have hr := l2_opNorm_commutator_roundProd_le
    (fun x : (Fin w → spongeIn X Z p) × HwReg X Z M ↦ decide (x.2 ∈ S))
    (fun x : (Fin w → spongeIn X Z p) × HwReg X Z M ↦ dbGrade x.2.1) (r := √(6 * ε.toReal))
    (fun j : Fin w ↦ slotLift j ((spongeHardwired X Z W₀ m₀).U p)) n
    (fun j ↦ (l2_opNorm_slotLift_le _ _).trans
      (l2_opNorm_le_one_of_mem_unitaryGroup ((spongeHardwired X Z W₀ m₀).unitary p)))
    (fun j x x' hx ↦ by
      rw [slotLift_apply] at hx
      split_ifs at hx
      · exact dbGrade_le_of_spongeHardwired_U_ne_zero W₀ m₀ p (x.1 j) (x'.1 j) x.2 x'.2 hx
      · exact absurd rfl hx)
    fun j m' hm' ↦ by
      have hQ : labelProjector (fun x : (Fin w → spongeIn X Z p) × HwReg X Z M ↦
          decide (x.2 ∈ S)) true = slotLift j (labelProjector
            (fun q : spongeIn X Z p × HwReg X Z M ↦ decide (q.2 ∈ S)) true) :=
        (slotLift_labelProjector j (fun s : HwReg X Z M ↦ decide (s ∈ S)) true).symm
      have hP : labelProjector (fun x : (Fin w → spongeIn X Z p) × HwReg X Z M ↦
          decide (dbGrade x.2.1 ≤ m')) true = slotLift j (labelProjector
            (fun q : spongeIn X Z p × HwReg X Z M ↦ decide (dbGrade q.2.1 ≤ m')) true) :=
        (slotLift_labelProjector j (fun s : HwReg X Z M ↦ decide (dbGrade s.1 ≤ m')) true).symm
      rw [hQ, hP, ← slotLift_mul, ← slotLift_mul, ← slotLift_sub, ← slotLift_mul]
      exact (l2_opNorm_slotLift_le _ _).trans (l2_opNorm_commutator_spongeHardwired_le S p hup
        hεtop (fun W m ↦ (hε W m).mono (by omega)) W₀ m₀)
  have hc : (w : ℝ) * √(6 * ε.toReal) = √((w : ℝ) ^ 2 * (6 * ε.toReal)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]
  refine (rpow_inv_two_potential_conj_le_of_norm S (roundProd_mem_unitaryGroup fun _ ↦
    onFactor_mem_unitaryGroup _ ((spongeHardwired X Z W₀ m₀).unitary p)) (by positivity)
    (hr.trans_eq hc) hσ hσg).trans_eq ?_
  congr 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hεtop,
    mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

/-- **The parallel transition lemma for port `h`** (`l2_opNorm_commutator_hRound_le`) from the
`h` fields of the cell events only. -/
theorem l2_opNorm_commutator_hRound_le_at (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)] (hsub : ∀ c, Sc c ⊆ S)
    (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hup : ∀ c W m, UpClosedAt (slice (Sc c) W m) .h) {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : ∀ c W m, FreshAt (slice (Sc c) W m) (n + 1) ε .h) (W₀ : Hw X Z) (m₀ : M) (w : ℕ) :
    ‖(labelProjector (fun x : (Fin w → Z × X) × HwReg X Z M ↦ decide (x.2 ∈ S)) true *
          roundProd (fun j : Fin w ↦ slotLift j (portMat (hwReadH X Z M) (compressReg X Z M))) -
        roundProd (fun j : Fin w ↦ slotLift j (portMat (hwReadH X Z M) (compressReg X Z M))) *
          labelProjector (fun x : (Fin w → Z × X) × HwReg X Z M ↦ decide (x.2 ∈ S)) true) *
      labelProjector (fun x : (Fin w → Z × X) × HwReg X Z M ↦ decide (dbGrade x.2.1 ≤ n))
        true‖ ≤ √(w * (6 * ε.toReal)) := by
  refine l2_opNorm_commutator_roundProd_portMat_le (hwReadH X Z M)
    (compressReg_mul_self (X := X) (Z := Z) (M := M))
    conjTranspose_compressReg (fun s ↦ decide (s ∈ S)) (fun s ↦ decide (dbGrade s.1 ≤ n))
    (fun c s ↦ decide (s ∈ Sc c)) (by positivity) (fun c s h ↦ ?_) (fun s h ↦ ?_)
    (fun c p p' h hc ↦ ?_) (fun c ↦ ?_)
  · simp only [decide_eq_true_eq] at h ⊢
    exact hsub c h
  · simp only [decide_eq_true_eq] at h ⊢
    exact hunion s h
  · obtain ⟨h2, -, h3⟩ := eraseCell_of_spongeHardwired_U_ne_zero W₀ m₀ .h p.1 p'.1 p.2 p'.2 h
    simp only [eraseCell, Prod.mk.injEq] at h3
    have h1 : p'.2.1.1 c = p.2.1.1 c := by
      have := congrFun h3.1 c
      rwa [Function.update_of_ne (Ne.symm hc), Function.update_of_ne (Ne.symm hc)] at this
    exact decide_eq_decide.mpr (hloc c p.2 p'.2 h1 (Prod.ext h3.2.1 h3.2.2) h2)
  · have cert : ((6 * ε.toReal) • (1 : Matrix ((Z × X) × HwReg X Z M) ((Z × X) × HwReg X Z M) ℂ) -
        ((((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c)) *
            portMat (hwReadH X Z M) (compressReg X Z M) -
          portMat (hwReadH X Z M) (compressReg X Z M) *
            ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c))) *
          diagonal fun q : (Z × X) × HwReg X Z M ↦ if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0)ᴴ *
        ((((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c)) *
            portMat (hwReadH X Z M) (compressReg X Z M) -
          portMat (hwReadH X Z M) (compressReg X Z M) *
            ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c))) *
          diagonal fun q : (Z × X) × HwReg X Z M ↦
            if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0)).PosSemidef :=
      posSemidef_spongeHardwired_certificate_at (Sc c) .h (hup c) hεtop (hε c) W₀ m₀
    rw [one_kronecker_hwProjector, diagonal_dbGrade_eq] at cert
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      (l2_opNorm_sq_le_of_posSemidef (by positivity) cert)

/-- **One round of `h`** (`rpow_inv_two_potential_hRound_le`) from the `h` fields of the cell
events only: the square root of the event weight rises by at most `√(6 ε w tr σ)`. -/
theorem rpow_inv_two_potential_hRound_le_at (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)] (hsub : ∀ c, Sc c ⊆ S)
    (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hup : ∀ c W m, UpClosedAt (slice (Sc c) W m) .h) {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : ∀ c W m, FreshAt (slice (Sc c) W m) (n + 1) ε .h) (W₀ : Hw X Z) (m₀ : M) (w : ℕ)
    {σ : Matrix ((Fin w → Z × X) × HwReg X Z M) ((Fin w → Z × X) × HwReg X Z M) ℂ}
    (hσ : σ.PosSemidef)
    (hσg : QuerySupportedOn (fun q : (Fin w → Z × X) × HwReg X Z M ↦ dbGrade q.2.1)
      (Set.Iic n) σ) :
    potential (hwProjector S) (MatrixMap.conj (hRound (X := X) (Z := Z) (M := M) w) σ) ^
        (2⁻¹ : ℝ) ≤
      potential (hwProjector S) σ ^ (2⁻¹ : ℝ) +
        (6 * ε * w * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) := by
  refine (rpow_inv_two_potential_conj_le_of_norm S (hRound_mem_unitaryGroup w W₀ m₀)
    (by positivity) (l2_opNorm_commutator_hRound_le_at S Sc hsub hunion hloc hup hεtop hε W₀ m₀ w)
    hσ hσg).trans_eq ?_
  congr 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_toReal hεtop, ENNReal.ofReal_natCast]
  norm_num
  ring_nf

omit [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z] in
/-- The `h` field of the event from those of its cell events: filling cell `z` of `h` moves the
state only in and out of the cell event of `z`. -/
theorem freshAt_h_of_cells (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)] (hsub : ∀ c, Sc c ⊆ S)
    (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c)) {T : ℕ} {ε : ℝ≥0∞}
    (hε : ∀ c W m, FreshAt (slice (Sc c) W m) T ε .h) (W : Hw X Z) (m : M) :
    FreshAt (slice S W m) T ε .h := by
  intro D hD h₁ h₂ h₃ z hz
  refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2 (Finset.card_le_card fun u hu ↦ ?_)) _)
    (hε z W m D (fun h ↦ hD (hsub z h)) h₁ h₂ h₃ z hz)
  have hu' : ((Function.update D.h z (some u), D.k, D.k'), W, m) ∈ S := (Finset.mem_filter.1 hu).2
  obtain ⟨c, hc⟩ := hunion _ hu'
  by_cases hcz : c = z
  · subst hcz
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩
  · exact absurd (hsub c ((hloc c ((Function.update D.h z (some u), D.k, D.k'), W, m)
      ((D.h, D.k, D.k'), W, m) (Function.update_of_ne hcz _ _).symm rfl rfl).2 hc)) hD

end hardwired

/-! ## The event bound with rounds of every port -/

section split

section charges

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {M : Type}
  {t : QuantumOracleSpec.{0, 0}}

variable (X Z M t) in
/-- The port map of the rounds: a round of sponge port `p` is a round of the port `p` of the
hardwired runtime. -/
abbrev hwPortMap : SpongePort → ((hwSpec X Z M).sum t).Port := fun p ↦ .inl (.inl (.inl p))

variable (port : SpongePort → ((hwSpec X Z M).sum t).Port)

/-- The calls of port `p` in a command: one for a single call of `p`, the width for a round of
`p` alone. -/
def portWidth (p : SpongePort) : (parSpec ((hwSpec X Z M).sum t) port).Port → ℕ
  | .inl (.inl (.inl (.inl p'))) => if p' = p then 1 else 0
  | .inl _ => 0
  | .inr (.round w f) => if ∀ j, f j = p then w else 0

/-- Whether a command calls port `p`: the depth charge of `p`. -/
def portDepth (p : SpongePort) (i : (parSpec ((hwSpec X Z M).sum t) port).Port) : ℕ :=
  if portWidth port p i = 0 then 0 else 1

/-- The calls of `k` and `k'` in a command. -/
def capWidth (i : (parSpec ((hwSpec X Z M).sum t) port).Port) : ℕ :=
  portWidth port .k i + portWidth port .k' i

/-- The rounds mixing sponge ports. -/
def mixedRounds : (parSpec ((hwSpec X Z M).sum t) port).Port → ℕ
  | .inl _ => 0
  | .inr (.round _ f) => if (∀ j, f j = .h) ∨ (∀ j, f j = .k) ∨ (∀ j, f j = .k') then 0 else 1

theorem portWidth_single (p q : SpongePort) :
    portWidth port q (.inl (.inl (.inl (.inl p)))) = if p = q then 1 else 0 :=
  rfl

theorem portWidth_round_const (p q : SpongePort) (w : ℕ) :
    portWidth port q (.inr (.round w fun _ ↦ p)) = if p = q then w else 0 := by
  show (if ∀ _ : Fin w, p = q then w else 0) = if p = q then w else 0
  split_ifs with h1 h2 h2
  · rfl
  · rcases Nat.eq_zero_or_pos w with rfl | hw
    · rfl
    · exact absurd (h1 ⟨0, hw⟩) h2
  · exact absurd (fun _ ↦ h2) h1
  · rfl

theorem portWidth_round_self (p : SpongePort) (w : ℕ) :
    portWidth port p (.inr (.round w fun _ ↦ p)) = w := by
  rw [portWidth_round_const, ite_eq_left rfl]

theorem portWidth_round_ne {p q : SpongePort} (h : p ≠ q) (w : ℕ) :
    portWidth port q (.inr (.round w fun _ ↦ p)) = 0 := by
  rw [portWidth_round_const, ite_eq_right h]

/-- A round that does not mix ports is a round of one port. -/
theorem exists_eq_const_of_mixedRounds {w : ℕ} {f : Fin w → SpongePort}
    (h : mixedRounds port (.inr (.round w f)) = 0) : ∃ p, f = fun _ ↦ p := by
  have h' : (∀ j, f j = .h) ∨ (∀ j, f j = .k) ∨ (∀ j, f j = .k') := by
    change (if (∀ j, f j = .h) ∨ (∀ j, f j = .k) ∨ (∀ j, f j = .k') then 0 else 1) = 0 at h
    split_ifs at h with h0
    exact h0
  rcases h' with h' | h' | h' <;> exact ⟨_, funext h'⟩

end charges

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]
  {t : QuantumOracleSpec.{0, 0}}

variable {L : LocalSig.{u, v}} {Xr : QReg → Type w} {A : QReg}

/-- A round of one sponge port of the extended runtime, through the port map. -/
theorem par_step_portRound_branch (W₀ : Hw X Z) (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j)) (p : SpongePort) (w : ℕ)
    (rs : RoundResult ((hwSpec X Z M).sum t) fun _ : Fin w ↦ hwPortMap X Z M t p) :
    ((((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (hwPortMap X Z M t)).step
        (.inr (.round w fun _ ↦ p))).branch rs =
      MatrixMap.conj (roundProd fun j : Fin w ↦
        slotLift (S := spongeIn X Z p) (N := HwReg X Z M) j ((spongeHardwired X Z W₀ m₀).U p)) := by
  have h := branch_roundStep_of_conj_on ((spongeHardwiredRuntime X Z W₀ m₀).extend step')
    (hwExtKraus X Z W₀ m₀)
    (fun _ : Fin w ↦ (.inl (.inl (.inl p)) : ((hwSpec X Z M).sum t).Port))
    (fun _ r ↦ spongeHardwiredRuntime_step_branch W₀ m₀ (.inl (.inl p)) r) rs
  rw [roundKraus_extend] at h
  exact h

/-- **The event bound with rounds, from budgets with slack.** As
`rpow_inv_two_tsum_potential_run_le_rounds`, with two changes: a port of charge `cf i > 0` never
occurs (budget `0`), and a quantum port's bound is needed only on inputs of grade `n` with
`n + cg i ≤ G`, so a round may use fresh bounds up to its last slot. -/
theorem rpow_inv_two_tsum_potential_run_le_slack {spec : QuantumOracleSpec.{u₁, v₁}}
    (R : QuantumRuntime spec) (I : L.Interp) (Q : Matrix R.D R.D ℂ) (cls : spec.Port → Bool)
    (g : R.D → ℕ) (cq cd cr cg cf : spec.Port → ℕ)
    (hg : ∀ i, cf i = 0 → ∀ r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + cg i))
          ((R.step i).branch r σ))
    (α β : ℝ≥0∞) (G : ℕ) (hδ : ∀ i, cls i = false → cq i = 0 ∨ 1 ≤ cd i)
    (hq : ∀ i, cls i = false → cf i = 0 → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → ∀ n, n + cg i ≤ G →
        QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic n) σ →
        (∑' r, potential Q ((R.step i).branch r σ)) ^ (2⁻¹ : ℝ) ≤
          potential Q σ ^ (2⁻¹ : ℝ) + (α * (cq i : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ) +
            (cr i : ℝ≥0∞) * (β * ENNReal.ofReal σ.trace.re) ^ (2⁻¹ : ℝ))
    (d : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞)
    (hc : ∀ i, cls i = true → cf i = 0 → ∀ σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ,
      σ.PosSemidef → ∑' r, potential Q ((R.step i).branch r σ) ≤ potential Q σ + d i σ)
    {A : QReg} (x : QuantumComp L spec Xr A) (q' dr rr T t : ℕ)
    (hxq : IFreeM.IsChargeBound x (portCharge cq) q')
    (hxd : IFreeM.IsChargeBound x (portCharge cd) dr)
    (hxr : IFreeM.IsChargeBound x (portCharge cr) rr)
    (hxT : IFreeM.IsChargeBound x (portCharge cg) T)
    (hxf : IFreeM.IsChargeBound x (portCharge cf) 0) (htG : t + T ≤ G)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ} (hρ : ρ.PosSemidef)
    (hρg : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    (∑' p, potential Q ((R.run I x).branch p ρ)) ^ (2⁻¹ : ℝ) ≤
      (α * ((dr * q' : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (rr : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
        (potential Q ρ + R.totalWeight I d x ρ) ^ (2⁻¹ : ℝ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing q' dr rr T t with
  | pure B y =>
    rw [run_pure, tsum_eq_single (⟨_, y⟩ : Σ u, Xr u) fun p hp ↦ by
        rw [DSubInstrument.branch_ret_of_ne _ hp, LinearMap.zero_apply]
        simp [potential],
      DSubInstrument.branch_ret_self, LinearMap.id_apply]
    exact le_add_left (ENNReal.rpow_le_rpow le_self_add (by norm_num))
  | primBind B o k ih =>
    have hρb := fun b ↦ ((I o).frame R.D).posSemidef_branch_apply b hρ
    have hL : ∀ p, potential Q ((R.run I (QuantumComp.primBind o k)).branch p ρ) =
        ∑' b, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)) :=
      fun p ↦ by
        rw [run_primBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum Q ((((I o).frame R.D).isCPTNIFamily.comp_eval
          (fun b ↦ (R.run I (k b)).isCPTNIFamily) p).summable_apply ρ)
          fun b ↦ (R.run I (k b)).posSemidef_branch_apply p (hρb b)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_primBind_iff] at hxq hxd hxr hxT hxf
    refine (rpow_inv_two_tsum_le_of_le_add_two
      (t := fun b ↦ ∑' p, potential Q ((R.run I (k b)).branch p (((I o).frame R.D).branch b ρ)))
      (a := fun b ↦ α * ((dr * q' : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re)
      (c := fun b ↦ (rr : ℝ≥0∞) ^ (2 : ℝ) * (β *
        ENNReal.ofReal (((I o).frame R.D).branch b ρ).trace.re))
      (b := fun b ↦ potential Q (((I o).frame R.D).branch b ρ) +
        R.totalWeight I d (k b) (((I o).frame R.D).branch b ρ))
      fun b ↦ (ih b q' dr rr T t (hxq b) (hxd b) (hxr b) (hxT b) (hxf b) htG (hρb b)
        (hρg.amplify_snd _)).trans_eq (by rw [rpow_two_mul_rpow_inv_two])).trans ?_
    have htr := ((I o).frame R.D).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    gcongr
    · rw [ENNReal.tsum_mul_left]
      gcongr
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, rpow_two_mul_rpow_inv_two]
      gcongr
    · rw [ENNReal.tsum_add, totalWeight_primBind]
      gcongr
      exact tsum_potential_frame_le Q (I o) hρ
  | queryBind B i E ℓ k ih =>
    have hρr := fun r ↦ (R.queryStep i E ℓ).posSemidef_branch_apply r hρ
    have hL : ∀ p, potential Q ((R.run I (QuantumComp.queryBind i E ℓ k)).branch p ρ) =
        ∑' r, potential Q ((R.run I (k r)).branch p ((R.queryStep i E ℓ).branch r ρ)) :=
      fun p ↦ by
        rw [run_queryBind, DSubInstrument.branch_bind_apply]
        exact potential_tsum Q (((R.queryStep i E ℓ).isCPTNIFamily.comp_eval
          (fun r ↦ (R.run I (k r)).isCPTNIFamily) p).summable_apply ρ)
          fun r ↦ (R.run I (k r)).posSemidef_branch_apply p (hρr r)
    simp only [hL]
    rw [ENNReal.tsum_comm]
    rw [isChargeBound_portCharge_queryBind_iff] at hxq hxd hxr hxT hxf
    have hf0 : cf i = 0 := Nat.le_zero.mp hxf.1
    have hxf' : ∀ r, IFreeM.IsChargeBound (k r) (portCharge cf) 0 :=
      fun r ↦ (Nat.zero_sub (cf i)) ▸ hxf.2 r
    have hT1 : cg i ≤ T := hxT.1
    have hσ := posSemidef_callInput ℓ hρ
    have hσg : QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t)
        (callInput ℓ R.D ρ) := hρg.callInput ℓ
    have hρrg := fun r ↦ querySupportedOn_queryStep_of_step R g i (cg i)
      (fun r t σ hσ ↦ hg i hf0 r t σ hσ) E ℓ r hρg
    have hpot : ∑' r, potential Q ((R.queryStep i E ℓ).branch r ρ) =
        ∑' r, potential Q ((R.step i).branch r (callInput ℓ R.D ρ)) :=
      tsum_congr fun r ↦ potential_queryStep R Q i E ℓ r ρ
    have htr : ∑' r, ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re ≤
        ENNReal.ofReal ρ.trace.re := (R.queryStep i E ℓ).isCPTNIFamily.tsum_ofReal_trace_re_le hρ
    have hk := fun r ↦ ih r (q' - cq i) (dr - cd i) (rr - cr i) (T - cg i) (t + cg i)
      (hxq.2 r) (hxd.2 r) (hxr.2 r) (hxT.2 r) (hxf' r) (by omega) (hρr r) (hρrg r)
    refine (rpow_inv_two_tsum_le_of_le_add_two
      (t := fun r ↦ ∑' p, potential Q ((R.run I (k r)).branch p
        ((R.queryStep i E ℓ).branch r ρ)))
      (a := fun r ↦ α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)
      (c := fun r ↦ ((rr - cr i : ℕ) : ℝ≥0∞) ^ (2 : ℝ) * (β *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re))
      (b := fun r ↦ potential Q ((R.queryStep i E ℓ).branch r ρ) +
        R.totalWeight I d (k r) ((R.queryStep i E ℓ).branch r ρ))
      fun r ↦ (hk r).trans_eq (by rw [rpow_two_mul_rpow_inv_two])).trans ?_
    have ha : (∑' r, α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re) ≤
          α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    have hb : (∑' r, ((rr - cr i : ℕ) : ℝ≥0∞) ^ (2 : ℝ) * (β *
        ENNReal.ofReal ((R.queryStep i E ℓ).branch r ρ).trace.re)) ^ (2⁻¹ : ℝ) ≤
          ((rr - cr i : ℕ) : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, rpow_two_mul_rpow_inv_two]
      gcongr
    rw [totalWeight_queryBind, ENNReal.tsum_add]
    cases hci : cls i
    · -- A quantum call.
      have hq0 := hq i hci hf0 _ hσ t (by omega) hσg
      rw [potential_callInput, trace_callInput, ← hpot, add_assoc] at hq0
      have h2 := rpow_inv_two_add_le_of_le_two (C := ∑' r, R.totalWeight I d (k r)
        ((R.queryStep i E ℓ).branch r ρ)) hq0
      have hs := rpow_inv_two_round_le α (ENNReal.ofReal ρ.trace.re)
        (sqrt_round_le (x := cq i) (q := q') (d := dr) (e := cd i) hxq.1 hxd.1 (hδ i hci))
      have hr : ((rr - cr i : ℕ) : ℝ≥0∞) + cr i = rr := by
        rw [← Nat.cast_add, Nat.sub_add_cancel hxr.1]
      calc _ ≤ (α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^
              (2⁻¹ : ℝ) + ((rr - cr i : ℕ) : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^
                (2⁻¹ : ℝ) + ((α * (cq i : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (cr i : ℝ≥0∞) * (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (potential Q ρ + ∑' r, R.totalWeight I d (k r)
                ((R.queryStep i E ℓ).branch r ρ)) ^ (2⁻¹ : ℝ)) :=
            add_le_add (add_le_add (ENNReal.rpow_le_rpow ha (by norm_num)) hb) h2
        _ = ((α * (cq i : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (α * (((dr - cd i) * (q' - cq i) : ℕ) : ℝ≥0∞) * ENNReal.ofReal ρ.trace.re) ^
                (2⁻¹ : ℝ)) + (((rr - cr i : ℕ) : ℝ≥0∞) + cr i) *
                  (β * ENNReal.ofReal ρ.trace.re) ^ (2⁻¹ : ℝ) +
              (potential Q ρ + ∑' r, R.totalWeight I d (k r)
                  ((R.queryStep i E ℓ).branch r ρ)) ^ (2⁻¹ : ℝ) := by ring
        _ ≤ _ := by
            rw [hr]
            gcongr
            exact le_add_self
    · -- A classical call.
      have hc0 := hc i hci hf0 _ hσ
      rw [potential_callInput, ← hpot] at hc0
      refine add_le_add (add_le_add (ENNReal.rpow_le_rpow (ha.trans ?_) (by norm_num))
        (hb.trans ?_)) (ENNReal.rpow_le_rpow ?_ (by norm_num))
      · gcongr <;> omega
      · gcongr
        omega
      · rw [← add_assoc]
        gcongr

/-- The end of the split event bound: no weight at the start, trace at most one. -/
theorem rpow_inv_two_split_finish {T P W τ εh εc : ℝ≥0∞} {d q n : ℕ} (hP : P = 0) (hτ : τ ≤ 1)
    (h : T ^ (2⁻¹ : ℝ) ≤ (6 * εh * ((d * q : ℕ) : ℝ≥0∞) * τ) ^ (2⁻¹ : ℝ) +
      (n : ℝ≥0∞) * (6 * εc * τ) ^ (2⁻¹ : ℝ) + (P + W) ^ (2⁻¹ : ℝ)) :
    T ^ (2⁻¹ : ℝ) ≤ (6 * εh * d * q) ^ (2⁻¹ : ℝ) + n * (6 * εc) ^ (2⁻¹ : ℝ) + W ^ (2⁻¹ : ℝ) := by
  refine h.trans ?_
  rw [hP, zero_add, Nat.cast_mul, ← mul_assoc]
  have h1 : 6 * εh * d * q * τ ≤ 6 * εh * d * q :=
    (by gcongr : 6 * εh * d * q * τ ≤ 6 * εh * d * q * 1).trans_eq (mul_one _)
  have h2 : 6 * εc * τ ≤ 6 * εc := (by gcongr : 6 * εc * τ ≤ 6 * εc * 1).trans_eq (mul_one _)
  gcongr

/-- **The event bound with rounds of every sponge port, split by port.** Let `S` be a union of
cell events `Sc c` as in `rpow_inv_two_eventWeight_extend_par_le`, with `h` fields of the cell
events at rate `ε_h` and `k`, `k'` fields of `S` at rate `ε_c`, below `q_h + n_k + K + 1`
entries. A program over the extended runtime with rounds of one sponge port each, through the
port map `port p = .inl (.inl (.inl p))`, with `q_h` calls of `h` in `d_h` rounds (a single call
counts as a round), `n_k` calls of `k` and `k'` (single or in rounds), `K` classical calls, and no
round mixing ports, ends with `√w ≤ √(6 ε_h d_h q_h) + n_k √(6 ε_c) + √(∑ d)`. -/
theorem rpow_inv_two_eventWeight_extend_split_le (S : Set (HwReg X Z M))
    [DecidablePred (· ∈ S)] (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)]
    (hsub : ∀ c, Sc c ⊆ S) (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hupc : ∀ c W m, UpClosedAt (slice (Sc c) W m) .h) (hup : ∀ W m, UpClosed (slice S W m))
    (W₀ : Hw X Z) (m₀ : M)
    (hempty : ((Database.empty, Database.empty, Database.empty), W₀, m₀) ∉ S)
    {qh dh nk K : ℕ} {εh εc : ℝ≥0∞} (hεh : εh ≠ ⊤) (hεc : εc ≠ ⊤)
    (hfh : ∀ c W m, FreshAt (slice (Sc c) W m) (qh + nk + K + 1) εh .h)
    (hfk : ∀ W m, FreshAt (slice S W m) (qh + nk + K + 1) εc .k)
    (hfk' : ∀ W m, FreshAt (slice S W m) (qh + nk + K + 1) εc .k')
    (dR : HwRead X Z M → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (dP : HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞)
    (hdR : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwReadKraus c r) σ) ≤ potential (hwProjector S) σ + dR c σ)
    (hdP : ∀ c σ, σ.PosSemidef → ∑' r, potential (hwProjector S)
      (MatrixMap.conj (hwProgKraus c r) σ) ≤ potential (hwProjector S) σ + dP c σ)
    (σ₀ : SubState (QReg.of (HwReg X Z M)))
    (s₀ : ∀ i, SubInstrument ((hwSpec X Z M).In i × QReg.of (HwReg X Z M))
      ((hwSpec X Z M).Out i × QReg.of (HwReg X Z M)) ((hwSpec X Z M).Result i))
    (hσ₀ : σ₀ = (spongeHardwiredRuntime X Z W₀ m₀).init)
    (hs₀ : s₀ = (spongeHardwiredRuntime X Z W₀ m₀).step)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × QReg.of (HwReg X Z M))
      (t.Out j × QReg.of (HwReg X Z M)) (t.Result j))
    (dT : ∀ j : t.Port,
      Matrix (t.In j × QReg.of (HwReg X Z M)) (t.In j × QReg.of (HwReg X Z M)) ℂ → ℝ≥0∞)
    (hgT : ∀ j r n (σ : Matrix (t.In j × QReg.of (HwReg X Z M))
        (t.In j × QReg.of (HwReg X Z M)) ℂ),
      QuerySupportedOn (fun q : t.In j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1) (Set.Iic n) σ →
      QuerySupportedOn (fun q : t.Out j × QReg.of (HwReg X Z M) ↦ dbGrade q.2.1)
        (Set.Iic (n + 1)) ((step' j).branch r σ))
    (hdT : ∀ j σ, σ.PosSemidef → ∑' r, potential (hwProjector S) ((step' j).branch r σ) ≤
      potential (hwProjector S) σ + dT j σ)
    (port : SpongePort → ((hwSpec X Z M).sum t).Port)
    (hport : ∀ p, port p = .inl (.inl (.inl p)))
    (I : L.Interp) (x : QuantumComp L (parSpec ((hwSpec X Z M).sum t) port) Xr A)
    (hxq : IFreeM.IsChargeBound x (portCharge (portWidth port .h)) qh)
    (hxd : IFreeM.IsChargeBound x (portCharge (portDepth port .h)) dh)
    (hxk : IFreeM.IsChargeBound x (portCharge (capWidth port)) nk)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount port (hwExtCls X Z M t))) K)
    (hxm : IFreeM.IsChargeBound x (portCharge (mixedRounds port)) 0) (ρ : SubState A) :
    (((QuantumRuntime.mk _ σ₀ s₀).extend step').par port).eventWeight I
        (hwProjector S) x (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ) ≤
      (6 * εh * dh * qh) ^ (2⁻¹ : ℝ) + nk * (6 * εc) ^ (2⁻¹ : ℝ) +
        (((QuantumRuntime.mk _ σ₀ s₀).extend step').par port).totalWeight I
          (parWeight port (hwExtCost dR dP dT)) x (ρ.matrix ⊗ₖ σ₀.matrix) ^ (2⁻¹ : ℝ) := by
  obtain rfl : port = hwPortMap X Z M t := funext hport
  subst hσ₀ hs₀
  have hρ0 : (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).PosSemidef :=
    (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).posSemidef
  have htr : ENNReal.ofReal
      (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix).trace.re ≤ 1 := by
    rw [← SubState.matrix_prod]
    exact ENNReal.ofReal_le_one.mpr (ρ.prod (spongeHardwiredRuntime X Z W₀ m₀).init).trace_re_le_one
  have hcls : ∀ a, hwExtCls X Z M t (hwPortMap X Z M t a) = false := fun _ ↦ rfl
  have hh : ∀ n, n ≤ qh + nk + K → ∀ W m, FreshAt (slice S W m) (n + 1) εh .h :=
    fun n hn ↦ freshAt_h_of_cells S Sc hsub hunion hloc
      (fun c W m ↦ (hfh c W m).mono (by omega))
  have h := rpow_inv_two_tsum_potential_run_le_slack
    (((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (hwPortMap X Z M t)) I
    (hwProjector S) (parCls (hwPortMap X Z M t) (hwExtCls X Z M t))
    (fun s : HwReg X Z M ↦ dbGrade s.1) (portWidth (hwPortMap X Z M t) .h)
    (portDepth (hwPortMap X Z M t) .h) (capWidth (hwPortMap X Z M t))
    (fun i ↦ portWidth (hwPortMap X Z M t) .h i + capWidth (hwPortMap X Z M t) i +
      clsCount (hwPortMap X Z M t) (hwExtCls X Z M t) i)
    (mixedRounds (hwPortMap X Z M t)) ?_ (6 * εh) (6 * εc) (qh + nk + K)
    (fun i _ ↦ by unfold portDepth; split_ifs with h0 <;> simp [h0]) ?_
    (parWeight (hwPortMap X Z M t) (hwExtCost dR dP dT)) ?_ x qh dh nk (qh + nk + K) 0 hxq hxd
    hxk (isChargeBound_portCharge_add _ _ x (isChargeBound_portCharge_add _ _ x hxq hxk) hxK) hxm
    (by omega) hρ0 (querySupportedOn_start W₀ m₀ ρ)
  · exact (le_of_eq (congrArg (· ^ (2⁻¹ : ℝ)) (eventWeight_eq_tsum_potential
      (((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (hwPortMap X Z M t)) I
      (hwProjector S) x (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix)))).trans
      (rpow_inv_two_split_finish (potential_start_eq_zero S W₀ m₀ hempty ρ) htr h)
  · -- Grades: a single call raises the grade by one, a round by its width.
    intro i hf r n σ hσ
    rcases i with i | ⟨w, f⟩
    · have h1 : 1 ≤ portWidth (hwPortMap X Z M t) .h (.inl i) +
          capWidth (hwPortMap X Z M t) (.inl i) +
          clsCount (hwPortMap X Z M t) (hwExtCls X Z M t) (.inl i) := by
        rcases i with (((p | c) | c) | j)
        · cases p <;> simp [portWidth, capWidth, clsCount, widthCharge, hwExtCls, hwCls]
        all_goals simp [portWidth, capWidth, clsCount, widthCharge, hwExtCls, hwCls]
      rcases i with i | j
      · exact (querySupportedOn_spongeHardwiredRuntime_step W₀ m₀ i r n σ hσ).mono
          (Set.Iic_subset_Iic.mpr (by omega))
      · exact (hgT j r n σ hσ).mono (Set.Iic_subset_Iic.mpr (by omega))
    · obtain ⟨p, rfl⟩ := exists_eq_const_of_mixedRounds (hwPortMap X Z M t) hf
      have hb := LinearMap.congr_fun (par_step_portRound_branch W₀ m₀ step' p w r) σ
      refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
      have hcw := clsCount_round (port := hwPortMap X Z M t) (cls := hwExtCls X Z M t) hcls w
        fun _ ↦ p
      have hw : w ≤ portWidth (hwPortMap X Z M t) .h (.inr (.round w fun _ ↦ p)) +
          capWidth (hwPortMap X Z M t) (.inr (.round w fun _ ↦ p)) +
          clsCount (hwPortMap X Z M t) (hwExtCls X Z M t) (.inr (.round w fun _ ↦ p)) := by
        have hs := portWidth_round_self (hwPortMap X Z M t) p w
        unfold capWidth
        cases p <;> omega
      exact QuerySupportedOn.conj hσ fun y' y hK hy ↦ by
        have := dbGrade_le_of_portRound_ne_zero W₀ m₀ p y y' hK
        simp only [Set.mem_Iic] at hy ⊢
        omega
  · -- Quantum calls: single sponge calls and rounds of one port.
    intro i hi hf σ hσ n hn hσg
    rcases i with ((((p | c) | c) | j) | ⟨w, f⟩)
    · have hs : ∑' r : Unit, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inl p))).branch r σ) =
          potential (hwProjector S) (MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ) := by
        rw [tsum_fintype, Fintype.sum_unique, spongeHardwiredRuntime_step_sponge]
        rfl
      refine (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le ?_
      have hn1 : n ≤ qh + nk + K := by
        have : 1 ≤ portWidth (hwPortMap X Z M t) .h (.inl (.inl (.inl (.inl p)))) +
            capWidth (hwPortMap X Z M t) (.inl (.inl (.inl (.inl p)))) +
            clsCount (hwPortMap X Z M t) (hwExtCls X Z M t) (.inl (.inl (.inl (.inl p)))) := by
          cases p <;> simp [portWidth, capWidth, clsCount, widthCharge, hwExtCls, hwCls]
        omega
      cases p
      · have e1 : (portWidth (hwPortMap X Z M t) .h (.inl (.inl (.inl (.inl SpongePort.h)))) :
            ℝ≥0∞) = 1 := by simp [portWidth]
        have e2 : (capWidth (hwPortMap X Z M t) (.inl (.inl (.inl (.inl SpongePort.h)))) :
            ℝ≥0∞) = 0 := by simp [capWidth, portWidth]
        rw [e1, e2, mul_one, zero_mul, add_zero]
        exact rpow_inv_two_potential_single_le S .h (fun W m ↦ (hup W m).port .h) hεh
          (hh n hn1) W₀ m₀ hσ hσg
      · have e1 : (portWidth (hwPortMap X Z M t) .h (.inl (.inl (.inl (.inl SpongePort.k)))) :
            ℝ≥0∞) = 0 := by simp [portWidth]
        have e2 : (capWidth (hwPortMap X Z M t) (.inl (.inl (.inl (.inl SpongePort.k)))) :
            ℝ≥0∞) = 1 := by simp [capWidth, portWidth]
        rw [e1, e2, mul_zero, zero_mul, ENNReal.zero_rpow_of_pos (by norm_num), add_zero, one_mul]
        exact rpow_inv_two_potential_single_le S .k (fun W m ↦ (hup W m).port .k) hεc
          (fun W m ↦ (hfk W m).mono (by omega)) W₀ m₀ hσ hσg
      · have e1 : (portWidth (hwPortMap X Z M t) .h (.inl (.inl (.inl (.inl SpongePort.k')))) :
            ℝ≥0∞) = 0 := by simp [portWidth]
        have e2 : (capWidth (hwPortMap X Z M t) (.inl (.inl (.inl (.inl SpongePort.k')))) :
            ℝ≥0∞) = 1 := by simp [capWidth, portWidth]
        rw [e1, e2, mul_zero, zero_mul, ENNReal.zero_rpow_of_pos (by norm_num), add_zero, one_mul]
        exact rpow_inv_two_potential_single_le S .k' (fun W m ↦ (hup W m).port .k') hεc
          (fun W m ↦ (hfk' W m).mono (by omega)) W₀ m₀ hσ hσg
    · exact absurd hi (by simp [parCls, hwExtCls, hwCls])
    · exact absurd hi (by simp [parCls, hwExtCls, hwCls])
    · exact absurd hi (by simp [parCls, hwExtCls])
    · obtain ⟨p, rfl⟩ := exists_eq_const_of_mixedRounds (hwPortMap X Z M t) hf
      have hs : ∑' r : Fin w → Unit, potential (hwProjector S)
          (((((spongeHardwiredRuntime X Z W₀ m₀).extend step').par (hwPortMap X Z M t)).step
            (.inr (.round w fun _ ↦ p))).branch r σ) =
          potential (hwProjector S) (MatrixMap.conj (roundProd fun j : Fin w ↦
            slotLift (S := spongeIn X Z p) (N := HwReg X Z M) j
              ((spongeHardwired X Z W₀ m₀).U p)) σ) := by
        rw [tsum_fintype, Fintype.sum_unique]
        exact congrArg _ (LinearMap.congr_fun (par_step_portRound_branch W₀ m₀ step' p w _) σ)
      refine (congrArg (· ^ (2⁻¹ : ℝ)) hs).trans_le ?_
      have hcw := clsCount_round (port := hwPortMap X Z M t) (cls := hwExtCls X Z M t) hcls w
        fun _ ↦ p
      cases p
      · have e1 : portWidth (hwPortMap X Z M t) .h (.inr (.round w fun _ ↦ SpongePort.h)) = w :=
          portWidth_round_self _ _ _
        have e2 : capWidth (hwPortMap X Z M t) (.inr (.round w fun _ ↦ SpongePort.h)) = 0 :=
          by rw [capWidth, portWidth_round_ne _ (by decide), portWidth_round_ne _ (by decide)]
        rw [e1, e2, hcw] at hn
        rw [e1, e2, Nat.cast_zero, zero_mul, add_zero]
        exact rpow_inv_two_potential_hRound_le_at S Sc hsub hunion hloc hupc hεh
          (fun c W m ↦ (hfh c W m).mono (by omega)) W₀ m₀ w hσ hσg
      · have e1 : portWidth (hwPortMap X Z M t) .h (.inr (.round w fun _ ↦ SpongePort.k)) = 0 :=
          portWidth_round_ne _ (by decide) _
        have e2 : capWidth (hwPortMap X Z M t) (.inr (.round w fun _ ↦ SpongePort.k)) = w :=
          by rw [capWidth, portWidth_round_self, portWidth_round_ne _ (by decide), Nat.add_zero]
        rw [e1, e2, hcw] at hn
        rw [e1, e2, Nat.cast_zero, mul_zero, zero_mul, ENNReal.zero_rpow_of_pos (by norm_num),
          add_zero]
        exact rpow_inv_two_potential_portRound_le S .k (fun W m ↦ (hup W m).port .k) hεc
          (fun W m ↦ (hfk W m).mono (by omega)) W₀ m₀ hσ hσg
      · have e1 : portWidth (hwPortMap X Z M t) .h (.inr (.round w fun _ ↦ SpongePort.k')) = 0 :=
          portWidth_round_ne _ (by decide) _
        have e2 : capWidth (hwPortMap X Z M t) (.inr (.round w fun _ ↦ SpongePort.k')) = w :=
          by rw [capWidth, portWidth_round_ne _ (by decide), portWidth_round_self, Nat.zero_add]
        rw [e1, e2, hcw] at hn
        rw [e1, e2, Nat.cast_zero, mul_zero, zero_mul, ENNReal.zero_rpow_of_pos (by norm_num),
          add_zero]
        exact rpow_inv_two_potential_portRound_le S .k' (fun W m ↦ (hup W m).port .k') hεc
          (fun W m ↦ (hfk' W m).mono (by omega)) W₀ m₀ hσ hσg
  · -- Classical calls: the read, program and added ports.
    intro i hi hf σ hσ
    rcases i with ((((p | c) | c) | j) | ⟨w, f⟩)
    · exact absurd hi (by simp [parCls, hwExtCls, hwCls])
    · have hs : ∑' r : c.Result, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inr c))).branch r σ) =
          ∑' r : c.Result, potential (hwProjector S) (MatrixMap.conj (hwReadKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_read]; rfl
      exact hs.trans_le (hdR c σ hσ)
    · have hs : ∑' r : c.Result, potential (hwProjector S)
          (((spongeHardwiredRuntime X Z W₀ m₀).step (.inr c)).branch r σ) =
          ∑' r : c.Result, potential (hwProjector S) (MatrixMap.conj (hwProgKraus c r) σ) :=
        tsum_congr fun r ↦ by rw [spongeHardwiredRuntime_step_prog]; rfl
      exact hs.trans_le (hdP c σ hσ)
    · exact hdT j σ hσ
    · exact absurd hi (by simp [parCls])

end split

end Quantum.Par

end
