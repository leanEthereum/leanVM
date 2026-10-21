import KeccakGkr.Layer

/-!
# The two openings

`§keccak:segments` of `doc/leanvm`, the second as in `§keccak:openings`. Both settle claims against
the committed column by short sumchecks of degree `2`:

* the committed state after the first segment, which the first claim's `c_st` speaks of, reduces
  to an evaluation of the column's words at `(r_low, r_pack, ρ_out)` (`outSummand`, equations
  `keccak:eq:out` and `keccak:eq:out-claim`);
* the claim at level `0`, on the committed inputs, reduces to the `64` bit slices of the column
  at one point (`inSummand₁` over the instance, then `inSummand₂` over the slot, equations
  `keccak:eq:in` and `keccak:eq:in-claim`).
-/

open Polynomial OracleComp
open scoped ENNReal

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (x : E)

/-! ## The committed state after the first segment -/

/-- The weights of `keccak:eq:out`: the second segment's input slots, weighted by the first
claim's lane weights and `eq(r_seg, 0)`. -/
def outWeights (rseg : E) (rlane : Fin 5 → E) : Cube 6 → E :=
  pad (fun ℓ => slotCube true ℓ) fun ℓ => (1 - rseg) * eqPoly rlane (toPt (laneCube ℓ))

/-- The summand of the sumcheck on `keccak:eq:out`. -/
def outSummand (rl : Fin 4 → E) (rp : Fin n → E) (rseg : E) (rlane : Fin 5 → E)
    (ro : Fin 6 → E) : E :=
  mle (outWeights rseg rlane) ro * colEval Q x rl rp ro

theorem colEval_deg (rl : Fin 4 → E) (rp : Fin n → E) :
    IndivDeg 1 (colEval Q x rl rp) := by
  unfold colEval
  exact IndivDeg.sum _ fun o _ => (IndivDeg.eqPoly_left _).mul_const _

theorem outSummand_deg (rl : Fin 4 → E) (rp : Fin n → E) (rseg : E) (rlane : Fin 5 → E) :
    IndivDeg 2 (outSummand Q x rl rp rseg rlane) :=
  (IndivDeg.mle _).mul (colEval_deg Q x rl rp)

/-! ## The committed inputs -/

/-- The weights of `keccak:eq:in` at slice `z`: slot `slotCube m ℓ` weighs
`eq(r_seg, m) w(ℓ, z)`. -/
def inWeights (rseg : E) (w : Pos → E) (z : Slice) : Cube 6 → E :=
  pad (fun mℓ : Bool × Lane => slotCube mℓ.1 mℓ.2) fun mℓ => eqBit rseg mℓ.1 * w (mℓ.2, z)

/-- The summand of the sumcheck over the instance. -/
def inSummand₁ (μ : Cube 4 → E) (rp : Fin n → E) (rseg : E) (w : Pos → E) (rl : Fin 4 → E) :
    E :=
  mle μ rl * ∑ o : Cube 6, ∑ z : Slice, inWeights rseg w z o * sliceEval Q z rl rp (toPt o)

/-- The summand of the sumcheck over the slot. -/
def inSummand₂ (μ : Cube 4 → E) (rp : Fin n → E) (rseg : E) (w : Pos → E) (fl : Fin 4 → E)
    (ro : Fin 6 → E) : E :=
  mle μ fl * ∑ z : Slice, mle (inWeights rseg w z) ro * sliceEval Q z fl rp ro

theorem sliceEval_deg_slot (z : Slice) (rl : Fin 4 → E) (rp : Fin n → E) :
    IndivDeg 1 (sliceEval Q z rl rp) := by
  unfold sliceEval
  exact IndivDeg.sum _ fun o _ => (IndivDeg.eqPoly_left _).mul_const _

theorem sliceEval_deg_inst (z : Slice) (rp : Fin n → E) (ro : Fin 6 → E) :
    IndivDeg 1 fun rl => sliceEval Q z rl rp ro := by
  unfold sliceEval mleStep
  refine IndivDeg.sum _ fun o _ => IndivDeg.smul _ (IndivDeg.sum _ fun i _ => ?_)
  refine IndivDeg.sum _ fun p _ => ?_
  have := IndivDeg.smul (eqPoly rp (toPt p) * ι (Q i p o z)) (IndivDeg.eqPoly_left (toPt i))
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

theorem inSummand₁_deg (μ : Cube 4 → E) (rp : Fin n → E) (rseg : E) (w : Pos → E) :
    IndivDeg 2 (inSummand₁ Q μ rp rseg w) :=
  (IndivDeg.mle μ).mul (IndivDeg.sum _ fun o _ => IndivDeg.sum _ fun z _ =>
    IndivDeg.smul _ (sliceEval_deg_inst Q z rp (toPt o)))

theorem inSummand₂_deg (μ : Cube 4 → E) (rp : Fin n → E) (rseg : E) (w : Pos → E)
    (fl : Fin 4 → E) : IndivDeg 2 (inSummand₂ Q μ rp rseg w fl) := by
  have := (IndivDeg.const (n := 6) (mle μ fl)).mul (IndivDeg.sum Finset.univ fun z _ =>
    (IndivDeg.mle (inWeights rseg w z)).mul (sliceEval_deg_slot Q z fl rp))
  exact this

/-! ## The sums -/

omit [CharP E 2] in
theorem mleStep_toPt (f : Cube 4 → Cube n → E) (i : Cube 4) (rp : Fin n → E) :
    mleStep f (toPt i) rp = ∑ p, eqPoly rp (toPt p) * f i p := by
  simp only [mleStep, eqPoly_toPt_toPt, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem total_out (rl : Fin 4 → E) (rp : Fin n → E) (rseg : E) (rlane : Fin 5 → E) :
    ∑ o : Cube 6, outSummand Q x rl rp rseg rlane (toPt o) =
      ∑ o : Cube 6, outWeights rseg rlane o * colEval Q x rl rp (toPt o) := by
  simp [outSummand, mle_toPt]

theorem sliceEval_toPt (z : Slice) (i : Cube 4) (rp : Fin n → E) (o : Cube 6) :
    sliceEval Q z (toPt i) rp (toPt o) = ∑ p, eqPoly rp (toPt p) * ι (Q i p o z) := by
  simp only [sliceEval, eqPoly_toPt_toPt, ite_mul, one_mul, zero_mul, mleStep_toPt]
  rw [Finset.sum_eq_single o]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

/-- The sumcheck over the instance starts from the claim's value at level `0`. -/
theorem total_in₁ (cl : Claim E n) :
    ∑ i : Cube 4, inSummand₁ Q cl.μ (Fin.init cl.r) (cl.r (Fin.last n)) cl.w (toPt i) =
      claimValue P D Q 0 cl.μ cl.r cl.w := by
  set rp := Fin.init cl.r
  set rseg := cl.r (Fin.last n)
  have L : ∑ i : Cube 4, inSummand₁ Q cl.μ rp rseg cl.w (toPt i) =
      ∑ t : Cube 4 × Slice × (Bool × Lane) × Cube n, cl.μ t.1 * (eqBit rseg t.2.2.1.1 *
        cl.w (t.2.2.1.2, t.2.1) * (eqPoly rp (toPt t.2.2.2) *
          ι (Q t.1 t.2.2.2 (slotCube t.2.2.1.1 t.2.2.1.2) t.2.1))) := by
    simp only [inSummand₁, mle_toPt, sliceEval_toPt]
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [inWeights, sum_pad_mul, Fintype.sum_prod_type]
  have R : claimValue P D Q 0 cl.μ cl.r cl.w =
      ∑ t : Bool × Cube n × Cube 4 × Lane × Slice, eqPoly rp (toPt t.2.1) * eqBit rseg t.1 *
        (cl.μ t.2.2.1 * (cl.w (t.2.2.2.1, t.2.2.2.2) *
          ι (Q t.2.2.1 t.2.1 (slotCube t.1 t.2.2.2.1) t.2.2.2.2))) := by
    simp only [claimValue]
    rw [sum_cube_snoc]
    have hr : cl.r = Fin.snoc rp rseg := (Fin.snoc_init_self _).symm
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun p _ => ?_
    rw [hr, toPt_snoc, eqPoly_snoc, Fin.snoc_last, Fin.init_snoc]
    congr 1
    · cases m <;> simp [eqBit, bit]
  rw [L, R]
  refine Fintype.sum_equiv
    { toFun := fun t => (t.2.2.1.1, t.2.2.2, t.1, t.2.2.1.2, t.2.1)
      invFun := fun t => (t.2.2.1, t.2.2.2.2, (t.1, t.2.2.2.1), t.2.1)
      left_inv := fun t => rfl
      right_inv := fun t => rfl } _ _ fun t => ?_
  simp only [Equiv.coe_fn_mk]
  ring

theorem total_in₂ (μ : Cube 4 → E) (rp : Fin n → E) (rseg : E) (w : Pos → E) (fl : Fin 4 → E) :
    ∑ o : Cube 6, inSummand₂ Q μ rp rseg w fl (toPt o) = inSummand₁ Q μ rp rseg w fl := by
  simp only [inSummand₂, inSummand₁, mle_toPt, ← Finset.mul_sum]

end KeccakGkr
