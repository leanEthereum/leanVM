import KeccakGkr.Openings

/-!
# The first claim

The protocol starts from the main protocol's point `(r_low, r_pack)` over the steps and its
values `v_ℓ` on the output lanes there. The verifier samples `r_seg` and `r_lane` (together `ρ`,
`r_seg` its first coordinate), the prover sends `c_st`, its value for the committed state after
the first segment, and the first claim is a random combination of both segments' outputs as
words (`firstClaim`, `§keccak:claims`).

`firstClaim_identity` is the soundness analysis's comparison of the two sides
(`§keccak:soundness`, the two ends): what the first claim and `keccak:eq:out` leave over is the
multilinear extension of `startTable` at `ρ`, a table that vanishes exactly when the statement
holds at the step point.
-/

open Polynomial

namespace KeccakGkr

variable {E : Type} [Field E] [CharP E 2]
variable (P : Perm) (D : ℕ) {n : ℕ} (Q : Column n) (x : E)

/-- The public data the start fixes. -/
structure Ctx (E : Type) (n : ℕ) where
  rl : Fin 4 → E
  rp : Fin n → E
  v : Lane → E
  ρ : Fin 6 → E
  cst : E

/-- The segment challenge. -/
def Ctx.rseg {n : ℕ} (c : Ctx E n) : E := c.ρ 0

/-- The lane challenges. -/
def Ctx.rlane {n : ℕ} (c : Ctx E n) : Fin 5 → E := Fin.tail c.ρ

/-- The first claim, at level `D`. -/
def firstClaim (c : Ctx E n) : Claim E n where
  c := c.cst + c.rseg * ∑ ℓ, eqPoly c.rlane (toPt (laneCube ℓ)) * c.v ℓ
  μ i := eqPoly c.rl (toPt i)
  r := Fin.snoc c.rp c.rseg
  w j := eqPoly c.rlane (toPt (laneCube j.1)) * x ^ j.2.val

/-- The right side of `keccak:eq:out`: the committed state after the first segment, at the
first claim's weights. -/
def outTotal (rl : Fin 4 → E) (rp : Fin n → E) (ρ : Fin 6 → E) : E :=
  ∑ o : Cube 6, outWeights (ρ 0) (Fin.tail ρ) o * colEval Q x rl rp (toPt o)

/-- `c_st` is what `keccak:eq:out` says. -/
def OutClaim (c : Ctx E n) : Prop := c.cst = outTotal Q x c.rl c.rp c.ρ

/-- Where the first segment's output and the committed state after it differ, as words. -/
def segDiff (i : Cube 4) (p : Cube n) (ℓ : Lane) : E :=
  word x (segState P D Q false D i p) ℓ - colWord Q x i p (slotCube true ℓ)

/-- The difference of the first segment's output lanes, at `r_low`. -/
def diffLow (rl : Fin 4 → E) (p : Cube n) (ℓ : Lane) : E :=
  ∑ i, eqPoly rl (toPt i) * segDiff P D Q x i p ℓ

/-- The difference of the first segment's output lanes, at `(r_low, r_pack)`. -/
def diffStep (rl : Fin 4 → E) (rp : Fin n → E) (ℓ : Lane) : E :=
  ∑ p, eqPoly rp (toPt p) * diffLow P D Q x rl p ℓ

/-- The table whose multilinear extension the first claim tests: the first segment's
differences on slot `0 ‖ ℓ`, the output values' on `1 ‖ ℓ`. -/
def startTable (rl : Fin 4 → E) (rp : Fin n → E) (v : Lane → E) (o : Cube 6) : E :=
  if o 0 then pad laneCube (fun ℓ => outEval P D Q x ℓ rl rp - v ℓ) (Fin.tail o)
  else pad laneCube (diffStep P D Q x rl rp) (Fin.tail o)

omit [CharP E 2] in
theorem eqPoly_snoc_toPt (r : Fin n → E) (t : E) (p : Cube n) (m : Bool) :
    eqPoly (Fin.snoc r t : Fin (n + 1) → E) (toPt (Fin.snoc p m)) = eqPoly r (toPt p) * eqBit t m := by
  rw [toPt_snoc, eqPoly_snoc]
  cases m <;> simp [eqBit, bit]

/-- The first claim's true value, lane by lane. -/
theorem firstClaim_value (c : Ctx E n) :
    claimValue P D Q D (firstClaim x c).μ (firstClaim x c).r (firstClaim x c).w =
      ∑ m : Bool, eqBit c.rseg m * ∑ ℓ, eqPoly c.rlane (toPt (laneCube ℓ)) *
        mleStep (fun i p => word x (segState P D Q m D i p) ℓ) c.rl c.rp := by
  have L : claimValue P D Q D (firstClaim x c).μ (firstClaim x c).r (firstClaim x c).w =
      ∑ t : Bool × Cube n × Cube 4 × Lane × Slice,
        eqPoly c.rp (toPt t.2.1) * eqBit c.rseg t.1 * (eqPoly c.rl (toPt t.2.2.1) *
          (eqPoly c.rlane (toPt (laneCube t.2.2.2.1)) * x ^ t.2.2.2.2.val *
            ι (segState P D Q t.1 D t.2.2.1 t.2.1 (t.2.2.2.1, t.2.2.2.2)))) := by
    simp only [claimValue, firstClaim]
    rw [sum_cube_snoc]
    simp only [Fin.snoc_last, Fin.init_snoc, eqPoly_snoc_toPt, Fintype.sum_prod_type,
      Finset.mul_sum]
  have R : (∑ m : Bool, eqBit c.rseg m * ∑ ℓ, eqPoly c.rlane (toPt (laneCube ℓ)) *
        mleStep (fun i p => word x (segState P D Q m D i p) ℓ) c.rl c.rp) =
      ∑ t : Bool × Lane × Cube 4 × Cube n × Slice, eqBit c.rseg t.1 *
        (eqPoly c.rlane (toPt (laneCube t.2.1)) * (eqPoly c.rl (toPt t.2.2.1) *
          eqPoly c.rp (toPt t.2.2.2.1) * (ι (segState P D Q t.1 D t.2.2.1 t.2.2.2.1
            (t.2.1, t.2.2.2.2)) * x ^ t.2.2.2.2.val))) := by
    simp only [mleStep, word, Fintype.sum_prod_type, Finset.mul_sum]
  rw [L, R]
  refine Fintype.sum_equiv
    { toFun := fun t => (t.1, t.2.2.2.1, t.2.2.1, t.2.1, t.2.2.2.2)
      invFun := fun t => (t.1, t.2.2.2.1, t.2.2.1, t.2.1, t.2.2.2.2)
      left_inv := fun t => rfl
      right_inv := fun t => rfl } _ _ fun t => ?_
  simp only [Equiv.coe_fn_mk]
  ring

theorem mle_startTable (rl : Fin 4 → E) (rp : Fin n → E) (v : Lane → E) (ρ : Fin 6 → E) :
    mle (startTable P D Q x rl rp v) ρ =
      (1 - ρ 0) * ∑ ℓ, eqPoly (Fin.tail ρ) (toPt (laneCube ℓ)) * diffStep P D Q x rl rp ℓ +
        ρ 0 * ∑ ℓ, eqPoly (Fin.tail ρ) (toPt (laneCube ℓ)) * (outEval P D Q x ℓ rl rp - v ℓ) := by
  have hm : ∀ f : Lane → E, ∑ o : Cube 5, eqPoly (Fin.tail ρ) (toPt o) * pad laneCube f o =
      ∑ ℓ, eqPoly (Fin.tail ρ) (toPt (laneCube ℓ)) * f ℓ := fun f => mle_pad laneCube f _
  simp only [mle, startTable]
  rw [sum_cube_cons]
  conv_lhs => rw [← Fin.cons_self_tail ρ]
  simp only [toPt_cons, eqPoly_cons, Fin.cons_zero, Fin.tail_cons, Fintype.sum_bool, ite_true,
    Bool.false_eq_true, ite_false, bit_true, bit_false, mul_assoc, ← Finset.mul_sum, hm]
  ring

theorem colEval_toPt (rl : Fin 4 → E) (rp : Fin n → E) (o : Cube 6) :
    colEval Q x rl rp (toPt o) = mleStep (fun i p => colWord Q x i p o) rl rp := by
  simp only [colEval, eqPoly_toPt_toPt, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single o]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem diffStep_eq (rl : Fin 4 → E) (rp : Fin n → E) (ℓ : Lane) :
    diffStep P D Q x rl rp ℓ = mleStep (fun i p => word x (segState P D Q false D i p) ℓ) rl rp -
      mleStep (fun i p => colWord Q x i p (slotCube true ℓ)) rl rp := by
  simp only [diffStep, diffLow, segDiff, mleStep, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring

theorem firstClaim_identity (c : Ctx E n) :
    claimValue P D Q D (firstClaim x c).μ (firstClaim x c).r (firstClaim x c).w -
        (firstClaim x c).c + (c.cst - outTotal Q x c.rl c.rp c.ρ) =
      mle (startTable P D Q x c.rl c.rp c.v) c.ρ := by
  have hout : outTotal Q x c.rl c.rp c.ρ = ∑ ℓ, (1 - c.ρ 0) * eqPoly (Fin.tail c.ρ)
      (toPt (laneCube ℓ)) * mleStep (fun i p => colWord Q x i p (slotCube true ℓ)) c.rl c.rp := by
    simp only [outTotal, outWeights, sum_pad_mul, colEval_toPt]
  rw [firstClaim_value, mle_startTable, hout]
  simp only [diffStep_eq, outEval, firstClaim, Ctx.rseg, Ctx.rlane, Fintype.sum_bool, eqBit,
    ite_true, Bool.false_eq_true, ite_false, Finset.mul_sum, mul_sub, mul_assoc,
    Finset.sum_sub_distrib]
  ring

end KeccakGkr
