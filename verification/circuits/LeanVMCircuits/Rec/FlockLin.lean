module

public import LeanVMCircuits.Rec.TableChain
public import LeanVMCircuits.Rec.Bind

@[expose] public section

/-!
Flock's lincheck over the recursion circuit's HASH rows (`lincheck::verify_deferred`), as a check of `RecParts`.

The zerocheck leaves a claimed triple `(a, b, c)` at the point `(ζ, x_inner, x_outer)`. The lincheck draws `α`, takes the input claim `a + α b + α^2 c + α^3` (the last term the constant wire's pin, its target one) and runs `h` plain degree-two rounds (`read_round(3, running, None)`), binding the top inner variable first. Then it reads the 64 bit slices `s_i` and the matrices' form value `M`, and tests the last claim against `M + α^3 s_{pin % 64} eq(pin / 64, R) + α^2 eq(x_inner, R) Σ_i L_i(ζ) s_i`, `R` the challenges reversed. The value `M` is not checked here: `verify_deferred` returns it as a `MatrixClaim` that the tree's matrix reduction settles.

The semantic layer (`FlockLin`) is parametric in the circuit's base matrices `A_0`, `B_0` and pin column (`Mats`), the skip's Lagrange weights at `ζ` (`lz`), the inner point and the witness folded at the outer point (`Zv i J = Σ_t eq(x_outer, t) Q_i(J, t)`, `outerFold`). Column `64 J + i` of the base matrices is slice `i` of inner word `J`. Row `row`'s weight is `u(row) = lz(row % 64) eq(x_inner, row / 64)` (`rowW`), the column marginal `M_α(i, J) = Σ_row u(row) (A_0 + α B_0)(row, 64 J + i)` (`marg`).

`linInst`: the honest instance, `mvInst` of the polynomial `H(J) = Σ_i [M_α(i, J) + α^2 lz(i) eq(x_inner, J) + α^3 [i = pin % 64] eq(pin / 64, J)] Z_i(J)` with its variables reversed. `linInst_sum`, `linInst_ok` (degree two), `linInst_final`, `linInst_weight` (no eq weight factored out). `linInst_sum_eq`: its sum is `a* + α b* + α^2 c* + α^3 z_pin`, the true triple (`triA`, `triB`, `triC`) and the pin's outer-folded value (`pinV`). `formVal_eq`: the matrices' form `u^T (A_0 + α B_0) w`, `w(64 J + i) = s_i eq(R, J)`, is `Σ_i M̃_α(i)(R) s_i`.

The batching: `alphaBad d` is the set of `α` at which the nonzero difference `d` (`diff`, the claimed triple less the true one and one less the pin's folded value) satisfies `d_0 + α d_1 + α^2 d_2 + α^3 d_3 = 0`, at most three (`alphaBad_card`); off it the input claim at the honest sum makes the triple true and the folded pin one (`claim_true`). `alphaRun_frac`: as a run's draw after the triple, at most `3/|E|` of the oracles. `pinBad`: the outer points at which a pin column not one on every row still folds to one, at most `no/|E|` of them (`pinBad_card`, Schwartz-Zippel; `pinRun_frac`); off it the folded pin being one makes every row's pin one (`pin_rows`). `slice_mle`: the slice `MLE(Z_i)(R)` is the committed slice's extension at `R ++ x_outer`.

The certificate (`Bind.LinCert`): its `SumcheckCert`, `α`, the triple, the input claim's calls (`mul(α, α)`, `mul(α^2, α)`, `mul_add(α, b, a)`, `mul_add(α^2, c, ·)`, `add(·, α^3)`, `mul_add(one, ·, zero)`), the inner point, the 64 slices, the form value, the pin's `eq_bits` calls (by the pin's bits, top variable first), the Lagrange sum's `mul_add(s_i, inv_i, acc)` and `mul(scale, ·)`, `eq_eval`'s `add(x_k, R_k)` and `mul_add(acc, ·, acc)`, and the terminal's `mul`, `mul_add` calls. `LinCert.okIn` also checks the sumcheck's shape: no residual, degree two, no eq weight, the HASH circuit's pin `hashPin`, the input claim the batch's output and the test's other side the terminal's. `LinCert.zeroLink`: the triple and the inner point are the zerocheck's. `LinCert.sem`: what the calls give where they hold. `LinCert.final_eq`: at true slices, the true matrix form (`LinCert.MatrixHolds`, the deferred obligation) and the Lagrange weights `lz i = scale · inv_i`, the sumcheck's final side is `linInst`'s final value. `Bind.lin_part`: the input claim is then `linInst`'s sum off `sumcheckFalse`. `Bind.lin_triple`: off `alphaBad` too, the claimed triple is the true one and the pin folds to one. `Bind.linOf` names a `LinCert` from a replay.

What stays a premise: the slices' truth (an opening, `slice_mle` its form, the ring switch's to discharge), the matrix claim (`MatrixHolds`, the tree's matrix reduction's), the Lagrange weights `scale · inv_i` being the skip's basis at `ζ` (the skip domain's), and the inner point and triple being the zerocheck's (`zeroLink`).
-/

namespace LeanVMCircuits.Rec.FlockLin

open LeanVMCircuits.Rec Model MvPolynomial Finset Classical Sumcheck AirLink

/-! The honest objects. -/

/-- The base matrices' side, `2^(6 + h)`: column `64 J + i` is slice `i` of inner word `J`. -/
def nc (h : ℕ) : ℕ := 2 ^ h * 64

/-- A circuit's lincheck data: its base matrices `A_0`, `B_0` by (row, column) and its constant wire's column. -/
structure Mats where
  A0 : ℕ → ℕ → E
  B0 : ℕ → ℕ → E
  pin : ℕ

variable {h : ℕ}

/-- Row `row`'s weight `u(row)`: the skip's Lagrange weight `lz` of its low six bits times `eq(x_inner, ·)` of its
inner word. -/
noncomputable def rowW (lz : ℕ → E) (xin : Fin h → E) (row : ℕ) : E :=
  lz (row % 64) * eqv xin (bitPoint h (row / 64))

/-- The outer-folded witness at column `col`: slice `col % 64` of inner word `col / 64`. -/
def colZ (Zv : ℕ → ℕ → E) (col : ℕ) : E := Zv (col % 64) (col / 64)

/-- The true `a* = (A z)*` at `(ζ, x_inner, x_outer)`: `u^T A_0 Z`. -/
noncomputable def triA (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) : E :=
  ∑ row ∈ range (nc h), rowW lz xin row * ∑ col ∈ range (nc h), M.A0 row col * colZ Zv col

/-- The true `b* = (B z)*`: `u^T B_0 Z`. -/
noncomputable def triB (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) : E :=
  ∑ row ∈ range (nc h), rowW lz xin row * ∑ col ∈ range (nc h), M.B0 row col * colZ Zv col

/-- The true `c* = z*`: `u^T Z`. -/
noncomputable def triC (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) : E :=
  ∑ row ∈ range (nc h), rowW lz xin row * colZ Zv row

/-- The pin's outer-folded value. -/
def pinV (M : Mats) (Zv : ℕ → ℕ → E) : E := colZ Zv M.pin

/-- The column marginal `M_α(i, J) = Σ_row u(row) (A_0 + α B_0)(row, 64 J + i)` (`fold_alpha_batched`). -/
noncomputable def marg (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (α : E) (i J : ℕ) : E :=
  ∑ row ∈ range (nc h), rowW lz xin row * (M.A0 row (64 * J + i) + α * M.B0 row (64 * J + i))

/-- The summand's coefficient of `Z_i(J)` on the cube. -/
noncomputable def comb (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (α : E) (i J : ℕ) : E :=
  marg M lz xin α i J + α ^ 2 * lz i * eqv xin (bitPoint h J) +
    α ^ 3 * (if i = M.pin % 64 then 1 else 0) * (if M.pin / 64 = J then 1 else 0)

/-- Values on the cube's points `J < 2^h` as a multilinear polynomial. -/
noncomputable def mlePoly (h : ℕ) (V : ℕ → E) : MvPolynomial (Fin h) E :=
  ∑ J ∈ range (2 ^ h), eqPoly h h J * C (V J)

/-- `eq(x, X) = Π_j (1 + x_j + X_j)`, as `eq_eval` computes it. -/
noncomputable def eqX (xin : Fin h → E) : MvPolynomial (Fin h) E := ∏ j, (1 + C (xin j) + X j)

/-- Slice `i`'s coefficient polynomial. -/
noncomputable def combPoly (h : ℕ) (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (α : E) (i : ℕ) :
    MvPolynomial (Fin h) E :=
  mlePoly h (marg M lz xin α i) + C (α ^ 2 * lz i) * eqX xin +
    C (α ^ 3 * if i = M.pin % 64 then 1 else 0) * eqPoly h h (M.pin / 64)

/-- The lincheck's polynomial `H`. -/
noncomputable def linPoly (h : ℕ) (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E) :
    MvPolynomial (Fin h) E :=
  ∑ i ∈ range 64, combPoly h M lz xin α i * mlePoly h (Zv i)

/-- The lincheck's honest instance: `linPoly` with its variables reversed, round `j` binding inner variable
`h - 1 - j` (the top first). -/
noncomputable def linInst (h : ℕ) (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E) : Inst E h :=
  mvInst h (rename Fin.rev (linPoly h M lz xin Zv α))

/-! Evaluations. -/

theorem eval_mlePoly_bit (V : ℕ → E) {J : ℕ} (hJ : J < 2 ^ h) : eval (bitPoint h J) (mlePoly h V) = V J := by
  simp only [mlePoly, map_sum, map_mul, eval_C]
  rw [sum_congr rfl fun z hz => by rw [eval_eqPoly le_rfl (mem_range.mp hz) hJ]]
  simp [hJ]

theorem eval_mlePoly (V : ℕ → E) (R : Fin h → E) : eval R (mlePoly h V) = mleAt h R V := by
  simp only [mlePoly, mleAt, map_sum, map_mul, eval_C, eval_eqPoly_eqv]

theorem eval_eqX (xin R : Fin h → E) : eval R (eqX xin) = ∏ j, (1 + xin j + R j) := by
  simp only [eqX, map_prod, map_add, map_one, eval_C, eval_X]

theorem eval_eqPoly_at (z : ℕ) (R : Fin h → E) :
    eval R (eqPoly h h z) = ∏ j : Fin h, if z.testBit j then R j else 1 + R j := by
  simp only [eqPoly, map_prod]
  refine prod_congr rfl fun j _ => ?_
  simp only [j.isLt, if_true]
  split_ifs <;> simp

/-- In characteristic two, `eq(x, b)` at a Boolean point is `Π_j (1 + x_j + b_j)`. -/
theorem eqv_bitPoint (x : Fin h → E) (J : ℕ) : eqv x (bitPoint h J) = ∏ j, (1 + x j + bitPoint h J j) := by
  simp only [eqv]
  refine prod_congr rfl fun j _ => ?_
  by_cases hb : J.testBit j = true
  · simp only [bitPoint, hb, if_true]
    linear_combination (-1 : E) * one_add_one
  · have hb' : J.testBit j = false := by simpa using hb
    simp only [bitPoint, hb', Bool.false_eq_true, if_false, sub_zero, mul_one, mul_zero, add_zero]
    exact one_sub_eq_one_add _

theorem eval_combPoly_bit (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (α : E) (i : ℕ) {J : ℕ} (hJ : J < 2 ^ h)
    (hpin : M.pin / 64 < 2 ^ h) : eval (bitPoint h J) (combPoly h M lz xin α i) = comb M lz xin α i J := by
  simp only [combPoly, comb, map_add, map_mul, eval_C, eval_mlePoly_bit _ hJ, eval_eqX, ← eqv_bitPoint,
    eval_eqPoly le_rfl hpin hJ]

/-! The honest instance's truths. -/

/-- The instance's sum: each inner word's coefficients times its outer-folded slices. -/
theorem linInst_sum (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E)
    (hpin : M.pin / 64 < 2 ^ h) :
    (linInst h M lz xin Zv α).sum = ∑ J ∈ range (2 ^ h), ∑ i ∈ range 64, comb M lz xin α i J * Zv i J := by
  rw [linInst, mvInst_sum]
  simp only [eval_rename]
  rw [sum_cube_rev h (fun x => eval x (linPoly h M lz xin Zv α)), sum_cube_bits]
  refine sum_congr rfl fun J hJ => ?_
  simp only [linPoly, map_sum, map_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [eval_combPoly_bit M lz xin α i (mem_range.mp hJ) hpin, eval_mlePoly_bit _ (mem_range.mp hJ)]

theorem degreeOf_mlePoly (V : ℕ → E) (i : Fin h) : degreeOf i (mlePoly h V) ≤ 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun z _ => ?_)
  exact (degreeOf_mul_C_le _ _ _).trans (degreeOf_eqPoly i)

theorem degreeOf_eqX (xin : Fin h → E) (i : Fin h) : degreeOf i (eqX xin) ≤ 1 :=
  degreeOf_prod_factors i _ fun j => degreeOf_factor_le i j _ (degreeOf_one_add_C i _)

theorem degreeOf_combPoly (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (α : E) (k : ℕ) (i : Fin h) :
    degreeOf i (combPoly h M lz xin α k) ≤ 1 := by
  unfold combPoly
  refine (degreeOf_add_le _ _ _).trans (max_le ((degreeOf_add_le _ _ _).trans (max_le ?_ ?_)) ?_)
  · exact degreeOf_mlePoly _ i
  · refine (degreeOf_mul_le _ _ _).trans ?_
    rw [degreeOf_C, zero_add]
    exact degreeOf_eqX xin i
  · refine (degreeOf_mul_le _ _ _).trans ?_
    rw [degreeOf_C, zero_add]
    exact degreeOf_eqPoly i

theorem degreeOf_linPoly (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E) (i : Fin h) :
    degreeOf i (linPoly h M lz xin Zv α) ≤ 2 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_combPoly M lz xin α k i
  have h2 := degreeOf_mlePoly (Zv k) i
  omega

/-- The instance has degree `d` for every `d ≥ 2`: `read_round(3, ..)` reads degree-two rounds. -/
theorem linInst_ok (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E) {d : ℕ} (hd : 2 ≤ d) :
    (linInst h M lz xin Zv α).ok d := by
  refine mvInst_ok d _ fun i => ?_
  have hr := degreeOf_rename_of_injective (p := linPoly h M lz xin Zv α) Fin.rev_injective (Fin.rev i)
  rw [Fin.rev_rev] at hr
  rw [hr]
  exact (degreeOf_linPoly M lz xin Zv α _).trans hd

/-- No round factors out an eq weight, as `read_round(3, running, None)` reads them. -/
theorem linInst_weight (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E) (r : Fin h → E)
    (i : Fin h) : (linInst h M lz xin Zv α).weight r i = none :=
  mvInst_weight _ r i

/-- `eq_bits(z, R) = Π_j (z_j ? R_j : 1 + R_j)`. -/
noncomputable def eqBits (z : ℕ) (R : Fin h → E) : E := ∏ j : Fin h, if z.testBit j then R j else 1 + R j

/-- `eq_eval(x, R) = Π_j (1 + x_j + R_j)`. -/
noncomputable def eqAdd (x R : Fin h → E) : E := ∏ j, (1 + x j + R j)

/-- The instance's final value along `r`, at `R = chi r`: each slice's coefficient (the marginal's extension, the `C`
term at `eq(x_inner, R)` and the pin at `eq(pin / 64, R)`) times the slice's extension. -/
theorem linInst_final (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E) (r : Fin h → E) :
    (linInst h M lz xin Zv α).final r = ∑ i ∈ range 64,
      (mleAt h (chi r) (marg M lz xin α i) + α ^ 2 * lz i * eqAdd xin (chi r) +
        α ^ 3 * (if i = M.pin % 64 then 1 else 0) * eqBits (M.pin / 64) (chi r)) * mleAt h (chi r) (Zv i) := by
  rw [linInst, mvInst_final, eval_rename]
  simp only [linPoly, combPoly, map_sum, map_mul, map_add, eval_C, eval_mlePoly, eval_eqX, eval_eqPoly_at, eqAdd,
    eqBits]
  rfl

/-! The sum as the true triple and pin. -/

/-- The base matrices' columns as inner words and slices. -/
theorem sum_cols (f : ℕ → E) :
    ∑ col ∈ range (nc h), f col = ∑ J ∈ range (2 ^ h), ∑ i ∈ range 64, f (64 * J + i) :=
  sum_range_mul f 64 (2 ^ h)

theorem colZ_split (Zv : ℕ → ℕ → E) {i : ℕ} (J : ℕ) (hi : i < 64) : colZ Zv (64 * J + i) = Zv i J := by
  simp only [colZ]
  congr 1 <;> omega

theorem rowW_split (lz : ℕ → E) (xin : Fin h → E) {i : ℕ} (J : ℕ) (hi : i < 64) :
    rowW lz xin (64 * J + i) = lz i * eqv xin (bitPoint h J) := by
  simp only [rowW]
  rw [show (64 * J + i) % 64 = i by omega, show (64 * J + i) / 64 = J by omega]

/-- Three sums in the reverse order. -/
theorem sum3_comm {s t u : Finset ℕ} (f : ℕ → ℕ → ℕ → E) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ b ∈ t, ∑ a ∈ s, f a b c := by
  rw [sum_comm, sum_congr rfl fun b _ => sum_comm, sum_comm]

/-- A marginal's sum against the folded slices is the matrix's bilinear form against the folded witness. -/
theorem sum_marg (g : ℕ → ℕ → E) (Zv : ℕ → ℕ → E) :
    ∑ J ∈ range (2 ^ h), ∑ i ∈ range 64, (∑ row ∈ range (nc h), g row (64 * J + i)) * Zv i J =
      ∑ row ∈ range (nc h), ∑ col ∈ range (nc h), g row col * colZ Zv col := by
  simp only [sum_mul]
  rw [sum_congr rfl fun J _ => sum_comm, sum_comm]
  refine sum_congr rfl fun row _ => ?_
  rw [sum_cols]
  exact sum_congr rfl fun J _ => sum_congr rfl fun i hi => by rw [colZ_split Zv J (mem_range.mp hi)]

/-- The instance's sum is the batch of the true triple and pin: `a* + α b* + α^2 c* + α^3 z_pin`, the pin's inner
word on the cube. -/
theorem linInst_sum_eq (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E)
    (hpin : M.pin / 64 < 2 ^ h) :
    (linInst h M lz xin Zv α).sum =
      triA M lz xin Zv + α * triB M lz xin Zv + α ^ 2 * triC lz xin Zv + α ^ 3 * pinV M Zv := by
  rw [linInst_sum M lz xin Zv α hpin]
  simp only [comb, add_mul, sum_add_distrib]
  have e1 : ∑ J ∈ range (2 ^ h), ∑ i ∈ range 64, marg M lz xin α i J * Zv i J =
      triA M lz xin Zv + α * triB M lz xin Zv := by
    simp only [marg]
    rw [sum_marg (fun row col => rowW lz xin row * (M.A0 row col + α * M.B0 row col)) Zv]
    simp only [triA, triB, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun row _ => sum_congr rfl fun col _ => by ring
  have e2 : ∑ J ∈ range (2 ^ h), ∑ i ∈ range 64, α ^ 2 * lz i * eqv xin (bitPoint h J) * Zv i J =
      α ^ 2 * triC lz xin Zv := by
    rw [triC, sum_cols, mul_sum]
    refine sum_congr rfl fun J _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [rowW_split lz xin J (mem_range.mp hi), colZ_split Zv J (mem_range.mp hi)]
    ring
  have e3 : ∑ J ∈ range (2 ^ h), ∑ i ∈ range 64,
      α ^ 3 * (if i = M.pin % 64 then 1 else 0) * (if M.pin / 64 = J then 1 else 0) * Zv i J = α ^ 3 * pinV M Zv := by
    have hl : M.pin % 64 < 64 := Nat.mod_lt _ (by norm_num)
    have hterm : ∀ J i, α ^ 3 * (if i = M.pin % 64 then 1 else 0) * (if M.pin / 64 = J then 1 else 0) * Zv i J =
        if i = M.pin % 64 then (if J = M.pin / 64 then α ^ 3 * Zv (M.pin % 64) (M.pin / 64) else 0) else 0 := by
      intro J i
      by_cases h1 : J = M.pin / 64 <;> by_cases h2 : i = M.pin % 64 <;> simp [h1, h2, eq_comm]
    simp only [hterm, sum_ite_eq', mem_range, hl, hpin, if_true]
    rfl
  rw [e1, e2, e3]

/-! The deferred matrix claim. -/

/-- The matrices' form `u^T (A_0 + α B_0) w` at `R` with slices `s`, `w(64 J + i) = s_i eq(R, J)`
(`LincheckCircuit::bilinear_form`): what `verify_deferred`'s `MatrixClaim` holds the prover's value to. -/
noncomputable def formVal (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (α : E) (R : Fin h → E) (s : ℕ → E) : E :=
  ∑ row ∈ range (nc h), rowW lz xin row *
    ∑ col ∈ range (nc h), (M.A0 row col + α * M.B0 row col) * (s (col % 64) * eqv R (bitPoint h (col / 64)))

/-- The form is each slice times its marginal's extension at `R`. -/
theorem formVal_eq (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (α : E) (R : Fin h → E) (s : ℕ → E) :
    formVal M lz xin α R s = ∑ i ∈ range 64, mleAt h R (marg M lz xin α i) * s i := by
  have hl : formVal M lz xin α R s = ∑ row ∈ range (nc h), ∑ J ∈ range (2 ^ h), ∑ i ∈ range 64,
      rowW lz xin row * (M.A0 row (64 * J + i) + α * M.B0 row (64 * J + i)) * (s i * eqv R (bitPoint h J)) := by
    refine sum_congr rfl fun row _ => ?_
    rw [sum_cols, mul_sum]
    refine sum_congr rfl fun J _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    rw [show (64 * J + i) % 64 = i by omega, show (64 * J + i) / 64 = J by omega]
    ring
  rw [hl]
  simp only [mleAt, marg, sum_mul, mul_sum]
  rw [sum3_comm]
  exact sum_congr rfl fun row _ => sum_congr rfl fun J _ => sum_congr rfl fun i _ => by ring

/-! The batching at `α`. -/

/-- `d_0 + d_1 α + d_2 α^2 + d_3 α^3` as a polynomial in `α`. -/
noncomputable def alphaPoly (d : Fin 4 → E) : Polynomial E :=
  Polynomial.C (d 0) + Polynomial.C (d 1) * Polynomial.X + Polynomial.C (d 2) * Polynomial.X ^ 2 +
    Polynomial.C (d 3) * Polynomial.X ^ 3

theorem eval_alphaPoly (d : Fin 4 → E) (α : E) :
    (alphaPoly d).eval α = d 0 + α * d 1 + α ^ 2 * d 2 + α ^ 3 * d 3 := by
  simp only [alphaPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  ring

theorem coeff_alphaPoly (d : Fin 4 → E) (N : ℕ) : (alphaPoly d).coeff N =
    (if N = 0 then d 0 else 0) + (if N = 1 then d 1 else 0) + (if N = 2 then d 2 else 0) +
      (if N = 3 then d 3 else 0) := by
  simp only [alphaPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]

/-- The input claim's draw event at the difference `d` between the claimed and the true triple and pin: `d` is
nonzero, yet its batch vanishes at `α`. -/
noncomputable def alphaBad (d : Fin 4 → E) : Finset E := {α | d ≠ 0 ∧ d 0 + α * d 1 + α ^ 2 * d 2 + α ^ 3 * d 3 = 0}

/-- At most three `α`: a nonzero polynomial of degree at most three. -/
theorem alphaBad_card (d : Fin 4 → E) : #(alphaBad d) ≤ 3 := by
  by_cases hd : d = 0
  · have : alphaBad d = ∅ := by
      ext α
      simp [alphaBad, hd]
    rw [this, card_empty]
    exact Nat.zero_le _
  have hp : alphaPoly d ≠ 0 := by
    intro h0
    refine hd (funext fun k => ?_)
    have e := coeff_alphaPoly d k
    rw [h0, Polynomial.coeff_zero] at e
    fin_cases k <;> simp at e ⊢ <;> exact e.symm
  have hdeg : (alphaPoly d).natDegree ≤ 3 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_alphaPoly, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  calc #(alphaBad d) ≤ (alphaPoly d).roots.toFinset.card := by
        refine card_le_card fun α hα => ?_
        simp only [alphaBad, Finset.mem_filter, Finset.mem_univ, true_and] at hα
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_alphaPoly]
        exact hα.2
    _ ≤ Multiset.card (alphaPoly d).roots := Multiset.toFinset_card_le _
    _ ≤ (alphaPoly d).natDegree := Polynomial.card_roots' _
    _ ≤ 3 := hdeg

/-- Off the event, the batch vanishing makes the difference zero. -/
theorem batch_eq {d : Fin 4 → E} {α : E} (hα : α ∉ alphaBad d)
    (h : d 0 + α * d 1 + α ^ 2 * d 2 + α ^ 3 * d 3 = 0) : d = 0 := by
  by_contra hne
  exact hα (by simp only [alphaBad, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hne, h⟩)

/-- The difference between a claimed triple `t` with the pin's target one and the true triple `T` with the pin's
value `p`. -/
noncomputable def diff (t T : Fin 3 → E) (p : E) : Fin 4 → E := ![t 0 - T 0, t 1 - T 1, t 2 - T 2, 1 - p]

/-- The lincheck's batching: off the event at the difference, the input claim `a + α b + α^2 c + α^3` being the true
batch makes each of the claimed triple true and the pin's value one. -/
theorem claim_true {t T : Fin 3 → E} {p α : E} (hα : α ∉ alphaBad (diff t T p))
    (h : t 0 + α * t 1 + α ^ 2 * t 2 + α ^ 3 = T 0 + α * T 1 + α ^ 2 * T 2 + α ^ 3 * p) :
    t = T ∧ p = 1 := by
  have hd := batch_eq hα (by simp only [diff]; simp; linear_combination h)
  have e : ∀ k, diff t T p k = 0 := fun k => by rw [hd]; rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3
  simp only [diff] at e0 e1 e2 e3
  simp at e0 e1 e2 e3
  refine ⟨funext fun k => ?_, by linear_combination -e3⟩
  fin_cases k
  · simpa using sub_eq_zero.mp e0
  · simpa using sub_eq_zero.mp e1
  · simpa using sub_eq_zero.mp e2

open Classical in
/-- `α` as a run's challenge drawn after time `k`: where the difference is committed before `k`, the oracles at which
`α` is in the draw event are at most `3/|E|` of them. -/
theorem alphaRun_frac {c : Bind.Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (hR : Bind.Run c s T C st val) {own : Fin 1 → Fin 3 → ℕ} {time : Fin 1 → ℕ}
    (hown : Bind.OwnAt s (c.transcripts.getD T default) own time) (hinj : Bind.OwnInj own) {k : ℕ}
    (hk : ∀ i, k ≤ time i) (d : (ℕ → K) → Fin 4 → E)
    (hd : Bind.CommittedBefore s (c.transcripts.getD T default) val k d)
    (U : Finset ℕ) (hU : Bind.oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | Bind.readR own (Bind.extU U ρ) 0 ∈ alphaBad (d (Bind.extU U ρ))} : ℚ≥0) /
      Fintype.card (U → K) ≤ ((3 : ℕ) : ℚ≥0) / Fintype.card E := by
  have key := Bind.run_frac hinj (fun i j => hU (Bind.own_mem_oracleWords hown i j))
    (fun ρ => Bind.readR own ρ 0 ∈ alphaBad (d ρ)) 3 fun ρ => by
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card
        (t := ({r : Fin 1 → E | r 0 ∈ alphaBad (d ρ)} : Finset _)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, Bind.readR_oracleAt hinj,
          hR.committed_at hown hinj hk hd ρ] at hr ⊢
        exact hr
      · have hc : #({r : Fin 1 → E | r 0 ∈ alphaBad (d ρ)} : Finset _) ≤ #(alphaBad (d ρ)) :=
          card_le_card_of_injOn (fun r => r 0) (fun r hr => by simpa using hr)
            fun r _ r' _ he => funext fun i => by rw [Subsingleton.elim i 0]; exact he
        rw [pow_one]
        exact Nat.mul_le_mul_right _ (hc.trans (alphaBad_card _))
  convert key

/-! The pin's identity test. -/

/-- `Σ_t eq(x, t)` over the cube is one. -/
theorem sum_eqv_one {no : ℕ} (x : Fin no → E) : ∑ t ∈ range (2 ^ no), eqv x (bitPoint no t) = 1 := by
  rw [← sum_cube_bits no (fun b => eqv x b)]
  simp only [eqv, cube]
  rw [← Finset.prod_univ_sum (t := fun _ => ({0, 1} : Finset E))
    (f := fun i y => (1 - x i) * (1 - y) + x i * y)]
  refine prod_eq_one fun j _ => ?_
  rw [sum_pair zero_ne_one]
  ring

/-- A pin column `q` less one, as a multilinear polynomial in the outer point. -/
noncomputable def pinPoly (no : ℕ) (q : ℕ → E) : MvPolynomial (Fin no) E :=
  ∑ t ∈ range (2 ^ no), eqPoly no no t * C (q t - 1)

theorem eval_pinPoly {no : ℕ} (q : ℕ → E) (x : Fin no → E) :
    eval x (pinPoly no q) = ∑ t ∈ range (2 ^ no), eqv x (bitPoint no t) * q t - 1 := by
  simp only [pinPoly, map_sum, map_mul, eval_C, eval_eqPoly_eqv, mul_sub, mul_one, sum_sub_distrib, sum_eqv_one]

theorem totalDegree_pinPoly (no : ℕ) (q : ℕ → E) : (pinPoly no q).totalDegree ≤ no := by
  refine totalDegree_finsetSum_le fun z _ => (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  refine (totalDegree_finsetProd _ _).trans ?_
  have : ∀ j : Fin no, (if (j : ℕ) < no then (if z.testBit j then X j else 1 + X j) else 1 :
      MvPolynomial (Fin no) E).totalDegree ≤ 1 := by
    intro j
    split
    · split
      · rw [totalDegree_X]
      · exact (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; norm_num) (by rw [totalDegree_X]))
    · rw [totalDegree_one]; norm_num
  calc ∑ j : Fin no, _ ≤ ∑ _j : Fin no, 1 := Finset.sum_le_sum fun j _ => this j
    _ = no := by simp

/-- The pin test's draw event: the pin column is not one on every row, yet its fold at the outer point is one. -/
noncomputable def pinBad (no : ℕ) (q : ℕ → E) : Finset (Fin no → E) :=
  {x | (∃ t < 2 ^ no, q t ≠ 1) ∧ ∑ t ∈ range (2 ^ no), eqv x (bitPoint no t) * q t = 1}

/-- Schwartz-Zippel: at most `no/|E|` of the outer points. -/
theorem pinBad_card (no : ℕ) (q : ℕ → E) : #(pinBad no q) * Fintype.card E ≤ no * Fintype.card E ^ no := by
  by_cases hq : ∃ t < 2 ^ no, q t ≠ 1
  swap
  · have : pinBad no q = ∅ := by
      ext x
      simp only [pinBad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hq h.1
    rw [this, card_empty, zero_mul]
    exact Nat.zero_le _
  obtain ⟨t0, ht0, hne⟩ := hq
  have hp : pinPoly no q ≠ 0 := by
    intro h0
    have e := eval_pinPoly (no := no) q (bitPoint no t0)
    rw [h0, map_zero] at e
    have hs : ∑ t ∈ range (2 ^ no), eqv (bitPoint no t0) (bitPoint no t) * q t = q t0 := by
      rw [sum_eq_single t0 (fun t ht htne => ?_) (fun h => absurd (mem_range.mpr ht0) h)]
      · rw [← eval_eqPoly_eqv, eval_eqPoly le_rfl ht0 ht0, if_pos rfl, one_mul]
      · rw [← eval_eqPoly_eqv, eval_eqPoly le_rfl (mem_range.mp ht) ht0, if_neg htne, zero_mul]
    rw [hs] at e
    exact hne (sub_eq_zero.mp e.symm)
  have sz := schwartz_zippel_totalDegree hp (univ : Finset E)
  rw [Fintype.piFinset_univ, card_univ] at sz
  have hsub : pinBad no q ⊆ ({x | eval x (pinPoly no q) = 0} : Finset (Fin no → E)) := fun x hx => by
    simp only [pinBad, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [eval_pinPoly, hx.2, sub_self]
  have hE : (0 : ℚ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hE] at sz
  have hdeg : ((pinPoly no q).totalDegree : ℚ≥0) ≤ no := by exact_mod_cast totalDegree_pinPoly no q
  have hc : (#(pinBad no q) : ℚ≥0) ≤ #({x | eval x (pinPoly no q) = 0} : Finset (Fin no → E)) := by
    exact_mod_cast card_le_card hsub
  have : (#(pinBad no q) : ℚ≥0) * Fintype.card E ≤ no * Fintype.card E ^ no :=
    (mul_le_mul_of_nonneg_right hc (by positivity)).trans (sz.trans (by gcongr))
  exact_mod_cast this

/-- Off the event, the pin's fold being one makes the pin one on every row. -/
theorem pin_rows {no : ℕ} {q : ℕ → E} {x : Fin no → E} (hx : x ∉ pinBad no q)
    (h : ∑ t ∈ range (2 ^ no), eqv x (bitPoint no t) * q t = 1) : ∀ t < 2 ^ no, q t = 1 := by
  by_contra hne
  push Not at hne
  exact hx (by simp only [pinBad, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hne, h⟩)

open Classical in
/-- The outer point as a run's challenges drawn after time `k`: where the pin column is committed before `k`, the
oracles at which the point is in the pin test's event are at most `no/|E|` of them. -/
theorem pinRun_frac {c : Bind.Cert} {s : State} {T : ℕ} {C : (ℕ → K) → Prop} {st : (ℕ → K) → ℕ → Fin 4 → K}
    {val : (ℕ → K) → Val} (hR : Bind.Run c s T C st val) {no : ℕ} {own : Fin no → Fin 3 → ℕ} {time : Fin no → ℕ}
    (hown : Bind.OwnAt s (c.transcripts.getD T default) own time) (hinj : Bind.OwnInj own) {k : ℕ}
    (hk : ∀ i, k ≤ time i) (q : (ℕ → K) → ℕ → E)
    (hq : Bind.CommittedBefore s (c.transcripts.getD T default) val k q)
    (U : Finset ℕ) (hU : Bind.oracleWords s (c.transcripts.getD T default) ⊆ U) :
    (#{ρ : U → K | Bind.readR own (Bind.extU U ρ) ∈ pinBad no (q (Bind.extU U ρ))} : ℚ≥0) /
      Fintype.card (U → K) ≤ (no : ℚ≥0) / Fintype.card E := by
  have key := Bind.run_frac hinj (fun i j => hU (Bind.own_mem_oracleWords hown i j))
    (fun ρ => Bind.readR own ρ ∈ pinBad no (q ρ)) no fun ρ => by
      refine le_trans (Nat.mul_le_mul_right _ (card_le_card
        (t := ({r : Fin no → E | r ∈ pinBad no (q ρ)} : Finset _)) fun r hr => ?_)) ?_
      · simp only [mem_filter, mem_univ, true_and, Bind.readR_oracleAt hinj,
          hR.committed_at hown hinj hk hq ρ] at hr ⊢
        exact hr
      · have he : ({r : Fin no → E | r ∈ pinBad no (q ρ)} : Finset _) = pinBad no (q ρ) := by
          ext r
          simp
        rw [he]
        exact pinBad_card no (q ρ)
  convert key

/-! The slices as the committed region's extension. -/

/-- The witness folded at the outer point `x_outer`: `Z_i(J) = Σ_t eq(x_outer, t) Q_i(J, t)`, `Q_i(J, t)` slice `i` of
inner word `J` of row `t`. -/
noncomputable def outerFold (no : ℕ) (xo : Fin no → E) (Q : ℕ → ℕ → ℕ → E) (i J : ℕ) : E :=
  ∑ t ∈ range (2 ^ no), eqv xo (bitPoint no t) * Q i J t

/-- The pin's folded value is the pin column's fold at the outer point. -/
theorem pinV_outerFold (M : Mats) (no : ℕ) (xo : Fin no → E) (Q : ℕ → ℕ → ℕ → E) :
    pinV M (outerFold no xo Q) = ∑ t ∈ range (2 ^ no), eqv xo (bitPoint no t) * Q (M.pin % 64) (M.pin / 64) t :=
  rfl

theorem bitPoint_append {no : ℕ} {j : ℕ} (hj : j < 2 ^ h) (c : ℕ) :
    bitPoint (h + no) (2 ^ h * c + j) = Fin.append (bitPoint h j) (bitPoint no c) := by
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · rw [Fin.append_left]
    simp only [bitPoint, Fin.val_castAdd, Nat.testBit_two_pow_mul_add c hj, k.isLt, if_true]
  · rw [Fin.append_right]
    simp only [bitPoint, Fin.val_natAdd, Nat.testBit_two_pow_mul_add c hj, Nat.add_sub_cancel_left]
    simp

theorem eqv_append {no : ℕ} (p a : Fin h → E) (q b : Fin no → E) :
    eqv (Fin.append p q) (Fin.append a b) = eqv p a * eqv q b := by
  simp only [eqv, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- Slice `i`'s claim `MLE(Z_i)(R)` is the committed slice's extension at `R ++ x_outer`, its words indexed `J + 2^h t`:
the `SliceClaim` the ring switch opens. -/
theorem slice_mle {no : ℕ} (R : Fin h → E) (xo : Fin no → E) (Q : ℕ → ℕ → ℕ → E) (i : ℕ) :
    mleAt (h + no) (Fin.append R xo) (fun z => Q i (z % 2 ^ h) (z / 2 ^ h)) = mleAt h R (outerFold no xo Q i) := by
  simp only [mleAt, outerFold, mul_sum]
  rw [pow_add, mul_comm, sum_range_mul _ (2 ^ h) (2 ^ no), sum_comm]
  refine sum_congr rfl fun j hj => sum_congr rfl fun t _ => ?_
  have hj' := mem_range.mp hj
  have hp : 0 < 2 ^ h := by positivity
  have e1 : (2 ^ h * t + j) % 2 ^ h = j := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  have e2 : (2 ^ h * t + j) / 2 ^ h = t := by rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hj', add_zero]
  rw [bitPoint_append hj' t, eqv_append, e1, e2]
  ring

end LeanVMCircuits.Rec.FlockLin

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model AirLink FlockLin Finset

/-- The HASH circuit's constant wire's column: the first after its 18 port words (`CircuitId::shape`,
`const_pin_col = 64 * n_ports`). -/
def hashPin : ℕ := 64 * 18

/-- `eq_bits` from `acc`: per step `(bit, z, call)`, a `mul(acc, z)` for a one bit and a `mul_add(acc, z, acc)`
(`times_one_plus`) for a zero. -/
def bitsCalls (os : Array (List ℕ)) (acc : ℕ) : List (Bool × ℕ × ℕ) → List (ℕ × Call)
  | (b, z, j) :: ts => (j, if b then .mul acc z else .mulAdd acc z acc) :: bitsCalls os (o os j) ts
  | [] => []

/-- The chain's output. -/
def bitsOut (os : Array (List ℕ)) (acc : ℕ) : List (Bool × ℕ × ℕ) → ℕ
  | (_, _, j) :: ts => bitsOut os (o os j) ts
  | [] => acc

/-- `eq_eval` from `acc`: per step `(x, y, addCall, mulCall)`, an `add(x, y)` and a `mul_add(acc, x + y, acc)`. -/
def eqeCalls (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → List (ℕ × Call)
  | (x, y, ja, jm) :: ts => (ja, .add x y) :: (jm, .mulAdd acc (o os ja) acc) :: eqeCalls os (o os jm) ts
  | [] => []

/-- The chain's output. -/
def eqeOut (os : Array (List ℕ)) (acc : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → ℕ
  | (_, _, _, jm) :: ts => eqeOut os (o os jm) ts
  | [] => acc

/-- A sumcheck's rounds' challenges' values. -/
noncomputable def roundV (val : Val) (sc : SumcheckCert) : Fin sc.rounds.length → E :=
  fun j => Model.ev val (sc.rounds.getD j default).chal

/-- The HASH lincheck as `verify_deferred` makes it for a one-circuit batch: its certified sumcheck `sc`; `α`; the
zerocheck's triple `a`, `b`, `c`; the input claim's calls (a `one` and a `zero`, `mul(α, α)` at `sqAt`,
`mul(α^2, α)` at `betaAt`, `mul_add(α, b, a)`, `mul_add(α^2, c, ·)`, `add(·, α^3)` and the batch's
`mul_add(one, ·, zero)`); the inner point `xin` (wire `k` its `x_k`); the 64 slices and the form value; the pin's
column, its `eq_bits` calls (top variable first) and the `mul(s_pin, eq)` and `mul_add(α^3, ·, value)` calls; the
Lagrange sum's `scale`, inverses and `mul_add(s_i, inv_i, acc)` calls and its `mul(scale, ·)`; `eq_eval`'s `add` and
`mul_add` calls; the `C` term's `mul(eq, ·)`, the terminal's `mul_add(α^2, ·, own)` and the batch's
`mul_add(one, ·, zero)`. -/
structure LinCert where
  sc : ℕ
  alpha : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  oneAt : ℕ
  zeroAt : ℕ
  sqAt : ℕ
  betaAt : ℕ
  in1At : ℕ
  in2At : ℕ
  in3At : ℕ
  batchAt : ℕ
  xin : List ℕ := []
  slices : List ℕ := []
  value : ℕ
  pin : ℕ
  pinAt : List ℕ := []
  pinTermAt : ℕ
  ownAt : ℕ
  scale : ℕ
  invs : List ℕ := []
  lagAt : List ℕ := []
  lagSumAt : ℕ
  eqAddAt : List ℕ := []
  eqMulAt : List ℕ := []
  ctermAt : ℕ
  finAt : ℕ
  totAt : ℕ
  deriving Inhabited, Repr

namespace LinCert

variable (os : Array (List ℕ)) (lc : LinCert)

def one : ℕ := o os lc.oneAt
def zero : ℕ := o os lc.zeroAt
def sq : ℕ := o os lc.sqAt
def beta : ℕ := o os lc.betaAt

/-- Round `k`'s challenge. -/
def chal (sc : SumcheckCert) (k : ℕ) : ℕ := (sc.rounds.getD k default).chal

/-- `eq_bits(pin / 64, R)`'s steps: step `k` reads `R_(n-1-k)`, round `k`'s challenge, by the pin's bit `n - 1 - k`. -/
def pinSteps (sc : SumcheckCert) : List (Bool × ℕ × ℕ) :=
  (List.range sc.rounds.length).map fun k =>
    ((lc.pin / 64).testBit (sc.rounds.length - 1 - k), chal sc k, lc.pinAt.getD k 0)

/-- `eq_eval(x_inner, R)`'s steps: step `k` reads `x_k` and `R_k`, round `n - 1 - k`'s challenge. -/
def eqSteps (sc : SumcheckCert) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range sc.rounds.length).map fun k =>
    (lc.xin.getD k 0, chal sc (sc.rounds.length - 1 - k), lc.eqAddAt.getD k 0, lc.eqMulAt.getD k 0)

/-- The Lagrange sum's steps: slice `i` times inverse `i`. -/
def lagSteps : List (ℕ × ℕ × ℕ) :=
  (List.range 64).map fun i => (lc.slices.getD i 0, lc.invs.getD i 0, lc.lagAt.getD i 0)

def eqPin (sc : SumcheckCert) : ℕ := bitsOut os (lc.one os) (lc.pinSteps sc)
def eqIn (sc : SumcheckCert) : ℕ := eqeOut os (lc.one os) (lc.eqSteps sc)
def lagSum : ℕ := residOut os (lc.zero os) lc.lagSteps

/-- The input claim's and the terminal's calls. -/
def headCalls (sc : SumcheckCert) : List (ℕ × Call) :=
  [(lc.oneAt, .one), (lc.zeroAt, .zero), (lc.sqAt, .mul lc.alpha lc.alpha), (lc.betaAt, .mul (lc.sq os) lc.alpha),
    (lc.in1At, .mulAdd lc.alpha lc.b lc.a), (lc.in2At, .mulAdd (lc.sq os) lc.c (o os lc.in1At)),
    (lc.in3At, .add (o os lc.in2At) (lc.beta os)), (lc.batchAt, .mulAdd (lc.one os) (o os lc.in3At) (lc.zero os)),
    (lc.pinTermAt, .mul (lc.slices.getD (lc.pin % 64) 0) (lc.eqPin os sc)),
    (lc.ownAt, .mulAdd (lc.beta os) (o os lc.pinTermAt) lc.value), (lc.lagSumAt, .mul lc.scale (lc.lagSum os)),
    (lc.ctermAt, .mul (lc.eqIn os sc) (o os lc.lagSumAt)),
    (lc.finAt, .mulAdd (lc.sq os) (o os lc.ctermAt) (o os lc.ownAt)),
    (lc.totAt, .mulAdd (lc.one os) (o os lc.finAt) (lc.zero os))]

/-- Every named call. -/
def calls (sc : SumcheckCert) : List (ℕ × Call) :=
  lc.headCalls os sc ++ bitsCalls os (lc.one os) (lc.pinSteps sc) ++ residCalls os (lc.zero os) lc.lagSteps ++
    eqeCalls os (lc.one os) (lc.eqSteps sc)

/-- The sumcheck's shape: no residual, degree two, no eq weight in any round; one inner coordinate, `eq_bits` step
and `eq_eval` step per round, 64 slices, inverses and Lagrange steps; the HASH circuit's pin, its inner word on the
cube; the input claim the batch's output and the test's other side the terminal's. -/
def shapeOk (sc : SumcheckCert) : Bool :=
  sc.resid.isEmpty && sc.deg == 2 && sc.rounds.all (·.weight.isNone) && lc.xin.length == sc.rounds.length &&
    lc.pinAt.length == sc.rounds.length && lc.eqAddAt.length == sc.rounds.length &&
    lc.eqMulAt.length == sc.rounds.length && lc.slices.length == 64 && lc.invs.length == 64 &&
    lc.lagAt.length == 64 && lc.pin == hashPin && decide (lc.pin / 64 < 2 ^ sc.rounds.length) &&
    o os lc.batchAt == sc.claim0 && sc.final == o os lc.totAt

/-- The check: the named sumcheck's shape and every named call in the replay. -/
def okIn (scs : Array SumcheckCert) (cs : Array Call) (rl : Array Bool) : Bool :=
  match scs[lc.sc]? with
  | some sc => lc.shapeOk os sc && callsOk cs rl (lc.calls os sc)
  | none => false

/-- `LinCert`'s check on a certificate. -/
def ok (c : Cert) : Bool := lc.okIn os c.sumchecks c.calls c.relax

/-- The link to the zerocheck: the named triple is the zerocheck's terminal triple `tri`, and the inner point is the
zerocheck's first round challenges (`x_inner = chi[0..h]`, `zc.mlv_challenges[..rest]`). -/
def zeroLink (zsc : SumcheckCert) (tri : ℕ × ℕ × ℕ) : Bool :=
  (lc.a, lc.b, lc.c) == tri && lc.xin == (zsc.rounds.map (·.chal)).take lc.xin.length

/-- The named inner point's values. -/
noncomputable def xinV (val : Val) (n : ℕ) : Fin n → E := fun j => Model.ev val (lc.xin.getD j 0)

/-- Slice `i`'s claimed value. -/
noncomputable def sliceV (val : Val) (i : ℕ) : E := Model.ev val (lc.slices.getD i 0)

/-- The Lagrange sum's value: `scale · Σ_i s_i inv_i`. -/
noncomputable def lagV (val : Val) : E :=
  Model.ev val lc.scale * ∑ i ∈ range 64, Model.ev val (lc.slices.getD i 0) * Model.ev val (lc.invs.getD i 0)

/-- The deferred matrix claim (`MatrixClaim`, `tree/reduce/matrix.rs`): the prover's form value is the matrices' form
`u^T (A_0 + α B_0) w` at the circuit's matrices `M`, the Lagrange weights `lz`, the inner point `xin`, `α`, `R` and the
claimed slices. The tree's matrix reduction must discharge it. -/
def MatrixHolds (val : Val) (sc : SumcheckCert) (M : Mats) (lz : ℕ → E) (xin : Fin sc.rounds.length → E) : Prop :=
  Model.ev val lc.value = formVal M lz xin (Model.ev val lc.alpha) (chi (roundV val sc))
    fun i => Model.ev val (lc.slices.getD i 0)

end LinCert

/-! What the calls give. -/

section Sem

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

theorem bits_sem (hF : Facts cs rl os st val) : ∀ (acc : ℕ) (ts : List (Bool × ℕ × ℕ)),
    callsOk cs rl (bitsCalls os acc ts) = true →
      Model.ev val (bitsOut os acc ts) =
        Model.ev val acc * (ts.map fun t => if t.1 then Model.ev val t.2.1 else 1 + Model.ev val t.2.1).prod
  | acc, [], _ => by simp [bitsOut]
  | acc, (b, z, j) :: ts, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    have hj := holds_of_mem hF h1 (List.mem_singleton_self _)
    rw [bitsOut, bits_sem hF (o os j) ts h2, List.map_cons, List.prod_cons]
    cases b
    · have e : Model.ev val (o os j) = Model.ev val acc * Model.ev val z + Model.ev val acc := hj
      simp only [e, Bool.false_eq_true, if_false]
      ring
    · have e : Model.ev val (o os j) = Model.ev val acc * Model.ev val z := hj
      simp only [e, if_true]
      ring

theorem eqe_sem (hF : Facts cs rl os st val) : ∀ (acc : ℕ) (ts : List (ℕ × ℕ × ℕ × ℕ)),
    callsOk cs rl (eqeCalls os acc ts) = true →
      Model.ev val (eqeOut os acc ts) =
        Model.ev val acc * (ts.map fun t => 1 + Model.ev val t.1 + Model.ev val t.2.1).prod
  | acc, [], _ => by simp [eqeOut]
  | acc, (x, y, ja, jm) :: ts, h => by
    obtain ⟨h1, h2⟩ := callsOk_cons h
    obtain ⟨h3, h4⟩ := callsOk_cons h2
    have ea : Model.ev val (o os ja) = Model.ev val x + Model.ev val y := holds_of_mem hF h1 (List.mem_singleton_self _)
    have em : Model.ev val (o os jm) = Model.ev val acc * Model.ev val (o os ja) + Model.ev val acc :=
      holds_of_mem hF h3 (List.mem_singleton_self _)
    rw [eqeOut, eqe_sem hF (o os jm) ts h4, List.map_cons, List.prod_cons, em, ea]
    ring

theorem listProd_range (f : ℕ → E) : ∀ n, ((List.range n).map f).prod = ∏ k ∈ range n, f k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, listProd_range f n, Finset.prod_range_succ]
    simp

theorem listSum_range (f : ℕ → E) : ∀ n, ((List.range n).map f).sum = ∑ k ∈ range n, f k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, listSum_range f n, Finset.sum_range_succ]
    simp

/-- A passing `LinCert`'s shape. -/
theorem LinCert.shape {lc : LinCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : lc.okIn os scs cs rl = true) (hsc : scs[lc.sc]? = some sc) :
    sc.resid = [] ∧ sc.deg = 2 ∧ (∀ i, (sc.rounds.getD i default).weight = none) ∧ lc.pin = hashPin ∧
      lc.pin / 64 < 2 ^ sc.rounds.length ∧ o os lc.batchAt = sc.claim0 ∧ sc.final = o os lc.totAt ∧
      callsOk cs rl (lc.calls os sc) = true := by
  unfold LinCert.okIn at h
  rw [hsc] at h
  simp only [LinCert.shapeOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_iff, List.all_eq_true,
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, hdeg⟩, hw⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hpin⟩, hlt⟩, hcl⟩, hfin⟩, hcalls⟩ := h
  refine ⟨hres, hdeg, fun i => ?_, hpin, hlt, hcl, hfin, hcalls⟩
  by_cases hi : i < sc.rounds.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

/-- What a passing `LinCert` gives where the calls hold: the input claim is `a + α b + α^2 c + α^3`, and the test's
other side is the form value plus the pin's term `α^3 s_pin eq(pin / 64, R)` and the `C` term
`α^2 eq(x_inner, R) · scale · Σ_i s_i inv_i`, `R = chi r`. -/
theorem LinCert.sem (hF : Facts cs rl os st val) {lc : LinCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : lc.okIn os scs cs rl = true) (hsc : scs[lc.sc]? = some sc) :
    Model.ev val sc.claim0 = Model.ev val lc.a + Model.ev val lc.alpha * Model.ev val lc.b +
      Model.ev val lc.alpha ^ 2 * Model.ev val lc.c + Model.ev val lc.alpha ^ 3 ∧
    Model.ev val sc.final = Model.ev val lc.value +
      Model.ev val lc.alpha ^ 3 * (lc.sliceV val (lc.pin % 64) * eqBits (lc.pin / 64) (chi (roundV val sc))) +
      Model.ev val lc.alpha ^ 2 * (eqAdd (lc.xinV val sc.rounds.length) (chi (roundV val sc)) * lc.lagV val) := by
  obtain ⟨-, -, -, -, -, hcl, hfin, hcalls⟩ := LinCert.shape h hsc
  simp only [LinCert.calls, callsOk_append, Bool.and_eq_true] at hcalls
  obtain ⟨⟨⟨hhead, hbits⟩, hlag⟩, heqe⟩ := hcalls
  have H : ∀ x ∈ lc.headCalls os sc, x.2.Holds st val (os.getD x.1 []) := fun x hx => holds_of_mem hF hhead hx
  simp only [LinCert.headCalls, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at H
  obtain ⟨hone, hzero, hsq, hbeta, hin1, hin2, hin3, hbatch, hpt, hown, hls, hct, hfn, htot⟩ := H
  have hone' : Model.ev val (lc.one os) = 1 := hone
  have hzero' : Model.ev val (lc.zero os) = 0 := hzero
  have hsq' : Model.ev val (lc.sq os) = Model.ev val lc.alpha * Model.ev val lc.alpha := hsq
  have hbeta' : Model.ev val (lc.beta os) = Model.ev val (lc.sq os) * Model.ev val lc.alpha := hbeta
  have hin1' : Model.ev val (o os lc.in1At) = Model.ev val lc.alpha * Model.ev val lc.b + Model.ev val lc.a := hin1
  have hin2' : Model.ev val (o os lc.in2At) =
      Model.ev val (lc.sq os) * Model.ev val lc.c + Model.ev val (o os lc.in1At) := hin2
  have hin3' : Model.ev val (o os lc.in3At) = Model.ev val (o os lc.in2At) + Model.ev val (lc.beta os) := hin3
  have hbatch' : Model.ev val (o os lc.batchAt) =
      Model.ev val (lc.one os) * Model.ev val (o os lc.in3At) + Model.ev val (lc.zero os) := hbatch
  have hpt' : Model.ev val (o os lc.pinTermAt) =
      Model.ev val (lc.slices.getD (lc.pin % 64) 0) * Model.ev val (lc.eqPin os sc) := hpt
  have hown' : Model.ev val (o os lc.ownAt) =
      Model.ev val (lc.beta os) * Model.ev val (o os lc.pinTermAt) + Model.ev val lc.value := hown
  have hls' : Model.ev val (o os lc.lagSumAt) = Model.ev val lc.scale * Model.ev val (lc.lagSum os) := hls
  have hct' : Model.ev val (o os lc.ctermAt) = Model.ev val (lc.eqIn os sc) * Model.ev val (o os lc.lagSumAt) := hct
  have hfn' : Model.ev val (o os lc.finAt) =
      Model.ev val (lc.sq os) * Model.ev val (o os lc.ctermAt) + Model.ev val (o os lc.ownAt) := hfn
  have htot' : Model.ev val (o os lc.totAt) =
      Model.ev val (lc.one os) * Model.ev val (o os lc.finAt) + Model.ev val (lc.zero os) := htot
  -- The three chains.
  have hpin : Model.ev val (lc.eqPin os sc) = eqBits (lc.pin / 64) (chi (roundV val sc)) := by
    rw [LinCert.eqPin, bits_sem hF _ _ hbits, hone', one_mul, LinCert.pinSteps, List.map_map, listProd_range,
      ← Fin.prod_univ_eq_prod_range, eqBits]
    refine Fintype.prod_equiv Fin.revPerm _ _ fun k => ?_
    have hk : sc.rounds.length - 1 - (k : ℕ) = sc.rounds.length - ((k : ℕ) + 1) := by omega
    simp only [Function.comp_apply, Fin.revPerm_apply, chi, Fin.rev_rev, roundV, LinCert.chal, Fin.val_rev, hk]
  have heq : Model.ev val (lc.eqIn os sc) = eqAdd (lc.xinV val sc.rounds.length) (chi (roundV val sc)) := by
    rw [LinCert.eqIn, eqe_sem hF _ _ heqe, hone', one_mul, LinCert.eqSteps, List.map_map, listProd_range,
      ← Fin.prod_univ_eq_prod_range, eqAdd]
    refine Fintype.prod_congr _ _ fun k => ?_
    have hk : sc.rounds.length - 1 - (k : ℕ) = sc.rounds.length - ((k : ℕ) + 1) := by omega
    simp only [Function.comp_apply, chi, roundV, LinCert.chal, LinCert.xinV, Fin.val_rev, hk]
  have hlagv : Model.ev val (lc.lagSum os) =
      ∑ i ∈ range 64, Model.ev val (lc.slices.getD i 0) * Model.ev val (lc.invs.getD i 0) := by
    rw [LinCert.lagSum, resid_sem hF _ _ hlag, hzero', zero_add, LinCert.lagSteps, List.map_map, listSum_range]
    rfl
  refine ⟨?_, ?_⟩
  · rw [← hcl, hbatch', hone', hzero', hin3', hin2', hin1', hbeta', hsq']
    ring
  · rw [hfin, htot', hone', hzero', hfn', hown', hct', hls', hpt', hpin, heq, hlagv, hbeta', hsq', LinCert.lagV,
      LinCert.sliceV]
    ring

end Sem

section Main

variable {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

/-- The terminal is the honest instance's final value (`FlockLin.linInst_final`) where the named slices are the
folded witness's extensions at `R = chi r`, the deferred matrix claim holds, the Lagrange weights are the named
`scale · inv_i` and the named inner point is `xin`. -/
theorem LinCert.final_eq (hF : Facts cs rl os st val) {lc : LinCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : lc.okIn os scs cs rl = true) (hsc : scs[lc.sc]? = some sc) (M : Mats) (lz : ℕ → E)
    (xin : Fin sc.rounds.length → E) (Zv : ℕ → ℕ → E) (hpin : M.pin = lc.pin)
    (hlz : ∀ i < 64, Model.ev val lc.scale * Model.ev val (lc.invs.getD i 0) = lz i)
    (hx : ∀ k : Fin sc.rounds.length, Model.ev val (lc.xin.getD k 0) = xin k)
    (hs : ∀ i < 64, Model.ev val (lc.slices.getD i 0) = mleAt sc.rounds.length (chi (roundV val sc)) (Zv i))
    (hmat : lc.MatrixHolds val sc M lz xin) :
    Model.ev val sc.final = (linInst sc.rounds.length M lz xin Zv (Model.ev val lc.alpha)).final (roundV val sc) := by
  have hsem := (LinCert.sem hF h hsc).2
  have hxv : lc.xinV val sc.rounds.length = xin := funext hx
  rw [hxv] at hsem
  rw [hsem, linInst_final, hpin]
  have hv := hmat
  rw [LinCert.MatrixHolds, formVal_eq] at hv
  have hl : lc.pin % 64 < 64 := Nat.mod_lt _ (by norm_num)
  set R := chi (roundV val sc)
  set α := Model.ev val lc.alpha
  simp only [add_mul, sum_add_distrib]
  have e1 : ∑ i ∈ range 64, mleAt sc.rounds.length R (marg M lz xin α i) * mleAt sc.rounds.length R (Zv i) =
      Model.ev val lc.value := by
    rw [hv]
    exact sum_congr rfl fun i hi => by rw [hs i (mem_range.mp hi)]
  have e2 : ∑ i ∈ range 64, α ^ 2 * lz i * eqAdd xin R * mleAt sc.rounds.length R (Zv i) =
      α ^ 2 * (eqAdd xin R * lc.lagV val) := by
    rw [LinCert.lagV, mul_sum, mul_sum, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [← hlz i (mem_range.mp hi), hs i (mem_range.mp hi)]
    ring
  have e3 : ∑ i ∈ range 64, α ^ 3 * (if i = lc.pin % 64 then 1 else 0) * eqBits (lc.pin / 64) R *
      mleAt sc.rounds.length R (Zv i) = α ^ 3 * (lc.sliceV val (lc.pin % 64) * eqBits (lc.pin / 64) R) := by
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, sum_ite_eq', mem_range, hl, if_true]
    rw [LinCert.sliceV, hs _ hl]
    ring
  rw [e1, e2, e3]
  ring

/-- The rounds read no eq weight, as the honest instance `linInst` has none: `SumcheckAnswers`' eq-weight field. -/
theorem LinCert.answers_weight {lc : LinCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : lc.okIn os scs cs rl = true) (hsc : scs[lc.sc]? = some sc) (M : Mats) (lz : ℕ → E)
    (xin : Fin sc.rounds.length → E) (Zv : ℕ → ℕ → E) (α : E) (f : ℕ → E) (r : Fin sc.rounds.length → E)
    (i : Fin sc.rounds.length) :
    (sc.rounds.getD i default).weight.map f = (linInst sc.rounds.length M lz xin Zv α).weight r i := by
  rw [(LinCert.shape h hsc).2.2.1 i, linInst_weight]
  rfl

/-- The lincheck as a check of `RecParts`: where the calls hold and `LinCert.okIn` passes, the named slices are the
folded witness's extensions at `chi r`, the deferred matrix claim holds (`LinCert.MatrixHolds`), the Lagrange weights
are the named `scale · inv_i` and the inner point the named one, its input claim is its honest instance `linInst`'s sum
off its event `sumcheckFalse`. -/
theorem lin_part {c : Cert} {s : State} {val : (ℕ → K) → Val} {lc : LinCert} {sc : SumcheckCert} {T' : ℕ → E}
    (ρ : ℕ → K) (hF : Facts cs rl os st (val ρ)) (h : lc.okIn os c.sumchecks cs rl = true)
    (hsc : c.sumchecks[lc.sc]? = some sc) (M : Mats) (lz : ℕ → E) (xin : Fin sc.rounds.length → E)
    (Zv : ℕ → ℕ → E) (hpin : M.pin = lc.pin)
    (hlz : ∀ i < 64, Model.ev (val ρ) lc.scale * Model.ev (val ρ) (lc.invs.getD i 0) = lz i)
    (hx : ∀ k : Fin sc.rounds.length, Model.ev (val ρ) (lc.xin.getD k 0) = xin k)
    (hchal : ∀ j : Fin sc.rounds.length,
      Model.ev (val ρ) (sc.rounds.getD j default).chal = readR (chalWords c.outs sc.chals) ρ j)
    (htest : ∀ a b, s.unions[sc.test]? = some (a, b) → val ρ a = val ρ b)
    (hhint : ∀ w ∈ sc.hints, Model.ev (val ρ) w = T' w)
    (hs : ∀ i < 64, Model.ev (val ρ) (lc.slices.getD i 0) = mleAt sc.rounds.length (chi (roundV (val ρ) sc)) (Zv i))
    (hmat : lc.MatrixHolds (val ρ) sc M lz xin)
    (hnot : ¬ sumcheckFalse c s sc (linInst sc.rounds.length M lz xin Zv (Model.ev (val ρ) lc.alpha)) T' val ρ) :
    Model.ev (val ρ) sc.claim0 = (linInst sc.rounds.length M lz xin Zv (Model.ev (val ρ) lc.alpha)).sum := by
  refine sumcheck_part ρ htest ⟨hhint, ?_⟩ hnot
  rw [(LinCert.shape h hsc).1, List.map_nil, List.sum_nil, add_zero,
    LinCert.final_eq hF h hsc M lz xin Zv hpin hlz hx hs hmat]
  congr 1
  funext j
  exact hchal j

/-- The lincheck's batching on the named certificate: its input claim being its honest instance's sum makes the named
triple the true one and the pin's folded value one, off `α`'s draw event at the difference (`FlockLin.alphaBad`,
at most three `α`). -/
theorem lin_triple (hF : Facts cs rl os st val) {lc : LinCert} {scs : Array SumcheckCert} {sc : SumcheckCert}
    (h : lc.okIn os scs cs rl = true) (hsc : scs[lc.sc]? = some sc) (M : Mats) (lz : ℕ → E)
    (xin : Fin sc.rounds.length → E) (Zv : ℕ → ℕ → E) (hpin : M.pin = lc.pin)
    (hin : Model.ev val sc.claim0 = (linInst sc.rounds.length M lz xin Zv (Model.ev val lc.alpha)).sum)
    (hα : Model.ev val lc.alpha ∉ alphaBad (diff ![Model.ev val lc.a, Model.ev val lc.b, Model.ev val lc.c]
      ![triA M lz xin Zv, triB M lz xin Zv, triC lz xin Zv] (pinV M Zv))) :
    Model.ev val lc.a = triA M lz xin Zv ∧ Model.ev val lc.b = triB M lz xin Zv ∧ Model.ev val lc.c = triC lz xin Zv ∧
      pinV M Zv = 1 := by
  obtain ⟨-, -, -, -, hlt, -⟩ := LinCert.shape h hsc
  rw [(LinCert.sem hF h hsc).1, linInst_sum_eq M lz xin Zv _ (hpin ▸ hlt)] at hin
  obtain ⟨ht, hp⟩ := claim_true hα (by simpa using hin)
  refine ⟨by simpa using congrFun ht 0, by simpa using congrFun ht 1, by simpa using congrFun ht 2, hp⟩

end Main

/-! Naming the lincheck in a replay. -/

/-- The HASH lincheck closing certified sumcheck `scIdx` (`verify_deferred`), named back from its test's other side
`sc.final`: the batch's `mul_add(one, ·, zero)` and the terminal's `mul_add(α^2, C term, own)`; from these `α`, the
pin's and the `C` term's products, the Lagrange sum back to its `zero`, `eq_eval` back to its `one` (step `k` reading
round `n - 1 - k`'s challenge), `eq_bits` back to its `one` by `hashPin`'s bits; and from the input claim the batch's
calls back to the triple. -/
def linOf (rp : Replay) (idx : Std.HashMap ℕ (Array (ℕ × ℕ))) (os : Array (List ℕ)) (scIdx : ℕ)
    (sc : SumcheckCert) : Option LinCert := Id.run do
  let callAt := fun (j : ℕ) => rp.calls.getD j .zero
  let makers := fun (w : ℕ) => ((idx.getD w #[]).filterMap fun (j, p) => if p == 0 then some j else none).toList
  let n := sc.rounds.length
  let chal := fun (k : ℕ) => (sc.rounds.getD k default).chal
  if !sc.resid.isEmpty || n == 0 then return none
  let some oneW := rp.state.units.eOne | return none
  let some zeroW := rp.state.units.eZero | return none
  let some oneAt := (makers oneW).find? fun j => callAt j == .one | return none
  let some zeroAt := (makers zeroW).find? fun j => callAt j == .zero | return none
  if o os oneAt != oneW || o os zeroAt != zeroW then return none
  let fin := sc.final
  let some totAt := (makers fin).find? fun j => callAt j == .mulAdd oneW fin zeroW | return none
  let some (finAt, sq, ct, own) := ((makers fin).findSome? fun j => match callAt j with
    | .mulAdd x y z => if x == oneW then none else some (j, x, y, z)
    | _ => none) | return none
  let some (sqAt, alpha) := ((makers sq).findSome? fun j => match callAt j with
    | .mul x y => if x == y then some (j, x) else none
    | _ => none) | return none
  let some (ownAt, beta, pt, value) := ((makers own).findSome? fun j => match callAt j with
    | .mulAdd x y z => some (j, x, y, z)
    | _ => none) | return none
  let some betaAt := (makers beta).find? fun j => callAt j == .mul sq alpha | return none
  let some (pinTermAt, sPin, eqPin) := ((makers pt).findSome? fun j => match callAt j with
    | .mul x y => some (j, x, y)
    | _ => none) | return none
  let some (ctermAt, eqOut, lagS) := ((makers ct).findSome? fun j => match callAt j with
    | .mul x y => some (j, x, y)
    | _ => none) | return none
  let some (lagSumAt, scale, sumW) := ((makers lagS).findSome? fun j => match callAt j with
    | .mul x y => some (j, x, y)
    | _ => none) | return none
  -- The Lagrange sum, back to its `zero`.
  let mut cur := sumW
  let mut lag : List (ℕ × ℕ × ℕ) := []
  for _ in [0:64] do
    let some (j, sv, hv, acc) := ((makers cur).findSome? fun j => match callAt j with
      | .mulAdd x y z => some (j, x, y, z)
      | _ => none) | return none
    lag := (sv, hv, j) :: lag
    cur := acc
  if cur != zeroW then return none
  -- `eq_eval`, back to its `one`.
  cur := eqOut
  let mut eqs : List (ℕ × ℕ × ℕ) := []
  for k in (List.range n).reverse do
    let y := chal (n - 1 - k)
    let some (jm, ja, x, acc) := ((makers cur).findSome? fun j => match callAt j with
      | .mulAdd acc sw acc' => if acc != acc' then none else
        (makers sw).findSome? fun ja => match callAt ja with
          | .add x y' => if y' == y then some (j, ja, x, acc) else none
          | _ => none
      | _ => none) | return none
    eqs := (x, ja, jm) :: eqs
    cur := acc
  if cur != oneW then return none
  -- `eq_bits`, back to its `one`.
  cur := eqPin
  let mut pinAt : List ℕ := []
  for k in (List.range n).reverse do
    let z := chal k
    let bit := (hashPin / 64).testBit (n - 1 - k)
    let some (j, acc) := ((makers cur).findSome? fun j => match callAt j with
      | .mul acc z' => if bit && z' == z then some (j, acc) else none
      | .mulAdd acc z' acc' => if !bit && z' == z && acc == acc' then some (j, acc) else none
      | _ => none) | return none
    pinAt := j :: pinAt
    cur := acc
  if cur != oneW then return none
  let slices := lag.map (·.1)
  if slices.getD (hashPin % 64) 0 != sPin then return none
  -- The input claim, back to the triple.
  let claim0 := sc.claim0
  let some batchAt := (makers claim0).find? fun j => callAt j == .mulAdd oneW claim0 zeroW | return none
  let some (in3At, in2) := ((makers claim0).findSome? fun j => match callAt j with
    | .add x y => if y == beta then some (j, x) else none
    | _ => none) | return none
  let some (in2At, c, in1) := ((makers in2).findSome? fun j => match callAt j with
    | .mulAdd x y z => if x == sq then some (j, y, z) else none
    | _ => none) | return none
  let some (in1At, b, a) := ((makers in1).findSome? fun j => match callAt j with
    | .mulAdd x y z => if x == alpha then some (j, y, z) else none
    | _ => none) | return none
  return some {
    sc := scIdx, alpha := alpha, a := a, b := b, c := c, oneAt := oneAt, zeroAt := zeroAt, sqAt := sqAt,
    betaAt := betaAt, in1At := in1At, in2At := in2At, in3At := in3At, batchAt := batchAt, xin := eqs.map (·.1),
    slices := slices, value := value, pin := hashPin, pinAt := pinAt, pinTermAt := pinTermAt, ownAt := ownAt,
    scale := scale, invs := lag.map (·.2.1), lagAt := lag.map (·.2.2), lagSumAt := lagSumAt,
    eqAddAt := eqs.map (·.2.1), eqMulAt := eqs.map (·.2.2), ctermAt := ctermAt, finAt := finAt, totAt := totAt }

/-! Mutation tests of `LinCert.okIn`, on calls whose call `j` outputs wire `100 + j`: the certificate's own calls laid
out at its indices pass, and each rule rejects a call or a sumcheck that breaks it. -/

/-- Five rounds of challenges `900 + k`; `α` wire 50, the triple 51 to 53, the form value 54, the scale 55, the inner
point 60 to 64, the slices `300 + i` and the inverses `400 + i`. -/
def mutLin : LinCert where
  sc := 0
  alpha := 50
  a := 51
  b := 52
  c := 53
  oneAt := 0
  zeroAt := 1
  sqAt := 2
  betaAt := 3
  in1At := 4
  in2At := 5
  in3At := 6
  batchAt := 7
  pinTermAt := 8
  ownAt := 9
  lagSumAt := 10
  ctermAt := 11
  finAt := 12
  totAt := 13
  pinAt := (List.range 5).map (14 + ·)
  lagAt := (List.range 64).map (19 + ·)
  eqAddAt := (List.range 5).map (83 + 2 * ·)
  eqMulAt := (List.range 5).map (84 + 2 * ·)
  xin := (List.range 5).map (60 + ·)
  slices := (List.range 64).map (300 + ·)
  invs := (List.range 64).map (400 + ·)
  value := 54
  scale := 55
  pin := hashPin

def mutSc : SumcheckCert :=
  { claim0 := 107, rounds := (List.range 5).map fun k => { (default : RoundCert) with chal := 900 + k }, deg := 2,
    test := 0, final := 113, transcript := 0 }

/-- The certificate's calls at their indices. -/
def mutLinCalls : Array Call :=
  ((List.range 93).map fun j => ((mutLin.calls (mutOuts 93) mutSc).lookup j).getD .zero).toArray

example : mutLin.okIn (mutOuts 93) #[mutSc] mutLinCalls #[] = true := by decide +kernel

/-- `eq_bits` follows the pin's bits: step 0 reads bit 4 of `18`, a one, as `mul(one, r_0)`; `times_one_plus` fails. -/
example : mutLinCalls.getD 14 .zero = .mul 100 900 ∧
    mutLin.okIn (mutOuts 93) #[mutSc] (mutLinCalls.set! 14 (.mulAdd 100 900 100)) #[] = false := by decide +kernel

/-- `eq_eval` pairs `x_k` with `R_k`, round `n - 1 - k`'s challenge: pairing `x_0` with round 0's fails. -/
example : mutLinCalls.getD 83 .zero = .add 60 904 ∧
    mutLin.okIn (mutOuts 93) #[mutSc] (mutLinCalls.set! 83 (.add 60 900)) #[] = false := by decide +kernel

/-- The input claim is `a + α b`, not `b + α a`. -/
example : mutLinCalls.getD 4 .zero = .mulAdd 50 52 51 ∧
    mutLin.okIn (mutOuts 93) #[mutSc] (mutLinCalls.set! 4 (.mulAdd 50 51 52)) #[] = false := by decide +kernel

/-- The pin's target is `α^3`, not `α^2`. -/
example : mutLinCalls.getD 6 .zero = .add 105 103 ∧
    mutLin.okIn (mutOuts 93) #[mutSc] (mutLinCalls.set! 6 (.add 105 102)) #[] = false := by decide +kernel

/-- The pin's term rides `α^3`, not `α^2`. -/
example : mutLinCalls.getD 9 .zero = .mulAdd 103 108 54 ∧
    mutLin.okIn (mutOuts 93) #[mutSc] (mutLinCalls.set! 9 (.mulAdd 102 108 54)) #[] = false := by decide +kernel

/-- The Lagrange sum pairs slice `i` with inverse `i`. -/
example : mutLinCalls.getD 19 .zero = .mulAdd 300 400 101 ∧
    mutLin.okIn (mutOuts 93) #[mutSc] (mutLinCalls.set! 19 (.mulAdd 300 401 101)) #[] = false := by decide +kernel

/-- The `C` term rides `α^2`, not `α^3`. -/
example : mutLinCalls.getD 12 .zero = .mulAdd 102 111 109 ∧
    mutLin.okIn (mutOuts 93) #[mutSc] (mutLinCalls.set! 12 (.mulAdd 103 111 109)) #[] = false := by decide +kernel

/-- Degree three, an eq weight, another pin, another input claim or another test side fail. -/
example : mutLin.okIn (mutOuts 93) #[{ mutSc with deg := 3 }] mutLinCalls #[] = false := by decide +kernel

example : mutLin.okIn (mutOuts 93)
    #[{ mutSc with rounds := mutSc.rounds.set 2 { (default : RoundCert) with chal := 902, weight := some 7 } }]
    mutLinCalls #[] = false := by decide +kernel

example : ({ mutLin with pin := hashPin + 64 } : LinCert).okIn (mutOuts 93) #[mutSc] mutLinCalls #[] = false := by
  decide +kernel

example : mutLin.okIn (mutOuts 93) #[{ mutSc with claim0 := 106 }] mutLinCalls #[] = false := by decide +kernel

example : mutLin.okIn (mutOuts 93) #[{ mutSc with final := 112 }] mutLinCalls #[] = false := by decide +kernel

/-- The zerocheck link: the inner point is the zerocheck's first challenges, and the triple its terminal's. -/
example : mutLin.zeroLink { (default : SumcheckCert) with
    rounds := (List.range 7).map fun k => { (default : RoundCert) with chal := 60 + k } } (51, 52, 53) = true := by
  decide +kernel

example : mutLin.zeroLink { (default : SumcheckCert) with
    rounds := (List.range 7).map fun k => { (default : RoundCert) with chal := 61 + k } } (51, 52, 53) = false := by
  decide +kernel

example : mutLin.zeroLink { (default : SumcheckCert) with
    rounds := (List.range 7).map fun k => { (default : RoundCert) with chal := 60 + k } } (52, 51, 53) = false := by
  decide +kernel

/-! Non-vacuity of the premises' families. -/

/-- `α`'s event is not empty: the nonzero difference `(1, 1, 0, 0)` vanishes at `α = 1`. -/
example : (1 : E) ∈ alphaBad ![1, 1, 0, 0] := by
  simp only [alphaBad, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun h => one_ne_zero (congrFun h 0), ?_⟩
  show (1 : E) + 1 * 1 + 1 ^ 2 * 0 + 1 ^ 3 * 0 = 0
  rw [mul_one, mul_zero, mul_zero, add_zero, add_zero]
  exact one_add_one

/-- The pin test's event is not empty: a pin column `(0, 1)` over one outer variable folds to one at `x = 1`. -/
example : (fun _ => (1 : E)) ∈ pinBad 1 fun t => if t = 1 then 1 else 0 := by
  simp only [pinBad, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨0, by norm_num, by simp⟩, ?_⟩
  simp [Sumcheck.eqv, bitPoint]

/-- The honest prover meets the lincheck: where the pin column folds to one, the input claim at the true triple is the
honest instance's sum. -/
example {h : ℕ} (M : Mats) (lz : ℕ → E) (xin : Fin h → E) (Zv : ℕ → ℕ → E) (α : E) (hpin : M.pin / 64 < 2 ^ h)
    (hp : pinV M Zv = 1) :
    triA M lz xin Zv + α * triB M lz xin Zv + α ^ 2 * triC lz xin Zv + α ^ 3 = (linInst h M lz xin Zv α).sum := by
  rw [linInst_sum_eq M lz xin Zv α hpin, hp, mul_one]

/-- The deferred matrix claim is met by the honest form value. -/
example (lc : LinCert) (val : Val) (sc : SumcheckCert) (M : Mats) (lz : ℕ → E) (xin : Fin sc.rounds.length → E)
    (h : Model.ev val lc.value = formVal M lz xin (Model.ev val lc.alpha) (chi (roundV val sc))
      fun i => Model.ev val (lc.slices.getD i 0)) : lc.MatrixHolds val sc M lz xin := h

end LeanVMCircuits.Rec.Bind
