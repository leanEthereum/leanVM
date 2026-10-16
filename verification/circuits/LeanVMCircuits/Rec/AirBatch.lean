module

public import LeanVMCircuits.Rec.TreeBound

@[expose] public section

/-!
The constraint batch's event: the tables' identities from the recursion leaf's table sumcheck.

`TableArgument::verify` draws `ξ` after the bus, whose GKR leaves the point `ζ` and the totals its forms owe, and runs one sumcheck (`constraints::verify`) of the claim that the sum over every owned table `t` and every row `z` below its height `2^τ_t` of `eq(ζ[..τ_t], z)` times the row's summand is the totals' `σ_0 + ξ σ_1`. A row's summand (`TableSummand::batch`) is its push form, `ξ` times its pull form, and its table's identities, the `k`th at `ξ^(2 + off_t + k)`, the tables' ranges of powers consecutive in table order (`xi_offsets`). As a polynomial in `ξ` the claim is `a_0 + a_1 ξ + Σ_j ξ^(2 + j) C_j(ζ) = 0`: `a_0` and `a_1` are the bus forms' sums less the totals, and `C_j(ζ)` is identity `j`'s sum over its table's rows weighted by `eq(ζ, z)`, a multilinear polynomial in `ζ` whose values on the cube are the identity's values on the rows. That sumcheck's soundness is a check of `RecParts` like the others; what this file takes is its input claim, `BatchClaim`, on the committed witness.

`batchDraws_card`: if some row breaks an identity (`Viol`), the draws `(ζ, ξ)` of `E^n × E` at which the claim holds, the bus parts any function of `ζ`, are at most a `(n + 66 + 1)/|E|` fraction: by Schwartz-Zippel the broken identity's `C_j(ζ)` vanishes on at most `n/|E|` of the `ζ`, and elsewhere the claim is a nonzero polynomial in `ξ` of degree at most `66 + 1`, `66` the identities (`allIds_length`). `batchBad_frac` bounds the outcomes at which the draw is in its witness's event, the draw uniform after the commitment and the bus parts fixed before `ξ` (a lens, as `busBad_frac` takes). Off the event the claim gives every identity on every row (`no_viol`), and with the hash rows' packed BLAKE2s witnesses (`Flocked`, flock's reduction, not the batch's) the rows' claims (`tables_of`).

`ChecksGiveBatch` is the premise left: where the parent's circuit is satisfied, every check's inputs are true, no compression collides and the parent's verifier reads statement `st`, the child's committed witness fits the layout, carries the public columns at `st`, has its hash rows' packed witnesses, and meets the batch claim at its draw and the bus's product claim at its draw. `checksGiveRows_of_batch` gives `ChecksGiveRows` from it with `batchBad` the batch's event, and `tree_sound_batch` and `tree_sound_ideal_batch` are `tree_sound_bound` and `tree_sound_ideal` with the batch's bound `(n_v + 67)/|E|` in place of `epsBatch`.

What differs from Rust: the model's batch is the claim's polynomial in `ξ` with the bus parts left as values `a_0`, `a_1`, so it says nothing of the bus forms, which `ProductClaim` covers; row `z`'s bit `j` is paired with `ζ_j`; and the table's height is `2^τ` with `τ = ⌈log₂ height⌉` of the witness's height, the rows past the model's height in the batch as Rust's padding rows are.
-/

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec LeanVMCircuits.Blake2s Model Finset Edges Classical

/-! The identities and the batch claim. -/

/-- The identities each owned table's rows satisfy (`Table::identities`): `HASH`'s mux bit and `SPLIT`'s. -/
def ids : Table → List Identity
  | .hash => hashIdentities
  | .split => splitIdentities
  | _ => []

/-- Every identity with its table, in table order: identity `j` is weighed by `ξ^(2 + j)` (`xi_offsets`). -/
def allIds : List (Table × Identity) := Table.all.flatMap fun T => (ids T).map (T, ·)

theorem allIds_length : allIds.length = 66 := by
  rfl

theorem mem_allIds {T : Table} {id : Identity} (h : id ∈ ids T) : (T, id) ∈ allIds := by
  simp only [allIds, List.mem_flatMap, List.mem_map]
  exact ⟨T, by cases T <;> simp [Table.all], id, h, rfl⟩

/-- A table's `τ`: its height rounded up to a power of two, `2^τ` rows. -/
def tauOf (w : Witness) (T : Table) : ℕ := Nat.clog 2 (w.height T)

theorem height_le_pow (w : Witness) (T : Table) : w.height T ≤ 2 ^ tauOf w T := Nat.le_pow_clog (by norm_num) _

/-- `eq(ζ[..τ], z)`: bit `j < τ` of row `z` choosing `ζ_j` over `1 + ζ_j`. -/
noncomputable def rowEq {n : ℕ} (ζ : Fin n → E) (τ z : ℕ) : E :=
  ∏ j : Fin n, if (j : ℕ) < τ then (if z.testBit j then ζ j else 1 + ζ j) else 1

/-- Identity `p`'s sum over its table's rows, weighted by `eq(ζ, z)`. -/
noncomputable def coef {n : ℕ} (w : Witness) (ζ : Fin n → E) (p : Table × Identity) : E :=
  ∑ z ∈ range (2 ^ tauOf w p.1), rowEq ζ (tauOf w p.1) z * emb (p.2.eval (w.cols p.1 z))

/-- The batch claim at `(ζ, ξ)` with bus parts `a`: `a_0 + a_1 ξ + Σ_j ξ^(2 + j) C_j(ζ) = 0`. -/
def BatchClaim {n : ℕ} (w : Witness) (ζ : Fin n → E) (a : Fin 2 → E) (ξ : E) : Prop :=
  a 0 + ξ * a 1 + ∑ j : Fin allIds.length, ξ ^ (2 + (j : ℕ)) * coef w ζ allIds[j] = 0

/-- Some row breaks an identity. -/
def Viol (w : Witness) : Prop := ∃ p ∈ allIds, ∃ z < 2 ^ tauOf w p.1, p.2.eval (w.cols p.1 z) ≠ 0

/-- The batch's draw event for a committed witness and bus parts depending on `ζ`: the draws at which its claim holds though some row breaks an identity. -/
noncomputable def batchDraws {n : ℕ} (w : Witness) (a : (Fin n → E) → Fin 2 → E) : Finset ((Fin n → E) × E) :=
  {x | Viol w ∧ BatchClaim w x.1 (a x.1) x.2}

/-- Off the draw event, the batch claim gives every identity on every row. -/
theorem no_viol {n : ℕ} {w : Witness} {a : (Fin n → E) → Fin 2 → E} {x : (Fin n → E) × E}
    (hx : x ∉ batchDraws w a) (h : BatchClaim w x.1 (a x.1) x.2) : ¬ Viol w := fun hv =>
  hx (by simp only [batchDraws, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hv, h⟩)

/-- Non-vacuity of `BatchClaim`: with every identity on every row and no bus parts, it holds at every draw. -/
theorem batch_of_rows {n : ℕ} {w : Witness} (h : ¬ Viol w) (ζ : Fin n → E) (ξ : E) : BatchClaim w ζ 0 ξ := by
  have hc : ∀ p ∈ allIds, coef w ζ p = 0 := by
    intro p hp
    refine Finset.sum_eq_zero fun z hz => ?_
    have : p.2.eval (w.cols p.1 z) = 0 := by
      by_contra hne
      exact h ⟨p, hp, z, Finset.mem_range.mp hz, hne⟩
    rw [this, emb_zero, mul_zero]
  unfold BatchClaim
  rw [Finset.sum_eq_zero fun j _ => by rw [hc allIds[j] (List.getElem_mem j.isLt), mul_zero]]
  simp

/-! The batch's polynomial in `ζ`. -/

open MvPolynomial in
/-- `eq(ζ[..τ], z)` as a polynomial in `ζ`. -/
noncomputable def eqPoly (n τ z : ℕ) : MvPolynomial (Fin n) E :=
  ∏ j : Fin n, if (j : ℕ) < τ then (if z.testBit j then X j else 1 + X j) else 1

open MvPolynomial in
/-- `C_p(ζ)` as a polynomial in `ζ`. -/
noncomputable def coefPoly (n : ℕ) (w : Witness) (p : Table × Identity) : MvPolynomial (Fin n) E :=
  ∑ z ∈ range (2 ^ tauOf w p.1), eqPoly n (tauOf w p.1) z * C (emb (p.2.eval (w.cols p.1 z)))

open MvPolynomial in
theorem eval_coefPoly {n : ℕ} (w : Witness) (p : Table × Identity) (ζ : Fin n → E) :
    eval ζ (coefPoly n w p) = coef w ζ p := by
  simp only [coefPoly, coef, eqPoly, rowEq, map_sum, map_mul, map_prod, apply_ite, map_add, map_one, eval_X, eval_C]

/-- The Boolean point naming row `z`. -/
noncomputable def bitPoint (n z : ℕ) (j : Fin n) : E := if z.testBit j then 1 else 0

theorem one_add_one : (1 : E) + 1 = 0 := UnionSound.one_add_one_E

open MvPolynomial in
theorem eval_eqPoly {n τ z z' : ℕ} (hτ : τ ≤ n) (hz : z < 2 ^ τ) (hz' : z' < 2 ^ τ) :
    eval (bitPoint n z') (eqPoly n τ z) = if z = z' then 1 else 0 := by
  have factor : ∀ j : Fin n, eval (bitPoint n z')
      (if (j : ℕ) < τ then (if z.testBit j then X j else 1 + X j) else 1 : MvPolynomial (Fin n) E) =
      if (j : ℕ) < τ then (if z.testBit j = z'.testBit j then 1 else 0) else 1 := by
    intro j
    by_cases h1 : (j : ℕ) < τ <;> by_cases h2 : z.testBit j <;> by_cases h3 : z'.testBit j <;>
      simp [h1, h2, h3, bitPoint, one_add_one]
  rw [eqPoly, map_prod, Finset.prod_congr rfl fun j _ => factor j]
  split_ifs with hzz
  · subst hzz
    exact Finset.prod_eq_one fun j _ => by simp
  · obtain ⟨i, hi⟩ : ∃ i, z.testBit i ≠ z'.testBit i := by
      by_contra hall
      push Not at hall
      exact hzz (Nat.eq_of_testBit_eq hall)
    have hiτ : i < τ := by
      by_contra hge
      have h1 := Nat.testBit_eq_false_of_lt (i := i)
        (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h2 := Nat.testBit_eq_false_of_lt (i := i)
        (lt_of_lt_of_le hz' (Nat.pow_le_pow_right (by norm_num) (by omega)))
      exact hi (h1.trans h2.symm)
    refine Finset.prod_eq_zero (i := ⟨i, by omega⟩) (Finset.mem_univ _) ?_
    simp [hiτ, hi]

theorem emb_injective : Function.Injective emb := (AdjoinRoot.of extModulus).injective

open MvPolynomial in
theorem eval_coefPoly_point {n : ℕ} {w : Witness} {p : Table × Identity} (hτ : tauOf w p.1 ≤ n) {z' : ℕ}
    (hz' : z' < 2 ^ tauOf w p.1) : eval (bitPoint n z') (coefPoly n w p) = emb (p.2.eval (w.cols p.1 z')) := by
  simp only [coefPoly, map_sum, map_mul, eval_C]
  rw [Finset.sum_congr rfl fun z hz => by rw [eval_eqPoly hτ (Finset.mem_range.mp hz) hz']]
  simp [Finset.sum_ite_eq', Finset.mem_range.mpr hz']

open MvPolynomial in
theorem totalDegree_coefPoly (n : ℕ) (w : Witness) (p : Table × Identity) : (coefPoly n w p).totalDegree ≤ n := by
  refine totalDegree_finsetSum_le fun z _ => (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  refine (totalDegree_finsetProd _ _).trans ?_
  have : ∀ j : Fin n, (if (j : ℕ) < tauOf w p.1 then (if z.testBit j then X j else 1 + X j) else 1 :
      MvPolynomial (Fin n) E).totalDegree ≤ 1 := by
    intro j
    split
    · split
      · rw [totalDegree_X]
      · exact (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; norm_num) (by rw [totalDegree_X]))
    · rw [totalDegree_one]; norm_num
  calc ∑ j : Fin n, _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => this j
    _ = n := by simp

open MvPolynomial in
/-- Schwartz-Zippel: a broken identity's weighted sum vanishes on at most `n/|E|` of the points `ζ`. -/
theorem zeros_card {n : ℕ} {w : Witness} {p : Table × Identity} (hτ : tauOf w p.1 ≤ n) {z' : ℕ}
    (hz' : z' < 2 ^ tauOf w p.1) (hv : p.2.eval (w.cols p.1 z') ≠ 0) :
    #({ζ | coef w ζ p = 0} : Finset (Fin n → E)) * Fintype.card E ≤ n * Fintype.card E ^ n := by
  have hp : coefPoly n w p ≠ 0 := by
    intro h0
    have := eval_coefPoly_point (n := n) hτ hz'
    rw [h0, map_zero] at this
    exact hv (emb_injective (this.symm.trans emb_zero.symm))
  have sz := schwartz_zippel_totalDegree hp (univ : Finset E)
  rw [Fintype.piFinset_univ, card_univ] at sz
  have hset : ({f | eval f (coefPoly n w p) = 0} : Finset (Fin n → E)) =
      ({ζ | coef w ζ p = 0} : Finset (Fin n → E)) := by
    apply Finset.filter_congr
    intro f _
    rw [eval_coefPoly]
  rw [hset] at sz
  have hE : (0 : ℚ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hE] at sz
  have hdeg : ((coefPoly n w p).totalDegree : ℚ≥0) ≤ n := by exact_mod_cast totalDegree_coefPoly n w p
  have : (#({ζ | coef w ζ p = 0} : Finset (Fin n → E)) : ℚ≥0) * Fintype.card E ≤ n * Fintype.card E ^ n :=
    sz.trans (by gcongr)
  exact_mod_cast this

/-! The batch's polynomial in `ξ`. -/

/-- `a_0 + a_1 ξ + Σ_j ξ^(2 + j) c_j` as a polynomial in `ξ`. -/
noncomputable def xiPoly {m : ℕ} (c : Fin m → E) (a : Fin 2 → E) : Polynomial E :=
  Polynomial.C (a 0) + Polynomial.C (a 1) * Polynomial.X + ∑ j : Fin m, Polynomial.C (c j) * Polynomial.X ^ (2 + (j : ℕ))

theorem eval_xiPoly {m : ℕ} (c : Fin m → E) (a : Fin 2 → E) (ξ : E) :
    (xiPoly c a).eval ξ = a 0 + ξ * a 1 + ∑ j : Fin m, ξ ^ (2 + (j : ℕ)) * c j := by
  simp only [xiPoly, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_finsetSum, Polynomial.eval_pow]
  rw [mul_comm (a 1)]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem coeff_xiPoly {m : ℕ} (c : Fin m → E) (a : Fin 2 → E) (N : ℕ) :
    (xiPoly c a).coeff N = (if N = 0 then a 0 else 0) + (if N = 1 then a 1 else 0) +
      ∑ j : Fin m, if N = 2 + (j : ℕ) then c j else 0 := by
  simp only [xiPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]

/-- A nonzero coefficient past `ξ^1` leaves at most `m + 1` roots. -/
theorem xi_roots {m : ℕ} (c : Fin m → E) (a : Fin 2 → E) (j₀ : Fin m) (hc : c j₀ ≠ 0) :
    #({ξ | a 0 + ξ * a 1 + ∑ j : Fin m, ξ ^ (2 + (j : ℕ)) * c j = 0} : Finset E) ≤ m + 1 := by
  have hp : xiPoly c a ≠ 0 := by
    intro h0
    have := coeff_xiPoly c a (2 + j₀)
    have hs : (∑ j : Fin m, if 2 + (j₀ : ℕ) = 2 + (j : ℕ) then c j else 0) = c j₀ := by
      rw [Finset.sum_eq_single j₀ (fun j _ hj => if_neg fun h => hj (Fin.ext (by omega))) (by simp)]
      simp
    rw [h0, Polynomial.coeff_zero, if_neg (by omega), if_neg (by omega), zero_add, zero_add, hs] at this
    exact hc this.symm
  have hdeg : (xiPoly c a).natDegree ≤ m + 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_xiPoly, if_neg (by omega), if_neg (by omega), zero_add, zero_add]
    exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
  calc #({ξ | a 0 + ξ * a 1 + ∑ j : Fin m, ξ ^ (2 + (j : ℕ)) * c j = 0} : Finset E)
      ≤ (xiPoly c a).roots.toFinset.card := by
        refine card_le_card fun ξ hξ => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_xiPoly]
        exact hξ
    _ ≤ Multiset.card (xiPoly c a).roots := Multiset.toFinset_card_le _
    _ ≤ (xiPoly c a).natDegree := Polynomial.card_roots' _
    _ ≤ m + 1 := hdeg

/-! The batch's event. -/

/-- The draws `(x, y)` satisfying `P` are the sum over `x` of the `y` satisfying it. -/
theorem card_pairs {A B : Type} [Fintype A] [Fintype B] (P : A × B → Prop) [DecidablePred P] :
    #({x | P x} : Finset (A × B)) = ∑ a : A, #({b | P (a, b)} : Finset B) := by
  simp only [card_filter]
  exact Fintype.sum_prod_type _

theorem card_draws (n : ℕ) : Fintype.card (Fin n → E) = Fintype.card E ^ n := by simp

/-- The batch's draw event is at most a `(n + 66 + 1)/|E|` fraction of the draws `E^n × E`, every table's `τ` at most `n`, whatever the bus parts as a function of `ζ`. -/
theorem batchDraws_card {n : ℕ} (w : Witness) (htau : ∀ T, tauOf w T ≤ n) (a : (Fin n → E) → Fin 2 → E) :
    #(batchDraws w a) * Fintype.card E ≤ (n + allIds.length + 1) * Fintype.card E ^ (n + 1) := by
  by_cases hv : Viol w
  swap
  · have : batchDraws w a = ∅ := by
      ext x
      simp [batchDraws, hv]
    simp [this]
  obtain ⟨p, hp, z', hz', hne⟩ := hv
  obtain ⟨j₀, hj₀, hj₀p⟩ := List.getElem_of_mem hp
  set Z : Finset (Fin n → E) := {ζ | coef w ζ p = 0}
  have hZ := zeros_card (htau p.1) hz' hne
  have hfib : ∀ ζ : Fin n → E, #({ξ | (ζ, ξ) ∈ batchDraws w a} : Finset E) ≤
      (if ζ ∈ Z then Fintype.card E else 0) + (allIds.length + 1) := by
    intro ζ
    by_cases hζ : ζ ∈ Z
    · rw [if_pos hζ]
      exact (card_le_univ _).trans (Nat.le_add_right _ _)
    · rw [if_neg hζ, zero_add]
      have hc : coef w ζ allIds[j₀] ≠ 0 := by
        rw [hj₀p]
        simpa [Z] using hζ
      refine le_trans (card_le_card fun ξ hξ => ?_) (xi_roots (fun j : Fin allIds.length => coef w ζ allIds[j])
        (a ζ) ⟨j₀, hj₀⟩ hc)
      simp only [batchDraws, Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
      exact hξ.2
  have hsum : #(batchDraws w a) ≤ #Z * Fintype.card E + Fintype.card E ^ n * (allIds.length + 1) := by
    calc #(batchDraws w a) = ∑ ζ : Fin n → E, #({ξ | (ζ, ξ) ∈ batchDraws w a} : Finset E) := by
          have := card_pairs (fun x : (Fin n → E) × E => x ∈ batchDraws w a)
          rw [← this]
          congr 1
          ext x
          simp
      _ ≤ ∑ ζ : Fin n → E, ((if ζ ∈ Z then Fintype.card E else 0) + (allIds.length + 1)) :=
          sum_le_sum fun ζ _ => hfib ζ
      _ = #Z * Fintype.card E + Fintype.card E ^ n * (allIds.length + 1) := by
          rw [sum_add_distrib, sum_const, card_univ, card_draws, smul_eq_mul, ← sum_filter, sum_const,
            smul_eq_mul]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  calc #(batchDraws w a) * Fintype.card E
      ≤ (#Z * Fintype.card E + Fintype.card E ^ n * (allIds.length + 1)) * Fintype.card E :=
        Nat.mul_le_mul_right _ hsum
    _ = #Z * Fintype.card E * Fintype.card E + (allIds.length + 1) * Fintype.card E ^ (n + 1) := by ring
    _ ≤ n * Fintype.card E ^ n * Fintype.card E + (allIds.length + 1) * Fintype.card E ^ (n + 1) := by
        gcongr
    _ = (n + allIds.length + 1) * Fintype.card E ^ (n + 1) := by ring

theorem card_E_ge : 2 ^ 64 ≤ Fintype.card E := by
  rw [← card_K]
  exact Fintype.card_le_of_injective emb emb_injective

/-- Mutation test of the rule in general: a witness breaking an identity fails the batch claim at some draw, whatever the bus parts, when `n + 66 + 1 < |E|`. -/
theorem batch_rejects {n : ℕ} (w : Witness) (htau : ∀ T, tauOf w T ≤ n) (hv : Viol w)
    (hn : n + allIds.length + 1 < Fintype.card E) (a : (Fin n → E) → Fin 2 → E) :
    ∃ x : (Fin n → E) × E, ¬ BatchClaim w x.1 (a x.1) x.2 := by
  by_contra hall
  push Not at hall
  have huniv : batchDraws w a = univ := by
    ext x
    simp [batchDraws, hv, hall x]
  have hc := batchDraws_card w htau a
  rw [huniv, card_univ, Fintype.card_prod, card_draws] at hc
  have hpos : 0 < Fintype.card E ^ (n + 1) := by have := Fintype.card_pos (α := E); positivity
  have : Fintype.card E ≤ n + allIds.length + 1 := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Fintype.card E ^ (n + 1) * Fintype.card E = Fintype.card E ^ n * Fintype.card E * Fintype.card E := by
          ring
      _ ≤ (n + allIds.length + 1) * Fintype.card E ^ (n + 1) := hc
      _ = Fintype.card E ^ (n + 1) * (n + allIds.length + 1) := by ring
  omega

/-- A witness whose one `SPLIT` row has bit column `1` holding `2`, not a bit. -/
noncomputable def badSplit : Witness where
  height _ := 1
  cols T _ c := if T = .split ∧ c = 1 then ofWord 2 else 0

theorem badSplit_viol : Viol badSplit := by
  refine ⟨(.split, boolean 1), mem_allIds (by simp [ids, splitIdentities]; exact Or.inr ⟨0, by norm_num, rfl⟩),
    0, by simp [tauOf, badSplit], ?_⟩
  intro h
  rw [boolean_spec] at h
  have h2 : toWord (ofWord 2) = 2 := toWord_ofWord 2 (by norm_num)
  simp only [badSplit, and_self, if_true] at h
  rcases h with h | h
  · rw [h, ← ofWord_zero, toWord_ofWord 0 (by norm_num)] at h2
    omega
  · rw [h, ← ofWord_one, toWord_ofWord 1 (by norm_num)] at h2
    omega

/-- Mutation test: the batch claim rejects `badSplit` at some draw, whatever the bus parts. -/
theorem badSplit_rejected (a : (Fin 0 → E) → Fin 2 → E) :
    ∃ x : (Fin 0 → E) × E, ¬ BatchClaim badSplit x.1 (a x.1) x.2 :=
  batch_rejects badSplit (fun T => by simp [tauOf, badSplit]) badSplit_viol
    (by rw [allIds_length]; exact lt_of_lt_of_le (by norm_num) card_E_ge) a

/-! The rows' claims from the batch. -/

/-- The hash rows' packed BLAKE2s witnesses with their ports (`HashRow.witness`), which flock's reduction proves, not the batch. -/
def Flocked (s : State) (w : Witness) : Prop :=
  ∀ z < (rowsOf s .hash).size, ∃ a, Compress.artifact.Holds a ∧
    Export.ports a = (portsOf fun j => columnWord (w.cols .hash z) j) ∧
    Export.result a = resultOf fun k => columnWord (w.cols .hash z) (hashO + k)

/-- Every identity on every row, the hash rows' packed witnesses and the rows within the heights give every row of the circuit its table. -/
theorem tables_of {s : State} {w : Witness} (hfit : ∀ T, (rowsOf s T).size ≤ w.height T) (hfl : Flocked s w)
    (hv : ¬ Viol w) : ∀ T, ∀ z < (rowsOf s T).size, holds T (w.cols T z) := by
  intro T z hz
  have hid : ∀ id ∈ ids T, id.eval (w.cols T z) = 0 := by
    intro id hid
    by_contra hne
    exact hv ⟨(T, id), mem_allIds hid, z, lt_of_lt_of_le (lt_of_lt_of_le hz (hfit T)) (height_le_pow w T), hne⟩
  cases T
  · trivial
  · trivial
  · exact ⟨hfl z hz, hid⟩
  · exact hid
  · trivial
  · trivial

/-- Non-vacuity of `Flocked`: the honest witness of a satisfied circuit has its hash rows' packed witnesses. -/
theorem flocked_honest {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val)
    (hsize : ∀ T, (rowsOf s T).size ≤ 2 ^ 32) : Flocked s (honest h) := fun z hz =>
  ((claims_of_sat h hsize).tables .hash z hz).witness

theorem eval_zero_row (id : Identity) : id.eval (fun _ => 0) = 0 := by
  simp [Identity.eval]

/-- Non-vacuity of the batch claim at the honest witness: it holds at every draw with no bus parts. -/
theorem batch_honest {st : ℕ → Fin 4 → K} {s : State} {val : Val} (h : Sat st s val)
    (hsize : ∀ T, (rowsOf s T).size ≤ 2 ^ 32) {n : ℕ} (ζ : Fin n → E) (ξ : E) : BatchClaim (honest h) ζ 0 ξ := by
  refine batch_of_rows ?_ ζ ξ
  rintro ⟨⟨T, id⟩, hp, z, -, hne⟩
  simp only [allIds, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hp
  obtain ⟨T', -, id', hid', rfl, rfl⟩ := hp
  apply hne
  by_cases hz : z < (rowsOf s T').size
  · have ht := (claims_of_sat h hsize).tables T' z hz
    cases T' <;> simp only [ids, List.not_mem_nil] at hid'
    · exact ht.identities id' hid'
    · exact ht id' hid'
  · have : (honest h).cols T' z = fun _ => 0 := by
      funext c
      simp [honest, hz]
    simp only at this ⊢
    rw [this, eval_zero_row]

/-! The batch's draw over outcomes. -/

/-- The batch's event over outcomes: where the outcome's draw is in its committed witness's draw event, at the outcome's bus parts. -/
noncomputable def batchBad {Ω : Type} [Fintype Ω] {n : ℕ} (wit : Ω → Witness) (aOf : Ω → (Fin n → E) → Fin 2 → E)
    (bdraw : Ω → (Fin n → E) × E) : Finset Ω :=
  {ω | bdraw ω ∈ batchDraws (wit ω) (aOf ω)}

/-- The batch's event is at most an `(n + 66 + 1)/|E|` fraction of the outcomes when the draw `(ζ, ξ)` is uniform and made after the commitment, and the bus parts are fixed but for `ζ`: a lens `put`/`bdraw` (`Bind.card_lens`) leaving the committed witness and the bus parts' dependence on `ζ` unchanged. -/
theorem batchBad_frac {Ω : Type} [Fintype Ω] {n : ℕ} (wit : Ω → Witness) (aOf : Ω → (Fin n → E) → Fin 2 → E)
    (bdraw : Ω → (Fin n → E) × E) (put : Ω → (Fin n → E) × E → Ω) (hgp : ∀ ω x, bdraw (put ω x) = x)
    (hpg : ∀ ω, put ω (bdraw ω) = ω) (hpp : ∀ ω x y, put (put ω x) y = put ω y)
    (hwit : ∀ ω x, wit (put ω x) = wit ω) (haOf : ∀ ω x, aOf (put ω x) = aOf ω)
    (htau : ∀ ω T, tauOf (wit ω) T ≤ n) :
    (#(batchBad wit aOf bdraw) : ℚ≥0) / Fintype.card Ω ≤ ((n + allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E := by
  have hpos : 0 < Fintype.card E := Fintype.card_pos
  set B := n + allIds.length + 1
  have hterm : ∀ ω, #(batchDraws (wit ω) (aOf ω)) ≤ B * Fintype.card E ^ n := by
    intro ω
    have hc := batchDraws_card (wit ω) (htau ω) (aOf ω)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc #(batchDraws (wit ω) (aOf ω)) * Fintype.card E ≤ B * Fintype.card E ^ (n + 1) := hc
      _ = B * Fintype.card E ^ n * Fintype.card E := by ring
  have hlens := Bind.card_lens put bdraw hgp hpg hpp fun ω => bdraw ω ∈ batchDraws (wit ω) (aOf ω)
  have hA : #(batchBad wit aOf bdraw) * Fintype.card ((Fin n → E) × E) ≤
      Fintype.card Ω * (B * Fintype.card E ^ n) := by
    refine le_trans (Nat.mul_le_mul_right _ (card_le_card ?_)) (hlens.trans ?_)
    · intro ω hω
      simp only [batchBad, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hω
    · calc _ ≤ ∑ _ω : Ω, B * Fintype.card E ^ n :=
            sum_le_sum fun ω _ => (card_le_card fun x hx => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
              rwa [hgp, hwit, haOf] at hx).trans (hterm ω)
        _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
  rw [Fintype.card_prod, card_draws] at hA
  refine Bind.frac_of_card n ?_
  calc #(batchBad wit aOf bdraw) * Fintype.card E * Fintype.card E ^ n =
        #(batchBad wit aOf bdraw) * (Fintype.card E ^ n * Fintype.card E) := by ring
    _ ≤ Fintype.card Ω * (B * Fintype.card E ^ n) := hA
    _ = Fintype.card Ω * B * Fintype.card E ^ n := by ring

/-! The batch in the tree. -/

section Tree

variable {ι Ω : Type}

/-- The premise left: where the parent's circuit is satisfied, every check's inputs are true, no compression collides (off `crBad v`) and the parent's verifier reads statement `st`, child `v`'s committed witness `wit v ω` holds its rows within heights below `2^32`, carries the public columns at `st`, has its hash rows' packed BLAKE2s witnesses (`Flocked`), meets the batch claim at its draw `bdraw v ω` with bus parts `aOf v ω` (`BatchClaim`) and the bus's product claim at its draw `draw v ω` (`ProductClaim`). These are the inputs of the table sumcheck, the bus GKR and flock's reduction, true on the committed witness, and the layout's and public columns' reads. -/
def ChecksGiveBatch [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (aOf : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness) : Prop :=
  ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
    Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
    (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v →
    ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
      (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
    (∀ T', (rowsOf (t v) T').size ≤ (wit v ω).height T' ∧ (wit v ω).height T' ≤ 2 ^ 32) ∧
    (∀ z (hz : z < (t v).pub.size) (i : Fin 4),
      (wit v ω).cols .pub z i = srcVal (treeStmt T cert slot stRoot val v ω) (t v).pub[z].2 i) ∧
    Flocked (t v) (wit v ω) ∧
    BatchClaim (wit v ω) (bdraw v ω).1 (aOf v ω (bdraw v ω).1) (bdraw v ω).2 ∧
    ProductClaim (t v) (wit v ω) (draw v ω)

/-- `ChecksGiveRows` from `ChecksGiveBatch`, `batchBad` the batch's event: off it the batch claim gives every identity on every row (`no_viol`), and with the hash rows' packed witnesses every row its table (`tables_of`). -/
theorem checksGiveRows_of_batch [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (aOf : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness)
    (h : ChecksGiveBatch T cert t os L slot stRoot val P n bdraw aOf draw wit) :
    ChecksGiveRows T cert t os L slot stRoot val P (fun v => batchBad (wit v) (aOf v) (bdraw v)) draw wit := by
  intro v hv hne ω hps hin hcr hb hver
  obtain ⟨hfit, hpub, hfl, hbat, hprod⟩ := h v hv hne ω hps hin hcr hver
  have hx : bdraw v ω ∉ batchDraws (wit v ω) (aOf v ω) := fun hm =>
    hb (by simp only [batchBad, Finset.mem_filter, Finset.mem_univ, true_and]; exact hm)
  exact ⟨⟨hfit, tables_of (fun T' => (hfit T').1) hfl (no_viol hx hbat), hpub⟩, hprod⟩

/-- Non-vacuity of `ChecksGiveBatch`: parts whose one check per child has its conclusion as its inputs meet it. -/
theorem checksGiveBatch_claims [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E) (aOf : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E)
    (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness) (outOk : ι → ℕ → Ω → Prop)
    (testBad : ι → ℕ → Finset Ω) (pcsBad crBad : ι → Finset Ω) :
    ChecksGiveBatch T cert t os L slot stRoot val
      ⟨fun _ => 1, fun v _ ω =>
        (∀ T', (rowsOf (t v) T').size ≤ (wit v ω).height T' ∧ (wit v ω).height T' ≤ 2 ^ 32) ∧
        (∀ z (hz : z < (t v).pub.size) (i : Fin 4),
          (wit v ω).cols .pub z i = srcVal (treeStmt T cert slot stRoot val v ω) (t v).pub[z].2 i) ∧
        Flocked (t v) (wit v ω) ∧
        BatchClaim (wit v ω) (bdraw v ω).1 (aOf v ω (bdraw v ω).1) (bdraw v ω).2 ∧
        ProductClaim (t v) (wit v ω) (draw v ω), outOk, testBad, pcsBad, crBad⟩ n bdraw aOf draw wit :=
  fun _ _ _ _ _ hin _ _ => hin 0 Nat.one_pos

/-! The table sumcheck's and bus GKR's honest instances on the committed witness. -/

/-- The table sumcheck's honest sum on a committed witness at `(ζ, ξ)` (`TableSummand::batch` summed with
`eq(ζ, ·)`): the bus forms' weighted sums `a` at `ξ^0` (push) and `ξ^1` (pull), and each identity's, `coef`, at
`ξ^(2 + j)`. -/
noncomputable def tableSum {n : ℕ} (w : Witness) (ζ : Fin n → E) (a : Fin 2 → E) (ξ : E) : E :=
  a 0 + ξ * a 1 + ∑ j : Fin allIds.length, ξ ^ (2 + (j : ℕ)) * coef w ζ allIds[j]

/-- The batch claim from the table sumcheck's input claim: the verifier's claim, the bus totals' `σ_0 + ξ σ_1`, equal
to the committed witness's honest sum is the batch claim with bus parts the forms' sums less the totals. -/
theorem batchClaim_of_sum {n : ℕ} {w : Witness} {ζ : Fin n → E} {a σ : Fin 2 → E} {ξ : E}
    (h : σ 0 + ξ * σ 1 = tableSum w ζ a ξ) : BatchClaim w ζ (fun i => a i - σ i) ξ := by
  unfold BatchClaim
  unfold tableSum at h
  linear_combination -h

/-- The bus GKR's honest root over the pulls at a draw `f = (β, A)`: the product of `β + fp_A(t)` over them. -/
noncomputable def pullRoot (s : State) (w : Witness) (f : Fin 5 → E) : E :=
  UnionSound.prodAt (pulls busTuple (fun i : Fin (slots w).length => key (slots w)[i])
    (fun i => carried w (slots w)[i])) (f 0) (Fin.tail f)

/-- The bus GKR's honest root over the pushes at a draw `f = (β, A)`. -/
noncomputable def pushRoot (s : State) (w : Witness) (f : Fin 5 → E) : E :=
  UnionSound.prodAt (pushes busTuple (fun i : Fin (slots w).length => key (slots w)[i])
    (classNext fun i => slotClass s (slots w)[i]) (fun i => carried w (slots w)[i])) (f 0) (Fin.tail f)

/-- The product claim is the two honest roots' agreement. -/
theorem productClaim_iff {s : State} {w : Witness} {f : Fin 5 → E} :
    ProductClaim s w f ↔ pullRoot s w f = pushRoot s w f := Iff.rfl

/-- The premise with the table sumcheck's and bus GKR's honest instances the committed witness's: where the parent's
circuit is satisfied, every check's inputs are true, no compression collides and the parent's verifier reads statement
`st`, child `v`'s committed witness `wit v ω` holds its rows within heights below `2^32`, carries the public columns at
`st` and has its hash rows' packed witnesses; the table sumcheck's input claim, the bus totals `tot` at the batch's
draw as `σ_0 + ξ σ_1`, is the committed witness's honest sum (`tableSum`, with the bus forms' weighted sums `forms`);
and the bus GKR's root claims `roots` are the committed witness's honest roots at its draw (`pullRoot`, `pushRoot`),
which the verifier holds equal (`bus::verify_balance`). -/
def ChecksGiveInst [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (forms tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (wit : ι → Ω → Witness) : Prop :=
  ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
    Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
    (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v →
    ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
      (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
    (∀ T', (rowsOf (t v) T').size ≤ (wit v ω).height T' ∧ (wit v ω).height T' ≤ 2 ^ 32) ∧
    (∀ z (hz : z < (t v).pub.size) (i : Fin 4),
      (wit v ω).cols .pub z i = srcVal (treeStmt T cert slot stRoot val v ω) (t v).pub[z].2 i) ∧
    Flocked (t v) (wit v ω) ∧
    tot v ω (bdraw v ω).1 0 + (bdraw v ω).2 * tot v ω (bdraw v ω).1 1 =
      tableSum (wit v ω) (bdraw v ω).1 (forms v ω (bdraw v ω).1) (bdraw v ω).2 ∧
    roots v ω 0 = pullRoot (t v) (wit v ω) (draw v ω) ∧ roots v ω 1 = pushRoot (t v) (wit v ω) (draw v ω) ∧
    roots v ω 0 = roots v ω 1

/-- `ChecksGiveBatch` from `ChecksGiveInst`, the batch's bus parts the forms' sums less the totals: the batch claim from
the table sumcheck's input claim (`batchClaim_of_sum`), the product claim from the bus GKR's roots. -/
theorem checksGiveBatch_of_inst [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (forms tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (wit : ι → Ω → Witness) (h : ChecksGiveInst T cert t os L slot stRoot val P n bdraw forms tot roots draw wit) :
    ChecksGiveBatch T cert t os L slot stRoot val P n bdraw (fun v ω ζ i => forms v ω ζ i - tot v ω ζ i) draw wit := by
  intro v hv hne ω hps hin hcr hver
  obtain ⟨hfit, hpub, hfl, hsum, h0, h1, heq⟩ := h v hv hne ω hps hin hcr hver
  exact ⟨hfit, hpub, hfl, batchClaim_of_sum hsum, productClaim_iff.mpr (h0.symm.trans (heq.trans h1))⟩

/-- Non-vacuity of `ChecksGiveInst`: parts whose one check per child has its conclusion as its inputs meet it. -/
theorem checksGiveInst_claims [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E) (forms tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E)
    (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness) (outOk : ι → ℕ → Ω → Prop)
    (testBad : ι → ℕ → Finset Ω) (pcsBad crBad : ι → Finset Ω) :
    ChecksGiveInst T cert t os L slot stRoot val
      ⟨fun _ => 1, fun v _ ω =>
        (∀ T', (rowsOf (t v) T').size ≤ (wit v ω).height T' ∧ (wit v ω).height T' ≤ 2 ^ 32) ∧
        (∀ z (hz : z < (t v).pub.size) (i : Fin 4),
          (wit v ω).cols .pub z i = srcVal (treeStmt T cert slot stRoot val v ω) (t v).pub[z].2 i) ∧
        Flocked (t v) (wit v ω) ∧
        tot v ω (bdraw v ω).1 0 + (bdraw v ω).2 * tot v ω (bdraw v ω).1 1 =
          tableSum (wit v ω) (bdraw v ω).1 (forms v ω (bdraw v ω).1) (bdraw v ω).2 ∧
        roots v ω 0 = pullRoot (t v) (wit v ω) (draw v ω) ∧ roots v ω 1 = pushRoot (t v) (wit v ω) (draw v ω) ∧
        roots v ω 0 = roots v ω 1, outOk, testBad, pcsBad, crBad⟩ n bdraw forms tot roots draw wit :=
  fun _ _ _ _ _ hin _ _ => hin 0 Nat.one_pos

/-- Mutation test of `batchClaim_of_sum`: with no identities broken, the batch claim at bus parts `a - σ` fails where
the claim `σ_0 + ξ σ_1` misses the honest sum by one. -/
example {n : ℕ} (w : Witness) (ζ : Fin n → E) (a : Fin 2 → E) (ξ : E) (hc : ∀ j : Fin allIds.length, coef w ζ allIds[j] = 0) :
    ¬ BatchClaim w ζ (fun i => a i - (a i + if i = 0 then 1 else 0)) ξ := by
  unfold BatchClaim
  simp only [hc, mul_zero, Finset.sum_const_zero, add_zero]
  simp

open Classical in
/-- `tree_sound_bound` with the batch's bound: the constraint batch's event is the batch's draw event (`batchBad`), at most `(n_v + 66 + 1)/|E|` of the outcomes (`batchBad_frac`), and the premise left is `ChecksGiveBatch`. -/
theorem tree_sound_batch [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι Ω)
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E) (aOf : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E)
    (draw : ι → Ω → Fin 5 → E) (wit : ι → Ω → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveBatch T cert (fun v => stmtFirst (t v)) os L slot stRoot val P n bdraw aOf draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (bput : (v : ι) → Ω → (Fin (n v) → E) × E → Ω) (hgp : ∀ v ω x, bdraw v (bput v ω x) = x)
    (hpg : ∀ v ω, bput v ω (bdraw v ω) = ω) (hpp : ∀ v ω x y, bput v (bput v ω x) y = bput v ω y)
    (hwit : ∀ v ω x, wit v (bput v ω x) = wit v ω) (haOf : ∀ v ω x, aOf v (bput v ω x) = aOf v ω)
    (htau : ∀ v ω T', tauOf (wit v ω) T' ≤ n v)
    (epsPCS epsCR epsBus : ι → ℚ≥0) (hpcs : PcsBound P epsPCS)
    (hcr : ∀ v ∈ T.nodes, ((P.crBad v).card : ℚ≥0) / Fintype.card Ω ≤ epsCR v)
    (hbus : ∀ v ∈ T.nodes, ((busBad (stmtFirst (t v)) (wit v) (draw v)).card : ℚ≥0) / Fintype.card Ω ≤ epsBus v) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) / Fintype.card Ω +
        epsPCS v + epsCR v + epsBus v + ((n v + allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E) :=
  tree_sound_bound T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP
    (fun v => batchBad (wit v) (aOf v) (bdraw v)) draw wit hval
    (checksGiveRows_of_batch T cert (fun v => stmtFirst (t v)) os L slot stRoot val P n bdraw aOf draw wit hlink) tD tM bad hstep hroot
    epsPCS epsCR epsBus (fun v => ((n v + allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E) hpcs hcr hbus
    (fun v _ => batchBad_frac (wit v) (aOf v) (bdraw v) (bput v) (hgp v) (hpg v) (hpp v) (hwit v) (haOf v)
      (htau v))

end Tree

section Ideal

variable {ι Ω₀ X V C R : Type}

open Classical in
/-- `tree_sound_ideal` with the batch's bound: in the ideal compression model with the bus's draw uniform after the commitment, the batch's draw `(ζ, ξ)` uniform after the commitment with the bus parts fixed but for `ζ`, and `ChecksGiveBatch`, the bound is the sum over the nodes of their reduction's `bad` and checks' `testBad` fractions, `epsPCS v`, `epsCR V (Q v)`, `4 N_v/|E|` and `(n_v + 66 + 1)/|E|`. -/
theorem tree_sound_ideal_batch [Fintype Ω₀] [Fintype X] [Fintype V] [Nonempty V] (T : TreeSound.Tree ι)
    (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (hr : ∀ v ∈ T.nodes, replayR (cert v).calls #[] 0 {} #[] = some (t v, os v))
    (hacc : ∀ v ∈ T.nodes, (cert v).accepts (os v) = true) (hver : ∀ v ∈ T.nodes, (cert v).verifies (os v) = true)
    (L : Layout) (hL : ∀ v ∈ T.nodes, (cert v).layout = L)
    (slot : ι → ℕ) (hslot : ∀ v ∈ T.nodes, v ≠ T.root → slot v < (cert (T.parent v)).children.length)
    (stRoot : Ω₀ × (X → Fin 4 → V) → ℕ → Fin 4 → K) (val : ι → Ω₀ × (X → Fin 4 → V) → Val)
    (hsroot : ∀ ω, Sat (stRoot ω) (t T.root) (val T.root ω)) (P : RecParts ι (Ω₀ × (X → Fin 4 → V)))
    (hP : P.Ok fun v ω => Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v))
      (val (T.parent v) ω))
    (n : ι → ℕ) (bdraw : (v : ι) → Ω₀ × (X → Fin 4 → V) → (Fin (n v) → E) × E)
    (aOf : (v : ι) → Ω₀ × (X → Fin 4 → V) → (Fin (n v) → E) → Fin 2 → E)
    (draw : ι → Ω₀ × (X → Fin 4 → V) → Fin 5 → E) (wit : ι → Ω₀ × (X → Fin 4 → V) → Witness)
    (hval : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, val v ω = assign (stmtFirst (t v)) (wit v ω))
    (hlink : ChecksGiveBatch T cert (fun v => stmtFirst (t v)) os L slot stRoot val P n bdraw aOf draw wit)
    (tD : Dense E → Prop) (tM : Matrix E → Prop) (bad : ι → Finset (Ω₀ × (X → Fin 4 → V)))
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v →
      stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω → ins cert val tD tM v ω)
    (hroot : ∀ ω, stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM T.root ω)
    (ch : X → C) (re : X → R) (hinj : ∀ x y, re x = re y → ch x = ch y → x = y)
    (σ : ι → Ω₀ → List (Fin 4 → V) → X) (Q : ι → ℕ) (hcrEq : ∀ v, P.crBad v = crEvent ch re (σ v) (Q v))
    (put : ι → Ω₀ × (X → Fin 4 → V) → (Fin 5 → E) → Ω₀ × (X → Fin 4 → V))
    (hgp : ∀ v ω x, draw v (put v ω x) = x) (hpg : ∀ v ω, put v ω (draw v ω) = ω)
    (hpp : ∀ v ω x y, put v (put v ω x) y = put v ω y) (hwit : ∀ v ω x, wit v (put v ω x) = wit v ω)
    (hfit : ∀ v ω T', (wit v ω).height T' ≤ 2 ^ 32) (N : ι → ℕ) (hN : ∀ v ω, (slots (wit v ω)).length ≤ N v)
    (bput : (v : ι) → Ω₀ × (X → Fin 4 → V) → (Fin (n v) → E) × E → Ω₀ × (X → Fin 4 → V))
    (bgp : ∀ v ω x, bdraw v (bput v ω x) = x) (bpg : ∀ v ω, bput v ω (bdraw v ω) = ω)
    (bpp : ∀ v ω x y, bput v (bput v ω x) y = bput v ω y) (bwit : ∀ v ω x, wit v (bput v ω x) = wit v ω)
    (baOf : ∀ v ω x, aOf v (bput v ω x) = aOf v ω) (htau : ∀ v ω T', tauOf (wit v ω) T' ≤ n v)
    (epsPCS : ι → ℚ≥0) (hpcs : PcsBound P epsPCS) :
    (Finset.card {ω | ∃ v ∈ T.nodes, ¬ (stmt T cert slot L (treeStmt T cert slot stRoot val) tD tM v ω ∧
        ins cert val tD tM v ω)} : ℚ≥0) / Fintype.card (Ω₀ × (X → Fin 4 → V)) ≤
      ∑ v ∈ T.nodes, (((bad v).card + ∑ j ∈ range (P.J v), (P.testBad v j).card : ℚ≥0) /
        Fintype.card (Ω₀ × (X → Fin 4 → V)) + epsPCS v + Edges.epsCR V (Q v) +
        ((4 * N v : ℕ) : ℚ≥0) / Fintype.card E + ((n v + allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E) :=
  tree_sound_ideal T cert t os hr hacc hver L hL slot hslot stRoot val hsroot P hP
    (fun v => batchBad (wit v) (aOf v) (bdraw v)) draw wit hval
    (checksGiveRows_of_batch T cert (fun v => stmtFirst (t v)) os L slot stRoot val P n bdraw aOf draw wit hlink) tD tM bad hstep hroot
    ch re hinj σ Q hcrEq put hgp hpg hpp hwit hfit N hN epsPCS
    (fun v => ((n v + allIds.length + 1 : ℕ) : ℚ≥0) / Fintype.card E) hpcs
    (fun v _ => batchBad_frac (wit v) (aOf v) (bdraw v) (bput v) (bgp v) (bpg v) (bpp v) (bwit v) (baOf v)
      (htau v))

end Ideal

end LeanVMCircuits.Rec.AirLink
