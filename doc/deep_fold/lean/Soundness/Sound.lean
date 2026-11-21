/-
Soundness of the model of Protocol 4.2 of the paper from its round-by-round soundness: the sum of
the errors of the verifier messages of a run bounds the probability that a prover wins.

`budget` is that sum, as a function of the position: the errors of the messages still to come.
`rounds` counts them. The end statements are `protocolD_sound` (the winning condition `win`),
`protocolD_sound_plain` (Theorem 5.2: the verifier accepts although the input claims are false)
and `protocolD_sound_extract` (Theorem 5.6: the verifier accepts and the descent from the final
polynomial does not reach a tuple that satisfies the relation). They bound every prover strategy,
and `strategy_nonempty_ladder` shows that strategies exist on every ladder and with every tail
that satisfy two conditions on the abstract maps of the model.
-/
import Soundness.ProtocolD

open Polynomial
open Finset hiding dens
open scoped Classical

namespace Soundness

open Protocol (Lane Word dens)

variable {K : Type} [Field K] [Fintype K] (T : Terminal K) (τ : ℚ) (K₀ M : ℕ)

/-- The errors of `r` fold challenges of a level: `r (K₀ - 1)/q^2 + (r - 1) τ`. -/
noncomputable def budgetFolds (K : Type) [Fintype K] (τ : ℚ) (K₀ : ℕ) : ℕ → ℚ
  | 0 => 0
  | r + 1 => errFold K τ K₀ r + budgetFolds K τ K₀ r

/-- The errors of the messages from the end of the folds of a level on: the queries and the tail
if the level is the last, and otherwise the next level's points, the queries, the next level's
folds, and so on. `k` is the number of rounds the level has. -/
noncomputable def budgetEnd : Level K → ℕ → List (Level K) → ℚ
  | lv, k, [] => errQuery lv k + T.ν * (2 / (Fintype.card K : ℚ))
  | lv, k, lv' :: rest =>
      errPoints τ K₀ M lv' + (errQuery lv k + ((lv.s + lv.t : ℕ) : ℚ) / (Fintype.card K : ℚ)) +
        budgetFolds K τ K₀ lv'.ℓ + budgetEnd lv' lv'.ℓ rest

/-- **The budget of a position**: the sum of the errors of the verifier messages still to come. -/
noncomputable def budget (J : ℕ) : Pos K → ℚ
  | .commit lv rest =>
      errPoints τ K₀ M lv + ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) + budgetFolds K τ K₀ lv.ℓ +
        budgetEnd T τ K₀ M lv lv.ℓ rest
  | .opening lv rest _ _ =>
      ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) + budgetFolds K τ K₀ lv.ℓ +
        budgetEnd T τ K₀ M lv lv.ℓ rest
  | .fold lv rest k r _ _ _ _ _ _ _ => budgetFolds K τ K₀ r + budgetEnd T τ K₀ M lv (k + r) rest
  | .boundary lv k _ _ _ _ _ _ _ lv' rest _ _ =>
      errQuery lv k + ((lv.s + lv.t : ℕ) : ℚ) / (Fintype.card K : ℚ) +
        budgetFolds K τ K₀ lv'.ℓ + budgetEnd T τ K₀ M lv' lv'.ℓ rest
  | .tail r _ _ _ _ _ _ => r * (2 / (Fintype.card K : ℚ))
  | .done _ _ _ => 0

variable {τ K₀ M}

theorem errPoints_nonneg (hτ : 0 ≤ τ) (lv : Level K) : 0 ≤ errPoints τ K₀ M lv := by
  unfold errPoints
  have h : ∀ j, 0 ≤ τ⁻¹ ^ j := fun j => pow_nonneg (inv_nonneg.mpr hτ) j
  have hs : 0 ≤ ∑ j ∈ range lv.ℓ, τ⁻¹ ^ j := Finset.sum_nonneg fun j _ => h j
  positivity

theorem errFold_nonneg (hτ : 0 ≤ τ) (hK₀ : 1 ≤ K₀) (r : ℕ) : 0 ≤ errFold K τ K₀ r := by
  unfold errFold
  have h1 : (1 : ℚ) ≤ K₀ := by exact_mod_cast hK₀
  have h2 : 0 ≤ ((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2 := div_nonneg (by linarith) (by positivity)
  split_ifs <;> linarith

omit [Fintype K] in
theorem errQuery_nonneg (lv : Level K) (k : ℕ) : 0 ≤ errQuery lv k := by
  unfold errQuery
  positivity

theorem budgetFolds_nonneg (hτ : 0 ≤ τ) (hK₀ : 1 ≤ K₀) : ∀ r, 0 ≤ budgetFolds K τ K₀ r
  | 0 => le_rfl
  | r + 1 => add_nonneg (errFold_nonneg hτ hK₀ r) (budgetFolds_nonneg hτ hK₀ r)

theorem budgetEnd_nonneg (hτ : 0 ≤ τ) (hK₀ : 1 ≤ K₀) :
    ∀ (rest : List (Level K)) (lv : Level K) (k : ℕ), 0 ≤ budgetEnd T τ K₀ M lv k rest
  | [], lv, k => by
      have := errQuery_nonneg lv k
      unfold budgetEnd
      positivity
  | lv' :: rest, lv, k => by
      have h1 := errQuery_nonneg lv k
      have h2 := errPoints_nonneg (K₀ := K₀) (M := M) hτ lv'
      have h3 := budgetFolds_nonneg (K := K) hτ hK₀ lv'.ℓ
      have h4 := budgetEnd_nonneg hτ hK₀ rest lv' lv'.ℓ
      have h5 : (0 : ℚ) ≤ ((lv.s + lv.t : ℕ) : ℚ) / (Fintype.card K : ℚ) := by positivity
      unfold budgetEnd
      linarith

theorem budget_nonneg (hτ : 0 ≤ τ) (hK₀ : 1 ≤ K₀) (J : ℕ) (s : Pos K) :
    0 ≤ budget T τ K₀ M J s := by
  have hJ : (0 : ℚ) ≤ ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) := by positivity
  cases s with
  | commit lv rest =>
      have h1 := errPoints_nonneg (K₀ := K₀) (M := M) hτ lv
      have h2 := budgetFolds_nonneg (K := K) hτ hK₀ lv.ℓ
      have h3 := budgetEnd_nonneg T (M := M) hτ hK₀ rest lv lv.ℓ
      simp only [budget]
      linarith
  | opening lv rest O z =>
      have h2 := budgetFolds_nonneg (K := K) hτ hK₀ lv.ℓ
      have h3 := budgetEnd_nonneg T (M := M) hτ hK₀ rest lv lv.ℓ
      simp only [budget]
      linarith
  | fold lv rest k r O z v W σ G tru =>
      have h2 := budgetFolds_nonneg (K := K) hτ hK₀ r
      have h3 := budgetEnd_nonneg T (M := M) hτ hK₀ rest lv (k + r)
      simp only [budget]
      linarith
  | boundary lv k O z v W σ G tru lv' rest h z' =>
      have h1 := errQuery_nonneg lv k
      have h2 := budgetFolds_nonneg (K := K) hτ hK₀ lv'.ℓ
      have h3 := budgetEnd_nonneg T (M := M) hτ hK₀ rest lv' lv'.ℓ
      have h5 : (0 : ℚ) ≤ ((lv.s + lv.t : ℕ) : ℚ) / (Fintype.card K : ℚ) := by positivity
      simp only [budget]
      linarith
  | tail r Wt ft σ ok ext tru =>
      simp only [budget]
      positivity
  | done a e t => exact le_rfl

/-- The budget of a position is the error of its verifier message plus the budget of the
position that follows, whatever is sent. -/
theorem budget_step (J : ℕ) (s : Pos K) (p : Msg K T J s) (c : Chal K s) :
    err τ K₀ M J s + budget T τ K₀ M J (next K T J s p c) = budget T τ K₀ M J s := by
  cases s with
  | commit lv rest =>
      simp only [err, next, budget]
      ring
  | opening lv rest O z =>
      simp only [err, next, budget, Nat.zero_add]
      ring
  | fold lv rest k r O z v W σ G tru =>
      cases r with
      | succ r =>
          simp only [err, next, foldNext, budget, budgetFolds]
          rw [show k + 1 + r = k + (r + 1) by omega]
          ring
      | zero =>
          cases rest with
          | nil =>
              simp only [err, next, foldNext, budget, budgetFolds, budgetEnd, Nat.add_zero]
              ring
          | cons lv' rest =>
              simp only [err, next, foldNext, budget, budgetFolds, budgetEnd, Nat.add_zero]
              ring
  | boundary lv k O z v W σ G tru lv' rest h z' =>
      simp only [err, next, budget, Nat.zero_add]
      ring
  | tail r Wt ft σ ok ext tru =>
      cases r with
      | succ r =>
          simp only [err, next, tailNext, budget]
          push_cast
          ring
      | zero =>
          simp only [err, next, tailNext, budget]
          norm_num
  | done a e t =>
      simp only [err, next, budget]
      ring

omit [Field K] in
/-- The fold errors of a level with `r + 1` rounds: `(r + 1) (K₀ - 1)/q^2 + r τ`. -/
theorem budgetFolds_succ (r : ℕ) :
    budgetFolds K τ K₀ (r + 1) =
      (r + 1) * (((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2) + r * τ := by
  induction r with
  | zero => simp [budgetFolds, errFold]
  | succ r ih =>
      rw [budgetFolds, ih, errFold]
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      push_cast
      ring

/-- The budget of a run on one level: the points, the batching, the folds, the queries and the
tail. -/
theorem budget_one_level (J : ℕ) (lv : Level K) :
    budget T τ K₀ M J (.commit lv []) =
      errPoints τ K₀ M lv + ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) +
        budgetFolds K τ K₀ lv.ℓ + (errQuery lv lv.ℓ + T.ν * (2 / (Fintype.card K : ℚ))) := rfl

omit [Field K] in
/-- The fold errors of a level with `ℓ ≥ 1` rounds: `ℓ (K₀ - 1)/q^2 + (ℓ - 1) τ`. -/
theorem budgetFolds_eq {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    budgetFolds K τ K₀ ℓ =
      ℓ * (((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2) + ((ℓ - 1 : ℕ) : ℚ) * τ := by
  obtain ⟨r, rfl⟩ : ∃ r, ℓ = r + 1 := ⟨ℓ - 1, by omega⟩
  rw [budgetFolds_succ]
  push_cast
  simp

theorem one_le_of_tripleThr_pos (hΘ : 0 < tripleThr K₀ M) : 1 ≤ K₀ := by
  rcases Nat.eq_zero_or_pos K₀ with h | h
  · simp [tripleThr, h] at hΘ
  · exact h

/-- **Soundness of the model of Protocol 4.2** (the composition of Theorem 5.2 and Theorem 5.6 of
the paper over a whole run). Over a finite field of characteristic two, with analysis constants
`τ > 0`, `M ≥ 2q` and `K₀ (K₀ - 1) (K₀ - M) > 0`, on every ladder of levels that satisfies the
standing assumptions and the hypothesis `ListBound` (`Level.OK`): for every prover strategy and
every number of rounds, the probability that the prover wins (the verifier accepts, and it is not
the case that the final polynomial descends to a member of the level-0 list that matches the
commit-phase answers and satisfies all input claims) is at most the sum of the errors of Theorem 5.2
over the verifier messages of the run. -/
theorem protocolD_sound [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (rest : List (Level K))
    (hOK : ∀ l ∈ lv :: rest, l.OK M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv rest)) :
    (protocolD K T J).winProb win n (Pos.commit lv rest) σ ≤
      budget T τ K₀ M J (Pos.commit lv rest) :=
  (protocolD_rbr (T := T) τ K₀ M hτ hMq hΘ J).winProb_le (fun _ => budget T τ K₀ M J)
    (fun _ s => budget_nonneg T hτ.le (one_le_of_tripleThr_pos hΘ) J s)
    (fun _ s p c => (budget_step T J s p c).le) n (Pos.commit lv rest) σ hOK

/-- **Plain soundness** (Theorem 5.2 of the paper composed): the probability that the verifier
accepts although the input claims are false (no member of the level-0 list matches the commit-phase
answers and satisfies all input claims) is at most the sum of the errors. -/
theorem protocolD_sound_plain [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (rest : List (Level K))
    (hOK : ∀ l ∈ lv :: rest, l.OK M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv rest)) :
    (protocolD K T J).winProb winPlain n (Pos.commit lv rest) σ ≤
      budget T τ K₀ M J (Pos.commit lv rest) :=
  ((protocolD K T J).winProb_mono (win := winPlain) (win' := win) winPlain_le n _ σ).trans
    (protocolD_sound T hτ hMq hΘ J lv rest hOK n σ)

/-- **Knowledge soundness in the relativised form** (Theorem 5.6 of the paper composed): the
probability that the verifier accepts and the descent from the final polynomial does not reach a
member of the level-0 list that matches the commit-phase answers and satisfies all input claims is
at most the sum of the errors. -/
theorem protocolD_sound_extract [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (rest : List (Level K))
    (hOK : ∀ l ∈ lv :: rest, l.OK M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv rest)) :
    (protocolD K T J).winProb winExtract n (Pos.commit lv rest) σ ≤
      budget T τ K₀ M J (Pos.commit lv rest) :=
  ((protocolD K T J).winProb_mono (win := winExtract) (win' := win) winExtract_le n _ σ).trans
    (protocolD_sound T hτ hMq hΘ J lv rest hOK n σ)

/-- **Soundness of the model on one level**, with the sum written out: the point message, the
batching message, `ℓ` fold messages, the last query message and `ν` tail rounds. -/
theorem protocolD_sound_one_level [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (hOK : lv.OK M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv [])) :
    (protocolD K T J).winProb win n (Pos.commit lv []) σ ≤
      errPoints τ K₀ M lv + ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) +
        (lv.ℓ * (((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2) + ((lv.ℓ - 1 : ℕ) : ℚ) * τ) +
        (errQuery lv lv.ℓ + T.ν * (2 / (Fintype.card K : ℚ))) := by
  have h := protocolD_sound T hτ hMq hΘ J lv [] (fun l hl => by
    rw [List.mem_singleton.mp hl]
    exact hOK) n σ
  rwa [budget_one_level, budgetFolds_eq hOK.ell_pos] at h

/-- At a doomed position the verifier has a message to send: the probabilities above are over
nonempty sets. -/
theorem chal_nonempty_of_doomed (s : Pos K) (hd : doomed τ K₀ M s) : Nonempty (Chal K s) := by
  cases s with
  | commit lv rest => exact inferInstanceAs (Nonempty (Fin lv.s → K × K))
  | opening lv rest O z => exact inferInstanceAs (Nonempty K)
  | fold lv rest k r O z v W σ G tru =>
      cases r with
      | succ r => exact inferInstanceAs (Nonempty (K × K))
      | zero =>
          cases rest with
          | nil =>
              have := (hd.1 lv (List.mem_cons_self ..)).nonempty.to_subtype
              exact inferInstanceAs (Nonempty (Fin lv.t → lv.D))
          | cons lv' rest => exact inferInstanceAs (Nonempty (Fin lv'.s → K × K))
  | boundary lv k O z v W σ G tru lv' rest h z' =>
      have := hd.1.nonempty.to_subtype
      exact inferInstanceAs (Nonempty ((Fin lv.t → lv.D) × K))
  | tail r Wt ft σ ok ext tru =>
      cases r with
      | succ r => exact inferInstanceAs (Nonempty K)
      | zero => exact inferInstanceAs (Nonempty PUnit)
  | done a e t => exact inferInstanceAs (Nonempty PUnit)

/-- The positions of a run on one level. -/
def oneLevel : Pos K → Prop
  | .commit _ rest => rest = []
  | .opening _ rest _ _ => rest = []
  | .fold _ rest _ _ _ _ _ _ _ _ _ => rest = []
  | .boundary _ _ _ _ _ _ _ _ _ _ _ _ _ => False
  | .tail _ _ _ _ _ _ _ => True
  | .done _ _ _ => True

/-- **Prover strategies exist** for the model on one level with no tail (`Terminal.direct`),
for every number of rounds: the statements "for every strategy" above are not about an empty
set. (On a ladder, or with a tail, whether the prover has a hand-over or a final message depends
on the abstract maps `low` and `Terminal`; for the real encoder the honest prover has one, which
is completeness and is not formalized. `strategy_nonempty_ladder` below is the general case, under
one hypothesis on each of the two.) -/
theorem strategy_nonempty_one_level (J : ℕ) (lv : Level K) (n : ℕ) :
    Nonempty ((protocolD K (Terminal.direct K) J).Strategy n (Pos.commit lv [])) := by
  refine (protocolD K (Terminal.direct K) J).strategy_nonempty oneLevel (fun s hs => ?_)
    (fun s p c hs => ?_) n (Pos.commit lv []) rfl
  · cases s with
    | commit lv rest => exact ⟨fun _ _ => (0 : K)⟩
    | opening lv rest O z => exact ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
    | fold lv rest k r O z v W σ G tru =>
        cases r with
        | succ r => exact ⟨⟨0, 0, 0, 0, fun _ => 0⟩⟩
        | zero =>
            cases rest with
            | nil =>
                exact ⟨⟨0, by simp, by
                  simp only [Terminal.direct, one_mul]
                  exact (Fintype.sum_unique fun _ : Lane 0 => W fun _ => (0 : K[X])).symm⟩⟩
            | cons lv' rest => exact absurd hs (List.cons_ne_nil _ _)
    | boundary lv k O z v W σ G tru lv' rest h z' => exact hs.elim
    | tail r Wt ft σ ok ext tru =>
        cases r with
        | succ r => exact ⟨⟨0, by simp⟩⟩
        | zero => exact ⟨PUnit.unit⟩
    | done a e t => exact ⟨PUnit.unit⟩
  · cases s with
    | commit lv rest => exact hs
    | opening lv rest O z => exact hs
    | fold lv rest k r O z v W σ G tru =>
        cases r with
        | succ r => exact hs
        | zero =>
            cases rest with
            | nil => exact trivial
            | cons lv' rest => exact absurd hs (List.cons_ne_nil _ _)
    | boundary lv k O z v W σ G tru lv' rest h z' => exact hs.elim
    | tail r Wt ft σ ok ext tru =>
        cases r with
        | succ r => exact trivial
        | zero => exact trivial
    | done a e t => exact trivial

section Strategies

/-! ### Strategies exist on every ladder and with every tail

At every position but two the prover's message type is inhabited outright: a word, answers,
scalars, a round polynomial. The two exceptions are the typed messages.

- `FinalMsg` (the end of the last level) asks for a polynomial `P` with `⟨W, P⟩` the inner product
  of the tables of the tail at `P`. The tables are arbitrary functions of `(W, P)`, so there may
  be none (`finalMsg_isEmpty`). There is one if the tables of the zero polynomial have inner
  product zero (`Terminal.AdmitsZero`), as for no tail and for every tail whose tables represent
  the running weight.
- `Handover` (the end of a level that is not the last) asks for a next word `O'` and a high part
  `C` with `deg(low U + C) ≤ d` for every list member `U` of `O'`. The map `low` is an arbitrary
  linear map, so there may be none (`handover_isEmpty`). There is one, with `C = 0`, if `low` maps
  the tuples within the degree bound of the next level to polynomials within the degree bound of
  the level that ends (`Level.Fits`), as the real encoder does.

Under these two hypotheses a strategy exists from every position (`strategy_nonempty_of_fits`). -/

section

omit [Fintype K]

/-- The lane whose variables are all zero. -/
def lane₀ : ∀ r : ℕ, Lane r
  | 0 => ()
  | r + 1 => Sum.inl (lane₀ r)

/-- The level `lv'` fits the level `lv` before it: a tuple within the degree bound of `lv'`
encodes a polynomial within the degree bound of `lv`. -/
def Level.Fits (lv lv' : Level K) : Prop :=
  ∀ U : Lane lv'.ℓ → K[X], (∀ u, (U u).natDegree ≤ lv'.d) → (lv'.low U).natDegree ≤ lv.d

/-- Every level of the ladder `lv :: rest` after the first fits the level before it. -/
def ladderFits : Level K → List (Level K) → Prop
  | _, [] => True
  | lv, lv' :: rest => lv.Fits lv' ∧ ladderFits lv' rest

/-- The positions from which the levels still to come fit. -/
def Pos.Fits : Pos K → Prop
  | .commit lv rest => ladderFits lv rest
  | .opening lv rest _ _ => ladderFits lv rest
  | .fold lv rest _ _ _ _ _ _ _ _ _ => ladderFits lv rest
  | .boundary _ _ _ _ _ _ _ _ _ lv' rest _ _ => ladderFits lv' rest
  | .tail _ _ _ _ _ _ _ => True
  | .done _ _ _ => True

/-- The zero polynomial is a final message for the tail `T`: its tables have inner product
zero. -/
def Terminal.AdmitsZero : Prop :=
  ∀ W : (Lane 0 → K[X]) →ₗ[K] K, ∑ x, T.wtab W 0 x * T.ftab W 0 x = 0

theorem Terminal.direct_admitsZero : (Terminal.direct K).AdmitsZero := by
  intro W
  have h0 : W (fun _ => (0 : K[X])) = 0 := map_zero W
  simp [Terminal.direct, h0]

variable (K) in
/-- A tail with `ν` rounds whose tables represent the running weight: the terminal weight is
`⟨W, P⟩` at the all-zero vertex of the cube and zero elsewhere, the other table is constant one. -/
noncomputable def Terminal.point (ν : ℕ) : Terminal K where
  ν := ν
  wtab := fun W P x => if x = lane₀ ν then W (fun _ => P) else 0
  ftab := fun _ _ _ => 1

theorem Terminal.point_admitsZero (ν : ℕ) : (Terminal.point K ν).AdmitsZero := by
  intro W
  have h0 : W (fun _ => (0 : K[X])) = 0 := map_zero W
  simp [Terminal.point, h0]

/-- The final message can be missing: with no tail round, both tables constant one and the zero
running weight, `FinalMsg` asks for `0 = 1`. -/
theorem finalMsg_isEmpty (lv : Level K) :
    IsEmpty (FinalMsg K ⟨0, fun _ _ _ => 1, fun _ _ _ => 1⟩ lv 0) :=
  ⟨fun p => by simpa using p.hspec⟩

/-- The hand-over can be missing: if the first threshold of the next level is zero, every tuple
within its degree bound is in every list, and if `low` sends one of them above the degree bound of
the level that ends, no high part serves both it and the zero tuple. -/
theorem handover_isEmpty (lv lv' : Level K) (W : (Lane 0 → K[X]) →ₗ[K] K) (hthr : lv'.thr 0 = 0)
    {U : Lane lv'.ℓ → K[X]} (hU : ∀ u, (U u).natDegree ≤ lv'.d)
    (hlow : lv.d < (lv'.low U).natDegree) : IsEmpty (Handover K lv lv' W) := by
  refine ⟨fun h => ?_⟩
  have h0 := h.hdeg 0 ⟨fun u => by simp, by rw [hthr]; exact Nat.zero_le _⟩
  have h1 := h.hdeg U ⟨hU, by rw [hthr]; exact Nat.zero_le _⟩
  rw [map_zero, zero_add] at h0
  have h2 : (lv'.low U).natDegree ≤ lv.d := by
    have h3 := Polynomial.natDegree_sub_le (lv'.low U + h.C) h.C
    rw [add_sub_cancel_right] at h3
    exact h3.trans (max_le h1 h0)
  omega

end

/-- **Prover strategies exist from every position**, for every number of rounds, if the tail
admits the zero polynomial and the levels still to come fit: the prover sends zeros. So the
statements "for every strategy" above are not about an empty set, on any such ladder and with any
such tail. -/
theorem strategy_nonempty_of_fits (hT : T.AdmitsZero) (J : ℕ) (n : ℕ) (s : Pos K)
    (hs : s.Fits) : Nonempty ((protocolD K T J).Strategy n s) := by
  refine (protocolD K T J).strategy_nonempty Pos.Fits (fun s hs => ?_) (fun s p c hs => ?_) n s hs
  · cases s with
    | commit lv rest => exact ⟨fun _ _ => (0 : K)⟩
    | opening lv rest O z => exact ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
    | fold lv rest k r O z v W σ G tru =>
        cases r with
        | succ r => exact ⟨⟨0, 0, 0, 0, fun _ => 0⟩⟩
        | zero =>
            cases rest with
            | nil => exact ⟨⟨0, by simp, (map_zero W).trans (hT W).symm⟩⟩
            | cons lv' rest =>
                exact ⟨⟨fun _ _ => 0, 0, map_zero W, fun U hU => by
                  rw [add_zero]
                  exact hs.1 U hU.1⟩⟩
    | boundary lv k O z v W σ G tru lv' rest h z' => exact ⟨fun _ => (0 : K)⟩
    | tail r Wt ft σ ok ext tru =>
        cases r with
        | succ r => exact ⟨⟨0, by simp⟩⟩
        | zero => exact ⟨PUnit.unit⟩
    | done a e t => exact ⟨PUnit.unit⟩
  · cases s with
    | commit lv rest => exact hs
    | opening lv rest O z => exact hs
    | fold lv rest k r O z v W σ G tru =>
        cases r with
        | succ r => exact hs
        | zero =>
            cases rest with
            | nil => exact trivial
            | cons lv' rest => exact hs.2
    | boundary lv k O z v W σ G tru lv' rest h z' => exact hs
    | tail r Wt ft σ ok ext tru =>
        cases r with
        | succ r => exact trivial
        | zero => exact trivial
    | done a e t => exact trivial

/-- **Prover strategies exist on every ladder and with every tail** that fit: from the start of a
run on the ladder `lv :: rest`, for every number of rounds. -/
theorem strategy_nonempty_ladder (hT : T.AdmitsZero) (J : ℕ) (lv : Level K)
    (rest : List (Level K)) (h : ladderFits lv rest) (n : ℕ) :
    Nonempty ((protocolD K T J).Strategy n (Pos.commit lv rest)) :=
  strategy_nonempty_of_fits T hT J n (Pos.commit lv rest) h

end Strategies

section Rounds

omit [Fintype K]

/-- The number of verifier messages from the end of the folds of a level on. -/
def roundsEnd : List (Level K) → ℕ
  | [] => T.ν + 2
  | lv' :: rest => 2 + lv'.ℓ + roundsEnd rest

/-- The number of rounds still to come at a position. -/
def rounds : Pos K → ℕ
  | .commit lv rest => 2 + lv.ℓ + roundsEnd T rest
  | .opening lv rest _ _ => 1 + lv.ℓ + roundsEnd T rest
  | .fold _ rest _ r _ _ _ _ _ _ _ => r + roundsEnd T rest
  | .boundary _ _ _ _ _ _ _ _ _ lv' rest _ _ => 1 + lv'.ℓ + roundsEnd T rest
  | .tail r _ _ _ _ _ _ => r + 1
  | .done _ _ _ => 0

theorem roundsEnd_pos (rest : List (Level K)) : 2 ≤ roundsEnd T rest := by
  cases rest <;> simp only [roundsEnd] <;> omega

/-- A round consumes one round. -/
theorem rounds_next (J : ℕ) (s : Pos K) (p : Msg K T J s) (c : Chal K s) :
    rounds T (next K T J s p c) = rounds T s - 1 := by
  cases s with
  | commit lv rest => simp only [next, rounds]; omega
  | opening lv rest O z => simp only [next, rounds]; omega
  | fold lv rest k r O z v W σ G tru =>
      cases r with
      | succ r => simp only [next, foldNext, rounds]; omega
      | zero =>
          cases rest with
          | nil => simp only [next, foldNext, rounds, roundsEnd]; omega
          | cons lv' rest => simp only [next, foldNext, rounds, roundsEnd]; omega
  | boundary lv k O z v W σ G tru lv' rest h z' => simp only [next, rounds]; omega
  | tail r Wt ft σ ok ext tru =>
      cases r with
      | succ r => simp only [next, tailNext, rounds]; omega
      | zero => simp only [next, tailNext, rounds, Nat.zero_add, Nat.sub_self]
  | done a e t => simp only [next, rounds, Nat.zero_sub]

/-- With no round to come the protocol has ended. -/
theorem done_of_rounds_eq_zero (s : Pos K) (h : rounds T s = 0) :
    ∃ acc ext tru, s = .done acc ext tru := by
  cases s with
  | done a e t => exact ⟨a, e, t, rfl⟩
  | commit lv rest => exact absurd h (by simp only [rounds]; omega)
  | opening lv rest O z => exact absurd h (by simp only [rounds]; omega)
  | fold lv rest k r O z v W σ G tru =>
      have := roundsEnd_pos T rest
      exact absurd h (by simp only [rounds]; omega)
  | boundary lv k O z v W σ G tru lv' rest h' z' => exact absurd h (by simp only [rounds]; omega)
  | tail r Wt ft σ ok ext tru => exact absurd h (by simp only [rounds]; omega)

end Rounds

end Soundness
