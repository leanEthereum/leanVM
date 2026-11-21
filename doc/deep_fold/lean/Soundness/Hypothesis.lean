/-
The hypothesis `ListBound` (Hypothesis 5.1 of the paper) from the library `Interleave`, and the
numbers of level 0.

- `Level.OK.of_rsListBound`: the standing assumptions of a level whose domain lies in a subfield
  `F`, from a list bound of `Interleave` (`RSListBound`, for every lane count) at the level's
  first threshold.
- `Level.HK`: the hypothesis for single-lane words with values in the subfield (`H_K`,
  Hypothesis 6.4), at an agreement above `(n + 3d)/4` or with a list size at most half the
  subfield: in both cases lanes and the extension cost a factor two (Theorem 6.1,
  Proposition 6.2). `protocolD_sound_of_HK` is the soundness of the model under it.
- `Level.Unique`: the unique-decoding range, where the hypothesis is a theorem.
  `protocolD_sound_unique` has no list hypothesis at all, and `protocolD_sound_concrete_unique`
  instantiates it on a concrete level over a field of `2^128` elements with its domain in
  `GF(2^64)`: the hypotheses of the soundness theorem are satisfiable together. The level is not
  a deployed parameter set. `protocolD_sound_concrete_ladder` does the same on two levels with a
  tail of two rounds, so that a run has a message of every row M0 to M5.
- `err_level0`: at `q = 2^128`, twelve points, list `2^40`, `K₀ = 2^9 q`, `τ = 2^-119`, the
  point message of level 0 has error at most `2^-110`, a fold message at most `2^-118` (`2^-119`
  in the last round), the batching message at most `2^-119` for up to 512 claims and a tail
  round `2^-127` (Theorem 5.2 and Proposition 7.1), before their grinds.
-/
import Soundness.Sound
import Interleave.Axioms
import Protocol.Params

open Polynomial
open Finset hiding dens
open scoped Classical

namespace Soundness

open Protocol (Lane Word listW)

section Bridge

variable {F : Type*} [Field F] {K : Type} [Field K] [Fintype K] [Algebra F K]

/-- A list bound of the library `Interleave`, for words on points of the subfield `F`, bounds the
list `Protocol.listW` of a word whose domain is the image of those points. -/
theorem card_listW_le_of_rsListBound {D₀ : Finset F} {d A L r : ℕ}
    (h : Interleave.RSListBound D₀ K (Lane r) d A L) (O : Word K r) :
    (listW (D₀.image (algebraMap F K)) O d A).card ≤ L := by
  refine h.image O _ fun P hP => ?_
  obtain ⟨hdeg, hagr⟩ := Protocol.mem_listW.mp hP
  refine ⟨hdeg, hagr.trans (card_le_card fun x hx => ?_)⟩
  rw [Protocol.agrW, mem_filter] at hx
  exact Interleave.mem_agr.mpr ⟨hx.1, funext fun u => (hx.2 u).symm⟩

/-- Thresholds that grow are at least the first one. -/
theorem thr_zero_le {thr : ℕ → ℕ} (h : ∀ k, thr k + 1 ≤ thr (k + 1)) : ∀ k, thr 0 ≤ thr k
  | 0 => le_rfl
  | k + 1 => (thr_zero_le h k).trans ((Nat.le_succ _).trans (h k))

/-- The standing assumptions of a level whose domain is the image of points `D₀` of a subfield,
from a list bound of `Interleave` at the first threshold for every lane count up to `ℓ`. -/
theorem Level.OK.of_rsListBound {M : ℕ} (lv : Level K) (D₀ : Finset F)
    (hD : lv.D = D₀.image (algebraMap F K))
    (hRS : ∀ r, r ≤ lv.ℓ → Interleave.RSListBound D₀ K (Lane r) lv.d (lv.thr 0) lv.L)
    (hℓ : 1 ≤ lv.ℓ) (hne : D₀.Nonempty) (hMn : D₀.card.choose 2 ≤ M)
    (hthr : ∀ k, lv.thr k + 1 ≤ lv.thr (k + 1)) : lv.OK M where
  ell_pos := hℓ
  nonempty := by
    rw [hD]
    exact hne.image _
  choose_le := by
    rw [hD]
    exact (Nat.choose_le_choose 2 Finset.card_image_le).trans hMn
  thr_step := hthr
  listBound := by
    rw [hD]
    exact Protocol.listBound_level
      (fun r hr O' => card_listW_le_of_rsListBound (hRS r hr) O') (thr_zero_le hthr)

variable (F)

/-- **The single-lane hypothesis for a level** (`H_K`, Hypothesis 6.4 of the paper). The
domain is the image of points `D₀` of the subfield `F`; every word `F → F` has at most `L₁`
polynomials of degree at most `d` within agreement `A₀ = thr 0`; either `A₀ > (n + 3d)/4`
(Theorem 6.1) or `2 L₁ ≤ |F|` (Proposition 6.2); and the list size the level assumes is
`2 L₁ - 1`. With the standing assumptions that are not about lists. -/
def Level.HK [Fintype F] (M : ℕ) (lv : Level K) : Prop :=
  ∃ (D₀ : Finset F) (L₁ : ℕ), lv.D = D₀.image (algebraMap F K) ∧ D₀.Nonempty ∧
    D₀.card.choose 2 ≤ M ∧ 1 ≤ lv.ℓ ∧ (∀ k, lv.thr k + 1 ≤ lv.thr (k + 1)) ∧
    Interleave.RSListBound₁ D₀ lv.d (lv.thr 0) L₁ ∧ lv.d < lv.thr 0 ∧
    (D₀.card + 3 * lv.d < 4 * lv.thr 0 ∨ 2 * L₁ ≤ Fintype.card F) ∧ lv.L = 2 * L₁ - 1

/-- **The unique-decoding range for a level**: the domain is the image of points `D₀` of the
subfield, the first threshold is above `(n + d)/2`, and the list size the level assumes is one.
No hypothesis on lists. -/
def Level.Unique (M : ℕ) (lv : Level K) : Prop :=
  ∃ D₀ : Finset F, lv.D = D₀.image (algebraMap F K) ∧ D₀.Nonempty ∧ D₀.card.choose 2 ≤ M ∧
    1 ≤ lv.ℓ ∧ (∀ k, lv.thr k + 1 ≤ lv.thr (k + 1)) ∧ D₀.card + lv.d < 2 * lv.thr 0 ∧
    lv.d < lv.thr 0 ∧ lv.L = 1

variable {F}

/-- The single-lane hypothesis gives the standing assumptions, `ListBound` included: Theorem 6.1
of the paper (`Interleave.rs_interleave_two_mul`) or Proposition 6.2
(`Interleave.rs_descent₁_listBound`). -/
theorem Level.HK.ok [Fintype F] {M : ℕ} {lv : Level K} (h : lv.HK F M) : lv.OK M := by
  obtain ⟨D₀, L₁, hD, hne, hMn, hℓ, hthr, hH, hda, h4, hL⟩ := h
  have : Module.Finite F K := Module.Finite.of_finite
  refine Level.OK.of_rsListBound lv D₀ hD (fun r _ => ?_) hℓ hne hMn hthr
  rw [hL]
  rcases h4 with h4 | h2
  · exact Interleave.rs_interleave_two_mul K (Lane r) hH hda h4
  · exact Interleave.rs_descent₁_listBound K (Lane r) hH h2

/-- In the unique-decoding range the standing assumptions hold, `ListBound` included
(`Interleave.rsListBound₁_one` and `Interleave.rs_interleave_same`). -/
theorem Level.Unique.ok {M : ℕ} {lv : Level K} (h : lv.Unique F M) : lv.OK M := by
  obtain ⟨D₀, hD, hne, hMn, hℓ, hthr, h2, hda, hL⟩ := h
  have : Module.Finite F K := Module.Finite.of_finite
  refine Level.OK.of_rsListBound lv D₀ hD (fun r _ => ?_) hℓ hne hMn hthr
  rw [hL]
  exact Interleave.rs_interleave_same K (Lane r) (Interleave.rsListBound₁_one D₀ h2) hda
    (by omega)

variable (F) (T : Terminal K) {τ : ℚ} {K₀ M : ℕ}

/-- **Soundness of the model of Protocol 4.2 under the single-lane hypothesis.** The statement of
`protocolD_sound` with the hypothesis `ListBound` of every level replaced by `H_K`: a bound on
the lists of single words with values in the subfield `F` that contains the domain. -/
theorem protocolD_sound_of_HK [Fintype F] [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (rest : List (Level K))
    (hHK : ∀ l ∈ lv :: rest, l.HK F M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv rest)) :
    (protocolD K T J).winProb win n (Pos.commit lv rest) σ ≤
      budget T τ K₀ M J (Pos.commit lv rest) :=
  protocolD_sound T hτ hMq hΘ J lv rest (fun l hl => (hHK l hl).ok) n σ

/-- **Soundness of the model in the unique-decoding range, with no hypothesis on lists.** -/
theorem protocolD_sound_unique [CharP K 2] (hτ : 0 < τ) (hMq : 2 * Fintype.card K ≤ M)
    (hΘ : 0 < tripleThr K₀ M) (J : ℕ) (lv : Level K) (rest : List (Level K))
    (hU : ∀ l ∈ lv :: rest, l.Unique F M) (n : ℕ)
    (σ : (protocolD K T J).Strategy n (Pos.commit lv rest)) :
    (protocolD K T J).winProb win n (Pos.commit lv rest) σ ≤
      budget T τ K₀ M J (Pos.commit lv rest) :=
  protocolD_sound T hτ hMq hΘ J lv rest (fun l hl => (hU l hl).ok) n σ

end Bridge

section Level0

variable {K : Type} [Field K] [Fintype K]

/-- The point message of level 0 (`q = 2^128`, `d = 2^24 + 5`, six fold rounds, twelve points,
list `2^40`, `K₀ = 2^9 q`, `M = 2 q`, `τ = 2^-119`): error at most `2^-110`. -/
theorem errPoints_level0 (hq : Fintype.card K = 2 ^ 128) (lv : Level K)
    (hd : lv.d = 2 ^ 24 + 5) (hℓ : lv.ℓ = 6) (hs : lv.s = 12) (hL : lv.L = 2 ^ 40) :
    errPoints (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) lv ≤ 1 / 2 ^ 110 := by
  unfold errPoints
  rw [hd, hℓ, hs, hL, hq]
  exact Protocol.point_error_level0_arith

omit [Field K] in
/-- A fold message at `q = 2^128`, `K₀ = 2^9 q`, `τ = 2^-119`: error at most `2^-118`. -/
theorem errFold_level0 (hq : Fintype.card K = 2 ^ 128) (r : ℕ) :
    errFold K (1 / 2 ^ 119) (2 ^ 137) r ≤ 1 / 2 ^ 118 := by
  unfold errFold
  rw [hq]
  split_ifs
  · exact (add_zero _).le.trans (Protocol.fold_error_last_arith.trans (by norm_num))
  · exact Protocol.fold_error_arith

omit [Field K] in
/-- The last fold message of a level: error at most `2^-119`. -/
theorem errFold_level0_last (hq : Fintype.card K = 2 ^ 128) :
    errFold K (1 / 2 ^ 119) (2 ^ 137) 0 ≤ 1 / 2 ^ 119 := by
  unfold errFold
  rw [hq]
  simp only [↓reduceIte, add_zero]
  exact Protocol.fold_error_last_arith

/-- **The errors of the messages of level 0 at the deployed sizes**, before their grinds: over a
field of `2^128` elements, for a first level with `d = 2^24 + 5`, six fold rounds, twelve points
and list size `2^40`, with `K₀ = 2^9 q`, `M = 2 q`, `τ = 2^-119` and at most 512 input claims:
the point message has error at most `2^-110`, the batching message at most `2^-119`, a fold
message at most `2^-118`, and a tail round at most `2^-127`. -/
theorem err_level0 (hq : Fintype.card K = 2 ^ 128) (lv : Level K) (rest : List (Level K))
    (hd : lv.d = 2 ^ 24 + 5) (hℓ : lv.ℓ = 6) (hs : lv.s = 12) (hL : lv.L = 2 ^ 40) {J : ℕ}
    (hJ : J ≤ 512) :
    err (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) J (Pos.commit lv rest) ≤ 1 / 2 ^ 110 ∧
      (∀ O z, err (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) J (Pos.opening lv rest O z) ≤ 1 / 2 ^ 119) ∧
      (∀ k r O z v W σ G tru, err (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) J
        (Pos.fold lv rest k (r + 1) O z v W σ G tru) ≤ 1 / 2 ^ 118) ∧
      (∀ k O z v W σ G tru, err (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) J
        (Pos.fold lv rest k 1 O z v W σ G tru) ≤ 1 / 2 ^ 119) ∧
      ∀ r Wt ft σ ok ext tru, err (K := K) (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) J
        (Pos.tail (r + 1) Wt ft σ ok ext tru) ≤ 1 / 2 ^ 127 := by
  refine ⟨errPoints_level0 hq lv hd hℓ hs hL, fun O z => ?_,
    fun k r O z v W σ G tru => errFold_level0 hq r,
    fun k O z v W σ G tru => errFold_level0_last hq, fun r Wt ft σ ok ext tru => ?_⟩
  · simp only [err]
    rw [hq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h : ((J - 1 : ℕ) : ℚ) ≤ 511 := by exact_mod_cast (by omega : J - 1 ≤ 511)
    push_cast
    nlinarith
  · simp only [err]
    rw [hq]
    norm_num

end Level0

section Concrete

open Interleave (K64 E128)

noncomputable instance instFintypeK64 : Fintype K64 := Fintype.ofFinite _

noncomputable instance instFintypeE128 : Fintype E128 := Fintype.ofFinite _

instance instCharPE128 : CharP E128 2 :=
  charP_of_injective_algebraMap (algebraMap K64 E128).injective 2

theorem card_K64 : Fintype.card K64 = 2 ^ 64 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 64 (by norm_num)

theorem card_E128 : Fintype.card E128 = 2 ^ 128 := by
  rw [Fintype.card_eq_nat_card]
  exact Interleave.natCard_E128

/-- A concrete level over a field of `2^128` elements in the unique-decoding range: the whole of
`GF(2^64)` as domain, `d = 2^24 + 5`, six fold rounds, twelve points, 128 queries, thresholds
`A^{(0,k)} = 2^63 + 2^24 + k` and list size one. It is not a deployed parameter set: the degree
bound, the rounds and the points are those of leanVM's level 0, the domain and the thresholds are
not. -/
noncomputable def levelConcrete : Level E128 where
  D := (Finset.univ : Finset K64).image (algebraMap K64 E128)
  d := 2 ^ 24 + 5
  ℓ := 6
  s := 12
  t := 128
  thr := fun k => 2 ^ 63 + 2 ^ 24 + k
  L := 1
  low := 0

theorem levelConcrete_unique : levelConcrete.Unique K64 (2 ^ 129) := by
  refine ⟨Finset.univ, rfl, Finset.univ_nonempty, ?_, by norm_num [levelConcrete],
    fun k => by simp only [levelConcrete]; omega, ?_, by norm_num [levelConcrete], rfl⟩
  · rw [Finset.card_univ, card_K64, Nat.choose_two_right]
    norm_num
  · rw [Finset.card_univ, card_K64]
    norm_num [levelConcrete]

/-- **The soundness theorem is not vacuous.** For the level `levelConcrete` over a field of
`2^128` elements (domain in `GF(2^64)`, unique-decoding thresholds, so that `ListBound` is a theorem),
with `K₀ = 2^9 q`, `M = 2 q`, `τ = 2^-119`, no tail and 512 input claims: for every prover
strategy and every number of rounds, the probability that the prover wins is at most the sum of
the errors of the verifier messages. No hypothesis is left. -/
theorem protocolD_sound_concrete_unique (n : ℕ)
    (σ : (protocolD E128 (Terminal.direct E128) 512).Strategy n (Pos.commit levelConcrete [])) :
    (protocolD E128 (Terminal.direct E128) 512).winProb win n (Pos.commit levelConcrete []) σ ≤
      budget (Terminal.direct E128) (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) 512
        (Pos.commit levelConcrete []) := by
  refine protocolD_sound_unique K64 (Terminal.direct E128) (by norm_num) ?_
    Protocol.threshold_level0_pos 512 levelConcrete [] (fun l hl => ?_) n σ
  · rw [card_E128]
    norm_num
  · rw [List.mem_singleton.mp hl]
    exact levelConcrete_unique

/-- The first two messages of that run have errors at most `2^-110` (points) and `2^-119`
(batching), and its fold messages at most `2^-118`: with list size one the bound of
`errPoints_level0`, stated for list size `2^40`, holds a fortiori. -/
theorem errPoints_levelConcrete :
    errPoints (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) levelConcrete ≤ 1 / 2 ^ 110 := by
  unfold errPoints
  rw [card_E128]
  simp only [levelConcrete]
  norm_num [Finset.sum_range_succ]

theorem card_levelConcrete_D : levelConcrete.D.card = 2 ^ 64 := by
  show ((Finset.univ : Finset K64).image (algebraMap K64 E128)).card = 2 ^ 64
  rw [Finset.card_image_of_injective _ (algebraMap K64 E128).injective, Finset.card_univ,
    card_K64]

/-- The query message of that run (128 queries at agreement `2^63 + 2^24 + 6` out of `2^64`) has
error at most `2^-127`. -/
theorem errQuery_levelConcrete : errQuery levelConcrete levelConcrete.ℓ ≤ 1 / 2 ^ 127 := by
  unfold errQuery
  rw [card_levelConcrete_D]
  simp only [levelConcrete]
  norm_num

/-- The sum of the errors of that run is at most `2^-109`. -/
theorem budget_levelConcrete_le :
    budget (Terminal.direct E128) (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) 512
        (Pos.commit levelConcrete []) ≤ 1 / 2 ^ 109 := by
  have h1 := errPoints_levelConcrete
  have h2 := errQuery_levelConcrete
  have hℓ : levelConcrete.ℓ = 6 := rfl
  have hν : (Terminal.direct E128).ν = 0 := rfl
  rw [budget_one_level, budgetFolds_eq (by rw [hℓ]; norm_num), card_E128, hℓ, hν]
  rw [hℓ] at h2
  norm_num at h1 h2 ⊢
  linarith

/-- **A statement with no hypothesis and an explicit number.** In the model of Protocol 4.2 on the
level `levelConcrete` over a field of `2^128` elements, with 512 input claims and no tail, every
prover strategy wins with probability at most `2^-109`, whatever the number of rounds: the
verifier accepts false input claims, or accepts a final polynomial from which the descent does not
reach a list member that satisfies the claims, with at most that probability. Strategies exist
(`strategy_nonempty_one_level`). This is the interactive bound, before Fiat-Shamir and before
any grind, on one level with no tail: it is not a deployed parameter set. -/
theorem protocolD_sound_concrete_unique_le (n : ℕ)
    (σ : (protocolD E128 (Terminal.direct E128) 512).Strategy n (Pos.commit levelConcrete [])) :
    (protocolD E128 (Terminal.direct E128) 512).winProb win n (Pos.commit levelConcrete []) σ ≤
      1 / 2 ^ 109 :=
  (protocolD_sound_concrete_unique n σ).trans budget_levelConcrete_le

/-- A second concrete level in the unique-decoding range, to follow `levelConcrete` on a ladder:
the same domain, `d = 2^20 + 5`, four fold rounds, twelve points, 128 queries, thresholds
`A^{(1,k)} = 2^63 + 2^20 + k`, list size one, and as `low` the first lane of a tuple. -/
noncomputable def levelConcrete₁ : Level E128 where
  D := (Finset.univ : Finset K64).image (algebraMap K64 E128)
  d := 2 ^ 20 + 5
  ℓ := 4
  s := 12
  t := 128
  thr := fun k => 2 ^ 63 + 2 ^ 20 + k
  L := 1
  low := LinearMap.proj (lane₀ 4)

theorem levelConcrete₁_unique : levelConcrete₁.Unique K64 (2 ^ 129) := by
  refine ⟨Finset.univ, rfl, Finset.univ_nonempty, ?_, by norm_num [levelConcrete₁],
    fun k => by simp only [levelConcrete₁]; omega, ?_, by norm_num [levelConcrete₁], rfl⟩
  · rw [Finset.card_univ, card_K64, Nat.choose_two_right]
    norm_num
  · rw [Finset.card_univ, card_K64]
    norm_num [levelConcrete₁]

/-- **Two levels and a tail, with no hypothesis.** For the ladder `levelConcrete`,
`levelConcrete₁` over a field of `2^128` elements, both in the unique-decoding range, with the
tail `Terminal.point` of two rounds, `K₀ = 2^9 q`, `M = 2 q`, `τ = 2^-119` and 512 input claims:
for every prover strategy and every number of rounds, the probability that the prover wins is at
most the sum of the errors of the verifier messages. A run has a message of every row M0 to M5 of
Theorem 5.2 of the paper: the queries at the level boundary (M3) and the tail rounds (M5), which
a run on one level with no tail lacks. Not a deployed parameter set. -/
theorem protocolD_sound_concrete_ladder (n : ℕ)
    (σ : (protocolD E128 (Terminal.point E128 2) 512).Strategy n
      (Pos.commit levelConcrete [levelConcrete₁])) :
    (protocolD E128 (Terminal.point E128 2) 512).winProb win n
        (Pos.commit levelConcrete [levelConcrete₁]) σ ≤
      budget (Terminal.point E128 2) (1 / 2 ^ 119) (2 ^ 137) (2 ^ 129) 512
        (Pos.commit levelConcrete [levelConcrete₁]) := by
  refine protocolD_sound_unique K64 (Terminal.point E128 2) (by norm_num) ?_
    Protocol.threshold_level0_pos 512 levelConcrete [levelConcrete₁] (fun l hl => ?_) n σ
  · rw [card_E128]
    norm_num
  · rcases List.mem_cons.mp hl with rfl | hl
    · exact levelConcrete_unique
    · rw [List.mem_singleton.mp hl]
      exact levelConcrete₁_unique

/-- The ladder fits: a tuple of `levelConcrete₁` encodes its first lane, of degree at most
`2^20 + 5`. -/
theorem ladderFits_concrete : ladderFits levelConcrete [levelConcrete₁] := by
  refine ⟨fun U hU => ?_, trivial⟩
  show (U (lane₀ 4)).natDegree ≤ 2 ^ 24 + 5
  exact (hU (lane₀ 4)).trans (by norm_num [levelConcrete₁])

/-- Strategies exist for that run, so `protocolD_sound_concrete_ladder` is not about an empty
set. -/
theorem strategy_nonempty_concrete_ladder (n : ℕ) :
    Nonempty ((protocolD E128 (Terminal.point E128 2) 512).Strategy n
      (Pos.commit levelConcrete [levelConcrete₁])) :=
  strategy_nonempty_ladder (Terminal.point E128 2) (Terminal.point_admitsZero 2) 512 levelConcrete
    [levelConcrete₁] ladderFits_concrete n

end Concrete

end Soundness
