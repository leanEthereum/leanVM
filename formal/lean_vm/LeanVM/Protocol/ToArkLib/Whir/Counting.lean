/-
  LeanVM.Protocol.ToArkLib.Whir.Counting

  Small counts for a round-by-round soundness analysis: independent queries landing in a set, a
  union bound over a list, power batching of a nonzero discrepancy, and agreement of two distinct
  low-degree polynomials. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToCompPoly.PowerBatching
public import Mathlib.Data.Fintype.Pi

/-!
# Counting lemmas for WHIR

Count forms of the elementary steps of the proof of Annex B, `thm:rbr`, of the leanVM
specification (leanVM `127510d1`, `doc/leanvm/body/b-polynomial-commitment-scheme.tex`):

* `card_forall_mem`, `card_forall_mem_fin`: the query step. Of the `|ι|^t` query vectors
  `x : Fin t → ι`, exactly `|A|^t` land in `A` at every query, the count behind the error
  `(1 - γ)^t` when `A` is the agreement set of a far word.
* `card_filter_exists_le`: the union bound over a finite list, used for the batching and fold
  challenges with one bad set per list member.
* `card_powerBatch_eq_zero_le`: the batching step. A discrepancy vector `d : Fin J → F` that is
  not identically zero has `Σ_t λ^t d_t = 0` at at most `J - 1` values `λ`, from
  `card_false_batch_le` of `LeanVM.Protocol.ToCompPoly.PowerBatching`.
* `card_polyEval_eq_le`, `card_quadratic_eq_le`: the fold step's sumcheck part. Two distinct
  coefficient vectors of length `d + 1` agree as polynomials at at most `d` points; for degree
  `2` in Horner form `c₀ + x (c₁ + x c₂)`, at at most `2` points. The sumcheck round's message
  form is `LeanVM.Protocol.SumcheckRound.card_filter_evaluate_eq_le`.
-/

namespace LeanVM.Protocol.Whir

open Finset

@[expose] public section

/-! ## Queries -/

/-- **Query count.** Exactly `|A|^|Q|` maps `Q → ι` land in `A` at every point of `Q`. -/
theorem card_forall_mem {Q ι : Type*} [Fintype Q] [DecidableEq Q] [Fintype ι] [DecidableEq ι]
    (A : Finset ι) [DecidablePred fun x : Q → ι ↦ ∀ q, x q ∈ A] :
    (univ.filter fun x : Q → ι ↦ ∀ q, x q ∈ A).card = A.card ^ Fintype.card Q := by
  classical
  have h : (univ.filter fun x : Q → ι ↦ ∀ q, x q ∈ A) = Fintype.piFinset fun _ ↦ A := by
    ext x
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

/-- **Query count, `t` queries.** Exactly `|A|^t` query vectors `x : Fin t → ι` land in `A`
at every query. -/
theorem card_forall_mem_fin {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Finset ι) (t : ℕ)
    [DecidablePred fun x : Fin t → ι ↦ ∀ q, x q ∈ A] :
    (univ.filter fun x : Fin t → ι ↦ ∀ q, x q ∈ A).card = A.card ^ t := by
  rw [card_forall_mem, Fintype.card_fin]

/-! ## Union bound -/

/-- **Union bound over a list.** If each member of `L` has at most `N` bad challenges, at most
`|L| N` challenges are bad for some member. -/
theorem card_filter_exists_le {X G : Type*} [Fintype G] [DecidableEq G] (L : Finset X)
    (bad : X → G → Prop) [∀ U, DecidablePred (bad U)] [DecidablePred fun s ↦ ∃ U ∈ L, bad U s]
    {N : ℕ} (h : ∀ U ∈ L, (univ.filter (bad U)).card ≤ N) :
    (univ.filter fun s ↦ ∃ U ∈ L, bad U s).card ≤ L.card * N := by
  classical
  calc
    _ ≤ (L.biUnion fun U ↦ univ.filter (bad U)).card :=
      Finset.card_le_card fun s hs ↦ by
        obtain ⟨U, hU, hb⟩ := (Finset.mem_filter.mp hs).2
        exact Finset.mem_biUnion.mpr ⟨U, hU, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
    _ ≤ ∑ U ∈ L, (univ.filter (bad U)).card := Finset.card_biUnion_le
    _ ≤ L.card * N := by simpa using Finset.sum_le_card_nsmul L _ N h

/-! ## Polynomial agreement -/

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Batching count.** A discrepancy vector `d : Fin J → F` that is not identically zero has
`Σ_t d_t λ^t = 0` at at most `J - 1` values of `λ`. -/
theorem card_powerBatch_eq_zero_le {J : ℕ} (d : Fin J → F) (h : ∃ t, d t ≠ 0) :
    (univ.filter fun l : F ↦ ∑ t : Fin J, d t * l ^ t.val = 0).card ≤ J - 1 := by
  have := card_false_batch_le d 0 (by simpa using h)
  simpa [powerBatch] using this

/-- **Low-degree agreement count.** Two distinct coefficient vectors of length `d + 1` give
polynomials agreeing at at most `d` points. -/
theorem card_polyEval_eq_le {d : ℕ} (c c' : Fin (d + 1) → F) (hne : c ≠ c') :
    (univ.filter fun x : F ↦ ∑ i : Fin (d + 1), c i * x ^ i.val =
        ∑ i : Fin (d + 1), c' i * x ^ i.val).card ≤ d := by
  have h : ∃ i, c i ≠ c' i := by
    by_contra hall
    exact hne (funext fun i ↦ not_not.mp fun hi ↦ hall ⟨i, hi⟩)
  have hb := card_false_batch_le c c' h
  simp only [powerBatch, Nat.add_sub_cancel] at hb
  refine le_of_eq_of_le ?_ hb
  congr 1

/-- **Quadratic agreement count.** Two distinct polynomials of degree at most `2`, given by their
coefficient vectors in Horner form `c₀ + x (c₁ + x c₂)`, agree at at most `2` points. -/
theorem card_quadratic_eq_le (c c' : Fin 3 → F) (hne : c ≠ c') :
    (univ.filter fun x : F ↦ c 0 + x * (c 1 + x * c 2) = c' 0 + x * (c' 1 + x * c' 2)).card ≤
      2 := by
  have hform (e : Fin 3 → F) (x : F) :
      e 0 + x * (e 1 + x * e 2) = ∑ i : Fin 3, e i * x ^ i.val := by
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two]
    ring
  simpa only [hform] using card_polyEval_eq_le (d := 2) c c' hne

end Field

end
end LeanVM.Protocol.Whir
