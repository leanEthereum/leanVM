/-
The link with the pinning lemma (Lemma 4.11 of the paper, `Protocol/Pinning.lean`): the hypothesis
"at most one list member matches all answers" of the transitions M1 and M3 is the conclusion of
Lemma 4.11 for points outside `Protocol.NonSep`, the set of point vectors that do not separate the
list. So M1 and M3 hold for every point vector that is separating, whatever the answers.
-/
import Rounds.Query
import Protocol.Pinning

open Polynomial Finset
open scoped Classical

namespace Rounds

open DeepFold Protocol

variable {K : Type*} [Field K] [Fintype K] {ι : Type*} [Fintype ι]

/-- `InList` is membership in the finite set `Protocol.listW`, the list `List(O; A, d)` of
Definition 2.1 of the paper. -/
theorem inList_iff_mem_listW {D : Finset K} {O : K → ι → K} {d A : ℕ} {U : ι → K[X]} :
    InList D O d A U ↔ U ∈ listW D O d A :=
  mem_listW.symm

/-- Separating points pin at most one list member for every answer vector (the last sentence of
Lemma 4.11 of the paper). -/
theorem sep_of_not_mem_nonSep {D : Finset K} {O : K → ι → K} {d A : ℕ} {ex : ι → ℕ} {s : ℕ}
    {z : Fin s → K × K} (hz : z ∉ NonSep (listW D O d A) ex s) (y : Fin s → K) :
    ∀ U U' : ι → K[X], InList D O d A U → InList D O d A U' →
      (∀ m, evL ex (z m) U = y m) → (∀ m, evL ex (z m) U' = y m) → U = U' :=
  fun _ _ hU hU' h h' =>
    pinned_unique hz y (inList_iff_mem_listW.mp hU) (inList_iff_mem_listW.mp hU') h h'

/-- **Transition M1 for separating points**: `batch_transition` with its separation hypothesis
discharged by Lemma 4.11's conclusion `z ∉ NonSep(List(O; A, d))`. -/
theorem batch_transition_pinned (D : Finset K) (O : K → ι → K) (d A : ℕ) (ex : ι → ℕ) {s : ℕ}
    {z : Fin s → K × K} (hz : z ∉ NonSep (listW D O d A) ex s) (y : Fin s → K) {J : ℕ}
    (Wk : Fin J → (ι → K[X]) →ₗ[K] K) (ck : Fin J → K) (B : (ι → K[X]) → Prop)
    (hfalse : ∀ U : ι → K[X], InList D O d A U → B U → (∀ m, evL ex (z m) U = y m) →
      ∃ k, Wk k U ≠ ck k) :
    (univ.filter (fun l : K =>
      ¬ Doomed D O d A ex z y (batchW Wk l) (batchC ck l) B)).card ≤ J - 1 :=
  batch_transition D O d A ex z y Wk ck B (sep_of_not_mem_nonSep hz y) hfalse

/-- **Transition M3 for separating points**: `query_transition` with its separation hypothesis
discharged by Lemma 4.11's conclusion for the points of the next level. -/
theorem query_transition_pinned [CharP K 2] (D : Finset K) (w : K → K) (d A : ℕ) {s : ℕ}
    (ζ v : Fin s → K) (W : K[X] →ₗ[K] K) (σ : K) (B : K[X] → Prop)
    (hI : Doomed₁ D w d A ζ v W σ B)
    (D' : Finset K) (O' : K → ι → K) (d' A' : ℕ) (ex' : ι → ℕ) {s' : ℕ}
    {z' : Fin s' → K × K} (hz' : z' ∉ NonSep (listW D' O' d' A') ex' s') (y' : Fin s' → K)
    (low : (ι → K[X]) →ₗ[K] K[X]) (C : K[X])
    (hdeg : ∀ U : ι → K[X], InList D' O' d' A' U → (low U + C).natDegree ≤ d)
    (hWC : W C = 0) (t : ℕ) :
    (((Fintype.piFinset (fun _ : Fin t => D)) ×ˢ (univ : Finset K)).filter
      (fun xl : (Fin t → K) × K =>
        ¬ Doomed D' O' d' A' ex' z' y' (nextW W low ζ xl.1 xl.2) (nextC σ C w ζ v xl.1 xl.2)
          (fun U => B (low U + C)))).card ≤
      (A - 1) ^ t * Fintype.card K + D.card ^ t * (s + t) :=
  query_transition D w d A ζ v W σ B hI D' O' d' A' ex' z' y' (sep_of_not_mem_nonSep hz' y')
    low C hdeg hWC t

end Rounds
