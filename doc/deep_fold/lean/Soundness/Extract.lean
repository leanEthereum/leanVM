/-
The extraction predicate of the model of Protocol 4.2 and the extractor step (Section 5.5 of the
paper).

In `Soundness/ProtocolD.lean` a position carries a predicate `G` on the tuples of its round: at
round 0 of level 0 it is `claimsHold` (a member of the list that matches the commit-phase answers
and satisfies every input claim), a fold round replaces it by `descend` (the tuple agrees with the
fold on at least `A` columns and a near tuple of the unfolded word on its agreement set satisfies
`G`), and a level boundary by `U ↦ G(low U + C)`. The winning condition `winExtract` is "the
verifier accepts and `G` fails on the final polynomial".

Here: under (S2), `d + 3 ≤ A`, the descent step is unique decoding. The near tuple is unique, it
is a member of the list of the previous round, and it folds to the tuple it was decoded from
(`Rounds.descent_step`). So `G` on the final polynomial says that the chain of tuples the
extractor of Section 5.5 computes (one near tuple a round, with at most one error on a known
set) ends in a member of the level-0 list that matches the answers and satisfies the claims; and
for good points that member is the one the commit-phase answers pin (`claimsHold_unique`,
Corollary 5.7).
-/
import Soundness.ProtocolD
import Rounds.Extract

open Polynomial
open Finset hiding dens
open scoped Classical

namespace Soundness

open DeepFold
open Protocol (Lane Word exL Good foldW)
open Rounds (InList NearT agr foldTuple pull)

variable {K : Type} [Field K]

/-- **The descent step is unique decoding** (the paragraph *Descent* of the proof of Theorem 5.6 of
the paper). Let `A ≥ d + 3` and let `P` have degree at most `d`. If `P` descends through the fold by
`c`, then `P` is in `List(O_c; A, d)` and there is a tuple `T` such that: `T` is a near tuple of the
unfolded word on the agreement set of `P`, and the only one; `T ∈ List(O; A - 1, d)`; `G(T)`; and
`P` is the fold of `T`. -/
theorem descend_step {D : Finset K} {d A : ℕ} (hdA : d + 3 ≤ A) {r : ℕ} (O : Word K (r + 1))
    (c : K × K) (G : (Lane (r + 1) → K[X]) → Prop) {P : Lane r → K[X]}
    (hP : ∀ u, (P u).natDegree ≤ d) (h : descend D d A O c G P) :
    InList D (foldW O c) d A P ∧
      ∃ T : Lane (r + 1) → K[X], NearT D O d (agr D (foldW O c) P) T ∧ InList D O d (A - 1) T ∧
        G T ∧ P = foldTuple c T ∧
        ∀ T' : Lane (r + 1) → K[X], NearT D O d (agr D (foldW O c) P) T' → T' = T := by
  have hnb : ¬ pull D O d A c (fun U => ¬ G U) P := fun hp =>
    (pull_not_iff D d A O c G P).mp hp h
  obtain ⟨hin, T, hT, hTin, hG, hfold, huniq⟩ :=
    Rounds.descent_step D O d A c (fun U => ¬ G U) hdA hP hnb
  exact ⟨hin, T, hT, hTin, not_not.mp hG, hfold, huniq⟩

/-- For `A ≥ d + 3` the descent reads "the near tuple satisfies `G`": `P` descends if and only if
it agrees with the fold on at least `A` columns, the unfolded word has a near tuple on its
agreement set, that near tuple is the only one, and it satisfies `G`. -/
theorem descend_iff_unique {D : Finset K} {d A : ℕ} (hdA : d + 3 ≤ A) {r : ℕ}
    (O : Word K (r + 1)) (c : K × K) (G : (Lane (r + 1) → K[X]) → Prop) (P : Lane r → K[X]) :
    descend D d A O c G P ↔ A ≤ (agr D (foldW O c) P).card ∧
      ∃ T : Lane (r + 1) → K[X], NearT D O d (agr D (foldW O c) P) T ∧
        (∀ T' : Lane (r + 1) → K[X], NearT D O d (agr D (foldW O c) P) T' → T' = T) ∧ G T := by
  constructor
  · rintro ⟨hA, T, hT, hG⟩
    exact ⟨hA, T, hT, fun T' hT' => Rounds.nearT_unique (hdA.trans hA) hT' hT, hG⟩
  · rintro ⟨hA, T, hT, _, hG⟩
    exact ⟨hA, T, hT, hG⟩

variable [Fintype K]

/-- **Corollary 5.7 of the paper, the uniqueness part**: for good points, at most one tuple
satisfies the level-0 extraction predicate, the member of the list that the commit-phase answers
pin. So when the descent succeeds it reaches that member, and that member satisfies every input
claim. -/
theorem claimsHold_unique {τ : ℚ} {Θ : ℕ} (lv : Level K) {J : ℕ} (O : Word K lv.ℓ)
    {z : Fin lv.s → K × K} (hz : Good τ lv.D lv.d lv.thr lv.s Θ lv.ℓ O z) (p : OpenMsg K lv J)
    {U U' : Lane lv.ℓ → K[X]} (hU : claimsHold lv O z p U) (hU' : claimsHold lv O z p U') :
    U = U' :=
  (Good.not_bad hz).1 p.y U U' hU.1 hU'.1 hU.2.1 hU'.2.1

end Soundness
