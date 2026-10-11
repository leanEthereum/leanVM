import Whir.AuthenticatedResetSuffix
import Whir.AuthenticatedResetProbability

/-! Exact averaging of a random actual prefix and an independent full reset.
Tape coordinates are swapped by bijections; no accepted-prover goodness or
conditional independence of replies is an input to this law. -/
namespace Whir.AuthenticatedResetSupport
open Concrete Protocol CausalGame CausalProbability SamplingProbability AuthenticatedResetProbability

private theorem get_resetCoordinates {c : Config} (cut : Nat) (fresh base : Tape c)
    (qs : List (Coordinate c)) (q : Coordinate c) :
    get q (resetCoordinates cut fresh qs base) =
      if cut ≤ position q ∧ q ∈ qs then get q fresh else get q base := by
  induction qs generalizing base with
  | nil => simp [resetCoordinates]
  | cons r rs ih =>
    by_cases same : q = r
    · subst r
      by_cases later : cut ≤ position q
      · simp [resetCoordinates, ih, later]
      · simp [resetCoordinates, ih, later]
    · by_cases later : cut ≤ position r
      · simp [resetCoordinates, ih, later, same, get_set_ne _ _ _ _ same]
      · simp [resetCoordinates, ih, later, same]

private theorem levelCoordinate_visible {c : Config} (i : Fin c.folds.size) (q : Coordinate c)
    (member : q ∈ levelCoordinates c i.val) : q ∈ visibleCoordinates c := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨i.val, List.mem_range.mpr i.isLt, member⟩

private theorem coordinate_enumerated {c : Config} (q : Coordinate c) :
    q ∈ visibleCoordinates c ++ List.ofFn (fun j : Fin (c.logN - c.folds.toList.sum) => Coordinate.tail j) := by
  cases q with
  | initial => simp [visibleCoordinates]
  | fold i j =>
    apply List.mem_append_left
    apply levelCoordinate_visible i
    simp only [levelCoordinates, i.isLt, dite_true, List.mem_append]
    exact Or.inl (Or.inl (List.mem_ofFn.mpr ⟨j, rfl⟩))
  | ood i j =>
    apply List.mem_append_left
    apply levelCoordinate_visible i
    simp only [levelCoordinates, i.isLt, dite_true, List.mem_append]
    exact Or.inl (Or.inr (List.mem_ofFn.mpr ⟨j, rfl⟩))
  | query i =>
    apply List.mem_append_left
    apply levelCoordinate_visible i
    simp [levelCoordinates, i.isLt]
  | tail j => exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

def mixedTape {c : Config} (cut : Nat) (base fresh : Tape c) : Tape c :=
  (coordinates c).symm (fun q => if position q < cut then get q base else get q fresh)

@[simp] theorem get_mixedTape {c : Config} (cut : Nat) (base fresh : Tape c) (q : Coordinate c) :
    get q (mixedTape cut base fresh) = if position q < cut then get q base else get q fresh := by
  change ((coordinates c) ((coordinates c).symm _)) q = _
  simp

theorem resetSuffix_eq_mixedTape {c : Config} (cut : Nat) (base fresh : Tape c) :
    resetSuffix cut base fresh = mixedTape cut base fresh := by
  apply (coordinates c).injective
  funext q
  change get q _ = get q _
  rw [get_mixedTape]
  unfold resetSuffix
  rw [get_resetCoordinates]
  simp only [coordinate_enumerated, and_true]
  split_ifs <;> first | rfl | omega

/-- Swapping coordinates is an involution of the ENTIRE two-tape space. -/
def mixEquiv (c : Config) (cut : Nat) : Tape c × Tape c ≃ Tape c × Tape c where
  toFun p := (mixedTape cut p.1 p.2, mixedTape cut p.2 p.1)
  invFun p := (mixedTape cut p.1 p.2, mixedTape cut p.2 p.1)
  left_inv p := by
    apply Prod.ext <;> apply (coordinates c).injective <;> funext q
    all_goals change get q (mixedTape cut _ _) = get q _
    all_goals simp only [get_mixedTape]; split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext <;> apply (coordinates c).injective <;> funext q
    all_goals change get q (mixedTape cut _ _) = get q _
    all_goals simp only [get_mixedTape]; split_ifs <;> rfl

theorem resetSuffix_probability {c : Config} (cut : Nat) (event : Tape c → Prop) :
    probability (fun p : Tape c × Tape c => event (resetSuffix cut p.1 p.2)) = probability event := by
  simp only [resetSuffix_eq_mixedTape]
  exact (probability_equiv (mixEquiv c cut) (fun p => event p.1)).trans (product_left event)

def replaceEquiv {c : Config} (q : Coordinate c) : Tape c × Sample q ≃ Tape c × Sample q where
  toFun p := (set q p.1 p.2, get q p.1)
  invFun p := (set q p.1 p.2, get q p.1)
  left_inv p := by simp
  right_inv p := by simp

theorem replace_probability {c : Config} (q : Coordinate c) (event : Tape c → Prop) :
    probability (fun p : Tape c × Sample q => event (set q p.1 p.2)) = probability event :=
  (probability_equiv (replaceEquiv q) (fun p => event p.1)).trans (product_left event)

/-- Full reset/query replacement preserves the original verifier law when the
prefix is independently uniform; no first-accepted-prefix conditioning occurs. -/
theorem resetAndReplace_probability {c : Config} (cut : Nat) (q : Coordinate c) (event : Tape c → Prop) :
    probability (fun p : (Tape c × Tape c) × Sample q =>
      event (set q (resetSuffix cut p.1.1 p.1.2) p.2)) = probability event := by
  simp only [resetSuffix_eq_mixedTape]
  have mixed := probability_equiv (Equiv.prodCongr (mixEquiv c cut) (Equiv.refl (Sample q)))
    (fun p : (Tape c × Tape c) × Sample q => event (set q p.1.1 p.2))
  change probability (fun p : (Tape c × Tape c) × Sample q =>
    event (set q (mixedTape cut p.1.1 p.1.2) p.2)) = _ at mixed
  rw [mixed]
  let shuffle : (Tape c × Tape c) × Sample q ≃ (Tape c × Sample q) × Tape c :=
    { toFun := fun p => ((p.1.1, p.2), p.1.2)
      invFun := fun p => ((p.1.1, p.2), p.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have reordered := probability_equiv shuffle
    (fun p : (Tape c × Sample q) × Tape c => event (set q p.1.1 p.1.2))
  change probability (fun p : (Tape c × Tape c) × Sample q => event (set q p.1.1 p.2)) = _ at reordered
  rw [reordered, product_left (fun p : Tape c × Sample q => event (set q p.1 p.2))]
  exact replace_probability q event

def fullResetEquiv (input : Public) (level : Fin input.config.folds.size) (depth : Nat)
    (chunks : queryChunks input.config level =
      ((input.config.queries[level.val]! + 192 / depth - 1) / (192 / depth))) :
    Tape input.config × (RewindCoverage.QueryTape depth input.config.queries[level.val]! ×
      (E × Tape input.config)) ≃
        (Tape input.config × Tape input.config) × Sample (.query level) where
  toFun p := ((p.1, p.2.2.2), ((fun j => p.2.1 (Fin.cast chunks j)), p.2.2.1))
  invFun p := (p.1.1, ((fun j => p.2.1 (Fin.cast chunks.symm j)), (p.2.2, p.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact acceptance averaging for the implemented legal full-reset sampler,
not an assumed law on partially accepting prover answers. -/
theorem fullResetTape_probability (input : Public) (level : Fin input.config.folds.size)
    (depth : Nat) (chunks) (event : Tape input.config → Prop) :
    probability (fun p : Tape input.config ×
      (RewindCoverage.QueryTape depth input.config.queries[level.val]! × (E × Tape input.config)) =>
      event (fullResetTape input p.1 level depth chunks p.2.1 p.2.2)) = probability event := by
  have fact := probability_equiv (fullResetEquiv input level depth chunks)
    (fun p : (Tape input.config × Tape input.config) × Sample (.query level) =>
      event (set (.query level) (resetSuffix (position (.query level)) p.1.1 p.1.2) p.2))
  simpa only [fullResetTape, fullResetEquiv, Equiv.coe_fn_mk] using
    fact.trans (resetAndReplace_probability _ _ event)

#print axioms fullResetTape_probability

#print axioms resetSuffix_probability
#print axioms resetAndReplace_probability
end Whir.AuthenticatedResetSupport
