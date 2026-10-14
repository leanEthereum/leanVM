import Whir.CountedCandidateCheckOriginalCost

/-! Instrumented literal source squaring and six additive-map stages. The 75-operation public transformation charge is connected to the actual field-valued map, not an uninterpreted counter or an assumed backend. -/
namespace Whir.OriginalClaimsChecker
open Concrete RingPCSGame CountedCandidateCheck

set_option maxHeartbeats 4000000

def countedSquare (x : E) : Nat → E × Nat
  | 0 => (x, 0)
  | n + 1 => let y := countedSquare x n; (y.1 * y.1, y.2 + 1)

theorem countedSquare_value (x : E) (n : Nat) : (countedSquare x n).1 = squareIter x n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countedSquare, squareIter, ih]

theorem countedSquare_field (x : E) (n : Nat) : (countedSquare x n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [countedSquare, ih]

def countedMapStep (challenges : Fin 6 → E) (value : E) (j : Fin 6) : E × Nat :=
  let square := countedSquare value (2 ^ (5 - j.val))
  (value + challenges j * square.1, square.2 + 2)
private theorem countedMapStep_value (challenges : Fin 6 → E) (value : E) (j : Fin 6) :
    (countedMapStep challenges value j).1 = mapStage (challenges j) (2 ^ (5 - j.val)) value := by
  simp [countedMapStep, countedSquare_value, mapStage]
private theorem countedMapStep_field (challenges : Fin 6 → E) (value : E) (j : Fin 6) :
    (countedMapStep challenges value j).2 = 2 ^ (5 - j.val) + 2 := by
  simp [countedMapStep, countedSquare_field]

def countedMap (challenges : Fin 6 → E) (x : E) : E × Nat :=
  loop (countedMapStep challenges) (List.finRange 6) (x, 0)

private theorem composed_value (challenges : Fin 6 → E) (xs : List (Fin 6))
    (hom : E →+ E) (x : E) :
    (xs.foldl (fun φ j => (mapStage (challenges j) (2 ^ (5 - j.val))).comp φ) hom) x =
      xs.foldl (fun value j => mapStage (challenges j) (2 ^ (5 - j.val)) value) (hom x) := by
  induction xs generalizing hom with
  | nil => rfl
  | cons j xs ih =>
    simpa only [List.foldl_cons, AddMonoidHom.comp_apply] using
      (ih ((mapStage (challenges j) (2 ^ (5 - j.val))).comp hom))

theorem countedMap_value (challenges : Fin 6 → E) (x : E) :
    (countedMap challenges x).1 = executableMap challenges x := by
  rw [countedMap, loop_value]
  simp only [countedMapStep_value]
  exact (composed_value challenges (List.finRange 6) (AddMonoidHom.id E) x).symm

theorem countedMap_field (challenges : Fin 6 → E) (x : E) : (countedMap challenges x).2 = 75 := by
  have charge := loop_constant_charge (countedMapStep challenges)
    (fun j => 2 ^ (5 - j.val) + 2) (countedMapStep_field challenges) (List.finRange 6) (x, 0)
  have exactCharge : (countedMap challenges x).2 = mapField := by
    simpa only [countedMap, Nat.zero_add, mapField] using charge
  exact exactCharge.trans mapField_eq

#print axioms countedMap_value
#print axioms countedMap_field

end Whir.OriginalClaimsChecker
