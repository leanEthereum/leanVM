import Whir.BatchingRefinement
import Whir.TerminalRefinement

namespace Whir.AccumulatedTerminalAlgebra
open Concrete Protocol ArrayLayout ArrayAlgebra TerminalRefinement
open scoped BigOperators
variable {R : Type*} [CommRing R] [Inhabited R]

theorem mle_weightGlue (b other point : Array R) (s : R)
    (hb : b.size = 2 ^ point.size) (ho : other.size = b.size) :
    Concrete.mle (weightGlue b other s) point =
      Concrete.mle b point + s * Concrete.mle other point := by
  simp only [Concrete.mle, dot_eq_sum, size_weightGlue, size_eqTable, hb, ho, min_self]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [weightGlue, getElem!_tab _ _ _ (by simpa [hb] using Finset.mem_range.mp hi)]
  ring

theorem mle_scale (a point : Array R) (s : R) :
    Concrete.mle (a.map (s * ·)) point = s * Concrete.mle a point := by
  simp only [Concrete.mle, dot_eq_sum, Array.size_map, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have h : i < a.size := (Finset.mem_range.mp hi).trans_le (Nat.min_le_left ..)
  simp [getElem!_pos, h, mul_assoc]

theorem foldLow_eqTable_cons [CharP R 2] (z r : R) (zs : Array R) :
    foldLow (eqTable (#[z] ++ zs)) r = (eqTable zs).map ((1 + z + r) * ·) := by
  apply Array.ext
  · simp [pow_succ, Nat.add_comm]
  · intro i hi hi'
    have h : i < 2 ^ zs.size := by simpa using hi'
    have hz := eqTable_cons_get z zs i h
    suffices hh : (foldLow (eqTable (#[z] ++ zs)) r)[i]! =
        ((eqTable zs).map ((1 + z + r) * ·))[i]! by
      simpa only [getElem!_pos, hi, hi'] using hh
    rw [foldLow, getElem!_tab _ _ _ (by simpa only [size_foldLow] using hi), hz.1, hz.2]
    simp only [getElem!_pos, h, size_eqTable, Array.size_map, Array.getElem_map, foldPair]
    ring_nf
    simp [CharTwo.two_eq_zero]

def equalityProduct (z point : List R) : R :=
  ((z.zip point).map fun (a, b) => 1 + a + b).prod

theorem mle_eqTable [CharP R 2] (z point : List R) (h : z.length = point.length) :
    Concrete.mle (eqTable z.toArray) point.toArray = equalityProduct z point := by
  induction z generalizing point with
  | nil =>
    have hp : point = [] := by simpa using h.symm
    subst point
    simp [equalityProduct, mle_empty, eqTable_empty]
  | cons z zs ih =>
    cases point with
    | nil => simp at h
    | cons r rs =>
      have he : zs.length = rs.length := by simpa using h
      rw [show (z :: zs).toArray = #[z] ++ zs.toArray by simp,
        show (r :: rs).toArray = #[r] ++ rs.toArray by simp]
      rw [mle_cons _ _ _ (by simp [he]), foldLow_eqTable_cons, mle_scale]
      rw [ih rs he]
      simp [equalityProduct]

inductive Step (R : Type*) where
  | fold (r : R)
  | glue (weight : Array R) (beta : R)

def challenges : List (Step R) → List R
  | [] => []
  | .fold r :: xs => r :: challenges xs
  | .glue _ _ :: xs => challenges xs

def runDense : List (Step R) → Array R → Array R
  | [], b => b
  | .fold r :: xs, b => runDense xs (foldLow b r)
  | .glue w beta :: xs, b => runDense xs (weightGlue b w beta)

def Valid : List (Step R) → Nat → Prop
  | [], _ => True
  | .fold _ :: xs, n => Valid xs n
  | .glue w _ :: xs, n => w.size = 2 ^ ((challenges xs).length + n) ∧ Valid xs n

/-- The term inserted now is evaluated at precisely the future low-coordinate
suffix. No level-local coordinate permutation occurs. -/
def contributions (tail : List R) : List (Step R) → R
  | [] => 0
  | .fold _ :: xs => contributions tail xs
  | .glue w beta :: xs =>
      beta * Concrete.mle w ((challenges xs) ++ tail).toArray + contributions tail xs

theorem runDense_size (xs : List (Step R)) (b : Array R) (n : Nat)
    (hb : b.size = 2 ^ ((challenges xs).length + n)) :
    (runDense xs b).size = 2 ^ n := by
  induction xs generalizing b with
  | nil => simpa [runDense, challenges] using hb
  | cons x xs ih =>
    cases x with
    | fold r =>
      apply ih
      simp only [challenges, List.length_cons] at hb
      simp only [size_foldLow, hb]
      rw [show (challenges xs).length + 1 + n = ((challenges xs).length + n) + 1 by omega,
        pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
    | glue w beta => exact ih _ (by simpa [challenges] using hb)

theorem accumulated (xs : List (Step R)) (b : Array R) (tail : List R)
    (hb : b.size = 2 ^ ((challenges xs).length + tail.length)) (hv : Valid xs tail.length) :
    Concrete.mle (runDense xs b) tail.toArray =
      Concrete.mle b ((challenges xs) ++ tail).toArray + contributions tail xs := by
  induction xs generalizing b with
  | nil => simp [runDense, challenges, contributions]
  | cons x xs ih =>
    cases x with
    | fold r =>
      have hs : (foldLow b r).size = 2 ^ ((challenges xs).length + tail.length) := by
        simp only [challenges, List.length_cons] at hb
        simp only [size_foldLow, hb]
        rw [show (challenges xs).length + 1 + tail.length =
          ((challenges xs).length + tail.length) + 1 by omega,
          pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
      rw [runDense, ih _ hs hv]
      simp only [challenges, List.cons_append, contributions]
      rw [show (r :: (challenges xs ++ tail)).toArray =
        #[r] ++ (challenges xs ++ tail).toArray by simp]
      rw [mle_cons _ _ _ (by simpa [challenges, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hb)]
    | glue w beta =>
      obtain ⟨hw, hv⟩ := hv
      rw [runDense, ih _ (by simpa [challenges] using hb) hv]
      rw [mle_weightGlue _ _ _ _ (by simpa [challenges] using hb)
        (by simpa [challenges] using hw.trans hb.symm)]
      simp only [challenges, contributions, add_assoc]

structure Saved (R : Type*) where
  risStart : Nat
  weight : Array R
  beta : R

def save : List (Step R) → Nat → List (Saved R)
  | [], _ => []
  | .fold _ :: xs, start => save xs (start + 1)
  | .glue w beta :: xs, start => ⟨start, w, beta⟩ :: save xs start

def evalSaved (saved : List (Saved R)) (point : List R) : R :=
  (saved.map fun s => s.beta * Concrete.mle s.weight (point.drop s.risStart).toArray).sum

theorem save_chronology (xs : List (Step R)) (pre tail : List R) :
    evalSaved (save xs pre.length) (pre ++ challenges xs ++ tail) = contributions tail xs := by
  induction xs generalizing pre with
  | nil => simp [save, evalSaved, contributions]
  | cons x xs ih =>
    cases x with
    | fold r =>
      simpa [save, challenges, contributions, List.append_assoc] using ih (pre ++ [r])
    | glue w beta =>
      simp only [save, evalSaved, List.map_cons, List.sum_cons, challenges, contributions]
      rw [show (pre ++ challenges xs ++ tail).drop pre.length = challenges xs ++ tail by
        rw [List.append_assoc, List.drop_left]]
      exact congrArg (beta * Concrete.mle w (challenges xs ++ tail).toArray + ·) (ih pre)

theorem terminal (xs : List (Step R)) (b : Array R)
    (hb : b.size = 2 ^ (challenges xs).length) (hv : Valid xs 0) :
    (runDense xs b)[0]! = Concrete.mle b (challenges xs).toArray +
      evalSaved (save xs 0) (challenges xs) := by
  have h := accumulated xs b [] (by simpa using hb) hv
  rw [mle_empty _ (by simpa using runDense_size xs b 0 (by simpa using hb))] at h
  simp only [List.append_nil] at h
  rw [← save_chronology xs [] []] at h
  simpa using h

end Whir.AccumulatedTerminalAlgebra
