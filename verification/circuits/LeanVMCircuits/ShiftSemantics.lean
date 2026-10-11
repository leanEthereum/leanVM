module

public import LeanVMCircuits.WordMux

@[expose] public section

namespace LeanVMCircuits.Words

variable {α β : Type} {n : ℕ}

def filled (bits : Vector α n) (fill : α) (i : ℕ) : α :=
  if h : i < n then bits[i] else fill

def right (amount : ℕ) (fill : α) (bits : Vector α n) : Vector α n :=
  Vector.mapFinRange n fun i => filled bits fill (i.val + amount)

theorem right_zero (fill : α) (bits : Vector α n) : right 0 fill bits = bits := by
  apply Vector.ext
  intro i hi
  simp [right, filled, Vector.getElem_mapFinRange]

theorem right_add (a b : ℕ) (fill : α) (bits : Vector α n) :
    right a fill (right b fill bits) = right (a + b) fill bits := by
  apply Vector.ext
  intro i hi
  simp only [right, Vector.getElem_mapFinRange]
  by_cases h : i + a < n
  · simp [filled, h, Vector.getElem_mapFinRange, Nat.add_assoc]
  · have hab : ¬ i + (a + b) < n := by omega
    simp [filled, h, hab]

theorem right_map (f : α → β) (amount : ℕ) (fill : α) (bits : Vector α n) :
    (right amount fill bits).map f = right amount (f fill) (bits.map f) := by
  apply Vector.ext
  intro i hi
  simp only [right, Vector.getElem_map, Vector.getElem_mapFinRange, filled]
  split <;> simp

def reverse (bits : Vector α n) : Vector α n :=
  Vector.mapFinRange n fun i => bits[n - 1 - i.val]'(by omega)

theorem reverse_map (f : α → β) (bits : Vector α n) :
    (reverse bits).map f = reverse (bits.map f) := by
  apply Vector.ext
  intro i hi
  simp [reverse, Vector.getElem_mapFinRange]

theorem reverse_reverse (bits : Vector α n) : reverse (reverse bits) = bits := by
  apply Vector.ext
  intro i hi
  simp only [reverse, Vector.getElem_mapFinRange]
  congr 1
  omega

def left (amount : ℕ) (fill : α) (bits : Vector α n) : Vector α n :=
  Vector.mapFinRange n fun i => if h : amount ≤ i.val then bits[i.val - amount]'(by omega) else fill

theorem reverse_right (amount : ℕ) (fill : α) (bits : Vector α n) :
    reverse (right amount fill (reverse bits)) = left amount fill bits := by
  apply Vector.ext
  intro i hi
  simp only [reverse, right, filled, left, Vector.getElem_mapFinRange]
  by_cases h : amount ≤ i
  · have hr : n - 1 - i + amount < n := by omega
    simp only [h, hr, dif_pos]
    congr 1
    omega
  · have hr : ¬ n - 1 - i + amount < n := by omega
    simp [h, hr]

end LeanVMCircuits.Words
