module

public import NativeVm.Wire.Model

/-!
# `insD` as `ins_d` computes it

`ins_d` scans for the first position `i` whose value is at least `x`: if it is `x`, the list is
kept (`insD_self`); else `x` goes in at `i` (`insD_at`), at the end if there is none (`insD_end`).
-/

namespace NativeRustcVm.Wire

open NativeVm.Wire

public section

theorem insD_end (x : Nat) : ∀ l : List Nat, (∀ y ∈ l, y < x) → insD l x = l ++ [x]
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    simp only [insD, show ¬x < a by omega, show x ≠ a by omega, ↓reduceIte, List.cons_append]
    rw [insD_end x l fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

theorem insD_at (x : Nat) : ∀ (l : List Nat) (i : Nat) (hi : i < l.length),
    (∀ j (hj : j < i), l[j] < x) → x < l[i] → insD l x = l.take i ++ x :: l.drop i
  | [], _, hi, _, _ => absurd hi (by simp)
  | a :: l, 0, _, _, h => by
    simp only [List.getElem_cons_zero] at h
    simp [insD, h]
  | a :: l, i + 1, hi, hlt, h => by
    have ha := hlt 0 (by omega)
    simp only [List.getElem_cons_zero] at ha
    simp only [insD, show ¬x < a by omega, show x ≠ a by omega, ↓reduceIte, List.take_succ_cons,
      List.drop_succ_cons, List.cons_append]
    rw [insD_at x l i (by simpa using hi) (fun j hj ↦ by simpa using hlt (j + 1) (by omega))
      (by simpa using h)]

theorem insD_self (x : Nat) : ∀ (l : List Nat) (i : Nat) (hi : i < l.length),
    (∀ j (hj : j < i), l[j] < x) → l[i] = x → insD l x = l
  | [], _, hi, _, _ => absurd hi (by simp)
  | a :: l, 0, _, _, h => by
    simp only [List.getElem_cons_zero] at h
    simp [insD, h]
  | a :: l, i + 1, hi, hlt, h => by
    have ha := hlt 0 (by omega)
    simp only [List.getElem_cons_zero] at ha
    simp only [insD, show ¬x < a by omega, show x ≠ a by omega, ↓reduceIte]
    rw [insD_self x l i (by simpa using hi) (fun j hj ↦ by simpa using hlt (j + 1) (by omega))
      (by simpa using h)]

end

end NativeRustcVm.Wire
