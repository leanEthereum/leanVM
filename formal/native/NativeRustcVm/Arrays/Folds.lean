module

public import NativeVm.Model.Field

/-!
# The model's array functions as list folds

`dot`, `eqEval`, `sumE`, `prodE` on the lists of their arrays (`dot_eq`, `eqEval_eq`, `sumE_eq`,
`prodE_eq`), a fold over a zip one element further (`zipFold_take_succ`) and over the common length
(`zipWith_take_min`): the invariants of the loops computing them.
-/

namespace NativeRustcVm

open NativeVm.Model

public section

theorem zipWith_take_min {α β γ : Type} (f : α → β → γ) :
    ∀ (L : List α) (R : List β),
      List.zipWith f L R = List.zipWith f (L.take (min L.length R.length)) (R.take (min L.length R.length))
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: L, b :: R => by
    rw [List.length_cons, List.length_cons, Nat.add_min_add_right, List.take_succ_cons,
      List.take_succ_cons, List.zipWith_cons_cons, List.zipWith_cons_cons, ← zipWith_take_min f L R]

theorem zipFold_take_succ {α β γ δ : Type} (f : α → β → γ) (g : δ → γ → δ) (init : δ)
    (L : List α) (R : List β) {i : Nat} (hL : i < L.length) (hR : i < R.length) :
    (List.zipWith f (L.take (i + 1)) (R.take (i + 1))).foldl g init =
      g ((List.zipWith f (L.take i) (R.take i)).foldl g init) (f L[i] R[i]) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hL,
    List.getElem?_eq_getElem hR, Option.toList_some, Option.toList_some,
    List.zipWith_append (by simp; omega), List.foldl_append]
  rfl

theorem dot_eq (L R : List EW) :
    dot L.toArray R.toArray = (List.zipWith (· * ·) L R).foldl (· + ·) 0 := by
  rw [dot, ← Array.foldl_toList, Array.toList_zipWith]

theorem eqEval_eq (L R : List EW) :
    eqEval L.toArray R.toArray = (List.zipWith (fun x z ↦ 1 + x + z) L R).foldl (· * ·) 1 := by
  rw [eqEval, ← Array.foldl_toList, Array.toList_zipWith]

theorem sumE_eq (L : List EW) : sumE L.toArray = L.foldl (· + ·) 0 := by
  rw [sumE, ← Array.foldl_toList]

theorem prodE_eq (L : List EW) : prodE L.toArray = L.foldl (· * ·) 1 := by
  rw [prodE, ← Array.foldl_toList]

theorem foldl_take_succ {α β : Type} (g : β → α → β) (init : β) (L : List α) {i : Nat}
    (h : i < L.length) : (L.take (i + 1)).foldl g init = g ((L.take i).foldl g init) L[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append]
  rfl

end

end NativeRustcVm
