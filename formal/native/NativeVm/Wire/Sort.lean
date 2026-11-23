module

public import NativeVm.Wire.ModelSpec

/-!
# The decoder's distinct positions
-/

@[expose] public section

namespace NativeVm.Wire

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Wire

theorem length_insD (x : Nat) : ∀ l : List Nat, (insD l x).length ≤ l.length + 1
  | [] => by simp [insD]
  | a :: l => by
    unfold insD
    split
    · simp
    · split
      · simp
      · have := length_insD x l
        simp only [List.length_cons]
        omega

theorem length_foldl_insD (qs : List Nat) :
    ∀ l : List Nat, (qs.foldl insD l).length ≤ l.length + qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    intro l
    have h1 := ih (insD l q)
    have h2 := length_insD q l
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem length_sortD (qs : List Nat) : (sortD qs).length ≤ qs.length := by
  simpa [sortD] using length_foldl_insD qs []

theorem sortD_take_succ (qs : List Nat) {i : Nat} (h : i < qs.length) :
    sortD (qs.take (i + 1)) = insD (sortD (qs.take i)) qs[i] := by
  rw [sortD, sortD, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some,
    List.foldl_append]
  rfl

theorem pairwise_sortD (qs : List Nat) : (sortD qs).Pairwise (· < ·) :=
  (sortD_aux qs [] List.Pairwise.nil).1

theorem mem_sortD {qs : List Nat} {y : Nat} (h : y ∈ sortD qs) : y ∈ qs := by
  have := ((sortD_aux qs [] List.Pairwise.nil).2 y).1 h
  simpa using this

end NativeVm.Wire
