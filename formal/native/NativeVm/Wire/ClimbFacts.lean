module

public import NativeVm.Wire.ModelSpec

/-!
# The decoder's climb step and parent count
-/

@[expose] public section

namespace NativeVm.Wire

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Wire

theorem climbM_succ {B : List UInt8} {h : Nat} {nodes : List (Nat × Digest)} {c : Nat} :
    climbM B (h + 1) nodes c = (sibsM B nodes nodes c).bind fun p ↦
      (climbM B h (parentsOf nodes p.1) p.2).map fun q ↦
        (p.1.map (fun s ↦ (s.1, s.2.1)) :: q.1, q.2) := by
  rw [climbM]
  simp only [Option.bind_eq_bind]
  cases sibsM B nodes nodes c with
  | none => rfl
  | some p =>
    simp only [Option.bind_some]
    cases climbM B h (parentsOf nodes p.1) p.2 <;> rfl

theorem climb_parentsOf_length : ∀ (l : List (Nat × Digest)) (m : List (Nat × Digest × Bool)),
    (parentsOf l m).length ≤ l.length
  | [], _ => by simp [parentsOf]
  | _ :: _, [] => by simp [parentsOf]
  | a :: l, b :: m => by
    have := climb_parentsOf_length l m
    have h1 : (parentOf a b).length ≤ 1 := by unfold parentOf; split <;> simp
    simp only [parentsOf, List.zip_cons_cons, List.flatMap_cons, List.length_append,
      List.length_cons] at this ⊢
    omega

end NativeVm.Wire
