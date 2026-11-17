/-
  LeanVM.Protocol.Extraction.AS.Forward

  The transcript's first forward answers, indexed.
-/

module

public import LeanVM.Protocol.Extraction.Fast.Lookup
public import LeanVM.Protocol.Rpm.ExtractF

/-!
# The first forward answers, indexed

`fwdIndex qs`: a sorted map from each forward query's input to the answer of the first forward
query at it, so `fwdF (fwdIndex qs) = Rpm.firstForward qs` (`fwdF_fwdIndex`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Extraction.Fast Common

@[expose] public section

attribute [local instance] lexOrd

/-- One query: a forward query's answer kept unless its input has one. -/
def fwdStep (m : SortedMap (List UInt64) KeccakState) :
    PermutationQuery KeccakState × KeccakState → SortedMap (List UInt64) KeccakState
  | (.forward x, y) => insertIfNew m x.toList y
  | (.inverse _, _) => m

/-- **The transcript's first forward answers, indexed.** -/
def fwdIndex (qs : List (PermutationQuery KeccakState × KeccakState)) :
    SortedMap (List UInt64) KeccakState :=
  qs.foldl fwdStep .empty

/-- The permutation the index answers. -/
def fwdF (M : SortedMap (List UInt64) KeccakState) (x : KeccakState) : Option KeccakState :=
  M.get? x.toList

theorem foldl_fwdStep (qs : List (PermutationQuery KeccakState × KeccakState))
    (m : SortedMap (List UInt64) KeccakState) (x : KeccakState) :
    (qs.foldl fwdStep m).get? x.toList = (m.get? x.toList).or (Rpm.firstForward qs x) := by
  induction qs generalizing m with
  | nil => simp [Rpm.firstForward]
  | cons q qs ih =>
    rw [List.foldl_cons, ih]
    obtain ⟨q, y⟩ := q
    cases q with
    | inverse z =>
      simp only [fwdStep, Rpm.firstForward, List.find?_cons]
      simp
    | forward z =>
      simp only [fwdStep, insertIfNew, Rpm.firstForward, List.find?_cons]
      by_cases hm : m.contains z.toList = true
      · simp only [hm, ↓reduceIte]
        by_cases hx : z = x
        · subst hx
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hm
          simp [hv]
        · simp [hx]
      · simp only [hm, Bool.false_eq_true, ↓reduceIte, SortedMap.get?_insert]
        by_cases hx : z = x
        · subst hx
          have hn : m.get? z.toList = none := by simpa [SortedMap.contains] using hm
          simp [hn]
        · have hx' : z.toList ≠ x.toList := fun h ↦ hx (Vector.toList_inj.mp h)
          simp [hx, hx']

/-- **The index answers as the transcript's first forward queries.** -/
theorem fwdF_fwdIndex (qs : List (PermutationQuery KeccakState × KeccakState)) :
    fwdF (fwdIndex qs) = Rpm.firstForward qs := by
  funext x
  rw [fwdF, fwdIndex, foldl_fwdStep, SortedMap.get?_empty, Option.none_or]

end
end LeanVM.Extraction.AS
