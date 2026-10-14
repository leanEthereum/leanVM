import Whir.TraceExtraction

/-! An in-place-friendly array ladder for the source trace splitter. It computes every required Frobenius scalar once; the recursion retains no duplicate power arrays. -/
namespace Whir.FrobeniusExtraction
variable {F : Type*} [CommRing F]

/-- The n successive scalar powers, using n−1 squarings and no inversions. -/
def powers : Nat → F → Array F
  | 0, _ => #[]
  | n + 1, beta =>
    let previous := powers n beta
    if n = 0 then previous.push beta
    else
      let last := previous.getD (n - 1) 0
      previous.push (last * last)

theorem powers_size (count : Nat) (beta : F) : (powers count beta).size = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [powers]; split <;> simp [ih]

theorem powers_value (count : Nat) (beta : F) :
    powers count beta = Array.ofFn (fun i : Fin count => beta ^ (2 ^ i.val)) := by
  induction count with
  | zero => simp [powers]
  | succ count ih =>
    simp only [powers, ih]
    split
    · subst count
      simp
      apply Array.ext
      · simp
      · intro i hi hi'
        have same : i = 0 := by simpa using hi'
        subst i
        simp
    · rename_i positive
      apply Array.ext
      · simp
      · intro i hi hi'
        have bound : i ≤ count := by simpa using hi'
        by_cases old : i < count
        · simp [Array.getElem_push, old]
        · have same : i = count := by omega
          subst i
          have pred : count - 1 < count := by omega
          simp only [Array.getElem_push, Array.size_ofFn, lt_self_iff_false,
            dite_false, Array.getElem_ofFn, Array.getD, pred, dite_true]
          change (Array.ofFn (fun i : Fin count => beta ^ (2 ^ i.val)))[count - 1]'(by simpa using pred) *
            (Array.ofFn (fun i : Fin count => beta ^ (2 ^ i.val)))[count - 1]'(by simpa using pred) =
              beta ^ (2 ^ count)
          simp only [Array.getElem_ofFn]
          rw [← pow_two, ← pow_mul]
          congr 1
          have step : count = (count - 1) + 1 := by omega
          rw [step, pow_succ]
          simp

/-- Counts exactly the scalar multiplication sites of the ladder (array work is separate). -/
def multiplicationCalls : Nat → Nat
  | 0 => 0
  | n + 1 => multiplicationCalls n + if n = 0 then 0 else 1

theorem multiplicationCalls_eq (count : Nat) : multiplicationCalls count = count - 1 := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [multiplicationCalls, ih]; split <;> omega

#print axioms powers_size
#print axioms powers_value
#print axioms multiplicationCalls_eq
end Whir.FrobeniusExtraction
