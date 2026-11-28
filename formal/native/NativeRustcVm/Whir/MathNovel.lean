module

public import NativeVm.Model.Whir

/-!
# `novel_eval` as `whir.rs` computes it

`novel_eval(coefficients, what)` builds `novelBasis` in a buffer, one `What_i` at a time
(`novelPre`, `novelPre_succ`), and stops at the first basis at least as long as the coefficients
(`novelPre_stable`: the model's later steps keep it); a basis it doubles is shorter than the
coefficients (at most 64), hence at most 32 long (`novelPre_pow`, `size_le_32`). Then it sums the
products of the first `min size count` basis values and coefficients (`novelAcc`,
`novelEval_eq`).
-/

namespace NativeRustcVm.Whir

open NativeVm.Model

@[expose] public section

/-- One step of `novelBasis`'s fold. -/
def novelStep (count : Nat) (basis : Array UInt64) (value : UInt64) : Array UInt64 :=
  if count ≤ basis.size then basis else basis ++ basis.map (kmul · value)

/-- The basis after the first `j` values. -/
def novelPre (what : Array UInt64) (count j : Nat) : Array UInt64 :=
  (what.toList.take j).foldl (novelStep count) #[1]

/-- The products, `p·X`, summed over the first `t`. -/
def novelAcc (coefficients : Array EW) (basis : Array UInt64) (t : Nat) : EW :=
  ((List.zipWith (fun p b ↦ EW.scale b p) coefficients.toList basis.toList).take t).foldl
    (· + ·) 0

end

public section

theorem novelPre_zero (what : Array UInt64) (count : Nat) : novelPre what count 0 = #[1] := by
  simp [novelPre]

theorem novelPre_succ (what : Array UInt64) (count : Nat) {j : Nat} (hj : j < what.size) :
    novelPre what count (j + 1) = novelStep count (novelPre what count j) what[j] := by
  rw [novelPre, novelPre, List.take_add_one, List.foldl_append]
  simp [hj]

theorem novelBasis_eq (what : Array UInt64) (count : Nat) :
    novelBasis what count = (novelPre what count what.size).extract 0 count := by
  rw [novelPre, List.take_of_length_le (by simp), Array.foldl_toList]
  rfl

theorem novelPre_of_ge (what : Array UInt64) (count : Nat) {j : Nat} (h : what.size ≤ j) :
    novelPre what count j = novelPre what count what.size := by
  rw [novelPre, novelPre, List.take_of_length_le (by simp; omega),
    List.take_of_length_le (by simp)]

/-- Once long enough, the basis stays. -/
theorem novelPre_stable (what : Array UInt64) {count j : Nat}
    (h : count ≤ (novelPre what count j).size) : ∀ k, j ≤ k →
      novelPre what count k = novelPre what count j := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    by_cases hw : k < what.size
    · rw [novelPre_succ _ _ hw, ih, novelStep]
      simp [h]
    · rw [novelPre_of_ge _ _ (show what.size ≤ k + 1 by omega), ← ih,
        novelPre_of_ge _ _ (show what.size ≤ k by omega)]

/-- The basis's length is a power of `2`. -/
theorem novelPre_pow (what : Array UInt64) (count : Nat) :
    ∀ j, ∃ e, (novelPre what count j).size = 2 ^ e
  | 0 => ⟨0, by simp [novelPre_zero]⟩
  | j + 1 => by
    obtain ⟨e, he⟩ := novelPre_pow what count j
    by_cases hw : j < what.size
    · rw [novelPre_succ _ _ hw, novelStep]
      split
      · exact ⟨e, he⟩
      · exact ⟨e + 1, by simp [he, Nat.pow_succ]; omega⟩
    · rw [novelPre_of_ge _ _ (by omega)]
      rw [novelPre_of_ge _ _ (by omega)] at he
      exact ⟨e, he⟩

/-- A power of `2` below `64` is at most `32`. -/
theorem size_le_32 {n e : Nat} (h : n = 2 ^ e) (hn : n < 64) : n ≤ 32 := by
  subst h
  rcases Nat.lt_or_ge e 6 with he | he
  · interval_cases e <;> simp
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) he
    simp at this
    omega

theorem novelPre_size_pos (what : Array UInt64) (count j : Nat) :
    0 < (novelPre what count j).size := by
  obtain ⟨e, he⟩ := novelPre_pow what count j
  rw [he]
  exact Nat.two_pow_pos e

/-- For at most `64` coefficients, the basis is at most `64` long. -/
theorem novelPre_size_le (what : Array UInt64) {count : Nat} (hc : count ≤ 64) :
    ∀ j, (novelPre what count j).size ≤ 64
  | 0 => by simp [novelPre_zero]
  | j + 1 => by
    have ih := novelPre_size_le what hc j
    by_cases hw : j < what.size
    · rw [novelPre_succ _ _ hw, novelStep]
      split
      · exact ih
      · obtain ⟨e, he⟩ := novelPre_pow what count j
        have := size_le_32 he (by omega)
        simp only [Array.size_append, Array.size_map]
        omega
    · rw [novelPre_of_ge _ _ (by omega)]
      rw [novelPre_of_ge _ _ (by omega)] at ih
      exact ih

theorem novelAcc_zero (coefficients : Array EW) (basis : Array UInt64) :
    novelAcc coefficients basis 0 = 0 := by
  simp [novelAcc]

theorem novelAcc_succ (coefficients : Array EW) (basis : Array UInt64) {t : Nat}
    (h1 : t < coefficients.size) (h2 : t < basis.size) :
    novelAcc coefficients basis (t + 1) =
      novelAcc coefficients basis t + EW.scale basis[t] coefficients[t] := by
  rw [novelAcc, novelAcc, List.take_add_one, List.foldl_append]
  simp [h1, h2]

/-- **`novelEval`** is the sum over the first `min size count` products. -/
theorem novelEval_eq (coefficients : Array EW) (what : Array UInt64) :
    novelEval coefficients what =
      novelAcc coefficients (novelPre what coefficients.size what.size)
        (min (novelPre what coefficients.size what.size).size coefficients.size) := by
  rw [novelEval, novelBasis_eq, sumE, novelAcc, ← Array.foldl_toList, Array.toList_zipWith,
    Array.toList_extract, List.extract_eq_take_drop, List.drop_zero]
  congr 1
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp

end

end NativeRustcVm.Whir
