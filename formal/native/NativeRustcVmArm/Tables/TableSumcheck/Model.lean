module

public import NativeRustcVmArm.Spec.Tables
public import NativeRustcVm.Tables.Weights
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVmArm.Tables.Common

/-!
# `table_sumcheck` in the model's terms

The phase step by step (`tableSumcheck_run`); the six heights' maximum (`foldl_max6`, at most
`30`); the heights `table_weights` reads (`heightsOf_eq`); the in-place reverse of the challenges,
`j` swaps in (`rv`, `rv_zero`, `rv_succ`, `rv_half`); `EW`'s `==` by halves (`ew_beq`).
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeVm.Model NativeRustcVm.Tables

@[expose] public section

/-- The challenges after `j` swaps of the reverse: element `i`, the first and last `j` swapped. -/
def rv (xs : List EW) (j i : Nat) : EW :=
  if i < j ∨ xs.length - j ≤ i then xs.getD (xs.length - 1 - i) 0 else xs.getD i 0

end

public section

/-- **The table sumcheck**: the sumcheck, the reversed point's weights and terms, the final
check. -/
theorem tableSumcheck_run (heights : Array Nat) (forms : Array (Array FormW))
    (cp fp eqp : Array EW) (target : EW) (s : TState) :
    (tableSumcheck heights forms cp fp eqp target).run s =
      ((sumcheckPlain target 4 (heights.foldl max 0)).run s).bind fun p ↦
        ((tableTerms cp fp p.1.1.reverse
            (tableRows heights forms (tableWeights heights eqp p.1.1.reverse))).run p.2).bind
          fun q ↦ if q.1.1 == p.1.2 then some (q.1.2, q.2) else none := by
  simp only [tableSumcheck, StateT.run, tableRows]
  cases h : sumcheckPlain target 4 (heights.foldl max 0) s with
  | none => simp [bind, StateT.bind, h]
  | some p =>
    obtain ⟨⟨xs, c⟩, s1⟩ := p
    cases h2 : tableTerms cp fp xs.reverse
        (tablesW.zip (heights.zip (forms.zip (tableWeights heights eqp xs.reverse)))) s1 with
    | none => simp [bind, StateT.bind, h, h2]
    | some q =>
      obtain ⟨⟨f, ev⟩, s2⟩ := q
      by_cases hb : f = c <;>
        simp [bind, StateT.bind, h, h2, hb, require, reject, pure, StateT.pure]

theorem foldl_max6 (H : Array Nat) (h : H.size = 6) :
    H.foldl max 0 = max (max (max (max (max (H[0]'(by omega)) (H[1]'(by omega)))
      (H[2]'(by omega))) (H[3]'(by omega))) (H[4]'(by omega))) (H[5]'(by omega)) := by
  rcases H with ⟨l⟩
  simp only [List.size_toArray] at h
  match l, h with
  | [a, b, c, d, e, f], _ => simp

theorem foldl_max_le (H : Array Nat) (h : H.size = 6) (hle : ∀ x ∈ H, x ≤ 30) :
    H.foldl max 0 ≤ 30 := by
  rw [foldl_max6 H h]
  have h0 := hle _ (Array.getElem_mem (i := 0) (by omega))
  have h1 := hle _ (Array.getElem_mem (i := 1) (by omega))
  have h2 := hle _ (Array.getElem_mem (i := 2) (by omega))
  have h3 := hle _ (Array.getElem_mem (i := 3) (by omega))
  have h4 := hle _ (Array.getElem_mem (i := 4) (by omega))
  have h5 := hle _ (Array.getElem_mem (i := 5) (by omega))
  omega

/-- The heights `table_weights` reads: the six words. -/
theorem heightsOf_eq {d : Mem 64} {a : BitVec 64} {heights : Array Nat} (h : HeightsAt d a heights) :
    heightsOf d a = heights := by
  obtain ⟨hs, hle, hw⟩ := h
  have e := NativeRustcVm.wordsOf_of_wordsAt hw
  rw [List.length_map, Array.length_toList, hs] at e
  unfold heightsOf
  rw [e]
  apply Array.ext (by simp)
  intro i h1 h2
  simp only [List.getElem_toArray, List.getElem_map, Array.getElem_toList]
  have := hle _ (Array.getElem_mem h2)
  exact toNat_toUInt64 (by omega)

theorem getD0 {xs : List EW} {i : Nat} (h : i < xs.length) : xs.getD i 0 = xs[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- No swap yet: the challenges. -/
theorem rv_zero {xs : List EW} {i : Nat} (hi : i < xs.length) : rv xs 0 i = xs[i] := by
  unfold rv
  split
  · omega
  · exact getD0 hi

/-- **A swap more**: elements `j` and `|xs| - 1 - j` exchanged. -/
theorem rv_succ (xs : List EW) {j : Nat} (hj : 2 * j + 2 ≤ xs.length) (i : Nat) :
    rv xs (j + 1) i =
      if i = j then rv xs j (xs.length - 1 - j)
      else if i = xs.length - 1 - j then rv xs j j else rv xs j i := by
  unfold rv
  split <;> split <;> split <;> (try split) <;> first | rfl | omega | (congr 1; omega)

/-- **Half the swaps**: the reverse. -/
theorem rv_half {xs : List EW} {i : Nat} (hi : i < xs.length) :
    rv xs (xs.length / 2) i = xs.reverse[i]'(by simpa using hi) := by
  rw [List.getElem_reverse]
  unfold rv
  split
  · exact getD0 (by omega)
  · have e : xs.length - 1 - i = i := by omega
    simp only [e]
    exact getD0 hi

/-- `EW`'s `==`: both halves. -/
theorem ew_beq (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  cases x; cases y; rfl

end

end NativeRustcVmArm.Tables.TableSumcheck
