module

public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Model

/-!
# `batchedOf` row by row

`each_row::<next_level's closure>` adds row `i`'s term `qw[i] · (foldRow … + scale)` to the batched
value for every opened row, the weight `0` past the query weights (`nextTerm`, its partial sums
`nextPartial`). `batchedOf` is the partial sum over all rows (`batchedOf_eq`): the terms past the
weights vanish (`EW.mul 0 x = 0`, `ew_zero_mul`).
-/

namespace NativeRustcVmArm.Whir.EachRow

open NativeVm.Model NativeRustcVm NativeRustcVm.Whir

@[expose] public section

/-- Row `i`'s term of the batched value. -/
def nextTerm (index mu : Nat) (rounds : Array FoldRoundW) (high : Array EW) (qs : Array UInt64)
    (words : Array (Array UInt64)) (qw : Array EW) (i : Nat) : EW :=
  qw.getD i 0 * (foldRow (lanesOf index (words.getD i #[])) (qs.getD i 0) rounds +
    EW.scale ((subspaceAtTable (subspaceTable mu) (qs.getD i 0)).getD mu 0)
      (novelEval high (subspaceAtTable (subspaceTable mu) (qs.getD i 0))))

/-- The batched value after `j` rows. -/
def nextPartial (index mu : Nat) (rounds : Array FoldRoundW) (high : Array EW) (qs : Array UInt64)
    (words : Array (Array UInt64)) (qw : Array EW) (j : Nat) : EW :=
  (List.range j).foldl (fun acc i ↦ acc + nextTerm index mu rounds high qs words qw i) 0

end

public section

variable {index mu : Nat} {rounds : Array FoldRoundW} {high : Array EW} {qs : Array UInt64}
  {words : Array (Array UInt64)} {qw : Array EW}

theorem kmul_zero_left (b : UInt64) : kmul 0 b = 0 := by
  unfold kmul
  rw [BF64.mulShift]
  simp only [↓reduceIte]
  decide

theorem ew_zero_mul (x : EW) : (0 : EW) * x = 0 := by
  show EW.mul ⟨0, 0⟩ x = ⟨0, 0⟩
  simp only [EW.mul, kmul_zero_left]
  decide

theorem ew_add_zero (x : EW) : x + 0 = x := by
  show (⟨x.c0 ^^^ 0, x.c1 ^^^ 0⟩ : EW) = x
  simp

theorem nextPartial_zero : nextPartial index mu rounds high qs words qw 0 = 0 := rfl

theorem nextPartial_succ (j : Nat) :
    nextPartial index mu rounds high qs words qw (j + 1) =
      nextPartial index mu rounds high qs words qw j +
        nextTerm index mu rounds high qs words qw j := by
  simp [nextPartial, List.range_succ, List.foldl_append]

/-- Past the weights, the partial sums stay. -/
theorem nextPartial_stay {m : Nat} (hm : qw.size ≤ m) :
    ∀ n, nextPartial index mu rounds high qs words qw (m + n) =
      nextPartial index mu rounds high qs words qw m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← Nat.add_assoc, nextPartial_succ, ih]
    have : nextTerm index mu rounds high qs words qw (m + n) = 0 := by
      unfold nextTerm
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      exact ew_zero_mul _
    rw [this, ew_add_zero]

/-- **`batchedOf` is the partial sum over all rows.** -/
theorem batchedOf_eq : batchedOf index mu rounds high qs words qw =
    nextPartial index mu rounds high qs words qw (min qs.size words.size) := by
  unfold batchedOf sumE
  rw [← Array.foldl_toList, Array.toList_zipWith, Array.toList_zip]
  have hl : List.zipWith (fun (x : UInt64 × Array UInt64) (queryWeight : EW) ↦
        queryWeight * (foldRow (lanesOf index x.2) x.1 rounds +
          EW.scale ((subspaceAtTable (subspaceTable mu) x.1).getD mu 0)
            (novelEval high (subspaceAtTable (subspaceTable mu) x.1))))
      (qs.toList.zip words.toList) qw.toList =
      (List.range (min (min qs.size words.size) qw.size)).map
        (nextTerm index mu rounds high qs words qw) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have hb : i < qs.size ∧ i < words.size ∧ i < qw.size := by
      simp only [List.length_map, List.length_range, Nat.lt_min] at h2
      exact ⟨h2.1.1, h2.1.2, h2.2⟩
    simp only [List.getElem_zipWith, List.getElem_zip, List.getElem_map, List.getElem_range,
      Array.getElem_toList, nextTerm]
    rw [show qw.getD i 0 = qw[i] by simp [Array.getD, hb.2.2],
      show words.getD i #[] = words[i] by simp [Array.getD, hb.2.1],
      show qs.getD i 0 = qs[i] by simp [Array.getD, hb.1]]
  rw [hl, List.foldl_map]
  show nextPartial index mu rounds high qs words qw _ = _
  rcases Nat.le_total (min qs.size words.size) qw.size with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h
    rw [hn, nextPartial_stay le_rfl]

end

end NativeRustcVmArm.Whir.EachRow
