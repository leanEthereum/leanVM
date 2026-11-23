module

public import NativeRustcVm.Whir.Model
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# What `each_row`'s proofs need of the model (x86-64)

The arch-neutral facts of `NativeRustcVmArm.Whir.EachRow`'s model files, restated here (no
AArch64 import): the table's pairs read back (`pairsOf_of_pairsAt`); an opened row's lanes fit
the row (`lanesOf_size_le`); `finalOk` row by row (`finalOk_of`, `finalOk_false`); `E`'s equality
test limb by limb (`ew_beq`); `batchedOf` as the partial sums of the rows' terms (`nextTerm`,
`nextPartial`, `batchedOf_eq`).
-/

namespace NativeRustcVmX64.Whir.EachRow

open NativeVm.Model NativeRustcVm NativeRustcVm.Whir

public section

theorem pairWords_bytes (ps : List (UInt64 × UInt64)) :
    (pairWords ps).flatMap wordBytes = (ps.map fun p ↦ (⟨p.1, p.2⟩ : EW)).flatMap ewBytes := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairWords, List.flatMap_cons, List.map_cons, ewBytes] at *
    rw [List.flatMap_append, ih]
    simp

theorem length_pairWords (ps : List (UInt64 × UInt64)) : (pairWords ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pairWords, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at *
    omega

/-- **The table's pairs read back.** -/
theorem pairsOf_of_pairsAt {d : Mem 64} {a : BitVec 64} {ps : List (UInt64 × UInt64)}
    (h : PairsAt d a ps) : pairsOf d a ps.length = ps := by
  have h' : EWsAt d a (ps.map fun p ↦ (⟨p.1, p.2⟩ : EW)) := by
    unfold EWsAt
    rw [← pairWords_bytes]
    exact h
  have := ewsOf_of_ewsAt h'
  rw [List.length_map] at this
  unfold pairsOf
  rw [this, List.map_map]
  exact List.map_id'' (fun _ ↦ rfl) ps

/-- An opened row's lanes are at most its words. -/
theorem lanesOf_size_le (index : Nat) (row : Array UInt64) :
    (lanesOf index row).size ≤ row.size := by
  unfold lanesOf
  split
  · simp
  · simp [extRow]
    omega

/-- `E`'s equality test, limb by limb. -/
theorem ew_beq (a b : EW) : (a == b) = (a.c0 == b.c0 && a.c1 == b.c1) := by
  cases a; cases b; rfl

/-- The check of query `i`. -/
@[expose] def rowOk (index mu : Nat) (rounds : Array FoldRoundW) (folded : Array EW)
    (q : UInt64) (row : Array UInt64) : Bool :=
  foldRow (lanesOf index row) q rounds == novelEval folded (subspaceAtTable (subspaceTable mu) q)

theorem finalOk_iff {index mu : Nat} {rounds : Array FoldRoundW} {folded : Array EW}
    {qs : Array UInt64} {words : Array (Array UInt64)} :
    finalOk index mu rounds folded qs words = true ↔
      ∀ i (h1 : i < qs.size) (h2 : i < words.size),
        rowOk index mu rounds folded qs[i] words[i] = true := by
  unfold finalOk rowOk
  rw [Array.all_eq_true]
  constructor
  · intro h i h1 h2
    have := h i (by simp; omega)
    simpa using this
  · intro h i hi
    simp only [Array.size_zip] at hi
    have := h i (by omega) (by omega)
    simpa using this

/-- All rows checked: `finalOk`. -/
theorem finalOk_of {index mu : Nat} {rounds : Array FoldRoundW} {folded : Array EW}
    {qs : Array UInt64} {words : Array (Array UInt64)} {j : Nat}
    (hj : qs.size ≤ j ∨ words.size ≤ j)
    (h : ∀ i (h1 : i < qs.size) (h2 : i < words.size), i < j →
      rowOk index mu rounds folded qs[i] words[i] = true) :
    finalOk index mu rounds folded qs words = true :=
  finalOk_iff.mpr fun i h1 h2 ↦ h i h1 h2 (by omega)

/-- A row failing its check: not `finalOk`. -/
theorem finalOk_false {index mu : Nat} {rounds : Array FoldRoundW} {folded : Array EW}
    {qs : Array UInt64} {words : Array (Array UInt64)} {j : Nat} (h1 : j < qs.size)
    (h2 : j < words.size) (h : rowOk index mu rounds folded qs[j] words[j] = false) :
    finalOk index mu rounds folded qs words = false := by
  cases hf : finalOk index mu rounds folded qs words
  · rfl
  · rw [finalOk_iff.mp hf j h1 h2] at h
    cases h

end

/-! ## `batchedOf` row by row -/

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

end NativeRustcVmX64.Whir.EachRow
