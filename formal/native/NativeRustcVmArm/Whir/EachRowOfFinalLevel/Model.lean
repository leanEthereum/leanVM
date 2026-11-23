module

public import NativeRustcVm.Whir.Model
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# What `each_row`'s proofs need of the model

The table's pairs read back (`pairsOf_of_pairsAt`); an opened row's lanes fit the 64 lanes
(`lanesOf_size_le`); `finalOk` row by row (`finalOk_of`, `finalOk_false`); `E`'s equality test
limb by limb (`ew_beq`).
-/

namespace NativeRustcVmArm.Whir.EachRow

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
theorem lanesOf_size_le (index : Nat) (row : Array UInt64) : (lanesOf index row).size ≤ row.size := by
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

end NativeRustcVmArm.Whir.EachRow
