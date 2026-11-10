module

public import LeanVM.Cost.Bounds.Decoder.EntryMaps
public import LeanVM.Cost.Bounds.Decoder.PreTest
public import LeanVM.Cost.Bounds.Decoder.GuestTablesBounds

/-!
# Bound: the replayed frame map's parts, compiled

The prices of `Cost/Decoder/EntryTable.lean`'s parts the sorted entry array
(`Bounds/Decoder/EntryArray.lean`) and the pc table (`Bounds/Decoder/PcTable.lean`) use.
Parameters: `R` a memory read (the reader closure).

* `listFoldl_amortized'`: a fold amortized, its final potential and invariant kept;
* the guest's tables' maxima (`argCount_le`, `retCount_le`, `loc_lt`, from
  `GuestTablesBounds.lean`);
* `wordsWith_cost`, `callKey_cost`, **`entryKeyT_cost`**: a state's key, its `56 + 10` words read
  (`guestArgCounts`, `guestRetCounts`), at most `66R + 41200`, of at most `56` argument and `10`
  return codes (`entryKeyT_ok`);
* `isFunctionIndex_cost` (`11`), **`frameWordAt_cost`**: a frame's word, the table of frame cells
  and a read, at most `R + 1535`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.Fast

public section

attribute [local instance] lexOrd

variable (P : MachineProgram)

/-! ## A fold, amortized, its final potential kept -/

/-- **`List.foldl`, amortized**, the final potential and invariant kept (`listFoldl_amortized`). -/
theorem listFoldl_amortized' {α β : Type} [MachineEncoding α] [MachineEncoding β]
    (hP : Includes P listFoldl.costDeps) (f : α → β → α) (fVal : MachineValue)
    (hf : ∀ a b, RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b))) (A : ℕ)
    (Φ : α → ℕ) (I : α → ℕ → Prop) :
    ∀ (l : List β) (init : α), I init l.length →
      (∀ acc r, I acc (r + 1) → ∀ b ∈ l, I (f acc b) r ∧
        appCost P fVal [encodeValue acc, encodeValue b] + Φ (f acc b) ≤ Φ acc + A) →
      I (l.foldl f init) 0 ∧
        machineCost P listFoldl.costIdx [fVal, encodeValue init, encodeValue l] +
          Φ (l.foldl f init) ≤ Φ init + (A + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil =>
    intro init hI _
    rw [listFoldl.costEq_nil P hP f fVal hf]
    refine ⟨hI, ?_⟩
    simp only [List.foldl_nil, List.length_nil]
    omega
  | cons b l ih =>
    intro init hI hB
    rw [listFoldl.costEq_cons P hP f fVal hf, List.foldl_cons]
    obtain ⟨hI', h2⟩ := hB init l.length (by simpa using hI) b (by simp)
    obtain ⟨hF, h1⟩ := ih (f init b) hI' (fun acc r hacc b' hb ↦ hB acc r hacc b' (by simp [hb]))
    refine ⟨hF, ?_⟩
    simp only [List.length_cons]
    nlinarith

/-! ## The guest's tables -/

theorem toArray_getD_le_of_all {l : List ℕ} {B : ℕ} (h : l.all (· ≤ B) = true) (j : ℕ) :
    l.toArray.getD j 0 ≤ B := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rw [List.all_eq_true] at h
  cases hj : l[j]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (h x (List.mem_of_getElem? hj))

theorem argCount_le (j : ℕ) : guestArgCounts.getD j 0 ≤ 56 :=
  toArray_getD_le_of_all guestArgCountsList_le j

theorem retCount_le (j : ℕ) : guestRetCounts.getD j 0 ≤ 10 :=
  toArray_getD_le_of_all guestRetCountsList_le j

theorem getD_getD_lt (A : Array (Array ℕ)) (B : ℕ) (hB : 0 < B)
    (h : ∀ a ∈ A, ∀ x ∈ a, x < B) (j i : ℕ) : (A.getD j #[]).getD i 0 < B := by
  by_cases h1 : j < A.size
  · have e : A.getD j #[] = A[j] := by simp [Array.getD, h1]
    rw [e]
    by_cases h2 : i < A[j].size
    · have e2 : A[j].getD i 0 = A[j][i] := by simp [Array.getD, h2]
      rw [e2]
      exact h _ (Array.getElem_mem h1) _ (Array.getElem_mem h2)
    · have e2 : A[j].getD i 0 = 0 := by simp [Array.getD, h2]
      rw [e2]
      exact hB
  · have e : A.getD j #[] = #[] := by simp [Array.getD, h1]
    rw [e]
    simpa using hB

theorem loc_lt (j i : ℕ) : (guestLocs.getD j #[]).getD i 0 < 2 ^ 20 := by
  refine getD_getD_lt _ _ (by norm_num) (fun a ha x hx ↦ ?_) j i
  have h := guestLocsList_lt
  rw [List.all_eq_true] at h
  rw [show guestLocs = (guestLocsList.map List.toArray).toArray from rfl, List.mem_toArray,
    List.mem_map] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  have hl' := h l hl
  rw [List.all_eq_true] at hl'
  exact of_decide_eq_true (hl' x (by simpa using hx))

/-! ## A state's key -/

/-- A word's code (`wordCodeC`): at most `12`. -/
theorem wordCode_cost (hP : Includes P wordCodeC.costDeps) (x : E) :
    machineCost P wordCodeC.costIdx [encodeValue x] ≤ 12 := by
  rw [wordCodeC.costEq P hP] <;> omega

/-- A call's key (`callKeyC`): `27` per word, `19`. -/
theorem callKey_cost (hP : Includes P callKeyC.costDeps) (j : ℕ) (args rets : List E) :
    machineCost P callKeyC.costIdx [encodeValue j, encodeValue args, encodeValue rets] ≤
      27 * (args.length + rets.length) + 19 := by
  rw [callKeyC.costEq P hP]
  have hlam : ∀ x : E, appCost P (.closure callKeyC.lam0.costIdx []) [encodeValue x] ≤ 14 := by
    intro x
    rw [appCost_fn, List.nil_append, callKeyC.lam0.costEq P (by includes), List.length_nil]
    have := wordCode_cost P (by includes) x
    omega
  have h1 := map_cost P (by includes) _ (.closure callKeyC.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (callKeyC.lam0.costSpec P (by includes) x)) 14 args
    (fun x _ ↦ hlam x)
  have h2 := map_cost P (by includes) _ (.closure callKeyC.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (callKeyC.lam0.costSpec P (by includes) x)) 14 rets
    (fun x _ ↦ hlam x)
  omega

/-- The code of a word: word-sized. -/
theorem wordCode_ok (x : E) : PairOK (wordCode x) :=
  ⟨UInt64.toNat_lt _, UInt64.toNat_lt _⟩

/-- A call's key, its callee word-sized, its lists at most `L`: of at most `L` codes. -/
theorem callKey_ok {L j : ℕ} {args rets : List E} (hj : j < 2 ^ 64) (ha : args.length ≤ L)
    (hr : rets.length ≤ L) : KeyOK L (callKey j args rets) := by
  refine ⟨hj, by simpa [callKey] using ha, by simpa [callKey] using hr, ?_, ?_⟩ <;>
  · intro x hx
    simp only [callKey, List.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact wordCode_ok y

theorem length_wordsWith (rd : Reader) (fp : K) (o n : ℕ) : (wordsWith rd fp o n).length = n := by
  simp [wordsWith]

section Reads

variable (rd : Reader) (rdVal : MachineValue)
  (hrd : ∀ a : K, RunsApp P rdVal [encodeValue a] (encodeValue (rd a)))
  (R : ℕ) (hR : ∀ a : K, appCost P rdVal [encodeValue a] ≤ R)

include hrd hR in
/-- `n` words of a frame from cell `o` (`wordsWithC`), `o + n ≤ 2^W`: at most
`(psAt W + R + 80)·n + 19`. -/
theorem wordsWith_cost (hP : Includes P wordsWithC.costDeps) {W : ℕ} (hW : 0 < W) (hW64 : W < 64)
    (fp : K) (o n : ℕ) (hon : o + n ≤ 2 ^ W) :
    machineCost P wordsWithC.costIdx [rdVal, encodeValue fp, encodeValue o, encodeValue n] ≤
      (psAt W + R + 80) * n + 19 := by
  have h64 : 2 ^ W < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hW64
  rw [wordsWithC.costEq P hP rd rdVal hrd]
  have hr := rangeLoop_cost P (by includes) n [] (by omega)
  have hm := map_cost P (by includes) _
    (.closure wordsWithC.lam0.costIdx [rdVal, encodeValue fp, encodeValue o])
    (fun i ↦ RunsApp.of_spec (wordsWithC.lam0.costSpec P (by includes) rd rdVal hrd fp o i))
    (psAt W + R + 52) (List.range n) (fun i hi ↦ by
      have hi' := List.mem_range.mp hi
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [wordsWithC.lam0.costEq P (by includes) rd rdVal hrd, limbs_of_lt (by omega : o < 2 ^ 64),
        limbs_of_lt (by omega : i < 2 ^ 64), limbs_of_lt (by omega : o + i < 2 ^ 64)]
      have := wordWith_cost P rd rdVal hrd R hR hW hW64 (by includes) fp (o + i) (by omega)
      simp only [max_self]
      omega)
  rw [List.length_range] at hm
  nlinarith

include hrd hR in
/-- **A state's key** (`entryKeyTC`): its `≤ 56` argument and `≤ 10` return words read, at most
`66R + 41200`. -/
theorem entryKeyT_cost (hP : Includes P entryKeyTC.costDeps) (s : Registers K) (j : ℕ) :
    machineCost P entryKeyTC.costIdx [rdVal, encodeValue s, encodeValue j] ≤ 66 * R + 41200 := by
  have ha := argCount_le j
  have hr := retCount_le j
  rw [entryKeyTC.costEq P hP rd rdVal hrd, limbs_of_lt (by omega : guestArgCounts.getD j 0 < 2 ^ 64),
    limbs_of_lt (by omega : 2 + guestArgCounts.getD j 0 < 2 ^ 64)]
  have h1 := wordsWith_cost P rd rdVal hrd R hR (by includes) (W := 7) (by norm_num) (by norm_num)
    s.fp 2 (guestArgCounts.getD j 0) (show 2 + guestArgCounts.getD j 0 ≤ 2 ^ 7 by omega)
  have h2 := wordsWith_cost P rd rdVal hrd R hR (by includes) (W := 7) (by norm_num) (by norm_num)
    s.fp (2 + guestArgCounts.getD j 0) (guestRetCounts.getD j 0)
    (show 2 + guestArgCounts.getD j 0 + guestRetCounts.getD j 0 ≤ 2 ^ 7 by omega)
  have h3 := callKey_cost P (by includes) j (wordsWith rd s.fp 2 (guestArgCounts.getD j 0))
    (wordsWith rd s.fp (2 + guestArgCounts.getD j 0) (guestRetCounts.getD j 0))
  rw [length_wordsWith, length_wordsWith] at h3
  unfold psAt at h1 h2
  simp only [max_self]
  generalize guestArgCounts.getD j 0 = a at *
  generalize guestRetCounts.getD j 0 = b at *
  nlinarith

/-- A state's key: of at most `56` argument codes and `10` return codes. -/
theorem entryKeyT_ok (s : Registers K) {j : ℕ} (hj : j < 2 ^ 64) :
    KeyOK 56 (entryKeyT rd s j) ∧ (entryKeyT rd s j).2.2.length ≤ 10 :=
  ⟨callKey_ok hj (by rw [length_wordsWith]; exact argCount_le j)
    (by rw [length_wordsWith]; have := retCount_le j; omega),
   by simp only [entryKeyT, callKey, List.length_map, length_wordsWith]; exact retCount_le j⟩

/-! ## The frame map -/

/-- Whether `j` is a function's index (`isFunctionIndexC`), `j` word-sized: at most `11`. -/
theorem isFunctionIndex_cost (hP : Includes P isFunctionIndexC.costDeps) (j : ℕ) (hj : j < 2 ^ 64) :
    machineCost P isFunctionIndexC.costIdx [encodeValue j] ≤ 11 := by
  rw [isFunctionIndexC.costEq P hP, limbs_of_lt hj]
  split_ifs <;> omega

include hrd hR in
/-- A frame's word (`frameWordAtC`): the table of frame cells (`guestLocsTableC`, a literal), a
read, at most `R + 1535`. -/
theorem frameWordAt_cost (hP : Includes P frameWordAtC.costDeps) (fp : K) (j : ℕ)
    (hj : j < 2 ^ 64) (v : V) :
    machineCost P frameWordAtC.costIdx [rdVal, encodeValue fp, encodeValue j, encodeValue v] ≤
      R + 1535 := by
  rw [frameWordAtC.costEq P hP rd rdVal hrd]
  have h0 := guestLocsTableC.costEq P (by includes)
  have h1 := isFunctionIndex_cost P (by includes) j hj
  have h2 := wordWith_cost P rd rdVal hrd R hR (W := 20) (by norm_num) (by norm_num) (by includes)
    fp _ (loc_lt (canonIndex j) v.idx)
  unfold psAt at h2
  split_ifs <;> omega

theorem canonIndex_lt64 (j : ℕ) : canonIndex j < 2 ^ 64 := by
  unfold canonIndex isFunctionIndex
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
  · norm_num

end Reads

end

end LeanVM.Cost.Bounds
