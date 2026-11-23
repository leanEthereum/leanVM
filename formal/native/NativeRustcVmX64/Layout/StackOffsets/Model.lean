module

public import NativeRustcVmX64.Spec.Layout
public import NativeVm.Math.Layout
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Frame

/-!
# `stack_offsets` on x86-64: the model, the order array, the offsets

- The model (`ord`, `P`): the order `insertion_sort` leaves in the order array (`ord`, a
  permutation of the indices, `ord_perm`), and the layout after its first `k` blocks (`P`, the
  model's fold `placeStep` along it); `stackOffsets` is `P` after all (`stackOffsets_eq`).
  `OffsetsFit` fails where the code fails: a size past `63` (`not_fit_size`), a sum past `u64`
  (`not_fit_sum`), and holds where the sum stays a `u64` (`fit_end`).
- Memory: the order array's first `j` words (`Ords`), the offsets placed so far (`OutAt`), each
  kept by the writes of the next block (`Ords.step`, `OutAt.step`) and complete at the end
  (`OutAt.words`).
-/

namespace NativeRustcVmX64.Layout.StackOffsets

open NativeRustcX64 NativeVm.Model NativeRustcVm.Layout
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeVm.Math.Layout (placeStep getD_set! stackOffsets_order)
open LeanVM.Protocol.Verifier (log2Ceil)

@[expose] public section

/-! ## The model -/

/-- The number of blocks. -/
abbrev n (m : MachineData) : Nat := (reg m .rsi).toNat
/-- The sizes. -/
abbrev sizes (m : MachineData) : Array Nat := natsOf m (reg m .rdi) (reg m .rsi).toNat
/-- A block's log-size, `0` past the sizes. -/
abbrev size (m : MachineData) (i : Nat) : Nat := (sizes m).getD i 0
/-- The order `insertion_sort` leaves in the order array. -/
def ord (m : MachineData) : Array Nat :=
  insertionSort (sortLt (size m)) (Array.range (n m))
/-- The layout after the first `k` blocks of the order. -/
def P (m : MachineData) (k : Nat) : Array Nat × Nat :=
  ((ord m).toList.take k).foldl (placeStep (size m)) (Array.replicate (n m) 0, 0)

theorem toNat_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem size_sizes (m : MachineData) : (sizes m).size = n m := by
  simp [sizes, natsOf, NativeRustcVm.wordsOf]

theorem ord_perm (m : MachineData) : (ord m).toList.Perm (List.range (n m)) := by
  have h : (insertionSort (fun i j ↦ decide (size m j < size m i) ||
      (decide (size m i = size m j) && decide (i < j))) (Array.range (sizes m).size)).toList.Perm
      (List.range (sizes m).size) := (stackOffsets_order (sizes m)).1
  rw [size_sizes] at h
  exact h

theorem ord_size (m : MachineData) : (ord m).size = n m := by
  simpa using (ord_perm m).length_eq

theorem ord_mem {m : MachineData} {i : Nat} (h : i ∈ (ord m).toList) : i < n m :=
  List.mem_range.mp ((ord_perm m).mem_iff.mp h)

theorem ord_lt {m : MachineData} {k : Nat} (hk : k < (ord m).size) : (ord m)[k] < n m :=
  ord_mem (Array.getElem_mem_toList hk)

theorem foldl_snd (sz : Nat → Nat) :
    ∀ (L : List Nat) (acc : Array Nat × Nat),
      (L.foldl (placeStep sz) acc).2 = acc.2 + (L.map (2 ^ sz ·)).sum
  | [], acc => by simp
  | x :: L, acc => by
    rw [List.foldl_cons, foldl_snd sz L, List.map_cons, List.sum_cons, placeStep]
    simp only
    omega

theorem foldl_size (sz : Nat → Nat) :
    ∀ (L : List Nat) (acc : Array Nat × Nat), (L.foldl (placeStep sz) acc).1.size = acc.1.size
  | [], acc => rfl
  | x :: L, acc => by
    rw [List.foldl_cons, foldl_size sz L, placeStep]
    simp

theorem P_snd (m : MachineData) (k : Nat) :
    (P m k).2 = (((ord m).toList.take k).map (2 ^ size m ·)).sum := by
  rw [P, foldl_snd, Nat.zero_add]

theorem P_size (m : MachineData) (k : Nat) : (P m k).1.size = n m := by
  rw [P, foldl_size]; simp

theorem P_zero (m : MachineData) : P m 0 = (Array.replicate (n m) 0, 0) := by
  simp [P]

theorem P_succ {m : MachineData} {k : Nat} (hk : k < (ord m).size) :
    P m (k + 1) = placeStep (size m) (P m k) (ord m)[k] := by
  simp [P, List.take_add_one, List.foldl_append, hk]

theorem P_succ_snd {m : MachineData} {k : Nat} (hk : k < (ord m).size) :
    (P m (k + 1)).2 = (P m k).2 + 2 ^ size m (ord m)[k] := by
  rw [P_succ hk, placeStep]

theorem P_succ_getD {m : MachineData} {k : Nat} (hk : k < (ord m).size) (i : Nat) :
    (P m (k + 1)).1.getD i 0 = if i = (ord m)[k] then (P m k).2 else (P m k).1.getD i 0 := by
  rw [P_succ hk, placeStep, getD_set!, P_size]
  have := ord_lt hk
  by_cases h : i = (ord m)[k] <;> simp [h, this]

theorem take_length_ord (m : MachineData) : (ord m).toList.take (n m) = (ord m).toList :=
  List.take_of_length_le (by simp [ord_size])

/-- **The model's `stackOffsets`** is `P` after every block. -/
theorem stackOffsets_eq (m : MachineData) :
    stackOffsets (sizes m) = ((P m (n m)).1, log2Ceil (P m (n m)).2) := by
  have e : stackOffsets (sizes m) =
      (((ord m).toList.foldl (placeStep (size m)) (Array.replicate (n m) 0, 0)).1,
        log2Ceil ((ord m).toList.foldl (placeStep (size m)) (Array.replicate (n m) 0, 0)).2) := by
    rw [Array.foldl_toList]
    unfold stackOffsets
    simp only [size_sizes]
    rfl
  rw [e, P, take_length_ord]

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp
  | y :: _, _, .tail _ h => by have := le_sum_of_mem h; simp; omega

theorem sum_take_le (f : Nat → Nat) (L : List Nat) (j : Nat) :
    ((L.take j).map f).sum ≤ (L.map f).sum := by
  conv_rhs => rw [← List.take_append_drop j L]
  rw [List.map_append, List.sum_append]
  omega

/-- The total of the sizes, along the order. -/
theorem total_eq (m : MachineData) :
    ((sizes m).toList.map (2 ^ ·)).sum = ((ord m).toList.map (2 ^ size m ·)).sum := by
  have e : (sizes m).toList.map (2 ^ ·) = (List.range (n m)).map (2 ^ size m ·) := by
    apply List.ext_getElem (by simp [size_sizes])
    intro i h1 h2
    have hi : i < (sizes m).size := by simpa using h1
    simp [size, Array.getD, hi]
  rw [e, ((ord_perm m).map _).sum_eq]

/-- A size past `63`: the blocks do not fit. -/
theorem not_fit_size {m : MachineData} {i : Nat} (hi : i < n m) (h : 64 ≤ size m i) :
    ¬OffsetsFit (sizes m) := fun hf ↦ by
  have hi' : i < (sizes m).size := by rw [size_sizes]; exact hi
  have := hf.1 _ (Array.getElem_mem hi')
  have e : size m i = (sizes m)[i] := by simp [size, Array.getD, hi']
  omega

/-- A sum past `u64`: the blocks do not fit. -/
theorem not_fit_sum {m : MachineData} {k : Nat} (hk : k < (ord m).size)
    (h : 2 ^ 64 ≤ (P m k).2 + 2 ^ size m (ord m)[k]) : ¬OffsetsFit (sizes m) := fun hf ↦ by
  have h1 := hf.2
  rw [total_eq] at h1
  have h2 := sum_take_le (2 ^ size m ·) (ord m).toList (k + 1)
  rw [← P_snd, P_succ_snd hk] at h2
  omega

/-- The sum a `u64`: the blocks fit. -/
theorem fit_end {m : MachineData} (h : (P m (n m)).2 < 2 ^ 64) : OffsetsFit (sizes m) := by
  have ht : ((sizes m).toList.map (2 ^ ·)).sum = (P m (n m)).2 := by
    rw [total_eq, P_snd, take_length_ord]
  refine ⟨fun s hs ↦ ?_, by rw [ht]; exact h⟩
  have h1 := le_sum_of_mem (List.mem_map_of_mem (f := (2 ^ ·)) (Array.mem_toList_iff.mpr hs))
  rw [ht] at h1
  by_contra hc
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.le_of_not_lt hc)
  omega

/-- `P`'s sum after `j` blocks is at most the total. -/
theorem P_le {m : MachineData} (j : Nat) : (P m j).2 ≤ (P m (n m)).2 := by
  rw [P_snd, P_snd, take_length_ord]
  exact sum_take_le _ _ _

/-! ## Memory -/

/-- The order array: byte `16` of the frame. -/
def ob (m : MachineData) : BitVec 64 := stackBelow m 1328 + BitVec.ofNat 64 16
/-- `offsets`. -/
abbrev out (m : MachineData) : BitVec 64 := reg m .rdx
/-- `offsets`' length. -/
abbrev cap (m : MachineData) : Nat := (reg m .rcx).toNat

/-- **The order array's first `j` words**: `0`, …, `j - 1`. -/
def Ords (m0 : MachineData) (j : Nat) (d : Mem 64) : Prop :=
  ∀ t < j, WordAt d (ob m0 + BitVec.ofNat 64 (8 * t)) t.toUInt64

/-- **`c` more words of the order array**, written by a block into `8 c` bytes from word `j`. -/
theorem Ords.step {m0 : MachineData} {j c : Nat} {d d' : Mem 64} (h : Ords m0 j d)
    (hnw : NativeRustcVm.NoWrap (ob m0) 1264) (hle : 8 * (j + c) ≤ 1264)
    (hs : ∀ p, ¬NativeRustcVm.InRange (ob m0 + BitVec.ofNat 64 (8 * j)) (8 * c) p →
      d'.get? p = d.get? p)
    (hnew : ∀ t, j ≤ t → t < j + c → WordAt d' (ob m0 + BitVec.ofNat 64 (8 * t)) t.toUInt64) :
    Ords m0 (j + c) d' := fun t ht ↦ by
  by_cases htj : t < j
  · refine NativeRustcVm.Transcript.bytesAt_congr (h t htj) fun q hq ↦ hs _ ?_
    have hq8 : q < 8 := by simpa [NativeRustcVm.length_wordBytes] using hq
    rw [NativeRustcVm.addr_add]
    exact NativeRustcVm.not_inRange_sub (a := ob m0) (N := 1264) (o := 8 * j) (m := 8 * c)
      (i := 8 * t + q) hnw (by omega) (by omega) (by omega)
  · exact hnew t (by omega) ht

/-- The order array's words: `natsOf` reads the indices. -/
theorem natsOf_ords {m0 st : MachineData} {a : BitVec 64} (ha : a = ob m0) {j : Nat}
    (hj : j < 2 ^ 64) (h : Ords m0 j st.dmem) : natsOf st a j = Array.range j := by
  have hl : (wordsOf st.dmem a j).map UInt64.toNat = List.range j := by
    apply List.ext_getElem (by simp [NativeRustcVm.wordsOf])
    intro t h1 h2
    have ht : t < j := by simpa using h2
    simp only [NativeRustcVm.wordsOf, List.getElem_map, List.getElem_range]
    rw [ha, NativeRustcVm.wordOf_of_wordAt (h t ht)]
    exact toNat_toUInt64 (by omega)
  rw [natsOf, hl]
  apply Array.ext'
  simp

/-- **The offsets placed after `k` blocks.** -/
def OutAt (m0 : MachineData) (k : Nat) (d : Mem 64) : Prop :=
  ∀ i ∈ (ord m0).toList.take k,
    WordAt d (out m0 + BitVec.ofNat 64 (8 * i)) ((P m0 k).1.getD i 0).toUInt64

theorem outAt_zero (m0 : MachineData) (d : Mem 64) : OutAt m0 0 d := by
  intro i hi; simp at hi

/-- **Block `k` placed**: `P k`'s sum stored at its offset, the others kept. -/
theorem OutAt.step {m0 : MachineData} {k : Nat} {d d' : Mem 64} (h : OutAt m0 k d)
    (hk : k < (ord m0).size) (hnw : NativeRustcVm.NoWrap (out m0) (8 * cap m0))
    (hcap : n m0 ≤ cap m0)
    (hw : WordAt d' (out m0 + BitVec.ofNat 64 (8 * (ord m0)[k])) (P m0 k).2.toUInt64)
    (hs : ∀ p, ¬NativeRustcVm.InRange (out m0 + BitVec.ofNat 64 (8 * (ord m0)[k])) 8 p →
      d'.get? p = d.get? p) : OutAt m0 (k + 1) d' := by
  intro i hi
  rw [P_succ_getD hk]
  have hik := ord_lt hk
  rw [List.take_add_one, List.mem_append, Array.getElem?_toList, Array.getElem?_eq_getElem hk] at hi
  by_cases he : i = (ord m0)[k]
  · simp only [he, ↓reduceIte]; exact hw
  · simp only [he, ↓reduceIte]
    have hi' : i ∈ (ord m0).toList.take k := by
      rcases hi with hi | hi
      · exact hi
      · simp at hi; exact absurd hi he
    have hin : i < n m0 := ord_mem (List.mem_of_mem_take hi')
    refine NativeRustcVm.Transcript.bytesAt_congr (h i hi') fun q hq ↦ hs _ ?_
    have hq8 : q < 8 := by simpa [NativeRustcVm.length_wordBytes] using hq
    rw [NativeRustcVm.addr_add]
    refine NativeRustcVm.not_inRange_sub (a := out m0) (N := 8 * cap m0) (o := 8 * (ord m0)[k])
      (m := 8) (i := 8 * i + q) hnw (by omega) (by omega) ?_
    omega

/-- **Every block placed**: the offsets are `P`'s. -/
theorem OutAt.words {m0 : MachineData} {d : Mem 64} (h : OutAt m0 (n m0) d) :
    WordsAt d (out m0) (natWords (P m0 (n m0)).1) := by
  rw [NativeRustcVm.wordsAt_iff]
  intro t ht
  have ht' : t < (P m0 (n m0)).1.size := by simpa [natWords] using ht
  have hmem : t ∈ (ord m0).toList.take (n m0) := by
    rw [take_length_ord]
    exact (ord_perm m0).mem_iff.mpr (List.mem_range.mpr (by rw [P_size] at ht'; exact ht'))
  have := h t hmem
  simp only [natWords, List.getElem_map, Array.getElem_toList]
  rw [show (P m0 (n m0)).1[t] = (P m0 (n m0)).1.getD t 0 by simp [Array.getD, ht']]
  exact this

/-- Word `j` of the order array. -/
theorem ord_word {m0 : MachineData} {d : Mem 64} (h : WordsAt d (ob m0) (natWords (ord m0)))
    {j : Nat} (hj : j < (ord m0).size) :
    WordAt d (ob m0 + BitVec.ofNat 64 (8 * j)) (ord m0)[j].toUInt64 := by
  have := NativeRustcVm.WordsAt.getElem h (i := j) (by simp [natWords]; exact hj)
  simpa [natWords] using this

/-- Entry `t` of `natsOf`. -/
theorem natsOf_getD (m : MachineData) (a : BitVec 64) {n t : Nat} (ht : t < n) :
    (natsOf m a n).getD t 0 = (wordOf m.dmem (a + BitVec.ofNat 64 (8 * t))).toNat := by
  simp [natsOf, NativeRustcVm.wordsOf, Array.getD, ht]

end

end NativeRustcVmX64.Layout.StackOffsets
