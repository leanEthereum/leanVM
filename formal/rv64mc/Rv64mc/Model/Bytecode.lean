module

public import Rv64mc.Model.KeccakGkr

/-!
# `bytecode.rs` as the Rust computes it

Mirrors of `crates/verifier/src/bytecode.rs` under `Model.Multilinear`'s conventions (a `u16` is a
`BitVec 16`, `as u16` is `BitVec.ofNat 16`, `E * K` is `mulKE`): the IV (`fiatShamirIvRust`), the
check that the words encode a program (`validEncodingRust`), the counting sort, the grouping of a
block's words, `Bytecode::new` (`newRust`) and `Bytecode::evaluate` (`evaluateRust`). A mirror fails
(`none`) exactly where the Rust returns `Err`; where the Rust panics it may return anything.

The statement has no counterpart of the encoding check (it verifies a proof for any words); the
IV is `fiatShamirIv` (`fiatShamirIvRust_eq`). What the walk needs of a prepared bytecode is
`BytecodeOk`. The counting sort permutes its items (`countingSortRust_perm`), so a block's members
hold exactly its nonzero words at their positions, whatever their order.
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
  LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The Fiat-Shamir IV -/

/-- `TAG`, `b"leanvm-v1"`: the statement's `versionTag` (its nine bytes, checked in
`Model.TestsWalk`). -/
def tagRust : List (BitVec 8) := byteBits versionTag

/-- `Bytecode::new`'s IV: `keccak_hash` of `TAG` then the words as little-endian bytes. -/
def fiatShamirIvRust (words : List (BitVec 64)) : List (BitVec 8) :=
  keccakHashRust (tagRust ++ words.flatMap toLeBytes)

/-! ## `is_valid_encoding_of_a_leanisa_program` -/

/-- Slot `s` of instruction `pc`: `stacked_bytecode[s * n + pc]`. -/
def slotRust (words : List (BitVec 64)) (n pc s : ℕ) : BitVec 64 := words.getD (s * n + pc) 0

/-- One instruction's check: slots `0..3` zero, slot `3` a one-hot opcode, and its operands'
shape. -/
def instructionOkRust (words : List (BitVec 64)) (n pc : ℕ) : Bool :=
  let slot := slotRust words n pc
  let zeroFrom := fun first ↦ (List.range' first (16 - first)).all fun s ↦ slot s == 0
  (List.range 3).all (fun s ↦ slot s == 0) &&
    match (List.range 6).find? (fun op ↦ slot 3 == 1#64 <<< op) with
    | some 3 =>
      ((slot 7 == 0 && slot 8 == 0) || (slot 7 == 1 && slot 8 == 0) ||
        (slot 7 == 0 && slot 8 == 1)) && zeroFrom 9
    | some 5 =>
      decide (slot 12 ≤ 1) && decide (slot 13 ≤ 1) &&
        ((slot 14 == 0 && slot 15 == 0) || (slot 14 == 1 && slot 15 == 0) ||
          (slot 14 == 1 && slot 15 == 1))
    | some _ => zeroFrom 7
    | none => false

/-- `is_valid_encoding_of_a_leanisa_program(stacked_bytecode)`. -/
def validEncodingRust (words : List (BitVec 64)) : Bool :=
  let n := words.length >>> 4
  (n != 0 && n &&& (n - 1) == 0) && words.length == n <<< 4 && decide (n ≤ 2 ^ 30) &&
    (List.range n).all (instructionOkRust words n)

/-! ## `counting_sort`, `group_by_word`, `block_members` -/

/-- `counting_sort(items, keys, key)`: count each key at `starts[key + 1]`, prefix sums, then
place each item at its key's next position. -/
def countingSortRust {α : Type} (items : List α) (keys : ℕ) (key : α → ℕ) : List α :=
  let counts := items.foldl (fun starts item ↦
    starts.set (key item + 1) (starts.getD (key item + 1) 0 + 1)) (List.replicate (keys + 1) 0)
  let starts := (List.range' 1 keys).foldl (fun starts k ↦
    starts.set k (starts.getD k 0 + starts.getD (k - 1) 0)) counts
  (items.foldl (fun (acc : List α × List ℕ) item ↦
    let k := key item
    (acc.1.set (acc.2.getD k 0) item, acc.2.set k (acc.2.getD k 0 + 1))) (items, starts)).1

/-- The byte `byte` of a word, the key of `group_by_word`'s passes. -/
def byteKey (byte : ℕ) (pair : BitVec 64 × BitVec 16) : ℕ :=
  ((pair.1 >>> (8 * byte % 64)).setWidth 8).toNat

/-- One iteration of `group_by_word`'s grouping loop: a new member unless the last has the word. -/
def groupStep (members : List (BitVec 64 × List (BitVec 16))) (pair : BitVec 64 × BitVec 16) :
    List (BitVec 64 × List (BitVec 16)) :=
  match members.getLast? with
  | some (last, pos) =>
    if last = pair.1 then members.dropLast ++ [(last, pos ++ [pair.2])]
    else members ++ [(pair.1, [pair.2])]
  | none => members ++ [(pair.1, [pair.2])]

/-- `group_by_word(block)`: the nonzero words with their positions, sorted by word a byte at a time
from the lowest, then grouped by runs. -/
def groupByWordRust (block : List (BitVec 64)) : List (BitVec 64 × List (BitVec 16)) :=
  let pairs := (block.zipIdx.filter fun wp ↦ wp.1 != 0).map fun wp ↦ (wp.1, BitVec.ofNat 16 wp.2)
  let pairs := (List.range 8).foldl (fun pairs byte ↦ countingSortRust pairs 256 (byteKey byte))
    pairs
  pairs.foldl groupStep []

/-- `block_members(block)`: the groups, ordered by a counting sort of their indices on their
position counts, each taken (`std::mem::take`) as it is read. -/
def blockMembersRust (block : List (BitVec 64)) : List (BitVec 64 × List (BitVec 16)) :=
  let members := groupByWordRust block
  let order := countingSortRust (List.range members.length) (block.length + 1)
    fun index ↦ (members.getD index (0, [])).2.length
  (order.foldl (fun (acc : List (BitVec 64 × List (BitVec 16)) ×
      List (BitVec 64 × List (BitVec 16))) index ↦
    let member := acc.2.getD index (0, [])
    (acc.1 ++ [member], acc.2.set index (member.1, []))) ([], members)).1

/-- `slice.chunks(size)`. -/
def chunksW {α : Type} (size : ℕ) (l : List α) : List (List α) :=
  if _h : l = [] ∨ size = 0 then []
  else l.take size :: chunksW size (l.drop size)
termination_by l.length
decreasing_by
  have h1 : l.length ≠ 0 := fun e ↦ _h (Or.inl (List.length_eq_zero_iff.mp e))
  have h2 : size ≠ 0 := fun e ↦ _h (Or.inr e)
  simp only [List.length_drop]
  omega

/-! ## `Bytecode` -/

/-- `Bytecode`: `len`, `fiat_shamir_iv`, `blocks`. -/
structure BytecodeRust where
  /-- `len`. -/
  len : ℕ
  /-- `fiat_shamir_iv`. -/
  fiatShamirIv : List (BitVec 8)
  /-- `blocks`. -/
  blocks : List (List (BitVec 64 × List (BitVec 16)))

/-- `BLOCK_LOG`. -/
def blockLog : ℕ := 14

/-- `Bytecode::new(stacked_bytecode)`: `BytecodeShape` unless the words encode a program. -/
def newRust (words : List (BitVec 64)) : Option BytecodeRust :=
  if validEncodingRust words then
    some ⟨words.length, fiatShamirIvRust words, (chunksW (2 ^ blockLog) words).map blockMembersRust⟩
  else none

/-- One block's value: `E::sum` over its members of `E::sum` of their positions' low weights, times
the word. -/
def blockValueRust (lowWeights : List E) (block : List (BitVec 64 × List (BitVec 16))) : E :=
  (block.map fun (word, pos) ↦
    mulKE ((pos.map fun i ↦ lowWeights.getD i.toNat 0).foldl (· + ·) 0) (BF64.ofBitVec word)).foldl
    (· + ·) 0

/-- `Bytecode::evaluate(point)`: the size check (`MultilinearSize`), then each block's value
weighed by the high coordinates' eq table. -/
def evaluateRust (bc : BytecodeRust) (point : List E) : Option E :=
  if point.length < 64 ∧ bc.len = 2 ^ point.length then
    let low := point.take (min point.length blockLog)
    let high := point.drop (min point.length blockLog)
    let lowWeights := eqKernelRust low
    let highWeights := eqKernelRust high
    some (((bc.blocks.zip highWeights).map fun (block, weight) ↦
      weight * blockValueRust lowWeights block).foldl (· + ·) 0)
  else none

/-! ## The counting sort permutes its items -/

section CountingSort

variable {α : Type} (key : α → ℕ)

private def cntK (l : List α) (k : ℕ) : ℕ := l.countP fun x ↦ key x = k

private def belowK (l : List α) (k : ℕ) : ℕ := l.countP fun x ↦ key x < k

private theorem belowK_succ (l : List α) (k : ℕ) :
    belowK key l (k + 1) = belowK key l k + cntK key l k := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [belowK, cntK, List.countP_cons] at ih ⊢
    rw [ih]
    by_cases h1 : key x < k
    · simp [h1, show key x < k + 1 by omega, show key x ≠ k by omega]; omega
    · by_cases h2 : key x = k
      · simp [h2]; omega
      · simp [h1, h2, show ¬ key x < k + 1 by omega]

private theorem belowK_mono (l : List α) {k k' : ℕ} (h : k ≤ k') :
    belowK key l k ≤ belowK key l k' :=
  List.countP_mono_left fun x _ hx ↦ by simp only [decide_eq_true_eq] at hx ⊢; omega

private theorem belowK_all (l : List α) (keys : ℕ) (h : ∀ x ∈ l, key x < keys) :
    belowK key l keys = l.length := by
  rw [belowK, List.countP_eq_length]
  intro x hx
  simpa using h x hx

private theorem getD_setN (l : List ℕ) (i j a : ℕ) :
    (l.set i a).getD j 0 = if i = j ∧ i < l.length then a else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < l.length
    · simp [hl]
    · simp [hl]
  · simp [h]

private theorem counts_spec (keys : ℕ) : ∀ (P : List α) (init : List ℕ),
    (∀ x ∈ P, key x < keys) → init.length = keys + 1 →
    (P.foldl (fun st item ↦ st.set (key item + 1) (st.getD (key item + 1) 0 + 1)) init).length =
        keys + 1 ∧
      ∀ k, (P.foldl (fun st item ↦ st.set (key item + 1) (st.getD (key item + 1) 0 + 1))
        init).getD k 0 = init.getD k 0 + if k = 0 then 0 else cntK key P (k - 1)
  | [], init, _, hl => ⟨hl, fun k ↦ by split <;> simp [cntK]⟩
  | x :: P, init, hP, hl => by
    have hx := hP x (by simp)
    obtain ⟨h1, h2⟩ := counts_spec keys P (init.set (key x + 1) (init.getD (key x + 1) 0 + 1))
      (fun y hy ↦ hP y (by simp [hy])) (by rw [List.length_set, hl])
    refine ⟨h1, fun k ↦ ?_⟩
    rw [List.foldl_cons, h2, getD_setN]
    simp only [cntK, List.countP_cons]
    by_cases hk : key x + 1 = k
    · subst hk
      simp [hl, hx]
      omega
    · simp only [hk, false_and, ↓reduceIte]
      split
      · rfl
      · simp only [decide_eq_true_eq, show ¬ key x = k - 1 by omega, ↓reduceIte, add_zero]

private theorem starts_spec (items : List α) (keys : ℕ) (counts : List ℕ)
    (hc : counts.length = keys + 1) (h0 : counts.getD 0 0 = 0)
    (hk : ∀ k, 1 ≤ k → counts.getD k 0 = cntK key items (k - 1)) :
    ∀ m ≤ keys, ((List.range' 1 m).foldl (fun st k ↦
        st.set k (st.getD k 0 + st.getD (k - 1) 0)) counts).length = keys + 1 ∧
      (∀ k ≤ m, ((List.range' 1 m).foldl (fun st k ↦
        st.set k (st.getD k 0 + st.getD (k - 1) 0)) counts).getD k 0 = belowK key items k) ∧
      ∀ k, m < k → ((List.range' 1 m).foldl (fun st k ↦
        st.set k (st.getD k 0 + st.getD (k - 1) 0)) counts).getD k 0 = counts.getD k 0
  | 0, _ => ⟨hc, fun k hk0 ↦ by
      rw [show k = 0 by omega, show (List.range' 1 0) = [] from rfl, List.foldl_nil, h0]
      simp [belowK],
    fun k _ ↦ rfl⟩
  | m + 1, hm => by
    obtain ⟨h1, h2, h3⟩ := starts_spec items keys counts hc h0 hk m (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.one_mul]
    refine ⟨by rw [List.length_set, h1], fun k hk' ↦ ?_, fun k hk' ↦ ?_⟩
    · rw [getD_setN, h1]
      by_cases hk2 : 1 + m = k
      · subst hk2
        rw [ite_eq_left ⟨rfl, by omega⟩, h3 _ (by omega), hk _ (by omega),
          show 1 + m - 1 = m by omega, h2 m le_rfl, show 1 + m = m + 1 by omega, belowK_succ]
        omega
      · rw [ite_eq_right (by omega), h2 k (by omega)]
    · rw [getD_setN, ite_eq_right (by omega), h3 k (by omega)]

private theorem cntK_take_le (items : List α) {i j : ℕ} (h : i ≤ j) (k : ℕ) :
    cntK key (items.take i) k ≤ cntK key (items.take j) k :=
  (List.take_sublist_take_left h).countP_le

private theorem cntK_take_le_all (items : List α) (i k : ℕ) :
    cntK key (items.take i) k ≤ cntK key items k :=
  (List.take_sublist i items).countP_le

variable [Inhabited α]

/-- Where the counting sort puts item `i`: past every item of a smaller key and every earlier one
of its key. -/
private def posK (items : List α) (i : ℕ) : ℕ :=
  belowK key items (key (items.getD i default)) +
    cntK key (items.take i) (key (items.getD i default))

private theorem cntK_take_succ (items : List α) {i : ℕ} (hi : i < items.length) (k : ℕ) :
    cntK key (items.take (i + 1)) k =
      cntK key (items.take i) k + if key (items.getD i default) = k then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, cntK, List.countP_append,
    List.countP_singleton, ← cntK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  simp

private theorem posK_lt (items : List α) (keys : ℕ) (h : ∀ x ∈ items, key x < keys) {i : ℕ}
    (hi : i < items.length) : posK key items i < items.length := by
  have hx : key (items.getD i default) < keys := h _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact List.getElem_mem hi)
  have h1 := cntK_take_succ key items hi (key (items.getD i default))
  have h2 := cntK_take_le_all key items (i + 1) (key (items.getD i default))
  have h3 := belowK_succ key items (key (items.getD i default))
  have h4 := belowK_mono key items (show key (items.getD i default) + 1 ≤ keys by omega)
  rw [belowK_all key items keys h] at h4
  simp only [↓reduceIte] at h1
  unfold posK
  omega

private theorem posK_le_of_lt (items : List α) {i i' : ℕ} (hi : i < items.length)
    (hk : key (items.getD i default) < key (items.getD i' default)) :
    posK key items i < posK key items i' := by
  have h1 := cntK_take_succ key items hi (key (items.getD i default))
  have h2 := cntK_take_le_all key items (i + 1) (key (items.getD i default))
  have h3 := belowK_succ key items (key (items.getD i default))
  have h4 := belowK_mono key items (show key (items.getD i default) + 1 ≤
    key (items.getD i' default) by omega)
  simp only [↓reduceIte] at h1
  unfold posK
  omega

private theorem posK_injective (items : List α) {i i' : ℕ} (hi : i < items.length)
    (hi' : i' < items.length) (h : posK key items i = posK key items i') : i = i' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · by_cases hk : key (items.getD i default) = key (items.getD i' default)
    · have h1 := cntK_take_succ key items hi (key (items.getD i default))
      have h2 := cntK_take_le key items (show i + 1 ≤ i' by omega) (key (items.getD i default))
      simp only [↓reduceIte] at h1
      unfold posK at h
      rw [← hk] at h
      omega
    · rcases Nat.lt_or_gt_of_ne hk with hk | hk
      · exact absurd h (posK_le_of_lt key items hi hk).ne
      · exact absurd h (posK_le_of_lt key items hi' hk).ne'
  · by_cases hk : key (items.getD i default) = key (items.getD i' default)
    · have h1 := cntK_take_succ key items hi' (key (items.getD i' default))
      have h2 := cntK_take_le key items (show i' + 1 ≤ i by omega) (key (items.getD i' default))
      simp only [↓reduceIte] at h1
      unfold posK at h
      rw [hk] at h
      omega
    · rcases Nat.lt_or_gt_of_ne hk with hk | hk
      · exact absurd h (posK_le_of_lt key items hi hk).ne
      · exact absurd h (posK_le_of_lt key items hi' hk).ne'

private theorem getD_setA (l : List α) (i j : ℕ) (a : α) :
    (l.set i a).getD j default = if i = j ∧ i < l.length then a else l.getD j default := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h
    by_cases hl : i < l.length
    · simp [hl]
    · simp [hl]
  · simp [h]

private theorem place_spec (items : List α) (keys : ℕ) (h : ∀ x ∈ items, key x < keys)
    (starts : List ℕ) (hs : starts.length = keys + 1)
    (hst : ∀ k ≤ keys, starts.getD k 0 = belowK key items k) :
    ∀ j ≤ items.length,
      let R := (items.take j).foldl (fun (acc : List α × List ℕ) item ↦
        (acc.1.set (acc.2.getD (key item) 0) item,
          acc.2.set (key item) (acc.2.getD (key item) 0 + 1))) (items, starts)
      R.1.length = items.length ∧ R.2.length = keys + 1 ∧
        (∀ k < keys + 1, R.2.getD k 0 = belowK key items k + cntK key (items.take j) k) ∧
        (∀ i < j, R.1.getD (posK key items i) default = items.getD i default)
  | 0, _ => ⟨rfl, hs, fun k hk ↦ by
      rw [List.take_zero, List.foldl_nil]
      show starts.getD k 0 = _
      rw [hst k (by omega)]
      simp [cntK], fun i hi ↦ by omega⟩
  | j + 1, hj => by
    obtain ⟨h1, h2, h3, h4⟩ := place_spec items keys h starts hs hst j (by omega)
    have hjl : j < items.length := by omega
    have hx : items.getD j default ∈ items := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
      exact List.getElem_mem hjl
    have hkx := h _ hx
    rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hgx : items[j] = items.getD j default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
    rw [hgx]
    generalize hR : (items.take j).foldl (fun (acc : List α × List ℕ) item ↦
        (acc.1.set (acc.2.getD (key item) 0) item,
          acc.2.set (key item) (acc.2.getD (key item) 0 + 1))) (items, starts) = R at h1 h2 h3 h4
    have hpos : R.2.getD (key (items.getD j default)) 0 = posK key items j := by
      rw [h3 _ (by omega)]
      rfl
    refine ⟨by rw [List.length_set, h1], by rw [List.length_set, h2], fun k hk ↦ ?_,
      fun i hi ↦ ?_⟩
    · have hc : cntK key (items.take j ++ [items.getD j default]) k =
          cntK key (items.take j) k + if key (items.getD j default) = k then 1 else 0 := by
        simp [cntK, List.countP_append]
      rw [getD_setN, h2, hc]
      by_cases hkk : key (items.getD j default) = k
      · subst hkk
        rw [ite_eq_left ⟨rfl, by omega⟩, h3 _ hk, ite_eq_left rfl]
        omega
      · rw [ite_eq_right (fun e ↦ hkk e.1), h3 k hk, ite_eq_right hkk, add_zero]
    · rw [getD_setA, hpos, h1]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left ⟨rfl, posK_lt key items keys h hjl⟩]
      · rw [ite_eq_right (fun e ↦ hij (posK_injective key items hjl (by omega) e.1).symm),
          h4 i (by omega)]

/-- **The counting sort permutes its items**, every key below `keys`. -/
theorem countingSortRust_perm (items : List α) (keys : ℕ) (h : ∀ x ∈ items, key x < keys) :
    (countingSortRust items keys key).Perm items := by
  obtain ⟨hc1, hc2⟩ := counts_spec key keys items (List.replicate (keys + 1) 0) h (by simp)
  obtain ⟨hs1, hs2, -⟩ := starts_spec key items keys _ hc1
    (by rw [hc2]; simp) (fun k hk ↦ by
      rw [hc2, ite_eq_right (show k ≠ 0 by omega), List.getD_eq_getElem?_getD,
        List.getElem?_replicate]
      split <;> simp)
    keys le_rfl
  unfold countingSortRust
  dsimp only
  generalize (List.range' 1 keys).foldl (fun st k ↦ st.set k (st.getD k 0 + st.getD (k - 1) 0))
    (items.foldl (fun starts item ↦ starts.set (key item + 1) (starts.getD (key item + 1) 0 + 1))
      (List.replicate (keys + 1) 0)) = starts at hs1 hs2 ⊢
  obtain ⟨h1, -, -, h4⟩ := place_spec key items keys h starts hs1 hs2 items.length le_rfl
  rw [List.take_length] at h1 h4
  generalize items.foldl (fun (acc : List α × List ℕ) item ↦
      (acc.1.set (acc.2.getD (key item) 0) item,
        acc.2.set (key item) (acc.2.getD (key item) 0 + 1))) (items, starts) = R at h1 h4 ⊢
  let f : Fin items.length → Fin items.length :=
    fun i ↦ ⟨posK key items i, posK_lt key items keys h i.isLt⟩
  have hf : Function.Injective f := fun a b hab ↦
    Fin.ext (posK_injective key items a.isLt b.isLt (congrArg Fin.val hab))
  let σ := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hR : R.1 = List.ofFn ((fun i : Fin items.length ↦ items[i.val]) ∘ σ.symm) := by
    apply List.ext_getElem (by simp [h1])
    intro q hq hq'
    simp only [List.getElem_ofFn, Function.comp_apply]
    have hσ : f (σ.symm ⟨q, by simpa using hq'⟩) = ⟨q, by simpa using hq'⟩ :=
      σ.apply_symm_apply _
    have := h4 (σ.symm ⟨q, by simpa using hq'⟩).val (σ.symm _).isLt
    rw [show posK key items (σ.symm ⟨q, by simpa using hq'⟩).val = q from
      congrArg Fin.val hσ] at this
    rw [← List.getElem_eq_getD default, ← List.getElem_eq_getD default] at this
    exact this
  show R.1.Perm items
  rw [hR]
  have := Equiv.Perm.ofFn_comp_perm σ.symm (fun i : Fin items.length ↦ items[i.val])
  rwa [List.ofFn_getElem] at this

end CountingSort

/-! ## The IV is the statement's -/

theorem ivPreimage_eq (words : List K) :
    tagRust ++ (words.map BF64.toBitVec).flatMap toLeBytes =
      byteBits (versionTag ++ words.flatMap K.toBytes) := by
  rw [tagRust, byteBits, byteBits, List.map_append, List.map_flatMap, List.flatMap_map]
  exact congrArg _ (List.flatMap_congr fun a _ ↦ toLeBytes_toBitVec (K.lane a))

/-- **The IV is `fiatShamirIv`**, as bytes. -/
theorem fiatShamirIvRust_eq (words : List K) :
    fiatShamirIvRust (words.map BF64.toBitVec) = digestBits (fiatShamirIv words) := by
  rw [fiatShamirIvRust, ivPreimage_eq, keccakHashRust_eq]
  rfl

/-- What a prepared bytecode is to the walk: the words' count, their IV, and an `evaluate` that
is their multilinear extension wherever the size check passes. `Bytecode::new` builds one
(`newRust_ok`). -/
structure BytecodeOk (words : List K) (bc : BytecodeRust) : Prop where
  len : bc.len = words.length
  iv : bc.fiatShamirIv = digestBits (fiatShamirIv words)
  evaluate : ∀ point, evaluateRust bc point =
    if point.length < 64 ∧ words.length = 2 ^ point.length then
      some (multilinearEval (words.map ofK) point) else none

end

end Rv64mc.Model
