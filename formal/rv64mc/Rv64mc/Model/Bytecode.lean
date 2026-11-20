module

public import Rv64mc.Model.KeccakGkr

/-!
# `bytecode.rs` as the Rust computes it

Mirrors of `crates/verifier/src/bytecode.rs` under `Model.Multilinear`'s conventions (a `u16` is a
`BitVec 16`, `as u16` is `BitVec.ofNat 16`, `E * K` is `mulKE`): the IV (`fiatShamirIvRust`), the
check that the words encode a program (`validEncodingRust`), the counting sort, the grouping of a
block's words, `Bytecode::new` (`newRust`) and `Bytecode::evaluate` (`evaluateRust`). A mirror fails
(`none`) exactly where the Rust returns `Err`; where the Rust panics it may return anything.

The statement has no counterpart of the encoding check (it verifies a proof for any words), but
every program's bytecode passes it (`validEncodingRust_bytecodeWords`); the IV is `fiatShamirIv`
(`fiatShamirIvRust_eq`). What the walk needs of a prepared bytecode is `BytecodeOk`, which
`Bytecode::new` gives (`newRust_ok`): the counting sort permutes its items
(`countingSortRust_perm`), so a block's members hold exactly its nonzero words at their positions,
and `evaluate`'s blocks, weighed by the eq table's low and high coordinates, sum to the
multilinear extension (`multilinearEval_eq_sum`, `eqKernel_split`).
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
    rw [List.foldl_cons, h2, getD_set]
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
    · rw [getD_set, h1]
      by_cases hk2 : 1 + m = k
      · subst hk2
        rw [ite_eq_left ⟨rfl, by omega⟩, h3 _ (by omega), hk _ (by omega),
          show 1 + m - 1 = m by omega, h2 m le_rfl, show 1 + m = m + 1 by omega, belowK_succ]
        omega
      · rw [ite_eq_right (by omega), h2 k (by omega)]
    · rw [getD_set, ite_eq_right (by omega), h3 k (by omega)]

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
      rw [getD_set, h2, hc]
      by_cases hkk : key (items.getD j default) = k
      · subst hkk
        rw [ite_eq_left ⟨rfl, by omega⟩, h3 _ hk, ite_eq_left rfl]
        omega
      · rw [ite_eq_right (fun e ↦ hkk e.1), h3 k hk, ite_eq_right hkk, add_zero]
    · rw [getD_set, hpos, h1]
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

/-! ## The multilinear extension as an eq-weighted sum -/

section EqSum

private theorem foldPairs_getElem?' (r : E) : ∀ (A : List E) (i : ℕ), (foldPairs r A)[i]? =
    if i < A.length / 2 then some (A.getD (2 * i) 0 * (1 + r) + A.getD (2 * i + 1) 0 * r)
    else none
  | [], i => by simp [foldPairs]
  | [a], i => by simp [foldPairs]
  | a :: b :: rest, 0 => by simp [foldPairs]
  | a :: b :: rest, i + 1 => by
    rw [foldPairs, List.getElem?_cons_succ, foldPairs_getElem?' r rest i]
    have h1 : 2 * (i + 1) = 2 * i + 1 + 1 := by ring
    simp only [List.length_cons, h1, List.getD_cons_succ]
    congr 1
    apply propext
    omega

private theorem foldPairs_length' (r : E) : ∀ (A : List E), (foldPairs r A).length = A.length / 2
  | [] => by simp [foldPairs]
  | [a] => by simp [foldPairs]
  | a :: b :: rest => by
    rw [foldPairs, List.length_cons, foldPairs_length' r rest]
    simp only [List.length_cons]
    omega

private theorem eqKernel_foldl (rs : List E) : ∀ out : List E,
    rs.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out =
      (eqKernel rs).flatMap fun w ↦ out.map (· * w) := by
  induction rs with
  | nil => intro out; simp [eqKernel]
  | cons r rs ih =>
    intro out
    have he : eqKernel (r :: rs) = (eqKernel rs).flatMap fun w ↦
        ([1].map (· * (1 + r)) ++ [1].map (· * r)).map (· * w) := ih _
    rw [List.foldl_cons, ih, he, List.flatMap_assoc]
    apply List.flatMap_congr
    intro w _
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.map_append, List.map_map]
    refine congrArg₂ (· ++ ·) (List.map_congr_left fun x _ ↦ ?_) (List.map_congr_left fun x _ ↦ ?_)
    · simp only [Function.comp_apply]
      ring
    · simp only [Function.comp_apply]
      ring

private theorem eqKernel_append (low high : List E) :
    eqKernel (low ++ high) = (eqKernel high).flatMap fun w ↦ (eqKernel low).map (· * w) := by
  rw [eqKernel, List.foldl_append, ← eqKernel, eqKernel_foldl]

private theorem getD_append_l {l l' : List E} {i : ℕ} (h : i < l.length) :
    (l ++ l').getD i 0 = l.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_r {l l' : List E} {i : ℕ} (h : l.length ≤ i) :
    (l ++ l').getD i 0 = l'.getD (i - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem getD_flatMap_mul (A : List E) (hA : 0 < A.length) : ∀ (W : List E) (i : ℕ),
    (W.flatMap fun w ↦ A.map (· * w)).getD i 0 = A.getD (i % A.length) 0 * W.getD (i / A.length) 0
  | [], i => by simp
  | w :: W, i => by
    rw [List.flatMap_cons]
    by_cases hi : i < A.length
    · rw [getD_append_l (by simpa using hi), Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
      simp [List.getD_eq_getElem?_getD]
      cases A[i]? <;> simp
    · have hL : A.length ≤ i := by omega
      rw [getD_append_r (by simpa using hL), List.length_map,
        getD_flatMap_mul A hA W]
      have h1 : i % A.length = (i - A.length) % A.length := Nat.mod_eq_sub_mod hL
      have h2 : i / A.length = (i - A.length) / A.length + 1 := Nat.div_eq_sub_div hA hL
      rw [h1, h2, List.getD_cons_succ]

private theorem sum_range_two_mul (f : ℕ → E) : ∀ N : ℕ,
    ∑ i ∈ Finset.range (2 * N), f i = ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul f N, Finset.sum_range_succ]
    ring

/-- **`multilinearEval` is the eq-weighted sum of the table.** -/
theorem multilinearEval_eq_sum : ∀ (point mle : List E), mle.length = 2 ^ point.length →
    multilinearEval mle point =
      ∑ i ∈ Finset.range (2 ^ point.length), (eqKernel point).getD i 0 * mle.getD i 0
  | [], mle, h => by
    match mle, h with
    | [a], _ => simp [multilinearEval, eqKernel]
  | r :: rs, mle, h => by
    have hF : (foldPairs r mle).length = 2 ^ rs.length := by
      rw [foldPairs_length', h, List.length_cons, pow_succ]
      omega
    have hm : multilinearEval mle (r :: rs) = multilinearEval (foldPairs r mle) rs := rfl
    have hk : eqKernel (r :: rs) = (eqKernel rs).flatMap fun w ↦ [1 + r, r].map (· * w) := by
      rw [show r :: rs = [r] ++ rs from rfl, eqKernel_append]
      simp [eqKernel]
    rw [hm, multilinearEval_eq_sum rs _ hF, hk, List.length_cons, pow_succ, mul_comm,
      sum_range_two_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hp := foldPairs_getElem?' r mle j
    rw [ite_eq_left (by rw [h, List.length_cons, pow_succ]; omega)] at hp
    rw [getD_flatMap_mul _ (by simp), getD_flatMap_mul _ (by simp),
      List.getD_eq_getElem?_getD (l := foldPairs r mle) (i := j), hp, Option.getD_some,
      show [1 + r, r].length = 2 from rfl]
    rw [show 2 * j % 2 = 0 by omega, show (2 * j + 1) % 2 = 1 by omega, show 2 * j / 2 = j by omega,
      show (2 * j + 1) / 2 = j by omega]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring

/-- The eq weights split at `m`: the low coordinates by the index's remainder, the high by its
quotient. -/
theorem eqKernel_split (point : List E) (m j : ℕ) (hm : m ≤ point.length) :
    (eqKernel point).getD j 0 = (eqKernel (point.take m)).getD (j % 2 ^ m) 0 *
      (eqKernel (point.drop m)).getD (j / 2 ^ m) 0 := by
  conv_lhs => rw [← List.take_append_drop m point]
  rw [eqKernel_append, getD_flatMap_mul _ (by rw [eqKernel_length]; positivity), eqKernel_length,
    List.length_take, min_eq_left hm]

/-- A sum over `A · B` indices, block by block. -/
private theorem sum_range_blocks (f : ℕ → E) (B : ℕ) : ∀ A : ℕ,
    ∑ j ∈ Finset.range (A * B), f j = ∑ b ∈ Finset.range A, ∑ i ∈ Finset.range B, f (b * B + i)
  | 0 => by simp
  | A + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_blocks f B A, Finset.sum_range_succ]

end EqSum


/-! ## `Bytecode::new` prepares the words' bytecode -/

section NewOk

/-- A word as a field element: `K(word)` in `E`. -/
def wordE (w : BitVec 64) : E := ofK (BF64.ofBitVec w)

theorem wordE_zero : wordE 0#64 = 0 := rfl

/-- The (word, position) pairs of a block's members. -/
def pairsOf (ms : List (BitVec 64 × List (BitVec 16))) : List (BitVec 64 × BitVec 16) :=
  ms.flatMap fun m ↦ m.2.map fun p ↦ (m.1, p)

/-- A pair's share of a block's value. -/
def pairTerm (lw : List E) (pw : BitVec 64 × BitVec 16) : E := lw.getD pw.2.toNat 0 * wordE pw.1

theorem blockValueRust_eq (lw : List E) (ms : List (BitVec 64 × List (BitVec 16))) :
    blockValueRust lw ms = ((pairsOf ms).map (pairTerm lw)).sum := by
  unfold blockValueRust
  rw [foldl_add_eq_add_sum, zero_add]
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    obtain ⟨w, ps⟩ := m
    rw [List.map_cons, List.sum_cons, ih, show pairsOf ((w, ps) :: ms) = ps.map (fun p ↦ (w, p)) ++
      pairsOf ms from rfl, List.map_append,
      List.sum_append]
    dsimp only
    rw [foldl_add_eq_add_sum, zero_add, mulKE_eq, ← List.sum_map_mul_right, List.map_map]
    rfl

theorem pairsOf_groupStep (ms : List (BitVec 64 × List (BitVec 16))) (p : BitVec 64 × BitVec 16) :
    pairsOf (groupStep ms p) = pairsOf ms ++ [p] := by
  unfold groupStep
  cases h : ms.getLast? with
  | none => simp [pairsOf]
  | some lp =>
    obtain ⟨last, pos⟩ := lp
    dsimp only
    split_ifs with he
    · obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
      subst he
      simp [pairsOf]
    · simp [pairsOf]

theorem pairsOf_foldl_groupStep (l : List (BitVec 64 × BitVec 16)) :
    ∀ acc, pairsOf (l.foldl groupStep acc) = pairsOf acc ++ l := by
  induction l with
  | nil => intro acc; simp
  | cons p l ih => intro acc; rw [List.foldl_cons, ih, pairsOf_groupStep, List.append_assoc]; rfl

theorem byteKey_lt (byte : ℕ) (p : BitVec 64 × BitVec 16) : byteKey byte p < 256 :=
  BitVec.isLt _

theorem sortPasses_perm : ∀ (bytes : List ℕ) (pairs : List (BitVec 64 × BitVec 16)),
    (bytes.foldl (fun pairs byte ↦ countingSortRust pairs 256 (byteKey byte)) pairs).Perm pairs
  | [], _ => List.Perm.refl _
  | b :: bs, _ => (sortPasses_perm bs _).trans
      (countingSortRust_perm _ _ _ fun x _ ↦ byteKey_lt b x)

/-- `group_by_word`'s input: the nonzero words with their positions. -/
def wordPairs (c : List (BitVec 64)) : List (BitVec 64 × BitVec 16) :=
  (c.zipIdx.filter fun wp ↦ wp.1 != 0).map fun wp ↦ (wp.1, BitVec.ofNat 16 wp.2)

theorem pairsOf_groupByWord (c : List (BitVec 64)) :
    (pairsOf (groupByWordRust c)).Perm (wordPairs c) := by
  unfold groupByWordRust
  rw [pairsOf_foldl_groupStep]
  exact sortPasses_perm _ _

private theorem length_le_pairsOf {ms : List (BitVec 64 × List (BitVec 16))} {m}
    (h : m ∈ ms) : m.2.length ≤ (pairsOf ms).length := by
  unfold pairsOf
  rw [List.length_flatMap]
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun m : BitVec 64 × List (BitVec 16) ↦
    (m.2.map fun p ↦ (m.1, p)).length) h)
  simpa using this

private theorem takeFold (ms : List (BitVec 64 × List (BitVec 16))) :
    ∀ (order : List ℕ) (out cur : List (BitVec 64 × List (BitVec 16))), order.Nodup →
      (∀ i ∈ order, cur.getD i (0, []) = ms.getD i (0, [])) →
      (order.foldl (fun (acc : List (BitVec 64 × List (BitVec 16)) ×
          List (BitVec 64 × List (BitVec 16))) index ↦
        let member := acc.2.getD index (0, [])
        (acc.1 ++ [member], acc.2.set index (member.1, []))) (out, cur)).1 =
        out ++ order.map fun i ↦ ms.getD i (0, [])
  | [], out, cur, _, _ => by simp
  | i :: rest, out, cur, hnd, hcur => by
    rw [List.foldl_cons]
    dsimp only
    rw [takeFold ms rest _ _ (List.nodup_cons.mp hnd).2 fun j hj ↦ ?_, hcur i (by simp),
      List.map_cons, List.append_assoc, List.singleton_append]
    have hji : i ≠ j := fun e ↦ (List.nodup_cons.mp hnd).1 (e ▸ hj)
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hji, ← List.getD_eq_getElem?_getD,
      hcur j (by simp [hj])]

theorem blockMembersRust_perm (c : List (BitVec 64)) :
    (blockMembersRust c).Perm (groupByWordRust c) := by
  unfold blockMembersRust
  dsimp only
  have hlen : (pairsOf (groupByWordRust c)).length ≤ c.length := by
    rw [(pairsOf_groupByWord c).length_eq, wordPairs, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  have hord := countingSortRust_perm (fun index ↦ ((groupByWordRust c).getD index (0, [])).2.length)
    (List.range (groupByWordRust c).length) (c.length + 1) fun i hi ↦ by
      have hi' : i < (groupByWordRust c).length := List.mem_range.mp hi
      show ((groupByWordRust c).getD i (0, [])).2.length < c.length + 1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      exact Nat.lt_succ_of_le ((length_le_pairsOf (List.getElem_mem hi')).trans hlen)
  rw [takeFold _ _ _ _ (hord.nodup_iff.mpr List.nodup_range) fun _ _ ↦ rfl, List.nil_append]
  refine (hord.map _).trans ?_
  apply List.Perm.of_eq
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

private theorem wordPairs_sum (lw : List E) : ∀ (c : List (BitVec 64)) (k : ℕ),
    k + c.length ≤ 2 ^ 16 →
    ((((c.zipIdx k).filter fun wp ↦ wp.1 != 0).map fun wp ↦
      (wp.1, BitVec.ofNat 16 wp.2)).map (pairTerm lw)).sum =
      ∑ i ∈ Finset.range c.length, lw.getD (k + i) 0 * wordE (c.getD i 0)
  | [], _, _ => by simp
  | w :: c, k, hk => by
    rw [List.zipIdx_cons, List.length_cons, Finset.sum_range_succ', List.getD_cons_zero]
    have ih := wordPairs_sum lw c (k + 1) (by simp at hk; omega)
    have hrest : ∑ i ∈ Finset.range c.length, lw.getD (k + (i + 1)) 0 * wordE ((w :: c).getD
        (i + 1) 0) = ∑ i ∈ Finset.range c.length, lw.getD (k + 1 + i) 0 * wordE (c.getD i 0) :=
      Finset.sum_congr rfl fun i _ ↦ by rw [List.getD_cons_succ, show k + (i + 1) = k + 1 + i by
        omega]
    rw [hrest, ← ih, List.filter_cons]
    have hkn : (BitVec.ofNat 16 k).toNat = k := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp at hk; omega)]
    by_cases hw : w = 0#64
    · simp [hw, wordE_zero]
    · rw [ite_eq_left (by simpa using hw), List.map_cons, List.map_cons, List.sum_cons, add_comm]
      simp [pairTerm, hkn]

theorem pairsOf_perm {ms ms' : List (BitVec 64 × List (BitVec 16))} (h : ms.Perm ms') :
    (pairsOf ms).Perm (pairsOf ms') :=
  h.flatMap_right _

theorem blockValueRust_blockMembers (lw : List E) (c : List (BitVec 64))
    (hc : c.length ≤ 2 ^ 16) :
    blockValueRust lw (blockMembersRust c) =
      ∑ i ∈ Finset.range c.length, lw.getD i 0 * wordE (c.getD i 0) := by
  rw [blockValueRust_eq, ((pairsOf_perm (blockMembersRust_perm c)).map _).sum_eq,
    ((pairsOf_groupByWord c).map _).sum_eq, wordPairs,
    wordPairs_sum lw c 0 (by omega)]
  simp

private theorem chunksW_eq {α : Type} (S : ℕ) (hS : 0 < S) :
    ∀ (A : ℕ) (l : List α), l.length = A * S →
    chunksW S l = (List.range A).map fun b ↦ (l.drop (b * S)).take S
  | 0, l, h => by
    rw [chunksW, dite_eq_left (Or.inl (List.length_eq_zero_iff.mp (by simpa using h)))]
    rfl
  | A + 1, l, h => by
    have hne : l ≠ [] := by
      rintro rfl
      simp only [List.length_nil] at h
      have : 0 < (A + 1) * S := Nat.mul_pos (by omega) hS
      omega
    rw [chunksW, dite_eq_right fun h' ↦ h'.elim hne (by omega), chunksW_eq S hS A (l.drop S) (by
      rw [List.length_drop, h, Nat.succ_mul]; omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, zero_mul, List.drop_zero]
    congr 1
    refine List.map_congr_left fun b _ ↦ ?_
    simp only [Function.comp_apply, List.drop_drop]
    congr 2
    rw [Nat.succ_mul]
    omega

theorem chunksW_single {α : Type} (S : ℕ) (l : List α) (h0 : l ≠ []) (h : l.length ≤ S) :
    chunksW S l = [l] := by
  have hS : S ≠ 0 := fun e ↦ h0 (List.length_eq_zero_iff.mp (by omega))
  rw [chunksW, dite_eq_right fun h' ↦ h'.elim h0 hS, List.take_of_length_le h, chunksW,
    dite_eq_left (Or.inl (List.drop_eq_nil_of_le h))]

private theorem sum_zip_range {α : Type} (F : α × E → E) :
    ∀ (hw : List E) (g : ℕ → α),
      ((((List.range hw.length).map g).zip hw).map F).sum =
        ∑ b ∈ Finset.range hw.length, F (g b, hw.getD b 0)
  | [], _ => by simp
  | x :: hw, g => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.zip_cons_cons,
      List.map_cons, List.sum_cons, sum_zip_range F hw, Finset.sum_range_succ', add_comm]
    rfl

private theorem getD_map_ofK (words : List K) (j : ℕ) :
    (words.map ofK).getD j 0 = wordE ((words.map BF64.toBitVec).getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map]
  cases words[j]? <;> rfl

private theorem chunk_getD (W : List (BitVec 64)) (o B i : ℕ) (hi : i < B) :
    ((W.drop o).take B).getD i 0 = W.getD (o + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
    List.getElem?_drop]

/-- **`Bytecode::new` prepares the words' bytecode**: where it returns `Ok`, the count, the IV,
and `evaluate`, the multilinear extension by blocks, are the words'. -/
theorem newRust_ok {words : List K} {bc : BytecodeRust}
    (h : newRust (words.map BF64.toBitVec) = some bc) : BytecodeOk words bc := by
  unfold newRust at h
  split_ifs at h with hv
  cases h
  refine ⟨by simp, fiatShamirIvRust_eq words, fun point ↦ ?_⟩
  unfold evaluateRust
  simp only [List.length_map]
  split_ifs with hc
  swap
  · rfl
  obtain ⟨hn, hwl⟩ := hc
  generalize hW : words.map BF64.toBitVec = W
  have hWl : W.length = 2 ^ point.length := by rw [← hW, List.length_map, hwl]
  generalize hm : min point.length blockLog = m
  have hmn : m ≤ point.length := hm ▸ min_le_left _ _
  have hm14 : m ≤ 14 := hm ▸ min_le_right _ _
  have hBA : 2 ^ point.length = 2 ^ (point.length - m) * 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  have hblocks : chunksW (2 ^ blockLog) W =
      (List.range (2 ^ (point.length - m))).map fun b ↦ (W.drop (b * 2 ^ m)).take (2 ^ m) := by
    by_cases hb : blockLog ≤ point.length
    · rw [show m = blockLog by rw [← hm]; exact min_eq_right hb]
      exact chunksW_eq _ (by positivity) _ _ (by
        rw [hWl, hBA, show m = blockLog by rw [← hm]; exact min_eq_right hb])
    · have hmp : m = point.length := by rw [← hm]; exact min_eq_left (by omega)
      rw [hmp, Nat.sub_self, pow_zero, chunksW_single _ _ (fun e ↦ by
        simp only [e, List.length_nil] at hWl; exact absurd hWl.symm (by positivity))
        (by rw [hWl]; exact Nat.pow_le_pow_right (by norm_num) (by omega))]
      simp [← hWl]
  have hhw : (eqKernel (point.drop m)).length = 2 ^ (point.length - m) := by
    rw [eqKernel_length, List.length_drop]
  rw [eqKernelRust_eq _ (by simp; omega), eqKernelRust_eq _ (by simp; omega), hblocks,
    List.map_map, foldl_add_eq_add_sum, zero_add, ← hhw, sum_zip_range, hhw,
    multilinearEval_eq_sum point _ (by simp [hwl]), hBA, sum_range_blocks]
  congr 1
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  rw [Finset.mem_range] at hb
  have hlen : ((W.drop (b * 2 ^ m)).take (2 ^ m)).length = 2 ^ m := by
    rw [List.length_take, List.length_drop, hWl, hBA]
    have : (b + 1) * 2 ^ m ≤ 2 ^ (point.length - m) * 2 ^ m := Nat.mul_le_mul_right _ hb
    rw [Nat.succ_mul] at this
    omega
  have h16 : 2 ^ m ≤ 2 ^ 16 := Nat.pow_le_pow_right (by norm_num) (by omega)
  dsimp only [Function.comp_apply]
  rw [blockValueRust_blockMembers _ _ (by rw [hlen]; exact h16), hlen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [eqKernel_split point m _ hmn, getD_map_ofK, hW, chunk_getD _ _ _ _ hi,
    show (b * 2 ^ m + i) % 2 ^ m = i by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi],
    show (b * 2 ^ m + i) / 2 ^ m = b by
      rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hi, add_zero]]
  ring


/-- `Bytecode::new`'s words number at most `2^34` (`16 · 2^30`). -/
theorem newRust_length {words : List (BitVec 64)} {bc : BytecodeRust}
    (h : newRust words = some bc) : words.length ≤ 2 ^ 34 := by
  unfold newRust at h
  split_ifs at h with hv
  unfold validEncodingRust at hv
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨-, hl⟩, hn⟩, -⟩ := hv
  rw [Nat.shiftLeft_eq] at hl
  omega

end NewOk


/-! ## Every program's encoding is valid -/

section ValidEncoding

open LeanVM LeanVM.Arithmetization

private theorem busCode_toBitVec (op : Opcode) :
    (op.busCode).toBitVec = 1#64 <<< (match op with
      | .xor => 0 | .mulNative => 1 | .setConstant => 2 | .deref => 3 | .jump => 4
      | .keccak => 5) := by
  have h : ∀ n, (g ^ (n + 1)).toBitVec = timesX (g ^ n).toBitVec := fun n ↦ by
    rw [pow_succ, timesX_eq]
  have h0 : (g ^ 0).toBitVec = 1#64 := rfl
  cases op <;> simp only [Opcode.busCode, addressOfIndex, h, h0] <;> decide

private theorem getD_flatMap_finRange {β : Type} (d : β) (N pc : ℕ) (hpc : pc < N) :
    ∀ (m : ℕ) (f : Fin m → Fin N → β) (s : ℕ),
      ((List.finRange m).flatMap fun s ↦ (List.finRange N).map (f s)).getD (s * N + pc) d =
        if h : s < m then f ⟨s, h⟩ ⟨pc, hpc⟩ else d
  | 0, _, s => by simp
  | m + 1, f, 0 => by
    rw [List.finRange_succ, List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simpa using hpc)]
    simp [List.getElem?_eq_getElem (show pc < (List.finRange N).length by simpa using hpc)]
  | m + 1, f, s + 1 => by
    rw [List.finRange_succ, List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp; nlinarith), ← List.getD_eq_getElem?_getD,
      List.flatMap_map]
    have := getD_flatMap_finRange d N pc hpc m (fun s ↦ f s.succ) s
    simp only [List.length_map, List.length_finRange,
      show (s + 1) * N + pc - N = s * N + pc by rw [Nat.succ_mul]; omega] at this ⊢
    rw [this]
    simp

private theorem getD_map_toBitVec (l : List K) (n : ℕ) :
    (l.map BF64.toBitVec).getD n (BF64.toBitVec 0) = BF64.toBitVec (l.getD n 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> rfl

/-- **`is_valid_encoding_of_a_leanisa_program` accepts every program's bytecode**: the statement's
programs have at most `2^30` instructions, and `instructionSlots` meets every slot check. -/
theorem validEncodingRust_bytecodeWords (program : LeanIsaProgram) :
    validEncodingRust ((bytecodeWords program).map BF64.toBitVec) = true := by
  have hlen : ((bytecodeWords program).map BF64.toBitVec).length = 2 ^ program.logSize <<< 4 := by
    simp [bytecodeWords, Nat.shiftLeft_eq]
    omega
  have hL : program.logSize ≤ 30 := program.logSize_le
  have hslot : ∀ pc (hpc : pc < 2 ^ program.logSize) s,
      slotRust ((bytecodeWords program).map BF64.toBitVec) (2 ^ program.logSize) pc s =
        ((instructionSlots (program.instructions ⟨pc, hpc⟩)).toList.getD s 0).toBitVec := by
    intro pc hpc s
    unfold slotRust
    rw [show (0 : BitVec 64) = BF64.toBitVec 0 from rfl, getD_map_toBitVec, bytecodeWords,
      getD_flatMap_finRange 0 _ pc hpc, List.getD_eq_getElem?_getD]
    split
    · simp [*]
    · rw [List.getElem?_eq_none (by simp; omega)]
      rfl
  have hsh : 2 ^ program.logSize <<< 4 >>> 4 = 2 ^ program.logSize := by
    simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ program.logSize &&& (2 ^ program.logSize - 1) = 0 := by
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self]
  unfold validEncodingRust
  simp only [hlen, hsh, hpow, List.all_eq_true, List.mem_range, Bool.and_eq_true]
  refine ⟨⟨⟨by simp, by simp⟩, by simpa using Nat.pow_le_pow_right two_pos hL⟩, fun pc hpc ↦ ?_⟩
  unfold instructionOkRust
  simp only [hslot pc hpc]
  generalize program.instructions ⟨pc, hpc⟩ = ins
  cases ins with
  | deref _ _ _ mode =>
    cases mode <;> simp [instructionSlots, busEntry, busCode_toBitVec, List.range_succ,
      List.range'_succ, List.getD_eq_getElem?_getD, derefFlags]
  | keccak _ _ _ _ _ inOdd outOdd outCells =>
    cases inOdd <;> cases outOdd <;> cases outCells <;> simp [instructionSlots, busEntry,
      busCode_toBitVec, List.range_succ, List.getD_eq_getElem?_getD, keccakOutputFlags,
      layoutFlagWord]
  | _ => simp [instructionSlots, busEntry, busCode_toBitVec, List.range_succ, List.range'_succ,
    List.getD_eq_getElem?_getD]

/-- `Bytecode::new` prepares every program's bytecode. -/
theorem newRust_bytecodeWords (program : LeanIsaProgram) :
    ∃ bc, newRust ((bytecodeWords program).map BF64.toBitVec) = some bc :=
  ⟨_, by rw [newRust, ite_eq_left (validEncodingRust_bytecodeWords program)]⟩

end ValidEncoding

end

end Rv64mc.Model
