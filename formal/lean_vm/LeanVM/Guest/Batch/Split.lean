/-
  LeanVM.Guest.Batch.Split

  The split program as one table: its multilinear extension at a point over the instructions and
  the columns is the split columns' values there (`split_values`), folded at the columns'
  coordinates.
-/

module

public import Statement.LeanVmGuestBatching
public import LeanVM.Facts.Hotwire
public import LeanVM.Protocol.Tables
import LeanVM.Parameters.Field

/-!
# The split table at a point

`splitTable bytecode` (`split_table`, `crates/aggregation/src/split.rs`) lays the split columns
out one after the other, `n = len / 2^BYTECODE_SLOT_BITS` entries each, `2^splitLog` columns; a point on it
is the instructions' `log₂ n` coordinates, then the columns' `splitLog`. A child's fresh claim
reads the columns at a point `p` over the instructions (`splitValues`, `split_values`, through
`Bytecode::split`, `splitAt`). This module proves that the table's multilinear extension at
`p ++ c` is those values folded at `c` (`mle_splitTable_append`):

`T̃(p ++ c) = Σ_{j < 2^splitLog} eq(c, j) · splitValues(p)[j]`,

the columns past `splitColumns tables` being zero. Column by column (`splitValueOf_splitAt`),
`Bytecode::split`'s sums over the instructions are the column's multilinear extension: each split
column reads an opcode below `N_TABLES`, an operand slot `s` with `4 ≤ s < 2^BYTECODE_SLOT_BITS`, and a
`pc` column a pair `pc_slots` names (`valid_splitColumns`, decided on `tables`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node Finset
open LeanVM.Protocol.Hotwire (eqAt mle)

@[expose] public section

/-! ## The split columns of `tables` -/

/-- `split_terms()` on `tables()` (`split.rs`): the six counts, then the slots and the one `pc`
column the links name. -/
theorem splitColumns_tables : splitColumns tables = [.count 0, .count 1, .count 2, .count 3,
    .count 4, .count 5, .slot 0 4, .slot 0 5, .slot 0 6, .slot 1 4, .slot 1 5, .slot 1 6,
    .slot 2 4, .slot 2 5, .slot 2 6, .slot 3 5, .slot 3 7, .slot 3 8, .slot 3 4, .pc 3 7,
    .slot 3 6, .slot 4 4, .slot 4 5, .slot 4 6, .slot 5 11, .slot 5 12, .slot 5 13, .slot 5 14,
    .slot 5 15, .slot 5 4, .slot 5 5, .slot 5 6, .slot 5 7, .slot 5 8, .slot 5 9, .slot 5 10] := by
  decide +kernel

/-- `pc_slots(tables())` (`link.rs`): `DEREF`'s slot `7`. -/
theorem pcSlots_tables : pcSlots tables = [(3, 7)] := by decide +kernel

theorem length_splitColumns : (splitColumns tables).length = 36 := by
  rw [splitColumns_tables]; rfl

/-- A split column `Bytecode::split` computes, at the pairs `pcs` read times `pc`: its opcode
below `N_TABLES`, an operand slot `4 ≤ s < 2^BYTECODE_SLOT_BITS`, and for a `pc` column a pair of `pcs`. -/
def validColumn (pcs : List (ℕ × ℕ)) : SplitColumn → Bool
  | .count op => decide (op < opKeccak + 1)
  | .slot op s => decide (op < opKeccak + 1 ∧ 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits)
  | .pc op s => decide (op < opKeccak + 1 ∧ 4 ≤ s ∧ s < 2 ^ bytecodeSlotBits) && pcs.contains (op, s)

theorem valid_splitColumns : ∀ c ∈ splitColumns tables, validColumn (pcSlots tables) c = true := by
  rw [splitColumns_tables, pcSlots_tables]
  decide

/-! ## Entries -/

/-- Entry `k` of the split column `c` (`split_table`'s, `splitEntry`'s case for `c`). -/
def columnEntry (bytecode : List K) (c : SplitColumn) (k : ℕ) : K :=
  let n := bytecode.length >>> bytecodeSlotBits
  let word := fun s ↦ bytecode.getD (s * n + k) 0
  let op := opcodeOf (word 3)
  match c with
  | .count o => if op = o then 1 else 0
  | .slot o slot => if op = o then word slot else 0
  | .pc o slot => if op = o then g ^ k * word slot else 0

theorem splitEntry_eq (bytecode : List K) (j k : ℕ) :
    splitEntry bytecode j k = match (splitColumns tables)[j]? with
      | some c => columnEntry bytecode c k
      | none => 0 := by
  unfold splitEntry columnEntry
  rcases (splitColumns tables)[j]? with _ | (_ | _ | _) <;> rfl

theorem length_splitTable (bytecode : List K) :
    (splitTable bytecode).length = (bytecode.length >>> bytecodeSlotBits) * 2 ^ splitLog := by
  simp [splitTable, List.length_flatMap, mul_comm]

/-- Entry `k + n·j` of the table is column `j`'s entry `k`. -/
theorem getD_splitTable (bytecode : List K) {j k : ℕ} (hj : j < 2 ^ splitLog)
    (hk : k < bytecode.length >>> bytecodeSlotBits) :
    (splitTable bytecode).getD (k + (bytecode.length >>> bytecodeSlotBits) * j) 0 = splitEntry bytecode j k := by
  set n := bytecode.length >>> bytecodeSlotBits
  have key : ∀ (js : List ℕ) (i : ℕ), i < js.length →
      (js.flatMap fun j ↦ (List.range n).map (splitEntry bytecode j)).getD (k + n * i) 0 =
        splitEntry bytecode (js.getD i 0) k := by
    intro js
    induction js with
    | nil => intro i hi; simp at hi
    | cons j' js ih =>
      intro i hi
      rw [List.flatMap_cons]
      rcases i with _ | i
      · rw [List.getD_append _ _ _ _ (by simpa using hk)]
        simp [List.getD_eq_getElem?_getD, hk]
      · rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
        have e : k + n * (i + 1) - ((List.range n).map (splitEntry bytecode j')).length =
            k + n * i := by simp; ring_nf; omega
        rw [e, ih i (by simpa using hi)]
        simp
  rw [splitTable, key _ j (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

/-! ## Sums over the rows of `Bytecode::split` -/

/-- A sum over an indexed list is a sum over its indices. -/
theorem sum_map_zipIdx {α : Type} (f : α × ℕ → E) (d : α) :
    ∀ (l : List α) (s : ℕ), ((l.zipIdx s).map f).sum =
      ∑ k ∈ range l.length, f (l.getD k d, s + k)
  | [], _ => by simp
  | a :: l, s => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_map_zipIdx f d l (s + 1),
      List.length_cons, sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    rw [add_comm]
    refine congrArg₂ _ (sum_congr rfl fun k _ ↦ ?_) rfl
    rw [add_assoc, add_comm 1 k]

/-- `powers(base, count)`, entry `k`: `base^k`. -/
theorem getD_powersFrom (base : E) : ∀ (count : ℕ) (acc : E) (k : ℕ), k < count →
    (powersFrom acc base count).getD k 0 = acc * base ^ k
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | count + 1, acc, 0, _ => by simp [powersFrom]
  | count + 1, acc, k + 1, h => by
    rw [powersFrom, List.getD_cons_succ, getD_powersFrom base count _ k (by omega), pow_succ']
    ring

theorem length_powersFrom (base : E) : ∀ (count : ℕ) (acc : E),
    (powersFrom acc base count).length = count
  | 0, _ => rfl
  | count + 1, acc => by simp [powersFrom, length_powersFrom base count]

/-- The rows of `Bytecode::split` at a point of `m` coordinates, each instruction `k < 2^m` with
its weights `eq(point, k)` and `g^k`, summed. -/
theorem sumE_rows (point : List E) (F : (E × E) × ℕ → E) :
    sumE ((((eqKernel point).zip (powers gen (2 ^ point.length))).zipIdx).map F) =
      ∑ k ∈ range (2 ^ point.length), F ((eqAt point k, gen ^ k), k) := by
  rw [Tables.sumE_eq, sum_map_zipIdx _ (0, 0)]
  have hl : ((eqKernel point).zip (powers gen (2 ^ point.length))).length = 2 ^ point.length := by
    simp [Hotwire.eqKernel_length, powers, length_powersFrom]
  rw [hl]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  have hz : ((eqKernel point).zip (powers gen (2 ^ point.length))).getD k (0, 0) =
      ((eqKernel point).getD k 0, (powers gen (2 ^ point.length)).getD k 0) := by
    have h1 : k < (eqKernel point).length := by rw [Hotwire.eqKernel_length]; exact hk'
    have h2 : k < (powers gen (2 ^ point.length)).length := by
      rw [powers, length_powersFrom]; exact hk'
    simp [List.getD_eq_getElem?_getD, h1, h2]
  rw [hz, Hotwire.eqKernel_getD, ite_eq_left hk', powers, getD_powersFrom _ _ _ _ hk', one_mul,
    zero_add]

/-- Entry `i` of a list made over `range n`, `i < n`. -/
theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) {n i : ℕ} (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, h]

theorem gen_pow (k : ℕ) : gen ^ k = ofK (g ^ k) := by
  show gen ^ k = algebraMap K E (g ^ k)
  rw [map_pow]
  rfl

/-! ## Column by column -/

/-- What `split_values` reads of a split for one column. -/
def splitValueOf (split : Split) : SplitColumn → E
  | .count op => split.count.getD op 0
  | .slot op slot => (split.slots.getD op []).getD slot 0
  | .pc op slot => (split.pc.getD op []).getD slot 0

theorem splitValues_eq (bytecode : List K) (point : List E) :
    splitValues bytecode point =
      (splitColumns tables).map (splitValueOf (splitAt bytecode point (pcSlots tables))) := by
  rfl

/-- **A split column's value is its multilinear extension over the instructions**: what
`Bytecode::split` sums for the column, at a point of one coordinate per instruction bit. -/
theorem splitValueOf_splitAt {bytecode : List K} {point : List E}
    (hn : bytecode.length >>> bytecodeSlotBits = 2 ^ point.length) {c : SplitColumn}
    (hc : validColumn (pcSlots tables) c = true) :
    splitValueOf (splitAt bytecode point (pcSlots tables)) c =
      mle point fun k ↦ ofK (columnEntry bytecode c k) := by
  unfold mle
  cases c with
  | count op =>
    simp only [validColumn, decide_eq_true_eq] at hc
    simp only [splitValueOf, splitAt, columnEntry, hn]
    rw [getD_map_range _ _ hc, sumE_rows]
    refine sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> simp
  | slot op s =>
    simp only [validColumn, decide_eq_true_eq] at hc
    obtain ⟨hop, h4, hs⟩ := hc
    simp only [splitValueOf, splitAt, columnEntry, hn]
    rw [getD_map_range _ _ hop, getD_map_range _ _ hs, ite_eq_left h4, sumE_rows]
    refine sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> simp
  | pc op s =>
    simp only [validColumn, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hop, h4, hs⟩, hpc⟩ := hc
    simp only [splitValueOf, splitAt, columnEntry, hn]
    rw [getD_map_range _ _ hop, getD_map_range _ _ hs, ite_eq_left ⟨h4, hpc⟩, sumE_rows]
    refine sum_congr rfl fun k _ ↦ ?_
    split_ifs <;> simp [gen_pow, ofK_mul]

/-- A column's value at a point, as the extension of its entries. -/
theorem splitValues_getD {bytecode : List K} {point : List E}
    (hn : bytecode.length >>> bytecodeSlotBits = 2 ^ point.length) (j : ℕ) :
    (splitValues bytecode point).getD j 0 =
      mle point fun k ↦ ofK (splitEntry bytecode j k) := by
  rw [splitValues_eq]
  rcases hj : (splitColumns tables)[j]? with _ | c
  · have : (splitColumns tables).length ≤ j := List.getElem?_eq_none_iff.mp hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hj, Option.map_none, Option.getD_none]
    unfold mle
    simp [splitEntry_eq, hj]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, hj, Option.map_some, Option.getD_some,
      splitValueOf_splitAt hn (valid_splitColumns c (List.mem_of_getElem? hj))]
    unfold mle
    simp [splitEntry_eq, hj]

/-! ## The table -/

/-- A sum over `a · b` indices, block by block. -/
theorem sum_range_mul (a : ℕ) (f : ℕ → E) : ∀ b : ℕ,
    ∑ v ∈ range (a * b), f v = ∑ j ∈ range b, ∑ k ∈ range a, f (k + a * j)
  | 0 => by simp
  | b + 1 => by
    rw [mul_add, mul_one, sum_range_add, sum_range_mul a f b, sum_range_succ]
    congr 1
    refine sum_congr rfl fun k _ ↦ ?_
    rw [add_comm]

/-- **The split table at a point over the instructions and the columns** is the split columns'
values at the instructions' coordinates, folded at the columns': for `n = 2^|p|` instructions
and `splitLog` column coordinates. -/
theorem mle_splitTable_append {bytecode : List K} {p c : List E}
    (hn : bytecode.length >>> bytecodeSlotBits = 2 ^ p.length) (hc : c.length = splitLog) :
    multilinearEval ((splitTable bytecode).map ofK) (p ++ c) =
      ∑ j ∈ range (2 ^ splitLog), eqAt c j * (splitValues bytecode p).getD j 0 := by
  have hlen : ((splitTable bytecode).map ofK).length = 2 ^ (p ++ c).length := by
    rw [List.length_map, length_splitTable, hn, List.length_append, hc, pow_add]
  rw [Hotwire.multilinearEval_eq_mle _ _ hlen, mle, List.length_append, hc, pow_add,
    sum_range_mul]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [splitValues_getD hn, mle, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' := mem_range.mp hk
  have hj' := mem_range.mp hj
  rw [Hotwire.eqAt_append, Hotwire.eqAt_mod p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk',
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hk', zero_add,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  have hT := getD_splitTable bytecode hj' (by rw [hn]; exact hk')
  rw [hn, List.getD_eq_getElem?_getD] at hT
  rcases ht : (splitTable bytecode)[k + 2 ^ p.length * j]? with _ | x
  · have : (splitTable bytecode).length ≤ k + 2 ^ p.length * j := List.getElem?_eq_none_iff.mp ht
    rw [length_splitTable, hn] at this
    nlinarith
  · rw [ht, Option.getD_some] at hT
    rw [Option.map_some, Option.getD_some, hT]
    ring

/-! ## The fold of a fresh claim's values -/

/-- `Σ x·y` of two lists, as a sum over the shorter's indices. -/
theorem sumE_zipWith_mul : ∀ (a b : List E),
    sumE (List.zipWith (· * ·) a b) = ∑ j ∈ range (min a.length b.length), a.getD j 0 * b.getD j 0
  | [], _ => by simp [sumE]
  | _ :: _, [] => by simp [sumE]
  | x :: a, y :: b => by
    rw [List.zipWith_cons_cons, Tables.sumE_eq, List.sum_cons, ← Tables.sumE_eq,
      sumE_zipWith_mul a b, List.length_cons, List.length_cons, Nat.add_min_add_right,
      sum_range_succ']
    simp [add_comm]

/-- **The fold of a fresh claim's values** at column challenges of `splitLog` coordinates, its
values at most `2^splitLog`: `Σ_j eq(c, j)·values[j]`. -/
theorem foldColumns_eq {c values : List E} (hc : c.length = splitLog)
    (hv : values.length ≤ 2 ^ splitLog) :
    foldColumns c values = ∑ j ∈ range (2 ^ splitLog), eqAt c j * values.getD j 0 := by
  rw [foldColumns, sumE_zipWith_mul, Hotwire.eqKernel_length, hc, min_eq_right hv]
  rw [← sum_range_add_sum_Ico _ hv]
  rw [show ∑ j ∈ Ico values.length (2 ^ splitLog), eqAt c j * values.getD j 0 = 0 from
    sum_eq_zero fun j hj ↦ by
      rw [List.getD_eq_default _ _ (mem_Ico.mp hj).1, mul_zero]]
  rw [add_zero]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [Hotwire.eqKernel_getD, hc, ite_eq_left ((mem_range.mp hj).trans_le hv)]

end
end LeanVM.Guest.Batch
