/-
  LeanVM.Guest.Value.KeccakLayout

  The bytes of canonical cells, the lanes of the thirteen cells of a `KECCAK` in either layout,
  and one `KECCAK` as the absorption of a block of message cells XORed into a previous output.
-/

module

public import LeanVM.Guest.Value.KeccakEval
public import LeanVM.Guest.Value.Tower
public import LeanVM.Guest.Word
public import LeanVM.Semantics.KeccakCells
import Mathlib.Data.List.GetD

/-!
# The cells of a Keccak state

A canonical cell holds sixteen message bytes, its limb `0` then its limb `1`, each as eight
little-endian bytes (`cellBytes`; the Rust's `pack_16_bytes`, the Spec's `kBytes`). A Keccak state
sits in thirteen cells in one of two layouts (`cellLanes`, `Statement/LeanIsa.lean`): lane `l` is
limb `laneLimbIdx odd l` of cell `laneCellIdx odd l` (`lane_stateOfCells`). The compiler's
`emit_keccak_message` (`crates/lean_compiler/src/lower/builtins.rs:275-335` at leanVM main `40f877dc`)
reads block `k` of a message from its cell `17k/2` in the layout of `k`'s parity: a block of `136`
bytes is `8.5` cells, so an odd block starts in its first cell's limb `1`, which the odd layout
places at lane `0`. XORing the block's nine cells into the previous output, which `KECCAK` wrote in
that same layout, XORs its seventeen lanes into the rate (`stateOfCells_xor`), and the instruction
is `absorbBlock` (`keccak_block`).

* `leLane_cellsBytes`: lane `l` of the bytes of cells is limb `l % 2` of cell `l / 2`;
* `lane_stateOfCells`, `limb_cellsOfState`: where each lane sits;
* `stateOfCells_cellsOfState`: the cells `KECCAK` writes hold the state;
* `keccak_block`: a `KECCAK` whose inputs are a state's cells plus a block's is `absorbBlock`.
-/

namespace LeanVM.Guest.Value.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value.KeccakEval

@[expose] public section

/-! ## Bytes of cells -/

/-- The sixteen bytes a cell holds: its limb `0`, then its limb `1`, little-endian
(`pack_16_bytes`, `crates/rec_aggregation/src/aggregation/cells.rs:23-26`). -/
def cellBytes (c : E) : List UInt8 := K.toBytes (c.limb 0) ++ K.toBytes (c.limb 1)

/-- The bytes of a run of cells, in order. -/
def cellsBytes (cs : List E) : List UInt8 := cs.flatMap cellBytes

@[simp] theorem length_wordBytes (w : UInt64) : (wordBytes w).length = 8 := by
  simp [wordBytes]

@[simp] theorem length_cellBytes (c : E) : (cellBytes c).length = 16 := by
  simp [cellBytes, K.toBytes]

@[simp] theorem cellsBytes_nil : cellsBytes [] = [] := rfl

theorem cellsBytes_cons (c : E) (cs : List E) :
    cellsBytes (c :: cs) = cellBytes c ++ cellsBytes cs := rfl

@[simp] theorem length_cellsBytes (cs : List E) : (cellsBytes cs).length = 16 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [cellsBytes_cons, List.length_append, ih, length_cellBytes]; simp; ring

theorem cellsBytes_append (cs ds : List E) :
    cellsBytes (cs ++ ds) = cellsBytes cs ++ cellsBytes ds := by
  simp [cellsBytes]

theorem cellsBytes_drop (cs : List E) (m : ℕ) :
    cellsBytes (cs.drop m) = (cellsBytes cs).drop (16 * m) := by
  induction cs generalizing m with
  | nil => simp
  | cons c cs ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [List.drop_succ_cons, ih, cellsBytes_cons, show 16 * (m + 1) = 16 + 16 * m by ring,
        ← List.drop_drop, List.drop_left' (length_cellBytes c)]

/-- The bytes of zero cells are zero. -/
theorem cellsBytes_replicate_zero (n : ℕ) :
    cellsBytes (List.replicate n 0) = List.replicate (16 * n) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, cellsBytes_cons, ih, show 16 * (n + 1) = 16 + 16 * n by ring,
      List.replicate_add, cellBytes, limb_zero, limb_zero]
    rfl

/-! ## Lanes of bytes -/

/-- A fold is determined by its steps on the list's elements. -/
theorem foldl_congr_mem {α β : Type} {f g : α → β → α} :
    ∀ (l : List β) (a : α), (∀ a b, b ∈ l → f a b = g a b) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h a b List.mem_cons_self]
    exact foldl_congr_mem l _ fun a b hb ↦ h a b (List.mem_cons_of_mem _ hb)

/-- Eight little-endian bytes, reassembled: the bytes of `n` below `2^(8m)`. -/
private theorem foldl_bytes (n : ℕ) :
    ∀ m, m ≤ 8 → (List.range m).foldl
      (fun acc k ↦ acc ||| (((n >>> (8 * k)) % 256) <<< (8 * k)) % 2 ^ 64) 0 = n % 2 ^ (8 * m)
  | 0, _ => by simp [Nat.mod_one]
  | m + 1, hm => by
    rw [List.range_succ, List.foldl_append, foldl_bytes n m (by omega), List.foldl_cons,
      List.foldl_nil, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have hlt : n / 2 ^ (8 * m) % 256 * 2 ^ (8 * m) < 2 ^ 64 := by
      have h1 : n / 2 ^ (8 * m) % 256 < 2 ^ 8 := Nat.mod_lt _ (by norm_num)
      calc n / 2 ^ (8 * m) % 256 * 2 ^ (8 * m) < 2 ^ 8 * 2 ^ (8 * m) :=
            Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
        _ = 2 ^ (8 + 8 * m) := (Nat.pow_add 2 8 (8 * m)).symm
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.mod_eq_of_lt hlt, Nat.or_comm, Nat.mul_comm,
      two_pow_mul_or (Nat.mod_lt _ (Nat.two_pow_pos _)),
      show 8 * (m + 1) = 8 * m + 8 by ring, Nat.pow_add, Nat.mod_mul]
    ring

/-- **The lane of a word's bytes is the word.** -/
theorem leLane_wordBytes_append (w : UInt64) (rest : List UInt8) :
    littleEndianLane (wordBytes w ++ rest) 0 = w := by
  apply UInt64.toNat_inj.mp
  rw [leLane_toNat, leLaneN]
  have hk : ∀ k ∈ List.range 8, ((wordBytes w ++ rest).map UInt8.toNat).getD (8 * 0 + k) 0 =
      w.toNat >>> (8 * k) % 256 := by
    intro k hk
    have hk : k < 8 := List.mem_range.mp hk
    have h8 : (8 * k).toUInt64.toNat = 8 * k := by simp; omega
    rw [List.map_append, List.getD_append _ _ _ _ (by simp [wordBytes]; omega)]
    simp only [wordBytes, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some, Function.comp_apply,
      UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8,
      Nat.mod_eq_of_lt (show 8 * k < 64 by omega),
      Nat.zero_add, Nat.mul_zero]
  rw [foldl_congr_mem
    (g := fun acc k ↦ acc ||| (((w.toNat >>> (8 * k)) % 256) <<< (8 * k)) % 2 ^ 64)
    _ _ (fun acc k hm ↦ by rw [hk k hm]), foldl_bytes _ 8 le_rfl, Nat.mod_eq_of_lt w.toNat_lt]

/-- A lane past the first reads the bytes past the first eight. -/
theorem leLane_succ (bs : List UInt8) (l : ℕ) : littleEndianLane bs (l + 1) = littleEndianLane
    (bs.drop 8) l := by
  unfold littleEndianLane
  congr 1
  funext acc k
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop,
    show 8 * (l + 1) + k = 8 + (8 * l + k) by ring]

theorem leLane_nil (l : ℕ) : littleEndianLane [] l = 0 := by
  simp [littleEndianLane]

/-- Lane `l` of a byte string is the bytes from `8l`. -/
theorem leLane_eq_drop (bs : List UInt8) (l : ℕ) : littleEndianLane bs l = littleEndianLane (bs.drop
    (8 * l)) 0 := by
  induction l generalizing bs with
  | zero => rfl
  | succ l ih => rw [leLane_succ, ih, List.drop_drop]; congr 2; ring

/-- **Lane `l` of the bytes of cells** is limb `l % 2` of cell `l / 2` (zero past the end). -/
theorem leLane_cellsBytes (cs : List E) (l : ℕ) :
    littleEndianLane (cellsBytes cs) l = ((cs.getD (l / 2) 0).limb ⟨l % 2, by omega⟩).lane := by
  rw [leLane_eq_drop, show 8 * l = 16 * (l / 2) + 8 * (l % 2) by omega, ← List.drop_drop,
    ← cellsBytes_drop]
  rw [List.getD_eq_getElem?_getD, show cs[l / 2]? = (cs.drop (l / 2))[0]? by simp]
  generalize cs.drop (l / 2) = ds
  rcases ds with _ | ⟨d, ds⟩
  · simp only [cellsBytes_nil, List.drop_nil, leLane_nil, List.getElem?_nil, Option.getD_none]
    rw [limb_zero]; rfl
  · rcases Nat.mod_two_eq_zero_or_one l with h | h <;>
      simp only [h, cellsBytes_cons, cellBytes, K.toBytes, List.append_assoc, Nat.mul_zero,
        List.drop_zero, Nat.mul_one, leLane_wordBytes_append, List.getElem?_cons_zero,
        Option.getD_some, List.drop_left' (length_wordBytes _)]
    · rfl
    · rfl

/-! ## Lanes in the two layouts -/

/-- The cell holding lane `l` in the layout `odd` (`cellLanes`). -/
def laneCellIdx (odd : Bool) (l : ℕ) : ℕ := if odd ∨ 17 ≤ l then (l + 1) / 2 else l / 2

/-- The limb of `laneCellIdx odd l` holding lane `l`. -/
def laneLimbIdx (odd : Bool) (l : ℕ) : ℕ := if odd ∨ 17 ≤ l then (l + 1) % 2 else l % 2

theorem laneCellIdx_lt (odd : Bool) {l : ℕ} (hl : l < 25) : laneCellIdx odd l < 13 := by
  unfold laneCellIdx; split <;> omega

theorem laneLimbIdx_lt (odd : Bool) (l : ℕ) : laneLimbIdx odd l < 3 := by
  unfold laneLimbIdx; split <;> omega

/-- The cell holding lane `l < 25`. -/
def laneCell (odd : Bool) (l : Fin 25) : Fin 13 := ⟨laneCellIdx odd l, laneCellIdx_lt odd l.isLt⟩

/-- The limb holding lane `l`. -/
def laneLimb (odd : Bool) (l : ℕ) : Fin 3 := ⟨laneLimbIdx odd l, laneLimbIdx_lt odd l⟩

private theorem lane_stateOfCells_nat (cells : Fin 13 → E) (odd : Bool) (l : ℕ) (hl : l < 25) :
    Keccak.lane (stateOfCells cells odd) l =
      ((cells ⟨laneCellIdx odd l, laneCellIdx_lt odd hl⟩).limb (laneLimb odd l)).lane := by
  cases odd <;>
  · simp only [stateOfCells, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.foldl,
      cellLanes]
    interval_cases l <;> simp [Keccak.lane, laneCellIdx, laneLimbIdx, laneLimb]

/-- **Where the cells hold each lane**: lane `l` of the state thirteen cells hold is limb
`laneLimb odd l` of cell `laneCell odd l`. -/
theorem lane_stateOfCells (cells : Fin 13 → E) (odd : Bool) (l : Fin 25) :
    Keccak.lane (stateOfCells cells odd) l =
      ((cells (laneCell odd l)).limb (laneLimb odd l)).lane :=
  lane_stateOfCells_nat cells odd l l.isLt

/-- The cells `KECCAK` writes hold lane `l` where `lane_stateOfCells` reads it. -/
theorem limb_cellsOfState (S : KeccakState) (odd : Bool) (l : Fin 25) :
    (cellsOfState S odd (laneCell odd l)).limb (laneLimb odd l) = K.ofLane (Keccak.lane S l) := by
  cases odd <;> fin_cases l <;> rfl

theorem laneCellIdx_lt_nine (odd : Bool) {l : ℕ} (hl : l < 17) : laneCellIdx odd l < 9 := by
  unfold laneCellIdx; split <;> omega

theorem nine_le_laneCellIdx (odd : Bool) {l : ℕ} (hl : 17 ≤ l) : 9 ≤ laneCellIdx odd l := by
  unfold laneCellIdx; split <;> omega

/-! ## A block XORed into a state -/

/-- Addition in `K` is `XOR` of the lanes. -/
theorem lane_add (a b : K) : K.lane (a + b) = K.lane a ^^^ K.lane b := rfl

@[simp] theorem lane_ofLane (w : UInt64) : K.lane (K.ofLane w) = w := rfl

@[simp] theorem lane_zero : K.lane 0 = 0 := rfl

@[simp] theorem ofLane_zero : K.ofLane 0 = 0 := rfl

/-- The bytes of a block held by the nine cells from its first, in the layout `odd`: in the odd
layout the block starts at the first cell's limb `1`. -/
def blockBytes (odd : Bool) (blk : List E) : List UInt8 :=
  if odd then (cellsBytes blk).drop 8 else cellsBytes blk

/-- The state with a block's seventeen lanes XORed into the rate: what `absorbBlock` permutes. -/
def xorRate (S : KeccakState) (block : List UInt8) : KeccakState :=
  Vector.ofFn fun i ↦ if i.val < 17
      then Keccak.lane S i ^^^ littleEndianLane block i else Keccak.lane S i

theorem absorbBlock_eq (S : KeccakState) (block : List UInt8) :
    absorbBlock S block = keccakF1600 (xorRate S block) := rfl

/-- Lane `l` of a block is where its cells hold it in the block's layout. -/
theorem leLane_blockBytes (odd : Bool) (blk : List E) {l : ℕ} (hl : l < 17) :
    littleEndianLane (blockBytes odd blk) l =
      ((blk.getD (laneCellIdx odd l) 0).limb (laneLimb odd l)).lane := by
  cases odd
  · simp only [blockBytes, Bool.false_eq_true, ↓reduceIte, leLane_cellsBytes, laneCellIdx,
      laneLimb, laneLimbIdx, false_or, show ¬ 17 ≤ l by omega]
  · simp only [blockBytes, ↓reduceIte, ← leLane_succ, leLane_cellsBytes, laneCellIdx, laneLimb,
      laneLimbIdx, true_or]

/-- **The cells of a state plus a block's nine cells hold the state with the block XORed into
its rate**, in the block's layout. -/
theorem stateOfCells_xor {S : KeccakState} {odd : Bool} {blk : List E} {I : Fin 13 → E}
    (hI : ∀ c : Fin 13, I c = cellsOfState S odd c + if c.val < 9 then blk.getD c 0 else 0) :
    stateOfCells I odd = xorRate S (blockBytes odd blk) := by
  apply Vector.ext
  intro i hi
  have e := lane_fin (stateOfCells I odd) ⟨i, hi⟩
  simp only [Fin.getElem_fin] at e
  rw [← e, lane_stateOfCells I odd ⟨i, hi⟩, xorRate, Vector.getElem_ofFn, hI, limb_add,
    limb_cellsOfState, lane_add, lane_ofLane]
  by_cases h : i < 17
  · have h9 := laneCellIdx_lt_nine odd h
    simp only [laneCell, h9, ↓reduceIte, h, leLane_blockBytes odd blk h]
  · have h9 := nine_le_laneCellIdx odd (Nat.le_of_not_lt h)
    simp only [laneCell, show ¬ laneCellIdx odd i < 9 by omega, ↓reduceIte, h, limb_zero,
      lane_zero, UInt64.xor_zero]

/-- **One `KECCAK` absorbs a block**: inputs that are the cells of `S` in the block's layout plus
the block's nine cells (the capacity cells unchanged) permute to the cells of
`absorbBlock S (blockBytes inOdd blk)`, in the output layout. -/
theorem keccak_block {S : KeccakState} {inOdd outOdd : Bool} {blk : List E} {I O : Fin 13 → E}
    (hI : ∀ c : Fin 13, I c = cellsOfState S inOdd c + if c.val < 9 then blk.getD c 0 else 0)
    (h : KeccakCellsRelation I inOdd O outOdd .all) :
    O = cellsOfState (absorbBlock S (blockBytes inOdd blk)) outOdd := by
  funext c
  rw [h.2 c c.isLt, stateOfCells_xor hI, absorbBlock_eq]

/-- The zero state's cells are zero. -/
theorem cellsOfState_zero (odd : Bool) (c : Fin 13) :
    cellsOfState (Vector.replicate 25 0) odd c = 0 := by
  apply E.ext
  intro i
  rw [limb_zero]
  cases odd <;> fin_cases c <;> fin_cases i <;> rfl

end
end LeanVM.Guest.Value.Keccak
