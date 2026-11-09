/-
  LeanVM.Guest.Value.KeccakSponge

  A chain of `KECCAK` atoms absorbing message cells, as the compiler lowers `keccak` and
  `keccak_cells`, computes Keccak-256 of the message bytes.
-/

module

public import LeanVM.Guest.Value.KeccakLayout

/-!
# The sponge over message cells

The compiler's `emit_keccak_message` (`crates/lean_compiler/src/lower/builtins.rs:275-335` at leanVM
`40f877dc`, with `padded` false) absorbs a message held in cells `P` in `B` blocks of `136` bytes,
one `KECCAK` each: block `k` reads the nine cells from `P[17k/2]` in the layout of `k`'s parity,
XORed into the previous output (the zero state, or the `state=` run, for the first), and writes its
output in the next block's layout, the last in the even layout. With a length `len=` (`final`, the
default) the message is the cells' first `len` bytes, padded by XORing `0x01` into byte `len` and
`0x80` into the last byte of block `len / 136` (`xor_byte`, the cells zero-extended to the nine
cells the last block reads: `padCells`); with `final=0` there is no padding and the cells are
zero-extended to whole blocks.

* `absorbChunks n S bytes`: `n` blocks of `136` bytes absorbed into `S`, no padding;
* `keccak256_eq_absorbChunks`: Keccak-256 is `absorbChunks` of the padded message (`padBytes`)
  from the zero state;
* `keccak_chain`: the `KECCAK` chain over cells `P` computes `absorbChunks B S0 (cellsBytes P)`;
* `padCells_bytes`: the compiler's padded cells hold the padded message;
* `keccak_final`, `keccak_final_digest`: a `final` chain (after a prefix of whole blocks, the
  `state=` continuation) computes the state, and the digest cells `0`, `1` are
  `digestHalves (keccak256 (prefix ++ message))`.
-/

namespace LeanVM.Guest.Value.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value.KeccakEval

@[expose] public section

/-! ## Absorbing whole blocks -/

/-- `n` blocks of `136` bytes absorbed into `S`, without padding. -/
def absorbChunks : ℕ → KeccakState → List UInt8 → KeccakState
  | 0, S, _ => S
  | n + 1, S, bs => absorbChunks n (absorbBlock S (bs.take rate)) (bs.drop rate)

/-- The zero state. -/
abbrev zeroState : KeccakState := Vector.replicate 25 0

/-- A state's digest: its first four lanes. -/
def digestOf (S : KeccakState) : Digest :=
  #v[Keccak.lane S 0, Keccak.lane S 1, Keccak.lane S 2, Keccak.lane S 3]

/-- The padded message Keccak-256 absorbs: its whole blocks, then the padded last block. -/
def padBytes (data : List UInt8) : List UInt8 :=
  data.take (rate * (data.length / rate)) ++ padBlock (data.drop (rate * (data.length / rate)))

/-- A block's permutation reads only its first `136` bytes. -/
theorem absorbBlock_take (S : KeccakState) (bs : List UInt8) :
    absorbBlock S (bs.take rate) = absorbBlock S bs := by
  rw [absorbBlock_eq, absorbBlock_eq, xorRate, xorRate]
  refine congrArg keccakF1600 (congrArg Vector.ofFn (funext fun i ↦ ?_))
  split
  · rename_i hi
    congr 1
    unfold littleEndianLane
    refine foldl_congr_mem _ _ fun acc k hk ↦ ?_
    have hk := List.mem_range.mp hk
    have h8 : 8 * i.val + k < rate := by simp only [rate]; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h8, ↓reduceIte]
  · rfl

/-- The last block of `n + 1`. -/
theorem absorbChunks_succ (n : ℕ) (S : KeccakState) (bs : List UInt8) :
    absorbChunks (n + 1) S bs =
      absorbBlock (absorbChunks n S bs) ((bs.drop (rate * n)).take rate) := by
  induction n generalizing S bs with
  | zero => simp [absorbChunks]
  | succ n ih =>
    rw [absorbChunks, ih, absorbChunks, List.drop_drop]
    congr 3
    ring

/-- Blocks absorbed in two runs. -/
theorem absorbChunks_append (n m : ℕ) (S : KeccakState) (bs cs : List UInt8)
    (h : bs.length = rate * n) :
    absorbChunks (n + m) S (bs ++ cs) = absorbChunks m (absorbChunks n S bs) cs := by
  induction n generalizing S bs with
  | zero =>
    rw [Nat.mul_zero, List.length_eq_zero_iff] at h
    subst h
    simp [absorbChunks]
  | succ n ih =>
    rw [show n + 1 + m = (n + m) + 1 by ring, absorbChunks, absorbChunks,
      List.take_append_of_le_length (by rw [h]; simp only [rate]; nlinarith),
      List.drop_append_of_le_length (by rw [h]; simp only [rate]; nlinarith), ih]
    rw [List.length_drop, h]
    simp only [rate]
    ring_nf
    omega

/-- **The Spec's absorption with padding is `absorbChunks` of the padded bytes.** -/
theorem absorb_eq_absorbChunks : ∀ (b : ℕ) (S : KeccakState) (data : List UInt8),
    rate * b ≤ data.length →
      absorb b S data =
        absorbChunks (b + 1) S (data.take (rate * b) ++ padBlock (data.drop (rate * b)))
  | 0, S, data, _ => by
    simp [absorb, absorbChunks, absorbBlock_take]
  | b + 1, S, data, h => by
    have h' : rate ≤ data.length := le_trans (by simp only [rate]; omega) h
    rw [absorb,
      absorb_eq_absorbChunks b _ _ (by rw [List.length_drop]; simp only [rate] at h ⊢; omega)]
    rw [show ∀ S bs, absorbChunks (b + 1 + 1) S bs =
      absorbChunks (b + 1) (absorbBlock S (bs.take rate)) (bs.drop rate) from fun _ _ ↦ rfl]
    rw [List.take_append_of_le_length
        (by simp only [List.length_take]; simp only [rate] at h ⊢; omega),
      List.drop_append_of_le_length
        (by simp only [List.length_take]; simp only [rate] at h ⊢; omega),
      List.take_take, List.drop_take, List.drop_drop]
    have e1 : min rate (rate * (b + 1)) = rate := by simp only [rate]; omega
    have e2 : rate * (b + 1) - rate = rate * b := by simp only [rate]; omega
    have e3 : rate + rate * b = rate * (b + 1) := by ring
    rw [e1, e2, e3]

/-- **Keccak-256 is `absorbChunks` of the padded message from the zero state.** -/
theorem keccak256_eq_absorbChunks (data : List UInt8) :
    keccak256 data =
      digestOf (absorbChunks (data.length / rate + 1) zeroState (padBytes data)) := by
  rw [keccak256_eq_absorb, absorb_eq_absorbChunks _ _ _ (Nat.mul_div_le _ _)]
  rfl

/-! ## The chain of `KECCAK`s -/

/-- The layout block `k` is read in: its parity (`in_odd: k % 2 == 1`). -/
def inLayout (k : ℕ) : Bool := k % 2 == 1

/-- The layout block `k` of `blocks` writes in: the next block's, the last's even
(`out_odd: !last && k % 2 == 0`). -/
def outLayout (blocks k : ℕ) : Bool := k + 1 != blocks && k % 2 == 0

theorem outLayout_eq {blocks k : ℕ} (hk : k < blocks) :
    outLayout blocks k = if k + 1 < blocks then inLayout (k + 1) else false := by
  unfold outLayout inLayout
  by_cases h : k + 1 < blocks
  · rw [ite_eq_left h]
    have : (k + 1 != blocks) = true := by simp; omega
    rw [this, Bool.true_and]
    rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
    · simp [hk2]; omega
    · simp [hk2]; omega
  · rw [ite_eq_right h, show k + 1 = blocks by omega]
    simp

/-- Block `k` of cells `P` read from cell `17k / 2` in its layout is bytes `136k` on. -/
theorem blockBytes_drop (P : List E) (k : ℕ) :
    blockBytes (inLayout k) (P.drop (17 * k / 2)) = (cellsBytes P).drop (rate * k) := by
  rcases Nat.even_or_odd' k with ⟨t, rfl | rfl⟩
  · have : 17 * (2 * t) / 2 = 17 * t := by omega
    simp only [blockBytes, inLayout, this, cellsBytes_drop]
    simp only [rate]
    rw [show (2 * t) % 2 = 0 by omega]
    simp only [beq_iff_eq, zero_ne_one, ↓reduceIte]
    congr 1; ring
  · have : 17 * (2 * t + 1) / 2 = 17 * t + 8 := by omega
    simp only [blockBytes, inLayout, this, cellsBytes_drop, List.drop_drop]
    simp only [rate]
    rw [show (2 * t + 1) % 2 = 1 by omega]
    simp only [beq_self_eq_true, ↓reduceIte]
    congr 1; ring

theorem getD_drop {α : Type} (l : List α) (m c : ℕ) (d : α) :
    (l.drop m).getD c d = l.getD (m + c) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **A chain of `KECCAK`s over message cells is `absorbChunks`.** Block `k < B` reads `I k`:
its nine rate cells the previous output `O k` plus the message cells from `17k / 2`, its four
capacity cells `O k`'s; it writes `O (k + 1)`. From `O 0`, the cells of `S0` in the even layout
(the zero state, or a previous output for `state=`), the last output is the cells of
`absorbChunks B S0 (cellsBytes P)` in the even layout. A message cell past `P` reads `0`. -/
theorem keccak_chain {P : List E} {S0 : KeccakState} {B : ℕ} {I O : ℕ → Fin 13 → E}
    (h0 : O 0 = cellsOfState S0 false)
    (hrate : ∀ k < B, ∀ c : Fin 13, c.val < 9 → I k c = O k c + P.getD (17 * k / 2 + c) 0)
    (hcap : ∀ k < B, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c)
    (hK : ∀ k < B, KeccakCellsRelation (I k) (inLayout k) (O (k + 1)) (outLayout B k) .all) :
    O B = cellsOfState (absorbChunks B S0 (cellsBytes P)) false := by
  have inv : ∀ j ≤ B, O j =
      cellsOfState (absorbChunks j S0 (cellsBytes P)) (if j < B then inLayout j else false) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [h0]
      split <;> rfl
    | succ j ih =>
      intro hj
      have hjB : j < B := by omega
      have hO := ih (by omega)
      rw [ite_eq_left hjB] at hO
      have hb := keccak_block (S := absorbChunks j S0 (cellsBytes P)) (blk := P.drop (17 * j / 2))
        (fun c ↦ by
          by_cases hc : c.val < 9
          · rw [ite_eq_left hc, hrate j hjB c hc, hO, getD_drop]
          · rw [ite_eq_right hc, hcap j hjB c (by omega), hO, add_zero])
        (hK j hjB)
      rw [hb, blockBytes_drop, ← absorbBlock_take, ← absorbChunks_succ, outLayout_eq hjB]
  have := inv B le_rfl
  rwa [ite_eq_right (lt_irrefl B)] at this

/-! ## The padding cells -/

/-- The cell `xor_byte` XORs byte `v` into a message cell with: `v` at byte `pos % 16`, in limb
`0` or `1` (`F192::new(v << 8·(byte % 8), 0, 0)` or `F192::new(0, ·, 0)`, `builtins.rs:339-345`). -/
def byteCell (pos v : ℕ) : E :=
  if pos % 16 < 8 then LeanVM.Guest.word (v * 2 ^ (8 * (pos % 16))) 0 0
  else LeanVM.Guest.word 0 (v * 2 ^ (8 * (pos % 16 - 8))) 0

/-- `xor_byte(cells, pos, v)`: the message cell holding byte `pos` plus `byteCell pos v`
(`builtins.rs:337-355`; a `Zero` cell becomes the constant, a `Const` the constant's sum, a
`Cell` one `XOR` with a constant cell: in each case the sum). -/
def xorByte (cs : List E) (pos v : ℕ) : List E := cs.modify (pos / 16) (· + byteCell pos v)

/-- The cells the last of the `len / 136 + 1` blocks reads up to (`read`, `builtins.rs:288`). -/
def padRead (len : ℕ) : ℕ := 17 * (len / rate) / 2 + 9

/-- **`emit_keccak_message`'s cells for a message of `len` bytes**: the cells zero-extended to
`padRead len`, `0x01` XORed into byte `len` and `0x80` into the last block's last byte
(`builtins.rs:287-305`). -/
def padCells (cells : List E) (len : ℕ) : List E :=
  xorByte (xorByte (cells ++ List.replicate (padRead len - cells.length) 0) len 0x01)
    (rate * (len / rate + 1) - 1) 0x80

/-! ## Bytes of cells, one at a time -/

/-- Byte `b < 16` of a cell. -/
def cellByte (c : E) (b : ℕ) : UInt8 := (K.toBytes (c.limb ⟨b / 8 % 2, by omega⟩)).getD (b % 8) 0

theorem getD_append_left' {l l' : List UInt8} {j : ℕ} (h : j < l.length) :
    (l ++ l').getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {l l' : List UInt8} {j : ℕ} (h : l.length ≤ j) :
    (l ++ l').getD j 0 = l'.getD (j - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_of_length_le {l : List UInt8} {j : ℕ} (h : l.length ≤ j) : l.getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem kBytes_zero : K.toBytes 0 = List.replicate 8 0 := rfl

/-- The bytes past the cells read zero (the hypothesis `hz` of `keccak_final` for a message of
whole cells). -/
theorem getD_cellsBytes_of_le {cs : List E} {len : ℕ} (hlen : 16 * cs.length ≤ len) :
    ∀ j, len ≤ j → (cellsBytes cs).getD j 0 = 0 := fun _ hj ↦
  getD_of_length_le (by rw [length_cellsBytes]; omega)

/-- **Byte `j` of the bytes of cells** is byte `j % 16` of cell `j / 16`. -/
theorem getD_cellsBytes (cs : List E) (j : ℕ) :
    (cellsBytes cs).getD j 0 = cellByte (cs.getD (j / 16) 0) (j % 16) := by
  induction cs generalizing j with
  | nil =>
    have h8 : j % 16 % 8 < 8 := Nat.mod_lt _ (by norm_num)
    rw [cellsBytes_nil, List.getD_nil, List.getD_nil, cellByte, limb_zero, kBytes_zero,
      List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left h8]
    rfl
  | cons c cs ih =>
    rw [cellsBytes_cons]
    by_cases hj : j < 16
    · rw [getD_append_left' (by simpa using hj), cellBytes, Nat.div_eq_of_lt hj,
        Nat.mod_eq_of_lt hj]
      simp only [List.getD_cons_zero, cellByte]
      by_cases h8 : j < 8
      · rw [getD_append_left' (by simpa [K.toBytes] using h8), Nat.mod_eq_of_lt h8]
        simp [Nat.div_eq_of_lt h8]
      · rw [getD_append_right' (by simp [K.toBytes]; omega)]
        have : j / 8 % 2 = 1 := by omega
        simp only [this, K.toBytes, length_wordBytes]
        congr 1; omega
    · rw [getD_append_right' (by simp; omega), ih, length_cellBytes,
        show (c :: cs).getD (j / 16) 0 = cs.getD ((j - 16) / 16) 0 by
          rw [show j / 16 = (j - 16) / 16 + 1 by omega]; rfl]
      congr 1; omega

theorem getD_wordBytes (w : UInt64) {k : ℕ} (hk : k < 8) :
    (wordBytes w).getD k 0 = (w >>> (8 * k).toUInt64).toUInt8 := by
  simp [wordBytes, List.getD_eq_getElem?_getD, List.getElem?_range hk]

/-- A byte of a sum of cells is the `XOR` of their bytes. -/
theorem cellByte_add (c d : E) (b : ℕ) : cellByte (c + d) b = cellByte c b ^^^ cellByte d b := by
  simp only [cellByte, limb_add, K.toBytes, lane_add, getD_wordBytes _ (Nat.mod_lt b (by norm_num))]
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_xor, UInt8.toNat_xor,
    Nat.shiftRight_xor_distrib, Nat.xor_mod_two_pow]

theorem byteCell_mod (pos v : ℕ) : byteCell (pos % 16) v = byteCell pos v := by
  simp [byteCell]

/-- **`xor_byte` XORs one byte**: byte `j` of the cells after `xorByte cs pos v` is byte `j` before,
XORed with byte `j % 16` of `byteCell pos v` in the cell `pos / 16`. -/
theorem getD_xorByte (cs : List E) {pos : ℕ} (v : ℕ) (hpos : pos / 16 < cs.length) (j : ℕ) :
    (cellsBytes (xorByte cs pos v)).getD j 0 = (cellsBytes cs).getD j 0 ^^^
      if j / 16 = pos / 16 then cellByte (byteCell pos v) (j % 16) else 0 := by
  rw [getD_cellsBytes, getD_cellsBytes, xorByte]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases h : j / 16 = pos / 16
  · rw [h, List.getElem?_eq_getElem hpos]
    simp [cellByte_add]
  · simp only [Ne.symm h, h, ↓reduceIte, UInt8.xor_zero]
    rcases cs[j / 16]? <;> rfl

/-- The pad bytes' cells hold their byte where `xor_byte` puts it (checked on the sixteen
positions). -/
theorem cellByte_byteCell_pad (v : ℕ) (hv : v = 1 ∨ v = 0x80) (p b : ℕ) (hp : p < 16)
    (hb : b < 16) :
    cellByte (byteCell p v) b = if b = p then v.toUInt8 else 0 := by
  have h1 : ∀ p, p < 16 → ∀ b, b < 16 → cellByte (byteCell p 1) b = if b = p then 1 else 0 := by
    decide
  have h2 : ∀ p, p < 16 → ∀ b, b < 16 →
      cellByte (byteCell p 0x80) b = if b = p then 0x80 else 0 := by
    decide
  rcases hv with rfl | rfl
  · exact h1 p hp b hb
  · exact h2 p hp b hb

/-- `xor_byte` of a pad byte: byte `j` gains `v` exactly at `j = pos`. -/
theorem getD_xorByte_pad (cs : List E) {pos v : ℕ} (hv : v = 1 ∨ v = 0x80)
    (hpos : pos / 16 < cs.length) (j : ℕ) :
    (cellsBytes (xorByte cs pos v)).getD j 0 =
      (cellsBytes cs).getD j 0 ^^^ if j = pos then v.toUInt8 else 0 := by
  rw [getD_xorByte cs v hpos, ← byteCell_mod,
    cellByte_byteCell_pad v hv _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))]
  congr 1
  by_cases h : j = pos
  · simp [h]
  · have : ¬ (j / 16 = pos / 16 ∧ j % 16 = pos % 16) := fun ⟨h1, h2⟩ ↦ h (by omega)
    by_cases h1 : j / 16 = pos / 16
    · simp [h, h1, show ¬ j % 16 = pos % 16 from fun h2 ↦ this ⟨h1, h2⟩]
    · simp [h, h1]

theorem length_xorByte (cs : List E) (pos v : ℕ) : (xorByte cs pos v).length = cs.length := by
  simp [xorByte]

/-- Byte `i` of the padded last block. -/
theorem getD_padBlock (rest : List UInt8) (hr : rest.length < rate) {i : ℕ} (hi : i < rate) :
    (padBlock rest).getD i 0 =
      rest.getD i 0 ^^^ (if i = rest.length then 1 else 0) ^^^
        (if i = rate - 1 then 0x80 else 0) := by
  have hbase : (rest ++ List.replicate (rate - rest.length) 0)[i]? = some (rest.getD i 0) := by
    by_cases h : i < rest.length
    · rw [List.getElem?_append_left h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
      rfl
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate,
        ite_eq_left (by omega), getD_of_length_le (by omega)]
  simp only [padBlock, List.getD_eq_getElem?_getD (l := List.modify _ _ _), List.getElem?_modify,
    hbase, Option.map_eq_map, Option.map_some, Option.getD_some, padFirst, padLast]
  have e1 : i = rest.length ↔ rest.length = i := eq_comm
  have e2 : i = rate - 1 ↔ rate - 1 = i := eq_comm
  simp only [e1, e2]
  by_cases h1 : rest.length = i <;> by_cases h2 : rate - 1 = i <;>
    simp [h1, h2]

theorem length_padBlock (rest : List UInt8) (hr : rest.length ≤ rate) :
    (padBlock rest).length = rate := by
  simp [padBlock]; omega

/-- Byte `j` of the padded message: the message's, `0x01` at its length, `0x80` at the end. -/
theorem getD_padBytes (data : List UInt8) {j : ℕ} (hj : j < rate * (data.length / rate + 1)) :
    (padBytes data).getD j 0 = data.getD j 0 ^^^ (if j = data.length then 1 else 0) ^^^
      (if j = rate * (data.length / rate + 1) - 1 then 0x80 else 0) := by
  have hq := Nat.mul_div_le data.length rate
  have hq' : data.length < rate * (data.length / rate + 1) := by
    have := Nat.lt_div_mul_add (a := data.length) (b := rate) (by simp [rate])
    simp only [rate] at this ⊢; nlinarith
  rw [padBytes]
  by_cases hjq : j < rate * (data.length / rate)
  · rw [getD_append_left' (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left hjq, ← List.getD_eq_getElem?_getD,
      ite_eq_right (show ¬ j = data.length by omega),
      ite_eq_right (show ¬ j = rate * (data.length / rate + 1) - 1 by simp only [rate] at *; omega)]
    simp
  · rw [getD_append_right' (by simp; omega), List.length_take, min_eq_left (by omega),
      getD_padBlock _ (by simp only [List.length_drop, rate] at *; omega)
        (by simp only [rate] at *; omega)]
    rw [getD_drop, List.length_drop,
      show rate * (data.length / rate) + (j - rate * (data.length / rate)) = j by omega]
    have c1 : j - rate * (data.length / rate) = data.length - rate * (data.length / rate) ↔
        j = data.length := by omega
    have c2 : j - rate * (data.length / rate) = rate - 1 ↔
        j = rate * (data.length / rate + 1) - 1 := by simp only [rate] at *; omega
    simp only [c1, c2]

theorem length_padBytes (data : List UInt8) :
    (padBytes data).length = rate * (data.length / rate + 1) := by
  have hq := Nat.mul_div_le data.length rate
  have hr : data.length - rate * (data.length / rate) < rate := by
    have := Nat.lt_div_mul_add (a := data.length) (b := rate) (by simp [rate])
    simp only [rate] at *; omega
  rw [padBytes, List.length_append, List.length_take, length_padBlock _ (by simp; omega)]
  simp only [rate] at *; omega

/-- Lists of equal length agreeing at every index are equal. -/
theorem ext_getD {l l' : List UInt8} (hl : l.length = l'.length)
    (h : ∀ j < l.length, l.getD j 0 = l'.getD j 0) : l = l' := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := h j h1
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

/-- **The compiler's padded cells hold the padded message**: for `len ≤ 16 · n` bytes of `n`
cells whose bytes past `len` are zero (the compiler requires a cell wholly past `len` to be a
literal `0`; the bytes past `len` in the last cell are the caller's), the first
`136 (len / 136 + 1)` bytes of `padCells cells len` are `padBytes` of the message. -/
theorem padCells_bytes (cells : List E) (len : ℕ) (hlen : len ≤ 16 * cells.length)
    (hz : ∀ j, len ≤ j → (cellsBytes cells).getD j 0 = 0) :
    (cellsBytes (padCells cells len)).take (rate * (len / rate + 1)) =
      padBytes ((cellsBytes cells).take len) := by
  set ext := cells ++ List.replicate (padRead len - cells.length) 0 with hext
  have hextl : ext.length = max cells.length (padRead len) := by
    simp [hext]; omega
  have hread : rate * (len / rate + 1) ≤ 16 * padRead len := by
    simp only [padRead, rate]; omega
  have hlast : (rate * (len / rate + 1) - 1) / 16 < padRead len := by
    simp only [padRead, rate]; omega
  have hdata : ((cellsBytes cells).take len).length = len := by simp; omega
  have hextb : ∀ j, (cellsBytes ext).getD j 0 = ((cellsBytes cells).take len).getD j 0 := by
    intro j
    have h1 : (cellsBytes ext).getD j 0 = (cellsBytes cells).getD j 0 := by
      rw [hext, cellsBytes_append, cellsBytes_replicate_zero]
      by_cases hj' : j < 16 * cells.length
      · exact getD_append_left' (by simpa using hj')
      · rw [getD_append_right' (by simp; omega), getD_of_length_le (l := cellsBytes cells)
          (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
    rw [h1, List.getD_eq_getElem?_getD (l := List.take _ _), List.getElem?_take]
    by_cases hj : j < len
    · rw [ite_eq_left hj, List.getD_eq_getElem?_getD]
    · rw [ite_eq_right hj, Option.getD_none, hz j (by omega)]
  apply ext_getD
  · rw [length_padBytes, hdata, List.length_take, length_cellsBytes, padCells, length_xorByte,
      length_xorByte, hextl]
    simp only [rate] at *
    omega
  · intro j hj
    rw [List.length_take] at hj
    have hj : j < rate * (len / rate + 1) := lt_of_lt_of_le hj (min_le_left _ _)
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj,
      ← List.getD_eq_getElem?_getD, getD_padBytes _ (by rw [hdata]; exact hj), hdata, padCells,
      getD_xorByte_pad _ (Or.inr rfl) (by rw [length_xorByte, hextl]; omega),
      getD_xorByte_pad _ (Or.inl rfl) (by rw [hextl]; simp only [padRead, rate] at *; omega),
      hextb]
    rfl

/-! ## The hash computed by a chain -/

/-- `absorbChunks` reads only the first `136 n` bytes. -/
theorem absorbChunks_take (n : ℕ) (S : KeccakState) (bs : List UInt8) :
    absorbChunks n S (bs.take (rate * n)) = absorbChunks n S bs := by
  induction n generalizing S bs with
  | zero => rfl
  | succ n ih =>
    rw [absorbChunks, absorbChunks, List.take_take, min_eq_left (by simp only [rate]; omega),
      List.drop_take, show rate * (n + 1) - rate = rate * n by simp only [rate]; omega, ih]

/-- A prefix of whole blocks passes through the padding. -/
theorem padBytes_append (pre data : List UInt8) (n : ℕ) (h : pre.length = rate * n) :
    padBytes (pre ++ data) = pre ++ padBytes data := by
  have hl : (pre ++ data).length / rate = n + data.length / rate := by
    rw [List.length_append, h, Nat.mul_comm, Nat.add_comm,
      Nat.add_mul_div_right _ _ (by simp [rate]),
      Nat.add_comm]
  rw [padBytes, padBytes, hl, Nat.mul_add, ← h, List.take_length_add_append,
    List.drop_length_add_append, List.append_assoc]

/-- **Keccak-256 after a prefix of whole blocks**: the prefix's blocks, then the padded rest. -/
theorem keccak256_append (pre data : List UInt8) (n : ℕ) (h : pre.length = rate * n) :
    keccak256 (pre ++ data) =
      digestOf (absorbChunks (data.length / rate + 1) (absorbChunks n zeroState pre)
        (padBytes data)) := by
  have hl : (pre ++ data).length / rate = n + data.length / rate := by
    rw [List.length_append, h, Nat.mul_comm, Nat.add_comm,
      Nat.add_mul_div_right _ _ (by simp [rate]),
      Nat.add_comm]
  rw [keccak256_eq_absorbChunks, hl, padBytes_append pre data n h, Nat.add_assoc,
    absorbChunks_append _ _ _ _ _ h]

/-- A digest's two cells are the first two cells of the state, in the even layout. -/
theorem digestScalars_digestOf (S : KeccakState) :
    digestHalves (digestOf S) = (cellsOfState S false 0, cellsOfState S false 1) := rfl

/-- **A `final` chain computes Keccak-256** (`keccak(...)` and `keccak_cells(...)` with the
default `final`, `builtins.rs:275-335`). The message is the first `len` bytes of `cells`, its
bytes past `len` zero; it is absorbed after `pre`, whole blocks already absorbed into `O 0`
(the zero state, `pre = []`, or a `state=` run); the chain is `keccak_chain`'s over
`padCells cells len`, `len / 136 + 1` blocks. Then the last output is the cells of the state, and
its cells `0` and `1` the digest of `pre ++ message`. -/
theorem keccak_final {cells : List E} {len : ℕ} {pre : List UInt8} {n : ℕ}
    {I O : ℕ → Fin 13 → E}
    (hpre : pre.length = rate * n) (hlen : len ≤ 16 * cells.length)
    (hz : ∀ j, len ≤ j → (cellsBytes cells).getD j 0 = 0)
    (h0 : O 0 = cellsOfState (absorbChunks n zeroState pre) false)
    (hrate : ∀ k < len / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O k c + (padCells cells len).getD (17 * k / 2 + c) 0)
    (hcap : ∀ k < len / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c)
    (hK : ∀ k < len / rate + 1,
      KeccakCellsRelation (I k) (inLayout k) (O (k + 1)) (outLayout (len / rate + 1) k) .all) :
    O (len / rate + 1) = cellsOfState (absorbChunks (n + (len / rate + 1)) zeroState
      (pre ++ padBytes ((cellsBytes cells).take len))) false := by
  rw [keccak_chain h0 hrate hcap hK, ← absorbChunks_take, padCells_bytes cells len hlen hz,
    absorbChunks_append _ _ _ _ _ hpre]

/-- **The digest cells of a `final` chain** (`keccak_final`): cells `0` and `1` of the last
output are `digestHalves (keccak256 (pre ++ message))`. -/
theorem keccak_final_digest {cells : List E} {len : ℕ} {pre : List UInt8} {n : ℕ}
    {I O : ℕ → Fin 13 → E}
    (hpre : pre.length = rate * n) (hlen : len ≤ 16 * cells.length)
    (hz : ∀ j, len ≤ j → (cellsBytes cells).getD j 0 = 0)
    (h0 : O 0 = cellsOfState (absorbChunks n zeroState pre) false)
    (hrate : ∀ k < len / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I k c = O k c + (padCells cells len).getD (17 * k / 2 + c) 0)
    (hcap : ∀ k < len / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c)
    (hK : ∀ k < len / rate + 1,
      KeccakCellsRelation (I k) (inLayout k) (O (k + 1)) (outLayout (len / rate + 1) k) .all) :
    (O (len / rate + 1) 0, O (len / rate + 1) 1) =
      digestHalves (keccak256 (pre ++ (cellsBytes cells).take len)) := by
  have hdata : ((cellsBytes cells).take len).length = len := by simp; omega
  rw [keccak_final hpre hlen hz h0 hrate hcap hK, keccak256_append _ _ _ hpre, hdata,
    ← absorbChunks_append _ _ _ _ _ hpre, digestScalars_digestOf]

/-- **One block from the zero state** (`keccak(a, b, out, tail=, len=)`, at most `128` bytes, one
`KECCAK` in the even layouts, its capacity cells the zero run `keccak_pad_run() + 1`): the
digest cells are `digestHalves (keccak256 message)`, the output the state's cells. -/
theorem keccak_one {cells : List E} {len : ℕ} {I O : Fin 13 → E}
    (hlen : len ≤ 16 * cells.length) (hlt : len < rate)
    (hz : ∀ j, len ≤ j → (cellsBytes cells).getD j 0 = 0)
    (hrate : ∀ c : Fin 13, c.val < 9 → I c = (padCells cells len).getD c 0)
    (hcap : ∀ c : Fin 13, 9 ≤ c.val → I c = 0)
    (hK : KeccakCellsRelation I false O false .all) :
    O = cellsOfState (absorbChunks 1 zeroState (padBytes ((cellsBytes cells).take len))) false ∧
      (O 0, O 1) = digestHalves (keccak256 ((cellsBytes cells).take len)) := by
  have hB : len / rate + 1 = 1 := by rw [Nat.div_eq_of_lt hlt]
  let O' : ℕ → Fin 13 → E := fun k ↦ if k = 0 then cellsOfState zeroState false else O
  let I' : ℕ → Fin 13 → E := fun _ ↦ I
  have h0 : O' 0 = cellsOfState (absorbChunks 0 zeroState []) false := rfl
  have hrate' : ∀ k < len / rate + 1, ∀ c : Fin 13, c.val < 9 →
      I' k c = O' k c + (padCells cells len).getD (17 * k / 2 + c) 0 := by
    intro k hk c hc
    obtain rfl : k = 0 := by omega
    simp [I', O', cellsOfState_zero, hrate c hc]
  have hcap' : ∀ k < len / rate + 1, ∀ c : Fin 13, 9 ≤ c.val → I' k c = O' k c := by
    intro k hk c hc
    obtain rfl : k = 0 := by omega
    simp [I', O', cellsOfState_zero, hcap c hc]
  have hK' : ∀ k < len / rate + 1,
      KeccakCellsRelation (I' k) (inLayout k) (O' (k + 1)) (outLayout (len / rate + 1) k) .all := by
    intro k hk
    obtain rfl : k = 0 := by omega
    rw [hB]
    exact hK
  have hf := keccak_final (pre := []) (n := 0) rfl hlen hz h0 hrate' hcap' hK'
  have hd := keccak_final_digest (pre := []) (n := 0) rfl hlen hz h0 hrate' hcap' hK'
  simp only [hB, O', one_ne_zero, ↓reduceIte, List.nil_append, Nat.zero_add] at hf hd
  exact ⟨hf, hd⟩

/-- **A `final=0` chain over whole blocks** (`keccak_cells(cells, out, state=, final=0)` with
`16 n = 136 B`): the state after `pre ++ cells`, ready for a later `state=` continuation. -/
theorem keccak_whole {cells : List E} {pre : List UInt8} {n B : ℕ} {I O : ℕ → Fin 13 → E}
    (hpre : pre.length = rate * n) (hB : 16 * cells.length = rate * B)
    (h0 : O 0 = cellsOfState (absorbChunks n zeroState pre) false)
    (hrate : ∀ k < B, ∀ c : Fin 13, c.val < 9 → I k c = O k c + cells.getD (17 * k / 2 + c) 0)
    (hcap : ∀ k < B, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c)
    (hK : ∀ k < B, KeccakCellsRelation (I k) (inLayout k) (O (k + 1)) (outLayout B k) .all) :
    O B = cellsOfState (absorbChunks (n + B) zeroState (pre ++ cellsBytes cells)) false ∧
      (pre ++ cellsBytes cells).length = rate * (n + B) := by
  refine ⟨?_, by rw [List.length_append, hpre, length_cellsBytes, hB, Nat.mul_add]⟩
  rw [keccak_chain h0 hrate hcap hK, absorbChunks_append _ _ _ _ _ hpre]

@[simp] theorem lane_zeroState (i : ℕ) : Keccak.lane zeroState i = 0 := by
  simp only [Keccak.lane, Array.getD_eq_getD_getElem?]
  by_cases h : i < 25
  · simp [h]
  · simp [h]

/-- **The Fiat-Shamir seed** (`keccak_cells([seed_0, seed_1, pi_0, pi_1], sp, final=0)` in
`verify_sub`): one block of the digests' cells, zero-extended, is
`keccakF (Compile.seedInput iv pi)`. -/
theorem absorbChunks_seed (iv pi : Digest) :
    absorbChunks 1 zeroState (cellsBytes [(digestHalves iv).1, (digestHalves iv).2,
      (digestHalves pi).1, (digestHalves pi).2]) = keccakF1600 (Compile.seedInput iv pi) := by
  rw [absorbChunks, absorbChunks, absorbBlock_take, absorbBlock_eq]
  refine congrArg keccakF1600 ?_
  apply Vector.ext
  intro i hi
  simp only [xorRate, Vector.getElem_ofFn, Compile.seedInput]
  split
  · rename_i h17
    rw [leLane_cellsBytes, lane_zeroState, UInt64.zero_xor]
    interval_cases i <;> simp [digestHalves, limb_zero]
  · rename_i h17
    rw [dite_eq_right (by omega), dite_eq_right (by omega), lane_zeroState]

end
end LeanVM.Guest.Value.Keccak
