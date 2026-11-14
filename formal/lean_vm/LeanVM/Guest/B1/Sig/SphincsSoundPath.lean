/-
  LeanVM.Guest.B1.Sig.SphincsSoundPath

  `sp_path` (`lean_ethereum.py`) is sound: whatever children are
  hinted, the node a path reaches is the tree's fold of the hinted siblings; with the pieces the
  FORS trees share (`is_child`, `sp_be16`, a node's 80-byte hash).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsForsT
public import LeanVM.Guest.B1.Sig.Merkle
public import LeanVM.Guest.B1.Sig.MerkleComplete

/-!
# `sp_path`, sound

* `pFold`, `nIter`: a path folded from the bottom, and level by level;
* `a1Hi h i`: limb `1` of an address cell `A1` of height `h` and index `i < 2^16`; `sBe16_sound`,
  `a1Hi_xor`: `sp_be16` places the index, and the indices of disjoint bits add;
* `isChild_sound`: `is_child` makes the node the hinted child its bit names, the two children being
  the node and its sibling `siblingOf` in the bit's order (`mPair`);
* `kMsg_cells_sound`, `kNode_sound`: a message of whole cells hashes to their `hcell`; a node's
  80-byte hash;
* `pathAdr`, `pNodeE`, `sPathSib`: a path's node addresses (type `TREE`), its nodes, the hinted
  siblings; `sPath_sound`: `sp_path` of `height` levels from leaf bit `off`, its bits those of
  `e < 2^height` and its shifts `e`'s, reaches `pFold` of `pNodeE`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-! ## Folds -/

/-- A path folded from the bottom: the node at level `l + 1` is `node l` of the one at `l`. -/
def pFold (node : Nat → E → E) : Nat → E → E
  | 0, v => v
  | l + 1, v => node l (pFold node l v)

/-- A path folded level by level, from level `l`, `m` levels. -/
def nIter (node : Nat → E → E) : Nat → Nat → E → E
  | _, 0, v => v
  | l, m + 1, v => nIter node (l + 1) m (node l v)

theorem nIter_pFold (node : Nat → E → E) : ∀ (m l : Nat) (v : E),
    nIter node l m (pFold node l v) = pFold node (l + m) v
  | 0, _, _ => rfl
  | m + 1, l, v => by
      rw [nIter, show node l (pFold node l v) = pFold node (l + 1) v from rfl,
        nIter_pFold node m (l + 1), show l + 1 + m = l + (m + 1) by omega]

theorem nIter_zero (node : Nat → E → E) (m : Nat) (v : E) : nIter node 0 m v = pFold node m v := by
  have := nIter_pFold node m 0 v
  rw [Nat.zero_add] at this
  exact this

/-- `nIter` from level `l` reads the levels from `l` only. -/
theorem nIter_congr {node node' : Nat → E → E} : ∀ (m l : Nat) (v : E),
    (∀ j, l ≤ j → node j = node' j) → nIter node l m v = nIter node' l m v
  | 0, _, _, _ => rfl
  | m + 1, l, v, h => by
      rw [nIter, nIter, h l le_rfl]
      exact nIter_congr m (l + 1) _ fun j hj => h j (by omega)

/-- `nIter` from level `l`, `m` levels, reads the levels `l ..< l + m` only. -/
theorem nIter_congr_lt {node node' : Nat → E → E} : ∀ (m l : Nat) (v : E),
    (∀ j, l ≤ j → j < l + m → node j = node' j) → nIter node l m v = nIter node' l m v
  | 0, _, _, _ => rfl
  | m + 1, l, v, h => by
      rw [nIter, nIter, h l le_rfl (by omega)]
      exact nIter_congr_lt m (l + 1) _ fun j hj1 hj2 => h j (by omega) (by omega)

/-! ## Address words -/

/-- Limb `1` of an address cell `A1`: the height (or chain index) `h` at bit `24`,
the index `i`'s high byte at bit `48` and its low byte at bit `56` (FIPS 205's bytes `27`, `30`,
`31`, big endian). -/
def a1Hi (h i : Nat) : Nat := 2 ^ 24 * h + 2 ^ 48 * (i / 256) + 2 ^ 56 * (i % 256)

theorem pow_mul_xor_pow_mul (s a b : Nat) : 2 ^ s * a ^^^ 2 ^ s * b = 2 ^ s * (a ^^^ b) := by
  rw [Nat.mul_comm (2 ^ s) a, Nat.mul_comm (2 ^ s) b, Nat.mul_comm (2 ^ s), ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.shiftLeft_xor_distrib]

/-- **Indices of disjoint bits**: the `A1` limb of height `z` and index `P`, XOR the index `v`. -/
theorem a1Hi_xor {z P v : Nat} (hz : z < 2 ^ 24) (hP : P < 2 ^ 16) (hv : v < 2 ^ 16) :
    a1Hi z P ^^^ a1Hi 0 v = a1Hi z (P ^^^ v) := by
  have hPv : P ^^^ v < 2 ^ 16 := Nat.xor_lt_two_pow hP hv
  have e1 : ∀ x, x < 2 ^ 16 → (2 ^ 8 * (x % 256) ^^^ x / 256) = 2 ^ 8 * (x % 256) + x / 256 :=
    fun x hx => two_pow_mul_xor (by omega)
  have eP : a1Hi z P = 2 ^ 48 * (2 ^ 8 * (P % 256) ^^^ P / 256) ^^^ 2 ^ 24 * z := by
    rw [e1 P hP, two_pow_mul_xor (by omega), a1Hi]
    ring
  have ev : a1Hi 0 v = 2 ^ 48 * (2 ^ 8 * (v % 256) ^^^ v / 256) := by
    rw [e1 v hv, a1Hi]
    ring
  have eM : (2 ^ 8 * (P % 256) ^^^ P / 256) ^^^ (2 ^ 8 * (v % 256) ^^^ v / 256) =
      2 ^ 8 * ((P ^^^ v) % 256) ^^^ (P ^^^ v) / 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.xor_mod_two_pow, Nat.xor_div_two_pow,
      ← pow_mul_xor_pow_mul]
    ac_rfl
  rw [eP, ev, Nat.xor_assoc, Nat.xor_comm (2 ^ 24 * z), ← Nat.xor_assoc, pow_mul_xor_pow_mul, eM,
    e1 _ hPv, two_pow_mul_xor (by omega), a1Hi]
  ring

/-- Two words add limb by limb. -/
theorem word_add_word (a b c d : Nat) : word a b + word c d = word (a ^^^ c) (b ^^^ d) := by
  simp only [word, ofLimbs_add, ofBits_xor]

/-- A literal past the low limb. -/
theorem lit_hi {X : Nat} (h : X < 2 ^ 64) : lit (2 ^ 64 * X) = word 0 X := by
  simp only [lit, Nat.mul_mod_right, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64),
    Nat.mod_eq_of_lt h]

/-- A word times `y·2^s`. -/
theorem eOfNat_mul_word_hi' {a s : Nat} (h : 2 ^ s * a < 2 ^ 64) :
    eOfNat a * word 0 (2 ^ s) = word 0 (2 ^ s * a) := by
  rw [eOfNat_eq_ofLimbs]
  simp only [word]
  rw [mul_comm, ← ofK_eq_ofLimbs, ofLimbs_mul_ofK, Value.ofBits_zero, zero_mul,
    ofBits_two_pow_mul h]

variable {rd : Reader} {σ : Val}

/-- **`sp_be16`'s multiplier**: `g^8 · 2^120 + 2^112`, the `y` limb's `g^64` reduced. -/
theorem be16HiW_eq : be16HiW = eOfNat 256 * lit (2 ^ 120) + lit (2 ^ 112) := by
  rw [show lit (2 ^ 120) = word 0 (2 ^ 56) by norm_num [lit],
    show lit (2 ^ 112) = word 0 (2 ^ 48) by norm_num [lit], be16HiW, mul_comm, eOfNat, word,
    word, word, ofLimbs_mul_ofK, ofLimbs_add, ofLimbs_inj]
  decide +kernel

/-- **An index's two bytes placed**: `v · 2^120 + (v >> 8) · (g^8 · 2^120 + 2^112)`, `v < 2^16`, is
the index of an `A1`: the high bits' part at `g^128` cancels. -/
theorem be16_split {v : Nat} (hv : v < 2 ^ 16) :
    eOfNat v * lit (2 ^ 120) + eOfNat (v / 256) * be16HiW = word 0 (a1Hi 0 v) := by
  have hq : v / 256 < 2 ^ 8 := by omega
  have hv' : eOfNat v = eOfNat 256 * eOfNat (v / 256) + eOfNat (v % 256) := by
    have e1 : eOfNat 256 * eOfNat (v / 256) = eOfNat (2 ^ 8 * (v / 256)) :=
      eOfNat_two_pow_mul (s := 8) (by omega)
    have e2 : eOfNat (2 ^ 8 * (v / 256)) + eOfNat (v % 256) = eOfNat (2 ^ 8 * (v / 256) + v % 256) :=
      eOfNat_add_of_lt (by omega)
    rw [e1, e2]
    congr 1
    omega
  have hX : eOfNat v * lit (2 ^ 120) + eOfNat (v / 256) * be16HiW =
      eOfNat (v % 256) * lit (2 ^ 120) + eOfNat (v / 256) * lit (2 ^ 112) +
        (eOfNat 256 * eOfNat (v / 256) * lit (2 ^ 120) +
          eOfNat 256 * eOfNat (v / 256) * lit (2 ^ 120)) := by
    rw [hv', be16HiW_eq]
    ring
  have e4 : eOfNat (v % 256) * lit (2 ^ 120) = word 0 (2 ^ 56 * (v % 256)) := by
    rw [show (2 : Nat) ^ 120 = 2 ^ 64 * 2 ^ 56 by norm_num, lit_hi (by norm_num),
      eOfNat_mul_word_hi' (by omega)]
  have e6 : eOfNat (v / 256) * lit (2 ^ 112) = word 0 (2 ^ 48 * (v / 256)) := by
    rw [show (2 : Nat) ^ 112 = 2 ^ 64 * 2 ^ 48 by norm_num, lit_hi (by norm_num),
      eOfNat_mul_word_hi' (by omega)]
  rw [hX, e_add_self, add_zero, e4, e6, word_add_word, Nat.xor_zero]
  congr 1
  rw [show 2 ^ 56 * (v % 256) = 2 ^ 48 * (2 ^ 8 * (v % 256)) by ring, pow_mul_xor_pow_mul,
    two_pow_mul_xor hq, a1Hi]
  ring

/-- **`sp_be16`, sound**: an `n`-bit value `v` (`n ≤ 16`), its shift by eight given when it has a
second byte, is placed as the index of an `A1`. -/
theorem sBe16_sound {val : Nat → V} {pos n x v : Nat} (hn : n ≤ 16) (hv : v < 2 ^ n)
    (h0 : σ (val pos) = eOfNat v) (h8 : 9 ≤ n → σ (val (pos + 8)) = eOfNat (v / 256))
    (h : AtomsHold rd σ (sBe16 val pos n x).1) :
    σ (sBe16 val pos n x).2.2 = word 0 (a1Hi 0 v) := by
  have hv16 : v < 2 ^ 16 := lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hn)
  by_cases h2 : (n + 7) / 8 = 2
  · have q8 := h8 (by omega)
    simp only [sBe16, h2, ↓reduceIte] at h ⊢
    have c0 : σ (.n x) = lit (2 ^ 120) := h.atom (a := .const (.n x) _) (by simp [cst])
    have a1 : σ (.n (x + 1)) = σ (val pos) * σ (.n x) :=
      h.atom (a := .mul (.n (x + 1)) _ _) (by simp [mulS])
    have c2 : σ (.n (x + 2)) = be16HiW := h.atom (a := .const (.n (x + 2)) _) (by simp [cst])
    have a3 : σ (.n (x + 3)) = σ (val (pos + 8)) * σ (.n (x + 2)) :=
      h.atom (a := .mul (.n (x + 3)) _ _) (by simp [mulS])
    have a4 : σ (.n (x + 4)) = σ (.n (x + 1)) + σ (.n (x + 3)) :=
      h.atom (a := .add (.n (x + 4)) _ _) (by simp [addS])
    rw [a4, a1, a3, c0, c2, h0, q8, be16_split hv16]
  · have hv8 : v < 256 := lt_of_lt_of_le hv (by
      calc 2 ^ n ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 256 := by norm_num)
    simp only [sBe16, h2, ↓reduceIte] at h ⊢
    have c0 : σ (.n x) = lit (2 ^ 120) := h.atom (a := .const (.n x) _) (by simp [cst])
    have a1 : σ (.n (x + 1)) = σ (val pos) * σ (.n x) := h.atom (a := .mul _ _ _) (by simp [mulS])
    rw [a1, c0, h0, show (2 : Nat) ^ 120 = 2 ^ 64 * 2 ^ 56 by norm_num, lit_hi (by norm_num),
      eOfNat_mul_word_hi' (by omega), a1Hi, Nat.div_eq_of_lt hv8, Nat.mod_eq_of_lt hv8]
    ring_nf

/-! ## `is_child` -/

/-- **`is_child`, sound**: the children are the node and its sibling, in the order of the bit. -/
theorem isChild_sound {cur bit : V} {x b : Nat} (hbit : IsBit (σ bit))
    (e1 : σ (.n b) = σ cur + σ (.n x)) (e2 : σ (.n (b + 1)) = σ (.n x) + σ (.n (x + 1)))
    (e3 : σ (.n b) = σ bit * σ (.n (b + 1))) :
    (σ (.n x), σ (.n (x + 1))) = mPair (decide (σ bit = 1)) (σ cur) (siblingOf σ bit x) := by
  rcases isBit_cases hbit with h0 | h1
  · rw [h0, zero_mul, e1] at e3
    have : σ cur = σ (.n x) := e_add_eq_zero_iff.mp e3
    simp [h0, this, mPair, siblingOf]
  · rw [h1, one_mul, e1, e2] at e3
    have : σ cur = σ (.n (x + 1)) :=
      add_left_cancel (a := σ (.n x)) (by rw [add_comm (σ (.n x))]; exact e3)
    simp [h1, this, mPair, siblingOf]

/-- A bit of `e` as a cell, pinned Boolean, and its `decide`. -/
theorem bit_facts {σ : Val} {bit : V} {e z : Nat} (hb : σ bit = if e.testBit z then 1 else 0) :
    IsBit (σ bit) ∧ decide (σ bit = 1) = e.testBit z := by
  refine ⟨by rw [hb]; split <;> simp [IsBit], ?_⟩
  rw [hb]
  cases e.testBit z <;> simp

/-! ## The hashes -/

theorem flatMap_cellBytes_length : ∀ cs : List E, (cs.flatMap cellBytes).length = 16 * cs.length
  | [] => rfl
  | c :: cs => by
      simp only [List.flatMap_cons, List.length_append, length_cellBytes,
        flatMap_cellBytes_length cs, List.length_cons]
      ring

theorem kXorByte_getD_ne (cs : List KC) (pos v b : Nat) {j : Nat} (hj : j ≠ pos / 16) :
    (kXorByte cs pos v b).2.1.getD j .zero = cs.getD j .zero := by
  unfold kXorByte
  dsimp only
  split <;> simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]

/-- A message's cells below its length, as `kMsg` absorbs them, are the cells themselves. -/
theorem kMsgCells_getD (cells : List KC) (len b : Nat) {j : Nat} (hj : j < len / 16)
    (hjc : j < cells.length) : (kMsgCells cells len b).getD j .zero = cells.getD j .zero := by
  unfold kMsgCells
  dsimp only
  rw [kXorByte_getD_ne _ _ _ _ (by unfold kBlocksOf; omega),
    kXorByte_getD_ne _ _ _ _ (by omega), List.getD_append _ _ _ _ hjc]

/-- **A message of whole cells has cells for its first block's tail.** -/
theorem tailCells_of_cells {vs : List V} {len b : Nat} (h8 : 8 ≤ vs.length) (hl : 128 ≤ len) :
    TailCells (blockOf (kMsgCells (vs.map KC.cell) len b) 0) := by
  have e : ∀ j, 4 ≤ j → j < 8 →
      (blockOf (kMsgCells (vs.map KC.cell) len b) 0).getD j .zero = .cell (vs.getD j default) := by
    intro j hj1 hj2
    rw [blockOf, Nat.mul_zero, Nat.zero_div, List.drop_zero, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD,
      kMsgCells_getD _ _ _ (by omega) (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, show j < vs.length by omega]
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  exacts [⟨_, e 4 (by omega) (by omega)⟩, ⟨_, e 5 (by omega) (by omega)⟩,
    ⟨_, e 6 (by omega) (by omega)⟩, ⟨_, e 7 (by omega) (by omega)⟩]

/-- **A message of whole cells** hashes to their `hcell`, its one output cell the first half; its
first block's tail may be read in place (`tailRun`) when it has eight cells or more. -/
theorem kMsg_cells_sound {pad : Nat} (hp : PadOK σ pad) {vs : List V} {len b : Nat}
    {tailRun : Bool} (hlen : len = 16 * vs.length) (htr : tailRun = true → 8 ≤ vs.length)
    (h : AtomsHold rd σ (kMsg pad (vs.map KC.cell) len tailRun none b).1) :
    σ (.n (kMsg pad (vs.map KC.cell) len tailRun none b).2.2) = (hcell (vs.map σ)).1 := by
  have hm : (vs.map KC.cell).map (KC.val σ) = vs.map σ := by
    rw [List.map_map]
    rfl
  have k := kMsg_sound (cells := vs.map KC.cell) (len := len) (tailRun := tailRun) (out := none) hp
    (fun ht => tailCells_of_cells (htr ht) (by have := htr ht; omega)) h (by simp [hlen]) (fun j hj => by
    rw [hm, cellsBytes_eq_flatMap, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [flatMap_cellBytes_length, List.length_map]; omega)]
    rfl)
  rw [k, hm, hcell, cellsBytes_eq_flatMap, List.take_of_length_le (by
    rw [flatMap_cellBytes_length, List.length_map]; omega)]

theorem kNode_shape (pad : Nat) (pp a0 adr k0 k1 : V) (y : Nat) :
    (kNode pad pp a0 adr k0 k1 y).2.1 = y + 5 ∧ (kNode pad pp a0 adr k0 k1 y).2.2 = y + 4 := by
  constructor <;> rfl

theorem padCells_five (a b c d e : E) :
    padCells [a, b, c, d, e] 80 = [a, b, c, d, e, word 1 0, 0, 0, word (2 ^ 63) 0] := by
  simp [padCells, xorByte, padRead, rate, byteCell]

/-- **A node's 80-byte hash** of `P`, `A0`, its address and its two children: the right child read
in place, the three cells after it set to the padding (`pad_tail=1`). -/
theorem kNode_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 adr k0 k1 : V} {y : Nat}
    (h : AtomsHold rd σ (kNode pad pp a0 adr k0 k1 y).1) :
    σ (.n (y + 4)) = (hcell [σ pp, σ a0, σ adr, σ k0, σ k1]).1 := by
  obtain ⟨-, p1, p2, p3, p4⟩ := hp
  have c0 : σ (.n y) = word 1 0 := h.atom (a := .const (.n y) _) (by simp [kNode, cst])
  have c1 : σ (.n (y + 1)) = word 0 0 := h.atom (a := .const (.n (y + 1)) _) (by simp [kNode, cst])
  have c2 : σ (.n (y + 2)) = word 0 0 := h.atom (a := .const (.n (y + 2)) _) (by simp [kNode, cst])
  have c3 : σ (.n (y + 3)) = word (2 ^ 63) 0 :=
    h.atom (a := .const (.n (y + 3)) _) (by simp [kNode, cst])
  set ins : List V := [pp, a0, adr, k0, k1, .n y, .n (y + 1), .n (y + 2), .n (y + 3), .n (pad + 1),
    .n (pad + 2), .n (pad + 3), .n (pad + 4)] with hins
  have hk := h.atom (a := .keccak ins (runV (y + 4) 1) false false) (by simp [kNode, kecS, hins])
  obtain ⟨-, -, O, hk, hw⟩ := keccak_holds_full hk
  have hget : ∀ k : Fin 13, cells13 (ins.map σ) k = σ (ins.getD k.val (.n 0)) := fun k => by
    simp only [cells13, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simp [hins])]
    rfl
  have := keccak_one (cells := [σ pp, σ a0, σ adr, σ k0, σ k1]) (len := 80) (by simp)
    (by simp [rate])
    (fun j hj => by
      rw [cellsBytes_eq_flatMap, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        rw [flatMap_cellBytes_length]; simp; omega)]
      rfl)
    (fun k hk => by
      rw [hget, padCells_five]
      obtain ⟨k, hk13⟩ := k
      simp only at hk
      interval_cases k <;> simp [hins, c0, c1, c2, c3, word_zero])
    (fun k hk => by
      rw [hget]
      obtain ⟨k, hk13⟩ := k
      simp only at hk
      interval_cases k <;> simp [hins, p1, p2, p3, p4])
    hk
  have hlen : (cellsBytes [σ pp, σ a0, σ adr, σ k0, σ k1]).length ≤ 80 := by
    rw [cellsBytes_eq_flatMap, flatMap_cellBytes_length]; simp
  rw [List.take_of_length_le hlen] at this
  rw [hcell, ← cellsBytes_eq_flatMap, ← this.2]
  simpa [runV] using hw 0 (by simp [runV])

/-- **One level of a tree**: the children hinted at `x` and checked by `is_child` against `cur` and
the bit `bit`, then hashed at the address `adr` holding `A`, give the parent of `cur` and its
sibling in the bit's order. -/
theorem level_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 adr cur bit : V} {x y : Nat}
    (hbit : IsBit (σ bit))
    (hc : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) bit (x + 2)))
    (hk : AtomsHold rd σ (kNode pad pp a0 adr (.n x) (.n (x + 1)) y).1) :
    σ (.n (y + 4)) = (hcell [σ pp, σ a0, σ adr, (mPair (decide (σ bit = 1)) (σ cur)
      (siblingOf σ bit x)).1, (mPair (decide (σ bit = 1)) (σ cur) (siblingOf σ bit x)).2]).1 := by
  have e1 : σ (.n (x + 2)) = σ cur + σ (.n x) :=
    hc.atom (a := .add (.n (x + 2)) cur (.n x)) (by simp [isChildS, addS])
  have e2 : σ (.n (x + 3)) = σ (.n x) + σ (.n (x + 1)) :=
    hc.atom (a := .add (.n (x + 3)) (.n x) (.n (x + 1))) (by simp [isChildS, addS])
  have e3 : σ (.n (x + 2)) = σ bit * σ (.n (x + 3)) :=
    hc.atom (a := .mul (.n (x + 2)) bit (.n (x + 3))) (by simp [isChildS, mulS])
  rw [← isChild_sound hbit e1 e2 e3]
  exact kNode_sound hp hk

/-! ## The paths -/

/-- The address of a path's node at height `h`, index `i`: type `TREE`, no key pair. -/
def pathAdr (h i : Nat) : E := word (2 * 2 ^ 24) (a1Hi h i)

/-- A path's node at height `z + 1` from the one at `z`, the leaf `e`, its siblings `sib`. -/
def pNodeE (pp a0 : E) (e : Nat) (sib : Nat → E) (z : Nat) (v : E) : E :=
  (hcell [pp, a0, pathAdr (z + 1) (e >>> (z + 1)), (mPair (e.testBit z) v (sib z)).1,
    (mPair (e.testBit z) v (sib z)).2]).1

/-- A path level's width when `m` levels follow it. -/
def pathWidth (m : Nat) : Nat := if m = 0 then 10 else if (m + 7) / 8 = 2 then 16 else 13

/-- The hinted sibling of level `j` of `sPath … m z cur x` (`0` outside its levels). -/
def sPathSib (σ : Val) (bit : Nat → V) (off : Nat) : Nat → Nat → Nat → Nat → E
  | 0, _, _, _ => 0
  | m + 1, z, x, j => if j = z then siblingOf σ (bit (off + z)) x
      else sPathSib σ bit off m (z + 1) (x + pathWidth m) j

/-- A path level's address from base `x`, `m` levels after it: below the root the
index `val (off + z + 1)` (`sBe16`) plus the constant, at the root the constant alone. The
statements, the next base and the address. -/
def sPathAddr (val : Nat → V) (off z m x : Nat) : List Stmt × Nat × V :=
  if m = 0 then ([cst x (lit (pathConst (z + 1)))], x + 1, .n x)
  else
    let be := sBe16 val (off + z + 1) m x
    (be.1 ++ [cst be.2.1 (lit (pathConst (z + 1))), addS (.n (be.2.1 + 1)) be.2.2 (.n be.2.1)],
      be.2.1 + 2, .n (be.2.1 + 1))

theorem sPath_succ (pad : Nat) (pp a0 : V) (bit val : Nat → V) (off m z : Nat) (cur : V) (x : Nat) :
    sPath pad pp a0 bit val off (m + 1) z cur x =
      ([hintW "siblings" [.n x, .n (x + 1)]] ++
        isChildS cur (.n x) (.n (x + 1)) (bit (off + z)) (x + 2) ++
          (sPathAddr val off z m (x + 4)).1 ++
          (kNode pad pp a0 (sPathAddr val off z m (x + 4)).2.2 (.n x) (.n (x + 1))
            (sPathAddr val off z m (x + 4)).2.1).1 ++
          (sPath pad pp a0 bit val off m (z + 1) (.n ((sPathAddr val off z m (x + 4)).2.1 + 4))
            ((sPathAddr val off z m (x + 4)).2.1 + 5)).1,
        (sPath pad pp a0 bit val off m (z + 1) (.n ((sPathAddr val off z m (x + 4)).2.1 + 4))
            ((sPathAddr val off z m (x + 4)).2.1 + 5)).2.1,
        (sPath pad pp a0 bit val off m (z + 1) (.n ((sPathAddr val off z m (x + 4)).2.1 + 4))
            ((sPathAddr val off z m (x + 4)).2.1 + 5)).2.2) := by
  simp only [sPath, sPathAddr, (kNode_shape ..).1, (kNode_shape ..).2]

theorem sBe16_next (val : Nat → V) (pos n x : Nat) :
    (sBe16 val pos n x).2.1 = x + (if (n + 7) / 8 = 2 then 5 else 2) := by
  unfold sBe16; split <;> rfl

/-- The address part of a path level ends `pathWidth m - 5` after its base. -/
theorem sPathAddr_next (val : Nat → V) (off z m x : Nat) :
    (sPathAddr val off z m (x + 4)).2.1 = x + pathWidth m - 5 := by
  unfold sPathAddr pathWidth
  by_cases hm0 : m = 0
  · simp [hm0]
  · simp only [hm0, ↓reduceIte, sBe16_next]
    split_ifs <;> omega

/-- **A path level's address, sound**: the node at height `z + 1` on the path of `e`, `m` levels
after it (`e < 2^(z + 1 + m)`). -/
theorem sPathAddr_sound {val : Nat → V} {off e z m x : Nat} (hzm : z + 1 + m ≤ 16)
    (he : e < 2 ^ (z + 1 + m))
    (hval : ∀ j, z < j → j ≤ z + m → σ (val (off + j)) = eOfNat (e >>> j))
    (hA : AtomsHold rd σ (sPathAddr val off z m x).1) :
    σ (sPathAddr val off z m x).2.2 = pathAdr (z + 1) (e >>> (z + 1)) := by
  unfold sPathAddr at hA ⊢
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte] at hA ⊢
    have c0 : σ (.n x) = lit (pathConst (z + 1)) := hA.atom (a := .const _ _) (by simp [cst])
    have hq : e >>> (z + 1) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (by simpa using he)
    have hlo : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) % 2 ^ 64 = 2 * 2 ^ 24 := by omega
    have hhi : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) / 2 ^ 64 % 2 ^ 64 = 2 ^ 24 * (z + 1) := by omega
    rw [c0, hq, pathAdr, a1Hi, pathConst, lit, hlo, hhi]
    simp only [Nat.zero_div, Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · simp only [hm0, ↓reduceIte] at hA ⊢
    have hv : e >>> (z + 1) < 2 ^ m := by
      rw [Nat.shiftRight_eq_div_pow]
      have : e < 2 ^ (z + 1) * 2 ^ m := by rw [← pow_add]; exact he
      exact Nat.div_lt_of_lt_mul this
    have hbv := sBe16_sound (rd := rd) (n := m) (x := x) (by omega) hv
      (by rw [show off + z + 1 = off + (z + 1) by omega, hval (z + 1) (by omega) (by omega)])
      (fun _ => by
        rw [show off + z + 1 + 8 = off + (z + 9) by omega, hval (z + 9) (by omega) (by omega),
          Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
          show (256 : Nat) = 2 ^ 8 from rfl, ← pow_add])
      hA.left
    have c1 : σ (.n (sBe16 val (off + z + 1) m x).2.1) = lit (pathConst (z + 1)) :=
      hA.right.atom (a := .const _ _) (by simp [cst])
    have a2 : σ (.n ((sBe16 val (off + z + 1) m x).2.1 + 1)) =
        σ (sBe16 val (off + z + 1) m x).2.2 + σ (.n (sBe16 val (off + z + 1) m x).2.1) :=
      hA.right.atom (a := .add _ _ _) (by simp [addS])
    have hv16 : e >>> (z + 1) < 2 ^ 16 :=
      lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [a2, hbv, c1, pathConst, lit, pathAdr, word_add_word]
    have hlo : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) % 2 ^ 64 = 2 * 2 ^ 24 := by omega
    have hhi : (2 * 2 ^ 24 + 2 ^ 88 * (z + 1)) / 2 ^ 64 % 2 ^ 64 = 2 ^ 24 * (z + 1) := by omega
    rw [hlo, hhi, Nat.zero_xor, Nat.xor_comm]
    have := a1Hi_xor (z := z + 1) (P := 0) (v := e >>> (z + 1)) (by omega) (by norm_num) hv16
    rw [Nat.zero_xor] at this
    rw [← this, show a1Hi (z + 1) 0 = 2 ^ 24 * (z + 1) by simp [a1Hi]]

/-- **`sp_path`, sound**: from level `z` (base `x`), `m` levels to height `height`, the bits those
of `e < 2^height` and the shifted values `e`'s, the node reached is `nIter` of the levels, the
siblings those hinted (`sPathSib`). -/
theorem sPath_sound {pad : Nat} (hp : PadOK σ pad) {pp a0 : V} {bit val : Nat → V}
    {off e height : Nat}
    (hh : height ≤ 16) (he : e < 2 ^ height)
    (hbit : ∀ z < height, σ (bit (off + z)) = if e.testBit z then 1 else 0)
    (hval : ∀ z, z < height → σ (val (off + z)) = eOfNat (e >>> z)) :
    ∀ (m z : Nat) (cur : V) (x : Nat), z + m = height →
      AtomsHold rd σ (sPath pad pp a0 bit val off m z cur x).1 →
      σ (sPath pad pp a0 bit val off m z cur x).2.2 =
        nIter (pNodeE (σ pp) (σ a0) e (sPathSib σ bit off m z x)) z m (σ cur)
  | 0, _, _, _, _, _ => rfl
  | m + 1, z, cur, x, hm, hA => by
      rw [sPath_succ] at hA ⊢
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hadr := sPathAddr_sound (off := off) (x := x + 4) (by omega)
        (by rw [show z + 1 + m = height by omega]; exact he)
        (fun j _ hj => hval j (by omega)) hA.left.left.right
      have hk := hA.left.right
      have hc : AtomsHold rd σ (isChildS cur (.n x) (.n (x + 1)) (bit (off + z)) (x + 2)) :=
        hA.left.left.left.sub fun s hs => List.mem_append_right _ hs
      have hlv := level_sound hp hib hc hk
      have hrest := sPath_sound hp hh he hbit hval m (z + 1) _ _ (by omega) hA.right
      have hfirst : σ (.n ((sPathAddr val off z m (x + 4)).2.1 + 4)) =
          pNodeE (σ pp) (σ a0) e (sPathSib σ bit off (m + 1) z x) z (σ cur) := by
        rw [hlv, hd, hadr]
        simp [pNodeE, sPathSib]
      rw [hrest, nIter, hfirst, sPathAddr_next,
        show x + pathWidth m - 5 + 5 = x + pathWidth m by unfold pathWidth; split_ifs <;> omega]
      refine nIter_congr _ _ _ fun j hj => ?_
      unfold pNodeE
      simp only [sPathSib, show j ≠ z by omega, ite_false]

end
end LeanVM.Guest.B1.Sig
