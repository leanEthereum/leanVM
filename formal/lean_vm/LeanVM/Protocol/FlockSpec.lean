/-
  LeanVM.Protocol.FlockSpec

  What the Flock region of an arithmetization means: an R1CS on the region's blocks, the cells
  where each block carries the eighteen limbs of a BLAKE2s compression, and the two directions
  between the region predicate and the compression relation. Its inhabitant is the BLAKE2s
  circuit of leanVM.
-/

module

public import LeanVM.Protocol.Blake2sCircuit
public import LeanVM.Protocol.Spine.Instance

/-!
# The Flock specification and its BLAKE2s inhabitant

The Flock phase establishes `BlockR1CS.BatchHolds r1cs 512 (bitTable c)` of the committed region
`c` (`FlockRegion.Holds`): every block of `2 ^ 14` bits, packed 64 to a cell, satisfies the
region's R1CS and holds `1` at position `512`. Block `t` is the cells `256 t, …, 256 t + 255`;
cell `s` of it holds the bits `64 s, …, 64 s + 63`.

A `FlockSpec` says what that predicate means, with no instance in sight:

* `r1cs`, the block R1CS; `slot j`, the cell of a block holding limb `j` of a compression, in
  the order of the eighteen value limbs `m0, m1, m2, m3, out0, out1, cv0, cv1, md`, low limb
  first (`slotLimbs`);
* `compress_of_holds` (soundness): every block of a column satisfying the predicate carries a
  compression at its slots (`LimbsCompress`, the cell relation `CompressCells` of the nine cells
  the limbs form);
* `gen`, `holds_gen` (completeness): the column the honest prover builds from a batch of limb
  rows satisfies the predicate;
* `slots_gen`: the column carries every row that is a compression at its block's slots.

`compress_of_region`, `region_holds_gen`: the two directions for a Flock region whose matrices
are the specification's, whatever walks it evaluates them by. The inhabitant's `r1cs` carries the
naive walks of `ProductCircuit.toBlockR1CS`, which sum `2 ^ 28` entries and do not run at
leanVM's size; a region with fast walks of the same matrices inherits both directions through
these two theorems.

`blake2sFlockSpec` is the inhabitant: the R1CS of `blake2sCircuit` and the deployed slots
(transcribed from `crates/leanvm_core/src/hash_flock.rs:76-108` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, `SLOTS` in the order of
`tables::BLAKE2S_VALUE_COLS`); its generator places each row's input limbs at their slots and
runs the circuit's trace.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters LeanVM.Semantics CompPoly ProductCircuit

@[expose] public section

/-! ## Blocks of a column -/

section Blocks

variable {κ : ℕ}

/-- Cell `s` of block `t` of a column of `2 ^ κ` blocks of `256` cells: cell `s + 256 t`. -/
def blockCell (c : Column (8 + κ)) (t : Fin (2 ^ κ)) (s : Fin 256) : K :=
  c.values[cubeIndex (k := 8) s t]

/-- The limbs block `t` carries at the cells `slot j`. -/
def slotLimbs (slot : Fin 18 → Fin 256) (c : Column (8 + κ)) (t : Fin (2 ^ κ)) : Fin 18 → K :=
  fun j ↦ blockCell c t (slot j)

end Blocks

/-- The eighteen limbs, in the order `m0, m1, m2, m3, out0, out1, cv0, cv1, md` (low limb first),
are a BLAKE2s compression: the nine cells they form satisfy `CompressCells`. -/
def LimbsCompress (l : Fin 18 → K) : Prop :=
  CompressCells ![E.ofCell #v[l 0, l 1], E.ofCell #v[l 2, l 3], E.ofCell #v[l 4, l 5],
      E.ofCell #v[l 6, l 7]]
    (E.ofCell #v[l 12, l 13]) (E.ofCell #v[l 14, l 15]) (E.ofCell #v[l 8, l 9])
    (E.ofCell #v[l 10, l 11]) (E.ofCell #v[l 16, l 17])

instance (l : Fin 18 → K) : Decidable (LimbsCompress l) := by
  unfold LimbsCompress; infer_instance

/-- What the Flock region means: its R1CS, the cells of a block holding the limbs of a
compression, and the two directions between the region predicate and the compression
relation. -/
structure FlockSpec where
  /-- The R1CS of one block. -/
  r1cs : BlockR1CS E (Flock.kSkip + Flock.kIn)
  /-- The cell of a block holding limb `j`. -/
  slot : Fin 18 → Fin 256
  /-- Soundness: every block of a column satisfying the predicate carries a compression. -/
  compress_of_holds : ∀ {κ : ℕ} (c : Column (8 + κ)),
    BlockR1CS.BatchHolds r1cs Flock.constPos (bitTable c) → ∀ t, LimbsCompress (slotLimbs slot c t)
  /-- The honest prover's column of a batch of limb rows. -/
  gen : {κ : ℕ} → Vector (Fin 18 → K) (2 ^ κ) → Column (8 + κ)
  /-- Completeness: the honest column satisfies the predicate. -/
  holds_gen : ∀ {κ : ℕ} (rows : Vector (Fin 18 → K) (2 ^ κ)),
    BlockR1CS.BatchHolds r1cs Flock.constPos (bitTable (gen rows))
  /-- The honest column carries every row that is a compression at its block's slots. -/
  slots_gen : ∀ {κ : ℕ} (rows : Vector (Fin 18 → K) (2 ^ κ)) (t : Fin (2 ^ κ)),
    LimbsCompress rows[t] → slotLimbs slot (gen rows) t = rows[t]

namespace FlockSpec

variable (F : FlockSpec)

/-- Soundness on a Flock region whose matrices are the specification's, whatever its walks. -/
theorem compress_of_region {S : Shape} (r : FlockRegion S) (hA : r.r1cs.A = F.r1cs.A)
    (hB : r.r1cs.B = F.r1cs.B) (c : Column (8 + r.kBatch)) (h : r.Holds c)
    (t : Fin (2 ^ r.kBatch)) : LimbsCompress (slotLimbs F.slot c t) :=
  F.compress_of_holds c (fun t ↦ ⟨(BlockR1CS.holds_congr hA hB _).mp (h t).1, (h t).2⟩) t

/-- Completeness on such a region: the honest column satisfies the region predicate. -/
theorem region_holds_gen {S : Shape} (r : FlockRegion S) (hA : r.r1cs.A = F.r1cs.A)
    (hB : r.r1cs.B = F.r1cs.B) (rows : Vector (Fin 18 → K) (2 ^ r.kBatch)) :
    r.Holds (F.gen rows) := fun t ↦
  ⟨(BlockR1CS.holds_congr hA hB _).mpr (F.holds_gen rows t).1, (F.holds_gen rows t).2⟩

end FlockSpec

/-! ## The BLAKE2s inhabitant -/

namespace Blake2sFlock

open Blake2sCircuit

/-- The deployed slots, `SLOTS` of `hash_flock.rs:86-108`: message cells `10 … 17`, output cells
`4 … 7`, chaining-value cells `0 … 3`, metadata cells `18, 19`. -/
def slots : Fin 18 → Fin 256 := ![10, 11, 12, 13, 14, 15, 16, 17, 4, 5, 6, 7, 0, 1, 2, 3, 18, 19]

/-- No two limbs share a cell. -/
theorem slots_injective : Function.Injective slots := by decide

section Blocks

variable {κ : ℕ}

/-- Block `t` of a column as a Boolean block: position `j` is bit `j mod 64` of cell `j / 64`. -/
def blockBits (c : Column (8 + κ)) (t : Fin (2 ^ κ)) : Pos m → Bool := fun j ↦
  (blockCell c t ⟨j.val / 64, by have : j.val < 16384 := j.isLt; omega⟩).toBitVec.getLsbD
    (j.val % 64)

private theorem cubeSplit_symm {k n : ℕ} (j : Fin (2 ^ (k + n))) :
    (cubeSplit k n).symm j =
      (⟨j.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩,
        ⟨j.val / 2 ^ k, Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact j.isLt)⟩) := by
  rw [Equiv.symm_apply_eq, cubeSplit_apply]
  ext
  simp only [cubeIndex_val]
  exact (Nat.mod_add_div _ _).symm

/-- The block the region predicate reads at batch index `t` is the Boolean block
`blockBits c t`. -/
theorem batchBlock_bitTable (c : Column (8 + κ)) (t : Fin (2 ^ κ)) :
    BlockR1CS.batchBlock (s := Flock.kSkip) (m := Flock.kIn) (bitTable c) t =
      liftBlock E (blockBits c t) := by
  refine Vector.ext fun j hj ↦ ?_
  simp only [BlockR1CS.batchBlock, liftBlock, Vector.getElem_ofFn, bitTable, cubeSplit_symm,
    ofBool, cellBit, blockBits, blockCell, Vector.get_eq_getElem, Fin.getElem_fin]
  rfl

private theorem blockBits_pos (c : Column (8 + κ)) (t : Fin (2 ^ κ)) (s : Fin 256) {i : ℕ}
    (hi : i < 64) :
    blockBits c t (pos (64 * s.val + i)) = (blockCell c t s).toBitVec.getLsbD i := by
  have h1 : (64 * s.val + i) % 2 ^ m = 64 * s.val + i := Nat.mod_eq_of_lt (by
    have := s.isLt; show _ < 16384; omega)
  have h2 : (64 * s.val + i) / 64 = s.val := by omega
  have h3 : (64 * s.val + i) % 64 = i := by omega
  simp only [blockBits, pos, h1, h2, h3]

/-- Word `w` of block `t`: the low (`w` even) or high (`w` odd) word of cell `w / 2`. -/
private def colWord (c : Column (8 + κ)) (t : Fin (2 ^ κ)) (w : Fin 512) : UInt32 :=
  if w.val % 2 = 0 then lowWord (blockCell c t ⟨w.val / 2, by omega⟩)
  else highWord (blockCell c t ⟨w.val / 2, by omega⟩)

/-- The input word at `32 w` of block `t` denotes word `w` of the block. -/
private theorem den_colWord (c : Column (8 + κ)) (t : Fin (2 ^ κ)) (w : Fin 512) {b : ℕ}
    (hb : b = 32 * w.val) : Den (blockBits c t) (inW b) (colWord c t w) := by
  refine den_inW fun i ↦ ?_
  subst hb
  unfold colWord
  split_ifs with h
  · rw [show 32 * w.val + i.val = 64 * (w.val / 2) + i.val by omega,
      blockBits_pos c t ⟨w.val / 2, by omega⟩ (by omega)]
    simp [lowWord, i.isLt]
  · rw [show 32 * w.val + i.val = 64 * (w.val / 2) + (32 + i.val) by omega,
      blockBits_pos c t ⟨w.val / 2, by omega⟩ (by omega)]
    simp [highWord, i.isLt, Nat.add_comm]

end Blocks

/-! ### Soundness -/

section Soundness

variable {κ : ℕ}

private theorem cellWords_ofCell (a b : K) :
    cellWords (E.ofCell #v[a, b]) = #v[lowWord a, highWord a, lowWord b, highWord b] := rfl

private theorem append_4_4 {α : Type} (a b c d e f g h : α) :
    #v[a, b, c, d] ++ #v[e, f, g, h] = #v[a, b, c, d, e, f, g, h] := by
  apply Vector.toArray_inj.mp; simp only [Vector.toArray_append]; rfl

private theorem append_4_4_4_4 {α : Type} (a b c d e f g h i j k l m n o p : α) :
    #v[a, b, c, d] ++ #v[e, f, g, h] ++ #v[i, j, k, l] ++ #v[m, n, o, p] =
      #v[a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p] := by
  apply Vector.toArray_inj.mp; simp only [Vector.toArray_append]; rfl

private theorem ofFn_8 {α : Type} (f : Fin 8 → α) :
    Vector.ofFn f = #v[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7] := by
  apply Vector.toArray_inj.mp; simp [Array.ofFn_succ]

private theorem ofFn_16 {α : Type} (f : Fin 16 → α) :
    Vector.ofFn f = #v[f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13,
      f 14, f 15] := by
  apply Vector.toArray_inj.mp; simp [Array.ofFn_succ]

private theorem counterLo_eq (a : K) : lowWord a = (⟨a.toBitVec⟩ : UInt64).toUInt32 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [lowWord, hi]

private theorem counterHi_eq (a : K) :
    highWord a = ((⟨a.toBitVec⟩ : UInt64) >>> 32).toUInt32 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [highWord, hi]

/-- The words of two consecutive cells `s, s + 1` of block `t` are its words `2 s, …, 2 s + 3`. -/
private theorem cellWords_pair (c : Column (8 + κ)) (t : Fin (2 ^ κ)) (s s' : Fin 256)
    (hs : s'.val = s.val + 1) :
    cellWords (E.ofCell #v[blockCell c t s, blockCell c t s']) =
      #v[colWord c t ⟨2 * s.val, by omega⟩, colWord c t ⟨2 * s.val + 1, by omega⟩,
        colWord c t ⟨2 * s.val + 2, by omega⟩, colWord c t ⟨2 * s.val + 3, by omega⟩] := by
  rw [cellWords_ofCell]
  have e0 : (⟨2 * s.val / 2, by omega⟩ : Fin 256) = s := Fin.ext (by simp only; omega)
  have e1 : (⟨(2 * s.val + 1) / 2, by omega⟩ : Fin 256) = s := Fin.ext (by simp only; omega)
  have e2 : (⟨(2 * s.val + 2) / 2, by omega⟩ : Fin 256) = s' := Fin.ext (by simp only; omega)
  have e3 : (⟨(2 * s.val + 3) / 2, by omega⟩ : Fin 256) = s' := Fin.ext (by simp only; omega)
  simp only [colWord, show 2 * s.val % 2 = 0 by omega, show (2 * s.val + 1) % 2 = 1 by omega,
    show (2 * s.val + 2) % 2 = 0 by omega, show (2 * s.val + 3) % 2 = 1 by omega, e0, e1, e2, e3]
  rfl

/-- Soundness of the BLAKE2s circuit on a region: every block of a column satisfying the region
predicate with the circuit's R1CS carries a compression at the deployed slots. -/
theorem compress_of_holds (c : Column (8 + κ))
    (h : BlockR1CS.BatchHolds (blake2sCircuit.toBlockR1CS E) Flock.constPos (bitTable c))
    (t : Fin (2 ^ κ)) : LimbsCompress (slotLimbs slots c t) := by
  obtain ⟨hz, h1⟩ := h t
  rw [batchBlock_bitTable] at hz h1
  have h1' : blockBits c t Flock.constPos = true := by
    have : ofBool E (blockBits c t Flock.constPos) = 1 := by simpa [liftBlock] using h1
    exact ofBool_injective (this.trans (by simp [ofBool]))
  have key := blake2s_sound (blockBits c t) hz h1'
    (h := Vector.ofFn fun k : Fin 8 ↦ colWord c t ⟨k, by omega⟩)
    (msg := Vector.ofFn fun k : Fin 16 ↦ colWord c t ⟨20 + k, by omega⟩)
    (t := ⟨(blockCell c t 18).toBitVec⟩) (f0 := colWord c t 38) (f1 := colWord c t 39)
    (fun k ↦ by
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact den_colWord c t _ rfl)
    (fun k ↦ by
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact den_colWord c t _ (by simp only [msgBase]; omega))
    (den_congr (den_colWord c t 36 rfl) (counterLo_eq _))
    (den_congr (den_colWord c t 37 rfl) (counterHi_eq _))
    (den_colWord c t 38 rfl) (den_colWord c t 39 rfl)
  unfold LimbsCompress CompressCells
  refine ⟨fun i ↦ by fin_cases i <;> rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [slotLimbs, slots, Matrix.cons_val]
  have hcv : cellWords (E.ofCell #v[blockCell c t 0, blockCell c t 1]) ++
      cellWords (E.ofCell #v[blockCell c t 2, blockCell c t 3]) =
      Vector.ofFn fun k : Fin 8 ↦ colWord c t ⟨k, by omega⟩ := by
    rw [cellWords_pair c t 0 1 rfl, cellWords_pair c t 2 3 rfl, append_4_4, ofFn_8]
    rfl
  have hmsg : messageWords ![E.ofCell #v[blockCell c t 10, blockCell c t 11],
      E.ofCell #v[blockCell c t 12, blockCell c t 13],
      E.ofCell #v[blockCell c t 14, blockCell c t 15],
      E.ofCell #v[blockCell c t 16, blockCell c t 17]] =
      Vector.ofFn fun k : Fin 16 ↦ colWord c t ⟨20 + k, by omega⟩ := by
    rw [messageWords]
    simp only [Matrix.cons_val]
    rw [cellWords_pair c t 10 11 rfl, cellWords_pair c t 12 13 rfl,
      cellWords_pair c t 14 15 rfl, cellWords_pair c t 16 17 rfl, append_4_4_4_4, ofFn_16]
    rfl
  have hout : cellWords (E.ofCell #v[blockCell c t 4, blockCell c t 5]) ++
      cellWords (E.ofCell #v[blockCell c t 6, blockCell c t 7]) =
      Vector.ofFn fun k : Fin 8 ↦ colWord c t ⟨8 + k, by omega⟩ := by
    rw [cellWords_pair c t 4 5 rfl, cellWords_pair c t 6 7 rfl, append_4_4, ofFn_8]
    rfl
  have hmd : unpackMetadata (E.ofCell #v[blockCell c t 18, blockCell c t 19]) =
      ((⟨(blockCell c t 18).toBitVec⟩ : UInt64), colWord c t 38, colWord c t 39) := rfl
  rw [hcv, hmsg, hout, hmd]
  refine Vector.ext fun k hk ↦ ?_
  rw [Vector.getElem_ofFn]
  exact den_unique (den_colWord c t ⟨8 + k, by omega⟩ (b := 256 + 32 * k) (by simp; omega))
    (key ⟨k, hk⟩)

end Soundness

/-! ### Completeness -/

section Completeness

variable {κ : ℕ}

/-- A cell is determined by its two words. -/
private theorem eq_of_words {a a' : K} (hl : lowWord a = lowWord a')
    (hh : highWord a = highWord a') :
    a = a' := by
  apply BF64.toBitVec_injective
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases h : i < 32
  · have := congrArg (fun w : UInt32 ↦ w.toBitVec.getLsbD i) hl
    simpa [lowWord, h] using this
  · have := congrArg (fun w : UInt32 ↦ w.toBitVec.getLsbD (i - 32)) hh
    simpa [highWord, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega] using this

/-- The fourteen input limbs: the message, chaining-value and metadata limbs. -/
def IsInputLimb (j : Fin 18) : Prop := j.val < 8 ∨ 12 ≤ j.val

instance : DecidablePred IsInputLimb :=
  fun j ↦ inferInstanceAs (Decidable (j.val < 8 ∨ 12 ≤ j.val))

/-- A compression is determined by its input limbs: two compressions agreeing on the fourteen
input limbs are equal. -/
theorem limbsCompress_unique {l l' : Fin 18 → K} (hl : LimbsCompress l) (hl' : LimbsCompress l')
    (h : ∀ j, IsInputLimb j → l j = l' j) : l = l' := by
  unfold LimbsCompress CompressCells at hl hl'
  have e := hl.2.2.2.2.2.2
  have e' := hl'.2.2.2.2.2.2
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), h 12 (by decide), h 13 (by decide),
    h 14 (by decide), h 15 (by decide), h 16 (by decide), h 17 (by decide), ← e'] at e
  rw [cellWords_ofCell, cellWords_ofCell, cellWords_ofCell, cellWords_ofCell, append_4_4,
    append_4_4] at e
  have w (i : ℕ) (hi : i < 8) := congrArg (fun v : Vector UInt32 8 ↦ v[i]) e
  funext j
  by_cases hj : IsInputLimb j
  · exact h j hj
  · have : j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by
      unfold IsInputLimb at hj; omega
    rcases this with rfl | rfl | rfl | rfl
    · exact eq_of_words (w 0 (by decide)) (w 1 (by decide))
    · exact eq_of_words (w 2 (by decide)) (w 3 (by decide))
    · exact eq_of_words (w 4 (by decide)) (w 5 (by decide))
    · exact eq_of_words (w 6 (by decide)) (w 7 (by decide))

/-- The cell of a limb row's input block: the input limbs at their slots, `0` elsewhere (the
output cells are the trace's to fill). -/
def inputCell (l : Fin 18 → K) : ℕ → K
  | 0 => l 12 | 1 => l 13 | 2 => l 14 | 3 => l 15
  | 10 => l 0 | 11 => l 1 | 12 => l 2 | 13 => l 3 | 14 => l 4 | 15 => l 5 | 16 => l 6 | 17 => l 7
  | 18 => l 16 | 19 => l 17
  | _ => 0

private theorem inputCell_slots (l : Fin 18 → K) (j : Fin 18) (hj : IsInputLimb j) :
    inputCell l (slots j) = l j := by
  fin_cases j <;> first | rfl | (exfalso; revert hj; decide)

/-- The input block of a limb row, as a bitset: bit `j mod 64` of input cell `j / 64` for the
`1280` positions below the gates, `0` above. -/
def inputForm (l : Fin 18 → K) : Form m :=
  (BitVec.ofFnLE fun j : Fin 1280 ↦
    (inputCell l (j.val / 64)).toBitVec.getLsbD (j.val % 64)).setWidth (2 ^ m)

/-- The honest block of a limb row: the circuit's trace on its input block. -/
def honestBlock (l : Fin 18 → K) : Form m := blake2sCircuit.trace (inputForm l)

/-- Cell `s` of a block given as a bitset: its bits `64 s, …, 64 s + 63`. -/
def packCell (z : Form m) (s : Fin 256) : K := BF64.ofBitVec (z.extractLsb' (64 * s.val) 64)

/-- The column of a batch of blocks given as bitsets: cell `s` of block `t` is cell `s + 256 t`. -/
def columnOf (blocks : Vector (Form m) (2 ^ κ)) : Column (8 + κ) :=
  ⟨Vector.ofFn fun u ↦ packCell blocks[((cubeSplit 8 κ).symm u).2] ((cubeSplit 8 κ).symm u).1⟩

/-- The honest column of a batch of limb rows: block `t` is the honest block of row `t`, each
computed once. -/
def genColumn (rows : Vector (Fin 18 → K) (2 ^ κ)) : Column (8 + κ) :=
  columnOf (rows.map honestBlock)

private theorem blockCell_genColumn (rows : Vector (Fin 18 → K) (2 ^ κ)) (t : Fin (2 ^ κ))
    (s : Fin 256) : blockCell (genColumn rows) t s = packCell (honestBlock rows[t]) s := by
  have h : (cubeSplit 8 κ).symm (cubeIndex s t) = (s, t) := by
    rw [← cubeSplit_apply, Equiv.symm_apply_apply]
  simp only [blockCell, genColumn, columnOf, Fin.getElem_fin, Vector.getElem_ofFn, h,
    Vector.getElem_map]

private theorem blockBits_genColumn (rows : Vector (Fin 18 → K) (2 ^ κ)) (t : Fin (2 ^ κ)) :
    blockBits (genColumn rows) t =
      blake2sCircuit.traceF fun j ↦ (inputForm rows[t]).getLsbD j := by
  rw [← trace_getLsbD]
  funext j
  have hj : j.val < 16384 := j.isLt
  rw [blockBits, blockCell_genColumn, packCell, honestBlock]
  simp only [BF64.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 64),
    decide_true, Bool.true_and]
  congr 1
  omega

/-- Completeness on the region: the honest column satisfies the region predicate. -/
theorem holds_gen (rows : Vector (Fin 18 → K) (2 ^ κ)) :
    BlockR1CS.BatchHolds (blake2sCircuit.toBlockR1CS E) Flock.constPos
      (bitTable (genColumn rows)) := by
  intro t
  rw [batchBlock_bitTable, blockBits_genColumn]
  have hs := trace_satisfies (R := E) bounded_blake2s (fun j ↦ (inputForm rows[t]).getLsbD j)
  exact ⟨hs.1, by simpa [liftBlock, blake2sCircuit_cpos] using hs.2⟩

/-- The honest column carries every row that is a compression at its block's slots. -/
theorem slots_gen (rows : Vector (Fin 18 → K) (2 ^ κ)) (t : Fin (2 ^ κ))
    (hrel : LimbsCompress rows[t]) : slotLimbs slots (genColumn rows) t = rows[t] := by
  refine limbsCompress_unique (compress_of_holds _ (holds_gen rows) t) hrel fun j hj ↦ ?_
  apply BF64.toBitVec_injective
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hs : (slots j).val < 4 ∨ (10 ≤ (slots j).val ∧ (slots j).val < 20) := by
    revert hj; fin_cases j <;> decide
  have hpos : 64 * (slots j).val + i < 2 ^ m := by show _ < 16384; omega
  rw [slotLimbs, ← blockBits_pos (genColumn rows) t (slots j) hi, blockBits_genColumn,
    traceF_inputs _ (by rw [getLsbD_inputs, pos_val hpos]; exact decide_eq_true (by omega)),
    inputForm, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofFnLE]
  simp only [pos_val hpos, hpos, show 64 * (slots j).val + i < 1280 by omega, dite_true,
    decide_true, Bool.true_and, show (64 * (slots j).val + i) / 64 = (slots j).val by omega,
    show (64 * (slots j).val + i) % 64 = i by omega, inputCell_slots _ j hj]

end Completeness

/-- The BLAKE2s inhabitant of the Flock specification: the R1CS of `blake2sCircuit`, the deployed
slots, and the honest column of the circuit's traces. -/
def blake2sFlockSpec : FlockSpec where
  r1cs := blake2sCircuit.toBlockR1CS E
  slot := slots
  compress_of_holds := compress_of_holds
  gen := genColumn
  holds_gen := holds_gen
  slots_gen := slots_gen

end Blake2sFlock

end
end LeanVM.Protocol
