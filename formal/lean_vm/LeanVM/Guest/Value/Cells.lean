/-
  LeanVM.Guest.Value.Cells

  Cells as bytes: the 16 bytes of a canonical cell, a block of four cells as the message words of
  one compression, the metadata cell, the initial chaining value, and one `BLAKE2S` over cells as
  the compression of their bytes.
-/

module

public import LeanVM.Guest.Value.Tower
public import LeanVM.Spec.Isa
public import LeanVM.Protocol.Blake2sHash

/-!
# Cells as bytes

The guest hashes cells: one `BLAKE2S` instruction (`Spec/Isa.lean`, `CompressCells`) reads four
message cells, a chaining value of two cells and a metadata cell, and writes two output cells.
The specification hashes bytes (`Spec/Blake2s.lean`). The bridge is TRIAGE's convention: a
canonical cell `c0 + c1·y` is the 16 bytes `kBytes c0 ++ kBytes c1` (`cellBytes`), a block of
four cells is 64 bytes (`blockBytes`) whose little-endian words are the instruction's message
words (`messageWords_eq_blockWords`), and a digest is its two cells (`digestScalars`,
`digestBytes_eq`).

The metadata cell of a compile-time `counter=`, `final=` (`lean_compiler/src/lower/builtins.rs`,
lines 111-133) is `hash_flock::metadata(counter, f0, 0)` (`leanvm_core/src/hash_flock.rs:123`),
with `f0 = FINAL_FLAG = u32::MAX` (`flock/src/hash.rs:240`) on a final block: `metadataCell`. A runtime one is built by the disjoint-bit split, a runtime
`E(base)` plus a compile-time `metadata(64·j, f0, 0)` (`zkDSL.md` §BLAKE2s), which is
`metadataCell (base ^^^ 64·j)` (`eOfNat_add_metadataCell`). An omitted `cv=` is the parameterized
IV (`builtins.rs:271-284`, `hash_flock::IV_CELLS`), `ivCells`; so are the guest's `BLAKE2S_IV_0`,
`BLAKE2S_IV_1` (`ivCells_eq`).

`compressCells_iff` is one instruction as the compression of the block's bytes.
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Bytes of cells and blocks -/

/-- The 16 bytes of a canonical cell `c0 + c1·y`: its two limbs, little-endian. -/
def cellBytes (x : E) : List UInt8 := kBytes (x.limb 0) ++ kBytes (x.limb 1)

/-- The 64 bytes of a block of four cells. -/
def blockBytes (m : Fin 4 → E) : List UInt8 :=
  cellBytes (m 0) ++ cellBytes (m 1) ++ cellBytes (m 2) ++ cellBytes (m 3)

@[simp] theorem length_cellBytes (x : E) : (cellBytes x).length = 16 := rfl

@[simp] theorem length_blockBytes (m : Fin 4 → E) : (blockBytes m).length = 64 := rfl

/-- The bytes of the cells of a list. -/
theorem length_flatMap_cellBytes (cs : List E) : (cs.flatMap cellBytes).length = 16 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.flatMap_cons, List.length_append, ih, length_cellBytes,
      List.length_cons]; ring

/-- The zero cell is sixteen zero bytes. -/
theorem cellBytes_zero : cellBytes 0 = List.replicate 16 0 := by
  rw [cellBytes, ← ofK_zero, limb_ofK, limb_ofK]
  rfl

/-! ## Words of bytes -/

/-- Reading back the four little-endian bytes of a word. -/
theorem leWord_wordBytes (w : UInt32) :
    leWord w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8 = w := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [leWord, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32,
    UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    UInt32.toBitVec_ofNat, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.toNat_umod, BitVec.toNat_ofNat]
  interval_cases i <;> simp

/-- Entry `i` of a block's words is the little-endian word of bytes `4i .. 4i + 3`. -/
theorem blockWords_getElem (b : List UInt8) (i : ℕ) (hi : i < 16) :
    (blockWords b)[i] = leWord (b.getD (4 * i) 0) (b.getD (4 * i + 1) 0) (b.getD (4 * i + 2) 0)
      (b.getD (4 * i + 3) 0) := by
  interval_cases i <;> rfl

/-- Byte `4i + k` of the concatenated images of a function with four-element images. -/
theorem getD_flatMap_four {α β : Type} (f : α → List β) (hf : ∀ a, (f a).length = 4) (d : β) :
    ∀ (l : List α) (i k : ℕ) (hi : i < l.length), k < 4 →
      (l.flatMap f).getD (4 * i + k) d = (f (l[i]'hi)).getD k d
  | [], _, _, h, _ => absurd h (by simp)
  | a :: l, 0, k, _, hk => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hf]; omega)]
    simp [List.getD_eq_getElem?_getD]
  | a :: l, i + 1, k, hi, hk => by
    rw [List.flatMap_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hf]; omega), hf,
      show 4 * (i + 1) + k - 4 = 4 * i + k by omega, ← List.getD_eq_getElem?_getD,
      getD_flatMap_four f hf d l i k (by simpa using hi) hk]
    simp

/-- The words of the bytes of sixteen words are the words. -/
theorem blockWords_flatMap_wordBytes (v : Vector UInt32 16) :
    blockWords (v.toList.flatMap wordBytes) = v := by
  ext i hi
  rw [blockWords_getElem _ i hi]
  have hl : i < v.toList.length := by simpa using hi
  have g : ∀ k, k < 4 → (v.toList.flatMap wordBytes).getD (4 * i + k) 0 =
      (wordBytes (v.toList[i]'hl)).getD k 0 := fun k hk ↦
    getD_flatMap_four wordBytes (fun _ ↦ rfl) 0 v.toList i k hl hk
  rw [show 4 * i = 4 * i + 0 from rfl, g 0 (by decide), g 1 (by decide), g 2 (by decide),
    g 3 (by decide), Vector.getElem_toList]
  exact leWord_wordBytes v[i]

/-- Zero bytes past the end are what `blockWords` reads there anyway. -/
theorem blockWords_append_zeros (r : List UInt8) (k : ℕ) :
    blockWords (r ++ List.replicate k 0) = blockWords r := by
  have h : ∀ n, (r ++ List.replicate k 0).getD n 0 = r.getD n 0 := by
    intro n
    simp only [List.getD_eq_getElem?_getD]
    by_cases hn : n < r.length
    · rw [List.getElem?_append_left hn]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := r) (by omega),
        List.getElem?_replicate]
      split <;> rfl
  simp only [blockWords, h]

/-! ## Cells as words -/

/-- A cell's bytes are its four words' bytes. -/
theorem cellBytes_eq (x : E) : cellBytes x = (cellWords x).toList.flatMap wordBytes := by
  simp [cellBytes, kBytes, cellWords]

/-- The message words of four cells are the words of their 64 bytes. -/
theorem messageWords_eq_blockWords (m : Fin 4 → E) : messageWords m = blockWords (blockBytes m) := by
  rw [blockBytes, cellBytes_eq, cellBytes_eq, cellBytes_eq, cellBytes_eq, ← List.flatMap_append,
    ← List.flatMap_append, ← List.flatMap_append, ← Vector.toList_append, ← Vector.toList_append,
    ← Vector.toList_append, blockWords_flatMap_wordBytes]
  rfl

/-- The words of a digest's two cells are the digest. -/
theorem cellWords_digestScalars (d : Digest) :
    cellWords (digestScalars d).1 ++ cellWords (digestScalars d).2 = d := by
  have h := digestOfScalars_digestScalars d
  unfold digestOfScalars at h
  split at h
  · exact Option.some.inj h
  · exact absurd h (by simp)

theorem isCanonical128_digestScalars (d : Digest) :
    IsCanonical128 (digestScalars d).1 ∧ IsCanonical128 (digestScalars d).2 :=
  ⟨isCanonical128_wordsCell _, isCanonical128_wordsCell _⟩

/-- Two cells are a digest's cells exactly when they are canonical and their words are it. -/
theorem pair_eq_digestScalars_iff {o0 o1 : E} {d : Digest} :
    (o0, o1) = digestScalars d ↔
      IsCanonical128 o0 ∧ IsCanonical128 o1 ∧ cellWords o0 ++ cellWords o1 = d := by
  constructor
  · intro h
    have h0 : o0 = (digestScalars d).1 := congrArg Prod.fst h
    have h1 : o1 = (digestScalars d).2 := congrArg Prod.snd h
    subst h0 h1
    exact ⟨(isCanonical128_digestScalars d).1, (isCanonical128_digestScalars d).2,
      cellWords_digestScalars d⟩
  · rintro ⟨h0, h1, h⟩
    refine (digestScalars_digestOfScalars ?_).symm
    simp only [digestOfScalars, h0, h1, and_self, ↓reduceIte, h]

/-- The 32 bytes of a digest are its two cells' bytes. -/
theorem digestBytes_eq (d : Digest) :
    digestBytes d = cellBytes (digestScalars d).1 ++ cellBytes (digestScalars d).2 := by
  rw [cellBytes_eq, cellBytes_eq, ← List.flatMap_append, ← Vector.toList_append,
    cellWords_digestScalars]
  rfl

/-! ## The metadata cell -/

/-- The metadata cell of a block with byte counter `counter` and the final flag `final`
(`hash_flock::metadata(counter, final ? u32::MAX : 0, 0)`): the counter in limb 0, the flag
words in limb 1. -/
def metadataCell (counter : ℕ) (final : Bool) : E :=
  E.ofLimbs (K.ofBits counter) (K.ofBits (if final then 0xFFFFFFFF else 0)) 0

theorem isCanonical128_metadataCell (c : ℕ) (f : Bool) : IsCanonical128 (metadataCell c f) := rfl

/-- What `BLAKE2S` reads from a metadata cell: the counter modulo `2^64`, and the last-block
flag when `final`. -/
theorem unpackMetadata_metadataCell (c : ℕ) (f : Bool) :
    unpackMetadata (metadataCell c f) = (c.toUInt64, if f then lastBlock else 0, 0) := by
  have hc : (⟨(K.ofBits c).toBitVec⟩ : UInt64) = c.toUInt64 := rfl
  cases f
  · simp only [unpackMetadata, metadataCell, ofLimbs_limb0, ofLimbs_limb1, hc, Prod.mk.injEq]
    exact ⟨trivial, by decide, by decide⟩
  · simp only [unpackMetadata, metadataCell, ofLimbs_limb0, ofLimbs_limb1, hc, Prod.mk.injEq]
    exact ⟨trivial, by decide, by decide⟩

/-- **The disjoint-bit split** (`claims_window`, `claims_tail`, `claim_list_digest`,
`da_vector_cell`): a runtime `E(a)` plus a metadata cell is the metadata cell of `a ^^^ c`. -/
theorem eOfNat_add_metadataCell (a c : ℕ) (f : Bool) :
    eOfNat a + metadataCell c f = metadataCell (a ^^^ c) f := by
  rw [eOfNat_eq_ofLimbs, metadataCell, metadataCell, ofLimbs_add, ofBits_xor]
  simp

/-- `E(a)` is the non-final metadata cell of counter `a`. -/
theorem eOfNat_eq_metadataCell (a : ℕ) : eOfNat a = metadataCell a false := by
  rw [eOfNat_eq_ofLimbs, metadataCell]
  rfl

/-- The metadata cell as the `u128` literal the host substitutes (`MD_FINAL` is
`metadataCell 0 true`, `aggregation.rs:2839-2846`). -/
theorem metadataCell_eq_eOfNat192 {c : ℕ} (hc : c < 2 ^ 64) (f : Bool) :
    metadataCell c f = eOfNat192 (c + 2 ^ 64 * (if f then 0xFFFFFFFF else 0)) := by
  rw [metadataCell, eOfNat192, ofLimbs_inj]
  refine ⟨?_, ?_, ?_⟩
  · rw [← ofBits_mod (c + _), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hc, zero_add]
  · cases f
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hc (by decide))]
      rfl
    · simp only [↓reduceIte]
      rw [Nat.div_eq_of_lt (by omega)]
      rfl

/-! ## The initial chaining value -/

/-- The parameterized IV as the two cells a chaining value occupies (`hash_flock::IV_CELLS`,
`hash_flock.rs:153`): what an omitted `cv=` reads, and the guest's `BLAKE2S_IV_0`,
`BLAKE2S_IV_1`. -/
def ivCells : E × E := digestScalars paramIv

/-- The IV cells as the `u128` literals the host substitutes (`aggregation.rs:2831-2838`). -/
theorem ivCells_eq :
    ivCells = (eOfNat192 0xa54ff53a3c6ef372bb67ae856b08e647,
      eOfNat192 0x5be0cd191f83d9ab9b05688c510e527f) := by
  simp only [ivCells, digestScalars, wordsCell, eOfNat192, Prod.mk.injEq, ofLimbs_inj]
  decide

/-! ## One compression -/

/-- **One `BLAKE2S` over cells** (`Spec/Isa.lean`, `CompressCells`): under the chaining value of
the digest `h`, with canonical message and metadata cells, the output cells are the digest of
the compression of the block's 64 bytes. -/
theorem compressCells_iff {m : Fin 4 → E} {md out0 out1 : E} {h : Digest}
    (hm : ∀ i, IsCanonical128 (m i)) (hmd : IsCanonical128 md) :
    CompressCells m (digestScalars h).1 (digestScalars h).2 out0 out1 md ↔
      (out0, out1) = digestScalars (compress h (blockWords (blockBytes m))
        (unpackMetadata md).1 (unpackMetadata md).2.1 (unpackMetadata md).2.2) := by
  rw [pair_eq_digestScalars_iff, CompressCells, cellWords_digestScalars,
    messageWords_eq_blockWords]
  constructor
  · rintro ⟨_, _, _, h0, h1, _, he⟩
    exact ⟨h0, h1, he⟩
  · rintro ⟨h0, h1, he⟩
    exact ⟨hm, (isCanonical128_digestScalars h).1, (isCanonical128_digestScalars h).2, h0, h1,
      hmd, he⟩

/-- The forward direction of `compressCells_iff`, which needs no canonicity hypothesis: the
instruction checks it. -/
theorem compressCells_eq {m : Fin 4 → E} {md out0 out1 : E} {h : Digest}
    (hc : CompressCells m (digestScalars h).1 (digestScalars h).2 out0 out1 md) :
    (out0, out1) = digestScalars (compress h (blockWords (blockBytes m))
      (unpackMetadata md).1 (unpackMetadata md).2.1 (unpackMetadata md).2.2) :=
  (compressCells_iff hc.1 hc.2.2.2.2.2.1).mp hc

end
end LeanVM.Guest.Value
