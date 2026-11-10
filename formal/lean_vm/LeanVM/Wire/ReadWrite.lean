/-
  LeanVM.Wire.ReadWrite

  The wire encoding's readers and writers are inverse: each reader (`readU32`, `readWords`, …,
  `LeanVM.Wire.Encoding`) reads back what its writer (`Prover.u32Bytes`, `K.toBytes`, …)
  wrote, and reads nothing else.
-/

module

public import LeanVM.Wire.Encoding
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Readers and writers of the wire encoding

Each reader of `Proof.fromBytes` reads back its writer's bytes and the rest untouched
(`readU32_u32Bytes`, `readWords_toBytes`, `readDigest_digestBytes`, `readRows_toBytes`, …), and,
conversely, what a reader accepts is its writer's bytes of what it returns
(`readU32_eq_some_iff`, `readWords_eq_some_iff`, …: the one encoding of each field). The stream
travels as its elements' limbs, regrouped in threes as `readProof` does (`streamOfWords`,
`readStream_toBytes`).

The base facts are about one 64-bit lane: `littleEndianLane` of a word's bytes is the word
(`littleEndianLane_wordBytes_append`), and the bytes of the lane of eight bytes are those bytes
(`wordBytes_littleEndianLane`).

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

public section

/-! ## One lane -/

/-- The bytes `b_k` from `8 i` on, as the number `∑ b_k 256^k` below `2 ^ (8 m)`. -/
private theorem sum_bytes_lt (f : ℕ → UInt8) :
    ∀ m, ∑ k ∈ Finset.range m, (f k).toNat * 2 ^ (8 * k) < 2 ^ (8 * m)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_bytes_lt f m
    have hf := (f m).toNat_lt
    calc _ < 2 ^ (8 * m) + (f m).toNat * 2 ^ (8 * m) := by omega
      _ = (1 + (f m).toNat) * 2 ^ (8 * m) := by ring
      _ ≤ 2 ^ 8 * 2 ^ (8 * m) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ (8 * (m + 1)) := by rw [← pow_add]; ring_nf

private theorem toNat_foldl_lane (bs : List UInt8) (i : ℕ) :
    ∀ m, m ≤ 8 → ((List.range m).foldl (fun acc k ↦ acc ||| ((bs.getD (8 * i + k) 0).toUInt64 <<<
      (8 * k).toUInt64)) 0).toNat =
        ∑ k ∈ Finset.range m, (bs.getD (8 * i + k) 0).toNat * 2 ^ (8 * k)
  | 0, _ => rfl
  | m + 1, hm => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
      UInt64.toNat_or, toNat_foldl_lane bs i m (by omega), UInt64.toNat_shiftLeft]
    have h8 : (8 * m).toUInt64.toNat % 64 = 8 * m := by simp; omega
    have hb := (bs.getD (8 * i + m) 0).toNat_lt
    have hlt : (bs.getD (8 * i + m) 0).toNat * 2 ^ (8 * m) < 2 ^ 64 :=
      calc _ < 2 ^ 8 * 2 ^ (8 * m) := Nat.mul_lt_mul_of_pos_right (by simpa using hb)
            (Nat.two_pow_pos _)
        _ = 2 ^ (8 * m + 8) := by rw [← pow_add]; ring_nf
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h8, UInt8.toNat_toUInt64, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt, Nat.lor_comm,
      ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt
        (sum_bytes_lt (fun k ↦ bs.getD (8 * i + k) 0) m), Nat.shiftLeft_eq, Nat.add_comm]

/-- **Lane `i` of bytes, as a number:** `∑ b_(8i+k) 256^k`, the bytes past the end zero. -/
theorem toNat_littleEndianLane (bs : List UInt8) (i : ℕ) :
    (littleEndianLane bs i).toNat =
      ∑ k ∈ Finset.range 8, (bs.getD (8 * i + k) 0).toNat * 2 ^ (8 * k) :=
  toNat_foldl_lane bs i 8 le_rfl

/-- Lane `i` of bytes is lane `0` of the bytes from `8 i`. -/
theorem littleEndianLane_eq_drop (bs : List UInt8) (i : ℕ) :
    littleEndianLane bs i = littleEndianLane (bs.drop (8 * i)) 0 := by
  apply UInt64.toNat_inj.mp
  simp only [toNat_littleEndianLane, List.getD_eq_getElem?_getD, List.getElem?_drop,
    Nat.mul_zero, Nat.zero_add]

/-- Lane `0` reads only the first eight bytes. -/
theorem littleEndianLane_take (bs : List UInt8) (n : ℕ) (hn : 8 ≤ n) :
    littleEndianLane (bs.take n) 0 = littleEndianLane bs 0 := by
  apply UInt64.toNat_inj.mp
  simp only [toNat_littleEndianLane]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk := Finset.mem_range.mp hk
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, Nat.mul_zero, Nat.zero_add,
    show k < n by omega, ite_true]

/-- **The lane of a word's bytes is the word.** -/
theorem littleEndianLane_wordBytes_append (w : UInt64) (rest : List UInt8) :
    littleEndianLane (wordBytes w ++ rest) 0 = w := by
  apply UInt64.toNat_inj.mp
  have hw := w.toNat_lt
  simp only [toNat_littleEndianLane, Finset.sum_range_succ, Finset.sum_range_zero, wordBytes,
    List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  norm_num
  omega

/-- **The bytes of the lane of eight bytes are those bytes.** -/
theorem wordBytes_littleEndianLane {bs : List UInt8} (h : 8 ≤ bs.length) :
    wordBytes (littleEndianLane bs 0) = bs.take 8 := by
  match bs, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ =>
    have hl := toNat_littleEndianLane (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) 0
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Nat.mul_zero,
      Nat.zero_add] at hl
    have h0 := b0.toNat_lt
    have h1 := b1.toNat_lt
    have h2 := b2.toNat_lt
    have h3 := b3.toNat_lt
    have h4 := b4.toNat_lt
    have h5 := b5.toNat_lt
    have h6 := b6.toNat_lt
    have h7 := b7.toNat_lt
    generalize littleEndianLane _ 0 = w at hl ⊢
    simp only [wordBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.take_succ_cons, List.take_zero, List.cons.injEq,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] <;>
      norm_num at hl h0 h1 h2 h3 h4 h5 h6 h7 ⊢ <;> omega

/-- The lanes of words' bytes are the words, whatever follows. -/
theorem lanes_flatMap_wordBytes (rest : List UInt8) :
    ∀ ws : List UInt64,
      (List.range ws.length).map (littleEndianLane (ws.flatMap wordBytes ++ rest)) = ws
  | [] => rfl
  | w :: ws => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.flatMap_cons, List.append_assoc, littleEndianLane_wordBytes_append]
    congr 1
    conv_rhs => rw [← lanes_flatMap_wordBytes rest ws]
    refine List.map_congr_left fun i _ ↦ ?_
    rw [Function.comp_apply, littleEndianLane_eq_drop, littleEndianLane_eq_drop _ i,
      show 8 * i.succ = 8 + 8 * i by rw [Nat.succ_eq_add_one]; ring, ← List.drop_drop,
      List.drop_left' (by simp [wordBytes])]

/-- Bytes of length `8 c` are the bytes of their `c` lanes. -/
theorem flatMap_wordBytes_lanes :
    ∀ (c : ℕ) {bs : List UInt8}, bs.length = 8 * c →
      ((List.range c).map (littleEndianLane bs)).flatMap wordBytes = bs
  | 0, bs, h => by simp_all
  | c + 1, bs, h => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatMap_cons,
      wordBytes_littleEndianLane (by omega)]
    have hmap : (List.range c).map (littleEndianLane bs ∘ Nat.succ) =
        (List.range c).map (littleEndianLane (bs.drop 8)) := by
      refine List.map_congr_left fun i _ ↦ ?_
      rw [Function.comp_apply, littleEndianLane_eq_drop, littleEndianLane_eq_drop _ i,
        List.drop_drop, Nat.add_comm, show 8 * i.succ = 8 * i + 8 by rw [Nat.succ_eq_add_one]; ring]
    rw [hmap, flatMap_wordBytes_lanes c (by simp; omega), List.take_append_drop]

/-! ## `readBytes` -/

/-- **What `readBytes` accepts:** its length's bytes, then the rest. -/
theorem readBytes_eq_some_iff {length : ℕ} {input head rest : List UInt8} :
    readBytes length input = some (head, rest) ↔ head.length = length ∧ input = head ++ rest := by
  unfold readBytes
  split
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨by simp; omega, (List.take_append_drop _ _).symm⟩
    · rintro ⟨rfl, rfl⟩
      simp
  · simp only [reduceCtorEq, false_iff, not_and]
    rintro rfl rfl
    simp_all

/-- `readBytes` reads back the bytes in front. -/
theorem readBytes_append (l rest : List UInt8) : readBytes l.length (l ++ rest) = some (l, rest) :=
  readBytes_eq_some_iff.mpr ⟨rfl, rfl⟩

/-! ## `readU32` -/

@[simp] theorem length_u32Bytes (n : ℕ) : (Prover.u32Bytes n).length = 4 := by
  simp [Prover.u32Bytes]

private theorem toNat_littleEndianLane_four (b0 b1 b2 b3 : UInt8) :
    (littleEndianLane [b0, b1, b2, b3] 0).toNat =
      b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 := by
  rw [toNat_littleEndianLane]
  simp [Finset.sum_range_succ, List.getD_eq_getElem?_getD]

/-- **What `readU32` accepts:** the four bytes of a number below `2 ^ 32`, then the rest. -/
theorem readU32_eq_some_iff {input rest : List UInt8} {n : ℕ} :
    readU32 input = some (n, rest) ↔ n < 2 ^ 32 ∧ input = Prover.u32Bytes n ++ rest := by
  unfold readU32
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨head, rest'⟩, hread, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hlen, rfl⟩ := readBytes_eq_some_iff.mp hread
    match head, hlen with
    | [b0, b1, b2, b3], _ =>
      rw [toNat_littleEndianLane_four]
      have h0 := b0.toNat_lt
      have h1 := b1.toNat_lt
      have h2 := b2.toNat_lt
      have h3 := b3.toNat_lt
      refine ⟨by omega, ?_⟩
      simp only [Prover.u32Bytes, List.range_succ, List.range_zero, List.nil_append,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq,
        and_true]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
        simp only [UInt8.toNat_ofNat'] <;> norm_num <;> omega
  · rintro ⟨hn, rfl⟩
    refine ⟨(Prover.u32Bytes n, rest), by rw [← length_u32Bytes n, readBytes_append], ?_⟩
    simp only [Prod.mk.injEq, and_true]
    simp only [Prover.u32Bytes, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.cons_append, toNat_littleEndianLane_four,
      UInt8.toNat_ofNat']
    norm_num
    omega

/-- `readU32` reads back a number below `2 ^ 32`. -/
theorem readU32_u32Bytes {n : ℕ} (hn : n < 2 ^ 32) (rest : List UInt8) :
    readU32 (Prover.u32Bytes n ++ rest) = some (n, rest) :=
  readU32_eq_some_iff.mpr ⟨hn, rfl⟩

/-! ## Lists of fields -/

/-- `count` fields in order, each read by `read`: the shape of `readU32s`, `readDigests` and
`readRows`. -/
def readList {α : Type} (read : List UInt8 → Option (α × List UInt8)) :
    ℕ → List UInt8 → Option (List α × List UInt8)
  | 0, input => some ([], input)
  | count + 1, input => do
    let (value, input) ← read input
    let (values, input) ← readList read count input
    some (value :: values, input)

/-- **What `readList` accepts**, from what its reader accepts: `count` fields' encodings in order,
then the rest. -/
theorem readList_eq_some_iff {α : Type} {read : List UInt8 → Option (α × List UInt8)}
    (encode : α → List UInt8) (valid : α → Prop)
    (hread : ∀ {input value rest}, read input = some (value, rest) ↔
      valid value ∧ input = encode value ++ rest) :
    ∀ {count : ℕ} {input : List UInt8} {values : List α} {rest : List UInt8},
      readList read count input = some (values, rest) ↔
        values.length = count ∧ (∀ v ∈ values, valid v) ∧ input = values.flatMap encode ++ rest
  | 0, input, values, rest => by
    simp only [readList, Option.some.injEq, Prod.mk.injEq, List.length_eq_zero_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      simp
    · rintro ⟨rfl, -, rfl⟩
      simp
  | count + 1, input, values, rest => by
    simp only [readList, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists]
    constructor
    · rintro ⟨value, input', hv, values', rest', hvs, heq⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨hvalid, rfl⟩ := hread.mp hv
      obtain ⟨hlen, hall, rfl⟩ := (readList_eq_some_iff encode valid hread).mp hvs
      refine ⟨by simp [hlen], ?_, by simp⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hvalid
      · exact hall v hv
    · rintro ⟨hlen, hall, rfl⟩
      match values, hlen with
      | value :: values', hlen =>
        refine ⟨value, values'.flatMap encode ++ rest,
          hread.mpr ⟨hall value List.mem_cons_self, by simp⟩, values', rest,
          (readList_eq_some_iff encode valid hread).mpr
            ⟨by simpa using hlen, fun v hv ↦ hall v (List.mem_cons_of_mem _ hv), rfl⟩, rfl⟩

theorem readU32s_eq_readList : readU32s = readList readU32 := by
  funext count input
  induction count generalizing input with
  | zero => rfl
  | succ count ih => simp only [readU32s, readList, ih]

/-- **What `readU32s` accepts:** `count` numbers below `2 ^ 32`, then the rest. -/
theorem readU32s_eq_some_iff {count : ℕ} {input rest : List UInt8} {values : List ℕ} :
    readU32s count input = some (values, rest) ↔ values.length = count ∧
      (∀ n ∈ values, n < 2 ^ 32) ∧ input = values.flatMap Prover.u32Bytes ++ rest := by
  rw [readU32s_eq_readList]
  exact readList_eq_some_iff Prover.u32Bytes (· < 2 ^ 32) readU32_eq_some_iff

/-- `readU32s` reads back numbers below `2 ^ 32`. -/
theorem readU32s_u32Bytes {ns : List ℕ} (hns : ∀ n ∈ ns, n < 2 ^ 32) (rest : List UInt8) :
    readU32s ns.length (ns.flatMap Prover.u32Bytes ++ rest) = some (ns, rest) :=
  readU32s_eq_some_iff.mpr ⟨rfl, hns, rfl⟩

/-! ## `readWords` -/

theorem flatMap_kToBytes (ws : List K) :
    ws.flatMap K.toBytes = (ws.map K.lane).flatMap wordBytes := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.map_cons, ih]; rfl

@[simp] theorem length_flatMap_wordBytes (ws : List UInt64) :
    (ws.flatMap wordBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons,
      wordBytes, List.length_map, List.length_range]; ring

/-- **What `readWords` accepts:** `count` words' bytes, then the rest. -/
theorem readWords_eq_some_iff {count : ℕ} {input rest : List UInt8} {ws : List K} :
    readWords count input = some (ws, rest) ↔
      ws.length = count ∧ input = ws.flatMap K.toBytes ++ rest := by
  unfold readWords
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨head, rest'⟩, hread, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hlen, rfl⟩ := readBytes_eq_some_iff.mp hread
    refine ⟨by simp, ?_⟩
    rw [flatMap_kToBytes, List.map_map]
    congr 1
    exact (flatMap_wordBytes_lanes count hlen).symm
  · rintro ⟨rfl, rfl⟩
    refine ⟨(ws.flatMap K.toBytes, rest), ?_, ?_⟩
    · rw [show 8 * ws.length = (ws.flatMap K.toBytes).length by
        rw [flatMap_kToBytes, length_flatMap_wordBytes, List.length_map], readBytes_append]
    · simp only [Prod.mk.injEq, and_true]
      have h := lanes_flatMap_wordBytes [] (ws.map K.lane)
      rw [List.append_nil, ← flatMap_kToBytes, List.length_map] at h
      calc _ = ((List.range ws.length).map
            (littleEndianLane (ws.flatMap K.toBytes))).map K.ofLane := by
            rw [List.map_map]; rfl
        _ = ws := by rw [h, List.map_map]; exact List.map_id' _ |>.trans rfl

/-- `readWords` reads back words. -/
theorem readWords_toBytes (ws : List K) (rest : List UInt8) :
    readWords ws.length (ws.flatMap K.toBytes ++ rest) = some (ws, rest) :=
  readWords_eq_some_iff.mpr ⟨rfl, rfl⟩

/-! ## Digests -/

theorem digestBytes_eq (d : Digest) : digestBytes d = d.toList.flatMap wordBytes := rfl

/-- **What `readDigest` accepts:** a digest's 32 bytes, then the rest. -/
theorem readDigest_eq_some_iff {input rest : List UInt8} {d : Digest} :
    readDigest input = some (d, rest) ↔ input = digestBytes d ++ rest := by
  unfold readDigest
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨⟨head, rest'⟩, hread, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hlen, rfl⟩ := readBytes_eq_some_iff.mp hread
    congr 1
    exact (flatMap_wordBytes_lanes 4 hlen).symm
  · rintro rfl
    refine ⟨(digestBytes d, rest), ?_, ?_⟩
    · rw [show 32 = (digestBytes d).length by
        rw [digestBytes_eq, length_flatMap_wordBytes, Vector.length_toList], readBytes_append]
    · simp only [Prod.mk.injEq, and_true]
      have h := lanes_flatMap_wordBytes [] d.toList
      rw [List.append_nil, ← digestBytes_eq, Vector.length_toList] at h
      apply Vector.toList_inj.mp
      rw [← h]
      rfl

/-- `readDigest` reads back a digest. -/
theorem readDigest_digestBytes (d : Digest) (rest : List UInt8) :
    readDigest (digestBytes d ++ rest) = some (d, rest) :=
  readDigest_eq_some_iff.mpr rfl

theorem readDigests_eq_readList : readDigests = readList readDigest := by
  funext count input
  induction count generalizing input with
  | zero => rfl
  | succ count ih => simp only [readDigests, readList, ih]

/-- **What `readDigests` accepts:** `count` digests' bytes, then the rest. -/
theorem readDigests_eq_some_iff {count : ℕ} {input rest : List UInt8} {ds : List Digest} :
    readDigests count input = some (ds, rest) ↔
      ds.length = count ∧ input = ds.flatMap digestBytes ++ rest := by
  rw [readDigests_eq_readList,
    readList_eq_some_iff digestBytes (fun _ ↦ True) (by simp [readDigest_eq_some_iff])]
  simp

/-- `readDigests` reads back digests. -/
theorem readDigests_digestBytes (ds : List Digest) (rest : List UInt8) :
    readDigests ds.length (ds.flatMap digestBytes ++ rest) = some (ds, rest) :=
  readDigests_eq_some_iff.mpr ⟨rfl, rfl⟩

/-! ## Rows -/

theorem readRows_eq_readList (rowWords : ℕ) :
    readRows rowWords = readList (readWords rowWords) := by
  funext count input
  induction count generalizing input with
  | zero => rfl
  | succ count ih => simp only [readRows, readList, ih]

/-- **What `readRows` accepts:** `count` rows of `rowWords` words, then the rest. -/
theorem readRows_eq_some_iff {rowWords count : ℕ} {input rest : List UInt8}
    {rows : List (List K)} :
    readRows rowWords count input = some (rows, rest) ↔ rows.length = count ∧
      (∀ row ∈ rows, row.length = rowWords) ∧
        input = rows.flatMap (·.flatMap K.toBytes) ++ rest := by
  rw [readRows_eq_readList]
  exact readList_eq_some_iff (fun row : List K ↦ row.flatMap K.toBytes)
    (fun row : List K ↦ row.length = rowWords) readWords_eq_some_iff

/-- `readRows` reads back rows of one width. -/
theorem readRows_toBytes {w : ℕ} {rows : List (List K)} (hrows : ∀ r ∈ rows, r.length = w)
    (rest : List UInt8) :
    readRows w rows.length (rows.flatMap (·.flatMap K.toBytes) ++ rest) = some (rows, rest) :=
  readRows_eq_some_iff.mpr ⟨rfl, hrows, rfl⟩

/-! ## The stream -/

/-- The stream `readProof` regroups from its words: element `i` is the words `3 i, 3 i + 1,
3 i + 2` as its limbs (`F192::new`). -/
def streamOfWords (length : ℕ) (words : List K) : List E :=
  (List.range length).map fun i ↦
    E.ofLimbs (words.getD (3 * i) 0) (words.getD (3 * i + 1) 0) (words.getD (3 * i + 2) 0)

/-- The words a stream travels as: each element's three limbs. -/
def streamWords (stream : List E) : List K :=
  stream.flatMap fun x ↦ [x.limb 0, x.limb 1, x.limb 2]

theorem flatMap_toBytes_streamWords (stream : List E) :
    (streamWords stream).flatMap K.toBytes = stream.flatMap E.toBytes := by
  induction stream with
  | nil => rfl
  | cons x stream ih =>
    simp only [streamWords, List.flatMap_cons] at ih ⊢
    rw [List.flatMap_append, ih]
    simp [E.toBytes]

@[simp] theorem length_streamWords (stream : List E) :
    (streamWords stream).length = 3 * stream.length := by
  induction stream with
  | nil => rfl
  | cons x stream ih =>
    simp only [streamWords, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]; simp; ring

private theorem ofLimbs_limbs (x : E) : E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) = x :=
  CompPoly.Extension.Ext.ext fun i ↦ by fin_cases i <;> rfl

/-- The first element of a regrouped stream is its first three words. -/
theorem streamOfWords_succ (length : ℕ) (a b c : K) (words : List K) :
    streamOfWords (length + 1) (a :: b :: c :: words) =
      E.ofLimbs a b c :: streamOfWords length words := by
  simp only [streamOfWords, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg₂ _ rfl (List.map_congr_left fun i _ ↦ ?_)
  simp only [Function.comp_apply, List.getD_eq_getElem?_getD, Nat.succ_eq_add_one,
    show 3 * (i + 1) = 3 * i + 3 by ring, List.getElem?_cons_succ]

/-- Regrouping a stream's words gives the stream. -/
theorem streamOfWords_streamWords :
    ∀ stream : List E, streamOfWords stream.length (streamWords stream) = stream
  | [] => rfl
  | x :: stream => by
    rw [streamWords, List.flatMap_cons, ← streamWords, List.length_cons, List.cons_append,
      List.cons_append, List.cons_append, List.nil_append, streamOfWords_succ,
      streamOfWords_streamWords stream, ofLimbs_limbs]

/-- The words of a stream regrouped from `3 * length` words are those words. -/
theorem streamWords_streamOfWords :
    ∀ (length : ℕ) {words : List K}, words.length = 3 * length →
      streamWords (streamOfWords length words) = words
  | 0, words, h => by simp_all [streamOfWords, streamWords]
  | length + 1, a :: b :: c :: words, h => by
    rw [streamOfWords_succ, streamWords, List.flatMap_cons, ← streamWords,
      streamWords_streamOfWords length (by simp at h; omega)]
    rfl
  | length + 1, [], h => by simp at h
  | length + 1, [_], h => by simp at h; omega
  | length + 1, [_, _], h => by simp at h; omega

@[simp] theorem length_streamOfWords (length : ℕ) (words : List K) :
    (streamOfWords length words).length = length := by
  simp [streamOfWords]

/-- **The stream reads back:** `readProof` reads its elements' words and regroups them into the
stream. -/
theorem readStream_toBytes (stream : List E) (rest : List UInt8) :
    readWords (3 * stream.length) (stream.flatMap E.toBytes ++ rest) =
        some (streamWords stream, rest) ∧
      streamOfWords stream.length (streamWords stream) = stream := by
  refine ⟨readWords_eq_some_iff.mpr ⟨by simp, by rw [flatMap_toBytes_streamWords]⟩,
    streamOfWords_streamWords stream⟩

/-- **What the stream's read accepts:** the bytes of the stream it regroups, then the rest. -/
theorem eq_of_readWords_stream {length : ℕ} {input rest : List UInt8} {words : List K}
    (h : readWords (3 * length) input = some (words, rest)) :
    input = (streamOfWords length words).flatMap E.toBytes ++ rest := by
  obtain ⟨hlen, rfl⟩ := readWords_eq_some_iff.mp h
  rw [← flatMap_toBytes_streamWords, streamWords_streamOfWords length hlen]

end

end LeanVM.Wire
