module

public import LeanVM.Protocol.Extraction.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.IntervalCases
public import LeanVM.Protocol.WithHash

/-!
# The computed committed word is the statement's (proofs)

* **Byte encodings.** `bytesWord_wordBytes_append`: `bytesWord` reads back the word of
  `wordBytes w` whatever follows; `wordBytes_bytesWord`: on eight bytes it is a right inverse.
  Hence `bytesDigest` inverts `digestBytes` (`bytesDigest_digestBytes_append`,
  `digestBytes_bytesDigest`), `bytesWords` inverts `flatMap kBytes` (`bytesWords_flatMap_kBytes`,
  `flatMap_kBytes_bytesWords`), and `splitNode` inverts the concatenation of two digests.
  The proofs go through the base-256 digits of a natural number (`digits`).
* **The answer table.** With `KeysCover answers keys` (`answers x = some d → x ∈ keys`),
  `preimage (answerPairs answers keys) d len = some x` exactly when `x` is the unique byte string
  of length `len` answered by `d` (`preimage_eq_some_iff`); so it does not depend on the keys
  (`preimage_keys_congr`), and with `AnswersInj` the uniqueness is automatic.
* **Top-down = bottom-up.** `descend h d v` follows position `v`'s bits from the top
  (`subtreeLeaves_getD`: the computed leaves are its results). A climb splits at its last step
  (`climb_append`), so by induction on the height: an accepted opening's leaf is what `descend`
  finds (`descend_of_openOne`, with `AnswersInj` and the keys covering), and whatever `descend`
  finds is the leaf of an accepted opening (`openOne_of_descend`, the siblings as the path).
* **`committedWordC_eq`**: with `AnswersInj answers` and keys covering the support,
  `committedWordC answers keys root height width = committedWord answers root height width`.
  It replaces the classical choice.
* **`committedWordC_keys_congr`**: two covering key lists give the same word (no injectivity
  needed); the RPM bridge rewrites the answer function and then changes the keys.

`AnswersInj` is a verbatim copy of leanerVM `lean_vm/LeanVM/Protocol/Compile/Rom/Log.lean`
(`mumbai`, `935b9d40`).
-/

namespace LeanVM.Extraction.MerkleProofs

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Extraction

public section

/-! ## Base-256 digits -/

/-- The `L` little-endian base-256 digits of `N`. -/
@[expose] def digits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | L + 1, N => N % 256 :: digits L (N / 256)

/-- Reading `L` digits back gives `N mod 256^L`. -/
theorem foldr_digits (L N : ℕ) :
    (digits L N).foldr (fun x acc ↦ x + 256 * acc) 0 = N % 256 ^ L := by
  induction L generalizing N with
  | zero => simp [digits, Nat.mod_one]
  | succ L ih =>
    rw [digits, List.foldr_cons, ih, pow_succ', Nat.mod_mul]

/-- The digits of a number read from digits below `256` are those digits. -/
theorem digits_foldr (l : List ℕ) (hl : ∀ x ∈ l, x < 256) :
    digits l.length (l.foldr (fun x acc ↦ x + 256 * acc) 0) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx := hl x (by simp)
    rw [List.length_cons, digits, List.foldr_cons]
    congr 1
    · omega
    · rw [show (x + 256 * l.foldr (fun x acc ↦ x + 256 * acc) 0) / 256 =
          l.foldr (fun x acc ↦ x + 256 * acc) 0 by omega]
      exact ih fun y hy ↦ hl y (by simp [hy])

/-- A number read from `L` digits below `256` is below `256^L`. -/
theorem foldr_lt (l : List ℕ) (hl : ∀ x ∈ l, x < 256) :
    l.foldr (fun x acc ↦ x + 256 * acc) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hl x (by simp)
    have := ih fun y hy ↦ hl y (by simp [hy])
    rw [List.foldr_cons, List.length_cons, pow_succ]
    omega

/-- Byte `k` of a word is digit `k` of its value. -/
theorem toNat_wordByte (w : UInt64) {k : ℕ} (hk : k < 8) :
    ((w >>> (8 * k).toUInt64).toUInt8).toNat = w.toNat / 256 ^ k % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h8 : (8 * k).toUInt64.toNat % 64 = 8 * k := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [h8, pow_mul]
  norm_num

/-- The bytes of a word are its eight base-256 digits. -/
theorem map_toNat_wordBytes (w : UInt64) : (wordBytes w).map UInt8.toNat = digits 8 w.toNat := by
  simp only [wordBytes, List.map_map]
  apply List.ext_getElem (by simp [digits])
  intro k hk _
  simp only [List.length_map, List.length_range] at hk
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [toNat_wordByte w hk]
  interval_cases k <;> simp [digits, Nat.div_div_eq_div_mul]

theorem length_wordBytes (w : UInt64) : (wordBytes w).length = 8 := by simp [wordBytes]

/-- **`bytesWord` reads back a word**, whatever follows its bytes. -/
theorem bytesWord_wordBytes_append (w : UInt64) (rest : Bytes) :
    bytesWord (wordBytes w ++ rest) = w := by
  rw [bytesWord, List.take_left' (length_wordBytes w),
    ← List.foldr_map (f := UInt8.toNat) (g := fun x acc ↦ x + 256 * acc), map_toNat_wordBytes,
    foldr_digits, Nat.mod_eq_of_lt (by simpa using w.toNat_lt)]
  exact UInt64.ofNat_toNat

/-- **`wordBytes` reads back eight bytes.** -/
theorem wordBytes_bytesWord {b : Bytes} (hb : b.length = 8) : wordBytes (bytesWord b) = b := by
  have hlt : ∀ x ∈ b.map UInt8.toNat, x < 256 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.toNat_lt
  have hN := foldr_lt _ hlt
  rw [List.length_map, hb] at hN
  apply List.map_injective_iff.mpr (fun _ _ h ↦ UInt8.toNat.inj h)
  rw [map_toNat_wordBytes, bytesWord, List.take_of_length_le (by omega),
    ← List.foldr_map (f := UInt8.toNat) (g := fun x acc ↦ x + 256 * acc), UInt64.toNat_ofNat',
    Nat.mod_eq_of_lt (by norm_num at hN ⊢; omega)]
  have := digits_foldr _ hlt
  rwa [List.length_map, hb] at this

theorem bytesWord_take (b : Bytes) : bytesWord (b.take 8) = bytesWord b := by
  simp [bytesWord, List.take_take]

/-! ## Lanes, digests, words, nodes -/

theorem length_flatMap_wordBytes (ws : List UInt64) :
    (ws.flatMap wordBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => rw [List.flatMap_cons, List.length_append, ih, length_wordBytes]; simp; ring

theorem length_bytesLanes (L : ℕ) (b : Bytes) : (bytesLanes L b).length = L := by
  induction L generalizing b with
  | zero => rfl
  | succ L ih => simp [bytesLanes, ih]

/-- `bytesLanes` reads back the words of `flatMap wordBytes`. -/
theorem bytesLanes_flatMap_append (ws : List UInt64) (rest : Bytes) :
    bytesLanes ws.length (ws.flatMap wordBytes ++ rest) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.length_cons, bytesLanes, List.flatMap_cons, List.append_assoc,
      bytesWord_wordBytes_append, List.drop_left' (length_wordBytes w), ih]

/-- `flatMap wordBytes` reads back the first `8L` bytes. -/
theorem flatMap_bytesLanes (L : ℕ) (b : Bytes) (hb : 8 * L ≤ b.length) :
    (bytesLanes L b).flatMap wordBytes = b.take (8 * L) := by
  induction L generalizing b with
  | zero => simp [bytesLanes]
  | succ L ih =>
    rw [bytesLanes, List.flatMap_cons, ih _ (by simp; omega), ← bytesWord_take,
      wordBytes_bytesWord (by simp; omega), show 8 * (L + 1) = 8 + 8 * L by ring, List.take_add]

theorem length_digestBytes (d : Digest) : (digestBytes d).length = 32 := by
  rw [digestBytes, length_flatMap_wordBytes, Vector.length_toList]

theorem toList_bytesDigest (b : Bytes) : (bytesDigest b).toList = bytesLanes 4 b := by
  rw [bytesDigest, Vector.toList_ofFn]
  apply List.ext_getElem (by simp [length_bytesLanes])
  intro i h1 h2
  rw [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- **`bytesDigest` reads back a digest**, whatever follows its bytes. -/
theorem bytesDigest_digestBytes_append (d : Digest) (rest : Bytes) :
    bytesDigest (digestBytes d ++ rest) = d := by
  apply Vector.toList_inj.mp
  have key := bytesLanes_flatMap_append d.toList rest
  rw [Vector.length_toList] at key
  rw [toList_bytesDigest, digestBytes, key]

/-- **`digestBytes` reads back 32 bytes.** -/
theorem digestBytes_bytesDigest (b : Bytes) (hb : 32 ≤ b.length) :
    digestBytes (bytesDigest b) = b.take 32 := by
  rw [digestBytes, toList_bytesDigest, flatMap_bytesLanes 4 b (by omega)]

/-- `splitNode` inverts the concatenation of two digests. -/
theorem splitNode_append (c s : Digest) : splitNode (digestBytes c ++ digestBytes s) = (c, s) := by
  rw [splitNode, bytesDigest_digestBytes_append, List.drop_left' (length_digestBytes c),
    ← List.append_nil (digestBytes s), bytesDigest_digestBytes_append]

/-- A node's 64 bytes are its two children's. -/
theorem append_splitNode (x : Bytes) (hx : x.length = 64) :
    digestBytes (splitNode x).1 ++ digestBytes (splitNode x).2 = x := by
  rw [splitNode, digestBytes_bytesDigest _ (by omega), digestBytes_bytesDigest _ (by simp; omega),
    List.take_of_length_le (show (x.drop 32).length ≤ 32 by simp; omega), List.take_append_drop]

theorem flatMap_kBytes (leaf : List K) :
    leaf.flatMap K.toBytes = (leaf.map K.lane).flatMap wordBytes := by
  rw [List.flatMap_map]
  rfl

theorem length_flatMap_kBytes (leaf : List K) : (leaf.flatMap K.toBytes).length = 8 *
    leaf.length := by
  rw [flatMap_kBytes, length_flatMap_wordBytes, List.length_map]

theorem length_bytesWords (w : ℕ) (b : Bytes) : (bytesWords w b).length = w := by
  rw [bytesWords, List.length_map, length_bytesLanes]

/-- **`bytesWords` reads back a leaf.** -/
theorem bytesWords_flatMap_kBytes (leaf : List K) :
    bytesWords leaf.length (leaf.flatMap K.toBytes) = leaf := by
  rw [bytesWords, flatMap_kBytes, ← List.append_nil ((leaf.map K.lane).flatMap wordBytes),
    show leaf.length = (leaf.map K.lane).length by simp, bytesLanes_flatMap_append, List.map_map]
  exact List.map_id'' (fun _ ↦ rfl) leaf

/-- **`flatMap kBytes` reads back `8w` bytes.** -/
theorem flatMap_kBytes_bytesWords (w : ℕ) (b : Bytes) (hb : b.length = 8 * w) :
    (bytesWords w b).flatMap K.toBytes = b := by
  rw [flatMap_kBytes, bytesWords, List.map_map]
  rw [show (bytesLanes w b).map (K.lane ∘ K.ofLane) = bytesLanes w b from
    List.map_id'' (fun _ ↦ rfl) _]
  rw [flatMap_bytesLanes w b (by omega), List.take_of_length_le (by omega)]

/-! ## The answer table -/

/-- No two byte strings have the same answer (verbatim, leanerVM
`lean_vm/LeanVM/Protocol/Compile/Rom/Log.lean`). -/
@[expose] def AnswersInj (H : Bytes → Option Digest) : Prop :=
  ∀ x y v, H x = some v → H y = some v → x = y

/-- The keys cover the answers' support. -/
@[expose] def KeysCover (answers : Bytes → Option Digest) (keys : List Bytes) : Prop :=
  ∀ x d, answers x = some d → x ∈ keys

theorem mem_answerPairs {answers : Bytes → Option Digest} {keys : List Bytes} {x : Bytes}
    {d : Digest} : (x, d) ∈ answerPairs answers keys ↔ x ∈ keys ∧ answers x = some d := by
  simp only [answerPairs, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, d', hd', rfl, rfl⟩
    exact ⟨ha, hd'⟩
  · rintro ⟨ha, hd⟩
    exact ⟨x, ha, d, hd, rfl, rfl⟩

/-- **The preimage lookup**: with covering keys, `preimage` returns `x` exactly when `x` is the
unique byte string of length `len` answered by `d`. -/
theorem preimage_eq_some_iff {answers : Bytes → Option Digest} {keys : List Bytes}
    (hc : KeysCover answers keys) {d : Digest} {len : ℕ} {x : Bytes} :
    preimage (answerPairs answers keys) d len = some x ↔
      answers x = some d ∧ x.length = len ∧ ∀ y, answers y = some d → y.length = len → y = x := by
  have hpair : ∀ p ∈ answerPairs answers keys, answers p.1 = some p.2 := fun p hp ↦
    (mem_answerPairs.mp (show (p.1, p.2) ∈ _ from hp)).2
  have hin : ∀ y, answers y = some d → (y, d) ∈ answerPairs answers keys := fun y hy ↦
    mem_answerPairs.mpr ⟨hc y d hy, hy⟩
  have hhit : ∀ p : Bytes × Digest, (decide (p.2.toList = d.toList) && decide (p.1.length = len))
      = true ↔ p.2 = d ∧ p.1.length = len := by
    intro p
    simp [Vector.toList_inj]
  unfold preimage
  dsimp only
  split
  · rename_i hf
    simp only [reduceCtorEq, false_iff]
    rintro ⟨hx, hlen, -⟩
    exact (List.find?_eq_none.mp hf) (x, d) (hin x hx) ((hhit _).mpr ⟨rfl, hlen⟩)
  · rename_i p hf
    have hp := List.mem_of_find?_eq_some hf
    have hpt := List.find?_some hf
    obtain ⟨hpd, hplen⟩ := (hhit p).mp hpt
    have hpa : answers p.1 = some d := hpd ▸ hpair p hp
    split
    · rename_i hall
      rw [List.all_eq_true] at hall
      have huniq : ∀ y, answers y = some d → y.length = len → y = p.1 := by
        intro y hy hylen
        have := hall (y, d) (hin y hy)
        rw [(hhit (y, d)).mpr ⟨rfl, hylen⟩] at this
        simpa using this
      rw [Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨hpa, hplen, huniq⟩
      · rintro ⟨hx, hlen, -⟩
        exact (huniq x hx hlen).symm
    · rename_i hall
      simp only [reduceCtorEq, false_iff]
      rintro ⟨-, -, huniq⟩
      apply hall
      rw [List.all_eq_true]
      intro p' hp'
      by_cases h : (decide (p'.2.toList = d.toList) && decide (p'.1.length = len)) = true
      · obtain ⟨hp'd, hp'len⟩ := (hhit p').mp h
        have e1 := huniq p'.1 (hp'd ▸ hpair p' hp') hp'len
        have e2 := huniq p.1 hpa hplen
        simp [e1, e2]
      · simp only [Bool.not_eq_true] at h
        simp [h]

/-- **The lookup does not depend on the keys**, as long as they cover the support. -/
theorem preimage_keys_congr {answers : Bytes → Option Digest} {keys keys' : List Bytes}
    (hc : KeysCover answers keys) (hc' : KeysCover answers keys') :
    preimage (answerPairs answers keys) = preimage (answerPairs answers keys') := by
  funext d len
  apply Option.ext
  intro x
  rw [preimage_eq_some_iff hc, preimage_eq_some_iff hc']

/-- Without collisions, an answered byte string is the lookup's preimage. -/
theorem preimage_of_answer {answers : Bytes → Option Digest} {keys : List Bytes}
    (hinj : AnswersInj answers) (hc : KeysCover answers keys) {x : Bytes} {d : Digest}
    (hx : answers x = some d) : preimage (answerPairs answers keys) d x.length = some x :=
  (preimage_eq_some_iff hc).mpr ⟨hx, rfl, fun y hy _ ↦ hinj y x d hy hx⟩

/-! ## Climbing -/

/-- A climb's last step. -/
theorem climb_append (H : Bytes → Option Digest) (node : Digest) (q : ℕ) (ss : List Digest)
    (s : Digest) :
    climbWithHash H node q (ss ++ [s]) =
      (climbWithHash H node q ss).bind fun c ↦ climbWithHash H c (q / 2 ^ ss.length) [s] := by
  induction ss generalizing node q with
  | nil => simp [climbWithHash]
  | cons t ss ih =>
    simp only [List.cons_append, climbWithHash, List.length_cons, Option.bind_eq_bind] at ih ⊢
    split <;>
    · rw [Option.bind_assoc]
      congr 1
      funext parent
      rw [ih]
      congr 1
      funext c
      simp only [pow_succ', Nat.div_div_eq_div_mul]

theorem climb_single (H : Bytes → Option Digest) (c : Digest) (q : ℕ) (s : Digest) :
    climbWithHash H c q [s] =
      if q % 2 = 0 then H (digestBytes c ++ digestBytes s) else H (digestBytes s ++ digestBytes c) := by
  simp only [climbWithHash]
  split <;> cases H _ <;> rfl

theorem div_two_pow_mod_two (q h : ℕ) : q / 2 ^ h % 2 = 0 ↔ q.testBit h = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not]
  omega

/-- When an opening is accepted. -/
theorem openOne_eq_some_true (H : Bytes → Option Digest) (root : Digest) (h w q : ℕ)
    (o : Opening) : openOneWithHash H root h w q o = some true ↔
      o.leaf.length = w ∧ o.path.length = h ∧
        ∃ ld, H (o.leaf.flatMap K.toBytes) = some ld ∧ climbWithHash H ld q o.path = some root := by
  unfold openOneWithHash
  split
  · rename_i hlen
    rw [and_iff_right hlen.1, and_iff_right hlen.2]
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      decide_eq_true_eq, Vector.toList_inj]
    constructor
    · rintro ⟨ld, hld, top, htop, rfl⟩
      exact ⟨ld, hld, htop⟩
    · rintro ⟨ld, hld, hclimb⟩
      exact ⟨ld, hld, root, hclimb, rfl⟩
  · rename_i hlen
    simp only [Option.pure_def, Option.some.injEq, Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, -⟩
    exact hlen ⟨h1, h2⟩

/-! ## Top-down descent -/

/-- The descent to position `v` from `d` at height `h`, following `v`'s bits from bit `h − 1`. -/
@[expose] def descend (pairs : List (Bytes × Digest)) (w : ℕ) : ℕ → Digest → ℕ → Option (List K)
  | 0, d, _ => (preimage pairs d (8 * w)).map (bytesWords w)
  | h + 1, d, v => (preimage pairs d 64).bind fun x ↦
      descend pairs w h (if v.testBit h then (splitNode x).2 else (splitNode x).1) v

/-- The descent reads only the low `h` bits of the position. -/
theorem descend_congr_bits (pairs : List (Bytes × Digest)) (w : ℕ) {h : ℕ} (d : Digest)
    {v v' : ℕ} (hv : ∀ i < h, v.testBit i = v'.testBit i) :
    descend pairs w h d v = descend pairs w h d v' := by
  induction h generalizing d with
  | zero => rfl
  | succ h ih =>
    simp only [descend]
    rw [hv h (by omega)]
    congr 1
    funext x
    exact ih _ fun i hi ↦ hv i (by omega)

theorem size_subtreeLeaves (pairs : List (Bytes × Digest)) (w h : ℕ) (d : Digest) :
    (subtreeLeaves pairs w h d).size = 2 ^ h := by
  induction h generalizing d with
  | zero => rfl
  | succ h ih =>
    simp only [subtreeLeaves]
    split
    · rw [Array.size_append, ih, ih, pow_succ]; ring
    · simp

/-- **The computed leaves are the descents' results.** -/
theorem subtreeLeaves_getD (pairs : List (Bytes × Digest)) (w h : ℕ) (d : Digest) {v : ℕ}
    (hv : v < 2 ^ h) :
    (subtreeLeaves pairs w h d).getD v (List.replicate w 0) =
      (descend pairs w h d v).getD (List.replicate w 0) := by
  induction h generalizing d v with
  | zero =>
    obtain rfl : v = 0 := by simpa using hv
    simp only [subtreeLeaves, descend, leafOf]
    split <;> simp_all
  | succ h ih =>
    simp only [subtreeLeaves, descend]
    split
    · rename_i x hx
      rw [hx, Option.bind_some]
      by_cases hlo : v < 2 ^ h
      · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by rwa [size_subtreeLeaves]),
          ← Array.getD_eq_getD_getElem?, ih _ hlo, Nat.testBit_lt_two_pow hlo]
        rfl
      · have hr : v - 2 ^ h < 2 ^ h := by rw [pow_succ] at hv; omega
        have hv' : v = 2 ^ h + (v - 2 ^ h) := by omega
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by rw [size_subtreeLeaves]; omega),
          size_subtreeLeaves, ← Array.getD_eq_getD_getElem?, ih _ hr]
        have hbit : v.testBit h = true := by
          rw [hv', Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]; rfl
        rw [hbit, ite_eq_left rfl]
        congr 1
        refine descend_congr_bits pairs w _ fun i hi ↦ ?_
        conv_rhs => rw [hv']
        exact (Nat.testBit_two_pow_add_gt hi _).symm
    · rename_i hx
      rw [hx]
      simp [Array.getD_eq_getD_getElem?, hv]

/-! ## Top-down = bottom-up -/

/-- **An accepted opening's leaf is what the descent finds** (no collision, keys covering). -/
theorem descend_of_openOne {answers : Bytes → Option Digest} {keys : List Bytes}
    (hinj : AnswersInj answers) (hc : KeysCover answers keys) (w v : ℕ) {h : ℕ} {d : Digest}
    {o : Opening} (ho : openOneWithHash answers d h w v o = some true) :
    descend (answerPairs answers keys) w h d v = some o.leaf := by
  induction h generalizing d o with
  | zero =>
    obtain ⟨hw, hpath, ld, hld, hclimb⟩ := (openOne_eq_some_true ..).mp ho
    rw [List.length_eq_zero_iff.mp hpath] at hclimb
    obtain rfl : ld = d := by simpa [climbWithHash] using hclimb
    rw [descend, ← hw, show 8 * o.leaf.length = (o.leaf.flatMap K.toBytes).length by
      rw [length_flatMap_kBytes], preimage_of_answer hinj hc hld, Option.map_some,
      bytesWords_flatMap_kBytes]
  | succ h ih =>
    obtain ⟨hw, hpath, ld, hld, hclimb⟩ := (openOne_eq_some_true ..).mp ho
    have hne : o.path ≠ [] := by intro h'; rw [h'] at hpath; simp at hpath
    have hsplit := List.dropLast_append_getLast hne
    set ss := o.path.dropLast
    set s := o.path.getLast hne
    have hss : ss.length = h := by simp [ss, hpath]
    rw [← hsplit, climb_append, hss] at hclimb
    obtain ⟨c, hc1, hc2⟩ := Option.bind_eq_some_iff.mp hclimb
    have hsub : openOneWithHash answers c h w v ⟨o.leafIndex, o.leaf, ss⟩ = some true :=
      (openOne_eq_some_true ..).mpr ⟨hw, hss, ld, hld, hc1⟩
    have ihc := ih hsub
    rw [climb_single] at hc2
    simp only [descend]
    split at hc2
    · rename_i hbit
      rw [div_two_pow_mod_two] at hbit
      rw [show 64 = (digestBytes c ++ digestBytes s).length by simp [length_digestBytes],
        preimage_of_answer hinj hc hc2, Option.bind_some, splitNode_append, hbit]
      exact ihc
    · rename_i hbit
      rw [div_two_pow_mod_two, Bool.not_eq_false] at hbit
      rw [show 64 = (digestBytes s ++ digestBytes c).length by simp [length_digestBytes],
        preimage_of_answer hinj hc hc2, Option.bind_some, splitNode_append, hbit]
      exact ihc

/-- **What the descent finds is the leaf of an accepted opening** (keys covering). -/
theorem openOne_of_descend {answers : Bytes → Option Digest} {keys : List Bytes}
    (hc : KeysCover answers keys) (w v : ℕ) {h : ℕ} {d : Digest} {l : List K}
    (hl : descend (answerPairs answers keys) w h d v = some l) :
    ∃ o : Opening, openOneWithHash answers d h w v o = some true ∧ o.leaf = l := by
  induction h generalizing d l with
  | zero =>
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hl
    obtain ⟨hxa, hxlen, -⟩ := (preimage_eq_some_iff hc).mp hx
    refine ⟨⟨v, bytesWords w x, []⟩, (openOne_eq_some_true ..).mpr
      ⟨length_bytesWords w x, rfl, d, ?_, rfl⟩, rfl⟩
    rw [flatMap_kBytes_bytesWords w x hxlen]
    exact hxa
  | succ h ih =>
    obtain ⟨x, hx, hl⟩ := Option.bind_eq_some_iff.mp hl
    obtain ⟨hxa, hxlen, -⟩ := (preimage_eq_some_iff hc).mp hx
    obtain ⟨o, ho, rfl⟩ := ih hl
    obtain ⟨hw, hpath, ld, hld, hclimb⟩ := (openOne_eq_some_true ..).mp ho
    let sib := if v.testBit h then (splitNode x).1 else (splitNode x).2
    refine ⟨⟨o.leafIndex, o.leaf, o.path ++ [sib]⟩, (openOne_eq_some_true ..).mpr
      ⟨hw, by simp [hpath], ld, hld, ?_⟩, rfl⟩
    rw [climb_append, hclimb, Option.bind_some, climb_single, hpath]
    have hx64 := append_splitNode x hxlen
    by_cases hbit : v.testBit h
    · have : ¬ v / 2 ^ h % 2 = 0 := by rw [div_two_pow_mod_two, hbit]; simp
      simp only [this, ite_false, sib, hbit, ite_true]
      rw [hx64]
      exact hxa
    · have : v / 2 ^ h % 2 = 0 := by rw [div_two_pow_mod_two]; simpa using hbit
      simp only [this, ite_true, sib, hbit]
      simp only [Bool.false_eq_true, ite_false]
      rw [hx64]
      exact hxa

/-! ## The committed word -/

/-- **The computed committed word is the statement's**: without collisions among the
answers and with keys covering their support, `committedWordC = committedWord`. -/
theorem committedWordC_eq {answers : Bytes → Option Digest} {keys : List Bytes}
    (hinj : AnswersInj answers) (hc : KeysCover answers keys) (root : Digest)
    (height width : ℕ) :
    committedWordC answers keys root height width = committedWord answers root height width := by
  funext v
  have hmod : v % 2 ^ height < 2 ^ height := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hdesc : descend (answerPairs answers keys) width height root (v % 2 ^ height) =
      descend (answerPairs answers keys) width height root v :=
    descend_congr_bits _ _ _ fun i hi ↦ by rw [Nat.testBit_mod_two_pow]; simp [hi]
  simp only [committedWordC, committedLeaves, leafAt, committedWord]
  rw [subtreeLeaves_getD _ _ _ _ hmod, hdesc]
  split
  · rename_i h
    rw [descend_of_openOne hinj hc width v h.choose_spec]
    rfl
  · rename_i h
    cases hd : descend (answerPairs answers keys) width height root v with
    | none => rfl
    | some l =>
      obtain ⟨o, ho, -⟩ := openOne_of_descend hc width v hd
      exact absurd ⟨o, ho⟩ h

/-- The computed leaves depend on the pairs only through the lookup. -/
theorem subtreeLeaves_congr {pairs pairs' : List (Bytes × Digest)}
    (h : preimage pairs = preimage pairs') (w ht : ℕ) (d : Digest) :
    subtreeLeaves pairs w ht d = subtreeLeaves pairs' w ht d := by
  induction ht generalizing d with
  | zero => simp only [subtreeLeaves, leafOf, h]
  | succ ht ih => simp only [subtreeLeaves, h, ih]

end
end LeanVM.Extraction.MerkleProofs
