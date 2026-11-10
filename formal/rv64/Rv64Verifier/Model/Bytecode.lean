import Rv64Verifier.Model.Hash
import Rv64Verifier.Model.Multilinear
import Rv64Verifier.Model.FieldAlg

/-!
# The prepared bytecode as the Rust computes it

`crates/verifier/src/bytecode.rs`, mirrored as `Model.Multilinear` mirrors `multilinear.rs`: a
`u16` is a `BitVec 16`, `as u16` is `BitVec.ofNat 16`, `Bytecode` is `BytecodeRust`.

`fiatShamirIvRust` is `Bytecode::new`'s IV, Keccak-256 of `TAG` and the table's bytes
(`fiatShamirIvRust_eq`, `fiatShamirIvRust_words`: the statement's `fiatShamirIvWith`).

`evaluateRust` is `Bytecode::evaluate`. What it needs of the structure is `Prepared`: the blocks'
positions, each with its group's word, are a permutation of the table's nonzero entries; positions
lie in their block; each block lists the bucket of every nonzero byte of its words, and only buckets
in range. Neither distinct words nor duplicate-free buckets are needed: a bucket is taken when read,
so a repeat reads zero. From `Prepared`, `evaluateRust_eq`: one block from clean buckets
(`block_eval`, the bucket algebra `Σ_p w_p · word_p = Σ_k x^k · Σ_{p : bit k of word_p} w_p` with
`monomialSumRust_eq`), the blocks summed (`blocksFold_eq`), the low and high eq weights recombined
(`eqKernel_split`), and the multilinear extension as the eq-weighted sum (`multilinearEval_eq_sum`).

`newRust` is `Bytecode::new`. `group`'s probing `loop` takes at most as many probes as there are
slots (`probeRust`'s fuel): the table holds one slot per distinct word, at most `2^BLOCK_LOG` of the
`2^(BLOCK_LOG + 1)` slots, so a probe that ran out of fuel would have found every slot occupied
(`groupRust_spec`). `newRust_spec`: `new` returns, and its structure is `Prepared` (the counting
sort `place_spec`, the buckets `wordsUsed_spec`, block by block `blockNew_spec`).
`newRust_evaluate` puts them together: on the words of a table of `K`, `evaluate` returns the
statement's `computedBytecodeValue`.

An index the Rust would bounds-check is read with `getD`; on a prepared structure it is in range.
-/

namespace Rv64Verifier.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
  LeanVM.Protocol.Verifier BinaryField CompPoly.Extension

/-! ## The Fiat-Shamir IV -/

/-- `TAG`, `b"leanvm-v1"`. -/
def tagRust : List (BitVec 8) := [0x6c#8, 0x65#8, 0x61#8, 0x6e#8, 0x76#8, 0x6d#8, 0x2d#8, 0x76#8, 0x31#8]

theorem tagRust_eq : tagRust = byteBits versionTag := by decide +kernel

/-- `Bytecode::new`'s IV: `keccak_hash` of `TAG` then the table's words as little-endian bytes. -/
def fiatShamirIvRust (table : List (BitVec 64)) : List (BitVec 8) :=
  keccakHashRust (tagRust ++ table.flatMap toLeBytes)

theorem ivPreimage_eq (table : List K) :
    tagRust ++ (table.map BF64.toBitVec).flatMap toLeBytes =
      byteBits (versionTag ++ table.flatMap K.toBytes) := by
  rw [tagRust_eq, byteBits, byteBits, List.map_append, List.map_flatMap, List.flatMap_map]
  exact congrArg _ (List.flatMap_congr fun a _ ↦ (toLeBytes_toBitVec (K.lane a)))

/-- **The IV's bytes are the statement's IV's.** -/
theorem fiatShamirIvRust_eq (table : List K) :
    fiatShamirIvRust (table.map BF64.toBitVec) =
      byteBits (digestBytes (fiatShamirIvWith (m := Id) keccakF1600 table)) := by
  rw [fiatShamirIvRust, ivPreimage_eq, keccakHashRust_eq]
  rfl

/-- **The IV's words are the statement's IV.** -/
theorem fiatShamirIvRust_words (table : List K) :
    digestWordsRust (fiatShamirIvRust (table.map BF64.toBitVec)) =
      (fiatShamirIvWith (m := Id) keccakF1600 table).toList.map UInt64.toBitVec := by
  rw [fiatShamirIvRust_eq, digestWordsRust_digestBytes]

/-! ## The multilinear extension as a weighted sum -/

theorem eqKernel_foldl (rs : List E) : ∀ out : List E,
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

theorem eqKernel_append (low high : List E) :
    eqKernel (low ++ high) = (eqKernel high).flatMap fun w ↦ (eqKernel low).map (· * w) := by
  rw [eqKernel, List.foldl_append, ← eqKernel, eqKernel_foldl]

theorem getD_flatMap_mul (A : List E) (hA : 0 < A.length) : ∀ (W : List E) (i : ℕ),
    (W.flatMap fun w ↦ A.map (· * w)).getD i 0 = A.getD (i % A.length) 0 * W.getD (i / A.length) 0
  | [], i => by simp
  | w :: W, i => by
    rw [List.flatMap_cons]
    by_cases hi : i < A.length
    · rw [List.getD_append _ _ _ _ (by simpa using hi), Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
      simp [List.getD_eq_getElem?_getD]
      cases A[i]? <;> simp
    · have hL : A.length ≤ i := by omega
      rw [List.getD_append_right _ _ _ _ (by simpa using hL), List.length_map,
        getD_flatMap_mul A hA W]
      have h1 : i % A.length = (i - A.length) % A.length := Nat.mod_eq_sub_mod hL
      have h2 : i / A.length = (i - A.length) / A.length + 1 := Nat.div_eq_sub_div hA hL
      rw [h1, h2, List.getD_cons_succ]

theorem sum_range_two_mul (f : ℕ → E) : ∀ N : ℕ,
    ∑ i ∈ Finset.range (2 * N), f i = ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1))
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_two_mul f N, Finset.sum_range_succ]
    ring

/-- **`multilinear_eval` is the eq-weighted sum of the table.** -/
theorem multilinearEval_eq_sum : ∀ (point mle : List E), mle.length = 2 ^ point.length →
    multilinearEval mle point =
      ∑ i ∈ Finset.range (2 ^ point.length), (eqKernel point).getD i 0 * mle.getD i 0
  | [], mle, h => by
    match mle, h with
    | [a], _ => simp [multilinearEval, eqKernel]
  | r :: rs, mle, h => by
    have hF : (foldPairs r mle).length = 2 ^ rs.length := by
      rw [foldPairs_length, h, List.length_cons, pow_succ]
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
    have hp := foldPairs_getElem? r mle j
    rw [ite_eq_left (by rw [h, List.length_cons, pow_succ]; omega)] at hp
    rw [getD_flatMap_mul _ (by simp), getD_flatMap_mul _ (by simp),
      List.getD_eq_getElem?_getD (l := foldPairs r mle) (i := j), hp, Option.getD_some,
      show [1 + r, r].length = 2 from rfl]
    rw [show 2 * j % 2 = 0 by omega, show (2 * j + 1) % 2 = 1 by omega, show 2 * j / 2 = j by omega,
      show (2 * j + 1) / 2 = j by omega]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ring

/-! ## The structure and `evaluate` -/

/-- `Block`. -/
structure BlockRust where
  index : ℕ
  wordsEnd : ℕ
  bytesEnd : ℕ

/-- `Bytecode`, a `u16` as a `BitVec 16`. -/
structure BytecodeRust where
  len : ℕ
  fiatShamirIv : List (BitVec 8)
  blocks : List BlockRust
  words : List (BitVec 64 × ℕ)
  positions : List (BitVec 16)
  bytes : List (BitVec 16)

/-- `E::new`. -/
def eOfLimbs (l : Limbs) : E :=
  E.ofLimbs (BF64.ofBitVec l.1) (BF64.ofBitVec l.2.1) (BF64.ofBitVec l.2.2)

/-- `E::masked`. -/
def emasked (x : E) (mask : BitVec 64) : E :=
  eOfLimbs ((limbs x).1 &&& mask, (limbs x).2.1 &&& mask, (limbs x).2.2 &&& mask)

/-- `monomial_sum`: each limb of `sums[k]` widened and shifted by `k`, XORed, then reduced. -/
def monomialSumRust (sums : List E) : E :=
  let c := (List.range 64).foldl (fun (c : BitVec 128 × BitVec 128 × BitVec 128) k ↦
    let s := limbs (sums.getD k 0)
    (c.1 ^^^ s.1.setWidth 128 <<< k, c.2.1 ^^^ s.2.1.setWidth 128 <<< k,
      c.2.2 ^^^ s.2.2.setWidth 128 <<< k)) (0#128, 0#128, 0#128)
  eOfLimbs (reduce128 c.1, reduce128 c.2.1, reduce128 c.2.2)

/-- `E::sum` of the low weights at a word's positions. -/
def memberSumRust (lowW : List E) (members : List (BitVec 16)) : E :=
  members.foldl (fun acc p ↦ acc + lowW.getD p.toNat 0) 0

/-- The loop over `word.to_le_bytes().into_iter().enumerate()`: `sum` into each byte's bucket. -/
def addToBuckets (word : BitVec 64) (sum : E) (buckets : List E) : List E :=
  (List.range 8).foldl (fun buckets byte ↦
    let i := 256 * byte + ((toLeBytes word).getD byte 0).toNat
    buckets.set i (buckets.getD i 0 + sum)) buckets

/-- One `(word, positions_end)` of a block, from `positions_start`. -/
def wordStepRust (lowW : List E) (positions : List (BitVec 16)) (st : List E × ℕ)
    (entry : BitVec 64 × ℕ) : List E × ℕ :=
  (addToBuckets entry.1 (memberSumRust lowW ((positions.drop st.2).take (entry.2 - st.2))) st.1,
    entry.2)

/-- The loop over `bit_sums[8 * byte..8 * byte + 8]`: `sum` masked by each bit of `value`. -/
def creditBits (byte : ℕ) (value : BitVec 64) (sum : E) (bitSums : List E) : List E :=
  (List.range 8).foldl (fun bitSums bit ↦
    bitSums.set (8 * byte + bit) (bitSums.getD (8 * byte + bit) 0 +
      emasked sum (0#64 - (value >>> bit &&& 1#64)))) bitSums

/-- One bucket of a block: taken, then credited to each bit its byte value sets. -/
def bucketStepRust (st : List E × List E) (bucket : BitVec 16) : List E × List E :=
  (st.1.set bucket.toNat 0,
    creditBits (bucket.toNat / 256) (bucket.setWidth 64 % 256#64) (st.1.getD bucket.toNat 0) st.2)

/-- `evaluate`'s loop state. -/
structure EvalState where
  buckets : List E
  wordsStart : ℕ
  positionsStart : ℕ
  bytesStart : ℕ
  total : E

/-- One block of `evaluate`'s loop. -/
def blockStepRust (bc : BytecodeRust) (lowW highW : List E) (st : EvalState) (block : BlockRust) :
    EvalState :=
  let w := ((bc.words.drop st.wordsStart).take (block.wordsEnd - st.wordsStart)).foldl
    (wordStepRust lowW bc.positions) (st.buckets, st.positionsStart)
  let b := ((bc.bytes.drop st.bytesStart).take (block.bytesEnd - st.bytesStart)).foldl
    bucketStepRust (w.1, List.replicate 64 0)
  ⟨b.1, block.wordsEnd, w.2, block.bytesEnd,
    st.total + highW.getD block.index 0 * monomialSumRust b.2⟩

/-- `Bytecode::evaluate`; `none` is the `Err`. -/
def evaluateRust (bc : BytecodeRust) (point : List E) : Option E :=
  if point.length < 64 ∧ bc.len = 2 ^ point.length then
    let lowW := eqKernelRust (point.take (min point.length 14))
    let highW := eqKernelRust (point.drop (min point.length 14))
    some (bc.blocks.foldl (blockStepRust bc lowW highW) ⟨List.replicate 2048 0, 0, 0, 0, 0⟩).total
  else none

/-! ## What `evaluate` reads -/

/-- The words of a block with their positions, as `evaluate` slices them from `positions`. -/
def groupsFrom (positions : List (BitVec 16)) :
    List (BitVec 64 × ℕ) → ℕ → List (BitVec 64 × List (BitVec 16))
  | [], _ => []
  | e :: es, start => (e.1, (positions.drop start).take (e.2 - start)) :: groupsFrom positions es e.2

/-- Where the slicing of `groupsFrom` ends. -/
def positionsEnd : List (BitVec 64 × ℕ) → ℕ → ℕ
  | [], start => start
  | e :: es, _ => positionsEnd es e.2

/-- A block as `evaluate` reads it. -/
structure BlockView where
  index : ℕ
  groups : List (BitVec 64 × List (BitVec 16))
  buckets : List (BitVec 16)

/-- The blocks from the given starts. -/
def viewsFrom (bc : BytecodeRust) : List BlockRust → ℕ → ℕ → ℕ → List BlockView
  | [], _, _, _ => []
  | b :: bs, ws, ps, bys =>
    let entries := (bc.words.drop ws).take (b.wordsEnd - ws)
    ⟨b.index, groupsFrom bc.positions entries ps, (bc.bytes.drop bys).take (b.bytesEnd - bys)⟩ ::
      viewsFrom bc bs b.wordsEnd (positionsEnd entries ps) b.bytesEnd

/-- The blocks as `evaluate` reads them. -/
def BytecodeRust.views (bc : BytecodeRust) : List BlockView := viewsFrom bc bc.blocks 0 0 0

/-- The buckets of a word's nonzero bytes, `256 * byte + value`. -/
def wordBuckets (w : BitVec 64) : List ℕ :=
  ((List.range 8).filter fun b ↦ (toLeBytes w).getD b 0 ≠ 0).map fun b ↦
    256 * b + ((toLeBytes w).getD b 0).toNat

/-- The table entries a block stands for: each position's index and its group's word. -/
def BlockView.entries (v : BlockView) : List (ℕ × BitVec 64) :=
  v.groups.flatMap fun g ↦ g.2.map fun p ↦ (2 ^ 14 * v.index + p.toNat, g.1)

/-- The table's nonzero entries. -/
def nonzeroEntries (table : List (BitVec 64)) : List (ℕ × BitVec 64) :=
  ((List.range table.length).filter fun i ↦ table.getD i 0 ≠ 0).map fun i ↦ (i, table.getD i 0)

/-- **What `evaluate` needs of the prepared table**: the blocks' positions, each with its group's
word, are the table's nonzero entries, each once; a position lies in its block; a block lists the
bucket of every nonzero byte of its words, and only buckets in range. -/
structure Prepared (table : List (BitVec 64)) (bc : BytecodeRust) : Prop where
  len : bc.len = table.length
  entries : (bc.views.flatMap BlockView.entries).Perm (nonzeroEntries table)
  positions_lt : ∀ v ∈ bc.views, ∀ g ∈ v.groups, ∀ p ∈ g.2, p.toNat < 2 ^ 14
  buckets_mem : ∀ v ∈ bc.views, ∀ g ∈ v.groups, ∀ b ∈ wordBuckets g.1,
    b ∈ v.buckets.map BitVec.toNat
  buckets_lt : ∀ v ∈ bc.views, ∀ b ∈ v.buckets, b.toNat < 2048

/-! ## Limbs -/

theorem limbs_eOfLimbs (l : Limbs) : limbs (eOfLimbs l) = l := by
  rcases l with ⟨a, b, c⟩
  rfl

theorem eOfLimbs_limbs (x : E) : eOfLimbs (limbs x) = x := limbs_inj (limbs_eOfLimbs _)

theorem emasked_bit (x : E) (value : BitVec 64) (bit : ℕ) :
    emasked x (0#64 - (value >>> bit &&& 1#64)) = if value.getLsbD bit then x else 0 := by
  have hm : 0#64 - (value >>> bit &&& 1#64) =
      if value.getLsbD bit then BitVec.allOnes 64 else 0#64 := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (value >>> bit &&& 1#64).toNat = if value.getLsbD bit then 1 else 0 := by
      rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.and_one_is_mod]
      simp only [BitVec.getLsbD, Nat.testBit, Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero]
      split <;> simp_all
    rw [BitVec.toNat_sub, h1]
    split <;> simp
  rw [hm]
  split
  · rw [emasked]
    simp only [BitVec.and_allOnes]
    exact eOfLimbs_limbs x
  · apply limbs_inj
    rw [emasked, limbs_eOfLimbs, limbs_zero]
    simp [lzero]

theorem limbs_mul_ofK (z : E) (c : K) : limbs (z * ofK c) =
    ((BF64.ofBitVec (limbs z).1 * c).toBitVec, (BF64.ofBitVec (limbs z).2.1 * c).toBitVec,
      (BF64.ofBitVec (limbs z).2.2 * c).toBitVec) := by
  rw [← lmul_eq, limbs_ofK, ← BF64.toBitVec_zero]
  unfold limbs
  generalize Ext.coeffNat z 0 = z0, Ext.coeffNat z 1 = z1, Ext.coeffNat z 2 = z2
  simp only [lmul, emul, cl_xor_left, cl_xor_right, reduce_xor, reduce_cl]
  simp only [mul_zero, BF64.toBitVec_zero, BitVec.xor_zero, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> xor_cancel'
  all_goals rfl

theorem toPoly_one_shift {k : ℕ} (hk : k < 64) : toPoly (1#64 <<< k) = Polynomial.X ^ k := by
  rw [← toPoly_one_shiftLeft (w := 64) k hk]
  exact congrArg toPoly (BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_shiftLeft]))

theorem toBitVec_g_pow {k : ℕ} (hk : k < 64) : (g ^ k).toBitVec = 1#64 <<< k := by
  have h : g ^ k = BF64.ofBitVec (1#64 <<< k) := by
    apply BF64.toQuot_injective
    rw [BF64.toQuot_npow, BF64.toQuot, BF64.toQuot, BF64.toPolyBF64, BF64.toPolyBF64,
      BF64.toBitVec_ofBitVec, toPoly_one_shift hk,
      show toPoly g.toBitVec = Polynomial.X ^ 1 from toPoly_one_shiftLeft (w := 64) 1 (by norm_num),
      pow_one, map_pow]
  rw [h, BF64.toBitVec_ofBitVec]

theorem cl_shift (a : BitVec 64) {k : ℕ} (hk : k < 64) : cl a (1#64 <<< k) = a.setWidth 128 <<< k := by
  apply BF64.bitVec_toPoly_injective
  have hlt : (zeroExtendTo (w := 128) a).toNat < 2 ^ 64 := by
    rw [toNat_zeroExtendTo _ (by omega)]; exact a.isLt
  rw [cl, toPoly_carryLessMul _ _ (by norm_num), toPoly_one_shift hk,
    show a.setWidth 128 = zeroExtendTo (w := 128) a from rfl,
    toPoly_shiftLeft_no_overflow _ hlt (by omega), toPoly_zeroExtendTo _ (by norm_num)]

theorem limbs_mul_ex_pow (z : E) {k : ℕ} (hk : k < 64) : limbs (z * ex ^ k) =
    (reduce128 ((limbs z).1.setWidth 128 <<< k), reduce128 ((limbs z).2.1.setWidth 128 <<< k),
      reduce128 ((limbs z).2.2.setWidth 128 <<< k)) := by
  rw [show ex ^ k = ofK (g ^ k) from (map_pow (algebraMap K E) g k).symm, limbs_mul_ofK]
  simp only [BF64.toBitVec_mul, BF64.toBitVec_ofBitVec, toBitVec_g_pow hk, reduce128_eq]
  rw [← cl, cl_shift _ hk, ← cl, cl_shift _ hk, ← cl, cl_shift _ hk]

/-- **`monomial_sum` is `Σ_k sums[k] x^k`.** -/
theorem monomialSumRust_eq (sums : List E) :
    monomialSumRust sums = ∑ k ∈ Finset.range 64, sums.getD k 0 * ex ^ k := by
  suffices h : ∀ n ≤ 64,
      let c := (List.range n).foldl (fun (c : BitVec 128 × BitVec 128 × BitVec 128) k ↦
        let s := limbs (sums.getD k 0)
        (c.1 ^^^ s.1.setWidth 128 <<< k, c.2.1 ^^^ s.2.1.setWidth 128 <<< k,
          c.2.2 ^^^ s.2.2.setWidth 128 <<< k)) (0#128, 0#128, 0#128)
      (reduce128 c.1, reduce128 c.2.1, reduce128 c.2.2) =
        limbs (∑ k ∈ Finset.range n, sums.getD k 0 * ex ^ k) by
    apply limbs_inj
    rw [monomialSumRust, limbs_eOfLimbs]
    exact h 64 le_rfl
  intro n hn
  induction n with
  | zero =>
    have h0 : reduce128 0#128 = 0#64 := by decide +kernel
    simp only [List.range_zero, List.foldl_nil, Finset.sum_range_zero, limbs_zero, h0]
    rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ladd_eq, ← ih (by omega),
      limbs_mul_ex_pow _ (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, reduce128_eq, reduce_xor, ladd]

/-! ## One block -/

theorem getD_set_eq {α : Type} (l : List α) (i j : ℕ) (a d : α) :
    (l.set i a).getD j d = if i = j ∧ i < l.length then a else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < l.length
    · simp [hi]
    · simp [hi]
  · simp [hij]

theorem toLeBytes_lt (w : BitVec 64) (b : ℕ) : ((toLeBytes w).getD b 0).toNat < 256 :=
  ((toLeBytes w).getD b 0).isLt

theorem addToBuckets_spec (w : BitVec 64) (s : E) (B : List E) (hB : B.length = 2048) :
    (addToBuckets w s B).length = 2048 ∧ ∀ b < 2048, (addToBuckets w s B).getD b 0 =
      B.getD b 0 + if ((toLeBytes w).getD (b / 256) 0).toNat = b % 256 then s else 0 := by
  suffices h : ∀ n ≤ 8, ((List.range n).foldl (fun buckets byte ↦
      let i := 256 * byte + ((toLeBytes w).getD byte 0).toNat
      buckets.set i (buckets.getD i 0 + s)) B).length = 2048 ∧ ∀ b < 2048,
      ((List.range n).foldl (fun buckets byte ↦
        let i := 256 * byte + ((toLeBytes w).getD byte 0).toNat
        buckets.set i (buckets.getD i 0 + s)) B).getD b 0 =
        B.getD b 0 + if b / 256 < n ∧ ((toLeBytes w).getD (b / 256) 0).toNat = b % 256 then s
          else 0 by
    obtain ⟨h1, h2⟩ := h 8 le_rfl
    refine ⟨by rw [addToBuckets]; exact h1, fun b hb ↦ ?_⟩
    rw [addToBuckets, h2 b hb]
    simp [show b / 256 < 8 by omega]
  intro n hn
  induction n with
  | zero => simp [hB]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hv := toLeBytes_lt w n
    refine ⟨by rw [List.length_set, ih1], fun b hb ↦ ?_⟩
    rw [getD_set_eq, ih1]
    by_cases hi : 256 * n + ((toLeBytes w).getD n 0).toNat = b
    · subst hi
      rw [ite_eq_left ⟨rfl, by omega⟩, ih2 _ (by omega)]
      have h1 : (256 * n + ((toLeBytes w).getD n 0).toNat) / 256 = n := by omega
      have h2 : (256 * n + ((toLeBytes w).getD n 0).toNat) % 256 = ((toLeBytes w).getD n 0).toNat := by
        omega
      rw [h1, h2]
      simp
    · rw [ite_eq_right (fun h ↦ hi h.1), ih2 b hb]
      congr 1
      by_cases hb' : b / 256 = n
      · have : ¬ ((toLeBytes w).getD (b / 256) 0).toNat = b % 256 := by
          rw [hb']
          omega
        rw [ite_eq_right (fun h ↦ this h.2), ite_eq_right (fun h ↦ this h.2)]
      · have : b / 256 < n + 1 ↔ b / 256 < n := by omega
        simp only [this]

theorem groupsFold_spec (lowW : List E) : ∀ (G : List (BitVec 64 × List (BitVec 16))) (B : List E),
    B.length = 2048 →
    (G.foldl (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) B).length = 2048 ∧
    ∀ b < 2048, (G.foldl (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) B).getD b 0 =
      B.getD b 0 + (G.map fun g ↦ if ((toLeBytes g.1).getD (b / 256) 0).toNat = b % 256 then
        memberSumRust lowW g.2 else 0).sum
  | [], B, hB => by simp [hB]
  | g :: G, B, hB => by
    obtain ⟨h1, h2⟩ := addToBuckets_spec g.1 (memberSumRust lowW g.2) B hB
    obtain ⟨ih1, ih2⟩ := groupsFold_spec lowW G _ h1
    refine ⟨by rw [List.foldl_cons]; exact ih1, fun b hb ↦ ?_⟩
    rw [List.foldl_cons, ih2 b hb, h2 b hb, List.map_cons, List.sum_cons, add_assoc]

theorem value_getLsbD (c : BitVec 16) (bit : ℕ) :
    (c.setWidth 64 % 256#64).getLsbD bit = (c.toNat % 256).testBit bit := by
  have hc := c.isLt
  rw [BitVec.getLsbD, BitVec.toNat_umod, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (a := c.toNat) (b := 2 ^ 64) (by omega)]
  rfl

theorem creditBits_spec (sum : E) (c : BitVec 16) (S : List E)
    (hS : S.length = 64) :
    (creditBits (c.toNat / 256) (c.setWidth 64 % 256#64) sum S).length = 64 ∧
    ∀ k < 64, (creditBits (c.toNat / 256) (c.setWidth 64 % 256#64) sum S).getD k 0 =
      S.getD k 0 + if k / 8 = c.toNat / 256 ∧ (c.toNat % 256).testBit (k % 8) then sum else 0 := by
  suffices h : ∀ n ≤ 8, ((List.range n).foldl (fun bitSums bit ↦
      bitSums.set (8 * (c.toNat / 256) + bit) (bitSums.getD (8 * (c.toNat / 256) + bit) 0 +
        emasked sum (0#64 - ((c.setWidth 64 % 256#64) >>> bit &&& 1#64)))) S).length = 64 ∧
      ∀ k < 64, ((List.range n).foldl (fun bitSums bit ↦
        bitSums.set (8 * (c.toNat / 256) + bit) (bitSums.getD (8 * (c.toNat / 256) + bit) 0 +
          emasked sum (0#64 - ((c.setWidth 64 % 256#64) >>> bit &&& 1#64)))) S).getD k 0 =
        S.getD k 0 + if k / 8 = c.toNat / 256 ∧ k % 8 < n ∧ (c.toNat % 256).testBit (k % 8) then sum
          else 0 by
    obtain ⟨h1, h2⟩ := h 8 le_rfl
    refine ⟨by rw [creditBits]; exact h1, fun k hk ↦ ?_⟩
    rw [creditBits, h2 k hk]
    simp [show k % 8 < 8 by omega]
  intro n hn
  induction n with
  | zero => simp [hS]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [List.length_set, ih1], fun k hk ↦ ?_⟩
    rw [getD_set_eq, ih1]
    by_cases hi : 8 * (c.toNat / 256) + n = k
    · subst hi
      rw [ite_eq_left ⟨rfl, by omega⟩, ih2 _ (by omega), emasked_bit, value_getLsbD c n]
      have h1 : (8 * (c.toNat / 256) + n) / 8 = c.toNat / 256 := by omega
      have h2 : (8 * (c.toNat / 256) + n) % 8 = n := by omega
      rw [h1, h2]
      by_cases ht : (c.toNat % 256).testBit n <;> simp [ht]
    · rw [ite_eq_right (fun h ↦ hi h.1), ih2 k hk]
      congr 1
      by_cases hk' : k / 8 = c.toNat / 256
      · have : k % 8 < n + 1 ↔ k % 8 < n := by omega
        simp only [this]
      · simp [hk']

theorem sum_insert_update (R : Finset ℕ) (c : ℕ) (f : ℕ → E) :
    f c + ∑ b ∈ R, (if c = b then 0 else f b) = ∑ b ∈ insert c R, f b := by
  by_cases hc : c ∈ R
  · rw [Finset.insert_eq_of_mem hc, ← Finset.sum_erase_add _ _ hc, ← Finset.sum_erase_add _ _ hc,
      ite_eq_left rfl, add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [ite_eq_right (fun h ↦ Finset.ne_of_mem_erase hb h.symm)]
  · rw [Finset.sum_insert hc]
    congr 1
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [ite_eq_right (fun h ↦ hc (by rw [h]; exact hb))]

theorem bucketFold_spec : ∀ (L : List (BitVec 16)) (B S : List E), (∀ c ∈ L, c.toNat < 2048) →
    B.length = 2048 → S.length = 64 →
    (L.foldl bucketStepRust (B, S)).1.length = 2048 ∧
    (∀ b, (L.foldl bucketStepRust (B, S)).1.getD b 0 =
      if b ∈ L.map BitVec.toNat then 0 else B.getD b 0) ∧
    (L.foldl bucketStepRust (B, S)).2.length = 64 ∧
    ∀ k < 64, (L.foldl bucketStepRust (B, S)).2.getD k 0 = S.getD k 0 +
      ∑ b ∈ (L.map BitVec.toNat).toFinset,
        if k / 8 = b / 256 ∧ (b % 256).testBit (k % 8) then B.getD b 0 else 0
  | [], B, S, _, hB, hS => by simp [hB, hS]
  | c :: L, B, S, hL, hB, hS => by
    have hc := hL c (by simp)
    obtain ⟨h1, h2⟩ := creditBits_spec (B.getD c.toNat 0) c S hS
    have hB' : (B.set c.toNat 0).length = 2048 := by rw [List.length_set, hB]
    obtain ⟨i1, i2, i3, i4⟩ := bucketFold_spec L (B.set c.toNat 0) _
      (fun c' h ↦ hL c' (by simp [h])) hB' h1
    simp only [List.foldl_cons, bucketStepRust]
    refine ⟨i1, fun b ↦ ?_, i3, fun k hk ↦ ?_⟩
    · rw [i2 b, getD_set_eq, hB]
      by_cases hbL : b ∈ L.map BitVec.toNat
      · simp [hbL]
      · by_cases hbc : c.toNat = b
        · subst hbc
          simp [hc]
        · have : b ∉ (c :: L).map BitVec.toNat := by
            rw [List.map_cons, List.mem_cons]
            rintro (h | h)
            · exact hbc h.symm
            · exact hbL h
          rw [ite_eq_right hbL, ite_eq_right (fun h ↦ hbc h.1), ite_eq_right this]
    · rw [i4 k hk, h2 k hk, List.map_cons, List.toFinset_cons, add_assoc]
      congr 1
      rw [← sum_insert_update]
      congr 1
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [getD_set_eq, hB]
      by_cases hbc : c.toNat = b
      · subst hbc
        simp [hc]
      · simp [hbc]

/-- The buckets between blocks: `2048`, those of a nonzero byte value zero. -/
def Clean (B : List E) : Prop := B.length = 2048 ∧ ∀ b < 2048, b % 256 ≠ 0 → B.getD b 0 = 0

theorem getD_toLeBytes (w : BitVec 64) {j : ℕ} (hj : j < 8) :
    (toLeBytes w).getD j 0 = (w >>> (8 * j)).setWidth 8 := by
  simp [toLeBytes, hj]

theorem testBit_toLeBytes (w : BitVec 64) {j : ℕ} (hj : j < 8) (i : ℕ) (hi : i < 8) :
    ((toLeBytes w).getD j 0).toNat.testBit i = w.getLsbD (8 * j + i) := by
  rw [getD_toLeBytes w hj, BitVec.testBit_toNat, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  simp [hi, Nat.add_comm]

theorem mem_wordBuckets (w : BitVec 64) {j : ℕ} (hj : j < 8) (h : (toLeBytes w).getD j 0 ≠ 0) :
    256 * j + ((toLeBytes w).getD j 0).toNat ∈ wordBuckets w := by
  simp only [wordBuckets, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨j, ⟨hj, by simpa using h⟩, rfl⟩

theorem sum_comm_list {α : Type} (s : Finset ℕ) (l : List α) (f : ℕ → α → E) :
    ∑ k ∈ s, (l.map (f k)).sum = (l.map fun a ↦ ∑ k ∈ s, f k a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

/-- **One block of `evaluate`**: from clean buckets, the bit sums' `monomial_sum` is the block's
words, each times its positions' summed weights, and the buckets are clean again. -/
theorem block_eval (lowW : List E) (v : BlockView) (B : List E) (hB : Clean B)
    (hmem : ∀ g ∈ v.groups, ∀ b ∈ wordBuckets g.1, b ∈ v.buckets.map BitVec.toNat)
    (hlt : ∀ b ∈ v.buckets, b.toNat < 2048) :
    Clean (v.buckets.foldl bucketStepRust (v.groups.foldl
      (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) B, List.replicate 64 0)).1 ∧
    monomialSumRust (v.buckets.foldl bucketStepRust (v.groups.foldl
      (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) B, List.replicate 64 0)).2 =
      (v.groups.map fun g ↦ memberSumRust lowW g.2 * ofK (BF64.ofBitVec g.1)).sum := by
  obtain ⟨g1, g2⟩ := groupsFold_spec lowW v.groups B hB.1
  generalize v.groups.foldl (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) B = B1 at g1 g2 ⊢
  obtain ⟨r1, r2, -, r4⟩ := bucketFold_spec v.buckets B1 (List.replicate 64 0) hlt g1 (by simp)
  generalize v.buckets.foldl bucketStepRust (B1, List.replicate 64 0) = r at r1 r2 r4 ⊢
  have hT : ∀ b ∈ (v.buckets.map BitVec.toNat).toFinset, b < 2048 := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    exact hlt c hc
  have hbits : ∀ k < 64, r.2.getD k 0 = (v.groups.map fun g ↦
      if g.1.getLsbD k then memberSumRust lowW g.2 else 0).sum := by
    intro k hk
    have hz : (List.replicate 64 (0 : E)).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [r4 k hk, hz, zero_add]
    rw [Finset.sum_congr rfl (g := fun b ↦ (v.groups.map fun g ↦
      if (k / 8 = b / 256 ∧ (b % 256).testBit (k % 8)) ∧
        ((toLeBytes g.1).getD (b / 256) 0).toNat = b % 256 then memberSumRust lowW g.2 else 0).sum)
      (fun b hb ↦ ?_), sum_comm_list]
    · congr 1
      apply List.map_congr_left
      intro g hg
      set bs := 256 * (k / 8) + ((toLeBytes g.1).getD (k / 8) 0).toNat
      have hv := toLeBytes_lt g.1 (k / 8)
      have hbit : ((toLeBytes g.1).getD (k / 8) 0).toNat.testBit (k % 8) = g.1.getLsbD k := by
        rw [testBit_toLeBytes _ (by omega) _ (by omega)]
        congr 1
        omega
      rw [Finset.sum_congr rfl (g := fun b ↦ if bs = b then
        (if g.1.getLsbD k then memberSumRust lowW g.2 else 0) else 0) (fun b _ ↦ ?_),
        Finset.sum_ite_eq]
      · by_cases hk' : g.1.getLsbD k
        · have hne : (toLeBytes g.1).getD (k / 8) 0 ≠ 0 := by
            intro h0
            rw [← hbit, h0] at hk'
            simp at hk'
          rw [ite_eq_left (List.mem_toFinset.mpr (hmem g hg bs (mem_wordBuckets g.1 (by omega) hne)))]
        · simp [hk']
      · by_cases hb : bs = b
        · subst hb
          have h1 : bs / 256 = k / 8 := by omega
          have h2 : bs % 256 = ((toLeBytes g.1).getD (k / 8) 0).toNat := by omega
          rw [h1, h2, hbit]
          simp
        · rw [ite_eq_right hb, ite_eq_right]
          rintro ⟨⟨h1, -⟩, h2⟩
          apply hb
          rw [← h1] at h2
          omega
    · have hb' := hT b hb
      rw [g2 b hb']
      by_cases hc : k / 8 = b / 256 ∧ (b % 256).testBit (k % 8)
      · have h0 : b % 256 ≠ 0 := by
          intro h0
          rw [h0] at hc
          simp at hc
        rw [ite_eq_left hc, hB.2 b hb' h0, zero_add]
        congr 1
        apply List.map_congr_left
        intro g _
        by_cases he : ((toLeBytes g.1).getD (b / 256) 0).toNat = b % 256
        · rw [ite_eq_left he, ite_eq_left ⟨hc, he⟩]
        · rw [ite_eq_right he, ite_eq_right (fun h ↦ he h.2)]
      · rw [ite_eq_right hc]
        symm
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx
        rw [ite_eq_right (fun h ↦ hc h.1)]
  constructor
  · refine ⟨r1, fun b hb h0 ↦ ?_⟩
    rw [r2 b]
    split
    · rfl
    · rename_i hbL
      rw [g2 b hb, hB.2 b hb h0, zero_add]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      rw [ite_eq_right]
      intro he
      apply hbL
      have hne : (toLeBytes g.1).getD (b / 256) 0 ≠ 0 := by
        intro h'
        rw [h'] at he
        exact h0 (by simpa using he.symm)
      have := hmem g hg _ (mem_wordBuckets g.1 (by omega) hne)
      rwa [he, Nat.div_add_mod] at this
  · rw [monomialSumRust_eq, Finset.sum_congr rfl (fun k hk ↦ by
      rw [hbits k (Finset.mem_range.mp hk)])]
    simp only [← List.sum_map_mul_right]
    rw [sum_comm_list]
    congr 1
    apply List.map_congr_left
    intro g _
    rw [← ofK_sum_bits, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    split <;> simp

/-! ## The blocks -/

theorem wordFold_eq (lowW : List E) (positions : List (BitVec 16)) :
    ∀ (es : List (BitVec 64 × ℕ)) (B : List E) (ps : ℕ),
    es.foldl (wordStepRust lowW positions) (B, ps) =
      ((groupsFrom positions es ps).foldl (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) B,
        positionsEnd es ps)
  | [], _, _ => rfl
  | e :: es, B, ps => by
    rw [List.foldl_cons, groupsFrom, positionsEnd, List.foldl_cons]
    exact wordFold_eq lowW positions es _ _

/-- A block's words, each times its positions' summed low weights. -/
def blockValue (lowW : List E) (v : BlockView) : E :=
  (v.groups.map fun g ↦ memberSumRust lowW g.2 * ofK (BF64.ofBitVec g.1)).sum

/-- A block's buckets cover its words' nonzero bytes, and are in range. -/
def BucketsOk (v : BlockView) : Prop :=
  (∀ g ∈ v.groups, ∀ b ∈ wordBuckets g.1, b ∈ v.buckets.map BitVec.toNat) ∧
    ∀ b ∈ v.buckets, b.toNat < 2048

theorem blocksFold_eq (bc : BytecodeRust) (lowW highW : List E) :
    ∀ (bs : List BlockRust) (st : EvalState), Clean st.buckets →
    (∀ v ∈ viewsFrom bc bs st.wordsStart st.positionsStart st.bytesStart, BucketsOk v) →
    (bs.foldl (blockStepRust bc lowW highW) st).total = st.total +
      ((viewsFrom bc bs st.wordsStart st.positionsStart st.bytesStart).map fun v ↦
        highW.getD v.index 0 * blockValue lowW v).sum
  | [], st, _, _ => by simp [viewsFrom]
  | b :: bs, st, hc, hv => by
    set entries := (bc.words.drop st.wordsStart).take (b.wordsEnd - st.wordsStart)
    set v : BlockView := ⟨b.index, groupsFrom bc.positions entries st.positionsStart,
      (bc.bytes.drop st.bytesStart).take (b.bytesEnd - st.bytesStart)⟩ with hvdef
    have hviews : viewsFrom bc (b :: bs) st.wordsStart st.positionsStart st.bytesStart =
        v :: viewsFrom bc bs b.wordsEnd (positionsEnd entries st.positionsStart) b.bytesEnd := rfl
    rw [hviews] at hv ⊢
    have hv0 := hv v List.mem_cons_self
    obtain ⟨c1, c2⟩ := block_eval lowW v st.buckets hc hv0.1 hv0.2
    have hstep : blockStepRust bc lowW highW st b =
        ⟨(v.buckets.foldl bucketStepRust (v.groups.foldl
          (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) st.buckets,
            List.replicate 64 0)).1, b.wordsEnd, positionsEnd entries st.positionsStart, b.bytesEnd,
          st.total + highW.getD b.index 0 * monomialSumRust (v.buckets.foldl bucketStepRust
            (v.groups.foldl (fun B g ↦ addToBuckets g.1 (memberSumRust lowW g.2) B) st.buckets,
              List.replicate 64 0)).2⟩ := by
      simp only [blockStepRust, wordFold_eq]
      rfl
    rw [List.foldl_cons, blocksFold_eq bc lowW highW bs _ (by rw [hstep]; exact c1)
      (by rw [hstep]; exact fun v' hv' ↦ hv v' (List.mem_cons_of_mem _ hv')), hstep]
    simp only [c2, List.map_cons, List.sum_cons, blockValue]
    ring

/-! ## The sum -/

theorem foldl_add_eq_sum {α : Type} (f : α → E) : ∀ (l : List α) (a : E),
    l.foldl (fun acc x ↦ acc + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_eq_sum f l, List.map_cons, List.sum_cons, add_assoc]

theorem sum_flatMap {α β : Type} (F : β → E) (f : α → List β) : ∀ l : List α,
    ((l.flatMap f).map F).sum = (l.map fun a ↦ ((f a).map F).sum).sum
  | [] => by simp
  | a :: l => by rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap F f l]; simp

/-- The weight and value of a table entry. -/
def entryTerm (lowW highW : List E) (e : ℕ × BitVec 64) : E :=
  lowW.getD (e.1 % 2 ^ 14) 0 * highW.getD (e.1 / 2 ^ 14) 0 * ofK (BF64.ofBitVec e.2)

theorem blockValue_eq (lowW highW : List E) (v : BlockView)
    (hp : ∀ g ∈ v.groups, ∀ p ∈ g.2, p.toNat < 2 ^ 14) :
    highW.getD v.index 0 * blockValue lowW v = (v.entries.map (entryTerm lowW highW)).sum := by
  rw [blockValue, BlockView.entries, sum_flatMap, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro g hg
  rw [memberSumRust, foldl_add_eq_sum, zero_add, List.map_map, ← List.sum_map_mul_right,
    ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun p hp' ↦ ?_)
  have hlt := hp g hg p hp'
  simp only [Function.comp, entryTerm]
  rw [show (2 ^ 14 * v.index + p.toNat) % 2 ^ 14 = p.toNat by omega,
    show (2 ^ 14 * v.index + p.toNat) / 2 ^ 14 = v.index by omega]
  ring

theorem sum_filter_range (p : ℕ → Prop) [DecidablePred p] (f : ℕ → E) : ∀ n : ℕ,
    (((List.range n).filter fun i ↦ decide (p i)).map f).sum =
      ∑ i ∈ Finset.range n, if p i then f i else 0
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      sum_filter_range p f n, Finset.sum_range_succ]
    by_cases h : p n <;> simp [h]

theorem nonzeroEntries_sum (lowW highW : List E) (table : List (BitVec 64)) :
    ((nonzeroEntries table).map (entryTerm lowW highW)).sum =
      ∑ i ∈ Finset.range table.length, lowW.getD (i % 2 ^ 14) 0 * highW.getD (i / 2 ^ 14) 0 *
        ofK (BF64.ofBitVec (table.getD i 0)) := by
  rw [nonzeroEntries, List.map_map, sum_filter_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : table.getD i 0 = 0
  · rw [ite_eq_right (fun h' ↦ h' h), h]
    have : ofK (BF64.ofBitVec 0) = 0 := Ext.ofBase_zero
    rw [this, mul_zero]
  · rw [ite_eq_left h]
    rfl

theorem eqKernel_split (point : List E) {i : ℕ} (hi : i < 2 ^ point.length) :
    (eqKernel point).getD i 0 = (eqKernel (point.take (min point.length 14))).getD (i % 2 ^ 14) 0 *
      (eqKernel (point.drop (min point.length 14))).getD (i / 2 ^ 14) 0 := by
  have hm : (point.take (min point.length 14)).length = min point.length 14 := by simp
  conv_lhs => rw [← List.take_append_drop (min point.length 14) point]
  rw [eqKernel_append, getD_flatMap_mul _ (by rw [eqKernel_length]; positivity), eqKernel_length, hm]
  by_cases h : 14 ≤ point.length
  · rw [min_eq_right h]
  · have hlt : i < 2 ^ 14 := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [min_eq_left (by omega), Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hlt,
      Nat.div_eq_of_lt hlt]

/-- **`evaluate` on a prepared table is the table's multilinear extension**, where the size
check passes. -/
theorem evaluateRust_eq (table : List (BitVec 64)) (bc : BytecodeRust) (h : Prepared table bc)
    (point : List E) :
    evaluateRust bc point = if point.length < 64 ∧ table.length = 2 ^ point.length then
      some (multilinearEval (table.map fun w ↦ ofK (BF64.ofBitVec w)) point) else none := by
  rw [evaluateRust, h.len]
  split
  · rename_i hs
    refine congrArg some ?_
    simp only [eqKernelRust_eq]
    have hclean : Clean (List.replicate 2048 (0 : E)) := by
      refine ⟨List.length_replicate, fun b _ _ ↦ ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl
    rw [blocksFold_eq bc _ _ bc.blocks ⟨List.replicate 2048 0, 0, 0, 0, 0⟩ hclean
      (fun v hv ↦ ⟨h.buckets_mem v hv, h.buckets_lt v hv⟩),
      zero_add]
    rw [multilinearEval_eq_sum _ _ (by rw [List.length_map]; exact hs.2), ← hs.2]
    have hv : (bc.views.map fun v ↦ (eqKernel (point.drop (min point.length 14))).getD v.index 0 *
        blockValue (eqKernel (point.take (min point.length 14))) v).sum =
        ((bc.views.flatMap BlockView.entries).map (entryTerm (eqKernel (point.take
          (min point.length 14))) (eqKernel (point.drop (min point.length 14))))).sum := by
      rw [sum_flatMap]
      exact congrArg List.sum (List.map_congr_left fun v hv ↦
        blockValue_eq _ _ v (h.positions_lt v hv))
    have hperm := (h.entries.map (entryTerm (eqKernel (point.take (min point.length 14)))
      (eqKernel (point.drop (min point.length 14))))).sum_eq
    rw [show viewsFrom bc bc.blocks 0 0 0 = bc.views from rfl, hv, hperm, nonzeroEntries_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range, hs.2] at hi
    rw [eqKernel_split point hi]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases table[i]? <;> rfl
  · rfl

/-- **`Bytecode::evaluate` computes the statement's bytecode value**: on a table prepared from the
words of `table`, at a point of the table's size, it returns what `computedBytecodeValue` does. -/
theorem evaluateRust_computed (table : List K) (bc : BytecodeRust)
    (h : Prepared (table.map BF64.toBitVec) bc) (point : List E)
    (hp : point.length < 64 ∧ table.length = 2 ^ point.length) :
    ∃ v, evaluateRust bc point = some v ∧ computedBytecodeValue table point = pure v := by
  refine ⟨multilinearEval (table.map ofK) point, ?_, rfl⟩
  rw [evaluateRust_eq _ bc h, List.length_map, ite_eq_left hp, List.map_map]
  rfl

/-! ## `Bytecode::new` -/

/-- `byte_buckets`: the nonzero bytes of `word`, each as `256 * byte + value`. -/
def byteBucketsRust (word : BitVec 64) : List (BitVec 16) :=
  ((toLeBytes word).zipIdx.filter fun e ↦ e.1 != 0#8).map fun e ↦
    256#16 * BitVec.ofNat 16 e.2 + e.1.setWidth 16

/-- `slot_of`. -/
def slotOfRust (word : BitVec 64) : ℕ := ((word * 0x9E3779B97F4A7C15#64) >>> 49).toNat

/-- `group`'s `loop` for `word` from `slot`, at most `fuel` probes: the slots, the distinct words
and the word's group. `none` where the Rust would probe on, which never happens with `fuel` the
number of slots (`groupRust_spec`). -/
def probeRust (word : BitVec 64) (distinct : List (BitVec 64)) (slots : List (Option (BitVec 16))) :
    ℕ → ℕ → Option (List (Option (BitVec 16)) × List (BitVec 64) × BitVec 16)
  | 0, _ => none
  | fuel + 1, slot =>
    match slots.getD slot none with
    | none => some (slots.set slot (some (BitVec.ofNat 16 distinct.length)), distinct ++ [word],
        BitVec.ofNat 16 (distinct.length + 1) - 1#16)
    | some g => if distinct.getD g.toNat 0 = word then some (slots, distinct, g)
        else probeRust word distinct slots fuel ((slot + 1) % slots.length)

/-- One position of `group`: the slots, `group_of` and the distinct words. -/
def groupStepRust (block : List (BitVec 64))
    (st : Option (List (Option (BitVec 16)) × List (BitVec 16) × List (BitVec 64))) (position : ℕ) :
    Option (List (Option (BitVec 16)) × List (BitVec 16) × List (BitVec 64)) :=
  st.bind fun st ↦
    if block.getD position 0 = 0 then some st
    else (probeRust (block.getD position 0) st.2.2 st.1 st.1.length
      (slotOfRust (block.getD position 0))).map fun r ↦ (r.1, st.2.1.set position r.2.2, r.2.1)

/-- `group`, its buffers `slots` and `group_of` returned with the distinct words. -/
def groupRust (block : List (BitVec 64)) (slots : List (Option (BitVec 16))) (groupOf : List (BitVec 16)) :
    Option (List (Option (BitVec 16)) × List (BitVec 16) × List (BitVec 64)) :=
  (List.range block.length).foldl (groupStepRust block) (some (slots.map fun _ ↦ none, groupOf, []))

/-- One position of the count: `counts[group_of[position]] += 1` at a nonzero word. -/
def countStep (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (counts : List ℕ)
    (position : ℕ) : List ℕ :=
  if block.getD position 0 ≠ 0 then
    counts.set (groupOf.getD position 0).toNat (counts.getD (groupOf.getD position 0).toNat 0 + 1)
  else counts

/-- One `(word, count)`: `next.push(end)`, `end += count`, `words.push((word, end))`. -/
def runStep (st : List ℕ × ℕ × List (BitVec 64 × ℕ)) (wc : BitVec 64 × ℕ) :
    List ℕ × ℕ × List (BitVec 64 × ℕ) :=
  (st.1 ++ [st.2.1], st.2.1 + wc.2, st.2.2 ++ [(wc.1, st.2.1 + wc.2)])

/-- `Vec::resize(n, 0)`. -/
def resizeRust (l : List (BitVec 16)) (n : ℕ) : List (BitVec 16) :=
  l.take n ++ List.replicate (n - l.length) 0

/-- One position of the placement: `positions[next[g]] = position`, `next[g] += 1`. -/
def placeStep (block : List (BitVec 64)) (groupOf : List (BitVec 16))
    (st : List (BitVec 16) × List ℕ) (position : ℕ) : List (BitVec 16) × List ℕ :=
  if block.getD position 0 ≠ 0 then
    (st.1.set (st.2.getD (groupOf.getD position 0).toNat 0) (BitVec.ofNat 16 position),
      st.2.set (groupOf.getD position 0).toNat (st.2.getD (groupOf.getD position 0).toNat 0 + 1))
  else st

/-- One bucket of a word: pushed if not yet `used`. -/
def usedStep (st : List Bool × List (BitVec 16)) (bucket : BitVec 16) : List Bool × List (BitVec 16) :=
  if !st.1.getD bucket.toNat false then (st.1.set bucket.toNat true, st.2 ++ [bucket]) else st

/-- `Bytecode::new`'s buffers. -/
structure NewState where
  blocks : List BlockRust
  words : List (BitVec 64 × ℕ)
  positions : List (BitVec 16)
  bytes : List (BitVec 16)
  slots : List (Option (BitVec 16))
  groupOf : List (BitVec 16)

/-- One block of `Bytecode::new`'s loop over `table.chunks(1 << BLOCK_LOG).enumerate()`. -/
def blockNewRust (table : List (BitVec 64)) (st : NewState) (index : ℕ) : Option NewState :=
  let block := (table.drop (index * 2 ^ 14)).take (2 ^ 14)
  (groupRust block st.slots st.groupOf).map fun g ↦
    let slots := g.1
    let groupOf := g.2.1
    let distinct := g.2.2
    if distinct.isEmpty then { st with slots, groupOf } else
    let counts := (List.range block.length).foldl (countStep block groupOf)
      (List.replicate distinct.length 0)
    let runs := (distinct.zip counts).foldl runStep ([], st.positions.length, st.words)
    let placed := (List.range block.length).foldl (placeStep block groupOf)
      (resizeRust st.positions runs.2.1, runs.1)
    let used := distinct.foldl (fun u word ↦ (byteBucketsRust word).foldl usedStep u)
      (List.replicate 2048 false, st.bytes)
    ⟨st.blocks ++ [⟨index, runs.2.2.length, used.2.length⟩], runs.2.2, placed.1, used.2, slots,
      groupOf⟩

/-- `Bytecode::new`: `none` where the Rust would not return (never: `newRust_isSome`). -/
def newRust (table : List (BitVec 64)) : Option BytecodeRust :=
  ((List.range ((table.length + 2 ^ 14 - 1) / 2 ^ 14)).foldl
    (fun st index ↦ st.bind fun st ↦ blockNewRust table st index)
    (some ⟨[], [], [], [], List.replicate (2 ^ 15) none, List.replicate (2 ^ 14) 0⟩)).map fun st ↦
    ⟨table.length, fiatShamirIvRust table, st.blocks, st.words, st.positions, st.bytes⟩

/-! ### `group` -/

theorem probe_some (word : BitVec 64) (hw : word ≠ 0) (distinct : List (BitVec 64))
    (slots : List (Option (BitVec 16))) (hL : 0 < slots.length) :
    ∀ (fuel slot : ℕ) r, slot < slots.length → probeRust word distinct slots fuel slot = some r →
    (r.1 = slots ∧ r.2.1 = distinct ∧ r.2.2.toNat < distinct.length ∧
      distinct.getD r.2.2.toNat 0 = word) ∨
    (∃ t < slots.length, slots.getD t none = none ∧
      r.1 = slots.set t (some (BitVec.ofNat 16 distinct.length)) ∧ r.2.1 = distinct ++ [word] ∧
      r.2.2 = BitVec.ofNat 16 (distinct.length + 1) - 1#16)
  | 0, _, _, _, h => by simp [probeRust] at h
  | fuel + 1, slot, r, hs, h => by
    rw [probeRust] at h
    split at h
    · rename_i hn
      right
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨slot, hs, hn, rfl, rfl, rfl⟩
    · rename_i g hg
      split at h
      · rename_i he
        left
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨rfl, rfl, ?_, he⟩
        show g.toNat < distinct.length
        by_contra hlt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at he
        exact hw he.symm
      · exact probe_some word hw distinct slots hL fuel _ r (Nat.mod_lt _ hL) h

theorem probe_none (word : BitVec 64) (distinct : List (BitVec 64))
    (slots : List (Option (BitVec 16))) (hL : 0 < slots.length) :
    ∀ (fuel slot : ℕ), slot < slots.length → probeRust word distinct slots fuel slot = none →
    ∀ j < fuel, (slots.getD ((slot + j) % slots.length) none).isSome
  | 0, _, _, _ => by simp
  | fuel + 1, slot, hs, h => by
    rw [probeRust] at h
    split at h
    · simp at h
    · rename_i g hg
      split at h
      · simp at h
      · intro j hj
        rcases j with _ | j
        · rw [Nat.add_zero, Nat.mod_eq_of_lt hs, hg]
          rfl
        · have := probe_none word distinct slots hL fuel _ (Nat.mod_lt _ hL) h j (by omega)
          rwa [Nat.mod_add_mod, show slot + 1 + j = slot + (j + 1) by omega] at this

/-- The occupied slots. -/
def occupied (slots : List (Option (BitVec 16))) : ℕ := slots.countP fun o ↦ o.isSome

/-- `group` after the positions `< q`: every slot table entry stands for a distinct word, and each
nonzero position's group holds its word. -/
structure GroupInv (block : List (BitVec 64)) (n0 q : ℕ)
    (st : List (Option (BitVec 16)) × List (BitVec 16) × List (BitVec 64)) : Prop where
  slots_len : st.1.length = 2 ^ 15
  occupied_eq : occupied st.1 = st.2.2.length
  groupOf_len : st.2.1.length = n0
  distinct_le : st.2.2.length ≤ q
  group : ∀ p < q, block.getD p 0 ≠ 0 →
    (st.2.1.getD p 0).toNat < st.2.2.length ∧ st.2.2.getD (st.2.1.getD p 0).toNat 0 = block.getD p 0

theorem slotOfRust_lt (word : BitVec 64) : slotOfRust word < 2 ^ 15 := by
  rw [slotOfRust, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := (word * 0x9E3779B97F4A7C15#64).isLt
  omega

theorem toNat_newGroup {n : ℕ} (hn : n < 2 ^ 14) :
    (BitVec.ofNat 16 (n + 1) - 1#16).toNat = n := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem all_occupied (slots : List (Option (BitVec 16))) (s : ℕ) (hs : s < slots.length)
    (h : ∀ j < slots.length, (slots.getD ((s + j) % slots.length) none).isSome) :
    occupied slots = slots.length := by
  rw [occupied, List.countP_eq_length]
  intro a ha
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  have hj := h ((t + (slots.length - s)) % slots.length) (Nat.mod_lt _ (by omega))
  rw [Nat.add_mod_mod, show s + (t + (slots.length - s)) = t + slots.length by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt ht, List.getD_eq_getElem _ _ ht] at hj
  exact hj

theorem groupRust_spec (block : List (BitVec 64)) (hb : block.length ≤ 2 ^ 14)
    (slots : List (Option (BitVec 16))) (hs : slots.length = 2 ^ 15) (groupOf : List (BitVec 16))
    (hg : block.length ≤ groupOf.length) :
    ∃ st, groupRust block slots groupOf = some st ∧
      GroupInv block groupOf.length block.length st := by
  suffices h : ∀ q ≤ block.length, ∃ st, (List.range q).foldl (groupStepRust block)
      (some (slots.map fun _ ↦ none, groupOf, [])) = some st ∧ GroupInv block groupOf.length q st from
    h _ le_rfl
  intro q hq
  induction q with
  | zero =>
    refine ⟨_, rfl, ⟨by rw [List.length_map, hs], ?_, rfl, Nat.zero_le _,
      fun p hp ↦ absurd hp (Nat.not_lt_zero _)⟩⟩
    rw [occupied, List.countP_eq_zero.mpr (fun a ha ↦ ?_)]
    · rfl
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
      simp
  | succ q ih =>
    obtain ⟨st, hst, hinv⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, hst, List.foldl_cons, List.foldl_nil, groupStepRust,
      Option.bind_some]
    by_cases hz : block.getD q 0 = 0
    · rw [ite_eq_left hz]
      refine ⟨st, rfl, ⟨hinv.slots_len, hinv.occupied_eq, hinv.groupOf_len, by
        have := hinv.distinct_le; omega, fun p hp hp0 ↦ ?_⟩⟩
      rcases (show p < q ∨ p = q by omega) with hp' | rfl
      · exact hinv.group p hp' hp0
      · exact absurd hz hp0
    · rw [ite_eq_right hz]
      have hL : 0 < st.1.length := by rw [hinv.slots_len]; norm_num
      have hslot : slotOfRust (block.getD q 0) < st.1.length := by
        rw [hinv.slots_len]; exact slotOfRust_lt _
      have hqg : q < st.2.1.length := by rw [hinv.groupOf_len]; omega
      cases hpr : probeRust (block.getD q 0) st.2.2 st.1 st.1.length (slotOfRust (block.getD q 0)) with
      | none =>
        exfalso
        have hall := all_occupied st.1 _ hslot
          (probe_none _ _ _ hL _ _ hslot hpr)
        rw [hinv.occupied_eq, hinv.slots_len] at hall
        have := hinv.distinct_le
        omega
      | some r =>
        refine ⟨_, rfl, ?_⟩
        show GroupInv block groupOf.length (q + 1) (r.1, st.2.1.set q r.2.2, r.2.1)
        rcases probe_some _ hz _ _ hL _ _ r hslot hpr with
          ⟨h1, h2, h3, h4⟩ | ⟨t, ht, htn, h1, h2, h3⟩
        · refine ⟨by rw [h1]; exact hinv.slots_len, by rw [h1, h2]; exact hinv.occupied_eq,
            by rw [List.length_set]; exact hinv.groupOf_len, by
              rw [h2]; dsimp only; have := hinv.distinct_le; omega, fun p hp hp0 ↦ ?_⟩
          rw [h2, getD_set_eq]
          rcases (show p < q ∨ p = q by omega) with hp' | rfl
          · rw [ite_eq_right (fun h ↦ by omega)]
            exact hinv.group p hp' hp0
          · rw [ite_eq_left ⟨rfl, hqg⟩]
            exact ⟨h3, h4⟩
        · have hd := hinv.distinct_le
          have hdl : st.2.2.length < 2 ^ 14 := by omega
          refine ⟨by rw [h1, List.length_set]; exact hinv.slots_len, ?_,
            by rw [List.length_set]; exact hinv.groupOf_len, by rw [h2]; simp; omega,
            fun p hp hp0 ↦ ?_⟩
          · have htn' : st.1[t] = none := by rwa [List.getD_eq_getElem _ _ ht] at htn
            rw [h1, h2, occupied, List.countP_set ht, htn', ← occupied, hinv.occupied_eq]
            simp
          · rw [h2, getD_set_eq]
            rcases (show p < q ∨ p = q by omega) with hp' | rfl
            · rw [ite_eq_right (fun h ↦ by omega)]
              obtain ⟨g1, g2⟩ := hinv.group p hp' hp0
              refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_⟩
              rw [List.getD_append _ _ _ _ g1, g2]
            · rw [ite_eq_left ⟨rfl, hqg⟩, h3, toNat_newGroup hdl]
              simp

/-! ### The counting sort -/

/-- The nonzero positions `< q` of group `g`. -/
def members (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (g q : ℕ) : List ℕ :=
  (List.range q).filter fun p ↦ block.getD p 0 ≠ 0 ∧ (groupOf.getD p 0).toNat = g

theorem members_succ (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (g q : ℕ) :
    members block groupOf g (q + 1) = members block groupOf g q ++
      if block.getD q 0 ≠ 0 ∧ (groupOf.getD q 0).toNat = g then [q] else [] := by
  rw [members, List.range_succ, List.filter_append, List.filter_singleton, Bool.cond_decide]
  rfl

theorem ext_getD {α : Type} (d : α) {l1 l2 : List α} (h : l1.length = l2.length)
    (h' : ∀ i < l1.length, l1.getD i d = l2.getD i d) : l1 = l2 := by
  apply List.ext_getElem h
  intro i h1 h2
  have := h' i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) {m g : ℕ} (hg : g < m) :
    ((List.range m).map f).getD g d = f g := by
  rw [List.getD_eq_getElem _ _ (by simpa using hg)]
  simp

theorem counts_eq (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (m : ℕ)
    (hgi : ∀ p < block.length, block.getD p 0 ≠ 0 → (groupOf.getD p 0).toNat < m) :
    ∀ q ≤ block.length, (List.range q).foldl (countStep block groupOf) (List.replicate m 0) =
      (List.range m).map fun g ↦ (members block groupOf g q).length
  | 0, _ => by
    apply ext_getD 0 (by simp)
    intro g hg
    rw [List.range_zero, List.foldl_nil, List.length_replicate] at hg
    rw [List.range_zero, List.foldl_nil, getD_map_range _ _ hg]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, hg, ite_true, Option.getD_some]
    rfl
  | q + 1, hq => by
    rw [List.range_succ, List.foldl_append, counts_eq block groupOf m hgi q (by omega),
      List.foldl_cons, List.foldl_nil, countStep]
    by_cases hz : block.getD q 0 ≠ 0
    · rw [ite_eq_left hz]
      apply ext_getD 0 (by simp)
      intro g hg
      simp only [List.length_set, List.length_map, List.length_range] at hg
      have hlt := hgi q (by omega) hz
      rw [getD_set_eq, getD_map_range _ _ hg, getD_map_range _ _ hg, members_succ,
        List.length_append]
      by_cases hgq : (groupOf.getD q 0).toNat = g
      · rw [ite_eq_left ⟨hgq, by simpa using hlt⟩, getD_map_range _ _ hlt, ite_eq_left ⟨hz, hgq⟩,
          hgq]
        rfl
      · rw [ite_eq_right (fun h ↦ hgq h.1), ite_eq_right (fun h ↦ hgq h.2)]
        rfl
    · rw [ite_eq_right hz]
      apply ext_getD 0 (by simp)
      intro g hg
      simp only [List.length_map, List.length_range] at hg
      rw [getD_map_range _ _ hg, getD_map_range _ _ hg, members_succ, List.length_append,
        ite_eq_right (fun h ↦ hz h.1)]
      rfl

/-- `next`: where each run of a block's positions starts. -/
def runStarts : ℕ → List (BitVec 64 × ℕ) → List ℕ
  | _, [] => []
  | e, x :: l => e :: runStarts (e + x.2) l

/-- The `(word, end)` of each run. -/
def runEntries : ℕ → List (BitVec 64 × ℕ) → List (BitVec 64 × ℕ)
  | _, [] => []
  | e, x :: l => (x.1, e + x.2) :: runEntries (e + x.2) l

theorem runs_eq : ∀ (l : List (BitVec 64 × ℕ)) (nx : List ℕ) (e : ℕ) (ws : List (BitVec 64 × ℕ)),
    l.foldl runStep (nx, e, ws) = (nx ++ runStarts e l, e + (l.map Prod.snd).sum, ws ++ runEntries e l)
  | [], nx, e, ws => by simp [runStarts, runEntries]
  | x :: l, nx, e, ws => by
    rw [List.foldl_cons, runStep, runs_eq l]
    simp [runStarts, runEntries, Nat.add_assoc]

/-- The runs' slices of `positions`. -/
def runSlices (positions : List (BitVec 16)) : ℕ → List (BitVec 64 × ℕ) →
    List (BitVec 64 × List (BitVec 16))
  | _, [] => []
  | e, x :: l => (x.1, (positions.drop e).take x.2) :: runSlices positions (e + x.2) l

theorem groupsFrom_runEntries (positions : List (BitVec 16)) : ∀ (e : ℕ) (l : List (BitVec 64 × ℕ)),
    groupsFrom positions (runEntries e l) e = runSlices positions e l ∧
      positionsEnd (runEntries e l) e = e + (l.map Prod.snd).sum
  | e, [] => by simp [runEntries, groupsFrom, positionsEnd, runSlices]
  | e, x :: l => by
    obtain ⟨h1, h2⟩ := groupsFrom_runEntries positions (e + x.2) l
    refine ⟨?_, ?_⟩
    · rw [runEntries, groupsFrom, Nat.add_sub_cancel_left, h1, runSlices]
    · rw [runEntries, positionsEnd, h2]
      simp [Nat.add_assoc]

theorem getD_runStarts : ∀ (e : ℕ) (l : List (BitVec 64 × ℕ)) (g : ℕ), g < l.length →
    (runStarts e l).getD g 0 = e + ((l.map Prod.snd).take g).sum
  | e, [], g, h => absurd h (Nat.not_lt_zero _)
  | e, x :: l, 0, _ => by simp [runStarts]
  | e, x :: l, g + 1, h => by
    rw [runStarts, List.getD_cons_succ, getD_runStarts _ l g (by simpa using h)]
    simp [Nat.add_assoc]

theorem length_runStarts : ∀ (e : ℕ) (l : List (BitVec 64 × ℕ)), (runStarts e l).length = l.length
  | _, [] => rfl
  | e, x :: l => by rw [runStarts, List.length_cons, length_runStarts, List.length_cons]

theorem runSlices_eq : ∀ (positions : List (BitVec 16)) (e : ℕ) (l : List (BitVec 64 × ℕ)),
    runSlices positions e l = (List.range l.length).map fun g ↦ ((l.getD g (0, 0)).1,
      (positions.drop (e + ((l.map Prod.snd).take g).sum)).take (l.getD g (0, 0)).2)
  | _, _, [] => rfl
  | positions, e, x :: l => by
    rw [runSlices, runSlices_eq positions (e + x.2) l, List.length_cons, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    simp [Nat.add_assoc]

theorem take_drop_set_out {α : Type} (l : List α) (i s k : ℕ) (a : α) (h : i < s ∨ s + k ≤ i) :
    ((l.set i a).drop s).take k = (l.drop s).take k := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_set]
  split
  · rw [ite_eq_right (by omega)]
  · rfl

theorem take_drop_set_end {α : Type} (l : List α) (s k : ℕ) (a : α) (h : s + k < l.length) :
    ((l.set (s + k) a).drop s).take (k + 1) = (l.drop s).take k ++ [a] := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_set, List.getElem?_append,
    List.length_take, List.length_drop]
  rcases (show j < k ∨ j = k ∨ k < j by omega) with hj | rfl | hj
  · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega)]
  · rw [ite_eq_left (by omega), ite_eq_left rfl, ite_eq_left h, ite_eq_right (by omega),
      Nat.min_eq_left (by omega), Nat.sub_self]
    rfl
  · rw [ite_eq_right (show ¬ j < k + 1 by omega),
      ite_eq_right (show ¬ j < min k (l.length - s) by omega)]
    symm
    apply List.getElem?_eq_none
    simp
    omega

theorem sum_take_mono (l : List ℕ) {i j : ℕ} (h : i ≤ j) : (l.take i).sum ≤ (l.take j).sum := by
  rw [show j = i + (j - i) by omega, List.take_add, List.sum_append]
  omega

theorem sum_take_succ_le (l : List ℕ) {i j : ℕ} (h : i < j) (hi : i < l.length) :
    (l.take i).sum + l.getD i 0 ≤ (l.take j).sum := by
  have := List.sum_take_succ l i hi
  rw [List.getD_eq_getElem _ _ hi, ← this]
  exact sum_take_mono l h

theorem members_length_mono (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (g : ℕ)
    {q q' : ℕ} (h : q ≤ q') : (members block groupOf g q).length ≤ (members block groupOf g q').length :=
  ((List.range_sublist.mpr h).filter _).length_le

/-- The placement after the positions `< q`. -/
structure PlaceInv (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (P : List (BitVec 16))
    (cs : List ℕ) (q : ℕ) (st : List (BitVec 16) × List ℕ) : Prop where
  len : st.1.length = P.length + cs.sum
  prefix_eq : ∀ i < P.length, st.1.getD i 0 = P.getD i 0
  next_len : st.2.length = cs.length
  next : ∀ g < cs.length, st.2.getD g 0 = P.length + (cs.take g).sum + (members block groupOf g q).length
  slice : ∀ g < cs.length, (st.1.drop (P.length + (cs.take g).sum)).take
    (members block groupOf g q).length = (members block groupOf g q).map (BitVec.ofNat 16)

theorem place_spec (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (P : List (BitVec 16))
    (cs : List ℕ) (hcs : ∀ g < cs.length, cs.getD g 0 = (members block groupOf g block.length).length)
    (hgi : ∀ p < block.length, block.getD p 0 ≠ 0 → (groupOf.getD p 0).toNat < cs.length)
    (nx : List ℕ) (hnx : nx.length = cs.length)
    (hnx' : ∀ g < cs.length, nx.getD g 0 = P.length + (cs.take g).sum) :
    ∀ q ≤ block.length, PlaceInv block groupOf P cs q
      ((List.range q).foldl (placeStep block groupOf) (resizeRust P (P.length + cs.sum), nx))
  | 0, _ => by
    have hr : resizeRust P (P.length + cs.sum) = P ++ List.replicate cs.sum 0 := by
      rw [resizeRust, List.take_of_length_le (by omega), show P.length + cs.sum - P.length = cs.sum
        by omega]
    refine ⟨by rw [List.range_zero, List.foldl_nil, hr]; simp, fun i hi ↦ ?_, hnx, fun g hg ↦ ?_,
      fun g hg ↦ ?_⟩
    · rw [List.range_zero, List.foldl_nil, hr, List.getD_append _ _ _ _ hi]
    · rw [List.range_zero, List.foldl_nil, hnx' g hg]
      simp [members]
    · simp [members]
  | q + 1, hq => by
    have ih := place_spec block groupOf P cs hcs hgi nx hnx hnx' q (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range q).foldl (placeStep block groupOf)
      (resizeRust P (P.length + cs.sum), nx) = st at ih ⊢
    rw [placeStep]
    by_cases hz : block.getD q 0 ≠ 0
    · rw [ite_eq_left hz]
      set g0 := (groupOf.getD q 0).toNat
      have hg0 : g0 < cs.length := hgi q (by omega) hz
      set k0 := (members block groupOf g0 q).length
      have hk0 : k0 + 1 ≤ cs.getD g0 0 := by
        rw [hcs g0 hg0]
        have := members_length_mono block groupOf g0 (show q + 1 ≤ block.length from hq)
        rw [members_succ, List.length_append, ite_eq_left ⟨hz, rfl⟩] at this
        simpa using this
      have hat : st.2.getD g0 0 = P.length + (cs.take g0).sum + k0 := ih.next g0 hg0
      have hend : P.length + (cs.take g0).sum + k0 < st.1.length := by
        rw [ih.len]
        have := sum_take_succ_le cs (show g0 < cs.length + 1 by omega) hg0
        rw [List.take_of_length_le (show cs.length ≤ cs.length + 1 by omega)] at this
        omega
      rw [hat]
      refine ⟨by rw [List.length_set, ih.len], fun i hi ↦ ?_, by rw [List.length_set, ih.next_len],
        fun g hg ↦ ?_, fun g hg ↦ ?_⟩
      · rw [getD_set_eq, ite_eq_right (by omega), ih.prefix_eq i hi]
      · rw [getD_set_eq, members_succ, List.length_append]
        by_cases hgg : g0 = g
        · subst hgg
          rw [ite_eq_left ⟨rfl, by rw [ih.next_len]; exact hg0⟩, ite_eq_left ⟨hz, rfl⟩,
            List.length_singleton]
          omega
        · rw [ite_eq_right (fun h ↦ hgg h.1), ih.next g hg, ite_eq_right (fun h ↦ hgg h.2)]
          simp
      · rw [members_succ]
        by_cases hgg : g0 = g
        · subst hgg
          rw [ite_eq_left ⟨hz, rfl⟩, List.length_append, List.length_singleton, List.map_append,
            ← ih.slice g0 hg0, take_drop_set_end _ _ _ _ hend]
          rfl
        · rw [ite_eq_right (fun h ↦ hgg h.2), List.append_nil, take_drop_set_out, ih.slice g hg]
          have hkg := members_length_mono block groupOf g (show q ≤ block.length by omega)
          rw [← hcs g hg] at hkg
          rcases (show g < g0 ∨ g0 < g by omega) with hlt | hlt
          · have := sum_take_succ_le cs hlt hg
            right; omega
          · have := sum_take_succ_le cs hlt hg0
            left; omega
    · rw [ite_eq_right hz]
      refine ⟨ih.len, ih.prefix_eq, ih.next_len, fun g hg ↦ ?_, fun g hg ↦ ?_⟩
      · rw [ih.next g hg, members_succ, ite_eq_right (fun h ↦ hz h.1), List.append_nil]
      · rw [members_succ, ite_eq_right (fun h ↦ hz h.1), List.append_nil]
        exact ih.slice g hg

/-! ### The buckets -/

theorem bucket_toNat (v : BitVec 8) {i : ℕ} (hi : i < 8) :
    (256#16 * BitVec.ofNat 16 i + v.setWidth 16).toNat = 256 * i + v.toNat := by
  have hv := v.isLt
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]
  omega

theorem byteBucketsRust_lt (w : BitVec 64) : ∀ c ∈ byteBucketsRust w, c.toNat < 2048 := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  have he' := (List.mem_filter.mp he).1
  have hi : e.2 < 8 := by
    have := List.mem_zipIdx_iff_getElem?.mp he'
    have h8 : (toLeBytes w).length = 8 := length_toLeBytes w
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at this
    exact absurd this (by simp)
  rw [bucket_toNat _ hi]
  have := e.1.isLt
  omega

theorem wordBuckets_sub (w : BitVec 64) :
    ∀ b ∈ wordBuckets w, b ∈ (byteBucketsRust w).map BitVec.toNat := by
  intro b hb
  simp only [wordBuckets, List.mem_map, List.mem_filter, List.mem_range] at hb
  obtain ⟨j, ⟨hj, hne⟩, rfl⟩ := hb
  refine List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨((toLeBytes w).getD j 0, j), List.mem_filter.mpr
    ⟨List.mem_zipIdx_iff_getElem?.mpr ?_, by simpa using hne⟩, rfl⟩, bucket_toNat _ hj⟩
  rw [List.getD_eq_getElem _ _ (by rw [length_toLeBytes]; exact hj)]
  simp

/-- The `used` table and the buckets `Z` pushed so far. -/
def UsedInv (used : List Bool) (Z : List (BitVec 16)) : Prop :=
  used.length = 2048 ∧ (∀ b < 2048, used.getD b false = true ↔ b ∈ Z.map BitVec.toNat) ∧
    ∀ c ∈ Z, c.toNat < 2048

theorem usedFold_spec (Y : List (BitVec 16)) : ∀ (cs : List (BitVec 16)) (used : List Bool)
    (Z : List (BitVec 16)), (∀ c ∈ cs, c.toNat < 2048) → UsedInv used Z →
    ∃ used' Z', cs.foldl usedStep (used, Y ++ Z) = (used', Y ++ Z') ∧ UsedInv used' Z' ∧
      (∀ c ∈ cs, c.toNat ∈ Z'.map BitVec.toNat) ∧ ∀ x ∈ Z.map BitVec.toNat, x ∈ Z'.map BitVec.toNat
  | [], used, Z, _, h => ⟨used, Z, rfl, h, by simp, fun _ hx ↦ hx⟩
  | c :: cs, used, Z, hcs, ⟨h1, h2, h3⟩ => by
    have hc := hcs c (by simp)
    rw [List.foldl_cons, usedStep]
    by_cases hu : used.getD c.toNat false = true
    · rw [ite_eq_right (by rw [hu]; decide)]
      obtain ⟨u', Z', he, hinv, hmem, hsub⟩ :=
        usedFold_spec Y cs used Z (fun c' h ↦ hcs c' (by simp [h])) ⟨h1, h2, h3⟩
      refine ⟨u', Z', he, hinv, fun c' hc' ↦ ?_, hsub⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hsub _ ((h2 _ hc).mp hu)
      · exact hmem c' hc'
    · have hu' : used.getD c.toNat false = false := Bool.eq_false_iff.mpr hu
      rw [ite_eq_left (by rw [hu']; rfl), List.append_assoc]
      have hinv : UsedInv (used.set c.toNat true) (Z ++ [c]) := by
        refine ⟨by rw [List.length_set, h1], fun b hb ↦ ?_, fun c' hc' ↦ ?_⟩
        · rw [getD_set_eq, List.map_append, List.mem_append, ← h2 b hb, h1]
          by_cases hbc : c.toNat = b
          · subst hbc; simp [hb]
          · rw [ite_eq_right (fun h ↦ hbc h.1)]
            simp [Ne.symm hbc]
        · rcases List.mem_append.mp hc' with hc' | hc'
          · exact h3 c' hc'
          · rw [List.mem_singleton.mp hc']; exact hc
      obtain ⟨u', Z', he, hinv', hmem, hsub⟩ :=
        usedFold_spec Y cs _ (Z ++ [c]) (fun c' h ↦ hcs c' (by simp [h])) hinv
      refine ⟨u', Z', he, hinv', fun c' hc' ↦ ?_, fun x hx ↦ hsub x (by simp at hx ⊢; simp [hx])⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hsub _ (by simp)
      · exact hmem c' hc'

theorem wordsUsed_spec (Y : List (BitVec 16)) : ∀ (D : List (BitVec 64)) (used : List Bool)
    (Z : List (BitVec 16)), UsedInv used Z →
    ∃ used' Z', D.foldl (fun u word ↦ (byteBucketsRust word).foldl usedStep u) (used, Y ++ Z) =
      (used', Y ++ Z') ∧ UsedInv used' Z' ∧
      (∀ w ∈ D, ∀ b ∈ wordBuckets w, b ∈ Z'.map BitVec.toNat) ∧
      ∀ x ∈ Z.map BitVec.toNat, x ∈ Z'.map BitVec.toNat
  | [], used, Z, h => ⟨used, Z, rfl, h, by simp, fun _ hx ↦ hx⟩
  | w :: D, used, Z, h => by
    obtain ⟨u1, Z1, he1, hinv1, hmem1, hsub1⟩ :=
      usedFold_spec Y (byteBucketsRust w) used Z (byteBucketsRust_lt w) h
    obtain ⟨u2, Z2, he2, hinv2, hmem2, hsub2⟩ := wordsUsed_spec Y D u1 Z1 hinv1
    refine ⟨u2, Z2, by rw [List.foldl_cons, he1, he2], hinv2, fun w' hw' b hb ↦ ?_,
      fun x hx ↦ hsub2 x (hsub1 x hx)⟩
    rcases List.mem_cons.mp hw' with rfl | hw'
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (wordBuckets_sub w' b hb)
      exact hsub2 _ (hmem1 c hc)
    · exact hmem2 w' hw' b hb

/-! ### The entries -/

/-- The nonzero entries of `l`, their indices offset by `off`. -/
def nzFrom (l : List (BitVec 64)) (off : ℕ) : List (ℕ × BitVec 64) :=
  ((List.range l.length).filter fun i ↦ l.getD i 0 ≠ 0).map fun i ↦ (off + i, l.getD i 0)

theorem nonzeroEntries_eq (table : List (BitVec 64)) : nonzeroEntries table = nzFrom table 0 := by
  simp [nonzeroEntries, nzFrom]

theorem nzFrom_append (l1 l2 : List (BitVec 64)) (off : ℕ) :
    nzFrom (l1 ++ l2) off = nzFrom l1 off ++ nzFrom l2 (off + l1.length) := by
  rw [nzFrom, List.length_append, List.range_add, List.filter_append, List.map_append, nzFrom, nzFrom]
  congr 1
  · rw [List.filter_congr (fun i hi ↦ by rw [List.getD_append _ _ _ _ (List.mem_range.mp hi)])]
    exact List.map_congr_left fun i hi ↦ by
      rw [List.getD_append _ _ _ _ (List.mem_range.mp (List.mem_filter.mp hi).1)]
  · rw [List.filter_map, List.map_map]
    have h : ∀ i, (l1 ++ l2).getD (l1.length + i) 0 = l2.getD i 0 := fun i ↦ by
      rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    simp only [Function.comp_def, h, Nat.add_assoc]

theorem perm_groups (block : List (BitVec 64)) (groupOf : List (BitVec 16)) (D : List (BitVec 64))
    (hgi : ∀ p < block.length, block.getD p 0 ≠ 0 →
      (groupOf.getD p 0).toNat < D.length ∧ D.getD (groupOf.getD p 0).toNat 0 = block.getD p 0)
    (off : ℕ) :
    ((List.range D.length).flatMap fun g ↦ (members block groupOf g block.length).map fun p ↦
      (off + p, D.getD g 0)).Perm (nzFrom block off) := by
  have hf : ((List.range D.length).flatMap fun g ↦ (members block groupOf g block.length).map
      fun p ↦ (off + p, D.getD g 0)) = ((List.range D.length).flatMap fun g ↦
        members block groupOf g block.length).map fun p ↦ (off + p, block.getD p 0) := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro g _
    apply List.map_congr_left
    intro p hp
    simp only [members, List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
    rw [← hp.2.2, (hgi p hp.1 hp.2.1).2]
  rw [hf, nzFrom]
  apply List.Perm.map
  rw [List.perm_ext_iff_of_nodup]
  · intro p
    simp only [List.mem_flatMap, List.mem_range, members, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨g, _, hp, hz, _⟩
      exact ⟨hp, hz⟩
    · rintro ⟨hp, hz⟩
      exact ⟨_, (hgi p hp hz).1, hp, hz, rfl⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun g _ ↦ List.nodup_range.filter _, ?_⟩
    refine List.pairwise_lt_range.imp fun {a b} hab ↦ ?_
    intro p hpa hpb
    simp only [members, List.mem_filter, decide_eq_true_eq] at hpa hpb
    omega
  · exact List.nodup_range.filter _

/-! ### The walk over the blocks -/

/-- A block as `evaluate` reads it from the given starts. -/
def viewAt (bc : BytecodeRust) (b : BlockRust) (ws ps bys : ℕ) : BlockView :=
  ⟨b.index, groupsFrom bc.positions ((bc.words.drop ws).take (b.wordsEnd - ws)) ps,
    (bc.bytes.drop bys).take (b.bytesEnd - bys)⟩

/-- Where the walk over the blocks ends. -/
def walkEnd (bc : BytecodeRust) : List BlockRust → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | [], ws, ps, bys => (ws, ps, bys)
  | b :: bs, ws, ps, _ =>
    walkEnd bc bs b.wordsEnd (positionsEnd ((bc.words.drop ws).take (b.wordsEnd - ws)) ps)
      b.bytesEnd

theorem viewsFrom_append (bc : BytecodeRust) (b : BlockRust) : ∀ (bs : List BlockRust) (ws ps bys : ℕ),
    viewsFrom bc (bs ++ [b]) ws ps bys = viewsFrom bc bs ws ps bys ++
      [viewAt bc b (walkEnd bc bs ws ps bys).1 (walkEnd bc bs ws ps bys).2.1
        (walkEnd bc bs ws ps bys).2.2]
  | [], _, _, _ => rfl
  | c :: bs, ws, ps, bys => by
    rw [List.cons_append, viewsFrom, viewsFrom, viewsFrom_append bc b bs, walkEnd, List.cons_append]

theorem walkEnd_append (bc : BytecodeRust) (b : BlockRust) : ∀ (bs : List BlockRust) (ws ps bys : ℕ),
    walkEnd bc (bs ++ [b]) ws ps bys = (b.wordsEnd, positionsEnd ((bc.words.drop
      (walkEnd bc bs ws ps bys).1).take (b.wordsEnd - (walkEnd bc bs ws ps bys).1))
        (walkEnd bc bs ws ps bys).2.1, b.bytesEnd)
  | [], _, _, _ => rfl
  | c :: bs, ws, ps, bys => by rw [List.cons_append, walkEnd, walkEnd_append bc b bs, walkEnd]

theorem slice_prefix {α : Type} (l l' : List α) (h : l'.take l.length = l) {a b : ℕ}
    (hb : b ≤ l.length) : (l'.drop a).take (b - a) = (l.drop a).take (b - a) := by
  rw [← List.drop_take, ← List.drop_take]
  congr 1
  rw [← h, List.take_take, Nat.min_eq_left hb]

theorem groupsFrom_prefix (P P' : List (BitVec 16)) (h : P'.take P.length = P) :
    ∀ (es : List (BitVec 64 × ℕ)) (ps : ℕ), (∀ e ∈ es, e.2 ≤ P.length) →
    groupsFrom P' es ps = groupsFrom P es ps
  | [], _, _ => rfl
  | e :: es, ps, hes => by
    rw [groupsFrom, groupsFrom, slice_prefix P P' h (hes e (by simp)),
      groupsFrom_prefix P P' h es e.2 (fun e' he' ↦ hes e' (by simp [he']))]

theorem viewsFrom_prefix (bc bc' : BytecodeRust) (hW : bc'.words.take bc.words.length = bc.words)
    (hP : bc'.positions.take bc.positions.length = bc.positions)
    (hY : bc'.bytes.take bc.bytes.length = bc.bytes)
    (hw : ∀ e ∈ bc.words, e.2 ≤ bc.positions.length) :
    ∀ (bs : List BlockRust), (∀ b ∈ bs, b.wordsEnd ≤ bc.words.length ∧ b.bytesEnd ≤ bc.bytes.length) →
    ∀ ws ps bys, viewsFrom bc' bs ws ps bys = viewsFrom bc bs ws ps bys ∧
      walkEnd bc' bs ws ps bys = walkEnd bc bs ws ps bys
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | b :: bs, hbs, ws, ps, bys => by
    have hb := hbs b (by simp)
    have he : (bc'.words.drop ws).take (b.wordsEnd - ws) = (bc.words.drop ws).take (b.wordsEnd - ws) :=
      slice_prefix _ _ hW hb.1
    have hg : groupsFrom bc'.positions ((bc.words.drop ws).take (b.wordsEnd - ws)) ps =
        groupsFrom bc.positions ((bc.words.drop ws).take (b.wordsEnd - ws)) ps :=
      groupsFrom_prefix _ _ hP _ _ fun e he' ↦ hw e (List.mem_of_mem_drop (List.mem_of_mem_take he'))
    obtain ⟨ih1, ih2⟩ := viewsFrom_prefix bc bc' hW hP hY hw bs (fun b' hb' ↦ hbs b' (by simp [hb']))
      b.wordsEnd (positionsEnd ((bc.words.drop ws).take (b.wordsEnd - ws)) ps) b.bytesEnd
    refine ⟨?_, ?_⟩
    · rw [viewsFrom, viewsFrom, he, hg, slice_prefix _ _ hY hb.2, ih1]
    · rw [walkEnd, walkEnd, he, ih2]

theorem runEntries_le : ∀ (e : ℕ) (l : List (BitVec 64 × ℕ)), ∀ x ∈ runEntries e l,
    x.2 ≤ e + (l.map Prod.snd).sum
  | _, [], x, hx => by simp [runEntries] at hx
  | e, y :: l, x, hx => by
    rw [runEntries, List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp
    · have := runEntries_le (e + y.2) l x hx
      simp only [List.map_cons, List.sum_cons]
      omega

theorem length_runEntries : ∀ (e : ℕ) (l : List (BitVec 64 × ℕ)), (runEntries e l).length = l.length
  | _, [] => rfl
  | e, x :: l => by rw [runEntries, List.length_cons, length_runEntries, List.length_cons]

theorem getD_zip (D : List (BitVec 64)) (cs : List ℕ) {g : ℕ} (hg : g < D.length)
    (hc : cs.length = D.length) : (D.zip cs).getD g (0, 0) = (D.getD g 0, cs.getD g 0) := by
  rw [List.getD_eq_getElem _ _ (by simp [hc, hg]), List.getElem_zip,
    List.getD_eq_getElem _ _ hg, List.getD_eq_getElem _ _ (by omega)]

/-! ### `new` establishes the invariant -/

/-- The structure `new` builds from its buffers. -/
def NewState.toBytecode (st : NewState) (len : ℕ) (iv : List (BitVec 8)) : BytecodeRust :=
  ⟨len, iv, st.blocks, st.words, st.positions, st.bytes⟩

/-- `new` after the blocks `< I`. -/
structure NewInv (table : List (BitVec 64)) (I : ℕ) (st : NewState) : Prop where
  slots_len : st.slots.length = 2 ^ 15
  groupOf_len : st.groupOf.length = 2 ^ 14
  blocks_le : ∀ b ∈ st.blocks, b.wordsEnd ≤ st.words.length ∧ b.bytesEnd ≤ st.bytes.length
  words_le : ∀ e ∈ st.words, e.2 ≤ st.positions.length
  walk : walkEnd (st.toBytecode table.length (fiatShamirIvRust table)) st.blocks 0 0 0 =
    (st.words.length, st.positions.length, st.bytes.length)
  entries : ((viewsFrom (st.toBytecode table.length (fiatShamirIvRust table)) st.blocks 0 0 0).flatMap
    BlockView.entries).Perm (nzFrom (table.take (I * 2 ^ 14)) 0)
  ok : ∀ v ∈ viewsFrom (st.toBytecode table.length (fiatShamirIvRust table)) st.blocks 0 0 0,
    (∀ g ∈ v.groups, ∀ p ∈ g.2, p.toNat < 2 ^ 14) ∧ BucketsOk v

theorem take_succ_block (table : List (BitVec 64)) (I : ℕ) :
    table.take ((I + 1) * 2 ^ 14) = table.take (I * 2 ^ 14) ++ (table.drop (I * 2 ^ 14)).take (2 ^ 14) := by
  rw [show (I + 1) * 2 ^ 14 = I * 2 ^ 14 + 2 ^ 14 by ring, List.take_add]

theorem blockNew_spec (table : List (BitVec 64)) (I : ℕ) (hI : I * 2 ^ 14 < table.length)
    (st : NewState) (h : NewInv table I st) :
    ∃ st', blockNewRust table st I = some st' ∧ NewInv table (I + 1) st' := by
  set block := (table.drop (I * 2 ^ 14)).take (2 ^ 14) with hblock
  have hn : block.length ≤ 2 ^ 14 := by rw [hblock, List.length_take]; omega
  have htake : (table.take (I * 2 ^ 14)).length = I * 2 ^ 14 := by
    rw [List.length_take]; omega
  have hnz : nzFrom (table.take ((I + 1) * 2 ^ 14)) 0 =
      nzFrom (table.take (I * 2 ^ 14)) 0 ++ nzFrom block (I * 2 ^ 14) := by
    rw [take_succ_block, nzFrom_append, htake, Nat.zero_add]
  obtain ⟨gst, hg, ginv⟩ := groupRust_spec block hn st.slots h.slots_len st.groupOf
    (by rw [h.groupOf_len]; exact hn)
  rw [h.groupOf_len] at ginv
  refine ⟨_, by rw [blockNewRust, hg]; rfl, ?_⟩
  dsimp only
  split
  · rename_i hD
    have hD' : gst.2.2 = [] := List.isEmpty_iff.mp hD
    have hblock0 : nzFrom block (I * 2 ^ 14) = [] := by
      rw [nzFrom, List.map_eq_nil_iff, List.filter_eq_nil_iff]
      intro p hp hz
      have := (ginv.group p (List.mem_range.mp hp) (by simpa using hz)).1
      rw [hD'] at this
      exact absurd this (Nat.not_lt_zero _)
    exact ⟨ginv.slots_len, ginv.groupOf_len, h.blocks_le, h.words_le, h.walk,
      by rw [hnz, hblock0, List.append_nil]; exact h.entries, h.ok⟩
  · rename_i hD
    have hgi := ginv.group
    have hDle := ginv.distinct_le
    have hGl := ginv.groupOf_len
    have hSl := ginv.slots_len
    generalize gst.2.2 = D at hgi hD hDle ⊢
    generalize gst.2.1 = G at hgi hGl ⊢
    rw [counts_eq block G D.length (fun p hp hz ↦ (hgi p hp hz).1) block.length le_rfl]
    set cs := (List.range D.length).map fun g ↦ (members block G g block.length).length with hcs
    have hcsl : cs.length = D.length := by simp [hcs]
    have hcsg : ∀ g < cs.length, cs.getD g 0 = (members block G g block.length).length := by
      intro g hg
      rw [hcs, getD_map_range _ _ (by simpa [hcs] using hg)]
    have hL : (D.zip cs).map Prod.snd = cs := List.map_snd_zip (by omega)
    have hLl : (D.zip cs).length = D.length := by simp [hcsl]
    rw [runs_eq (D.zip cs) [] st.positions.length st.words, hL, List.nil_append]
    have hpl := place_spec block G st.positions cs hcsg
      (fun p hp hz ↦ by rw [hcsl]; exact (hgi p hp hz).1) (runStarts st.positions.length (D.zip cs))
      (by rw [length_runStarts, hLl, hcsl])
      (fun g hg ↦ by rw [getD_runStarts _ _ g (by omega), hL]) block.length le_rfl
    generalize (List.range block.length).foldl (placeStep block G) (resizeRust st.positions
      (st.positions.length + cs.sum), runStarts st.positions.length (D.zip cs)) = placed at hpl ⊢
    obtain ⟨u', Z, hu, hUinv, hUmem, -⟩ := wordsUsed_spec st.bytes D (List.replicate 2048 false) []
      ⟨List.length_replicate, fun b hb ↦ by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hb]
        simp, fun c hc ↦ absurd hc List.not_mem_nil⟩
    rw [List.append_nil] at hu
    rw [hu]
    dsimp only
    have hW := h.words_le
    have hB := h.blocks_le
    have hwalk := h.walk
    have hent := h.entries
    have hok := h.ok
    simp only [NewState.toBytecode] at hwalk hent hok ⊢
    set np := st.positions.length with hnp
    set R := runEntries np (D.zip cs) with hR
    have hRle : ∀ e ∈ R, e.2 ≤ np + cs.sum := fun e he ↦ by
      have := runEntries_le np (D.zip cs) e he
      rwa [hL] at this
    have hP'len : placed.1.length = np + cs.sum := hpl.len
    have hPfx : placed.1.take np = st.positions := by
      apply ext_getD 0 (by rw [List.length_take, hP'len, hnp]; omega)
      intro i hi
      simp only [List.length_take] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
        ← List.getD_eq_getElem?_getD, hpl.prefix_eq i (by omega)]
    have hext := viewsFrom_prefix ⟨table.length, fiatShamirIvRust table, st.blocks, st.words,
      st.positions, st.bytes⟩ ⟨table.length, fiatShamirIvRust table,
      st.blocks ++ [⟨I, (st.words ++ R).length, (st.bytes ++ Z).length⟩], st.words ++ R, placed.1,
      st.bytes ++ Z⟩ (List.take_left' rfl) hPfx (List.take_left' rfl) hW st.blocks hB 0 0 0
    have hslice : ((st.words ++ R).drop st.words.length).take
        ((st.words ++ R).length - st.words.length) = R := by
      rw [List.drop_left, List.length_append, Nat.add_sub_cancel_left, List.take_length]
    have hbslice : ((st.bytes ++ Z).drop st.bytes.length).take
        ((st.bytes ++ Z).length - st.bytes.length) = Z := by
      rw [List.drop_left, List.length_append, Nat.add_sub_cancel_left, List.take_length]
    have hGR := groupsFrom_runEntries placed.1 np (D.zip cs)
    rw [hL] at hGR
    have hRS : runSlices placed.1 np (D.zip cs) = (List.range D.length).map fun g ↦
        (D.getD g 0, (members block G g block.length).map (BitVec.ofNat 16)) := by
      rw [runSlices_eq, hLl, hL]
      apply List.map_congr_left
      intro g hg
      have hg' := List.mem_range.mp hg
      rw [getD_zip D cs hg' hcsl]
      dsimp only
      rw [hcsg g (by omega), hpl.slice g (by omega)]
    have hviews : viewsFrom ⟨table.length, fiatShamirIvRust table,
        st.blocks ++ [⟨I, (st.words ++ R).length, (st.bytes ++ Z).length⟩], st.words ++ R, placed.1,
        st.bytes ++ Z⟩ (st.blocks ++ [⟨I, (st.words ++ R).length, (st.bytes ++ Z).length⟩]) 0 0 0 =
        viewsFrom ⟨table.length, fiatShamirIvRust table, st.blocks, st.words, st.positions, st.bytes⟩
          st.blocks 0 0 0 ++ [⟨I, (List.range D.length).map fun g ↦
            (D.getD g 0, (members block G g block.length).map (BitVec.ofNat 16)), Z⟩] := by
      rw [viewsFrom_append, hext.1, hext.2, hwalk]
      simp only [viewAt]
      rw [hslice, hbslice, hGR.1, hRS]
    have hmem16 : ∀ g, ∀ p ∈ members block G g block.length, (BitVec.ofNat 16 p).toNat = p := by
      intro g p hp
      have := List.mem_range.mp (List.mem_filter.mp hp).1
      rw [BitVec.toNat_ofNat]
      omega
    refine ⟨hSl, hGl, fun b hb ↦ ?_, fun e he ↦ ?_, ?_, ?_, ?_⟩
    · rcases List.mem_append.mp hb with hb | hb
      · have := hB b hb
        simp only [List.length_append]
        omega
      · rw [List.mem_singleton.mp hb]
        exact ⟨le_rfl, le_rfl⟩
    · rw [hP'len]
      rcases List.mem_append.mp he with he | he
      · have := hW e he
        omega
      · exact hRle e he
    · dsimp only [NewState.toBytecode]
      rw [walkEnd_append, hext.2, hwalk]
      dsimp only
      rw [hslice, hGR.2, hP'len]
    · dsimp only [NewState.toBytecode]
      rw [hviews, List.flatMap_append, hnz]
      refine hent.append ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, BlockView.entries]
      rw [List.flatMap_map]
      have := perm_groups block G D hgi (I * 2 ^ 14)
      refine List.Perm.trans (List.Perm.of_eq ?_) this
      apply List.flatMap_congr
      intro g _
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      show (2 ^ 14 * I + (BitVec.ofNat 16 p).toNat, D.getD g 0) = (I * 2 ^ 14 + p, D.getD g 0)
      rw [hmem16 g p hp, Nat.mul_comm]
    · dsimp only [NewState.toBytecode]
      rw [hviews]
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hok v hv
      · rw [List.mem_singleton.mp hv]
        refine ⟨fun g hg p hp ↦ ?_, fun g hg b hb ↦ ?_, hUinv.2.2⟩
        · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hg
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          rw [hmem16 j q hq]
          have := List.mem_range.mp (List.mem_filter.mp hq).1
          omega
        · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
          exact hUmem _ (by
            rw [List.getD_eq_getElem _ _ (by simpa using hj)]
            exact List.getElem_mem _) b hb

/-- **`Bytecode::new` returns, and the structure it builds is prepared for `evaluate`.** -/
theorem newRust_spec (table : List (BitVec 64)) :
    ∃ bc, newRust table = some bc ∧ bc.fiatShamirIv = fiatShamirIvRust table ∧ Prepared table bc := by
  have h14 : (2 : ℕ) ^ 14 = 16384 := by norm_num
  have h15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
  set N := (table.length + 2 ^ 14 - 1) / 2 ^ 14 with hN
  have hfold : ∀ I ≤ N, ∃ st, (List.range I).foldl
      (fun st index ↦ st.bind fun st ↦ blockNewRust table st index)
      (some ⟨[], [], [], [], List.replicate (2 ^ 15) none, List.replicate (2 ^ 14) 0⟩) = some st ∧
      NewInv table I st := by
    intro I hI
    induction I with
    | zero =>
      refine ⟨_, rfl, ⟨List.length_replicate, List.length_replicate, fun _ h ↦ absurd h List.not_mem_nil,
        fun _ h ↦ absurd h List.not_mem_nil, rfl, ?_, fun _ h ↦ absurd h List.not_mem_nil⟩⟩
      simp [viewsFrom, nzFrom]
    | succ I ih =>
      obtain ⟨st, hst, hinv⟩ := ih (by omega)
      have hI' : I * 2 ^ 14 < table.length := by
        rw [hN, h14] at hI
        rw [h14]
        omega
      obtain ⟨st', h1, h2⟩ := blockNew_spec table I hI' st hinv
      refine ⟨st', ?_, h2⟩
      rw [List.range_succ, List.foldl_append, hst, List.foldl_cons, List.foldl_nil, Option.bind_some,
        h1]
  obtain ⟨st, hst, hinv⟩ := hfold N le_rfl
  refine ⟨_, by rw [newRust, hst]; rfl, rfl, ?_⟩
  have htake : table.take (N * 2 ^ 14) = table := List.take_of_length_le (by rw [hN, h14]; omega)
  have hent := hinv.entries
  rw [htake] at hent
  exact ⟨rfl, by rw [nonzeroEntries_eq]; exact hent, fun v hv ↦ (hinv.ok v hv).1,
    fun v hv ↦ (hinv.ok v hv).2.1, fun v hv ↦ (hinv.ok v hv).2.2⟩

/-- **`Bytecode::evaluate` on what `Bytecode::new` builds computes the statement's bytecode
value**: `new` returns, its IV is `fiatShamirIvRust` (the statement's IV, `fiatShamirIvRust_eq`),
and at a point of the table's size `evaluate` returns what `computedBytecodeValue` does. -/
theorem newRust_evaluate (table : List K) (point : List E)
    (hp : point.length < 64 ∧ table.length = 2 ^ point.length) :
    ∃ bc v, newRust (table.map BF64.toBitVec) = some bc ∧
      bc.fiatShamirIv = fiatShamirIvRust (table.map BF64.toBitVec) ∧
      evaluateRust bc point = some v ∧ computedBytecodeValue table point = pure v := by
  obtain ⟨bc, h1, h2, h3⟩ := newRust_spec (table.map BF64.toBitVec)
  obtain ⟨v, h4, h5⟩ := evaluateRust_computed table bc h3 point hp
  exact ⟨bc, v, h1, h2, h4, h5⟩

end Rv64Verifier.Model
