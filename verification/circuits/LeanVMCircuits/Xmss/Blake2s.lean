import EthCryptographySpecs.Xmss.Blake2s
import LeanVMCircuits.Rec.Statement

/-!
# The specification's BLAKE2s on whole words

`EthCryptographySpecs.Xmss.Blake2s.hash` of the little-endian bytes of 64-bit words is the 32 little-endian bytes of
`digest (hashWords ws)`, the RFC 7693 BLAKE2s-256 the circuit computes (`hash_wordsBytes`). The specification's
`UInt32` lanes are RFC 7693's `BitVec 32` words (`enc`), its `mix` is `G` (`mix_enc`), its ten rounds are `F`'s fold
(`compress_enc`), its block reader reads `Statement.block` (`blockWords_eq`), its byte counters are `blake2s256`'s
(`drive`), and its serializer writes `digest`'s words (`stateBytes_eq`). The compression machinery is private to the
specification: statements name it through `spec_private%`, and `delta_private` unfolds it.

This file imports the vendored specification, so it is not a module.
-/

open Lean Elab Term in
/-- The private declaration `id` of the specification's `Blake2s` file, as a term. -/
elab "spec_private% " id:ident : term => do
  let n := mkPrivateNameCore `EthCryptographySpecs.Xmss.Blake2s id.getId
  mkConstWithLevelParams n

open Lean Elab Tactic Meta in
/-- Unfold the private declaration `id` of the specification's `Blake2s` file in the goal. -/
elab "delta_private " id:ident : tactic => do
  let n := mkPrivateNameCore `EthCryptographySpecs.Xmss.Blake2s (`EthCryptographySpecs.Xmss.Blake2s ++ id.getId)
  liftMetaTactic1 fun g => some <$> g.deltaTarget (· == n)

namespace LeanVMCircuits.Xmss.Spec

open EthCryptographySpecs.Xmss LeanVMCircuits.Blake2s.Rfc7693 LeanVMCircuits.Rec

/-! ## Bytes of words -/

/-- Byte `k` of a word, little endian. -/
def byteOf {n : ℕ} (w : BitVec n) (k : ℕ) : UInt8 := UInt8.ofBitVec (w.extractLsb' (8 * k) 8)

/-- A 64-bit word from its eight little-endian bytes, the way the specification reads one. -/
def or64 (f : ℕ → UInt8) : UInt64 :=
  (f 0).toUInt64 ||| ((f 1).toUInt64 <<< 8) ||| ((f 2).toUInt64 <<< 16) ||| ((f 3).toUInt64 <<< 24)
    ||| ((f 4).toUInt64 <<< 32) ||| ((f 5).toUInt64 <<< 40) ||| ((f 6).toUInt64 <<< 48)
    ||| ((f 7).toUInt64 <<< 56)

/-- A 32-bit word from its four little-endian bytes, the way the specification reads one. -/
def or32 (f : ℕ → UInt8) : UInt32 :=
  (f 0).toUInt32 ||| ((f 1).toUInt32 <<< 8) ||| ((f 2).toUInt32 <<< 16) ||| ((f 3).toUInt32 <<< 24)

/-- Words with the same bytes are equal. -/
theorem byteOf_ext {n : ℕ} (a b : BitVec n) (h : ∀ k, 8 * k < n → byteOf a k = byteOf b k) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun u : UInt8 => u.toBitVec.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp only [byteOf, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb'] at this
  rw [show 8 * (j / 8) + j % 8 = j by omega] at this
  simpa [show j % 8 < 8 by omega] using this

theorem byteOf_or64 (f : ℕ → UInt8) (k : ℕ) (hk : k < 8) : byteOf (or64 f).toBitVec k = f k := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases k <;> interval_cases j <;>
    simp [byteOf, or64, BitVec.getLsbD_extractLsb', UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
      UInt8.toBitVec_toUInt64, BitVec.shiftLeft_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]

theorem byteOf_or32 (f : ℕ → UInt8) (k : ℕ) (hk : k < 4) : byteOf (or32 f).toBitVec k = f k := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  interval_cases k <;> interval_cases j <;>
    simp [byteOf, or32, BitVec.getLsbD_extractLsb', UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
      UInt8.toBitVec_toUInt32, BitVec.shiftLeft_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth]

theorem or64_bytes (w : BitVec 64) : or64 (byteOf w) = UInt64.ofBitVec w := by
  apply UInt64.toBitVec_inj.mp
  apply byteOf_ext
  intro k hk
  rw [byteOf_or64 _ _ (by omega)]

theorem or32_bytes (w : BitVec 32) : or32 (byteOf w) = UInt32.ofBitVec w := by
  apply UInt32.toBitVec_inj.mp
  apply byteOf_ext
  intro k hk
  rw [byteOf_or32 _ _ (by omega)]

/-- Byte `t` of half `s` of a word is its byte `4s + t`. -/
theorem byteOf_half (w : BitVec 64) (s t : ℕ) (hs : s < 2) (ht : t < 4) :
    byteOf (half w s) t = byteOf w (4 * s + t) := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h1 : 8 * t + j < 32 := by omega
  simp only [byteOf, half, UInt8.toBitVec_ofBitVec, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, h1, hj, decide_true, Bool.true_and]
  congr 1
  omega

/-- The byte the specification serializes a 32-bit word to, at position `p`. -/
theorem shift_toUInt8 (x : UInt32) (p : ℕ) (hp : p < 4) :
    (x >>> UInt32.ofNat (8 * p)).toUInt8 = byteOf x.toBitVec p := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h8 : (8 * p) % 4294967296 % 32 = 8 * p := by omega
  simp [byteOf, UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, BitVec.ushiftRight_eq',
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb', BitVec.toNat_umod, hj, h8]

theorem byteOf_toNat {n : ℕ} (w : BitVec n) (k : ℕ) : (byteOf w k).toNat = w.toNat / 2 ^ (8 * k) % 256 := by
  simp [byteOf, UInt8.toNat, Nat.shiftRight_eq_div_pow]

theorem byteOf_zero {n : ℕ} (k : ℕ) : byteOf (0 : BitVec n) k = 0 := by
  apply UInt8.toNat_inj.mp
  simp [byteOf_toNat]


/-- Byte `k` of the little-endian bytes of `ws`, zero past their end. -/
def byteAt (ws : List (BitVec 64)) (k : ℕ) : UInt8 := byteOf (wordAt ws (k / 8)) (k % 8)

/-- The little-endian bytes of 64-bit words, eight per word. -/
def wordsBytes (ws : List (BitVec 64)) : ByteArray := ⟨Array.ofFn fun k : Fin (8 * ws.length) => byteAt ws k⟩

/-- The first `n` little-endian bytes of 64-bit words, zero past their end. -/
def wordsVec (n : ℕ) (ws : List (BitVec 64)) : Vector UInt8 n := Vector.ofFn fun k => byteAt ws k

theorem wordsBytes_size (ws : List (BitVec 64)) : (wordsBytes ws).size = 8 * ws.length := by
  simp [wordsBytes, ByteArray.size]

theorem wordsBytes_getD (ws : List (BitVec 64)) (k : ℕ) : (wordsBytes ws).data.getD k 0 = byteAt ws k := by
  by_cases hk : k < 8 * ws.length
  · simp [wordsBytes, Array.getD_eq_getD_getElem?, hk]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp [wordsBytes]; omega)]
    simp only [byteAt, wordAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (show ws.length ≤ k / 8 by omega),
      Option.getD_none]
    apply UInt8.toNat_inj.mp
    simp [byteOf_toNat]

/-! ## Lanes as words -/

/-- The `UInt32` lanes holding the words of a vector. -/
def enc {n : ℕ} (v : Vector (BitVec 32) n) : Array UInt32 := v.toArray.map UInt32.ofBitVec

@[simp] theorem enc_size {n : ℕ} (v : Vector (BitVec 32) n) : (enc v).size = n := by simp [enc]

theorem enc_get {n : ℕ} (v : Vector (BitVec 32) n) (i : ℕ) (h : i < n) : (enc v)[i]! = UInt32.ofBitVec v[i] := by
  simp [enc, getElem!_pos, h]

theorem enc_set {n : ℕ} (v : Vector (BitVec 32) n) (i : ℕ) (h : i < n) (x : UInt32) :
    (enc v).set! i x = enc (v.set i x.toBitVec) := by
  rw [Array.set!_eq_setIfInBounds]
  apply Array.ext
  · simp [enc]
  · intro j h1 h2
    have hj : j < n := by simpa using h2
    rw [Array.getElem_setIfInBounds (by simpa using hj)]
    simp only [enc, Array.getElem_map, Vector.getElem_toArray]
    rw [Vector.getElem_set]
    split <;> simp_all

theorem enc_append {n m : ℕ} (a : Vector (BitVec 32) n) (b : Vector (BitVec 32) m) :
    enc a ++ enc b = enc (a ++ b) := by
  simp [enc]

/-- The specification's rotation is `BitVec.rotateRight`. -/
theorem rot (x n : UInt32) (h0 : 0 < n.toNat) (h : n.toNat < 32) :
    ((spec_private% EthCryptographySpecs.Xmss.Blake2s.rotateRight) x n).toBitVec = x.toBitVec.rotateRight n.toNat := by
  delta_private rotateRight
  rw [BitVec.rotateRight_def, UInt32.toBitVec_or, UInt32.toBitVec_shiftRight, UInt32.toBitVec_shiftLeft,
    BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
  congr 2
  · simp [BitVec.toNat_umod]; omega

theorem rot16 (x : UInt32) :
    ((spec_private% EthCryptographySpecs.Xmss.Blake2s.rotateRight) x 16).toBitVec = x.toBitVec.rotateRight 16 := by
  simpa using rot x 16 (by decide) (by decide)
theorem rot12 (x : UInt32) :
    ((spec_private% EthCryptographySpecs.Xmss.Blake2s.rotateRight) x 12).toBitVec = x.toBitVec.rotateRight 12 := by
  simpa using rot x 12 (by decide) (by decide)
theorem rot8 (x : UInt32) :
    ((spec_private% EthCryptographySpecs.Xmss.Blake2s.rotateRight) x 8).toBitVec = x.toBitVec.rotateRight 8 := by
  simpa using rot x 8 (by decide) (by decide)
theorem rot7 (x : UInt32) :
    ((spec_private% EthCryptographySpecs.Xmss.Blake2s.rotateRight) x 7).toBitVec = x.toBitVec.rotateRight 7 := by
  simpa using rot x 7 (by decide) (by decide)

/-- The specification's `mix` is RFC 7693's `G`. -/
theorem mix_enc (v : Vector (BitVec 32) 16) (a b c d : ℕ) (ha : a < 16) (hb : b < 16) (hc : c < 16)
    (hd : d < 16) (x y : UInt32) :
    (spec_private% EthCryptographySpecs.Xmss.Blake2s.mix) (enc v) a b c d x y =
      enc (G v ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ x.toBitVec y.toBitVec) := by
  delta_private mix
  simp (disch := omega) only [Id.run, enc_get, enc_set, UInt32.toBitVec_add, UInt32.toBitVec_xor,
    UInt32.toBitVec_ofBitVec, rot16, rot12, rot8, rot7, G]
  rfl

/-- The specification's message schedule is RFC 7693's `SIGMA`. -/
theorem sigma_eq : ∀ r : Fin 10, Blake2s.Internal.sigma[r.val]! = (SIGMA[r].map Fin.val).toArray := by
  decide +kernel

/-- A fold on lanes that is a fold on words on each step is one on the whole list. -/
theorem foldl_enc {α γ : Type} (l : List α) (f : Array UInt32 → α → Array UInt32) (g : γ → α → γ)
    (e : γ → Array UInt32) (c : γ) (hf : ∀ c a, a ∈ l → f (e c) a = e (g c a)) :
    l.foldl f (e c) = e (l.foldl g c) := by
  induction l generalizing c with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [hf c a (by simp), ih]
    intro c a h
    exact hf c a (by simp [h])

/-- The specification's IV is RFC 7693's. -/
theorem iv_enc : (spec_private% EthCryptographySpecs.Xmss.Blake2s.IV) = enc IV := by decide +kernel

theorem sched (r : ℕ) (hr : r < 10) (k : ℕ) (hk : k < 16) :
    (Blake2s.Internal.sigma[r]!)[k]! = (SIGMA[r]'hr)[k].val := by
  have := sigma_eq ⟨r, hr⟩
  simp only at this
  rw [this]
  simp [hk]

theorem ofBitVec_xor (a b : BitVec 32) : UInt32.ofBitVec a ^^^ UInt32.ofBitVec b = UInt32.ofBitVec (a ^^^ b) := rfl

theorem enc_ofFn {n : ℕ} (f : Fin n → BitVec 32) : enc (Vector.ofFn f) = Array.ofFn fun i => UInt32.ofBitVec (f i) := by
  apply Array.ext <;> simp [enc]

theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem <;> simp

theorem foldl_finRange {β : Type} (n : ℕ) (f : β → Fin n → β) (b : β) :
    (List.finRange n).foldl f b = (List.range' 0 n).foldl (fun b r => if h : r < n then f b ⟨r, h⟩ else b) b := by
  rw [← map_val_finRange, List.foldl_map]
  congr
  funext b i
  simp

/-- The specification's compression is RFC 7693's `F`, counter and finalization flag included. -/
theorem compress_enc (h : Vector (BitVec 32) 8) (m : Vector (BitVec 32) 16) (c : UInt64) (last : Bool) :
    (spec_private% EthCryptographySpecs.Xmss.Blake2s.compress) (enc h) (enc m) c last =
      enc (F h m c.toBitVec last) := by
  delta_private compress
  rw [iv_enc, enc_append]
  have hs : [:10].size = 10 := rfl
  have h32 : ∀ x : BitVec 64, x >>> (UInt64.toBitVec 32 % 64) = x >>> 32 := fun x => rfl
  cases last <;>
  · simp (disch := omega) only [Id.run, enc_get, enc_set, Std.Legacy.Range.forIn_eq_forIn_range',
      List.forIn_pure_yield_eq_foldl, Bool.false_eq_true, if_false, if_true, pure_bind, hs]
    rw [foldl_enc (List.range' 0 10) _ (fun v r => if h : r < 10 then round v m SIGMA[r] else v) enc]
    · simp (disch := omega) only [enc_get, ofBitVec_xor, LeanVMCircuits.Blake2s.Rfc7693.F, enc_ofFn, h32,
        foldl_finRange,
        UInt32.toBitVec_xor, Blake2s.Internal.counterLow, Blake2s.Internal.counterHigh, UInt64.toBitVec_toUInt32,
        UInt64.toBitVec_shiftRight, UInt32.toBitVec_not, BitVec.xor_allOnes, if_true, if_false, Bool.false_eq_true]
      rfl
    · intro v r hr
      have hr' : r < 10 := by simp at hr; omega
      rw [dif_pos hr']
      simp (disch := omega) only [sched _ hr', enc_get, mix_enc]
      rfl

/-! ## Blocks, counters and the digest -/

theorem or32_congr (f g : ℕ → UInt8) (h : ∀ t < 4, f t = g t) : or32 f = or32 g := by
  simp [or32, h]

/-- Block `j` of the bytes of words, read as the specification reads it, is `Statement.block`. -/
theorem blockWords_eq (ws : List (BitVec 64)) (j : ℕ) :
    (spec_private% EthCryptographySpecs.Xmss.Blake2s.blockWords) (wordsBytes ws) (Blake2s.Internal.blockOffset j) =
      enc (block ws j) := by
  delta_private blockWords
  apply Array.ext
  · simp [enc]
  · intro r h1 h2
    have hr : r < 16 := by simpa using h1
    have hl : ∀ o, Blake2s.Internal.little32 (wordsBytes ws) o = or32 fun t => byteAt ws (o + t) := by
      intro o
      simp only [Blake2s.Internal.little32, wordsBytes_getD, or32, Nat.add_zero]
    simp only [Array.getElem_ofFn, hl, enc, Array.getElem_map, Vector.getElem_toArray, block, Vector.getElem_ofFn]
    rw [← or32_bytes]
    apply or32_congr
    intro t ht
    rw [byteOf_half _ _ _ (by omega) ht]
    simp only [byteAt, Blake2s.Internal.blockOffset]
    congr 2 <;> omega

theorem byteOf_digest (h : Vector (BitVec 32) 8) (k : Fin 4) (b : ℕ) (hb : b < 8) :
    byteOf (digest h k) b = byteOf (h[2 * k.val + b / 4]'(by omega)) (b % 4) := by
  have := byteOf_half (digest h k) (b / 4) (b % 4) (by omega) (by omega)
  rw [show 4 * (b / 4) + b % 4 = b by omega, half_digest _ _ _ (by omega)] at this
  exact this.symm

/-- The specification's serialization of a chaining value is the bytes of its `digest` words. -/
theorem stateBytes_eq (h : Vector (BitVec 32) 8) :
    (spec_private% EthCryptographySpecs.Xmss.Blake2s.stateBytes) (enc h) = wordsVec 32 (List.ofFn (digest h)) := by
  delta_private stateBytes
  apply Vector.ext
  intro i hi
  have hq : ∀ j : Fin 32, (j / 4).val = j.val / 4 := by intro j; rw [Fin.div_val]; rfl
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Blake2s.Internal.wordBytes, wordsVec, byteAt, hq, Fin.val_mk]
  have hx : ∀ (a : Array UInt32) (j : Fin 32), a[j]! = a[j.val]! := fun _ _ => rfl
  simp only [hx, hq, Fin.val_mk]
  rw [enc_get _ (i / 4) (by omega), shift_toUInt8 _ _ (by omega)]
  have hw : wordAt (List.ofFn (digest h)) (i / 8) = digest h ⟨i / 8, by omega⟩ := by
    simp [wordAt, List.getD_eq_getElem?_getD, show i / 8 < 4 by omega]
    rcases (by omega : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3) with e | e | e | e <;> simp [e]
  rw [hw, byteOf_digest _ _ _ (by omega)]
  have e1 : 2 * (i / 8) + i % 8 / 4 = i / 4 := by omega
  have e2 : i % 8 % 4 = i % 4 := by omega
  simp only [e1, e2, UInt32.toBitVec_ofBitVec]

/-- The specification's block loop from block `i` is `blocksFrom` at the same counters. -/
theorem drive (ws : List (BitVec 64)) (f : Array UInt32 → ℕ → Array UInt32)
    (hf : ∀ h b, b < nBlocks ws.length → f (enc h) b = enc (F h (block ws b)
        (BitVec.ofNat 64 (if b + 1 = nBlocks ws.length then 8 * ws.length else 64 * (b + 1)))
        (b + 1 == nBlocks ws.length))) :
    ∀ k i h, i + k + 1 = nBlocks ws.length →
      (List.range' i (k + 1)).foldl f (enc h) =
        enc (blocksFrom (BitVec.ofNat 64 (8 * ws.length)) h i (block ws i) ((List.range' (i + 1) k).map (block ws)))
  | 0, i, h, hk => by
    simp only [List.range'_succ, List.range'_zero, List.foldl_cons, List.foldl_nil, List.map_nil, blocksFrom]
    rw [hf h i (by omega)]
    simp [show i + 1 = nBlocks ws.length by omega]
  | k + 1, i, h, hk => by
    rw [List.range'_succ, List.foldl_cons, hf h i (by omega), drive ws f hf k (i + 1) _ (by omega),
      List.range'_succ, List.map_cons, blocksFrom]
    have : (i + 1 == nBlocks ws.length) = false := by simp; omega
    have hne : i + 1 ≠ nBlocks ws.length := by omega
    rw [this, if_neg hne]

/-- The specification's BLAKE2s of the bytes of words is the bytes of the words of `hashWords`. -/
theorem hash_wordsBytes (ws : List (BitVec 64)) :
    Blake2s.hash (wordsBytes ws) = wordsVec 32 (List.ofFn (digest (hashWords ws))) := by
  have hN : Blake2s.Internal.blockCount (wordsBytes ws).size = nBlocks ws.length := by
    simp only [Blake2s.Internal.blockCount, nBlocks, wordsBytes_size]
    omega
  have hinit : (spec_private% EthCryptographySpecs.Xmss.Blake2s.IV).set! 0
      ((spec_private% EthCryptographySpecs.Xmss.Blake2s.IV)[0]! ^^^ 16842784) = enc paramIV := by
    decide +kernel
  have hs : ∀ n, [:n].size = n := by intro n; simp [Std.Legacy.Range.size]
  simp only [Blake2s.hash]
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    pure_bind, hN, hinit, hs]
  have hpos : 0 < nBlocks ws.length := by simp [nBlocks]
  rw [show List.range' 0 (nBlocks ws.length) = List.range' 0 (nBlocks ws.length - 1 + 1) by
    rw [Nat.sub_add_cancel hpos]]
  rw [drive ws _ ?hf (nBlocks ws.length - 1) 0 _ (by omega)]
  case hf =>
    intro h b hb
    rw [blockWords_eq, compress_enc, UInt64.toBitVec_ofNat']
    congr 3
    simp only [Blake2s.Internal.blockCounter, Blake2s.Internal.blockOffset,
      Blake2s.Internal.bytesInBlock, wordsBytes_size]
    by_cases hc : b + 1 = nBlocks ws.length
    · rw [if_pos hc]; simp only [nBlocks] at hb hc; omega
    · rw [if_neg hc]; simp only [nBlocks] at hb hc; omega
  rw [stateBytes_eq]
  have hh : hashWords ws = blocksFrom (BitVec.ofNat 64 (8 * ws.length)) paramIV 0 (block ws 0)
      ((List.range' (0 + 1) (nBlocks ws.length - 1)).map (block ws)) := by
    simp only [hashWords, blake2s256, List.range'_eq_map_range, List.map_map]
    congr 2
    funext j
    simp [Nat.add_comm]
  rw [hh]
  rfl

end LeanVMCircuits.Xmss.Spec
