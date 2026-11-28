module

public import NativeRustcArm.Spec.Keccak
public import NativeRustcArm.Sym

/-!
# Bytes in memory, for `Hasher::update` and `Hasher::finalize`

The bytes `bytesOf` reads (`getD_bytesOf`, `bytesOf_of_bytesAt`, `bytesOf_congr`,
`bytesOf_add`), the bytes of a write (`getD_writeAt`), of stored and loaded 64-bit values
(`wordBytes_ofBitVec`, `byteOf_xor`, `byteOf_ofBytes`), of `xorBlock` (`getD_xorBlock`), and the
addresses a range holds (`inRange_add_iff`).
-/

namespace NativeRustcArm.Hasher

open NativeRustc NativeRustc.Keccak LeanVM.Semantics LeanVM.Protocol.KeccakHash Native.Keccak Native.Keccak.Proof
open NativeRustcArm.Sym

public section

theorem ite_pos' {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by
  simp [h]

theorem ite_neg' {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by
  simp [h]

/-! ## Lists of bytes -/

/-- Two byte lists of one length with the same bytes. -/
theorem ext_getD {l l' : List UInt8} (hl : l.length = l'.length)
    (h : ∀ i < l.length, l.getD i 0 = l'.getD i 0) : l = l' :=
  List.ext_getElem hl fun i h1 h2 => by
    have := h i h1
    simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem getElem_eq_getD (l : List UInt8) {i : Nat} (h : i < l.length) : l[i] = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

theorem length_writeAt {h src : List UInt8} {off : Nat} (hl : off + src.length ≤ h.length) :
    (writeAt h off src).length = h.length := by
  simp only [writeAt, List.length_append, List.length_take, List.length_drop]
  omega

/-- **A byte after a write**: `src`'s where it covers, else `h`'s. -/
theorem getD_writeAt (h src : List UInt8) (off i : Nat) (hl : off + src.length ≤ h.length) :
    (writeAt h off src).getD i 0 =
      if off ≤ i ∧ i < off + src.length then src.getD (i - off) 0 else h.getD i 0 := by
  simp only [writeAt, List.getD_eq_getElem?_getD, List.append_assoc]
  by_cases h1 : i < off
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h1,
      ite_neg' (by omega)]
  · rw [List.getElem?_append_right (by simp; omega), List.length_take,
      Nat.min_eq_left (by omega)]
    by_cases h2 : i < off + src.length
    · rw [List.getElem?_append_left (by omega), ite_pos' ⟨by omega, h2⟩]
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop, ite_neg' (by omega)]
      congr 2
      omega

/-! ## `bytesOf` -/

theorem length_bytesOf (d : DataMem) (a : BitVec 64) (n : Nat) : (bytesOf d a n).length = n := by
  simp [bytesOf]

theorem getD_bytesOf (d : DataMem) (a : BitVec 64) {n i : Nat} (hi : i < n) :
    (bytesOf d a n).getD i 0 = (d.get? (a + BitVec.ofNat 64 i)).getD 0 := by
  simp [bytesOf, List.getD_eq_getElem?_getD, hi]

/-- The bytes `BytesAt` gives. -/
theorem bytesOf_of_bytesAt {d : DataMem} {a : BitVec 64} {bs : List UInt8} (h : BytesAt d a bs) :
    bytesOf d a bs.length = bs :=
  ext_getD (length_bytesOf ..) fun i hi => by
    rw [length_bytesOf] at hi
    rw [getD_bytesOf _ _ hi, h i hi]
    simp [List.getD_eq_getElem?_getD, hi]

/-- `BytesAt` of the bytes `bytesOf` reads, where they are mapped. -/
theorem bytesAt_bytesOf {d : DataMem} {a : BitVec 64} {n : Nat} (h : Mapped d a n) :
    BytesAt d a (bytesOf d a n) := by
  intro i hi
  rw [length_bytesOf] at hi
  have := h i hi
  simp only [bytesOf, List.getElem_map, List.getElem_range]
  revert this
  cases d.get? (a + BitVec.ofNat 64 i) <;> simp

theorem bytesOf_congr {d d' : DataMem} {a : BitVec 64} {n : Nat}
    (h : ∀ i < n, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i)) :
    bytesOf d' a n = bytesOf d a n := by
  unfold bytesOf
  apply List.map_congr_left
  intro i hi
  rw [h i (List.mem_range.mp hi)]

theorem add_ofNat_add (a : BitVec 64) (c i : Nat) :
    a + BitVec.ofNat 64 c + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (c + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The bytes from `a + c` are a slice of those from `a`. -/
theorem bytesOf_add (d : DataMem) (a : BitVec 64) {c t n : Nat} (h : c + t ≤ n) :
    bytesOf d (a + BitVec.ofNat 64 c) t = ((bytesOf d a n).drop c).take t :=
  ext_getD (by simp [length_bytesOf]; omega) fun i hi => by
    rw [length_bytesOf] at hi
    rw [getD_bytesOf _ _ hi, getD_take, ite_pos' hi, getD_drop, getD_bytesOf _ _ (by omega),
      add_ofNat_add]

/-! ## Addresses -/

theorem toNat_add_ofNat' {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **The bytes a range from `a + o` holds**, as offsets from `a`. -/
theorem inRange_add_iff {a : BitVec 64} {o t i : Nat} (hi : a.toNat + i < 2 ^ 64)
    (ho : a.toNat + o + t ≤ 2 ^ 64) (ht : 0 < t) :
    InRange (a + BitVec.ofNat 64 o) t (a + BitVec.ofNat 64 i) ↔ o ≤ i ∧ i < o + t := by
  unfold InRange
  rw [BitVec.toNat_sub, toNat_add_ofNat' hi, toNat_add_ofNat' (by omega)]
  constructor
  · intro h
    by_cases hoi : o ≤ i
    · omega
    · rw [show 2 ^ 64 - (a.toNat + o) + (a.toNat + i) = 2 ^ 64 - (o - i) by omega,
        Nat.mod_eq_of_lt (by omega)] at h
      omega
  · intro h
    rw [show 2 ^ 64 - (a.toNat + o) + (a.toNat + i) = (i - o) + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem inRange_self_iff {a : BitVec 64} {t i : Nat} (hi : a.toNat + i < 2 ^ 64)
    (ho : a.toNat + t ≤ 2 ^ 64) (ht : 0 < t) :
    InRange a t (a + BitVec.ofNat 64 i) ↔ i < t := by
  have := inRange_add_iff (o := 0) hi (by simpa using ho) ht
  simpa using this

/-! ## Bytes of 64-bit values -/

theorem byteOf_xor (x y : BitVec 64) (t : Nat) : byteOf (x ^^^ y) t = byteOf x t ^^^ byteOf y t := by
  apply UInt8.toNat_inj.mp
  simp only [byteOf, UInt8.toNat_ofNat', UInt8.toNat_xor, BitVec.toNat_xor]
  apply Nat.eq_of_testBit_eq
  intro j
  show ((x.toNat ^^^ y.toNat) / 2 ^ (8 * t) % 2 ^ 8).testBit j =
    ((x.toNat / 2 ^ (8 * t) % 2 ^ 8) ^^^ (y.toNat / 2 ^ (8 * t) % 2 ^ 8)).testBit j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  by_cases hj : j < 8 <;> simp [hj]

/-- A word's bytes are its `byteOf`s. -/
theorem wordBytes_ofBitVec (x : BitVec 64) :
    wordBytes (UInt64.ofBitVec x) = (List.range 8).map (byteOf x) := by
  apply List.ext_getElem (by simp [wordBytes])
  intro i h1 h2
  have hi : i < 8 := by simpa using h2
  simp only [wordBytes, List.getElem_map, List.getElem_range, byteOf]
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, show 8 * i % 2 ^ 64 % 64 = 8 * i by omega]
  rfl

theorem natOfBytes_digit : ∀ (bs : List UInt8) (t : Nat),
    Nat.ofBytes bs / 2 ^ (8 * t) % 256 = (bs.getD t 0).toNat
  | [], t => by simp [Nat.ofBytes]
  | b :: bs, 0 => by
    show (Nat.ofBytes bs * 256 + b.toNat) / 1 % 256 = b.toNat
    have := b.toNat_lt
    omega
  | b :: bs, t + 1 => by
    show (Nat.ofBytes bs * 256 + b.toNat) / 2 ^ (8 * (t + 1)) % 256 = (bs.getD t 0).toNat
    rw [show 8 * (t + 1) = 8 + 8 * t by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show (2 : Nat) ^ 8 = 256 from rfl, show (Nat.ofBytes bs * 256 + b.toNat) / 256 =
        Nat.ofBytes bs by have := b.toNat_lt; omega]
    exact natOfBytes_digit bs t

/-- **The bytes of a loaded value**: byte `t` of the integer of `bs` is `bs`'s. -/
theorem byteOf_ofBytes (bs : List UInt8) (t : Nat) :
    byteOf (BitVec.ofInt 64 (Int.ofBytes bs)) t =
      UInt8.ofNat (Nat.ofBytes bs % 2 ^ 64 / 2 ^ (8 * t)) := by
  rw [ofBytes_natCast, BitVec.ofInt_natCast]
  simp [byteOf, BitVec.toNat_ofNat]

theorem byteOf_ofBytes_of_le (bs : List UInt8) (hn : bs.length ≤ 8) (t : Nat) :
    byteOf (BitVec.ofInt 64 (Int.ofBytes bs)) t = bs.getD t 0 := by
  rw [byteOf_ofBytes]
  have hlt : Nat.ofBytes bs < 2 ^ 64 := by
    have h := Int.ofBytes_lt bs
    rw [ofBytes_natCast] at h
    have h' : Nat.ofBytes bs < 256 ^ bs.length := by exact_mod_cast h
    have h2 : (256 : Nat) ^ bs.length ≤ 2 ^ 64 :=
      le_trans (Nat.pow_le_pow_right (by decide) hn) (by decide)
    omega
  rw [Nat.mod_eq_of_lt hlt]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', ← natOfBytes_digit bs t]

/-- The lane of the 8 bytes `bs` is the value Kraken loads from them. -/
theorem lane_ofBytes {bs : List UInt8} (h : bs.length = 8) :
    littleEndianLane bs 0 = UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes bs)) := by
  have hw : wordBytes (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes bs))) = bs := by
    rw [wordBytes_ofBitVec]
    apply List.ext_getElem (by simp [h])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [byteOf_ofBytes_of_le _ (by omega)]
    simp [List.getD_eq_getElem?_getD, h2]
  conv_lhs => rw [← hw]
  exact littleEndianLane_wordBytes _

/-- `buf_len` after a store of `w` into it. -/
theorem bufLen_writeAt {X : List UInt8} (hX : X.length = 344) (w : UInt64) :
    bufLen (writeAt X 336 (wordBytes w)) = w.toNat := by
  rw [bufLen, writeAt, length_wordBytes,
    List.drop_eq_nil_of_le (as := X) (i := 336 + 8) (by omega), List.append_nil,
    List.drop_left' (by simp; omega), littleEndianLane_wordBytes]

/-- `buf_len` as the value Kraken loads from its bytes. -/
theorem bufLen_ofBytes {H : List UInt8} (h : H.length = 344) :
    (BitVec.ofInt 64 (Int.ofBytes (H.drop 336))).toNat = bufLen H := by
  rw [bufLen, lane_ofBytes (by simp [h])]
  rfl

/-- The environment's `n` bytes at `off` in a region based at `a`, as `bytesOf` reads them. -/
theorem load_eq_bytesOf (env : Env) {r off n N : Nat} {a : BitVec 64} (hb : env.base r = a)
    (hN : off + n ≤ N) (hmap : Mapped env.mem0 a N) :
    env.load r off n = BitVec.ofInt 64 (Int.ofBytes (((bytesOf env.mem0 a N).drop off).take n)) := by
  refine Env.load_of_bytesAt (by simp [length_bytesOf]; omega) ?_
  rw [hb, ← bytesOf_add _ _ hN]
  exact bytesAt_bytesOf fun i hi => by rw [add_ofNat_add]; exact hmap _ (by omega)

/-- The 64-bit value of a value's 8 bytes. -/
theorem ofInt_ofBytes_byteOf (x : BitVec 64) :
    BitVec.ofInt 64 (Int.ofBytes ((List.range 8).map (byteOf x))) = x := by
  have := ofBytes_byteOf x 0 8
  simp only [Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  rw [this, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := x.isLt
  omega

/-- The addresses a block's writes into region 0 cover are in region 0. -/
theorem written_hasher {m : MachineData} [Labels] {h : BitVec 64} {sz : Nat}
    {rest : List (BitVec 64 × Nat)} {S : SState} {p : BitVec 64}
    (hS : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ sz)
    (hw : Written (Env.ofMachine m ((h, sz) :: rest)) S p) :
    h.toNat ≤ p.toNat ∧ p.toNat < h.toNat + sz := by
  obtain ⟨w, hw, b, sz, hb, h1, h2⟩ := hw
  obtain ⟨hr, hoff⟩ := hS w hw
  rw [hr] at hb
  simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
    Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  omega

/-- The addresses a block's writes into region `r` cover are in region `r`. -/
theorem written_in {m : MachineData} [Labels] {rs : List (BitVec 64 × Nat)} {r : Nat}
    {h : BitVec 64} {sz : Nat} (hr : rs[r]? = some (h, sz)) {S : SState} {p : BitVec 64}
    (hS : ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ sz) (hw : Written (Env.ofMachine m rs) S p) :
    h.toNat ≤ p.toNat ∧ p.toNat < h.toNat + sz := by
  obtain ⟨w, hw, b, sz', hb, h1, h2⟩ := hw
  obtain ⟨hwr, hoff⟩ := hS w hw
  rw [hwr] at hb
  simp only [Env.ofMachine_regions, hr, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  omega

/-- The first `t` of the `n` bytes from `a`. -/
theorem bytesOf_take (d : DataMem) (a : BitVec 64) {t n : Nat} (h : t ≤ n) :
    bytesOf d a t = (bytesOf d a n).take t :=
  ext_getD (by simp [length_bytesOf]; omega) fun i hi => by
    rw [length_bytesOf] at hi
    rw [getD_bytesOf _ _ hi, getD_take, ite_pos' hi, getD_bytesOf _ _ (by omega)]

/-! ## Reading registers -/

/-- A register a block leaves as its atom keeps the value it had. -/
theorem Match.reg_atom [Labels] {m m' : MachineData} {rs : List (BitVec 64 × Nat)}
    {vs : Nat → BitVec 64} {S : SState} (hm : Match (Env.ofMachine m rs vs) S m') {r : XReg}
    (h : S.reg r = some (.reg r)) : m'.regs.getXReg r = m.regs.getXReg r :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

/-! ## `xorBlock` -/

theorem laneOf_byte (f : Nat → UInt8) {k : Nat} (hk : k < 8) :
    ((laneOf f) >>> (8 * k).toUInt64).toUInt8 = f k := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro j
  have h8 : (8 * k).toUInt64.toNat % 64 = 8 * k := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases hj : j < 8
  · rw [testBit_laneOf, show (8 * k + j) / 8 = k by omega, show (8 * k + j) % 8 = j by omega]
    simp [hj, show 8 * k + j < 64 by omega]
  · simp [hj, testBit_byte _ (show 8 ≤ j by omega)]

theorem getD_stateBytes (A : KeccakState) (p : Nat) :
    (stateBytes A).getD p 0 = (Keccak.lane A (p / 8) >>> (8 * (p % 8)).toUInt64).toUInt8 := by
  rw [stateBytes, getD_wordsBytes]
  congr 2
  simp [Keccak.lane, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

/-- **A byte of `xorBlock`**: the state's, XOR the block's in the rate. -/
theorem getD_xorBlock (st blk : List UInt8) {j : Nat} (hj : j < 200) :
    (NativeRustc.Keccak.xorBlock st blk).getD j 0 =
      if j < 136 then st.getD j 0 ^^^ blk.getD j 0 else st.getD j 0 := by
  rw [NativeRustc.Keccak.xorBlock, getD_stateBytes, lane_xorRate _ _ (by omega), lane_stateOf _ (by omega)]
  have hj8 : 8 * (j / 8) + j % 8 = j := by omega
  by_cases h : j < 136
  · rw [ite_pos' (by omega), ite_pos' h, littleEndianLane_eq, littleEndianLane_eq, ← laneOf_xor,
      laneOf_byte _ (by omega), hj8]
  · rw [ite_neg' (by omega), ite_neg' h, littleEndianLane_eq, laneOf_byte _ (by omega), hj8]

/-! ## The model -/

/-- A turn of `update`'s loop on no input keeps the hasher. -/
theorem updateStep_nil {h a : List UInt8} (hh : HasherHolds h a) : (updateStep h []).1 = h := by
  obtain ⟨rest, hr, rfl⟩ := hh
  have hT : (a.drop (136 * (a.length / 136))).length = a.length % 136 := by simp; omega
  rw [updateStep_split _ _ _ [] (length_stateBytes _) hT hr (Nat.mod_lt _ (by omega))]
  simp [show ¬(a.length % 136 = 136) by omega]

/-- **A turn of `update`'s loop on the input past its first `c` bytes** absorbs the
`min (136 - bufLen h) (D.length - c)` bytes it takes. -/
theorem holds_updateStep_drop {H0 H D : List UInt8} {c : Nat} (hc : c ≤ D.length)
    (hH : ∀ a, HasherHolds H0 a → HasherHolds H (a ++ D.take c)) (a : List UInt8)
    (ha : HasherHolds H0 a) :
    HasherHolds (updateStep H (D.drop c)).1
      (a ++ D.take (c + min (136 - bufLen H) (D.length - c))) := by
  have hh := hH a ha
  by_cases hD : c = D.length
  · subst hD
    rw [List.drop_length, updateStep_nil hh, Nat.sub_self, Nat.min_zero, Nat.add_zero]
    exact hh
  · obtain ⟨k, hk0, hkl, hrest, hh'⟩ := holds_updateStep (data := D.drop c) hh (by rw [ne_eq, List.drop_eq_nil_iff]; omega)
    have hk : k = min (136 - bufLen H) (D.length - c) := by
      have h2 : (updateStep H (D.drop c)).2 =
          (D.drop c).drop (min (136 - bufLen H) (D.drop c).length) := by
        simp only [updateStep]
        split <;> rfl
      rw [hrest] at h2
      have := congrArg List.length h2
      simp only [List.length_drop] at this hkl
      omega
    rw [List.append_assoc, ← List.take_add, hk] at hh'
    exact hh'

end

end NativeRustcArm.Hasher
