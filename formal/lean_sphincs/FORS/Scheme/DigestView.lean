import FORS.Scheme.Uniform
import Mathlib.Data.BitVec

/-!
The full view of a message digest (its index and the leaf index of each of the `k` FORS trees) is a
bijection, so a uniform digest gives a uniform view; and uniform digest calls give a uniform digest,
since FIPS 205's Algorithm 19 reads each digest bit from a distinct bit of the calls. Coverage of a
view by disclosed secrets: the selected leaf of every tree is disclosed.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace FORS.Concrete

variable [Params]

abbrev FullDigestView := Index × (FTree → FLeaf)

def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, digestLeaves digest)

/-- Two digests with the same bits in a window agree at every position of the window. -/
theorem getLsbD_of_extract {left right : MessageDigest} {offset len position : Nat}
    (h : left.extractLsb' offset len = right.extractLsb' offset len)
    (hlow : offset ≤ position) (hhigh : position < offset + len) :
    left.getLsbD position = right.getLsbD position := by
  have hwithin : position - offset < len := by omega
  have hbit := congrArg (fun bits : BitVec len => bits.getLsbD (position - offset)) h
  simp only [BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and] at hbit
  rwa [show offset + (position - offset) = position by omega] at hbit

/-- The index and the `k` leaf indices hold every bit of the digest: bits `0 .. h - 1` are the index,
and bits `h + a κ .. h + a κ + a - 1` the leaf of tree `κ`. -/
theorem fullDigestView_injective : Function.Injective fullDigestView := by
  intro left right heq
  have hidx : left.extractLsb' 0 totalHeight = right.extractLsb' 0 totalHeight := by
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin view.1) heq
    simpa only [fullDigestView, digestIndex, BitVec.ofFin_toFin] using hcomponent
  have hleaf : ∀ κ : FTree,
      left.extractLsb' (leafOffset κ) forsHeight = right.extractLsb' (leafOffset κ) forsHeight := by
    intro κ
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin (view.2 κ)) heq
    simpa only [fullDigestView, digestLeaves, BitVec.ofFin_toFin] using hcomponent
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hlow : position < totalHeight
  · exact getLsbD_of_extract hidx (Nat.zero_le _) (by omega)
  · have ha := forsHeight_pos
    have hk : (position - totalHeight) / forsHeight < forsTrees := by
      have : position - totalHeight < forsTrees * forsHeight := by
        unfold messageDigestBits at hposition; omega
      exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at this)
    let κ : FTree := ⟨(position - totalHeight) / forsHeight, hk⟩
    refine getLsbD_of_extract (hleaf κ) ?_ ?_
    · have := Nat.div_mul_le_self (position - totalHeight) forsHeight
      simp only [leafOffset, κ]
      rw [mul_comm]
      omega
    · have := Nat.lt_div_mul_add (a := position - totalHeight) ha
      simp only [leafOffset, κ]
      rw [mul_comm]
      omega

theorem fullDigestView_bijective : Function.Bijective fullDigestView := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fullDigestView_injective, ?_⟩
  rw [card_bitVec, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  unfold messageDigestBits
  ring

theorem evalDist_fullDigestView_uniform :
    𝒟[fullDigestView <$> ($ᵗ MessageDigest : ProbComp MessageDigest)] =
    𝒟[($ᵗ FullDigestView : ProbComp FullDigestView)] :=
  evalDist_map_bijective_uniform_cross (α := MessageDigest) (β := FullDigestView)
    fullDigestView fullDigestView_bijective

/-! ### Reading the digest bit by bit

Bit `g` of the calls is bit `g % 256` of call `g / 256`, so byte `j` of `digestOutputBytes` holds bits
`8 j .. 8 j + 7`. Every bit of the digest is one bit of the calls (`digestSource`), and distinct bits of
the digest come from distinct bits of the calls (`digestTarget` inverts it). -/

/-- Bit `g` of the digest calls, call 0 in the low 256 bits. -/
def outputBit (outputs : DigestCall → HashOutput) (g : Nat) : Bool :=
  if h : g / 256 < digestCalls then (outputs ⟨g / 256, h⟩).getLsbD (g % 256) else false

theorem digestOutputBytes_eq (outputs : DigestCall → HashOutput) :
    digestOutputBytes outputs = List.ofFn (fun j : Fin (digestCalls * 32) =>
      UInt8.ofBitVec ((outputs ⟨j.val / 32, by have := j.isLt; omega⟩).extractLsb' (8 * (j.val % 32)) 8)) := by
  rw [List.ofFn_mul, digestOutputBytes]
  congr 1
  congr 1
  funext call
  unfold bytesLE
  congr 1
  funext i
  have h1 : (call.val * 32 + i.val) / 32 = call.val := by omega
  have h2 : (call.val * 32 + i.val) % 32 = i.val := by omega
  simp only [h1, h2, Fin.eta]
  rfl

theorem digestOutputBytes_length (outputs : DigestCall → HashOutput) :
    (digestOutputBytes outputs).length = digestCalls * 32 := by
  rw [digestOutputBytes_eq, List.length_ofFn]

theorem testBit_digestOutputByte (outputs : DigestCall → HashOutput) (j t : Nat) (ht : t < 8) :
    ((digestOutputBytes outputs).getD j 0).toNat.testBit t = outputBit outputs (8 * j + t) := by
  rw [digestOutputBytes_eq, List.getD_eq_getElem?_getD, List.getElem?_ofFn, outputBit]
  by_cases hj : j < digestCalls * 32
  · have hc : (8 * j + t) / 256 < digestCalls := by omega
    rw [dif_pos hj, dif_pos hc]
    have h1 : (8 * j + t) / 256 = j / 32 := by omega
    have h2 : (8 * j + t) % 256 = 8 * (j % 32) + t := by omega
    simp only [Option.getD_some, UInt8.toNat_ofBitVec, BitVec.testBit_toNat, BitVec.getLsbD_extractLsb', ht,
      decide_true, Bool.true_and, h1, h2]
  · have hc : ¬ (8 * j + t) / 256 < digestCalls := by omega
    rw [dif_neg hj, dif_neg hc]
    simp

/-- The bit of a byte string read least significant bit first that holds bit `p` of the string read most
significant bit first. -/
def msbPos (p : Nat) : Nat := 8 * (p / 8) + (7 - p % 8)

theorem msbBit_digestOutputBytes (outputs : DigestCall → HashOutput) (p : Nat) :
    msbBit (digestOutputBytes outputs) p = (outputBit outputs (msbPos p)).toNat := by
  rw [msbBit, ← Nat.toNat_testBit, testBit_digestOutputByte _ _ _ (by omega), msbPos]

theorem msbBit_lt (bytes : List UInt8) (p : Nat) : msbBit bytes p < 2 := Nat.mod_lt _ (by decide)

theorem msbField_succ (bytes : List UInt8) (offset width : Nat) :
    msbField bytes offset (width + 1) = 2 * msbField bytes offset width + msbBit bytes (offset + width) := by
  simp only [msbField, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem msbField_lt (bytes : List UInt8) (offset : Nat) : ∀ width, msbField bytes offset width < 2 ^ width
  | 0 => by simp [msbField]
  | width + 1 => by
    have := msbField_lt bytes offset width
    have := msbBit_lt bytes (offset + width)
    rw [msbField_succ, pow_succ]
    omega

/-- Bit `i` of a `base_2b` value is the string's bit `width - 1 - i` places after its offset. -/
theorem testBit_msbField (bytes : List UInt8) (offset : Nat) : ∀ width i : Nat,
    (msbField bytes offset width).testBit i =
      (decide (i < width) && decide (msbBit bytes (offset + (width - 1 - i)) = 1))
  | 0, i => by simp [msbField]
  | width + 1, 0 => by
      have hlt := msbBit_lt bytes (offset + width)
      have hmod : (2 * msbField bytes offset width + msbBit bytes (offset + width)) % 2 =
          msbBit bytes (offset + width) := by omega
      rw [msbField_succ, Nat.testBit_zero, hmod]
      simp
  | width + 1, i + 1 => by
      have hlt := msbBit_lt bytes (offset + width)
      have hdiv : (2 * msbField bytes offset width + msbBit bytes (offset + width)) / 2 =
          msbField bytes offset width := by omega
      rw [msbField_succ, Nat.testBit_succ, hdiv, testBit_msbField bytes offset width i]
      have hidx : width + 1 - 1 - (i + 1) = width - 1 - i := by omega
      rw [hidx]
      simp

theorem beInt_append (l : List UInt8) (x : UInt8) : beInt (l ++ [x]) = 2 ^ 8 * beInt l + x.toNat := by
  simp [beInt, List.foldl_append]

/-- Bit `i` of a big-endian integer is bit `i % 8` of its byte `i / 8` from the end. -/
theorem testBit_beInt (l : List UInt8) : ∀ i : Nat, (beInt l).testBit i =
    (decide (i < 8 * l.length) && (l.getD (l.length - 1 - i / 8) 0).toNat.testBit (i % 8)) := by
  induction l using List.reverseRecOn with
  | nil => intro i; simp [beInt]
  | append_singleton l x ih =>
    intro i
    rw [beInt_append, Nat.testBit_two_pow_mul_add _ x.toNat_lt, List.length_append, List.length_singleton]
    split_ifs with hi
    · have h0 : l.length + 1 - 1 - i / 8 = l.length := by omega
      have hx : (l ++ [x]).getD l.length 0 = x := by simp [List.getD_eq_getElem?_getD]
      have : i < 8 * (l.length + 1) := by omega
      rw [h0, hx, Nat.mod_eq_of_lt hi]
      simp [this]
    · rw [ih]
      by_cases hlt : i - 8 < 8 * l.length
      · have hi' : i < 8 * (l.length + 1) := by omega
        have h0 : l.length + 1 - 1 - i / 8 = l.length - 1 - (i - 8) / 8 := by omega
        have h1 : (i - 8) % 8 = i % 8 := by omega
        have hx : (l ++ [x]).getD (l.length - 1 - (i - 8) / 8) 0 = l.getD (l.length - 1 - (i - 8) / 8) 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show l.length - 1 - (i - 8) / 8 < l.length by omega)]
        rw [h0, h1, hx]
        simp [hlt, hi']
      · have hi' : ¬ i < 8 * (l.length + 1) := by omega
        simp [hlt, hi']

theorem getD_take_drop (bytes : List UInt8) (s t j : Nat) (hj : j < t) :
    ((bytes.drop s).take t).getD j 0 = bytes.getD (s + j) 0 := by
  simp [List.getD_eq_getElem?_getD, hj, List.getElem?_drop]

theorem length_take_drop (bytes : List UInt8) (s t : Nat) (h : s + t ≤ bytes.length) :
    ((bytes.drop s).take t).length = t := by
  simp only [List.length_take, List.length_drop]
  omega

/-- `k` values of `a` bits packed least significant first stay below `2^(a k)`. -/
theorem packed_lt (a : Nat) : ∀ {k : Nat} (f : Fin k → Nat), (∀ κ, f κ < 2 ^ a) →
    ∑ κ : Fin k, f κ * 2 ^ (a * κ.val) < 2 ^ (a * k)
  | 0, _, _ => by simp
  | k + 1, f, hf => by
    rw [Fin.sum_univ_castSucc]
    have ih := packed_lt a (fun κ : Fin k => f κ.castSucc) (fun κ => hf _)
    have hl : (f (Fin.last k) + 1) * 2 ^ (a * k) ≤ 2 ^ a * 2 ^ (a * k) :=
      Nat.mul_le_mul_right _ (hf (Fin.last k))
    simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
    rw [show a * (k + 1) = a + a * k by ring, pow_add]
    rw [Nat.add_mul, Nat.one_mul] at hl
    omega

/-- Bit `i` of `k` packed values of `a` bits is bit `i % a` of value `i / a`. -/
theorem testBit_packed (a : Nat) (ha : 0 < a) : ∀ {k : Nat} (f : Fin k → Nat), (∀ κ, f κ < 2 ^ a) →
    ∀ i : Nat, (∑ κ : Fin k, f κ * 2 ^ (a * κ.val)).testBit i =
      if hi : i / a < k then (f ⟨i / a, hi⟩).testBit (i % a) else false
  | 0, _, _, i => by simp
  | k + 1, f, hf, i => by
    rw [Fin.sum_univ_castSucc]
    have hlow := packed_lt a (fun κ : Fin k => f κ.castSucc) (fun κ => hf _)
    have ih := testBit_packed a ha (fun κ : Fin k => f κ.castSucc) (fun κ => hf _) i
    simp only [Fin.val_castSucc, Fin.val_last] at hlow ih ⊢
    rw [add_comm, mul_comm, Nat.testBit_two_pow_mul_add _ hlow]
    have hdm := Nat.div_add_mod i a
    split_ifs with h1 h2 h2
    · have h3 : i / a < k := (Nat.div_lt_iff_lt_mul ha).2 (by rw [mul_comm]; exact h1)
      rw [ih, dif_pos h3]
      rfl
    · exact absurd (Nat.lt_succ_of_lt ((Nat.div_lt_iff_lt_mul ha).2 (by rw [mul_comm]; exact h1))) h2
    · have h3 : i / a = k := by
        apply Nat.div_eq_of_lt_le
        · rw [mul_comm]; omega
        · have := (Nat.div_lt_iff_lt_mul ha).1 h2
          rw [Nat.succ_mul]; rw [Nat.add_mul, one_mul] at this; omega
      have h4 : i % a = i - a * k := by rw [h3] at hdm; omega
      have h5 : (⟨i / a, h2⟩ : Fin (k + 1)) = Fin.last k := Fin.ext h3
      rw [h5, h4]
    · have h3 : (k + 1) * a ≤ i := (Nat.le_div_iff_mul_le ha).1 (by omega)
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le (hf _) (Nat.pow_le_pow_right (by decide) (by rw [Nat.add_mul, one_mul, mul_comm k a] at h3; omega))

theorem digestIndexValue_lt (bytes : List UInt8) : digestIndexValue bytes < 2 ^ totalHeight := by
  have hb := bottomHeight_le
  unfold digestIndexValue
  have h1 := Nat.mod_lt (beInt ((bytes.drop mdBytes).take treeIndexBytes)) (Nat.two_pow_pos (totalHeight - bottomHeight))
  have h2 := Nat.mod_lt (beInt ((bytes.drop (mdBytes + treeIndexBytes)).take leafIndexBytes)) (Nat.two_pow_pos bottomHeight)
  have h3 : (beInt ((bytes.drop mdBytes).take treeIndexBytes) % 2 ^ (totalHeight - bottomHeight) + 1) * 2 ^ bottomHeight ≤
      2 ^ (totalHeight - bottomHeight) * 2 ^ bottomHeight := Nat.mul_le_mul_right _ h1
  rw [← pow_add, Nat.sub_add_cancel hb, Nat.add_mul, one_mul] at h3
  omega

theorem testBit_digestIndexValue (bytes : List UInt8) (q : Nat) : (digestIndexValue bytes).testBit q =
    if q < bottomHeight then (beInt ((bytes.drop (mdBytes + treeIndexBytes)).take leafIndexBytes)).testBit q
    else (decide (q - bottomHeight < totalHeight - bottomHeight) &&
      (beInt ((bytes.drop mdBytes).take treeIndexBytes)).testBit (q - bottomHeight)) := by
  unfold digestIndexValue
  rw [mul_comm, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)), Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow]
  split_ifs with h <;> simp [h]

theorem testBit_digestFieldsValue (bytes : List UInt8) (q : Nat) : (digestFieldsValue bytes).testBit q =
    if q < totalHeight then (digestIndexValue bytes).testBit q
    else if _ : (q - totalHeight) / forsHeight < forsTrees then
      (msbField bytes (forsHeight * ((q - totalHeight) / forsHeight)) forsHeight).testBit
        ((q - totalHeight) % forsHeight)
    else false := by
  have hsum : ∑ κ : FTree, msbField bytes (forsHeight * κ.val) forsHeight * 2 ^ (totalHeight + forsHeight * κ.val) =
      2 ^ totalHeight * ∑ κ : FTree, msbField bytes (forsHeight * κ.val) forsHeight * 2 ^ (forsHeight * κ.val) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [pow_add]
    ring
  have hfield : ∀ κ : FTree, msbField bytes (forsHeight * κ.val) forsHeight < 2 ^ forsHeight := fun κ =>
    msbField_lt bytes _ forsHeight
  have hp := testBit_packed forsHeight forsHeight_pos
    (fun κ : FTree => msbField bytes (forsHeight * κ.val) forsHeight) hfield (q - totalHeight)
  rw [digestFieldsValue, hsum, add_comm, Nat.testBit_two_pow_mul_add _ (digestIndexValue_lt bytes)]
  by_cases h : q < totalHeight
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact hp

/-- The FORS leaf bits, `base_2b` reads them: digest bit `q ≥ h` is bit `forsBit q` of the string read most
significant bit first. -/
def forsBit (q : Nat) : Nat :=
  forsHeight * ((q - totalHeight) / forsHeight) + (forsHeight - 1 - (q - totalHeight) % forsHeight)

/-- The digest bit that bit `p` of the leaf string, read most significant bit first, lands at. -/
def forsTarget (p : Nat) : Nat :=
  totalHeight + forsHeight * (p / forsHeight) + (forsHeight - 1 - p % forsHeight)

theorem forsBit_lt {q : Nat} (hlow : totalHeight ≤ q) (hq : q < messageDigestBits) :
    forsBit q < forsTrees * forsHeight := by
  have ha := forsHeight_pos
  unfold messageDigestBits at hq
  have hr := Nat.mod_lt (q - totalHeight) ha
  have hκ : (q - totalHeight) / forsHeight < forsTrees := (Nat.div_lt_iff_lt_mul ha).2 (by omega)
  have hle := Nat.mul_le_mul_left forsHeight (Nat.succ_le_of_lt hκ)
  rw [Nat.mul_succ, mul_comm forsHeight forsTrees] at hle
  unfold forsBit
  omega

theorem forsTarget_forsBit {q : Nat} (hlow : totalHeight ≤ q) : forsTarget (forsBit q) = q := by
  have ha := forsHeight_pos
  have hdm := Nat.div_add_mod (q - totalHeight) forsHeight
  have hr := Nat.mod_lt (q - totalHeight) ha
  have hs : forsHeight - 1 - (q - totalHeight) % forsHeight < forsHeight := by omega
  unfold forsTarget forsBit
  rw [Nat.mul_add_div ha, Nat.div_eq_of_lt hs, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hs]
  omega

theorem msbPos_msbPos (p : Nat) : msbPos (msbPos p) = p := by unfold msbPos; omega

/-- The bit of the calls that digest bit `q` is read from. -/
def digestSource (q : Nat) : Nat :=
  if q < bottomHeight then 8 * (mdBytes + treeIndexBytes + leafIndexBytes - 1 - q / 8) + q % 8
  else if q < totalHeight then
    8 * (mdBytes + treeIndexBytes - 1 - (q - bottomHeight) / 8) + (q - bottomHeight) % 8
  else msbPos (forsBit q)

/-- The digest bit read from bit `g` of the calls. -/
def digestTarget (g : Nat) : Nat :=
  if g / 8 < mdBytes then forsTarget (msbPos g)
  else if g / 8 < mdBytes + treeIndexBytes then bottomHeight + 8 * (mdBytes + treeIndexBytes - 1 - g / 8) + g % 8
  else 8 * (mdBytes + treeIndexBytes + leafIndexBytes - 1 - g / 8) + g % 8

theorem field_bytes_le : bottomHeight ≤ 8 * leafIndexBytes ∧ totalHeight - bottomHeight ≤ 8 * treeIndexBytes ∧
    forsTrees * forsHeight ≤ 8 * mdBytes ∧ mdBytes + treeIndexBytes + leafIndexBytes ≤ digestCalls * 32 := by
  unfold digestCalls digestBytes leafIndexBytes treeIndexBytes mdBytes
  omega

theorem digestTarget_source {q : Nat} (hq : q < messageDigestBits) : digestTarget (digestSource q) = q := by
  have hb := bottomHeight_le
  obtain ⟨hli, hti, hmd, -⟩ := field_bytes_le
  unfold digestSource
  split_ifs with h1 h2
  · unfold digestTarget
    rw [if_neg (by omega), if_neg (by omega)]
    omega
  · unfold digestTarget
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  · have hp := forsBit_lt (by omega) hq
    unfold digestTarget
    rw [if_pos (by unfold msbPos; omega), msbPos_msbPos, forsTarget_forsBit (by omega)]

theorem digestSource_lt {q : Nat} (hq : q < messageDigestBits) : digestSource q < hashOutputBits * digestCalls := by
  have hb := bottomHeight_le
  obtain ⟨hli, hti, hmd, hN⟩ := field_bytes_le
  unfold digestSource hashOutputBits
  split_ifs with h1 h2
  · omega
  · omega
  · have hp := forsBit_lt (by omega) hq
    unfold msbPos
    omega

/-- Every bit of the digest is one bit of the calls. -/
theorem getLsbD_truncateMessageDigest (outputs : DigestCall → HashOutput) {q : Nat} (hq : q < messageDigestBits) :
    (truncateMessageDigest outputs).getLsbD q = outputBit outputs (digestSource q) := by
  have hb := bottomHeight_le
  obtain ⟨hli, hti, hmd, hN⟩ := field_bytes_le
  have hlen := digestOutputBytes_length outputs
  rw [truncateMessageDigest, BitVec.getLsbD_ofNat, decide_eq_true hq, Bool.true_and, testBit_digestFieldsValue]
  by_cases hbq : q < bottomHeight
  · have hh : q < totalHeight := by omega
    rw [if_pos hh, testBit_digestIndexValue, if_pos hbq, digestSource, if_pos hbq, testBit_beInt,
      length_take_drop _ _ _ (by omega), getD_take_drop _ _ _ _ (by omega),
      testBit_digestOutputByte _ _ _ (by omega), decide_eq_true (by omega), Bool.true_and]
    congr 2
    omega
  · by_cases hh : q < totalHeight
    · rw [if_pos hh, testBit_digestIndexValue, if_neg hbq, digestSource, if_neg hbq, if_pos hh, testBit_beInt,
        length_take_drop _ _ _ (by omega), getD_take_drop _ _ _ _ (by omega),
        testBit_digestOutputByte _ _ _ (by omega), decide_eq_true (by omega), decide_eq_true (by omega),
        Bool.true_and, Bool.true_and]
      congr 2
      omega
    · have hk : (q - totalHeight) / forsHeight < forsTrees := by
        unfold messageDigestBits at hq
        exact (Nat.div_lt_iff_lt_mul forsHeight_pos).2 (by omega)
      rw [if_neg hh, dif_pos hk, digestSource, if_neg hbq, if_neg hh, testBit_msbField,
        decide_eq_true (Nat.mod_lt _ forsHeight_pos), Bool.true_and, msbBit_digestOutputBytes]
      unfold forsBit
      cases outputBit outputs _ <;> rfl

theorem sourceFin_injective :
    Function.Injective fun q : Fin messageDigestBits =>
      (⟨digestSource q.val, digestSource_lt q.isLt⟩ : Fin (hashOutputBits * digestCalls)) := by
  intro x y h
  have := congrArg (fun g : Fin (hashOutputBits * digestCalls) => digestTarget g.val) h
  simp only [digestTarget_source x.isLt, digestTarget_source y.isLt] at this
  exact Fin.ext this

/-- The bits of the calls that the digest drops. -/
abbrev DroppedBit := {g : Fin (hashOutputBits * digestCalls) //
  g ∈ (Finset.univ.image fun q : Fin messageDigestBits =>
    (⟨digestSource q.val, digestSource_lt q.isLt⟩ : Fin (hashOutputBits * digestCalls)))ᶜ}

/-- The digest calls, as the digest and the bits it drops. -/
def splitCalls (outputs : DigestCall → HashOutput) : MessageDigest × (DroppedBit → Bool) :=
  (truncateMessageDigest outputs, fun g => outputBit outputs g.val.val)

theorem outputs_ext {left right : DigestCall → HashOutput}
    (h : ∀ g < hashOutputBits * digestCalls, outputBit left g = outputBit right g) : left = right := by
  funext call
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc := call.isLt
  unfold hashOutputBits at hi h
  have hbit := h (256 * call.val + i) (by omega)
  have h1 : (256 * call.val + i) / 256 = call.val := by omega
  have h2 : (256 * call.val + i) % 256 = i := by omega
  unfold outputBit at hbit
  rw [dif_pos (by omega), dif_pos (by omega)] at hbit
  simpa only [h1, h2, Fin.eta] using hbit

theorem splitCalls_bijective : Function.Bijective splitCalls := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fun left right heq => outputs_ext fun g hg => ?_, ?_⟩
  · by_cases hmem : (⟨g, hg⟩ : Fin (hashOutputBits * digestCalls)) ∈ (Finset.univ.image fun q : Fin messageDigestBits =>
        (⟨digestSource q.val, digestSource_lt q.isLt⟩ : Fin (hashOutputBits * digestCalls)))
    · obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hmem
      have hg' : digestSource q.val = g := congrArg Fin.val hq
      have hd := congrArg (fun x => (Prod.fst x).getLsbD q.val) heq
      simp only [splitCalls, getLsbD_truncateMessageDigest _ q.isLt, hg'] at hd
      exact hd
    · have hd := congrFun (congrArg Prod.snd heq) ⟨⟨g, hg⟩, Finset.mem_compl.2 hmem⟩
      exact hd
  · have hd : Fintype.card DroppedBit = hashOutputBits * digestCalls - messageDigestBits := by
      rw [Fintype.card_coe, Finset.card_compl, Finset.card_image_of_injective _ sourceFin_injective,
        Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, hd, card_bitVec, Fintype.card_fin]
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' messageDigestBits_le, mul_comm]

/-- Uniform outputs of the digest calls give a uniform digest. -/
theorem evalDist_truncateMessageDigest_uniform :
    𝒟[truncateMessageDigest <$> ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] =
      𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  have hmap : truncateMessageDigest <$> ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput)) =
      Prod.fst <$> (splitCalls <$> ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))) := by
    simp [Functor.map_map, splitCalls]
  rw [hmap, evalDist_map,
    evalDist_map_bijective_uniform_cross (α := DigestCall → HashOutput)
      (β := MessageDigest × (DroppedBit → Bool)) splitCalls splitCalls_bijective, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

/-! ### Coverage -/

/-- The revealed secrets of every FORS tree, by leaf. -/
abbrev Disclosures := Index → FTree → Finset FLeaf

/-- The leaf the view selects in tree `κ` is disclosed. -/
def TreeCov (revealed : Disclosures) (view : FullDigestView) (κ : FTree) : Prop :=
  view.2 κ ∈ revealed view.1 κ

instance (revealed : Disclosures) (view : FullDigestView) : DecidablePred (TreeCov revealed view) :=
  fun κ => by unfold TreeCov; infer_instance

/-- The leaf the view selects in every tree is disclosed. -/
def Covered (revealed : Disclosures) (view : FullDigestView) : Prop :=
  ∀ κ : FTree, TreeCov revealed view κ

instance (revealed : Disclosures) : DecidablePred (Covered revealed) := fun view => by
  unfold Covered; infer_instance

end FORS.Concrete
