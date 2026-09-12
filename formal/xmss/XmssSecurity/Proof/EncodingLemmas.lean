import XmssSecurity.Proof.IdealStatement
import Mathlib.Data.BitVec

namespace XmssSecurity

def verificationChainHashes : Nat := numChains * (chainLength - 1) - targetSum

namespace TargetSum

open scoped BigOperators

def PointwiseLE (x y : Encoding) : Prop := ∀ i, x i ≤ y i

def Incomparable (x y : Encoding) : Prop := ¬PointwiseLE x y ∧ ¬PointwiseLE y x

def verificationWork (x : Encoding) : Nat :=
  ∑ i, (chainLength - 1 - (x i).val)

/-- The verifier's domain-separated WOTS chain positions for one encoding. -/
abbrev SuffixPosition (x : Encoding) :=
  Σ i : ChainIndex, Fin (chainLength - 1 - (x i).val)

/-- Every valid encoding makes the verifier walk exactly 99 WOTS chain edges. -/
theorem verificationWork_eq (x : Encoding) (hx : Valid x) :
    verificationWork x = verificationChainHashes := by
  unfold Valid sum at hx
  unfold verificationWork verificationChainHashes
  rw [Finset.sum_tsub_distrib Finset.univ]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact congrArg (numChains * (chainLength - 1) - ·) hx
  · intro i _
    exact Nat.le_pred_of_lt (x i).isLt

theorem card_suffixPosition (x : Encoding) (hx : Valid x) :
    Fintype.card (SuffixPosition x) = verificationChainHashes := by
  rw [Fintype.card_sigma]
  simpa [verificationWork] using verificationWork_eq x hx

noncomputable def enumerateSuffixPositions (x : Encoding) (hx : Valid x) :
    SuffixPosition x ≃ Fin verificationChainHashes :=
  Fintype.equivFinOfCardEq (card_suffixPosition x hx)

/-! The encoding-view decomposition of a digest: the 42 three-bit digits together with the two padding bits 63 and 127, packed as a `Fin 4`. The statement's `decodeDigest` tests the padding bits directly; `decodeDigest_eq_decodeView` below restates it through this view. -/

/-- The two unused digest bits accompany the 42 three-bit digits. -/
abbrev EncodingView := Encoding × Fin 4

def digestPadding (digest : Digest) : Fin 4 :=
  ⟨(if digest.getLsbD 63 then 1 else 0) +
    (if digest.getLsbD 127 then 2 else 0), by
      cases digest.getLsbD 63 <;> cases digest.getLsbD 127 <;> simp⟩

/-- The concrete little-endian layout used by `IncEnc`: 21 digits, one padding bit, 21 digits, and one padding bit. -/
def digestView (digest : Digest) : EncodingView :=
  (digestEncoding digest, digestPadding digest)

def ValidView (view : EncodingView) : Prop :=
  view.2 = 0 ∧ Valid view.1

noncomputable def decodeView (view : EncodingView) : Option Encoding := by
  classical
  exact if ValidView view then some view.1 else none

theorem digestPadding_eq_zero_iff {digest : Digest} :
    digestPadding digest = 0 ↔
      digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false := by
  cases h63 : digest.getLsbD 63 <;> cases h127 : digest.getLsbD 127 <;>
    simp [digestPadding, h63, h127, Fin.ext_iff]

theorem decodeDigest_eq_decodeView (digest : Digest) :
    decodeDigest digest = decodeView (digestView digest) := by
  classical
  unfold decodeDigest decodeView
  refine if_congr ?_ rfl rfl
  simp only [ValidView, digestView, digestPadding_eq_zero_iff, and_assoc]

theorem digestPadding_eq_iff {left right : Digest} :
    digestPadding left = digestPadding right ↔
      left.getLsbD 63 = right.getLsbD 63 ∧
      left.getLsbD 127 = right.getLsbD 127 := by
  generalize hl0 : left.getLsbD 63 = leftLow
  generalize hl1 : left.getLsbD 127 = leftHigh
  generalize hr0 : right.getLsbD 63 = rightLow
  generalize hr1 : right.getLsbD 127 = rightHigh
  cases leftLow <;> cases leftHigh <;> cases rightLow <;> cases rightHigh <;>
    simp [digestPadding, hl0, hl1, hr0, hr1]

theorem digestView_injective : Function.Injective digestView := by
  intro left right hview
  have hencoding : digestEncoding left = digestEncoding right :=
    congrArg Prod.fst hview
  have hpadding : digestPadding left = digestPadding right :=
    congrArg Prod.snd hview
  have hpaddingBits := digestPadding_eq_iff.mp hpadding
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hbelow128 : bit < 128 := by simpa [digestBits] using hbit
  by_cases heq63 : bit = 63
  · simpa [heq63] using hpaddingBits.1
  by_cases heq127 : bit = 127
  · simpa [heq127] using hpaddingBits.2
  by_cases hlow : bit < 63
  · let chain : ChainIndex := ⟨bit / winternitzBits, by
      change bit / 3 < 42
      omega⟩
    let offsetBit := bit % winternitzBits
    have hoffsetBit : offsetBit < winternitzBits := by
      exact Nat.mod_lt bit (by decide)
    have hoffset : digitOffset chain + offsetBit = bit := by
      unfold digitOffset
      change 3 * (bit / 3) + (if bit / 3 < 21 then 0 else 1) + bit % 3 = bit
      rw [if_pos (by omega)]
      have hdiv := Nat.mod_add_div bit 3
      omega
    have hextract :
        left.extractLsb' (digitOffset chain) winternitzBits =
          right.extractLsb' (digitOffset chain) winternitzBits := by
      apply BitVec.toFin_injective
      exact congrFun hencoding chain
    have hlocalBit := congrArg (fun value => value.getLsbD offsetBit) hextract
    simpa [BitVec.getLsbD_extractLsb', hoffsetBit, hoffset] using hlocalBit
  · have hge64 : 64 ≤ bit := by omega
    have hbelow127 : bit < 127 := by omega
    let shifted := bit - 64
    let chain : ChainIndex := ⟨digitsPerHalf + shifted / winternitzBits, by
      change 21 + (bit - 64) / 3 < 42
      omega⟩
    let offsetBit := shifted % winternitzBits
    have hoffsetBit : offsetBit < winternitzBits := by
      exact Nat.mod_lt shifted (by decide)
    have hoffset : digitOffset chain + offsetBit = bit := by
      unfold digitOffset
      change 3 * (21 + (bit - 64) / 3) +
        (if 21 + (bit - 64) / 3 < 21 then 0 else 1) + (bit - 64) % 3 = bit
      rw [if_neg (by omega)]
      have hdiv := Nat.mod_add_div (bit - 64) 3
      omega
    have hextract :
        left.extractLsb' (digitOffset chain) winternitzBits =
          right.extractLsb' (digitOffset chain) winternitzBits := by
      apply BitVec.toFin_injective
      exact congrFun hencoding chain
    have hlocalBit := congrArg (fun value => value.getLsbD offsetBit) hextract
    simpa [BitVec.getLsbD_extractLsb', hoffsetBit, hoffset] using hlocalBit

theorem decodeView_eq_some_iff {view : EncodingView} {x : Encoding} :
    decodeView view = some x ↔ view = (x, 0) ∧ Valid x := by
  classical
  rcases view with ⟨digits, padding⟩
  simp only [decodeView, ValidView]
  split <;> rename_i hview
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro hdigits
      subst x
      exact ⟨⟨rfl, hview.1⟩, hview.2⟩
    · exact fun h => h.1.1
  · simp only [Prod.mk.injEq]
    constructor
    · intro heq
      cases heq
    · rintro ⟨⟨hdigits, hpadding⟩, hvalid⟩
      exfalso
      apply hview
      refine ⟨hpadding, ?_⟩
      exact hdigits.symm ▸ hvalid

theorem decodeDigest_eq_some_iff {digest : Digest} {x : Encoding} :
    decodeDigest digest = some x ↔ digestView digest = (x, 0) ∧ Valid x := by
  rw [decodeDigest_eq_decodeView]
  exact decodeView_eq_some_iff

theorem decodeDigest_zero_eq_none : decodeDigest (0 : Digest) = none := by
  cases hdecode : decodeDigest (0 : Digest) with
  | none => rfl
  | some encoding =>
      exfalso
      have hview := decodeDigest_eq_some_iff.mp hdecode
      have hencoding : digestEncoding (0 : Digest) = encoding :=
        congrArg Prod.fst hview.1
      rw [← hencoding] at hview
      have hsum : sum (digestEncoding (0 : Digest)) = 0 := by
        unfold sum
        apply Finset.sum_eq_zero
        intro chain _
        simp [digestEncoding]
      unfold Valid at hview
      rw [hsum] at hview
      exact (by decide : (0 : Nat) ≠ targetSum) hview.2

/-- A valid target-sum encoding and zero padding determine one exact 128-bit digest. -/
theorem digest_eq_of_decodeDigest_eq_some {left right : Digest} {x : Encoding}
    (hleft : decodeDigest left = some x) (hright : decodeDigest right = some x) :
  left = right := by
  apply digestView_injective
  rw [(decodeDigest_eq_some_iff.mp hleft).1, (decodeDigest_eq_some_iff.mp hright).1]

/-- Two distinct encoding-hash inputs decoding to the same valid encoding form a target collision. -/
theorem hash_collision_of_same_decodedEncoding {α : Type} (hash : α → Digest)
    {left right : α} {x : Encoding} (hne : left ≠ right)
    (hleft : decodeDigest (hash left) = some x)
    (hright : decodeDigest (hash right) = some x) :
    left ≠ right ∧ hash left = hash right :=
  ⟨hne, digest_eq_of_decodeDigest_eq_some hleft hright⟩

theorem eq_of_pointwiseLE_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hxy : PointwiseLE x y) : x = y := by
  by_contra hne
  have hlt : ∃ i ∈ Finset.univ, (x i).val < (y i).val := by
    by_contra h
    push Not at h
    apply hne
    funext i
    exact Fin.ext (Nat.le_antisymm (hxy i) (h i (Finset.mem_univ i)))
  have hsum : sum x < sum y := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hxy i
    · exact hlt
  exact (Nat.ne_of_lt hsum) (hx.trans hy.symm)

theorem incomparable_of_valid_of_ne {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hne : x ≠ y) : Incomparable x y := by
  constructor
  · exact fun hxy => hne (eq_of_pointwiseLE_of_valid hx hy hxy)
  · exact fun hyx => hne (eq_of_pointwiseLE_of_valid hy hx hyx).symm

/-- A different valid encoding moves backward on at least one chain. -/
theorem exists_forged_lt_signed {signedEncoding forgedEncoding : Encoding}
    (hsigned : Valid signedEncoding) (hforged : Valid forgedEncoding)
    (hne : signedEncoding ≠ forgedEncoding) :
    ∃ i, forgedEncoding i < signedEncoding i := by
  have hnot := (incomparable_of_valid_of_ne hsigned hforged hne).1
  simpa only [PointwiseLE, not_forall, not_le] using hnot

end TargetSum

end XmssSecurity
