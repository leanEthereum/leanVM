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

/-! The encoding-view decomposition of a digest: the 58 two-bit digits together with the top 12 bits.
The statement's `decodeDigest` tests the top bits; `decodeDigest_eq_decodeView` restates it through this
view. -/

/-- The top bits accompany the 58 two-bit digits. -/
abbrev EncodingView := Encoding × BitVec zeroBits

def digestView (digest : Digest) : EncodingView :=
  (digestEncoding digest, digestTop digest)

def ValidView (view : EncodingView) : Prop :=
  view.2 = 0 ∧ Valid view.1

noncomputable def decodeView (view : EncodingView) : Option Encoding := by
  classical
  exact if ValidView view then some view.1 else none

theorem decodeDigest_eq_decodeView (digest : Digest) :
    decodeDigest digest = decodeView (digestView digest) := by
  classical
  unfold decodeDigest decodeView
  refine if_congr ?_ rfl rfl
  simp only [ValidView, digestView]

theorem digestView_injective : Function.Injective digestView := by
  intro left right hview
  have hencoding : digestEncoding left = digestEncoding right :=
    congrArg Prod.fst hview
  have htop : digestTop left = digestTop right :=
    congrArg Prod.snd hview
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  have hbelow128 : bit < 128 := by simpa [digestBits] using hbit
  by_cases hlow : bit < winternitzBits * numChains
  · let chain : ChainIndex := ⟨bit / winternitzBits, by
      change bit / 2 < 58
      simp only [winternitzBits, numChains] at hlow
      omega⟩
    let offsetBit := bit % winternitzBits
    have hoffsetBit : offsetBit < winternitzBits := Nat.mod_lt bit (by decide)
    have hoffset : digitOffset chain + offsetBit = bit := by
      unfold digitOffset
      change 2 * (bit / 2) + bit % 2 = bit
      omega
    have hextract :
        left.extractLsb' (digitOffset chain) winternitzBits =
          right.extractLsb' (digitOffset chain) winternitzBits := by
      apply BitVec.toFin_injective
      exact congrFun hencoding chain
    have hlocalBit := congrArg (fun value => value.getLsbD offsetBit) hextract
    simpa [BitVec.getLsbD_extractLsb', hoffsetBit, hoffset] using hlocalBit
  · have hrel : bit - winternitzBits * numChains < zeroBits := by
      simp only [zeroBits, digestBits, winternitzBits, numChains] at hlow ⊢
      omega
    have hlocalBit := congrArg (fun value => value.getLsbD (bit - winternitzBits * numChains)) htop
    have hsum : winternitzBits * numChains + (bit - winternitzBits * numChains) = bit := by omega
    simpa [digestTop, BitVec.getLsbD_extractLsb', hrel, hsum] using hlocalBit

theorem decodeView_eq_some_iff {view : EncodingView} {x : Encoding} :
    decodeView view = some x ↔ view = (x, 0) ∧ Valid x := by
  classical
  rcases view with ⟨digits, padding⟩
  simp only [decodeView]
  by_cases hview : ValidView (digits, padding)
  · rw [ite_eq_left hview]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro hdigits
      subst x
      exact ⟨⟨rfl, hview.1⟩, hview.2⟩
    · exact fun h => h.1.1
  · rw [ite_eq_right hview]
    simp only [Prod.mk.injEq]
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
