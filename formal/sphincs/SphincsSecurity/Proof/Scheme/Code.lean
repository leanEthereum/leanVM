import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Bytes
/-!
# The target-sum code

Two codewords of equal digit sum cannot be ordered componentwise unless they are equal. That is what
removes the Winternitz checksum, and what makes a one-time key unforgeable on a new message: an
adversary holding the chain values at `x` can walk each chain forward, so it can produce any
codeword above `x`, and this says the only one is `x` itself.
-/

namespace SphincsSecurity.TargetSum

theorem valid_of_decodeDigest_eq_some {digest : Digest} {encoding : Encoding}
  (hdecode : decodeDigest digest = some encoding) : Valid encoding := by
  by_cases hvalid : digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false
      ∧ Valid (digestEncoding digest)
  · rw [decodeDigest, if_pos hvalid] at hdecode
    have hencoding : digestEncoding digest = encoding := Option.some.inj hdecode
    exact hencoding ▸ hvalid.2.2
  · rw [decodeDigest, if_neg hvalid] at hdecode
    simp at hdecode

private theorem digest_eq_of_encoding_eq_of_padding {left right : Digest}
    (hencoding : digestEncoding left = digestEncoding right)
    (hleft63 : left.getLsbD 63 = false) (hleft127 : left.getLsbD 127 = false)
    (hright63 : right.getLsbD 63 = false) (hright127 : right.getLsbD 127 = false) :
    left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  by_cases hlow : bit < 63
  · let chainIdx : ChainIndex := ⟨bit / 3, by
      have : bit / 3 < 21 := by omega
      exact lt_of_lt_of_le this (by decide)⟩
    have hchain := congrFun hencoding chainIdx
    change (left.extractLsb' (digitOffset chainIdx) winternitzBits).toFin =
      (right.extractLsb' (digitOffset chainIdx) winternitzBits).toFin at hchain
    have hword := BitVec.toFin_injective hchain
    have hchainVal : chainIdx.val = bit / 3 := rfl
    have hoffset : digitOffset chainIdx = 3 * chainIdx.val := by
      rw [digitOffset, if_pos]
      · norm_num [winternitzBits]
      · rw [hchainVal]
        norm_num [digitsPerHalf, numChains]
        omega
    have hwithin : bit - 3 * chainIdx.val < winternitzBits := by
      dsimp only [chainIdx]
      norm_num [winternitzBits]
      omega
    have hbitEq := congrArg (fun word : BitVec winternitzBits =>
      word.getLsbD (bit - 3 * chainIdx.val)) hword
    simpa only [digestEncoding, BitVec.getLsbD_extractLsb', hwithin, decide_true,
      Bool.true_and, hoffset, show 3 * chainIdx.val + (bit - 3 * chainIdx.val) = bit by
        dsimp only [chainIdx]
        omega] using hbitEq
  · by_cases hpad : bit = 63
    · subst bit
      rw [hleft63, hright63]
    · by_cases hhigh : bit < 127
      · let chainIdx : ChainIndex := ⟨21 + (bit - 64) / 3, by
          have hbit64 : 64 ≤ bit := by omega
          have : (bit - 64) / 3 < 21 := by omega
          norm_num [numChains]
          omega⟩
        have hchain := congrFun hencoding chainIdx
        change (left.extractLsb' (digitOffset chainIdx) winternitzBits).toFin =
          (right.extractLsb' (digitOffset chainIdx) winternitzBits).toFin at hchain
        have hword := BitVec.toFin_injective hchain
        have hchainVal : chainIdx.val = 21 + (bit - 64) / 3 := rfl
        have hge : digitsPerHalf ≤ chainIdx.val := by
          rw [hchainVal]
          norm_num [digitsPerHalf, numChains]
        have hoffset : digitOffset chainIdx = 64 + 3 * ((bit - 64) / 3) := by
          rw [digitOffset, if_neg (by omega)]
          rw [hchainVal]
          norm_num [winternitzBits]
          omega
        have hwithin : bit - (64 + 3 * ((bit - 64) / 3)) < winternitzBits := by
          norm_num [winternitzBits]
          omega
        have hbitEq := congrArg (fun word : BitVec winternitzBits =>
          word.getLsbD (bit - (64 + 3 * ((bit - 64) / 3)))) hword
        simpa only [digestEncoding, BitVec.getLsbD_extractLsb', hwithin, decide_true,
          Bool.true_and, hoffset,
          show 64 + 3 * ((bit - 64) / 3) +
              (bit - (64 + 3 * ((bit - 64) / 3))) = bit by omega] using hbitEq
      · have : bit = 127 := by
          have := hbit
          norm_num [digestBits] at this
          omega
        subst bit
        rw [hleft127, hright127]

theorem decodeDigest_some_injective {left right : Digest} {encoding : Encoding}
    (hleft : decodeDigest left = some encoding)
    (hright : decodeDigest right = some encoding) : left = right := by
  rw [decodeDigest] at hleft hright
  split at hleft <;> split at hright
  · rename_i hleftValid hrightValid
    exact digest_eq_of_encoding_eq_of_padding (Option.some.inj hleft |>.trans
      (Option.some.inj hright).symm) hleftValid.1 hleftValid.2.1
      hrightValid.1 hrightValid.2.1
  all_goals simp at hleft hright

theorem eq_of_le_of_sum_eq {x y : Encoding} (hle : ∀ i, (x i).val ≤ (y i).val)
    (hsum : sum x = sum y) : x = y := by
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hlt
  have hstrict : (x i).val < (y i).val := by omega
  have : sum x < sum y := by
    refine Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega

theorem eq_of_le_of_valid {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y :=
  eq_of_le_of_sum_eq hle (hx.trans hy.symm)

noncomputable instance instDecidablePredDigestValidDigest : DecidablePred ValidDigest :=
  Classical.decPred _

/-- A concatenation of fixed-length blocks determines the blocks. -/
theorem flatMap_ofFn_injective {α β : Type} (g : α → List β) (len : Nat)
    (hlen : ∀ a, (g a).length = len) (hinj : ∀ a b, g a = g b → a = b) :
    ∀ {n : Nat} {f f' : Fin n → α},
      (List.ofFn f).flatMap g = (List.ofFn f').flatMap g → f = f' := by
  intro n
  induction n with
  | zero => intro f f' _; funext i; exact i.elim0
  | succ n ih =>
      intro f f' h
      simp only [List.ofFn_succ, List.flatMap_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (by rw [hlen, hlen])
      have hzero := hinj _ _ hhead
      have hsucc := ih htail
      funext i
      cases i using Fin.cases with
      | zero => exact hzero
      | succ j => exact congrFun hsucc j

/-- A one-time signature's payload is its `v` endpoints, and the concatenation determines them. -/
theorem leafPayload_injective {endpoints endpoints' : ChainIndex → Digest}
    (h : Concrete.leafPayload endpoints = Concrete.leafPayload endpoints') :
    endpoints = endpoints' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

/-- A few-time public key's payload is its `k - 1` roots. -/
theorem ftsRootsPayload_injective {roots roots' : FtsTree → Digest}
    (h : Concrete.ftsRootsPayload roots = Concrete.ftsRootsPayload roots') : roots = roots' :=
  flatMap_ofFn_injective Concrete.digestBytes 16 digestBytes_length
    (fun _ _ => digestBytes_injective) h

end SphincsSecurity.TargetSum
