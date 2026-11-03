import FORS.Scheme.Uniform
import Mathlib.Data.BitVec

/-!
The full view of a message digest (its index and the leaf index of each of the `k` FORS trees) is a
bijection, so a uniform digest gives a uniform view; and uniform digest calls give a uniform
digest. Coverage of a view by disclosed secrets: the selected leaf of every tree is disclosed.
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

/-! ### Uniform digest calls give a uniform digest -/

theorem digestValue_eq (outputs : DigestCall → HashOutput) :
    digestValue outputs = (finFunctionFinEquiv fun call => (outputs call).toFin : Fin _).val := by
  rw [finFunctionFinEquiv_apply, digestValue]
  refine Finset.sum_congr rfl fun call _ => ?_
  rw [pow_mul]
  rfl

theorem digestValue_lt (outputs : DigestCall → HashOutput) :
    digestValue outputs < 2 ^ (hashOutputBits * digestCalls) := by
  rw [digestValue_eq, pow_mul]
  exact (finFunctionFinEquiv fun call => (outputs call).toFin).isLt

/-- The low 256 bits of the digest are the first call. -/
theorem digestValue_mod (outputs : DigestCall → HashOutput) :
    digestValue outputs % 2 ^ hashOutputBits = (outputs firstCall).toNat := by
  have h := congrArg Fin.val
    (congrFun (finFunctionFinEquiv.symm_apply_apply fun call => (outputs call).toFin) firstCall)
  rw [finFunctionFinEquiv_symm_apply_val] at h
  rw [digestValue_eq]
  simpa [firstCall] using h

/-- The index of the digest is the index of the first call. -/
theorem digestIndex_truncate (outputs : DigestCall → HashOutput) :
    digestIndex (truncateMessageDigest outputs) = blockIndex (outputs firstCall) := by
  apply Fin.ext
  have hh := totalHeight_le_hashOutput
  have hd := totalHeight_le_digest
  change (BitVec.extractLsb' 0 totalHeight (BitVec.ofNat messageDigestBits (digestValue outputs))).toNat =
    (BitVec.extractLsb' 0 totalHeight (outputs firstCall)).toNat
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftRight_zero,
    BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hd), ← digestValue_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hh)]

/-- The digest calls, as the truncated digest and the bits above it. -/
def splitCalls (outputs : DigestCall → HashOutput) :
    MessageDigest × Fin (2 ^ (hashOutputBits * digestCalls - messageDigestBits)) :=
  (truncateMessageDigest outputs, ⟨digestValue outputs / 2 ^ messageDigestBits, by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_sub_cancel' messageDigestBits_le]
    exact digestValue_lt outputs⟩)

theorem splitCalls_bijective : Function.Bijective splitCalls := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fun left right heq => ?_, ?_⟩
  · have hlow : digestValue left % 2 ^ messageDigestBits = digestValue right % 2 ^ messageDigestBits := by
      have := congrArg (fun x => (Prod.fst x).toNat) heq
      simpa [splitCalls, truncateMessageDigest, BitVec.toNat_ofNat] using this
    have hhigh : digestValue left / 2 ^ messageDigestBits = digestValue right / 2 ^ messageDigestBits := by
      have := congrArg (fun x => (Prod.snd x).val) heq
      simpa [splitCalls] using this
    have hvalue : digestValue left = digestValue right := by
      rw [← Nat.div_add_mod (digestValue left) (2 ^ messageDigestBits),
        ← Nat.div_add_mod (digestValue right) (2 ^ messageDigestBits), hlow, hhigh]
    rw [digestValue_eq, digestValue_eq] at hvalue
    have hfin := finFunctionFinEquiv.injective (Fin.ext hvalue)
    funext call
    exact BitVec.eq_of_toFin_eq (congrFun hfin call)
  · rw [Fintype.card_prod, Fintype.card_fin, card_bitVec, Fintype.card_fun, Fintype.card_fin,
      card_bitVec, ← pow_add, Nat.add_sub_cancel' messageDigestBits_le, ← pow_mul, mul_comm]

/-- Uniform outputs of the digest calls give a uniform digest. -/
theorem evalDist_truncateMessageDigest_uniform :
    𝒟[truncateMessageDigest <$> ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] =
      𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  have hmap : truncateMessageDigest <$> ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput)) =
      Prod.fst <$> (splitCalls <$> ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))) := by
    simp [Functor.map_map, splitCalls]
  rw [hmap, evalDist_map,
    evalDist_map_bijective_uniform_cross (α := DigestCall → HashOutput)
      (β := MessageDigest × Fin (2 ^ (hashOutputBits * digestCalls - messageDigestBits)))
      splitCalls splitCalls_bijective, ← evalDist_map]
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
