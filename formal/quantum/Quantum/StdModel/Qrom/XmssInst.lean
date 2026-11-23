module

public import Quantum.StdModel.Qrom.Prf
public import Quantum.StdModel.Xmss.PrfInst

@[expose] public section

/-!
# The leanXMSS instances of the QROM property bounds

The obligations of the generic QROM bounds of `Quantum.StdModel.Qrom` at the leanXMSS instances
of Theorem 1, and the bounds they give.

* **KIM-PRF** (`abs_avg_xmssPrfAdv_le`): the composite key `S_0 ↦ H("leanXMSS" ‖ S_0)` on the
  formats X2, X3, X4. Every keyed input has the 32-byte prefix `P ‖ A`, so a byte string is
  keyed under at most one key (`card_filter_prfKimInput_le`), and the seed input
  `"leanXMSS" ‖ S_0` (40 bytes) is no keyed input (64 bytes or more). The averaged advantage of an
  adversary with `q` hash calls is at most `4 q √(2 / 2^256)`.
-/

open IPFunctor OracleComp OracleSpec HashSig HashSig.OverPermutation LeanXmss
open scoped ENNReal

open Quantum.Xmss (length_littleEndianBytes length_addressBytes)
open Quantum.Qrom.Xmss (littleEndianBytes_inj)
open Quantum.StdModel.Qrom (kimInput KimCellInjective kimCellInjective_of
  card_filter_kimInput_le abs_avg_derivedKimPrfAdv_le)

namespace Quantum.StdModel.Xmss

open Quantum.StdModel Props

/-! ## KIM-PRF -/

theorem prfFmt_inj : Function.Injective prfFmt := fun x y h ↦ by
  obtain ⟨hP, hT⟩ := prfHead_inj (congrArg (·.1) h)
  exact prfFields_inj (Prod.ext hP hT) (congrArg (·.2) h)

theorem length_prfFmt_fst (x : PrfDom) : (prfFmt x).1.length = 32 := by
  simp only [prfFmt, List.length_append, length_littleEndianBytes, length_addressBytes]

theorem length_prfKey (S : HashOutput) : (prfKey S).length = 32 :=
  length_littleEndianBytes 32 S

/-- Under every key, distinct formats have distinct keyed inputs. -/
theorem prfKimCellInjective : KimCellInjective prfFmt prfKey :=
  kimCellInjective_of prfFmt_inj length_prfKey fun x y ↦
    .inl (by rw [length_prfFmt_fst, length_prfFmt_fst])

theorem prfSeedBytes_injective : Function.Injective prfSeedBytes :=
  fun _ _ h ↦ littleEndianBytes_inj h

theorem prfKey_injective : Function.Injective prfKey :=
  fun _ _ h ↦ littleEndianBytes_inj h

/-- The seed input `"leanXMSS" ‖ S_0` is no keyed input: its 40 bytes against at least 64. -/
theorem prfSeedInput_ne_kimInput (S0 : MasterSeed) (S : HashOutput) (x : PrfDom) :
    seedTag ++ prfSeedBytes S0 ≠ kimInput prfFmt prfKey S x := fun h ↦ by
  have hl := congrArg List.length h
  have h8 : seedTag.length = 8 := rfl
  simp only [kimInput, List.length_append, length_prfFmt_fst, length_prfKey, prfSeedBytes,
    length_littleEndianBytes, h8] at hl
  omega

/-- A byte string is keyed under at most one key: the key's bytes follow the 32-byte prefix. -/
theorem card_filter_prfKimInput_le (l : HashInput) :
    (Finset.univ.filter fun K ↦ ∃ x, kimInput prfFmt prfKey K x = l).card ≤ 1 :=
  (card_filter_kimInput_le prfFmt prfKey prfKey_injective length_prfKey l).trans
    ((Finset.card_le_card (t := {32}) (Finset.image_subset_iff.2 fun x _ ↦
      Finset.mem_singleton.2 (length_prfFmt_fst x))).trans_eq (Finset.card_singleton 32))

theorem card_bitVec (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

/-- **The leanXMSS KIM-PRF in the QROM**: averaged over the random oracle, the derived-key
KIM-PRF advantage of an adversary with `q` hash calls (its classical PRF queries free) is at
most `4 q √(2 / 2^256)` in absolute value. -/
theorem abs_avg_xmssPrfAdv_le (B : Adversary romWorld (PrfDom →ₒ HashOutput) Unit Bool) {q : ℕ}
    (hB : ∀ p, IFreeM.IsChargeBound (B p) (cmdCharge hashCharge) q) :
    |∑ H, (Fintype.card romWorld.Tab : ℝ)⁻¹ * xmssPrfAdv romWorld H B| ≤
      4 * q * Real.sqrt (2 / 2 ^ 256) := by
  have h := abs_avg_derivedKimPrfAdv_le seedTag prfSeedBytes prfKey prfFmt prfTrunc
    prfFmt_lengthLe length_prfSeedInput prfKimCellInjective prfSeedBytes_injective
    prfSeedInput_ne_kimInput card_filter_prfKimInput_le B hB
  have hs : (Fintype.card HashOutput : ℝ) = 2 ^ 256 := by exact_mod_cast card_bitVec 256
  rw [hs] at h
  refine h.trans_eq ?_
  norm_num

end Quantum.StdModel.Xmss

end
