module

public import LeanDa.RpmScheme
public import Common.Duplex.Vec
public import Common.Rerun
public import LeanDa.Defs
public import LeanDa.WithHash
import all Init.Data.Array.Basic

@[expose] public section

/-!
# LeanDA's challenges as a duplex

The challenge's sponge (`membershipChallengeMWithHash`, and the pair of its two samples,
`membershipChallengePairM`) over the direct calls `F` of the two-oracle model is a duplex challenge
derivation in the sense of `Common.SeedDuplex` (`daDuplex`, two samples): a root's chain starts at
the fresh sponge of the label's hash and the root (`first`, `Sponge::new`: lanes `0 … 3` the
hash, `4 … 7` the root's words, the rest zero), a sample writes zeros over the rate (`next`), and
a challenge is the three lanes `0 … 2` of an answer (`out`); the deployed challenge is the second
sample. The fresh sponges have the zero capacity, and a sample keeps lanes `16 … 24`, the bytes
`128 … 199` of the state (`cap_first`, `cap_next`), which the duplex lemma calls the capacity:
`72` bytes, so a uniform state has a given capacity with probability `2^-576` (`daDuplex_cap`).
Over `F`, the pair is the duplex's challenges (`membershipChallengePairM_eq_chalP`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common Common.SeedDuplex
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace LeanDa

/-! ## The state as bytes -/

theorem bytesEquiv_apply (y : KState) (i : Fin 200) : bytesEquiv y i = byteAt y i := rfl

/-! ## Splitting the bytes -/

theorem splitEquiv_fst {m k : ℕ} (f : Fin (m + k) → UInt8) (j : Fin m) :
    (splitEquiv m k f).1 j = f (Fin.castAdd k j) := by
  simp [splitEquiv, Equiv.sumArrowEquivProdArrow, Equiv.arrowCongr]

theorem daBuild_symm_fst (y : KState) :
    (daBuild.symm y).1 = limbsEquiv fun j : Fin 24 ↦ byteAt y j := by
  simp only [daBuild, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.prodCongr_symm,
    Equiv.prodCongr_apply, Prod.map_fst]
  congr 1

/-! ## The duplex -/

/-! ## The root's words determine the root -/

/-! ## The challenge of an answer -/

theorem limbsEquiv_apply (f : Fin 24 → UInt8) :
    limbsEquiv f = CompPoly.Extension.Ext.ofFn (P := BF64.ext3Params) fun a : Fin 3 ↦
      laneBytes.symm (Vector.ofFn fun b : Fin 8 ↦ f (finProdFinEquiv (a, b))) := rfl

theorem ofFn_eq_ofLimbs (g : Fin 3 → K) :
    (CompPoly.Extension.Ext.ofFn (P := BF64.ext3Params) g : E) = ofLimbs (g 0) (g 1) (g 2) := by
  simp only [CompPoly.Extension.Ext.ofFn, ofLimbs]
  congr 1

theorem kBytes_ofLane (w : UInt64) : LeanVM.Parameters.K.toBytes (K.ofLane w) =
    LeanVM.Protocol.KeccakHash.wordBytes w :=
  rfl

/-- Lane `a` of a state, read as an element of `K`, from its eight bytes. -/
theorem laneBytes_symm_bytes (y : KState) (a : ℕ) (ha : a < 25) :
    laneBytes.symm (Vector.ofFn fun b : Fin 8 ↦ byteAt y (8 * a + b)) =
      K.ofLane ((stateToLanes y)[a]'ha) := by
  rw [Equiv.symm_apply_eq]
  apply Vector.toList_inj.mp
  rw [laneBytes_toList, kBytes_ofLane]
  refine List.ext_getElem (by simp [LeanVM.Protocol.KeccakHash.wordBytes]) fun b h1 h2 ↦ ?_
  have hb : b < 8 := by simpa using h1
  simp only [Vector.toList_ofFn, List.getElem_ofFn]
  have e := byteAt_stateToLanes y (8 * a + b) (by omega)
  simp only [show (8 * a + b) / 8 = a from by omega, show (8 * a + b) % 8 = b from by omega] at e
  rw [← e, List.getD_eq_getElem _ _ h2]

/-- **The challenge an answer carries is its lanes `0 … 2`** (`Sponge.sample`). -/
theorem daBuild_symm_fst_eq (y : KState) :
    (daBuild.symm y).1 = ofLimbs (K.ofLane (stateToLanes y)[0]) (K.ofLane (stateToLanes y)[1])
      (K.ofLane (stateToLanes y)[2]) := by
  rw [daBuild_symm_fst, limbsEquiv_apply]
  have key : ∀ a : Fin 3, laneBytes.symm (Vector.ofFn fun b : Fin 8 ↦
      byteAt y (finProdFinEquiv (a, b) : ℕ)) = K.ofLane (stateToLanes y)[(a : ℕ)] := by
    intro a
    rw [← laneBytes_symm_bytes y a (by omega)]
    refine congrArg laneBytes.symm ?_
    apply Vector.ext
    intro b hb
    simp only [Vector.getElem_ofFn, finProdFinEquiv_apply_val]
    congr 1
    ring
  rw [ofFn_eq_ofLimbs, key 0, key 1, key 2]
  rfl

/-! ## LeanDA's duplex -/

theorem card_bytes (k : ℕ) : Fintype.card (Fin k → UInt8) = 256 ^ k := by
  rw [Fintype.card_fun, card_uInt8, Fintype.card_fin]

/-- **A capacity is hit with probability `2^-576`.** -/
theorem daDuplex_cap (c : DaCp) :
    Pr{let w ← ($ᵗ DaW : ProbComp DaW)}[daDuplex.capW w = c] ≤ (2 ^ 576 : ℝ≥0∞)⁻¹ := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hf : (Finset.univ.filter fun w : DaW ↦ daDuplex.capW w = c) =
      (Finset.univ : Finset (Fin 104 → UInt8)) ×ˢ {c} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    exact Iff.rfl
  simp only [hf, Finset.card_product, Finset.card_singleton, mul_one, Finset.card_univ, Fintype.card_prod, card_bytes, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have h256 : (256 : ℝ≥0∞) ^ 72 = 2 ^ 576 := by
    rw [show (256 : ℝ≥0∞) = 2 ^ 8 by norm_num, ← pow_mul]
  have ha : (256 : ℝ≥0∞) ^ 104 ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha' : (256 : ℝ≥0∞) ^ 104 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  refine le_of_eq ?_
  rw [h256, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl ha) (Or.inl ha'),
    mul_comm ((256 : ℝ≥0∞) ^ 104)⁻¹, mul_assoc, ENNReal.inv_mul_cancel ha ha', mul_one]

/-! ## The challenges over `F` are the duplex's -/

theorem daDuplex_out (y : KState) :
    daDuplex.out y = ofLimbs (K.ofLane (stateToLanes y)[0]) (K.ofLane (stateToLanes y)[1])
      (K.ofLane (stateToLanes y)[2]) :=
  daBuild_symm_fst_eq y

/-- **Over `F`, the pair of LeanDA's samples is the duplex's challenges** (`n = 2`): the fresh
sponge's answer at `daFirst root iv`, then the sample's at `daNext`. -/
theorem membershipChallengePairM_eq_chalP (root : Common.DigestBytes) :
    membershipChallengePairM hR pR root = toVec <$> chalP daDuplex root := by
  simp only [membershipChallengePairM, Sponge.newWith, Sponge.sampleWith, Sponge.duplexWith, pR,
    lanePerm, chalP, chainP, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  refine bind_congr fun iv ↦ bind_congr fun y₁ ↦ bind_congr fun y₂ ↦ ?_
  congr 1
  funext j
  fin_cases j <;> simp [toVec, daDuplex_out]

end LeanDa
