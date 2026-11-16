module

public import Quantum.Sphincs.Assembly.ReparamFull
public import Quantum.Sphincs.Assembly.ChgRevLoad

@[expose] public section

/-!
# The static condition of the digest blocks

The first-meeting record mass of the charged coordinates (`Quantum.Sphincs.Assembly.ChgRevBound`)
charges a message whose digest label shares a capacity with another message's label at their
hidden randomizers. At a first meeting both randomizers are undisclosed, so the charge costs the
number of colliding pairs of digest blocks `(R, (M, i))`, `(R', (M', j))` over `|Randomizer|²`; a
static condition on the public data and the root bounds it.

* **The digest blocks** `DBlk = Randomizer × DLab` and their first blocks `dPt` (distinct:
  `dPt_injective`), the pairs of calls of a message `dSib`.
* `ChgStatic pub root` (ChgRevLoad's `StaticK`): the blocks' rates are distinct, the two calls of
  a message at a randomizer never share a capacity, and the blocks of a message share capacities
  with at most `254` blocks of other messages.
* `frac_chgStatic_le_keccak`: at most `2^-128 + 2^-199` of ReparamFull's coordinates fail it (the
  two calls of a message at one capacity: `|Message × Randomizer| / |Z| = 2^-128`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest Message PublicParameter Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (XW)
open Quantum.Sphincs.Hybrid (DLab dLabCell dLabCell_injective card_dLab card_message)

namespace Quantum.Sphincs.Assembly

/-! ## The condition -/

/-- **The digest blocks**: a randomizer and a label `(M, i)`. -/
abbrev DBlk : Type := Randomizer × DLab

/-- A digest block's first block under `PK.seed` and the root, with its `k`. -/
def dPt (w : XW) (root : Digest) (b : DBlk) : X × Z :=
  (dLabCell b.2 w.1 root b.1, w.2.2.1 (dLabCell b.2 w.1 root b.1))

theorem dPt_injective (w : XW) (root : Digest) : Function.Injective (dPt w root) :=
  fun _ _ h ↦ dLabCell_injective w.1 root (congrArg Prod.fst h)

/-- The two calls of a message at a randomizer. -/
def dSib (i : Message × Randomizer) : DBlk × DBlk :=
  ((i.2, (i.1, 0)), (i.2, (i.1, 1)))

theorem dSib_ne (i : Message × Randomizer) : (dSib i).1 ≠ (dSib i).2 := by
  simp [dSib, digestCallCount]

/-- The message of a digest block. -/
def dMsg (b : DBlk) : Message :=
  b.2.1

/-- The rate of a digest block's first round at the template's public data. -/
abbrev cRate (pub : Pub) (root : Digest) (b : DBlk) : X :=
  (pub.xw.2.1 (dPt pub.xw root b)).1

/-- The capacity of a digest block's first round before `k'`. -/
abbrev cBase (pub : Pub) (root : Digest) (b : DBlk) : Z :=
  (pub.xw.2.1 (dPt pub.xw root b)).2

/-- **The static condition of the digest blocks** at the template's public data and the root:
distinct rates, the two calls of a message at a randomizer at distinct capacities, and every
message's blocks sharing capacities with at most `254` blocks of other messages. -/
def ChgStatic (pub : Pub) (root : Digest) : Prop :=
  StaticK (cRate pub root) (cBase pub root) dMsg dSib pub.xw.2.2.2 (2 * 127)

/-! ## Its fraction -/

/-- The rest of Reparam's coordinates beside `π` and the public `k'`. -/
abbrev WD : Type := (((Z → X) × PublicParameter × (X → Z)) × (ValPos → Digest)) × RestF

noncomputable instance instFintypeWD : Fintype WD :=
  instFintypeProd _ _

/-- Reparam's coordinates with `π` and the public `k'` first. -/
def eYQ : YS ≃ (Equiv.Perm (X × Z) × (X → Z)) × WD where
  toFun y := ((y.1.1.2.2.1, y.1.1.2.2.2.2), ((y.1.1.1, y.1.1.2.1, y.1.1.2.2.2.1), y.1.2), y.2)
  invFun q := (((q.2.1.1.1, (q.2.1.1.2.1, q.1.1, q.2.1.1.2.2, q.1.2)), q.2.1.2), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The digest blocks' first blocks at the rest of the coordinates. -/
def dPtW (w : WD) (b : DBlk) : X × Z :=
  (dLabCell b.2 w.1.1.2.1 (w.1.2 rootPos) b.1,
    w.1.1.2.2 (dLabCell b.2 w.1.1.2.1 (w.1.2 rootPos) b.1))

theorem dPtW_injective (w : WD) : Function.Injective (dPtW w) :=
  fun _ _ h ↦ dLabCell_injective w.1.1.2.1 (w.1.2 rootPos) (congrArg Prod.fst h)

theorem chgStatic_psiE_iff (y : YS) :
    ChgStatic (pubP (psiE y).1) (rootV (psiE y).2.1) ↔
      StaticK (rtQ dPtW (eYQ y)) (btQ dPtW (eYQ y)) dMsg dSib (eYQ y).1.2 (2 * 127) := by
  rw [ChgStatic, pubP, sPub_xw]
  exact Iff.rfl

set_option exponentiation.threshold 4096 in
theorem card_dBlk : Fintype.card DBlk = 2 ^ 385 := by
  simp only [DBlk, DLab, Fintype.card_prod, Fintype.card_fin, Quantum.Xmss.Hybrid.R0.card_bitVec_eq]
  norm_num [HashSig.digestBits, digestCallCount]

set_option exponentiation.threshold 4096 in
theorem card_msgRnd : Fintype.card (Message × Randomizer) = 2 ^ 384 := by
  simp only [Fintype.card_prod, Quantum.Xmss.Hybrid.R0.card_bitVec_eq]
  norm_num [HashSig.digestBits]

theorem card_ownB_dMsg (m : Message) : (ownB dMsg m).card ≤ 2 ^ 128 * 2 := by
  have h := card_ownB_prod (R := Randomizer) (Mg := Message) (C := DigestCall) m
  refine le_of_eq (h.trans ?_)
  simp only [Fintype.card_fin, Quantum.Xmss.Hybrid.R0.card_bitVec_eq]
  norm_num [HashSig.digestBits, digestCallCount]

set_option exponentiation.threshold 1024 in
/-- `2^712 ≤ 128!`. -/
theorem pow_le_factorial_128 : 2 ^ 712 ≤ (127 + 1).factorial := by
  decide +kernel

set_option exponentiation.threshold 70000 in
open scoped Classical in
/-- **The static condition's fraction** on ReparamFull's coordinates: at most `2^-128 + 2^-199`
(rates `2^-318`, the two calls of a message `2^-128`, three blocks of a message `2^-381`, more than
`127` foreign blocks on a message's capacities `2^-200`). -/
theorem frac_chgStatic_le_keccak :
    (Fintype.card YS : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : YS ↦
        ¬ChgStatic (pubP (psiE y).1) (rootV (psiE y).2.1)).card ≤
      ENNReal.ofReal (1 / 2 ^ 128) + ENNReal.ofReal (1 / 2 ^ 199) := by
  have hf : (Finset.univ.filter fun y : YS ↦
      ¬ChgStatic (pubP (psiE y).1) (rootV (psiE y).2.1)) =
      Finset.univ.filter fun y : YS ↦
        ¬StaticK (rtQ dPtW (eYQ y)) (btQ dPtW (eYQ y)) dMsg dSib (eYQ y).1.2 (2 * 127) :=
    Finset.filter_congr fun y _ ↦ not_congr (chgStatic_psiE_iff y)
  rw [hf, frac_comp_equiv eYQ (fun q ↦ ¬StaticK (rtQ dPtW q) (btQ dPtW q) dMsg dSib q.1.2
    (2 * 127))]
  refine (frac_not_staticK_le dPtW dPtW_injective dMsg dSib dSib_ne 127 (2 ^ 128 * 2)
    card_ownB_dMsg).trans ?_
  rw [card_dBlk, card_msgRnd, card_message, Quantum.Xmss.Hybrid.R0.card_rate,
    Quantum.Xmss.Hybrid.R0.card_cap]
  have t1 : (((2 ^ 385 * 2 ^ 385 : ℕ) : ℝ≥0∞) / ((2 ^ 1088 : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (1 / 2 ^ 318) :=
    natCast_div_le_ofReal (by positivity) le_rfl (by norm_num)
  have t2 : (((2 ^ 384 : ℕ) : ℝ≥0∞) / ((2 ^ 512 : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (1 / 2 ^ 128) :=
    natCast_div_le_ofReal (by positivity) le_rfl (by norm_num)
  have t3 : (((2 ^ 256 * (2 ^ 128 * 2) ^ 3 : ℕ) : ℝ≥0∞) / (((2 ^ 512) ^ 2 : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (1 / 2 ^ 381) :=
    natCast_div_le_ofReal (by positivity) le_rfl (by norm_num)
  have t4 : (((2 ^ 256 * (2 ^ 385 * (2 ^ 128 * 2)) ^ (127 + 1) : ℕ) : ℝ≥0∞) /
      (((127 + 1).factorial * (2 ^ 512) ^ (127 + 1) : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal (1 / 2 ^ 200) := by
    refine (ENNReal.div_le_div_left (Nat.cast_le.mpr (Nat.mul_le_mul_right _
      pow_le_factorial_128)) _).trans ?_
    exact natCast_div_le_ofReal (by positivity) le_rfl (by norm_num)
  refine (add_le_add (add_le_add (add_le_add t1 t2) t3) t4).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end Quantum.Sphincs.Assembly

end
