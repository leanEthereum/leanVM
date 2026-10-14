import Whir.WHIRObservableSecurity
import Whir.DuplexRefinement

/-! The deployed sampler consumes consecutive 24-byte scalars from one 32-byte
output stream. Full oracle blocks remain public, including the retained suffix. -/
namespace Whir.AnchoredFiatShamirSecurityCodec
open Concrete FiatShamirGame
open scoped BigOperators

def blockCount (dimension : Nat) : Nat := (24*dimension+31)/32
def residualCount (dimension : Nat) : Nat := 32*blockCount dimension-24*dimension
abbrev Blocks (dimension : Nat) := Fin (blockCount dimension) → Digest32
abbrev Residual (dimension : Nat) := Fin (residualCount dimension) → Byte
abbrev Joint (dimension : Nat) := (Fin dimension → E) × Residual dimension

theorem block_capacity (dimension : Nat) : 24*dimension ≤ 32*blockCount dimension := by
  unfold blockCount
  omega

theorem residual_lt_block (dimension : Nat) : residualCount dimension < 32 := by
  unfold residualCount blockCount
  omega

/-- Row-major concatenation, not a separate low-word projection per digest. -/
def flatten (dimension : Nat) : Blocks dimension ≃ (Fin (32*blockCount dimension) → Byte) where
  toFun blocks := fun i => blocks ⟨i.val/32, by omega⟩ ⟨i.val%32, Nat.mod_lt _ (by decide)⟩
  invFun bytes := fun j i => bytes ⟨32*j.val+i.val, by have := j.isLt; have := i.isLt; omega⟩
  left_inv blocks := by
    funext j i
    dsimp
    congr 2 <;> have := i.isLt <;> omega
  right_inv bytes := by
    funext i
    dsimp
    congr 1
    apply Fin.ext
    dsimp
    omega

/-- Split at the actual consumed cursor. The residual is at most 31 bytes,
not eight discarded bytes for every scalar. -/
def splitBytes (dimension : Nat) : (Fin (32*blockCount dimension) → Byte) ≃
    ((Fin dimension → Scalar24) × Residual dimension) where
  toFun bytes := (fun j i => bytes ⟨24*j.val+i.val, by
      have := j.isLt; have := i.isLt; have := block_capacity dimension; omega⟩,
    fun i => bytes ⟨24*dimension+i.val, by
      have := i.isLt; have := block_capacity dimension; unfold residualCount at *; omega⟩)
  invFun parts := fun i => if h : i.val < 24*dimension then
    parts.1 ⟨i.val/24, by omega⟩ ⟨i.val%24, Nat.mod_lt _ (by decide)⟩
    else parts.2 ⟨i.val-24*dimension, by
      have := i.isLt; unfold residualCount; omega⟩
  left_inv bytes := by
    funext i
    dsimp
    split
    · congr 1; apply Fin.ext; dsimp; omega
    · congr 1; apply Fin.ext; dsimp; omega
  right_inv parts := by
    apply Prod.ext
    · funext j i
      dsimp
      have h : 24*j.val+i.val < 24*dimension := by have := j.isLt; have := i.isLt; omega
      simp only [h, dite_true]
      apply congrArg₂ parts.1
      · apply Fin.ext; dsimp; have := i.isLt; omega
      · apply Fin.ext; dsimp; have := i.isLt; omega
    · funext i
      dsimp
      have h : ¬ 24*dimension+i.val < 24*dimension := by omega
      simp only [h, dite_false]
      apply congrArg parts.2
      apply Fin.ext
      dsimp
      omega

def vectorParts (dimension : Nat) : Blocks dimension ≃ Joint dimension :=
  (flatten dimension).trans ((splitBytes dimension).trans
    (Equiv.prodCongr (Equiv.piCongrRight fun _ => WHIRFiatShamir.scalarCodec) (Equiv.refl _)))

def point (dimension : Nat) (blocks : Blocks dimension) : Fin dimension → E :=
  (vectorParts dimension blocks).1

/-- Executable specification of the source's block-straddling 24-byte chunks. -/
theorem point_bytes (dimension : Nat) (blocks : Blocks dimension) (j : Fin dimension) :
    point dimension blocks j = ByteCodec.decodeE (fun i =>
      blocks ⟨(24*j.val+i.val)/32, by
        have := j.isLt; have := i.isLt; have := block_capacity dimension; omega⟩
        ⟨(24*j.val+i.val)%32, Nat.mod_lt _ (by decide)⟩) := rfl

/-- Exact joint public-view equality, with no restriction on the payoff's
inspection of any fourth word, retained bytes or decoded coordinate. -/
theorem vector_full_average (dimension : Nat) (payoff : Joint dimension → ℚ) :
    average (fun blocks : Blocks dimension => payoff (vectorParts dimension blocks)) =
      average payoff := RawOracleCoupling.average_equiv (vectorParts dimension) payoff

theorem vector_point_average (dimension : Nat) (payoff : (Fin dimension → E) → ℚ) :
    average (fun blocks : Blocks dimension => payoff (point dimension blocks)) =
      average payoff := by
  have h := vector_full_average dimension (fun parts => payoff parts.1)
  rw [WHIRObservableSecurity.average_product] at h
  simpa only [point, average_const] using h

/-- The complete public block vector can always be reconstructed exactly. -/
theorem full_answer_recovered (dimension : Nat) (blocks : Blocks dimension) :
    (vectorParts dimension).symm (vectorParts dimension blocks) = blocks :=
  (vectorParts dimension).symm_apply_apply blocks

end Whir.AnchoredFiatShamirSecurityCodec

#print axioms Whir.AnchoredFiatShamirSecurityCodec.vector_full_average
#print axioms Whir.AnchoredFiatShamirSecurityCodec.vector_point_average
