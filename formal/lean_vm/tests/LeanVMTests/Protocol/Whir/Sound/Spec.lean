/-
  LeanVMTests.Protocol.Whir.Sound.Spec

  Controls for the WHIR round-by-round specification: a concrete level code, the lane fold's
  bit order, the round polynomial's derived coefficient, the level-0 lane reversal, the query
  chunks, distinct powers in the glued claim, and the shape of the final statements.
-/

import LeanVM.Protocol.Verifier.WhirTarget
import LeanVM.Protocol.Whir.Sound.Spec

/-!
# WHIR soundness controls

* **Inhabitant.** `smallCode` is a `LevelCode` (`κ = 1`, `R = 1`, `η = 1/4`, agreement fraction
  `√(1/4) + 1/4 = 3/4 ≤ 1`), so the hypotheses of ArkLib's Johnson count are satisfiable.
* **Lane order.** `dot(row, eq_kernel([a, b]))` is the fold with `a` on the low lane bit
  (`dot_eqKernel`); folding with the challenges swapped gives a different value, so the order of
  `foldsN` is load-bearing.
* **Round polynomial.** The coefficient `c₁ = σ + c₂` that `sumcheck_round_poly` derives gives
  `q(0) + q(1) = σ` (`quadOK_roundPoly`); deriving `c₁ = σ + c₀` instead does not.
* **Level-0 lanes.** Reading a level-0 leaf without the reversal gives a different enforced
  value: the reversal of `whirLevels` (`row.reverse.map ofK`) is load-bearing.
* **Chunks.** `sample_queries`' shifted chunks are the base-`2^depth` digits
  (`chunk_eq_shiftRight`).
* **Distinct powers.** The glued claim uses the powers `1, λ, λ², λ³, …`; with a repeated power
  (the out-of-domain claim and the first query both with `λ`) a nonzero discrepancy vector
  `(0, 1, −1)` gives a batched discrepancy that vanishes at every `λ`, so the distinct powers of
  `card_glue_bad_le` are load-bearing.
-/

namespace LeanVMTests.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound ReedSolomon.HiddenDerivative

/-! ## A concrete level code -/

private theorem smallAgreement : johnsonAgreement (2 ^ (1 + 1)) (2 ^ 1 - 1) (1 / 4) ≤ 1 := by
  have h : √(johnsonRhoMinus (2 ^ (1 + 1)) (2 ^ 1 - 1)) ≤ 1 / 2 := by
    rw [Real.sqrt_le_iff]
    norm_num [johnsonRhoMinus]
  rw [johnsonAgreement]
  linarith

/-- A level code: `κ = 1`, `R = 1`, `η = 1/4`. -/
noncomputable def smallCode : LevelCode :=
  ⟨1, 1, 1 / 4, by norm_num, le_rfl, le_rfl, by norm_num, smallAgreement⟩

example : smallCode.n = 4 := rfl
example : smallCode.D = 1 := rfl
example : 2 ^ smallCode.κ ≤ smallCode.thr := smallCode.two_pow_le_thr

/-! ## Lane order -/

private def a₀ : E := E.ofLimbs (K.ofBits 3) (K.ofBits 5) 0
private def b₀ : E := E.ofLimbs (K.ofBits 7) 0 (K.ofBits 2)
private def row₀ : List E :=
  [E.ofLimbs (K.ofBits 1) 0 0, E.ofLimbs (K.ofBits 9) (K.ofBits 4) 0,
    E.ofLimbs 0 (K.ofBits 6) (K.ofBits 1), E.ofLimbs (K.ofBits 12) 0 (K.ofBits 8)]

/-- The row folded low bit first, written out: `(1+a)(1+b) r₀ + a(1+b) r₁ + (1+a) b r₂ +
a b r₃` (characteristic two). -/
private def folded (a b : E) (r : List E) : E :=
  (1 + a) * (1 + b) * r.getD 0 0 + a * (1 + b) * r.getD 1 0 + (1 + a) * b * r.getD 2 0 +
    a * b * r.getD 3 0

#guard dot row₀ (eqKernel [a₀, b₀]) == folded a₀ b₀ row₀
#guard dot row₀ (eqKernel [a₀, b₀]) != folded b₀ a₀ row₀

example : dot row₀ (eqKernel [a₀, b₀]) =
    foldsN [a₀, b₀] (fun j (_ : Unit) ↦ row₀.getD j 0) 0 () :=
  dot_eqKernel row₀ [a₀, b₀] rfl

/-! ## The round polynomial -/

private def σ₀ : E := E.ofLimbs (K.ofBits 11) (K.ofBits 13) (K.ofBits 17)
private def c₀ : E := E.ofLimbs (K.ofBits 19) 0 (K.ofBits 23)
private def c₂ : E := E.ofLimbs 0 (K.ofBits 29) (K.ofBits 31)

#guard polyEval [c₀, σ₀ + sumE [c₂], c₂] 0 + polyEval [c₀, σ₀ + sumE [c₂], c₂] 1 == σ₀
#guard polyEval [c₀, σ₀ + c₀, c₂] 0 + polyEval [c₀, σ₀ + c₀, c₂] 1 != σ₀

example : QuadOK [c₀, σ₀ + sumE [c₂], c₂] σ₀ := quadOK_roundPoly σ₀ c₀ c₂

/-! ## Level-0 lanes -/

private def leaf : List K := [K.ofBits 2, K.ofBits 3, K.ofBits 5, K.ofBits 7]

#guard dot (leaf.reverse.map ofK) (eqKernel [a₀, b₀]) != dot (leaf.map ofK) (eqKernel [a₀, b₀])
#guard lanesOf 0 leaf == leaf.reverse.map ofK

/-! ## Query chunks -/

#guard chunk 3 1 0b101110 == 5
#guard (0b101110 >>> (1 * 3)) % 2 ^ 3 == chunk 3 1 0b101110
#guard (List.range 4).all fun k ↦ (0xdeadbeef >>> (k * 8)) % 2 ^ 8 == chunk 8 k 0xdeadbeef

/-! ## Distinct powers -/

private def lams : List E := [E.ofLimbs (K.ofBits 2) 0 0, E.ofLimbs (K.ofBits 3) (K.ofBits 1) 0,
  E.ofLimbs 0 0 (K.ofBits 5), E.ofLimbs (K.ofBits 9) (K.ofBits 9) (K.ofBits 9)]

-- Repeated power: the discrepancy `(0, 1, −1)` batched with `(1, λ, λ)` vanishes everywhere.
#guard lams.all fun lam ↦ 0 + lam * 1 + lam * (0 - 1) == (0 : E)
-- Distinct powers `(1, λ, λ²)`: the same discrepancy batches to `λ − λ²`, nonzero at these `λ`.
#guard lams.all fun lam ↦ 0 + lam * 1 + lam * lam * (0 - 1) != (0 : E)

/-! ## Statement shapes -/

noncomputable example {μ R : ℕ} {codes : ℕ → LevelCode} {εmax : ENNReal} {t : E} {w : List E → E}
    {level : Whir.Level} {rest : List Whir.Level}
    (hc : Whir.ladder μ R = some (level :: rest))
    (hℓ : level.fold = LeanVM.Protocol.EndToEnd.laneBits)
    (hμ : LeanVM.Protocol.EndToEnd.laneBits ≤ μ)
    (hκ₀ : (codes 0).κ = μ - LeanVM.Protocol.EndToEnd.laneBits) (hR₀ : (codes 0).R = R)
    (hw : LeanVM.Protocol.EndToEnd.IsMultilinearFn μ w)
    (hA : LadderArith μ codes 0 0 (level :: rest)) (hε : whirEps codes (level :: rest) ≤ εmax) :
    Spec (verifyWhirT μ R t w) (fun h ↦ WhirPre μ R (codes 0) w t (commits h)) (fun _ _ ↦ False)
      εmax 0 0 :=
  whirSpec hc hℓ hμ hκ₀ hR₀ (isMultiaffine_of_isMultilinearFn hw) hA hε 0

end LeanVMTests.Protocol.Whir.Sound
