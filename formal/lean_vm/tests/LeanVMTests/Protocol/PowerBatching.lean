/-
  LeanVMTests.Protocol.PowerBatching

  Regression controls for zero-based power batching.
-/

import LeanVM.Protocol.ToCompPoly.PowerBatching
import LeanVM.Protocol.ClaimWeights
import Mathlib.Data.ZMod.Defs

/-!
# Power-batching controls

Zero challenge detects the exponent origin. Two false components may cancel at one challenge,
while a singleton has no such challenge. Empty batching is the zero claim.
-/

namespace LeanVMTests.Protocol

open LeanVM.Protocol

#guard powerBatch (fun _ : Fin 1 ↦ (1 : ZMod 5)) 0 = 1
#guard (∑ j : Fin 1, (1 : ZMod 5) * 0 ^ (j.val + 1)) = 0
#guard powerBatch (![1, -1] : Fin 2 → ZMod 5) 1 = 0
#guard powerBatch (![1, -1] : Fin 2 → ZMod 5) 0 = 1
#guard powerBatch (Fin.elim0 : Fin 0 → ZMod 5) 3 = 0

example (ρ : ZMod 5) : powerBatch (fun _ : Fin 1 ↦ (1 : ZMod 5)) ρ ≠
    powerBatch (fun _ : Fin 1 ↦ (0 : ZMod 5)) ρ :=
  singleton_batch_ne _ _ (by decide) ρ


/-! ## Mixed-field pairing and off-cube evaluation

These use the existing `Weight.pair` inner-product definition. A phase-facing batched `Weight`
constructor remains the opening phase's responsibility.
-/

open LeanVM.Parameters CompPoly CMlPolynomialEval OracleComp
open scoped NNReal ENNReal

private def u : E := E.ofLimbs 0 1 0
private def q : Column 1 := ⟨#v[K.ofBits 2, K.ofBits 3]⟩
private def weights : Fin 2 → Weight E 1 := ![eqWeight #v[u], eqWeight #v[u + 1]]
private def tables : Fin 2 → CMlPolynomialEval E 1 := fun j ↦ (weights j).onCube

-- The column is over K, while both the weights and challenge are over E.
#guard u ≠ 0 ∧ u ≠ 1
#guard sumCube (hadamard (batchWeight tables u) (CMlPolynomialEval.map (algebraMap K E) q.values)) =
  powerBatch (fun j ↦ (weights j).pair (algebraMap K E) q.values) u
#guard sumCube (hadamard (batchWeight tables 0) (CMlPolynomialEval.map (algebraMap K E) q.values)) =
  (weights 0).pair (algebraMap K E) q.values
-- A positive-power mutation erases the first pairing at zero; the intended batch does not.
#guard (weights 0).pair (algebraMap K E) q.values ≠ 0

#guard evalMle (batchWeight tables u) #v[u + 1] =
  powerBatch (fun j ↦ (weights j).mle #v[u + 1]) u
#guard evalMle (batchWeight tables 0) #v[u + 1] = (weights 0).mle #v[u + 1]
#guard evalMle (batchWeight (Fin.elim0 : Fin 0 → CMlPolynomialEval E 1) u) #v[u] = 0

-- The same bridge works for arbitrary weights and columns, without a new pairing definition.
example {J μ : ℕ} (w : Fin J → Weight E μ) (c : Column μ) (ρ : E) :
    sumCube (hadamard (batchWeight (fun j ↦ (w j).onCube) ρ)
      (CMlPolynomialEval.map (algebraMap K E) c.values)) =
      powerBatch (fun j ↦ (w j).pair (algebraMap K E) c.values) ρ := by
  rw [pairing_batchWeight]
  congr 1
  funext j
  unfold sumCube Weight.pair
  apply Finset.sum_congr rfl
  intro i _
  rw [hadamard_getElem]
  congr 1
  exact Vector.getElem_map _ _

example {J μ : ℕ} (w : Fin J → Weight E μ) (ρ : E) (r : Vector E μ) :
    evalMle (batchWeight (fun j ↦ (w j).onCube) ρ) r =
      powerBatch (fun j ↦ (w j).mle r) ρ := by
  simp_rw [Weight.mle_eq]
  exact evalMle_batchWeight _ _ _

-- A nonempty false family is essential. Equal families pass every challenge.
#guard (Finset.univ.filter fun ρ : ZMod 5 ↦
  powerBatch (![1, -1] : Fin 2 → ZMod 5) ρ = powerBatch ![0, 0] ρ).card = 1
#guard (Finset.univ.filter fun ρ : ZMod 5 ↦
  powerBatch (![0, 0] : Fin 2 → ZMod 5) ρ = powerBatch ![0, 0] ρ).card = 5

end LeanVMTests.Protocol
