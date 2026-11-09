import LeanVM.Protocol.ToArkLib.Typed.Batch
import LeanVM.Protocol.ToArkLib.Oracles
import LeanVM.Protocol.Field
import Mathlib.Data.ZMod.Defs

/-!
# Batching tests

* **The component.** `batch` draws `ρ` and records `Σ_j v_j ρ^j` (the claimed values combined by
  the powers of `ρ`, the power `ρ^0 = 1` on the first): the honest combination of true values is
  the combination of the true values at every challenge.
* **The count.** Over `ZMod 5`, a false family of two values collides with the true one at exactly
  one challenge (the root of the difference, degree one), a false singleton at none; equal
  families at every challenge; true values that depend on the witness collide at more
  challenges than one family's.
* **Completeness and knowledge soundness** have inhabitants over `E`, the security a plain
  definition that computes, at `(k - 1) / |E|`.

A plain file, so `#guard` evaluates the compiled definitions.
-/

namespace LeanVMTests.Protocol.Batch

open LeanVM.Parameters LeanVM.Protocol
open scoped NNReal

/-! ## The component -/

/-- The statement: three claimed values; the output: the challenge and the combined value. -/
abbrev Out : Type := E × E

/-- Three values of `E`. -/
def v₃ : Fin 3 → E := ![y, y + 1, y * y]

/-- Batching three claims; the output records the challenge and the combination. -/
def batch3 : Typed.Def NoOracle (Fin 3 → E) Unit Out Unit (Typed.drawSlot E) :=
  Typed.batch NoOracle E id fun _ ρ c ↦ (ρ, c)

/-- The challenge. -/
def ρ₀ : E := y + y * y

-- The combined claim weighs value `j` by `ρ^j`, `ρ^0 = 1` on the first.
#guard powerBatch v₃ ρ₀ = v₃ 0 + v₃ 1 * ρ₀ + v₃ 2 * (ρ₀ * ρ₀)

/-- The input relation: the claimed values are the true ones, `v₃`. -/
def relIn : Set (((Fin 3 → E) × ∀ i, NoOracle i) × Unit) := {p | p.1.1 = v₃}

/-- The output relation: the combined value is the combination of the true values. -/
def relOut : Set ((Out × ∀ i, NoOracle i) × Unit) := {p | p.1.1.2 = powerBatch v₃ p.1.1.1}

/-- Completeness: true claims combine into a true claim at every challenge. -/
theorem batchComplete3 : Typed.Complete batch3 relIn relOut :=
  Typed.batchComplete fun s _ _ h ρ ↦ by
    show powerBatch (id s) ρ = powerBatch v₃ ρ
    rw [show id s = v₃ from h]

/-- Knowledge soundness at `2 / |E|`: a false claim combines into the true combination at two
challenges at most. -/
def batchSecurity3 :
    Typed.Security batch3 relIn relOut
      (Typed.drawErrors E (((3 - 1 : ℕ) : ℝ≥0) / (Nat.card E : ℝ≥0))) :=
  Typed.batchSecurity fun _ _ ↦
    ⟨v₃, fun _ _ hs hρ ↦ ⟨fun h ↦ hs h.symm, hρ⟩⟩

/-! ## The count -/

#guard (Finset.univ.filter fun ρ : ZMod 5 ↦
  powerBatch (![1, -1] : Fin 2 → ZMod 5) ρ = powerBatch ![0, 0] ρ).card = 1
#guard (Finset.univ.filter fun ρ : ZMod 5 ↦
  powerBatch (![2] : Fin 1 → ZMod 5) ρ = powerBatch ![3] ρ).card = 0
#guard (Finset.univ.filter fun ρ : ZMod 5 ↦
  powerBatch (![1, 2] : Fin 2 → ZMod 5) ρ = powerBatch ![1, 2] ρ).card = 5

-- Why the true values are fixed before the witness: against the claim `(0, 0)`, two witnesses
-- with true values `(1, -1)` and `(2, -1)` each collide at one challenge, but at two between
-- them, above `k - 1 = 1`.
#guard (Finset.univ.filter fun ρ : ZMod 5 ↦
  powerBatch (![1, -1] : Fin 2 → ZMod 5) ρ = powerBatch ![0, 0] ρ ∨
    powerBatch (![2, -1] : Fin 2 → ZMod 5) ρ = powerBatch ![0, 0] ρ).card = 2

end LeanVMTests.Protocol.Batch
