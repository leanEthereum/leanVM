import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.StatementLemmas
/-!
# The hypertree

Three layers, bottom first. Each layer's fold produces the root of its tree, which is exactly the
message the layer above it signs, so the layers chain; layer `0`'s fold is the public root.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

theorem layerMessage_bottomLayer (secretKey : SecretKey) (index : Index) :
    layerMessage (m := m) secretKey index bottomLayer
      = ftsKey secretKey.parameter index (secretKey.ftsSecret index) := by
  rw [layerMessage, dif_neg (by decide)]

theorem layerMessage_of_lt (secretKey : SecretKey) (index : Index) (lay : Layer)
    (hbelow : lay.val + 1 < numLayers) :
    layerMessage (m := m) secretKey index lay
      = treeRoot secretKey.parameter ⟨lay.val + 1, hbelow⟩
          (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
          (secretKey.otsSecret ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)) := by
  rw [layerMessage, dif_pos hbelow]

/-- Honest leaf indices are in range for their layer, which is what lets a fold reach the root. -/
theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val < 2 ^ layerHeight lay := by
  rw [leafIndexAt_val]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

end SphincsSecurity.Concrete
