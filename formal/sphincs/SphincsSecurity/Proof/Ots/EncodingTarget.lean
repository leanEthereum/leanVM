import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.EncodingCached
import SphincsSecurity.Proof.Scheme.ForgeryClassify
/-!
# Canonical signed encoding targets

Every successful signer invocation using one one-time position computes the same layer message and
the same least admissible counter. Consequently an encoding collision at that position targets one
canonical signed payload, even when several signatures reuse the position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def layerMessagePosition (index : Index) (lay : Layer) : Position :=
  if h : lay.val + 1 < numLayers then
    let next : Layer := ⟨lay.val + 1, h⟩
    .node next (treeIndexAt index next)
      ⟨layerHeight next - 1, by
        have := next.isLt
        simp only [layerHeight, maxLayerHeight, numLayers] at *
        split_ifs <;> omega⟩ ⟨0, by positivity⟩
  else .ftsRoots index

@[simp] theorem layerMessagePosition_bottom (index : Index) :
    layerMessagePosition index bottomLayer = .ftsRoots index := by
  simp [layerMessagePosition, bottomLayer, numLayers]

theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
  by_cases hnext : lay.val + 1 < numLayers
  · rw [layerMessage_of_lt secretKey index lay hnext]
    rw [layerMessagePosition, dif_pos hnext, honestValue_node]
    have hheight : 1 ≤ layerHeight (⟨lay.val + 1, hnext⟩ : Layer) := by
      simp only [layerHeight, maxLayerHeight]
      split_ifs <;> omega
    simp only [Nat.sub_add_cancel hheight]
    rfl
  · have hbottom : lay = bottomLayer := by
      apply Fin.ext
      have := lay.isLt
      simp only [bottomLayer, numLayers] at *
      omega
    subst lay
    rw [layerMessage_bottomLayer secretKey index]
    rw [layerMessagePosition_bottom, honestValue_ftsRoots]
    rfl

end SphincsSecurity.Concrete
