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
  if lay = topLayer then
    .node middleLayer (treeIndexAt index middleLayer)
      ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else if lay = middleLayer then
    .node bottomLayer (treeIndexAt index bottomLayer)
      ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩
  else .ftsRoots index

private theorem topLayer_ne_middleLayer : topLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [topLayer, middleLayer] at this

private theorem bottomLayer_ne_topLayer : bottomLayer ≠ topLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, topLayer, numLayers] at this

private theorem bottomLayer_ne_middleLayer : bottomLayer ≠ middleLayer := by
  intro h
  have := congrArg Fin.val h
  norm_num [bottomLayer, middleLayer, numLayers] at this

@[simp] theorem layerMessagePosition_top (index : Index) :
    layerMessagePosition index topLayer =
      .node middleLayer (treeIndexAt index middleLayer)
        ⟨layerHeight middleLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_pos rfl]

@[simp] theorem layerMessagePosition_middle (index : Index) :
    layerMessagePosition index middleLayer =
      .node bottomLayer (treeIndexAt index bottomLayer)
        ⟨layerHeight bottomLayer - 1, by decide⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, if_neg topLayer_ne_middleLayer.symm, if_pos rfl]

@[simp] theorem layerMessagePosition_bottom (index : Index) :
    layerMessagePosition index bottomLayer = .ftsRoots index := by
  rw [layerMessagePosition, if_neg bottomLayer_ne_topLayer,
    if_neg bottomLayer_ne_middleLayer]

theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
  have hlayer : lay = topLayer ∨ lay = middleLayer ∨ lay = bottomLayer := by
    fin_cases lay
    · exact Or.inl (Fin.ext rfl)
    · exact Or.inr (Or.inl (Fin.ext rfl))
    · exact Or.inr (Or.inr (Fin.ext rfl))
  rcases hlayer with rfl | rfl | rfl
  · rw [layerMessage_of_lt secretKey index topLayer (by decide)]
    rw [layerMessagePosition_top, honestValue_node]
    simp only [show (⟨topLayer.val + 1, by decide⟩ : Layer) = middleLayer from rfl]
    rfl
  · rw [layerMessage_of_lt secretKey index middleLayer (by decide)]
    rw [layerMessagePosition_middle, honestValue_node]
    simp only [show (⟨middleLayer.val + 1, by decide⟩ : Layer) = bottomLayer from rfl]
    rfl
  · rw [layerMessage_bottomLayer secretKey index]
    rw [layerMessagePosition_bottom, honestValue_ftsRoots]
    rfl

end SphincsSecurity.Concrete
