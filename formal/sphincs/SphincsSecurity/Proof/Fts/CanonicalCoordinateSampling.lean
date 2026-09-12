import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CanonicalHiddenCoordinates
import SphincsSecurity.Proof.Base.UniformTableSplit
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local irreducible] instFintypePosition
set_option backward.isDefEq.respectTransparency false

abbrev CanonicalCoordinateLabels := CanonicalCoordinate → Digest
abbrev CanonicalGraphHighHalves := Position → Digest
abbrev CanonicalSecretGraph :=
  (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) ×
    (Index → FtsTree → FtsLeaf → Digest) × CanonicalGraphLabels

def coordinateOtsSecrets (labels : CanonicalCoordinateLabels) : Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leaf chain => labels (.otsStart lay tree leaf chain)

def coordinateFtsSecrets (labels : CanonicalCoordinateLabels) : Index → FtsTree → FtsLeaf → Digest :=
  fun index tree leaf => labels (.ftsStart index tree leaf)

noncomputable def digestHashHalves : HashOutput ≃ Digest × Digest :=
  splitHashOutputEquiv digestBits (by decide)

def canonicalGraphHighHalves (graph : CanonicalGraphLabels) : CanonicalGraphHighHalves :=
  fun position => (splitHashOutput digestBits (graph position)).2

noncomputable def coordinateGraphLabels (labels : CanonicalCoordinateLabels)
    (high : CanonicalGraphHighHalves) : CanonicalGraphLabels :=
  fun position => digestHashHalves.symm (labels (.graph position), high position)

theorem coordinateGraphLabels_low (labels : CanonicalCoordinateLabels)
    (high : CanonicalGraphHighHalves) (position : Position) :
    truncateHash (coordinateGraphLabels labels high position) = labels (.graph position) := by
  exact congrArg Prod.fst (digestHashHalves.apply_symm_apply (labels (.graph position), high position))

theorem coordinateGraphLabels_high (labels : CanonicalCoordinateLabels)
    (high : CanonicalGraphHighHalves) :
    canonicalGraphHighHalves (coordinateGraphLabels labels high) = high := by
  funext position
  exact congrArg Prod.snd (digestHashHalves.apply_symm_apply (labels (.graph position), high position))

theorem coordinateGraphLabels_value (labels : CanonicalCoordinateLabels)
    (high : CanonicalGraphHighHalves) :
    CanonicalCoordinate.value (coordinateOtsSecrets labels) (coordinateFtsSecrets labels)
      (coordinateGraphLabels labels high) = labels := by
  funext coordinate
  cases coordinate <;> simp only [CanonicalCoordinate.value, coordinateOtsSecrets, coordinateFtsSecrets,
    coordinateGraphLabels_low]

noncomputable def canonicalCoordinateEquiv :
    CanonicalSecretGraph ≃ CanonicalCoordinateLabels × CanonicalGraphHighHalves where
  toFun data := (CanonicalCoordinate.value data.1 data.2.1 data.2.2, canonicalGraphHighHalves data.2.2)
  invFun data := (coordinateOtsSecrets data.1, coordinateFtsSecrets data.1, coordinateGraphLabels data.1 data.2)
  left_inv data := by
    rcases data with ⟨ots, fts, graph⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext position
        exact digestHashHalves.symm_apply_apply (graph position)
  right_inv data := by
    apply Prod.ext
    · exact coordinateGraphLabels_value data.1 data.2
    · exact coordinateGraphLabels_high data.1 data.2

theorem uniform_canonicalCoordinateEquiv :
    (PMF.uniformOfFintype CanonicalSecretGraph).map canonicalCoordinateEquiv =
      (PMF.uniformOfFintype CanonicalCoordinateLabels).bind (fun labels =>
        (PMF.uniformOfFintype CanonicalGraphHighHalves).map (fun high => (labels, high))) := by
  rw [PMF.uniformOfFintype_map_of_bijective canonicalCoordinateEquiv canonicalCoordinateEquiv.bijective]
  exact UniformTableSplit.uniform_product

noncomputable local instance coordinateSamplingOts :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) := otsSecretsSampleableType

noncomputable local instance coordinateSamplingFts :
    SampleableType (Index → FtsTree → FtsLeaf → Digest) := ftsSecretsSampleableType

attribute [local semireducible] sampleOtsSecrets sampleFtsSecrets

theorem evalDist_sampleSecretGraph :
    (do
      let ots ← 𝒟[sampleOtsSecrets]
      let fts ← 𝒟[sampleFtsSecrets]
      let graph ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
      pure (ots, fts, graph) : SPMF CanonicalSecretGraph) =
        𝒟[PMF.uniformOfFintype CanonicalSecretGraph] := by
  rw [UniformTableSplit.uniform_product]
  simp only [← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
    evalDist_bind, evalDist_pure, map_eq_bind_pure_comp, Function.comp_def]
  rw [show 𝒟[sampleOtsSecrets] = 𝒟[PMF.uniformOfFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)]
      from evalDist_uniformSample _]
  apply congrArg (𝒟[PMF.uniformOfFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)] >>= ·)
  funext ots
  rw [UniformTableSplit.uniform_product]
  simp only [← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
    evalDist_bind, evalDist_pure, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  rw [show 𝒟[sampleFtsSecrets] = 𝒟[PMF.uniformOfFintype (Index → FtsTree → FtsLeaf → Digest)]
      from evalDist_uniformSample _]

theorem sampleSecretGraph_bind_coordinates {Result : Type}
    (next : (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) →
      (Index → FtsTree → FtsLeaf → Digest) → CanonicalGraphLabels → SPMF Result) :
    (𝒟[sampleOtsSecrets] >>= fun ots => 𝒟[sampleFtsSecrets] >>= fun fts =>
      𝒟[PMF.uniformOfFintype CanonicalGraphLabels] >>= next ots fts) =
        (𝒟[PMF.uniformOfFintype CanonicalCoordinateLabels] >>= fun labels =>
          𝒟[PMF.uniformOfFintype CanonicalGraphHighHalves] >>= fun high =>
            next (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)) := by
  have h := congrArg (fun law : PMF (CanonicalCoordinateLabels × CanonicalGraphHighHalves) =>
    𝒟[law] >>= fun data => next (coordinateOtsSecrets data.1) (coordinateFtsSecrets data.1)
      (coordinateGraphLabels data.1 data.2)) uniform_canonicalCoordinateEquiv
  simp only [← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind, evalDist_map] at h
  rw [← evalDist_sampleSecretGraph] at h
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] at h
  change (𝒟[sampleOtsSecrets] >>= fun ots => 𝒟[sampleFtsSecrets] >>= fun fts =>
    𝒟[PMF.uniformOfFintype CanonicalGraphLabels] >>= fun graph =>
      next (canonicalCoordinateEquiv.symm (canonicalCoordinateEquiv (ots, fts, graph))).1
        (canonicalCoordinateEquiv.symm (canonicalCoordinateEquiv (ots, fts, graph))).2.1
        (canonicalCoordinateEquiv.symm (canonicalCoordinateEquiv (ots, fts, graph))).2.2) = _ at h
  simpa only [Equiv.symm_apply_apply] using h

end SphincsSecurity.Concrete
