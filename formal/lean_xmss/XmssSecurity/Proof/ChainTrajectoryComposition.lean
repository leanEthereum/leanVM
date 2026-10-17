import XmssSecurity.Proof.ChainTrajectoryUniformity

namespace XmssSecurity

abbrev FullChainTrajectory := Vector Digest (chainLength - 1 + 1)

noncomputable def allLeafIndices : List LeafIndex :=
  Finset.univ.toList

theorem allLeafIndices_nodup : allLeafIndices.Nodup := by
  exact Finset.nodup_toList Finset.univ

theorem mem_allLeafIndices (leafIndex : LeafIndex) : leafIndex ∈ allLeafIndices := by
  simp [allLeafIndices]

theorem allLeafIndices_length : allLeafIndices.length = lifetime := by
  simp [allLeafIndices, LeafIndex]

/-- Every one-time key of both layers, in a fixed order. -/
noncomputable def allChainKeys : List ChainKey :=
  Finset.univ.toList

theorem allChainKeys_nodup : allChainKeys.Nodup := by
  exact Finset.nodup_toList Finset.univ

theorem mem_allChainKeys (key : ChainKey) : key ∈ allChainKeys := by
  simp [allChainKeys]

theorem allChainKeys_length : allChainKeys.length = Fintype.card ChainKey := by
  simp [allChainKeys]

attribute [irreducible] allLeafIndices allChainKeys

end XmssSecurity
