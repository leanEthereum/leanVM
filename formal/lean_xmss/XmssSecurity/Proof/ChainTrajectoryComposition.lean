module

public import XmssSecurity.Proof.ChainKey

@[expose] public section

namespace XmssSecurity

abbrev FullChainTrajectory := Vector Digest (chainLength - 1 + 1)

/-- Every one-time key of both layers, in a fixed order. -/
noncomputable def allChainKeys : List ChainKey :=
  Finset.univ.toList

theorem allChainKeys_nodup : allChainKeys.Nodup := by
  exact Finset.nodup_toList Finset.univ

theorem mem_allChainKeys (key : ChainKey) : key ∈ allChainKeys := by
  simp [allChainKeys]

theorem allChainKeys_length : allChainKeys.length = Fintype.card ChainKey := by
  simp [allChainKeys]

attribute [irreducible] allChainKeys

end XmssSecurity
