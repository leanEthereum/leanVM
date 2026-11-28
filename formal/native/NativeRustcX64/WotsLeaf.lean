module

public import NativeRustcX64.Code.Xmss.WotsLeaf.Names

public import NativeRustcX64.WotsLeaf.Codeword.Region
public import NativeRustcX64.WotsLeaf.Chain.Outer
public import NativeRustcX64.WotsLeaf.Leaf.Out

/-!
# `lean_xmss::wots::wots_leaf` meets its contract

`wotsLeaf_spec`: rustc's x86-64 `wots_leaf`, placed anywhere in a program whose `memcpy`,
`memset`, `Hasher::update`, `Hasher::finalize` and `keccak_f` meet their contracts
(`WotsLeafCallees`), meets `WotsLeafPre`/`WotsLeafPost` (`NativeRustcX64.Spec.WotsLeaf`): the
message digest (`digest_region`), the codeword or the tag 0 (`codeword_region`), the 58 chains
(`chains_region`), the leaf's hash (`leaf_hash`) and the result (`leaf_out`). With Lean's three
axioms only.
-/

namespace NativeRustcX64

open WotsLeafProof

/-- **`wots_leaf` meets its contract.** -/
public theorem wotsLeaf_spec [Host] {k : Nat} (hp : Placed Xmss.WotsLeaf.code k)
    (hc : WotsLeafCallees) : Spec (label NativeRustcX64.Xmss.WotsLeaf.entryLabel) WotsLeafPre WotsLeafPost := by
  intro m hpre
  let r : Run := ⟨m, k⟩
  have hp' : Placed Xmss.WotsLeaf.code r.k := hp
  have hpre' : r.Pre := hpre
  rw [hp.label NativeRustcX64.Xmss.WotsLeaf.entry_at]
  refine Eventually.bind (digest_region r hp' hc hpre' m rfl) fun st ⟨hpc, hA⟩ ↦ pc_at hpc ?_
  refine Eventually.bind (codeword_region r hp' hc hpre' _ hA) fun st₂ h₂ ↦ ?_
  rcases h₂ with hd | ⟨hpc₂, hA₂, hcw⟩
  · exact .done _ hd
  · exact pc_at hpc₂ (chains_region hp' hc hpre' hA₂ fun m' hK ↦
      leaf_hash hp' hc hpre' hK fun m'' hK' ↦ leaf_out hp' hc hpre' hcw hK')

/--
info: 'NativeRustcX64.wotsLeaf_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wotsLeaf_spec

end NativeRustcX64
