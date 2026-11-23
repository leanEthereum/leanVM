module

public import NativeRustcArm.Code.Common.Finalize.Names
public import NativeRustcArm.Code.Common.KeccakF.Names
public import NativeRustcArm.Code.Common.Memcpy.Names
public import NativeRustcArm.Code.Common.Memset.Names
public import NativeRustcArm.Code.Common.Update.Names
public import NativeRustcArm.Code.Xmss.WotsLeaf.Names

public import NativeRustcArm.WotsLeaf.Leaf.Out
public import NativeRustcArm.WotsLeaf.Codeword.Digits58

/-!
# `lean_xmss::wots::wots_leaf` meets its contract

`wotsLeaf_spec`: the function, placed anywhere in a program whose `memcpy`, `memset`,
`Hasher::update`, `Hasher::finalize` and `keccak_f` meet their contracts, meets
`WotsLeafPre`/`WotsLeafPost` (`NativeRustcArm.Spec.WotsLeaf`): the message digest
(`digest_region`), the codeword or the tag `0` and the return (`codeword_region`), the 58 chains
(`chains_region`), the leaf's hash (`leaf_b44`, `leaf_b45`), the result written and the return
(`leaf_out`).
-/

namespace NativeRustcArm.WotsLeaf

open NativeRustc NativeRustc.Keccak NativeRustc.Xmss NativeRustcArm.WotsLeafProof
open LeanVM.Protocol.KeccakHash

theorem addr2_eq (r : Run) : r.addr 2 0 = address (tweak 2 r.hi r.e) := rfl

/-- With a codeword `x`, the result is `x` and the leaf: the first 16 bytes of the hash of `P`,
the leaf's address and the chains' ends. -/
theorem result_some (r : Run) {x : List UInt8} (h : codeword r.digest16 = some x) :
    r.result = some (x, (hashBytes (r.pp ++ r.addr 2 0 ++ r.ends x 58)).take 16) := by
  simp only [Run.result, wotsLeaf, messageDigest_eq, h, wotsLeafHash, th, addr2_eq]
  rfl

/-- **`wots_leaf` meets its contract.** -/
public theorem wotsLeaf_spec [NativeRustcArm.Host] {k : Nat} (hp : Placed Xmss.WotsLeaf.code k)
    (hmemcpy : Spec (label NativeRustcArm.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hmemset : Spec (label NativeRustcArm.Common.Memset.entryLabel) MemsetPre MemsetPost)
    (hupdate : Spec (label NativeRustcArm.Common.Update.entryLabel) UpdatePre UpdatePost)
    (hfinalize : Spec (label NativeRustcArm.Common.Finalize.entryLabel) FinalizePre
      FinalizePost)
    (hkeccakF : Spec (label NativeRustcArm.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost) :
    Spec (label NativeRustcArm.Xmss.WotsLeaf.entryLabel) WotsLeafPre WotsLeafPost := by
  intro m₀ hpre
  let r : Run := ⟨m₀, k⟩
  have hp' : Placed Xmss.WotsLeaf.code r.k := hp
  have hc : Callees := ⟨hmemcpy, hmemset, hupdate, hfinalize, hkeccakF⟩
  have hpr : r.Pre := hpre
  rw [hp.label NativeRustcArm.Xmss.WotsLeaf.entry_at]
  show Eventually _ r.Done ⟨m₀, NativeRustcArm.Host.addrOf (r.k + NativeRustcArm.Xmss.WotsLeaf.b0Offset)⟩
  refine Eventually.bind (digest_region r hp' hc hpr m₀ rfl) fun st ⟨hpc, hA⟩ ↦ pc_at hpc ?_
  refine Eventually.bind (codeword_region r hp' hc hpr st.data hA) fun st2 h2 ↦ ?_
  rcases h2 with ⟨-, hD⟩ | ⟨hcw, hpc2, hA2⟩
  · exact .done _ hD
  refine pc_at hpc2 (Eventually.bind (chains_region r hp' hc hpr _ st2.data hA2)
    fun st3 ⟨hpc3, hA3⟩ ↦ pc_at hpc3 ?_)
  obtain ⟨-, hEl, hKc, -, -, -, -, -, h20, -⟩ := hA3
  rw [chainSlots_eq] at hKc
  have hK : r.CK (digits r.dNum) (r.ends (digits r.dNum) 58) st3.data :=
    ⟨⟨hKc.1, allOf_left hKc.2⟩, (allOf_right hKc.2).1.2.2, by omega⟩
  refine leaf_b44 hp' hc hpr hK h20 fun m4 hK4 h20' hadr hH ↦ ?_
  refine leaf_b45 hp' hc hpr (hEl.trans rfl) hK4 h20' hadr hH fun m5 hK5 hD ↦ ?_
  exact leaf_out hp' hpr (length_hashBytes _) hK5 hD (result_some r hcw)

end NativeRustcArm.WotsLeaf
