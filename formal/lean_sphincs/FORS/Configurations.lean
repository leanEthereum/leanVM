import FORS.Scheme.VerificationCost

/-! **The configuration's size and verification cost.** Height 26, three layers of 10 + 8 + 8, FORS
of 24 trees of height 10, Keccak-256 (`Layout.signature_size`, `Cost.verification_compressions`): the
theorems below hold for every `Params` of the configuration, whatever its signature limit. -/

open OracleComp

namespace FORS.Configurations

variable [Params]

open Concrete Cost

section h26_layered_k24

variable (hH : totalHeight = 26) (hd : numLayers = 3) (hk : forsTrees = 24) (ha : forsHeight = 10)
include hH hd hk ha

/-- Signature size, height 26, layers 10 + 8 + 8, `k = 24`: 7,740 bytes. -/
theorem size_h26_layered_k24 (signature : Signature) : (serializeSignature signature).length = 7740 := by
  rw [signature_size, hH, hd, hk, ha]

/-- Keccak-256, height 26, layers 10 + 8 + 8, `k = 24`: an accepted signature costs 515 Keccak-f permutations. -/
theorem keccak256_h26_layered_k24 (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (haccept : evalWithAnswerFn f (Concrete.verify pk message signature
      : OracleComp HashSpec Bool) = true) :
    verifyCompressions .keccak256 f pk message signature = 515 := by
  have hcalls : digestCalls = 2 := by
    have hℓ := Params.lowerHeight_ge
    have hle := Params.lower_le
    have hbottom : bottomHeight = lowerHeight := by
      unfold bottomHeight layerHeight
      rw [if_neg (by simp only [hd]; omega)]
    unfold digestCalls digestBytes mdBytes treeIndexBytes leafIndexBytes
    rw [hbottom, hH, hk, ha]
    rw [hH, hd] at hle
    omega
  rw [verification_compressions _ f pk message signature haccept, verifyCost, treeCost, hcalls, hH, hd, hk, ha]
  rfl

end h26_layered_k24

end FORS.Configurations
