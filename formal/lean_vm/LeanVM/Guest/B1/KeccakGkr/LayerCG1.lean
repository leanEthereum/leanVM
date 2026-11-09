/-
  LeanVM.Guest.B1.KeccakGkr.LayerCG1

  `keccak_layer`'s body as its completeness sections, and the kernel facts the assembly needs
  about its stores.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCSpec
public import LeanVM.Guest.B1.KeccakGkr.LayerCF
public import LeanVM.Guest.B1.KeccakGkr.StoreFacts

/-!
# The sections and the stores

`layerT_sections`: the body is the sections the completeness lemmas take, in order.
`layer_noStore`: no store goes through the cursor (`7`), the claim (`11`), the last record
(`1072`) or the cursor after the pack rounds (`1078`). `layer_residOk`: the loads the lane
weights, the weight section, the slices' weights, the top coordinate and the flips read are not
stores, and the flips' writes are.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem layerT_sections (first : ℕ) : layerT first =
    secA1 first ++ (secA2 first ++ (rmfeBlockT ++ (hornerS first ++ (packSetupT first ++
      (lastT ++ (localS ++ (tReadsT ++ (eqfS ++ (weightT first ++
        tailT (weightEnd first) (weightVal first)))))))))) := by
  simp only [layerT, secA1, secA2, hornerS, localS, eqfS, List.append_assoc]

theorem layer_noStore {first : ℕ} (hf : first < 2) :
    noStoreVia [.n 7, .n 11, .n 1072, .n 1078] (layerSt first) = true := by
  interval_cases first <;> decide +kernel

theorem layer_residOk {first : ℕ} (hf : first < 2) :
    noneIn (resid (atomsL eqfS)) (layerSt first) = true ∧
    noneIn (resid (atomsL (weightT first))) (layerSt first) = true ∧
    noneIn (resid (atomsL (tailEqf (weightEnd first)))) (layerSt first) = true ∧
    noneIn [.load (.n (topV (weightEnd first))) (.n 1081) 5] (layerSt first) = true ∧
    (∀ i < 7, noneIn (resid (atomsL (layerFlipT (weightEnd first) i))) (layerSt first) = true) ∧
    (∀ i < 7, (layerSt first).contains (.load (.n (flipB (weightEnd first) i + 42))
      (.n (topV (weightEnd first) + 3)) i) = true) := by
  interval_cases first
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end
end LeanVM.Guest.B1.VerifySub
