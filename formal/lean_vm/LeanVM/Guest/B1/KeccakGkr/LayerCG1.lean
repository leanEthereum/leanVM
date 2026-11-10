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
(`o + 739`) or the cursor after the pack rounds (`o + 745`). `layer_residOk`: the loads the lane
weights, the weight section, the slices' weights, the top coordinate and the flips read are not
stores, and the flips' writes are.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd

@[expose] public section

theorem layerT_sections (first : ℕ) : layerT first =
    secA1 first ++ (secA2 first ++ (rmfeBlockT (layOff first) ++ (hornerS first ++
      (packSetupT (layOff first) first ++ (lastT (layOff first) ++ (localS (layOff first) ++
        (tReadsT (layOff first) ++ (eqfS (layOff first) ++ (weightT first (layOff first) ++
          tailT (layOff first) (tW first) (tV first)))))))))) := by
  simp only [layerT, secA1, secA2, hornerS, localS, eqfS, tW, tV, List.append_assoc]

theorem layer_noStore {first : ℕ} (hf : first < 2) :
    noStoreVia [.n 7, .n 11, .n (layOff first + 739), .n (layOff first + 745)] (layerSt first) =
      true := by
  interval_cases first <;> decide +kernel

theorem layer_residOk {first : ℕ} (hf : first < 2) :
    noneIn (resid (atomsL (eqfS (layOff first)))) (layerSt first) = true ∧
    noneIn (resid (atomsL (weightT first (layOff first)))) (layerSt first) = true ∧
    noneIn (resid (atomsL (tailEqf (layOff first) (tW first)))) (layerSt first) = true ∧
    noneIn [.load (.n (topV (tW first))) (.n (layOff first + 748)) 5] (layerSt first) = true ∧
    (∀ i < 7, noneIn (resid (atomsL (layerFlipT (tW first) i))) (layerSt first) = true) ∧
    (∀ i < 7, (layerSt first).contains (.load (.n (flipB (tW first) i + 42))
      (.n (topV (tW first) + 3)) i) = true) := by
  interval_cases first
  all_goals exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end
end LeanVM.Guest.B1.VerifySub
