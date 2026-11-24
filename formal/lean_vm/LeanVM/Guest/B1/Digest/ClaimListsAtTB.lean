/-
  LeanVM.Guest.B1.Digest.ClaimListsAtTB

  `child_claim_list_digest`'s callees within bounds before the memory (`CompleteAtDTB`), for the
  budget's words.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListsAtT
public import LeanVM.Guest.B1.Digest.ClaimListAtTB

/-!
# A child's claim list, within bounds

`list_split_nB`: `list_split` on `g^n` within its static bound (a hypothesis, `TotalLe`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB kidsBoundL Returns Kid)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- `list_split` on `g^n`, within its static bound. -/
theorem list_split_nB (fs : String → ℕ) (cert : String → V → ℕ) {κ n : ℕ} (hκ : 20 ≤ κ)
    (hn : n < claimBig * bigFramesCap) {Bls : ℕ}
    (hT : TotalLe coreProgram fs "list_split" (fun _ => Bls)) :
    CompleteAtDTB fs cert κ "list_split" [] [gen ^ n]
      (Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]) (fun _ => True) Bls := by
  simp only [claimBig, bigFramesCap] at hn
  have := list_split_completeAtDTB fs cert (a := n / 136) (b := n % 136 / 17) (c := n % 17) hκ
    (by simp [bigFramesCap]; omega) (by simp [bigGroups]; omega) (by simp [claimGroup]; omega) hT
  rwa [show claimBig * (n / 136) + claimGroup * (n % 136 / 17) + n % 17 = n by
    simp [claimBig, claimGroup]; omega] at this

end
end LeanVM.Guest.B1.Digest
