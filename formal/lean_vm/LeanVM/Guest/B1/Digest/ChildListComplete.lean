/-
  LeanVM.Guest.B1.Digest.ChildListComplete

  `child_claim_list_any`'s frame loops `child_claim_list_any_loop0` and
  `child_claim_list_any_loop1`, completely and placed: from the chain buffer's states and the honest
  records among the caller's words.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListCLast
public import LeanVM.Guest.B1.Digest.ClaimListComplete
public import LeanVM.Guest.B1.Digest.PlacedLib
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.B1.Digest.ClaimListCChk
public import LeanVM.Guest.B1.Main.KidsT
public import LeanVM.Guest.Budget.Bounded

/-!
# The frames of child claims, placed

`recMem_group`: the records of claims `s, …, s + k - 1` of honest records are honest, the marks
`base · g^s`. `any136_unplaced`,
`any17_unplaced`: `child_claim_list_any_loop0`, `child_claim_list_any_loop1` place nothing before
their loop.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.Memory (atomUnplaced)
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDTB Returns LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {rd : Reader}

/-- The records of the claims `s, …, s + k - 1`. -/
theorem recMem_group {region limit entries base : E} {n : ℕ} {o : ℕ → ℕ} {cells : List E}
    (h : RecMem rd region limit entries base n o cells) {s k : ℕ} (hsk : s + k ≤ n) :
    RecMem rd region limit entries (base * gen ^ s) k (fun j => o (s + j))
      ((cells.drop (4 * s)).take (4 * k)) := by
  intro j hj
  obtain ⟨h1, h2, h3⟩ := h (s + j) (by omega)
  refine ⟨h1, by rwa [mul_assoc, ← pow_add], fun c hc => ?_⟩
  have e : ((cells.drop (4 * s)).take (4 * k)).getD (4 * j + c) 0 =
      cells.getD (4 * (s + j) + c) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    rw [ite_pos' (by omega), show 4 * s + (4 * j + c) = 4 * (s + j) + c by ring]
  rw [e]
  exact h3 c hc

theorem boundMem_of_low {κ : ℕ} (hl : LowDef κ rd) {L : ℕ} (hL : L ≤ 2 ^ κ) : BoundMem rd L :=
  fun i hi => ⟨_, by rw [gen_pow_eq_ofK]; exact B1.loadHolds_low hl (by omega)⟩

set_option maxRecDepth 100000 in
theorem any136_unplaced :
    (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_any_loop0» default))).all
        atomUnplaced = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem any17_unplaced :
    (atomsIn (loopPre (coreProgram.getD idx% «child_claim_list_any_loop1» default))).all
        atomUnplaced = true := by decide +kernel

end
end LeanVM.Guest.B1.Digest
