/-
  LeanVM.Guest.B1.Digest.ClaimListsAtTB

  `child_claim_list_digest` by a tree of honest shape, within bounds before the memory
  (`CompleteAtDTB`), for the budget's words: `child_claim_list_digest_completeAtT` (same proof,
  `cc_nonempty`) with its callees' bounds.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListsAtT
public import LeanVM.Guest.B1.Digest.ClaimListAtTB

/-!
# A child's claim list, within bounds

`ccB fs SB n`: `child_claim_list_digest`'s words on `n = 136a + 17b + c` claims: its frame; when
`n ≠ 0`, `list_split`'s static bound `SB "list_split"` (a hypothesis, `TotalLe`) and
`child_claim_list_any`'s `anyB fs n` (its frame, its chain buffer `13 (a + b + 1)`, `__loop17`
within `a + 1` frames, `__loop18` within `b + 1`, `child_claim_list_last__L{c}` a leaf within its
frame; a loop's frame alone when not entered). `child_claim_list_digest_completeAtTB`: the placed
completeness by a tree of honest shape within `ccB fs SB n`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB kidsBoundL Returns Kid)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- **`child_claim_list_digest`'s words** on `n` claims (the walk by hinted indices). -/
def ccB (fs : String → ℕ) (SB : String → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then fs "child_claim_list_digest" else
    fs "child_claim_list_digest" + (SB "list_split" + (anyB fs n + 0))

theorem kidsAt_of_kidsDTB {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {ks : List Kid}
    {Ts : List (Tree → Prop)} {Bs : List ℕ} (h : KidsDTB fs cert κ ks Ts Bs) (b : ℕ) :
    KidsAt fs cert κ ks Ts (· ≤ kidsBoundL fs ks Bs) b :=
  let ⟨N, L, outs, hN, ho, hW, hD, hI, hK⟩ := kidsFromInT_of_kidsDTB κ ks Ts Bs h b
  ⟨N, L, outs, hN, ho, hW, hD, hI, hK⟩

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

/-- **`child_claim_list_digest` is complete, placed, by a tree of honest shape, within
`ccB fs SB n`**: `n < 136 · 2^20` honest records among the caller's words; it returns their
cells' digest. -/
theorem child_claim_list_digest_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    (hκ : 20 ≤ κ) {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n) (hc : AllCanonical cells)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) {SB : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split")) :
    CompleteAtDTB fs cert κ "child_claim_list_digest" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (ccBufs n) (ccTs n))
      (ccB fs SB n) := by
  intro fp
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    exact ⟨fs "child_claim_list_digest", [], _, [], by simp [ccB], ⟨rfl, rfl⟩,
      fun q hq => by simp at hq, B1.disj_nil, fun rd _ _ => cc_empty fs cert fp rd⟩
  have hok : KidsDTB fs cert κ (ccKids Lin eP rg L n base (keccak256 (cellsBytes cells))) (ccTs n)
      [SB "list_split", anyB fs n] :=
    ⟨fun _ => list_split_nB fs cert hκ hn hLS,
      fun _ => child_claim_list_any_completeAtTB fs cert hn hl hc hL33 hLκ hrec hR2 hR3, trivial⟩
  obtain ⟨N, Lown, rets, Lout, hN, ⟨rfl, rfl⟩, hW, hD, hr⟩ :=
    cc_nonempty fs cert (by omega) hn fp (kidsAt_of_kidsDTB hok _)
  refine ⟨_, Lown, _, [], ?_, ⟨rfl, rfl⟩, hW, hD, hr⟩
  simp only [kidsBoundL, ccKids, List.headD_cons, List.tail_cons, ↓reduceIte] at hN
  simp only [ccB, show n ≠ 0 by omega, ↓reduceIte]
  omega

end
end LeanVM.Guest.B1.Digest
