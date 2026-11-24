/-
  LeanVM.Guest.B1.Digest.ClaimListsAtM

  `child_claim_list_digest`'s honest shape and words on either walk: the hint `child_mono = g` takes
  the gap walk `child_claim_list_mono`, any other hint `h` with `h + g` nonzero in `K` the walk by
  hinted indices `child_claim_list_any` (the honest prover hints `count 0 = 1` there).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListsAtTB
public import LeanVM.Guest.B1.Digest.MonoAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_digest»

/-!
# A child's claim list, on either walk

`ccQH n h`: `ccQ n` with the hint `h` at `v29`. `ccCallsM mono n`, `ccTsM mono n`: `list_split`,
then `child_claim_list_mono` (by `monoHonest n`) or `child_claim_list_any` (by `anyHonest n`).
`ccBM fs SB mono n`: the words, `monoB` or `anyB` after `list_split`. The placed completeness on
either walk is `ClaimListsAtMP.lean`'s.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB
  kidsBoundL Returns Kid DisjL Within regionsOk_of LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (exists_of_length_succ)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-! ## The honest shape -/

/-- `ccQ n` with the hint `child_mono = h`. -/
def ccQH (n : ℕ) (h : E) (σ : Val) : Prop :=
  σ (.n (val% «child_claim_list_digest» "n_g")) = gen ^ n ∧ (n ≠ 0 → σ (.n (val% «child_claim_list_digest» "bigs")) = gen ^ (n / 136) ∧ σ (.n (val% «child_claim_list_digest» "groups")) = gen ^ (n % 136 / 17) ∧
    σ (.n (val% «child_claim_list_digest» "rest")) = gen ^ (n % 17) ∧ σ (.n (val% «child_claim_list_digest» "mono")) = h)

/-- The walk's call: `child_claim_list_mono` or `child_claim_list_any`. -/
def ccWalkCall (mono : Bool) : Call :=
  if mono then ⟨"child_claim_list_mono", [.n (val% «child_claim_list_digest» "entries_ptr"), .n (val% «child_claim_list_digest» "region"), .n (val% «child_claim_list_digest» "base"), .n (val% «child_claim_list_digest» "limit_g"), .n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")],
      [.n (val% «child_claim_list_digest» "d0@1"), .n (val% «child_claim_list_digest» "d1@1")], true⟩
  else ⟨"child_claim_list_any", [.n (val% «child_claim_list_digest» "entries_ptr"), .n (val% «child_claim_list_digest» "region"), .n (val% «child_claim_list_digest» "base"), .n (val% «child_claim_list_digest» "limit_g"), .n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")], [.n (val% «child_claim_list_digest» "d0@2"), .n (val% «child_claim_list_digest» "d1@2")], true⟩

/-- `child_claim_list_digest`'s calls on either walk. -/
def ccCallsM (mono : Bool) (n : ℕ) (_ : Val) : List Call :=
  if n = 0 then [] else [⟨"list_split", [.n (val% «child_claim_list_digest» "n_g")], [.n (val% «child_claim_list_digest» "bigs"), .n (val% «child_claim_list_digest» "groups"), .n (val% «child_claim_list_digest» "rest")], true⟩, ccWalkCall mono]

/-- The walk's tree of honest shape. -/
def ccTsM (mono : Bool) (n : ℕ) : List (Tree → Prop) :=
  [fun _ => True, if mono then monoHonest n else anyHonest n]

/-- **`child_claim_list_digest`'s honest shape** on `n` claims, the walk `mono`, the hint `h`. -/
def ccHonestH (n : ℕ) (mono : Bool) (h : E) : Tree → Prop :=
  NodeHonest coreProgram "child_claim_list_digest" (ccQH n h) (ccCallsM mono n) (ccBufs n)
    (ccTsM mono n)

theorem ccQ_eq (n : ℕ) : ccQ n = ccQH n 0 := rfl

theorem ccCalls_eq (n : ℕ) : ccCalls n = ccCallsM false n := by
  funext σ; simp [ccCalls, ccCallsM, ccWalkCall]

theorem ccTs_eq (n : ℕ) : ccTs n = ccTsM false n := by simp [ccTs, ccTsM]

/-- `child_claim_list_digest`'s honest shape at the hint `0` is `ccHonestH` on the walk by hinted
indices. -/
theorem nodeHonest_cc_eq (n : ℕ) :
    NodeHonest coreProgram "child_claim_list_digest" (ccQ n) (ccCalls n) (ccBufs n) (ccTs n) =
      ccHonestH n false 0 := by
  rw [ccHonestH, ccQ_eq, ccCalls_eq, ccTs_eq]

/-! ## The nonempty list -/

/-- The nonempty list's valuation at the hint `h`. -/
noncomputable def ccEσH (eP rg L n : ℕ) (base : E) (D : Digest) (h : E) : Val :=
  B1.Val.ofArgs [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ n, word 1 0, gen ^ n + word 1 0,
    0, 0, 0, 0, 0, 0, (digestHalves D).1, (digestHalves D).2,
    gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17), h, word 2 0, h + word 2 0,
    (digestHalves D).1, (digestHalves D).2,
    (digestHalves D).1, (digestHalves D).2, (digestHalves D).1, (digestHalves D).2]

/-- `child_claim_list_digest`'s callees on a nonempty list, on either walk. -/
def ccKidsM (Lin : Main.Layout) (eP rg L n : ℕ) (base : E) (D : Digest) (mono : Bool) :
    List Kid :=
  [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]⟩,
    ⟨if mono then "child_claim_list_mono" else "child_claim_list_any", true, [gen ^ eP, gen ^ rg,
      base, gen ^ L, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)], Lin,
      Returns (digestCells D)⟩]

/-- The arm a hint takes. -/
def ccArm (mono : Bool) : List Stmt := if mono then ccMonoArm else ccAnyArm

/-! ## Within bounds -/

/-- **`child_claim_list_digest`'s words** on `n` claims, on the walk `mono`. -/
def ccBM (fs : String → ℕ) (SB : String → ℕ) (mono : Bool) (n : ℕ) : ℕ :=
  if n = 0 then fs "child_claim_list_digest" else
    fs "child_claim_list_digest" + (SB "list_split" + ((if mono then monoB fs n else anyB fs n) + 0))

/-- The empty list on any hint: the shape at `0` claims names no hint and no callee. -/
theorem ccHonestH_zero {mono : Bool} {h : E} {t : Tree} (ht : ccHonestH 0 false 0 t) :
    ccHonestH 0 mono h t := by
  obtain ⟨σ, ks, rfl, hQ, hc, -, -⟩ := ht
  have e : ∀ m, ccCallsM m 0 σ = [] := fun m => by simp [ccCallsM]
  refine ⟨σ, ks, rfl, ⟨hQ.1, fun h0 => absurd rfl h0⟩, fun fn es vs hf hw => ?_, ?_, ?_⟩
  · rw [hc fn es vs hf hw, e, e]
  · rw [e]; exact Nat.zero_le _
  · rw [e]; trivial

end
end LeanVM.Guest.B1.Digest
