/-
  LeanVM.Guest.B1.Digest.ChildListAt

  `child_claim_list_any`'s honest shape and words, for its placed completeness
  (`ChildListAtNP.lean`).
-/

module

public import LeanVM.Guest.B1.Digest.ChildListAt0
public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_any»

/-!
# The walk by hinted indices, its shape

`anyHonest n` (`anyQ`, `anyCalls`, `anyBufs`): the honest shape of `child_claim_list_any` on `n`
records; `anyB fs n`: its words.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB
  kidsBoundL Returns Kid DisjL Within disj_append regionsOk_of within_append LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

theorem regionL_append_left {L L' : Main.Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append_right {L L' : Main.Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_right _ hq, h1, h2⟩

/-! ## The honest shape -/

/-- `child_claim_list_any`'s words that end its loops and size its buffer (`n = 136a + 17b + c`):
`g^a`, `g^b`, `g^c` at `v4`, `v5`, `v6` (the first two end `child_claim_list_any_loop0`,
`child_claim_list_any_loop1`), the chain
buffer's size `g^(13 (a + b + 1))` at `v16`, the loops' start `1` at `v33`, `v51`. -/
def anyQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «child_claim_list_any» "bigs")) = gen ^ (n / 136) ∧ σ (.n (val% «child_claim_list_any» "groups")) = gen ^ (n % 136 / 17) ∧ σ (.n (val% «child_claim_list_any» "rest")) = gen ^ (n % 17) ∧
    σ (.n (val% «child_claim_list_any» "chain~7")) = gen ^ (13 * (n / 136 + n % 136 / 17 + 1)) ∧ σ (.n (val% «child_claim_list_any» "s3#2")) = 1 ∧ σ (.n (val% «child_claim_list_any» "s6#2")) = 1

/-- `child_claim_list_any`'s calls: `child_claim_list_any_loop0` when `n / 136 ≠ 0`,
`child_claim_list_any_loop1` when
`n % 136 / 17 ≠ 0`, `child_claim_list_last__L{n % 17}`. -/
def anyCalls (n : ℕ) (_ : Val) : List Call :=
  [⟨name% «child_claim_list_any_loop0», [.n (val% «child_claim_list_any» "s3#2"), .n (val% «child_claim_list_any» "bigs"), .n (val% «child_claim_list_any» "chain"), .n (val% «child_claim_list_any» "entries_ptr"), .n (val% «child_claim_list_any» "region"), .n (val% «child_claim_list_any» "base"), .n (val% «child_claim_list_any» "last_g")], [],
      decide (n / 136 ≠ 0)⟩,
    ⟨name% «child_claim_list_any_loop1», [.n (val% «child_claim_list_any» "s6#2"), .n (val% «child_claim_list_any» "groups"), .n (val% «child_claim_list_any» "mid"), .n (val% «child_claim_list_any» "entries_ptr"), .n (val% «child_claim_list_any» "region"), .n (val% «child_claim_list_any» "mid_base"), .n (val% «child_claim_list_any» "last_g")], [],
        decide (n % 136 / 17 ≠ 0)⟩,
    ⟨cclNames[n % 17]!, [.n (val% «child_claim_list_any» "last"), .n (val% «child_claim_list_any» "entries_ptr"), .n (val% «child_claim_list_any» "region"), .n (val% «child_claim_list_any» "d0~6"), .n (val% «child_claim_list_any» "last_g")], [.n (val% «child_claim_list_any» "d0"), .n (val% «child_claim_list_any» "d1")], true⟩]

/-- `child_claim_list_any`'s `HeapBuf`: the chain buffer. -/
def anyBufs (n : ℕ) (_ : Val) : List ℕ := [13 * (n / 136 + n % 136 / 17 + 1)]

/-- No constraint on `child_claim_list_any`'s callees. -/
def anyTs : List (Tree → Prop) := [fun _ => True, fun _ => True, fun _ => True]

/-- **`child_claim_list_any`'s honest shape** on `n` claims. -/
def anyHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "child_claim_list_any" (anyQ n) (anyCalls n) (anyBufs n) anyTs

/-- **`child_claim_list_any`'s words** on `n = 136a + 17b + c` claims: its frame, its chain buffer
`13 (a + b + 1)`, `child_claim_list_any_loop0` within `a` frames and its tail (its tail when not
entered), `child_claim_list_any_loop1` within `b` and its tail, `child_claim_list_last__L{c}` a leaf
within its frame. -/
def anyB (fs : String → ℕ) (n : ℕ) : ℕ :=
  fs "child_claim_list_any" + 13 * (n / 136 + n % 136 / 17 + 1) +
    ((if n / 136 ≠ 0 then n / 136 * fs name% «child_claim_list_any_loop0» + fs (tailKey name% «child_claim_list_any_loop0») else fs
        (tailKey name% «child_claim_list_any_loop0»)) +
      ((if n % 136 / 17 ≠ 0 then n % 136 / 17 * fs name% «child_claim_list_any_loop1» + fs (tailKey name% «child_claim_list_any_loop1») else fs
          (tailKey name% «child_claim_list_any_loop1»)) +
        (fs (cclNames.getD (n % 17) "") + 0)))

end
end LeanVM.Guest.B1.Digest
