/-
  LeanVM.Guest.B1.Digest.MonoAt

  `child_claim_list_mono`'s honest shape and words, for its placed completeness (`MonoAtNP.lean`).
-/

module

public import LeanVM.Guest.B1.Digest.MonoAt0
public import LeanVM.Guest.B1.Digest.ChildListAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono»

/-!
# The gap walk, its shape

`monoHonest n` (`monoQ`, `monoCalls`, `monoBufs`): the honest shape of `child_claim_list_mono` on
`n` claims; `monoB fs n`: its words.
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

/-! ## The honest shape -/

/-- `child_claim_list_mono`'s words that end its loops and size its buffer
(`n = 136a + 17b + c`): `g^a`, `g^b`, `g^c` at `v4`, `v5`, `v6`, the chain buffer's size
`g^(15 (a + b + 1))` at `v15`, the loops' start `1` at `v32`, `v42`. -/
def monoQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n (val% «child_claim_list_mono» "bigs")) = gen ^ (n / 136) ∧ σ (.n (val% «child_claim_list_mono» "groups")) = gen ^ (n % 136 / 17) ∧ σ (.n (val% «child_claim_list_mono» "rest")) = gen ^ (n % 17) ∧
    σ (.n (val% «child_claim_list_mono» "chain~8")) = gen ^ (15 * (n / 136 + n % 136 / 17 + 1)) ∧ σ (.n (val% «child_claim_list_mono» "s4#2")) = 1 ∧ σ (.n (val% «child_claim_list_mono» "s6#2")) = 1

/-- `child_claim_list_mono`'s calls: `child_claim_list_mono_loop0` when `n / 136 ≠ 0`,
`child_claim_list_mono_loop1` when `n % 136 / 17 ≠ 0`, `child_claim_list_mono_last__L{n % 17}`. -/
def monoCalls (n : ℕ) (_ : Val) : List Call :=
  [⟨name% «child_claim_list_mono_loop0», [.n (val% «child_claim_list_mono» "s4#2"), .n (val% «child_claim_list_mono» "bigs"), .n (val% «child_claim_list_mono» "chain"), .n (val% «child_claim_list_mono» "base")], [], decide (n / 136 ≠ 0)⟩,
    ⟨name% «child_claim_list_mono_loop1», [.n (val% «child_claim_list_mono» "s6#2"), .n (val% «child_claim_list_mono» "groups"), .n (val% «child_claim_list_mono» "mid"), .n (val% «child_claim_list_mono» "base")], [],
      decide (n % 136 / 17 ≠ 0)⟩,
    ⟨mlNames[n % 17]!, [.n (val% «child_claim_list_mono» "last"), .n (val% «child_claim_list_mono» "region"), .n (val% «child_claim_list_mono» "base"), .n (val% «child_claim_list_mono» "limit_g")], [.n (val% «child_claim_list_mono» "d0"), .n (val% «child_claim_list_mono» "d1")], true⟩]

/-- `child_claim_list_mono`'s `HeapBuf`: the chain buffer. -/
def monoBufs (n : ℕ) (_ : Val) : List ℕ := [15 * (n / 136 + n % 136 / 17 + 1)]

/-- No constraint on `child_claim_list_mono`'s callees. -/
def monoTs : List (Tree → Prop) := [fun _ => True, fun _ => True, fun _ => True]

/-- **`child_claim_list_mono`'s honest shape** on `n` claims. -/
def monoHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "child_claim_list_mono" (monoQ n) (monoCalls n) (monoBufs n) monoTs

/-- **`child_claim_list_mono`'s words** on `n = 136a + 17b + c` claims: its frame, its chain
buffer `15 (a + b + 1)`, `child_claim_list_mono_loop0` within `a` frames and its tail (its tail when
not entered), `child_claim_list_mono_loop1` within `b` and its tail, `child_claim_list_mono_last__L{c}` a leaf
within its frame. -/
def monoB (fs : String → ℕ) (n : ℕ) : ℕ :=
  fs "child_claim_list_mono" + 15 * (n / 136 + n % 136 / 17 + 1) +
    ((if n / 136 ≠ 0 then n / 136 * fs name% «child_claim_list_mono_loop0» + fs (tailKey name% «child_claim_list_mono_loop0») else fs
        (tailKey name% «child_claim_list_mono_loop0»)) +
      ((if n % 136 / 17 ≠ 0 then n % 136 / 17 * fs name% «child_claim_list_mono_loop1» + fs (tailKey name% «child_claim_list_mono_loop1») else
          fs (tailKey name% «child_claim_list_mono_loop1»)) +
        (fs (mlNames.getD (n % 17) "") + 0)))

theorem mono136_find : coreProgram.find? name% «child_claim_list_mono_loop0» =
    some (coreProgram.getD idx% «child_claim_list_mono_loop0» default) := find_of_idx mono136_idx

theorem mono17_find : coreProgram.find? name% «child_claim_list_mono_loop1» =
    some (coreProgram.getD idx% «child_claim_list_mono_loop1» default) := find_of_idx mono17_idx

end
end LeanVM.Guest.B1.Digest
