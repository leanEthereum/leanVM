/-
  LeanVM.Guest.B1.Main.WordsDefs

  The constants of `main`'s words budget (`MainWords.lean`), in the frame sizes `fs` and the static
  bounds `SB`, `SK`: `da_verify`'s, the claim lists' digests', the children's loop's and
  `aggregate_claims`'. Definitions only, so that the deployed numbers (`Count/Deployed*`) need not
  wait for `main`'s proofs.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.B1.Main.IterK
public import LeanVM.Guest.Memory.Alloc
public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Digest.MonoDefs
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Consts

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Memory

@[expose] public section

/-- The bounds `g` of the first `n` names of `names`. -/
def nameSum (g : String → ℕ) (names : List String) (n : ℕ) : ℕ :=
  ((List.range n).map fun j => g names[j]!).sum

theorem le_nameSum {g : String → ℕ} {names : List String} {n j : ℕ} (hj : j < n) :
    g names[j]! ≤ nameSum g names n :=
  List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

variable (fs SB SK : String → ℕ)

/-! ## `da_verify` -/

/-- The words of the tree over the blob roots per row of the padded matrix, at most:
`⌈SB dlTop / DA_MAX_ROWS⌉`. -/
def dlK : ℕ := (SB Da.dlTop + guest_const% DA_MAX_ROWS - 1) / guest_const% DA_MAX_ROWS

/-- `da_verify`'s constant words: its frame, `da_padding`'s frame, `da_vector`'s and `da_weights`'
words, the blob loop's phantom frame, `da_pad`'s and its loop's phantom frame (or its frame when it
does not run): a static loop helper's run is charged its phantom frame once, here, and
`iterK fs SK g` per iteration. -/
def dvC : ℕ :=
  fs "da_verify" + fs "da_padding" + SB "da_vector" + SB "da_weights" +
    fs name% «da_verify_loop0» + fs "da_pad" + fs name% «da_pad_loop0»

/-- `da_verify`'s words per blob: the blob loop's iteration past the padding loop's
(`iterK`). -/
def dvS : ℕ := iterK fs SK name% «da_verify_loop0» - iterK fs SK name% «da_pad_loop0»

/-- `da_verify`'s words per padded blob: the roots (`4`), the padding loop's iteration, the
levels. -/
def dvP : ℕ := 4 + iterK fs SK name% «da_pad_loop0» + dlK SB

/-! ## The claim lists -/

/-- A claim list's digest's constant words. -/
def clC : ℕ :=
  fs "claim_list_digest" + 13 + SB "list_split" + fs "claim_list_chain" + fs name% «claim_list_chain_loop0» + fs
      name% «claim_list_chain_loop1» + SB "claim_list_tail"

/-- A claim list's digest's words per claim: `13` and a `claim_list_chain_loop0` iteration per
`136` claims (`CLAIM_BIG`), `13` and a `claim_list_chain_loop1` iteration per `17` claims
(`CLAIM_GROUP`), the loops' runs'
phantom frames in the constant (`clC`). -/
def clS : ℕ := 1 + (iterK fs SK name% «claim_list_chain_loop0» + 135) / 136 + (iterK fs SK
    name% «claim_list_chain_loop1» + 16) / 17

/-- A child's claim list's digest's constant words, on either walk: its frame, `list_split`, the
walk's frame and its chain's first record (at most `15` words), its two loops' frames twice and
its last group's helper, each the larger of the two walks'. -/
def ccC : ℕ :=
  fs "child_claim_list_digest" + 15 + SB "list_split" +
    max (fs "child_claim_list_any") (fs "child_claim_list_mono") +
    2 * max (fs name% «child_claim_list_any_loop0») (fs name% «child_claim_list_mono_loop0») +
    2 * max (fs name% «child_claim_list_any_loop1») (fs name% «child_claim_list_mono_loop1») +
    max (nameSum (fun g => fs g) B1.Digest.cclNames 17) (nameSum (fun g => fs g) B1.Digest.mlNames 17)

/-- A child's claim list's digest's words per claim, on either walk: a record (at most `15` words)
and a big loop's frame per `136` claims, a record and a group loop's frame per `17` claims. -/
def ccS : ℕ :=
  1 + (max (fs name% «child_claim_list_any_loop0») (fs name% «child_claim_list_mono_loop0») + 135) / 136 +
    (max (fs name% «child_claim_list_any_loop1») (fs name% «child_claim_list_mono_loop1») + 16) / 17

/-! ## The children's loop -/

/-- A child's constant words in the children's loop (but `verify_sub`'s): the iteration's frame,
its claim lists' digests' constants, `statement_digest`. -/
def l5A1 : ℕ := fs name% «main_loop4» + 2 * ccC fs SB + SB "statement_digest"

/-- The children's loop's words per child's claim. -/
def l5A2 : ℕ := ccS fs

/-- The children's loop's constant words: its last call's phantom. -/
def l5A0 : ℕ := fs (tailKey name% «main_loop4»)

/-! ## `aggregate_claims` -/

/-- `aggregate_claims`' constant words. -/
def agA0 : ℕ := fs "aggregate_claims" + 109 + SB "batch_sumcheck__L23"

/-- `aggregate_claims`' words per child: its buffers' and its three loops' iterations, each with
its run's phantom frame, which `agA0` would otherwise charge `main` when it has no child. -/
def agA1 : ℕ := 18 + (iterK fs SK name% «aggregate_claims_loop0» + fs
    name% «aggregate_claims_loop0») + (iterK fs SK name% «aggregate_claims_loop1» + fs
    name% «aggregate_claims_loop1») +
  (iterK fs SK name% «aggregate_claims_loop2» + fs name% «aggregate_claims_loop2»)

end
end LeanVM.Guest.B1.Main
