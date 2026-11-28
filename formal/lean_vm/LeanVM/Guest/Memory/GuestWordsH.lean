/-
  LeanVM.Guest.Memory.GuestWordsH

  The guest's words with its hand functions (`Memory/GuestWordsH/`, `Memory/GuestWordsZ/`, written
  by `scripts/count/hand.py`), checked by the kernel: the check with hand functions, the
  zero-challenge sum counted (`wh_checkedH`) or its functions absent (`wz_checkedH`), and the loop
  hand's iteration check in each (`wh_loopChecked`, `wz_loopChecked`).
-/

module

public import LeanVM.Guest.Memory.GuestWordsH.All
public import LeanVM.Guest.Memory.GuestWordsZ.All
public import LeanVM.Guest.Memory.GuestWordsA

/-!
# The guest's words with hand functions, certified

Every function of the guest's core IR is checked counting words at `fsPad fsW alW`, the weights of
`Memory/GuestWordsA.lean`: the `1533` functions the checker bounds from their arguments by their
certificates, the others as hand functions (`scripts/count/hand.py --report`) over virtual
parameters, their callers seeing their outer certificates:

* `main`, its virtual parameters the loop ends and slot counts of its meta hint;
* `claim_list_digest`, `child_claim_list_digest` (`list_split`'s blocks and groups, outer bounds
  `15` and `45` words a claim of the list), `da_verify` (its blob count and padding);
* in `verify_sub`'s subtree: `squeeze_packed`, `link_rounds__*`, `rs_eq_run`, `ring_rows` (a count's
  quotient, outer bounds by the count), `verify_keccak` (the Keccak table's sizes, outer bound by its
  log height), `open_stacked__L0 ..= L14` (the query positions' total, outer bound at the largest
  rate's), `check_stack_terminal` (the Keccak table's `q_keccak` size, at log height `24`), and
  `verify_sub` (the stream's chunks, the link's permutations, the pointer width, the tallest table,
  the Keccak table: outer bound at `32, 19, 24, 24, 24`).

`da_verify`'s and the children's loop's outer bounds are the node's (`main` their only caller), zero
in the family: `main`'s bound takes them as constants (`Memory/HandNode.lean`). The children's loop
`__loop4_main` is a loop hand: its iteration's inner check is `wh_loopChecked`; it is left out of the
check, with the absent functions (in `wz_*`, the zero-challenge sum's `level_residual_sum__*`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The certificates with the hand functions' outer ones, the zero-challenge sum counted. -/
noncomputable def whCertOf (g : String) : Cert := Data.whcertJ (coreIdx g)
/-- The hand functions' inner checks, the zero-challenge sum counted. -/
noncomputable def whHandOf (g : String) : Option Hand := Data.whhandJ (coreIdx g)
/-- Left out of the check: the loop hand. -/
noncomputable def whOut (g : String) : Prop :=
  Data.whabsJ (coreIdx g) = true ∨ (Data.whloopJ (coreIdx g)).isSome = true

/-- The certificates with the hand functions' outer ones, the zero-challenge sum absent. -/
noncomputable def wzCertOf (g : String) : Cert := Data.wzcertJ (coreIdx g)
/-- The hand functions' inner checks, the zero-challenge sum absent. -/
noncomputable def wzHandOf (g : String) : Option Hand := Data.wzhandJ (coreIdx g)
/-- Left out of the check: the zero-challenge sum's functions and the loop hand. -/
noncomputable def wzOut (g : String) : Prop :=
  Data.wzabsJ (coreIdx g) = true ∨ (Data.wzloopJ (coreIdx g)).isSome = true

theorem waomega_eq (j : ℕ) (hj : j < coreProgram.length) :
    fsPad fsW alW coreProgram[j].name = Data.waomegaJ j := by
  simp only [fsPad, fsW, alW, coreIdx_getElem hj, Data.waomegaJ]

/-- **The guest's check with hand functions, the zero-challenge sum counted**, by the kernel. -/
theorem wh_checkedH : CheckedH coreProgram true whCertOf (fsPad fsW alW) whHandOf whOut :=
  checkedH_of_chkHJ wh_all waomega_eq

/-- **The guest's check with hand functions, the zero-challenge sum absent**, by the kernel. -/
theorem wz_checkedH : CheckedH coreProgram true wzCertOf (fsPad fsW alW) wzHandOf wzOut :=
  checkedH_of_chkHJ wz_all waomega_eq

/-- **The loop hand's iteration checks**, the zero-challenge sum counted. -/
theorem wh_loopChecked {j : ℕ} (hj : j < coreProgram.length) {h : Hand} {endc : Option ℕ}
    (hl : Data.whloopJ j = some (h, endc)) (ha : Data.whabsJ j = false) :
    chkHandL (lookS Data.whcertJ j) (omLookS Data.waomegaJ j) true h endc (Data.waomegaJ j) coreProgram[j] = true :=
  loopHand_checked wh_all hj hl ha

/-- **The loop hand's iteration checks**, the zero-challenge sum absent. -/
theorem wz_loopChecked {j : ℕ} (hj : j < coreProgram.length) {h : Hand} {endc : Option ℕ}
    (hl : Data.wzloopJ j = some (h, endc)) (ha : Data.wzabsJ j = false) :
    chkHandL (lookS Data.wzcertJ j) (omLookS Data.waomegaJ j) true h endc (Data.waomegaJ j) coreProgram[j] = true :=
  loopHand_checked wz_all hj hl ha

end
end LeanVM.Guest.Memory
