/-
  LeanVM.Guest.Lift.OsCallees

  `open_stacked`'s callees complete in the uniform placed form, on the regions they load:
  `CompleteRelRegD`, from each callee's `Rel`-level meaning and a kernel check of its body.
-/

module

public import LeanVM.Guest.Lift.RegD
public import LeanVM.Guest.B1.Fs.MessageComplete
public import LeanVM.Guest.B1.Fs.SqueezePoint
public import LeanVM.Guest.B1.Fs.TailRound
public import LeanVM.Guest.B1.Merkle.CapAll
public import LeanVM.Guest.B1.Eq.FoldFinal
public import LeanVM.Guest.B1.Bits.GrindPlaced
public import LeanVM.Guest.B1.Whir.Round

/-!
# `open_stacked`'s callees, placed on their regions

The form `CompleteRelRegD` and its lift `completeRelRegD_of_iff` are in `Lift/RegD.lean`.

**The leaves** (`OsCalleesRegD`, `osCalleesRegD_holds`): `opening_message__L{n}_L{nonce}`,
`squeeze_point_from__L{n}`, `opening_tail_round`,
`verify_merkle_cap__L{D}`, `fold_final_msg__L{n}`, with their meanings (B1's `*_holds`) and the
loads a kernel check of each body bounds (`*Spec`); `grind_check__L{bits}` by its own placed
form (`grind_check_completeD`, its table reads forced into the caller's words).
`opening_round` calls `grind_check__L8`, so it is not a leaf: its placed form is a field of its
own (`OsRoundRegD`). `decode_query_windows`, which writes its own frame run, has its own form
(`QwDecodeAtD`, `B1/Bits/QueryWindowsAt.lean`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.Lift (anyAtom)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-! ## The callees' loads -/

/-- `opening_message__L{n}_L{nonce}`'s loads: `n + nonce` words at the cursor (argument 5), `n` at
`out` (6). -/
def msgSpec (n nonce : ℕ) : List (ℕ × ℕ) := [(5, n + nonce), (6, n)]

/-- `squeeze_point_from__L{n}`'s: the `n` coordinates at `point` (argument 6). -/
def spfSpec (n : ℕ) : List (ℕ × ℕ) := [(6, n)]

/-- `opening_tail_round`'s: the two words at the cursor (argument 5). -/
def tailSpec : List (ℕ × ℕ) := [(5, 2)]

/-- `opening_round`'s: the five words at the cursor (argument 5), `α` at `alphas` (8), `α, β` at
`coefs` (9). -/
def roundSpec : List (ℕ × ℕ) := [(5, 5), (8, 1), (9, 2)]

/-- `verify_merkle_cap__L{D}`'s: the cap's `2^(D+2)` cells (0), the `2^D` flags (1). -/
def merkleCapSpec (D : ℕ) : List (ℕ × ℕ) := [(0, 2 ^ (D + 2)), (1, 2 ^ D)]

/-- `fold_final_msg__L{n}`'s: the `2^n` message words (0), the `n` coordinates (1). -/
def foldFinalSpec (n : ℕ) : List (ℕ × ℕ) := [(0, 2 ^ n), (1, n)]

/-- **`opening_round`, placed on its regions**: its meaning, the window tables at `tabs`
(argument 7) wherever the caller's words are held. -/
def OsRoundRegD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop :=
  CompleteRelRegD fs cert k "opening_round"
    (fun rd args rets => Whir.MeaningOpeningRound rd args rets ∧ WinTabs rd (args.getD 7 0))
    (RegPtrs roundSpec)

/-- **`open_stacked`'s leaf callees, placed on their regions.** -/
structure OsCalleesRegD (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) : Prop where
  msg : ∀ p ∈ omDeployed, CompleteRelRegD fs cert k (omName p) (MeaningOpeningMessage p.1 p.2)
    (RegPtrs (msgSpec p.1 p.2))
  spf : ∀ n ∈ spfDeployed, CompleteRelRegD fs cert k (spfName n) (MeaningSqueezePointFrom n)
    (RegPtrs (spfSpec n))
  tail : CompleteRelRegD fs cert k "opening_tail_round" MeaningOpeningTailRound (RegPtrs tailSpec)
  merkleCap : ∀ p ∈ merkleCapNames, CompleteRelRegD fs cert k p.1 (MeaningVerifyMerkleCap p.2)
    (RegPtrs (merkleCapSpec p.2))
  foldFinal : ∀ p ∈ foldFinalMsgNames, CompleteRelRegD fs cert k p.1 (MeaningFoldFinalMsg p.2)
    (RegPtrs (foldFinalSpec p.2))
  grind : ∀ b ∈ grindBitsDeployed, CompleteRelRegD fs cert k (grindCheckName b) (grindPre b)
    (RegPtrs [])

/-! ### The kernel's checks -/

set_option maxRecDepth 100000 in
theorem msg_leafSpec : (omDeployed.all fun p => leafSpecB (omName p) (msgSpec p.1 p.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spf_leafSpec : (spfDeployed.all fun n => leafSpecB (spfName n) (spfSpec n)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tail_leafSpec : leafSpecB "opening_tail_round" tailSpec = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem merkleCap_leafSpec :
    (merkleCapNames.all fun p => leafSpecB p.1 (merkleCapSpec p.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem foldFinal_leafSpec :
    (foldFinalMsgNames.all fun p => leafSpecB p.1 (foldFinalSpec p.2)) = true := by
  decide +kernel

theorem leafSpecOk_allP {α : Type} {xs : List α} {name : α → String} {spec : α → List (ℕ × ℕ)}
    (h : (xs.all fun p => leafSpecB (name p) (spec p)) = true) :
    ∀ p ∈ xs, LeafSpecOk (name p) (spec p) := fun p hp =>
  leafSpecOk_of (List.all_eq_true.mp h p hp)

/-- A placed form without a region hypothesis gives one with any. -/
theorem CompleteRelD.regD {k : ℕ} {f : String} {Pre : Reader → List E → List E → Prop}
    {Reg : List E → (ℕ → Prop) → Prop} (h : CompleteRelD fs cert k f Pre) :
    CompleteRelRegD fs cert k f Pre Reg :=
  fun args rets Lin _ hp => h args rets Lin hp

/-- **`open_stacked`'s leaf callees are complete, placed on their regions**, at every frame size
and certificate, on memories defined below `2^k`, `11 ≤ k` (the grinds' range checks). -/
theorem osCalleesRegD_holds {k : ℕ} (hk : 11 ≤ k) : OsCalleesRegD fs cert k where
  msg p hp := completeRelRegD_of_iff (leafSpecOk_allP msg_leafSpec p hp)
    (opening_message_holds p hp) k
  spf n hn := completeRelRegD_of_iff (leafSpecOk_allP spf_leafSpec n hn)
    (squeeze_point_from_holds n hn) k
  tail := completeRelRegD_of_iff (leafSpecOk_of tail_leafSpec) opening_tail_round_holds k
  merkleCap p hp := completeRelRegD_of_iff (leafSpecOk_all merkleCap_leafSpec p hp)
    (verify_merkle_cap_holds p hp) k
  foldFinal p hp := completeRelRegD_of_iff (leafSpecOk_all foldFinal_leafSpec p hp)
    (fold_final_msg_holds p hp) k
  grind _ hb := (grind_check_completeD hb hk).regD

end
end LeanVM.Guest.B1
