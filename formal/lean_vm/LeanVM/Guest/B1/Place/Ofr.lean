/-
  LeanVM.Guest.B1.Place.Ofr

  `opening_fold_round` complete placed, at both its specializations: the statement.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Whir.Folds
public import LeanVM.Guest.Lift.OsCallees

/-!
# `opening_fold_round`, placed

`opening_fold_round__L{b}(fs0 .. fs4, w0, w1, cursor, c0, c1, c2)` is a fold round at `b` bits of
proof of work: at `b = 0` a call of `opening_fold` (`ofrZeroBody`), at `b > 0` inline, the nonce at
the cursor absorbed, the permutation's first cell ground to `b` bits by `grind_check__L{b}`
(`ofrBody b`). Its specializations are `ofrTable`: `__L0` and `__L3`.

**The statement** (`OfrAtO`): on canonical capacity cells, its loads (the round's `roundLen b`
words at the cursor) among the caller's words `Lin`, on every memory holding them where the
round's meaning holds (`MeaningFoldRound b`: the words, the proof of work, the returns), the
helper relates the arguments to the returns, by a tree within `Bd` when given.
`opening_fold_round_completeAt_Spec`: both entries.

**Design note for the proof.** Build on:
* `ofr0_rel`, `ofr_rel` (`Whir/CFoldCall.lean`, from `ofrZero_complete`, `ofr_complete` in
  `Whir/COfr.lean`): the unplaced relations from the meaning; `ofr0_fn`, `ofr3_fn`
  (`Whir/HelperData17.lean`) for the bodies.
* `opening_fold` and `grind_check__L3` are leaves: `completeRelRegDB_of_iff` with `fold_leafSpec`,
  `opening_fold_holds` and `grind_leafSpec` and the grinding check's `holds` at `3` bits
  (`Bits/Grind3`); `grind_meaning` gives the check's meaning from `PowOk`.
* a straight-line body with one call, no buffer; the bound by `TotalLe` at `Bd = some B`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (MeaningFoldRound roundLen)

@[expose] public section

/-- `opening_fold_round`'s specializations: name, bits of proof of work. -/
def ofrTable : List (String × ℕ) := [("opening_fold_round__L0", 0), ("opening_fold_round__L3", 3)]

/-- **`opening_fold_round` at `(name, b)`, placed**: on canonical capacity cells, its round's
words among the caller's, on every memory holding them where the round's meaning holds, complete
by a tree within `Bd` when given. -/
def OfrAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String) (b : ℕ)
    (Bd : Option ℕ) : Prop :=
  ∀ (Lin : Layout) (args rets : List E), args.length = 11 → AllCanonical (args.take 5) →
    RegPtrs [(7, roundLen b)] args (RegionL Lin) →
    (∀ rd, LowDef κ rd → MemL rd Lin → MeaningFoldRound b rd args rets) →
    BoundsAt fs name Bd →
    CompleteAtO fs cert κ name Lin args (Returns rets) Bd

/-- **`opening_fold_round` is complete placed at both specializations**: for frame runs fitting
their frames, their cells consecutive, on memories defined below `2^κ`, `7 ≤ κ`, each entry of
`ofrTable` is `OfrAtO` at every bound. -/
def opening_fold_round_completeAt_Spec : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert → RunsConsec cert →
    7 ≤ κ → ∀ e ∈ ofrTable, ∀ Bd : Option ℕ, OfrAtO fs cert κ e.1 e.2 Bd

end
end LeanVM.Guest.B1
