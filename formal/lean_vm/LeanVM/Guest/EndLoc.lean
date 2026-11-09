/-
  LeanVM.Guest.EndLoc

  B2, located: a valid execution's memory holds `main`'s body at its frame, its calls located.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.JumpTable
public import LeanVM.Guest.Glob
public import LeanVM.Guest.Located.Basic

/-!
# `main` at its frame

A run of `guest` starts in `__jump_tables`, which writes the jump table into `main`'s frame and
falls through into `main` at `fp = 1` (`safe_jumpTables`). B2 (`b2_step`, `b2_mainL`, checker K's
contracts over `glob`, proved from the kernel-checked certificates) then gives `main`'s body
under the valuation of its certificate's cells at `fp = 1` (`Check.valG L 1 (certOf 1)`), each
call located at a frame the run from `(g^0, 1)` entered the callee at, its precondition holding
there and its argument and return cells holding the call's words (`Located.RLg`,
`Check.EnteredAt`; `reach_jumpTables` reaches `main`'s entry), the contracts of every function, on
that run, holding for runs of any length (`globSpec`: `funSpecReached_induction` over `b2_step`).

`B2SoundL` states B2 as `Sound.lean` proves it (`b2_step`, `b2_mainL`), so that this module and
the assembly above it do not import the certificates; `EndSound.lean` proves it, from B1's
statements about the core IR there (`VsDimsKnown`, `VsKnown`, `ExpTablesSound`, `WalkKnown`).
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash

@[expose] public section

/-- Every contract of `glob`, for runs shorter than `n`. -/
abbrev GlobLt {κ : ℕ} (L : MemoryImage κ) (n : ℕ) : Prop :=
  ∀ j, FunSpecLtReached guestProgram L n (glob.sig j).entry (Check.Pre glob L j)
    (Check.Post coreProgram glob L certByName (Check.EnteredAt glob L) j)

/-- **B2, as checker K states it** (`b2_step`, `b2_mainL` of `Sound.lean`). -/
structure B2SoundL : Prop where
  /-- Every function's contract for runs shorter than `n + 1`, given all of them for runs shorter
  than `n`. -/
  step : ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ n, GlobLt L n →
    ∀ i, FunSpecLtReached guestProgram L (n + 1) (glob.sig i).entry (Check.Pre glob L i)
      (Check.Post coreProgram glob L certByName (Check.EnteredAt glob L) i)
  /-- From `main`'s entry at `fp = 1`, the jump table written and the contracts holding for runs
  shorter than `k`, a halting run gives `main`'s body at its frame, its calls located. -/
  mainL : ∀ {κ : ℕ} (L : MemoryImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
    GlobLt L k → SafeReached guestProgram L k ⟨addressOfIndex mainEntry, 1⟩ →
      Stmt.HoldsList (RL coreProgram L certByName (Check.EnteredAt glob L)) L.read (valG L 1 (certOf 1)) (coreOf 1).body
        False (fun rs ↦ rs = [])

/-- **Every contract of `glob`**, on the run from `(g^0, 1)`, for runs of any length
(`funSpecReached_induction` over B2's step). -/
theorem globSpec (hb2 : B2SoundL) {κ : ℕ} {L : MemoryImage κ} (h16 : minLogMem ≤ κ)
    (h32 : κ ≤ maxLogMem) (j : ℕ) :
    FunSpecReached guestProgram L (glob.sig j).entry (Check.Pre glob L j)
      (Check.Post coreProgram glob L certByName (Check.EnteredAt glob L) j) :=
  funSpecReached_induction (P := fun j ↦ Check.Pre glob L j)
    (Q := fun j ↦ Check.Post coreProgram glob L certByName (Check.EnteredAt glob L) j)
    (hb2.step L h16 h32) j

/-- **B2 at `main`, located, for a halting run from `(g^0, 1)`**. -/
theorem mainBodyL_of_safe (hb2 : B2SoundL) {κ : ℕ} {L : MemoryImage κ}
    (h16 : minLogMem ≤ κ) (h32 : κ ≤ maxLogMem) {k : ℕ} (hs : Safe guestProgram L k ⟨addressOfIndex
        0, 1⟩) :
    Stmt.HoldsList (Located.RLg L) L.read (valG L 1 (certOf 1)) Data.core0.body False
      (fun rs ↦ rs = []) := by
  obtain ⟨hjt, k', hk'⟩ := safe_jumpTables hs
  exact hb2.mainL L h16 h32 hjt k' (fun j ↦ (globSpec hb2 h16 h32 j).lt k')
    ⟨hk', reach_jumpTables hjt⟩

/-- **B2 at `main`, located, for a valid execution**: `main`'s body under its frame's valuation,
its calls located, and the public input's cells at `g^0`, `g^1`. -/
theorem mainBodyL_of (hb2 : B2SoundL) {input : PublicInput}
    {t : Execution guestProgram} (hv : ValidExecution guestProgram input t) :
    Stmt.HoldsList (Located.RLg t.memory) t.memory.read (valG t.memory 1 (certOf 1)) Data.core0.body
      False (fun rs ↦ rs = []) ∧
    LoadHolds t.memory.read 1 0 (digestHalves (publicInputDigest input)).1 ∧
    LoadHolds t.memory.read 1 1 (digestHalves (publicInputDigest input)).2 :=
  ⟨mainBodyL_of_safe hb2 hv.1.1 hv.1.2.1 (safe_of_validExecution hv), pub_loads hv⟩

end
end LeanVM.Guest.End
