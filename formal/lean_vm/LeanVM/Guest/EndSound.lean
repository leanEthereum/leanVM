/-
  LeanVM.Guest.EndSound

  The soundness end theorem from its pieces as their owners state them: checker K's contracts over
  the program context `glob`, and group 7's `main_sound` with its callees' and `aggregate_claims`'
  soundness on every valid execution's memory.
-/

module

public import LeanVM.Guest.End
public import LeanVM.Guest.Glob
public import LeanVM.Guest.CheckSound
public import LeanVM.Guest.B1.Main.Sound

/-!
# Soundness, the pieces' own forms

`contracts` is checker K's family: function `j` of `glob`, entered at its compiled entry, under
`Check.Pre glob` and `Check.Post coreProgram glob`. `B2Sound` is B2 stated over it, unfolded (the
hypothesis `checkFn_run` takes), and `B1Sound` is what `main_sound` (group 7) takes beyond the
memory and the public input: its callees' soundness (`Callees`) and `aggregate_claims`', on every
memory of `2^κ` words, `16 ≤ κ ≤ 32` (`MemOk`). `guest_sound_of_parts`: the two give
`GuestSound`, so the final theorem only plugs in the owners' lemmas.
-/

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.EndToEnd
open scoped ENNReal

@[expose] public section

/-- **Checker K's contracts**: function `j` of `glob`, from its entry, under `Check.Pre` and
`Check.Post`. -/
noncomputable def contracts : Contracts where
  ι := ℕ
  entry j := (glob.sig j).entry
  pre j _ L := Check.Pre glob L j
  post j _ L := Check.Post coreProgram glob L j

/-- Every contract of `glob`, for runs shorter than `n` (`contracts.Lt`, unfolded). -/
abbrev GlobLt {κ : ℕ} (L : MemImage κ) (n : ℕ) : Prop :=
  ∀ j, FunSpecLt guest L n (glob.sig j).entry (Check.Pre glob L j) (Check.Post coreProgram glob L j)

/-- **B2, as checker K states it** (`SoundPieces.step` and `.main` over `contracts`). -/
structure B2Sound : Prop where
  /-- Every function's contract for runs shorter than `n + 1`, given all of them for runs shorter
  than `n` (`checkFn_run` at `main = false`, for each checked function). -/
  step : ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → ∀ n, GlobLt L n →
    ∀ i, FunSpecLt guest L (n + 1) (glob.sig i).entry (Check.Pre glob L i)
      (Check.Post coreProgram glob L i)
  /-- From `main`'s entry at `fp = 1`, the jump table written and the contracts holding for runs
  shorter than `k`, a halting run gives `main`'s relation (`checkFn_run` at `main = true`, the
  jump table's adapter `JumpTables L → JTHolds glob L`, and `main`'s `nret = 0`). -/
  main : ∀ {κ : ℕ} (L : MemImage κ), minLogMem ≤ κ → κ ≤ maxLogMem → JumpTables L → ∀ k,
    GlobLt L k → Safe guest L k ⟨gpow mainEntry, 1⟩ → coreProgram.Rel L.read "main" [] []

/-- **B1 of `main`, what group 7's `main_sound` takes**: on every memory of a valid execution,
the callees' soundness and `aggregate_claims`'. -/
structure B1Sound : Prop where
  /-- The callees (groups 2, 3, 6), soundly. -/
  callees : ∀ rd, B1.Main.MemOk rd → B1.Main.Callees bytecode rd
  /-- `aggregate_claims` (group 7), soundly. -/
  aggregate_claims : ∀ rd, B1.Main.MemOk rd → ∀ args rets,
    coreProgram.Rel rd "aggregate_claims" args rets → B1.Main.Meaning_aggregate_claims rd args rets

/-- The pieces of `SoundPieces contracts`, from their owners' forms. -/
theorem soundPieces_of (hb2 : B2Sound) (hb1 : B1Sound) : SoundPieces contracts where
  step := hb2.step
  main := hb2.main
  mainB1 L h16 h32 _ h0 h1 h :=
    have hm : B1.Main.MemOk L.read := ⟨_, h16, h32, L, rfl⟩
    B1.Main.main_sound bytecode_length hm (hb1.callees _ hm) (hb1.aggregate_claims _ hm) h0 h1 h

/-- **Soundness, from its pieces' own forms.** -/
theorem guest_sound_of_parts (hb2 : B2Sound) (hb1 : B1Sound) : GuestSound :=
  guest_sound_of (soundPieces_of hb2 hb1)

/-- **The guest's soundness in the random-oracle experiment, from its pieces' own forms**
(`aggregate_sound_of`). -/
theorem aggregate_sound_of_parts (hb2 : B2Sound) (hb1 : B1Sound) {A : Adversary} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment A}[z.1.2 = true ∧ z.1.1.1.1 = guest ∧
      ¬ ∃ seed s, statementDigest seed s = publicDigest z.1.1.1.2 ∧ s.defer.Shaped bytecode ∧
        NodeSpec bytecode seed s] ≤ soundnessError Q :=
  aggregate_sound_of (soundPieces_of hb2 hb1) hA

end
end LeanVM.Guest.End
