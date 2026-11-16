/-
  LeanVM.Guest.Located.Basic

  Frames of the memory, the first one passing a test, and witnesses read off a call's frame or a
  loop's frames.
-/

module

public import LeanVM.Guest.Backend.Guest.End
public import LeanVM.Guest.Backend.Guest.Compiled

/-!
# Frames

A located call (`RLg L`, the back end's located relation `World.C` of the guest's world
`guestW L`) runs at a frame `g^a` of the memory, `a < 2^κ` (`Backend.InMem`), entered on the run
from `(g^0, 1)`, under the valuation by the back end's places there (`valAt`, `World.vf`). A
witness is read off the first frame passing a Boolean test (`firstFrame`). The frame of a call
(`frameOf`) is the first at which the callee's code holds on the call's words (`BodyAt`), a
classical test of the guest's own semantics (the callee's core IR body under the located
relation, its in-circuit checks such as `KECCAK`'s `KeccakCellsRelation` included). The decoder
computes no hash and runs no verifier of its own.

* `RLg_eq`: the located relation is `coreProgram`'s, located by the world's valuation and entries.
* `rlg_le_rel`: the located relation lies below `coreProgram.Rel`; it unfolds along the memory's
  frame map (`Located.unfoldsV_RL`, `Located/Interface.lean`).
-/

namespace LeanVM.Guest.Located

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core
open LeanVM.Protocol.Verifier

@[expose] public section

/-- **The guest's world on the memory `L`**: the back end's compilation of the guest, its callers'
preconditions `guestU`. -/
noncomputable abbrev guestW {κ : ℕ} (L : MemoryImage κ) : Backend.World κ :=
  Backend.guestEnd Backend.guestFns Backend.guestSlots L

/-- **The guest's located call relation** on the memory `L`. -/
noncomputable abbrev RLg {κ : ℕ} (L : MemoryImage κ) : CallRel := (guestW L).C

/-- The valuation of the guest function `f` with the memory's word `a` as its frame. -/
noncomputable def valAt {κ : ℕ} (L : MemoryImage κ) (f : String) (a : ℕ) : Val :=
  (guestW L).vf f (addressOfIndex a)

/-- `main`'s valuation at its frame `fp = 1`. -/
noncomputable def mainVal {κ : ℕ} (L : MemoryImage κ) : Val := (guestW L).vf "main" 1

/-- The first frame `a < 2^κ` passing the test `t`. -/
def firstFrame (κ : ℕ) (t : ℕ → Bool) : Option ℕ := (List.range (2 ^ κ)).find? t

/-- A frame passing the test makes the scan find one. -/
theorem firstFrame_some {κ : ℕ} {t : ℕ → Bool} {a : ℕ} (ha : a < 2 ^ κ) (h : t a = true) :
    ∃ b, firstFrame κ t = some b ∧ t b = true := by
  unfold firstFrame
  rcases hf : (List.range (2 ^ κ)).find? t with _ | b
  · exact absurd h (by simpa using List.find?_eq_none.mp hf a (List.mem_range.mpr ha))
  · exact ⟨b, rfl, List.find?_some hf⟩

/-! ## The located relation -/

/-- The located relation is `coreProgram`'s, located by the guest world's valuation and entries. -/
theorem RLg_eq {κ : ℕ} (L : MemoryImage κ) :
    RLg L = coreProgram.RelL L.read (guestW L).vf (guestW L).Entered := by
  show Core.Program.RelL _ _ _ _ = _
  rw [Backend.guestWorld_core]
  rfl

/-- The located relation lies below the relation. -/
theorem rlg_le_rel {κ : ℕ} (L : MemoryImage κ) : CallRel.Le (RLg L) (coreProgram.Rel L.read) :=
  RLg_eq L ▸ relL_le_rel coreProgram

/-! ## The frame the guest's code ran at -/

/-- **The guest's code for `f` holds at the memory's frame `a`** on the argument words `args` and
the return words `rets`: its body, under the frame's valuation, its calls located. -/
def BodyAt {κ : ℕ} (L : MemoryImage κ) (f : String) (args rets : List E) (a : ℕ) : Prop :=
  ∃ fn, coreProgram.find? f = some fn ∧ fn.params.map (valAt L f a) = args ∧
    Stmt.HoldsList (RLg L) L.read (valAt L f a) fn.body False (fun rs ↦ rs = rets)

open Classical in
/-- **The frame of a call**: the first frame of the memory at which the callee's code holds on the
call's words, decided classically: the test is the guest's own semantics (the callee's core IR
body under the located relation, its in-circuit checks included); it computes no hash and runs no
verifier of its own. -/
noncomputable def frameOf {κ : ℕ} (L : MemoryImage κ) (f : String) (args rets : List E) : ℕ :=
  match firstFrame κ (fun a ↦ decide (BodyAt L f args rets a)) with
  | some a => a
  | none => 0

/-- A located call's callee holds at the call's frame. -/
theorem bodyAt_frameOf {κ : ℕ} {L : MemoryImage κ} {f : String} {args rets : List E}
    (h : RLg L f args rets) : BodyAt L f args rets (frameOf L f args rets) := by
  classical
  rw [RLg_eq] at h
  obtain ⟨fn, fp, hf, ⟨⟨a, ha, rfl⟩, -⟩, hp, hb⟩ := (relL_iff coreProgram f args rets).mp h
  rw [← RLg_eq] at hb
  obtain ⟨b, hb', ht⟩ := firstFrame_some (t := fun a ↦ decide (BodyAt L f args rets a)) ha
    (decide_eq_true ⟨fn, hf, hp, hb⟩)
  unfold frameOf
  rw [hb']
  exact of_decide_eq_true ht

end
end LeanVM.Guest.Located
