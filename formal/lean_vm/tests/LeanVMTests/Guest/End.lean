import LeanVM.Guest.EndRpm

/-!
# Tests: the end theorems' axioms

The guest's soundness theorems for the deployed bytecode (`LeanVM.Guest.EndFinal`, and in the
random-permutation model `LeanVM.Guest.EndRpm`) and the pieces
they rest on, B2 from the back end's compilation of the guest (`LeanVM.Guest.EndLoc`), the replay
(`LeanVM.Guest.Located.Replay`) and B1's statements, rest on Lean's three standard axioms only.
-/

open LeanVM LeanVM.Guest LeanVM.Guest.End LeanVM.Node LeanVM.Semantics

/-- info: 'LeanVM.Guest.End.globSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.globSpec

/-- info: 'LeanVM.Guest.End.mainBodyL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.mainBodyL_of

/-- info: 'LeanVM.Guest.Located.unfoldsV_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Located.unfoldsV_replay

/-- info: 'LeanVM.Guest.Located.placesAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Located.placesAgree

/-- info: 'LeanVM.Guest.B1.VerifySub.verify_sub_sound_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VerifySub.verify_sub_sound_w

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.guest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound

/-! ## The statements, as the specification states them -/

example : MemoryGuestKnowledge guestProgram decode := guest_knowledge

example : MemoryAggregateSound guestProgram decode transcriptExtractor := aggregate_sound_outer

/-- The decoder reads the seed and the statement off `main`'s frame, by `main`'s row of the back
end's table of places, through the index of the memory's addresses (on fewer than `2^64` words,
the memory's own reads). -/
example {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    (decode L).seed = B1.Main.decSeed (mainValWith L.read) := by rw [decode_eq hκ]

example {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    (decode L).statement = B1.Main.decStmt (mainValWith L.read) L.read := by
  rw [decode_eq hκ]

/-- The decoder's witness: `main`'s, each callee's read off the frame the replayed run entered it
at, each child's proof by `VerifySub.vsPiOf`. -/
example {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    (decode L).witness = B1.Main.decWitV (mainValWith L.read) L.read (Located.replayFrameV L)
      B1.VerifySub.vsPiOf := by
  rw [decode_eq hκ]

/-- `main`'s row of the table is, on `main`'s values, the back end's valuation by places at its
frame. -/
example {κ : ℕ} (L : MemoryImage κ) (v : Core.V)
    (hv : v ∈ Data.core0.params ++ Core.Stmt.valsList Data.core0.body) :
    mainValWith L.read v = Located.mainVal L v := by
  have h := Located.placesAgree 1 le_rfl (by decide) L 1 v hv
  rw [coreOf_one, core0_main.1] at h
  exact h
