import LeanVM.Guest.EndRpm

/-!
# Tests: the end theorems' axioms

The guest's soundness theorems for the deployed bytecode (`LeanVM.Guest.EndFinal`, and in the
random-permutation model `LeanVM.Guest.EndRpm`) and the pieces
they rest on, B2 from the kernel-checked certificates (`LeanVM.Guest.EndSound`) and B1's
statements, rest on Lean's three standard axioms only.
-/

open LeanVM LeanVM.Guest LeanVM.Guest.End LeanVM.Node LeanVM.Semantics

/-- info: 'LeanVM.Guest.End.expTablesSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.expTablesSound

/-- info: 'LeanVM.Guest.End.vsKnown_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.vsKnown_proved

/-- info: 'LeanVM.Guest.End.b2SoundL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.b2SoundL

/-- info: 'LeanVM.Guest.End.subSoundW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.subSoundW

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.guest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound

/-! ## The statements, as the specification states them -/

example : MemoryGuestKnowledge guestProgram decode := guest_knowledge

example : MemoryAggregateSound guestProgram decode transcriptExtractor := aggregate_sound_outer

/-- The decoder reads the seed and the statement off `main`'s frame, through the index of the
memory's addresses (on fewer than `2^64` words, the memory's own reads). -/
example {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    (decode L).seed = B1.Main.decSeed (Check.valG L 1 (certOf 1)) := by rw [decode_eq hκ]

example {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    (decode L).statement = B1.Main.decStmt (Check.valG L 1 (certOf 1)) L.read := by
  rw [decode_eq hκ]

/-- The decoder's witness: `main`'s, each callee's read off the frame the replayed run entered it
at, each child's proof by `VerifySub.vsPiOf`. -/
example {κ : ℕ} (hκ : κ < 64) (L : MemoryImage κ) :
    (decode L).witness = B1.Main.decWitV (Check.valG L 1 (certOf 1)) L.read (Located.replayFrameV L)
      B1.VerifySub.vsPiOf := by
  rw [decode_eq hκ]
