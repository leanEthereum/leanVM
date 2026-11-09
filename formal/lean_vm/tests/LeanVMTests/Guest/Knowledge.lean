import LeanVM.Guest.EndRpm

/-!
# Tests: the guest's soundness, its witness named

* The end theorems from their hypotheses rest on Lean's three standard axioms only.
* The decoder reads the seed and the statement off `main`'s frame, by definition, and the witness
  off `main`'s valuation, the memory and the memory's frame map.
* The named form implies the existential one (`∃ w, NodeRelation …` at the input's digest).
* Why the existential one says little: the empty statement holds under any seed and any deferred
  value (`∃ w, NodeRelation …` of a statement with no claims, no children and the point at zero), so a digest
  of it exists for almost every public input.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Check
open LeanVM.Guest.End LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.B1

/-- info: 'LeanVM.Guest.End.guest_knowledge_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge_of

/-- info: 'LeanVM.Guest.End.aggregate_knowledge_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge_of

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer_of

/-- info: 'LeanVM.Guest.End.decode_binds_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds_of

/-- info: 'LeanVM.Guest.End.guest_knowledge_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge_V

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer_V

/-- info: 'LeanVM.Guest.End.decode_binds_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds_V

/-- info: 'LeanVM.Guest.Binding.statementDigest_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Binding.statementDigest_binds

/-- info: 'LeanVM.Guest.Located.unfoldsV_RL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Located.unfoldsV_RL

/-! ## The decoder reads `main`'s frame -/

example (W : Val → Reader → FrameMap → NodeWitness) {κ : ℕ} (L : MemoryImage κ) :
    (decodeWith W L).seed = B1.Main.decSeed (valG L 1 (certOf 1)) := rfl

example (W : Val → Reader → FrameMap → NodeWitness) {κ : ℕ} (L : MemoryImage κ) :
    (decodeWith W L).statement = B1.Main.decStmt (valG L 1 (certOf 1)) L.read := rfl

example (W : Val → Reader → FrameMap → NodeWitness) {κ : ℕ} (L : MemoryImage κ) :
    (decodeWith W L).witness = W (valG L 1 (certOf 1)) L.read (Located.frameV L) := rfl

/-- A call's valuation in the frame map is the valuation of the call's frame. -/
example {κ : ℕ} (L : MemoryImage κ) (f : String) (args rets : List E) :
    Located.frameV L f args rets = frameVal L certByName f (addressOfIndex (Located.frameOf L f args
        rets)) :=
  rfl

/-! ## The named form implies the existential one -/

example (W : Val → Reader → FrameMap → NodeWitness) (h : SoundHyps W) (input : PublicInput)
    (t : Execution guestProgram) (hv : ValidExecution guestProgram input t) :
    ∃ seed s, statementDigest seed s = publicInputDigest input ∧ s.deferredClaim.HasBytecodeShape bytecode ∧
      ∃ w, NodeRelation bytecode seed s w := by
  obtain ⟨hd, hrel⟩ := guest_knowledge_of h input t hv
  exact ⟨_, _, hd, hrel.hasBytecodeShape, _, hrel⟩

/-! ## The existential one is nearly vacuous -/

/-- The statement with no claims and its deferred claim at the zero point, value `v`. -/
def emptyStatement (v : E) : NodeStatement :=
  ⟨⟨[], [], zeroDigest⟩, ⟨List.replicate 23 0, v⟩⟩

/-- A witness holds the empty statement, whatever the seed and the deferred value: its digest
ranges over a seed and a field element, so almost every public input is one's. -/
example (seed : Digest) (v : E) (hints : BatchingHints) :
    ∃ w, NodeRelation bytecode seed (emptyStatement v) w := by
  have hlog : Nat.log2 bytecode.length = 23 := by rw [bytecode_length, Nat.log2_two_pow]
  refine ⟨⟨[], [], [], none, hints⟩, ?_⟩
  unfold NodeRelation SignatureClaimsHeld DaDigestHeld ChildrenProven DeferredClaimBatched
  refine ⟨⟨by simp, by simp, by simp [emptyStatement], by simp [emptyStatement]⟩,
    by simp [emptyStatement], by simp, ?_⟩
  simp [emptyStatement, DeferredClaim.HasZeroPoint, hlog]
