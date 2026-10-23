import LeanVM.Protocol.EndToEnd.Front.WalkFaithful

/-!
# The forward walk's fidelity: tests

* **Statement locks** of `walkFaithful_blake2sFlockSpec`, of its corollary for the lincheck's
  terminal, of the position-by-position reading `walk_rows`, and of the two adder simulations.
* **Axioms**: the fidelity theorems use the standard axioms only.
* **What is load-bearing.** The simulation `Sim` pins the rows the walk writes: a walk that skips
  the row of a gate the builder records is rejected, and so is one writing it at another position
  or with another value.
* **Inhabitants**: the empty program simulates the empty program; the adders simulate theirs at
  every position.
-/

namespace LeanVMTests.Protocol.EndToEnd.Front.WalkFaithful

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.ProductCircuit
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Front.WalkSim

/-! ## Statement locks -/

example : WalkFaithful Blake2sFlock.blake2sFlockSpec := walkFaithful_blake2sFlockSpec

example (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes) :
    TerminalFaithful Blake2sFlock.blake2sFlockSpec prog s :=
  terminalFaithful_blake2sFlockSpec prog s

example (w : List E) (k : Pos Blake2sCircuit.m) :
    (Verifier.blake2sRowValues w).1.getD k 0 =
        formVal w.toArray (Blake2sCircuit.blake2sCircuit.rowOf k).a ∧
      (Verifier.blake2sRowValues w).2.getD k 0 =
        formVal w.toArray (Blake2sCircuit.blake2sCircuit.rowOf k).b :=
  walk_rows w k

example {m : ℕ} (cw : Array E) (x y : Word m) (n : ℕ) :
    Sim cw n 31 (ProductCircuit.addW x y)
      (Verifier.addW cw (wordVal cw x) (wordVal cw y) n) (fun o oa ↦ oa = wordVal cw o) :=
  sim_addW cw x y n

example {m : ℕ} (cw : Array E) (x y z : Word m) (n : ℕ) :
    Sim cw n 61 (ProductCircuit.add3W x y z)
      (Verifier.add3W cw (wordVal cw x) (wordVal cw y) (wordVal cw z) n)
      (fun o oa ↦ oa = wordVal cw o) :=
  sim_add3W cw x y z n

/-! ## Axioms -/

/--
info: 'LeanVM.Protocol.EndToEnd.Front.walkFaithful_blake2sFlockSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms walkFaithful_blake2sFlockSpec

/--
info: 'LeanVM.Protocol.EndToEnd.Front.terminalFaithful_blake2sFlockSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms terminalFaithful_blake2sFlockSpec

/-! ## What is load-bearing -/

/-- The row vectors `(#[1, 1], #[1, 1])`. -/
private def ones : Array E × Array E := (#[1, 1], #[1, 1])

/-- One gate `(0, 0)` recorded at position `0` of a block of two. -/
private def oneGate : Builder 1 (Form 1) := ProductCircuit.mul 0 0

/-- What the walk must leave when the builder records `oneGate` from position `0`. -/
private theorem sim_oneGate_forces {mw : Verifier.RowM Unit} {R : Form 1 → Unit → Prop}
    (h : Sim (#[] : Array E) 0 1 oneGate mw R) :
    (mw.run ones).2 = (#[0, 1], #[0, 1]) := by
  obtain ⟨new, h1, -, h3, -⟩ := h (by norm_num) ⟨0, #[]⟩ rfl ones
  have hg := congrArg (fun σ : BuildState 1 ↦ σ.gates.toList) h1
  simp only [oneGate, run_mul, Array.toList_push, List.nil_append, Array.toList_append] at hg
  rw [h3, ← hg]
  have h0 : formVal (m := 1) (#[] : Array E) (BitVec.ofNat 2 0) = 0 := by simp [formVal]
  simp [writeRows, writeRow, ones, pos, h0]

/-- A walk that skips the row of a recorded gate does not simulate it. -/
example : ¬ Sim (#[] : Array E) 0 1 oneGate (pure ()) (fun _ _ ↦ True) := by
  intro h
  have h' := sim_oneGate_forces h
  rw [show ((pure () : Verifier.RowM Unit).run ones).2 = (#[1, 1], #[1, 1]) from rfl] at h'
  have := congrArg (fun s : Array E × Array E ↦ s.1[0]!) h'
  simp at this

/-- A walk that writes the row at the wrong position does not simulate it. -/
example :
    ¬ Sim (#[] : Array E) 0 1 oneGate (Verifier.setRow 1 0 0) (fun _ _ ↦ True) := by
  intro h
  have h' := sim_oneGate_forces h
  rw [show ((Verifier.setRow 1 0 0 : Verifier.RowM Unit).run ones).2 = (#[1, 0], #[1, 0]) from
    rfl] at h'
  have := congrArg (fun s : Array E × Array E ↦ s.1[0]!) h'
  simp at this

/-- A walk that writes the wrong value does not simulate it. -/
example :
    ¬ Sim (#[] : Array E) 0 1 oneGate (Verifier.setRow 0 1 0) (fun _ _ ↦ True) := by
  intro h
  have h' := sim_oneGate_forces h
  rw [show ((Verifier.setRow 0 1 0 : Verifier.RowM Unit).run ones).2 = (#[1, 1], #[0, 1]) from
    rfl] at h'
  have := congrArg (fun s : Array E × Array E ↦ s.1[0]!) h'
  simp at this

/-- The honest walk does. -/
example : Sim (#[] : Array E) 0 1 oneGate (Verifier.setRow 0 0 0) (fun _ _ ↦ True) := by
  intro _ σ hσ s
  refine ⟨[(pos σ.next, ⟨0, 0⟩)], ?_, ?_, ?_, trivial⟩
  · simp [oneGate, run_mul, hσ]
  · simp [hσ, pos]
  · simp [writeRows, writeRow, Verifier.setRow, hσ, pos]
    rfl

/-! ## Inhabitants -/

example {m : ℕ} (cw : Array E) (n : ℕ) :
    Sim (m := m) cw n 0 (pure ()) (pure ()) (fun _ _ ↦ True) :=
  sim_pure trivial

end LeanVMTests.Protocol.EndToEnd.Front.WalkFaithful
