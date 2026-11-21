module

public import NativeVm.Equiv.TablesPure

/-!
# Phase 4's model in the code's shape

`tablePhase` with its constants evaluated (`tablePhase_eq`: no grind, `ξ`'s five powers, the
constraints' two and the forms' three), a round of the table sumcheck as the code runs it
(`roundPoly_eq`: three scalars read, then the message), and the tables' data the code holds as
literals (`tableW_width`, `tableW_opcode`, `tableW_nConstraints`).
-/

@[expose] public section

namespace NativeVm.Code.P4

open NativeVm.Model LeanVM.Parameters

theorem nConstraints_two : (tablesW.map (·.nConstraints)).sum = 2 := by
  rw [nConstraints_eq]; rfl

theorem grindingBits_four : grindingBits 4 = 0 := by decide

theorem grindingBits_three : grindingBits 3 = 0 := by decide

theorem grind_zero : Model.grind 0 = pure () := rfl

/-- `ξ`'s powers: the constraints' two. -/
def cpOf (xi : EW) : Array EW := (powers xi 5).extract 0 2

/-- `ξ`'s powers: the forms' three. -/
def fpOf (xi : EW) : Array EW := (powers xi 5).extract 2 5

theorem powers_size (b : EW) (n : Nat) : (powers b n).size = n := by
  unfold powers
  suffices ∀ (l : List Nat) (acc : Array EW × EW),
      (l.foldl (fun (acc : Array EW × EW) _ ↦ (acc.1.push acc.2, acc.2 * b)) acc).1.size =
        acc.1.size + l.length by
    rw [this]; simp
  intro l
  induction l with
  | nil => intro acc; simp
  | cons x l ih => intro acc; rw [List.foldl_cons, ih]; simp; omega

theorem fpOf_size (xi : EW) : (fpOf xi).size = 3 := by
  simp [fpOf, powers_size]

theorem cpOf_size (xi : EW) : (cpOf xi).size = 2 := by
  simp [cpOf, powers_size]

/-- **Phase 4's model**, its constants evaluated. -/
theorem tablePhase_eq (layout : LayoutW) (bus : BusResultW) :
    tablePhase layout bus = (Model.sampleChallenge >>= fun xi ↦
      tableSumcheck layout.tableLogHeights bus.forms (cpOf xi) (fpOf xi) bus.point
        (dot (fpOf xi) bus.totals)) := by
  simp only [tablePhase, nConstraints_two]
  rw [show (2 + LeanVM.Protocol.Verifier.nTrees - 1) = 4 from rfl, grindingBits_four, grind_zero,
    pure_bind]
  congr 1

/-- The message of a round from its three scalars. -/
def msgOf (claim : EW) (xs : Array EW) : Array EW :=
  #[xs.getD 0 0, claim + sumE #[xs.getD 1 0, xs.getD 2 0], xs.getD 1 0, xs.getD 2 0]

theorem readScalars_three : readScalars 3 = (Model.readScalar >>= fun x0 ↦
    Model.readScalar >>= fun x1 ↦ Model.readScalar >>= fun x2 ↦ pure #[x0, x1, x2]) := by
  simp [readScalars, List.range_succ]

theorem readScalars_two : readScalars 2 = (Model.readScalar >>= fun x1 ↦
    Model.readScalar >>= fun x2 ↦ pure #[x1, x2]) := by
  simp [readScalars, List.range_succ]

/-- **A round's message** as the code reads it: three scalars, then the message. -/
theorem roundPoly_eq (claim : EW) :
    sumcheckRoundPoly 4 claim none = (readScalars 3 >>= fun xs ↦ pure (msgOf claim xs)) := by
  simp only [sumcheckRoundPoly, readScalars_three, show (4 - 2) = 2 from rfl, readScalars_two,
    bind_assoc, pure_bind, show (4 - 1) = 3 from rfl, grindingBits_three, grind_zero]
  rfl

end NativeVm.Code.P4
