module

public import NativeRustcVm.Top.Phases

/-!
# `verifyExecution` from each call of `verify_execution` on

The walk's rest after each phase (`walkCommit`, …, `walkRing`), each the phase's step bound to the
next rest, so that `verifyExecution` is phase 1 bound to `walkCommit` (`verifyExecution_eq`) and a
run of a bind is the step's run then the rest's (`run_bind_eq`). Ring switching returns the point
it is given (`ringSwitch_point`).
-/

namespace NativeRustcVm.Top

open NativeVm.Model

public section

/-- Phase 7: ring switching, then the stacked opening. -/
@[expose] def walkRing (L : LayoutW) (rate : Nat) (ood : StackClaimW) (cs : Array ColumnClaimW)
    (kp ks : Array EW) : VM Unit := do
  let (target, ringPoint, coefficients) ← ringSwitch kp ks
  verifyStackedOpening L.stackLog rate
    (#[ringSwitchClaim L target ringPoint coefficients] ++ cs.filterMap (·.onStack L) ++ #[ood])

/-- From phase 6 on. -/
@[expose] def walkKeccak (L : LayoutW) (rate : Nat) (ood : StackClaimW) (cs : Array ColumnClaimW)
    (ev : Array (Array EW × Array EW)) : VM Unit := do
  let (outputs, kp, ks) ← keccakPhase L ev
  walkRing L rate ood (cs ++ outputs) kp ks

/-- From phase 5 on. -/
@[expose] def walkPublic (P : Vector UInt64 4) (L : LayoutW) (rate : Nat) (ood : StackClaimW)
    (cs : Array ColumnClaimW) (ev : Array (Array EW × Array EW)) : VM Unit := do
  let pc ← publicInputPhase L P
  walkKeccak L rate ood (cs ++ pc) ev

/-- From phase 4 on. -/
@[expose] def walkTables (P : Vector UInt64 4) (L : LayoutW) (rate : Nat) (ood : StackClaimW)
    (bus : BusResultW) : VM Unit := do
  let ev ← tablePhase L bus
  walkPublic P L rate ood (bus.claims ++ tableColumnClaims ev) ev

/-- From phase 3 on. -/
@[expose] def walkBus (P : Vector UInt64 4) (L : LayoutW) (rate : Nat) (ood : StackClaimW) :
    VM Unit := do
  let bus ← verifyBusBalance L
  walkTables P L rate ood bus

/-- From the out-of-domain sample on. -/
@[expose] def walkOod (P : Vector UInt64 4) (L : LayoutW) (rate : Nat) : VM Unit := do
  let ood ← readOod L.stackLog
  walkBus P L rate ood

/-- From phase 2 on. -/
@[expose] def walkCommit (P : Vector UInt64 4) (L : LayoutW) (rate : Nat) : VM Unit := do
  commitStack L.stackLog rate
  walkOod P L rate

theorem verifyExecution_eq (B : Array UInt64) (P : Vector UInt64 4) :
    verifyExecution B P = (readAnnouncedSizes B >>= fun p ↦ walkCommit P p.1 p.2) := rfl

theorem run_bind_eq {α β : Type} (m : VM α) (f : α → VM β) (s : TState) :
    (m >>= f).run s = (m.run s).bind fun p ↦ (f p.1).run p.2 := by
  simp only [StateT.run_bind, Option.bind_eq_bind]

/-- **Ring switching** returns the point it is given. -/
theorem ringSwitch_point (p sl : Array EW) : Gives (ringSwitch p sl) (·.2.1 = p) := by
  unfold ringSwitch; gives

end

end NativeRustcVm.Top
