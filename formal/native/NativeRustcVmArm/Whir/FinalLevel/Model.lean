module

public import NativeRustcVm.Whir.Model

/-!
# `finalLevelM` step by step

`finalLevelM` as `final_level` runs it: the folded lane read, then the continuations `C1` (the
grind) to `C6` (the end check), each step's run from the state it leaves (`run_bind_some`,
`run_bind_none`). `finalWeight` as the code accumulates it over the glued claims
(`finalWeight_take`).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeVm.Model NativeRustcVm.Whir LeanVM.Parameters

@[expose] public section

section
variable (index : Nat) (level : Whir.Level) (mu lf : Nat) (b : BasisW) (w : WhirStateW)
  (rounds : Array FoldRoundW)

/-- The end check. -/
def C6 (folded : Array EW) (tc : Array EW × EW) : VM Unit :=
  require (finalWeight lf b w tc.1 * multilinearEval (folded.extract 0 (2 ^ mu)) tc.1 == tc.2)

/-- The last sumcheck. -/
def C5 (folded : Array EW) : VM Unit :=
  sumcheckPlain w.claim 3 mu >>= C6 mu lf b w folded

/-- The rows checked. -/
def C4 (folded : Array EW) (queries : Array UInt64) (words : Array (Array UInt64)) : VM Unit :=
  require (finalOk index mu rounds folded queries words) >>= fun _ ↦ C5 mu lf b w folded

/-- The openings. -/
def C3 (folded : Array EW) (queries : Array UInt64) : VM Unit :=
  queryOpenings index queries >>= C4 index mu lf b w rounds folded queries

/-- The queries. -/
def C2 (folded : Array EW) : VM Unit :=
  sampleQueries (mu + level.logInvRate) level.queries >>= C3 index mu lf b w rounds folded

/-- The grind. -/
def C1 (folded : Array EW) : VM Unit :=
  grind Whir.queryGrindingBits >>= fun _ ↦ C2 index level mu lf b w rounds folded

theorem finalLevelM_eq :
    finalLevelM index level mu lf b w rounds =
      (readScalars (2 ^ mu + level.fold) >>= C1 index level mu lf b w rounds) := rfl

end

theorem run_bind_some {α β : Type} {m : VM α} {f : α → VM β} {s s' : TState} {x : α}
    (h : m.run s = some (x, s')) : (m >>= f).run s = (f x).run s' := by
  show (m s).bind (fun p ↦ f p.1 p.2) = f x s'
  rw [show m s = some (x, s') from h]
  rfl

theorem run_bind_none {α β : Type} {m : VM α} {f : α → VM β} {s : TState}
    (h : m.run s = none) : (m >>= f).run s = none := by
  show (m s).bind (fun p ↦ f p.1 p.2) = none
  rw [show m s = none from h]
  rfl

theorem run_require (c : Bool) (s : TState) :
    (require c).run s = if c then some ((), s) else none := by
  cases c <;> rfl

theorem run_require_bind {β : Type} (c : Bool) (f : Unit → VM β) (s : TState) :
    (require c >>= f).run s = if c then (f ()).run s else none := by
  cases c <;> rfl

theorem ew_beq (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  cases x; cases y; rfl

/-- One glued claim's term. -/
def gStep (point : Array EW) (weight : EW) (g : GluedClaimW) : EW :=
  weight + g.scalar * g.weight.eval (point.extract g.foldStart point.size)

/-- The weight after the first `i` glued claims. -/
def weightAt (lf : Nat) (b : BasisW) (w : WhirStateW) (tail : Array EW) (i : Nat) : EW :=
  (w.glued.toList.take i).foldl (gStep (w.alphas ++ tail))
    (b.eval ((w.alphas ++ tail).extract lf (w.alphas ++ tail).size ++
      (w.alphas ++ tail).extract 0 lf))

theorem weightAt_zero (lf : Nat) (b : BasisW) (w : WhirStateW) (tail : Array EW) :
    weightAt lf b w tail 0 =
      b.eval ((w.alphas ++ tail).extract lf (w.alphas ++ tail).size ++
        (w.alphas ++ tail).extract 0 lf) := rfl

theorem weightAt_succ (lf : Nat) (b : BasisW) (w : WhirStateW) (tail : Array EW) {i : Nat}
    (hi : i < w.glued.size) :
    weightAt lf b w tail (i + 1) =
      gStep (w.alphas ++ tail) (weightAt lf b w tail i) w.glued[i] := by
  unfold weightAt
  rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Array.getElem_toList, Option.toList_some, List.foldl_cons, List.foldl_nil]

theorem weightAt_size (lf : Nat) (b : BasisW) (w : WhirStateW) (tail : Array EW) :
    weightAt lf b w tail w.glued.size = finalWeight lf b w tail := by
  unfold weightAt finalWeight
  rw [List.take_of_length_le (by simp), Array.foldl_toList]
  rfl

end

end NativeRustcVmArm.Whir.FinalLevel
