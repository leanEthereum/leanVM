/-
  Rv64mc.Spec.Whir.GluedWeightEvaluate

  The contract of `GluedWeight::evaluate(&self, x: &[E]) -> Result<E, VerifierError>`, which the compiled code calls
  with the result's slot (`sret`) in `a0`, `self` in `a1` and `x` as a pointer and a length in `a2`, `a3`: it writes
  `Model.GluedWeightRust.evaluate`'s answer at `sret`. The weight sits at `self` as `GluedWeightAt` says: `Ood` by
  its niche tag and its point's `Vec`, `Queries` by its two `Vec`s and `message_log`. An `Ood` point has `x`'s
  length (`verify_whir` evaluates it on the level's `mu` coordinates; `eq_eval` would panic otherwise), and a
  `Queries` weight has fewer than `64` variables (`InducedWeight`).
-/

import Rv64mc.Spec.Whir.InducedWeight

namespace Rv64mc.Spec.Whir.GluedWeightEvaluate

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters

/-- **The `GluedWeight` `g` at `a`**, its buffers live. -/
def GluedWeightAt (env : Env) (m : MachineState) (a : Word) : Model.GluedWeightRust → Prop
  | .ood point => m.getMem (a + BitVec.ofNat 64 Layouts.GluedWeight.tagOffset) =
        BitVec.ofNat 64 Layouts.GluedWeight.Ood.tag ∧
      ∃ ptr cap, VecAt EListAt m (a + BitVec.ofNat 64 Layouts.GluedWeight.Ood.f0) ptr cap (point.map Model.limbs) ∧
        env.Live m ptr (Layouts.E.byteSize * point.length)
  | .queries ml qs qw => m.getMem (a + BitVec.ofNat 64 Layouts.GluedWeight.Queries.message_log) =
        BitVec.ofNat 64 ml ∧
      (∃ ptr cap, VecAt WordsAt m (a + BitVec.ofNat 64 Layouts.GluedWeight.Queries.queries) ptr cap qs ∧
        env.Live m ptr (8 * qs.length)) ∧
      ∃ ptr cap, VecAt EListAt m (a + BitVec.ofNat 64 Layouts.GluedWeight.Queries.query_weights) ptr cap
          (qw.map Model.limbs) ∧ env.Live m ptr (Layouts.E.byteSize * qw.length)

/-- What `verify_whir` gives of a weight it evaluates at `x`. -/
def Shape (x : List E) : Model.GluedWeightRust → Prop
  | .ood point => point.length = x.length
  | .queries ml _ _ => ml < 64

def Pre (env : Env) (g : Model.GluedWeightRust) (x : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.ResultE.byteSize ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.GluedWeight.byteSize ∧ GluedWeightAt env m (regs .x11) g ∧
    SliceArgs EListAt m (regs .x12) (regs .x13) (x.map Model.limbs) ∧
    env.Live m (regs .x12) (Layouts.E.byteSize * x.length) ∧ Shape x g

def Post (g : Model.GluedWeightRust) (x : List E) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ResultEAt m' (regs .x10) (g.evaluate x)

/-- **The contract of `GluedWeight::evaluate`**, function `i` of `p` with `need` bytes of stack (its frame is 16
    bytes; it calls `eq_eval` and tail-calls `induced_weight`), for every weight and point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ g x, Holds env p i need (Pre env g x) (Post g x) (SretOut Layouts.ResultE.byteSize)

end Rv64mc.Spec.Whir.GluedWeightEvaluate
