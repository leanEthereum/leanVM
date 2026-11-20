/-
  Rv64mc.Spec.Bus.TableSumcheck

  The contract of `verifier::bus::table_sumcheck(tables, table_log_heights, bus_forms, constraint_powers,
  form_powers, equality_point, target, transcript) -> Result<Vec<TableEvaluations>, VerifierError>`, as the image
  passes its fifteen words: the result's slot (`sret`) in `a0`; the slices `tables` (`a1`, `a2`),
  `table_log_heights` (`a3`, `a4`), `bus_forms` (`a5`, `a6`), `constraint_powers` (`a7`, `t3`), `form_powers`
  (`t4`, `t5`) and `equality_point`'s pointer (`t6`); on the stack at entry, `equality_point`'s length, `target`'s
  limbs and the transcript. It is the mirror's step `Model.tableSumcheckRust`: where the mirror returns the rows and
  `t'`, the slot holds `Ok(rows)` (`ResultEvaluationsAt`, its buffers allocated by the call) and the transcript is
  `t'`; where it fails, the slot holds an `Err`. It writes the slot and the transcript (`Out`).
-/

import Rv64mc.Spec.Bus.Repr
import Rv64mc.Model.Bus

namespace Rv64mc.Spec.Bus.TableSumcheck

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters LeanVM.Protocol.Verifier Rv64mc.Spec.Transcript
  Rv64mc.Spec.Layout

/-- The stack word `k` at entry: the arguments past the registers. -/
def arg (regs : Reg → Word) (m : MachineState) (k : Nat) : Word := m.getMem (regs .x2 + BitVec.ofNat 64 (8 * k))

/-- The transcript's address. -/
def transcript (regs : Reg → Word) (m : MachineState) : Word := arg regs m 3

/-- An `E` slice passed as a pointer and a length, its elements live. -/
def ESlice (env : Env) (m : MachineState) (ptr len : Word) (xs : List E) : Prop :=
  SliceArgs EListAt m ptr len (xs.map Model.limbs) ∧ env.Live m ptr (Layouts.E.byteSize * xs.length)

def Pre (env : Env) (tables : List Model.TableRust) (heights : List Nat) (forms : List (List Form))
    (cps fps eqp : List E) (target : E) (t : Model.TState) (regs : Reg → Word) (m : MachineState) : Prop :=
  SliceArgs (ArrayAt Layouts.Table.byteSize (TableAt env)) m (regs .x11) (regs .x12) tables ∧
    env.Live m (regs .x11) (Layouts.Table.byteSize * tables.length) ∧
    SliceArgs UsizesAt m (regs .x13) (regs .x14) heights ∧ env.Live m (regs .x13) (8 * heights.length) ∧
    SliceArgs (ArrayAt Layouts.Vec.byteSize (FormsAt env)) m (regs .x15) (regs .x16) forms ∧
    env.Live m (regs .x15) (Layouts.Vec.byteSize * forms.length) ∧
    ESlice env m (regs .x17) (regs .x28) cps ∧ ESlice env m (regs .x29) (regs .x30) fps ∧
    ESlice env m (regs .x31) (arg regs m 0) eqp ∧
    arg regs m 1 = (Model.limbs target).1 ∧ arg regs m 2 = (Model.limbs target).2 ∧
    TranscriptAt env m (transcript regs m) t ∧ InFrame (regs .x2) (transcript regs m) Layouts.Transcript.byteSize ∧
    InFrame (regs .x2) (regs .x10) Layouts.ResultTableEvaluations.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    Transcript.Apart (regs .x10) Layouts.ResultTableEvaluations.byteSize (transcript regs m) Layouts.Transcript.byteSize

def Post (env : Env) (tables : List Model.TableRust) (heights : List Nat) (forms : List (List Form))
    (cps fps eqp : List E) (target : E) (t : Model.TState) (regs : Reg → Word) (m : MachineState)
    (_r' : Reg → Word) (m' : MachineState) : Prop :=
  match (Model.tableSumcheckRust tables heights forms cps fps eqp target).run t with
  | some (rows, t') => ResultEvaluationsAt env m' (regs .x10) (some rows) ∧ TranscriptAt env m' (transcript regs m) t'
  | none => ResultEvaluationsAt env m' (regs .x10) none

/-- What it writes besides its stack and allocations: the result's slot and the transcript. -/
def Out (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) Layouts.ResultTableEvaluations.byteSize b ∨
    InRange (transcript regs m) Layouts.Transcript.byteSize b

/-- **The contract of `table_sumcheck`**, function `i` of `p` with `need` bytes of stack (its frame is 336 bytes),
    for every argument. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ tables heights forms cps fps eqp target t,
    Holds env p i need (Pre env tables heights forms cps fps eqp target t)
      (Post env tables heights forms cps fps eqp target t) Out

end Rv64mc.Spec.Bus.TableSumcheck
