/-
  Rv64mc.Spec.Bus.Repr

  How `bus.rs`'s values sit in memory, at the offsets of `Gen/Layouts.lean`:

  * `ColumnClaimAt`: a `ColumnClaim` (its column, its point's `Vec<E>` with the elements live, its value);
  * `OptStackClaimAt`: the `Option<(StackWeight, E)>` `ColumnClaim::on_stack` returns through `sret`: `None` as
    the niche tag, `Some((Eq(point), value))` as `Eq`'s tag, the point's fresh `Vec<E>` and the value;
  * `LayoutAt`: the `Layout` fields the bus reads (`BlocksAt`, `TableAt`, the borrowed `Walk.BytecodeAt`);
  * `ResultBusResultAt`, `ResultEvaluationsAt`: what `verify_bus_balance` and `table_sumcheck` return through `sret`,
    every buffer live (`LiveVecAt`, `LiveFormAt`).
-/

import Rv64mc.Spec.Multilinear.Basic
import Rv64mc.Spec.Layout.Repr
import Rv64mc.Spec.Walk.Repr
import Rv64mc.Model.Walk

namespace Rv64mc.Spec.Bus

open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier

/-- **The column claim `c` at `a`**: its column (a `usize`), its point's `Vec<E>`, elements live, and its value. -/
def ColumnClaimAt (env : Env) (m : MachineState) (a : Word) (c : ColumnClaim) : Prop :=
  m.getMem (a + BitVec.ofNat 64 Layouts.ColumnClaim.column) = BitVec.ofNat 64 c.column ∧ c.column < 2 ^ 64 ∧
    (∃ cap, VecAt EListAt m (a + BitVec.ofNat 64 Layouts.ColumnClaim.point)
      (vecPtr m (a + BitVec.ofNat 64 Layouts.ColumnClaim.point)) cap (c.point.map Model.limbs)) ∧
    env.Live m (vecPtr m (a + BitVec.ofNat 64 Layouts.ColumnClaim.point)) (Layouts.E.byteSize * c.point.length) ∧
    EAt m (a + BitVec.ofNat 64 Layouts.ColumnClaim.value) (Model.limbs c.value)

/-- **The `Option<(StackWeight, E)>` `o` at `a`**, its point's `Vec` allocated between `m` and `m'`; only `Eq`
    weights are ever returned. -/
def OptStackClaimAt (env : Env) (m m' : MachineState) (a : Word) : Option (Model.StackWeightRust × E) → Prop
  | none => m'.getMem (a + BitVec.ofNat 64 Layouts.OptionStackClaim.tagOffset) =
      BitVec.ofNat 64 Layouts.OptionStackClaim.None.tag
  | some (.eq pt, v) =>
      m'.getMem (a + BitVec.ofNat 64 (Layouts.StackClaim.f0 + Layouts.StackWeight.tagOffset)) =
        BitVec.ofNat 64 Layouts.StackWeight.Eq.tag ∧
      Multilinear.FreshVecE env m m' (a + BitVec.ofNat 64 (Layouts.StackClaim.f0 + Layouts.StackWeight.Eq.f0)) pt ∧
      EAt m' (a + BitVec.ofNat 64 Layouts.StackClaim.f1) (Model.limbs v)
  | some _ => False

/-! ## The layout `verify_bus_balance` and `table_sumcheck` read, and their results -/

open Rv64mc.Spec.Transcript (LiveVecAt ArrayAt)

/-- **A live `Form` at `a`**: its terms, every buffer allocated before (`FormIn` over `[0, NEXT)`). -/
def LiveFormAt (env : Env) (m : MachineState) (a : Word) (f : Form) : Prop := Layout.FormIn 0#64 (env.next m) m a f

/-- A `Vec<Form>` of live forms at `a`. -/
def FormsAt (env : Env) (m : MachineState) (a : Word) (fs : List Form) : Prop :=
  LiveVecAt env Layouts.Form.byteSize (ArrayAt Layouts.Form.byteSize (LiveFormAt env)) m a fs

/-- **The `BusBlock` at `a`**: its coordinates, log-rows, rows and owner, each `usize` below `2^64`. -/
def BusBlockAt (env : Env) (m : MachineState) (a : Word) (b : BusBlock) : Prop :=
  FormsAt env m (a + BitVec.ofNat 64 Layouts.BusBlock.coordinates) b.coordinates ∧
    m.getMem (a + BitVec.ofNat 64 Layouts.BusBlock.log_rows) = BitVec.ofNat 64 b.logRows ∧ b.logRows < 2 ^ 64 ∧
    m.getMem (a + BitVec.ofNat 64 Layouts.BusBlock.rows) = BitVec.ofNat 64 b.rows ∧ b.rows < 2 ^ 64 ∧
    m.getMem (a + BitVec.ofNat 64 Layouts.BusBlock.owner) = BitVec.ofNat 64 b.owner ∧ b.owner < 2 ^ 64

/-- A side's `Vec<BusBlock>` at `a`. -/
def BlocksAt (env : Env) (m : MachineState) (a : Word) (bs : List BusBlock) : Prop :=
  LiveVecAt env Layouts.BusBlock.byteSize (ArrayAt Layouts.BusBlock.byteSize (BusBlockAt env)) m a bs

/-- **The `Table` at `a`** as the bus and the table sumcheck read it: its opcode and its padding row. -/
def TableAt (env : Env) (m : MachineState) (a : Word) (t : Model.TableRust) : Prop :=
  m.getMem (a + BitVec.ofNat 64 Layouts.Table.opcode) = BitVec.ofNat 64 t.opcode ∧ t.opcode < 2 ^ 64 ∧
    LiveVecAt env Layouts.E.byteSize EListAt m (a + BitVec.ofNat 64 Layouts.Table.padding) (t.padding.map Model.limbs)

/-- **The `Layout` at `a` is `l`, borrowing the bytecode `bc`**: the fields the bus reads (its framework sizes, its
    tables, its three sides' blocks, and the bytecode it evaluates), each `usize` below `2^64`. -/
structure LayoutAt (env : Env) (m : MachineState) (a : Word) (l : Model.LayoutRust) (bc : Model.BytecodeRust) :
    Prop where
  logMemory : m.getMem (a + BitVec.ofNat 64 Layouts.Layout.log_memory) = BitVec.ofNat 64 l.logMemory
  logMemory_lt : l.logMemory < 2 ^ 64
  logBytecode : m.getMem (a + BitVec.ofNat 64 Layouts.Layout.log_bytecode) = BitVec.ofNat 64 l.logBytecode
  logBytecode_lt : l.logBytecode < 2 ^ 64
  tables : LiveVecAt env Layouts.Table.byteSize (ArrayAt Layouts.Table.byteSize (TableAt env)) m
    (a + BitVec.ofNat 64 Layouts.Layout.tables) l.tables
  push : BlocksAt env m (a + BitVec.ofNat 64 Layouts.Layout.push) l.push
  pull : BlocksAt env m (a + BitVec.ofNat 64 Layouts.Layout.pull) l.pull
  count : BlocksAt env m (a + BitVec.ofNat 64 Layouts.Layout.count) l.count
  bytecode : Walk.BytecodeAt env m (m.getMem (a + BitVec.ofNat 64 Layouts.Layout.bytecode)) bc

/-- A live `Vec<E>` of `xs` at `a`. -/
def EVecAt (env : Env) (m : MachineState) (a : Word) (xs : List E) : Prop :=
  LiveVecAt env Layouts.E.byteSize EListAt m a (xs.map Model.limbs)

/-- **The `BusResult` at `a` is `r`**, every buffer live. -/
structure BusResultAt (env : Env) (m : MachineState) (a : Word) (r : Model.BusResultRust) : Prop where
  claims : LiveVecAt env Layouts.ColumnClaim.byteSize (ArrayAt Layouts.ColumnClaim.byteSize (ColumnClaimAt env)) m
    (a + BitVec.ofNat 64 Layouts.BusResult.claims) r.claims
  bytecodePoint : EVecAt env m (a + BitVec.ofNat 64 Layouts.BusResult.bytecode_point) r.bytecodePoint
  point : EVecAt env m (a + BitVec.ofNat 64 Layouts.BusResult.point) r.point
  forms : LiveVecAt env Layouts.Vec.byteSize (ArrayAt Layouts.Vec.byteSize (FormsAt env)) m
    (a + BitVec.ofNat 64 Layouts.BusResult.forms) r.forms
  totals : EVecAt env m (a + BitVec.ofNat 64 Layouts.BusResult.totals) r.totals

/-- **The `Result<BusResult, VerifierError>` at `a`**: `Ok` (any tag but `Err`'s niche) with the result, or `Err`. -/
def ResultBusResultAt (env : Env) (m : MachineState) (a : Word) : Option Model.BusResultRust → Prop
  | some r => m.getMem (a + BitVec.ofNat 64 Layouts.ResultBusResult.tagOffset) ≠
        BitVec.ofNat 64 Layouts.ResultBusResult.Err.tag ∧
      BusResultAt env m (a + BitVec.ofNat 64 Layouts.ResultBusResult.Ok.f0) r
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.ResultBusResult.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultBusResult.Err.tag

/-- A table's evaluations `(point, values)` at `a`, both live `Vec<E>`s. -/
def EvaluationsAt (env : Env) (m : MachineState) (a : Word) (e : List E × List E) : Prop :=
  EVecAt env m (a + BitVec.ofNat 64 Layouts.VecEVecE.f0) e.1 ∧ EVecAt env m (a + BitVec.ofNat 64 Layouts.VecEVecE.f1) e.2

/-- **The `Result<Vec<TableEvaluations>, VerifierError>` at `a`**: `Ok` with each table's evaluations, or `Err`. -/
def ResultEvaluationsAt (env : Env) (m : MachineState) (a : Word) : Option (List (List E × List E)) → Prop
  | some rows => m.getMem (a + BitVec.ofNat 64 Layouts.ResultTableEvaluations.tagOffset) ≠
        BitVec.ofNat 64 Layouts.ResultTableEvaluations.Err.tag ∧
      LiveVecAt env Layouts.VecEVecE.byteSize (ArrayAt Layouts.VecEVecE.byteSize (EvaluationsAt env)) m
        (a + BitVec.ofNat 64 Layouts.ResultTableEvaluations.Ok.f0) rows
  | none => m.getMem (a + BitVec.ofNat 64 Layouts.ResultTableEvaluations.tagOffset) =
      BitVec.ofNat 64 Layouts.ResultTableEvaluations.Err.tag

end Rv64mc.Spec.Bus
