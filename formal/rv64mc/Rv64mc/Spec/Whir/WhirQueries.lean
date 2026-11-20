/-
  Rv64mc.Spec.Whir.WhirQueries

  The contract of `verifier::whir::whir_queries(log_n, log_inv_rate) -> Option<&'static [usize]>`: `log_n` in `a0`,
  `log_inv_rate` in `a1`; the result, `Model.whirQueriesRust`'s, as the slice's pointer in `a0` (`0` for `None`)
  and its length in `a1`, its elements constants of the image (`DataWords`). The table it reads, `WHIR_QUERIES`,
  is a constant of the image (`Table`): its proof takes the table's place in `env.data` as a hypothesis.
-/

import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Whir

namespace Rv64mc.Spec.Whir.WhirQueries

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **The `&'static [usize]` slice `qs` returned** in `a0` (its pointer, not null) and `a1` (its length). -/
def SliceRet (env : Env) (r' : Reg → Word) (qs : List Nat) : Prop :=
  r' .x10 ≠ 0#64 ∧ r' .x11 = BitVec.ofNat 64 qs.length ∧ DataWords env (r' .x10) (qs.map (BitVec.ofNat 64))

/-- **`WHIR_QUERIES` at `a`**: row `r` (rate `r + 1`), column `c` (size `c + 16`) is a slice header, its pointer
    and length, at `a + 240 r + 16 c`, of the tabulated counts. -/
def Table (env : Env) (a : Word) : Prop :=
  ∀ r c (hr : r < Model.whirQueriesTable.length) (hc : c < (Model.whirQueriesTable[r]).length), ∃ ptr : Word,
    ptr ≠ 0#64 ∧ DataWords env (a + BitVec.ofNat 64 (240 * r + 16 * c))
      [ptr, BitVec.ofNat 64 (Model.whirQueriesTable[r][c]).length] ∧
    DataWords env ptr ((Model.whirQueriesTable[r][c]).map (BitVec.ofNat 64))

def Post (env : Env) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  match Model.whirQueriesRust (regs .x10).toNat (regs .x11).toNat with
  | none => r' .x10 = 0#64
  | some qs => SliceRet env r' qs

/-- **The contract of `whir_queries`**, function `i` of `p` with `need` bytes of stack (a leaf without a frame). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun _ _ => True) (Post env)

end Rv64mc.Spec.Whir.WhirQueries
