/-
  Rv64mc.Spec.Layout.Table

  The contracts of `Table::n_constraints` and `Table::count_columns`, which the compiled code calls with the table's
  `opcode` in `a0` (LLVM passes the one field they read): an index into a constant table of the static data, a
  bounds check panicking past the sixth table. `n_constraints` returns `N_CONSTRAINTS[opcode]` in `a0`;
  `count_columns` returns the static slice `COUNT_COLUMNS[opcode]` as a pointer and a length in `a0`, `a1`, its
  words fixed wherever the static data hold. What the tables hold is a hypothesis of each proof, discharged from
  the image's data (`NConstraintsData`, `CountColumnsData`).
-/

import Rv64mc.Core.ReprLemmas
import Rv64mc.Model.Layout

namespace Rv64mc.Spec.Layout.Table

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- Leaves without a frame; their panic needs none. -/
def need : Nat := 0

/-! ## `n_constraints` -/

/-- `N_CONSTRAINTS` at the data reference `d`. -/
def NConstraintsData (env : Env) (d : DataRef) : Prop :=
  DataRef.Words env d (Model.nConstraintsRust.map (BitVec.ofNat 64))

def NConstraintsPost (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = BitVec.ofNat 64 (Model.nConstraintsRust.getD (regs .x10).toNat 0)

/-- **The contract of `Table::n_constraints`**, function `i` of `p`. -/
def nConstraintsSpec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  Holds env p i need (fun _ _ => True) NConstraintsPost

/-! ## `count_columns` -/

/-- **`COUNT_COLUMNS` at the data reference `d`**: entry `k` a static slice, its pointer and length at
    `d + 16 k`, holding table `k`'s count columns, the same wherever the static data hold. -/
def CountColumnsData (env : Env) (d : DataRef) : Prop :=
  ∀ k, k < 6 → ∃ q : Word, ∀ m, env.Static m →
    m.getMem (d.hi + d.lo + BitVec.ofNat 64 (16 * k)) = q ∧
    m.getMem (d.hi + d.lo + BitVec.ofNat 64 (16 * k + 8)) = BitVec.ofNat 64 (Model.countColumnsRust.getD k []).length ∧
    WordsAt m q ((Model.countColumnsRust.getD k []).map (BitVec.ofNat 64))

/-- The slice returned holds the table's count columns wherever the static data hold. -/
def CountColumnsPost (env : Env) (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) :
    Prop :=
  ∀ m, env.Static m →
    SliceArgs WordsAt m (r' .x10) (r' .x11) ((Model.countColumnsRust.getD (regs .x10).toNat []).map (BitVec.ofNat 64))

/-- **The contract of `Table::count_columns`**, function `i` of `p`. -/
def countColumnsSpec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  Holds env p i need (fun _ _ => True) (CountColumnsPost env)

end Rv64mc.Spec.Layout.Table
