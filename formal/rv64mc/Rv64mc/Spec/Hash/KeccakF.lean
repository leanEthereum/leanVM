/-
  Rv64mc.Spec.Hash.KeccakF

  The contract of `verifier::hash::keccak_f(state: &mut [u64; 25])`: the state's `25` lanes at `a0`, in memory its
  caller may write (`Owned`); it leaves there `Model.keccakFRust`'s permutation of them. It writes the state
  (`Out`).
-/

import Rv64mc.Core.Repr
import Rv64mc.Model.Hash

namespace Rv64mc.Spec.Hash.KeccakF

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The state's size in bytes: `25` lanes. -/
abbrev stateBytes : Nat := 8 * 25

def Pre (env : Env) (ws : List Word) (regs : Reg → Word) (m : MachineState) : Prop :=
  ws.length = 25 ∧ WordsAt m (regs .x10) ws ∧ env.Owned m (regs .x2) (regs .x10) stateBytes

def Post (ws : List Word) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  WordsAt m' (regs .x10) (Model.keccakFRust ws)

/-- What it writes besides its stack: the state. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) stateBytes b

/-- **The contract of `keccak_f`**, function `i` of `p` with `need` bytes of stack, for every state. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ ws, Holds env p i need (Pre env ws) (Post ws) Out

end Rv64mc.Spec.Hash.KeccakF
