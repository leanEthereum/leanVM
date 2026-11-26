/-
  Rv64mc.Spec.Runtime.Drop

  The contract of the drop glue the image keeps (`Layout`, `Vec<Vec<Form>>`, `Vec<Table>`, `Vec<BusBlock>`,
  `Vec<Form>`, `Vec<(StackWeight, E)>`): the allocator never frees (`dealloc` is a no-op), so a drop walks its
  value, or not even that, and writes nothing beyond its own stack: `Holds`'s frame with nothing in `out`.
-/

import Rv64mc.Core.Holds

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **A drop writes nothing a caller sees**: any arguments, and the calling convention and memory frame alone. -/
def DropSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun _ _ => True) (fun _ _ _ _ => True)

end Rv64mc.Spec.Runtime
