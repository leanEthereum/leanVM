/-
  Rv64mc.Proof.Transcript.SpongeReprT

  The representation the total contracts of `Sponge`'s methods share (`SpongeT`): the sponge at `a` (`Layouts.Sponge`,
  `328` bytes) 8-byte aligned, its bytes in a window (`InWin`), at most four scalars waiting (`n_pending`, at `320`),
  and its ground challenge's tag `None`'s or `Some`'s (at `0`). It is what their safety reads: the window for every
  access, and nothing else, since every index the methods compute from `n_pending` is checked (`slice_index_fail`,
  `panic_bounds_check`). The two field facts are kept because the partial contracts' `SpongeAt` asks them of every
  sponge (`SpongeRust.Inv`'s bound, `OptionEAt`'s tag), and `Transcript::next`'s total contract asks `SpongeAt` of the
  transcript it reads.

  ## Main definitions

  * `SpongeT`
-/

import Rv64mc.Spec.Transcript.Repr
import Rv64mc.Proof.Runtime.MemsetT

namespace Rv64mc.Proof.Transcript.SpongeReprT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript
open Rv64mc.Proof.Runtime.MemsetT (InWin)

/-- **The sponge at `a`, well-formed for its methods' safety**: 8-byte aligned, its `328` bytes in a window, at most
    four scalars waiting, its ground challenge's tag `0` (`None`) or `1` (`Some`). -/
def SpongeT (env : Env) (m : MachineState) (a : Word) : Prop :=
  a.toNat % 8 = 0 ∧ InWin env a 328 ∧ (m.getMem (a + 320#64)).toNat ≤ 4 ∧ (m.getMem a = 0#64 ∨ m.getMem a = 1#64)

end Rv64mc.Proof.Transcript.SpongeReprT
