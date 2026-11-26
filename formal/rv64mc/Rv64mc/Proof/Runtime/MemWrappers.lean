/-
  Rv64mc.Proof.Runtime.MemWrappers

  `memcpy`, `memmove` and `memset` are tail calls of `compiler_builtins`' functions of the same names, so they have
  their contracts (`tail_ok`): none reads `t1`.
-/

import Rv64mc.Proof.Runtime.Forward
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Gen.Tmpl.Memcpy
import Rv64mc.Gen.Tmpl.Memmove
import Rv64mc.Gen.Tmpl.Memset

namespace Rv64mc.Proof.Runtime.MemWrappers

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen

variable {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}

theorem memcpy_ok (L : Memcpy.Link) (hp : p[i]? = some (Memcpy.tmpl L)) (hL : L.WF p)
    (h : MemcpySpec env p L.memcpy.idx need) : MemcpySpec env p i need :=
  tail_ok hp rfl hL.memcpy hL.s0 h (fun _ _ h => by simpa [CopyPre, CopyApart, updReg_apply] using h)
    (fun _ _ _ _ h => by simpa [CopyPost, updReg_apply] using h)
    (fun _ _ _ h => by simpa [CopyOut, updReg_apply] using h)

theorem memmove_ok (L : Memmove.Link) (hp : p[i]? = some (Memmove.tmpl L)) (hL : L.WF p)
    (h : MemmoveSpec env p L.memmove.idx need) : MemmoveSpec env p i need :=
  tail_ok hp rfl hL.memmove hL.s0 h (fun _ _ h => by simpa [CopyPre, CopyApart, updReg_apply] using h)
    (fun _ _ _ _ h => by simpa [CopyPost, updReg_apply] using h)
    (fun _ _ _ h => by simpa [CopyOut, updReg_apply] using h)

theorem memset_ok (L : Memset.Link) (hp : p[i]? = some (Memset.tmpl L)) (hL : L.WF p)
    (h : MemsetSpec env p L.memset.idx need) : MemsetSpec env p i need :=
  tail_ok hp rfl hL.memset hL.s0 h (fun _ _ h => by simpa [SetPre, updReg_apply] using h)
    (fun _ _ _ _ h => by simpa [SetPost, updReg_apply] using h)
    (fun _ _ _ h => by simpa [CopyOut, updReg_apply] using h)

end Rv64mc.Proof.Runtime.MemWrappers
