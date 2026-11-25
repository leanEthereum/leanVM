/-
  Rv64mc.Proof.Runtime.MemWrappersT

  The C wrappers `memcpy` and `memmove` are total, from `compiler_builtins`' functions of the same names
  (`MemcpySpecT`, `MemmoveSpecT`, taken as hypotheses): each is a tail call (`MemsetT.tail_total`), and neither
  contract reads `t1`, which the call writes. The total counterpart of `MemWrappers.lean`'s `memcpy_ok` and
  `memmove_ok`; `memset`'s is `MemsetT.memset_total`.

  ## Main results

  * `memcpy_total`, `memmove_total`
-/

import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Proof.Runtime.MemcpyT
import Rv64mc.Proof.Runtime.MemmoveT
import Rv64mc.Gen.Tmpl.Memcpy
import Rv64mc.Gen.Tmpl.Memmove

namespace Rv64mc.Proof.Runtime.MemWrappersT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (tail_total)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Runtime.MemmoveT (MemmoveSpecT)
open Rv64mc.Gen

variable {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}

/-- **The C wrapper `memcpy` is total**, from `compiler_builtins`' `memcpy`. -/
theorem memcpy_total (L : Memcpy.Link) (hp : p[i]? = some (Memcpy.tmpl L)) (hL : L.WF p)
    (h : MemcpySpecT env p L.memcpy.idx need) : MemcpySpecT env p i need :=
  tail_total hp rfl hL.memcpy hL.s0 h (fun _ _ h => by simpa [CopyPreT, CopyPre, updReg_apply] using h)
    (fun _ _ _ _ h => by simpa [CopyPostT, updReg_apply] using h)
    (fun _ _ _ h => by simpa [CopyOut, updReg_apply] using h)

/-- **The C wrapper `memmove` is total**, from `compiler_builtins`' `memmove`. -/
theorem memmove_total (L : Memmove.Link) (hp : p[i]? = some (Memmove.tmpl L)) (hL : L.WF p)
    (h : MemmoveSpecT env p L.memmove.idx need) : MemmoveSpecT env p i need :=
  tail_total hp rfl hL.memmove hL.s0 h (fun _ _ h => by simpa [CopyPreT, CopyPre, updReg_apply] using h)
    (fun _ _ _ _ h => by simpa [CopyPostT, updReg_apply] using h)
    (fun _ _ _ h => by simpa [CopyOut, updReg_apply] using h)

end Rv64mc.Proof.Runtime.MemWrappersT

/-- info: 'Rv64mc.Proof.Runtime.MemWrappersT.memcpy_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemWrappersT.memcpy_total

/-- info: 'Rv64mc.Proof.Runtime.MemWrappersT.memmove_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemWrappersT.memmove_total
