/-
  Rv64mc.Proof.Runtime.BoxNewUninit

  `Box::<T>::new_uninit` meets `BoxNewUninitSpec` for its `T` of 80 bytes (the constant of its code): `alloc(80)`,
  and `panic_nounwind_fmt` if that were null, which the allocator never returns.
-/

import Rv64mc.Spec.Runtime.Boxed
import Rv64mc.Spec.Runtime.Alloc
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Alloc.Boxed.BoxNewUninit
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Runtime.BoxNewUninit

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Alloc.Boxed.BoxNewUninit (Link tmpl)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA : Nat} (hn : 16 + needA ≤ need) (hal : AllocSpec env p L.alloc.idx needA)
    (hpanic : NoReturn env p L.panicNounwindFmt.idx needA) : BoxNewUninitSpec env 80 p i need := by
  rv_auto hp with [hL] using [hal, hpanic]
  · decide
  · have hb8 : env.stackLimit.toNat ≤ (top + 0xfffffffffffffff8#64).toNat := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    rw [Env.next_setMem_stack hb8] at hret1_16
    rw [show (80#64 : Word).toNat = 80 by decide] at hret1_18
    exact ⟨hret1_16, Nat.le_of_eq hret1_18⟩

end Rv64mc.Proof.Runtime.BoxNewUninit
