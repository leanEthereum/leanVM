/-
  Rv64mc.Proof.Runtime.BoxNewUninitT

  `Box::<T>::new_uninit` is total for its `T` of 80 bytes: `BoxNewUninitSpec`'s block (fresh, 8-byte aligned), or
  the run ends with the guest's abort (`AbortStop`) where `alloc` finds the heap exhausted. From `alloc`'s total
  contract (`AllocT`, its stop weakened) and `panic_nounwind_fmt`'s `Aborts` (not reached: the allocator never
  returns null). The partial proof (`BoxNewUninit.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `BoxNewUninitSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.BoxNewUninit
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.BoxNewUninitT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Gen.Alloc.Boxed.BoxNewUninit (Link tmpl)

/-- **The total contract of `Box::<T>::new_uninit`**, `T` of `size` bytes: `BoxNewUninitSpec`'s. -/
def BoxNewUninitSpecT (env : Env) (size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun _ _ => True) (fun _ m r' m' => (r' .x10).toNat % 8 = 0 ∧ env.Fresh m m' (r' .x10) size)
    (Stop := AbortStop)

/-- **`Box::<T>::new_uninit` is total**, with 16 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA : Nat} (hn : 16 + needA ≤ need) (hal : AllocSpecT env p L.alloc.idx needA)
    (hpanic : Aborts env p L.panicNounwindFmt.idx needA) : BoxNewUninitSpecT env 80 p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hpanic]
  · decide
  · have hb8 : env.stackLimit.toNat ≤ (top + 0xfffffffffffffff8#64).toNat := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    rw [Env.next_setMem_stack hb8] at hret1_16
    rw [show (80#64 : Word).toNat = 80 by decide] at hret1_18
    exact ⟨hret1_16, Nat.le_of_eq hret1_18⟩

end Rv64mc.Proof.Runtime.BoxNewUninitT

/-- info: 'Rv64mc.Proof.Runtime.BoxNewUninitT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.BoxNewUninitT.total
