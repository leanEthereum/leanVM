/-
  Rv64mc.Proof.Bus.ColumnClaimT

  `verify_bus_balance`'s closure `|column, point, value| ColumnClaim { column, point: point.to_vec(), value }` is
  total: called with the result's slot (`a0`), the column (`a1`), the point's buffer and length (`a2`, `a3`) and the
  value's two limbs (`a4`, `a5`), it allocates the point's copy (`alloc`, none when it is empty; `handle_error` were
  `alloc` to return null), copies it (`memcpy`) and writes the `ColumnClaim` (`Layouts.ColumnClaim`: the point's
  `Vec<E>` at `0`, the column at `24`, the value at `32`). Its result's point is a vector's (`VecReprT.VecT`) of the
  point's length with a fresh buffer, and its column and value are the arguments; the run ends with the guest's abort
  (`AbortStop`) where `alloc` does. The precondition: the slot a caller's object (`Owned`), in a window and 8-byte
  aligned; the point `len` elements of a vector's buffer (`BufT` with the length for the capacity), which also
  bounds the bytes `alloc` is asked for.

  ## Main definitions

  * `ClaimPreT`, `ClaimPostT`, `ClaimSpecT`

  ## Main results

  * `total`
  * `next_setMem_win`, `next_setMem_win0`: `NEXT` kept by a store into a range in a window
-/

import Rv64mc.Proof.Runtime.CloneT
import Rv64mc.Gen.Tmpl.Verifier.Bus.VerifyBusBalance.Closure0

namespace Rv64mc.Proof.Bus.ColumnClaimT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)

/-- The closure's total precondition: the result's slot a caller's, in a window and 8-byte aligned; the point
    `len` elements of a vector's buffer. -/
def ClaimPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) 48 ∧ InWin env (regs .x10) 48 ∧ (regs .x10).toNat % 8 = 0 ∧
    BufT env m (regs .x13) (regs .x12) 16

/-- The closure's total postcondition: the point's copy a vector's of its length, fresh unless empty; the column
    and the value's limbs as passed. -/
def ClaimPostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ vecLen m' (regs .x10) = regs .x13 ∧
    ((regs .x13).toNat = 0 ∨ env.Fresh m m' (vecPtr m' (regs .x10)) ((regs .x13).toNat * 16)) ∧
    m'.getMem (regs .x10 + 24#64) = regs .x11 ∧ m'.getMem (regs .x10 + 32#64) = regs .x14 ∧
    m'.getMem (regs .x10 + 40#64) = regs .x15

/-- **The total contract of `verify_bus_balance::{closure#0}`**, writing its 48-byte result. -/
def ClaimSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (ClaimPreT env) (ClaimPostT env) (fun regs _ => InRange (regs .x10) 48) AbortStop

/-- `NEXT` is kept by a store into a range in a window. -/
theorem next_setMem_win {env : Env} {M : MachineState} {q v : Word} {n o : Nat} (hW : InWin env q n) (ho : o < n) :
    env.next (M.setMem (q + BitVec.ofNat 64 o) v) = env.next M := by
  unfold Env.next
  rw [MachineState.getMem_setMem_ne (Ne.symm (hW.ne_next_add ho))]

/-- `NEXT` is kept by a store at the start of a range in a window. -/
theorem next_setMem_win0 {env : Env} {M : MachineState} {q v : Word} {n : Nat} (hW : InWin env q n) (ho : 0 < n) :
    env.next (M.setMem q v) = env.next M := by
  simpa using next_setMem_win (M := M) (v := v) hW ho

set_option rv_sym.heap true in
/-- **`verify_bus_balance::{closure#0}` is total**, with 80 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Verifier.Bus.VerifyBusBalance.Closure0.Link)
    (hp : p[i]? = some (Gen.Verifier.Bus.VerifyBusBalance.Closure0.tmpl L)) (hL : L.WF p)
    {need needA needM needH : Nat} (hnA : 80 + needA ≤ need) (hnM : 80 + needM ≤ need) (hnH : 80 + needH ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hhe : Aborts env p L.handleError.idx needH) : ClaimSpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hcp, hhe]
  all_goals simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr] at *
  all_goals try rv_closeT
  all_goals
    have hl := env.layout
    have hEnd := hpre_12.heapEnd_le
    have hge := hpre_12.next_ge
    have hn0 : (regs .x13).toNat ≠ 0 := fun h => by
      first | exact hc_1 (BitVec.eq_of_toNat_eq h) | exact hc (BitVec.eq_of_toNat_eq h)
    obtain ⟨hq1, hq2, hq3⟩ := hpre_10.resolve_left hn0
    unfold Env.Live at hq2
    have hsh : (regs .x13 <<< 4).toNat = (regs .x13).toNat * 16 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by have := env.heapEnd.isLt; omega)]
    try rw [hsh] at hret1_18
    try rw [hsh]
  · omega
  · omega
  · intro _ b h1 h2
    unfold InRange at h1 h2
    omega
  · have hn2 := hret1_14.2.1
    exact .inr ⟨.inl ⟨by omega, by omega⟩, by unfold OffStack; omega, inWindow_iff.2 (.inl ⟨by omega, by omega⟩),
      by unfold OffStack; omega⟩
  all_goals
    have hW : InWin env (regs .x10) 48 := hpre_8
    try unfold Env.Live
    try unfold Env.Fresh
    rw [next_setMem_win hW (o := 40) (by decide), next_setMem_win hW (o := 32) (by decide),
      next_setMem_win hW (o := 24) (by decide), next_setMem_win hW (o := 16) (by decide),
      next_setMem_win hW (o := 8) (by decide), next_setMem_win0 hW (by decide)]
    have hn3 := hret3_14.1
  · exact .inr ⟨by omega, by omega, hret1_17⟩
  · exact .inr ⟨by omega, by omega⟩

end Rv64mc.Proof.Bus.ColumnClaimT

/-- info: 'Rv64mc.Proof.Bus.ColumnClaimT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bus.ColumnClaimT.total
