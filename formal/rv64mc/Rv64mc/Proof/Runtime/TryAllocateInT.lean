/-
  Rv64mc.Proof.Runtime.TryAllocateInT

  `RawVecInner::try_allocate_in` is total, both instances: the guest crate's (`TryAllocRv64Spec`, uninitialized)
  and the verifier's (`TryAllocSpec`'s, less what it says of the bytes when zeroing is asked). Each returns its
  result at `sret`, on `Ok` with a buffer a vector's (`VecReprT.BufT`), or the run ends with the guest's abort
  (`AbortStop`) where `alloc` finds the heap exhausted. Neither had a partial proof: these are new proofs over the
  templates, from `alloc`'s total contract (`AllocT`, its stop weakened) and, for the verifier's, `memset`'s
  (`MemsetT`). The precondition adds that the result's slot lies in a window, 8-byte aligned.

  The verifier's instance zeroes the block when `init` is nonzero by `memset`, whose total contract
  (`MemsetSafeT`) does not say which bytes it writes, so `TryAllocSafePost` leaves out `TryAllocPost`'s zeroed
  bytes.

  ## Main definitions

  * `TryAllocPreT`, `TryAllocRv64SpecT`, `TryAllocSafePost`, `TryAllocSpecT`

  ## Main results

  * `rv64_total`, `total`
-/

import Rv64mc.Spec.Runtime.TryAllocateInRv64
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Proof.Runtime.FinishGrow
import Rv64mc.Core.AbortStop
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.TryAllocateInT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin MemsetSafeT)
open Rv64mc.Proof.Runtime.VecReprT (BufT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)

/-- The result's slot, as `try_allocate_in`'s total precondition adds it: in a window, 8-byte aligned. -/
def SretWin (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  InWin env (regs .x10) tryAllocBytes ∧ (regs .x10).toNat % 8 = 0

/-- On `Ok`, the buffer the result names is a vector's, for elements of `size` bytes. -/
def OkBuf (env : Env) (size : Nat) (regs : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (taTagAt (regs .x10)) = 0#64 →
    BufT env m' (m'.getMem (taCapAt (regs .x10))) (m'.getMem (taPtrAt (regs .x10))) size

theorem res3_tag {M : MachineState} {o a b t : Word} :
    (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t).getMem (taTagAt o) = t :=
  MachineState.getMem_setMem_eq

theorem res3_cap {M : MachineState} {o a b t : Word} (ho : o.toNat + 24 < 2 ^ 64) :
    (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t).getMem (taCapAt o) = a := by
  show (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t).getMem (o + 8#64) = a
  rw [MachineState.getMem_setMem_ne (FinishGrow.ne8 ho), MachineState.getMem_setMem_ne (FinishGrow.ne816 ho),
    MachineState.getMem_setMem_eq]

theorem res3_ptr {M : MachineState} {o a b t : Word} (ho : o.toNat + 24 < 2 ^ 64) :
    (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t).getMem (taPtrAt o) = b := by
  show (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t).getMem (o + 16#64) = b
  rw [MachineState.getMem_setMem_ne (FinishGrow.ne16 ho), MachineState.getMem_setMem_eq]

theorem res3_next {env : Env} {M : MachineState} {o a b t : Word} (h : InWin env o 24) :
    env.next (((M.setMem (o + 8#64) a).setMem (o + 16#64) b).setMem o t) = env.next M := by
  unfold Env.next
  rw [MachineState.getMem_setMem_ne (Ne.symm (by simpa using h.ne_next_add (o := 0) (by decide))),
    MachineState.getMem_setMem_ne (Ne.symm (h.ne_next_add (o := 16) (by decide))),
    MachineState.getMem_setMem_ne (Ne.symm (h.ne_next_add (o := 8) (by decide)))]

/-! ## The guest crate's instance -/

/-- **The total contract of the guest crate's `try_allocate_in`**: `TryAllocRv64Spec`'s, the buffer a vector's. -/
def TryAllocRv64SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => TryAllocRv64Pre env regs m ∧ SretWin env regs m)
    (fun regs m r' m' => TryAllocRv64Post env regs m r' m' ∧ OkBuf env (regs .x13).toNat regs m') TryAllocOut
    AbortStop

set_option rv_sym.heap true in
/-- **The guest crate's `try_allocate_in` is total**, with 48 bytes of stack beyond `alloc`'s. -/
theorem rv64_total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Gen.Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64.Link)
    (hp : p[i]? = some (Gen.Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64.tmpl L)) (hL : L.WF p)
    {need needA : Nat} (hn : 48 + needA ≤ need) (hal : AllocSpecT env p L.alloc.idx needA) :
    TryAllocRv64SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal']
  all_goals try (rv_symT hp with [hL] using [hal'])
  all_goals
    have ho : (regs .x10).toNat + 24 < 2 ^ 64 := hpre_7
    have hW : InWin env (regs .x10) 24 := hpre_12
    have hge := hpre_15.next_ge
  -- `Ok` with no bytes: capacity `0`, the alignment as the pointer
  · intro _
    have hb := FinishGrow.bytes_ok hc_1 hpre_8 (by omega)
    rw [res3_cap ho, res3_ptr ho]
    refine ⟨by rw [Nat.mul_comm, ← hb.1]; exact hb.2, .inl ⟨?_, rfl, rfl⟩⟩
    rw [Nat.mul_comm, ← hb.1, hc]; rfl
  · intro _; rw [res3_cap ho]; exact .inl rfl
  -- `alloc`'s argument
  · exact (FinishGrow.bytes_ok hc_1 hpre_8 (by omega)).2
  -- `Ok` with the block `alloc` returned
  · intro _
    have hb := FinishGrow.bytes_ok hc_1 hpre_8 (by omega)
    rw [res3_cap ho, res3_ptr ho]
    rw [hb.1, Nat.mul_comm] at hret1_18
    refine ⟨by rw [Nat.mul_comm, ← hb.1]; exact hb.2,
      .inr ⟨?_, rfl, ⟨hret1_16, by rw [res3_next hW]; omega⟩, hret1_17⟩⟩
    intro h0
    rw [Nat.mul_comm, ← hb.1] at h0
    exact hc_2 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  · intro _
    have hb := FinishGrow.bytes_ok hc_1 hpre_8 (by omega)
    rw [res3_cap ho, res3_ptr ho]
    rw [hb.1, Nat.mul_comm] at hret1_18
    refine .inr ⟨by omega, ?_, hret1_17⟩
    unfold Env.Live
    rw [res3_next hW]
    omega
  -- the size overflows `isize`: `Err`
  all_goals
    intro h
    simp only [taTagAt, MachineState.getMem_setMem_eq] at h
    exact absurd h (by decide)

/-! ## The verifier's instance -/

/-- `try_allocate_in`'s total postcondition: `TryAllocPost` without the zeroed bytes, the block 8-byte aligned. -/
def TryAllocSafePost (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  m'.getMem (taTagAt (regs .x10)) = 0#64 →
    (regs .x11).toNat * (regs .x14).toNat < 2 ^ 63 ∧
    (((regs .x11).toNat * (regs .x14).toNat = 0 ∧ m'.getMem (taCapAt (regs .x10)) = 0#64) ∨
    ((regs .x11).toNat * (regs .x14).toNat ≠ 0 ∧ m'.getMem (taCapAt (regs .x10)) = regs .x11 ∧
      env.Fresh m m' (m'.getMem (taPtrAt (regs .x10))) ((regs .x11).toNat * (regs .x14).toNat) ∧
      (m'.getMem (taPtrAt (regs .x10))).toNat % 8 = 0))

/-- **The total contract of the verifier's `try_allocate_in`**: `TryAllocSafePost`, the buffer a vector's. -/
def TryAllocSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => TryAllocPre env regs m ∧ SretWin env regs m)
    (fun regs m r' m' => TryAllocSafePost env regs m r' m' ∧ OkBuf env (regs .x14).toNat regs m') TryAllocOut
    AbortStop

set_option rv_sym.heap true in
/-- **The verifier's `try_allocate_in` is total**, with 48 bytes of stack beyond `alloc`'s and `memset`'s. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Gen.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.Link)
    (hp : p[i]? = some (Gen.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.tmpl L)) (hL : L.WF p)
    {need needA needM : Nat} (hnA : 48 + needA ≤ need) (hnM : 48 + needM ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hms : MemsetSafeT env p L.memset.idx needM) :
    TryAllocSpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hms]
  all_goals try (rv_symT hp with [hL] using [hal', hms])
  all_goals
    have ho : (regs .x10).toNat + 24 < 2 ^ 64 := hpre_7
    have hW : InWin env (regs .x10) 24 := hpre_10
    have hge := hpre_13.next_ge
  -- `Ok` with no bytes: capacity `0`
  · intro _
    have hb := FinishGrow.bytes_ok hc_1 hpre_8 hpre_9
    rw [res3_cap ho]
    refine ⟨by rw [Nat.mul_comm, ← hb.1]; exact hb.2, .inl ⟨?_, rfl⟩⟩
    rw [Nat.mul_comm, ← hb.1, hc]; rfl
  · intro _; rw [res3_cap ho]; exact .inl rfl
  -- `alloc`'s argument
  · exact (FinishGrow.bytes_ok hc_1 hpre_8 hpre_9).2
  -- `Ok` with the block `alloc` returned, zeroed by `memset` or not
  all_goals try
    have hb := FinishGrow.bytes_ok hc_1 hpre_8 hpre_9
    rw [hb.1, Nat.mul_comm] at hret1_18
  all_goals try have hn2 : (env.next m1).toNat ≤ (env.next m2).toNat := hret2_14.1
  all_goals first
    | (intro _
       rw [res3_cap ho, res3_ptr ho]
       refine ⟨by rw [Nat.mul_comm, ← hb.1]; exact hb.2,
         .inr ⟨?_, rfl, ⟨hret1_16, by rw [res3_next hW]; omega⟩, hret1_17⟩⟩
       intro h0
       rw [Nat.mul_comm, ← hb.1] at h0
       exact hc_2 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)))
    | (intro _
       rw [res3_cap ho, res3_ptr ho]
       refine .inr ⟨by omega, ?_, hret1_17⟩
       unfold Env.Live
       rw [res3_next hW]
       omega)
    | (intro h
       simp only [taTagAt, MachineState.getMem_setMem_eq] at h
       exact absurd h (by decide))

end Rv64mc.Proof.Runtime.TryAllocateInT

/-- info: 'Rv64mc.Proof.Runtime.TryAllocateInT.rv64_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.TryAllocateInT.rv64_total

/-- info: 'Rv64mc.Proof.Runtime.TryAllocateInT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.TryAllocateInT.total
