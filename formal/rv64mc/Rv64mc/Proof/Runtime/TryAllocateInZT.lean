/-
  Rv64mc.Proof.Runtime.TryAllocateInZT

  The verifier's `RawVecInner::try_allocate_in` is total with `TryAllocPost`, the zeroed bytes included: the
  partial contract's postcondition, `TryAllocateInT`'s `TryAllocSafePost` (the block 8-byte aligned) and `OkBuf`.
  The proof is `TryAllocateInT.total`'s over `memset`'s contract with its bytes (`MemsetBytesT`), with one more
  goal on the zeroing path: the bytes `memset` wrote survive the three stores of the result, which lie in the
  caller's slot, below `NEXT` at entry or at or above the stack pointer, apart from the fresh block.
  `TryAllocSpecZT.safe` gives `TryAllocateInT`'s `TryAllocSpecT` back.

  ## Main definitions

  * `ZeroPost`, `TryAllocSpecZT`

  ## Main results

  * `total`
  * `TryAllocSpecZT.safe`: the zeroed bytes dropped, `TryAllocSpecT`
-/

import Rv64mc.Proof.Runtime.TryAllocateInT
import Rv64mc.Proof.Runtime.MemsetBytesT

namespace Rv64mc.Proof.Runtime.TryAllocateInZT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.MemsetBytesT (MemsetSpecT)
open Rv64mc.Proof.Runtime.TryAllocateInT (SretWin OkBuf TryAllocSafePost TryAllocSpecT res3_cap res3_ptr res3_next)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)

/-- On `Ok` with bytes, when zeroing is asked, the block's bytes are zero. -/
def ZeroPost (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (taTagAt (regs .x10)) = 0#64 → (regs .x11).toNat * (regs .x14).toNat ≠ 0 → regs .x12 ≠ 0#64 →
    ∀ k, k < (regs .x11).toNat * (regs .x14).toNat →
      m'.getByte (m'.getMem (taPtrAt (regs .x10)) + BitVec.ofNat 64 k) = 0#8

/-- `TryAllocSafePost` and `ZeroPost` give `TryAllocPost`. -/
theorem tryAllocPost_of {env : Env} {regs : Reg → Word} {m : MachineState} {r' : Reg → Word} {m' : MachineState}
    (hs : TryAllocSafePost env regs m r' m') (hz : ZeroPost regs m r' m') : TryAllocPost env regs m r' m' := by
  intro ht
  obtain ⟨hb, h0 | ⟨hn, hc, hf, _⟩⟩ := hs ht
  · exact ⟨hb, .inl h0⟩
  · exact ⟨hb, .inr ⟨hn, hc, hf, hz ht hn⟩⟩

/-- **The total contract of the verifier's `try_allocate_in` with its zeroed bytes**: `TryAllocPost`, and
    `TryAllocSpecT`'s `TryAllocSafePost` and `OkBuf`. -/
def TryAllocSpecZT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => TryAllocPre env regs m ∧ SretWin env regs m)
    (fun regs m r' m' => TryAllocPost env regs m r' m' ∧ TryAllocSafePost env regs m r' m' ∧
      OkBuf env (regs .x14).toNat regs m') TryAllocOut AbortStop

/-- The zeroed bytes dropped: `TryAllocSpecT`. -/
theorem TryAllocSpecZT.safe {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : TryAllocSpecZT env p i need) :
    TryAllocSpecT env p i need :=
  Isa.TContract.mono h (fun _ _ _ _ hp => hp)
    (fun _ _ _ _ _ _ _ ⟨⟨ha, hf, hs, hp⟩, hc⟩ => ⟨⟨ha, hf, hs, hp.2⟩, hc⟩) fun _ _ _ _ _ _ _ hs => hs

/-- A byte of the block survives a doubleword store to the result's slot, which lies apart from it. -/
theorem getByte_setMem_apart {M : MachineState} {o v x : Word} (h : o.toNat + 8 ≤ x.toNat ∨ x.toNat < o.toNat) :
    (M.setMem o v).getByte x = M.getByte x := by
  refine getByte_setMem_ne fun he => ?_
  have := toNat_alignToDword x
  rw [← he] at this
  omega

set_option rv_sym.heap true in
/-- **The verifier's `try_allocate_in` is total, with its zeroed bytes.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Gen.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.Link)
    (hp : p[i]? = some (Gen.Alloc.RawVec.RawVecInner.TryAllocateInInVerifier.tmpl L)) (hL : L.WF p)
    {need needA needM : Nat} (hnA : 48 + needA ≤ need) (hnM : 48 + needM ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hms : MemsetSpecT env p L.memset.idx needM) :
    TryAllocSpecZT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  suffices h : HoldsT env p i need (fun regs m => TryAllocPre env regs m ∧ SretWin env regs m)
      (fun regs m r' m' => (TryAllocSafePost env regs m r' m' ∧ OkBuf env (regs .x14).toNat regs m') ∧
        ZeroPost regs m r' m') TryAllocOut AbortStop from
    Isa.TContract.mono h (fun _ _ _ _ hp => hp)
      (fun _ _ _ _ _ _ _ ⟨⟨ha, hf, hs, ⟨hp1, hp2⟩, hz⟩, hc⟩ => ⟨⟨ha, hf, hs, tryAllocPost_of hp1 hz, hp1, hp2⟩, hc⟩)
      fun _ _ _ _ _ _ _ hs => hs
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
  · intro _ hn
    have hb := FinishGrow.bytes_ok hc_1 hpre_8 hpre_9
    exact absurd (by rw [Nat.mul_comm, ← hb.1, hc]; rfl) hn
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
    | (intro _ _ h; exact absurd ‹regs .x12 = 0#64› h)
    | (intro _ _ _ k hk
       have hl := env.layout
       have hn1 := hret1_14.2.1
       have := env.stackLimit.isLt
       have := top.isLt
       have h6 : (regs .x10).toNat + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x10).toNat := by
         rw [← hpre_2]; exact hpre_6
       rw [res3_ptr ho]
       have hx : (r1 .x10 + BitVec.ofNat 64 k).toNat = (r1 .x10).toNat + k := toNat_add_ofNat (by omega)
       have h8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
       have h16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
       rw [getByte_setMem_apart (by omega), getByte_setMem_apart (by omega), getByte_setMem_apart (by omega),
         hret2_17 k (by rw [hb.1, Nat.mul_comm]; exact hk)]
       rfl)

end Rv64mc.Proof.Runtime.TryAllocateInZT

/-- info: 'Rv64mc.Proof.Runtime.TryAllocateInZT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.TryAllocateInZT.total
