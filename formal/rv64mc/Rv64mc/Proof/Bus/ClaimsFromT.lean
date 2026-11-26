/-
  Rv64mc.Proof.Bus.ClaimsFromT

  `<Vec<ColumnClaim> as From<[ColumnClaim; 2]>>::from` is total: called with the result's slot (`a0`) and the
  array (`a1`, 96 bytes), it allocates a buffer of two `ColumnClaim`s (`alloc`; `panic_nounwind_fmt` were `alloc` to
  return null), copies the array into it (`memcpy`) and writes the header (capacity and length `2`). Its result is a
  vector's (`VecReprT.VecT`) of length `2`, its buffer fresh and holding the array's bytes, so a caller keeps what it
  knew of the two claims; the run ends with the guest's abort (`AbortStop`) where `alloc` does. The precondition: the
  slot a caller's object (`SretPre`), in a window and 8-byte aligned; the array a caller's object (`Owned`: below
  `NEXT` or at or above the stack pointer) in a window.

  ## Main definitions

  * `FromPreT`, `FromPostT`, `FromSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Bus.ColumnClaimT
import Rv64mc.Proof.Runtime.TryAllocateInZT
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From

namespace Rv64mc.Proof.Bus.ClaimsFromT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemcpyT (MemcpySpecT)
open Rv64mc.Proof.Bus.ColumnClaimT (next_setMem_win next_setMem_win0)
open Rv64mc.Proof.Runtime.TryAllocateInZT (getByte_setMem_apart)

/-- `from`'s total precondition: the result's slot a caller's, in a window and 8-byte aligned; the array a caller's,
    in a window. -/
def FromPreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
    InWin env (regs .x11) 96 ∧ env.Owned m (regs .x2) (regs .x11) 96

/-- `from`'s total postcondition: the result a vector's of length `2`, its buffer fresh, holding the array's bytes. -/
def FromPostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 48 ∧ vecLen m' (regs .x10) = 2#64 ∧ env.Fresh m m' (vecPtr m' (regs .x10)) 96 ∧
    ∀ k, k < 96 → m'.getByte (vecPtr m' (regs .x10) + BitVec.ofNat 64 k) = m.getByte (regs .x11 + BitVec.ofNat 64 k)

/-- **The total contract of `Vec<ColumnClaim>::from([ColumnClaim; 2])`.** -/
def FromSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (FromPreT env) (FromPostT env) SretVecOut AbortStop

set_option rv_sym.heap true in
/-- **`Vec<ColumnClaim>::from` is total**, with 32 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat)
    (L : Gen.Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From.Link)
    (hp : p[i]? = some (Gen.Alloc.Vec.VecColumnClaim.AsFromArrColumnClaimN2.From.tmpl L)) (hL : L.WF p)
    {need needA needM needP : Nat} (hnA : 32 + needA ≤ need) (hnM : 32 + needM ≤ need) (hnP : 32 + needP ≤ need)
    (hal : AllocSpecT env p L.alloc.idx needA) (hcp : MemcpySpecT env p L.memcpy.idx needM)
    (hpa : Aborts env p L.panicNounwindFmt.idx needP) : FromSpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hcp, hpa]
  all_goals simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr] at *
  all_goals try rv_closeT
  all_goals
    have hl := env.layout
    have hW : Windows env top m := ‹_›
    have hEnd := hW.heapEnd_le
    have hge := hW.next_ge
    have hsrc : (regs .x11).toNat + 96 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x11).toNat := by
      rw [← hpre_2]; exact hpre_11
    have hown : (regs .x10).toNat + 24 ≤ (env.next m).toNat ∨ top.toNat ≤ (regs .x10).toNat := by
      rw [← hpre_2]; exact hpre_6
    have hn1 := hret1_14.2.1
    have ht32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    simp only [show (96#64 : Word).toNat = 96 from rfl] at *
  -- `memcpy`'s ranges: the fresh block, and the source below `NEXT` or in a caller's frame
  · exact Or.inr ⟨.inl ⟨by omega, by omega⟩, by unfold OffStack; omega,
      MemsetT.InWin.inWindow hpre_10 hW, by unfold OffStack; omega⟩
  -- the bytes copied, apart from the header's three words and from the prologue's slots
  · intro k hk
    have hx : (r1 .x10 + BitVec.ofNat 64 k).toNat = (r1 .x10).toNat + k := toNat_add_ofNat (by omega)
    have h8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
    have h16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
    rw [getByte_setMem_apart (by omega), getByte_setMem_apart (by omega), getByte_setMem_apart (by omega),
      hret3_17 k (by omega)]
    have hs : (regs .x11 + BitVec.ofNat 64 k).toNat = (regs .x11).toNat + k := toNat_add_ofNat (by omega)
    have ha := toNat_alignToDword (regs .x11 + BitVec.ofNat 64 k)
    have ht8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have ht16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have ht24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    rw [Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega), Env.next_setMem_stack (by omega),
      Env.next_setMem_stack (by omega)] at keep1_2
    refine (getByte_congr (keep1_2 _ (by omega))).trans ?_
    have hne : ∀ c : Word, (top + c).toNat + 8 ≤ top.toNat → top.toNat ≤ (top + c).toNat + 32 →
        top + c ≠ alignToDword (regs .x11 + BitVec.ofNat 64 k) := fun c h1 h2 he => by
      have := congrArg BitVec.toNat he
      omega
    rw [getByte_setMem_ne (hne 18446744073709551584#64 (by rw [ht32]; omega) (by rw [ht32]; omega)),
      getByte_setMem_ne (hne 18446744073709551592#64 (by rw [ht24]; omega) (by rw [ht24]; omega)),
      getByte_setMem_ne (hne 18446744073709551600#64 (by rw [ht16]; omega) (by rw [ht16]; omega)),
      getByte_setMem_ne (hne 18446744073709551608#64 (by rw [ht8]; omega) (by rw [ht8]; omega))]

end Rv64mc.Proof.Bus.ClaimsFromT

/-- info: 'Rv64mc.Proof.Bus.ClaimsFromT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bus.ClaimsFromT.total
