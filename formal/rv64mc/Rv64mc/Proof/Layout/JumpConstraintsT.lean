/-
  Rv64mc.Proof.Layout.JumpConstraintsT

  `jump_constraints(columns)` is total: it checks the columns `V_COND`, `W`, `B` (5, 12, 13) against the slice's
  length (else `panic_bounds_check` or `panic_nounwind_fmt`), allocates two elements (`alloc`), computes them with
  two products (`E::mul`) and stores the vector at `sret`. Its result is a vector's (`VecReprT.VecT`) of two
  elements in a fresh buffer; the run ends with the guest's abort (`AbortStop`) where `alloc` or a check does. It
  does not state the two constraints.

  The precondition: `sret` a caller's (`SretPre`), in a window, aligned; the columns `SliceT` (a heap vector's
  elements or a caller's stack array).

  ## Main definitions

  * `PreT`, `PostT`, `SpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Keccak.TryFromFnT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Gen.Tmpl.Verifier.Layout.JumpConstraints

namespace Rv64mc.Proof.Layout.JumpConstraintsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Keccak.TryFromFnT (SliceT)
open Rv64mc.Gen.Verifier.Layout.JumpConstraints (Link tmpl)

/-- The total precondition: `sret` a caller's (`SretPre`), in a window, aligned; the columns `(a1, a2)` `SliceT`. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  SretPre env regs m ∧ InWin env (regs .x10) Layouts.Vec.byteSize ∧ (regs .x10).toNat % 8 = 0 ∧
    SliceT env (regs .x11) (regs .x12).toNat

/-- The total postcondition: the result a vector's (`VecT`) of two elements, its buffer fresh. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ (vecLen m' (regs .x10)).toNat = 2 ∧ env.Fresh m m' (vecPtr m' (regs .x10)) 32

/-- **The total contract of `jump_constraints`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) SretVecOut AbortStop

/-- A doubleword at offset `o` of a slice of `n` elements, below its end, in a window and aligned. -/
theorem word_ok {env : Env} {top : Word} {m : MachineState} {q : Word} {n o : Nat} (hW : Windows env top m)
    (hs : SliceT env q n) (ho : o + 8 ≤ 16 * n) (ho8 : o % 8 = 0) :
    inWindow (q + BitVec.ofNat 64 o) 8 = true ∧ (q + BitVec.ofNat 64 o).toNat % 8 = 0 := by
  rcases hs with h0 | ⟨hw, hal⟩
  · omega
  have hlt := hw.lt
  exact hw.dword hW hal (toNat_add_ofNat (by omega)) ho ho8

set_option rv_sym.heap true in
/-- **`jump_constraints` is total**, with 80 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needM needF needP : Nat} (hnA : 80 + needA ≤ need) (hnM : 80 + needM ≤ need)
    (hnF : 80 + needF ≤ need) (hnP : 80 + needP ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hmul : Field.EMulT.specT env p L.mul.idx needM)
    (hpf : Aborts env p L.panicNounwindFmt.idx needF) (hpb : Aborts env p L.panicBoundsCheck.idx needP) :
    SpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hmul, hpf, hpb]
  all_goals try simp only [rvCapAt, rvPtrAt, Layouts.RawVecInner.cap, Layouts.RawVecInner.ptr, BitVec.add_zero]
  all_goals try rv_closeT
  all_goals
    have h14 : 14 ≤ (regs .x12).toNat := by
      have h1 := BitVec.le_def.1 hc_2
      have h2 : (regs .x12).toNat ≠ 13 := fun h => hc (BitVec.eq_of_toNat_eq h)
      simp only [BitVec.toNat_ofNat] at h1
      omega
  · exact (word_ok (o := 208) hpre_12 hpre_10 (by omega) rfl).1
  · exact (word_ok (o := 216) hpre_12 hpre_10 (by omega) rfl).1

end Rv64mc.Proof.Layout.JumpConstraintsT

/-- info: 'Rv64mc.Proof.Layout.JumpConstraintsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.JumpConstraintsT.total
