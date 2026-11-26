/-
  Rv64mc.Proof.Bus.FrameworkT

  `verify_bus_balance::{closure#2}` (`bus.rs`'s `framework` closure) is total (`specT`): from its result's slot
  (`a0`), its captures (`a1`: `&weights`, `&memory_index`, `&memory`, `&bytecode_index`, `&bytecode_share`) and three
  `E` arguments, it returns a vector of three elements in the slot, writing at most the slot besides its stack and
  the block it allocates, or ends the run with `a0 = 2` (the allocator out of heap, `weights` shorter than five,
  `memory` shorter than two). Safety only: no partial contract states the values. `dot` is used through
  `DotSafeT.dotSafe`, over the stack arrays the closure builds.

  ## Main definitions

  * `PreT`, `PostT`, `Out`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.DotSafeT
import Rv64mc.Proof.Layout.GpowT
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.PanicsT
import Rv64mc.Proof.Runtime.VecReprT
import Rv64mc.Proof.Runtime.WinT
import Rv64mc.Tactic.SymT
import Rv64mc.Gen.Tmpl.Verifier.Bus.VerifyBusBalance.Closure2

namespace Rv64mc.Proof.Bus.FrameworkT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT RawVecT BufT)
open Rv64mc.Gen.Verifier.Bus.VerifyBusBalance.Closure2 (Link tmpl)

/-- The total precondition. The slot (`a0`, 24 bytes), the captures (`a1`, five pointers: `&weights`, `&memory_index`,
    `&memory`, `&bytecode_index`, `&bytecode_share`), each `E` a capture points to (16 bytes) and each `Vec<E>`
    header (24 bytes) in the caller's frame (at or above the stack pointer), in a window and 8-byte aligned; each
    vector's buffer, unless its length is `0`, allocated before (`Live`) for the length's elements, in a window and
    aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x2).toNat ≤ (regs .x10).toNat ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧
  (regs .x2).toNat ≤ (regs .x11).toNat ∧ InWin env (regs .x11) 40 ∧ (regs .x11).toNat % 8 = 0 ∧
  -- `weights`
  (regs .x2).toNat ≤ (m.getMem (regs .x11)).toNat ∧ InWin env (m.getMem (regs .x11)) 24 ∧
    (m.getMem (regs .x11)).toNat % 8 = 0 ∧
  ((m.getMem (m.getMem (regs .x11) + 16#64)).toNat = 0 ∨
    (env.Live m (m.getMem (m.getMem (regs .x11) + 8#64)) (16 * (m.getMem (m.getMem (regs .x11) + 16#64)).toNat) ∧
      InWin env (m.getMem (m.getMem (regs .x11) + 8#64)) (16 * (m.getMem (m.getMem (regs .x11) + 16#64)).toNat) ∧
      (m.getMem (m.getMem (regs .x11) + 8#64)).toNat % 8 = 0)) ∧
  -- `memory_index`
  (regs .x2).toNat ≤ (m.getMem (regs .x11 + 8#64)).toNat ∧ InWin env (m.getMem (regs .x11 + 8#64)) 16 ∧
    (m.getMem (regs .x11 + 8#64)).toNat % 8 = 0 ∧
  -- `memory`
  (regs .x2).toNat ≤ (m.getMem (regs .x11 + 16#64)).toNat ∧ InWin env (m.getMem (regs .x11 + 16#64)) 24 ∧
    (m.getMem (regs .x11 + 16#64)).toNat % 8 = 0 ∧
  ((m.getMem (m.getMem (regs .x11 + 16#64) + 16#64)).toNat = 0 ∨
    (env.Live m (m.getMem (m.getMem (regs .x11 + 16#64) + 8#64))
        (16 * (m.getMem (m.getMem (regs .x11 + 16#64) + 16#64)).toNat) ∧
      InWin env (m.getMem (m.getMem (regs .x11 + 16#64) + 8#64))
          (16 * (m.getMem (m.getMem (regs .x11 + 16#64) + 16#64)).toNat) ∧
      (m.getMem (m.getMem (regs .x11 + 16#64) + 8#64)).toNat % 8 = 0)) ∧
  -- `bytecode_index`, `bytecode_share`
  (regs .x2).toNat ≤ (m.getMem (regs .x11 + 24#64)).toNat ∧ InWin env (m.getMem (regs .x11 + 24#64)) 16 ∧
    (m.getMem (regs .x11 + 24#64)).toNat % 8 = 0 ∧
  (regs .x2).toNat ≤ (m.getMem (regs .x11 + 32#64)).toNat ∧ InWin env (m.getMem (regs .x11 + 32#64)) 16 ∧
    (m.getMem (regs .x11 + 32#64)).toNat % 8 = 0

/-- The total postcondition: the slot a vector of three elements. -/
def PostT (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  VecT env m' (regs .x10) 16 ∧ vecLen m' (regs .x10) = 3#64

/-- What it writes besides its stack and its allocation: the slot. -/
def Out (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) Layouts.Vec.byteSize b

/-- **The total contract of `verify_bus_balance::{closure#2}`**. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) Out (Stop := AbortStop)

/-- The postcondition the steps give: the slot's capacity and length `3`, its pointer a block allocated from the
    input and heap window's start, 8-byte aligned, of three elements. -/
def PostR (env : Env) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  m'.getMem (regs .x10) = 3#64 ∧ m'.getMem (regs .x10 + 16#64) = 3#64 ∧
    0x10000000 ≤ (m'.getMem (regs .x10 + 8#64)).toNat ∧
    (m'.getMem (regs .x10 + 8#64)).toNat + 48 ≤ (env.next m').toNat ∧ (m'.getMem (regs .x10 + 8#64)).toNat % 8 = 0

theorem postT_of_postR {env : Env} {regs r' : Reg → Word} {m m' : MachineState} (hw : InWin env (regs .x10) 24)
    (ha : (regs .x10).toNat % 8 = 0) (h : PostR env regs m r' m') : PostT env regs m r' m' := by
  obtain ⟨hc, hl, hp0, hlive, hp8⟩ := h
  have hcap : m'.getMem (rvCapAt (regs .x10)) = 3#64 := by simpa [rvCapAt] using hc
  have hptr : m'.getMem (rvPtrAt (regs .x10)) = m'.getMem (regs .x10 + 8#64) := rfl
  refine ⟨⟨hw, ⟨Runtime.MemsetT.InWin.sub hw (Nat.le_refl _)
    (by simp only [Layouts.RawVecInner.byteSize]; omega), ha, ?_, by rw [hcap]; decide⟩, ?_⟩, hl⟩
  · rw [hcap, hptr]
    exact .inr ⟨hp0, by unfold Env.Live; simpa using hlive, hp8⟩
  · simp only [vecLen, vecCap, Layouts.Vec.len, Layouts.Vec.cap, BitVec.add_zero]
    rw [hc, show (16 : Nat) = 16 from rfl, hl]

/- One straight-line path through four calls, with no loop head to cut at: the default heartbeats do not cover it. -/
set_option maxHeartbeats 1600000 in
set_option rv_sym.heap true in
/-- The steps, to `PostR`. -/
theorem total_raw (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needG needD needP needS needB : Nat} (hnA : 288 + needA ≤ need) (hnG : 288 + needG ≤ need)
    (hnD : 288 + needD ≤ need) (hnP : 288 + needP ≤ need) (hnS : 288 + needS ≤ need) (hnB : 288 + needB ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hg : Layout.GpowT.specT env p L.gpow.idx needG)
    (hd : Multilinear.DotOwnT.specT env p L.dot.idx needD)
    (hpn : Aborts env p L.panicNounwindFmt.idx needP) (hsf : Aborts env p L.sliceIndexFail.idx needS)
    (hpb : Aborts env p L.panicBoundsCheck.idx needB) :
    HoldsT env p i need (PreT env) (PostR env) Out (Stop := AbortStop) := by
  have hal' : HoldsT env p L.alloc.idx needA AllocPre (AllocPost env) (Stop := AbortStop) :=
    hal.mono_stop fun _ _ _ _ _ h => h.1
  have hd' := Multilinear.DotSafeT.dotSafe hd
  rv_autoT hp with [hL] using [hal', hg, hd', hpn, hsf, hpb]
  all_goals first
    | (have hL : 2 ≤ (m.getMem (m.getMem (regs .x11 + 16#64) + 16#64)).toNat := by
        by_contra hn
        rcases (by omega : (m.getMem (m.getMem (regs .x11 + 16#64) + 16#64)).toNat = 0 ∨
          (m.getMem (m.getMem (regs .x11 + 16#64) + 16#64)).toNat = 1) with h | h
        · exact hc (BitVec.eq_of_toNat_eq (by simpa using h))
        · exact hc_4 (BitVec.eq_of_toNat_eq (by simpa using h))
       obtain ⟨-, hwm, ham⟩ := hpre_22.resolve_left (by omega)
       first
        | exact (hwm.dword_add (o := 0) (k := 8) hpre_30 ham (by simp) (by omega) (by omega)).1
        | exact (hwm.dword_add (o := 0) (k := 8) hpre_30 ham (by simp) (by omega) (by omega)).2
        | exact (hwm.dword_add (o := 0) (k := 16) hpre_30 ham (by simp) (by omega) (by omega)).1
        | exact (hwm.dword_add (o := 0) (k := 16) hpre_30 ham (by simp) (by omega) (by omega)).2
        | exact (hwm.dword_add (o := 0) (k := 24) hpre_30 ham (by simp) (by omega) (by omega)).1
        | exact (hwm.dword_add (o := 0) (k := 24) hpre_30 ham (by simp) (by omega) (by omega)).2
        | exact (hwm.dword (o := 0) hpre_30 ham (by simp) (by omega) (by omega)).1
        | exact (hwm.dword (o := 0) hpre_30 ham (by simp) (by omega) (by omega)).2)

/-- **`verify_bus_balance::{closure#2}` is total.** -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA needG needD needP needS needB : Nat} (hnA : 288 + needA ≤ need) (hnG : 288 + needG ≤ need)
    (hnD : 288 + needD ≤ need) (hnP : 288 + needP ≤ need) (hnS : 288 + needS ≤ need) (hnB : 288 + needB ≤ need)
    (hal : Runtime.AllocT.AllocSpecT env p L.alloc.idx needA) (hg : Layout.GpowT.specT env p L.gpow.idx needG)
    (hd : Multilinear.DotOwnT.specT env p L.dot.idx needD)
    (hpn : Aborts env p L.panicNounwindFmt.idx needP) (hsf : Aborts env p L.sliceIndexFail.idx needS)
    (hpb : Aborts env p L.panicBoundsCheck.idx needB) : specT env p i need :=
  Isa.TContract.mono (total_raw env p i L hp hL hnA hnG hnD hnP hnS hnB hal hg hd hpn hsf hpb) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ _ ⟨⟨_, _, _, _, hP, _⟩, _⟩ ⟨⟨ha, hf, hs, hq⟩, hc⟩ =>
      ⟨⟨ha, hf, hs, postT_of_postR hP.2.1 hP.2.2.1 hq⟩, hc⟩)
    fun _ _ _ _ _ _ _ h => h

end Rv64mc.Proof.Bus.FrameworkT

/-- info: 'Rv64mc.Proof.Bus.FrameworkT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Bus.FrameworkT.total
