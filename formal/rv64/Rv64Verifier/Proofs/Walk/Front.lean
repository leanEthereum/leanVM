import Rv64Verifier.Proofs.Walk.Spec
import Rv64Verifier.Proofs.Walk.Announced
import Rv64Verifier.Proofs.Walk.Limbs
import Rv64Verifier.Proofs.Walk.Rows
import Rv64Verifier.Proofs.Walk.Head
import Rv64Verifier.Proofs.Walk.R5
import Rv64Verifier.Proofs.Walk.R6
import Rv64Verifier.Proofs.Walk.R6U
import Rv64Verifier.Proofs.Walk.R7D
import Rv64Verifier.Proofs.Walk.R8B
import Rv64Verifier.Proofs.Walk.AtDeref
import Rv64Verifier.Proofs.Walk.AtR10
import Rv64Verifier.Proofs.Walk.ExtB10
import Rv64Verifier.Proofs.Walk.R11
import Rv64Verifier.Proofs.Walk.Tl12
import Rv64Verifier.Proofs.Walk.R13
import Rv64Verifier.Proofs.Walk.Lay14
import Rv64Verifier.Proofs.Walk.R16B
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Layout.All
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Transcript.All
import Rv64Verifier.Proofs.Hash.All
import Rv64Verifier.Proofs.Bus.All

/-!
# `walk`'s front, assembled

`front`: from `walk`'s entry to `AtR17` (`0x800035f0`), an `Err` return or a dead end, the
`hFront` of `walk_spec_of`. The stages chain in code order; every callee's contract is the proved
one, but for `verify_bus_balance`'s (`BusBalanceSpec`, or its two open stages in `frontV`), the
`Bytecode`'s reading by it (`BcWalk`), and DEREF, JUMP and the tables' vector (`AtDeref` to `AtR10`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Model

/-- From `u`, a state where `P` holds, or an `Err` return, or a dead end. -/
def Next (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (P : MachineState → Prop) : Prop :=
  ∃ t, Reaches Image.code u t ∧ (P t ∨ Done OI s t ∨ Dead Image.code t)

section Next
variable {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
  {P Q : MachineState → Prop}

theorem Next.bind (h : Next OI s u P) (k : ∀ t, P t → Next OI s t Q) : Next OI s u Q := by
  obtain ⟨t, hr, hp | hd | hd⟩ := h
  · obtain ⟨v, hr', hv⟩ := k t hp
    exact ⟨v, hr.trans hr', hv⟩
  · exact ⟨t, hr, Or.inr (Or.inl hd)⟩
  · exact ⟨t, hr, Or.inr (Or.inr hd)⟩

theorem Next.mono (h : Next OI s u P) (k : ∀ t, P t → Q t) : Next OI s u Q := by
  obtain ⟨t, hr, hp | hd⟩ := h
  · exact ⟨t, hr, Or.inl (k t hp)⟩
  · exact ⟨t, hr, Or.inr hd⟩

theorem Next.ofDone (h : ∃ t, Reaches Image.code u t ∧ (P t ∨ Done OI s t)) : Next OI s u P := by
  obtain ⟨t, hr, hp | hd⟩ := h
  · exact ⟨t, hr, Or.inl hp⟩
  · exact ⟨t, hr, Or.inr (Or.inl hd)⟩

theorem Next.ofDead (h : ∃ t, Reaches Image.code u t ∧ (P t ∨ Dead Image.code t)) :
    Next OI s u P := by
  obtain ⟨t, hr, hp | hd⟩ := h
  · exact ⟨t, hr, Or.inl hp⟩
  · exact ⟨t, hr, Or.inr (Or.inr hd)⟩

theorem Next.ofDead' (h : ∃ t, Reaches Image.code u t ∧ (Dead Image.code t ∨ P t)) :
    Next OI s u P := by
  obtain ⟨t, hr, hd | hp⟩ := h
  · exact ⟨t, hr, Or.inr (Or.inr hd)⟩
  · exact ⟨t, hr, Or.inl hp⟩

theorem Next.ofDoneDead (h : ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t ∨ P t)) :
    Next OI s u P := by
  obtain ⟨t, hr, hd | hd | hp⟩ := h
  · exact ⟨t, hr, Or.inr (Or.inl hd)⟩
  · exact ⟨t, hr, Or.inr (Or.inr hd)⟩
  · exact ⟨t, hr, Or.inl hp⟩

end Next

variable {OI : MachineState → Word → List (List Opening) → Prop}

/-- R0..R4: the entry to `build_layout`'s head checked (`Head`). -/
theorem frontHead {s : MachineState} (hpc : s.pc = 0x80000ef8) (hpre : WalkPre s) :
    Next OI s s (fun t ↦ t.pc = 0x80001338 ∧ ∃ A k, Head OI s t A k) := by
  refine Next.bind (toScalars Runtime.memset Runtime.memcpy Hash.keccakF Transcript.nextScalars hpc
    hpre) fun v ⟨hv, h⟩ ↦ ?_
  refine (Next.ofDone (high hpre hv h)).bind fun w ⟨hw, h⟩ ↦ ?_
  refine Next.bind (rowsStage Runtime.alloc_spec hpre hw h) fun x ⟨hx, h⟩ ↦ ?_
  exact (Next.ofDone (headStage hpre hx h)).mono fun t ⟨ht, k, h⟩ ↦ ⟨ht, _, k, h⟩

/-- `keccak_cell_lanes`' and `flushes_keccak`'s operands' contracts. -/
theorem loopSpecs : LoopSpecs :=
  ⟨Layout.limb_proved, Layout.term_proved, Layout.prod_proved, Layout.col_proved,
    Layout.memory_proved, Layout.add_scaled_proved, Layout.counted_proved⟩

/-- R5..R6: the heights and `flushes_keccak()` (`KM` at `0x80001f00`). -/
theorem frontKeccak {s u : MachineState} {A : List E} {k : Nat} (hpre : WalkPre s)
    (hpc : u.pc = 0x80001338) (h : Head OI s u A k) :
    Next OI s u (fun t ↦ t.pc = 0x80001f00 ∧
      ∃ R Q B, KM OI s t A k R Q B 1 LayoutMirror.flushesKeccakRust) := by
  refine (Next.ofDead (r5 Runtime.alloc_spec Runtime.reserveFast_8000d628 hpre hpc h)).bind
    fun v ⟨hv, Q, h⟩ ↦ ?_
  refine (Next.ofDead (r6a Runtime.alloc_spec Runtime.reserveFast_80004aec
    Layout.state_step_proved Layout.col_proved Layout.bytecode_proved hpre hv h)).bind
    fun w ⟨hw, h⟩ ↦ ?_
  exact (Next.ofDead (keccakLoop loopSpecs Layout.cell_lanes_proved hpre h hw)).mono
    fun t ⟨ht, h⟩ ↦ ⟨ht, _, _, _, h⟩

/-- R7..R8 up to DEREF: KECCAK's padding, the XOR, MUL and SET tables (`AtDeref`). -/
theorem frontDeref {s u : MachineState} {A : List E} {k : Nat} {R Q : Word} {B : Nat}
    (hpre : WalkPre s) (hpc : u.pc = 0x80001f00)
    (h : KM OI s u A k R Q B 1 LayoutMirror.flushesKeccakRust) :
    Next OI s u (fun t ↦ ∃ Bb, AtDeref OI s t A k R Q B Bb) := by
  refine (Next.ofDead (r7 Proofs.Multilinear.fromElem Runtime.memset Hash.keccakF Runtime.memcpy
    Runtime.alloc_spec hpre h hpc)).bind fun v ⟨hv, Bb, h, x8⟩ ↦ ?_
  refine (Next.ofDead (xorStage Layout.flushes_arith_proved Proofs.Multilinear.fromElem hpre h x8
    hv)).bind fun w ⟨hw, h, r, x10, x11, x12, x1⟩ ↦ ?_
  refine (Next.ofDead (mulStage Layout.flushes_arith_proved Proofs.Multilinear.fromElem hpre h r
    x10 x11 x12 x1 hw)).bind fun x ⟨hx, h, r, he, x10, x1⟩ ↦ ?_
  exact (Next.ofDead (setStage_atDeref Layout.state_step_proved Runtime.alloc_spec
    Layout.col_proved Layout.term_proved Layout.bytecode_proved Layout.prod_proved
    Layout.memory_cols_proved Proofs.Multilinear.fromElem hpre h r he x10 x1 hx)).mono
    fun t h ↦ ⟨_, h⟩

/-- R10..R12: the bus blocks, `kappas`, `blocks` and `block_kappas` (`AtR13`). -/
theorem frontR13 {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word} (hpre : WalkPre s)
    (h : AtR10 OI s u A k R Q B) :
    Next OI s u (fun t ↦ t.pc = 0x800032b8 ∧
      ∃ lo lo2 lo3 G BK, AtR13 OI s t A k R Q B lo lo2 lo3 G BK) := by
  refine (Next.ofDead' (r10c hpre h)).bind fun v ⟨hv, h⟩ ↦ ?_
  refine (Next.ofDead' (r11 Runtime.alloc_spec Runtime.tryAllocZeroed Runtime.reserveFast_8000d628
    Runtime.reserveFresh_8000d628 Runtime.memcpy hpre hv h)).bind fun w ⟨hw, h⟩ ↦ ?_
  exact (Next.ofDead' (r12 Runtime.alloc_spec Runtime.tryAllocZeroed Runtime.reserveFast_8000d628
    Runtime.reserveFresh_8000d628 hpre hw h)).mono fun t ⟨ht, G, BK, h⟩ ↦ ⟨ht, _, _, _, G, BK, h⟩

/-- R13..R16: the placements, the `Layout`, the root and `verify_bus_balance` (`AtR17`). -/
theorem frontR17 {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hBB : Bus.BusBalanceSpec BcOk bev)
    (hBW : BcWalk BcOk bev) {s u : MachineState} {A : List E} {k : Nat} {R Q B : Word}
    {lo lo2 lo3 : Nat} {G BK : Word} (hpre : WalkPre s) (hpc : u.pc = 0x800032b8)
    (h : AtR13 OI s u A k R Q B lo lo2 lo3 G BK) :
    Next OI s u (fun t ↦ ∃ layout rows lir bus, AtR17 OI s t layout rows lir bus) := by
  refine (Next.ofDead' (r13 Proofs.Multilinear.stackOffsets Runtime.tryAllocZeroed hpre hpc
    h)).bind fun v ⟨hv, PL, h⟩ ↦ ?_
  refine (Next.ofDoneDead (r14 Runtime.memcpy Runtime.dropLayout hpre hv h)).bind
    fun w ⟨hw, h⟩ ↦ ?_
  exact r1516 Transcript.nextScalars hBB hBW Runtime.dropLayout hpre hw h

/-- **`walk`'s front**: `walk_spec_of`'s `hFront`, given DEREF, JUMP and the tables' vector
(`hDJ`), `verify_bus_balance`'s contract and its reading of the `Bytecode`. -/
theorem front {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E}
    (hDJ : ∀ s u A k R Q B Bb, WalkPre s → AtDeref OI s u A k R Q B Bb →
      ∃ t, Reaches Image.code u t ∧ ((∃ A k R Q B, AtR10 OI s t A k R Q B) ∨ Done OI s t ∨
        Dead Image.code t))
    (hBB : Bus.BusBalanceSpec BcOk bev) (hBW : BcWalk BcOk bev) :
    ∀ s, s.pc = 0x80000ef8 → WalkPre s → ∃ u, Reaches Image.code s u ∧
      ((∃ layout rows lir bus, AtR17 OI s u layout rows lir bus) ∨ Done OI s u ∨
        Dead Image.code u) := by
  intro s hpc hpre
  refine (frontHead hpc hpre).bind fun v ⟨hv, A, k, h⟩ ↦ ?_
  refine (frontKeccak hpre hv h).bind fun w ⟨hw, R, Q, B, h⟩ ↦ ?_
  refine (frontDeref hpre hw h).bind fun x ⟨Bb, h⟩ ↦ ?_
  refine Next.bind (hDJ s x A k R Q B Bb hpre h) fun y ⟨A, k, R, Q, B, h⟩ ↦ ?_
  refine (frontR13 hpre h).bind fun z ⟨hz, lo, lo2, lo3, G, BK, h⟩ ↦ ?_
  exact frontR17 hBB hBW hpre hz h

/-- `verify_bus_balance`'s contract, but for its side loop's entry and iteration and
`eq_kernel`'s contract as the bus states it (`Vbb.EqKernelSpec`). -/
theorem busBalance {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hEK : Bus.Vbb.EqKernelSpec)
    (hE : Proofs.Bus.VerifyBusBalance.SidesEntry BcOk bev)
    (hS : Proofs.Bus.VerifyBusBalance.SideStage bev) : Bus.BusBalanceSpec BcOk bev :=
  Proofs.Bus.VerifyBusBalance.verify_bus_balance_spec Layout.bus_layout_proved Transcript.samples
    hEK Transcript.duplex Transcript.nextScalar Runtime.alloc_spec
    (Proofs.Bus.gkrStage bev) (Proofs.Bus.vbbTailStage hE hS)

/-- `front` with `verify_bus_balance`'s contract down to its side loop's two open stages and
`eq_kernel`'s bus-side contract. -/
theorem frontV {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E}
    (hDJ : ∀ s u A k R Q B Bb, WalkPre s → AtDeref OI s u A k R Q B Bb →
      ∃ t, Reaches Image.code u t ∧ ((∃ A k R Q B, AtR10 OI s t A k R Q B) ∨ Done OI s t ∨
        Dead Image.code t))
    (hEK : Bus.Vbb.EqKernelSpec) (hE : Proofs.Bus.VerifyBusBalance.SidesEntry BcOk bev)
    (hS : Proofs.Bus.VerifyBusBalance.SideStage bev) (hBW : BcWalk BcOk bev) :
    ∀ s, s.pc = 0x80000ef8 → WalkPre s → ∃ u, Reaches Image.code s u ∧
      ((∃ layout rows lir bus, AtR17 OI s u layout rows lir bus) ∨ Done OI s u ∨
        Dead Image.code u) :=
  front hDJ (busBalance hEK hE hS) hBW

end Rv64Verifier.Proofs.Walk
