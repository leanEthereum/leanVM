/-
  Rv64mc.Proof.Layout.CountedT

  `Flushes::counted(&mut self, a, form, col, b)` is total over a `Flushes` of `Form`s (`PairFormT.FlushesFormT`):
  it moves `form` (`a2`, a `Form` header) into its frame, concatenates `a` (`a1`, two `Form`s), it and `b` (`a4`,
  `a5`, a slice of `Form`s) into `push` (`<[&[Form]]>::concat`, `ConcatFormT`), builds `col(col, 0)` (`ColAlT`) in
  the moved `form`'s slot, concatenates `a`, it and `b` into `pull`, and pushes both with `Flushes::pair`
  (`PairFormT`). The `Flushes` stays a `Flushes` of `Form`s, each vector one longer, each buffer the entry's or
  allocated since (`StateDerivedT.PostT`); it writes what `pair` writes (`PairT.OutT`) besides its stack and fresh
  blocks. A safety-only contract (class D).

  The precondition: `self` `PairT.FlushesT`, 8-byte aligned, a `Flushes` of `Form`s; `a` and `b` slices of `Form`s
  (`ConcatFormT.SliceFT`) at the stack pointer; `form` a `Form` (`FormReprT.FormT`) in a caller's frame
  (`StackObj`). `concat`'s result is a `Vec<Form>` whose whole footprint was allocated by the call
  (`ConcatFormT.PostT.foot`, `NewV`), so above both of `self`'s buffers, which lie below `NEXT` at the entry: both
  pushed vectors are held (`PairFormT.HeldT`, `held_of`).

  The body is cut at two points, after the first `concat` (instruction 68) and after the second (98), into three
  parts (`total`, `mid`, `fin`). `concat`'s precondition and postcondition (`CPre`, `CPost`) are sealed, and so is
  this function's own precondition (`PreS`), so that the executor's arithmetic does not unfold them.

  ## Main definitions

  * `PreT`, `SpecT`, `NewV`, `Slots`, `Saved`

  ## Main results

  * `SliceFT.keep`, `concat_pre`, `NewV.keep`, `held_of`, `total`
-/

import Rv64mc.Proof.Layout.ConcatFormT
import Rv64mc.Proof.Layout.StateDerivedT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.Counted

namespace Rv64mc.Proof.Layout.CountedT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (VecT)
open Rv64mc.Proof.Layout.FormReprT (FormT)
open Rv64mc.Proof.Layout.FromElemVecFormT (VecFormT)
open Rv64mc.Proof.Layout.ExtendTrustedT (InFoot VecFormT.keep')
open Rv64mc.Proof.Layout.PairT (FlushesT OutT)
open Rv64mc.Proof.Layout.PairFormT (lo hi HeldT FlushesFormT vecT_bufCap)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Layout.ConcatFormT (SliceFT keepM)
open Rv64mc.Gen.Verifier.Layout.Flushes.Counted (Link tmpl)

variable {env : Env}

/-- The total precondition: `self` (`a0`) `PairT.FlushesT`, aligned, a `Flushes` of `Form`s; `a` (`a1`, two
    `Form`s) and `b` (`a4`, `a5`) slices of `Form`s; `form` (`a2`) a `Form` in a caller's frame. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧ FlushesFormT env m (regs .x10) ∧
    SliceFT env m (regs .x2) (regs .x11) 2#64 ∧ StackObj (regs .x2) (regs .x12) 24 ∧ FormT env m (regs .x12) ∧
    SliceFT env m (regs .x2) (regs .x14) (regs .x15)

/-- **The total contract of `Flushes::counted`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (StateDerivedT.PostT env) OutT AbortStop

/-! ## Slices and fresh vectors -/

/-- **A slice stays a slice** in a memory the frame relates to the entry, for a stack pointer no higher. -/
theorem SliceFT.keep {m M : MachineState} {top top' q l : Word} (hs : SliceFT env m top q l)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hF : env.Frame top Tactic.F m M) (ht : top'.toNat ≤ top.toNat) :
    SliceFT env M top' q l := by
  by_cases hl : l.toNat = 0
  · exact .inl hl
  have hK := (ConcatFormT.src_keep hs hl (keepM hlim hF) hF.1).1
  rcases hs with h0 | ⟨hw, hq, -⟩
  · exact absurd h0 hl
  exact .inr ⟨hw, hq.imp (fun h => by have := hF.1; omega) (fun h => by omega), hK⟩

/-- **`concat`'s precondition** from its array's six words and its three slices, `sret` and the array in the
    caller's frame. -/
theorem concat_pre {M : MachineState} {sp s a q0 l0 q1 l1 q2 l2 : Word} {R : Reg → Word}
    (hs1 : env.stackLimit.toNat ≤ sp.toNat) (hsp : sp.toNat ≤ s.toNat) (hs2 : s.toNat + 24 ≤ 0xc0000000)
    (hsa : s.toNat % 8 = 0) (ha1 : sp.toNat ≤ a.toNat) (ha2 : a.toNat + 48 ≤ 0xc0000000) (haa : a.toNat % 8 = 0)
    (g0 : M.getMem a = q0) (g8 : M.getMem (a + 8#64) = l0) (g16 : M.getMem (a + 16#64) = q1)
    (g24 : M.getMem (a + 24#64) = l1) (g32 : M.getMem (a + 32#64) = q2) (g40 : M.getMem (a + 40#64) = l2)
    (s0 : SliceFT env M sp q0 l0) (s1 : SliceFT env M sp q1 l1) (s2 : SliceFT env M sp q2 l2)
    (r2 : R .x2 = sp) (r10 : R .x10 = s) (r11 : R .x11 = a) : ConcatFormT.PreT env R M := by
  unfold ConcatFormT.PreT SretPre
  rw [r2, r10, r11, g0, g8, g16, g24, g32, g40]
  exact ⟨⟨.inr hsp, by simp only [Layouts.Vec.byteSize]; omega⟩, .inr ⟨by omega, hs2⟩, hsa, ⟨.inr ha1, by omega⟩,
    .inr ⟨by omega, ha2⟩, haa, s0, s1, s2⟩

/-- **A `Vec<Form>` at `s` allocated between `m` and `M`**: its whole footprint there. -/
def NewV (env : Env) (m M : MachineState) (s : Word) : Prop :=
  VecFormT env M s ∧ ∀ b, InFoot M s b → (env.next m).toNat ≤ b.toNat ∧ b.toNat < (env.next M).toNat

/-- **A fresh `Vec<Form>` is kept** by a memory agreeing on its header and on what was allocated since `m`. -/
theorem NewV.keep {m M M' : MachineState} {s : Word} (h : NewV env m M s)
    (hn : (env.next M).toNat ≤ (env.next M').toNat)
    (hh : ∀ b : Word, s.toNat ≤ b.toNat → b.toNat < s.toNat + 24 → M'.getMem b = M.getMem b)
    (hf : ∀ x : Word, (env.next m).toNat ≤ x.toNat → x.toNat < (env.next M).toNat → M'.getMem x = M.getMem x) :
    NewV env m M' s := by
  obtain ⟨hv, hsub⟩ := VecFormT.keep' h.1 hn hh fun x hx => hf x (h.2 x hx).1 (h.2 x hx).2
  exact ⟨hv, fun b hb => ⟨(h.2 b (hsub b hb)).1, by have := (h.2 b (hsub b hb)).2; omega⟩⟩

/-- **A fresh `Vec<Form>` is held** by a `Flushes` whose buffers lie below `NEXT` at `m0`, before `m`. -/
theorem held_of {m0 m M : MachineState} {a s : Word} (h : NewV env m M s) (hV1 : VecT env m0 a 24)
    (hV2 : VecT env m0 (a + 24#64) 24) (hn : (env.next m0).toNat ≤ (env.next m).toNat)
    (hl : lo M a = lo m0 a ∧ hi M a = hi m0 a ∧ lo M (a + 24#64) = lo m0 (a + 24#64) ∧
      hi M (a + 24#64) = hi m0 (a + 24#64)) : HeldT env M a s := by
  have b1 := vecT_bufCap hV1
  have b2 := vecT_bufCap hV2
  obtain ⟨l1, h1, l2, h2⟩ := hl
  refine ⟨h.1, fun b hb => ?_, fun b hb => ?_⟩
  · have := (h.2 b hb).1
    rw [l1, h1]
    unfold lo hi
    rcases b1 with h0 | ⟨-, h5, -⟩
    · rw [h0]; omega
    · unfold Env.Live at h5; rw [Nat.mul_comm] at h5; omega
  · have := (h.2 b hb).1
    rw [l2, h2]
    unfold lo hi
    rcases b2 with h0 | ⟨-, h5, -⟩
    · rw [h0]; omega
    · unfold Env.Live at h5; rw [Nat.mul_comm] at h5; omega

/-! ## The body -/

/-- Reads through stores at other addresses, by `omega` over the context's facts about the addresses. -/
local macro "rd" : tactic => `(tactic| repeat (first
  | rw [MachineState.getMem_setMem_eq]
  | rw [MachineState.getMem_setMem_ne (fun h => by have h' := congrArg BitVec.toNat h; omega)]))

/-- `top - k` as a number, for the frame's offsets. -/
theorem tk {top c : Word} (k : Nat) (hc : c.toNat + k = 2 ^ 64) (hk : k ≤ top.toNat) :
    (top + c).toNat = top.toNat - k :=
  Runtime.CloneT.toNat_add_neg hc hk

/-- The saved words' region, from `top - 72` to `top`, as in `S`. -/
def SlotsAt (M S : MachineState) (top : Word) : Prop :=
  ∀ x : Word, top.toNat - 72 ≤ x.toNat → x.toNat < top.toNat → M.getMem x = S.getMem x

theorem SlotsAt.store {M S : MachineState} {top a v : Word} (h : SlotsAt M S top)
    (ha : a.toNat < top.toNat - 72 ∨ top.toNat ≤ a.toNat) : SlotsAt (M.setMem a v) S top := fun x l1 l2 => by
  rw [MachineState.getMem_setMem_ne (fun e => by have := congrArg BitVec.toNat e; omega)]
  exact h x l1 l2

/-- The precondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl

/-- `concat`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def CPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := ConcatFormT.PreT env regs m

/-- `concat`'s postcondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def CPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  ConcatFormT.PostT env regs m r' m'

theorem c_spec {p : Lprog (Op Reg) Reg} {i need : Nat} (h : ConcatFormT.SpecT env p i need) :
    HoldsT env p i need (CPre env) (CPost env) SretVecOut AbortStop := by
  unfold CPre CPost; exact h

/-- **`concat`'s precondition at either call**: `sret` at `s`, the array at `top - 144` holding `a`, the `Form` at
    `top - 96` and `b`, the frame since the entry. -/
theorem cpre {m M : MachineState} {top s : Word} {regs R : Reg → Word} (hP : PreT env regs m) (h2 : regs .x2 = top)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hs : top.toNat - 192 ≤ s.toNat) (hs' : s.toNat + 24 ≤ top.toNat) (hsa : s.toNat % 8 = 0)
    (hF : env.Frame top Tactic.F m M) (hf : FormT env M (top + 18446744073709551520#64))
    (g0 : M.getMem (top + 18446744073709551472#64) = regs .x11) (g8 : M.getMem (top + 18446744073709551480#64) = 2#64)
    (g16 : M.getMem (top + 18446744073709551488#64) = top + 18446744073709551520#64)
    (g24 : M.getMem (top + 18446744073709551496#64) = 1#64)
    (g32 : M.getMem (top + 18446744073709551504#64) = regs .x14)
    (g40 : M.getMem (top + 18446744073709551512#64) = regs .x15)
    (r2 : R .x2 = top + 18446744073709551424#64) (r10 : R .x10 = s) (r11 : R .x11 = top + 18446744073709551472#64) :
    ConcatFormT.PreT env R M := by
  have hlay := env.layout
  have htl := hW.top_le
  have e192 := tk (top := top) (c := 18446744073709551424#64) 192 rfl (by omega)
  have e144 := tk (top := top) (c := 18446744073709551472#64) 144 rfl (by omega)
  have e96 := tk (top := top) (c := 18446744073709551520#64) 96 rfl (by omega)
  obtain ⟨-, -, -, sa, -, -, sb⟩ := hP
  rw [h2] at sa sb
  have a8 : top + 18446744073709551472#64 + 8#64 = top + 18446744073709551480#64 := by rw [BitVec.add_assoc]; rfl
  have a16 : top + 18446744073709551472#64 + 16#64 = top + 18446744073709551488#64 := by rw [BitVec.add_assoc]; rfl
  have a24 : top + 18446744073709551472#64 + 24#64 = top + 18446744073709551496#64 := by rw [BitVec.add_assoc]; rfl
  have a32 : top + 18446744073709551472#64 + 32#64 = top + 18446744073709551504#64 := by rw [BitVec.add_assoc]; rfl
  have a40 : top + 18446744073709551472#64 + 40#64 = top + 18446744073709551512#64 := by rw [BitVec.add_assoc]; rfl
  have one : (1#64).toNat = 1 := rfl
  refine concat_pre (sp := top + 18446744073709551424#64) (s := s) (a := top + 18446744073709551472#64)
    (q0 := regs .x11) (l0 := 2#64) (q1 := top + 18446744073709551520#64) (l1 := 1#64)
    (q2 := regs .x14) (l2 := regs .x15) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    g0 (by rw [a8]; exact g8) (by rw [a16]; exact g16) (by rw [a24]; exact g24) (by rw [a32]; exact g32)
    (by rw [a40]; exact g40) (SliceFT.keep sa (by omega) hF (by omega))
    (.inr ⟨.inr ⟨by omega, by omega⟩, .inr (by omega), fun i hi => ?_⟩) (SliceFT.keep sb (by omega) hF (by omega)) r2
    r10 r11
  have hi' : i < 1 := hi
  obtain rfl : i = 0 := by omega
  have z : top + 18446744073709551520#64 + BitVec.ofNat 64 (24 * 0) = top + 18446744073709551520#64 :=
    BitVec.add_zero _
  rw [z]
  exact hf

/-- **The `Form` moved into the frame** at `top - 96` from `form` (`a2`): a `Form` again. -/
theorem fmove {m M : MachineState} {top : Word} {regs : Reg → Word} (hP : PreT env regs m)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m M) (f0 : M.getMem (top + 18446744073709551520#64) = m.getMem (regs .x12))
    (f8 : M.getMem (top + 18446744073709551528#64) = m.getMem (regs .x12 + 8#64))
    (f16 : M.getMem (top + 18446744073709551536#64) = m.getMem (regs .x12 + 16#64)) :
    FormT env M (top + 18446744073709551520#64) := by
  have hlay := env.layout
  have htl := hW.top_le
  have e96 := tk (top := top) (c := 18446744073709551520#64) 96 rfl (by omega)
  have hf := hP.2.2.2.2.2.1
  have d8 : top + 18446744073709551520#64 + 8#64 = top + 18446744073709551528#64 := by rw [BitVec.add_assoc]; rfl
  have d16 : top + 18446744073709551520#64 + 16#64 = top + 18446744073709551536#64 := by rw [BitVec.add_assoc]; rfl
  refine (StateDerivedT.FormT.move hf hF.1 (.inr ⟨by rw [e96]; omega, by rw [e96]; omega⟩) (by rw [e96]; omega) f0
    (by rw [d8]; exact f8) (by rw [d16]; exact f16) fun x l1 l2 => keepM (by omega) hF x (.inl ?_)).1
  rcases hf.foot with h0 | ⟨-, h3, -⟩ <;> omega

/-- **`concat`'s precondition at its first call**: `cpre`, the `Form` at `top - 96` moved there from `form`. -/
theorem cpre1 {m M : MachineState} {top : Word} {regs R : Reg → Word} (hP : PreT env regs m) (h2 : regs .x2 = top)
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m M)
    (f0 : M.getMem (top + 18446744073709551520#64) = m.getMem (regs .x12))
    (f8 : M.getMem (top + 18446744073709551528#64) = m.getMem (regs .x12 + 8#64))
    (f16 : M.getMem (top + 18446744073709551536#64) = m.getMem (regs .x12 + 16#64))
    (g0 : M.getMem (top + 18446744073709551472#64) = regs .x11) (g8 : M.getMem (top + 18446744073709551480#64) = 2#64)
    (g16 : M.getMem (top + 18446744073709551488#64) = top + 18446744073709551520#64)
    (g24 : M.getMem (top + 18446744073709551496#64) = 1#64)
    (g32 : M.getMem (top + 18446744073709551504#64) = regs .x14)
    (g40 : M.getMem (top + 18446744073709551512#64) = regs .x15)
    (r2 : R .x2 = top + 18446744073709551424#64) (r10 : R .x10 = top + 18446744073709551424#64)
    (r11 : R .x11 = top + 18446744073709551472#64) : ConcatFormT.PreT env R M := by
  have e192 := tk (top := top) (c := 18446744073709551424#64) 192 rfl (by omega)
  exact cpre hP h2 hW h16 hlim (by omega) (by omega) (by omega) hF (fmove hP hW h16 hlim hF f0 f8 f16) g0 g8 g16
    g24 g32 g40 r2 r10 r11

/-- The prologue's nine saved words in `M`. -/
def Slots (M : MachineState) (top ret : Word) (regs : Reg → Word) : Prop :=
  M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
    M.getMem (top + 18446744073709551576#64) = regs .x19 ∧ M.getMem (top + 18446744073709551568#64) = regs .x20 ∧
    M.getMem (top + 18446744073709551560#64) = regs .x21 ∧ M.getMem (top + 18446744073709551552#64) = regs .x22 ∧
    M.getMem (top + 18446744073709551544#64) = regs .x23

/-- The four saved registers the function does not save, the entry's. -/
def Saved (regs R : Reg → Word) : Prop :=
  R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27

/-- The registers the body keeps from the prologue on. -/
def Regs (top : Word) (regs R : Reg → Word) : Prop :=
  R .x2 = top + 18446744073709551424#64 ∧ R .x8 = regs .x15 ∧ R .x9 = regs .x14 ∧ R .x18 = regs .x13 ∧
    R .x19 = regs .x11 ∧ R .x20 = regs .x10 ∧ R .x21 = 2#64 ∧ R .x22 = top + 18446744073709551520#64 ∧
    R .x23 = 1#64 ∧ Saved regs R

/-- The prologue's nine saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)).setMem (top + 18446744073709551552#64) (regs .x22)).setMem
    (top + 18446744073709551544#64) (regs .x23)

/-- The stores before the first `concat`: `form`'s three words at `top - 96`, then the array of three slices at
    `top - 144`. -/
def chainA (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((((((saved m top ret regs).setMem (top + 18446744073709551520#64)
    ((saved m top ret regs).getMem (regs .x12))).setMem (top + 18446744073709551528#64)
    ((saved m top ret regs).getMem (regs .x12 + 8#64))).setMem (top + 18446744073709551536#64)
    ((saved m top ret regs).getMem (regs .x12 + 16#64))).setMem (top + 18446744073709551472#64) (regs .x11)).setMem
    (top + 18446744073709551480#64) 2#64).setMem (top + 18446744073709551488#64) (top + 18446744073709551520#64)).setMem
    (top + 18446744073709551496#64) 1#64).setMem (top + 18446744073709551504#64) (regs .x14)).setMem
    (top + 18446744073709551512#64) (regs .x15)

/-- The frame's offsets as numbers. -/
theorem offs {top : Word} (h : 192 ≤ top.toNat) :
    (top + 18446744073709551608#64).toNat = top.toNat - 8 ∧ (top + 18446744073709551600#64).toNat = top.toNat - 16 ∧
    (top + 18446744073709551592#64).toNat = top.toNat - 24 ∧ (top + 18446744073709551584#64).toNat = top.toNat - 32 ∧
    (top + 18446744073709551576#64).toNat = top.toNat - 40 ∧ (top + 18446744073709551568#64).toNat = top.toNat - 48 ∧
    (top + 18446744073709551560#64).toNat = top.toNat - 56 ∧ (top + 18446744073709551552#64).toNat = top.toNat - 64 ∧
    (top + 18446744073709551544#64).toNat = top.toNat - 72 ∧ (top + 18446744073709551536#64).toNat = top.toNat - 80 ∧
    (top + 18446744073709551528#64).toNat = top.toNat - 88 ∧ (top + 18446744073709551520#64).toNat = top.toNat - 96 ∧
    (top + 18446744073709551512#64).toNat = top.toNat - 104 ∧
    (top + 18446744073709551504#64).toNat = top.toNat - 112 ∧
    (top + 18446744073709551496#64).toNat = top.toNat - 120 ∧
    (top + 18446744073709551488#64).toNat = top.toNat - 128 ∧
    (top + 18446744073709551480#64).toNat = top.toNat - 136 ∧
    (top + 18446744073709551472#64).toNat = top.toNat - 144 ∧
    (top + 18446744073709551448#64).toNat = top.toNat - 168 ∧
    (top + 18446744073709551424#64).toNat = top.toNat - 192 :=
  ⟨tk 8 rfl (by omega), tk 16 rfl (by omega), tk 24 rfl (by omega), tk 32 rfl (by omega), tk 40 rfl (by omega),
    tk 48 rfl (by omega), tk 56 rfl (by omega), tk 64 rfl (by omega), tk 72 rfl (by omega), tk 80 rfl (by omega),
    tk 88 rfl (by omega), tk 96 rfl (by omega), tk 104 rfl (by omega), tk 112 rfl (by omega), tk 120 rfl (by omega),
    tk 128 rfl (by omega), tk 136 rfl (by omega), tk 144 rfl (by omega), tk 168 rfl (by omega),
    tk 192 rfl (by omega)⟩

/-- What the prologue's stores keep: everything outside the nine slots. -/
theorem saved_get {m : MachineState} {top ret x : Word} {regs : Reg → Word} (h192 : 192 ≤ top.toNat)
    (hx : x.toNat < top.toNat - 72 ∨ top.toNat ≤ x.toNat) : (saved m top ret regs).getMem x = m.getMem x := by
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64, e72, -⟩ := offs (top := top) h192
  unfold saved
  repeat rw [StateDerivedT.get_ne (by omega)]

/-- The stores before the first `concat`: the frame, the nine saved words, the code. -/
theorem chainA_ok {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    env.Frame top Tactic.F m (chainA m top ret regs) ∧ Slots (chainA m top ret regs) top ret regs ∧
      (chainA m top ret regs).code = m.code := by
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104, e112, e120, e128, e136, e144, -, -⟩ :=
    offs (top := top) (by omega)
  refine ⟨?_, ?_, by simp only [chainA, saved, MachineState.code_setMem]⟩
  · unfold chainA saved
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Tactic.frame_refl hnx)
  · unfold Slots
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals (unfold chainA; rd)
    all_goals (unfold saved; rd)

/-- **`concat`'s precondition at its first call** (template step 33), over the stores before it. -/
theorem pre_call1 {m : MachineState} {top ret : Word} {regs R : Reg → Word} (hP : PreT env regs m)
    (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (r2 : R .x2 = top + 18446744073709551424#64) (r10 : R .x10 = top + 18446744073709551424#64)
    (r11 : R .x11 = top + 18446744073709551472#64) : CPre env R (chainA m top ret regs) := by
  have hlay := env.layout
  have htl := hW.top_le
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104, e112, e120, e128, e136, e144, -, -⟩ :=
    offs (top := top) (by omega)
  have hw12 := hP.2.2.2.2.2.1.1.1
  have hso := hP.2.2.2.2.1
  unfold InWin at hw12
  unfold StackObj at hso
  rw [h2] at hso
  simp only [Layouts.Vec.byteSize] at hw12
  have x8 : (regs .x12 + 8#64).toNat = (regs .x12).toNat + 8 := toNat_add_ofNat (by omega)
  have x16 : (regs .x12 + 16#64).toNat = (regs .x12).toNat + 16 := toNat_add_ofNat (by omega)
  unfold CPre
  refine cpre1 hP h2 hW h16 hlim ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ r2 r10 r11
  · unfold chainA saved
    repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact Tactic.frame_refl hnx)
  all_goals (unfold chainA; rd)
  all_goals (rw [saved_get (by omega) (.inr (by omega))])

/-- The array stored again before the second `concat` (template steps 39 to 44). -/
def chainB (M : MachineState) (top : Word) (regs : Reg → Word) : MachineState :=
  (((((M.setMem (top + 18446744073709551472#64) (regs .x11)).setMem (top + 18446744073709551480#64) 2#64).setMem
    (top + 18446744073709551488#64) (top + 18446744073709551520#64)).setMem (top + 18446744073709551496#64) 1#64).setMem
    (top + 18446744073709551504#64) (regs .x14)).setMem (top + 18446744073709551512#64) (regs .x15)

theorem chainB_get {M : MachineState} {top x : Word} {regs : Reg → Word} (h192 : 192 ≤ top.toNat)
    (hx : x.toNat < top.toNat - 144 ∨ top.toNat - 96 ≤ x.toNat) : (chainB M top regs).getMem x = M.getMem x := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e104, e112, e120, e128, e136, e144, -, -⟩ := offs (top := top) h192
  unfold chainB
  repeat rw [StateDerivedT.get_ne (by omega)]

theorem chainB_frame {m M : MachineState} {top : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hF : env.Frame top Tactic.F m M) :
    env.Frame top Tactic.F m (chainB M top regs) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, e104, e112, e120, e128, e136, e144, -, -⟩ := offs (top := top) (by omega)
  unfold chainB
  repeat (first | refine Tactic.frame_slot ?_ (by omega) (by omega) | exact hF)

/-- **`concat`'s precondition at its second call** (template step 48), `col`'s `Form` at `top - 96`. -/
theorem pre_call2 {m M : MachineState} {top : Word} {regs R : Reg → Word} (hP : PreT env regs m)
    (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (hf : FormT env M (top + 18446744073709551520#64))
    (r2 : R .x2 = top + 18446744073709551424#64) (r10 : R .x10 = top + 18446744073709551448#64)
    (r11 : R .x11 = top + 18446744073709551472#64) : CPre env R (chainB M top regs) := by
  have hlay := env.layout
  have htl := hW.top_le
  have hna := hW.nextAddr_ge
  have hx := hF.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, e96, e104, e112, e120, e128, e136, e144, e168, -⟩ :=
    offs (top := top) (by omega)
  have hnB : env.next (chainB M top regs) = env.next M := chainB_get (by omega) (.inl (by omega))
  have hfB : FormT env (chainB M top regs) (top + 18446744073709551520#64) := by
    refine hf.keep (by rw [hnB]) (fun b l1 l2 => chainB_get (by omega) (.inr (by omega))) fun b l1 l2 => ?_
    refine chainB_get (by omega) (.inl ?_)
    rcases hf.foot with h0 | ⟨-, h3, -⟩ <;> omega
  unfold CPre
  refine cpre hP h2 hW h16 hlim (by omega) (by omega) (by omega) (chainB_frame hlim hF) hfB ?_ ?_ ?_ ?_ ?_ ?_ r2 r10
    r11
  all_goals (unfold chainB; rd)

/-- **Through a call** from `top - 192` that writes, on the stack, only below `top - 72`: the frame, the slots, the
    heap below `NEXT` and what lies from `top - 192` outside its `out`. -/
theorem thru {m M M' : MachineState} {top ret : Word} {regs : Reg → Word} {out : Word → Prop}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (hsl : Slots M top ret regs) (hFc : env.Frame (top + 18446744073709551424#64) out M M')
    (hout : ∀ x, out x → top.toNat - 192 ≤ x.toNat ∧ x.toNat < top.toNat - 72) :
    env.Frame top Tactic.F m M' ∧ Slots M' top ret regs ∧
      (∀ x : Word, x.toNat < (env.next M).toNat → M'.getMem x = M.getMem x) ∧
      (∀ x : Word, top.toNat - 192 ≤ x.toNat → ¬ out x → M'.getMem x = M.getMem x) := by
  have hlay := env.layout
  have htl := hW.top_le
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64, e72, -, -, -, -, -, -, -, -, -, -, e192⟩ :=
    offs (top := top) (by omega)
  have hx := hF.2.1
  have hx' := hFc.2.1
  have hi : ∀ x : Word, top.toNat - 192 ≤ x.toNat → ¬ out x → M'.getMem x = M.getMem x := fun x l1 ho =>
    hFc.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at l1; omega
      · exact ho hw
  have hs : ∀ x : Word, top.toNat - 72 ≤ x.toNat → x.toNat < top.toNat → M'.getMem x = M.getMem x :=
    fun x l1 l2 => hi x (by omega) fun ho => by have := hout x ho; omega
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hsl
  refine ⟨hF.trans hFc (by omega) fun x hx => .inl ⟨by have := hout x hx; omega, by have := hout x hx; omega⟩,
    ⟨by rw [hs _ (by omega) (by omega), t1], by rw [hs _ (by omega) (by omega), t2],
      by rw [hs _ (by omega) (by omega), t3], by rw [hs _ (by omega) (by omega), t4],
      by rw [hs _ (by omega) (by omega), t5], by rw [hs _ (by omega) (by omega), t6],
      by rw [hs _ (by omega) (by omega), t7], by rw [hs _ (by omega) (by omega), t8],
      by rw [hs _ (by omega) (by omega), t9]⟩, fun x hx => hFc.2.2 x fun hw => ?_, hi⟩
  rcases hw with hw | hw | hw | hw
  · omega
  · omega
  · rw [hw] at hx; omega
  · have := hout x hw; omega

/-- **`concat`'s result** is a fresh `Vec<Form>`. -/
theorem newV_of {m M M' : MachineState} {R r : Reg → Word} (h : CPost env R M r M')
    (hn : (env.next m).toNat ≤ (env.next M).toNat) : NewV env m M' (R .x10) := by
  unfold CPost at h
  exact ⟨h.1, fun b hb => by have := ConcatFormT.PostT.foot h b hb; omega⟩

/-- **`pair`'s precondition** (template step 53): `self` kept from the entry, `push` and `pull` the two fresh
    `Vec<Form>`s at `top - 192` and `top - 168`. -/
theorem pair_pre {m M : MachineState} {top : Word} {regs R' : Reg → Word} (hP : PreT env regs m)
    (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (v1 : NewV env m M (top + 18446744073709551424#64)) (v2 : NewV env m M (top + 18446744073709551448#64))
    (r2 : R' .x2 = top + 18446744073709551424#64) (r10 : R' .x10 = regs .x10)
    (r11 : R' .x11 = top + 18446744073709551424#64) (r12 : R' .x12 = top + 18446744073709551448#64) :
    PairFormT.PreT env R' M := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, hal, hFF, -⟩ := hP
  rw [h2] at ha1
  have hlay := env.layout
  have htl := hW.top_le
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e168, e192⟩ := offs (top := top) (by omega)
  have kM := keepM (by omega) hF
  obtain ⟨hFM, -⟩ := StateDerivedT.FlushesFormT.keep hFF hF.1 (fun b hb => kM b (.inl hb))
    (fun b h1 h2 => kM b (.inr (by omega)))
  have hl := StateDerivedT.lohi_eq (m := m) (M := M) (a := regs .x10) (by omega) fun b h1 h2 => kM b (.inr (by omega))
  unfold PairFormT.PreT PairT.PreT PairT.FlushesT
  rw [r2, r10, r11, r12]
  exact ⟨⟨⟨hFM.1, hFM.2.1, ⟨by omega, ha2⟩, hFM.2.2.1⟩, hal, ⟨by omega, by omega⟩, by omega, ⟨by omega, by omega⟩,
    by omega, .inr (by omega), .inr (by omega)⟩, hFM, held_of v1 hV1 hV2 (Nat.le_refl _) hl,
    held_of v2 hV1 hV2 (Nat.le_refl _) hl⟩

/-- **The return, from `pair`'s**: the saved words kept, the frame, the postcondition. -/
theorem fin_post {m M m1 : MachineState} {top ret : Word} {regs R' r1 : Reg → Word}
    (hP : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hlim : env.stackLimit.toNat + 192 ≤ top.toNat) (hF : env.Frame top Tactic.F m M) (hsl : Slots M top ret regs)
    (hFp : env.Frame (top + 18446744073709551424#64) (PairT.OutT R' M) M m1)
    (hPo : StateDerivedT.PPost env R' M r1 m1) (r10 : R' .x10 = regs .x10) :
    Slots m1 top ret regs ∧ env.Frame top (OutT regs m) m m1 ∧ ∀ r', StateDerivedT.PostT env regs m r' m1 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hP
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have hnM := hF.2.1
  have hmM := hF.1
  obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64, e72, -, -, -, -, -, -, -, -, -, -, e192⟩ :=
    offs (top := top) (by omega)
  have kC := keepM (by omega) hF
  obtain ⟨hout, slotLow, hpost⟩ := StateDerivedT.self_kept hV1 hV2 hmM (fun x hx _ => kC x (.inr (by omega))) r10
  have k1 : ∀ x : Word, top.toNat - 72 ≤ x.toNat → x.toNat < top.toNat → m1.getMem x = M.getMem x :=
    fun x l1 l2 => hFp.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · omega
      · have := hFp.2.1; omega
      · rw [hw] at l1; omega
      · rcases slotLow x (hout x hw) with h | h <;> omega
  have F2 : env.Frame top (OutT regs m) m m1 :=
    (Tactic.frame_weaken hF).trans hFp (by omega) fun b hb => .inr (.inr (.inr (hout b hb)))
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hsl
  refine ⟨⟨by rw [k1 _ (by omega) (by omega), t1], by rw [k1 _ (by omega) (by omega), t2],
    by rw [k1 _ (by omega) (by omega), t3], by rw [k1 _ (by omega) (by omega), t4],
    by rw [k1 _ (by omega) (by omega), t5], by rw [k1 _ (by omega) (by omega), t6],
    by rw [k1 _ (by omega) (by omega), t7], by rw [k1 _ (by omega) (by omega), t8],
    by rw [k1 _ (by omega) (by omega), t9]⟩, F2, fun r' => ?_⟩
  unfold StateDerivedT.PPost PairFormT.PostT PairT.PostT PairT.PostM at hPo
  obtain ⟨⟨-, hl1, hl2, -, -, hK1, hK2⟩, hFF1⟩ := hPo
  exact hpost r1 r' m1 ⟨hFF1, hl1, hl2, hK1, hK2⟩

set_option rv_sym.heap true in
/-- **From the second `concat`'s return** (instruction 98): `pair`, then the return. -/
theorem fin {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L)) (_hL : L.WF p)
    {needP : Nat}
    (hpair : HoldsT env p L.pair.idx needP (StateDerivedT.PPre env) (StateDerivedT.PPost env) PairT.OutT AbortStop)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', HoldsT.post env (StateDerivedT.PostT env) OutT ret top regs m r' m' →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨rest, r', m'⟩)
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + 192 + needP ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hP : True → PreT env regs m) :
    ∀ R M, Regs top regs R → Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      NewV env m M (top + 18446744073709551424#64) → NewV env m M (top + 18446744073709551448#64) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 98, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hcd v1 v2
  have hnM := hF.2.1
  rv_introT hR
  replace hsl : True → Slots M top ret regs := fun _ => hsl
  replace v1 : True → NewV env m M (top + 18446744073709551424#64) := fun _ => v1
  replace v2 : True → NewV env m M (top + 18446744073709551448#64) := fun _ => v2
  rv_symT hp with [_hL] using [hpair]
  · unfold StateDerivedT.PPre
    exact pair_pre (hP trivial) h2 hW h16 (by omega) hF (v1 trivial) (v2 trivial) rfl rfl rfl rfl
  all_goals
    obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩, F2, hPo⟩ :=
      fin_post (hP trivial) h2 hW (by omega) hF (hsl trivial) hret1_14 hret1_16 rfl
  · exact s1
  · exact ⟨⟨rfl, s2, s3, s4, s5, s6, s7, s8, s9, rfl, rfl, rfl, rfl⟩, F2, hret1_15, hPo _⟩

set_option rv_sym.heap true in
/-- **From the first `concat`'s return** (instruction 68): `col`, the array again, the second `concat`. -/
theorem mid {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link} (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needL : Nat} (hnC : 192 + needC ≤ need) (hnL : 192 + needL ≤ need)
    (hc' : HoldsT env p L.concat.idx needC (CPre env) (CPost env) SretVecOut AbortStop)
    (hcol : ColAlT.colSpecT env p L.col.idx needL)
    {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hstop : ∀ fr st r' m', AbortStop regs m r' m' → rvIsa.accept p stmtCtx ⟨fr :: st, r', m'⟩ →
      Q ⟨fr :: st, r', m'⟩)
    (hneed : env.stackLimit.toNat + need ≤ top.toNat) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (h2 : regs .x2 = top) (hP : True → PreT env regs m)
    (hfin : ∀ R M, Regs top regs R → Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M →
      M.code = m.code → NewV env m M (top + 18446744073709551424#64) →
      NewV env m M (top + 18446744073709551448#64) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 98, ret, top⟩ :: rest, R, M⟩) :
    ∀ R M, Regs top regs R → Slots M top ret regs → env.Frame top Tactic.F m M → env.Static M → M.code = m.code →
      NewV env m M (top + 18446744073709551424#64) →
      rvIsa.Total p stmtCtx (WinOk p) Q ⟨⟨i, 68, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hR hsl hF hS hcd hV1
  have hlay := env.layout
  have htl := hW.top_le
  have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
  replace hsl : True → Slots M top ret regs := fun _ => hsl
  replace hV1 : True → NewV env m M (top + 18446744073709551424#64) := fun _ => hV1
  rv_introT hR
  rv_symT hp stop [98] with [hL, hnC, hnL] using [hcol, hc']
  all_goals
    obtain ⟨e8, e16, e24, e32, e40, e48, e56, e64, e72, e80, e88, e96, e104, e112, e120, e128, e136, e144, e168,
      e192⟩ := offs (top := top) (by omega)
    obtain ⟨hF1, hsl1, kb1, ka1⟩ := thru hW hlim hF (hsl trivial) hret1_14 fun x hx => by
      unfold Spec.Layout.Term.Out InRange at hx
      simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Form.byteSize] at hx
      omega
  · have hf1 : FormT env m1 (top + 18446744073709551520#64) :=
      TermAlT.formT_of hret1_16 ⟨hret1_17, hret1_18⟩ (by have := hW.next_ge; have := hF.1; omega) (Nat.le_refl _)
        hret1_14.2.1 hW.heapEnd_le (.inr ⟨by omega, by omega⟩) (by omega)
    refine pre_call2 (hP trivial) h2 hW h16 hlim hF1 hf1 ?_ ?_ ?_ <;> rfl
  · have hnB : env.next (chainB m1 top regs) = env.next m1 := chainB_get (by omega) (.inl (by
      have := hW.nextAddr_ge; omega))
    have hFB := chainB_frame (regs := regs) hlim hF1
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hsl1
    have hslB : Slots (chainB m1 top regs) top ret regs :=
      ⟨by rw [chainB_get (by omega) (.inr (by omega)), t1], by rw [chainB_get (by omega) (.inr (by omega)), t2],
        by rw [chainB_get (by omega) (.inr (by omega)), t3], by rw [chainB_get (by omega) (.inr (by omega)), t4],
        by rw [chainB_get (by omega) (.inr (by omega)), t5], by rw [chainB_get (by omega) (.inr (by omega)), t6],
        by rw [chainB_get (by omega) (.inr (by omega)), t7], by rw [chainB_get (by omega) (.inr (by omega)), t8],
        by rw [chainB_get (by omega) (.inr (by omega)), t9]⟩
    obtain ⟨hF2, hsl2, kb2, ka2⟩ := thru (M := chainB m1 top regs) hW hlim hFB hslB hret2_14 fun x hx => by
      unfold SretVecOut InRange at hx
      simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Vec.byteSize] at hx
      omega
    have hx1 := hret1_14.2.1
    have v1 : NewV env m m2 (top + 18446744073709551424#64) := by
      have w1 := (hV1 trivial).keep hret1_14.1 (fun b l1 l2 => ka1 b (by omega) fun hb => by
        unfold Spec.Layout.Term.Out InRange at hb
        simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Form.byteSize] at hb
        omega) fun x l1 l2 => kb1 x l2
      have w2 := w1.keep (M' := chainB m1 top regs) (by rw [hnB]) (fun b l1 l2 => chainB_get (by omega)
        (.inl (by omega))) fun x l1 l2 => chainB_get (by omega) (.inl (by omega))
      exact w2.keep hret2_14.1 (fun b l1 l2 => ka2 b (by omega) fun hb => by
        unfold SretVecOut InRange at hb
        simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Vec.byteSize] at hb
        omega) fun x l1 l2 => kb2 x l2
    have v2 := newV_of (m := m) hret2_16 (by
      have := hF.1; have := hret1_14.1; have h' := hnB; unfold chainB at h'; rw [h']; omega)
    exact hfin _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl2 hF2 hret2_15
      (by rw [hret2_17]; simp only [MachineState.code_setMem]; rw [hret1_19, hcd]) v1 v2

set_option rv_sym.heap true in
/-- **`Flushes::counted` is total**, with 192 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needL needP : Nat} (hnC : 192 + needC ≤ need) (hnL : 192 + needL ≤ need) (hnP : 192 + needP ≤ need)
    (hcat : ConcatFormT.SpecT env p L.concat.idx needC) (hcol : ColAlT.colSpecT env p L.col.idx needL)
    (hpr : PairFormT.SpecT env p L.pair.idx needP) : SpecT env p i need := by
  have hc' := c_spec hcat
  suffices h : HoldsT env p i need (PreS env) (StateDerivedT.PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp stop [68] with [hL, hnC, hnL, hnP] using [hc']
  all_goals
    have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 192 ≤ top.toNat := by omega
    have hw12 := hP.2.2.2.2.2.1.1.1
    have ha12 := hP.2.2.2.2.2.1.1.2.1.2.1
    have hso := hP.2.2.2.2.1
    unfold InWin at hw12
    unfold StackObj at hso
    rw [hpre_2] at hso
    simp only [Layouts.Vec.byteSize] at hw12
    have hE := hpre_8.heapEnd_le
    have htl := hpre_8.top_le
    have hna := hpre_8.nextAddr_ge
    have x8 : (regs .x12 + 8#64).toNat = (regs .x12).toNat + 8 := toNat_add_ofNat (by omega)
    have x16 : (regs .x12 + 16#64).toNat = (regs .x12).toNat + 16 := toNat_add_ofNat (by omega)
  all_goals try (rw [inWindow_iff]; omega)
  all_goals try omega
  · refine pre_call1 (ret := ret) hP hpre_2 hpre_8 hpre_7 hlim hpre_5 ?_ ?_ ?_
    all_goals rfl
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, e192⟩ := offs (top := top) (by omega)
    obtain ⟨hFA, hslA, hcA⟩ := chainA_ok (ret := ret) (regs := regs) hlim hpre_5
    obtain ⟨hF1, hsl1, -, -⟩ := thru (M := chainA m top ret regs) hpre_8 hlim hFA hslA hret1_14 fun x hx => by
      unfold SretVecOut InRange at hx
      simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Vec.byteSize] at hx
      omega
    have v1 := newV_of (m := m) hret1_16 hFA.1
    have hpair' : HoldsT env p L.pair.idx needP (StateDerivedT.PPre env) (StateDerivedT.PPost env) PairT.OutT
        AbortStop := by
      unfold StateDerivedT.PPre StateDerivedT.PPost; exact hpr
    have hfin := fin hp hL hpair' hk hstop (by omega) hpre_8 hpre_7 hpre_2 (fun _ => hP)
    exact mid hp hL hnC hnL hc' hcol hstop hpre_3 hpre_8 hpre_7 hpre_2 (fun _ => hP) hfin _ _
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hsl1 hF1 hret1_15 (hret1_17.trans hcA) v1

end Rv64mc.Proof.Layout.CountedT

/-- info: 'Rv64mc.Proof.Layout.CountedT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.CountedT.total
