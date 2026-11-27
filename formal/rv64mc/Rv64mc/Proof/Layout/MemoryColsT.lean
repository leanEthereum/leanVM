/-
  Rv64mc.Proof.Layout.MemoryColsT

  `Flushes::memory_cols(&mut self, address, count, columns)` is total over a `Flushes` of `Form`s
  (`PairFormT.FlushesFormT`): it builds the two limbs' `Form`s in its frame, `col(columns[0], 0)` and either
  `col(columns[1], 0)` (when `columns` has two entries) or `constant(ZERO)` (`ColAlT`, `ConstantAlT`; `map_or`'s
  default `constant(ZERO)` is built eagerly for each limb), moves them into an array at `sp`, and calls
  `Flushes::memory(self, address, count, &values)` (`MemoryT`). The `Flushes` stays a `Flushes` of `Form`s
  (`StateDerivedT.PostT`, `memory`'s); it writes what `pair` writes (`PairT.OutT`) besides its stack and fresh
  blocks. A safety-only contract (class D).

  The precondition is `MemoryT.PreT`'s for `self` and `address`, and for `columns` (`a3`, `a4`) at least one entry
  (the compiled function reads `columns[0]` without a check), its words in a window and aligned. The array's two
  `Form`s are the limbs' moved headers (`StateDerivedT.FormT.move`), their terms' blocks allocated by `col` or
  `constant` and kept since (`fin_pre`). The two branches end in the store chains `finA` (two columns) and `finB`
  (one column) before `memory`'s call; `memory`'s precondition and postcondition (`MPre`, `MPost`) and this
  function's own precondition (`PreS`) are sealed.

  ## Main definitions

  * `PreT`, `SpecT`, `saved`, `SlotsAt`, `pre1`, `finA`, `finB`

  ## Main results

  * `at2`, `at3`, `at6`, `fin_pre`, `finA_ok`, `finB_ok`, `post`, `total`
-/

import Rv64mc.Proof.Layout.MemoryIfT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.MemoryCols

namespace Rv64mc.Proof.Layout.MemoryColsT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Layout.FormReprT (FormT)
open Rv64mc.Proof.Layout.PairT (FlushesT OutT)
open Rv64mc.Proof.Layout.PairFormT (FlushesFormT)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Layout.StateDerivedT (get_ne top_sub fkeep)
open Rv64mc.Gen.Verifier.Layout.Flushes.MemoryCols (Link tmpl)

variable {env : Env}

/-- The total precondition: `self` (`a0`) `PairT.FlushesT`, aligned, a `Flushes` of `Form`s; `address` (`a1`) a
    `Form` in a caller's frame; `columns` (`a3`, `a4`) at least one word, its words in a window and aligned. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧ FlushesFormT env m (regs .x10) ∧
    StackObj (regs .x2) (regs .x11) 24 ∧ FormT env m (regs .x11) ∧
    1 ≤ (regs .x14).toNat ∧ inWindow (regs .x13) (8 * (regs .x14).toNat) = true ∧ (regs .x13).toNat % 8 = 0

/-- **The total contract of `Flushes::memory_cols`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (StateDerivedT.PostT env) OutT AbortStop

/-- The precondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl

/-- `memory`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def MPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := MemoryT.PreT env regs m

/-- `memory`'s postcondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def MPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  StateDerivedT.PostT env regs m r' m'

/-! ## The frame and the saved words -/

/-- The prologue's seven saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)).setMem
    (top + 18446744073709551560#64) (regs .x21)

/-- The prologue's stores keep the frame. -/
theorem saved_frame {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat + 208 ≤ top.toNat) :
    env.Frame top Tactic.F m (saved m top ret regs) := by
  have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  exact Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
    (Tactic.frame_store (Tactic.frame_store (Tactic.frame_refl hnx) (by omega) (by omega)) (by omega) (by omega))
    (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)

/-- The saved words' region, from `top - 56` to `top`, as in `S`. -/
def SlotsAt (M S : MachineState) (top : Word) : Prop :=
  ∀ x : Word, top.toNat - 56 ≤ x.toNat → x.toNat < top.toNat → M.getMem x = S.getMem x

/-- A call from `top - 208` writing below `top - 56` keeps the saved words. -/
theorem SlotsAt.thru {M M' S : MachineState} {top : Word} {out : Word → Prop} (h : SlotsAt M S top)
    (hF : env.Frame (top + 18446744073709551408#64) out M M') (hlim : env.stackLimit.toNat + 208 ≤ top.toNat)
    (ho : ∀ x : Word, out x → x.toNat < top.toNat - 56) : SlotsAt M' S top := fun x l1 l2 => by
  have hlay := env.layout
  have := hF.2.1
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  rw [fkeep (x := x) hF (.inr (by omega)) (.inr (by omega)) (fun e => by rw [e] at l1; omega)
    fun h => by have := ho x h; omega]
  exact h x l1 l2

/-- **The saved words at the return.** -/
theorem saved_read {m M : MachineState} {top ret : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 208 ≤ top.toNat) (hS : SlotsAt M (saved m top ret regs) top) :
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
      M.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M.getMem (top + 18446744073709551584#64) = regs .x18 ∧
      M.getMem (top + 18446744073709551576#64) = regs .x19 ∧
      M.getMem (top + 18446744073709551568#64) = regs .x20 ∧ M.getMem (top + 18446744073709551560#64) = regs .x21 := by
  have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [hS _ (by omega) (by omega)]; unfold saved; repeat rw [get_ne (by omega)]
    rw [MachineState.getMem_setMem_eq]

/-- `Form::term`'s result slot `top + c` as `[top - k, top - k + 24)`. -/
theorem out_of {R : Reg → Word} {M : MachineState} {top c : Word} {k : Nat} (hc : c.toNat + k = 2 ^ 64)
    (hk : k ≤ top.toNat) (r : R .x10 = top + c) :
    ∀ x : Word, Spec.Layout.Term.Out R M x → top.toNat - k ≤ x.toNat ∧ x.toNat < top.toNat - k + 24 := fun x hx => by
  have := top_sub (top := top) hc hk
  unfold Spec.Layout.Term.Out InRange at hx; rw [r] at hx; simp only [Layouts.Form.byteSize] at hx; omega

/-! ## The body, call by call -/

/-- **Up to `col(columns[0], 0)`**: `constant(ZERO)` at `top - 208`, then `col` at `top - 80`, a `Form`. -/
theorem at2 {m S m1 m2 : MachineState} {top : Word} {R1 R2 : Reg → Word} {f2 : LeanVM.Protocol.Verifier.Form}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 208 ≤ top.toNat)
    (hF0 : env.Frame top Tactic.F m S)
    (d1 : env.Frame (top + 18446744073709551408#64) (Spec.Layout.Term.Out R1 S) S m1)
    (r1 : R1 .x10 = top + 18446744073709551408#64)
    (d2 : env.Frame (top + 18446744073709551408#64) (Spec.Layout.Term.Out R2 m1) m1 m2)
    (e2 : FormIn (env.next m1) (env.next m2) m2 (top + 18446744073709551536#64) f2)
    (a2 : TermAlT.FormAl m2 (top + 18446744073709551536#64)) (r2 : R2 .x10 = top + 18446744073709551536#64) :
    env.Frame top Tactic.F m m2 ∧ SlotsAt m2 S top ∧ FormT env m2 (top + 18446744073709551536#64) := by
  have hlay := env.layout
  have htl := hW.top_le
  have hE := hW.heapEnd_le
  have hge := hW.next_ge
  have t80 := top_sub (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  have o1 := out_of (M := S) (k := 208) rfl (by omega) r1
  have o2 := out_of (M := m1) (k := 80) rfl (by omega) r2
  have F1 : env.Frame top Tactic.F m m1 := hF0.trans d1 (by omega) fun x hx => .inl (by have := o1 x hx; omega)
  have F2 : env.Frame top Tactic.F m m2 := F1.trans d2 (by omega) fun x hx => .inl (by have := o2 x hx; omega)
  have hS : SlotsAt S S top := fun _ _ _ => rfl
  have S2 := (hS.thru d1 hlim fun x hx => by have := o1 x hx; omega).thru d2 hlim fun x hx => by
    have := o2 x hx; omega
  have n1 := F1.1
  exact ⟨F2, S2, TermAlT.formT_of e2 a2 (by omega) (Nat.le_refl _) d2.2.1 hE (.inr ⟨by omega, by omega⟩)
    (by omega)⟩

/-- The copies of `col`'s header after its call: to `top - 120`, `top - 136`, `top - 96`, `top - 88`, `top - 160`,
    `top - 152`. -/
def pre1 (M : MachineState) (top : Word) : MachineState :=
  (((((M.setMem (top + 18446744073709551496#64) (M.getMem (top + 18446744073709551544#64))).setMem
    (top + 18446744073709551480#64) (M.getMem (top + 18446744073709551544#64))).setMem
    (top + 18446744073709551520#64) (M.getMem (top + 18446744073709551536#64))).setMem
    (top + 18446744073709551528#64) (M.getMem (top + 18446744073709551544#64))).setMem
    (top + 18446744073709551456#64) (M.getMem (top + 18446744073709551536#64))).setMem
    (top + 18446744073709551464#64) (M.getMem (top + 18446744073709551544#64))

/-- Reads past `pre1`'s stores, and its frame. -/
theorem pre1_ok {m M : MachineState} {top : Word} (hlim : env.stackLimit.toNat + 208 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m M) :
    (∀ x : Word, x.toNat < top.toNat - 160 ∨ top.toNat - 80 ≤ x.toNat → (pre1 M top).getMem x = M.getMem x) ∧
      env.Frame top Tactic.F m (pre1 M top) := by
  have t120 := top_sub (top := top) (c := 18446744073709551496#64) (k := 120) rfl (by omega)
  have t136 := top_sub (top := top) (c := 18446744073709551480#64) (k := 136) rfl (by omega)
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t160 := top_sub (top := top) (c := 18446744073709551456#64) (k := 160) rfl (by omega)
  have t152 := top_sub (top := top) (c := 18446744073709551464#64) (k := 152) rfl (by omega)
  refine ⟨fun x hx => ?_, ?_⟩
  · unfold pre1; repeat rw [get_ne (by omega)]
  · exact Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_store hF (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega)
      (by omega)) (by omega) (by omega)) (by omega) (by omega)

/-- **The second limb's default**: `pre1`'s stores, then `constant(ZERO)` at `top - 208`, a `Form`; what lies below
    `NEXT` after `col` kept. -/
theorem at3 {m S m2 m3 : MachineState} {top : Word} {R3 : Reg → Word} {f3 : LeanVM.Protocol.Verifier.Form}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 208 ≤ top.toNat)
    (hF2 : env.Frame top Tactic.F m m2) (hS2 : SlotsAt m2 S top)
    (d3 : env.Frame (top + 18446744073709551408#64) (Spec.Layout.Term.Out R3 (pre1 m2 top)) (pre1 m2 top) m3)
    (r3 : R3 .x10 = top + 18446744073709551408#64)
    (e3 : FormIn (env.next m2) (env.next m3) m3 (top + 18446744073709551408#64) f3)
    (a3 : TermAlT.FormAl m3 (top + 18446744073709551408#64)) :
    env.Frame top Tactic.F m m3 ∧ SlotsAt m3 S top ∧ FormT env m3 (top + 18446744073709551408#64) ∧
      (env.next m2).toNat ≤ (env.next m3).toNat ∧
      ∀ x : Word, x.toNat < (env.next m2).toNat → m3.getMem x = m2.getMem x := by
  have hlay := env.layout
  have htl := hW.top_le
  have hE := hW.heapEnd_le
  have hge := hW.next_ge
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  obtain ⟨g1, F1⟩ := pre1_ok (M := m2) hlim hF2
  have o3 := out_of (M := pre1 m2 top) (k := 208) rfl (by omega) r3
  have n2 := hF2.1
  have x2 := hF2.2.1
  have hn1 : env.next (pre1 m2 top) = env.next m2 := g1 _ (.inl (by omega))
  have F3 : env.Frame top Tactic.F m m3 := F1.trans d3 (by omega) fun x hx => .inl (by have := o3 x hx; omega)
  have S1 : SlotsAt (pre1 m2 top) S top := fun x l1 l2 => by rw [g1 x (.inr (by omega))]; exact hS2 x l1 l2
  have n3 := d3.1
  rw [hn1] at n3
  refine ⟨F3, S1.thru d3 hlim fun x hx => by have := o3 x hx; omega,
    TermAlT.formT_of e3 a3 (by omega) (Nat.le_refl _) d3.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega), n3,
    fun x hx => ?_⟩
  rw [fkeep (x := x) d3 (.inl (by omega)) (.inl (by rw [hn1]; exact hx)) (fun e => by rw [e] at hx; omega)
    fun h => by have := o3 x h; omega]
  exact g1 x (.inl (by omega))

/-- **The second limb from `columns[1]`**: `col` at `top - 80` after `at3`'s state. -/
theorem at6 {m S m2 m5 m6 : MachineState} {top : Word} {R6 : Reg → Word} {f6 : LeanVM.Protocol.Verifier.Form}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 208 ≤ top.toNat)
    (hF5 : env.Frame top Tactic.F m m5) (hS5 : SlotsAt m5 S top) (n25 : (env.next m2).toNat ≤ (env.next m5).toNat)
    (k52 : ∀ x : Word, x.toNat < (env.next m2).toNat → m5.getMem x = m2.getMem x)
    (d6 : env.Frame (top + 18446744073709551408#64) (Spec.Layout.Term.Out R6 m5) m5 m6)
    (r6 : R6 .x10 = top + 18446744073709551536#64)
    (e6 : FormIn (env.next m5) (env.next m6) m6 (top + 18446744073709551536#64) f6)
    (a6 : TermAlT.FormAl m6 (top + 18446744073709551536#64)) :
    env.Frame top Tactic.F m m6 ∧ SlotsAt m6 S top ∧ FormT env m6 (top + 18446744073709551536#64) ∧
      (env.next m2).toNat ≤ (env.next m6).toNat ∧
      ∀ x : Word, x.toNat < (env.next m2).toNat → m6.getMem x = m2.getMem x := by
  have hlay := env.layout
  have htl := hW.top_le
  have hE := hW.heapEnd_le
  have hge := hW.next_ge
  have t80 := top_sub (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  have o6 := out_of (M := m5) (k := 80) rfl (by omega) r6
  have n5 := hF5.1
  have x5 := hF5.2.1
  have n6 := d6.1
  refine ⟨hF5.trans d6 (by omega) fun x hx => .inl (by have := o6 x hx; omega),
    hS5.thru d6 hlim fun x hx => by have := o6 x hx; omega,
    TermAlT.formT_of e6 a6 (by omega) (Nat.le_refl _) d6.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega),
    by omega, fun x hx => ?_⟩
  rw [fkeep (x := x) d6 (.inl (by omega)) (.inl (by omega)) (fun e => by rw [e] at hx; omega)
    fun h => by have := o6 x h; omega]
  exact k52 x hx

/-! ## The array and `memory`'s call -/

/-- **`memory`'s precondition at its call**: the array at `top - 208` holds the first limb's header (from `M2`'s
    `top - 80`) and the second's (from `Ms`'s `s`), both `Form`s whose terms' blocks `M` keeps. -/
theorem fin_pre {m M2 Ms M : MachineState} {top s : Word} {regs R : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hlim : env.stackLimit.toNat + 208 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (G0 : FormT env M2 (top + 18446744073709551536#64)) (n2 : (env.next M2).toNat ≤ (env.next M).toNat)
    (k2 : ∀ x : Word, x.toNat < (env.next M2).toNat → M.getMem x = M2.getMem x)
    (a0 : M.getMem (top + 18446744073709551408#64) = M2.getMem (top + 18446744073709551536#64))
    (a8 : M.getMem (top + 18446744073709551416#64) = M2.getMem (top + 18446744073709551544#64))
    (a16 : M.getMem (top + 18446744073709551424#64) = M2.getMem (top + 18446744073709551552#64))
    (G1 : FormT env Ms s) (ns : (env.next Ms).toNat ≤ (env.next M).toNat)
    (ks : ∀ x : Word, x.toNat < (env.next Ms).toNat → M.getMem x = Ms.getMem x)
    (b0 : M.getMem (top + 18446744073709551432#64) = Ms.getMem s)
    (b8 : M.getMem (top + 18446744073709551440#64) = Ms.getMem (s + 8#64))
    (b16 : M.getMem (top + 18446744073709551448#64) = Ms.getMem (s + 16#64))
    (s2 : R .x2 = top + 18446744073709551408#64) (s10 : R .x10 = regs .x10) (s11 : R .x11 = regs .x11)
    (s13 : R .x13 = top + 18446744073709551408#64) : MemoryT.PreT env R M := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, hBA⟩, hal, hFF, ⟨ho1, ho2⟩, hfa, -⟩ := hpre
  rw [h2] at ha1 ho1
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  have t184 := top_sub (top := top) (c := 18446744073709551432#64) (k := 184) rfl (by omega)
  have nM := hF.1
  have xM := hF.2.1
  have k0 : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x :=
    fun x hx => hF.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at hx; omega
      · exact hw
  obtain ⟨hFF2, -⟩ := StateDerivedT.FlushesFormT.keep hFF nM (fun b hb => k0 b (.inl hb))
    fun b h1 h2 => k0 b (.inr (by omega))
  have hb := hfa.foot
  have hfa' : FormT env M (regs .x11) := FormReprT.FormT.keep hfa nM (fun x l1 l2 => k0 x (.inr (by omega)))
    fun x l1 l2 => k0 x (.inl (by rcases hb with h | ⟨-, h, -⟩ <;> omega))
  have hb0 := G0.foot
  obtain ⟨V0, -, -⟩ := StateDerivedT.FormT.move (d := top + 18446744073709551408#64) G0 n2
    (.inr ⟨by omega, by omega⟩) (by omega) a0
    (by rw [StateDerivedT.add_add (d := 18446744073709551416#64) rfl, a8,
      StateDerivedT.add_add (d := 18446744073709551544#64) rfl])
    (by rw [StateDerivedT.add_add (d := 18446744073709551424#64) rfl, a16,
      StateDerivedT.add_add (d := 18446744073709551552#64) rfl])
    fun x l1 l2 => k2 x (by rcases hb0 with h | ⟨-, h, -⟩ <;> omega)
  have hb1 := G1.foot
  obtain ⟨V1, -, -⟩ := StateDerivedT.FormT.move (d := top + 18446744073709551432#64) G1 ns
    (.inr ⟨by omega, by omega⟩) (by omega) b0
    (by rw [StateDerivedT.add_add (d := 18446744073709551440#64) rfl, b8])
    (by rw [StateDerivedT.add_add (d := 18446744073709551448#64) rfl, b16])
    fun x l1 l2 => ks x (by rcases hb1 with h | ⟨-, h, -⟩ <;> omega)
  have two : (2#64).toNat = 2 := rfl
  unfold MemoryT.PreT PairT.FlushesT
  rw [s2, s10, s11, s13]
  refine ⟨⟨hFF2.1, hFF2.2.1, ⟨by omega, ha2⟩, hFF2.2.2.1⟩, hal, hFF2, ⟨by omega, ho2⟩, hfa',
    .inr ⟨by rw [two]; exact .inr ⟨by omega, by omega⟩, .inr (Nat.le_refl _), fun i hi => ?_⟩⟩
  rw [two] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa using V0
  · rw [StateDerivedT.add_add (d := 18446744073709551432#64) rfl]; exact V1

/-- The stores before `memory`'s call when `columns` has two entries: the second limb's header at `top - 96`,
    `top - 88`, `top - 112`, then the array at `top - 208`. -/
def finA (M6 M2 : MachineState) (top : Word) : MachineState :=
  ((((((((M6.setMem (top + 18446744073709551520#64) (M6.getMem (top + 18446744073709551536#64))).setMem
    (top + 18446744073709551528#64) (M6.getMem (top + 18446744073709551544#64))).setMem
    (top + 18446744073709551504#64) (M6.getMem (top + 18446744073709551536#64))).setMem
    (top + 18446744073709551408#64) (M2.getMem (top + 18446744073709551536#64))).setMem
    (top + 18446744073709551416#64) (M2.getMem (top + 18446744073709551544#64))).setMem
    (top + 18446744073709551424#64) (M2.getMem (top + 18446744073709551552#64))).setMem
    (top + 18446744073709551432#64) (M6.getMem (top + 18446744073709551536#64))).setMem
    (top + 18446744073709551440#64) (M6.getMem (top + 18446744073709551544#64))).setMem
    (top + 18446744073709551448#64) (M6.getMem (top + 18446744073709551552#64))

/-- The stores before `memory`'s call when `columns` has one entry: `constant(ZERO)`'s header copied to `top - 80`
    and on as in `finA`. -/
def finB (M3 M2 : MachineState) (top : Word) : MachineState :=
  (((((((((((M3.setMem (top + 18446744073709551536#64) (M3.getMem (top + 18446744073709551408#64))).setMem
    (top + 18446744073709551544#64) (M3.getMem (top + 18446744073709551416#64))).setMem
    (top + 18446744073709551552#64) (M3.getMem (top + 18446744073709551424#64))).setMem
    (top + 18446744073709551520#64) (M3.getMem (top + 18446744073709551408#64))).setMem
    (top + 18446744073709551528#64) (M3.getMem (top + 18446744073709551416#64))).setMem
    (top + 18446744073709551504#64) (M3.getMem (top + 18446744073709551408#64))).setMem
    (top + 18446744073709551408#64) (M2.getMem (top + 18446744073709551536#64))).setMem
    (top + 18446744073709551416#64) (M2.getMem (top + 18446744073709551544#64))).setMem
    (top + 18446744073709551424#64) (M2.getMem (top + 18446744073709551552#64))).setMem
    (top + 18446744073709551432#64) (M3.getMem (top + 18446744073709551408#64))).setMem
    (top + 18446744073709551440#64) (M3.getMem (top + 18446744073709551416#64))).setMem
    (top + 18446744073709551448#64) (M3.getMem (top + 18446744073709551424#64))

/-- **`finA`'s state**: the frame, the saved words, and `memory`'s precondition at its call. -/
theorem finA_ok {m S M2 M6 : MachineState} {top : Word} {regs : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hlim : env.stackLimit.toNat + 208 ≤ top.toNat) (hF6 : env.Frame top Tactic.F m M6) (hS6 : SlotsAt M6 S top)
    (G0 : FormT env M2 (top + 18446744073709551536#64)) (G1 : FormT env M6 (top + 18446744073709551536#64))
    (n26 : (env.next M2).toNat ≤ (env.next M6).toNat)
    (k62 : ∀ x : Word, x.toNat < (env.next M2).toNat → M6.getMem x = M2.getMem x) :
    env.Frame top Tactic.F m (finA M6 M2 top) ∧ SlotsAt (finA M6 M2 top) S top ∧
      ∀ R : Reg → Word, R .x2 = top + 18446744073709551408#64 → R .x10 = regs .x10 → R .x11 = regs .x11 →
        R .x13 = top + 18446744073709551408#64 → MemoryT.PreT env R (finA M6 M2 top) := by
  have hlay := env.layout
  have hE := hW.heapEnd_le
  have x6 := hF6.2.1
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  have t200 := top_sub (top := top) (c := 18446744073709551416#64) (k := 200) rfl (by omega)
  have t192 := top_sub (top := top) (c := 18446744073709551424#64) (k := 192) rfl (by omega)
  have t184 := top_sub (top := top) (c := 18446744073709551432#64) (k := 184) rfl (by omega)
  have t176 := top_sub (top := top) (c := 18446744073709551440#64) (k := 176) rfl (by omega)
  have t168 := top_sub (top := top) (c := 18446744073709551448#64) (k := 168) rfl (by omega)
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have g : ∀ x : Word, x.toNat < top.toNat - 208 ∨ top.toNat - 56 ≤ x.toNat →
      (finA M6 M2 top).getMem x = M6.getMem x := fun x hx => by
    unfold finA; repeat rw [get_ne (by omega)]
  have FA : env.Frame top Tactic.F m (finA M6 M2 top) := by
    unfold finA
    exact Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF6 (by omega) (by omega))
      (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega)
      (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)
  have nA : env.next (finA M6 M2 top) = env.next M6 := g _ (.inl (by omega))
  have kA : ∀ x : Word, x.toNat < (env.next M6).toNat → (finA M6 M2 top).getMem x = M6.getMem x :=
    fun x hx => g x (.inl (by omega))
  refine ⟨FA, fun x l1 l2 => by rw [g x (.inr l1)]; exact hS6 x l1 l2, fun R s2 s10 s11 s13 => ?_⟩
  refine fin_pre hpre h2 hW h16 hlim FA G0 (by rw [nA]; exact n26) (fun x hx => by rw [kA x (by omega)]; exact k62 x hx)
    ?_ ?_ ?_ G1 (by rw [nA]) kA ?_ ?_ ?_ s2 s10 s11 s13
  all_goals
    unfold finA; repeat rw [get_ne (by omega)]
    first
      | (rw [MachineState.getMem_setMem_eq]; done)
      | (rw [MachineState.getMem_setMem_eq, StateDerivedT.add_add (d := 18446744073709551544#64) rfl])
      | (rw [MachineState.getMem_setMem_eq, StateDerivedT.add_add (d := 18446744073709551552#64) rfl])

/-- **`finB`'s state**: the frame, the saved words, and `memory`'s precondition at its call. -/
theorem finB_ok {m S M2 M3 : MachineState} {top : Word} {regs : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hlim : env.stackLimit.toNat + 208 ≤ top.toNat) (hF3 : env.Frame top Tactic.F m M3) (hS3 : SlotsAt M3 S top)
    (G0 : FormT env M2 (top + 18446744073709551536#64)) (G1 : FormT env M3 (top + 18446744073709551408#64))
    (n23 : (env.next M2).toNat ≤ (env.next M3).toNat)
    (k32 : ∀ x : Word, x.toNat < (env.next M2).toNat → M3.getMem x = M2.getMem x) :
    env.Frame top Tactic.F m (finB M3 M2 top) ∧ SlotsAt (finB M3 M2 top) S top ∧
      ∀ R : Reg → Word, R .x2 = top + 18446744073709551408#64 → R .x10 = regs .x10 → R .x11 = regs .x11 →
        R .x13 = top + 18446744073709551408#64 → MemoryT.PreT env R (finB M3 M2 top) := by
  have hlay := env.layout
  have hE := hW.heapEnd_le
  have x3 := hF3.2.1
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  have t200 := top_sub (top := top) (c := 18446744073709551416#64) (k := 200) rfl (by omega)
  have t192 := top_sub (top := top) (c := 18446744073709551424#64) (k := 192) rfl (by omega)
  have t184 := top_sub (top := top) (c := 18446744073709551432#64) (k := 184) rfl (by omega)
  have t176 := top_sub (top := top) (c := 18446744073709551440#64) (k := 176) rfl (by omega)
  have t168 := top_sub (top := top) (c := 18446744073709551448#64) (k := 168) rfl (by omega)
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t80 := top_sub (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have g : ∀ x : Word, x.toNat < top.toNat - 208 ∨ top.toNat - 56 ≤ x.toNat →
      (finB M3 M2 top).getMem x = M3.getMem x := fun x hx => by
    unfold finB; repeat rw [get_ne (by omega)]
  have FB : env.Frame top Tactic.F m (finB M3 M2 top) := by
    unfold finB
    exact Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
      (Tactic.frame_store (Tactic.frame_store hF3 (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega)
      (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)
  have nB : env.next (finB M3 M2 top) = env.next M3 := g _ (.inl (by omega))
  have kB : ∀ x : Word, x.toNat < (env.next M3).toNat → (finB M3 M2 top).getMem x = M3.getMem x :=
    fun x hx => g x (.inl (by omega))
  refine ⟨FB, fun x l1 l2 => by rw [g x (.inr l1)]; exact hS3 x l1 l2, fun R s2 s10 s11 s13 => ?_⟩
  refine fin_pre hpre h2 hW h16 hlim FB G0 (by rw [nB]; exact n23) (fun x hx => by rw [kB x (by omega)]; exact k32 x hx)
    ?_ ?_ ?_ G1 (by rw [nB]) kB ?_ ?_ ?_ s2 s10 s11 s13
  all_goals
    unfold finB; repeat rw [get_ne (by omega)]
    first
      | (rw [MachineState.getMem_setMem_eq]; done)
      | (rw [MachineState.getMem_setMem_eq, StateDerivedT.add_add (d := 18446744073709551416#64) rfl])
      | (rw [MachineState.getMem_setMem_eq, StateDerivedT.add_add (d := 18446744073709551424#64) rfl])

/-- **The return, from `memory`'s**: the saved words, the frame and the postcondition. -/
theorem post {m M m3 : MachineState} {top : Word} {regs R' r3 : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hstk : env.stackLimit.toNat + 208 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (hFs : env.Frame (top + 18446744073709551408#64) (OutT R' M) M m3)
    (hP : MPost env R' M r3 m3) (s10 : R' .x10 = regs .x10) :
    (∀ x : Word, top.toNat - 56 ≤ x.toNat → x.toNat < top.toNat → m3.getMem x = M.getMem x) ∧
      env.Frame top (OutT regs m) m m3 ∧ ∀ r', StateDerivedT.PostT env regs m r' m3 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have t208 := top_sub (top := top) (c := 18446744073709551408#64) (k := 208) rfl (by omega)
  have kM : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x :=
    fun x hx => hF.2.2 x fun hw => by
      have := hF.2.1
      have := hF.1
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at hx; omega
      · exact hw
  obtain ⟨hout, slotLow, hpost⟩ := StateDerivedT.self_kept hV1 hV2 hF.1 (fun x hx _ => kM x (.inr (by omega))) s10
  refine ⟨fun x l1 l2 => hFs.2.2 x fun hw => ?_, (Tactic.frame_weaken hF).trans hFs (by omega)
    fun b hb => .inr (.inr (.inr (hout b hb))), fun r' => ?_⟩
  · rcases hw with hw | hw | hw | hw
    · omega
    · have := hFs.2.1; omega
    · rw [hw] at l1; omega
    · rcases slotLow x (hout x hw) with h | h
      · have := hF.2.1; have := hF.1; omega
      · omega
  unfold MPost at hP
  exact hpost r3 r' m3 hP

set_option rv_sym.heap true in
/-- **`Flushes::memory_cols` is total**, with 208 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needM : Nat} (hnK : 208 + Constant.need ≤ need) (hnC : 208 + needC ≤ need)
    (hnM : 208 + needM ≤ need)
    (hconst : ConstantAlT.specT env p L.constant.idx) (hcol : ColAlT.colSpecT env p L.col.idx needC)
    (hmem : MemoryT.SpecT env p L.memory.idx needM) : SpecT env p i need := by
  have hmem' : HoldsT env p L.memory.idx needM (MPre env) (MPost env) OutT AbortStop := by
    unfold MPre MPost; exact hmem
  suffices h : HoldsT env p i need (PreS env) (StateDerivedT.PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp with [hL, hnK, hnC, hnM] using [hconst (Model.ofLimbsW (0#64, 0#64)), hcol, hmem']
  all_goals
    have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 208 ≤ top.toNat := by omega
    have hc1 : 1 ≤ (regs .x14).toNat := hP.2.2.2.2.2.1
    have hcw := hP.2.2.2.2.2.2.1
    have hca : (regs .x13).toNat % 8 = 0 := hP.2.2.2.2.2.2.2
    rw [inWindow_iff] at hcw
  all_goals try (rw [inWindow_iff]; omega)
  all_goals try omega
  all_goals try
    have x8 : (regs .x13 + 8#64).toNat = (regs .x13).toNat + 8 := toNat_add_ofNat (by omega)
    have one : (1#64).toNat = 1 := rfl
    rw [BitVec.lt_def, one] at hc
    first
      | (rw [inWindow_iff, x8]; omega)
      | (rw [x8]; omega)
  all_goals
    obtain ⟨F2, S2, G0⟩ := at2 hpre_8 hpre_7 hlim (saved_frame (ret := ret) (regs := regs) hpre_5 hlim)
      hret1_14 rfl hret2_14 hret2_16 ⟨hret2_17, hret2_18⟩ rfl
  all_goals first
    | (obtain ⟨F3, S3, G1, n23, k32⟩ := at3 hpre_8 hpre_7 hlim F2 S2 hret3_14 rfl hret3_16 ⟨hret3_17, hret3_18⟩
       obtain ⟨FB, SB, PB⟩ := finB_ok hP hpre_2 hpre_8 hpre_7 hlim F3 S3 G0 G1 n23 k32
       first
         | (unfold MPre; refine PB _ ?_ ?_ ?_ ?_ <;> rfl)
         | (obtain ⟨k4, F4, hPost⟩ := post hP hpre_2 hpre_8 hlim FB hret4_14 hret4_16 rfl
            obtain ⟨s8, s16, s24, s32, s40, s48, s56⟩ := saved_read (ret := ret) (regs := regs) hlim
              fun x l1 l2 => (k4 x l1 l2).trans (SB x l1 l2)
            first
              | exact s8
              | exact ⟨⟨rfl, s16, s24, s32, s40, s48, s56, rfl, rfl, rfl, rfl, rfl, rfl⟩, F4, hret4_15, hPost _⟩))
    | (obtain ⟨F5, S5, -, n25, k52⟩ := at3 hpre_8 hpre_7 hlim F2 S2 hret5_14 rfl hret5_16 ⟨hret5_17, hret5_18⟩
       obtain ⟨F6, S6, G1, n26, k62⟩ := at6 hpre_8 hpre_7 hlim F5 S5 n25 k52 hret6_14 rfl hret6_16
         ⟨hret6_17, hret6_18⟩
       obtain ⟨FA, SA, PA⟩ := finA_ok hP hpre_2 hpre_8 hpre_7 hlim F6 S6 G0 G1 n26 k62
       first
         | (unfold MPre; refine PA _ ?_ ?_ ?_ ?_ <;> rfl)
         | (obtain ⟨k7, F7, hPost⟩ := post hP hpre_2 hpre_8 hlim FA hret7_14 hret7_16 rfl
            obtain ⟨s8, s16, s24, s32, s40, s48, s56⟩ := saved_read (ret := ret) (regs := regs) hlim
              fun x l1 l2 => (k7 x l1 l2).trans (SA x l1 l2)
            first
              | exact s8
              | exact ⟨⟨rfl, s16, s24, s32, s40, s48, s56, rfl, rfl, rfl, rfl, rfl, rfl⟩, F7, hret7_15, hPost _⟩))

end Rv64mc.Proof.Layout.MemoryColsT

/-- info: 'Rv64mc.Proof.Layout.MemoryColsT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.MemoryColsT.total
