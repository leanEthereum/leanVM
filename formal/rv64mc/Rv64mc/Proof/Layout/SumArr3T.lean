/-
  Rv64mc.Proof.Layout.SumArr3T

  `<Form>::sum::<[Form; 3]>` is total: from `Form::zero()` it adds the array's three `Form`s in turn
  (`<Form as Add>::add`, `FormAddT`) and moves the sum to `sret`, a `Form` (`FormReprT.FormT`) whose whole terms'
  block, unless of capacity `0`, was allocated by the call (`MemoryIfT.Fresh40`). A safety-only contract (class D).

  The compiled function takes `sret` (`a0`) and the array (`a1`, 72 bytes); each `add` gets the running sum's header
  at `sp + 0x18` as `self` and the next element's terms' pointer and length as `other`. The precondition: `sret` a
  caller's frame object, 8-byte aligned; the array a caller's frame object, each element a `Form` (`FormsT`). At each
  `add`, `self`'s block is fresh since the entry (or empty) and `other`'s lies below `NEXT` at the entry, which is
  `FormAddT.PreT`'s apartness (`pre_at`). The state after each `add` and the copies before the next is a lemma
  (`step`), so the arithmetic runs in small contexts; this function's precondition (`PreS`) and `add`'s pre and post
  (`MemoryIfT.APre`, `APost`) are sealed.

  ## Main definitions

  * `PreT`, `PostT`, `OutT`, `SpecT`, `cp`, `Inv`

  ## Main results

  * `zero_ok`, `pre_at`, `step`, `fin_ok`, `total`
-/

import Rv64mc.Proof.Layout.MemoryIfT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Form.SumArrFormN3

namespace Rv64mc.Proof.Layout.SumArr3T

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FormReprT (FormT FormsT)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Layout.StateDerivedT (get_ne top_sub fkeep)
open Rv64mc.Proof.Layout.MemoryIfT (APre APost Fresh40)
open Rv64mc.Gen.Verifier.Layout.Form.SumArrFormN3 (Link tmpl)

variable {env : Env}

/-- The total precondition: `sret` (`a0`) a caller's frame object, 8-byte aligned; the array (`a1`) a caller's frame
    object of three `Form`s. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  StackObj (regs .x2) (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ StackObj (regs .x2) (regs .x11) 72 ∧
    FormsT env m (regs .x11) 3

/-- The total postcondition: the sum a `Form` whose whole terms' block was allocated by the call, unless empty. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  FormT env m' (regs .x10) ∧ Fresh40 m' (regs .x10) (env.next m).toNat (env.next m').toNat

/-- What it writes besides its stack and what it allocates: `sret`. -/
def OutT (regs : Reg → Word) (_m : MachineState) (b : Word) : Prop := InRange (regs .x10) 24 b

/-- **The total contract of `<Form>::sum::<[Form; 3]>`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-- The precondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl

/-! ## The body -/

/-- The prologue's three saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)

/-- The six words stored before each `add`: `self`'s header at `top - 72`, a copy of `other`'s at `top - 48`. -/
def cp (M : MachineState) (top u0 u8 u16 v0 v8 v16 : Word) : MachineState :=
  (((((M.setMem (top + 18446744073709551544#64) u0).setMem (top + 18446744073709551552#64) u8).setMem
    (top + 18446744073709551560#64) u16).setMem (top + 18446744073709551568#64) v0).setMem
    (top + 18446744073709551576#64) v8).setMem (top + 18446744073709551584#64) v16

/-- Reads past the six stores. -/
theorem cp_get {M : MachineState} {top u0 u8 u16 v0 v8 v16 x : Word} (h96 : 96 ≤ top.toNat)
    (hx : x.toNat < top.toNat - 72 ∨ top.toNat - 24 ≤ x.toNat) :
    (cp M top u0 u8 u16 v0 v8 v16).getMem x = M.getMem x := by
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  unfold cp
  repeat rw [get_ne (by omega)]

/-- `self`'s header words at `top - 72`. -/
theorem cp_self {M : MachineState} {top u0 u8 u16 v0 v8 v16 : Word} (h96 : 96 ≤ top.toNat) :
    (cp M top u0 u8 u16 v0 v8 v16).getMem (top + 18446744073709551544#64) = u0 ∧
      (cp M top u0 u8 u16 v0 v8 v16).getMem (top + 18446744073709551544#64 + 8#64) = u8 ∧
      (cp M top u0 u8 u16 v0 v8 v16).getMem (top + 18446744073709551544#64 + 16#64) = u16 := by
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  rw [StateDerivedT.add_add (d := 18446744073709551552#64) rfl,
    StateDerivedT.add_add (d := 18446744073709551560#64) rfl]
  unfold cp
  refine ⟨?_, ?_, ?_⟩
  all_goals
    repeat rw [get_ne (by omega)]
    rw [MachineState.getMem_setMem_eq]

/-- The saved words' region, from `top - 24` to `top`, as in `S`. -/
def Slots (M S : MachineState) (top : Word) : Prop :=
  ∀ x : Word, top.toNat - 24 ≤ x.toNat → x.toNat < top.toNat → M.getMem x = S.getMem x

/-- **The state before an `add`**: the frame, the saved words, `self` at `top - 72` a `Form` whose whole block is
    fresh since the entry (or empty). -/
def Inv (env : Env) (m S M : MachineState) (top : Word) : Prop :=
  env.Frame top Tactic.F m M ∧ Slots M S top ∧ FormT env M (top + 18446744073709551544#64) ∧
    Fresh40 M (top + 18446744073709551544#64) (env.next m).toNat (env.next M).toNat

/-- **`Form::zero()` at `top - 72`**, after the prologue. -/
theorem zero_ok {m : MachineState} {top ret v0 v8 v16 : Word} {regs : Reg → Word} (hW : Windows env top m)
    (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) :
    Inv env m (saved m top ret regs) (cp (saved m top ret regs) top 0#64 8#64 0#64 v0 v8 v16) top := by
  have hlay := env.layout
  have htl := hW.top_le
  have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  obtain ⟨z0, z8, z16⟩ := cp_self (M := saved m top ret regs) (top := top) (u0 := 0#64) (u8 := 8#64) (u16 := 0#64)
    (v0 := v0)
    (v8 := v8) (v16 := v16) (by omega)
  have hw : InWin env (top + 18446744073709551544#64) 24 := .inr ⟨by omega, by omega⟩
  have hc : vecCap (cp (saved m top ret regs) top 0#64 8#64 0#64 v0 v8 v16) (top + 18446744073709551544#64) = 0#64 := by
    rw [vecCap_eq, z0]
  have hl : vecLen (cp (saved m top ret regs) top 0#64 8#64 0#64 v0 v8 v16) (top + 18446744073709551544#64) = 0#64 := by
    rw [vecLen_eq, z16]
  refine ⟨?_, fun x l1 l2 => cp_get (by omega) (.inr l1), ⟨⟨hw, Runtime.VecReprT.RawVecT.of_empty
    (Runtime.MemsetT.InWin.sub hw (Nat.le_refl _) (by omega)) (by omega) (by rw [Runtime.GrowOne.rvCapAt_eq, z0]),
    by rw [hc, hl]⟩, fun t ht => by rw [hl] at ht; simp at ht⟩, .inl (by rw [hc]; rfl)⟩
  unfold cp saved
  repeat refine Tactic.frame_store ?_ (by omega) (by omega)
  exact Tactic.frame_refl hnx

/-- What the frame keeps of the entry: below `NEXT` and from the stack top. -/
theorem k0 {m M : MachineState} {top : Word} (hF : env.Frame top Tactic.F m M)
    (hlim : env.stackLimit.toNat ≤ top.toNat) :
    ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M.getMem x = m.getMem x := fun x hx =>
  hF.2.2 x fun hw => by
    have := env.layout
    have := hF.1
    have := hF.2.1
    rcases hw with hw | hw | hw | hw
    · omega
    · omega
    · rw [hw] at hx; omega
    · exact hw

/-- **`add`'s precondition** before each call: `self` at `top - 72` (`Inv`), `other` the array's element at `o`, its
    words read from a memory `N` agreeing with the entry from the stack top. -/
theorem pre_at {m M N S : MachineState} {top o o8 o16 : Word} {R : Reg → Word}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hI : Inv env m S M top) (ho : top.toNat ≤ o.toNat) (ho2 : o.toNat + 24 ≤ 0xc0000000) (hf : FormT env m o)
    (hN : ∀ x : Word, top.toNat ≤ x.toNat → N.getMem x = m.getMem x) (e8 : o8 = o + 8#64) (e16 : o16 = o + 16#64)
    (r2 : R .x2 = top + 18446744073709551520#64) (r10 : R .x10 = top + 18446744073709551520#64)
    (r11 : R .x11 = top + 18446744073709551544#64) (r12 : R .x12 = N.getMem o8) (r13 : R .x13 = N.getMem o16) :
    FormAddT.PreT env R M := by
  have hlay := env.layout
  have htl := hW.top_le
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  obtain ⟨hF, -, hs, hb⟩ := hI
  have kM := k0 hF (by omega)
  have x8 : (o + 8#64).toNat = o.toNat + 8 := toNat_add_ofNat (by omega)
  have x16 : (o + 16#64).toNat = o.toNat + 16 := toNat_add_ofNat (by omega)
  have p8 : M.getMem (o + 8#64) = m.getMem (o + 8#64) := kM _ (.inr (by omega))
  have p16 : M.getMem (o + 16#64) = m.getMem (o + 16#64) := kM _ (.inr (by omega))
  have hfoot := hf.foot
  have hfM : FormT env M o := FormReprT.FormT.keep hf hF.1 (fun x l1 l2 => kM x (.inr (by omega)))
    fun x l1 l2 => kM x (.inl (by rcases hfoot with h | ⟨-, h, -⟩ <;> omega))
  have q12 : R .x12 = vecPtr M o := by rw [r12, e8, hN _ (by omega), vecPtr_eq, p8]
  have q13 : R .x13 = vecLen M o := by rw [r13, e16, hN _ (by omega), vecLen_eq, p16]
  have ep : vecPtr M o = vecPtr m o := by rw [vecPtr_eq, vecPtr_eq, p8]
  have el : vecLen M o = vecLen m o := by rw [vecLen_eq, vecLen_eq, p16]
  unfold FormAddT.PreT
  rw [r2, r10, r11, q12, q13]
  refine ⟨⟨by omega, by omega⟩, by omega, ⟨by omega, by omega⟩, .inl (by omega), hs,
    (FormReprT.vecT_buf hfM.1).1, hfM.2, ?_⟩
  rw [ep, el]
  rcases hfoot with h | ⟨-, h, -⟩
  · exact .inl h
  unfold Fresh40 at hb
  rcases hb with h' | ⟨h1, -⟩
  · exact .inr (.inl h')
  · exact .inr (.inr (.inl (by omega)))

/-- **After an `add`**: the frame, the saved words, the sum at `top - 96` a `Form` whose block is fresh since the
    entry (or empty). -/
theorem after {m S M m' : MachineState} {top : Word} {R r : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hI : Inv env m S M top)
    (d : env.Frame (top + 18446744073709551520#64) (FormAddT.OutT R M) M m') (p : APost env R M r m')
    (q2 : R .x2 = top + 18446744073709551520#64) (q10 : R .x10 = top + 18446744073709551520#64)
    (q11 : R .x11 = top + 18446744073709551544#64) :
    env.Frame top Tactic.F m m' ∧ Slots m' S top ∧ FormT env m' (top + 18446744073709551520#64) ∧
      Fresh40 m' (top + 18446744073709551520#64) (env.next m).toNat (env.next m').toNat := by
  have hlay := env.layout
  have htl := hW.top_le
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  obtain ⟨hF, hS, hs, hb⟩ := hI
  have hn := hF.1
  have hd := d.1
  have hx := d.2.1
  have o : ∀ x : Word, FormAddT.OutT R M x → (env.stackLimit.toNat ≤ x.toNat ∧ x.toNat < top.toNat - 48) ∨
      ((env.next m).toNat ≤ x.toNat ∧ x.toNat < (env.next m').toNat) := fun x hx' => by
    unfold FormAddT.OutT InRange at hx'
    rw [q10, q11] at hx'
    rcases hx' with hx' | hx' | hx'
    · exact .inl (by omega)
    · exact .inl (by omega)
    · unfold Fresh40 at hb
      rcases hb with h0 | ⟨h1, h2⟩
      · rw [h0] at hx'; omega
      · exact .inr (by omega)
  obtain ⟨G, B⟩ := MemoryIfT.add_res (lo := (env.next m).toNat) p (by rw [q2]; exact d) (by rw [q11]; exact hb)
    hn q10
  refine ⟨hF.trans d (by omega) fun x hx' => ?_, fun x l1 l2 => ?_, G, B⟩
  · rcases o x hx' with h | h
    · exact .inl ⟨h.1, by omega⟩
    · exact .inr (.inl h)
  · rw [fkeep (x := x) d (.inr (by omega)) (.inr (by omega)) (fun e => by rw [e] at l1; omega)
      fun h => by rcases o x h with h | h <;> omega]
    exact hS x l1 l2

/-- **The copies before the next `add`**: the sum moved to `top - 72`, the state `Inv` again. -/
theorem step {m S m' : MachineState} {top v0 v8 v16 : Word}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat)
    (hF : env.Frame top Tactic.F m m') (hS : Slots m' S top) (G : FormT env m' (top + 18446744073709551520#64))
    (B : Fresh40 m' (top + 18446744073709551520#64) (env.next m).toNat (env.next m').toNat) :
    Inv env m S (cp m' top (m'.getMem (top + 18446744073709551520#64)) (m'.getMem (top + 18446744073709551528#64))
      (m'.getMem (top + 18446744073709551536#64)) v0 v8 v16) top := by
  have hlay := env.layout
  have htl := hW.top_le
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  have hx := hF.2.1
  obtain ⟨c0, c8, c16⟩ := cp_self (M := m') (top := top) (u0 := m'.getMem (top + 18446744073709551520#64))
    (u8 := m'.getMem (top + 18446744073709551528#64)) (u16 := m'.getMem (top + 18446744073709551536#64)) (v0 := v0)
    (v8 := v8) (v16 := v16) (by omega)
  have nC : env.next (cp m' top (m'.getMem (top + 18446744073709551520#64)) (m'.getMem (top + 18446744073709551528#64))
      (m'.getMem (top + 18446744073709551536#64)) v0 v8 v16) = env.next m' := cp_get (by omega) (.inl (by omega))
  have hfoot := G.foot
  obtain ⟨G', ep, -⟩ := StateDerivedT.FormT.move (d := top + 18446744073709551544#64) G (by rw [nC])
    (.inr ⟨by omega, by omega⟩) (by omega) c0
    (by rw [c8, StateDerivedT.add_add (d := 18446744073709551528#64) rfl])
    (by rw [c16, StateDerivedT.add_add (d := 18446744073709551536#64) rfl])
    fun x l1 l2 => cp_get (by omega) (.inl (by rcases hfoot with h | ⟨-, h, -⟩ <;> omega))
  refine ⟨?_, fun x l1 l2 => by rw [cp_get (by omega) (.inr l1)]; exact hS x l1 l2, G', ?_⟩
  · unfold cp
    repeat refine Tactic.frame_store ?_ (by omega) (by omega)
    exact hF
  · unfold Fresh40 at B ⊢
    rw [ep, nC, vecCap_eq, c0, ← vecCap_eq]
    exact B

/-- The sum's three words stored at `sret`, sealed so that no unification unfolds the stores. -/
@[irreducible] def fin (m3 : MachineState) (top a : Word) : MachineState :=
  ((m3.setMem a (m3.getMem (top + 18446744073709551520#64))).setMem (a + 8#64)
    (m3.getMem (top + 18446744073709551528#64))).setMem (a + 16#64) (m3.getMem (top + 18446744073709551536#64))

theorem fin_eq {m3 : MachineState} {top a : Word} : fin m3 top a =
    ((m3.setMem a (m3.getMem (top + 18446744073709551520#64))).setMem (a + 8#64)
      (m3.getMem (top + 18446744073709551528#64))).setMem (a + 16#64) (m3.getMem (top + 18446744073709551536#64)) := by
  unfold fin; rfl

/-- **The return**: the sum moved to `sret`, the frame and the saved words. -/
theorem fin_ok {m m3 : MachineState} {top ret : Word} {regs : Reg → Word}
    (hW : Windows env top m) (hlim : env.stackLimit.toNat + 96 ≤ top.toNat) (hpre : PreT env regs m)
    (h2 : regs .x2 = top)
    (hF : env.Frame top Tactic.F m m3) (hS : Slots m3 (saved m top ret regs) top)
    (G : FormT env m3 (top + 18446744073709551520#64))
    (B : Fresh40 m3 (top + 18446744073709551520#64) (env.next m).toNat (env.next m3).toNat)
    (hst : env.Static m3) :
    (∀ r', PostT env regs m r' (fin m3 top (regs .x10))) ∧ env.Static (fin m3 top (regs .x10)) ∧
    env.Frame top (OutT regs m) m (fin m3 top (regs .x10)) ∧
    (fin m3 top (regs .x10)).getMem (top + 18446744073709551608#64) = ret ∧
    (fin m3 top (regs .x10)).getMem (top + 18446744073709551600#64) = regs .x8 ∧
    (fin m3 top (regs .x10)).getMem (top + 18446744073709551592#64) = regs .x9 := by
  rw [fin_eq]
  obtain ⟨⟨ha1, ha2⟩, hal, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have htl := hW.top_le
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  have a8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
  have a16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
  have hx := hF.2.1
  have gM : ∀ x : Word, (x.toNat < (regs .x10).toNat ∨ (regs .x10).toNat + 24 ≤ x.toNat) →
      (((m3.setMem (regs .x10) (m3.getMem (top + 18446744073709551520#64))).setMem
      (regs .x10 + 8#64) (m3.getMem (top + 18446744073709551528#64))).setMem (regs .x10 + 16#64)
      (m3.getMem (top + 18446744073709551536#64))).getMem x = m3.getMem x := fun x hx' => by
    rw [get_ne (by omega), get_ne (by omega), get_ne (by omega)]
  have nM := gM env.nextAddr (.inl (by omega))
  have hfoot := G.foot
  obtain ⟨G', ep, -⟩ := StateDerivedT.FormT.move (d := regs .x10) G (by unfold Env.next; rw [nM])
    (.inr ⟨by omega, by omega⟩) hal
    (by rw [get_ne (by omega), get_ne (by omega), MachineState.getMem_setMem_eq])
    (by rw [StateDerivedT.add_add (d := 18446744073709551528#64) rfl, get_ne (by omega),
      MachineState.getMem_setMem_eq])
    (by rw [StateDerivedT.add_add (d := 18446744073709551536#64) rfl, MachineState.getMem_setMem_eq])
    fun x l1 l2 => gM x (.inl (by rcases hfoot with h | ⟨-, h, -⟩ <;> omega))
  have ec : vecCap (((m3.setMem (regs .x10) (m3.getMem (top + 18446744073709551520#64))).setMem
      (regs .x10 + 8#64) (m3.getMem (top + 18446744073709551528#64))).setMem (regs .x10 + 16#64)
      (m3.getMem (top + 18446744073709551536#64))) (regs .x10) = vecCap m3 (top + 18446744073709551520#64) := by
    rw [vecCap_eq, vecCap_eq, get_ne (by omega), get_ne (by omega), MachineState.getMem_setMem_eq]
  have n1 := hF.1
  have hs0 : env.stackLimit.toNat ≤ (regs .x10).toNat := by omega
  refine ⟨fun _ => ⟨G', ?_⟩, Env.static_setMem_stack (Env.static_setMem_stack (Env.static_setMem_stack hst hs0)
    (by omega)) (by omega), ⟨by unfold Env.next at n1 ⊢; rw [nM]; exact n1,
    by unfold Env.next at hx ⊢; rw [nM]; exact hx,
    fun x hx' => ?_⟩, ?_, ?_, ?_⟩
  · unfold Fresh40 at B ⊢
    rw [ep, ec]
    unfold Env.next at B ⊢
    rw [nM]
    exact B
  · by_cases hin : (regs .x10).toNat ≤ x.toNat ∧ x.toNat < (regs .x10).toNat + 24
    · exact absurd (.inr (.inr (.inr hin))) hx'
    · rw [gM x (by omega)]
      exact hF.2.2 x fun hw => hx' (by
        rcases hw with hw | hw | hw | hw
        · exact .inl hw
        · exact .inr (.inl (by unfold Env.next at hw ⊢; rw [nM]; exact hw))
        · exact .inr (.inr (.inl hw))
        · exact hw.elim)
  · rw [gM _ (.inl (by omega)), hS _ (by omega) (by omega)]
    unfold saved; rw [get_ne (by omega), get_ne (by omega), MachineState.getMem_setMem_eq]
  · rw [gM _ (.inl (by omega)), hS _ (by omega) (by omega)]
    unfold saved; rw [get_ne (by omega), MachineState.getMem_setMem_eq]
  · rw [gM _ (.inl (by omega)), hS _ (by omega) (by omega)]
    unfold saved; rw [MachineState.getMem_setMem_eq]

/-- The array's three `Form`s, and its alignment. -/
theorem arr_ok {m : MachineState} {a : Word} (h : FormsT env m a 3) :
    a.toNat % 8 = 0 ∧ FormT env m a ∧ FormT env m (a + 24#64) ∧ FormT env m (a + 48#64) := by
  have h0 : FormT env m a := by simpa using h 0 (by omega)
  exact ⟨h0.1.2.1.2.1, h0, h 1 (by omega), h 2 (by omega)⟩

/-- The prologue's stores keep the words from the stack top. -/
theorem saved_top {m : MachineState} {top ret : Word} {regs : Reg → Word} (h96 : 96 ≤ top.toNat) :
    ∀ x : Word, top.toNat ≤ x.toNat → (saved m top ret regs).getMem x = m.getMem x := fun x hx => by
  have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  unfold saved
  rw [get_ne (by omega), get_ne (by omega), get_ne (by omega)]

set_option rv_sym.heap true in
/-- **`<Form>::sum::<[Form; 3]>` is total**, with 96 bytes of stack beyond `add`'s. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA : Nat} (hnA : 96 + needA ≤ need) (hadd : FormAddT.SpecT env p L.add.idx needA) :
    SpecT env p i need := by
  have hadd' : HoldsT env p L.add.idx needA (APre env) (APost env) FormAddT.OutT AbortStop := by
    unfold APre APost; exact hadd
  suffices h : HoldsT env p i need (PreS env) (PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp with [hL, hnA] using [hadd']
  all_goals
    have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 96 ≤ top.toNat := by omega
    have htl := hpre_8.top_le
    have hna := hpre_8.nextAddr_ge
    have ha := hP.2.2.1
    have hs := hP.1
    have hsa := hP.2.1
    rw [hpre_2] at ha hs
    unfold StackObj at ha hs
    have hal := (arr_ok hP.2.2.2).1
  all_goals try (rw [inWindow_iff]; omega)
  all_goals try (rw [inWindow_iff]; simp only [toNat_add_ofNat (show (regs .x11).toNat + 8 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 16 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 24 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 32 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 40 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 48 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 56 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 64 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x10).toNat + 8 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x10).toNat + 16 < 2 ^ 64 by omega)]; omega)
  all_goals try (simp only [toNat_add_ofNat (show (regs .x11).toNat + 8 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 16 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 24 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 32 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 40 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 48 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 56 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x11).toNat + 64 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x10).toNat + 8 < 2 ^ 64 by omega),
    toNat_add_ofNat (show (regs .x10).toNat + 16 < 2 ^ 64 by omega)]; omega)
  all_goals try omega
  all_goals
    obtain ⟨-, E0, E1, E2⟩ := arr_ok hP.2.2.2
    have I0 := zero_ok (m := m) (top := top) (ret := ret) (regs := regs)
      (v0 := (saved m top ret regs).getMem (regs .x11)) (v8 := (saved m top ret regs).getMem (regs .x11 + 8#64))
      (v16 := (saved m top ret regs).getMem (regs .x11 + 16#64)) hpre_8 hpre_7 hlim hpre_5
  · unfold APre
    refine pre_at (N := saved m top ret regs) hpre_8 hpre_7 hlim I0 (by omega) (by omega) E0
      (saved_top (by omega)) rfl rfl ?_ ?_ ?_ ?_ ?_
    all_goals rfl
  all_goals
    obtain ⟨F1, S1, G1, B1⟩ := after hpre_8 hlim I0 hret1_14 hret1_16 rfl rfl rfl
    have I1 := step (v0 := m1.getMem (regs .x11 + 24#64)) (v8 := m1.getMem (regs .x11 + 32#64))
      (v16 := m1.getMem (regs .x11 + 40#64)) hpre_8 hpre_7 hlim F1 S1 G1 B1
  · unfold APre
    have e1 := toNat_add_ofNat (a := regs .x11) (k := 24) (by omega)
    refine pre_at (N := m1) (o := regs .x11 + 24#64) hpre_8 hpre_7 hlim I1 (by rw [e1]; omega) (by rw [e1]; omega) E1
      (fun x hx => k0 F1 (by omega) x (.inr hx)) (by rw [BitVec.add_assoc]) (by rw [BitVec.add_assoc])
      ?_ ?_ ?_ ?_ ?_
    all_goals rfl
  all_goals
    obtain ⟨F2, S2, G2, B2⟩ := after hpre_8 hlim I1 hret2_14 hret2_16 rfl rfl rfl
    have I2 := step (v0 := m2.getMem (regs .x11 + 48#64)) (v8 := m2.getMem (regs .x11 + 56#64))
      (v16 := m2.getMem (regs .x11 + 64#64)) hpre_8 hpre_7 hlim F2 S2 G2 B2
  · unfold APre
    have e2 := toNat_add_ofNat (a := regs .x11) (k := 48) (by omega)
    refine pre_at (N := m2) (o := regs .x11 + 48#64) hpre_8 hpre_7 hlim I2 (by rw [e2]; omega) (by rw [e2]; omega) E2
      (fun x hx => k0 F2 (by omega) x (.inr hx)) (by rw [BitVec.add_assoc]) (by rw [BitVec.add_assoc])
      ?_ ?_ ?_ ?_ ?_
    all_goals rfl
  all_goals
    obtain ⟨F3, S3, G3, B3⟩ := after hpre_8 hlim I2 hret3_14 hret3_16 rfl rfl rfl
    obtain ⟨hPost, hSt, F, s8, s16, s24⟩ := fin_ok hpre_8 hlim hP hpre_2 F3 S3 G3 B3 hret3_15
  all_goals rw [← fin_eq (m3 := m3) (top := top) (a := regs .x10)]
  · rw [Tactic.rf_get_x1]; exact s8
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, F, hSt, hPost _⟩
    · rw [Tactic.rf_get_x2]
    · rw [Tactic.rf_get_x8]; exact s16
    · rw [Tactic.rf_get_x9]; exact s24
    · rw [Tactic.rf_get_x18]
    · rw [Tactic.rf_get_x19]
    · rw [Tactic.rf_get_x20]
    · rw [Tactic.rf_get_x21]
    · rw [Tactic.rf_get_x22]
    · rw [Tactic.rf_get_x23]
    · rw [Tactic.rf_get_x24]
    · rw [Tactic.rf_get_x25]
    · rw [Tactic.rf_get_x26]
    · rw [Tactic.rf_get_x27]

end Rv64mc.Proof.Layout.SumArr3T

/-- info: 'Rv64mc.Proof.Layout.SumArr3T.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.SumArr3T.total
