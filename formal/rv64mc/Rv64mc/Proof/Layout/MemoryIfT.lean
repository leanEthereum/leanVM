/-
  Rv64mc.Proof.Layout.MemoryIfT

  `Flushes::memory_if(&mut self, flag, address, count, values)` is total over a `Flushes` of `Form`s
  (`PairFormT.FlushesFormT`): it builds the counter `col(count, 0) + prod(flag, count, 1) + prod(flag, count, 0)`
  (`ColAlT`, `ProdAlT`, two `<Form as Add>::add`s, `FormAddT`) in its frame, then `constant(SEP_MEM)`
  (`ConstantAlT`) and a copy of `address` (`a2`), and calls `Flushes::counted(self, [constant, address], counter,
  count, values)` (`CountedT`). The `Flushes` stays a `Flushes` of `Form`s (`StateDerivedT.PostT`, `counted`'s); it
  writes what `pair` writes (`PairT.OutT`) besides its stack and fresh blocks. A safety-only contract (class D).

  The precondition is `MemoryT.PreT`'s with the arguments one register later: `self` `PairT.FlushesT`, 8-byte
  aligned, a `Flushes` of `Form`s; `address` a `Form` (`FormReprT.FormT`) in a caller's frame (`StackObj`);
  `values` (`a4`) a slice of two `Form`s (`ConcatFormT.SliceFT`). Each `add`'s `self` is a `Form` built since the
  entry whose whole terms' block (`Fresh40`) ends before `other`'s (a `prod` allocated after it), which is
  `FormAddT.PreT`'s apartness (`add_pre`). The body runs as one executor pass; the state after each pair of calls is
  a lemma (`at2`, `at4`, `at6`) so that the arithmetic runs in small contexts. `add`'s and `counted`'s preconditions
  and postconditions (`APre`, `APost`, `MemoryT.KPre`, `MemoryT.KPost`) and this function's own precondition
  (`PreS`) are sealed.

  ## Main definitions

  * `PreT`, `SpecT`, `Fresh40`, `SlotsAt`, `saved`, `chain`

  ## Main results

  * `form_thru`, `add_pre`, `at2`, `at4`, `at6`, `cnt_pre`, `post`, `total`
-/

import Rv64mc.Proof.Layout.MemoryT
import Rv64mc.Proof.Layout.ProdAlT
import Rv64mc.Proof.Layout.FormAddT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.MemoryIf

namespace Rv64mc.Proof.Layout.MemoryIfT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Layout.FormReprT (FormT)
open Rv64mc.Proof.Layout.PairT (FlushesT OutT)
open Rv64mc.Proof.Layout.PairFormT (FlushesFormT)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Layout.ConcatFormT (SliceFT)
open Rv64mc.Proof.Layout.StateDerivedT (get_ne top_sub fkeep)
open Rv64mc.Proof.Layout.MemoryT (KPre KPost)
open Rv64mc.Gen.Verifier.Layout.Flushes.MemoryIf (Link tmpl)

variable {env : Env}

/-- The total precondition: `self` (`a0`) `PairT.FlushesT`, aligned, a `Flushes` of `Form`s; `address` (`a2`) a
    `Form` in a caller's frame; `values` (`a4`) a slice of two `Form`s. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧ FlushesFormT env m (regs .x10) ∧
    StackObj (regs .x2) (regs .x12) 24 ∧ FormT env m (regs .x12) ∧ SliceFT env m (regs .x2) (regs .x14) 2#64

/-- **The total contract of `Flushes::memory_if`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (StateDerivedT.PostT env) OutT AbortStop

/-- The precondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl

/-- `add`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def APre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := FormAddT.PreT env regs m

/-- `add`'s postcondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def APost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  FormAddT.PostT env regs m r' m'

/-! ## `Form`s across the calls -/

/-- **A `Form` kept by a call** that writes neither its header (at or above the call's stack pointer) nor its
    terms' block, with its header's words. -/
theorem form_thru {M M' : MachineState} {t a : Word} {out : Word → Prop} (hF : env.Frame t out M M')
    (hf : FormT env M a) (hlim : env.stackLimit.toNat ≤ t.toNat) (hta : t.toNat ≤ a.toNat)
    (ho : ∀ x : Word, out x → (x.toNat < a.toNat ∨ a.toNat + 24 ≤ x.toNat) ∧ env.stackLimit.toNat ≤ x.toNat) :
    FormT env M' a ∧ vecPtr M' a = vecPtr M a ∧ vecCap M' a = vecCap M a := by
  have hlay := env.layout
  have hx := hF.2.1
  have hn := hF.1
  have hb := hf.foot
  have hlt := FormReprT.vecT_lt hf.1
  have hh : ∀ x : Word, a.toNat ≤ x.toNat → x.toNat < a.toNat + 24 → M'.getMem x = M.getMem x := fun x l1 l2 =>
    fkeep (x := x) hF (.inr (by omega)) (.inr (by omega)) (fun e => by rw [e] at l1; omega)
      fun h => by have := ho x h; omega
  refine ⟨FormReprT.FormT.keep hf hF.1 hh fun x l1 l2 => ?_, ?_, ?_⟩
  · have hxn : x.toNat < (env.next M).toNat := by rcases hb with h | ⟨-, h, -⟩ <;> omega
    exact fkeep (x := x) hF (.inl (by omega)) (.inl hxn) (fun e => by rw [e] at hxn; omega)
      fun h => by have := ho x h; omega
  · rw [Runtime.VecHdrT.vecPtr_eq, Runtime.VecHdrT.vecPtr_eq]
    exact hh _ (by rw [toNat_add_ofNat (by omega)]; omega) (by rw [toNat_add_ofNat (by omega)]; omega)
  · rw [Runtime.VecHdrT.vecCap_eq, Runtime.VecHdrT.vecCap_eq]
    exact hh _ (Nat.le_refl _) (by omega)

/-- **A `Form` built by a call between `lo` and `hi`**: its whole terms' block, to its capacity, there. -/
theorem blk_of {lo hi : Word} {M : MachineState} {a : Word} {f : LeanVM.Protocol.Verifier.Form}
    (h : FormIn lo hi M a f) : (vecCap M a).toNat = 0 ∨
      (lo.toNat ≤ (vecPtr M a).toNat ∧ (vecPtr M a).toNat + 40 * (vecCap M a).toNat ≤ hi.toNat) := by
  obtain ⟨q, cap, hv, hb⟩ := h
  have hp : vecPtr M a = q := hv.ptr_eq
  have hc : (vecCap M a).toNat = cap := by rw [hv.cap_eq]; simp; have := hv.cap_lt; omega
  have hreg : cap = 0 ∨ (lo.toNat ≤ q.toNat ∧ q.toNat + 40 * cap ≤ hi.toNat) := by
    simpa [BufIn, Region, Layouts.VecUsizeE.byteSize] using hb
  rw [hp, hc]
  exact hreg

/-- A `Form`'s whole terms' block, to its capacity, below `NEXT`. -/
theorem cap_lt {M : MachineState} {a : Word} (hf : FormT env M a) :
    (vecCap M a).toNat = 0 ∨ (vecPtr M a).toNat + 40 * (vecCap M a).toNat ≤ (env.next M).toNat := by
  rcases PairFormT.vecT_bufCap hf.1 with h | ⟨-, h, -⟩
  · exact .inl h
  · unfold Env.Live at h; rw [Nat.mul_comm] at h; exact .inr h

/-- **`add`'s precondition**: the result's slot `s`, `self` at `f` a `Form` whose block ends by `N`, `other` the
    `Form` at `o` whose block starts from `N`. -/
theorem add_pre {M : MachineState} {sp s f o : Word} {N : Nat} {R : Reg → Word}
    (hs : StackObj sp s 24) (hsa : s.toNat % 8 = 0) (hf : StackObj sp f 24) (hap : PairT.Apart s 24 f 24)
    (G : FormT env M f) (P : FormT env M o)
    (hb : (vecCap M f).toNat = 0 ∨ (vecPtr M f).toNat + 40 * (vecCap M f).toNat ≤ N)
    (hp : (vecLen M o).toNat = 0 ∨ N ≤ (vecPtr M o).toNat)
    (r2 : R .x2 = sp) (r10 : R .x10 = s) (r11 : R .x11 = f) (r12 : R .x12 = M.getMem (o + 8#64))
    (r13 : R .x13 = M.getMem (o + 16#64)) : FormAddT.PreT env R M := by
  have e12 : M.getMem (o + 8#64) = vecPtr M o := rfl
  have e13 : M.getMem (o + 16#64) = vecLen M o := rfl
  unfold FormAddT.PreT
  rw [r2, r10, r11, r12, r13, e12, e13]
  refine ⟨hs, hsa, hf, hap, G, (FormReprT.vecT_buf P.1).1, P.2, ?_⟩
  rcases hp with h | h
  · exact .inl h
  rcases hb with h' | h'
  · exact .inr (.inl h')
  · exact .inr (.inr (.inr (by omega)))

/-- The `address` header's three words copied to `top - 72`, after `constant`. -/
def chain (M : MachineState) (top a : Word) : MachineState :=
  ((M.setMem (top + 18446744073709551544#64) (M.getMem a)).setMem (top + 18446744073709551552#64)
    (M.getMem (a + 8#64))).setMem (top + 18446744073709551560#64) (M.getMem (a + 16#64))

/-- Reads past the copy. -/
theorem chain_get {M : MachineState} {top a x : Word} (h144 : 144 ≤ top.toNat)
    (hx : x.toNat < top.toNat - 72 ∨ top.toNat - 48 ≤ x.toNat) : (chain M top a).getMem x = M.getMem x := by
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  unfold chain
  rw [get_ne (by omega), get_ne (by omega), get_ne (by omega)]

/-- **`counted`'s precondition at its call**: the prefix `[constant(SEP_MEM), address]` at `top - 96`, the counter
    (the second sum) at `top - 120`, `values` as at the entry. -/
theorem cnt_pre {m M6 : MachineState} {top : Word} {regs R' : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + 144 ≤ top.toNat) (hF : env.Frame top Tactic.F m M6)
    (G0 : FormT env M6 (top + 18446744073709551520#64)) (G1 : FormT env M6 (top + 18446744073709551496#64))
    (s2 : R' .x2 = top + 18446744073709551472#64) (s10 : R' .x10 = regs .x10)
    (s11 : R' .x11 = top + 18446744073709551520#64) (s12 : R' .x12 = top + 18446744073709551496#64)
    (s14 : R' .x14 = regs .x14) (s15 : R' .x15 = 2#64) :
    CountedT.PreT env R' (chain M6 top (regs .x12)) ∧ env.Frame top Tactic.F m (chain M6 top (regs .x12)) := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, hBA⟩, hal, hFF, ⟨ho1, ho2⟩, hfa, hsv⟩ := hpre
  rw [h2] at ha1 ho1 hsv
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have t144 := top_sub (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have t120 := top_sub (top := top) (c := 18446744073709551496#64) (k := 120) rfl (by omega)
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  have x6 := hF.2.1
  have n6 := hF.1
  have nC : env.next (chain M6 top (regs .x12)) = env.next M6 := chain_get (by omega) (.inl (by omega))
  have nC' : (env.next (chain M6 top (regs .x12))).toNat = (env.next M6).toNat := by rw [nC]
  have FC : env.Frame top Tactic.F m (chain M6 top (regs .x12)) :=
    Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  have kC : ∀ x : Word, (x.toNat < (env.next M6).toNat ∨ top.toNat - 144 ≤ x.toNat ∧ x.toNat < top.toNat - 72) →
      (chain M6 top (regs .x12)).getMem x = M6.getMem x := fun x hx => chain_get (by omega) (by omega)
  have k0C : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) →
      (chain M6 top (regs .x12)).getMem x = m.getMem x := fun x hx => FC.2.2 x fun hw => by
    rcases hw with hw | hw | hw | hw
    · omega
    · omega
    · rw [hw] at hx; omega
    · exact hw
  obtain ⟨hFF2, -⟩ := StateDerivedT.FlushesFormT.keep hFF (by rw [nC]; have := hF.1; omega)
    (fun b hb => k0C b (.inl hb)) fun b h1 h2 => k0C b (.inr (by omega))
  have keepS : ∀ a : Word, top.toNat - 144 ≤ a.toNat → a.toNat + 24 ≤ top.toNat - 72 → FormT env M6 a →
      FormT env (chain M6 top (regs .x12)) a := fun a l1 l2 hf => FormReprT.FormT.keep hf (by rw [nC])
    (fun x h1 h2 => kC x (.inr ⟨by omega, by omega⟩)) fun x h1 h2 => kC x (.inl (by
      rcases hf.foot with h | ⟨-, h, -⟩ <;> omega))
  have k6a : ∀ k, k ≤ 16 → M6.getMem (regs .x12 + BitVec.ofNat 64 k) = m.getMem (regs .x12 + BitVec.ofNat 64 k) :=
    fun k hk => hF.2.2 _ fun hw => by
      have e : (regs .x12 + BitVec.ofNat 64 k).toNat = (regs .x12).toNat + k := toNat_add_ofNat (by omega)
      rcases hw with hw | hw | hw | hw
      · omega
      · have := hF.2.1; omega
      · rw [hw] at e; omega
      · exact hw
  have w0 : (chain M6 top (regs .x12)).getMem (top + 18446744073709551544#64) = m.getMem (regs .x12) := by
    unfold chain; rw [get_ne (by omega), get_ne (by omega), MachineState.getMem_setMem_eq]
    simpa using k6a 0 (by omega)
  have w8 : (chain M6 top (regs .x12)).getMem (top + 18446744073709551544#64 + 8#64) =
      m.getMem (regs .x12 + 8#64) := by
    rw [StateDerivedT.add_add (d := 18446744073709551552#64) rfl]
    unfold chain; rw [get_ne (by omega), MachineState.getMem_setMem_eq]; exact k6a 8 (by omega)
  have w16 : (chain M6 top (regs .x12)).getMem (top + 18446744073709551544#64 + 16#64) =
      m.getMem (regs .x12 + 16#64) := by
    rw [StateDerivedT.add_add (d := 18446744073709551560#64) rfl]
    unfold chain; rw [MachineState.getMem_setMem_eq]; exact k6a 16 (by omega)
  obtain ⟨G2, -, -⟩ := StateDerivedT.FormT.move (d := top + 18446744073709551544#64) hfa
    (by rw [nC]; have := hF.1; omega) (.inr ⟨by omega, by omega⟩) (by omega) w0 w8 w16
    fun x l1 l2 => k0C x (.inl (by rcases hfa.foot with h | ⟨-, h, -⟩ <;> omega))
  have two : (2#64).toNat = 2 := rfl
  unfold CountedT.PreT PairT.FlushesT
  rw [s2, s10, s11, s12, s14, s15]
  refine ⟨⟨⟨hFF2.1, hFF2.2.1, ⟨by omega, ha2⟩, hFF2.2.2.1⟩, hal, hFF2,
    .inr ⟨by rw [two]; exact .inr ⟨by omega, by omega⟩, .inr (by omega), fun i hi => ?_⟩,
    ⟨by omega, by omega⟩, keepS _ (by omega) (by omega) G1,
    CountedT.SliceFT.keep hsv (by omega) FC (by omega)⟩, FC⟩
  rw [two] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa using keepS _ (by omega) (by omega) G0
  · rw [StateDerivedT.add_add (d := 18446744073709551544#64) rfl]; exact G2

/-! ## The body, call by call -/

/-- The prologue's six saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  (((((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)).setMem (top + 18446744073709551584#64) (regs .x18)).setMem
    (top + 18446744073709551576#64) (regs .x19)).setMem (top + 18446744073709551568#64) (regs .x20)

/-- The saved words' region, from `top - 48` to `top`, as in `S`. -/
def SlotsAt (M S : MachineState) (top : Word) : Prop :=
  ∀ x : Word, top.toNat - 48 ≤ x.toNat → x.toNat < top.toNat → M.getMem x = S.getMem x

/-- A call from `top - 144` writing below `top - 48` keeps the saved words. -/
theorem SlotsAt.thru {M M' S : MachineState} {top : Word} {out : Word → Prop} (h : SlotsAt M S top)
    (hF : env.Frame (top + 18446744073709551472#64) out M M') (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (ho : ∀ x : Word, out x → x.toNat < top.toNat - 48) : SlotsAt M' S top := fun x l1 l2 => by
  have hlay := env.layout
  have := hF.2.1
  have t144 := top_sub (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  rw [fkeep (x := x) hF (.inr (by omega)) (.inr (by omega)) (fun e => by rw [e] at l1; omega)
    fun h => by have := ho x h; omega]
  exact h x l1 l2

/-- `[ptr, ptr + 40 cap)`, the whole block of the `Form` at `a`, from `lo` to `hi` unless empty. -/
def Fresh40 (M : MachineState) (a : Word) (lo hi : Nat) : Prop :=
  (vecCap M a).toNat = 0 ∨ (lo ≤ (vecPtr M a).toNat ∧ (vecPtr M a).toNat + 40 * (vecCap M a).toNat ≤ hi)

/-- **Up to the first `add`**: `col(count, 0)` at `top - 120`, `prod(flag, count, 1)` at `top - 96`. -/
theorem at2 {m S m1 m2 : MachineState} {top : Word} {R1 R2 : Reg → Word} {f1 f2 : LeanVM.Protocol.Verifier.Form}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hF0 : env.Frame top Tactic.F m S)
    (d1 : env.Frame (top + 18446744073709551472#64) (Spec.Layout.Term.Out R1 S) S m1)
    (e1 : FormIn (env.next m) (env.next m1) m1 (top + 18446744073709551496#64) f1)
    (a1 : TermAlT.FormAl m1 (top + 18446744073709551496#64)) (r1 : R1 .x10 = top + 18446744073709551496#64)
    (d2 : env.Frame (top + 18446744073709551472#64) (Spec.Layout.Term.Out R2 m1) m1 m2)
    (e2 : FormIn (env.next m1) (env.next m2) m2 (top + 18446744073709551520#64) f2)
    (a2 : TermAlT.FormAl m2 (top + 18446744073709551520#64)) (r2 : R2 .x10 = top + 18446744073709551520#64) :
    env.Frame top Tactic.F m m2 ∧ SlotsAt m2 S top ∧
      (∀ R : Reg → Word, R .x2 = top + 18446744073709551472#64 → R .x10 = top + 18446744073709551472#64 →
        R .x11 = top + 18446744073709551496#64 → R .x12 = m2.getMem (top + 18446744073709551528#64) →
        R .x13 = m2.getMem (top + 18446744073709551536#64) → FormAddT.PreT env R m2) ∧
      Fresh40 m2 (top + 18446744073709551496#64) (env.next m).toNat (env.next m2).toNat := by
  have hlay := env.layout
  have htl := hW.top_le
  have hE := hW.heapEnd_le
  have hge := hW.next_ge
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t120 := top_sub (top := top) (c := 18446744073709551496#64) (k := 120) rfl (by omega)
  have t144 := top_sub (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have o1 : ∀ x : Word, Spec.Layout.Term.Out R1 S x → top.toNat - 120 ≤ x.toNat ∧ x.toNat < top.toNat - 96 :=
    fun x hx => by
      unfold Spec.Layout.Term.Out InRange at hx; rw [r1] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have o2 : ∀ x : Word, Spec.Layout.Term.Out R2 m1 x → top.toNat - 96 ≤ x.toNat ∧ x.toNat < top.toNat - 72 :=
    fun x hx => by
      unfold Spec.Layout.Term.Out InRange at hx; rw [r2] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have F1 : env.Frame top Tactic.F m m1 := hF0.trans d1 (by omega) fun x hx => .inl (by have := o1 x hx; omega)
  have F2 : env.Frame top Tactic.F m m2 := F1.trans d2 (by omega) fun x hx => .inl (by have := o2 x hx; omega)
  have hS : SlotsAt S S top := fun _ _ _ => rfl
  have S2 := (hS.thru d1 hlim fun x hx => by have := o1 x hx; omega).thru d2 hlim fun x hx => by
    have := o2 x hx; omega
  have n1 := F1.1
  have G1 : FormT env m1 (top + 18446744073709551496#64) :=
    TermAlT.formT_of e1 a1 hge (Nat.le_refl _) d1.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  obtain ⟨G1', p1, c1⟩ := form_thru d2 G1 (by omega) (by omega) fun x hx => by have := o2 x hx; omega
  have P2 : FormT env m2 (top + 18446744073709551520#64) :=
    TermAlT.formT_of e2 a2 (by omega) (Nat.le_refl _) d2.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have B1 := blk_of e1
  have n2 := d2.1
  refine ⟨F2, S2, fun R s2 s10 s11 s12 s13 => ?_, ?_⟩
  · refine add_pre (N := (env.next m1).toNat) ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩
      (.inl (by omega)) G1' P2 ?_ ((StateDerivedT.FormIn.terms e2).imp id (·.1)) s2 s10 s11
      (by rw [s12, StateDerivedT.add_add (d := 18446744073709551528#64) rfl]) (by
        rw [s13, StateDerivedT.add_add (d := 18446744073709551536#64) rfl])
    rw [p1, c1]
    rcases B1 with h | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  · unfold Fresh40
    rw [p1, c1]
    rcases B1 with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, by omega⟩

/-- **`add`'s result**: a `Form` whose whole block is `self`'s (fresh since `lo`) or allocated by the call. -/
theorem add_res {M M' : MachineState} {f : Word} {lo : Nat} {R r : Reg → Word}
    (h : APost env R M r M') (hF : env.Frame (R .x2) (FormAddT.OutT R M) M M')
    (hf : Fresh40 M (R .x11) lo (env.next M).toNat)
    (hlo : lo ≤ (env.next M).toNat) (hf' : R .x10 = f) :
    FormT env M' f ∧ Fresh40 M' f lo (env.next M').toNat := by
  unfold APost FormAddT.PostT at h
  rw [hf'] at h
  obtain ⟨G, hk⟩ := h
  refine ⟨G, ?_⟩
  have hc := cap_lt G
  have := hF.1
  unfold Fresh40 at hf ⊢
  rcases hc with h0 | hc
  · exact .inl h0
  rcases hk with ⟨hp, hcp⟩ | hk
  · rw [hp, hcp] at hc ⊢
    rcases hf with h0 | ⟨h1, -⟩
    · exact .inl h0
    · exact .inr ⟨h1, hc⟩
  · exact .inr ⟨by omega, hc⟩

/-- `add`'s writes, for a call from `top - 144` with its slots `s` and `f` there and `self`'s block fresh: on the
    stack below `top - 48`, or fresh since `m`. -/
theorem add_out {m M M' : MachineState} {top s f : Word} {R : Reg → Word}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hs1 : top.toNat - 144 ≤ s.toNat) (hs2 : s.toNat + 24 ≤ top.toNat - 48) (hf1 : top.toNat - 144 ≤ f.toNat)
    (hf2 : f.toNat + 24 ≤ top.toNat - 48) (r10 : R .x10 = s) (r11 : R .x11 = f)
    (hb : Fresh40 M f (env.next m).toNat (env.next M).toNat) (hn : (env.next M).toNat ≤ (env.next M').toNat) :
    ∀ x : Word, FormAddT.OutT R M x → (env.stackLimit.toNat ≤ x.toNat ∧ x.toNat < top.toNat - 48) ∨
      ((env.next m).toNat ≤ x.toNat ∧ x.toNat < (env.next M').toNat) := fun x hx => by
  unfold FormAddT.OutT InRange at hx
  rw [r10, r11] at hx
  rcases hx with hx | hx | hx
  · exact .inl (by omega)
  · exact .inl (by omega)
  · unfold Fresh40 at hb
    rcases hb with h0 | ⟨h1, h2⟩
    · rw [h0] at hx; omega
    · exact .inr (by omega)

/-- **Up to the second `add`**: the first `add` (`top - 144` the sum of the two at `top - 120` and `top - 96`), then
    `prod(flag, count, 0)` at `top - 96`. -/
theorem at4 {m S m2 m3 m4 : MachineState} {top : Word} {R3 R4 r3 : Reg → Word} {f4 : LeanVM.Protocol.Verifier.Form}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hF2 : env.Frame top Tactic.F m m2) (hS2 : SlotsAt m2 S top)
    (hb2 : Fresh40 m2 (top + 18446744073709551496#64) (env.next m).toNat (env.next m2).toNat)
    (d3 : env.Frame (top + 18446744073709551472#64) (FormAddT.OutT R3 m2) m2 m3) (p3 : APost env R3 m2 r3 m3)
    (q2 : R3 .x2 = top + 18446744073709551472#64) (q10 : R3 .x10 = top + 18446744073709551472#64)
    (q11 : R3 .x11 = top + 18446744073709551496#64)
    (d4 : env.Frame (top + 18446744073709551472#64) (Spec.Layout.Term.Out R4 m3) m3 m4)
    (e4 : FormIn (env.next m3) (env.next m4) m4 (top + 18446744073709551520#64) f4)
    (a4 : TermAlT.FormAl m4 (top + 18446744073709551520#64)) (r4 : R4 .x10 = top + 18446744073709551520#64) :
    env.Frame top Tactic.F m m4 ∧ SlotsAt m4 S top ∧
      (∀ R : Reg → Word, R .x2 = top + 18446744073709551472#64 → R .x10 = top + 18446744073709551496#64 →
        R .x11 = top + 18446744073709551472#64 → R .x12 = m4.getMem (top + 18446744073709551528#64) →
        R .x13 = m4.getMem (top + 18446744073709551536#64) → FormAddT.PreT env R m4) ∧
      Fresh40 m4 (top + 18446744073709551472#64) (env.next m).toNat (env.next m4).toNat := by
  have hlay := env.layout
  have htl := hW.top_le
  have hE := hW.heapEnd_le
  have hge := hW.next_ge
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t120 := top_sub (top := top) (c := 18446744073709551496#64) (k := 120) rfl (by omega)
  have t144 := top_sub (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have o3 := add_out (top := top) hlim (by omega) (by omega) (by omega) (by omega) q10 q11 hb2 d3.1
  have o4 : ∀ x : Word, Spec.Layout.Term.Out R4 m3 x → top.toNat - 96 ≤ x.toNat ∧ x.toNat < top.toNat - 72 :=
    fun x hx => by
      unfold Spec.Layout.Term.Out InRange at hx; rw [r4] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have n2 := hF2.1
  have F3 : env.Frame top Tactic.F m m3 := hF2.trans d3 (by omega) fun x hx => by
    rcases o3 x hx with h | h
    · exact .inl ⟨h.1, by omega⟩
    · exact .inr (.inl ⟨h.1, h.2⟩)
  have F4 : env.Frame top Tactic.F m m4 := F3.trans d4 (by omega) fun x hx => .inl (by have := o4 x hx; omega)
  have S4 := (hS2.thru d3 hlim fun x hx => by
    rcases o3 x hx with h | h
    · exact h.2
    · have := d3.2.1; omega).thru d4 hlim fun x hx => by have := o4 x hx; omega
  obtain ⟨G3, B3⟩ := add_res (lo := (env.next m).toNat) p3 (by rw [q2]; exact d3) (by rw [q11]; exact hb2)
    (by omega) q10
  obtain ⟨G3', p4, c4⟩ := form_thru d4 G3 (by omega) (by omega) fun x hx => by have := o4 x hx; omega
  have P4 : FormT env m4 (top + 18446744073709551520#64) :=
    TermAlT.formT_of e4 a4 (by have := F3.1; omega) (Nat.le_refl _) d4.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have n4 := d4.1
  refine ⟨F4, S4, fun R s2 s10 s11 s12 s13 => ?_, ?_⟩
  · refine add_pre (N := (env.next m3).toNat) ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩
      (.inr (by omega)) G3' P4 ?_ ((StateDerivedT.FormIn.terms e4).imp id (·.1)) s2 s10 s11
      (by rw [s12, StateDerivedT.add_add (d := 18446744073709551528#64) rfl]) (by
        rw [s13, StateDerivedT.add_add (d := 18446744073709551536#64) rfl])
    rw [p4, c4]
    rcases B3 with h | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  · unfold Fresh40 at B3 ⊢
    rw [p4, c4]
    rcases B3 with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, by omega⟩

/-- **Up to `counted`**: the second `add` (`top - 120` the sum of the two at `top - 144` and `top - 96`), then
    `constant(SEP_MEM)` at `top - 96`. -/
theorem at6 {m S m4 m5 m6 : MachineState} {top : Word} {R5 R6 r5 : Reg → Word} {f6 : LeanVM.Protocol.Verifier.Form}
    (hW : Windows env top m) (h16 : top.toNat % 16 = 0) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat)
    (hF4 : env.Frame top Tactic.F m m4) (hS4 : SlotsAt m4 S top)
    (hb4 : Fresh40 m4 (top + 18446744073709551472#64) (env.next m).toNat (env.next m4).toNat)
    (d5 : env.Frame (top + 18446744073709551472#64) (FormAddT.OutT R5 m4) m4 m5) (p5 : APost env R5 m4 r5 m5)
    (q2 : R5 .x2 = top + 18446744073709551472#64) (q10 : R5 .x10 = top + 18446744073709551496#64)
    (q11 : R5 .x11 = top + 18446744073709551472#64)
    (d6 : env.Frame (top + 18446744073709551472#64) (Spec.Layout.Term.Out R6 m5) m5 m6)
    (e6 : FormIn (env.next m5) (env.next m6) m6 (top + 18446744073709551520#64) f6)
    (a6 : TermAlT.FormAl m6 (top + 18446744073709551520#64)) (r6 : R6 .x10 = top + 18446744073709551520#64) :
    env.Frame top Tactic.F m m6 ∧ SlotsAt m6 S top ∧ FormT env m6 (top + 18446744073709551520#64) ∧
      FormT env m6 (top + 18446744073709551496#64) := by
  have hlay := env.layout
  have htl := hW.top_le
  have hE := hW.heapEnd_le
  have hge := hW.next_ge
  have t96 := top_sub (top := top) (c := 18446744073709551520#64) (k := 96) rfl (by omega)
  have t120 := top_sub (top := top) (c := 18446744073709551496#64) (k := 120) rfl (by omega)
  have t144 := top_sub (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
  have o5 := add_out (top := top) hlim (by omega) (by omega) (by omega) (by omega) q10 q11 hb4 d5.1
  have o6 : ∀ x : Word, Spec.Layout.Term.Out R6 m5 x → top.toNat - 96 ≤ x.toNat ∧ x.toNat < top.toNat - 72 :=
    fun x hx => by
      unfold Spec.Layout.Term.Out InRange at hx; rw [r6] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have n4 := hF4.1
  have F5 : env.Frame top Tactic.F m m5 := hF4.trans d5 (by omega) fun x hx => by
    rcases o5 x hx with h | h
    · exact .inl ⟨h.1, by omega⟩
    · exact .inr (.inl ⟨h.1, h.2⟩)
  have F6 : env.Frame top Tactic.F m m6 := F5.trans d6 (by omega) fun x hx => .inl (by have := o6 x hx; omega)
  have S6 := (hS4.thru d5 hlim fun x hx => by
    rcases o5 x hx with h | h
    · exact h.2
    · have := d5.2.1; omega).thru d6 hlim fun x hx => by have := o6 x hx; omega
  obtain ⟨G5, -⟩ := add_res (lo := (env.next m).toNat) p5 (by rw [q2]; exact d5) (by rw [q11]; exact hb4)
    (by omega) q10
  obtain ⟨G5', -, -⟩ := form_thru d6 G5 (by omega) (by omega) fun x hx => by have := o6 x hx; omega
  have C6 : FormT env m6 (top + 18446744073709551520#64) :=
    TermAlT.formT_of e6 a6 (by have := F5.1; omega) (Nat.le_refl _) d6.2.1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  exact ⟨F6, S6, C6, G5'⟩

/-- The prologue's stores keep the frame. -/
theorem saved_frame {m : MachineState} {top ret : Word} {regs : Reg → Word}
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) :
    env.Frame top Tactic.F m (saved m top ret regs) := by
  have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  exact Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
    (Tactic.frame_store (Tactic.frame_refl hnx) (by omega) (by omega)) (by omega) (by omega)) (by omega)
    (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)

/-- The copy's stores keep the frame. -/
theorem chain_frame {m M : MachineState} {top a : Word} (hF : env.Frame top Tactic.F m M)
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) : env.Frame top Tactic.F m (chain M top a) := by
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t56 := top_sub (top := top) (c := 18446744073709551560#64) (k := 56) rfl (by omega)
  exact Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF (by omega) (by omega)) (by omega) (by omega))
    (by omega) (by omega)

/-- **The saved words at the return.** -/
theorem saved_read {m M6 M7 : MachineState} {top ret a : Word} {regs : Reg → Word}
    (hlim : env.stackLimit.toNat + 144 ≤ top.toNat) (hS : SlotsAt M6 (saved m top ret regs) top)
    (k7 : ∀ x : Word, top.toNat - 48 ≤ x.toNat → x.toNat < top.toNat → M7.getMem x = (chain M6 top a).getMem x) :
    M7.getMem (top + 18446744073709551608#64) = ret ∧ M7.getMem (top + 18446744073709551600#64) = regs .x8 ∧
      M7.getMem (top + 18446744073709551592#64) = regs .x9 ∧ M7.getMem (top + 18446744073709551584#64) = regs .x18 ∧
      M7.getMem (top + 18446744073709551576#64) = regs .x19 ∧
      M7.getMem (top + 18446744073709551568#64) = regs .x20 := by
  have rd : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 48 →
      M7.getMem (top + c) = (saved m top ret regs).getMem (top + c) := fun c k hc h0 hk => by
    have := top_sub (top := top) hc (by omega)
    rw [k7 _ (by omega) (by omega), chain_get (by omega) (.inr (by omega))]
    exact hS _ (by omega) (by omega)
  have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
  have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
  have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
  have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have t48 := top_sub (top := top) (c := 18446744073709551568#64) (k := 48) rfl (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rd _ 8 rfl (by omega) (by omega)]; unfold saved; repeat rw [get_ne (by omega)]
    rw [MachineState.getMem_setMem_eq]
  · rw [rd _ 16 rfl (by omega) (by omega)]; unfold saved; repeat rw [get_ne (by omega)]
    rw [MachineState.getMem_setMem_eq]
  · rw [rd _ 24 rfl (by omega) (by omega)]; unfold saved; repeat rw [get_ne (by omega)]
    rw [MachineState.getMem_setMem_eq]
  · rw [rd _ 32 rfl (by omega) (by omega)]; unfold saved; repeat rw [get_ne (by omega)]
    rw [MachineState.getMem_setMem_eq]
  · rw [rd _ 40 rfl (by omega) (by omega)]; unfold saved; repeat rw [get_ne (by omega)]
    rw [MachineState.getMem_setMem_eq]
  · rw [rd _ 48 rfl (by omega) (by omega)]; unfold saved; rw [MachineState.getMem_setMem_eq]

/-- **The return, from `counted`'s**: the saved words, the frame and the postcondition. -/
theorem post {m M m3 : MachineState} {top : Word} {regs R' r3 : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hstk : env.stackLimit.toNat + 144 ≤ top.toNat) (hF : env.Frame top Tactic.F m M)
    (hFs : env.Frame (top + 18446744073709551472#64) (OutT R' M) M m3)
    (hP : KPost env R' M r3 m3) (s10 : R' .x10 = regs .x10) :
    (∀ x : Word, top.toNat - 48 ≤ x.toNat → x.toNat < top.toNat → m3.getMem x = M.getMem x) ∧
      env.Frame top (OutT regs m) m m3 ∧ ∀ r', StateDerivedT.PostT env regs m r' m3 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have t144 := top_sub (top := top) (c := 18446744073709551472#64) (k := 144) rfl (by omega)
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
  unfold KPost at hP
  exact hpost r3 r' m3 hP

set_option rv_sym.heap true in
/-- **`Flushes::memory_if` is total**, with 144 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needP needA needK : Nat} (hnK : 144 + Constant.need ≤ need) (hnC : 144 + needC ≤ need)
    (hnP : 144 + needP ≤ need) (hnA : 144 + needA ≤ need) (hnN : 144 + needK ≤ need)
    (hconst : ConstantAlT.specT env p L.constant.idx) (hcol : ColAlT.colSpecT env p L.col.idx needC)
    (hprod : ProdAlT.prodSpecT env p L.prod.idx needP) (hadd : FormAddT.SpecT env p L.add.idx needA)
    (hcnt : CountedT.SpecT env p L.counted.idx needK) : SpecT env p i need := by
  have hcnt' : HoldsT env p L.counted.idx needK (KPre env) (KPost env) OutT AbortStop := by
    unfold KPre KPost; exact hcnt
  have hadd' : HoldsT env p L.add.idx needA (APre env) (APost env) FormAddT.OutT AbortStop := by
    unfold APre APost; exact hadd
  suffices h : HoldsT env p i need (PreS env) (StateDerivedT.PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp with [hL, hnK, hnC, hnP, hnA, hnN]
    using [hconst (Model.ofLimbsW (2#64, 0#64)), hcol, hprod, hadd', hcnt']
  all_goals
    have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 144 ≤ top.toNat := by omega
    have htl := hpre_8.top_le
    have hE := hpre_8.heapEnd_le
    have hna := hpre_8.nextAddr_ge
    have hfw := hP.2.2.2.2.1.1.1
    have hfa : (regs .x12).toNat % 8 = 0 := hP.2.2.2.2.1.1.2.1.2.1
    unfold InWin at hfw
    simp only [Layouts.Vec.byteSize] at hfw
    have x8 : (regs .x12 + 8#64).toNat = (regs .x12).toNat + 8 := toNat_add_ofNat (by omega)
    have x16 : (regs .x12 + 16#64).toNat = (regs .x12).toNat + 16 := toNat_add_ofNat (by omega)
  all_goals try (rw [inWindow_iff]; omega)
  all_goals try omega
  all_goals
    obtain ⟨F2, S2, A1, B2⟩ := at2 hpre_8 hpre_7 hlim (saved_frame (ret := ret) (regs := regs) hpre_5 hlim)
      hret1_14 hret1_16 ⟨hret1_17, hret1_18⟩ rfl hret2_14 hret2_16 ⟨hret2_17, hret2_18⟩ rfl
  · unfold APre; exact A1 _ rfl rfl rfl rfl rfl
  all_goals
    obtain ⟨F4, S4, A2, B4⟩ := at4 hpre_8 hpre_7 hlim F2 S2 B2 hret3_14 hret3_16 rfl rfl rfl hret4_14 hret4_16
      ⟨hret4_17, hret4_18⟩ rfl
  · unfold APre; exact A2 _ rfl rfl rfl rfl rfl
  all_goals
    obtain ⟨F6, S6, C6, G6⟩ := at6 hpre_8 hpre_7 hlim F4 S4 B4 hret5_14 hret5_16 rfl rfl rfl hret6_14 hret6_16
      ⟨hret6_17, hret6_18⟩ rfl
  · unfold KPre
    refine (cnt_pre hP hpre_2 hpre_8 hpre_7 hlim F6 C6 G6 ?_ ?_ ?_ ?_ ?_ ?_).1
    all_goals rfl
  all_goals
    obtain ⟨k7, F7, hPost⟩ := post hP hpre_2 hpre_8 hlim (chain_frame F6 hlim) hret7_14 hret7_16 rfl
    obtain ⟨s8, s16, s24, s32, s40, s48⟩ := saved_read hlim S6 k7
  · exact s8
  · exact ⟨⟨rfl, s16, s24, s32, s40, s48, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, F7, hret7_15, hPost _⟩

end Rv64mc.Proof.Layout.MemoryIfT

/-- info: 'Rv64mc.Proof.Layout.MemoryIfT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.MemoryIfT.total
