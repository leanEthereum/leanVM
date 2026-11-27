/-
  Rv64mc.Proof.Layout.MemoryT

  `Flushes::memory(&mut self, address, count, values)` is total over a `Flushes` of `Form`s
  (`PairFormT.FlushesFormT`): it builds `constant(SEP_MEM)` (`ConstantAlT`, the limbs `(2, 0)`) at `sp`, copies
  `address` (`a1`, a `Form` header) after it, builds `col(count, 1)` (`ColAlT`) at `sp + 0x30`, and calls
  `Flushes::counted(self, [constant, address], counter, count, values)` (`CountedT`). The `Flushes` stays a `Flushes`
  of `Form`s, each vector one longer, each buffer the entry's or allocated since (`StateDerivedT.PostT`, `counted`'s);
  it writes what `pair` writes (`PairT.OutT`) besides its stack and fresh blocks. A safety-only contract (class D).

  The precondition: `self` `PairT.FlushesT`, 8-byte aligned, a `Flushes` of `Form`s; `address` a `Form`
  (`FormReprT.FormT`) in a caller's frame (`StackObj`); `values` a slice of two `Form`s
  (`ConcatFormT.SliceFT`). `counted`'s precondition at its call is `cnt_pre`: the prefix's two `Form`s are
  `constant`'s (`TermAlT.formT_of`) and `address`'s header moved (`StateDerivedT.FormT.move`); `counted`'s
  precondition and postcondition (`KPre`, `KPost`) and this function's own precondition (`PreS`) are sealed, so
  that the executor's arithmetic does not unfold them.

  ## Main definitions

  * `PreT`, `SpecT`, `chain`

  ## Main results

  * `frame2`, `cnt_pre`, `post`, `total`
-/

import Rv64mc.Proof.Layout.CountedT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.Memory

namespace Rv64mc.Proof.Layout.MemoryT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Layout.FormReprT (FormT)
open Rv64mc.Proof.Layout.PairT (FlushesT OutT)
open Rv64mc.Proof.Layout.PairFormT (FlushesFormT)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Layout.ConcatFormT (SliceFT)
open Rv64mc.Proof.Layout.StateDerivedT (get_ne top_sub fkeep)
open Rv64mc.Gen.Verifier.Layout.Flushes.Memory (Link tmpl)

variable {env : Env}

/-- The total precondition: `self` (`a0`) `PairT.FlushesT`, aligned, a `Flushes` of `Form`s; `address` (`a1`) a
    `Form` in a caller's frame; `values` (`a3`) a slice of two `Form`s. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧ FlushesFormT env m (regs .x10) ∧
    StackObj (regs .x2) (regs .x11) 24 ∧ FormT env m (regs .x11) ∧ SliceFT env m (regs .x2) (regs .x13) 2#64

/-- **The total contract of `Flushes::memory`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (StateDerivedT.PostT env) OutT AbortStop

/-- The precondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl

/-- `counted`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def KPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := CountedT.PreT env regs m

/-- `counted`'s postcondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def KPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  StateDerivedT.PostT env regs m r' m'

/-- The `address` header's three words copied to `top - 88`, after `constant`. -/
def chain (M : MachineState) (top a : Word) : MachineState :=
  ((M.setMem (top + 18446744073709551528#64) (M.getMem a)).setMem (top + 18446744073709551536#64)
    (M.getMem (a + 8#64))).setMem (top + 18446744073709551544#64) (M.getMem (a + 16#64))

/-- Reads past the copy. -/
theorem chain_get {M : MachineState} {top a x : Word} (h112 : 112 ≤ top.toNat)
    (hx : x.toNat < top.toNat - 88 ∨ top.toNat - 64 ≤ x.toNat) : (chain M top a).getMem x = M.getMem x := by
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t80 := top_sub (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  unfold chain
  rw [get_ne (by omega), get_ne (by omega), get_ne (by omega)]

/-- The `address` header's words at `top - 88`. -/
theorem chain_hdr {M : MachineState} {top a : Word} (h112 : 112 ≤ top.toNat) :
    (chain M top a).getMem (top + 18446744073709551528#64) = M.getMem a ∧
      (chain M top a).getMem (top + 18446744073709551536#64) = M.getMem (a + 8#64) ∧
      (chain M top a).getMem (top + 18446744073709551544#64) = M.getMem (a + 16#64) := by
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t80 := top_sub (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  unfold chain
  refine ⟨?_, ?_, ?_⟩
  · rw [get_ne (by omega), get_ne (by omega), MachineState.getMem_setMem_eq]
  · rw [get_ne (by omega), MachineState.getMem_setMem_eq]
  · rw [MachineState.getMem_setMem_eq]

/-- The frame up to `counted`'s call: `constant`'s, the copy at `top - 88`, `col`'s at `top - 64`. -/
theorem frame2 {m M1 M2 : MachineState} {top a : Word} {R2 : Reg → Word}
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top Tactic.F m M1)
    (d1 : env.Frame (top + 18446744073709551504#64) (Spec.Layout.Term.Out R2 (chain M1 top a)) (chain M1 top a) M2)
    (r2 : R2 .x10 = top + 18446744073709551552#64) : env.Frame top Tactic.F m M2 := by
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t80 := top_sub (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have FC : env.Frame top Tactic.F m (chain M1 top a) :=
    Tactic.frame_store (Tactic.frame_store (Tactic.frame_store hF (by omega) (by omega)) (by omega) (by omega))
      (by omega) (by omega)
  exact FC.trans d1 (by omega) fun x hx => .inl (by
    unfold Spec.Layout.Term.Out InRange at hx; rw [r2] at hx; simp only [Layouts.Form.byteSize] at hx; omega)

/-- **`counted`'s precondition at its call**: the prefix `[constant(SEP_MEM), address]` at `top - 112`, `col`'s
    counter at `top - 64`, `values` as at the entry. -/
theorem cnt_pre {m M1 M2 : MachineState} {top : Word} {regs R2 R' : Reg → Word}
    {f1 f2 : LeanVM.Protocol.Verifier.Form}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top Tactic.F m M1)
    (c1 : FormIn (env.next m) (env.next M1) M1 (top + 18446744073709551504#64) f1)
    (c2 : TermAlT.FormAl M1 (top + 18446744073709551504#64))
    (d1 : env.Frame (top + 18446744073709551504#64) (Spec.Layout.Term.Out R2 (chain M1 top (regs .x11)))
      (chain M1 top (regs .x11)) M2)
    (d2 : FormIn (env.next M1) (env.next M2) M2 (top + 18446744073709551552#64) f2)
    (d3 : TermAlT.FormAl M2 (top + 18446744073709551552#64))
    (r2 : R2 .x10 = top + 18446744073709551552#64)
    (s2 : R' .x2 = top + 18446744073709551504#64) (s10 : R' .x10 = regs .x10)
    (s11 : R' .x11 = top + 18446744073709551504#64) (s12 : R' .x12 = top + 18446744073709551552#64)
    (s14 : R' .x14 = regs .x13) (s15 : R' .x15 = 2#64) : CountedT.PreT env R' M2 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, hBA⟩, hal, hFF, ⟨ho1, ho2⟩, hfa, hsv⟩ := hpre
  rw [h2] at ha1 ho1 hsv
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have t88 := top_sub (top := top) (c := 18446744073709551528#64) (k := 88) rfl (by omega)
  have t80 := top_sub (top := top) (c := 18446744073709551536#64) (k := 80) rfl (by omega)
  have t72 := top_sub (top := top) (c := 18446744073709551544#64) (k := 72) rfl (by omega)
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have n1 := hF.1
  have x1 := hF.2.1
  have nC : env.next (chain M1 top (regs .x11)) = env.next M1 := chain_get (by omega) (.inl (by omega))
  have n2 := d1.1
  have x2 := d1.2.1
  rw [nC] at n2
  have o2 : ∀ x : Word, Spec.Layout.Term.Out R2 (chain M1 top (regs .x11)) x →
      top.toNat - 64 ≤ x.toNat ∧ x.toNat < top.toNat - 40 := fun x hx => by
    unfold Spec.Layout.Term.Out InRange at hx; rw [r2] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have k12 : ∀ x : Word, (x.toNat < (env.next M1).toNat ∨ (top.toNat - 112 ≤ x.toNat ∧
      (x.toNat < top.toNat - 88 ∨ top.toNat - 40 ≤ x.toNat))) → M2.getMem x = M1.getMem x := fun x hx => by
    have hna : x ≠ env.nextAddr := fun e => by rw [e] at hx; omega
    rw [fkeep d1 (by omega) (by rw [nC]; omega) hna (fun h => by have := o2 x h; omega), chain_get (by omega)
      (by omega)]
  have F2 := frame2 hstk hF d1 r2
  have k02 : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M2.getMem x = m.getMem x :=
    fun x hx => F2.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at hx; omega
      · exact hw
  obtain ⟨hFF2, -⟩ := StateDerivedT.FlushesFormT.keep hFF (by omega) (fun b hb => k02 b (.inl hb))
    fun b h1 h2 => k02 b (.inr (by omega))
  -- `constant`'s `Form` at `top - 112`
  have G1 : FormT env M1 (top + 18446744073709551504#64) :=
    TermAlT.formT_of c1 c2 hge (Nat.le_refl _) x1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have hb1 := G1.foot
  have G1' : FormT env M2 (top + 18446744073709551504#64) := FormReprT.FormT.keep G1 n2
    (fun x l1 l2 => k12 x (.inr ⟨by omega, .inl (by omega)⟩)) fun x l1 l2 => k12 x (.inl (by
      rcases hb1 with h | ⟨-, h, -⟩ <;> omega))
  -- `address` copied to `top - 88`
  obtain ⟨w0, w8, w16⟩ := chain_hdr (M := M1) (a := regs .x11) (top := top) (by omega)
  have hfw := hfa.1.1
  unfold InWin at hfw
  simp only [Layouts.Vec.byteSize] at hfw
  have k1a : ∀ k, k ≤ 16 → M1.getMem (regs .x11 + BitVec.ofNat 64 k) = m.getMem (regs .x11 + BitVec.ofNat 64 k) :=
    fun k hk => hF.2.2 _ fun hw => by
      have e : (regs .x11 + BitVec.ofNat 64 k).toNat = (regs .x11).toNat + k := toNat_add_ofNat (by omega)
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at e; omega
      · exact hw
  have k2c : ∀ x : Word, top.toNat - 88 ≤ x.toNat → x.toNat < top.toNat - 64 →
      M2.getMem x = (chain M1 top (regs .x11)).getMem x := fun x l1 l2 => by
    have hna : x ≠ env.nextAddr := fun e => by rw [e] at l1; omega
    exact fkeep d1 (by omega) (by rw [nC]; omega) hna (fun h => by have := o2 x h; omega)
  have e88 : ∀ k, k ≤ 16 → (top + 18446744073709551528#64 + BitVec.ofNat 64 k).toNat = top.toNat - 88 + k :=
    fun k hk => by rw [toNat_add_ofNat (by omega), t88]
  obtain ⟨G2, -, -⟩ := StateDerivedT.FormT.move (d := top + 18446744073709551528#64) hfa (by omega)
    (.inr ⟨by omega, by omega⟩) (by omega)
    (by rw [k2c _ (by omega) (by omega), w0]; simpa using k1a 0 (by omega))
    (by
      rw [StateDerivedT.add_add (d := 18446744073709551536#64) rfl, k2c _ (by omega) (by omega), w8]; exact k1a 8 (by omega))
    (by
      rw [StateDerivedT.add_add (d := 18446744073709551544#64) rfl, k2c _ (by omega) (by omega), w16]; exact k1a 16 (by omega))
    fun x l1 l2 => k02 x (.inl (by rcases hfa.foot with h | ⟨-, h, -⟩ <;> omega))
  have G3 : FormT env M2 (top + 18446744073709551552#64) :=
    TermAlT.formT_of d2 d3 (by omega) (Nat.le_refl _) x2 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have two : (2#64).toNat = 2 := rfl
  unfold CountedT.PreT PairT.FlushesT
  rw [s2, s10, s11, s12, s14, s15]
  refine ⟨⟨hFF2.1, hFF2.2.1, ⟨by omega, ha2⟩, hFF2.2.2.1⟩, hal, hFF2,
    .inr ⟨by rw [two]; exact .inr ⟨by omega, by omega⟩, .inr (Nat.le_refl _), fun i hi => ?_⟩,
    ⟨by omega, by omega⟩, G3, CountedT.SliceFT.keep hsv (by omega) F2 (by omega)⟩
  rw [two] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa using G1'
  · rw [StateDerivedT.add_add (d := 18446744073709551528#64) rfl]; exact G2

/-- **The return, from `counted`'s**: the saved words, the frame and the postcondition. -/
theorem post {m M2 m3 : MachineState} {top : Word} {regs R' r3 : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hstk : env.stackLimit.toNat + 112 ≤ top.toNat) (hF : env.Frame top Tactic.F m M2)
    (hFs : env.Frame (top + 18446744073709551504#64) (OutT R' M2) M2 m3)
    (hP : KPost env R' M2 r3 m3) (s10 : R' .x10 = regs .x10) :
    (∀ x : Word, top.toNat - 40 ≤ x.toNat → x.toNat < top.toNat → m3.getMem x = M2.getMem x) ∧
      env.Frame top (OutT regs m) m m3 ∧ ∀ r', StateDerivedT.PostT env regs m r' m3 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
  have kM : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M2.getMem x = m.getMem x :=
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
/-- **`Flushes::memory` is total**, with 112 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needK : Nat} (hnK : 112 + Constant.need ≤ need) (hnC : 112 + needC ≤ need)
    (hnN : 112 + needK ≤ need)
    (hconst : ConstantAlT.specT env p L.constant.idx) (hcol : ColAlT.colSpecT env p L.col.idx needC)
    (hcnt : CountedT.SpecT env p L.counted.idx needK) : SpecT env p i need := by
  have hcnt' : HoldsT env p L.counted.idx needK (KPre env) (KPost env) OutT AbortStop := by
    unfold KPre KPost; exact hcnt
  suffices h : HoldsT env p i need (PreS env) (StateDerivedT.PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp with [hL, hnK, hnC, hnN] using [hconst (Model.ofLimbsW (2#64, 0#64)), hcol, hcnt']
  all_goals
    have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 112 ≤ top.toNat := by omega
    have hfw := hP.2.2.2.2.1.1.1
    have hfa := hP.2.2.2.2.1.1.2.1.2.1
    unfold InWin at hfw
    simp only [Layouts.Vec.byteSize] at hfw
    have htl := hpre_8.top_le
    have hE := hpre_8.heapEnd_le
    have hna := hpre_8.nextAddr_ge
    have x8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
    have x16 : (regs .x11 + 16#64).toNat = (regs .x11).toNat + 16 := toNat_add_ofNat (by omega)
  all_goals try (rw [inWindow_iff]; omega)
  all_goals try omega
  all_goals
    have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
    have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
    have t24 := top_sub (top := top) (c := 18446744073709551592#64) (k := 24) rfl (by omega)
    have t32 := top_sub (top := top) (c := 18446744073709551584#64) (k := 32) rfl (by omega)
    have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
    have t112 := top_sub (top := top) (c := 18446744073709551504#64) (k := 112) rfl (by omega)
    have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
    have F0 : env.Frame top Tactic.F m (((((m.setMem (top + 18446744073709551608#64) ret).setMem
        (top + 18446744073709551600#64) (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem
        (top + 18446744073709551584#64) (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19)) :=
      Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
        (Tactic.frame_refl hpre_5) (by omega) (by omega)) (by omega) (by omega)) (by omega) (by omega)) (by omega)
        (by omega)) (by omega) (by omega)
    have F1 : env.Frame top Tactic.F m m1 := F0.trans hret1_14 (by omega) fun x hx => .inl (by
      unfold Spec.Layout.Term.Out InRange at hx
      simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Form.byteSize] at hx
      omega)
    have F2 := frame2 hlim F1 hret2_14 rfl
  · unfold KPre
    exact cnt_pre hP hpre_2 hpre_8 hpre_7 hlim F1 hret1_16 ⟨hret1_17, hret1_18⟩ hret2_14 hret2_16
      ⟨hret2_17, hret2_18⟩ rfl rfl rfl rfl rfl rfl rfl
  all_goals
    obtain ⟨k3, F3, hPost⟩ := post hP hpre_2 hpre_8 hlim F2 hret3_14 hret3_16 rfl
    have o1 : ∀ x : Word, top.toNat - 40 ≤ x.toNat → x.toNat < top.toNat → ¬ Spec.Layout.Term.Out
        (updReg (Tactic.rf (regs .x0) L.s0.hi (top + 18446744073709551504#64) (regs .x3) (regs .x4) (regs .x5)
          (regs .x6) (regs .x7) (regs .x13) (regs .x12) (top + 18446744073709551504#64) 2#64 0#64 (regs .x13)
          (regs .x14) (regs .x15) (regs .x16) (regs .x17) (regs .x11) (regs .x10) (regs .x20) (regs .x21) (regs .x22)
          (regs .x23) (regs .x24) (regs .x25) (regs .x26) (regs .x27) (regs .x28) (regs .x29) (regs .x30) (regs .x31))
          .x1 (L.base + 60#64)) m x := fun x l1 l2 hx => by
      unfold Spec.Layout.Term.Out InRange at hx
      simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Form.byteSize] at hx
      omega
    have s : ∀ x : Word, top.toNat - 40 ≤ x.toNat → x.toNat < top.toNat → m3.getMem x =
        ((((((m.setMem (top + 18446744073709551608#64) ret).setMem
        (top + 18446744073709551600#64) (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem
        (top + 18446744073709551584#64) (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19))).getMem x :=
      fun x l1 l2 => by
        have hna : x ≠ env.nextAddr := fun e => by rw [e] at l1; omega
        have := hret1_14.2.1
        have := hret2_14.2.1
        rw [k3 x l1 l2, fkeep hret2_14 (by omega) (.inr (by omega)) hna (fun h => by
            unfold Spec.Layout.Term.Out InRange at h
            simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Form.byteSize] at h
            omega)]
        refine (chain_get (M := m1) (top := top) (a := regs .x11) (by omega) (.inr (by omega))).trans ?_
        rw [fkeep hret1_14 (by omega) (.inr (by omega)) hna (o1 x l1 l2)]
    have rd : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 40 → m3.getMem (top + c) =
        ((((((m.setMem (top + 18446744073709551608#64) ret).setMem
        (top + 18446744073709551600#64) (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9)).setMem
        (top + 18446744073709551584#64) (regs .x18)).setMem (top + 18446744073709551576#64) (regs .x19))).getMem
          (top + c) := fun c k hc h0 hk => by
      have := top_sub (top := top) hc (by omega)
      exact s _ (by omega) (by omega)
    have s8 : m3.getMem (top + 18446744073709551608#64) = ret := by
      rw [rd _ 8 rfl (by omega) (by omega)]
      repeat rw [get_ne (by omega)]
      rw [MachineState.getMem_setMem_eq]
    have s16 : m3.getMem (top + 18446744073709551600#64) = regs .x8 := by
      rw [rd _ 16 rfl (by omega) (by omega)]
      repeat rw [get_ne (by omega)]
      rw [MachineState.getMem_setMem_eq]
    have s24 : m3.getMem (top + 18446744073709551592#64) = regs .x9 := by
      rw [rd _ 24 rfl (by omega) (by omega)]
      repeat rw [get_ne (by omega)]
      rw [MachineState.getMem_setMem_eq]
    have s32 : m3.getMem (top + 18446744073709551584#64) = regs .x18 := by
      rw [rd _ 32 rfl (by omega) (by omega)]
      repeat rw [get_ne (by omega)]
      rw [MachineState.getMem_setMem_eq]
    have s40 : m3.getMem (top + 18446744073709551576#64) = regs .x19 := by
      rw [rd _ 40 rfl (by omega) (by omega), MachineState.getMem_setMem_eq]
  · exact s8
  · exact ⟨⟨rfl, s16, s24, s32, s40, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, F3, hret3_15, hPost _⟩

end Rv64mc.Proof.Layout.MemoryT

/-- info: 'Rv64mc.Proof.Layout.MemoryT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.MemoryT.total
