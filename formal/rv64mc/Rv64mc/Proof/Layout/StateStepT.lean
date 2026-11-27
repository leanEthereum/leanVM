/-
  Rv64mc.Proof.Layout.StateStepT

  `Flushes::state_step(&mut self, pc, fp)` is total over a `Flushes` of `Form`s (`PairFormT.FlushesFormT`): it builds
  `col(pc, 1)` and `col(fp, 0)` in its frame (the image passes `pc = 0`, `fp = 1`; `ColAlT`) and calls
  `Flushes::state_derived` with them (`StateDerivedT`). The `Flushes` stays a `Flushes` of `Form`s, each vector one
  longer, each buffer the entry's or allocated since (`StateDerivedT.PostT`); it writes what `pair` writes
  (`PairT.OutT`) besides its stack and fresh blocks.

  The precondition: `self` `PairT.FlushesT`, 8-byte aligned, a `Flushes` of `Form`s. The two `col`s' `Form`s are
  `FormT` (`TermAlT.formT_of`) and their terms' blocks, allocated after the entry, avoid both buffers
  (`StateDerivedT.off_of_ge`), which is `state_derived`'s precondition (`sd_pre`). `state_derived`'s precondition
  and postcondition are sealed (`SPre`, `SPost`), and so is this function's own precondition (`PreS`), so that the
  executor's arithmetic does not unfold them.

  ## Main definitions

  * `PreT`, `SpecT`

  ## Main results

  * `sd_pre`, `post`, `total`
-/

import Rv64mc.Proof.Layout.StateDerivedT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Flushes.StateStep

namespace Rv64mc.Proof.Layout.StateStepT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Runtime Rv64mc.Spec.Layout
open Rv64mc.Proof.Runtime.VecHdrT (vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FormReprT (FormT)
open Rv64mc.Proof.Layout.PairT (FlushesT OutT)
open Rv64mc.Proof.Layout.PairFormT (FlushesFormT)
open Rv64mc.Proof.Layout.StateDerivedT (off_of_ge get_ne top_sub fkeep From)
open Rv64mc.Gen.Verifier.Layout.Flushes.StateStep (Link tmpl)

variable {env : Env}

/-- The total precondition: `self` (`a0`) `PairT.FlushesT`, aligned, a `Flushes` of `Form`s. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  FlushesT env m (regs .x2) (regs .x10) ∧ (regs .x10).toNat % 8 = 0 ∧ FlushesFormT env m (regs .x10)

/-- **The total contract of `Flushes::state_step`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (StateDerivedT.PostT env) OutT AbortStop

/-- The precondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def PreS (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := PreT env regs m

theorem preS_eq : PreS env = PreT env := by unfold PreS; rfl

/-- `state_derived`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def SPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := StateDerivedT.PreT env regs m

/-- `state_derived`'s postcondition, sealed so that the executor keeps it as one hypothesis. -/
@[irreducible] def SPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) :
    Prop :=
  StateDerivedT.PostT env regs m r' m'

/-- `self`'s words kept by a memory agreeing at and above the stack top, `self` there. -/
theorem self_words {m M : MachineState} {top a : Word} (ha : top.toNat ≤ a.toNat) (ha2 : a.toNat + 48 ≤ 0xc0000000)
    (hk : ∀ x : Word, top.toNat ≤ x.toNat → M.getMem x = m.getMem x) :
    ∀ k, k ≤ 40 → M.getMem (a + BitVec.ofNat 64 k) = m.getMem (a + BitVec.ofNat 64 k) := fun k hk' =>
  hk _ (by rw [toNat_add_ofNat (by omega)]; omega)

/-- **`state_derived`'s precondition at its call**, from the two `col`s' results. -/
theorem sd_pre {m M1 M2 : MachineState} {top : Word} {regs R2 R' : Reg → Word}
    {f1 f2 : LeanVM.Protocol.Verifier.Form}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m) (h16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + 64 ≤ top.toNat) (hF : env.Frame top Tactic.F m M1)
    (c1 : FormIn (env.next m) (env.next M1) M1 (top + 18446744073709551552#64) f1)
    (c2 : TermAlT.FormAl M1 (top + 18446744073709551552#64))
    (d1 : env.Frame (top + 18446744073709551552#64) (Spec.Layout.Term.Out R2 M1) M1 M2)
    (d2 : FormIn (env.next M1) (env.next M2) M2 (top + 18446744073709551576#64) f2)
    (d3 : TermAlT.FormAl M2 (top + 18446744073709551576#64))
    (r2 : R2 .x10 = top + 18446744073709551576#64)
    (s2 : R' .x2 = top + 18446744073709551552#64) (s10 : R' .x10 = regs .x10)
    (s11 : R' .x11 = top + 18446744073709551552#64) (s12 : R' .x12 = top + 18446744073709551576#64) :
    StateDerivedT.PreT env R' M2 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, hBA⟩, hal, hFF⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have hE := hW.heapEnd_le
  have htl := hW.top_le
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
  have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
  have n1 := hF.1
  have x1 := hF.2.1
  have n2 := d1.1
  have x2 := d1.2.1
  have o2 : ∀ x : Word, Spec.Layout.Term.Out R2 M1 x → top.toNat - 40 ≤ x.toNat ∧ x.toNat < top.toNat - 16 :=
    fun x hx => by
      unfold Spec.Layout.Term.Out InRange at hx; rw [r2] at hx; simp only [Layouts.Form.byteSize] at hx; omega
  have k12 : ∀ x : Word, (x.toNat < (env.next M1).toNat ∨ (top.toNat - 64 ≤ x.toNat ∧
      (x.toNat < top.toNat - 40 ∨ top.toNat - 16 ≤ x.toNat))) → M2.getMem x = M1.getMem x := fun x hx => by
    have hna : x ≠ env.nextAddr := fun e => by rw [e] at hx; omega
    exact fkeep d1 (by omega) (by omega) hna (fun h => by have := o2 x h; omega)
  have k01 : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M1.getMem x = m.getMem x :=
    fun x hx => hF.2.2 x fun hw => by
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at hx; omega
      · exact hw
  have k02 : ∀ x : Word, (x.toNat < (env.next m).toNat ∨ top.toNat ≤ x.toNat) → M2.getMem x = m.getMem x :=
    fun x hx => by rw [k12 x (by omega), k01 x hx]
  obtain ⟨hFF2, hoff⟩ := StateDerivedT.FlushesFormT.keep hFF (by omega) (fun b hb => k02 b (.inl hb))
    fun b h1 h2 => k02 b (.inr (by omega))
  have G1 : FormT env M1 (top + 18446744073709551552#64) :=
    TermAlT.formT_of c1 c2 hge (Nat.le_refl _) x1 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have f1 := StateDerivedT.FormIn.terms c1
  have e64 : ∀ k, k ≤ 16 → (top + 18446744073709551552#64 + BitVec.ofNat 64 k).toNat = top.toNat - 64 + k :=
    fun k hk => by rw [toNat_add_ofNat (by omega), t64]
  have k64 : ∀ k, k ≤ 16 → M2.getMem (top + 18446744073709551552#64 + BitVec.ofNat 64 k) =
      M1.getMem (top + 18446744073709551552#64 + BitVec.ofNat 64 k) :=
    fun k hk => k12 _ (.inr ⟨by rw [e64 k hk]; omega, .inl (by rw [e64 k hk]; omega)⟩)
  have p1 : vecPtr M2 (top + 18446744073709551552#64) = vecPtr M1 (top + 18446744073709551552#64) := by
    rw [vecPtr_eq, vecPtr_eq]; exact k64 8 (by omega)
  have l1 : vecLen M2 (top + 18446744073709551552#64) = vecLen M1 (top + 18446744073709551552#64) := by
    rw [vecLen_eq, vecLen_eq]; exact k64 16 (by omega)
  have hb1 := G1.foot
  have G1' : FormT env M2 (top + 18446744073709551552#64) := FormReprT.FormT.keep G1 n2
    (fun x l1 l2 => k12 x (.inr ⟨by omega, .inl (by omega)⟩)) fun x l1 l2 => k12 x (.inl (by
      rcases hb1 with h | ⟨-, h, -⟩ <;> omega))
  have G2 : FormT env M2 (top + 18446744073709551576#64) :=
    TermAlT.formT_of d2 d3 (by omega) (Nat.le_refl _) x2 hE (.inr ⟨by omega, by omega⟩) (by omega)
  have f2 := StateDerivedT.FormIn.terms d2
  have from1 : From M2 (top + 18446744073709551552#64) (env.next m).toNat := by
    unfold From; rw [p1, l1]; rcases f1 with h | h <;> omega
  have from2 : From M2 (top + 18446744073709551576#64) (env.next m).toNat := by
    unfold From; rcases f2 with h | h <;> omega
  unfold StateDerivedT.PreT PairT.FlushesT
  rw [s2, s10, s11, s12]
  exact ⟨⟨hFF2.1, hFF2.2.1, ⟨by omega, ha2⟩, hFF2.2.2.1⟩, hal, hFF2, ⟨Nat.le_refl _, by omega⟩,
    ⟨by omega, by omega⟩, G1', G2, StateDerivedT.terms_off hV1 hV2 hoff from1 (Nat.le_refl _),
    StateDerivedT.terms_off hV1 hV2 hoff from2 (Nat.le_refl _)⟩

/-- **The return, from `state_derived`'s**: the frame and the postcondition. -/
theorem post {m M2 m3 : MachineState} {top : Word} {regs R' r3 : Reg → Word}
    (hpre : PreT env regs m) (h2 : regs .x2 = top) (hW : Windows env top m)
    (hstk : env.stackLimit.toNat + 64 ≤ top.toNat) (hF : env.Frame top Tactic.F m M2)
    (hFs : env.Frame (top + 18446744073709551552#64) (OutT R' M2) M2 m3)
    (hP : SPost env R' M2 r3 m3) (s10 : R' .x10 = regs .x10) :
    (∀ x : Word, top.toNat - 16 ≤ x.toNat → x.toNat < top.toNat → m3.getMem x = M2.getMem x) ∧
      env.Frame top (OutT regs m) m m3 ∧ ∀ r', StateDerivedT.PostT env regs m r' m3 := by
  obtain ⟨⟨hV1, hV2, ⟨ha1, ha2⟩, -⟩, -, -⟩ := hpre
  rw [h2] at ha1
  have hlay := env.layout
  have hge := hW.next_ge
  have htl := hW.top_le
  have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
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
  unfold SPost at hP
  exact hpost r3 r' m3 hP

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needC needS : Nat} (hnC : 64 + needC ≤ need) (hnS : 64 + needS ≤ need)
    (hcol : ColAlT.colSpecT env p L.col.idx needC) (hsd : StateDerivedT.SpecT env p L.stateDerived.idx needS) :
    SpecT env p i need := by
  have hsd' : HoldsT env p L.stateDerived.idx needS (SPre env) (SPost env) OutT AbortStop := by
    unfold SPre SPost; exact hsd
  suffices h : HoldsT env p i need (PreS env) (StateDerivedT.PostT env) OutT AbortStop by rwa [preS_eq] at h
  rv_autoT hp with [hL, hnC, hnS] using [hcol, hsd']
  all_goals
    have hP : PreT env regs m := by rw [← preS_eq]; exact hpre_6
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
    have t8 := top_sub (top := top) (c := 18446744073709551608#64) (k := 8) rfl (by omega)
    have t16 := top_sub (top := top) (c := 18446744073709551600#64) (k := 16) rfl (by omega)
    have t40 := top_sub (top := top) (c := 18446744073709551576#64) (k := 40) rfl (by omega)
    have t64 := top_sub (top := top) (c := 18446744073709551552#64) (k := 64) rfl (by omega)
    have F0 : env.Frame top Tactic.F m ((m.setMem (top + 18446744073709551608#64) ret).setMem
        (top + 18446744073709551600#64) (regs .x8)) :=
      Tactic.frame_store (Tactic.frame_store (Tactic.frame_refl hpre_5) (by omega) (by omega)) (by omega) (by omega)
    have F1 : env.Frame top Tactic.F m m1 := F0.trans hret1_14 (by omega) fun x hx => .inl (by
      unfold Spec.Layout.Term.Out InRange at hx
      simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Form.byteSize] at hx
      omega)
  · unfold SPre
    exact sd_pre hP hpre_2 hpre_8 hpre_7 hlim F1 hret1_16 ⟨hret1_17, hret1_18⟩ hret2_14 hret2_16
      ⟨hret2_17, hret2_18⟩ rfl rfl rfl rfl rfl
  all_goals
    have F2 : env.Frame top Tactic.F m m2 := F1.trans hret2_14 (by omega) fun x hx => .inl (by
      unfold Spec.Layout.Term.Out InRange at hx
      simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false, Layouts.Form.byteSize] at hx
      omega)
    obtain ⟨k3, F3, hPost⟩ := post hP hpre_2 hpre_8 hlim F2 hret3_14 hret3_16 rfl
    have o : ∀ (R : Reg → Word) (M : MachineState) (x : Word), Spec.Layout.Term.Out R M x →
        R .x10 = top + 18446744073709551552#64 ∨ R .x10 = top + 18446744073709551576#64 →
        x.toNat < top.toNat - 16 := fun R M x hx hR => by
      unfold Spec.Layout.Term.Out InRange at hx
      simp only [Layouts.Form.byteSize] at hx
      rcases hR with hR | hR <;> rw [hR] at hx <;> omega
    have s : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 16 →
        m3.getMem (top + c) = ((m.setMem (top + 18446744073709551608#64) ret).setMem
          (top + 18446744073709551600#64) (regs .x8)).getMem (top + c) := fun c k hc h0 hk => by
      have := top_sub (top := top) hc (by omega)
      have hna : top + c ≠ env.nextAddr := fun e => by rw [e] at this; omega
      rw [k3 _ (by omega) (by omega), fkeep hret2_14 (by omega) (by have := hret2_14.2.1; omega) hna
        (fun h => by have := o _ _ _ h (.inr rfl); omega),
        fkeep hret1_14 (by omega) (by have := hret1_14.2.1; omega) hna
        (fun h => by have := o _ _ _ h (.inl rfl); omega)]
    have s8 : m3.getMem (top + 18446744073709551608#64) = ret := by
      rw [s _ 8 rfl (by omega) (by omega), get_ne (by omega), MachineState.getMem_setMem_eq]
    have s16 : m3.getMem (top + 18446744073709551600#64) = regs .x8 := by
      rw [s _ 16 rfl (by omega) (by omega), MachineState.getMem_setMem_eq]
  · exact s8
  · exact ⟨⟨rfl, s16, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, F3, hret3_15, hPost _⟩

end Rv64mc.Proof.Layout.StateStepT

/-- info: 'Rv64mc.Proof.Layout.StateStepT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.StateStepT.total
