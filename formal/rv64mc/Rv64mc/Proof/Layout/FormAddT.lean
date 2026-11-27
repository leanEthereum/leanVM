/-
  Rv64mc.Proof.Layout.FormAddT

  `<Form as Add>::add(self, other)` is total (`SpecT`): it calls `Form::add_scaled(&mut self, &other, ONE)` and
  moves `self`'s header to the result's slot, so the result is a `Form` (`FormReprT.FormT`) whose terms' block is
  `self`'s at entry (pointer and capacity) or allocated since; the run ends with the guest's abort (`AbortStop`)
  where `add_scaled` does. From `add_scaled`'s total contract (`AddScaledT`). Safety only: `add_scaled`'s contract
  states no values.

  The compiled function takes the result's slot (`a0`), `self`'s header by reference (`a1`) and `other`'s terms'
  pointer and length (`a2`, `a3`). The precondition asks the slot and `self`'s header in the caller's frame (at or
  above the stack pointer, `StackObj`), 8-byte aligned, apart; `self` a `FormT`; `other`'s terms a buffer's
  (`BufT`) of `TermsT`, apart from `self`'s buffer unless either is empty. At every call site in the image (the
  `Form::sum` closures, `flushes_arith`, `flushes_jump`, `Flushes::memory_if`) the slot and `self` are distinct
  24-byte slots of the caller's frame; `AddScaledT.PreT`'s apartness of `self`'s header from both buffers then holds
  because those lie below `NEXT` and the header on the stack.

  ## Main definitions

  * `PreT`, `PostT`, `OutT`, `SpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.AddScaledT
import Rv64mc.Gen.Tmpl.Verifier.Layout.Form.AsAdd.Add

namespace Rv64mc.Proof.Layout.FormAddT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Layout.FormReprT
open Rv64mc.Proof.Layout.PairT (Apart KeptOrFresh)
open Rv64mc.Proof.Layout.PlacementNextT (StackObj)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Verifier.Layout.Form.AsAdd.Add (Link tmpl)

/-- The total precondition: the result's slot and `self`'s header (`a1`) caller's frame objects, 8-byte aligned and
    apart; `self` a `Form`; `other`'s terms (`a2`, `a3`) a buffer's, each term's monomial a vector of words, apart
    from `self`'s buffer unless either is empty. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  StackObj (regs .x2) (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ StackObj (regs .x2) (regs .x11) 24 ∧
    Apart (regs .x10) 24 (regs .x11) 24 ∧ FormT env m (regs .x11) ∧ BufT env m (regs .x13) (regs .x12) 40 ∧
    TermsT env m (regs .x12) (regs .x13).toNat ∧
    ((regs .x13).toNat = 0 ∨ (vecCap m (regs .x11)).toNat = 0 ∨
      Apart (regs .x12) (40 * (regs .x13).toNat) (vecPtr m (regs .x11)) (40 * (vecCap m (regs .x11)).toNat))

/-- The total postcondition: the result a `Form` whose terms' block is `self`'s at entry or allocated since. -/
def PostT (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) : Prop :=
  FormT env m' (regs .x10) ∧
    ((vecPtr m' (regs .x10) = vecPtr m (regs .x11) ∧ vecCap m' (regs .x10) = vecCap m (regs .x11)) ∨
      (env.next m).toNat ≤ (vecPtr m' (regs .x10)).toNat)

/-- What `add` writes besides its stack and what it allocates: the result's slot, `self`'s header and its buffer at
    entry. -/
def OutT (regs : Reg → Word) (m : MachineState) (b : Word) : Prop :=
  InRange (regs .x10) 24 b ∨ InRange (regs .x11) 24 b ∨
    InRange (vecPtr m (regs .x11)) (40 * (vecCap m (regs .x11)).toNat) b

/-- **The total contract of `<Form as Add>::add`**, or the guest's abort. -/
def SpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (PreT env) (PostT env) OutT AbortStop

/-- The prologue's three saved words over `m`. -/
def saved (m : MachineState) (top ret : Word) (regs : Reg → Word) : MachineState :=
  ((m.setMem (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64) (regs .x8)).setMem
    (top + 18446744073709551592#64) (regs .x9)

variable {env : Env}

/-- A word at or above the stack top, or below the frame, is the entry's after the prologue. -/
theorem saved_get {m : MachineState} {top ret b : Word} {regs : Reg → Word} (h32 : 32 ≤ top.toNat)
    (hb : top.toNat ≤ b.toNat ∨ b.toNat + 32 ≤ top.toNat) : (saved m top ret regs).getMem b = m.getMem b := by
  have hne : ∀ c : Word, ∀ k, c.toNat + k = 2 ^ 64 → 0 < k → k ≤ 24 → b ≠ top + c := fun c k hc hk0 hk he => by
    have := congrArg BitVec.toNat he
    rw [Runtime.CloneT.toNat_add_neg hc (by omega)] at this
    omega
  simp only [saved]
  rw [MachineState.getMem_setMem_ne (hne _ 24 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 16 rfl (by omega) (by omega)),
    MachineState.getMem_setMem_ne (hne _ 8 rfl (by omega) (by omega))]

/-- A `Form`'s terms kept by a memory agreeing below `NEXT`. -/
theorem termsT_keep {m M : MachineState} {q : Word} {n : Nat} (h : TermsT env m q n)
    (hb : n = 0 ∨ q.toNat + n * 40 ≤ (env.next m).toNat) (hN : (env.next m).toNat ≤ (env.next M).toNat)
    (hk : ∀ b : Word, b.toNat < (env.next m).toNat → M.getMem b = m.getMem b) : TermsT env M q n := by
  intro t ht
  have hb' : q.toNat + n * 40 ≤ (env.next m).toNat := hb.resolve_left (by omega)
  have he : (q + BitVec.ofNat 64 (40 * t)).toNat = q.toNat + 40 * t := toNat_add_ofNat (by
    have := (env.next m).isLt; omega)
  exact vecT_keep (h t ht) hN fun b h1 h2 => hk b (by omega)

/-- A word of a 24-byte object apart from another 24-byte object at `a`. -/
theorem off24 {a x b : Nat} (hap : a + 24 ≤ x ∨ x + 24 ≤ a) (h1 : x ≤ b) (h2 : b < x + 24) :
    b < a ∨ a + 24 ≤ b := by omega

/-- `add_scaled`'s precondition, sealed so that the executor leaves it as one goal. -/
@[irreducible] def ASPre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop := AddScaledT.PreT env regs m

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needA : Nat} (hnA : 32 + needA ≤ need) (has : AddScaledT.SpecT env p L.addScaled.idx needA) :
    SpecT env p i need := by
  have has' : HoldsT env p L.addScaled.idx needA (ASPre env) (AddScaledT.PostT env) AddScaledT.OutT AbortStop := by
    unfold ASPre; exact has
  rv_autoT hp with [hL] using [has']
  all_goals
    have hlay := env.layout
    have hlim : env.stackLimit.toNat + 32 ≤ top.toNat := by omega
    have hMs : ((MachineState.setMem m (top + 18446744073709551608#64) ret).setMem (top + 18446744073709551600#64)
        (regs .x8)).setMem (top + 18446744073709551592#64) (regs .x9) = saved m top ret regs := rfl
    rw [hpre_2] at hpre_6 hpre_9
    have hF : FormT env m (regs .x11) := ⟨⟨hpre_12, ⟨hpre_13, hpre_14, hpre_15, hpre_16⟩, hpre_17⟩, hpre_18⟩
    have hft := hF.foot
    have hcb := vecT_buf hF.1
    have hbufN : (vecCap m (regs .x11)).toNat = 0 ∨
        (vecPtr m (regs .x11)).toNat + 40 * (vecCap m (regs .x11)).toNat ≤ (env.next m).toNat := by
      have hb := hpre_15
      rw [Runtime.GrowOne.rvCapAt_eq, Runtime.GrowOne.rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq] at hb
      rcases hb with h | ⟨-, h, -⟩
      · exact .inl h
      · unfold Env.Live at h; exact .inr (by omega)
    have hsg : ∀ b : Word, (top.toNat ≤ b.toNat ∨ b.toNat + 32 ≤ top.toNat) →
        (saved m top ret regs).getMem b = m.getMem b := fun b hb => saved_get (by omega) hb
    have hnS : env.next (saved m top ret regs) = env.next m := hsg _ (.inr (by omega))
  · unfold ASPre AddScaledT.PreT
    simp only [updReg, Tactic.rf_get_x2, Tactic.rf_get_x10, Tactic.rf_get_x11, Tactic.rf_get_x12, reduceCtorEq,
      ite_false]
    rw [hMs]
    have e8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
    have hh : ∀ b : Word, (regs .x11).toNat ≤ b.toNat → b.toNat < (regs .x11).toNat + 24 →
        (saved m top ret regs).getMem b = m.getMem b := fun b h1 h2 => hsg b (.inl (by omega))
    have ec : vecCap (saved m top ret regs) (regs .x11) = vecCap m (regs .x11) := by
      rw [vecCap_eq, vecCap_eq]; exact hh _ (by omega) (by omega)
    have ep : vecPtr (saved m top ret regs) (regs .x11) = vecPtr m (regs .x11) := by
      rw [vecPtr_eq, vecPtr_eq]; exact hh _ (by omega) (by omega)
    have hlow : ∀ b : Word, b.toNat < (env.next m).toNat → (saved m top ret regs).getMem b = m.getMem b :=
      fun b hb => hsg b (.inr (by omega))
    have e32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 :=
      Runtime.CloneT.toNat_add_neg rfl (by omega)
    have hob : (regs .x13).toNat = 0 ∨ (regs .x12).toNat + (regs .x13).toNat * 40 ≤ (env.next m).toNat :=
      hpre_19.imp id fun ⟨_, h2, _⟩ => by unfold Env.Live at h2; omega
    refine ⟨FormT.keep hF (by rw [hnS]) hh fun b h1 h2 => hlow b (by rcases hft with h | h <;> omega),
      ⟨.inr (by omega), by omega⟩,
      Runtime.VecReprT.BufT.mono (show BufT env m (regs .x13) (regs .x12) 40 from hpre_19) (by rw [hnS]),
      termsT_keep hpre_20 hob (by rw [hnS]) hlow, ?_, ?_⟩
    · rw [ec, ep]; exact hbufN.imp id fun h => .inr (by omega)
    · rw [ec, ep]
      by_cases hz : (regs .x13).toNat = 0
      · exact .inl hz
      · exact .inr ⟨.inl (by have := hob.resolve_left hz; omega), hpre_21.resolve_left hz⟩
  all_goals
    have e8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := Runtime.CloneT.toNat_add_neg rfl (by omega)
    have e16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := Runtime.CloneT.toNat_add_neg rfl (by omega)
    have e24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := Runtime.CloneT.toNat_add_neg rfl (by omega)
    have e32 : (top + 18446744073709551584#64).toNat = top.toNat - 32 := Runtime.CloneT.toNat_add_neg rfl (by omega)
    have x8 : (regs .x11 + 8#64).toNat = (regs .x11).toNat + 8 := toNat_add_ofNat (by omega)
    have x16 : (regs .x11 + 16#64).toNat = (regs .x11).toNat + 16 := toNat_add_ofNat (by omega)
    have ec : vecCap (saved m top ret regs) (regs .x11) = vecCap m (regs .x11) := by
      rw [vecCap_eq, vecCap_eq]; exact hsg _ (.inl (by omega))
    have ep : vecPtr (saved m top ret regs) (regs .x11) = vecPtr m (regs .x11) := by
      rw [vecPtr_eq, vecPtr_eq]; exact hsg _ (.inl (by omega))
    rw [hMs] at hret1_14 hret1_23
    have ne : ∀ a b : Word, a.toNat ≠ b.toNat → a ≠ b := fun a b hab e => hab (by rw [e])
    have k1 : ∀ b : Word, top.toNat - 32 ≤ b.toNat → b.toNat < top.toNat →
        m1.getMem b = (saved m top ret regs).getMem b := fun b h1 h2 => hret1_14.2.2 b fun hw => by
      have := hret1_14.2.1
      rcases hw with hw | hw | hw | hw
      · omega
      · omega
      · rw [hw] at h1; omega
      · rcases hw with hw | hw
        · simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false] at hw; unfold InRange at hw; omega
        · simp only [updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false] at hw
          rw [ep, ec] at hw; unfold InRange at hw; omega
    have s8 : m1.getMem (top + 18446744073709551608#64) = ret := by
      rw [k1 _ (by omega) (by omega)]; simp only [saved]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_eq]
  · exact s8
  · have s16 : m1.getMem (top + 18446744073709551600#64) = regs .x8 := by
      rw [k1 _ (by omega) (by omega)]; simp only [saved]
      rw [MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
    have s24 : m1.getMem (top + 18446744073709551592#64) = regs .x9 := by
      rw [k1 _ (by omega) (by omega)]; simp only [saved, MachineState.getMem_setMem_eq]
    have a8 : (regs .x10 + 8#64).toNat = (regs .x10).toNat + 8 := toNat_add_ofNat (by omega)
    have a16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
    have hn1 := hret1_14.1
    have hn1' := hret1_14.2.1
    rw [hnS] at hn1
    -- the frame
    have F0 : env.Frame top Tactic.F m (saved m top ret regs) :=
      Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_refl hpre_5) (by omega) (by omega))
        (by omega) (by omega)) (by omega) (by omega)
    have F1 : env.Frame top (OutT regs m) m m1 := (Tactic.frame_weaken F0).trans hret1_14 (by omega) fun b hb => by
      simp only [AddScaledT.OutT, updReg, Tactic.rf_get_x10, reduceCtorEq, ite_false] at hb
      rw [ep, ec] at hb
      exact .inr (.inr (.inr (.inr hb)))
    have hst : ∀ b : Word, (regs .x10).toNat ≤ b.toNat → b.toNat ≤ (regs .x10).toNat + 16 →
        b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat := fun b h1 h2 => .inr (by omega)
    have hnx : ∀ b : Word, (regs .x10).toNat ≤ b.toNat → b ≠ env.nextAddr := fun b h1 e => by rw [e] at h1; omega
    have hout : ∀ k, k ≤ 16 → ∀ b : Word, b.toNat = (regs .x10).toNat + k → OutT regs m b := fun k hk b hb =>
      .inl (by unfold InRange; omega)
    refine ⟨⟨rfl, s16, s24, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      Tactic.frame_out (Tactic.frame_out (Tactic.frame_out F1 (hout 0 (by omega) _ rfl) (hnx _ (by omega)))
        (hout 8 (by omega) _ a8) (hnx _ (by omega))) (hout 16 (by omega) _ a16) (hnx _ (by omega)),
      Tactic.static_store (Tactic.static_store (Tactic.static_store hret1_15 (hst _ (by omega) (by omega)))
        (hst _ (by omega) (by omega))) (hst _ (by omega) (by omega)), ?_⟩
    -- the result
    have hF1 : FormT env m1 (regs .x11) := ⟨⟨hret1_16, ⟨hret1_17, hret1_18, hret1_19, hret1_20⟩, hret1_21⟩, hret1_22⟩
    have hft1 := hF1.foot
    generalize hM3 : ((m1.setMem (regs .x10) (m1.getMem (regs .x11))).setMem (regs .x10 + 8#64)
        (m1.getMem (regs .x11 + 8#64))).setMem (regs .x10 + 16#64) (m1.getMem (regs .x11 + 16#64)) = M3
    have r0 : M3.getMem (regs .x10) = m1.getMem (regs .x11) := by
      rw [← hM3, MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_eq]
    have r8 : M3.getMem (regs .x10 + 8#64) = m1.getMem (regs .x11 + 8#64) := by
      rw [← hM3, MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_eq]
    have r16 : M3.getMem (regs .x10 + 16#64) = m1.getMem (regs .x11 + 16#64) := by
      rw [← hM3, MachineState.getMem_setMem_eq]
    have rk : ∀ b : Word, (b.toNat < (regs .x10).toNat ∨ (regs .x10).toNat + 24 ≤ b.toNat) →
        M3.getMem b = m1.getMem b := fun b hb => by
      rw [← hM3, MachineState.getMem_setMem_ne (ne _ _ (by omega)), MachineState.getMem_setMem_ne (ne _ _ (by omega)),
        MachineState.getMem_setMem_ne (ne _ _ (by omega))]
    have hN3 : env.next M3 = env.next m1 := rk _ (.inl (by omega))
    have hx10 : (env.next m1).toNat ≤ (regs .x10).toNat := by omega
    have hF3 : FormT env M3 (regs .x11) :=
      FormT.keep hF1 (by rw [hN3]) (fun b h1 h2 => rk b (off24 hpre_11 h1 h2))
        fun b h1 h2 => rk b (.inl (Nat.lt_of_lt_of_le (by rcases hft1 with h | h <;> omega) hx10))
    have ep3 : vecPtr M3 (regs .x10) = vecPtr m1 (regs .x11) := by rw [vecPtr_eq, vecPtr_eq, r8]
    have el3 : vecLen M3 (regs .x10) = vecLen m1 (regs .x11) := by rw [vecLen_eq, vecLen_eq, r16]
    have ec3 : vecCap M3 (regs .x10) = vecCap m1 (regs .x11) := by rw [vecCap_eq, vecCap_eq, r0]
    have hpl1 : vecPtr M3 (regs .x11) = vecPtr m1 (regs .x11) := by
      rw [vecPtr_eq, vecPtr_eq]; exact rk _ (off24 hpre_11 (by omega) (by omega))
    have hll1 : vecLen M3 (regs .x11) = vecLen m1 (regs .x11) := by
      rw [vecLen_eq, vecLen_eq]; exact rk _ (off24 hpre_11 (by omega) (by omega))
    have hcl1 : vecCap M3 (regs .x11) = vecCap m1 (regs .x11) := by
      rw [vecCap_eq, vecCap_eq]; exact rk _ (off24 hpre_11 (by omega) (by omega))
    refine ⟨⟨CloneFormsT.vecT_copy hF3.1 (.inr ⟨by omega, by omega⟩) hpre_8 (Nat.le_refl _)
      (by rw [r0]; exact (rk _ (off24 hpre_11 (by omega) (by omega))).symm)
      (by rw [r8]; exact (rk _ (off24 hpre_11 (by omega) (by omega))).symm)
      (by rw [r16]; exact (rk _ (off24 hpre_11 (by omega) (by omega))).symm), ?_⟩, ?_⟩
    · rw [ep3, el3, ← hpl1, ← hll1]; exact hF3.2
    · rw [ep3, ec3]
      rcases hret1_23 with ⟨h1, h2⟩ | h1
      · exact .inl ⟨by rw [h1, ep], by rw [h2, ec]⟩
      · exact .inr h1

end Rv64mc.Proof.Layout.FormAddT

/-- info: 'Rv64mc.Proof.Layout.FormAddT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.FormAddT.total
