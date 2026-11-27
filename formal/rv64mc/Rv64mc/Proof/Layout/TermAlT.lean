/-
  Rv64mc.Proof.Layout.TermAlT

  `Form::term`'s second total contract (`specT`), beside `TermT.specT`: `Spec.Layout.Term`'s postcondition and the
  `Form`'s buffers 8-byte aligned (`FormAl`), from `TermT`'s precondition and the monomial's buffer aligned unless it
  has no capacity. `Term.Post`'s `FormIn` places every buffer in a region but says nothing of their alignment, which a
  `Form`'s total representation (`FormReprT.FormT`: a `VecT` of 40-byte terms, each monomial a `VecT` of words) asks;
  with the alignments, the region below `NEXT` and from the heap window's start, and the header in a window, the
  `Form` is a `FormT` (`formT_of`). The proof is `TermT.total`'s, the alignments read off the stores (`chain_al`):
  the terms' block is `alloc`'s, 8-byte aligned (`AllocPost`), and the monomial's pointer is the caller's.

  ## Main definitions

  * `FormAl`, `specT`

  ## Main results

  * `formT_of`, `chain_al`, `total`
-/

import Rv64mc.Proof.Layout.TermT
import Rv64mc.Proof.Layout.FormReprT

namespace Rv64mc.Proof.Layout.TermAlT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Term
open Rv64mc.Proof.Layout.Term
open Rv64mc.Proof.Layout.TermT (TermWin)
open Rv64mc.Spec.Runtime (AllocPre AllocPost)
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Proof.Runtime.VecReprT (BufT VecT)
open Rv64mc.Proof.Runtime.GrowOne (rvCapAt_eq rvPtrAt_eq)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Proof.Layout.FormReprT (FormT TermsT)
open Rv64mc.Gen.Verifier.Layout.Form.Term (Link tmpl)

/-- **The buffers of the `Form` at `a` are 8-byte aligned**: its terms' block, and each term's monomial's buffer,
    each unless it has no capacity. -/
def FormAl (m : MachineState) (a : Word) : Prop :=
  ((vecCap m a).toNat = 0 ∨ (vecPtr m a).toNat % 8 = 0) ∧
    ∀ t, t < (vecLen m a).toNat → (vecCap m (vecPtr m a + BitVec.ofNat 64 (40 * t))).toNat = 0 ∨
      (vecPtr m (vecPtr m a + BitVec.ofNat 64 (40 * t))).toNat % 8 = 0

variable {env : Env}

/-- **A `Form` in a region below `NEXT`, its buffers aligned, its header in a window, is a `FormT`.** -/
theorem formT_of {m : MachineState} {lo hi a : Word} {f : LeanVM.Protocol.Verifier.Form} (h : FormIn lo hi m a f) (hal : FormAl m a)
    (hlo : 0x10000000 ≤ lo.toNat) (hhi : hi.toNat ≤ (env.next m).toNat)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hE : env.heapEnd.toNat ≤ 0x78000000) (hw : InWin env a 24)
    (ha : a.toNat % 8 = 0) : FormT env m a := by
  obtain ⟨q, cap, hv, hb⟩ := h
  have hlay := env.layout
  have hE := env.heapEnd.isLt
  have hc : vecCap m a = BitVec.ofNat 64 cap := hv.cap_eq
  have hcl : (vecCap m a).toNat = cap := by rw [hc]; simp; have := hv.cap_lt; omega
  have hp : vecPtr m a = q := hv.ptr_eq
  have hl : vecLen m a = BitVec.ofNat 64 f.terms.length := hv.len_eq
  have hll : (vecLen m a).toNat = f.terms.length := by rw [hl]; simp; have := hv.len_le; have := hv.cap_lt; omega
  have hreg : cap = 0 ∨ (lo.toNat ≤ q.toNat ∧ q.toNat + 40 * cap ≤ hi.toNat) := by
    simpa [BufIn, Region, Layouts.VecUsizeE.byteSize] using hb
  have gc : m.getMem (Spec.Runtime.rvCapAt a) = vecCap m a := by rw [rvCapAt_eq, vecCap_eq]
  have gp : m.getMem (Spec.Runtime.rvPtrAt a) = vecPtr m a := by rw [rvPtrAt_eq, vecPtr_eq]
  refine ⟨⟨hw, ⟨by unfold InWin at hw ⊢; simp only [Layouts.RawVecInner.byteSize]; omega, ha, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [gc, gp]
    unfold BufT
    rw [hcl, hp]
    by_cases hc0 : cap = 0
    · exact .inl hc0
    obtain ⟨h1, h2⟩ := hreg.resolve_left hc0
    refine .inr ⟨by omega, by unfold Env.Live; omega, ?_⟩
    rcases hal.1 with h3 | h3
    · omega
    · rwa [hp] at h3
  · rw [gc, hcl]
    rcases hreg with h0 | ⟨-, h2⟩ <;> omega
  · rw [hll, hcl]; exact hv.len_le
  · intro t ht
    have hal2 := hal.2 t ht
    rw [hll] at ht
    have hcap0 : cap ≠ 0 := by have := hv.len_le; omega
    obtain ⟨h1, h2⟩ := hreg.resolve_left hcap0
    have hlen := hv.len_le
    have he : (q + BitVec.ofNat 64 (40 * t)).toNat = q.toNat + 40 * t := toNat_add_ofNat (by omega)
    obtain ⟨qm, cm, hvm, hbm, -⟩ := hv.elems.2 t ht
    rw [hp]
    rw [hp] at hal2
    have hcm : (vecCap m (q + BitVec.ofNat 64 (40 * t))).toNat = cm := by
      rw [hvm.cap_eq]; simp; have := hvm.cap_lt; omega
    have hpm : vecPtr m (q + BitVec.ofNat 64 (40 * t)) = qm := hvm.ptr_eq
    have hregm : cm = 0 ∨ (lo.toNat ≤ qm.toNat ∧ qm.toNat + 8 * cm ≤ hi.toNat) := by
      simpa [BufIn, Region] using hbm
    have hqa : q.toNat % 8 = 0 := by
      rcases hal.1 with h3 | h3
      · rw [hcl] at h3; omega
      · rwa [hp] at h3
    refine ⟨.inl ⟨by rw [he]; omega, by rw [he]; simp only [Layouts.Vec.byteSize]; omega⟩, ⟨.inl ⟨by rw [he]; omega, by rw [he]; simp only [Layouts.RawVecInner.byteSize]; omega⟩, by rw [he]; omega, ?_, ?_⟩, ?_⟩
    · rw [rvCapAt_eq, rvPtrAt_eq, ← vecCap_eq, ← vecPtr_eq]
      unfold BufT
      rw [hcm, hpm]
      by_cases hc0 : cm = 0
      · exact .inl hc0
      obtain ⟨h3, h4⟩ := hregm.resolve_left hc0
      refine .inr ⟨by omega, by unfold Env.Live; omega, ?_⟩
      rcases hal2 with h5 | h5
      · omega
      · rwa [hpm] at h5
    · rw [rvCapAt_eq, ← vecCap_eq, hcm]
      rcases hregm with h0 | ⟨-, h4⟩ <;> omega
    · rw [hvm.len_eq, hvm.cap_eq]
      simp only [BitVec.toNat_ofNat]
      have := hvm.len_le; have := hvm.cap_lt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact hvm.len_le

/-- **The stores' `Form` is aligned**: its terms' block is `r`, aligned, and its one term's monomial is the header at
    `h`, of capacity `0` or with an aligned pointer. -/
theorem chain_al {m1 : MachineState} {r a h c0 c1 top : Word} (hp : Place env r a top)
    (htop : env.stackLimit.toNat ≤ top.toNat) (hr : r.toNat % 8 = 0)
    (hq : m1.getMem h = 0#64 ∨ (m1.getMem (h + 8#64)).toNat % 8 = 0) : FormAl (chain m1 r a h c0 c1) a := by
  have := hp.r_hi; have := hp.a_at; have := hp.a_hi; have := env.layout
  have ep : vecPtr (chain m1 r a h c0 c1) a = r := by
    simp only [vecPtr, Layouts.Vec.ptr, chain]
    rw [MachineState.getMem_setMem_ne (by addr_ne), MachineState.getMem_setMem_eq]
  have el : vecLen (chain m1 r a h c0 c1) a = 1#64 := by
    simp only [vecLen, Layouts.Vec.len, chain]
    rw [MachineState.getMem_setMem_eq]
  refine ⟨.inr (by rw [ep]; exact hr), fun t ht => ?_⟩
  rw [el] at ht
  have ht0 : t = 0 := by simp at ht; omega
  subst ht0
  rw [ep, show BitVec.ofNat 64 (40 * 0) = 0#64 from rfl, BitVec.add_zero]
  have ec : vecCap (chain m1 r a h c0 c1) r = m1.getMem h := by
    simp only [vecCap, Layouts.Vec.cap, chain, BitVec.add_zero]
    repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
    rw [MachineState.getMem_setMem_eq]
  have eq : vecPtr (chain m1 r a h c0 c1) r = m1.getMem (h + 8#64) := by
    simp only [vecPtr, Layouts.Vec.ptr, chain]
    repeat rw [MachineState.getMem_setMem_ne (by addr_ne)]
    rw [MachineState.getMem_setMem_eq]
  rw [ec, eq]
  exact hq.imp_left fun h0 => by rw [h0]; rfl

/-- The total precondition: `TermT`'s, and the monomial's buffer 8-byte aligned unless it has no capacity. -/
def PreA (env : Env) (ms : List Nat) (c : E) (lo q : Word) (cap : Nat) (regs : Reg → Word) (m : MachineState) :
    Prop :=
  Pre env ms c lo q cap regs m ∧ TermWin env regs m ∧ (cap = 0 ∨ q.toNat % 8 = 0)

/-- **`Form::term`'s second total contract**: `Term.Post` and the result's buffers aligned (`FormAl`). -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ ms c lo q cap, HoldsT env p i need (PreA env ms c lo q cap)
    (fun regs m r' m' => Post env ms c lo regs m r' m' ∧ FormAl m' (regs .x10)) Out AbortStop

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (halloc : AllocSpecT env p L.alloc.idx 0)
    (hpanic : Aborts env p L.panicNounwindFmt.idx 0) : specT env p i := by
  intro ms c lo q cap
  have hal' : HoldsT env p L.alloc.idx 0 AllocPre (AllocPost env) (Stop := AbortStop) :=
    halloc.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hpanic]
  all_goals
    have hlay := env.layout
    have hstk : env.stackLimit.toNat + 48 ≤ top.toNat := hpre_3
    have htop : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_11 hpre_13
    have hn1 := hret1_14.2.1
    rw [show (40#64 : Word).toNat = 40 from rfl] at hret1_18
    have hHS : env.heapEnd.toNat ≤ env.stackLimit.toNat := by omega
    have hP : Place env (r1 .x10) (regs .x10) top :=
      ⟨by omega, by simp only [Layouts.Form.byteSize] at hpre_13; omega, hpre_14⟩
    have hF : env.Frame top Tactic.F m m1 := Tactic.frame_call
      (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store (Tactic.frame_store
        (Tactic.frame_refl hpre_5) (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide)))
        (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide))) (Tactic.slot_ge hpre_3 (by decide))
        (Tactic.slot_lt hpre_3 (by decide))) (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide)))
        (Tactic.slot_ge hpre_3 (by decide)) (Tactic.slot_lt hpre_3 (by decide))) hret1_14
        (Tactic.slot_le hpre_3 (by decide))
    have hn := hF.1
    have hk : Keeps m m1 (regs .x11) Layouts.Vec.byteSize := by
      rcases hpre_11 with h1 | h1
      · exact Env.Frame.keeps_live hF hpre_5 h1 fun _ _ h => h
      · exact Env.Frame.keeps_above hF htop h1 fun _ _ h => h
    have hx := hpre_12
    simp only [Layouts.Vec.byteSize] at hk hx
    rw [← hk (regs .x11) ⟨Nat.le_refl _, by omega⟩,
      ← hk (regs .x11 + 8#64) ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩,
      ← hk (regs .x11 + 16#64) ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩]
    have hv1 := vec_keep hF hpre_5 htop hpre_6 hpre_7 ⟨hpre_11, hpre_12⟩
  · refine chain_post hP hv1 ?_ ?_ ?_ (by omega) (by omega) htop
    · exact hpre_7.imp id fun ⟨h1, h2⟩ => ⟨h1, by omega⟩
    · exact hpre_7.imp id fun ⟨_, h2⟩ => by omega
    · simp only [Layouts.Form.byteSize] at hpre_15
      exact hpre_7.imp id fun ⟨_, h2⟩ => by omega

  · have hq : m1.getMem (regs .x11) = 0#64 ∨ (m1.getMem (regs .x11 + 8#64)).toNat % 8 = 0 := by
      rcases hpre_20 with h0 | h0
      · left; rw [← vecCap_eq, hv1.cap_eq, h0]
      · right; rw [← vecPtr_eq, hv1.ptr_eq]; exact h0
    have hA := (chain_al (c0 := (Model.limbs c).1) (c1 := (Model.limbs c).2) hP htop hret1_17 hq).2
    have hl : (vecLen (chain m1 (r1 .x10) (regs .x10) (regs .x11) (Model.limbs c).1 (Model.limbs c).2)
        (regs .x10)).toNat = (1#64).toNat := by
      simp only [vecLen, Layouts.Vec.len, chain]
      rw [MachineState.getMem_setMem_eq]
    rw [hl] at hA
    unfold chain at hA
    intro t ht
    have h := hA t ht
    simp only [vecCap_eq] at h
    exact h
end Rv64mc.Proof.Layout.TermAlT

/-- info: 'Rv64mc.Proof.Layout.TermAlT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.TermAlT.total
