/-
  Rv64mc.Proof.Layout.TermT

  `Form::term` is total: `Spec.Layout.Term`'s postcondition, or the run ends with the guest's abort (`AbortStop`)
  where `alloc` finds the heap exhausted. From `alloc`'s total contract (`AllocT`, its stop weakened) and
  `panic_nounwind_fmt`'s `Aborts`. The partial proof (`Term.lean`) ported by `rv_autoT`, with its lemmas. The
  precondition adds that the monomial's header and the result's slot lie in windows, 8-byte aligned.

  ## Main definitions

  * `TermWin`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.Term
import Rv64mc.Proof.Runtime.AllocT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Layout.TermT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Term
open Rv64mc.Proof.Layout.Term
open Rv64mc.Spec.Runtime (AllocPre AllocPost)
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Layout.Form.Term (Link tmpl)

/-- The monomial's header (`a1`) and the result's slot (`a0`) in windows, 8-byte aligned. -/
def TermWin (env : Env) (regs : Reg → Word) (_m : MachineState) : Prop :=
  InWin env (regs .x11) Layouts.Vec.byteSize ∧ (regs .x11).toNat % 8 = 0 ∧
    InWin env (regs .x10) Layouts.Form.byteSize ∧ (regs .x10).toNat % 8 = 0

/-- **The total contract of `Form::term`**: `Spec.Layout.Term.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop :=
  ∀ ms c lo q cap, HoldsT env p i need (fun regs m => Pre env ms c lo q cap regs m ∧ TermWin env regs m)
    (Post env ms c lo) Out AbortStop

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    (halloc : AllocSpecT env p L.alloc.idx 0)
    (hpanic : Aborts env p L.panicNounwindFmt.idx 0) : specT env p i := by
  intro ms c lo q cap
  have hal' : HoldsT env p L.alloc.idx 0 AllocPre (AllocPost env) (Stop := AbortStop) :=
    halloc.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp with [hL] using [hal', hpanic]
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
  refine chain_post hP (vec_keep hF hpre_5 htop hpre_6 hpre_7 ⟨hpre_11, hpre_12⟩) ?_ ?_ ?_ (by omega) (by omega) htop
  · rcases hpre_7 with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨h1, by omega⟩
  · rcases hpre_7 with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · exact Or.inr (by omega)
  · rcases hpre_7 with h0 | ⟨h1, h2⟩
    · exact Or.inl h0
    · simp only [Layouts.Form.byteSize] at hpre_15; omega

end Rv64mc.Proof.Layout.TermT

/-- info: 'Rv64mc.Proof.Layout.TermT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.TermT.total
