/-
  Rv64mc.Proof.Hash.DigestFromHalvesT

  `Digest::from_halves` is total: it leaves `DigestFromHalves.Post`'s 32 bytes at `sret` (`Spec.Hash.Digest`), over
  any program holding its template. The total counterpart of `DigestFromHalves.lean`, whose lemmas close the same
  four goals here. Its 32 byte stores go through the caller's pointer `a0`, so the precondition adds that the
  digest's bytes lie in a window (`InWin`, `MemsetT.lean`'s), from which `rv_autoT` closes each store's window and
  no code under it. Both call sites in the image (`walk`, `verify_whir`'s closure) pass a slot of the caller's
  frame, `sp + c` with the 32 bytes below the caller's stack top, which is in the stack window.

  ## Main definitions

  * `PreT`, `specT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Hash.DigestFromHalves
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Hash.DigestFromHalvesT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Hash.DigestFromHalves Rv64mc.Proof.Hash.DigestFromHalves
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Hash.Digest.FromHalves (Link tmpl)

/-- `Digest::from_halves`'s total precondition: `Pre`, and the digest's bytes at `sret` in a window. -/
def PreT (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env regs m ∧ InWin env (regs .x10) Layouts.Digest.byteSize

/-- **The total contract of `Digest::from_halves`**: `DigestFromHalves.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := HoldsT env p i need (PreT env) Post Out

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    specT env p i need := by
  rv_autoT hp
  all_goals clear hpre_8 hpre_10
  all_goals have hw := bound_of hpre_7
  all_goals have hO : Pre env regs m := ⟨hpre_6, hpre_7⟩
  all_goals have hlim : env.stackLimit.toNat ≤ (regs .x2).toNat :=
    hpre_2 ▸ Nat.le_trans (Nat.le_add_right _ _) hpre_3
  all_goals have hown : ∀ a, InRange (regs .x10) 32 a → Out regs m (alignToDword a) ∧
      alignToDword a ≠ env.nextAddr ∧ ((alignToDword a).toNat < env.staticLo.toNat ∨
        env.staticHi.toNat ≤ (alignToDword a).toNat) := fun a ha =>
    ⟨dwordsOf_align ha, hO.not_next hpre_5 hlim (dwordsOf_align ha), hO.not_static hpre_5 hlim (dwordsOf_align ha)⟩
  · repeat' (first | refine frame_setByte ?_ (hown _ ?_).1 (hown _ ?_).2.1 | with_reducible exact Env.Frame.refl hpre_5)
    all_goals first | exact inRange_off (by decide) hw | exact ⟨le_refl _, by omega⟩
  · repeat' (first | refine Env.static_setMem ?_ (hown _ ?_).2.2 | with_reducible exact hpre_4)
    all_goals first | exact inRange_off (by decide) hw | exact ⟨le_refl _, by omega⟩
  · refine ⟨by simp [Model.digestFromHalvesRust, Model.toLeBytes]; omega, fun k hk => ?_⟩
    simp only [Model.digestFromHalvesRust, Model.toLeBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil, List.length_cons, List.length_nil] at hk ⊢
    interval_cases k <;> simp [getByte_setByte_eq, getByte_setByte_ne,
      BitVec.add_right_inj, BitVec.truncate_eq_setWidth]
  · intro b hb
    simp only [Layouts.Digest.byteSize] at hb
    repeat rw [getByte_setByte_ne]
    all_goals first | exact ne_off hb (by decide) hw | exact ne_self hb (by decide)

end Rv64mc.Proof.Hash.DigestFromHalvesT

/-- info: 'Rv64mc.Proof.Hash.DigestFromHalvesT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Hash.DigestFromHalvesT.total
