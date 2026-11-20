/-
  Rv64mc.Proof.Hash.DigestFromHalves

  `Digest::from_halves` keeps its contract (`Spec.Hash.DigestFromHalves.spec`), over any program holding its
  template: 32 byte stores, each limb's bytes little-endian. `rv_auto` leaves the memory as the chain of byte stores;
  the frame, the static data, the bytes written and the bytes kept are read through it here, a store at a time.
-/

import Rv64mc.Spec.Hash.Digest
import Rv64mc.Gen.Tmpl.Verifier.Hash.Digest.FromHalves
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Hash.DigestFromHalves

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Hash.DigestFromHalves
open Rv64mc.Gen.Verifier.Hash.Digest.FromHalves (Link tmpl)

/-! ## Byte stores into a caller's object -/

theorem inRange_off {q : Word} {c n : Nat} (hc : c < n) (hw : q.toNat + n < 2 ^ 64) :
    InRange q n (q + BitVec.ofNat 64 c) := by
  unfold InRange; rw [toNat_add_ofNat (by omega)]; omega

theorem ne_off {q b : Word} {c n : Nat} (hb : ¬ InRange q n b) (hc : c < n) (hw : q.toNat + n < 2 ^ 64) :
    b ≠ q + BitVec.ofNat 64 c := fun h => hb (h ▸ inRange_off hc hw)

theorem ne_self {q b : Word} {n : Nat} (hb : ¬ InRange q n b) (hn : 0 < n) : b ≠ q := fun h => hb (h ▸ ⟨le_refl _, by omega⟩)

/-- The doubleword of a byte of `[q, q + n)` is one of `DwordsOf q n`. -/
theorem dwordsOf_align {q a : Word} {n : Nat} (ha : InRange q n a) : Spec.Runtime.DwordsOf q n (alignToDword a) := by
  unfold Spec.Runtime.DwordsOf InRange at *
  rw [toNat_alignToDword, toNat_alignToDword]
  constructor <;> omega

/-- A byte store into the call's `out`, not into `NEXT`, is in its frame. -/
theorem frame_setByte {env : Env} {top a : Word} {v : BitVec 8} {out : Word → Prop} {m N : MachineState}
    (h : env.Frame top out m N) (ho : out (alignToDword a)) (hn : alignToDword a ≠ env.nextAddr) :
    env.Frame top out m (N.setByte a v) :=
  h.trans (Env.Frame.setMem_out h.2.1 ho hn) (le_refl _) fun _ hb => Or.inr (Or.inr (Or.inr hb))

/-- A frame whose `out` is no static address keeps the static data. -/
theorem static_of_frame_out {env : Env} {top : Word} {out : Word → Prop} {m M : MachineState} (hs : env.Static m)
    (h : env.Frame top out m M)
    (ho : ∀ b, out b → b.toNat < env.staticLo.toNat ∨ env.staticHi.toNat ≤ b.toNat) : env.Static M := by
  have := env.layout
  refine env.static_frame m M (fun a h1 h2 => h.2.2 a fun hw => ?_) hs
  rcases hw with hw | hw | hw | hw
  · omega
  · have := h.2.1; omega
  · rw [hw] at h2; omega
  · rcases ho a hw with h3 | h3 <;> omega

theorem bound_of {q : Word} (h : (alignToDword q).toNat + (Layouts.Digest.byteSize + q.toNat % 8) < 2 ^ 64) :
    q.toNat + 32 < 2 ^ 64 := by
  rw [toNat_alignToDword] at h; simp only [Layouts.Digest.byteSize] at h; omega

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    spec env p i need := by
  rv_auto hp
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

end Rv64mc.Proof.Hash.DigestFromHalves
