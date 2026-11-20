/-
  Rv64mc.Proof.Transcript.GrindCheck

  `Transcript::grind_check` keeps its contract (`Spec.Transcript.GrindCheck.spec`), from the contracts of `next`
  and `Sponge::absorb_nonce`. No bits: `Ok` at once. Otherwise the nonce is read (an `Err` passes its error on),
  absorbed and permuted, and in checked mode the proof of work is masked by `powMask` (the code's branchless
  `bits < 64` choice, `mask_eq`).
-/

import Rv64mc.Spec.Transcript.GrindCheck
import Rv64mc.Spec.Transcript.Next
import Rv64mc.Spec.Transcript.AbsorbNonce
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Transcript.Next
import Rv64mc.Proof.Transcript.NextScalar
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Transcript.GrindCheck
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.GrindCheck

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.GrindCheck
open Rv64mc.Proof.Transcript Rv64mc.Proof.Transcript.NextScalar
open Rv64mc.Gen.Verifier.Transcript.Transcript.GrindCheck (Link tmpl)

theorem grind_none {t : Model.TState} {bits : Nat} (hb : bits ≠ 0) (ho : t.proof.stream.length ≤ t.streamOffset) :
    (Model.TM.grindCheck bits).run t = none := by
  simp only [StateT.run, Model.TM.grindCheck, hb, ↓reduceIte, List.getElem?_eq_none ho]

theorem grind_some {t : Model.TState} {bits : Nat} (hb : bits ≠ 0) (ho : t.streamOffset < t.proof.stream.length)
    {pow : Word} {s : Model.SpongeRust} (hs : t.sponge.absorbNonce t.proof.stream[t.streamOffset] = some (pow, s)) :
    (Model.TM.grindCheck bits).run t =
      if !t.checked || pow &&& Model.powMask bits = 0#64 then
        some ((), { { t with streamOffset := t.streamOffset + 1 } with sponge := s })
      else none := by
  simp only [StateT.run, Model.TM.grindCheck, hb, ↓reduceIte, List.getElem?_eq_getElem ho, hs]

/-- The branchless test of the masked proof of work: `Ok`'s niche exactly on zero, the error's tag otherwise. -/
theorem tag3_iff (x : Word) :
    BinOp.ult.eval 0#64 x + 18446744073709551615#64 ||| 3#64 = BitVec.ofNat 64 Layouts.ResultUnit.Ok.tag ↔
      x = 0#64 := by
  by_cases h : x = 0#64
  · subst h; simp [BinOp.eval, Layouts.ResultUnit.Ok.tag]
  · have : BitVec.ult 0#64 x = true := by
      rw [BitVec.ult_iff_lt, BitVec.lt_def]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      exact Nat.pos_of_ne_zero fun h0 => h (BitVec.eq_of_toNat_eq (by simp [h0]))
    simp [BinOp.eval, this, h, Layouts.ResultUnit.Ok.tag]

/-- **The mask the code computes**: all ones below `bits`, or everywhere from `64` bits on. -/
theorem mask_eq (b : Word) :
    (0#64 - BinOp.ult.eval b 64#64 &&& 18446744073709551615#64 <<< (b &&& 63#64).toNat ^^^
      18446744073709551615#64) = Model.powMask b.toNat := by
  by_cases hb : b.toNat < 64
  · have hu : BitVec.ult b 64#64 = true := by rw [BitVec.ult_iff_lt, BitVec.lt_def]; simpa using hb
    have hk : (b &&& 63#64).toNat = b.toNat := by
      rw [BitVec.toNat_and]; simp only [BitVec.toNat_ofNat]
      rw [show (63 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]; omega
    simp only [BinOp.eval, hu, ↓reduceIte, hk, Model.powMask, hb]
    generalize b.toNat = k at hb ⊢
    interval_cases k <;> decide
  · have hu : BitVec.ult b 64#64 = false := by
      rw [Bool.eq_false_iff, ne_eq, BitVec.ult_iff_lt, BitVec.lt_def]; simp; omega
    simp only [BinOp.eval, hu, Bool.false_eq_true, ↓reduceIte, Model.powMask, hb]
    simp

theorem checked_of_byte {b : Bool} (h : BitVec.zeroExtend 64 (boolByte b) = 0#64) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem checked_of_byte' {b : Bool} (h : ¬ BitVec.zeroExtend 64 (boolByte b) = 0#64) : b = true := by
  cases b
  · exact absurd rfl h
  · rfl

/-- **`Transcript::grind_check` keeps its contract**, for one transcript state. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN needA : Nat} (hnN : 64 + needN ≤ need) (hnA : 64 + needA ≤ need)
    (hnext : Spec.Transcript.Next.spec env p L.next.idx needN)
    (han : Spec.Transcript.AbsorbNonce.spec env p L.absorbNonce.idx needA) (t : Model.TState) :
    Holds env p i need (Pre env t) (Post env t) Out := by
  rv_auto hp with [hL] using [hnext t, han t.sponge ((t.proof.stream[t.streamOffset]?).getD 0)]
  all_goals
    have hS : env.stackLimit.toNat + 64 ≤ top.toNat := by omega
    have hS40 : env.stackLimit.toNat + 32 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_7 hpre_9
    simp only [Layouts.Transcript.byteSize] at hpre_8
    have hst : ∀ c : Word, Tactic.slotOk 64 c = true → (top + c).toNat < top.toNat := fun c hc => Tactic.slot_lt hS hc
    have hlo : ∀ c : Word, Tactic.slotOk 64 c = true → env.stackLimit.toNat ≤ (top + c).toNat :=
      fun c hc => Tactic.slot_ge hS hc
    have hsp : (top + 18446744073709551552#64).toNat = top.toNat - 64 := by
      rw [show (18446744073709551552#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 64) by decide]
      exact toNat_sub_lit (by omega) (by decide)
    have hs8 : (top + 18446744073709551560#64).toNat = top.toNat - 56 := by
      rw [show (18446744073709551560#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 56) by decide]
      exact toNat_sub_lit (by omega) (by decide)
    have h328 : top.toNat ≤ (regs .x10 + 328#64).toNat := Nat.le_trans hpre_7 (toNat_le_add hpre_8 (by decide))
    have hlay := env.layout
  -- `next`'s and `absorb_nonce`'s preconditions
  all_goals try
    refine hpre_6.stack hpre_8 hpre_7 hpre_9 hpre_5 fun b hb => ?_
    rcases hb with hb | hb
    · simp (disch := exact Nat.lt_of_lt_of_le hb (hlo _ rfl)) only [getMem_setMem_gt]
    · simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) hb) only [getMem_setMem_lt]
  all_goals try (unfold proofAddr at hpre_9 ⊢
                 simp only [Layouts.ResultE.byteSize, Layouts.Proof.byteSize] at hpre_9 ⊢
                 simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) h328) only [getMem_setMem_lt]
                 rcases hpre_9 with hl | hl
                 · unfold Env.Live at hl; omega
                 · omega)
  all_goals try (simp only [Layouts.ResultE.byteSize, Layouts.Transcript.byteSize, Layouts.Sponge.byteSize]
                 rw [hs8]; omega)
  all_goals try (simp only [Layouts.Sponge.byteSize]; omega)
  all_goals try (rw [hsp, hs8]; omega)
  all_goals try exact Nat.le_trans (Tactic.slot_le hS rfl) hpre_7
  all_goals try exact hret1_14.2.1
  -- the path `next` took
  all_goals try
    rcases Nat.lt_or_ge t.streamOffset t.proof.stream.length with ho | ho
    all_goals first
      | (rw [Rv64mc.Proof.Transcript.Next.next_some ho] at hret1_16
         obtain ⟨hres, ht1⟩ := hret1_16
         try exact absurd (tag_some hres) ‹¬ _›)
      | (rw [Rv64mc.Proof.Transcript.Next.next_none ho] at hret1_16
         try first
           | exact absurd ((tag_none hret1_16).symm.trans hc_2) (by decide)
           | exact absurd ((tag_none hret1_16).symm.trans hc) (by decide))
  all_goals try simpa using ht1.sponge
  all_goals try
    rw [List.getElem?_eq_getElem ho, Option.getD_some]
    have h0 := limbs_some hres
    rw [BitVec.add_assoc, BitVec.add_assoc, show (18446744073709551560#64 + 8#64 : Word) = 18446744073709551568#64
      by decide, show (18446744073709551560#64 + 16#64 : Word) = 18446744073709551576#64 by decide] at h0
    first | rw [h0.1] | rw [h0.2]
  -- after the calls: the saved registers through the callees' frames
  all_goals try
    have hm1 := fun (c : Word) (hc : Tactic.slotOk 32 c = true) =>
      hret1_14.getMem_above (a := top + c) (Tactic.slot_ge hS rfl)
        (by have := slot_ge_sub (k := 32) hS (by decide) hc; rw [hsp]; omega) fun h => by
          have := Tactic.slot_lt hS40 hc
          have := slot_ge_sub (k := 32) hS (by decide) hc
          simp only [Spec.Transcript.Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.ResultE.byteSize] at h
          rcases h with h | h
          · rw [hs8] at h; omega
          · have := congrArg BitVec.toNat h
            rw [toNat_add_ofNat (by simp only [Layouts.Transcript.stream_offset]; omega)] at this
            omega
  all_goals try
    have hm2 := fun (c : Word) (hc : Tactic.slotOk 32 c = true) =>
      hret2_14.getMem_above (a := top + c) (Tactic.slot_ge hS rfl)
        (by have := slot_ge_sub (k := 32) hS (by decide) hc; rw [hsp]; omega) fun h => by
          have := Tactic.slot_lt hS40 hc
          simp only [Spec.Transcript.AbsorbNonce.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.Sponge.byteSize] at h
          omega
  all_goals try
    first
      | (simp (disch := decide) only [hm2, hm1]
         simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq])
      | (simp (disch := decide) only [hm1]
         simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq])
  -- the frames
  all_goals try
    have hF1 : env.Frame top (Out regs m) m m1 := by
      refine Env.Frame.trans ?_ hret1_14 (Tactic.slot_le hS rfl) fun b hb => ?_
      · rv_close
      · simp only [Spec.Transcript.Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ↓reduceIte, Layouts.ResultE.byteSize] at hb
        rcases hb with hb | hb
        · exact Or.inl ⟨by have := hlo (18446744073709551552#64) rfl; omega, by rw [hs8] at hb; omega⟩
        · subst hb
          exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  all_goals try exact hF1
  all_goals try
    exact hF1.trans hret2_14 (Tactic.slot_le hS rfl) fun b hb => Or.inr (Or.inr (Or.inr (Or.inl (by
      simpa only [Spec.Transcript.AbsorbNonce.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
        ↓reduceIte, Layouts.Sponge.byteSize] using hb))))
  -- no bits: `Ok` at once
  all_goals try
    rw [show (regs .x11).toNat = 0 by rw [hc]; rfl, Model.grindCheck_zero]
    refine ⟨by decide, hpre_6.stack hpre_8 hpre_7 hpre_9 hpre_5 fun b hb => ?_⟩
    rcases hb with hb | hb
    · simp (disch := exact Nat.lt_of_lt_of_le hb (hlo _ rfl)) only [getMem_setMem_gt]
    · simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) hb) only [getMem_setMem_lt]
  all_goals
    have hbits : (regs .x11).toNat ≠ 0 := fun h => ‹¬ regs .x11 = 0#64› (BitVec.eq_of_toNat_eq (by simp [h]))
  -- `next`'s `Err`, passed on
  all_goals try
    rw [grind_none hbits ho]
    have he := err_none hret1_16
    rw [BitVec.add_assoc, show (18446744073709551560#64 + 8#64 : Word) = 18446744073709551568#64 by decide] at he
    exact he
  -- the nonce absorbed and permuted
  all_goals
    have hx : (t.proof.stream[t.streamOffset]?).getD 0 = t.proof.stream[t.streamOffset] := by
      rw [List.getElem?_eq_getElem ho]; rfl
    have hsp2 : SpongeAt m2 (regs .x10)
        ((t.sponge.absorbNonce (t.proof.stream[t.streamOffset]?.getD 0)).getD (0, t.sponge)).2 := by assumption
    rw [hx] at hret2_16 hsp2
    obtain ⟨⟨pow, s⟩, hs⟩ := Option.isSome_iff_exists.1 hret2_16
    rw [hs, Option.getD_some] at hsp2
    have hn1 : (env.next m).toNat ≤ (env.next m1).toNat := by
      have := hret1_14.1
      unfold Env.next at this ⊢
      simp (disch := exact Nat.lt_of_lt_of_le (by omega) (hlo _ rfl)) only [getMem_setMem_gt] at this
      exact this
    have hq1 : m1.getMem (regs .x10 + 328#64) = m.getMem (regs .x10 + 328#64) := by
      rw [hret1_14.getMem_above (a := regs .x10 + 328#64) (Tactic.slot_ge hS rfl) (by rw [hsp]; omega) fun h => by
        simp only [Spec.Transcript.Next.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
          ↓reduceIte, Layouts.ResultE.byteSize] at h
        rcases h with h | h
        · rw [hs8] at h; omega
        · exact absurd h (add_ne_add (n := 360) hpre_8 (by decide) (by decide) (by decide))]
      simp (disch := exact Nat.lt_of_lt_of_le (hst _ rfl) h328) only [getMem_setMem_lt]
    have hnA : ∀ b : Word, ¬ InRange (regs .x10) 328 b → (top + 18446744073709551552#64).toNat ≤ b.toNat ∨
        b.toNat < (env.next m1).toNat → m2.getMem b = m1.getMem b := fun b hb hb' => by
      rcases hb' with hb' | hb'
      · exact hret2_14.getMem_above (Tactic.slot_ge hS rfl) hb' fun h => by
          simp only [Spec.Transcript.AbsorbNonce.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.Sponge.byteSize] at h
          exact hb h
      · exact hret2_14.getMem_below_next hret1_14.2.1 hb' fun h => by
          simp only [Spec.Transcript.AbsorbNonce.Out, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq,
            ↓reduceIte, Layouts.Sponge.byteSize] at h
          exact hb h
    have hsafe1 : ProofSafe env m1 top (regs .x10) := by
      unfold ProofSafe
      unfold proofAddr at hpre_9 ⊢
      simp only [Layouts.Transcript.proof, Layouts.Proof.byteSize] at hpre_9 ⊢
      rw [hq1]
      rcases hpre_9 with hl | hl
      · left; unfold Env.Live at hl ⊢; omega
      · right; exact hl
    have T2 := ht1.through (M := m2) (s := s) (by simpa using hsp2) hpre_8 hpre_7 hsafe1 hret2_14.1
      hret1_14.2.1 hlim fun b hb hb' => hnA b hb (hb'.elim Or.inr fun h => Or.inl (by rw [hsp]; omega))
    have hck := T2.checked
    simp only [Layouts.Transcript.checked] at hck
    rw [grind_some hbits ho hs]
    simp only [hx, hs, Option.getD_some]
  · rw [hck] at hc
    rw [ite_eq_left (by rw [checked_of_byte hc]; rfl)]
    exact ⟨by decide, T2⟩
  · rw [hck] at hc
    have hc' := checked_of_byte' hc
    rw [mask_eq]
    by_cases hz : pow &&& Model.powMask (regs .x11).toNat = 0#64
    · rw [ite_eq_left (by simp [hz])]
      exact ⟨(tag3_iff _).2 hz, T2⟩
    · rw [ite_eq_right (by simp [hz, hc'])]
      exact fun h => hz ((tag3_iff _).1 h)

/-- **`Transcript::grind_check` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needN needA : Nat} (hnN : 64 + needN ≤ need) (hnA : 64 + needA ≤ need)
    (hnext : Spec.Transcript.Next.spec env p L.next.idx needN)
    (han : Spec.Transcript.AbsorbNonce.spec env p L.absorbNonce.idx needA) : spec env p i need :=
  ok_at env p i L hp hL hnN hnA hnext han

end Rv64mc.Proof.Transcript.GrindCheck
