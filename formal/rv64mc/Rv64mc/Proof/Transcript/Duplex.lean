/-
  Rv64mc.Proof.Transcript.Duplex

  `Sponge::duplex` keeps its contract (`Spec.Transcript.Duplex.spec`), from the contracts of `memcpy`, `memset`,
  `keccak_f` and `slice_index_fail`. The stack's alignment comes from the first store into the frame
  (`safe_aligned_store`). `rv_sym` runs to instruction 100, where the five paths of the waiting scalars' writes
  meet; there the buffer holds `duplex`'s input (`Inv`): its capacity copied from the state and its rate zeroed,
  byte by byte (`hbase`, `Bytes.lean`), and each waiting scalar's lanes over it (`hpend`, lane by lane against
  `Model.duplexLanes_getD`). From there `tail` runs the permutation, the copy back and the count's reset once.
-/

import Rv64mc.Spec.Transcript.Duplex
import Rv64mc.Spec.Hash.KeccakF
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Proof.Transcript.Common
import Rv64mc.Proof.Transcript.Bytes
import Rv64mc.Proof.Transcript.Trap
import Rv64mc.Proof.Transcript.SpongeMem
import Rv64mc.Model.Extra.Transcript
import Rv64mc.Gen.Tmpl.Verifier.Transcript.Sponge.Duplex
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Transcript.Duplex

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Transcript Rv64mc.Spec.Transcript.Duplex Rv64mc.Spec.Runtime
open Rv64mc.Proof.Transcript
open Rv64mc.Gen.Verifier.Transcript.Sponge.Duplex (Link tmpl)

/-- The state at the permutation's call (instruction 100, where the five paths of the waiting scalars' writes
    meet): the buffer at `sp` holds `duplex`'s input, everything else as at the entry but the saved registers. -/
def Inv (env : Env) (r : Model.SpongeRust) (ret top : Word) (regs : Reg → Word) (m : MachineState)
    (R : Reg → Word) (M : MachineState) : Prop :=
  R .x2 = top + 18446744073709551392#64 ∧ R .x8 = regs .x10 ∧ R .x9 = regs .x10 + 24#64 ∧
    R .x18 = regs .x18 ∧ R .x19 = regs .x19 ∧ R .x20 = regs .x20 ∧ R .x21 = regs .x21 ∧ R .x22 = regs .x22 ∧
    R .x23 = regs .x23 ∧ R .x24 = regs .x24 ∧ R .x25 = regs .x25 ∧ R .x26 = regs .x26 ∧ R .x27 = regs .x27 ∧
    (top + 18446744073709551392#64).toNat % 8 = 0 ∧
    WordsAt M (top + 18446744073709551392#64) (Model.duplexLanes r) ∧
    env.Frame top Tactic.F m M ∧
    M.getMem (top + 18446744073709551608#64) = ret ∧ M.getMem (top + 18446744073709551600#64) = regs .x8 ∧
    M.getMem (top + 18446744073709551592#64) = regs .x9

theorem tail (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC needK : Nat} (hnC : 224 + needC ≤ need) (hnK : 224 + needK ≤ need)
    (hcpy : MemcpySpec env p L.memcpy.idx needC) (hkf : Spec.Hash.KeccakF.spec env p L.keccakF.idx needK)
    (r : Model.SpongeRust) {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} {regs : Reg → Word} {m : MachineState}
    (hk : ∀ r' m', Holds.post env (Post r) Out ret top regs m r' m' →
      rvIsa.SafeN p sp1Ctx G n Q ⟨rest, r', m'⟩) (hsp16 : top.toNat % 16 = 0)
    (hstk : env.stackLimit.toNat + need ≤ top.toNat) (hst : env.Static m)
    (hnx : (env.next m).toNat ≤ env.heapEnd.toNat) (hs : SpongeAt m (regs .x10) r)
    (ha : InFrame top (regs .x10) Layouts.Sponge.byteSize) :
    ∀ R M, Inv env r ret top regs m R M → rvIsa.SafeN p sp1Ctx G n Q ⟨⟨i, 100, ret, top⟩ :: rest, R, M⟩ := by
  intro R M hinv
  rv_intro hinv
  rv_sym hp with [hL] using [hcpy, hkf (Model.duplexLanes r)]
  all_goals
    have hS : env.stackLimit.toNat + 224 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    obtain ⟨hta, hab⟩ := ha
    simp only [Layouts.Sponge.byteSize] at hab
    have hal := hs.aligned
    simp only [Layouts.Sponge.byteAlign] at hal
    have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := slot_toNat (by decide) (by omega) (by decide)
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := slot_toNat (by decide) (by omega) (by decide)
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := slot_toNat (by decide) (by omega) (by decide)
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := slot_toNat (by decide) (by omega) (by decide)
    have ha24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
    have ha320 : (regs .x10 + 320#64).toNat = (regs .x10).toNat + 320 := toNat_add_ofNat (by omega)
    have hal24 : alignToDword (regs .x10 + 24#64) = regs .x10 + 24#64 :=
      alignToDword_of_aligned hal (by decide) (by omega)
    have hlen := (Model.duplex_inv r hs.inv).1
    simp only [Model.SpongeRust.duplex] at hlen
  all_goals try
    have hk1 : ∀ b : Word, top.toNat - 224 + 200 ≤ b.toNat → m1.getMem b = M.getMem b :=
      fun b h1 => hret1_14.getMem_above (Tactic.slot_ge hS rfl) (by omega) fun h => by
        simp only [Spec.Hash.KeccakF.Out, Spec.Hash.KeccakF.stateBytes, InRange, Lprog.updReg_apply, Tactic.rf,
          reduceCtorEq, ↓reduceIte] at h
        omega
  all_goals try
    have hk2 : ∀ b : Word, top.toNat - 224 ≤ b.toNat → (b.toNat < (regs .x10).toNat + 24 ∨
        (regs .x10).toNat + 224 ≤ b.toNat) → m2.getMem b = m1.getMem b :=
      fun b h1 h2 => hret2_14.getMem_above (Tactic.slot_ge hS rfl) (by omega) fun h => by
        simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hal24,
          BitVec.toNat_ofNat] at h
        omega
  -- the permutation's and the copy's preconditions
  all_goals try (rw [Model.duplexLanes_length]; exact hs.inv.1)
  all_goals try exact Or.inr (Nat.le_refl _)
  all_goals try (simp only [Spec.Hash.KeccakF.stateBytes]; omega)
  all_goals try exact hret1_14.2.1
  all_goals try (simp only [BitVec.toNat_ofNat]; omega)
  all_goals try
    intro _ b h1 h2
    simp only [InRange, BitVec.toNat_ofNat] at h1 h2
    omega
  -- the saved registers
  all_goals try
    rw [getMem_setMem_gt (by omega), hk2 _ (by omega) (Or.inl (by omega)), hk1 _ (by omega)]
    simp only [hinv_17, hinv_18, hinv_19]
  -- the frame, the static data
  all_goals try
    refine frame_store_obj (k := 320) ?_ hlim hta hab (by decide)
      (show InRange _ 328 _ from inRange_add hab (by decide))
    refine Env.Frame.trans (Env.Frame.trans (Tactic.frame_weaken hinv_16) hret1_14 (Tactic.slot_le hS rfl)
      fun b hb => Or.inl ?_) hret2_14 (Tactic.slot_le hS rfl) fun b hb => Or.inr (Or.inr (Or.inr ?_))
    · simp only [Spec.Hash.KeccakF.Out, Spec.Hash.KeccakF.stateBytes, InRange, Lprog.updReg_apply, Tactic.rf,
        reduceCtorEq, ↓reduceIte] at hb
      omega
    · simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte, hal24,
        BitVec.toNat_ofNat] at hb
      show InRange _ 328 _
      unfold InRange; omega
  all_goals try exact static_store_obj (k := 320) hret2_15 hlim hta hab (by decide)
  -- the sponge, permuted
  · have hw : WordsAt m2 (regs .x10 + 24#64) (Model.keccakFRust (Model.duplexLanes r)) :=
      WordsAt.of_copy hret1_16 (by omega) hinv_14 (by omega) fun k hk => hret2_17 k (by simp; omega)
    refine ⟨hal, Model.duplex_inv r hs.inv, ?_, fun k hk => by simp at hk, ?_, ?_⟩
    · simp only [Layouts.Sponge.state, Model.SpongeRust.duplex]
      exact hw.keep (Keeps.setMem fun h => by unfold InRange at h; omega)
    · simp only [Layouts.Sponge.n_pending, Model.duplex_nPending]
      exact MachineState.getMem_setMem_eq
    · have hg := hs.ground
      simp only [Layouts.Sponge.ground, Model.duplex_ground] at hg ⊢
      refine OptionEAt.congr hg fun k hk => ?_
      rw [show regs .x10 + 0#64 = regs .x10 from BitVec.add_zero _]
      have hk' : (regs .x10 + BitVec.ofNat 64 k).toNat = (regs .x10).toNat + k := toNat_add_ofNat (by omega)
      rw [getMem_setMem_gt (by omega), hk2 _ (by omega) (Or.inl (by omega)), hk1 _ (by omega)]
      exact Tactic.frame_above hinv_16 hlim _ (BitVec.le_def.2 (by omega))

/-- **`Sponge::duplex` keeps its contract**, for one sponge. -/
theorem ok_at (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC needS needK needF : Nat} (hnC : 224 + needC ≤ need) (hnS : 224 + needS ≤ need)
    (hnK : 224 + needK ≤ need) (hnF : 224 + needF ≤ need)
    (hcpy : MemcpySpec env p L.memcpy.idx needC) (hset : MemsetSpec env p L.memset.idx needS)
    (hkf : Spec.Hash.KeccakF.spec env p L.keccakF.idx needK)
    (hfail : NoReturn env p L.sliceIndexFail.idx needF) (r : Model.SpongeRust) :
    Holds env p i need (Pre r) (Post r) Out := by
  rv_auto hp stop [3] with [hL] using [hcpy, hset, hfail]
  refine safe_aligned_store (x := top + 18446744073709551392#64 + 216#64) hp rfl rfl fun hal => ?_
  rv_sym hp stop [100] with [hL] using [hcpy, hset, hfail]
  all_goals
    have hS : env.stackLimit.toNat + 224 ≤ top.toNat := by omega
    have hlim : env.stackLimit.toNat ≤ top.toNat := by omega
    rw [hpre_2] at hpre_7
    simp only [Layouts.Sponge.byteSize] at hpre_8
    have hal' := hpre_6.aligned
    simp only [Layouts.Sponge.byteAlign] at hal'
    have hsp : (top + 18446744073709551392#64).toNat = top.toNat - 224 := slot_toNat (by decide) (by omega) (by decide)
    have hsp8 : (top + 18446744073709551392#64).toNat % 8 = 0 := by
      rw [BitVec.add_assoc, show (18446744073709551392#64 + 216#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 8) by decide,
        toNat_sub_lit (by omega) (by decide)] at hal
      omega
    have ha24 : (regs .x10 + 24#64).toNat = (regs .x10).toNat + 24 := toNat_add_ofNat (by omega)
  -- the copy's and the fill's preconditions
  all_goals try (simp only [BitVec.toNat_ofNat]; omega)
  all_goals try exact hret1_14.2.1
  all_goals try exact hret2_14.2.1
  all_goals try
    intro _ b h1 h2
    simp only [InRange, BitVec.toNat_ofNat] at h1 h2
    omega
  -- the five paths meet before the permutation
  all_goals
    have hst : ∀ c : Word, Tactic.slotOk 224 c = true → (top + c).toNat < top.toNat :=
      fun c hc => Tactic.slot_lt hS hc
    have hF2 : env.Frame top Tactic.F m m2 := by
      refine Env.Frame.trans (Env.Frame.trans ?_ hret1_14 (Tactic.slot_le hS rfl) fun b hb => Or.inl ?_) hret2_14
        (Tactic.slot_le hS rfl) fun b hb => Or.inl ?_
      · rv_close
      · simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
          BitVec.toNat_ofNat, toNat_alignToDword] at hb
        omega
      · simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
          BitVec.toNat_ofNat, toNat_alignToDword] at hb
        omega
    have hm2 : ∀ b : Word, top.toNat ≤ b.toNat → m2.getMem b = m.getMem b :=
      fun b hb => Tactic.frame_above hF2 hlim b (BitVec.le_def.2 hb)
    have hcount : m2.getMem (regs .x10 + 320#64) = BitVec.ofNat 64 r.nPending := by
      rw [hm2 _ (by rw [toNat_add_ofNat (by omega)]; omega)]
      simpa [Layouts.Sponge.n_pending] using hpre_6.nPending
    rw [hcount] at hc
    have h8 : (top + 18446744073709551608#64).toNat = top.toNat - 8 := slot_toNat (by decide) (by omega) (by decide)
    have h16 : (top + 18446744073709551600#64).toNat = top.toNat - 16 := slot_toNat (by decide) (by omega) (by decide)
    have h24 : (top + 18446744073709551592#64).toNat = top.toNat - 24 := slot_toNat (by decide) (by omega) (by decide)
    refine tail env p i L hp hL hnC hnK hcpy hkf r hk hpre_9 hpre_3 hpre_4 hpre_5 hpre_6 ⟨hpre_7, hpre_8⟩ _ _ ?_
    rv_close
  -- the saved registers, past the waiting scalars' stores, the fill and the copy
  all_goals try
    simp (disch := decide) only [getMem_setMem_off]
  all_goals try
    first
      | rw [hret2_14.getMem_above (a := top + 18446744073709551608#64) (Tactic.slot_ge hS rfl)
          (slot_mono hS rfl rfl rfl) fun h => by
            simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
              BitVec.toNat_ofNat, toNat_alignToDword] at h
            omega,
          hret1_14.getMem_above (a := top + 18446744073709551608#64) (Tactic.slot_ge hS rfl)
          (slot_mono hS rfl rfl rfl) fun h => by
            simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
              BitVec.toNat_ofNat, toNat_alignToDword] at h
            omega]
      | rw [hret2_14.getMem_above (a := top + 18446744073709551600#64) (Tactic.slot_ge hS rfl)
          (slot_mono hS rfl rfl rfl) fun h => by
            simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
              BitVec.toNat_ofNat, toNat_alignToDword] at h
            omega,
          hret1_14.getMem_above (a := top + 18446744073709551600#64) (Tactic.slot_ge hS rfl)
          (slot_mono hS rfl rfl rfl) fun h => by
            simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
              BitVec.toNat_ofNat, toNat_alignToDword] at h
            omega]
      | rw [hret2_14.getMem_above (a := top + 18446744073709551592#64) (Tactic.slot_ge hS rfl)
          (slot_mono hS rfl rfl rfl) fun h => by
            simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
              BitVec.toNat_ofNat, toNat_alignToDword] at h
            omega,
          hret1_14.getMem_above (a := top + 18446744073709551592#64) (Tactic.slot_ge hS rfl)
          (slot_mono hS rfl rfl rfl) fun h => by
            simp only [CopyOut, DwordsOf, InRange, Lprog.updReg_apply, Tactic.rf, reduceCtorEq, ↓reduceIte,
              BitVec.toNat_ofNat, toNat_alignToDword] at h
            omega]
    simp (disch := decide) only [getMem_setMem_off, MachineState.getMem_setMem_eq]
  -- the buffer: zeros, the state's capacity, the waiting scalars' lanes
  all_goals
    have hsk : ∀ k, k < 25 → (top + 18446744073709551392#64 + BitVec.ofNat 64 (8 * k)).toNat =
        top.toNat - 224 + 8 * k := fun k hk => by rw [toNat_add_ofNat (by omega)]; omega
    have hbase : ∀ k, k < 25 → m2.getMem (top + 18446744073709551392#64 + BitVec.ofNat 64 (8 * k)) =
        if k < 16 then 0#64 else r.state.getD k 0 := fun k hk => by
      by_cases h16 : k < 16
      · simp only [h16, ↓reduceIte]
        refine getMem_of_zero_bytes (by rw [hsk k hk]; omega) fun j hj => ?_
        rw [add_ofNat_lit, hret2_17 (8 * k + j) (by simp; omega)]
        rfl
      · simp only [h16, ↓reduceIte]
        have hw := hpre_6.state.2 k (by rw [hpre_6.inv.1]; exact hk)
        rw [List.getD_eq_getElem _ _ (by rw [hpre_6.inv.1]; omega), ← hw]
        refine getMem_of_bytes (by rw [hsk k hk]; omega)
          (by simp only [Layouts.Sponge.state]; rw [add_ofNat_lit, toNat_add_ofNat (by omega)]; omega)
          fun j hj => ?_
        have hx : (regs .x10 + 24#64 + BitVec.ofNat 64 (8 * k + j)).toNat = (regs .x10).toNat + 24 + 8 * k + j := by
          rw [toNat_add_ofNat (by omega), ha24]; omega
        rw [show top + 18446744073709551392#64 + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j =
            top + 18446744073709551392#64 + BitVec.ofNat 64 (8 * k + j) from add_ofNat_lit,
          show regs .x10 + BitVec.ofNat 64 Layouts.Sponge.state + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j =
            regs .x10 + 24#64 + BitVec.ofNat 64 (8 * k + j) from add_ofNat_lit,
          hret2_18 _ fun h => by
            unfold InRange at h
            rw [toNat_add_ofNat (a := top + 18446744073709551392#64) (k := 8 * k + j) (by omega)] at h
            simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h; omega,
          hret1_17 (8 * k + j) (by simp only [BitVec.toNat_ofNat]; omega)]
        apply getByte_congr
        simp (disch := (refine Nat.lt_of_lt_of_le (hst _ rfl) ?_; rw [toNat_alignToDword, hx]; omega)) only
          [getMem_setMem_lt]
    have hn4 := hpre_6.inv.2.2
    have hl25 := hpre_6.inv.1
  all_goals try have hn : r.nPending = 0 := (ofNat_inj (by omega) (by decide)).1 hc
  all_goals try have hn : r.nPending = 1 := (ofNat_inj (by omega) (by decide)).1 hc
  all_goals try have hn : r.nPending = 2 := (ofNat_inj (by omega) (by decide)).1 hc
  all_goals try have hn : r.nPending = 3 := (ofNat_inj (by omega) (by decide)).1 hc
  all_goals try
    rw [hcount] at hc_2 hc_3 hc_4
    have hn : r.nPending = 4 := by
      have : r.nPending ≠ 0 := fun h => hc_2 (by rw [h])
      have : r.nPending ≠ 1 := fun h => hc_3 (by rw [h])
      have : r.nPending ≠ 2 := fun h => hc_4 (by rw [h])
      have : r.nPending ≠ 3 := fun h => hc (by rw [h])
      omega
  all_goals
    have hpend : ∀ j, j < r.nPending →
        m2.getMem (regs .x10 + BitVec.ofNat 64 (224 + 24 * j)) =
          (Model.limbs ((r.pending.take r.nPending).getD j (0, 0#64)).1).1 ∧
        m2.getMem (regs .x10 + BitVec.ofNat 64 (232 + 24 * j)) =
          (Model.limbs ((r.pending.take r.nPending).getD j (0, 0#64)).1).2 ∧
        m2.getMem (regs .x10 + BitVec.ofNat 64 (240 + 24 * j)) = ((r.pending.take r.nPending).getD j (0, 0#64)).2 :=
      fun j hj => by
        have hp4 := hpre_6.inv.2.1
        have hjl : j < (r.pending.take r.nPending).length := by simp; omega
        obtain ⟨⟨e0, e1⟩, e2⟩ := hpre_6.pending j hjl
        simp only [pendingSlot, pendingTag, Layouts.Sponge.pending, Layouts.Sponge.n_pending, Layouts.E.c0,
          Layouts.E.c1, Layouts.E.byteSize, add_ofNat_lit] at e0 e1 e2
        rw [List.getD_eq_getElem _ _ hjl]
        have hb : ∀ c, c ≤ 320 → top.toNat ≤ (regs .x10 + BitVec.ofNat 64 c).toNat := fun c hc => by
          rw [toNat_add_ofNat (by omega)]; omega
        rw [hm2 _ (hb _ (by omega)), hm2 _ (hb _ (by omega)), hm2 _ (hb _ (by omega)),
          show 224 + 24 * j = 224 + (320 - 224) / 4 * j + 0 by omega,
          show 232 + 24 * j = 224 + (320 - 224) / 4 * j + 8 by omega,
          show 240 + 24 * j = 224 + ((320 - 224) / 4 * j + 16) by omega]
        exact ⟨e0, e1, e2⟩
  all_goals
    refine ⟨by rw [Model.duplexLanes_length, hl25]; omega, fun k hk => ?_⟩
    have hk25 : k < 25 := by rwa [Model.duplexLanes_length, hl25] at hk
    rw [← List.getD_eq_getElem _ 0 hk, Model.duplexLanes_getD r hpre_6.inv k]
    have hb := hbase k hk25
    interval_cases k <;>
      simp (disch := decide) only [hn, BitVec.add_assoc, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.reduceLT, ↓reduceIte, BitVec.reduceAdd, getMem_setMem_off, MachineState.getMem_setMem_eq,
        Model.pendingWords, List.getD_cons_zero, List.getD_cons_succ] at hb ⊢
  all_goals
    have hball : ∀ (c : Word) (k : Nat), Tactic.slotOk 224 c = true → Nat.ble k 328 = true →
        (top + c).toNat < (regs .x10 + BitVec.ofNat 64 k).toNat := fun c k hc hk =>
      slot_below (K := 328) hS hc hpre_7 hpre_8 hk
    try simp (disch := (apply hball <;> decide)) only [getMem_setMem_lt]
  all_goals
    first
      | simp only [hb, BitVec.ofNat_eq_ofNat]
      | (have hj : 0 < r.nPending := by omega
         obtain ⟨e0, e1, e2⟩ := hpend 0 hj
         simp only [hn, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2
         simp only [e0, e1, e2])
      | (have hj : 1 < r.nPending := by omega
         obtain ⟨e0, e1, e2⟩ := hpend 1 hj
         simp only [hn, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2
         simp only [e0, e1, e2])
      | (have hj : 2 < r.nPending := by omega
         obtain ⟨e0, e1, e2⟩ := hpend 2 hj
         simp only [hn, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2
         simp only [e0, e1, e2])
      | (have hj : 3 < r.nPending := by omega
         obtain ⟨e0, e1, e2⟩ := hpend 3 hj
         simp only [hn, Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2
         simp only [e0, e1, e2])

/-- **`Sponge::duplex` keeps its contract.** -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) {need needC needS needK needF : Nat} (hnC : 224 + needC ≤ need) (hnS : 224 + needS ≤ need)
    (hnK : 224 + needK ≤ need) (hnF : 224 + needF ≤ need)
    (hcpy : MemcpySpec env p L.memcpy.idx needC) (hset : MemsetSpec env p L.memset.idx needS)
    (hkf : Spec.Hash.KeccakF.spec env p L.keccakF.idx needK)
    (hfail : NoReturn env p L.sliceIndexFail.idx needF) : spec env p i need :=
  ok_at env p i L hp hL hnC hnS hnK hnF hcpy hset hkf hfail

end Rv64mc.Proof.Transcript.Duplex
