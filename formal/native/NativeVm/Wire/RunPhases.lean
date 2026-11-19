module

public import NativeVm.Wire.RunPhase

/-!
# The phases

`phases` reads the phase count, at most `wireMaxPhases`, then decodes the phases one after the
other, phase `k` at `phaseBase L k`, as `allPhasesM` (`phases_ok`): one more pass of its loop
appends one phase to `phasesM` (`phasesM_snoc`), or fails where `phaseM` does (`phasesM_none`).
-/

@[expose] public section

namespace NativeVm.Wire

open Native LeanVM.Parameters LeanVM.Protocol.Compile
open Native.SphincsVerifier (toUInt64_add toUInt64_sub toUInt64_shl toUInt64_shr cond_ne_imm)

/-- The phase count, at most `wireMaxPhases`, then the phases, from `c`. -/
def allPhasesM (B : List UInt8) (c : Nat) : Option (List PhaseOut × Nat) := do
  let (p, c) ← rdU32 B c
  if wireMaxPhases < p then none
  phasesM B p c

/-- The model, its phases as `allPhasesM`. -/
theorem decodeM_eq (B : List UInt8) : decodeM B = (streamM B 0).bind fun r ↦
    (allPhasesM B r.2).bind fun t ↦ if t.2 ≠ B.length then none else some (r.1, t.1) := by
  unfold decodeM allPhasesM
  cases streamM B 0 with
  | none => rfl
  | some r =>
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases rdU32 B r.2 with
  | none => rfl
  | some q =>
  simp only [Option.bind_some]
  by_cases hq : wireMaxPhases < q.1
  · simp [hq]
  · simp only [hq, ite_false]
    cases phasesM B q.1 q.2 <;> rfl

/-- One more phase after `k`. -/
theorem phasesM_snoc (B : List UInt8) (k : Nat) : ∀ {c c1 c2 : Nat} {ps : List PhaseOut}
    {p : PhaseOut}, phasesM B k c = some (ps, c1) → phaseM B c1 = some (p, c2) →
      phasesM B (k + 1) c = some (ps ++ [p], c2) := by
  induction k with
  | zero =>
    intro c c1 c2 ps p h hp
    simp only [phasesM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [phasesM, hp]
  | succ k ih =>
    intro c c1 c2 ps p h hp
    rw [phasesM.eq_2] at h ⊢
    simp only [Option.bind_eq_bind] at h ⊢
    cases h1 : phaseM B c with
    | none => simp [h1] at h
    | some q =>
      obtain ⟨a, c3⟩ := q
      simp only [h1, Option.bind_some] at h ⊢
      cases h2 : phasesM B k c3 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨ps', c4⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih h2 hp]
        rfl

/-- A phase failing after `k` fails every longer run. -/
theorem phasesM_none (B : List UInt8) (k : Nat) : ∀ {c c1 m : Nat} {ps : List PhaseOut},
    phasesM B k c = some (ps, c1) → phaseM B c1 = none → phasesM B (k + m + 1) c = none := by
  induction k with
  | zero =>
    intro c c1 m ps h hp
    simp only [phasesM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Nat.zero_add]
    simp [phasesM, hp]
  | succ k ih =>
    intro c c1 m ps h hp
    rw [show k + 1 + m + 1 = (k + m + 1) + 1 by omega, phasesM.eq_2]
    rw [phasesM.eq_2] at h
    simp only [Option.bind_eq_bind] at h ⊢
    cases h1 : phaseM B c with
    | none => simp
    | some q =>
      obtain ⟨a, c2⟩ := q
      simp only [h1, Option.bind_some] at h ⊢
      cases h2 : phasesM B k c2 with
      | none => simp [h2] at h
      | some q =>
        obtain ⟨ps', c3⟩ := q
        simp only [h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih h2 hp]
        rfl

theorem openingWords_val : openingWords = 193 := rfl

theorem phaseWords_val : phaseWords = 49411 := rfl

/-- A word of opening `j < wireMaxQueries` lies in its phase's words. -/
theorem ob_lt {j k : Nat} (hj : j < wireMaxQueries) (hk : k < openingWords) :
    3 + j * openingWords + k < phaseWords := by
  have hq : wireMaxQueries = 256 := rfl
  rw [openingWords_val] at hk ⊢
  rw [phaseWords_val]
  omega

theorem phaseBase_succ (L k : Nat) : phaseBase L (k + 1) = phaseBase L k + phaseWords := by
  unfold phaseBase; rw [Nat.succ_mul]; omega

theorem phaseBase_mono (L : Nat) {j k : Nat} (h : j ≤ k) : phaseBase L j ≤ phaseBase L k := by
  unfold phaseBase; have := Nat.mul_le_mul_right phaseWords h; omega

/-- A decoded phase survives where its words do. -/
theorem PhaseAt.same {D D' : Nat → UInt64} {S : Nat → Prop} {base : Nat} {po : PhaseOut}
    (h : PhaseAt D base po) (hs : Same S D D')
    (hd : ∀ i, base ≤ i → i < base + phaseWords → ¬ S i) : PhaseAt D' base po := by
  have hq : wireMaxQueries = 256 := rfl
  have hml : wireMaxLeafWords = 64 := rfl
  have hmh : wireMaxHeight = 32 := rfl
  have hop := openingWords_val
  have hpw := phaseWords_val
  obtain ⟨a, b, c, d0, d1, d2, hj⟩ := h
  refine ⟨a, b, c, by rw [hs _ (hd _ le_rfl (by omega))]; exact d0,
    by rw [hs _ (hd _ (by omega) (by omega))]; exact d1,
    by rw [hs _ (hd _ (by omega) (by omega))]; exact d2, fun j hjl ↦ ?_⟩
  obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hj j hjl
  have hjq : j < wireMaxQueries := by omega
  refine ⟨x1, x2, x3, ?_, fun t ht ↦ ?_, fun d hd' l hl ↦ ?_⟩
  · have := ob_lt hjq (k := 0) (by omega)
    rw [hs _ (hd _ (by omega) (by omega))]; exact x4
  · have := ob_lt hjq (k := 1 + t) (by omega)
    rw [hs _ (hd _ (by omega) (by omega))]; exact x5 t ht
  · have := ob_lt hjq (k := 1 + wireMaxLeafWords + 4 * d + l) (by omega)
    rw [hs _ (hd _ (by omega) (by omega))]; exact x6 d hd' l hl

theorem streamEnd_lt_dn (L : Nat) : streamEnd L < decodedWords L := by
  unfold decodedWords phaseBase; omega

section Run

variable {e : Env} (P : Pre e)
include P

variable {s : QState} {D W : Nat → UInt64}

/-- **The phases.** -/
theorem phases_ok (hI : Inv e s D W) {c : Nat} (hp : s.reg .r15 = c.toUInt64) (hc : c ≤ e.L) :
    WP phases s (fun s' ↦ ∃ phs c', allPhasesM e.B c = some (phs, c') ∧ c' ≤ e.L ∧ ∃ D' W',
      Inv e s' D' W' ∧ phs.length ≤ wireMaxPhases ∧ D' (streamEnd e.L) = phs.length.toUInt64 ∧
      (∀ k (hk : k < phs.length), PhaseAt D' (phaseBase e.L k) phs[k]) ∧
      Same (fun k ↦ streamEnd e.L ≤ k) D D' ∧ s'.reg .r15 = c'.toUInt64)
      (fun s' ↦ allPhasesM e.B c = none ∧ Kept e s') := by
  have hL := P.L32
  have hmp : wireMaxPhases = 8 := rfl
  have hdn : decodedWords e.L = phaseBase e.L wireMaxPhases := rfl
  unfold phases
  apply WP.blk_cons
  refine WP.mono (getU32_ok P hI hp hc) (fun s1 ⟨n, hn1, hn32, h1, hb1, hr1, hf1⟩ ↦ ?_)
    (fun s1 ⟨hno, hk⟩ ↦ ⟨by simp [allPhasesM, hno], hk⟩)
  apply WP.blk_cons
  refine wp_failIf (fun hc1 ↦ ⟨?_, h1.kept⟩) fun hc1 ↦ ?_
  · rw [cond_geu_imm hb1 (k := 9) (K := 9) rfl hn32 (by norm_num), decide_eq_true_iff] at hc1
    simp [allPhasesM, hn1, show wireMaxPhases < n by omega]
  rw [cond_geu_imm hb1 (k := 9) (K := 9) rfl hn32 (by norm_num), decide_eq_false_iff_not] at hc1
  refine blk_load_ctx P h1 (eval_cw s1 h1.rdi cLen) (by decide) P.c1 ?_
  step; step
  refine blk_load_ctx P (h1.setReg (d := .rax) (by decide) _)
    (eval_cw _ (by simpa using h1.rdi) cDec) (by decide) P.c8 ?_
  step
  have hax : e.L.toUInt64 >>> Nat.toUInt64 4 <<< Nat.toUInt64 4 + e.da =
      adr e.da (2 * (e.L / 16)) := by
    rw [toUInt64_shr (by norm_num) (by omega), toUInt64_shl (by norm_num) (by omega), adr,
      UInt64.add_comm]
    rw [show e.L / 2 ^ 4 * 2 ^ 4 = 8 * (2 * (e.L / 16)) by
      rw [show (2 : Nat) ^ 4 = 16 from rfl]; omega]
  rw [hax]
  have hse := streamEnd_lt_dn e.L
  refine blk_store_dec P (((h1.setReg (d := .rax) (by decide) _).setReg (d := .rcx) (by decide)
    _).setReg (d := .rax) (by decide) _) (k := streamEnd e.L)
    (by rw [eval_rw _ .rax (a := e.da) (j := 2 * (e.L / 16)) (by simp) 1]; congr 1
        unfold streamEnd maxStream; omega)
    hse fun s3 h3 r3 ↦ ?_
  have hrax3 : s3.reg .rax = adr e.da (2 * (e.L / 16)) := by rw [r3]; simp
  have hrbx3 : s3.reg .rbx = n.toUInt64 := by rw [r3]; simp [hb1]
  have hr15_3 : s3.reg .r15 = (c + 4).toUInt64 := by rw [r3]; simp [hr1]
  simp only [QState.setReg_reg, reduceCtorEq, ite_false, hb1] at h3
  step
  rw [hrax3]
  have hb0 : adr e.da (2 * (e.L / 16)) + (16 : Int64).toUInt64 = adr e.da (phaseBase e.L 0) := by
    rw [show (16 : Int64).toUInt64 = (8 * 2 : Nat).toUInt64 from rfl, adr_add]
    congr 1; unfold phaseBase streamEnd maxStream; omega
  rw [hb0]
  refine blk_load_ctx P (h3.setReg (d := .rax) (by decide) _) (eval_cw _ (by simp [h3.rdi]) cWork)
    (by decide) P.c10 ?_
  have hwk : ∀ k, k < 2 ^ 10 → k < workWords := fun k hk ↦ by
    unfold workWords wLeaf wSib wSibN wPar wNode wFL wP wQ; omega
  refine blk_store_work P ((h3.setReg (d := .rax) (by decide) _).setReg (d := .rcx) (by decide) _)
    (k := wPB) (by rw [eval_rw _ .rcx (a := e.wk) (j := 0) (by simp [adr_zero]) wPB, Nat.zero_add])
    (hwk _ (by unfold wPB; omega)) fun s4 h4 r4 ↦ ?_
  refine blk_store_work P h4 (k := wPN)
    (by rw [eval_rw _ .rcx (a := e.wk) (j := 0) (by rw [r4]; simp [adr_zero]) wPN, Nat.zero_add])
    (hwk _ (by unfold wPN; omega)) fun s5 h5 r5 ↦ ?_
  simp only [QState.setReg_reg, reduceCtorEq, ite_true, ite_false, r4, hrbx3] at h5
  have hrbx5 : s5.reg .rbx = n.toUInt64 := by rw [r5, r4]; simp [hrbx3]
  have hr15_5 : s5.reg .r15 = (c + 4).toUInt64 := by rw [r5, r4]; simp [hr15_3]
  step
  have hwpb : wPB ≠ wPN := by unfold wPB wPN; omega
  have hpk : ∀ k, k ≤ n → phaseBase e.L k ≤ decodedWords e.L := fun k hk ↦ by
    rw [hdn]; exact phaseBase_mono _ (by omega)
  apply WP.blk_cons
  let Iv : QState → Prop := fun t ↦ ∃ k phs c' D' W', k ≤ n ∧
    phasesM e.B k (c + 4) = some (phs, c') ∧ phs.length = k ∧ c' ≤ e.L ∧ Inv e t D' W' ∧
    W' wPB = adr e.da (phaseBase e.L k) ∧ W' wPN = (n - k).toUInt64 ∧
    t.reg .rbp = (n - k).toUInt64 ∧ t.reg .r15 = c'.toUInt64 ∧ D' (streamEnd e.L) = n.toUInt64 ∧
    (∀ j (hj : j < phs.length), PhaseAt D' (phaseBase e.L j) phs[j]) ∧
    Same (fun i ↦ streamEnd e.L ≤ i) D D'
  have hall : ∀ {k phs c'}, phasesM e.B k (c + 4) = some (phs, c') → k = n →
      allPhasesM e.B c = some (phs, c') := fun h hk ↦ by
    rw [hk] at h
    simp only [allPhasesM, hn1, Option.bind_eq_bind, Option.bind_some,
      show ¬ wireMaxPhases < n by omega, ite_false, h]
  refine WP.mono (WP.loop Iv (fun t ↦ (t.reg .rbp).toNat) ?_ ?_ ?_) (fun _ h ↦ WP.blk_nil h)
    (fun _ h ↦ h)
  · refine ⟨0, [], c + 4, _, _, by omega, rfl, rfl,
      by have := rdU32_le hn1; rw [B_length P] at this; omega,
      h5.setReg (by decide) _, ?_, ?_, ?_, ?_, ?_, fun j hj ↦ absurd hj (by simp), ?_⟩
    · rw [Function.update_of_ne hwpb, Function.update_self]
    · rw [Function.update_self]; rfl
    · simp [hrbx5]
    · simp [hr15_5]
    · rw [Function.update_self]
    · exact (Same.refl _ D).update (S := fun i ↦ streamEnd e.L ≤ i) le_rfl _
  · intro t ⟨k, phs, c', D', W', hk, hph, hlen, hc', hIt, hpb, hpn, hbp, hr15, hD', hat, hsame⟩ hcnd
    rw [cond_ne_imm hbp (k := 0) (K := 0) rfl (by omega) (by norm_num), decide_eq_true_iff] at hcnd
    have hkn : k < n := by omega
    apply WP.blk_cons
    refine WP.mono (phase_ok P hIt hr15 hc' hpb (by rw [← phaseBase_succ]; exact hpk _ hkn))
      (fun s4 ⟨po, c2, hpm, hc2, D4, W4, h4, hat4, hsame4, hwpb4, hwpn4, hr15'⟩ ↦ ?_)
      (fun s4 ⟨hno, hkp⟩ ↦ ⟨?_, hkp⟩)
    swap
    · have := phasesM_none e.B k (m := n - k - 1) hph hno
      rw [show k + (n - k - 1) + 1 = n by omega] at this
      simp only [allPhasesM, hn1, Option.bind_eq_bind, Option.bind_some,
        show ¬ wireMaxPhases < n by omega, ite_false, this]
    refine blk_load_ctx P h4 (eval_cw s4 h4.rdi cWork) (by decide) P.c10 ?_
    refine blk_load_work (h4.setReg (d := .rcx) (by decide) _) (k := wPB)
      (by rw [eval_rw _ .rcx (a := e.wk) (j := 0) (by simp [adr_zero]) wPB, Nat.zero_add])
      (hwk _ (by unfold wPB; omega)) ?_
    rw [hwpb4, hpb]
    step
    rw [wd_toUInt64, adr_add, ← phaseBase_succ]
    refine blk_store_work P ((h4.setReg (d := .rcx) (by decide) _).setReg (d := .rax) (by decide) _)
      (k := wPB)
      (by rw [eval_rw _ .rcx (a := e.wk) (j := 0) (by simp [adr_zero]) wPB, Nat.zero_add])
      (hwk _ (by unfold wPB; omega)) fun s5 h5 r5 ↦ ?_
    refine blk_load_work h5 (k := wPN)
      (by rw [eval_rw _ .rcx (a := e.wk) (j := 0) (by rw [r5]; simp [adr_zero]) wPN,
        Nat.zero_add])
      (hwk _ (by unfold wPN; omega)) ?_
    rw [Function.update_of_ne hwpb.symm, hwpn4, hpn]
    step
    rw [show (1 : Int64).toUInt64 = (1 : Nat).toUInt64 from rfl, toUInt64_sub (by omega),
      Nat.sub_sub]
    refine blk_store_work P (h5.setReg (d := .rbp) (by decide) _) (k := wPN)
      (by rw [eval_rw _ .rcx (a := e.wk) (j := 0) (by simp [r5, adr_zero]) wPN, Nat.zero_add])
      (hwk _ (by unfold wPN; omega)) fun s6 h6 r6 ↦ ?_
    simp only [QState.setReg_reg, ite_true] at h6
    apply WP.blk_nil
    have hbk : streamEnd e.L < phaseBase e.L k := by unfold phaseBase; omega
    refine ⟨⟨k + 1, phs ++ [po], c2, D4, _, by omega, phasesM_snoc e.B k hph hpm,
      by simp [hlen], hc2, h6, ?_, ?_, ?_, ?_, ?_, fun j hj ↦ ?_, ?_⟩, ?_⟩
    · rw [Function.update_of_ne hwpb, Function.update_self]
    · rw [Function.update_self, Nat.sub_add_eq]
    · simp [r6, Nat.sub_add_eq]
    · rw [r6]; simp [r5, hr15']
    · rw [hsame4 _ (by omega), hD']
    · simp only [List.length_append, List.length_cons, List.length_nil] at hj
      by_cases hjk : j < phs.length
      · rw [List.getElem_append_left hjk]
        refine (hat j hjk).same hsame4 fun i hi1 hi2 ⟨hi3, _⟩ ↦ ?_
        have := phaseBase_mono e.L (show j + 1 ≤ k by omega)
        rw [phaseBase_succ] at this
        omega
      · rw [List.getElem_append_right (by omega)]
        obtain rfl : j = k := by omega
        simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
        exact hat4
    · exact hsame.trans (hsame4.mono fun i hi ↦ by omega)
    · simp only [r6, QState.setReg_reg, ite_true, hbp]
      rw [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
      omega
  · intro t ⟨k, phs, c', D', W', hk, hph, hlen, hc', hIt, hpb, hpn, hbp, hr15, hD', hat, hsame⟩ hcnd
    rw [cond_ne_imm hbp (k := 0) (K := 0) rfl (by omega) (by norm_num), decide_eq_false_iff_not,
      not_not] at hcnd
    have hkn : k = n := by omega
    exact ⟨phs, c', hall hph hkn, hc', D', W', hIt, by omega, by rw [hD', hlen, hkn], hat, hsame,
      hr15⟩

end Run

end NativeVm.Wire
