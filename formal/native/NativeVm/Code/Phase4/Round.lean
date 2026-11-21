module

public import NativeVm.Code.Phase4.Msg
public import NativeVm.Code.Phase4.RoundParts
public import NativeVm.Code.Phase4.ReadN

/-!
# One round of the table sumcheck

`roundC_refines`: `roundC` refines the sumcheck's round (`roundStep`): three scalars read after the
message's first entry (`readN`), the message (`msgC`), the challenge (`sampleChallenge`) to the
point's entry `r14 - 1` (`storeChC`), the next claim (`claimC`). Whatever survives the rounds'
writes (`RStab`) is kept, on either exit.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {s : QState} {E : QState → Prop}

/-- The words the rounds write: the claim, the message, the point, the rounds' count. -/
def WR (k : Nat) : Prop := (oCLM ≤ k ∧ k < oCLM + 2) ∨ (oMSG ≤ k ∧ k < oPT + 60) ∨ k = oNR

/-- What the rounds keep: anything that survives the phase's frame and the rounds' writes. -/
def RStab (env : Env) (X : QState → Prop) : Prop :=
  ∀ s s', X s → Fr env [scratchR] arrRegs s s' → WF env WR s s' → X s'

/-- A round of `sumcheck` (`Model.sumcheck`'s step). -/
def roundStep (acc : Array EW × EW) (equality : Option EW) : VM (Array EW × EW) := do
  let message ← sumcheckRoundPoly 4 acc.2 equality
  let challenge ← sampleChallenge
  pure (acc.1.push challenge, polyEval message challenge)

theorem sumcheckPlain_eq (claim : EW) (n : Nat) :
    sumcheckPlain claim 4 n = (List.replicate n none).foldlM roundStep (#[], claim) := by
  unfold sumcheckPlain sumcheck
  rw [← Array.foldlM_toList, Array.toList_replicate]
  rfl

/-- **The rounds' state** after `k` of `nR` rounds, with `acc` the challenges and the claim. -/
def RInv (env : Env) (X : QState → Prop) (nR k : Nat) (acc : Array EW × EW) (t : TState)
    (s : QState) : Prop :=
  CodeRel env t s ∧ X s ∧ WS env s ∧ s.reg .rbp = wd env.work 0 ∧
    s.reg .r14 = (nR - k).toUInt64 ∧ k ≤ nR ∧ nR ≤ 30 ∧ acc.1.size = k ∧
    EWAt s.mem (wd env.work oCLM) acc.2 ∧
    EWArr s.mem (wd env.work (oPT + 2 * (nR - k))) acc.1.reverse ∧
    s.mem (wd env.work oNR) = some nR.toUInt64

theorem eq_three {xs : Array EW} (h : xs.size = 3) : xs = #[xs[0], xs[1], xs[2]] := by
  apply Array.ext
  · simp [h]
  · intro i h1 _
    rw [h] at h1
    interval_cases i <;> rfl

/-- The local facts of a round, before its message. -/
def RLoc (env : Env) (X : QState → Prop) (nR k : Nat) (acc : Array EW × EW) (s : QState) : Prop :=
  X s ∧ s.reg .rbp = wd env.work 0 ∧ s.reg .r14 = (nR - k).toUInt64 ∧
    EWAt s.mem (wd env.work oCLM) acc.2 ∧
    EWArr s.mem (wd env.work (oPT + 2 * (nR - k))) acc.1.reverse ∧
    s.mem (wd env.work oNR) = some nR.toUInt64

theorem oPT_val : oPT = 52692 := rfl
theorem oCLM_val : oCLM = 52680 := rfl
theorem oMSG_val : oMSG = 52684 := rfl
theorem oNR_val : oNR = 52772 := rfl

/-- **The local facts survive** a frame that writes inside the message's words. -/
theorem RLoc.keep {X : QState → Prop} (hX : RStab env X) {nR k : Nat}
    {acc : Array EW × EW} {s s' : QState} {W : Nat → Prop} (h : RLoc env X nR k acc s)
    (hsz : acc.1.size = k) (hkn : k ≤ nR) (hnR : nR ≤ 30)
    (hf : Fr env [scratchR] arrRegs s s') (hw : WF env W s s') (hW : ∀ j, W j → oMSG ≤ j ∧ j < oPT)
    (hbp : s'.reg .rbp = s.reg .rbp) (h14 : s'.reg .r14 = s.reg .r14) : RLoc env X nR k acc s' := by
  obtain ⟨hx, h1, h2, h3, h5, h6⟩ := h
  rw [oPT_val, oMSG_val] at hW
  refine ⟨hX s s' hx hf (hw.mono fun j hj ↦ .inr (.inl (by have := hW j hj; rw [oMSG_val, oPT_val]; omega))),
    hbp.trans h1, h14.trans h2, ?_, ?_, ?_⟩
  · refine EWAt.wf hw h3 (by rw [oCLM_val]; omega) (by rw [oCLM_val]; omega) ⟨fun hj ↦ ?_, fun hj ↦ ?_⟩ <;>
      (have := hW _ hj; rw [oCLM_val] at this; omega)
  · refine EWArr.wf hw h5 (by rw [oPT_val]; omega) (by rw [oPT_val, Array.size_reverse]; omega)
      fun i hi hj ↦ ?_
    have := hW _ hj; rw [oPT_val] at this; omega
  · exact hw.word (by rw [oNR_val]; omega) (by rw [oNR_val]; omega)
      (fun hj ↦ by have := hW _ hj; rw [oNR_val] at this; omega) h6

/-- An element before an array in memory. -/
theorem EWArr.cons {mem : UInt64 → Option UInt64} {p : UInt64} {x : EW} {xs : Array EW}
    (hx : EWAt mem p x) (h : EWArr mem (wd p 2) xs) : EWArr mem p (#[x] ++ xs) := by
  intro i hi
  rw [Array.getElem_append]
  split
  · rename_i h'
    have : i = 0 := by simpa using h'
    subst this
    simpa [wd_zero] using hx
  · rename_i h'
    simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, not_lt] at h'
    have := h (i - 1) (by simp at hi; omega)
    rw [wd_wd] at this
    rwa [show 2 + 2 * (i - 1) = 2 * i by omega] at this

/-- The pure end of a round: the challenge stored, the claim, `r14` counted down. -/
theorem roundTail_spec (h4 : Env4 env) {X : QState → Prop} (hX : RStab env X) {nR k : Nat}
    (hk : k < nR) {acc : Array EW × EW} (hsz : acc.1.size = k) (hnR : nR ≤ 30) {t : TState}
    {msg : Array EW} (hmsz : msg.size = 4) {ch : EW} (hc : CodeRel env t s)
    (hl : RLoc env X nR k acc s) (hws : WS env s) (hmsg : EWArr s.mem (wd env.work oMSG) msg)
    (h9 : s.reg .r9 = ch.c0) (h10 : s.reg .r10 = ch.c1) :
    WP (blk [storeChC, claimC, I (.subi .r14 1)]) s
      (fun s' ↦ RInv env X nR (k + 1) (acc.1.push ch, polyEval msg ch) t s') (fun _ ↦ False) := by
  obtain ⟨hx, hbp, h14, hclm, hpt, hnr⟩ := hl
  have h14' : s.reg .r14 = (nR - k - 1 + 1).toUInt64 := by rw [h14]; congr 1; omega
  refine WP.then (WP.dom (storeChC_spec (m := nR - k - 1) (by omega) hbp h14' hws))
    fun s3 ⟨⟨hA, w3, rf3⟩, d3⟩ ↦ ?_
  have hbp3 : s3.reg .rbp = wd env.work 0 := by rw [rf3 .rbp (by decide), hbp]
  have hws3 : WS env s3 := WS.wr hws d3
  have wf3 := WF.ofWr (env := env) w3 fun j hj ↦ by rw [oPT_val] at hj; omega
  have hmsg3 : EWArr s3.mem (wd env.work oMSG) msg :=
    EWArr.wf wf3 hmsg (by rw [oMSG_val]; omega) (by rw [oMSG_val, hmsz]; omega)
      fun i hi hj ↦ by rw [oPT_val, oMSG_val] at *; omega
  refine WP.then (WP.dom (claimC_spec hbp3 msg hmsz hmsg3 hws3)) fun s4 ⟨⟨hC, w4, rf4⟩, d4⟩ ↦ ?_
  refine wp_regGuard (by decide) ?_
  fstep
  refine wp_done_gen fun s' hs' ↦ ?_
  subst hs'
  have hA3 : regA s3 = ch := by
    simp only [regA, rf3 .r9 (by decide), rf3 .r10 (by decide), h9, h10]
  have wf4 := WF.ofWr (env := env) w4 fun j hj ↦ by rw [oCLM_val] at hj; omega
  have w34 : Wr env.work WR s s4 :=
    (w3.mono fun j hj ↦ .inr (.inl (by rw [oPT_val] at hj; rw [oMSG_val, oPT_val]; omega))).trans
      (w4.mono fun j hj ↦ .inl hj)
  have d34 : DomEq s s4 := d3.trans d4
  have rf34 : RegsFrame arrRegs s s4 := rf_arr (rf_mono rf3) rf4
  have hrdi4 : s4.reg .rdi = s.reg .rdi := rf34 .rdi (by decide)
  have hWR : InRs [scratchR] WR := fun j hj ↦ ⟨scratchR, by simp, by
    rw [scratchR_off]; simp only [WR, oCLM, oMSG, oPT, oNR, oS] at hj ⊢; omega, by
    show j < scratchR.off + scratchR.size; rw [scratchR_off]
    simp only [WR, oCLM, oMSG, oPT, oNR, oS] at hj; show j < 52670 + 32768; omega⟩
  have wfr : WF env WR s s4 := WF.ofWr w34 fun j hj ↦ by simp only [WR, oCLM, oMSG, oPT, oNR, oS] at hj; omega
  have w5 := w34.setReg .r14 (s4.reg .r14 - 1)
  have rf5 := rf_setReg rf34 (r := .r14) (by decide) (s4.reg .r14 - 1)
  have d5 : DomEq s (s4.setReg .r14 (s4.reg .r14 - 1)) := d34
  refine ⟨CodeRel.only hc h4 (by decide) (Only.ofWr w5 hWR) d5 (rf5 .rdi (by decide)), ?_, ?_, ?_, ?_,
    by omega, hnR, by rw [Array.size_push, hsz], ?_, ?_, ?_⟩
  · exact hX s _ hx (Fr.ofWr w5 hWR d5 rf5 (by decide)) wfr
  · exact WS.wr hws d34
  · simp only [QState.setReg_reg, reduceCtorEq, ite_false]
    rw [rf4 .rbp (by decide), hbp3]
  · simp only [QState.setReg_reg, ↓reduceIte]
    rw [rf4 .r14 (by decide), rf3 .r14 (by decide), h14, show nR - k = nR - (k + 1) + 1 by omega]
    exact Field.toUInt64_succ_sub _
  · simp only [QState.setReg_mem]; rw [← hA3]; exact hC
  · simp only [QState.setReg_mem]
    rw [Array.reverse_push, show nR - (k + 1) = nR - k - 1 by omega]
    have hAc : regA s = ch := by simp only [regA, h9, h10]
    rw [hAc] at hA
    refine EWArr.cons ?_ ?_
    · refine EWAt.wf wf4 hA (by rw [oPT_val]; omega) (by rw [oPT_val]; omega) ⟨?_, ?_⟩ <;>
        (intro hj; rw [oPT_val, oCLM_val] at *; omega)
    · rw [wd_wd, show oPT + 2 * (nR - k - 1) + 2 = oPT + 2 * (nR - k) by omega]
      refine EWArr.wf wf4 (EWArr.wf wf3 hpt ?_ ?_ ?_) ?_ ?_ ?_ <;>
        simp only [Array.size_reverse, hsz, oPT_val, oCLM_val] at * <;> omega
  · simp only [QState.setReg_mem]
    exact wf4.word (by rw [oNR_val]; omega) (by rw [oNR_val]; omega)
      (by rw [oNR_val, oCLM_val]; omega)
      (wf3.word (by rw [oNR_val]; omega) (by rw [oNR_val]; omega)
        (by rw [oNR_val, oPT_val]; omega) hnr)

theorem CodeRel.setReg {t : TState} (h : CodeRel env t s) {r : Reg64} (hr : r ≠ .rdi) (v : UInt64) :
    CodeRel env t (s.setReg r v) := by
  obtain ⟨st, h1, h2, h3, h5⟩ := h
  exact ⟨st, h1, h2.of_mem rfl (by rw [QState.setReg_reg, ite_eq_right (Ne.symm hr)]), h3, h5⟩

/-- The round's local facts, with the round's constants. -/
def RLoc' (env : Env) (X : QState → Prop) (nR k : Nat) (acc : Array EW × EW) (s : QState) : Prop :=
  RLoc env X nR k acc s ∧ acc.1.size = k ∧ k ≤ nR ∧ nR ≤ 30

theorem RLoc'.keep {X : QState → Prop} (hX : RStab env X) {nR k : Nat} {acc : Array EW × EW}
    {s s' : QState} {W : Nat → Prop} (h : RLoc' env X nR k acc s)
    (hf : Fr env [scratchR] arrRegs s s') (hw : WF env W s s') (hW : ∀ j, W j → oMSG ≤ j ∧ j < oPT)
    (hbp : s'.reg .rbp = s.reg .rbp) (h14 : s'.reg .r14 = s.reg .r14) : RLoc' env X nR k acc s' :=
  ⟨RLoc.keep hX h.1 h.2.1 h.2.2.1 h.2.2.2 hf hw hW hbp h14, h.2⟩

theorem scratch_InRs {W : Nat → Prop} (hW : ∀ j, W j → 52670 ≤ j ∧ j < 52670 + 32768) :
    InRs [scratchR] W := fun j hj ↦ ⟨scratchR, by simp, by rw [scratchR_off]; exact (hW j hj).1, by
    show j < scratchR.off + scratchR.size; rw [scratchR_off]; exact (hW j hj).2⟩

/-- **A round.** -/
theorem roundC_refines (h4 : Env4 env) {X : QState → Prop} (hX : RStab env X) {nR k : Nat}
    (hk : k < nR) (acc : Array EW × EW) :
    Refines (RInv env X nR k acc) roundC (roundStep acc none)
      (fun acc' t s ↦ RInv env X nR (k + 1) acc' t s) X := by
  have hstep : roundStep acc none = (readScalars 3 >>= fun xs ↦ Model.sampleChallenge >>= fun ch ↦
      pure (acc.1.push ch, polyEval (msgOf acc.2 xs) ch)) := by
    simp only [roundStep, roundPoly_eq, bind_assoc, pure_bind]
  rw [hstep]
  unfold roundC
  refine Refines.pre_blk (P' := fun t s ↦ RInv env X nR k acc t s ∧
    s.reg .r12 = wd env.work (0 + (oMSG + 2))) (fun t s h ↦ WP.ins rfl ⟨?_, ?_⟩) ?_
  · obtain ⟨hc, hx, hws, hbp, h14, hkn, hnR, hsz, hcl, hpt, hnr⟩ := h
    have hf : Fr env [scratchR] arrRegs s (s.setReg .r12 ((wa .rbp (oMSG + 2)).eval s)) :=
      Fr.setReg (Fr.refl _ _ s) (by decide) (by decide) _
    exact ⟨CodeRel.setReg hc (by decide) _, hX s _ hx hf (WF.ofEq rfl), hws, hbp, h14, hkn, hnR, hsz, hcl, hpt, hnr⟩
  · simp only [QState.setReg_reg, ↓reduceIte]; rw [eval_wd h.2.2.2.1]
  refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧ RLoc' env X nR k acc s ∧ WS env s ∧
    s.reg .r12 = wd env.work (oMSG + 2) ∧ s.reg .r13 = (3 : Nat).toUInt64)
    (fun t s ⟨h, h12⟩ ↦ WP.ins rfl ?_) ?_
  · obtain ⟨hc, hx, hws, hbp, h14, hkn, hnR, hsz, hcl, hpt, hnr⟩ := h
    have hf : Fr env [scratchR] arrRegs s (s.setReg .r13 (Int64.toUInt64 3)) :=
      Fr.setReg (Fr.refl _ _ s) (by decide) (by decide) _
    refine ⟨CodeRel.setReg hc (by decide) _, ⟨⟨hX s _ hx hf (WF.ofEq rfl), ?_, ?_, hcl, hpt, hnr⟩,
      hsz, hkn, hnR⟩, hws, ?_, ?_⟩ <;> simp only [QState.setReg_reg, reduceCtorEq, ↓reduceIte]
    · exact hbp
    · exact h14
    · rw [h12, Nat.zero_add]
    · rfl
  have hY : Stab env [⟨oMSG + 2, 2 * 3⟩] readRegs (RLoc' env X nR k acc) := fun s s' hy hf ↦
    RLoc'.keep hX hy (hf.sub (by decide) (by decide)) (WF.ofFr h4 hf (by decide))
      (fun j ⟨r, hr, h1, h2⟩ ↦ by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.stop, oMSG, oPT, oS] at h1 h2 ⊢; omega)
      (hf.regs .rbp (by decide)) (hf.regs .r14 (by decide))
  refine Refines.blk_cons (Refines.mono (readN_refines h4 (a := oMSG + 2) (n := 3) (by decide) hY)
    (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) fun _ h ↦ h.1.1) fun xs ↦ ?_
  refine Refines.pre_blk (P' := fun t s ↦ CodeRel env t s ∧ (RLoc' env X nR k acc s ∧ WS env s ∧
    EWArr s.mem (wd env.work oMSG) (msgOf acc.2 xs))) (fun t s ⟨hc, hy, hws, hsz3, hxs⟩ ↦ ?_) ?_
  · rw [eq_three hsz3] at hxs ⊢
    obtain ⟨⟨hx, hbp, h14, hcl, hpt, hnr⟩, hsz, hkn, hnR⟩ := hy
    refine WP.mono (WP.dom (msgC_spec acc.2 _ _ _ hbp hcl.1 (by rw [← wd_wd]; exact hcl.2) hxs
      fun j h1 h2 ↦ hws j (by simp only [oMSG, oS] at h1; omega)
        (by simp only [oMSG, oS] at h2; omega))) (fun s' ⟨⟨hm, w1, rf1⟩, d1⟩ ↦ ?_) fun _ h ↦ h
    have hW1 : InRs [scratchR] (fun j ↦ oMSG ≤ j ∧ j < oMSG + 4) :=
      scratch_InRs fun j hj ↦ by simp only [oMSG, oS] at hj; omega
    have rf1' : RegsFrame arrRegs s s' := rf_mono rf1
    refine ⟨CodeRel.only hc h4 (by decide) (Only.ofWr w1 hW1) d1 (rf1 .rdi (by decide)),
      RLoc'.keep hX ⟨⟨hx, hbp, h14, hcl, hpt, hnr⟩, hsz, hkn, hnR⟩
        (Fr.ofWr w1 hW1 d1 rf1' (by decide))
        (WF.ofWr w1 fun j hj ↦ by simp only [oMSG, oS] at hj; omega)
        (fun j hj ↦ by simp only [oMSG, oPT, oS] at hj ⊢; omega)
        (rf1 .rbp (by decide)) (rf1 .r14 (by decide)), WS.wr hws d1, hm⟩
  refine Refines.blk_cons (Refines.mono (sampleChallenge_fr (env := env)
    (R := fun s ↦ RLoc' env X nR k acc s ∧ WS env s ∧ EWArr s.mem (wd env.work oMSG) (msgOf acc.2 xs))
    fun s s' ⟨hy, hws, hm⟩ hk hd ↦ ⟨RLoc'.keep (W := fun _ ↦ False) hX hy
      (Fr.ofKeeps hk hd (by decide)) (WF.ofKeeps h4 hk) (fun _ h ↦ h.elim)
      (hk.regs .rbp (by decide)) (hk.regs .r14 (by decide)), WS.wr hws hd,
      EWArr.wf (W := fun _ ↦ False) (WF.ofKeeps h4 hk) hm (by simp only [oMSG, oS]; omega)
        (by rw [show (msgOf acc.2 xs).size = 4 from rfl]; simp only [oMSG, oS]; omega)
        fun _ _ h ↦ h⟩)
    (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) fun _ h ↦ h.1.1.1) fun ch ↦ ?_
  refine Refines.pure fun t s ⟨hc, ⟨hy, hws, hm⟩, h9, h10⟩ ↦ ?_
  exact roundTail_spec h4 hX hk hy.2.1 hy.2.2.2 rfl hc hy.1 hws hm h9 h10

end NativeVm.Code.P4
