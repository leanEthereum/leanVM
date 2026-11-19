module

public import NativeVm.Code.Phase4.Frames
public import NativeVm.Code.Phase4.Model

/-!
# A round's challenge and claim

`storeChC_spec`: the challenge in `A` to the point's entry `r14 - 1`; `claimC_spec`: the claim,
the message at `oMSG` evaluated at the challenge, to `oCLM`.
-/

@[expose] public section

namespace NativeVm.Code.P4

open Native NativeVm.Model NativeVm.Transcript NativeVm.Field LeanVM.Parameters

variable {env : Env} {s : QState} {E : QState → Prop}

/-- **The challenge** to the point's entry `m`, `r14 = m + 1`. -/
theorem storeChC_spec {m : Nat} (hm : m < 30) (hbp : s.reg .rbp = wd env.work 0)
    (h14 : s.reg .r14 = (m + 1).toUInt64) (hws : WS env s) :
    WP storeChC s (fun s' ↦ EWAt s'.mem (wd env.work (oPT + 2 * m)) (regA s) ∧
      Wr env.work (fun k ↦ oPT + 2 * m ≤ k ∧ k < oPT + 2 * m + 2) s s' ∧
      RegsFrame [.rax] s s') E := by
  unfold storeChC
  refine wp_elemSub hbp h14 ?_
  have hs0 : (s.mem (wd env.work (0 + 2 * m + oPT))).isSome :=
    hws _ (by simp only [oPT, oS]; omega) (by simp only [oPT, oS]; omega)
  have hs1 : (s.mem (wd env.work (0 + 2 * m + (oPT + 1)))).isSome :=
    hws _ (by simp only [oPT, oS]; omega) (by simp only [oPT, oS]; omega)
  refine wp_stA (k := oPT) (by regw) hs0 ?_
  refine wp_stA (k := oPT + 1) (by regw) (by apply isSome_setMem; exact hs1) ?_
  refine wp_done_gen fun s' hs' ↦ ?_
  subst hs'
  refine ⟨EWAt.of ?_ ?_, ?_, by rfw⟩
  · rw [mem_setMem_ne _ (by omega) (by simp only [oPT, oS]; omega) (by simp only [oPT, oS]; omega),
      show 0 + 2 * m + oPT = oPT + 2 * m by omega, mem_setMem_self]
    rfl
  · rw [show 0 + 2 * m + (oPT + 1) = oPT + 2 * m + 1 by omega, mem_setMem_self]
    rfl
  · wr_tac

/-- **The claim**: the message at `oMSG` at the challenge in `A`. -/
theorem claimC_spec (hbp : s.reg .rbp = wd env.work 0) (msg : Array EW) (hsz : msg.size = 4)
    (hmsg : EWArr s.mem (wd env.work oMSG) msg) (hws : WS env s) :
    WP claimC s (fun s' ↦ EWAt s'.mem (wd env.work oCLM) (polyEval msg (regA s)) ∧
      Wr env.work (fun k ↦ oCLM ≤ k ∧ k < oCLM + 2) s s' ∧
      RegsFrame (.r11 :: .r12 :: polyRegs) s s') E := by
  unfold claimC
  wst; wst; wst; wst
  refine WP.then (epolyEvalW (cs := msg) ?_ ?_ (by rw [hsz]; decide)) fun s1 ⟨hp, hm, hr⟩ ↦ ?_
  · rsimp; simpa using hmsg
  · rsimp; rw [hsz]; rfl
  have hb1 : s1.reg .rbp = wd env.work 0 := by rw [hr .rbp (by decide)]; rsimp; exact hbp
  have hs0 : (s.mem (wd env.work (0 + oCLM))).isSome :=
    hws _ (by simp only [oCLM, oS]; omega) (by simp only [oCLM, oS]; omega)
  have hs1 : (s.mem (wd env.work (0 + (oCLM + 1)))).isSome :=
    hws _ (by simp only [oCLM, oS]; omega) (by simp only [oCLM, oS]; omega)
  refine wp_stA (k := oCLM) hb1 (by rw [hm]; simp only [QState.setReg_mem]; exact hs0) ?_
  refine wp_stA (k := oCLM + 1) (by regw) (by apply isSome_setMem; rw [hm]; exact hs1) ?_
  refine wp_done_gen fun s' hs' ↦ ?_
  subst hs'
  simp only [regB, QState.setReg_reg, reduceCtorEq, ite_true, ite_false] at hp
  refine ⟨EWAt.of ?_ ?_, ?_, ?_⟩
  · memw; rw [← hp]
  · memw; rw [← hp]
  · intro a ha
    rw [QState.setMem_mem, ite_eq_right (ha _ (by omega)), QState.setMem_mem,
      ite_eq_right (ha _ (by omega)), hm]
    rfl
  · intro r hr'
    simp only [QState.setMem_reg]
    rw [hr r fun h ↦ hr' (by simp [polyRegs] at h ⊢; tauto)]
    simp only [List.mem_cons, polyRegs, List.not_mem_nil, or_false, not_or] at hr'
    simp [QState.setReg_reg, hr']

end NativeVm.Code.P4
