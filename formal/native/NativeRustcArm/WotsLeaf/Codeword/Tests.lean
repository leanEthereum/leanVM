module

public import NativeRustcArm.WotsLeaf.Codeword.Facts

/-!
# The codeword's tests

From `AtCheck` at `b6` (directive 48): the digest's top bits (`b6`), then the bit counts (`b7`);
without a codeword the tag `0` and the return (`fail_path`), else `AtB8` at `b8` (directive 97).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym NativeRustcArm.Xmss.WotsLeaf Codeword

@[expose] public section

/-- **At `b8`**: a codeword; X8 and X9 the digest's words, X19 `out`, X20 `P`'s address, X22 the
chain values'. -/
def Run.AtB8 (r : Run) (m : MachineData) : Prop :=
  Keep r r.checkSlots m ∧ r.hiW.toNat < 2 ^ 52 ∧ isCodeword r.dNum = true ∧
    Run.RegIs m .X8 r.hiW ∧ Run.RegIs m .X9 r.lo ∧ Run.RegIs m .X19 r.out ∧
    Run.RegIs m .X20 r.m0.regs.X1.toBitVec ∧ Run.RegIs m .X22 r.m0.regs.X7.toBitVec

end

public section


variable [NativeRustcArm.Host]

/-- **The codeword's tests.** -/
theorem tests_region : RegionSpec Run.AtCheck NativeRustcArm.Xmss.WotsLeaf.b6Offset fun r st ↦
    (r.result = none ∧ r.Done st) ∨ (st.pc = r.pc NativeRustcArm.Xmss.WotsLeaf.b8Offset ∧ r.AtB8 st.data) := by
  intro r hp hc hpre m ⟨hK, h19, h20, h22⟩
  have hD : BytesAt m.dmem (r.off 1776) r.digest32 := hK.2.2.2.1.2.2
  refine frameStep r hp hpre b6_in_code (List.cons_ne_nil _ _) run_b6 (by decide) rfl hK trivial
    fun st hm1 hK1 hkb1 hpc1 ↦ ?_
  have hpc1' := pc_cond hpc1 (b6_cond run_b6 (load_hi hD))
  have g19 := regIs_reg hm1 rfl h19
  have g20 := regIs_reg hm1 rfl h20
  have g22 := regIs_reg hm1 rfl h22
  have g8 : Run.RegIs st.data .X8 r.hiW := by
    unfold Run.RegIs
    rw [hm1.regs .X8 _ rfl]
    exact load_hi hD
  by_cases h52 : r.hiW.toNat < 2 ^ 52
  · rw [decide_eq_true h52] at hpc1'
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, NativeRustcArm.Xmss.WotsLeaf.b6_next] at hpc1'
    refine pc_at hpc1' ?_
    have hD1 : BytesAt st.data.dmem (r.off 1776) r.digest32 := hK1.2.2.2.1.2.2
    refine frameStep r hp hpre b7_in_code (List.cons_ne_nil _ _) run_b7 (by decide) rfl hK1 trivial
      fun st2 hm2 hK2 hkb2 hpc2 ↦ ?_
    have hpc2' := pc_cond hpc2 (b7_cond run_b7 (load_lo hD1) g8 h52)
    by_cases hcw : isCodeword r.dNum = true
    · rw [show r.dNum = 2 ^ 64 * r.hiW.toNat + r.lo.toNat from rfl] at hcw
      rw [hcw] at hpc2'
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, NativeRustcArm.Xmss.WotsLeaf.b7_next] at hpc2'
      refine .done _ (.inr ⟨hpc2', hK2, h52, hcw, regIs_reg hm2 rfl g8, ?_, regIs_reg hm2 rfl g19,
        regIs_reg hm2 rfl g20, regIs_reg hm2 rfl g22⟩)
      unfold Run.RegIs
      rw [hm2.regs .X9 _ rfl]
      exact load_lo hD1
    · have hcw' : isCodeword r.dNum = false := by simpa using hcw
      rw [show r.dNum = 2 ^ 64 * r.hiW.toNat + r.lo.toNat from rfl] at hcw'
      rw [hcw'] at hpc2'
      simp only [Bool.not_false, ite_true] at hpc2'
      rw [Run.label_of_block r hp b11_in_code rfl] at hpc2'
      exact NativeRustcArm.Eventually.mono (pc_at hpc2' (fail_path r hp hpre st2.data hK2.1
        (regIs_reg hm2 rfl g19) (result_none r hcw'))) fun _ h ↦ .inl ⟨result_none r hcw', h⟩
  · rw [decide_eq_false h52] at hpc1'
    simp only [Bool.not_false, ite_true] at hpc1'
    rw [Run.label_of_block r hp b11_in_code rfl] at hpc1'
    exact NativeRustcArm.Eventually.mono (pc_at hpc1' (fail_path r hp hpre st.data hK1.1 g19
      (result_none_top r h52))) fun _ h ↦ .inl ⟨result_none_top r h52, h⟩

end

end NativeRustcArm.WotsLeafProof
