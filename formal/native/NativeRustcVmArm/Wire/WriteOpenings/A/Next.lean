module

public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Wire.WriteOpenings.A.Store

/-!
# `write_openings`' levels' loop and next query (`h > 0`)

`lev_loop`: from level `l` to the opening done (`EndA`) or a rejection. `next_step` (`b21`,
`b22`): the next query's head (`HeadA`), or the epilogue with every opening written.
-/

namespace NativeRustcVmArm.Wire.WriteOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt wordOf)
open NativeRustcVmArm.Vm.WriteOpenings

public section

variable {R : Run} {j : Nat} [Host]

/-- **The levels' loop**, from level `l`. -/
theorem lev_loop (hp : Placed code R.k) (G : Geo R)
    (hfind : Spec (Labels.label NativeRustcVmArm.Vm.Find.entryLabel) FindPre FindPost) {l : Nat} {st : MachineState}
    (H : LevA R j l st) : Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ EndA R j st') st := by
  refine Sym.loop (fun n st ↦ ∃ l, n = R.h - l ∧ LevA R j l st) (fun n st ⟨l, hn, H⟩ ↦ ?_)
    ⟨l, rfl, H⟩
  have hl := H.s.llt
  refine eventually_trans _ _ _ _ (b16_step hp G H) fun s1 h1 ↦ ?_
  rcases h1 with h1 | h1
  · exact .done _ (.inl (.inl h1))
  refine eventually_trans _ _ _ _ (call_step hp G hfind h1) fun s2 h2 ↦ ?_
  refine eventually_trans _ _ _ _ (dig_step hp G h2) fun s3 h3 ↦ ?_
  refine Eventually.mono (store_step hp G h3) fun s4 h4 ↦ ?_
  rcases h4 with h4 | h4
  · exact .inl (.inr h4)
  · exact .inr ⟨R.h - (l + 1), by omega, l + 1, rfl, h4⟩

omit [Host] in
theorem fw_load {m : MachineData} {cs : List (BitVec 64 × Nat)} {o : Nat} {v : BitVec 64}
    (h : FW R m.dmem o v) : (envOf R m cs).load 0 o 8 = v := frLoad h

/-- **Opening `j` done** (`b21`): the next query, or the epilogue. -/
theorem next_step (hp : Placed code R.k) (G : Geo R) {st : MachineState} (H : EndA R j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post R st' ∨ HeadA R (j + 1) st') st := by
  have hj := H.lt
  have hlw := G.lw64
  have hnq := G.nq256
  have hwf := G.wf0 H.fr.kept
  have hm := frMatch G H.fr
  refine run_block G hp b21_in_code (by simp [b21]) run_b21 H.fr H.pc hwf hm rfl
    (writesOk_frame (by decide)) fun s1 hfr1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 := regs_keep hm hm1 (rs := [.X19, .X21, .X22, .X23, .X26, .X29]) (by decide)
  have Cs1 : Cs R s1.data := H.cs.keep hk1
  have hqa : R.qa.toNat + 8 * R.nq ≤ 2 ^ 64 := G.noWrap (i := 2) (by omega)
  have hc : (SBool.cmp .eq .W64 (.load 0 72 8) (.load 0 64 8)).not.eval (envOf R st.data []) =
      decide (j + 1 ≠ R.nq) := by
    simp only [SBool.eval, eq_apply, Sym.eval]
    rw [fw_load H.w1.w72, fw_load H.w1.w64]
    by_cases h : j + 1 = R.nq
    · rw [h, decide_eq_true rfl, decide_eq_false (by omega)]; rfl
    · rw [decide_eq_true h]
      have hne : R.qa + BitVec.ofNat 64 (8 * (j + 1)) ≠ R.qa + BitVec.ofNat 64 (8 * R.nq) :=
        fun he ↦ h (by
          have := congrArg BitVec.toNat (show BitVec.ofNat 64 (8 * (j + 1)) =
              BitVec.ofNat 64 (8 * R.nq) by
            have := congrArg (· - R.qa) he
            simpa [BitVec.add_comm R.qa, BitVec.add_sub_cancel] using this)
          rw [ofNat_toNat (by omega), ofNat_toNat (by omega)] at this
          omega)
      rw [decide_eq_false fun he ↦ hne (BitVec.eq_of_toNat_eq he)]; rfl
  simp only [PcOk, hc] at hpc1
  have hx0 : s1.data.regs.X0 = 1 := by
    apply UInt64.toBitVec_inj.mp
    rw [show s1.data.regs.X0 = s1.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    rfl
  have e : ∀ (x : XReg) (o : Nat) (v : BitVec 64), FW R st.data.dmem o v →
      (after b21 frS).reg x = some (.load 0 o 8) → rv s1.data x = v := by
    intro x o v hv hx
    rw [after_eq run_b21] at hx
    rw [hm1.regs x _ hx]
    exact fw_load hv
  have e' : ∀ (x : XReg) (o : Nat) (v : BitVec 64), FW R st.data.dmem o v →
      (after b21 frS).reg x = some (.bin .add .W64 (.load 0 o 8) (.lit 1544)) →
      rv s1.data x = v + BitVec.ofNat 64 1544 := by
    intro x o v hv hx
    rw [after_eq run_b21] at hx
    rw [hm1.regs x _ hx]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
    rw [fw_load hv]
  have hob := ob_le (j := j) (by omega)
  have oadd : ∀ o, R.oa (ob j + o) + BitVec.ofNat 64 1544 = R.oa (ob (j + 1) + o) := fun o ↦ by
    show R.out + _ + _ = R.out + _
    rw [NativeRustcVm.addr_add_add]
    congr 2
    unfold ob; omega
  by_cases hend : j + 1 = R.nq
  · simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc1
    have hwf2 := G.wf0 hfr1.kept
    have hm2 := frMatch G hfr1
    refine run_block G hp b22_in_code (by simp [b22]) run_b22 hfr1
      (hpc1.trans (congrArg Host.addrOf rfl)) hwf2 hm2 rfl (writesOk_frame (by decide))
      fun s2 hfr2 hm2' hpc2 ↦ ?_
    have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
    have hx0' : s2.data.regs.X0 = 1 := by
      rw [show s2.data.regs.X0 = s2.data.regs.getXReg .X0 from rfl,
        Match.reg_eq hm2 hm2' (v := .reg .X0) rfl rfl]
      exact hx0
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b46Offset) NativeRustcVmArm.Vm.WriteOpenings.label_39_at] at hpc2
    refine Eventually.mono (end_spec hp G ⟨hpc2, hfr2, .inl ⟨hx0', ?_⟩⟩) fun _ h ↦ .inl h
    rw [hd2, hd1, ← hend]
    exact H.done
  · simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.WriteOpenings.b2Offset) NativeRustcVmArm.Vm.WriteOpenings.label_2_at]
      at hpc1
    refine .done _ (.inr ⟨hpc1, hfr1, Cs1, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, by omega,
      H.h0, by rw [hd1]; exact H.done⟩)
    · rw [hm1.regs .X15 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
      rw [H.cs.x21, and124 (by omega)]
    · rw [e' .X16 24 _ H.w2.w24 rfl, oadd]
    · rw [e' .X17 16 _ H.w2.w16 rfl, oadd]
    · rw [e' .X20 8 _ H.w2.w8 rfl, oadd]
    · exact e .X1 56 _ H.w1.w56 rfl
    · exact e .X3 48 _ H.w1.w48 rfl
    · exact e .X4 40 _ H.w1.w40 rfl
    · exact e .X5 64 _ H.w1.w64 rfl
    · exact e .X2 72 _ H.w1.w72 rfl
    · exact e .X9 32 _ H.w1.w32 rfl
    · rw [hm1.regs .X11 _ rfl]; rfl

end

end NativeRustcVmArm.Wire.WriteOpenings
