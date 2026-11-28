module

public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Whir.FoldRound.Read3

/-!
# `fold_round`: from the entry to the squeezes

`reads`: the prologue, the four scalars, the grind; `None` returned where one fails, else `b10`
(`AtB10`).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- **The prologue, the four scalars, the grind.** -/
theorem reads (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (cont : ∀ st s5 u0 v c0 c1, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b10Offset) →
      AtB10 a s0 w m0 s5 u0 v c0 c1 st.data → Eventually (step1 Host.exe) (Goal a s0 w m0) st) :
    Eventually (step1 Host.exe) (Goal a s0 w m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b0Offset)⟩ := by
  refine stage1 hp h hrs fun st1 hpc1 hb1 haft1 ↦ ?_
  -- `b1`: the first tag
  refine frame_block h b1_in_code (by simp [b1]) run_b1 rfl rfl hpc1 hp hb1
    fun st2 hm2 hpc2 hf2 hd2 ↦ ?_
  simp only [PcOk] at hpc2
  have hk2 : ∀ r, r ≠ .X8 → st2.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦
    reg_of hm2 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have hb2 : Base w m0 st2.data :=
    ⟨hf2, (hk2 .X19 (by decide)).trans hb1.x19, (hk2 .X20 (by decide)).trans hb1.x20,
      (hk2 .X23 (by decide)).trans hb1.x23, by rw [hd2]; exact hb1.ws⟩
  have ht8 := tag8 (env := frameEnv m0 st1.data) rfl haft1.opt
  have hcond : (SBool.cmp .eq .W64 (.load 0 88 8) (.lit 0)).eval (frameEnv m0 st1.data) =
      !(readScalar.run s0).isSome := by
    sym_simp
    rw [ht8]
    cases readScalar.run s0 <;> simp only [Option.map_none, Option.map_some,
      Option.isSome_none, Option.isSome_some, Bool.false_eq_true, ↓reduceIte] <;> decide
  rw [hcond] at hpc2
  cases hr1 : readScalar.run s0 with
  | none =>
    simp only [hr1, Option.isSome_none, Bool.not_false, ↓reduceIte,
      hp.label (j := NativeRustcVmArm.Vm.FoldRound.b21Offset) NativeRustcVmArm.Vm.FoldRound.label_8_at] at hpc2
    refine none0_exit hp h (by rw [foldRound_run, hr1]; rfl) hpc2 hb2 ?_
    refine reg_of hm2 (r := .X8) rfl ?_
    show (frameEnv m0 st1.data).load 0 88 8 = _
    rw [ht8, hr1]; rfl
  | some p1 =>
    obtain ⟨u0, s1⟩ := p1
    simp only [hr1, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      show k + NativeRustcVmArm.Vm.FoldRound.b1Offset + b1.length = k + NativeRustcVmArm.Vm.FoldRound.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRound.b1_next]] at hpc2
    have hopt1 := haft1.opt
    rw [hr1] at hopt1
    refine load_rs hp h hrs b2_in_code (by simp [b2]) run_b2 rfl rfl (rA := .X29) (rB := .X24)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun r hr h1 h2 ↦ by cases r <;> first | rfl | contradiction) hpc2 hb2
      (by rw [hd2]; exact hopt1) (by rw [hd2]; exact haft1.next _ _ hr1)
      fun st3 hpc3 hb3 haft3 h29 h24 hk3 ↦ ?_
    -- `b3`, `b4`: the second scalar `v`
    refine check4 hp h b3_in_code (by simp [b3]) run_b3 rfl rfl
      (fun r hr ↦ by cases r <;> first | rfl | contradiction) hpc3 hb3 haft3
      (fun hn ↦ by rw [foldRound_run, hr1]; simp only [Option.bind_some, hn]; rfl)
      fun v s2 st4 hr2 hpc4 hb4 hopt4 hts4 hk4 ↦ ?_
    refine load_rs hp h hrs b4_in_code (by simp [b4]) run_b4 rfl rfl (rA := .X27) (rB := .X28)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun r hr h1 h2 ↦ by cases r <;> first | rfl | contradiction) hpc4 hb4 hopt4 hts4
      fun st5 hpc5 hb5 haft5 h27 h28 hk5 ↦ ?_
    -- `b5`, `b6`: `c0`
    refine check4 hp h b5_in_code (by simp [b5]) run_b5 rfl rfl
      (fun r hr ↦ by cases r <;> first | rfl | contradiction) hpc5 hb5 haft5
      (fun hn ↦ by rw [foldRound_run, hr1]; simp only [Option.bind_some, hr2, hn]; rfl)
      fun c0 s3 st6 hr3 hpc6 hb6 hopt6 hts6 hk6 ↦ ?_
    refine load_rs hp h hrs b6_in_code (by simp [b6]) run_b6 rfl rfl (rA := .X25) (rB := .X26)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun r hr h1 h2 ↦ by cases r <;> first | rfl | contradiction) hpc6 hb6 hopt6 hts6
      fun st7 hpc7 hb7 haft7 h25 h26 hk7 ↦ ?_
    -- `b7`: `c1`'s tag; `b8`, `b9`: the grind
    refine check4 hp h b7_in_code (by simp [b7]) run_b7 rfl rfl
      (fun r hr ↦ by cases r <;> first | rfl | contradiction) hpc7 hb7 haft7
      (fun hn ↦ by rw [foldRound_run, hr1]; simp only [Option.bind_some, hr2, hr3, hn]; rfl)
      fun c1 s4 st8 hr4 hpc8 hb8 hopt8 hts8 hk8 ↦ ?_
    refine grind_step hp h hgr hpc8 hb8 hopt8 hts8
      (fun hn ↦ by rw [foldRound_run, hr1]; simp only [Option.bind_some, hr2, hr3, hr4, hn]; rfl)
      fun s5 st9 hg hpc9 hb9 hts9 h21 h22 hk9 ↦ cont st9 s5 u0 v c0 c1 hpc9 ?_
    -- the registers kept along the way
    have keep : ∀ r, calleeSaved r = true → r ≠ .X21 → r ≠ .X22 → r ≠ .X25 → r ≠ .X26 →
        r ≠ .X27 → r ≠ .X28 → st9.data.regs.getXReg r = st3.data.regs.getXReg r :=
      fun r hr a b c d e f ↦ (hk9 r hr a b).trans ((hk8 r (by rintro rfl; simp [calleeSaved] at hr)).trans
        ((hk7 r hr c d).trans ((hk6 r (by rintro rfl; simp [calleeSaved] at hr)).trans
          ((hk5 r hr e f).trans (hk4 r (by rintro rfl; simp [calleeSaved] at hr))))))
    have keep2 : ∀ r, calleeSaved r = true → r ≠ .X21 → r ≠ .X22 → r ≠ .X25 → r ≠ .X26 →
        st9.data.regs.getXReg r = st5.data.regs.getXReg r :=
      fun r hr a b c d ↦ (hk9 r hr a b).trans ((hk8 r (by rintro rfl; simp [calleeSaved] at hr)).trans
        ((hk7 r hr c d).trans (hk6 r (by rintro rfl; simp [calleeSaved] at hr))))
    have keep3 : ∀ r, calleeSaved r = true → r ≠ .X21 → r ≠ .X22 →
        st9.data.regs.getXReg r = st7.data.regs.getXReg r :=
      fun r hr a b ↦ (hk9 r hr a b).trans (hk8 r (by rintro rfl; simp [calleeSaved] at hr))
    exact {
      base := hb9
      x29 := (keep .X29 rfl (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans h29
      x24 := (keep .X24 rfl (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans h24
      x27 := (keep2 .X27 rfl (by decide) (by decide) (by decide) (by decide)).trans h27
      x28 := (keep2 .X28 rfl (by decide) (by decide) (by decide) (by decide)).trans h28
      x25 := (keep3 .X25 rfl (by decide) (by decide)).trans h25
      x26 := (keep3 .X26 rfl (by decide) (by decide)).trans h26
      x21 := h21
      x22 := h22
      ts := hts9
      model := by
        rw [foldRound_run, hr1]
        simp only [Option.bind_some, hr2, hr3, hr4, hg] }

end

end NativeRustcVmArm.Whir.FoldRound
