module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Step
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Keep
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names

/-!
# `verify_keccak`'s returns (x86-64)

`failG`: from `NativeRustcVmX64.Vm.VerifyKeccak.label_31` (`b72`, R13 zeroed) through the epilogue (`b73`): AL `0`, the
model's `none`. `okG`: from `b71` (R13 the last `extend`'s AL) through the epilogue: AL `1`, the
results in memory. A template with the pushes is `tM` (`toM_bnd`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt)

public section

variable {m0 : MachineData} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW}

/-- **Any template with the pushes is `tM`.** -/
theorem toM_bnd [Labels] {wr : Nat → Bool} {T : SState} {vals : Nat → BitVec 64} {d : MachineData}
    (hB : BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr T vals d) (h : toM T = true) :
    BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr tM vals d := by
  unfold toM at h
  split at h
  · rename_i L LW hL hLW
    refine ⟨fun ret ↦ match_links (hB.mt ret) rfl hL hLW (fun _ ↦ rfl) rfl rfl rfl
      (fun p hp ↦ varLinks_eval h _ p hp) rfl (regions_envZ rfl) rfl (fun _ _ h ↦ by cases h)
      (fun _ _ _ h ↦ by cases h), hB.same, hB.kept⟩
  · cases h

variable [Host] {k : Nat}

theorem label31 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.VerifyKeccak.label_31 = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyKeccak.b72Offset) :=
  label_of_infix hp b72_in_code rfl

theorem label32 (hp : Placed code k) : Labels.label NativeRustcVmX64.Vm.VerifyKeccak.label_32 = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyKeccak.b73Offset) :=
  label_of_infix hp b73_in_code rfl

/-- **A failed check**: AL `0`, the model's `none`. -/
theorem failG (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    {wr : Nat → Bool} {T : SState} {V : Vs} {st : MachineState}
    (hB : BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr T (vv m0 V) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.VerifyKeccak.label_31) (hT : toM T = true)
    (hnone : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s = none) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hM := toM_bnd hB hT
  refine stepJ (T' := tF) (vals' := vv m0 V) hp c h (o := NativeRustcVmX64.Vm.VerifyKeccak.b72Offset) ⟨hpc.trans (label31 hp), hM⟩
    b72_in_code (by simp [b72]) run_b72 nofun (hM.mt 0) (by decide) rfl rfl
    (varLinks_eval (by decide) _) rfl rfl rfl rfl (fun _ _ _ _ _ h ↦ by cases h) rfl
    fun st' hpc' hB' _ _ _ ↦ ?_
  obtain ⟨d, pc⟩ := st'
  simp only [PcOk] at hpc' hB'
  subst hpc'
  refine exitZ h hB' (b73_in_code.trans hp.1 (by simp [b73])) run_b73 (hB'.mt 0)
    (frameW_ok (by decide) le_rfl) rfl
    (fun r hr ↦ by cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr <;>
      exact ⟨_, rfl, rfl⟩) fun st hm hret hrsp hso hsv ↦ .done _ ⟨hret, hrsp, ?_⟩
  unfold VerifyKeccakPost
  dsimp only
  rw [hnone]
  refine ⟨?_, (fun _ _ _ _ h ↦ nomatch h), writes_of hso, hsv⟩
  have hax : reg st.data .rax = (Sym.lit 0).eval
      (envZ m0 d 3344 3368 (rsOf m0) (vv m0 V) 0) := hm.regs .rax _ rfl
  unfold OkAl boolRet
  rw [hax]
  rfl

/-- **A failed grind** (at `NativeRustcVmX64.Vm.VerifyKeccak.label_32`, R13 zero): AL `0`, the model's `none`. -/
theorem fail32 (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    {wr : Nat → Bool} {V : Vs} {st : MachineState}
    (hB : BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wr t2 (vv m0 V) st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.VerifyKeccak.label_32)
    (hnone : (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s = none) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have h := lay_of hpre
  obtain ⟨d, pc⟩ := st
  simp only at hpc hB
  subst hpc
  rw [label32 hp]
  refine exitZ h hB (b73_in_code.trans hp.1 (by simp [b73])) run_b73e (hB.mt 0)
    (frameW_ok (by decide) le_rfl) rfl
    (fun r hr ↦ by cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr <;>
      exact ⟨_, rfl, rfl⟩) fun st hm hret hrsp hso hsv ↦ .done _ ⟨hret, hrsp, ?_⟩
  unfold VerifyKeccakPost
  dsimp only
  rw [hnone]
  refine ⟨?_, (fun _ _ _ _ h ↦ nomatch h), writes_of hso, hsv⟩
  have hax : reg st.data .rax = (Sym.lit 0).eval
      (envZ m0 d 3344 3368 (rsOf m0) (vv m0 V) 0) := hm.regs .rax _ rfl
  unfold OkAl boolRet
  rw [hax]
  rfl

/-- **The last `extend` done**: AL `1`, the results in memory. -/
theorem okG (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0) {wr : Nat → Bool}
    {V : Vs} {st : MachineState} (hat : At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b71Offset wr t69 (vv m0 V) st)
    (hal : boolRet st.data = 1)
    (hsome : ((NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s).isSome = true)
    (hres : ∀ outs pt sl s', (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
      some ((outs, pt, sl), s') → TStateAt st.data.dmem (reg m0 .rdi) a s' ∧
        NativeRustcVm.Layout.ClaimsWAt st.data.dmem (keccakClaims m0) (cs ++ outs) ∧
        NativeRustcVm.KeccakGkr.KeccakOutAt st.data.dmem (keccakOutArg m0) pt sl) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0) st := by
  have c := ctx_of hpre
  have h := lay_of hpre
  let V' : Vs := { V with fin := UnOp.apply .trunc .W32 (reg st.data .rax) }
  refine stepJ (T' := tOk) (vals' := vv m0 V') hp c h hat b71_in_code (by simp [b71]) run_b71 nofun
    (hat.2.mt 0) (by decide) rfl rfl ?_ rfl rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st' hpc' hB' _ hchg hk1 ↦ ?_
  · intro p hp'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨d, pc⟩ := st'
  simp only [PcOk] at hpc' hB' hchg hk1
  subst hpc'
  rw [label32 hp]
  refine exitZ h hB' (b73_in_code.trans hp.1 (by simp [b73])) run_b73ok (hB'.mt 0)
    (frameW_ok (by decide) le_rfl) rfl
    (fun r hr ↦ by cases r <;> simp only [calleeSaved, Bool.false_eq_true] at hr <;>
      exact ⟨_, rfl, rfl⟩) fun st'' hm hret hrsp hso hsv ↦ .done _ ⟨hret, hrsp, ?_⟩
  -- Memory at the return: the state at `b71` but the pushes' words (and `b73`'s none).
  have hwf := h.wf hB'.kept (m := d) (vals := vv m0 V') (ret := 0)
  have hc2 := chg_block (wr := wr) c hm hwf (frameW_ok (by decide) le_rfl) (frameW_r0 (by decide))
  have hc := hchg.trans hc2
  unfold VerifyKeccakPost
  dsimp only
  refine ⟨?_, fun outs pt sl s' hr ↦ ?_, writes_of hso, hsv⟩
  · have hax : reg st''.data .rax = (Sym.un .trunc .W32 (.var 35)).eval
        (envZ m0 d 3344 3368 (rsOf m0) (vv m0 V') 0) := hm.regs .rax _ rfl
    unfold OkAl boolRet
    rw [hax, hsome]
    show (UnOp.apply .trunc .W32 (UnOp.apply .trunc .W32 (reg st.data .rax))).toNat % 256 = 1
    rw [al_trunc, al_trunc]
    exact hal
  · obtain ⟨h1, h2, h3⟩ := hres outs pt sl s' hr
    exact ⟨Chg.ts c hc (by decide) (by decide) rfl (NativeRustcVmX64.Transcript.kept_trans hk1 (hm.kept hwf)) h1,
      Chg.cls c hc (by decide) (by decide) rfl h2, Chg.kout c hc (by decide) (by decide) rfl h3⟩

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
