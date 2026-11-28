module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Exit
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Fx
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Model
public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Run1
public import NativeRustcVmX64.Spec.Field
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names

/-!
# `verify_keccak` from its entry to the samples (x86-64)

`b0` (the prologue, the arguments spilled, `bit_length(5)`), `b1` (the grind of
`bit_length(5) - 3 = 0` bits), `b2` (its check: on failure the return with AL `0`).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.KeccakGkr.SeqZ
open NativeRustcVmX64.Vm.VerifyKeccak NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript (DecArea TStateAt tstateBytes)

public section

variable [Host] {k : Nat} {m0 : MachineData} {a : DecArea} {s : TState}
  {cs : Array ColumnClaimW} {inst output : Array EW}

/-- **To the samples**: after the grind, at `b3` (`t2`), the `TState` the grind's. -/
theorem frontA (hp : Placed code k) (hpre : VerifyKeccakPre a s cs inst output m0)
    (hbl : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (cont : ∀ st s1, At m0 k NativeRustcVmX64.Vm.VerifyKeccak.b3Offset wrA t2 (vv m0 {}) st →
      TStateAt st.data.dmem (reg m0 .rdi) a s1 →
      (NativeVm.Model.verifyKeccak (reg m0 .rsi).toNat inst output).run s =
        (afterGrind (reg m0 .rsi).toNat inst output).run s1 →
      Eventually (step1 Host.exe) (Goal a s cs inst output m0) st) :
    Eventually (step1 Host.exe) (Goal a s cs inst output m0)
      ⟨m0, Labels.label NativeRustcVmX64.Vm.VerifyKeccak.entryLabel⟩ := by
  have c := ctx_of hpre
  have h := lay_of hpre
  have hrc : RcAt m0 verifyKeccakStack := hpre.2.2.1
  have hts : TStateAt m0.dmem (reg m0 .rdi) a s := hpre.2.2.2.2.2.1
  have hB0 : BndZ m0 3344 3368 verifyKeccakStack (rsOf m0) wrA tE (vv m0 {}) m0 :=
    startZ rfl fun ret ↦ ⟨((ev_frame 3344).trans off_frame_F).symm, trivial⟩
  have hpc0 : Labels.label NativeRustcVmX64.Vm.VerifyKeccak.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyKeccak.b0Offset) := hp.label NativeRustcVmX64.Vm.VerifyKeccak.entry_at
  -- `b0` and `bit_length`.
  refine stepC (hwfS := fun _ ↦ h.wf hB0.kept)
    (T' := t1) (vals' := vv m0 {}) (o := NativeRustcVmX64.Vm.VerifyKeccak.b0Offset) hp c h ⟨hpc0, hB0⟩ b0_in_code
    (by simp [b0]) run_b0 hB0.mt (by decide) (oc := 48) (by decide) rfl hbl (Sk := bitLengthStack)
    (by rw [vk_eq]; decide) (fun mc _ _ hsk _ _ _ _ ↦ hsk) (Lc := []) (Oc := [])
    (fun mc m' _ hq ↦ chgQ hq.2.1 (fun q h ↦ .inl h) hq.2.2) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi mc m' hmc hq ↦ by
      cases tregE (rfl : t1.reg .rax = some (.var 32)) hi
      have hdi : reg mc .rdi = 5#64 := hmc.regs .rdi _ rfl
      apply BitVec.eq_of_toNat_eq
      rw [hq.1, hdi]
      exact bitLength_five)
    (fun i hi ↦ nomatch tregE (rfl : t1.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st1 hpc1 hB1 _ hchg1 hk1 ↦ ?_
  have hts1 := Chg.ts c hchg1 (by decide) (by decide) (by decide) hk1 hts
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b0_next] at hpc1
  -- `b1` and the grind.
  refine stepC (hwfS := fun _ ↦ h.wf hB1.kept)
    (T' := t2) (vals' := vv m0 {}) (o := NativeRustcVmX64.Vm.VerifyKeccak.b1Offset) hp c h ⟨hpc1, hB1⟩ b1_in_code
    (by simp [b1]) run_b1 hB1.mt (by decide) (oc := 48) (by decide) rfl (hgr s) (Sk := grindStack)
    (by rw [vk_eq]; decide) (fun mc hmc hk hsk hso hrsp hch hkk ↦ ?_) (Lc := []) (Oc := [(1, 0, 760)])
    (fun mc m' hmc hq ↦ chgQ hq.2.2.1 (fun q h ↦ h.elim (fun h ↦ .inr (inR_reg (i := 1) (o := 0)
      ((hmc.regs .rdi _ rfl).trans (off0 _).symm) (by decide) h)) .inl) hq.2.2.2)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl (by vtacC)
    (fun i hi ↦ nomatch tregE (rfl : t2.reg .rax = some (.reg .rax)) hi)
    (fun i hi ↦ nomatch tregE (rfl : t2.reg .rdx = some (.reg .rdx)) hi) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st2 hpc2 hB2 ⟨mc, hmc, hrsp, hq, _⟩ hchg2 hk2 ↦ ?_
  · -- `grind`'s precondition.
    have ca : CallAt m0 wrA 48 mc := ⟨hrsp, by decide, hk, hso⟩
    have hdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ rfl
    have hsi : grindBits mc = 0 := by
      unfold grindBits
      rw [show reg mc .rsi = _ from hmc.regs .rsi _ rfl]
      simp only [Sym.eval, SBool.eval, vars_vv, vv32]
      rfl
    unfold GrindPre
    dsimp only
    rw [hdi, hsi]
    refine ⟨hsk, ca.rc c hrc (by rw [vk_eq]; decide),
      Chg.ts c hch (by decide) (by decide) (by decide) hkk hts1, ca.tok c (by rw [vk_eq]; decide),
      by decide, ?_⟩
    apply ca.got c (by rw [vk_eq]; decide)
    simp only [NativeRustcVm.Transcript.DecArea.region, tstateBytes]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨(reg m0 .rdi, 760), by simp, le_rfl, le_rfl⟩
    · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
    · exact ⟨(rcAddr, 192), by simp, le_rfl, le_rfl⟩
  -- `b2`: the grind's check.
  have hdi : reg mc .rdi = reg m0 .rdi := hmc.regs .rdi _ rfl
  have hsi : grindBits mc = 0 := by
    unfold grindBits
    rw [show reg mc .rsi = _ from hmc.regs .rsi _ rfl]
    simp only [Sym.eval, SBool.eval, vars_vv, vv32]
    rfl
  obtain ⟨hok, hnext, -, -⟩ := hq
  rw [hsi] at hok hnext
  rw [hdi] at hnext
  rw [NativeRustcVmX64.Vm.VerifyKeccak.b1_next] at hpc2
  refine stepJ (T' := t2) (vals' := vv m0 {}) (o := NativeRustcVmX64.Vm.VerifyKeccak.b2Offset) hp c h ⟨hpc2, hB2⟩ b2_in_code
    (by simp [b2]) run_b2 nofun (hB2.mt 0) (by decide) rfl rfl (by vtacJ) (by decide) rfl rfl rfl
    (fun _ _ _ _ _ h ↦ by cases h) rfl fun st3 hpc3 hB3 _ hchg3 hk3 ↦ ?_
  simp only [PcOk] at hpc3
  have hrun := verifyKeccak_grind (reg m0 .rsi).toNat inst output
  rw [gBits_eq] at hrun
  cases hr : (grind 0).run s with
  | none =>
    rw [hr] at hok
    have hal : boolRet st2.data = 0 := hok
    unfold boolRet at hal
    have hce : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
        (envZ m0 st2.data 3344 3368 (rsOf m0) (vv m0 {}) 0) = true := by
      rw [alCond]; exact decide_eq_true hal
    simp only [hce, ↓reduceIte] at hpc3
    exact fail32 hp hpre hB3 hpc3 (by rw [hrun]; exact run_bind_none hr)
  | some p =>
    obtain ⟨⟨⟩, s1⟩ := p
    rw [hr] at hok hnext
    have hal : boolRet st2.data = 1 := hok
    unfold boolRet at hal
    have hce : (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)).eval
        (envZ m0 st2.data 3344 3368 (rsOf m0) (vv m0 {}) 0) = false := by
      rw [alCond]; exact decide_eq_false fun h ↦ absurd (hal.symm.trans h) (by decide)
    simp only [hce, Bool.false_eq_true, ↓reduceIte] at hpc3
    refine cont st3 s1 ⟨hpc3.trans (by rw [NativeRustcVmX64.Vm.VerifyKeccak.b2_next]), hB3⟩
      (Chg.ts c hchg3 (by decide) (by decide) (by decide) hk3 (hnext () s1 rfl))
      (by rw [hrun]; exact run_bind_some hr)

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
