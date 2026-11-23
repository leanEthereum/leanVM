module

public import NativeRustcVmX64.Tables.PublicInputPhase.Calls
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names

/-!
# `public_input_phase`: the two limbs (x86-64)

`LimbAt`: a state of the frame at a limb's start (the challenge in R15, R12, the claims so far, the
point's words, the `TState` after the challenge). `limb1`: `b6`,
`multilinear_eval_by`, `b7`, `push_claim`, `b8`, the exit. `limb0`: `b3`, `multilinear_eval_by`,
`b4`, `push_claim`, `b5`, then `limb1` or the exit.
-/

namespace NativeRustcVmX64.Tables.PublicInputPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmX64.Vm.PublicInputPhase
open NativeRustcVmX64.Bus.Gkr (Fr testAl_okAl)
open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)
open NativeRustcVm.Layout (LayoutWAt layoutBytes Same ClaimsWAt claimsBytes claimCap pointCap)
open LeanVM.Protocol.Verifier (memory0 memory1)

@[expose] public section

/-- The challenge. -/
abbrev chOf (s : TState) : EW := s.sponge.squeeze.1

/-- The first claim. -/
def claim0 (s : TState) (L : LayoutW) (pub : Vector UInt64 4) : ColumnClaimW :=
  ⟨memory0, pt (chOf s) (vcOf L), multilinearEval #[EW.ofK pub[0], EW.ofK pub[2]] #[chOf s]⟩

/-- The second claim. -/
def claim1 (s : TState) (L : LayoutW) (pub : Vector UInt64 4) : ColumnClaimW :=
  ⟨memory1, pt (chOf s) (vcOf L), multilinearEval #[EW.ofK pub[1], EW.ofK pub[3]] #[chOf s]⟩

/-- **At a limb's start**: a state of the frame at offset `8`, the registers, the claims `cs'`,
the point's words from `lo`, the `TState` after the challenge. -/
structure LimbAt [Labels] (a : DecArea) (s : TState) (L : LayoutW) (cs' : Array ColumnClaimW)
    (lo : Nat) (m0 m : MachineData) : Prop where
  fr : St m0 8 m
  rbx : reg m .rbx = reg m0 .rcx
  r14 : reg m .r14 = reg m0 .rdx
  r15 : reg m .r15 = (chOf s).c0.toBitVec
  r12 : reg m .r12 = (chOf s).c1.toBitVec
  r13 : reg m .r13 = BitVec.ofNat 64 (max (vcOf L) 1)
  claims : ClaimsWAt m.dmem (reg m0 .rcx) cs'
  pt : PtW m0 m.dmem (chOf s) lo
  ts : TStateAt m.dmem (reg m0 .rdi) a { s with sponge := s.sponge.squeeze.2 }

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

omit [Host] in
theorem fits_iff (cs : Array ColumnClaimW) :
    (cs.push (claim0 s L pub)).size < claimCap ↔ cs.size + 2 ≤ claimCap := by
  simp only [Array.size_push]; omega

omit [Host] in
theorem run_some : ((publicInputPhase L pub).run s).isSome = true := by rw [run_eq]; rfl

/-- **The second limb**: `b6`, its value, `b7`, its claim, `b8`, the exit. -/
theorem limb1 (hp : Placed code k) (h : PublicInputPhasePre a s L pub cs m0)
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b6Offset))
    (hL : LimbAt a s L (cs.push (claim0 s L pub)) 0 m0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧ rspOf st'.data = rspOf m0 + 8#64 ∧
      PublicInputPhasePost a s L pub cs m0 st'.data) st := by
  have p := pre_parts h
  obtain ⟨hm6, h06, hw6, hr6, hwr6⟩ := after_eq run_b6 ▸ ok_b6
  refine mleStep h hL.fr hL.r14 hL.r15 hL.r12 (i := 1) (by omega) (b6_in_code.trans hp.1
    (by simp [b6])) run_b6 hm6 h06 (by simpa using hr6) (by simpa using hwr6) hmle hpc
    fun st1 st2 hm1 hpc2 fr2 hval hcs2 hkeep2 hs2 hk2 ↦ ?_
  have hwf1 := wfPub h hL.fr (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b6Offset + b6.length)).toBitVec)
  have hpt2 : PtW m0 st2.data.dmem (chOf s) 0 := fun i h1 h2 j hj ↦ by
    have hj' : j < 8 := by simpa [NativeRustcVm.length_wordBytes] using hj
    rw [off_add, hkeep2 _ (by omega) (by omega), keepHi hwf1 hm1 (writesIn_of_mid hm6) hw6
      (by omega) (by omega), ← off_add]
    exact hL.pt i h1 h2 j hj
  have hcl2 := claims_keep h hs2 (fun _ hq ↦ hq) hL.claims
  obtain ⟨hm7, h07, hw7, hr7⟩ := after_eq run_b7 ▸ ok_b7
  refine pushStep h fr2 hcl2 hpt2 ((hcs2 .rbx rfl).trans hL.rbx) ((hcs2 .r13 rfl).trans hL.r13)
    p.2.2.2.2.2.2.2.2.1 (col := 1) (v := .reg .rbp) (b7_in_code.trans hp.1 (by simp [b7]))
    run_b7 hm7 h07 hw7 hr7 (by decide) hpush (by rw [hpc2]; rfl)
    fun st3 st4 hm3 hpc4 fr4 hres4 hcs4 _ hs4 hk4 ↦ ?_
  have hts4 : TStateAt st4.data.dmem (reg m0 .rdi) a { s with sponge := s.sponge.squeeze.2 } :=
    tstate_keep h hL.ts (fun p hp ↦ hk4 p (hk2 p hp)) (hs2.trans hs4) fun q hq ↦ by
      rcases hq with hq | hq
      · exact .inl hq
      · exact hq
  -- `b8`, the exit
  obtain ⟨hm8, hmem8, hr8⟩ := after_eq run_b8 ▸ ok_b8
  refine blk h fr4 (b8_in_code.trans hp.1 (by simp [b8])) run_b8 hm8
    (by rw [hmem8]; intro w hw; cases hw) (by rw [hpc4]; rfl) fun st5 fr5 hm5 _ hpc5 ↦ ?_
  have hwf5 := wfF h fr4 (vars := fun _ ↦ 0) (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.PublicInputPhase.b8Offset + b8.length)).toBitVec)
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf5 hmem8
  have hrbp5 : (reg st5.data .rbp).toNat % 256 = boolRet st4.data := by
    rw [show reg st5.data .rbp = _ from hm5.regs _ _ (hr8 (.rbp, .un .trunc .W32 (.reg .rax)) (by simp))]
    exact NativeRustcVmX64.Transcript.trunc32_mod _
  simp only [PcOk] at hpc5
  refine exit9 hp h (by rw [hpc5]; rfl) fr5 ?_ ?_ ?_
  · rw [hrbp5, run_some, Bool.true_and]
    by_cases hf : (cs.push (claim0 s L pub)).size < claimCap
    · simp only [hf, ↓reduceIte] at hres4
      rw [hres4.1, decide_eq_true ((fits_iff cs).mp hf)]; rfl
    · simp only [hf, ↓reduceIte] at hres4
      rw [hres4, decide_eq_false fun h' ↦ hf ((fits_iff cs).mpr h')]; rfl
  · intro x s' hr hf
    rw [run_eq] at hr
    cases hr
    have hf' := (fits_iff (s := s) (L := L) (pub := pub) cs).mpr hf
    simp only [hf', ↓reduceIte] at hres4
    rw [hd5, ← push_push]
    have := hres4.2
    rw [show ewRet st2.data = (claim1 s L pub).value from hval] at this
    exact this
  · intro x s' hr
    rw [run_eq] at hr
    cases hr
    rw [hd5]; exact hts4

end

end NativeRustcVmX64.Tables.PublicInputPhase
