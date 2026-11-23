module

public import NativeRustcVmX64.Sumcheck.Plain.Frame
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# `sumcheck` with `sumcheck_plain`'s closure: a round's polynomial (x86-64)

From the loop's head (`Inv`), `b2` writes `eq = None` and calls `sumcheck_round_poly`; `b3` leaves
for `.L3` on a rejection (`exit_fail`), else at `b4` the polynomial read (`Mid`, `head_spec`).
-/

namespace NativeRustcVmX64.Sumcheck.Plain

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Sumcheck

@[expose] public section

/-- At `b4`, round `i`'s polynomial `msg` read, the state `s1`, the first `i` challenges `xs`. -/
structure Mid [Labels] (a : DecArea) (s : TState) (m0 : MachineData) (i : Nat) (xs msg : Array EW)
    (s1 : TState) (m : MachineData) : Prop where
  fr : FrP m0 8 m
  lt : i < nP m0
  out : NativeRustcVm.WordAt m.dmem (off (fP m0) 16) (UInt64.ofBitVec (outP m0))
  r12 : reg m .r12 = tP m0
  r13 : reg m .r13 = off (fP m0) 104
  r14 : reg m .r14 = off (slP m0) (16 * i)
  r15 : reg m .r15 = reg m0 .r8
  rbx : reg m .rbx = off (slP m0) (16 * nP m0)
  rbp : reg m .rbp = off (fP m0) 24
  run : (sumcheckFn (claimArg m0) (cntP m0) (fun _ ↦ none) (i + 1)).run s =
    some ((xs.push s1.sponge.squeeze.1, polyEval msg s1.sponge.squeeze.1),
      { s1 with sponge := s1.sponge.squeeze.2 })
  xsz : xs.size = i
  xs : NativeRustcVm.EWsAt m.dmem (slP m0) xs.toList
  msz : msg.size = cntP m0
  msg : NativeRustcVm.EWsAt m.dmem (off (fP m0) 24) msg.toList
  ts : TStateAt m.dmem (tP m0) a s1

/-- What the loop ends in: the exit (a rejection), or `.L5` after the last round. -/
abbrev Goal [Host] (a : DecArea) (s : TState) (m0 : MachineData) (k : Nat) (st : MachineState) :
    Prop :=
  (st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ SumcheckPlainPost a s m0 st.data) ∨
    (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b7Offset) ∧ Done a s m0 st.data)

end

public section

variable [Host] {a : DecArea} {s : TState} {m0 : MachineData} {k : Nat}

/-- **A round's polynomial**: from the head, a rejection's exit or `b4` with the polynomial. -/
theorem head_spec (hp : Placed code k)
    (hrp : ∀ a s e, Spec (Labels.label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e))
    (hpre : SumcheckPlainPre a s m0) {i : Nat} {m : MachineData} (hi : Inv a s m0 i m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Goal a s m0 k st ∨
        (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b4Offset) ∧ ∃ xs msg s1, Mid a s m0 i xs msg s1 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2Offset)⟩ := by
  have g := geo hpre
  obtain ⟨xs, si, hrun, hsz, hxs, hts⟩ := hi.run
  have hlt := hi.lt
  have hl3 : Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b8Offset) :=
    hp.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_3_at
  -- `b2`: `eq = None`, `sumcheck_round_poly`.
  have hwf2 := wf_envB hpre hi.fr (Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2Offset + b2.length)).toBitVec
  refine exec_then (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf2 (fun _ _ ↦ rfl)
    (match_bodyS hi.fr _) fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hw2, hW104, hrdi2, hrsi2, hrdx2, hrcx2, hr8_2, hr9_2, hk2⟩ := ok_b2
  have hin2 := writesIn_of_mid hmid2
  have hs2 : NativeRustcVm.SameOutside m.dmem st2.data.dmem (NativeRustcVm.InRange (fP m0) 176) :=
    sameOutside_low hwf2 hm2 (r := 0) rfl (hi := 176) (by omega) fun w hw ↦
      ⟨(hw2 w hw).1, by rcases (hw2 w hw).2 with h | h <;> omega⟩
  have hf2 : FrP m0 0 st2.data :=
    g.block hi.fr hwf2 hm2 hmid2 hs2 fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)
  have ts2 : TStateAt st2.data.dmem (tP m0) a si :=
    g.t_keep hs2 (hm2.kept hwf2) (fun q hq ↦ Or.inl (g.ctx.inRange_frame hq)) hts
  have xs2 : NativeRustcVm.EWsAt st2.data.dmem (slP m0) xs.toList :=
    g.sl_keep hs2 (fun q hq ↦ g.not_sl_stack (g.ctx.inRange_frame hq)) (by simp [hsz]; omega) hxs
  have he2 : OptEWAt st2.data.dmem (off (fP m0) 104) none :=
    wordAt_written hm2 (r := 0) (o := 104) rfl (by omega) hW104 (w := 0) rfl
  have out2 := keepW hwf2 hm2 hin2 (o := 16) (by omega) (fun w hw _ ↦ by
    rcases (hw2 w hw).2 with h | h <;> omega) hi.out
  have hrdi : reg st2.data .rdi = tP m0 := (hm2.regs .rdi _ hrdi2).trans hi.r12
  have hrsi : (reg st2.data .rsi).toNat = cntP m0 := by
    rw [show reg st2.data .rsi = _ from (hm2.regs .rsi _ hrsi2).trans hi.r15]
  have hr8 : reg st2.data .r8 = off (fP m0) 104 := (hm2.regs .r8 _ hr8_2).trans hi.r13
  have hr9 : reg st2.data .r9 = off (fP m0) 24 := (hm2.regs .r9 _ hr9_2).trans hi.rbp
  have hclaim : (⟨.ofBitVec (reg st2.data .rdx), .ofBitVec (reg st2.data .rcx)⟩ : EW) =
      claimR m := by
    rw [show reg st2.data .rdx = _ from hm2.regs .rdx _ hrdx2,
      show reg st2.data .rcx = _ from hm2.regs .rcx _ hrcx2]
    rfl
  have hreg2 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st2.data r = reg m r :=
    fun r hr ↦ hm2.regs r _ (Keeps.reg hk2 hr)
  refine call_then hpc2 (hrp a si none)
    (g.roundPolyPre hf2 (Mo := 24) (Eo := 104) (by omega) (by omega) (by omega) (by omega) ts2 he2
      hrdi hrsi hr8 hr9) fun st3 hpc3 hrsp3 hpost3 ↦ ?_
  have hok3 := hpost3.1
  have hsv3 := hpost3.2.2.2.2
  obtain ⟨hf3, hmsg3, hsl3, hloc3⟩ := g.afterRoundPoly hf2 (Mo := 24) (by omega) hpost3 hrsp3 hrdi hr9
  rw [hrsi, hclaim] at hok3 hmsg3
  have out3 := hloc3 16 (NativeRustcVm.wordBytes (UInt64.ofBitVec (outP m0))) (by omega)
    (by rw [NativeRustcVm.length_wordBytes]; omega)
    (Or.inl (by rw [NativeRustcVm.length_wordBytes])) out2
  have hreg3 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st3.data r = reg m r :=
    fun r hr ↦ (hsv3.1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)).trans
      (hreg2 r hr)
  -- `b3`: the polynomial's test.
  have hwf3 := wf_envB hpre hf3 0
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b2_next)) (match_bodyS hf3 _) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hmem4, hk4⟩ := ok_b3
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  have hf4 : FrP m0 8 st4.data := g.block hf3 hwf3 hm4 hmid4 (R := fun _ ↦ False)
    (fun q _ ↦ by rw [hd4]) fun _ h ↦ h.elim
  have hreg4 : ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], reg st4.data r = reg m r :=
    fun r hr ↦ (hm4.regs r _ (Keeps.reg hk4 hr)).trans (hreg3 r hr)
  have hc : cAl.eval (envB m0 st3.data 0) = decide ((reg st3.data .rax).toNat % 256 = 0) :=
    testAl_eq _
  simp only [PcOk, hc] at hpc4
  cases hr : (sumcheckRoundPoly (cntP m0) (claimR m) none).run si with
  | none =>
    rw [hr] at hok3
    have hal : (reg st3.data .rax).toNat % 256 = 0 := hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b8Offset) := by
      rw [hpc4, hal]; simp [hl3]
    have hnone := sumcheckFn_run_none_le (sumcheckFn_run_succ_none hrun hr)
      (show i + 1 ≤ nP m0 by omega)
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc
    subst hpc
    exact Eventually.mono (exit_fail hp hpre hf4 (by rw [hd4]; exact out3) hnone)
      fun st h ↦ .inl (.inl h)
  | some p =>
    obtain ⟨msg, s1⟩ := p
    rw [hr] at hok3
    have hal : (reg st3.data .rax).toNat % 256 = 1 := hok3
    have hpc : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.b4Offset) := by
      rw [hpc4, hal]; rfl
    obtain ⟨hmsg, hts3⟩ := hmsg3 msg s1 hr
    refine Eventually.done _ (.inr ⟨hpc, xs, msg, s1, hf4, hlt, by rw [hd4]; exact out3,
      ?_, ?_, ?_, ?_, ?_, ?_, sumcheckFn_run_succ_some hrun hr, hsz, ?_,
      roundPoly_size g.cnt2 hr, ?_, ?_⟩)
    · rw [hreg4 .r12 (by simp)]; exact hi.r12
    · rw [hreg4 .r13 (by simp)]; exact hi.r13
    · rw [hreg4 .r14 (by simp)]; exact hi.r14
    · rw [hreg4 .r15 (by simp)]; exact hi.r15
    · rw [hreg4 .rbx (by simp)]; exact hi.rbx
    · rw [hreg4 .rbp (by simp)]; exact hi.rbp
    · rw [hd4]; exact hsl3 xs.toList (by simp [hsz]; omega) xs2
    · rw [hd4]; exact hmsg
    · rw [hd4]; exact hts3

end

end NativeRustcVmX64.Sumcheck.Plain
