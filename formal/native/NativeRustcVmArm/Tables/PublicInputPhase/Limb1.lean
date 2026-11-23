module

public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Tables.PublicInputPhase.Limbs

/-!
# `public_input_phase`: the second limb

From `b6` (the first claim pushed): the limb's two words beside the challenge, `multilinear_eval_by`
(`b6`), the second claim (`b7`, `push_claim`), the exit (`b8`): `limb1`.
-/

namespace NativeRustcVmArm.Tables.PublicInputPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PublicInputPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)
open LeanVM.Protocol.Verifier (memory0 memory1)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

/-- **The second limb**, from `b6`. -/
theorem limb1 (hp : Placed code k)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hpre : PublicInputPhasePre a s L pub cs m0) {m : MachineData}
    (hi : LimbAt a s L pub (cs.push (claim0 s L pub)) (ptWords s.sponge.squeeze.1) m0 m) :
    Eventually (step1 Host.exe) (Goal a s L pub cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b6Offset)⟩ := by
  obtain ⟨hS, -, -, htok, hco, -, -, -, hvc, hPin, -⟩ := hpre
  have hS1 := StackOk.rebase hS hi.kept
  have hN := hS.2.1
  have hPR : Readable (reb m0 m.dmem) m0.regs.X2.toBitVec 32 :=
    ⟨fun i h ↦ hi.kept _ (hPin.1.1 i h), hPin.1.2⟩
  have hwf := Bus.wf_frame2 hS1 le_N hi.fr.kept hPR hPin.2.1
  have hm : Match (Env.ofMachine m [(base m0 608, 608), (m0.regs.X2.toBitVec, 32)]) pubS m := by
    have := Bus.match_frame2 (r := .X20) (n := 32) hS1 le_N rfl hi.fr.sp
    rwa [hi.x20] at this
  refine exec_then (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hwf hm fun st hm6 hpc6 ↦ ?_
  have hm6' : Match (Env.ofMachine m [(base m0 608, 608), (m0.regs.X2.toBitVec, 32)])
      (Bus.after b6 pubS) st.data := by
    rw [Bus.after_eq run_b6]; exact hm6
  obtain ⟨hsp6, hFW6, hk6, hnw6, h496, h504, h512, h520, h528, h536, h0, h1, h2, h3, h4, h19, -,
    -, -, h23⟩ := ok_b6
  have hfr6 := Bus.Fr.block hi.fr hN le_N hm6' hwf hsp6 hFW6 hk6 slots_le
  -- The point's words, kept.
  have hpt6 : Bus.FrameWords st.data.dmem (base m0 608) (ptWords s.sponge.squeeze.1) :=
    Bus.FrameWords.block hi.words hm6' fun p hp ↦ by
      obtain ⟨j, hj, e⟩ := ptWords_off _ p hp
      exact ⟨by omega, by rw [e]; exact hnw6 j hj⟩
  -- The limb's words and the challenge.
  have hpw : ∀ i (h : i < 4), NativeRustcVm.wordOf m.dmem
      (m0.regs.X2.toBitVec + BitVec.ofNat 64 (8 * i)) = pub[i] := fun i h ↦ by
    rw [NativeRustcVm.wordOf_of_wordAt (NativeRustcVm.wordsAt_getElem hi.pub (i := i)
      (by simp; omega))]
    simp
  have w496 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 496) pub[1] := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h496
    rwa [Bus.load_r1, hpw 1 (by omega)] at this
  have w512 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 512) pub[3] := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h512
    rwa [Bus.load_r1, hpw 3 (by omega)] at this
  have w504 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 504) 0 := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h504
    exact this
  have w520 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 520) 0 := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h520
    exact this
  have w528 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 528)
      s.sponge.squeeze.1.c0 := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h528
    rw [← hi.x21]; exact this
  have w536 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 536)
      s.sponge.squeeze.1.c1 := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h536
    rw [← hi.x22]; exact this
  have hxy : NativeRustcVm.EWsAt st.data.dmem (base m0 608 + BitVec.ofNat 64 496)
      [EW.ofK pub[1], EW.ofK pub[3]] := ewsAt_two w496 w504 w512 w520
  have hch : NativeRustcVm.EWsAt st.data.dmem (base m0 608 + BitVec.ofNat 64 528)
      [s.sponge.squeeze.1] := ewsAt_one w528 w536
  -- The arguments.
  have r1 : st.data.regs.X1.toBitVec = base m0 608 + BitVec.ofNat 64 496 := by
    show (st.data.regs.getXReg .X1).toBitVec = _
    rw [hm6'.regs .X1 _ h1, eval_ptr0]; rfl
  have r3 : st.data.regs.X3.toBitVec = base m0 608 + BitVec.ofNat 64 528 := by
    show (st.data.regs.getXReg .X3).toBitVec = _
    rw [hm6'.regs .X3 _ h3, eval_ptr0]; rfl
  have hpc6' : st.pc = Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel ∧
      retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b7Offset) := hpc6
  refine mle_call hmle hS1 hfr6 hpc6' (Bus.Gkr.reg_lit hm6' h0) (Bus.Gkr.reg_lit hm6' h2)
    (Bus.Gkr.reg_lit hm6' h4) r1 r3 hxy hch fun m7 hfr7 hres hcs7 hs7 ↦ ?_
  have hpt7 : Bus.FrameWords m7.dmem (base m0 608) (ptWords s.sponge.squeeze.1) :=
    Bus.FrameWords.call hpt6 hfr6.sp (by have := le_mle; omega)
      (fun p hp ↦ by obtain ⟨j, hj, e⟩ := ptWords_off _ p hp; omega) (fun _ h ↦ h.elim) hs7
  -- `b7`: the second claim's arguments.
  refine Bus.Gkr.Fr.runBlock hS1 le_N rfl hfr7 (b7_in_code.trans hp.1 (by simp [b7])) run_b7 rfl rfl
    (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_
  have hm8' : Match (Env.ofMachine m7 [(base (reb m0 m.dmem) 608, 608)]) (Bus.after b7 sF)
      st8.data := by
    rw [Bus.after_eq run_b7]; exact hm8
  obtain ⟨-, -, -, g0, g1, g2, g3, g4, g5, -, -, -, -, -⟩ := ok_b7
  have e19 : st8.data.regs.getXReg .X0 = m0.regs.X3 := by
    rw [Bus.Gkr.reg_of hm8' g0, hcs7 .X19 rfl, Bus.Gkr.reg_of hm6' h19, hi.x19]
  have e23 : st8.data.regs.X3.toNat = max (vcOf L) 1 := by
    show (st8.data.regs.getXReg .X3).toNat = _
    rw [Bus.Gkr.reg_of hm8' g3, hcs7 .X23 rfl, Bus.Gkr.reg_of hm6' h23, hi.x23]
  have e2 : st8.data.regs.X2.toBitVec = base (reb m0 m.dmem) 608 := by
    show (st8.data.regs.getXReg .X2).toBitVec = _
    rw [hm8'.regs .X2 _ g2, eval_ptr0]; simp
  have e1 : st8.data.regs.X1.toNat = 1 := by
    show (st8.data.regs.getXReg .X1).toBitVec.toNat = 1
    rw [Bus.Gkr.reg_lit hm8' g1]; rfl
  have e45 : ewArg st8.data.regs.X4 st8.data.regs.X5 = ewRet m7 := by
    show (⟨st8.data.regs.getXReg .X4, st8.data.regs.getXReg .X5⟩ : EW) =
      ⟨m7.regs.getXReg .X0, m7.regs.getXReg .X1⟩
    rw [Bus.Gkr.reg_of hm8' g4, Bus.Gkr.reg_of hm8' g5]
  have hn : max (vcOf L) 1 ≤ 31 := Nat.max_le.mpr ⟨hvc, by omega⟩
  have hcs8 : ClaimsWAt st8.data.dmem m0.regs.X3.toBitVec (cs.push (claim0 s L pub)) :=
    NativeRustcVm.Tables.ClaimsWAt.of_same hi.claims (same_fr hfr8 hS1 hco.2.1 hco.2.2.2.2.1)
  have hpt8 : Bus.FrameWords st8.data.dmem (base m0 608) (ptWords s.sponge.squeeze.1) := by
    rw [hd8]; exact hpt7
  have hcR : Readable (reb m0 m.dmem) m0.regs.X3.toBitVec claimsBytes :=
    ⟨fun i h ↦ hi.kept _ (hco.1 i h), hco.2.1⟩
  refine push_call hpush hS1 hcR hco.2.2.2.2.1 hfr8 hpc8 (by rw [show st8.data.regs.X0 =
    st8.data.regs.getXReg .X0 from rfl, e19]) e2 e23 hn hcs8 fun m9 hfr9 hq9 _ ↦ ?_
  -- The exit.
  refine exit8 hp hS hfr9 hi.kept hi.same fun m' hd' hx0' ↦ ?_
  have hslice : slice st8.data st8.data.regs.X2 st8.data.regs.X3 = pt s.sponge.squeeze.1 (vcOf L) := by
    unfold slice
    rw [e2, e23, ← pt_max]
    exact ewsOf_pt hpt8 (by omega) hn
  have hts9 : TStateAt m9.dmem m0.regs.X0.toBitVec a { s with sponge := s.sponge.squeeze.2 } :=
    tstate_fr hfr9 hS1 htok (out_not_ts hi.ts hco) hi.ts
  have hrun := run_eq L pub s
  refine ⟨?_, fun x s' hr hfit ↦ ?_, fun x s' hr ↦ ?_⟩
  · rw [hx0', hrun]
    obtain ⟨hif, -, -⟩ := hq9
    split at hif
    next hc =>
      have hfit : cs.size + 2 ≤ claimCap := by simp at hc; omega
      rw [hif.1]
      simp [hfit, okWord]
    next hc =>
      have hfit : ¬cs.size + 2 ≤ claimCap := fun h ↦
        hc ⟨by simp; omega, by rw [e23]; unfold pointCap; omega⟩
      rw [hif]
      simp [hfit, okWord]
  · rw [hrun] at hr
    cases hr
    obtain ⟨hif, -, -⟩ := hq9
    split at hif
    next hc =>
      have h2 := hif.2
      have e0' : st8.data.regs.X0 = m0.regs.X3 := e19
      rw [hslice, e1, e45, hres, ← hd', e0'] at h2
      rw [← push_push]
      exact h2
    next hc =>
      exact absurd ⟨by simp; omega, by rw [e23]; unfold pointCap; omega⟩ hc
  · rw [hrun] at hr
    cases hr
    rw [hd']
    exact hts9

end

end NativeRustcVmArm.Tables.PublicInputPhase
