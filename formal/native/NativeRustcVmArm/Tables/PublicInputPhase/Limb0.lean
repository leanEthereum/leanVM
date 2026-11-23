module

public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Tables.PublicInputPhase.Limb1

/-!
# `public_input_phase`: the first limb

From `b3` (the point zeroed): the challenge as the point's first element and the limb's two words
beside it, `multilinear_eval_by` (`b3`), the first claim (`b4`, `push_claim`), its result (`b5`):
none, the exit; else the second limb (`limb0`).
-/

namespace NativeRustcVmArm.Tables.PublicInputPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PublicInputPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap Same)
open LeanVM.Protocol.Verifier (memory0 memory1)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4}
  {cs : Array ColumnClaimW} {m0 : MachineData}

/-- **The first limb**, from `b3`. -/
theorem limb0 (hp : Placed code k)
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hpre : PublicInputPhasePre a s L pub cs m0) {m : MachineData}
    (hi : LimbAt a s L pub cs zeroWords m0 m) :
    Eventually (step1 Host.exe) (Goal a s L pub cs m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b3Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, -, -, htok, hco, -, -, -, hvc, hPin, -⟩ := hpre'
  have hS1 := StackOk.rebase hS hi.kept
  have hN := hS.2.1
  have hPR : Readable (reb m0 m.dmem) m0.regs.X2.toBitVec 32 :=
    ⟨fun i h ↦ hi.kept _ (hPin.1.1 i h), hPin.1.2⟩
  have hwf := Bus.wf_frame2 hS1 le_N hi.fr.kept hPR hPin.2.1
  have hm : Match (Env.ofMachine m [(base m0 608, 608), (m0.regs.X2.toBitVec, 32)]) pubS m := by
    have := Bus.match_frame2 (r := .X20) (n := 32) hS1 le_N rfl hi.fr.sp
    rwa [hi.x20] at this
  refine exec_then (b3_in_code.trans hp.1 (by simp [b3])) run_b3 hwf hm fun st hm6 hpc6 ↦ ?_
  have hm6' : Match (Env.ofMachine m [(base m0 608, 608), (m0.regs.X2.toBitVec, 32)])
      (Bus.after b3 pubS) st.data := by
    rw [Bus.after_eq run_b3]; exact hm6
  obtain ⟨hsp6, hFW6, hk6, hp0, hp8, hnw6, h496, h504, h512, h520, h528, h536, h0, h1, h2, h3, h4,
    h19, h20, h21, h22, h23⟩ := ok_b3
  have hfr6 := Bus.Fr.block hi.fr hN le_N hm6' hwf hsp6 hFW6 hk6 slots_le
  -- The point's words: the challenge, the zeros kept.
  have hpt6 : Bus.FrameWords st.data.dmem (base m0 608) (ptWords s.sponge.squeeze.1) := by
    intro p hp
    simp only [ptWords, List.mem_cons, List.mem_map, List.mem_range] at hp
    rcases hp with rfl | rfl | ⟨j, hj, rfl⟩
    · have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) hp0
      rw [← hi.x21]; exact this
    · have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) hp8
      rw [← hi.x22]; exact this
    · refine Bus.wordAt_keep hm6' (r := 0) rfl (by omega) (hnw6 j hj) ?_
      have := hi.words (8 * (j + 2), 0)
        (List.mem_map.mpr ⟨j + 2, List.mem_range.mpr (by omega), rfl⟩)
      rwa [show 8 * (j + 2) = 16 + 8 * j by omega] at this
  -- The limb's words and the challenge.
  have hpw : ∀ i (h : i < 4), NativeRustcVm.wordOf m.dmem
      (m0.regs.X2.toBitVec + BitVec.ofNat 64 (8 * i)) = pub[i] := fun i h ↦ by
    rw [NativeRustcVm.wordOf_of_wordAt (NativeRustcVm.wordsAt_getElem hi.pub (i := i)
      (by simp; omega))]
    simp
  have w496 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 496) pub[0] := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h496
    rwa [Bus.load_r1, hpw 0 (by omega)] at this
  have w512 : NativeRustcVm.WordAt st.data.dmem (base m0 608 + BitVec.ofNat 64 512) pub[2] := by
    have := Bus.wordAt_write hm6' (r := 0) rfl (by omega) h512
    rwa [Bus.load_r1, hpw 2 (by omega)] at this
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
      [EW.ofK pub[0], EW.ofK pub[2]] := ewsAt_two w496 w504 w512 w520
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
      retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b4Offset) := hpc6
  refine mle_call hmle hS1 hfr6 hpc6' (Bus.Gkr.reg_lit hm6' h0) (Bus.Gkr.reg_lit hm6' h2)
    (Bus.Gkr.reg_lit hm6' h4) r1 r3 hxy hch fun m7 hfr7 hres hcs7 hs7 ↦ ?_
  have hpt7 : Bus.FrameWords m7.dmem (base m0 608) (ptWords s.sponge.squeeze.1) :=
    Bus.FrameWords.call hpt6 hfr6.sp (by have := le_mle; omega)
      (fun p hp ↦ by obtain ⟨j, hj, e⟩ := ptWords_off _ p hp; omega) (fun _ h ↦ h.elim) hs7
  -- `b4`: the first claim's arguments.
  refine Bus.Gkr.Fr.runBlock hS1 le_N rfl hfr7 (b4_in_code.trans hp.1 (by simp [b4])) run_b4
    rfl rfl (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_
  have hm8' : Match (Env.ofMachine m7 [(base (reb m0 m.dmem) 608, 608)]) (Bus.after b4 sF)
      st8.data := by
    rw [Bus.after_eq run_b4]; exact hm8
  obtain ⟨-, -, -, g0, g1, g2, g3, g4, g5, -, -, -, -, -⟩ := ok_b4
  have e19 : st8.data.regs.getXReg .X0 = m0.regs.X3 := by
    rw [Bus.Gkr.reg_of hm8' g0, hcs7 .X19 rfl, Bus.Gkr.reg_of hm6' h19, hi.x19]
  have e23 : st8.data.regs.X3.toNat = max (vcOf L) 1 := by
    show (st8.data.regs.getXReg .X3).toNat = _
    rw [Bus.Gkr.reg_of hm8' g3, hcs7 .X23 rfl, Bus.Gkr.reg_of hm6' h23, hi.x23]
  have e2 : st8.data.regs.X2.toBitVec = base (reb m0 m.dmem) 608 := by
    show (st8.data.regs.getXReg .X2).toBitVec = _
    rw [hm8'.regs .X2 _ g2, eval_ptr0]; simp
  have e1 : st8.data.regs.X1.toNat = 0 := by
    show (st8.data.regs.getXReg .X1).toBitVec.toNat = 0
    rw [Bus.Gkr.reg_lit hm8' g1]; rfl
  have e45 : ewArg st8.data.regs.X4 st8.data.regs.X5 = ewRet m7 := by
    show (⟨st8.data.regs.getXReg .X4, st8.data.regs.getXReg .X5⟩ : EW) =
      ⟨m7.regs.getXReg .X0, m7.regs.getXReg .X1⟩
    rw [Bus.Gkr.reg_of hm8' g4, Bus.Gkr.reg_of hm8' g5]
  have hn : max (vcOf L) 1 ≤ 31 := Nat.max_le.mpr ⟨hvc, by omega⟩
  have hcs8 : ClaimsWAt st8.data.dmem m0.regs.X3.toBitVec cs :=
    NativeRustcVm.Tables.ClaimsWAt.of_same hi.claims (same_fr hfr8 hS1 hco.2.1 hco.2.2.2.2.1)
  have hpt8 : Bus.FrameWords st8.data.dmem (base m0 608) (ptWords s.sponge.squeeze.1) := by
    rw [hd8]; exact hpt7
  have hcR : Readable (reb m0 m.dmem) m0.regs.X3.toBitVec claimsBytes :=
    ⟨fun i h ↦ hi.kept _ (hco.1 i h), hco.2.1⟩
  have e0' : st8.data.regs.X0 = m0.regs.X3 := e19
  refine push_call hpush hS1 hcR hco.2.2.2.2.1 hfr8 hpc8 (by rw [e0']) e2 e23 hn hcs8
    fun m9 hfr9 hq9 hcs9 ↦ ?_
  have hslice : slice st8.data st8.data.regs.X2 st8.data.regs.X3 =
      pt s.sponge.squeeze.1 (vcOf L) := by
    unfold slice
    rw [e2, e23, ← pt_max]
    exact ewsOf_pt hpt8 (by omega) hn
  have hpt9 : Bus.FrameWords m9.dmem (base m0 608) (ptWords s.sponge.squeeze.1) :=
    Bus.FrameWords.call hpt8 hfr8.sp (by have := le_push; omega)
      (fun p hp ↦ by obtain ⟨j, hj, e⟩ := ptWords_off _ p hp; omega)
      (fun q hq ↦ NativeRustcVm.Apart.not_inRange (apart_frame hN le_N hco.2.2.2.2.1) hco.2.1
        (base_noWrap (by have := le_N; omega)) hq)
      (NativeRustcVm.SameOutside.mono hq9.2.1 fun q hq' ↦ hq'.elim
        (fun h ↦ .inr (by rw [e0'] at h; exact h)) .inl)
  have hts9 : TStateAt m9.dmem m0.regs.X0.toBitVec a { s with sponge := s.sponge.squeeze.2 } :=
    tstate_fr hfr9 hS1 htok (out_not_ts hi.ts hco) hi.ts
  have hrun := run_eq L pub s
  -- `b5`: the first claim's result.
  refine Bus.Gkr.Fr.runBlock hS1 le_N rfl hfr9 (b5_in_code.trans hp.1 (by simp [b5])) run_b5
    rfl rfl (by decide) (by decide) fun st10 hfr10 hd10 hm10 hpc10 ↦ ?_
  obtain ⟨hif, -, -⟩ := hq9
  have hpt : st8.data.regs.X3.toNat ≤ pointCap := by rw [e23]; unfold pointCap; omega
  split at hif
  next hc =>
    -- Pushed: the second limb.
    have hc0 : CmpOp.eq.apply .W32 (m9.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = false := by
      rw [show m9.regs.getXReg .X0 = m9.regs.X0 from rfl, hif.1]; decide
    simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, hc0, Bool.false_eq_true,
      ↓reduceIte] at hpc10
    refine Bus.Gkr.at_pc hpc10 (limb1 hp hmle hpush hpre ?_)
    have hfrR := Fr.rebase hfr10
    have hd10' : st10.data.dmem = m9.dmem := hd10
    have hclaims := hif.2
    rw [hslice, e1, e45, hres, e0'] at hclaims
    refine ⟨hfrR, ?_, ?_, ?_, ?_, ?_, by rw [hd10']; exact hpt9, by rw [hd10']; exact hclaims,
      ?_, by rw [hd10']; exact hts9, ?_, ?_⟩
    · rw [Bus.Gkr.reg_of hm10 (r := .X19) rfl, hcs9 .X19 rfl, Bus.Gkr.reg_of hm8' (r := .X19) rfl,
        hcs7 .X19 rfl, Bus.Gkr.reg_of hm6' h19, hi.x19]
    · apply UInt64.toBitVec_inj.mp
      rw [Bus.Gkr.reg_of hm10 (r := .X20) rfl, hcs9 .X20 rfl, Bus.Gkr.reg_of hm8' (r := .X20) rfl,
        hcs7 .X20 rfl, hm6'.regs .X20 _ h20]
      simp [Sym.eval]
    · rw [Bus.Gkr.reg_of hm10 (r := .X21) rfl, hcs9 .X21 rfl, Bus.Gkr.reg_of hm8' (r := .X21) rfl,
        hcs7 .X21 rfl, Bus.Gkr.reg_of hm6' h21, hi.x21]
    · rw [Bus.Gkr.reg_of hm10 (r := .X22) rfl, hcs9 .X22 rfl, Bus.Gkr.reg_of hm8' (r := .X22) rfl,
        hcs7 .X22 rfl, Bus.Gkr.reg_of hm6' h22, hi.x22]
    · rw [Bus.Gkr.reg_of hm10 (r := .X23) rfl, hcs9 .X23 rfl, Bus.Gkr.reg_of hm8' (r := .X23) rfl,
        hcs7 .X23 rfl, Bus.Gkr.reg_of hm6' h23, hi.x23]
    · -- The public input, apart from the claims.
      have hap := hPin.2.2 ⟨m0.regs.X3.toBitVec, claimsBytes⟩ (by simp)
      refine NativeRustcVm.Tables.WordsAt.of_same hi.pub
        (Bus.Fr.bytes_eq hfr10 hS1 hPin.1.2 hPin.2.1 fun j hj ↦
          Bus.not_inRange_of_apart hap hPin.1.2 hco.2.1 hj) (by simp)
    · exact fun p hp ↦ hfr10.kept p (hi.kept p hp)
    · exact (NativeRustcVm.SameOutside.trans hi.same hfr10.same).mono fun q hq ↦
        hq.elim id fun h ↦ h.elim Or.inl fun h ↦ Or.inr (Or.inr h)
  next hc =>
    -- Not pushed: the exit with `0`.
    have hc0 : CmpOp.eq.apply .W32 (m9.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = true := by
      rw [show m9.regs.getXReg .X0 = m9.regs.X0 from rfl, hif]; decide
    simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, hc0, ↓reduceIte] at hpc10
    have hfit : ¬cs.size + 2 ≤ claimCap := fun h ↦ hc ⟨by omega, hpt⟩
    refine Bus.Gkr.at_pc (hpc10.trans (hp.label (j := NativeRustcVmArm.Vm.PublicInputPhase.b8Offset) NativeRustcVmArm.Vm.PublicInputPhase.label_3_at)) (exit8 hp hS hfr10 hi.kept hi.same
      fun m' hd' hx0' ↦ ⟨?_, fun x s' _ h ↦ absurd h hfit, fun x s' hr ↦ ?_⟩)
    · rw [hx0', show st10.data.regs.X0 = m9.regs.X0 from Bus.Gkr.reg_of hm10 (r := .X0) rfl, hif,
        hrun]
      simp [hfit, okWord]
    · rw [hrun] at hr
      cases hr
      rw [hd', hd10]
      exact hts9

end

end NativeRustcVmArm.Tables.PublicInputPhase
