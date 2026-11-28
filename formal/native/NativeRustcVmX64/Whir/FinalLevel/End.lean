module

public import NativeRustcVmX64.Whir.FinalLevel.Glued
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names

/-!
# `final_level`: the end check (x86-64)

From `b33` (`GB` with the weight `finalWeight`): the folded scalars' first `2 ^ μ` evaluated at
the tail (`multilinear_eval`, `b33`), times the weight (`EW::mul`, `b34`), compared with the
claim at `88`, `96` (`b35`), to the epilogue: `finish`.
-/

namespace NativeRustcVmX64.Whir.Levels.FL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.FinalLevel

public section

theorem slice_take {m : MachineData} {a : BitVec 64} {xs : Array EW} {n : BitVec 64}
    (h : NativeRustcVm.EWsAt m.dmem a xs.toList) (hn : n.toNat ≤ xs.size) :
    slice m a n = xs.extract 0 n.toNat := by
  have ht := NativeRustcVm.ewsOf_of_ewsAt (NativeRustcVm.EWsAt.take h n.toNat)
  rw [List.length_take, Array.length_toList, Nat.min_eq_left hn] at ht
  unfold slice
  rw [ht]
  apply Array.ext'
  simp

theorem beq_toBitVec (x y : UInt64) : (x.toBitVec == y.toBitVec) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne]
    exact fun h' ↦ h (UInt64.toBitVec_inj.mp h')

theorem orxor_beq (x y u v : BitVec 64) :
    ((u ^^^ v ||| (x ^^^ y)) == 0#64) = (x == y && u == v) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Bool.and_eq_true, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h2, h1⟩, fun ⟨h1, h2⟩ ↦ ⟨h2, h1⟩⟩

theorem al_merge (x : BitVec 64) (b : Bool) :
    (BinOp.apply .merge .W8 x (if b then BitVec.ofNat 64 1 else BitVec.ofNat 64 0)).toNat % 256 =
      (okWord b).toNat := by
  have e : ∀ z : BitVec 64, z.toNat % 256 = (low .W8 z).toNat := fun z ↦ by
    simp [low, BitVec.toNat_setWidth]
  rw [e, BinOp.apply, low8_merge]
  cases b <;> rfl

theorem vEnd_eval [Labels] (env : Env) {x y u v : BitVec 64} (hax : env.regs .rax = x)
    (hdx : env.regs .rdx = u) (h88 : env.load 0 88 8 = y) (h96 : env.load 0 96 8 = v) :
    vEnd.eval env = if (x == y && u == v) then BitVec.ofNat 64 1 else BitVec.ofNat 64 0 := by
  simp only [vEnd, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, hax, hdx,
    h88, h96]
  rw [← orxor_beq]

theorem inRange_zero {a q : BitVec 64} : ¬NativeRustcVm.InRange a 0 q := fun h ↦ by
  unfold NativeRustcVm.InRange at h; omega

variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The end check**: `b33` to `b35`, the epilogue. -/
theorem finish (hp : Placed code k) (c : Ctx a s level ba b w rounds m0)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmle : Spec (Labels.label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    {st : MachineState} {folded tail : Array EW} {claim : EW} {s5 : TState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b33Offset)) (htn : tail.size = mu m0)
    (hgb : GB a level m0 folded tail claim (finalWeight (reg m0 .r8).toNat b w tail) s5 st.data)
    (hrun : runF level b w rounds m0 s =
      (C6 (mu m0) (reg m0 .r8).toNat b w folded (tail, claim)).run s5) :
    Eventually (step1 Host.exe) (Goal a s level b w rounds m0) st := by
  have g := c.geo
  have hfo : 2 ^ mu m0 + level.fold ≤ 64 := c.fold
  have hal : w.alphas.size + mu m0 ≤ 30 := c.alphas
  have hmu : mu m0 < 64 := c.mu64
  have hc := hgb.core
  have hf := hc.fr
  have h2mu : 2 ^ mu m0 ≤ 64 := by omega
  have htl : tail.toList.length = mu m0 := by rw [Array.length_toList, htn]
  -- `b33`: `multilinear_eval_by(2 ^ μ, folded, 2 ^ μ, tail, μ)`.
  let env1 := argEnv m0 st.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b34Offset)).toBitVec
  have hwf1 : env1.WF := c.wf0 hf.frame.kept
  refine exec_at (infix_of b33_in_code (by simp [b33]) hp) exit_b33 hwf1 (fun _ _ ↦ rfl) hpc
    (match_retS hf) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, hrdi1, hrsi1, hrdx1, hrcx1, hr81, hkr1⟩ := ok_b33
  have e1 : ∀ {r : Reg64} {v : Sym}, (after b33 retS).reg r = some v →
      reg st1.data r = v.eval env1 := fun h ↦ hm1.regs _ _ h
  obtain ⟨hf1, hs1⟩ := c.blk hf hwf1 hm1 hmid1 (hi := 40) (by omega) (hW1.le (by decide))
  have hk1 : KeepF m0 st.data.dmem st1.data.dmem 2624 0 :=
    keepF_blk hwf1 hm1 (writesIn_of_mid hmid1) hW1 (by decide)
  have hk1r : ∀ r ∈ six, reg st1.data r = reg st.data r := fun r hr ↦ e1 (hkr1 r hr)
  have hdi1 : reg st1.data .rdi = reg st.data .r14 := e1 hrdi1
  have hdx1 : reg st1.data .rdx = reg st.data .r14 := e1 hrdx1
  have hsi1 : reg st1.data .rsi = loc m0 1600 := (e1 hrsi1).trans (eval_ptr0A 1600)
  have hcx1 : reg st1.data .rcx = loc m0 1120 := (e1 hrcx1).trans (eval_ptr0A 1120)
  have h81 : reg st1.data .r8 = reg m0 .rcx :=
    (e1 hr81).trans (load_ofMachine (r := 0) (o := 40) rfl hc.w40)
  have hfold1 := hk1.ews (xs := folded.toList) (by omega)
    (by rw [Array.length_toList, hc.size]; omega)
    (by rw [Array.length_toList, hc.size]; omega) hc.fold
  have htail1 := hk1.ews (xs := tail.toList) (by omega) (by omega) (by omega) hgb.tail
  have hat1 := c.at_call (o := 32) (by omega) hf1
  have hle1 : 2672 - 32 + mleStack ≤ finalLevelStack := by decide
  have hdxn : (reg st1.data .rdx).toNat = 2 ^ mu m0 := by rw [hdx1]; exact hc.r14
  have hpre1 : MleOfMultilinearEvalPre st1.data := by
    refine ⟨(c.sctx (by decide)).stackOk hat1 hle1, hdi1.trans hdx1.symm, ?_, ?_, ?_⟩
    · rw [h81]; exact hmu
    · show SliceOk st1.data (reg st1.data .rsi) (reg st1.data .rdx) mleStack
      rw [hsi1]
      exact c.sliceLoc (o := 32) (by omega) hf1 hle1 (by omega) (by rw [hdxn]; omega)
    · show SliceOk st1.data (reg st1.data .rcx) (reg st1.data .r8) mleStack
      rw [hcx1]
      exact c.sliceLoc (o := 32) (by omega) hf1 hle1 (by omega) (by rw [h81]; show 1120 + 16 * mu m0 ≤ 2672; omega)
  refine call_then hpc1 hmle hpre1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hret2, hch2, hsv2⟩ := hq2
  rw [hsi1, hcx1, slice_take hfold1 (by rw [hdxn, hc.size]; omega), hdxn,
    slice_eq (by rw [h81]; exact htl.symm) htail1] at hret2
  have hch2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 2624) 0 q ∨
        NativeRustcVm.InRange (stackBelow st1.data mleStack) mleStack q) :=
    NativeRustcVm.SameOutside.mono hch2 fun q hq ↦ by
      rcases hq with hq | hq
      · exact absurd hq inRange_zero
      · exact Or.inr hq
  obtain ⟨hf2, hkeep2⟩ := c.call (o := 32) (by omega) hf1 hle1 hsv2 hrsp2
    (R := NativeRustcVm.InRange (loc m0 2624) 0) (lo := 2624) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inr hq) hch2'
  have hk2 : KeepF m0 st1.data.dmem st2.data.dmem 2624 0 := hkeep2
  have hts2 := c.ts_call (o := 32) (by omega) hf1 hle1 hsv2
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch2'
    (c.ts_frame (hi := 40) (by omega) (hm1.kept hwf1) hs1 hgb.ts)
  have hpc2' : st2.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b34Offset) := hpc2
  -- `b34`: `EW::mul(weight, mle)`.
  let env3 := argEnv m0 st2.data 2672 8 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b35Offset)).toBitVec
  have hwf3 : env3.WF := c.wf0 hf2.frame.kept
  refine exec_at (infix_of b34_in_code (by simp [b34]) hp) exit_b34 hwf3 (fun _ _ ↦ rfl) hpc2'
    (match_retS hf2) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hW3, hrdi3, hrsi3, hrdx3, hrcx3, hkr3⟩ := ok_b34
  have e3 : ∀ {r : Reg64} {v : Sym}, (after b34 retS).reg r = some v →
      reg st3.data r = v.eval env3 := fun h ↦ hm3.regs _ _ h
  obtain ⟨hf3, hs3⟩ := c.blk hf2 hwf3 hm3 hmid3 (hi := 40) (by omega) (hW3.le (by decide))
  have hk3 : KeepF m0 st2.data.dmem st3.data.dmem 2624 0 :=
    keepF_blk hwf3 hm3 (writesIn_of_mid hmid3) hW3 (by decide)
  set wt := finalWeight (reg m0 .r8).toNat b w tail with hwt
  set ml := multilinearEval (folded.extract 0 (2 ^ mu m0)) tail with hml
  have hargs : (⟨.ofBitVec (reg st3.data .rdi), .ofBitVec (reg st3.data .rsi)⟩ : EW) = wt ∧
      (⟨.ofBitVec (reg st3.data .rdx), .ofBitVec (reg st3.data .rcx)⟩ : EW) = ml := by
    refine ⟨?_, ?_⟩
    · rw [e3 hrdi3, e3 hrsi3]
      show (⟨.ofBitVec (reg st2.data .r15), .ofBitVec (reg st2.data .rbp)⟩ : EW) = _
      have hr15 : reg st2.data .r15 = reg st.data .r15 :=
        (hsv2.1 .r15 rfl).trans (hk1r .r15 (by simp [six]))
      have hrbp : reg st2.data .rbp = reg st.data .rbp :=
        (hsv2.1 .rbp rfl).trans (hk1r .rbp (by simp [six]))
      rw [hr15, hrbp, hgb.r15, hgb.rbp]
    · rw [e3 hrdx3, e3 hrcx3]
      exact hret2
  have hat3 := c.at_call (o := 32) (by omega) hf3
  have hle3 : 2672 - 32 + ewMulStack ≤ finalLevelStack := by decide
  refine call_then hpc3 hmul ((c.sctx (by decide)).stackOk hat3 hle3) fun st4 hpc4 hrsp4 hq4 ↦ ?_
  obtain ⟨hax4, hdx4, hch4, hsv4⟩ := hq4
  rw [hargs.1, hargs.2] at hax4 hdx4
  have hch4' : NativeRustcVm.SameOutside st3.data.dmem st4.data.dmem (fun q ↦
      NativeRustcVm.InRange (loc m0 2624) 0 q ∨
        NativeRustcVm.InRange (stackBelow st3.data ewMulStack) ewMulStack q) :=
    NativeRustcVm.SameOutside.mono hch4 fun q hq ↦ Or.inr hq
  obtain ⟨hf4, hkeep4⟩ := c.call (o := 32) (by omega) hf3 hle3 hsv4 hrsp4
    (R := NativeRustcVm.InRange (loc m0 2624) 0) (lo := 2624) (n := 0) (by omega) (by omega)
    (fun q hq ↦ Or.inr hq) hch4'
  have hk4 : KeepF m0 st3.data.dmem st4.data.dmem 2624 0 := hkeep4
  have hts4 := c.ts_call (o := 32) (by omega) hf3 hle3 hsv4
    (fun q hq ↦ c.loc_not_t (by omega) hq) hch4'
    (c.ts_frame (hi := 40) (by omega) (hm3.kept hwf3) hs3 hts2)
  have hpc4' : st4.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FinalLevel.b35Offset) := hpc4
  -- `b35`: the comparison.
  let env5 := argEnv m0 st4.data 2672 8 [] (fun _ ↦ 0) 0
  have hwf5 : env5.WF := c.wf0 hf4.frame.kept
  refine exec_at (infix_of b35_in_code (by simp [b35]) hp) exit_b35 hwf5 nofun hpc4'
    (match_retS hf4) fun st5 hm5 hpc5 ↦ ?_
  obtain ⟨hmid5, hmem5, hrax5, -⟩ := ok_b35
  have hd5 : st5.data.dmem = st4.data.dmem := hm5.dmem_eq hwf5 hmem5
  have hf5 : Fr m0 40 st5.data :=
    ⟨Frame.of_blockA hf4.frame hwf5 hm5 hmid5 slots_le, by rw [Sm, hd5]; exact hf4.same⟩
  have hk : ∀ {j : Nat} {u : UInt64}, 40 ≤ j → j + 8 ≤ 2624 →
      NativeRustcVm.WordAt st.data.dmem (loc m0 j) u →
      NativeRustcVm.WordAt st4.data.dmem (loc m0 j) u := fun h1 h2 hw ↦
    hk4.word (by omega) (by omega) (by omega) (hk3.word (by omega) (by omega) (by omega)
      (hk2.word (by omega) (by omega) (by omega) (hk1.word (by omega) (by omega) (by omega) hw)))
  have l88 : env5.load 0 88 8 = claim.c0.toBitVec := load_ofMachine (r := 0) (o := 88) rfl
    (hk (by omega) (by omega) hgb.w88)
  have l96 : env5.load 0 96 8 = claim.c1.toBitVec := load_ofMachine (r := 0) (o := 96) rfl
    (hk (by omega) (by omega) hgb.w96)
  have hcond : (EW.mul wt ml == claim) = ((EW.mul wt ml).c0.toBitVec == claim.c0.toBitVec &&
      (EW.mul wt ml).c1.toBitVec == claim.c1.toBitVec) := by
    rw [ew_beq, beq_toBitVec, beq_toBitVec]
  have hrun' : runF level b w rounds m0 s =
      if (EW.mul wt ml == claim) then some ((), s5) else none := by
    rw [hrun, C6, run_require]
    rfl
  have hal5 : (reg st5.data .rax).toNat % 256 =
      (okWord (runF level b w rounds m0 s).isSome).toNat := by
    rw [show reg st5.data .rax = _ from hm5.regs .rax _ hrax5]
    show (BinOp.apply .merge .W8 _ (vEnd.eval env5)).toNat % 256 = _
    rw [vEnd_eval env5 hax4 hdx4 l88 l96, al_merge, hrun', ← hcond]
    cases EW.mul wt ml == claim <;> rfl
  simp only [PcOk] at hpc5
  refine post37 hp c hf5 (hpc5.trans (l6 hp)) hal5 ?_
  rw [hrun']
  intro x s' h
  split at h
  · cases h; rw [hd5]; exact hts4
  · cases h

end

end NativeRustcVmX64.Whir.Levels.FL
