module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Code.Vm.VerifyGkrGrandProducts.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Head
public import NativeRustcVmArm.Bus.VerifyBusBalance.ClaimsA
public import NativeRustcVmArm.Tables.Frame

/-!
# `verify_bus_balance`'s grind, challenges and GKR walk

From `b10` (`k + NativeRustcVmArm.Vm.VerifyBusBalance.b10Offset`), the layouts built: `b10` calls `bit_length` of the push side's mask;
`b11` grinds; `b12` checks it; `b13` samples the `16` weights; `b14` squeezes `β`; `b15` keeps
`β`, empties the `GkrStateW` and calls `verify_gkr_grand_products`; `b16`, `b17` check its count
root (`grind_spec`, then `AtClaims`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeRustcVm.Bus
open NativeRustcVm.Layout NativeRustcVmArm.Bus.Gkr

public section

/-- The grind's bit count as `b11` computes it from the bit length `d`. -/
theorem grind_bits {x : BitVec 64} {d : Nat} (hx : x.toNat = d) (hd : d < 64) :
    (if CmpOp.apply .ult .W32 x (BitVec.ofNat 64 3) = true then BitVec.ofNat 64 0
      else BinOp.apply .sub .W32 x (BitVec.ofNat 64 3)).toNat % 2 ^ 32 = d - 3 := by
  have h32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  have hl : (low .W32 x).toNat = d := by
    rw [Sym.low_W32, BitVec.toNat_setWidth, hx, h32]; omega
  have h3 : (low .W32 (BitVec.ofNat 64 3)).toNat = 3 := by
    rw [Sym.low_W32, BitVec.toNat_setWidth]; rfl
  have hc : CmpOp.apply .ult .W32 x (BitVec.ofNat 64 3) = decide (d < 3) := by
    show decide ((low .W32 x).toNat < (low .W32 (BitVec.ofNat 64 3)).toNat) = _
    rw [hl, h3]
  rw [hc]
  by_cases h : d < 3
  · simp only [h, decide_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, BinOp.apply, Sym.ext_W32,
      BitVec.toNat_setWidth, BitVec.toNat_sub, hl, h3, h32]
    omega

/-- The count root's test (`b17`): its limbs' `or` is `0` when it is `0`. -/
theorem orr_eq0 (c : EW) :
    CmpOp.apply .eq .W64 (BinOp.apply .orr .W64 c.c1.toBitVec c.c0.toBitVec)
      (BitVec.ofNat 64 0) = (c == 0) := by
  obtain ⟨x, y⟩ := c
  simp only [CmpOp.apply, BinOp.apply, Sym.low_W64, Sym.ext_W64]
  rw [show ((⟨x, y⟩ : EW) == 0) = (x == 0 && y == 0) from rfl]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Bool.and_eq_true]
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.or_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨UInt64.toBitVec_inj.mp h2, UInt64.toBitVec_inj.mp h1⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

end

public section
variable [Labels] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData}

/-- **The `TState` through a call** writing below the frame only. -/
theorem ts_stack (h : VerifyBusBalancePre a s0 L m0) {m d : MachineData}
    (hfr : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) m) {N' : Nat}
    (hle : 5488 + N' ≤ verifyBusBalanceStack) (hk : Kept m.dmem d.dmem)
    (hs : SameOutside m.dmem d.dmem (InRange (stackBelow m N') N'))
    {s : TState} (hts : TStateAt m.dmem m0.regs.X0.toBitVec a s) :
    TStateAt d.dmem m0.regs.X0.toBitVec a s :=
  hts.frame hk (fun _ hq ↦ have c := callee_apart h hfr hle hq; ⟨fun h' ↦ c.2.1 (.inl h'), c.1⟩)
    hs

/-- **A call's changes keep the intervals**: below the frame and the `TState`. -/
theorem keepIv_callTS (h : VerifyBusBalancePre a s0 L m0) {m d : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 5488) {N' : Nat} (hle : 5488 + N' ≤ verifyBusBalanceStack)
    (hs : SameOutside m.dmem d.dmem (fun q ↦ InRange (stackBelow m N') N' q ∨
      InRange m0.regs.X0.toBitVec tstateBytes q))
    {ivs : List (Nat × Nat)} (hlt : ivs.all (fun p ↦ decide (p.2 ≤ 5488)) = true) :
    KeepIv ivs m0 m.dmem d.dmem :=
  keepIv_call (pre_stack h) hsp hle hs hlt fun _ hj ↦ loc_not_ts h (inIv_lt hlt hj)

end

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- **The grind, the challenges, the GKR walk** (`b10` to `b17`): the state at `b18`, or the
failure. -/
theorem grind_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hbit : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hgkr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s) (VerifyGkrPost a s))
    (hcl : ∀ w pt tv beta s m, AtClaims a s0 L m0 w pt tv beta s m →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b18Offset)⟩)
    {mG : MachineData} (A : AtGrind a s0 L m0 mG) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨mG, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b10Offset)⟩ := by
  have hS := pre_stack h
  have hN : verifyBusBalanceStack ≤ m0.regs.SP.toNat := hS.2.1
  have c := ctx h
  have hNv := N_eq
  have hdep := A.dep
  have hrun := vbb_run L s0
  simp only [hdep, ↓reduceIte, busGrindingBits_eq] at hrun
  -- `b10`: `bit_length` of the push side's mask.
  refine Fr.runBlock hS N_ge rfl A.fr (b10_in_code.trans hp.1 (by simp [b10])) run_b10 rfl rfl
    (by decide) (by decide) fun st1 hfr1 hd1 hm1 hpc1 ↦ ?_
  have R1 : RegsEq csK mG st1.data := regsEq_block hm1 (by decide)
  have e26 : (mG.regs.getXReg .X26).toBitVec.toNat = (pushL L).depth := A.x26
  have hx1 : st1.data.regs.X0.toNat = 2 ^ (pushL L).depth - 1 := by
    show (st1.data.regs.getXReg .X0).toBitVec.toNat = _
    rw [hm1.regs .X0 _ rfl]
    have := mask_toNat (x := (mG.regs.getXReg .X26).toBitVec) (by rw [e26]; exact hdep)
    rw [e26] at this
    exact this
  simp only [PcOk] at hpc1
  refine Fr.callSpec hfr1 hN le_len keep_callee slots_le (outs_not_frame h) hbit hpc1 trivial
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ .inl h, hq.2.2⟩)
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  have hx2 : m2.regs.X0.toNat = (pushL L).depth := by
    rw [hq2.1, hx1, bitLength_mask]
  have ts2 := ts_stack h hfr1 le_len hq2.2.2.2.2 hq2.2.1 (by rw [hd1]; exact A.ts)
  have kL2 : KeepIv [(160, 2824)] m0 st1.data.dmem m2.dmem :=
    keepIv_call hS hfr1.sp le_len (X := fun _ ↦ False)
      (NativeRustcVm.SameOutside.mono hq2.2.1 fun _ h ↦ .inl h) (by decide) fun _ _ h ↦ h
  have R2 : RegsEq csK st1.data m2 := regsEq_call hcs2 (by decide)
  -- `b11`: the grind of `depth - 3` bits.
  refine Fr.runBlock hS N_ge rfl hfr2 (b11_in_code.trans hp.1 (by simp [b11])) run_b11 rfl rfl
    (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have R3 : RegsEq csK m2 st3.data := regsEq_block hm3 (by decide)
  have RA : RegsEq csK mG st3.data := (R1.trans R2).trans R3
  have g0 : st3.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm3 (r := .X0) (r' := .X25) rfl).trans ((R3 .X25 (by simp)).symm.trans
      ((RA .X25 (by simp)).trans A.x25))
  have g1 : grindBits st3.data = (pushL L).depth - 3 := by
    unfold grindBits
    rw [show st3.data.regs.X1.toNat = (st3.data.regs.getXReg .X1).toBitVec.toNat from rfl,
      hm3.regs .X1 _ rfl]
    exact grind_bits (x := (m2.regs.getXReg .X0).toBitVec) hx2 hdep
  have hat3 := Fr.at_ c hfr3 (outs_not_rc h)
  simp only [PcOk] at hpc3
  refine Fr.callSpec hfr3 hN le_grind keep_callee slots_le (outs_not_frame h) (hgr a s0) hpc3
    ⟨hfr3.stackOk hS rfl le_grind, c.rcAt hat3 le_grind, by rw [g0, hd3]; exact ts2,
      by rw [g0]; exact c.tstateOk hat3 le_grind, by rw [g1]; omega⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [g0] at hq'
      exact hq'.elim (fun h' ↦ .inr (.inl h')) .inl, hq.2.2.2⟩)
    fun m4 hfr4 hq4 hcs4 ↦ ?_
  obtain ⟨hx4, hnext4, hs4, hsv4⟩ := hq4
  rw [g1] at hx4 hnext4
  rw [g0] at hnext4 hs4
  have kL4 : KeepIv [(160, 2824)] m0 st3.data.dmem m4.dmem :=
    keepIv_callTS h hfr3.sp le_grind
      (NativeRustcVm.SameOutside.mono hs4 fun _ hq ↦ hq.elim .inr .inl) (by decide)
  have R4 : RegsEq csK st3.data m4 := regsEq_call hcs4 (by decide)
  -- `b12`: the grind's result.
  refine Fr.runBlock hS N_ge rfl hfr4 (b12_in_code.trans hp.1 (by simp [b12])) run_b12 rfl rfl
    (by decide) (by decide) fun st5 hfr5 hd5 hm5 hpc5 ↦ ?_
  have hc5 : SBool.eval (Env.ofMachine m4 [(base m0 5488, 5488)])
      (.cmp .eq .W32 (.reg .X0) (.lit 0)) =
        !((grind ((pushL L).depth - 3)).run s0).isSome := by
    show CmpOp.eq.apply .W32 (m4.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
    rw [show m4.regs.getXReg .X0 = m4.regs.X0 from rfl, hx4, okW_eq0]
  cases hr1 : (grind ((pushL L).depth - 3)).run s0 with
  | none =>
    exact fail_cond hp h hpc5 (by rw [hc5, hr1]; rfl) hfr5 (by rw [hrun, hr1]; rfl)
  | some p1 =>
  obtain ⟨u, s1⟩ := p1
  rw [hr1, Option.bind_some] at hrun
  dsimp only at hrun
  have ts4 := hnext4 u s1 hr1
  have R5 : RegsEq csK m4 st5.data := regsEq_block hm5 (by decide)
  -- `b13`: the weights emptied; `sample_challenges` of the `16` weights.
  have hwf6 := Bus.wf_frame hS N_ge hfr5.kept
  refine at_pc (pass_cond hpc5 (by rw [hc5, hr1]; rfl)) (exec_then
    (b13_in_code.trans hp.1 (by simp [b13])) run_b13 hwf6 (Bus.match_frame hS N_ge rfl hfr5.sp)
    fun st6 hm6 hpc6 ↦ ?_)
  have hfr6 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st6.data :=
    Bus.Fr.block hfr5 hN N_ge hm6 hwf6 rfl (by decide) (by decide) slots_le
  have kL6 : KeepIv [(160, 2824)] m0 st5.data.dmem st6.data.dmem :=
    keepIv_block hm6 hwf6 (sizes := [5488]) rfl (by decide) (by decide)
  have ts6 := ts_block h hm6 hwf6 (by decide) (by rw [hd5]; exact ts4)
  have R6 : RegsEq csK st5.data st6.data := regsEq_block hm6 (by decide)
  have RB : RegsEq csK mG st6.data := (((RA.trans R4).trans R5)).trans R6
  have y0 : st6.data.regs.X0 = m0.regs.X0 :=
    (reg_of hm6 (r := .X0) (r' := .X25) rfl).trans ((R6 .X25 (by simp)).symm.trans
      ((RB .X25 (by simp)).trans A.x25))
  have y1 : st6.data.regs.X1.toBitVec = loc m0 2824 := reg_ptr (x := .X1) 2824 hm6 rfl
  have y2 : st6.data.regs.X2.toNat = 16 := by
    rw [show st6.data.regs.X2 = st6.data.regs.getXReg .X2 from rfl, ← UInt64.toNat_toBitVec,
      reg_lit hm6 (r := .X2) (n := 16) rfl]; rfl
  have hat6 := Fr.at_ c hfr6 (outs_not_rc h)
  simp only [PcOk] at hpc6
  refine Fr.callLocal (o := 2824) (n := 256)
    (X := fun q ↦ InRange (loc m0 2824) 256 q ∨ InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr6 hN le_samp keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h')) (hsc a s1) hpc6 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ by
      rw [y0, y1, y2] at hq'
      rcases hq' with hq' | hq' | hq'
      · exact .inr (.inl hq')
      · exact .inr (.inr hq')
      · exact .inl hq', hq.2.2⟩)
    fun m7 hfr7 hq7 hcs7 hs7 ↦ ?_
  · unfold SampleChallengesPre
    rw [y0, y1, y2]
    exact ⟨hfr6.stackOk hS rfl le_samp, c.rcAt hat6 le_samp, ts6, c.tstateOk hat6 le_samp,
      c.outOk hat6 le_samp (by omega)⟩
  obtain ⟨⟨w, s2, hr2, hw7, ts7⟩, -, -⟩ := hq7
  rw [y1] at hw7
  rw [y0] at ts7
  rw [y2] at hr2
  rw [hr2, Option.bind_some] at hrun
  dsimp only at hrun
  rw [show sampleChallenge.run s2 =
    some (s2.sponge.squeeze.1, { s2 with sponge := s2.sponge.squeeze.2 }) from rfl,
    Option.bind_some] at hrun
  dsimp only at hrun
  have kL7 : KeepIv [(160, 2824)] m0 st6.data.dmem m7.dmem :=
    keepIv_callT h hfr6.sp le_samp (by omega) hs7 (by decide) (by decide)
  have R7 : RegsEq csK st6.data m7 := regsEq_call hcs7 (by decide)
  -- `b14`: `β`, squeezed.
  refine Fr.runBlock hS N_ge rfl hfr7 (b14_in_code.trans hp.1 (by simp [b14])) run_b14 rfl rfl
    (by decide) (by decide) fun st8 hfr8 hd8 hm8 hpc8 ↦ ?_
  have R8 : RegsEq csK m7 st8.data := regsEq_block hm8 (by decide)
  have RC : RegsEq csK mG st8.data := (RB.trans R7).trans R8
  simp only [PcOk] at hpc8
  refine Tables.squeeze_call c hsq hfr8 (outs_not_rc h) le_sq keep_callee slots_le
    (outs_not_frame h) (fun q hq ↦ .inl hq) hpc8
    (by rw [show st8.data.regs.X0 = st8.data.regs.getXReg .X0 from rfl,
      reg_of hm8 (r := .X0) (r' := .X25) rfl, ← R8 .X25 (by simp), RC .X25 (by simp), A.x25])
    (by rw [hd8]; exact ts7) fun m9 hfr9 ts9 h90 h91 hcs9 hs9 ↦ ?_
  have hsl : spongeBytes ≤ tstateBytes := by decide
  have hsb : NativeRustcVm.NoWrap m0.regs.X0.toBitVec spongeBytes :=
    NativeRustcVm.NoWrap.mono (pre_ts h).footprint.1.2 hsl
  have kL9 : KeepIv [(160, 2824)] m0 st8.data.dmem m9.dmem :=
    keepIv_callTS h hfr8.sp le_sq (NativeRustcVm.SameOutside.mono hs9 fun _ hq ↦ hq.elim
      (fun h' ↦ .inr (NativeRustcVm.InRange.mono h' hsb (pre_ts h).footprint.1.2 (Nat.le_refl _)
        (by omega))) .inl) (by decide)
  have kW9 : KeepIv [(2824, 3080)] m0 st8.data.dmem m9.dmem :=
    keepIv_callTS h hfr8.sp le_sq (NativeRustcVm.SameOutside.mono hs9 fun _ hq ↦ hq.elim
      (fun h' ↦ .inr (NativeRustcVm.InRange.mono h' hsb (pre_ts h).footprint.1.2 (Nat.le_refl _)
        (by omega))) .inl) (by decide)
  have R9 : RegsEq csK st8.data m9 := regsEq_call hcs9 (by decide)
  have RD : RegsEq csK mG m9 := RC.trans R9
  -- `b15`: `β`'s limb `0` at `128`, the `GkrStateW` emptied; `verify_gkr_grand_products`.
  have hwf10 := Bus.wf_frame hS N_ge hfr9.kept
  refine exec_then (b15_in_code.trans hp.1 (by simp [b15])) run_b15 hwf10
    (Bus.match_frame hS N_ge rfl hfr9.sp) fun st10 hm10 hpc10 ↦ ?_
  have hfr10 : Fr m0 5488 verifyBusBalanceStack slots keep (outs m0) st10.data :=
    Bus.Fr.block hfr9 hN N_ge hm10 hwf10 rfl (by decide +kernel) (by decide) slots_le
  have kL10 : KeepIv [(160, 2824)] m0 m9.dmem st10.data.dmem :=
    keepIv_block hm10 hwf10 (sizes := [5488]) rfl (by decide) (by decide +kernel)
  have kW10 : KeepIv [(2824, 3080)] m0 m9.dmem st10.data.dmem :=
    keepIv_block hm10 hwf10 (sizes := [5488]) rfl (by decide) (by decide +kernel)
  have ts10 := ts_block h hm10 hwf10 (by decide +kernel) ts9
  have R10 : RegsEq csK m9 st10.data := regsEq_block hm10 (by decide)
  have w128 : NativeRustcVm.WordAt st10.data.dmem (loc m0 128) s2.sponge.squeeze.1.c0 :=
    wr_eval hm10 (o := 128) (by omega) (.reg .X0) (by decide +kernel) (by
      show (m9.regs.getXReg .X0).toBitVec = _
      rw [show m9.regs.getXReg .X0 = m9.regs.X0 from rfl, h90])
  have x22 : st10.data.regs.getXReg .X22 = s2.sponge.squeeze.1.c1 :=
    (reg_of hm10 (r := .X22) (r' := .X1) rfl).trans h91
  have x21 : (st10.data.regs.getXReg .X21).toBitVec = loc m0 3080 := reg_ptr 3080 hm10 rfl
  have z0 : st10.data.regs.X0.toBitVec = loc m0 4176 := reg_ptr (x := .X0) 4176 hm10 rfl
  have z1 : st10.data.regs.X1 = m0.regs.X0 :=
    (reg_of hm10 (r := .X1) (r' := .X25) rfl).trans ((RD .X25 (by simp)).trans A.x25)
  have z2 : st10.data.regs.X2.toNat = (pushL L).depth :=
    (congrArg UInt64.toNat (reg_of hm10 (r := .X2) (r' := .X26) rfl)).trans
      ((congrArg UInt64.toNat (RD .X26 (by simp))).trans A.x26)
  have z3 : st10.data.regs.X3.toBitVec = loc m0 3080 := reg_ptr (x := .X3) 3080 hm10 rfl
  have hgb : gkrStateBytes = 1064 := rfl
  have hat10 := Fr.at_ c hfr10 (outs_not_rc h)
  simp only [PcOk, NativeRustcVmArm.Vm.VerifyBusBalance.b15_length, NativeRustcVmArm.Vm.VerifyBusBalance.b15Length] at hpc10
  refine Fr.callLocal (o := 3080) (n := 1120)
    (X := fun q ↦ InRange (loc m0 3080) 1120 q ∨ InRange m0.regs.X0.toBitVec tstateBytes q)
    hfr10 hN le_gkr keep_callee (slots_lo (by omega)) (by omega) (outs_not_frame h)
    (fun q hq ↦ hq.elim .inr fun h' ↦ .inl (.inl h'))
    (hgkr a { s2 with sponge := s2.sponge.squeeze.2 }) hpc10 ?_
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q hq' ↦ by
      rw [z0, z1, z3] at hq'
      rcases hq' with hq' | hq' | hq' | hq'
      · exact .inr (.inl (loc_mono hS (by omega) (by omega) (by omega) hq'))
      · exact .inr (.inr hq')
      · exact .inr (.inl (loc_mono hS (by omega) (by omega) (by omega) hq'))
      · exact .inl hq', hq.2.2.2⟩)
    fun m11 hfr11 hq11 hcs11 hs11 ↦ ?_
  · unfold VerifyGkrPre GkrOk
    rw [z0, z1, z3]
    refine ⟨hfr10.stackOk hS rfl le_gkr, c.rcAt hat10 le_gkr, ts10, c.tstateOk hat10 le_gkr,
      by rw [z2]; unfold busPointCap; omega, c.outOk hat10 le_gkr (by omega),
      by rw [hgb]; exact c.outOk hat10 le_gkr (by omega), ?_⟩
    unfold Apart
    rw [loc_toNat hS (o := 4176) (by omega), loc_toNat hS (o := 3080) (by omega), hgb]
    omega
  dsimp only [VerifyGkrPost] at hq11
  rw [z0, z1, z2, z3] at hq11
  obtain ⟨hopt11, hsome11, -, -⟩ := hq11
  have kL11 : KeepIv [(160, 2824)] m0 st10.data.dmem m11.dmem :=
    keepIv_callT h hfr10.sp le_gkr (by omega) hs11 (by decide) (by decide)
  have kW11 : KeepIv [(128, 136), (2824, 3080)] m0 st10.data.dmem m11.dmem :=
    keepIv_callT h hfr10.sp le_gkr (by omega) hs11 (by decide) (by decide)
  have R11 : RegsEq csK st10.data m11 := regsEq_call hcs11 (by decide)
  -- `b16`: the count root's tag.
  refine Fr.runBlock hS N_ge rfl hfr11 (b16_in_code.trans hp.1 (by simp [b16])) run_b16 rfl rfl
    (by decide) (by decide) fun st12 hfr12 hd12 hm12 hpc12 ↦ ?_
  cases hr4 : (verifyGkrGrandProducts (pushL L).depth).run
      { s2 with sponge := s2.sponge.squeeze.2 } with
  | none =>
    rw [hr4] at hopt11
    refine fail_cond hp h hpc12 ?_ hfr12 (by rw [hrun, hr4]; rfl)
    show CmpOp.apply .eq .W64 ((Env.ofMachine m11 [(base m0 5488, 5488)]).load 0 4176 8)
      (BitVec.ofNat 64 0) = true
    rw [Transcript.load_ofMachine rfl (show NativeRustcVm.WordAt m11.dmem (loc m0 4176) 0
      from hopt11)]
    rfl
  | some p4 =>
  obtain ⟨⟨cr, pt, tv⟩, s4⟩ := p4
  rw [hr4] at hopt11
  rw [hr4, Option.bind_some] at hrun
  dsimp only at hrun
  obtain ⟨ts11, hgs11⟩ := hsome11 cr pt tv s4 hr4
  obtain ⟨o11a, o11b⟩ := hopt11
  obtain ⟨e11a, e11b⟩ := NativeRustcVm.ewAt_iff.mp o11b
  have hc12 : SBool.eval (Env.ofMachine m11 [(base m0 5488, 5488)])
      (.cmp .eq .W64 (.load 0 4176 8) (.lit 0)) = false := by
    show CmpOp.apply .eq .W64 ((Env.ofMachine m11 [(base m0 5488, 5488)]).load 0 4176 8)
      (BitVec.ofNat 64 0) = false
    rw [Transcript.load_ofMachine rfl o11a]
    rfl
  -- `b17`: the count root not `0`.
  refine at_pc (pass_cond hpc12 hc12) (Fr.runBlock hS N_ge rfl hfr12
    (b17_in_code.trans hp.1 (by simp [b17])) run_b17 rfl rfl (by decide) (by decide)
    fun st13 hfr13 hd13 hm13 hpc13 ↦ ?_)
  have hc13 : SBool.eval (Env.ofMachine st12.data [(base m0 5488, 5488)])
      (.cmp .eq .W64 (.bin .orr .W64 (.load 0 4192 8) (.load 0 4184 8)) (.lit 0)) = (cr == 0) := by
    show CmpOp.apply .eq .W64 (BinOp.apply .orr .W64
      ((Env.ofMachine st12.data [(base m0 5488, 5488)]).load 0 4192 8)
      ((Env.ofMachine st12.data [(base m0 5488, 5488)]).load 0 4184 8)) (BitVec.ofNat 64 0) = _
    have f1 : NativeRustcVm.WordAt st12.data.dmem (off (base m0 5488) 4192) cr.c1 := by
      rw [hd12]; simpa only [off, NativeRustcVm.addr_add_add] using e11b
    have f0 : NativeRustcVm.WordAt st12.data.dmem (off (base m0 5488) 4184) cr.c0 := by
      rw [hd12]; simpa only [off, NativeRustcVm.addr_add_add] using e11a
    rw [Transcript.load_ofMachine rfl f1, Transcript.load_ofMachine rfl f0, orr_eq0]
  by_cases hz : (cr == 0) = true
  · refine fail_cond hp h hpc13 (by rw [hc13, hz]) hfr13 ?_
    rw [hrun]
    have : (require (cr != 0)).run s4 = none := by
      unfold require
      rw [show (cr != 0) = false by simp [bne, hz]]
      rfl
    rw [this]
    rfl
  have hreq : (require (cr != 0)).run s4 = some ((), s4) := by
    unfold require
    rw [show (cr != 0) = true by simp [bne, hz]]
    rfl
  rw [hreq, Option.bind_some] at hrun
  dsimp only at hrun
  refine at_pc (pass_cond hpc13 (by rw [hc13]; simpa using hz)) (hcl w pt tv
    s2.sponge.squeeze.1 s4 st13.data ?_)
  -- The state at `b18`.
  have R12 : RegsEq csK m11 st12.data := regsEq_block hm12 (by decide)
  have R13 : RegsEq csK st12.data st13.data := regsEq_block hm13 (by decide)
  have RE : RegsEq csK mG st13.data := ((((RD.trans R10).trans R11).trans R12).trans R13)
  have kL : KeepIv [(160, 2824)] m0 mG.dmem st13.data.dmem :=
    ((((((((((((KeepIv.rfl' hd1).trans kL2).trans (KeepIv.rfl' hd3)).trans kL4).trans
      (KeepIv.rfl' hd5)).trans kL6).trans kL7).trans (KeepIv.rfl' hd8)).trans kL9).trans
      kL10).trans kL11).trans (KeepIv.rfl' hd12)).trans (KeepIv.rfl' hd13)
  have kW : KeepIv [(2824, 3080)] m0 m7.dmem st13.data.dmem :=
    (((((KeepIv.rfl' hd8).trans kW9).trans kW10).trans (kW11.mono (ivSub (by decide)))).trans
      (KeepIv.rfl' hd12)).trans (KeepIv.rfl' hd13)
  have k128 : KeepIv [(128, 136)] m0 st10.data.dmem st13.data.dmem :=
    ((kW11.mono (ivSub (by decide))).trans (KeepIv.rfl' hd12)).trans (KeepIv.rfl' hd13)
  have hw13 : NativeRustcVm.EWsAt st13.data.dmem (loc m0 2824) w.toList :=
    NativeRustcVm.Tables.EWsAt.of_same hw7 (kW.sameIn (lo := 2824) (hi := 3080) (by simp)
      (o := 2824) (n := 256) (by omega) (by omega))
      (by rw [Array.length_toList, sampleChallenges_size hr2])
  have hx21 : (st13.data.regs.getXReg .X21).toBitVec = loc m0 3080 := by
    rw [reg_of hm13 (r := .X21) (r' := .X21) rfl, reg_of hm12 (r := .X21) (r' := .X21) rfl,
      hcs11 .X21 rfl]
    exact x21
  have hx22 : st13.data.regs.getXReg .X22 = s2.sponge.squeeze.1.c1 := by
    rw [reg_of hm13 (r := .X22) (r' := .X22) rfl, reg_of hm12 (r := .X22) (r' := .X22) rfl,
      hcs11 .X22 rfl]
    exact x22
  exact ⟨hfr13, hrun,
    ⟨kL.blw (lo := 160) (hi := 2824) (by simp) (by omega) (by omega) A.push,
      kL.blw (lo := 160) (hi := 2824) (by simp) (by omega) (by omega) A.pull,
      kL.blw (lo := 160) (hi := 2824) (by simp) (by omega) (by omega) A.count, hw13,
      sampleChallenges_size hr2, by rw [hd13, hd12]; exact hgs11,
      k128.word (lo := 128) (hi := 136) (by simp) (by omega) (by omega) w128⟩,
    (RE .X19 (by simp)).trans A.x19, (RE .X20 (by simp)).trans A.x20, hx21, hx22,
    (RE .X23 (by simp)).trans A.x23, (RE .X24 (by simp)).trans A.x24,
    (RE .X25 (by simp)).trans A.x25, by rw [RE .X27 (by simp)]; exact A.x27,
    (RE .X28 (by simp)).trans A.x28, by rw [RE .X29 (by simp)]; exact A.x29,
    by rw [hd13, hd12]; exact ts11⟩

end

end NativeRustcVmArm.Bus.VerifyBusBalance
