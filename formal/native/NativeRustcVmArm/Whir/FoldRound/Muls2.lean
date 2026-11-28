module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.FoldRound.Muls

/-!
# `fold_round`: the six products, run

`muls`: from `b12` (`AtB12`) through the six calls to `EW::mul` to `b18` (`AtB18`).
-/

namespace NativeRustcVmArm.Whir.FoldRound

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.FoldRound

public section

variable [Host] {a : DecArea} {s0 : TState} {w : WhirStateW} {m0 : MachineData} {k : Nat}

/-- What the tail keeps, across a call to `EW::mul`. -/
theorem tb_call (h : FoldRoundPre a s0 w m0) {s : TState} {st m2 : MachineData}
    (hb : Tb a w m0 s st) (hf2 : FFr m0 m2)
    (hcs : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.regs.getXReg r)
    (hs : SameOutside st.dmem m2.dmem (InRange (stackBelow st ewMulStack) ewMulStack))
    (hk : Kept st.dmem m2.dmem) : Tb a w m0 s m2 :=
  ⟨hf2, (hcs .X19 rfl).trans hb.x19, (hcs .X20 rfl).trans hb.x20,
    ws_keep h hb.ws hs fun _ hq ↦ .inl (stack_sub h hb.fr mul_le hq),
    ts_stack h hb.fr mul_le hb.ts hk hs⟩

/-- The value of a register a block computes as the `xor` of two words. -/
theorem xor_reg {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {x y : Sym} (hr : S.reg r = some (.bin .eor .W64 x y)) {u v : UInt64}
    (hx : x.eval env = u.toBitVec) (hy : y.eval env = v.toBitVec) :
    m.regs.getXReg r = u ^^^ v := by
  refine reg_of hm hr ?_
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hx, hy, UInt64.toBitVec_xor]

theorem reg_eval {env : Env} {r : XReg} {u : UInt64} (h : env.regs r = u.toBitVec) :
    (Sym.reg r).eval env = u.toBitVec := h

/-- **The six products.** -/
theorem muls (hp : Placed code k) (h : FoldRoundPre a s0 w m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {s5 : TState} {u0 v c0 c1 : EW} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b12Offset))
    (hb : AtB12 a s0 w m0 s5 u0 v c0 c1 st.data) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRound.b18Offset) → AtB18 a s0 w m0 s5 u0 v c0 c1 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  -- `b12`: `P1`
  have hwf := state_wf h hb.base.fr
  have htb : Tb a w m0 (sq (sq s5).2).2 st.data :=
    ⟨hb.base.fr, hb.base.x19, hb.base.x20, hb.base.ws, hb.ts⟩
  have hm := state_match h htb
  refine exec_at (inf hp b12_in_code (by simp [b12])) run_b12 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show k + NativeRustcVmArm.Vm.FoldRound.b12Offset + b12.length = k + NativeRustcVmArm.Vm.FoldRound.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FoldRound.b12_next]] at hpc1
  have hf1 : FFr m0 st1.data :=
    Fr.ofBlock hb.base.fr hm hm1 hwf rfl rfl rfl (fun _ h ↦ by cases h)
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 : ∀ r, calleeSaved r = true → r ≠ .X20 → r ≠ .X21 → r ≠ .X23 →
      st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr a b c ↦
    reg_of hm1 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have htb1 : Tb a w m0 (sq (sq s5).2).2 st1.data :=
    ⟨hf1, (hk1 .X19 rfl (by decide) (by decide) (by decide)).trans hb.base.x19, by
      apply UInt64.toBitVec_inj.mp
      have := reg_val hm1 (r := .X20) rfl
      simp [Sym.eval] at this
      exact this, by rw [hd1]; exact hb.base.ws, by rw [hd1]; exact hb.ts⟩
  have hcl := claim_load (st := st.data) htb
  have e0 : st1.data.regs.X0 = (alA s5).c0 :=
    (reg_of hm1 (r := .X0) (v := .reg .X25) rfl rfl).trans hb.x25
  have e1 : st1.data.regs.X1 = (alA s5).c1 :=
    (reg_of hm1 (r := .X1) (v := .reg .X22) rfl rfl).trans hb.x22
  have e2 : st1.data.regs.X2 = w.claim.c0 ^^^ u0.c0 :=
    xor_reg hm1 (r := .X2) rfl hcl.1 (reg_eval (congrArg UInt64.toBitVec hb.x29))
  have e3 : st1.data.regs.X3 = w.claim.c1 ^^^ u0.c1 :=
    xor_reg hm1 (r := .X3) rfl hcl.2 (reg_eval (congrArg UInt64.toBitVec hb.x24))
  have e21 : st1.data.regs.X21 = (beA s5).c0 :=
    (reg_of hm1 (r := .X21) (v := .reg .X0) rfl rfl).trans hb.x0
  have e23 : st1.data.regs.X23 = (beA s5).c1 :=
    (reg_of hm1 (r := .X23) (v := .reg .X1) rfl rfl).trans hb.x1
  refine mul_call h hmul hf1 hpc1 fun m2 hf2 h0 h1 hcs2 hs2 hk2 ↦ ?_
  rw [e0, e1, e2, e3] at h0 h1
  have htb2 := tb_call h htb1 hf2 hcs2 hs2 hk2
  have hfw2 : FW m2.dmem m0 [(48, c0.c0), (72, c1.c1), (80, c1.c0)] :=
    fw_call h hf1 mul_le (NativeRustcVm.SameOutside.mono hs2 fun _ hq ↦ .inl hq) (by simp)
      (by rw [hd1]; exact hb.fw)
  -- callee-saved values at `m2`
  have k2 : ∀ r, calleeSaved r = true → r ≠ .X20 → r ≠ .X21 → r ≠ .X23 →
      m2.regs.getXReg r = st.data.regs.getXReg r := fun r hr a b c ↦
    (hcs2 r hr).trans (hk1 r hr a b c)
  have f21 : m2.regs.X21 = (beA s5).c0 := (hcs2 .X21 rfl).trans e21
  have f23 : m2.regs.X23 = (beA s5).c1 := (hcs2 .X23 rfl).trans e23
  have f25 : m2.regs.X25 = (alA s5).c0 :=
    (k2 .X25 rfl (by decide) (by decide) (by decide)).trans hb.x25
  have f22 : m2.regs.X22 = (alA s5).c1 :=
    (k2 .X22 rfl (by decide) (by decide) (by decide)).trans hb.x22
  -- `b13`: `P2`, `P1` saved
  refine mstep (st := ⟨m2, _⟩) hp h hmul b13_in_code (by simp [b13]) run_b13 rfl (by decide)
    (by decide) rfl rfl rfl htb2 fun st3 m3 hm3 hf3 htb3 h30 h31 hcs3 hs3 ↦ ?_
  have g0 : st3.data.regs.X0 = (alA s5).c0 := (reg_of hm3 (r := .X0) (v := .reg .X25) rfl rfl).trans f25
  have g1 : st3.data.regs.X1 = (alA s5).c1 := (reg_of hm3 (r := .X1) (v := .reg .X22) rfl rfl).trans f22
  have g2 : st3.data.regs.X2 = (alA s5).c0 := (reg_of hm3 (r := .X2) (v := .reg .X25) rfl rfl).trans f25
  have g3 : st3.data.regs.X3 = (alA s5).c1 := (reg_of hm3 (r := .X3) (v := .reg .X22) rfl rfl).trans f22
  rw [g0, g1, g2, g3] at h30 h31
  have k3 : ∀ r, calleeSaved r = true → m3.regs.getXReg r = m2.regs.getXReg r := fun r hr ↦
    (hcs3 r hr).trans (reg_of hm3 (v := .reg r) (by cases r <;> first | rfl | simp [calleeSaved] at hr) rfl)
  have hfw3 : FW m3.dmem m0 ([(48, c0.c0), (72, c1.c1), (80, c1.c0)] ++
      [(56, (p1 w s5 u0).c0), (64, (p1 w s5 u0).c1)]) := by
    refine FW.append (fw_through h hf2 hm3 hf3 hs3 (os := [48, 72, 80]) rfl (by decide) hfw2) (fun o x hp ↦ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fw_new h hm3 hf3 hs3 (o := 56) (by decide) (v := .reg .X0) (by decide)
        (x := (p1 w s5 u0).c0) (reg_eval (congrArg UInt64.toBitVec h0)) _ _ (by simp)
    · exact fw_new h hm3 hf3 hs3 (o := 64) (by decide) (v := .reg .X1) (by decide)
        (x := (p1 w s5 u0).c1) (reg_eval (congrArg UInt64.toBitVec h1)) _ _ (by simp)
  -- `b14`: `P3 = P2·v`
  refine mstep (st := ⟨m3, _⟩) hp h hmul b14_in_code (by simp [b14]) run_b14 rfl (by decide)
    (by decide) rfl rfl rfl htb3 fun st4 m4 hm4 hf4 htb4 h40 h41 hcs4 hs4 ↦ ?_
  have g40 : st4.data.regs.X0 = (EW.mul (alA s5) (alA s5)).c0 :=
    (reg_of hm4 (r := .X0) (v := .reg .X0) rfl rfl).trans h30
  have g41 : st4.data.regs.X1 = (EW.mul (alA s5) (alA s5)).c1 :=
    (reg_of hm4 (r := .X1) (v := .reg .X1) rfl rfl).trans h31
  have g42 : st4.data.regs.X2 = v.c0 := (reg_of hm4 (r := .X2) (v := .reg .X27) rfl rfl).trans
    ((k3 .X27 rfl).trans ((k2 .X27 rfl (by decide) (by decide) (by decide)).trans hb.x27))
  have g43 : st4.data.regs.X3 = v.c1 := (reg_of hm4 (r := .X3) (v := .reg .X28) rfl rfl).trans
    ((k3 .X28 rfl).trans ((k2 .X28 rfl (by decide) (by decide) (by decide)).trans hb.x28))
  rw [g40, g41, g42, g43] at h40 h41
  have k4 : ∀ r, calleeSaved r = true → m4.regs.getXReg r = m3.regs.getXReg r := fun r hr ↦
    (hcs4 r hr).trans (reg_of hm4 (v := .reg r) (by cases r <;> first | rfl | simp [calleeSaved] at hr) rfl)
  have hfw4 : FW m4.dmem m0 ([(48, c0.c0), (72, c1.c1), (80, c1.c0)] ++
      [(56, (p1 w s5 u0).c0), (64, (p1 w s5 u0).c1)]) :=
    fw_through h htb3.fr hm4 hf4 hs4 (os := [48, 72, 80, 56, 64]) rfl (by decide) hfw3
  -- `b15`: `P4 = β·c0`, `P3` saved
  refine mstep (st := ⟨m4, _⟩) hp h hmul b15_in_code (by simp [b15]) run_b15 rfl (by decide)
    (by decide) rfl rfl rfl htb4 fun st5 m5 hm5 hf5 htb5 h50 h51 hcs5 hs5 ↦ ?_
  have l48 : (frameEnv m0 m4).load 0 48 8 = c0.c0.toBitVec := fw_load rfl hfw4 (by simp)
  have b21 : m4.regs.X21 = (beA s5).c0 := (k4 .X21 rfl).trans ((k3 .X21 rfl).trans f21)
  have b23 : m4.regs.X23 = (beA s5).c1 := (k4 .X23 rfl).trans ((k3 .X23 rfl).trans f23)
  have g50 : st5.data.regs.X0 = (beA s5).c0 :=
    (reg_of hm5 (r := .X0) (v := .reg .X21) rfl rfl).trans b21
  have g51 : st5.data.regs.X1 = (beA s5).c1 :=
    (reg_of hm5 (r := .X1) (v := .reg .X23) rfl rfl).trans b23
  have g52 : st5.data.regs.X2 = c0.c0 := reg_of hm5 (r := .X2) (v := .load 0 48 8) rfl l48
  have g53 : st5.data.regs.X3 = c0.c1 := (reg_of hm5 (r := .X3) (v := .reg .X26) rfl rfl).trans
    ((k4 .X26 rfl).trans ((k3 .X26 rfl).trans
      ((k2 .X26 rfl (by decide) (by decide) (by decide)).trans hb.x26)))
  have g527 : st5.data.regs.X27 = c0.c0 := reg_of hm5 (r := .X27) (v := .load 0 48 8) rfl l48
  rw [g50, g51, g52, g53] at h50 h51
  have k5 : ∀ r, calleeSaved r = true → r ≠ .X27 → m5.regs.getXReg r = m4.regs.getXReg r :=
    fun r hr h27 ↦ (hcs5 r hr).trans (reg_of hm5 (v := .reg r)
      (by cases r <;> first | rfl | contradiction) rfl)
  have hfw5 : FW m5.dmem m0 (([(48, c0.c0), (72, c1.c1), (80, c1.c0)] ++
      [(56, (p1 w s5 u0).c0), (64, (p1 w s5 u0).c1)]) ++
      [(32, (p3 s5 v).c0), (40, (p3 s5 v).c1)]) := by
    refine FW.append (fw_through h htb4.fr hm5 hf5 hs5 (os := [48, 72, 80, 56, 64]) rfl (by decide)
      hfw4) (fun o x hp ↦ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fw_new h hm5 hf5 hs5 (o := 32) (by decide) (v := .reg .X0) (by decide)
        (x := (p3 s5 v).c0) (reg_eval (congrArg UInt64.toBitVec h40)) _ _ (by simp)
    · exact fw_new h hm5 hf5 hs5 (o := 40) (by decide) (v := .reg .X1) (by decide)
        (x := (p3 s5 v).c1) (reg_eval (congrArg UInt64.toBitVec h41)) _ _ (by simp)
  -- `b16`: `P5 = α·β`, `P4.c0` in X28, `P4.c1`, `β.c0`, `α.c0` saved
  refine mstep (st := ⟨m5, _⟩) hp h hmul b16_in_code (by simp [b16]) run_b16 rfl (by decide)
    (by decide) rfl rfl rfl htb5 fun st6 m6 hm6 hf6 htb6 h60 h61 hcs6 hs6 ↦ ?_
  have a25 : m5.regs.X25 = (alA s5).c0 :=
    (k5 .X25 rfl (by decide)).trans ((k4 .X25 rfl).trans ((k3 .X25 rfl).trans f25))
  have a22 : m5.regs.X22 = (alA s5).c1 :=
    (k5 .X22 rfl (by decide)).trans ((k4 .X22 rfl).trans ((k3 .X22 rfl).trans f22))
  have c21 : m5.regs.X21 = (beA s5).c0 := (k5 .X21 rfl (by decide)).trans b21
  have c23 : m5.regs.X23 = (beA s5).c1 := (k5 .X23 rfl (by decide)).trans b23
  have g60 : st6.data.regs.X0 = (alA s5).c0 :=
    (reg_of hm6 (r := .X0) (v := .reg .X25) rfl rfl).trans a25
  have g61 : st6.data.regs.X1 = (alA s5).c1 :=
    (reg_of hm6 (r := .X1) (v := .reg .X22) rfl rfl).trans a22
  have g62 : st6.data.regs.X2 = (beA s5).c0 :=
    (reg_of hm6 (r := .X2) (v := .reg .X21) rfl rfl).trans c21
  have g63 : st6.data.regs.X3 = (beA s5).c1 :=
    (reg_of hm6 (r := .X3) (v := .reg .X23) rfl rfl).trans c23
  have g628 : st6.data.regs.X28 = (p4 s5 c0).c0 :=
    (reg_of hm6 (r := .X28) (v := .reg .X0) rfl rfl).trans h50
  rw [g60, g61, g62, g63] at h60 h61
  have k6 : ∀ r, calleeSaved r = true → r ≠ .X28 → m6.regs.getXReg r = m5.regs.getXReg r :=
    fun r hr h28 ↦ (hcs6 r hr).trans (reg_of hm6 (v := .reg r)
      (by cases r <;> first | rfl | contradiction) rfl)
  have hfw6 : FW m6.dmem m0 ((([(48, c0.c0), (72, c1.c1), (80, c1.c0)] ++
      [(56, (p1 w s5 u0).c0), (64, (p1 w s5 u0).c1)]) ++
      [(32, (p3 s5 v).c0), (40, (p3 s5 v).c1)]) ++
      [(24, (p4 s5 c0).c1), (16, (beA s5).c0), (8, (alA s5).c0)]) := by
    refine FW.append (fw_through h htb5.fr hm6 hf6 hs6 (os := [48, 72, 80, 56, 64, 32, 40]) rfl
      (by decide) hfw5) (fun o x hp ↦ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fw_new h hm6 hf6 hs6 (o := 24) (by decide) (v := .reg .X1) (by decide)
        (x := (p4 s5 c0).c1) (reg_eval (congrArg UInt64.toBitVec h51)) _ _ (by simp)
    · exact fw_new h hm6 hf6 hs6 (o := 16) (by decide) (v := .reg .X21) (by decide)
        (x := (beA s5).c0) (reg_eval (congrArg UInt64.toBitVec c21)) _ _ (by simp)
    · exact fw_new h hm6 hf6 hs6 (o := 8) (by decide) (v := .reg .X25) (by decide)
        (x := (alA s5).c0) (reg_eval (congrArg UInt64.toBitVec a25)) _ _ (by simp)
  -- `b17`: `P6 = P5·(c1 + c0)`
  refine mstep (st := ⟨m6, _⟩) hp h hmul b17_in_code (by simp [b17]) run_b17 rfl (by decide)
    (by decide) rfl rfl rfl htb6 fun st7 m7 hm7 hf7 htb7 h70 h71 hcs7 hs7 ↦ ?_
  have l80 : (frameEnv m0 m6).load 0 80 8 = c1.c0.toBitVec := fw_load rfl hfw6 (by simp)
  have l72 : (frameEnv m0 m6).load 0 72 8 = c1.c1.toBitVec := fw_load rfl hfw6 (by simp)
  have d27 : m6.regs.X27 = c0.c0 := (k6 .X27 rfl (by decide)).trans
    ((hcs5 .X27 rfl).trans g527)
  have d26 : m6.regs.X26 = c0.c1 := (k6 .X26 rfl (by decide)).trans
    ((k5 .X26 rfl (by decide)).trans ((k4 .X26 rfl).trans ((k3 .X26 rfl).trans
      ((k2 .X26 rfl (by decide) (by decide) (by decide)).trans hb.x26))))
  have g70 : st7.data.regs.X0 = (EW.mul (alA s5) (beA s5)).c0 :=
    (reg_of hm7 (r := .X0) (v := .reg .X0) rfl rfl).trans h60
  have g71 : st7.data.regs.X1 = (EW.mul (alA s5) (beA s5)).c1 :=
    (reg_of hm7 (r := .X1) (v := .reg .X1) rfl rfl).trans h61
  have g72 : st7.data.regs.X2 = c1.c0 ^^^ c0.c0 :=
    xor_reg hm7 (r := .X2) rfl l80 (reg_eval (congrArg UInt64.toBitVec d27))
  have g73 : st7.data.regs.X3 = c1.c1 ^^^ c0.c1 :=
    xor_reg hm7 (r := .X3) rfl l72 (reg_eval (congrArg UInt64.toBitVec d26))
  rw [g70, g71, g72, g73] at h70 h71
  have k7 : ∀ r, calleeSaved r = true → m7.regs.getXReg r = m6.regs.getXReg r := fun r hr ↦
    (hcs7 r hr).trans (reg_of hm7 (v := .reg r) (by cases r <;> first | rfl | simp [calleeSaved] at hr) rfl)
  have hfw7 := fw_through h htb6.fr hm7 hf7 hs7 (os := [48, 72, 80, 56, 64, 32, 40, 24, 16, 8]) rfl
    (by decide) hfw6
  refine cont ⟨m7, _⟩ rfl {
    tb := htb7
    x0 := h70
    x1 := h71
    x28 := (k7 .X28 rfl).trans ((hcs6 .X28 rfl).trans g628)
    x29 := (k7 .X29 rfl).trans ((k6 .X29 rfl (by decide)).trans ((k5 .X29 rfl (by decide)).trans
      ((k4 .X29 rfl).trans ((k3 .X29 rfl).trans
        ((k2 .X29 rfl (by decide) (by decide) (by decide)).trans hb.x29)))))
    x24 := (k7 .X24 rfl).trans ((k6 .X24 rfl (by decide)).trans ((k5 .X24 rfl (by decide)).trans
      ((k4 .X24 rfl).trans ((k3 .X24 rfl).trans
        ((k2 .X24 rfl (by decide) (by decide) (by decide)).trans hb.x24)))))
    x22 := (k7 .X22 rfl).trans ((k6 .X22 rfl (by decide)).trans a22)
    x23 := (k7 .X23 rfl).trans ((k6 .X23 rfl (by decide)).trans c23)
    fw := FW.sub hfw7 (by simp)
    model := hb.model }

end

end NativeRustcVmArm.Whir.FoldRound
