module

public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontProj
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# `verify_layer`'s front: the prologue

`b0` saves the registers in the 2032-byte frame, zeroes the product and reads it
(`read_scalars(t, product, 47)`); `b1` returns `None` if that failed; `b2` stores the words the
body keeps in the frame and sets the projection's registers (`pro_run`, to `ProjI 0` and `FM`).
Blocks writing the frame only (`fb_blkW`, `frame_only`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

@[expose] public section

/-- **The front's memory** from the prologue to the first check: the frame's words
(`projWords`), the product, the `TState`. -/
structure FM [Labels] (m0 : MachineData) (a : DecArea) (s1 : TState) (p : Array EW)
    (d : DataMem) : Prop where
  fw : Bus.FrameWords d (base m0 2032) (projWords m0)
  prod : NativeRustcVm.EWsAt d (loc m0 152) p.toList
  psz : p.size = 47
  ts : TStateAt d (tA m0) a s1

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **`FM` kept** by changes below the frame. -/
theorem FM.bel (h : VerifyLayerPre a s c m0) {s1 : TState} {p : Array EW} {d d' : DataMem}
    (hf : FM m0 a s1 p d) (hk : Kept d d') (hs : SameOutside d d' (Bel m0)) :
    FM m0 a s1 p d' := by
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0
  exact ⟨FrameWords.of_same hf.fw (same_bel g hs (x := base m0 2032) (n := 2032)
      (by rw [g.bN]; omega) (by rw [g.bN]; omega))
      (fun p hp ↦ by have := projWords_le m0 p hp; omega),
    ewsAt_same hf.prod (loc_bel g hs (o := 152) (n := 752) (by omega))
      (by rw [Array.length_toList, hf.psz]),
    hf.psz, ts_bel h hk hs hf.ts⟩

/-- A block writing the frame only below its slots keeps the front's frame. -/
theorem fb_blkW (h : VerifyLayerPre a s c m0) {m m' : MachineData} {rs : List (BitVec 64 × Nat)}
    {S : SState} (hb : FB m0 m) (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 2032, 2032) :: rs)).WF) (hsp : S.sp = .ptr 0 0)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 1936) : FB m0 m' :=
  Bus.Fr.block hb (pre_stack h).2.1 N_ge hm hwf hsp
    (fun w hw ↦ ⟨(hmem w hw).1, by have := (hmem w hw).2; omega,
      fun p hp ↦ .inl (by have := (hmem w hw).2; have := slots_bound p hp; omega)⟩)
    (fun r hr ↦ by cases hr) slots_le

/-- A block writing the frame only changes the frame only. -/
theorem frame_only (h : VerifyLayerPre a s c m0) {m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 2032, 2032) :: rs)).WF)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 2032) :
    SameOutside m.dmem m'.dmem (InRange (base m0 2032) 2032) :=
  NativeRustcVm.SameOutside.mono (hm.sameOutside hwf) fun _ hq ↦
    Bus.Written.inRange (r := 0) rfl (Bus.frame_mapped (pre_stack h) N_ge).2 hmem hq

/-- The `TState` kept by a block writing the frame only. -/
theorem ts_frame (h : VerifyLayerPre a s c m0) {m m' : MachineData}
    {rs : List (BitVec 64 × Nat)} {S : SState}
    (hm : Match (Env.ofMachine m ((base m0 2032, 2032) :: rs)) S m')
    (hwf : (Env.ofMachine m ((base m0 2032, 2032) :: rs)).WF)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 2032) {s' : TState}
    (ht : TStateAt m.dmem (tA m0) a s') : TStateAt m'.dmem (tA m0) a s' :=
  ht.frame (hm.kept hwf) (fun _ hq ↦ Bus.Gkr.frame_not_tstate (ctx h) hq) (frame_only h hm hwf hmem)

omit [Labels] in
theorem packW_eq (m0 : MachineData) :
    (if CmpOp.apply .ult .W64 m0.regs.X1.toBitVec (BitVec.ofNat 64 4) = true then
      BitVec.ofNat 64 0 else BinOp.apply .sub .W64 m0.regs.X1.toBitVec (BitVec.ofNat 64 4)) =
      (packW m0).toBitVec := by
  rw [ult_apply, packW]
  have hu : (UInt64.ofNat (m0.regs.X1.toNat - 4)).toBitVec =
      BitVec.ofNat 64 (m0.regs.X1.toNat - 4) := rfl
  rw [hu]
  apply BitVec.eq_of_toNat_eq
  have hx : m0.regs.X1.toNat = m0.regs.X1.toBitVec.toNat := rfl
  have := m0.regs.X1.toBitVec.isLt
  split
  · rename_i hc
    simp only [decide_eq_true_eq, BitVec.toNat_ofNat] at hc ⊢
    omega
  · rename_i hc
    simp only [decide_eq_true_eq, BitVec.toNat_ofNat] at hc
    rw [sub_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
end


public section
variable [Labels] {env : Env}

theorem iteT {cnd : SBool} {A B : Sym} (h : cnd.eval env = true) :
    (Sym.ite cnd A B).eval env = A.eval env := by
  rw [ev_ite, h]; rfl

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The prologue**: the product read, the projection's head at coefficient `0`. -/
theorem pro_run (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hrs : ∀ s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (cont : ∀ (st : MachineState) (p : Array EW) (s1 : TState),
      (readScalars 47).run s = some (p, s1) → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset) →
      ProjI m0 c p 0 st.data → FM m0 a s1 p st.data.dmem →
      Eventually (step1 Host.exe) (Goal a s c m0) st) :
    Eventually (step1 Host.exe) (Goal a s c m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b0Offset)⟩ := by
  have hS := pre_stack h
  have g := geo_of h
  have pg := pgeo_of h
  have hN : verifyLayerStack ≤ m0.regs.SP.toNat := hS.2.1
  have hwf := Bus.wf_env0 hS (F := 2032) N_ge
  have hm : Match (Bus.env0 m0 2032) entryS m0 := Bus.match_entry hS N_ge rfl
  -- `b0`: the prologue, the product zeroed, `read_scalars`'s arguments.
  refine exec_then (blk hp b0_in_code (by simp [b0])) e0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hfb1 : FB m0 st1.data :=
    Fr.ofPrologue hN N_ge hm1 hwf rfl (by decide) slots_le (by decide) (by decide)
  have hts1 : TStateAt st1.data.dmem (tA m0) a s :=
    ts_frame h (rs := []) hm1 hwf (by decide) (pre_ts h)
  have w128 := Bus.wordAt_write (r := 0) (o := 128) hm1 rfl (by omega) (v := .reg .X2)
    (fun i hi ↦ by interval_cases i <;> rfl)
  have k1 : Bus.KeepRegs [.X0] m0 st1.data := Bus.KeepRegs.of_block hm1 rfl
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b0Offset + b0.length = k + NativeRustcVmArm.Vm.VerifyLayer.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b0_next]] at hpc1
  have x1v : st1.data.regs.X1.toBitVec = loc m0 152 := by
    show (st1.data.regs.getXReg .X1).toBitVec = _
    rw [hm1.regs .X1 _ rfl, ev_ptr]
    rfl
  have x2v : st1.data.regs.X2.toNat = 47 := by
    show (st1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl, litN 47]
  -- `read_scalars(t, product, 47)`.
  refine rs_call h hrs (o := 152) (n := 47) (by omega) hfb1 hpc1 (kg k1 .X0) x1v x2v hts1
    fun m2 hfb2 hx2 hok2 hcs2 hs2 ↦ ?_
  have k2 : Bus.KeepRegs [.X19, .X20, .X21, .X23, .X28] st1.data m2 :=
    Bus.KeepRegs.of_call hcs2 rfl
  -- `b1`: `None` if that failed.
  refine Fr.runBlock hS N_ge rfl hfb2 (blk hp b1_in_code (by simp [b1])) e1 rfl rfl
    (by decide) (by decide) fun st2 hfb3 hd3 hm3 hpc3 ↦ ?_
  have k3 : Bus.KeepRegs [.X0, .X19, .X20, .X21, .X23, .X28] m2 st2.data :=
    Bus.KeepRegs.of_block hm3 rfl
  have hc3 : SBool.eval (Env.ofMachine m2 [(base m0 2032, 2032)])
      (.cmp .eq .W32 (.reg .X0) (.lit 0)) = !((readScalars 47).run s).isSome := by
    show CmpOp.eq.apply .W32 (m2.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
    rw [show m2.regs.getXReg .X0 = m2.regs.X0 from rfl, hx2, okw_eq0]
  have hrun : runL s c m0 =
      ((readScalars 47).run s).bind fun p ↦ rest1 m0.regs.X1.toNat m0.regs.X2.toNat c p.1 p.2 :=
    run_rest _ _ _ _
  cases hr : (readScalars 47).run s with
  | none =>
    simp only [PcOk, hc3, hr, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc3
    refine exit hp h (hpc3.trans (label38 hp)) (FB.body h hfb3) ?_ fun c' s' he ↦ ?_
    · show st2.data.regs.getXReg .X0 = _
      rw [kg k3 .X0, hrun, hr]
      show m2.regs.X0 = _
      rw [hx2, hr]
      rfl
    · rw [hrun, hr] at he; cases he
  | some ps =>
    obtain ⟨p, s1⟩ := ps
    simp only [PcOk, hc3, hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hpc3
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b1Offset + b1.length = k + NativeRustcVmArm.Vm.VerifyLayer.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b1_next]] at hpc3
    obtain ⟨hprod2, hts2⟩ := hok2 p s1 hr
    have hpsz : p.size = 47 := NativeRustcVm.Sumcheck.readScalars_size hr
    -- `b2`: the frame's words, the projection's registers.
    have hb3 := FB.body h hfb3
    have r19 : st2.data.regs.X19 = m0.regs.X3 :=
      (kg k3 .X19).trans ((kg k2 .X19).trans (reg_of hm1 (r' := .X3) rfl))
    have hwfc := wf_claim h hb3
    have hmc := match_claim19 h hb3 r19
    refine exec_at (blk hp b2_in_code (by simp [b2])) e2 hwfc hpc3 hmc fun st3 hm4 hpc4 ↦ ?_
    have hfb4 := fb_blkW h hfb3 hm4 hwfc rfl (by decide)
    simp only [PcOk] at hpc4
    have hpc4' : st3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset) := hpc4.trans (label4 hp)
    have hd23 : st2.data.dmem = m2.dmem := hd3
    -- the claim's instance weights' count.
    have hc2 := claimAt_fb h hfb3
    obtain ⟨hmuw, hmu⟩ := mu_len hc2
    have hmun : (c.mu.size.toUInt64).toBitVec.toNat = c.mu.size := by simp; omega
    have l16 := ld1 (m := st2.data) (b0 := base m0 2032) (n0 := 2032) (n1 := 768) (o := 16) hmuw
    have hcnd : (SBool.cmp .ult .W64 (.load 1 16 8) (.lit 17)).eval
        (Env.ofMachine st2.data [(base m0 2032, 2032), (cA m0, 768)]) = true := by
      rw [sb_cmp, ult_apply, l16, litN 17, hmun]
      exact decide_eq_true (by omega)
    have r25 : (st3.data.regs.getXReg .X25).toBitVec.toNat = c.mu.size := by
      rw [hm4.regs .X25 _ rfl, iteT hcnd, l16, hmun]
    have r23 : (st3.data.regs.getXReg .X23).toBitVec.toNat = 2 * (c.mu.size / 2) := by
      rw [hm4.regs .X23 _ rfl, ev_bin, iteT hcnd, l16, ev_lit, and_apply, BitVec.toNat_and,
        hmun, BitVec.toNat_ofNat, show 30 % 2 ^ 64 = 30 from rfl, and30 _ (by omega)]
    have r19 : (st3.data.regs.getXReg .X19).toBitVec = cA m0 + BitVec.ofNat 64 32 := by
      rw [hm4.regs .X19 _ rfl, iteT hcnd, ev_ptr]
      rfl
    have r24 : (st3.data.regs.getXReg .X24).toBitVec = projectAddr := by
      rw [hm4.regs .X24 _ rfl]
      rfl
    have r26 : (st3.data.regs.getXReg .X26).toBitVec = projectAddr + BitVec.ofNat 64 8 := by
      rw [hm4.regs .X26 _ rfl, ev_bin, ev_lit, add_apply]
      rfl
    have r27 : (st3.data.regs.getXReg .X27).toBitVec.toNat = 1 := by
      rw [hm4.regs .X27 _ rfl, litN 1]
    have r20 : (st3.data.regs.getXReg .X20).toBitVec.toNat = 0 := by
      rw [hm4.regs .X20 _ rfl, litN 0]
    have r29 : (st3.data.regs.getXReg .X29).toBitVec.toNat = 0 := by
      rw [hm4.regs .X29 _ rfl, litN 0]
    have r21 : st3.data.regs.getXReg .X21 = 0 := reg_val hm4 rfl (x := 0) (by rw [ev_lit]; rfl)
    have r22 : st3.data.regs.getXReg .X22 = 0 := reg_val hm4 rfl (x := 0) (by rw [ev_lit]; rfl)
    have r28 : (st3.data.regs.getXReg .X28).toBitVec = loc m0 152 := by
      rw [Bus.keep_reg hm4 rfl, kg k3 .X28, kg k2 .X28, hm1.regs .X28 _ rfl, ev_ptr]
      rfl
    -- the words `b2` writes.
    have q23 : (Sym.reg .X23).eval (Env.ofMachine st2.data [(base m0 2032, 2032), (cA m0, 768)]) =
        sA m0 := by
      rw [ev_regU, kg k3 .X23, kg k2 .X23]
      exact congrArg UInt64.toBitVec (reg_of hm1 (r' := .X4) rfl)
    have q21 : (Sym.reg .X21).eval (Env.ofMachine st2.data [(base m0 2032, 2032), (cA m0, 768)]) =
        (packW m0).toBitVec := by
      rw [ev_regU, kg k3 .X21, kg k2 .X21, hm1.regs .X21 _ rfl]
      exact packW_eq m0
    have q20 : (Sym.reg .X20).eval (Env.ofMachine st2.data [(base m0 2032, 2032), (cA m0, 768)]) =
        m0.regs.X0.toBitVec := by
      rw [ev_regU, kg k3 .X20, kg k2 .X20]
      exact congrArg UInt64.toBitVec (reg_of hm1 (r' := .X0) rfl)
    have hrsN : readScalarsStack ≤ 1616 := by have := le_rs; rw [stack_eq] at this; omega
    have w128a : NativeRustcVm.WordAt st1.data.dmem (loc m0 128) m0.regs.X2 := w128
    have w128b : NativeRustcVm.WordAt m2.dmem (loc m0 128) m0.regs.X2 :=
      keep_call g hfb1.sp hrsN hs2 (o := 128) (bs := NativeRustcVm.wordBytes m0.regs.X2)
        (by rw [NativeRustcVm.length_wordBytes]; omega)
        (fun i hi ↦ by
          rw [NativeRustcVm.length_wordBytes] at hi
          rintro (hq | hq)
          · exact loc_not_loc g (o' := 152) (n := 16 * 47) (by omega) (by omega) (by omega) hq
          · exact (loc_not_ts h (o := 128 + i) (by omega)).1 hq) w128a
    have w128 : NativeRustcVm.WordAt st3.data.dmem (loc m0 128) m0.regs.X2 :=
      keep_blk hm4 hwfc (o := 128) (L := 8) (by omega)
        (fun w hw ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (le_of_eq (NativeRustcVm.length_wordBytes _)) (by rw [hd23]; exact w128b)
    have w144 := Bus.wordAt_write (r := 0) (o := 144) hm4 rfl (by omega)
      (v := .ite (.cmp .ult .W64 (.load 1 16 8) (.lit 17)) (.ptr 1 24) (.lit 8))
      (fun i hi ↦ by interval_cases i <;> rfl)
    rw [iteT hcnd, ev_ptr] at w144
    have w120 := Bus.wordAt_write (r := 0) (o := 120) hm4 rfl (by omega) (v := .reg .X23)
      (fun i hi ↦ by interval_cases i <;> rfl)
    rw [q23] at w120
    have w88 := Bus.wordAt_write (r := 0) (o := 88) hm4 rfl (by omega)
      (v := .bin .add .W64 (.reg .X23) (.lit 51200)) (fun i hi ↦ by interval_cases i <;> rfl)
    rw [ev_bin, q23, ev_lit, add_apply] at w88
    have w80 := Bus.wordAt_write (r := 0) (o := 80) hm4 rfl (by omega) (v := .ptr 1 16)
      (fun i hi ↦ by interval_cases i <;> rfl)
    rw [ev_ptr] at w80
    have w96 := Bus.wordAt_write (r := 0) (o := 96) hm4 rfl (by omega)
      (v := .bin .add .W64 (.reg .X23) (.lit 107528)) (fun i hi ↦ by interval_cases i <;> rfl)
    rw [ev_bin, q23, ev_lit, add_apply] at w96
    have w112 := Bus.wordAt_write (r := 0) (o := 112) hm4 rfl (by omega) (v := .reg .X21)
      (fun i hi ↦ by interval_cases i <;> rfl)
    rw [q21, UInt64.ofBitVec_toBitVec] at w112
    have w104 := Bus.wordAt_write (r := 0) (o := 104) hm4 rfl (by omega) (v := .reg .X20)
      (fun i hi ↦ by interval_cases i <;> rfl)
    rw [q20, UInt64.ofBitVec_toBitVec] at w104
    have w136 := Bus.wordAt_write (r := 0) (o := 136) hm4 rfl (by omega) (v := .ptr 1 0)
      (fun i hi ↦ by interval_cases i <;> rfl)
    rw [ev_ptr] at w136
    have hfw : Bus.FrameWords st3.data.dmem (base m0 2032) (projWords m0) := by
      intro q hq
      simp only [projWords, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact w128
      · exact w144
      · exact w120
      · exact w88
      · exact w80
      · exact w96
      · exact w112
      · exact w104
      · have e : (UInt64.ofBitVec ((Env.ofMachine st2.data
            [(base m0 2032, 2032), (cA m0, 768)]).base 1 + BitVec.ofInt 64 0)) = m0.regs.X3 := by
          apply UInt64.toBitVec_inj.mp
          rw [UInt64.toBitVec_ofBitVec]
          exact BitVec.add_zero _
        rw [← e]; exact w136
    have hprod : NativeRustcVm.EWsAt st3.data.dmem (loc m0 152) p.toList :=
      keep_blk hm4 hwfc (o := 152) (L := 752) (by omega)
        (fun w hw ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hpsz])
        (by rw [hd23]; exact hprod2)
    have hts3 : TStateAt st3.data.dmem (tA m0) a s1 :=
      ts_frame h hm4 hwfc (fun w hw ↦ by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (by rw [hd23]; exact hts2)
    refine cont st3 p s1 hr hpc4' ⟨⟨hfb4, by omega, r25, r23, r20, r24, r26, r19, r27, w144⟩,
      r28, r29, ?_, hprod, hpsz⟩ ⟨hfw, hprod, hpsz, hts3⟩
    show (⟨st3.data.regs.getXReg .X21, st3.data.regs.getXReg .X22⟩ : EW) = 0
    rw [r21, r22]
    rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
