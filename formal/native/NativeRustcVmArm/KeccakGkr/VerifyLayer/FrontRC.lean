module

public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontIota
import Mathlib.Tactic.IntervalCases

/-!
# `verify_layer`'s front: ι's two round constants' bit weights

From `b17` (`k + NativeRustcVmArm.Vm.VerifyLayer.b17Offset`, the segment kernel in the frame, `AtS`): the first round constant's bit
weights (`b17`, `bitsA_loop`), the second's (`b19`, `bitsB_loop`), to `b21` (`k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset`, `AtJ`,
`segB_run`); with the segment kernel, `seg_run` from `b15`.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)

public section

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- A state of the front with the round constants as region `1`. -/
theorem match_rc {m : MachineData} (h : VerifyLayerPre a s c m0) (hb : FB m0 m)
    {known : List (XReg × Sym)} {labels : List (Label × Nat)} {bounds : List (Sym × Nat)}
    (hknown : AllOf (fun p ↦ (m.regs.getXReg p.1).toBitVec =
      p.2.eval (Env.ofMachine m [(base m0 2032, 2032), (rcAddr, 192)])) known)
    (hlabels : AllOf (fun p ↦ (Env.ofMachine m [(base m0 2032, 2032), (rcAddr, 192)]).base p.2 =
      (Labels.label p.1).toBitVec) labels)
    (hbounds : AllOf (fun p ↦
      (p.1.eval (Env.ofMachine m [(base m0 2032, 2032), (rcAddr, 192)])).toNat < p.2) bounds) :
    Match (Env.ofMachine m [(base m0 2032, 2032), (rcAddr, 192)])
      (init [(2032, true), (192, false)] (.ptr 0 0) known labels bounds) m :=
  match_ofMachine (sregions := [(2032, true), (192, false)])
    (regions := [(base m0 2032, 2032), (rcAddr, 192)])
    ⟨rfl, fun _ ↦ Bus.base_aligned h.1 (by decide) (by decide), rfl, nofun, trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
          Option.getD_some]; rw [hb.sp]; simp)
    hknown hlabels hbounds trivial

end

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The round constants' bit weights**, from `b17` to `b21`. -/
theorem segB_run (hp : Placed code k) (h : VerifyLayerPre a s c m0) {p : Array EW}
    {s1 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b17Offset))
    (hs : AtS m0 a c p s1 st.data) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset) → AtJ m0 a c p s1 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have g := geo_of h
  have hstep := pre_step h
  have := g.hN; have := Geo.sp_lt m0
  have hfw := hs.fm.fw
  have hw128 := FrameWords.get hfw (o := 128) (v := m0.regs.X2) (by simp [projWords])
  have hw120 := FrameWords.get hfw (o := 120) (v := m0.regs.X4) (by simp [projWords])
  have hst : m0.regs.X2.toBitVec.toNat = m0.regs.X2.toNat := rfl
  -- `b17`: the first round constant, the first loop's registers.
  have hwfA := wf_rc h hs.fb
  have l128 := ld0 (m := st.data) (b1 := rcAddr) (n0 := 2032) (n1 := 192) (o := 128) hw128
  have l120 := ld0 (m := st.data) (b1 := rcAddr) (n0 := 2032) (n1 := 192) (o := 120) hw120
  have i11 : ((Sym.bin .sub .W64 (.lit 11) (.load 0 128 8)).eval
      (Env.ofMachine st.data [(base m0 2032, 2032), (rcAddr, 192)])).toNat =
        11 - m0.regs.X2.toNat :=
    subSym (litN 11) (by rw [l128]; rfl) (by omega)
  have hmA : Match (Env.ofMachine st.data [(base m0 2032, 2032), (rcAddr, 192)]) rc1S st.data :=
    match_rc h hs.fb trivial ⟨rfl, trivial⟩ ⟨lt_of_eq_of_lt i11 (by omega), trivial⟩
  refine exec_at (blk hp b17_in_code (by simp [b17])) e17 hwfA hpc hmA fun stA hmA' hpcA ↦ ?_
  have hfbA := fb_blkW h hs.fb hmA' hwfA rfl (by decide)
  simp only [PcOk, show k + NativeRustcVmArm.Vm.VerifyLayer.b17Offset + b17.length = k + NativeRustcVmArm.Vm.VerifyLayer.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b17_next]] at hpcA
  have rcA := rc_fb h hs.fb
  have xA18 : stA.data.regs.getXReg .X18 = wA m0 :=
    reg_val hmA' rfl (ev_loadx rfl i11 (by omega) (rc_word rcA (by omega)))
  have xA1 : stA.data.regs.getXReg .X1 = m0.regs.X2 := reg_val hmA' rfl l128
  have xA0 : (stA.data.regs.getXReg .X0).toBitVec = rcAddr := hmA'.regs .X0 _ rfl
  have kA : Bus.KeepRegs [.X21, .X22, .X25] st.data stA.data := Bus.KeepRegs.of_block hmA' rfl
  -- the frame after `b17`.
  have w32 := Bus.wordAt_write (r := 0) (o := 32) hmA' rfl (by omega) (v := .reg .X19)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ev_regU, show (st.data.regs.getXReg .X19).toBitVec = _ from hs.x19] at w32
  have w112 := Bus.wordAt_write (r := 0) (o := 112) hmA' rfl (by omega) (v := .load 0 904 8)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ld0 hs.s0a, UInt64.ofBitVec_toBitVec] at w112
  have w72 := Bus.wordAt_write (r := 0) (o := 72) hmA' rfl (by omega) (v := .load 0 912 8)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ld0 hs.s0b, UInt64.ofBitVec_toBitVec] at w72
  have fwA : Bus.FrameWords stA.data.dmem (base m0 2032) (iWords m0) :=
    fw_cons w32 (fw_blk hmA' hwfA pOffs (pWords_map m0) (by decide)
      (fw_sub hfw (pWords_sub m0)))
  have s920 := same_word hs.s1a (same_blk hmA' hwfA (o' := 920) (n' := 8) (by omega) (by decide))
  have s928 := same_word hs.s1b (same_blk hmA' hwfA (o' := 928) (n' := 8) (by omega) (by decide))
  have prodA := ewsAt_same hs.fm.prod
    (same_blk hmA' hwfA (o' := 152) (n' := 752) (by omega) (by decide))
    (by rw [Array.length_toList, hs.fm.psz])
  have tsA := ts_frame h hmA' hwfA (by decide) hs.fm.ts
  -- the first loop.
  refine bitsA_loop hp h (st0 := stA.data) (w := wA m0) ?_ 16 0 stA rfl hpcA
    ⟨hfbA, rfl, fun _ _ ↦ rfl, by decide, ?_, ?_, xA18, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · show (stA.data.regs.getXReg .X17).toBitVec.toNat = _
    rw [hmA'.regs .X17 _ rfl, litN 0]
  · show (stA.data.regs.getXReg .X2).toBitVec = _
    rw [hmA'.regs .X2 _ rfl, ev_bin, l120, ev_lit, add_apply]
  · show (stA.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hmA'.regs .X3 _ rfl, litN 1]
    rfl
  · show (stA.data.regs.getXReg .X4).toBitVec.toNat = _
    rw [hmA'.regs .X4 _ rfl, litN 2]
    rfl
  · show (stA.data.regs.getXReg .X5).toBitVec.toNat = _
    rw [hmA'.regs .X5 _ rfl, litN 4]
    rfl
  · show (stA.data.regs.getXReg .X6).toBitVec.toNat = _
    rw [hmA'.regs .X6 _ rfl, litN 8]
    rfl
  · show (⟨stA.data.regs.getXReg .X12, stA.data.regs.getXReg .X8⟩ : EW) = 0
    rw [reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  · show (⟨stA.data.regs.getXReg .X13, stA.data.regs.getXReg .X9⟩ : EW) = 0
    rw [reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  · show (⟨stA.data.regs.getXReg .X14, stA.data.regs.getXReg .X10⟩ : EW) = 0
    rw [reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  · show (⟨stA.data.regs.getXReg .X16, stA.data.regs.getXReg .X11⟩ : EW) = 0
    rw [reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmA' rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  intro stB hpcB hfbB hdB kB ha0 ha1 ha2 ha3
  -- `b19`: the second round constant, the second loop's registers.
  have xB1 : (stB.data.regs.getXReg .X1).toNat = m0.regs.X2.toNat := by
    rw [kg kB .X1, xA1]
  have xB0 : (stB.data.regs.getXReg .X0).toBitVec = rcAddr := by rw [kg kB .X0, xA0]
  have hwfB := wf_rc h hfbB
  have i23 : ((Sym.bin .sub .W64 (.lit 23) (.reg .X1)).eval
      (Env.ofMachine stB.data [(base m0 2032, 2032), (rcAddr, 192)])).toNat =
        23 - m0.regs.X2.toNat :=
    subSym (litN 23) (regN .X1 xB1) (by omega)
  have hmB : Match (Env.ofMachine stB.data [(base m0 2032, 2032), (rcAddr, 192)]) rc2S
      stB.data :=
    match_rc h hfbB ⟨by
        show (stB.data.regs.getXReg .X0).toBitVec = rcAddr + BitVec.ofInt 64 0
        rw [xB0, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
          NativeRustcVm.addr_add_zero], trivial⟩ trivial
      ⟨lt_of_eq_of_lt i23 (by omega), trivial⟩
  refine exec_at (blk hp b19_in_code (by simp [b19])) e19 hwfB hpcB hmB fun stC hmC hpcC ↦ ?_
  have hfbC := fb_blkW h hfbB hmC hwfB rfl (by decide)
  simp only [PcOk, show k + NativeRustcVmArm.Vm.VerifyLayer.b19Offset + b19.length = k + NativeRustcVmArm.Vm.VerifyLayer.b20Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b19_next]] at hpcC
  have rcB := rc_fb h hfbB
  rw [← hdB] at fwA s920 s928 prodA tsA w112 w72
  have l120B := ld0 (m := stB.data) (b1 := rcAddr) (n0 := 2032) (n1 := 192) (o := 120)
    (FrameWords.get fwA (o := 120) (v := m0.regs.X4) (by simp [iWords, pWords]))
  have xC12 : stC.data.regs.getXReg .X12 = wB m0 :=
    reg_val hmC rfl (ev_loadx (r := 1) (b := rcAddr) rfl i23 (by omega) (rc_word rcB (by omega)))
  have kC : Bus.KeepRegs [.X21, .X22, .X25] stB.data stC.data := Bus.KeepRegs.of_block hmC rfl
  have x13 : stB.data.regs.getXReg .X13 = (bAcc c (wA m0) 1 16).c0 := congrArg EW.c0 ha1
  have x12 : stB.data.regs.getXReg .X12 = (bAcc c (wA m0) 0 16).c0 := congrArg EW.c0 ha0
  have x16 : stB.data.regs.getXReg .X16 = (bAcc c (wA m0) 3 16).c0 := congrArg EW.c0 ha3
  have x14 : stB.data.regs.getXReg .X14 = (bAcc c (wA m0) 2 16).c0 := congrArg EW.c0 ha2
  have x9 : stB.data.regs.getXReg .X9 = (bAcc c (wA m0) 1 16).c1 := congrArg EW.c1 ha1
  have x8 : stB.data.regs.getXReg .X8 = (bAcc c (wA m0) 0 16).c1 := congrArg EW.c1 ha0
  have x11 : stB.data.regs.getXReg .X11 = (bAcc c (wA m0) 3 16).c1 := congrArg EW.c1 ha3
  have x10 : stB.data.regs.getXReg .X10 = (bAcc c (wA m0) 2 16).c1 := congrArg EW.c1 ha2
  have xC10 : stC.data.regs.getXReg .X10 =
      (bAcc c (wA m0) 1 16).c0 ^^^ (bAcc c (wA m0) 0 16).c0 := by
    rw [reg_val hmC rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)), x13, x12]
  have xC11 : stC.data.regs.getXReg .X11 =
      (bAcc c (wA m0) 3 16).c0 ^^^ (bAcc c (wA m0) 2 16).c0 := by
    rw [reg_val hmC rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)), x16, x14]
  have w40 := Bus.wordAt_write (r := 0) (o := 40) hmC rfl (by omega)
    (v := .bin .eor .W64 (.reg .X11) (.reg .X10)) (fun i hi ↦ by interval_cases i <;> rfl)
  rw [eorSym (ev_regU _ _ _) (ev_regU _ _ _), UInt64.ofBitVec_toBitVec, x11, x10] at w40
  have w48 := Bus.wordAt_write (r := 0) (o := 48) hmC rfl (by omega)
    (v := .bin .eor .W64 (.reg .X9) (.reg .X8)) (fun i hi ↦ by interval_cases i <;> rfl)
  rw [eorSym (ev_regU _ _ _) (ev_regU _ _ _), UInt64.ofBitVec_toBitVec, x9, x8] at w48
  have w64 := Bus.wordAt_write (r := 0) (o := 64) hmC rfl (by omega) (v := .load 0 920 8)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ld0 s920, UInt64.ofBitVec_toBitVec] at w64
  have w56 := Bus.wordAt_write (r := 0) (o := 56) hmC rfl (by omega) (v := .load 0 928 8)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ld0 s928, UInt64.ofBitVec_toBitVec] at w56
  have fwC := fw_blk hmC hwfB iOffs (iWords_map m0) (by decide) fwA
  have w112C := same_word w112 (same_blk hmC hwfB (o' := 112) (n' := 8) (by omega) (by decide))
  have w72C := same_word w72 (same_blk hmC hwfB (o' := 72) (n' := 8) (by omega) (by decide))
  have prodC := ewsAt_same prodA
    (same_blk hmC hwfB (o' := 152) (n' := 752) (by omega) (by decide))
    (by rw [Array.length_toList, hs.fm.psz])
  have tsC := ts_frame h hmC hwfB (by decide) tsA
  -- the second loop.
  refine bitsB_loop hp h (st0 := stC.data) (w := wB m0) ?_ 16 0 stC rfl hpcC
    ⟨hfbC, rfl, fun _ _ ↦ rfl, by decide, ?_, ?_, xC12, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · show (stC.data.regs.getXReg .X4).toBitVec.toNat = _
    rw [hmC.regs .X4 _ rfl, litN 0]
  · show (stC.data.regs.getXReg .X13).toBitVec = _
    rw [hmC.regs .X13 _ rfl, ev_bin, l120B, ev_lit, add_apply]
  · show (stC.data.regs.getXReg .X14).toBitVec.toNat = _
    rw [hmC.regs .X14 _ rfl, litN 1]
    rfl
  · show (stC.data.regs.getXReg .X15).toBitVec.toNat = _
    rw [hmC.regs .X15 _ rfl, litN 2]
    rfl
  · show (stC.data.regs.getXReg .X16).toBitVec.toNat = _
    rw [hmC.regs .X16 _ rfl, litN 4]
    rfl
  · show (stC.data.regs.getXReg .X20).toBitVec.toNat = _
    rw [hmC.regs .X20 _ rfl, litN 8]
    rfl
  · show (⟨stC.data.regs.getXReg .X5, stC.data.regs.getXReg .X17⟩ : EW) = 0
    rw [reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  · show (⟨stC.data.regs.getXReg .X6, stC.data.regs.getXReg .X18⟩ : EW) = 0
    rw [reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  · show (⟨stC.data.regs.getXReg .X7, stC.data.regs.getXReg .X2⟩ : EW) = 0
    rw [reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  · show (⟨stC.data.regs.getXReg .X19, stC.data.regs.getXReg .X3⟩ : EW) = 0
    rw [reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl),
      reg_val hmC rfl (x := 0) (by rw [ev_lit]; rfl)]
    rfl
  intro stD hpcD hfbD hdD kD hb0 hb1 hb2 hb3
  rw [← hdD] at fwC w112C w72C prodC tsC w40 w48 w64 w56
  refine cont stD hpcD ⟨hfbD, fwC, prodC, hs.fm.psz, tsC, ?_, ?_, w112C, w72C, w64, w56, ?_, ?_,
    w40, w48, hb0, hb1, hb2, hb3⟩
  · show (stD.data.regs.getXReg .X25).toNat = _
    rw [kg kD .X25, kg kC .X25, kg kB .X25, kg kA .X25]
    exact hs.x25
  · show (⟨stD.data.regs.getXReg .X21, stD.data.regs.getXReg .X22⟩ : EW) = _
    rw [kg kD .X21, kg kD .X22, kg kC .X21, kg kC .X22, kg kB .X21, kg kB .X22, kg kA .X21,
      kg kA .X22]
    exact hs.acc
  · show stD.data.regs.getXReg .X10 = _
    rw [kg kD .X10, xC10]
  · show stD.data.regs.getXReg .X11 = _
    rw [kg kD .X11, xC11]

/-- **The segment kernel and the bit weights**, from `b15` to `b21`. -/
theorem seg_run (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hek : Spec (Labels.label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost) {p : Array EW}
    {s1 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b15Offset))
    (hi : AtI m0 a c p s1 st.data) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset) → AtJ m0 a c p s1 st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  segA_run hp h hek hpc hi fun _ hpc' hs ↦ segB_run hp h hpc' hs cont

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
