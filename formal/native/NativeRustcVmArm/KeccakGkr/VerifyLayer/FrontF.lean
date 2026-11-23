module

public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontE

/-!
# `verify_layer`'s front: the second check

From `b42` (`k + NativeRustcVmArm.Vm.VerifyLayer.b42Offset`, `AtL`): the kernel's first `1600` entries against the claim's bit weights
(`dot`), `κ t0 + (κ + t1) t2` (`EW::mul` twice), its product with the dot, the comparison with
the plain sumcheck's claim (`b46`, `b47`), to `b48` (`k + NativeRustcVmArm.Vm.VerifyLayer.b48Offset`, `AtG`, `check2_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

public section

section
variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- A range of the scratch kept by a block writing the frame only. -/
theorem scr_blk (h : VerifyLayerPre a s c m0) {m m' : MachineData} {S : SState}
    (hm : Match (Env.ofMachine m [(base m0 2032, 2032)]) S m')
    (hwf : (Env.ofMachine m [(base m0 2032, 2032)]).WF)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 2032) {o n : Nat} (ho : o < 205824)
    (hon : o + n ≤ 205824) :
    NativeRustcVm.Layout.Same m.dmem m'.dmem (sA m0 + BitVec.ofNat 64 o) n :=
  NativeRustcVm.Layout.Same.of_sameOutside (frame_only h (rs := []) hm hwf hmem) fun j hj hq ↦
    scr_not_frame (geo_of h) ho hon (NativeRustcVm.inRange_add hj (by omega)) hq

omit [Labels] in
/-- An element of `E` of three at `loc 1888`, word by word. -/
theorem tv_words {d : DataMem} {tv : Array EW} (h : NativeRustcVm.EWsAt d (loc m0 1888) tv.toList)
    (hsz : tv.size = 3) {i : Nat} (hi : i < 3) :
    NativeRustcVm.WordAt d (base m0 2032 + BitVec.ofNat 64 (1888 + 16 * i)) (tv.getD i 0).c0 ∧
      NativeRustcVm.WordAt d (base m0 2032 + BitVec.ofNat 64 (1888 + 16 * i + 8))
        (tv.getD i 0).c1 := by
  have := ew_words h (i := i) (by rw [Array.length_toList, hsz]; exact hi)
  rw [show loc m0 1888 = base m0 2032 + BitVec.ofNat 64 1888 from rfl, NativeRustcVm.addr_add_add,
    NativeRustcVm.addr_add_add, ← getD_toList,
    show 1888 + (16 * i + 8) = 1888 + 16 * i + 8 by omega] at this
  exact this

end

theorem take_extract (xs : Array EW) (n : Nat) : (xs.toList.take n).toArray = xs.extract 0 n := by
  apply Array.ext'
  simp

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The second check**, from `b42` to `b48`. -/
theorem check2_run (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hdot : Spec (label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {ch : EW} {pt lp tv : Array EW} {val : EW} {s5 : TState} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b42Offset)) (hl : AtL m0 a ch pt lp tv val s5 st.data)
    (hrun : runL s c m0 = (if checkB c (sumE (keccakInstanceWeights ch)) lp tv val then
        rest6 ch pt lp tv s5 else none))
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b48Offset) →
      AtG m0 a s c ch pt lp tv s5 st'.data → Eventually (step1 Host.exe) (Goal a s c m0) st') :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hS := pre_stack h
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0; have := g.hs; have := g.hss
  set κ := sumE (keccakInstanceWeights ch) with hκ
  have tw0 := tv_words hl.htv hl.tsz (i := 0) (by decide)
  have tw1 := tv_words hl.htv hl.tsz (i := 1) (by decide)
  have tw2 := tv_words hl.htv hl.tsz (i := 2) (by decide)
  have hesz : (eqKernel lp).toList.length = 2048 := by
    rw [Array.length_toList, NativeVm.Math.Keccak.eqKernel_size, hl.hlp]; rfl
  have hpsz : 16 * pt.toList.length ≤ 480 := by rw [Array.length_toList]; have := hl.hps; omega
  have fwBel : ∀ {d d' : DataMem} {ws : List (Nat × UInt64)}, SameOutside d d' (Bel m0) →
      (∀ q ∈ ws, q.1 + 8 ≤ 2032) → Bus.FrameWords d (base m0 2032) ws →
      Bus.FrameWords d' (base m0 2032) ws := fun hs hle hw ↦
    FrameWords.of_same hw (same_bel g hs (x := base m0 2032) (n := 2032) (by rw [g.bN]; omega)
      (by rw [g.bN]; omega)) hle
  -- `b42`: `dot(kernel, 1600, weights, 1600)`, the values in registers, the claim in the frame.
  have hb0 := FB.body h hl.fb
  have hwf1 := wf_fr h hb0
  refine exec_at (blk hp b42_in_code (by simp [b42])) e42 hwf1 hpc (match_fr h hb0)
    fun st1 hm1 hpc1 ↦ ?_
  have hfb1 := fb_blkW h hl.fb hm1 hwf1 rfl (by decide)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b42Offset + b42.length = k + NativeRustcVmArm.Vm.VerifyLayer.b43Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b42_next]] at hpc1
  have u0 : st1.data.regs.X0.toBitVec = sA m0 + BitVec.ofNat 64 107520 := by
    show (st1.data.regs.getXReg .X0).toBitVec = _
    rw [hm1.regs .X0 _ rfl, ldF hl.f144]
  have u1 : st1.data.regs.X1.toNat = 1600 := by
    show (st1.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm1.regs .X1 _ rfl, litN 1600]
  have u2 : st1.data.regs.X2.toBitVec = sA m0 + BitVec.ofNat 64 25600 := by
    show (st1.data.regs.getXReg .X2).toBitVec = _
    rw [hm1.regs .X2 _ rfl, ev_bin, regB .X21 hl.x21, ev_lit, add_apply]
  have u3 : st1.data.regs.X3.toNat = 1600 := by
    show (st1.data.regs.getXReg .X3).toBitVec.toNat = _
    rw [hm1.regs .X3 _ rfl, litN 1600]
  have r29 : st1.data.regs.getXReg .X29 = (tv.getD 0 0).c0 := reg_val hm1 rfl (ldF tw0.1)
  have r27 : st1.data.regs.getXReg .X27 = (tv.getD 0 0).c1 := reg_val hm1 rfl (ldF tw0.2)
  have r23 : st1.data.regs.getXReg .X23 = (tv.getD 1 0).c0 := reg_val hm1 rfl (ldF tw1.1)
  have r19 : st1.data.regs.getXReg .X19 = (tv.getD 1 0).c1 := reg_val hm1 rfl (ldF tw1.2)
  have r20 : st1.data.regs.getXReg .X20 = (tv.getD 2 0).c0 := reg_val hm1 rfl (ldF tw2.1)
  have r28 : st1.data.regs.getXReg .X28 = (tv.getD 2 0).c1 := reg_val hm1 rfl (ldF tw2.2)
  have w112 := Bus.wordAt_write (r := 0) (o := 112) hm1 rfl (by omega) (v := .reg .X20)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ev_regU, UInt64.ofBitVec_toBitVec, show st.data.regs.getXReg .X20 = _ from hl.x20] at w112
  have w128 := Bus.wordAt_write (r := 0) (o := 128) hm1 rfl (by omega) (v := .reg .X19)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ev_regU, UInt64.ofBitVec_toBitVec, show st.data.regs.getXReg .X19 = _ from hl.x19] at w128
  have k1 : Bus.KeepRegs [.X22, .X24, .X25, .X26] st.data st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  have fw1 : Bus.FrameWords st1.data.dmem (base m0 2032)
      ((112, val.c0) :: (128, val.c1) :: (144, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107520)) ::
        eWords m0) :=
    fw_cons w112 (fw_cons w128 (fw_blk hm1 hwf1 [144, 120, 136, 80, 88, 96] rfl (by decide)
      (fw_cons hl.f144 hl.fw)))
  have mu1 := NativeRustcVm.Layout.BufEWAt.of_same hl.mu
    (same_blk hm1 hwf1 (o' := 968) (n' := 264) (by omega) (by decide)) (by omega)
  have pt1 := ewsAt_same hl.hpt (same_blk hm1 hwf1 (o' := 1232) (n' := 480) (by omega)
    (by decide)) hpsz
  have eq1 := ewsAt_same hl.heq (scr_blk h hm1 hwf1 (by decide) (o := 107520) (n := 32768)
    (by omega) (by omega)) (by rw [hesz])
  have ts1 := ts_frame h hm1 hwf1 (by decide) hl.ts
  -- `dot`.
  have hdotN : dotStack ≤ 1616 := by have := le_dot; rw [stack_eq] at this; omega
  refine fleaf h le_dot hdot (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ hq' ↦
      hq'.elim (fun h' ↦ absurd h' (Bus.not_inRange_zero _ _)) id, hq.2.2⟩) hfb1 hpc1
    ⟨hfb1.stackOk hS rfl le_dot,
      ⟨by rw [u0, u1]; exact readable_scr h hfb1 (by omega) (by omega),
        by rw [u0, u1]; exact offStack_scr h hfb1 (by omega) (by omega) hdotN⟩,
      ⟨by rw [u2, u3]; exact readable_scr h hfb1 (by omega) (by omega),
        by rw [u2, u3]; exact offStack_scr h hfb1 (by omega) (by omega) hdotN⟩⟩
    fun m2 hfb2 hq2 hcs2 hs2 hk2 ↦ ?_
  have hw1 := weightsAt_fb h hfb1
  have D2 : (⟨m2.regs.X0, m2.regs.X1⟩ : EW) =
      dot ((eqKernel lp).extract 0 LeanVM.Protocol.Verifier.keccakBits) c.weights := by
    have e := hq2.1
    rw [slice_eq (NativeRustcVm.EWsAt.take eq1 1600) u0 (by rw [u1, List.length_take, hesz]; rfl),
      slice_eq hw1.2 u2 (by rw [u3, Array.length_toList, hw1.1]; rfl), Array.toArray_toList] at e
    rw [← take_extract]
    exact e
  have hle : ∀ {ws : List (Nat × UInt64)} (offs : List Nat), ws.map Prod.fst = offs →
      offs.all (· + 8 ≤ 2032) = true → ∀ q ∈ ws, q.1 + 8 ≤ 2032 := fun offs ho hc q hq ↦ by
    have := List.all_eq_true.mp hc q.1 (ho ▸ List.mem_map_of_mem hq)
    simpa using this
  have fw2 := fwBel hs2 (hle [112, 128, 144, 120, 136, 80, 88, 96] rfl (by decide)) fw1
  have mu2 := NativeRustcVm.Layout.BufEWAt.of_same mu1 (loc_bel g hs2 (o := 968) (n := 264)
    (by omega)) (by omega)
  have pt2 := ewsAt_same pt1 (loc_bel g hs2 (o := 1232) (n := 480) (by omega)) hpsz
  have eq2 := ewsAt_same eq1 (scr_bel g hs2 (o := 107520) (n := 32768) (by omega) (by omega))
    (by rw [hesz])
  have ts2 := ts_bel h hk2 hs2 ts1
  -- `b43`: `κ t0`, the dot and `t0` in the frame.
  have hb2 := FB.body h hfb2
  have hwf3 := wf_fr h hb2
  refine exec_at (blk hp b43_in_code (by simp [b43])) e43 hwf3 rfl (match_fr h hb2)
    fun st3 hm3 hpc3 ↦ ?_
  have hfb3 := fb_blkW h hfb2 hm3 hwf3 rfl (by decide)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b43Offset + b43.length = k + NativeRustcVmArm.Vm.VerifyLayer.b44Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b43_next]] at hpc3
  have kap3 : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) = κ := by
    rw [show st3.data.regs.X0 = _ from reg_of (r := .X0) hm3 (r' := .X25) rfl,
      show st3.data.regs.X1 = _ from reg_of (r := .X1) hm3 (r' := .X26) rfl, hcs2 .X25 rfl,
      hcs2 .X26 rfl, kg k1 .X25, kg k1 .X26]
    exact hl.kap
  have t03 : (⟨st3.data.regs.X2, st3.data.regs.X3⟩ : EW) = tv.getD 0 0 := by
    rw [show st3.data.regs.X2 = _ from reg_of (r := .X2) hm3 (r' := .X29) rfl,
      show st3.data.regs.X3 = _ from reg_of (r := .X3) hm3 (r' := .X27) rfl, hcs2 .X29 rfl,
      hcs2 .X27 rfl, r29, r27]
  have w72 := Bus.wordAt_write (r := 0) (o := 72) hm3 rfl (by omega) (v := .reg .X0)
    (fun i hi ↦ by interval_cases i <;> rfl)
  have w64 := Bus.wordAt_write (r := 0) (o := 64) hm3 rfl (by omega) (v := .reg .X1)
    (fun i hi ↦ by interval_cases i <;> rfl)
  have w56 := Bus.wordAt_write (r := 0) (o := 56) hm3 rfl (by omega) (v := .reg .X29)
    (fun i hi ↦ by interval_cases i <;> rfl)
  have w48 := Bus.wordAt_write (r := 0) (o := 48) hm3 rfl (by omega) (v := .reg .X27)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ev_regU, UInt64.ofBitVec_toBitVec] at w72 w64 w56 w48
  rw [hcs2 .X29 rfl, r29] at w56
  rw [hcs2 .X27 rfl, r27] at w48
  have k3 : Bus.KeepRegs [.X19, .X20, .X22, .X23, .X24, .X25, .X26, .X28] m2 st3.data :=
    Bus.KeepRegs.of_block hm3 rfl
  have fw3 : Bus.FrameWords st3.data.dmem (base m0 2032)
      ((48, (tv.getD 0 0).c1) :: (56, (tv.getD 0 0).c0) :: (64, m2.regs.getXReg .X1) ::
        (72, m2.regs.getXReg .X0) :: (112, val.c0) :: (128, val.c1) ::
        (144, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107520)) :: eWords m0) :=
    fw_cons w48 (fw_cons w56 (fw_cons w64 (fw_cons w72
      (fw_blk hm3 hwf3 [112, 128, 144, 120, 136, 80, 88, 96] rfl (by decide) fw2))))
  have mu3 := NativeRustcVm.Layout.BufEWAt.of_same mu2
    (same_blk hm3 hwf3 (o' := 968) (n' := 264) (by omega) (by decide)) (by omega)
  have pt3 := ewsAt_same pt2 (same_blk hm3 hwf3 (o' := 1232) (n' := 480) (by omega)
    (by decide)) hpsz
  have eq3 := ewsAt_same eq2 (scr_blk h hm3 hwf3 (by decide) (o := 107520) (n := 32768)
    (by omega) (by omega)) (by rw [hesz])
  have ts3 := ts_frame h hm3 hwf3 (by decide) ts2
  refine fmul_call h hmul hfb3 hpc3 fun m4 hfb4 h40 h41 hcs4 hs4 hk4 ↦ ?_
  have A4 : (⟨m4.regs.X0, m4.regs.X1⟩ : EW) = κ * tv.getD 0 0 := by
    rw [h40, h41, kap3, t03]
    rfl
  have fw4 := fwBel hs4 (hle [48, 56, 64, 72, 112, 128, 144, 120, 136, 80, 88, 96] rfl
    (by decide)) fw3
  have mu4 := NativeRustcVm.Layout.BufEWAt.of_same mu3 (loc_bel g hs4 (o := 968) (n := 264)
    (by omega)) (by omega)
  have pt4 := ewsAt_same pt3 (loc_bel g hs4 (o := 1232) (n := 480) (by omega)) hpsz
  have eq4 := ewsAt_same eq3 (scr_bel g hs4 (o := 107520) (n := 32768) (by omega) (by omega))
    (by rw [hesz])
  have ts4 := ts_bel h hk4 hs4 ts3
  -- `b44`: `(κ + t1) t2`, `t1` and `t2` in the frame.
  have q23 : m4.regs.getXReg .X23 = (tv.getD 1 0).c0 := by
    rw [hcs4 .X23 rfl, kg k3 .X23, hcs2 .X23 rfl, r23]
  have q19 : m4.regs.getXReg .X19 = (tv.getD 1 0).c1 := by
    rw [hcs4 .X19 rfl, kg k3 .X19, hcs2 .X19 rfl, r19]
  have q20 : m4.regs.getXReg .X20 = (tv.getD 2 0).c0 := by
    rw [hcs4 .X20 rfl, kg k3 .X20, hcs2 .X20 rfl, r20]
  have q28 : m4.regs.getXReg .X28 = (tv.getD 2 0).c1 := by
    rw [hcs4 .X28 rfl, kg k3 .X28, hcs2 .X28 rfl, r28]
  have q25 : m4.regs.getXReg .X25 = κ.c0 := by
    rw [hcs4 .X25 rfl, kg k3 .X25, ← reg_of (r := .X0) hm3 (r' := .X25) rfl]
    exact congrArg EW.c0 kap3
  have q26 : m4.regs.getXReg .X26 = κ.c1 := by
    rw [hcs4 .X26 rfl, kg k3 .X26, ← reg_of (r := .X1) hm3 (r' := .X26) rfl]
    exact congrArg EW.c1 kap3
  have hb4 := FB.body h hfb4
  have hwf5 := wf_fr h hb4
  refine exec_at (blk hp b44_in_code (by simp [b44])) e44 hwf5 rfl (match_fr h hb4)
    fun st5 hm5 hpc5 ↦ ?_
  have hfb5 := fb_blkW h hfb4 hm5 hwf5 rfl (by decide)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b44Offset + b44.length = k + NativeRustcVmArm.Vm.VerifyLayer.b45Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b44_next]] at hpc5
  have s5a : (⟨st5.data.regs.X0, st5.data.regs.X1⟩ : EW) = κ + tv.getD 1 0 := by
    rw [show st5.data.regs.X0 = _ from
        reg_val (r := .X0) hm5 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      show st5.data.regs.X1 = _ from
        reg_val (r := .X1) hm5 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)), q23, q25, q19, q26,
      UInt64.xor_comm (tv.getD 1 0).c0, UInt64.xor_comm (tv.getD 1 0).c1]
    rfl
  have s5b : (⟨st5.data.regs.X2, st5.data.regs.X3⟩ : EW) = tv.getD 2 0 := by
    rw [show st5.data.regs.X2 = _ from reg_of (r := .X2) hm5 (r' := .X20) rfl,
      show st5.data.regs.X3 = _ from reg_of (r := .X3) hm5 (r' := .X28) rfl, q20, q28]
  have s21 : st5.data.regs.getXReg .X21 = m4.regs.X0 := reg_of hm5 (r' := .X0) rfl
  have s29 : st5.data.regs.getXReg .X29 = m4.regs.X1 := reg_of hm5 (r' := .X1) rfl
  have s19 : st5.data.regs.getXReg .X19 = val.c1 :=
    reg_val hm5 rfl (ldF (FrameWords.get fw4 (o := 128) (by simp)))
  have w24 := Bus.wordAt_write (r := 0) (o := 24) hm5 rfl (by omega) (v := .reg .X20)
    (fun i hi ↦ by interval_cases i <;> rfl)
  have w16 := Bus.wordAt_write (r := 0) (o := 16) hm5 rfl (by omega) (v := .reg .X28)
    (fun i hi ↦ by interval_cases i <;> rfl)
  have w40 := Bus.wordAt_write (r := 0) (o := 40) hm5 rfl (by omega) (v := .reg .X23)
    (fun i hi ↦ by interval_cases i <;> rfl)
  have w32 := Bus.wordAt_write (r := 0) (o := 32) hm5 rfl (by omega) (v := .reg .X19)
    (fun i hi ↦ by interval_cases i <;> rfl)
  rw [ev_regU, UInt64.ofBitVec_toBitVec] at w24 w16 w40 w32
  rw [q20] at w24
  rw [q28] at w16
  rw [q23] at w40
  rw [q19] at w32
  have k5 : Bus.KeepRegs [.X22, .X24] m4 st5.data := Bus.KeepRegs.of_block hm5 rfl
  have fw5 : Bus.FrameWords st5.data.dmem (base m0 2032)
      ((16, (tv.getD 2 0).c1) :: (24, (tv.getD 2 0).c0) :: (32, (tv.getD 1 0).c1) ::
        (40, (tv.getD 1 0).c0) :: (48, (tv.getD 0 0).c1) :: (56, (tv.getD 0 0).c0) ::
        (64, m2.regs.getXReg .X1) :: (72, m2.regs.getXReg .X0) :: (112, val.c0) ::
        (128, val.c1) :: (144, UInt64.ofBitVec (sA m0 + BitVec.ofNat 64 107520)) :: eWords m0) :=
    fw_cons w16 (fw_cons w24 (fw_cons w32 (fw_cons w40
      (fw_blk hm5 hwf5 [48, 56, 64, 72, 112, 128, 144, 120, 136, 80, 88, 96] rfl (by decide)
        fw4))))
  have mu5 := NativeRustcVm.Layout.BufEWAt.of_same mu4
    (same_blk hm5 hwf5 (o' := 968) (n' := 264) (by omega) (by decide)) (by omega)
  have pt5 := ewsAt_same pt4 (same_blk hm5 hwf5 (o' := 1232) (n' := 480) (by omega)
    (by decide)) hpsz
  have eq5 := ewsAt_same eq4 (scr_blk h hm5 hwf5 (by decide) (o := 107520) (n := 32768)
    (by omega) (by omega)) (by rw [hesz])
  have ts5 := ts_frame h hm5 hwf5 (by decide) ts4
  refine fmul_call h hmul hfb5 hpc5 fun m6 hfb6 h60 h61 hcs6 hs6 hk6 ↦ ?_
  have B6 : (⟨m6.regs.X0, m6.regs.X1⟩ : EW) = (κ + tv.getD 1 0) * tv.getD 2 0 := by
    rw [h60, h61, s5a, s5b]
    rfl
  have fw6 := fwBel hs6 (hle [16, 24, 32, 40, 48, 56, 64, 72, 112, 128, 144, 120, 136, 80, 88,
    96] rfl (by decide)) fw5
  have mu6 := NativeRustcVm.Layout.BufEWAt.of_same mu5 (loc_bel g hs6 (o := 968) (n := 264)
    (by omega)) (by omega)
  have pt6 := ewsAt_same pt5 (loc_bel g hs6 (o := 1232) (n := 480) (by omega)) hpsz
  have eq6 := ewsAt_same eq5 (scr_bel g hs6 (o := 107520) (n := 32768) (by omega) (by omega))
    (by rw [hesz])
  have ts6 := ts_bel h hk6 hs6 ts5
  -- `b45`: the dot times the sum.
  refine Fr.runBlock hS N_ge rfl hfb6 (blk hp b45_in_code (by simp [b45])) e45 rfl rfl
    (by decide) (by decide) fun st7 hfb7 hd7 hm7 hpc7 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b45Offset + b45.length = k + NativeRustcVmArm.Vm.VerifyLayer.b46Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b45_next]] at hpc7
  have d7 : (⟨st7.data.regs.X0, st7.data.regs.X1⟩ : EW) =
      dot ((eqKernel lp).extract 0 LeanVM.Protocol.Verifier.keccakBits) c.weights := by
    rw [show st7.data.regs.X0 = _ from
        reg_val (r := .X0) hm7 rfl (ldF (FrameWords.get fw6 (o := 72)
          (v := m2.regs.getXReg .X0) (by simp))),
      show st7.data.regs.X1 = _ from
        reg_val (r := .X1) hm7 rfl (ldF (FrameWords.get fw6 (o := 64)
          (v := m2.regs.getXReg .X1) (by simp)))]
    exact D2
  have e7 : (⟨st7.data.regs.X2, st7.data.regs.X3⟩ : EW) =
      κ * tv.getD 0 0 + (κ + tv.getD 1 0) * tv.getD 2 0 := by
    rw [show st7.data.regs.X2 = _ from
        reg_val (r := .X2) hm7 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      show st7.data.regs.X3 = _ from
        reg_val (r := .X3) hm7 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      hcs6 .X21 rfl, hcs6 .X29 rfl, s21, s29, ← ew_mk_add,
      show (⟨m6.regs.getXReg .X0, m6.regs.getXReg .X1⟩ : EW) = _ from B6, A4, ew_add_comm']
  have k7 : Bus.KeepRegs [.X19, .X22, .X24] m6 st7.data := Bus.KeepRegs.of_block hm7 rfl
  refine fmul_call h hmul hfb7 hpc7 fun m8 hfb8 h80 h81 hcs8 hs8 hk8 ↦ ?_
  set R := dot ((eqKernel lp).extract 0 LeanVM.Protocol.Verifier.keccakBits) c.weights *
    (κ * tv.getD 0 0 + (κ + tv.getD 1 0) * tv.getD 2 0) with hR
  have R8 : (⟨m8.regs.X0, m8.regs.X1⟩ : EW) = R := by
    rw [h80, h81, d7, e7]
    rfl
  have hB : checkB c κ lp tv val = (R.c0 == val.c0 && R.c1 == val.c1) := by
    rw [checkB, ew_beq]
  rw [← hd7] at fw6 mu6 pt6 eq6 ts6
  have fw8 := fwBel hs8 (hle [16, 24, 32, 40, 48, 56, 64, 72, 112, 128, 144, 120, 136, 80, 88,
    96] rfl (by decide)) fw6
  have mu8 := NativeRustcVm.Layout.BufEWAt.of_same mu6 (loc_bel g hs8 (o := 968) (n := 264)
    (by omega)) (by omega)
  have pt8 := ewsAt_same pt6 (loc_bel g hs8 (o := 1232) (n := 480) (by omega)) hpsz
  have eq8 := ewsAt_same eq6 (scr_bel g hs8 (o := 107520) (n := 32768) (by omega) (by omega))
    (by rw [hesz])
  have ts8 := ts_bel h hk8 hs8 ts6
  have x19 : m8.regs.getXReg .X19 = val.c1 := by
    rw [hcs8 .X19 rfl, kg k7 .X19, hcs6 .X19 rfl]; exact s19
  -- `b46`: the low words.
  refine Fr.runBlock hS N_ge rfl hfb8 (blk hp b46_in_code (by simp [b46])) e46 rfl rfl
    (by decide) (by decide) fun st9 hfb9 hd9 hm9 hpc9 ↦ ?_
  have hc9 : SBool.eval (Env.ofMachine m8 [(base m0 2032, 2032)])
      (.not (.cmp .eq .W64 (.reg .X0) (.load 0 112 8))) = !(R.c0 == val.c0) := by
    rw [sb_not, sb_cmp, eq_apply, ev_regU,
      ldF (FrameWords.get fw8 (o := 112) (v := val.c0) (by simp)),
      dec_u64]
    exact congrArg (fun x ↦ !(x == val.c0)) (congrArg EW.c0 R8)
  by_cases e0 : (R.c0 == val.c0) = false
  · refine reject hp h ((pc_true hpc9 (by rw [hc9, e0]; rfl)).trans (label37 hp))
      (FB.body h hfb9) ?_
    rw [hrun, hB, e0]
    rfl
  have e0' : (R.c0 == val.c0) = true := by simpa using e0
  have hpc9' := pc_false hpc9 (by rw [hc9, e0']; rfl)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b46Offset + b46.length = k + NativeRustcVmArm.Vm.VerifyLayer.b47Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b46_next]] at hpc9'
  have k9 : Bus.KeepRegs [.X19, .X22, .X24] m8 st9.data := Bus.KeepRegs.of_block hm9 rfl
  -- `b47`: the high words.
  refine at_pc hpc9' (Fr.runBlock hS N_ge rfl hfb9 (blk hp b47_in_code (by simp [b47])) e47 rfl
    rfl (by decide) (by decide) fun st10 hfb10 hd10 hm10 hpc10 ↦ ?_)
  have hc10 : SBool.eval (Env.ofMachine st9.data [(base m0 2032, 2032)])
      (.not (.cmp .eq .W64 (.reg .X1) (.reg .X19))) = !(R.c1 == val.c1) := by
    rw [sb_not, sb_cmp, eq_apply, ev_regU, ev_regU, kg k9 .X19, x19,
      reg_of hm9 (r := .X1) (r' := .X1) rfl, dec_u64]
    exact congrArg (fun x ↦ !(x == val.c1)) (congrArg EW.c1 R8)
  by_cases e1 : (R.c1 == val.c1) = false
  · refine reject hp h ((pc_true hpc10 (by rw [hc10, e1]; rfl)).trans (label37 hp))
      (FB.body h hfb10) ?_
    rw [hrun, hB, e0', e1]
    rfl
  have e1' : (R.c1 == val.c1) = true := by simpa using e1
  have hpc10' := pc_false hpc10 (by rw [hc10, e1']; rfl)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b47Offset + b47.length = k + NativeRustcVmArm.Vm.VerifyLayer.b48Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b47_next]] at hpc10'
  have k10 : Bus.KeepRegs [.X22, .X24] st9.data st10.data := Bus.KeepRegs.of_block hm10 rfl
  have hd : st10.data.dmem = m8.dmem := hd10.trans hd9
  refine cont st10 hpc10' ⟨hfb10, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, hl.hps, hl.hlp, ?_⟩
  · show st10.data.regs.getXReg .X22 = _
    rw [kg k10 .X22, kg k9 .X22, hcs8 .X22 rfl, kg k7 .X22, hcs6 .X22 rfl, kg k5 .X22,
      hcs4 .X22 rfl, kg k3 .X22, hcs2 .X22 rfl, kg k1 .X22]
    exact hl.x22
  · show (st10.data.regs.getXReg .X24).toNat = _
    rw [kg k10 .X24, kg k9 .X24, hcs8 .X24 rfl, kg k7 .X24, hcs6 .X24 rfl, kg k5 .X24,
      hcs4 .X24 rfl, kg k3 .X24, hcs2 .X24 rfl, kg k1 .X24]
    exact hl.x24
  · rw [hd]
    refine fw_sub fw8 fun q hq ↦ ?_
    simp only [tailWords, eWords, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
    rcases hq with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;> simp [h']
  · rw [hd]; exact FrameWords.get fw8 (by simp)
  · rw [hd]; exact FrameWords.get fw8 (by simp [eWords])
  · rw [hd]; exact mu8
  · rw [hd]; exact pt8
  · rw [hd]; exact eq8
  · rw [hd]; exact ts8
  · rw [hrun, hB, e0', e1']
    rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
