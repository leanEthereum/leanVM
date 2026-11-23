module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontRC
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontG

/-!
# `verify_layer`'s front: the first check, the grind, `s`

From `b21` (`k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset`, `AtJ`): ι's two terms (`EW::mul`), the instance weights' sum (`sum_e`),
ι times it, the comparison with the claim's value (`b25`, `b26`); the grind of
`grindingBits 46` bits (`bit_length`, `grind`), `s` (`squeeze`), to `b31` (`k + NativeRustcVmArm.Vm.VerifyLayer.b31Offset`, `AtH`,
`check_run`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

@[expose] public section

/-- The front's memory past the segment kernel: the frame's words, the product. -/
structure CM (m0 : MachineData) (p : Array EW) (d : DataMem) : Prop where
  fw : Bus.FrameWords d (base m0 2032) (iWords m0)
  prod : NativeRustcVm.EWsAt d (loc m0 152) p.toList
  psz : p.size = 47

/-- **After `s`** (`b31`, `k + NativeRustcVmArm.Vm.VerifyLayer.b31Offset`): the challenge `ch` in X0, X1, the state `s2`. -/
structure AtH [Labels] (m0 : MachineData) (a : DecArea) (p : Array EW) (ch : EW) (s2 : TState)
    (st : MachineData) : Prop where
  fb : FB m0 st
  cm : CM m0 p st.dmem
  ts : TStateAt st.dmem (tA m0) a s2
  x0 : st.regs.X0 = ch.c0
  x1 : st.regs.X1 = ch.c1
  x20 : st.regs.X20 = m0.regs.X3
  x22 : st.regs.X22 = m0.regs.X0

end

public section

theorem iWords_le (m0 : MachineData) : ∀ q ∈ iWords m0, q.1 + 8 ≤ 152 := by
  intro q hq
  simp only [iWords, pWords, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ew_beq (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  cases x; cases y; rfl

theorem dec_u64 (x y : UInt64) : decide (x.toBitVec.toNat = y.toBitVec.toNat) = (x == y) := by
  by_cases e' : x = y
  · subst e'; simp
  · have h1 : ¬(x.toBitVec.toNat = y.toBitVec.toNat) := fun h' ↦
      e' (UInt64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq h'))
    rw [decide_eq_false h1]
    exact (beq_eq_false_iff_ne.mpr e').symm

/-- Four accumulators as the code adds them. -/
theorem bits_mk (A0 A1 A2 A3 : EW) :
    (⟨A3.c0 ^^^ A2.c0 ^^^ (A1.c0 ^^^ A0.c0), A3.c1 ^^^ A2.c1 ^^^ (A1.c1 ^^^ A0.c1)⟩ : EW) =
      A0 + A1 + (A2 + A3) := by
  show A3 + A2 + (A1 + A0) = _
  ac_rfl

theorem ew_eta (x : EW) : (⟨x.c0, x.c1⟩ : EW) = x := rfl

variable {m0 : MachineData}

theorem CM.bel (g : Geo m0) {p : Array EW} {d d' : DataMem} (hc : CM m0 p d)
    (hs : SameOutside d d' (Bel m0)) : CM m0 p d' := by
  have := g.hN; have := Geo.sp_lt m0
  exact ⟨FrameWords.of_same hc.fw (same_bel g hs (x := base m0 2032) (n := 2032)
      (by rw [g.bN]; omega) (by rw [g.bN]; omega))
      (fun q hq ↦ by have := iWords_le m0 q hq; omega),
    ewsAt_same hc.prod (loc_bel g hs (o := 152) (n := 752) (by omega))
      (by rw [Array.length_toList, hc.psz]),
    hc.psz⟩

theorem CM.call [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW}
    (h : VerifyLayerPre a s c m0) {p : Array EW} {m m' : MachineData}
    (hsp : m.regs.SP.toBitVec = base m0 2032) {N' : Nat} (hle : N' ≤ 1616)
    (hs : SameOutside m.dmem m'.dmem fun q ↦
      InRange (stackBelow m N') N' q ∨ InRange (tA m0) tstateBytes q)
    (hc : CM m0 p m.dmem) : CM m0 p m'.dmem := by
  have hfr := fr_same h hsp hle hs
  exact ⟨FrameWords.of_same hc.fw hfr (fun q hq ↦ by have := iWords_le m0 q hq; omega),
    ewsAt_same hc.prod (hfr.sub (o := 152) (k := 752) (by omega))
      (by rw [Array.length_toList, hc.psz]), hc.psz⟩

/-- A slice holding `xs`. -/
theorem slice_eq {m : MachineData} {a n : UInt64} {q : BitVec 64} {xs : List EW}
    (h : NativeRustcVm.EWsAt m.dmem q xs) (ha : a.toBitVec = q) (hn : n.toNat = xs.length) :
    slice m a n = xs.toArray := by
  unfold slice
  rw [ha, hn]
  exact congrArg List.toArray (NativeRustcVm.ewsOf_of_ewsAt h)

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **The first check, the grind and `s`**, from `b21` to `b31`. -/
theorem check_run (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hsum : Spec (label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost)
    (hbl : Spec (label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ s, Spec (label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    {p : Array EW} {s1 : TState} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset))
    (hj : AtJ m0 a c p s1 st.data)
    (hrun : runL s c m0 = rest1 m0.regs.X1.toNat m0.regs.X2.toNat c p s1)
    (cont : ∀ (st' : MachineState) (ch : EW) (s2 : TState), st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b31Offset) →
      AtH m0 a p ch s2 st'.data → runL s c m0 = rest3 c p ch s2 →
      Eventually (step1 Host.exe) (Goal a s c m0) st') :
    Eventually (step1 Host.exe) (Goal a s c m0) st := by
  have hS := pre_stack h
  have g := geo_of h
  have := g.hN; have := Geo.sp_lt m0
  have cm0 : CM m0 p st.data.dmem := ⟨hj.fw, hj.prod, hj.psz⟩
  -- `b21`: the first segment's term.
  refine at_pc hpc (Fr.runBlock hS N_ge rfl hj.fb (blk hp b21_in_code (by simp [b21])) e21 rfl
    rfl (by decide) (by decide) fun st1 hfb1 hd1 hm1 hpc1 ↦ ?_)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b21Offset + b21.length = k + NativeRustcVmArm.Vm.VerifyLayer.b22Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b21_next]] at hpc1
  have a1 : (⟨st1.data.regs.X0, st1.data.regs.X1⟩ : EW) = (segK m0 c).getD 0 0 := by
    rw [show st1.data.regs.X0 = _ from reg_val (r := .X0) hm1 rfl (ldF hj.s0a),
      show st1.data.regs.X1 = _ from reg_val (r := .X1) hm1 rfl (ldF hj.s0b), ew_eta]
  have b1 : (⟨st1.data.regs.X2, st1.data.regs.X3⟩ : EW) = bitsOf c.weights (wA m0) := by
    rw [show st1.data.regs.X2 = _ from
        reg_val (r := .X2) hm1 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      show st1.data.regs.X3 = _ from
        reg_val (r := .X3) hm1 rfl (eorSym (ldF hj.w40) (ldF hj.w48)),
      show st.data.regs.getXReg .X11 = _ from hj.x11,
      show st.data.regs.getXReg .X10 = _ from hj.x10, bits_mk, bits_four]
  have k1 : Bus.KeepRegs [.X21, .X22, .X25] st.data st1.data := Bus.KeepRegs.of_block hm1 rfl
  have r19 : st1.data.regs.getXReg .X19 =
      (bAcc c (wB m0) 3 16).c0 ^^^ (bAcc c (wB m0) 2 16).c0 := by
    rw [reg_val hm1 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _))]
    rw [show st.data.regs.getXReg .X19 = _ from congrArg EW.c0 hj.b3,
      show st.data.regs.getXReg .X7 = _ from congrArg EW.c0 hj.b2]
  have r20 : st1.data.regs.getXReg .X20 =
      (bAcc c (wB m0) 1 16).c0 ^^^ (bAcc c (wB m0) 0 16).c0 := by
    rw [reg_val hm1 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _))]
    rw [show st.data.regs.getXReg .X6 = _ from congrArg EW.c0 hj.b1,
      show st.data.regs.getXReg .X5 = _ from congrArg EW.c0 hj.b0]
  have r23 : st1.data.regs.getXReg .X23 =
      (bAcc c (wB m0) 1 16).c1 ^^^ (bAcc c (wB m0) 0 16).c1 := by
    rw [reg_val hm1 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _))]
    rw [show st.data.regs.getXReg .X18 = _ from congrArg EW.c1 hj.b1,
      show st.data.regs.getXReg .X17 = _ from congrArg EW.c1 hj.b0]
  have r26 : st1.data.regs.getXReg .X26 =
      (bAcc c (wB m0) 3 16).c1 ^^^ (bAcc c (wB m0) 2 16).c1 := by
    rw [reg_val hm1 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _))]
    rw [show st.data.regs.getXReg .X3 = _ from congrArg EW.c1 hj.b3,
      show st.data.regs.getXReg .X2 = _ from congrArg EW.c1 hj.b2]
  refine fmul_call h hmul hfb1 hpc1 fun m2 hfb2 h20 h21 hcs2 hs2 hk2 ↦ ?_
  have T1 : (⟨m2.regs.X0, m2.regs.X1⟩ : EW) =
      (segK m0 c).getD 0 0 * bitsOf c.weights (wA m0) := by
    rw [h20, h21, a1, b1]
    rfl
  rw [← hd1] at cm0
  have cm2 := cm0.bel g hs2
  have keep2 : ∀ {o : Nat} {v : UInt64}, o + 8 ≤ 2032 →
      NativeRustcVm.WordAt st.data.dmem (loc m0 o) v → NativeRustcVm.WordAt m2.dmem (loc m0 o) v :=
    fun ho hw ↦ same_word (by rw [hd1]; exact hw) (loc_bel g hs2 ho)
  -- `b22`: the second segment's term.
  refine Fr.runBlock hS N_ge rfl hfb2 (blk hp b22_in_code (by simp [b22])) e22 rfl rfl
    (by decide) (by decide) fun st3 hfb3 hd3 hm3 hpc3 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b22Offset + b22.length = k + NativeRustcVmArm.Vm.VerifyLayer.b23Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b22_next]] at hpc3
  have a3 : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) = (segK m0 c).getD 1 0 := by
    rw [show st3.data.regs.X0 = _ from
        reg_val (r := .X0) hm3 rfl (ldF (keep2 (by omega) hj.s1a)),
      show st3.data.regs.X1 = _ from
        reg_val (r := .X1) hm3 rfl (ldF (keep2 (by omega) hj.s1b)), ew_eta]
  have b3 : (⟨st3.data.regs.X2, st3.data.regs.X3⟩ : EW) = bitsOf c.weights (wB m0) := by
    rw [show st3.data.regs.X2 = _ from
        reg_val (r := .X2) hm3 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      show st3.data.regs.X3 = _ from
        reg_val (r := .X3) hm3 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      hcs2 .X19 rfl, hcs2 .X20 rfl, hcs2 .X26 rfl, hcs2 .X23 rfl, r19, r20, r26, r23, bits_mk,
      bits_four]
  have r24 : st3.data.regs.getXReg .X24 = m2.regs.X0 := reg_of hm3 (r' := .X0) rfl
  have r29 : st3.data.regs.getXReg .X29 = m2.regs.X1 := reg_of hm3 (r' := .X1) rfl
  have k3 : Bus.KeepRegs [.X21, .X22, .X25] m2 st3.data := Bus.KeepRegs.of_block hm3 rfl
  refine fmul_call h hmul hfb3 hpc3 fun m4 hfb4 h40 h41 hcs4 hs4 hk4 ↦ ?_
  have T2 : (⟨m4.regs.X0, m4.regs.X1⟩ : EW) =
      (segK m0 c).getD 1 0 * bitsOf c.weights (wB m0) := by
    rw [h40, h41, a3, b3]
    rfl
  rw [← hd3] at cm2
  have cm4 := cm2.bel g hs4
  -- `b23`: the instance weights' sum.
  refine Fr.runBlock hS N_ge rfl hfb4 (blk hp b23_in_code (by simp [b23])) e23 rfl rfl
    (by decide) (by decide) fun st5 hfb5 hd5 hm5 hpc5 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b23Offset + b23.length = k + NativeRustcVmArm.Vm.VerifyLayer.b24Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b23_next]] at hpc5
  have hc5 := claimAt_fb h hfb5
  obtain ⟨-, hmu16⟩ := mu_len hc5
  have hmuw : NativeRustcVm.EWsAt st5.data.dmem (cA m0 + BitVec.ofNat 64 24) c.mu.toList := by
    have := hc5.2.1.2.2
    rwa [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, NativeRustcVm.KeccakGkr.off,
      NativeRustcVm.KeccakGkr.muOff, NativeRustcVm.addr_add_add] at this
  have x50 : st5.data.regs.X0.toBitVec = cA m0 + BitVec.ofNat 64 24 := by
    show (st5.data.regs.getXReg .X0).toBitVec = _
    rw [hm5.regs .X0 _ rfl]
    exact ldF (FrameWords.get cm4.fw (o := 144) (by simp [iWords, pWords]))
  have x51 : st5.data.regs.X1.toNat = c.mu.size := by
    show (st5.data.regs.getXReg .X1).toNat = _
    rw [reg_of hm5 (r' := .X25) rfl, hcs4 .X25 rfl, kg k3 .X25, hcs2 .X25 rfl, kg k1 .X25]
    exact hj.x25
  have r27 : st5.data.regs.getXReg .X27 = m4.regs.X0 := reg_of hm5 (r' := .X0) rfl
  have r28 : st5.data.regs.getXReg .X28 = m4.regs.X1 := reg_of hm5 (r' := .X1) rfl
  have k5 : Bus.KeepRegs [.X21, .X22, .X24, .X29] m4 st5.data := Bus.KeepRegs.of_block hm5 rfl
  refine fleaf h le_sum hsum (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ hq' ↦
      hq'.elim (fun h' ↦ absurd h' (Bus.not_inRange_zero _ _)) id, hq.2.2⟩) hfb5 hpc5
    ⟨by rw [x51]; exact hmu16,
      by rw [x50, x51]; exact readable_cl h hfb5 (by omega) (by omega)⟩
    fun m6 hfb6 hq6 hcs6 hs6 hk6 ↦ ?_
  have S6 : (⟨m6.regs.X0, m6.regs.X1⟩ : EW) = sumE c.mu := by
    have e := hq6.1
    rw [slice_eq hmuw x50 (by rw [Array.length_toList]; exact x51), Array.toArray_toList] at e
    exact e
  rw [← hd5] at cm4
  have cm6 := cm4.bel g hs6
  -- `b24`: ι times the sum.
  refine Fr.runBlock hS N_ge rfl hfb6 (blk hp b24_in_code (by simp [b24])) e24 rfl rfl
    (by decide) (by decide) fun st7 hfb7 hd7 hm7 hpc7 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b24Offset + b24.length = k + NativeRustcVmArm.Vm.VerifyLayer.b25Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b24_next]] at hpc7
  have a7 : (⟨st7.data.regs.X0, st7.data.regs.X1⟩ : EW) = iotaOf m0.regs.X1.toNat
      m0.regs.X2.toNat c := by
    rw [show st7.data.regs.X0 = _ from
        reg_val (r := .X0) hm7 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      show st7.data.regs.X1 = _ from
        reg_val (r := .X1) hm7 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
      hcs6 .X27 rfl, hcs6 .X28 rfl, hcs6 .X24 rfl, hcs6 .X29 rfl, r27, r28, kg k5 .X24,
      kg k5 .X29, hcs4 .X24 rfl, hcs4 .X29 rfl, r24, r29, ← ew_mk_add, T1, T2, iota_eq,
      ew_add_comm']
  have b7 : (⟨st7.data.regs.X2, st7.data.regs.X3⟩ : EW) = sumE c.mu := by
    rw [show st7.data.regs.X2 = _ from reg_of (r := .X2) hm7 (r' := .X0) rfl,
      show st7.data.regs.X3 = _ from reg_of (r := .X3) hm7 (r' := .X1) rfl]
    exact S6
  have k7 : Bus.KeepRegs [.X21, .X22] m6 st7.data := Bus.KeepRegs.of_block hm7 rfl
  refine fmul_call h hmul hfb7 hpc7 fun m8 hfb8 h80 h81 hcs8 hs8 hk8 ↦ ?_
  have T8 : (⟨m8.regs.X0, m8.regs.X1⟩ : EW) =
      iotaOf m0.regs.X1.toNat m0.regs.X2.toNat c * sumE c.mu := by
    rw [h80, h81, a7, b7]
    rfl
  have P8 : (⟨m8.regs.X21, m8.regs.X22⟩ : EW) = projectedOf c.mu p := by
    show (⟨m8.regs.getXReg .X21, m8.regs.getXReg .X22⟩ : EW) = _
    rw [hcs8 .X21 rfl, hcs8 .X22 rfl, kg k7 .X21, kg k7 .X22, hcs6 .X21 rfl, hcs6 .X22 rfl,
      kg k5 .X21, kg k5 .X22, hcs4 .X21 rfl, hcs4 .X22 rfl, kg k3 .X21, kg k3 .X22,
      hcs2 .X21 rfl, hcs2 .X22 rfl, kg k1 .X21, kg k1 .X22]
    exact hj.acc
  rw [← hd7] at cm6
  have cm8 := cm6.bel g hs8
  have ts8 : TStateAt m8.dmem (tA m0) a s1 := by
    have t2 := ts_bel h hk2 hs2 (by rw [hd1]; exact hj.ts)
    have t4 := ts_bel h hk4 hs4 (by rw [hd3]; exact t2)
    have t6 := ts_bel h hk6 hs6 (by rw [hd5]; exact t4)
    exact ts_bel h hk8 hs8 (by rw [hd7]; exact t6)
  -- the claimed value against the projection plus ι's part.
  set V := projectedOf c.mu p + iotaOf m0.regs.X1.toNat m0.regs.X2.toNat c * sumE c.mu with hV
  have v0 : m8.regs.X0 ^^^ m8.regs.X21 = V.c0 := by
    rw [hV, ← P8, ← T8]
    exact UInt64.xor_comm _ _
  have v1 : m8.regs.X1 ^^^ m8.regs.X22 = V.c1 := by
    rw [hV, ← P8, ← T8]
    exact UInt64.xor_comm _ _
  have hA : checkA m0.regs.X1.toNat m0.regs.X2.toNat c p = (V.c0 == c.value.c0 &&
      V.c1 == c.value.c1) := by
    rw [checkA, ew_beq]
  -- `b25`: the low words.
  have hb8 := FB.body h hfb8
  have hw136 : NativeRustcVm.WordAt m8.dmem (base m0 2032 + BitVec.ofNat 64 136) m0.regs.X3 :=
    FrameWords.get cm8.fw (by simp [iWords, pWords])
  have hc8 := claimAt_fb h hfb8
  have hval := NativeRustcVm.ewAt_iff.mp hc8.1
  have hwf9 := wf_claim h hb8
  refine exec_at (blk hp b25_in_code (by simp [b25])) e25 hwf9 rfl (match_claimF h hb8 hw136)
    fun st9 hm9 hpc9 ↦ ?_
  have hfb9 := fb_blkW h hfb8 hm9 hwf9 rfl (by decide)
  have hd9 : st9.data.dmem = m8.dmem := hm9.dmem_eq hwf9 rfl
  have l0 : NativeRustcVm.WordAt m8.dmem (cA m0 + BitVec.ofNat 64 0) c.value.c0 := by
    rw [NativeRustcVm.addr_add_zero]; exact hval.1
  have hc9 : SBool.eval (Env.ofMachine m8 [(base m0 2032, 2032), (cA m0, 768)])
      (.not (.cmp .eq .W64 (.bin .eor .W64 (.reg .X0) (.reg .X21)) (.load 1 0 8))) =
        !(V.c0 == c.value.c0) := by
    rw [sb_not, sb_cmp, eq_apply, eorSym (ev_regU _ _ _) (ev_regU _ _ _), ld1 l0, dec_u64]
    exact congrArg (fun b ↦ !(b == c.value.c0)) v0
  have x90 : st9.data.regs.getXReg .X0 = 0 := reg_val hm9 rfl (x := 0) (by rw [ev_lit]; rfl)
  by_cases e0 : (V.c0 == c.value.c0) = false
  · have hpc9' := (pc_true hpc9 (by rw [hc9, e0]; rfl)).trans (label38 hp)
    have hnone : runL s c m0 = none := by
      rw [hrun]; unfold rest1; rw [hA, e0]; rfl
    refine exit hp h hpc9' (FB.body h hfb9) ?_ fun c' s' he ↦ by rw [hnone] at he; cases he
    rw [hnone]
    exact x90
  have e0' : (V.c0 == c.value.c0) = true := by simpa using e0
  have hpc9' := pc_false hpc9 (by rw [hc9, e0']; rfl)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b25Offset + b25.length = k + NativeRustcVmArm.Vm.VerifyLayer.b26Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b25_next]] at hpc9'
  -- `b26`: the high words.
  have hwf10 : (Env.ofMachine st9.data [(cA m0, 16)]).WF := by
    have pg := pgeo_of h
    have := g.hc
    exact Env.wf_of ⟨⟨fun i hi ↦ hfb9.kept _ (pg.cm i (by omega)), by
      unfold NoWrap; dsimp only; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm10 : Match (Env.ofMachine st9.data [(cA m0, 16)]) valueS st9.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (st9.data.regs.getXReg .X20).toBitVec = cA m0 + BitVec.ofInt 64 0
        rw [hm9.regs .X20 _ rfl, ld0 hw136, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
          NativeRustcVm.addr_add_zero], trivial⟩ trivial trivial trivial
  refine fb_run hfb9 (blk hp b26_in_code (by simp [b26])) e26 hwf10 rfl hpc9' hm10 rfl rfl
    fun st10 hfb10 hd10 hm10' hpc10 ↦ ?_
  have l8 : NativeRustcVm.WordAt st9.data.dmem (cA m0 + BitVec.ofNat 64 8) c.value.c1 := by
    rw [hd9]; exact hval.2
  have hc10 : SBool.eval (Env.ofMachine st9.data [(cA m0, 16)])
      (.not (.cmp .eq .W64 (.bin .eor .W64 (.reg .X1) (.reg .X22)) (.load 0 8 8))) =
        !(V.c1 == c.value.c1) := by
    rw [sb_not, sb_cmp, eq_apply, eorSym (ev_regU _ _ _) (ev_regU _ _ _), ldF l8, dec_u64,
      reg_of hm9 (r := .X1) (r' := .X1) rfl, reg_of hm9 (r := .X22) (r' := .X22) rfl]
    exact congrArg (fun b ↦ !(b == c.value.c1)) v1
  have x100 : st10.data.regs.getXReg .X0 = 0 := by
    rw [reg_of hm10' (r := .X0) (r' := .X0) rfl]; exact x90
  by_cases e1 : (V.c1 == c.value.c1) = false
  · have hpc10' := (pc_true hpc10 (by rw [hc10, e1]; rfl)).trans (label38 hp)
    have hnone : runL s c m0 = none := by
      rw [hrun]; unfold rest1; rw [hA, e0', e1]; rfl
    refine exit hp h hpc10' (FB.body h hfb10) ?_ fun c' s' he ↦ by rw [hnone] at he; cases he
    rw [hnone]
    exact x100
  have e1' : (V.c1 == c.value.c1) = true := by simpa using e1
  have hAt : checkA m0.regs.X1.toNat m0.regs.X2.toNat c p = true := by rw [hA, e0', e1']; rfl
  have hpc10' := pc_false hpc10 (by rw [hc10, e1']; rfl)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b26Offset + b26.length = k + NativeRustcVmArm.Vm.VerifyLayer.b27Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b26_next]] at hpc10'
  have x20 : (st10.data.regs.getXReg .X20).toBitVec = cA m0 := by
    rw [hm10'.regs .X20 _ rfl, ev_ptr, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
      NativeRustcVm.addr_add_zero]
    rfl
  have cm10 : CM m0 p st10.data.dmem := by rw [hd10, hd9]; exact cm8
  have ts10 : TStateAt st10.data.dmem (tA m0) a s1 := by rw [hd10, hd9]; exact ts8
  -- `b27`: `bit_length(45)`.
  refine at_pc hpc10' (Fr.runBlock hS N_ge rfl hfb10 (blk hp b27_in_code (by simp [b27])) e27
    rfl rfl (by decide) (by decide) fun st11 hfb11 hd11 hm11 hpc11 ↦ ?_)
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b27Offset + b27.length = k + NativeRustcVmArm.Vm.VerifyLayer.b28Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b27_next]] at hpc11
  have k11 : Bus.KeepRegs [.X20] st10.data st11.data := Bus.KeepRegs.of_block hm11 rfl
  refine fleaf h le_bl hbl (fun _ _ hq ↦ ⟨hq.2.1, hq.2.2⟩) hfb11 hpc11 trivial
    fun m12 hfb12 hq12 hcs12 hs12 hk12 ↦ ?_
  have e12 : m12.regs.X0.toNat = 6 := by
    have h1 : st11.data.regs.X0.toNat = 45 := congrArg BitVec.toNat (hm11.regs .X0 _ rfl)
    rw [hq12.1, h1]
    rfl
  rw [← hd11] at cm10 ts10
  have cm12 := cm10.bel g hs12
  have ts12 := ts_bel h hk12 hs12 ts10
  -- `b28`: `grind(t, 3)`.
  refine Fr.runBlock hS N_ge rfl hfb12 (blk hp b28_in_code (by simp [b28])) e28 rfl rfl
    (by decide) (by decide) fun st13 hfb13 hd13 hm13 hpc13 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b28Offset + b28.length = k + NativeRustcVmArm.Vm.VerifyLayer.b29Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b28_next]] at hpc13
  have w104 : NativeRustcVm.WordAt m12.dmem (base m0 2032 + BitVec.ofNat 64 104) m0.regs.X0 :=
    FrameWords.get cm12.fw (by simp [iWords, pWords])
  have g0 : st13.data.regs.X0 = m0.regs.X0 := reg_val (r := .X0) hm13 rfl (ldF w104)
  have g22 : st13.data.regs.getXReg .X22 = m0.regs.X0 := reg_val hm13 rfl (ldF w104)
  have g1 : grindBits st13.data = 3 := by
    have hx : (Env.ofMachine m12 [(base m0 2032, 2032)]).regs .X0 = BitVec.ofNat 64 6 :=
      BitVec.eq_of_toNat_eq (by
        rw [show (Env.ofMachine m12 [(base m0 2032, 2032)]).regs .X0 =
          m12.regs.X0.toBitVec from rfl]; exact e12)
    unfold grindBits
    rw [show st13.data.regs.X1.toNat = (st13.data.regs.getXReg .X1).toBitVec.toNat from rfl,
      hm13.regs .X1 _ rfl, csel3 _ (by decide) hx]
    rfl
  have k13 : Bus.KeepRegs [.X20] m12 st13.data := Bus.KeepRegs.of_block hm13 rfl
  refine grind_call h hgr hfb13 hpc13 g0 g1 (by decide) (by rw [hd13]; exact ts12)
    fun m14 hfb14 hx14 hnext14 hcs14 hs14 ↦ ?_
  rw [← hd13] at cm12
  have cm14 := CM.call h hfb13.sp (by decide) hs14 cm12
  -- `b29`: the grind's result.
  refine Fr.runBlock hS N_ge rfl hfb14 (blk hp b29_in_code (by simp [b29])) e29 rfl rfl
    (by decide) (by decide) fun st15 hfb15 hd15 hm15 hpc15 ↦ ?_
  have hc15 : SBool.eval (Env.ofMachine m14 [(base m0 2032, 2032)])
      (.cmp .eq .W32 (.reg .X0) (.lit 0)) = !((grind 3).run s1).isSome := by
    show CmpOp.eq.apply .W32 (m14.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 0) = _
    rw [show m14.regs.getXReg .X0 = m14.regs.X0 from rfl, hx14, okw_eq0]
  have x15 : st15.data.regs.getXReg .X0 = m14.regs.X0 := reg_of hm15 (r' := .X0) rfl
  have k15 : Bus.KeepRegs [.X20, .X22] m14 st15.data := Bus.KeepRegs.of_block hm15 rfl
  cases hr : (grind 3).run s1 with
  | none =>
    have hpc15' := (pc_true hpc15 (by rw [hc15, hr]; rfl)).trans (label38 hp)
    have hnone : runL s c m0 = none := by
      rw [hrun]; unfold rest1; rw [hAt, grindingBits_46, hr]; rfl
    refine exit hp h hpc15' (FB.body h hfb15) ?_ fun c' s' he ↦ by rw [hnone] at he; cases he
    rw [hnone]
    show st15.data.regs.getXReg .X0 = _
    rw [x15, hx14, hr]
    rfl
  | some w =>
    have hpc15' := pc_false hpc15 (by rw [hc15, hr]; rfl)
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b29Offset + b29.length = k + NativeRustcVmArm.Vm.VerifyLayer.b30Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b29_next]] at hpc15'
    have ts14 : TStateAt m14.dmem (tA m0) a w.2 := hnext14 w.1 w.2 (by rw [hr])
    -- `b30`: `s`.
    refine at_pc hpc15' (Fr.runBlock hS N_ge rfl hfb15 (blk hp b30_in_code (by simp [b30])) e30
      rfl rfl (by decide) (by decide) fun st16 hfb16 hd16 hm16 hpc16 ↦ ?_)
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b30Offset + b30.length = k + NativeRustcVmArm.Vm.VerifyLayer.b31Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b30_next]] at hpc16
    have k16 : Bus.KeepRegs [.X20, .X22] st15.data st16.data := Bus.KeepRegs.of_block hm16 rfl
    have r22 : st15.data.regs.getXReg .X22 = m0.regs.X0 := by
      rw [kg k15 .X22, hcs14 .X22 rfl]; exact g22
    have r20 : (st15.data.regs.getXReg .X20).toBitVec = cA m0 := by
      rw [kg k15 .X20, hcs14 .X20 rfl, kg k13 .X20, hcs12 .X20 rfl, kg k11 .X20]; exact x20
    refine sq_call h hsq hfb16 hpc16 ((reg_of hm16 (r := .X0) (r' := .X22) rfl).trans r22)
      (by rw [hd16, hd15]; exact ts14) fun m17 hfb17 hts17 hx170 hx171 hcs17 hs17 ↦ ?_
    rw [← hd15, ← hd16] at cm14
    refine cont ⟨m17, _⟩ (sqS w.2).1 (sqS w.2).2 rfl
      ⟨hfb17, CM.call h hfb16.sp (by decide) hs17 cm14,
      hts17, hx170, hx171, ?_, ?_⟩ ?_
    · apply UInt64.toBitVec_inj.mp
      show (m17.regs.getXReg .X20).toBitVec = _
      rw [hcs17 .X20 rfl, kg k16 .X20]; exact r20
    · show m17.regs.getXReg .X22 = _
      rw [hcs17 .X22 rfl, kg k16 .X22]; exact r22
    · rw [hrun]; unfold rest1; rw [hAt, grindingBits_46, hr]; rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
