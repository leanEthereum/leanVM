module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.KeccakGkr.VerifyLayer.FrontMask

/-!
# `verify_layer`'s front: the product's projection

The loop over the product's `47` coefficients (`ProjI j` at `.LVerifyLayer_4`, `k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset`): the
masked sum (`masked_run`), times coefficient `j` (`b4`, `EW::mul`), added into X21, X22 (`b5`);
after the last one, `.LVerifyLayer_12` (`proj_loop`). A leaf call from the front changing only the
bytes below the frame (`fleaf`, `fmul_call`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeVm.Model
open NativeRustcVmArm.Vm.VerifyLayer
open NativeRustcVm.Transcript (tstateBytes TStateAt DecArea)
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt claimBytes)
open NativeRustcVmArm.Bus.Gkr (Fr.runBlock at_pc)

@[expose] public section

/-- The registers the projection keeps. -/
abbrev regsP : List XReg := [.X19, .X23, .X24, .X25, .X26, .X27, .X28]

/-- **The projection's head** (`b6`), `j` coefficients summed. -/
structure ProjI [Labels] (m0 : MachineData) (c : KeccakClaimW) (p : Array EW) (j : Nat)
    (st : MachineData) : Prop where
  mi : MaskIn m0 c j st
  x28 : st.regs.X28.toBitVec = loc m0 152
  x29 : st.regs.X29.toNat = 16 * j
  acc : (⟨st.regs.X21, st.regs.X22⟩ : EW) = xs (projTerm c.mu p) j
  prod : NativeRustcVm.EWsAt st.dmem (loc m0 152) p.toList
  psz : p.size = 47

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- **A leaf call from the front**: its contract changes its stack only. -/
theorem fleaf (h : VerifyLayerPre a s c m0) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' : Nat} (hle : 2032 + N' ≤ verifyLayerStack)
    (hspec : Spec (Labels.label l) P Q)
    (hQ : ∀ m m', Q m m' →
      SameOutside m.dmem m'.dmem (InRange (stackBelow m N') N') ∧ Saved m m')
    {st : MachineState} {next : Int64} {R : MachineState → Prop}
    (hfr : FB m0 st.data) (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (cont : ∀ m2, FB m0 m2 → Q st.data m2 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (Bel m0) → Kept st.data.dmem m2.dmem →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  leaf_call h hle hspec hQ hfr hpc hP fun m2 hf2 hq hcs hs hk ↦
    cont m2 hf2 hq hcs (NativeRustcVm.SameOutside.mono hs fun _ hq' ↦ hq'.elim
      (bel_of (geo_of h) hfr.sp (by rw [stack_eq] at hle; omega)) False.elim) hk

/-- **`EW::mul`** from the front. -/
theorem fmul_call (h : VerifyLayerPre a s c m0) (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st : MachineState} {next : Int64} {R : MachineState → Prop} (hfr : FB m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel ∧ retOf st.data = next)
    (cont : ∀ m2, FB m0 m2 →
      m2.regs.X0 = (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩
        ⟨st.data.regs.X2, st.data.regs.X3⟩).c0 →
      m2.regs.X1 = (EW.mul ⟨st.data.regs.X0, st.data.regs.X1⟩
        ⟨st.data.regs.X2, st.data.regs.X3⟩).c1 →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      SameOutside st.data.dmem m2.dmem (Bel m0) → Kept st.data.dmem m2.dmem →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  fleaf h le_mul hmul (fun _ _ hq ↦ ⟨hq.2.2.1, hq.2.2.2⟩) hfr hpc
    (hfr.stackOk (pre_stack h) rfl le_mul) fun m2 hf2 hq hcs hs hk ↦
      cont m2 hf2 hq.1 hq.2.1 hcs hs hk

theorem label4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b6Offset) NativeRustcVmArm.Vm.VerifyLayer.label_4_at

theorem label12 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.VerifyLayer.label_12 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b15Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.VerifyLayer.b15Offset) NativeRustcVmArm.Vm.VerifyLayer.label_12_at

/-- **The projection's loop**, from coefficient `j` to `.LVerifyLayer_12`. -/
theorem proj_loop (hp : Placed code k) (h : VerifyLayerPre a s c m0)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {p : Array EW} {st0 : MachineData}
    {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b15Offset) → FB m0 st'.data →
      SameOutside st0.dmem st'.data.dmem (Bel m0) → Kept st0.dmem st'.data.dmem →
      Bus.KeepRegs regsP st0 st'.data →
      (⟨st'.data.regs.X21, st'.data.regs.X22⟩ : EW) = xs (projTerm c.mu p) 47 →
      Eventually (step1 Host.exe) R st') :
    ∀ r j (st : MachineState), 47 - j = r → st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset) →
      ProjI m0 c p j st.data → SameOutside st0.dmem st.data.dmem (Bel m0) →
      Kept st0.dmem st.data.dmem → Bus.KeepRegs regsP st0 st.data →
      Eventually (step1 Host.exe) R st := by
  have g := geo_of h
  have hS := pre_stack h
  intro r
  induction r with
  | zero => intro j st hr _ hi; have := hi.mi.lt; omega
  | succ r ih =>
    intro j st hr hpc hi hs0 hk0 hr0
    have hj := hi.mi.lt
    refine masked_run hp h hpc hi.mi fun st1 hpc1 hb1 hd1 hk1 h01 ↦ ?_
    -- `b4`: coefficient `j`.
    have hprod : NativeRustcVm.EWsAt st1.data.dmem (loc m0 152) p.toList := by
      rw [hd1]; exact hi.prod
    have hpj := ew_words hprod (i := j) (by rw [Array.length_toList, hi.psz]; exact hj)
    have e152 := g.fa (o := 152 + 16 * j) (by omega)
    have := g.hN; have := Geo.sp_lt m0
    have hwf : (Env.ofMachine st1.data [(loc m0 (152 + 16 * j), 16)]).WF := by
      refine Env.wf_of ⟨⟨fun i hi' ↦ ?_, by unfold NoWrap; rw [e152]; omega⟩, trivial⟩
        (List.pairwise_singleton _ _)
      rw [NativeRustcVm.addr_add_add]
      exact hb1.kept _ (frame_mapped hS (by decide) _ (by omega))
    have r28 : (st1.data.regs.getXReg .X28).toBitVec = loc m0 152 := by
      rw [kg hk1 .X28]; exact hi.x28
    have r29 : (st1.data.regs.getXReg .X29).toNat = 16 * j := by
      rw [kg hk1 .X29]; exact hi.x29
    have hm : Match (Env.ofMachine st1.data [(loc m0 (152 + 16 * j), 16)]) prodS st1.data :=
      match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
        ⟨by
          show (Sym.bin .add .W64 (.reg .X28) (.reg .X29)).eval
            (Env.ofMachine st1.data [(loc m0 (152 + 16 * j), 16)]) =
              loc m0 (152 + 16 * j) + BitVec.ofInt 64 0
          rw [ev_bin, regB .X28 r28, ev_regU, add_apply,
            show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, NativeRustcVm.addr_add_zero,
            bv_of_toNat r29, show loc m0 152 = base m0 2032 + BitVec.ofNat 64 152 from rfl,
            NativeRustcVm.addr_add_add],
          trivial⟩
    refine fb_run hb1 (blk hp b4_in_code (by simp [b4])) e4 hwf rfl hpc1 hm rfl rfl
      fun st2 hb2 hd2 hm2 hpc2 ↦ ?_
    have hp0 := hpj.1
    have hp1 := hpj.2
    rw [show loc m0 152 = base m0 2032 + BitVec.ofNat 64 152 from rfl,
      NativeRustcVm.addr_add_add] at hp0 hp1
    have e2 := reg_val (r := .X2) hm2 rfl (ldF (o := 0) (by
      rw [NativeRustcVm.addr_add_zero]; exact hp0))
    have e3 := reg_val (r := .X3) hm2 rfl (ldF (o := 8) (by
      rw [NativeRustcVm.addr_add_add, show 152 + 16 * j + 8 = 152 + (16 * j + 8) by omega]
      exact hp1))
    have k2 : Bus.KeepRegs [.X0, .X1, .X19, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28]
        st1.data st2.data := Bus.KeepRegs.of_block hm2 rfl
    rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b4Offset + b4.length = k + NativeRustcVmArm.Vm.VerifyLayer.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b4_next]] at hpc2
    refine fmul_call h hmul hb2 hpc2 fun m3 hb3 h30 h31 hcs3 hs3 hk3 ↦ ?_
    have q0 : st2.data.regs.X0 = st1.data.regs.X0 := kg k2 .X0
    have q1 : st2.data.regs.X1 = st1.data.regs.X1 := kg k2 .X1
    have q2 : st2.data.regs.X2 = _ := e2
    have q3 : st2.data.regs.X3 = _ := e3
    rw [q0, q1, q2, q3] at h30 h31
    -- `b5`: the sum; the last coefficient?
    have k3 : Bus.KeepRegs regsL st2.data m3 := Bus.KeepRegs.of_call hcs3 rfl
    refine Fr.runBlock hS N_ge rfl hb3 (blk hp b5_in_code (by simp [b5])) e5 rfl rfl
      (by decide) (by decide) fun st4 hb4 hd4 hm4 hpc4 ↦ ?_
    have k4 : Bus.KeepRegs [.X19, .X20, .X23, .X24, .X25, .X26, .X27, .X28, .X29] m3 st4.data :=
      Bus.KeepRegs.of_block hm4 rfl
    have r29' : (m3.regs.getXReg .X29).toNat = 16 * (j + 1) := by
      rw [kg k3 .X29]
      show (st2.data.regs.getXReg .X29).toBitVec.toNat = _
      rw [hm2.regs .X29 _ rfl, ev_bin, ev_regU, ev_lit, add_toNat, BitVec.toNat_ofNat,
        show ((st1.data.regs.getXReg .X29).toBitVec).toNat = 16 * j from r29]
      omega
    have r20' : (st4.data.regs.getXReg .X20).toNat = j + 1 := by
      rw [kg k4 .X20, kg k3 .X20]
      show (st2.data.regs.getXReg .X20).toBitVec.toNat = _
      rw [hm2.regs .X20 _ rfl, ev_bin, ev_regU, ev_lit, add_toNat, BitVec.toNat_ofNat,
        show ((st1.data.regs.getXReg .X20).toBitVec).toNat = j from
          (congrArg UInt64.toNat (kg hk1 .X20)).trans hi.mi.x20]
      omega
    have hsS : SameOutside st.data.dmem st4.data.dmem (Bel m0) := by
      rw [hd4]
      exact (NativeRustcVm.SameOutside.of_eq (hd2.trans hd1) _).trans' hs3
    have hkS : Kept st.data.dmem st4.data.dmem := by
      rw [hd4]
      exact fun q hq ↦ hk3 q (by rw [hd2, hd1]; exact hq)
    have hs4 : SameOutside st0.dmem st4.data.dmem (Bel m0) :=
      NativeRustcVm.SameOutside.trans' hs0 hsS
    have hk4 : Kept st0.dmem st4.data.dmem := fun q hq ↦ hkS q (hk0 q hq)
    have hkS' : Bus.KeepRegs regsP st.data st4.data := fun r hr ↦ by
      simp only [regsP, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (kg k4 _).trans ((kg k3 _).trans ((kg k2 _).trans (kg hk1 _)))
    have hkr : Bus.KeepRegs regsP st0 st4.data := hr0.trans hkS'
    have hacc : (⟨st4.data.regs.X21, st4.data.regs.X22⟩ : EW) =
        xs (projTerm c.mu p) (j + 1) := by
      show (⟨st4.data.regs.getXReg .X21, st4.data.regs.getXReg .X22⟩ : EW) = _
      rw [reg_val hm4 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)),
        reg_val hm4 rfl (eorSym (ev_regU _ _ _) (ev_regU _ _ _)), xs_succ, ← hi.acc,
        kg k3 .X21, kg k3 .X22, kg k2 .X21, kg k2 .X22, kg hk1 .X21, kg hk1 .X22]
      show (⟨m3.regs.X0 ^^^ st.data.regs.X21, m3.regs.X1 ^^^ st.data.regs.X22⟩ : EW) = _
      rw [h30, h31, UInt64.xor_comm _ st.data.regs.X21, UInt64.xor_comm _ st.data.regs.X22]
      show _ = (⟨st.data.regs.X21, st.data.regs.X22⟩ : EW) + maskedOf c.mu j * p.getD j 0
      rw [← h01, getD_toList]
      rfl
    have hc5 : (SBool.cmp .eq .W64 (.reg .X29) (.lit 752)).eval
        (Env.ofMachine m3 [(base m0 2032, 2032)]) = decide (j + 1 = 47) := by
      rw [sb_cmp, eq_apply, regN .X29 r29', litN 752]
      by_cases hl : j + 1 = 47
      · rw [decide_eq_true hl, decide_eq_true (by omega)]
      · rw [decide_eq_false hl, decide_eq_false (by omega)]
    by_cases hl : j + 1 = 47
    · refine cont st4 ((pc_true hpc4 (by rw [hc5, decide_eq_true hl])).trans (label12 hp)) hb4
        hs4 hk4 hkr ?_
      rw [hacc, hl]
    · have hpc4' := pc_false hpc4 (by rw [hc5, decide_eq_false hl])
      rw [show k + NativeRustcVmArm.Vm.VerifyLayer.b5Offset + b5.length = k + NativeRustcVmArm.Vm.VerifyLayer.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyLayer.b5_next]] at hpc4'
      have hmi := hi.mi
      refine ih (j + 1) st4 (by omega) hpc4' ⟨⟨hb4, by omega, ?_, ?_, r20', ?_, ?_, ?_, ?_, ?_⟩,
        ?_, ?_, hacc, ?_, hi.psz⟩ hs4 hk4 hkr
      · exact (congrArg UInt64.toNat (kg hkS' .X25)).trans hmi.x25
      · exact (congrArg UInt64.toNat (kg hkS' .X23)).trans hmi.x23
      · exact (congrArg UInt64.toBitVec (kg hkS' .X24)).trans hmi.x24
      · exact (congrArg UInt64.toBitVec (kg hkS' .X26)).trans hmi.x26
      · exact (congrArg UInt64.toBitVec (kg hkS' .X19)).trans hmi.x19
      · exact (congrArg UInt64.toNat (kg hkS' .X27)).trans hmi.x27
      · exact NativeRustcVm.Layout.WordAt.of_same hmi.f144 (loc_bel g hsS (o := 144) (n := 8)
          (by omega)) (Nat.le_refl _)
      · exact (congrArg UInt64.toBitVec (kg hkS' .X28)).trans hi.x28
      · exact (congrArg UInt64.toNat (kg k4 .X29)).trans r29'
      · exact ewsAt_same hi.prod (loc_bel g hsS (o := 152) (n := 752) (by omega))
          (by rw [Array.length_toList, hi.psz])

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
