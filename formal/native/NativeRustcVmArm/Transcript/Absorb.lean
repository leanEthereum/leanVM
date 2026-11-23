module

public import NativeRustcVmArm.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmArm.Transcript.Absorb.Tail

/-!
# `SpongeW::absorb` on AArch64

**`absorb_spec`**: the sponge at X0 becomes `sp.absorb ⟨X1, X2⟩ X3`, given `duplex`'s contract. The
prologue (`b0`) saves five registers in a 48-byte frame and compares the queue's count with `4`;
below it, the scalar is pushed (`tail`); at `4`, `duplex` empties the queue (`b1`), the count is
reloaded (`b2`, `0`), and the scalar pushed.
-/

namespace NativeRustcVmArm.Transcript.Absorb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWAbsorb
open NativeRustcVm.Transcript NativeVm.Model NativeRustcArm LeanVM.Parameters LeanVM.Protocol.Compile

public section

theorem toNat_toBitVec_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toBitVec.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_toBitVec, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem absorb_lt {sp : SpongeW} (h : sp.pending.size ≠ rateScalars) (x : EW) (tag : UInt64) :
    sp.absorb x tag = { sp with pending := sp.pending.push (x, tag) } := by
  simp only [SpongeW.absorb, h, ite_false]

theorem absorb_eq {sp : SpongeW} (h : sp.pending.size = rateScalars) (x : EW) (tag : UInt64) :
    sp.absorb x tag = { sp.duplex with pending := sp.duplex.pending.push (x, tag) } := by
  simp only [SpongeW.absorb, h, ite_true]

variable [Host] {k : Nat}

/-- **`SpongeW::absorb` meets its contract.** -/
theorem absorb_spec (hp : Placed code k)
    (hdup : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp)) (sp : SpongeW) :
    Spec (Labels.label NativeRustcVmArm.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp) := by
  rintro m0 ⟨hst, hrc, ⟨hmap, hnw, hapS, hapR⟩, hsp⟩
  set p := m0.regs.X0.toBitVec with hpdef
  have hA : absorbStack = 464 := rfl
  have hD : duplexStack = 416 := rfl
  have hn : absorbStack ≤ m0.regs.SP.toNat := hst.2.1
  have hnw' : p.toNat + 328 ≤ 2 ^ 64 := hnw
  have hmap' : Mapped m0.dmem p 328 := hmap
  have hfnw := frame_noWrap (m := m0) (F := 48) (by omega)
  have hapF : NativeRustcVm.Apart p 328 (frameBase m0 48) 48 := apart_frame hapS hn (by decide)
  have hpF : ∀ q, NativeRustcVm.InRange p 328 q → ¬ NativeRustcVm.InRange (frameBase m0 48) 48 q :=
    fun q hq ↦ not_inRange_of_apart hapF hnw hfnw hq
  have hle := hsp.pending_le
  unfold rateScalars at hle
  -- `b0`: the prologue, the count against `4`.
  have hwf0 : (frameEnv m0 m0 48 [(p, 328)]).WF :=
    Env.wf_of ⟨⟨frame_mapped (F := 48) hst (by decide), hfnw⟩, ⟨hmap, hnw⟩, trivial⟩
      (List.pairwise_pair.mpr (Apart.symm' hapF))
  have hm0 : Match (frameEnv m0 m0 48 [(p, 328)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
      frameBase_add.symm ⟨known_ptr rfl rfl, trivial⟩ trivial trivial trivial
  obtain ⟨x0, hrun0, hpro, hw0, hx8, hx19, hx20, hx21, hx22, rfl⟩ := ok_b0
  unfold NativeRustcVmArm.Vm.SpongeWAbsorb.entryLabel
  rw [hp.label (j := NativeRustcVmArm.Vm.SpongeWAbsorb.entryOffset) NativeRustcVmArm.Vm.SpongeWAbsorb.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) hrun0 hwf0 hm0 fun st1 hm1 hpc1 => ?_
  have hf1 : Frame m0 48 slots st1.data := Frame.of_prologue hwf0 hm1 hpro slots_le
  have hs1 : SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange (frameBase m0 48) 48) :=
    sameOutside_region hwf0 hm1 rfl hw0
  have hso1 : SameOutside m0.dmem st1.data.dmem (Out m0) :=
    SameOutside.mono hs1 fun q hq ↦ Or.inr (inRange_frame_stack hn (by decide) hq)
  have hsp1 : SpongeAt st1.data.dmem p sp := hsp.frame hnw (fun q hq h ↦ hpF q h hq) hs1
  have hcnt : (frameEnv m0 m0 48 [(p, 328)]).load 1 296 8 = sp.pending.size.toUInt64.toBitVec :=
    load_ofMachine (o := 296) rfl hsp.n_pending
  have hX8 : st1.data.regs.X8.toNat = sp.pending.size := by
    show (st1.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [hm1.regs .X8 _ hx8, Sym.eval, hcnt, toNat_toBitVec_toUInt64 (by omega)]
  have hX19 : st1.data.regs.X19 = m0.regs.X3 := UInt64.toBitVec_inj.mp (hm1.regs .X19 _ hx19)
  have hX20 : st1.data.regs.X20.toBitVec = p := by
    show (st1.data.regs.getXReg .X20).toBitVec = _
    rw [hm1.regs .X20 _ hx20]; exact eval_ptr rfl
  have hX21 : st1.data.regs.X21 = m0.regs.X2 := UInt64.toBitVec_inj.mp (hm1.regs .X21 _ hx21)
  have hX22 : st1.data.regs.X22 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X22 _ hx22)
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [hcnt] at hpc1
  have hlt4 : (BitVec.ult sp.pending.size.toUInt64.toBitVec (BitVec.ofNat 64 4)) =
      decide (sp.pending.size < 4) := by
    simp only [BitVec.ult, toNat_toBitVec_toUInt64 (show sp.pending.size < 2 ^ 64 by omega),
      BitVec.toNat_ofNat]
  rw [hlt4] at hpc1
  by_cases h4 : sp.pending.size < 4
  · -- Below `4`: the push.
    simp only [h4, decide_true, ite_true] at hpc1
    have := tail hp hst hmap' hnw' hapF (hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.SpongeWAbsorb.b3Offset) NativeRustcVmArm.Vm.SpongeWAbsorb.label_2_at)) hf1 h4 hX8 hX19
      hX20 hX21 hX22 hsp1 hso1
    refine Eventually.mono this fun st' ⟨hpc', hsp', hso', hsv'⟩ ↦ ⟨hpc', ?_, hso', hsv'⟩
    rw [absorb_lt (by unfold rateScalars; omega)]
    exact hsp'
  · -- At `4`: `duplex`, then the push.
    simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have h4' : sp.pending.size = 4 := by omega
    -- `b1`: `bl duplex`.
    have hwf1 : (frameEnv m0 st1.data 48 []).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 48) hst (by decide)) hf1.kept, hfnw⟩, trivial⟩
        (List.pairwise_singleton _ _)
    have hm1' : Match (frameEnv m0 st1.data 48 []) callS st1.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), trivial⟩
        (by rw [hf1.sp]; exact (eval_ptr rfl).symm) trivial trivial trivial trivial
    refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf1
      (hpc1.trans (by change Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWAbsorb.b0Offset + NativeRustcVmArm.Vm.SpongeWAbsorb.b0.length) = Host.addrOf (k + NativeRustcVmArm.Vm.SpongeWAbsorb.b1Offset); rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWAbsorb.b0_next])) hm1' fun st2 hm2 hpc2 => ?_
    obtain ⟨hmid2, hmem2, hx0', hx20', hx19', hx21', hx22'⟩ := after_eq run_b1 ▸ ok_b1
    have hf2 : Frame m0 48 slots st2.data := Frame.of_block hf1 hwf1 hm2 hmid2 slots_le
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
    have hX0' : st2.data.regs.X0.toBitVec = p := by
      show (st2.data.regs.getXReg .X0).toBitVec = _
      rw [hm2.regs .X0 _ hx0']; exact hX20
    have hreg2 : ∀ r, (after b1 callS).reg r = some (.reg r) →
        st2.data.regs.getXReg r = st1.data.regs.getXReg r := fun r h ↦
      UInt64.toBitVec_inj.mp (hm2.regs r _ h)
    -- `duplex`.
    have h2sp : st2.data.regs.SP.toNat = m0.regs.SP.toNat - 48 := by
      rw [← UInt64.toNat_toBitVec, hf2.sp, frameBase_toNat hn (by decide)]
    have hrc0 : ∀ i < 192, st2.data.dmem.get? (rcAddr + BitVec.ofNat 64 i) =
        m0.dmem.get? (rcAddr + BitVec.ofNat 64 i) := by
      intro i hi
      have hq : NativeRustcVm.InRange rcAddr 192 (rcAddr + BitVec.ofNat 64 i) :=
        inRange_off_self hi (by have := hrc.2.1; omega)
      rw [hd2, hs1 _ fun h ↦ not_inRange_of_apart (apart_frame hrc.2.2 hn (by decide)) hrc.2.1
        hfnw hq h]
    have hrc2 : RcAt st2.data duplexStack := by
      have h := RcAt.call (F := 48) hrc hrc0 hn (by decide) h2sp
      rwa [show absorbStack - 48 = duplexStack from rfl] at h
    have hpre2 : DuplexPre sp st2.data := by
      unfold DuplexPre
      rw [hX0']
      exact ⟨stackOk_callee hst hf2.kept hf2.sp (by decide) (by decide) (by decide), hrc2,
        ⟨Mapped.keeps hmap hf2.kept, hnw, apart_callee hapS hf2.sp hn (by decide) (by decide), hapR⟩,
        hd2 ▸ hsp1⟩
    refine call_then hpc2 (hdup sp) hpre2 fun st3 hpc3 ⟨hsp3, hs3, hsv3⟩ => ?_
    rw [hX0'] at hsp3 hs3
    have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st2.data duplexStack) duplexStack q →
        NativeRustcVm.InRange (stackBelow m0 absorbStack) absorbStack q ∧
          ¬ NativeRustcVm.InRange (frameBase m0 48) 48 q :=
      fun q hq ↦ inRange_callee hf2.sp hn (by decide) (by decide) hq
    have hf3 : Frame m0 48 slots st3.data := by
      refine Frame.call hf2 hsv3 hs3 (fun q hq ↦ ?_) hfnw slots_le
      rcases hq with hq | hq
      · exact hpF q hq
      · exact (hcal q hq).2
    -- `b2`: the count reloaded.
    have hX20' : st3.data.regs.X20.toBitVec = p := by
      show (st3.data.regs.getXReg .X20).toBitVec = _
      rw [hsv3.1 .X20 rfl, hreg2 .X20 hx20']; exact hX20
    have hwf3 : (frameEnv m0 st3.data 48 [(p, 328)]).WF :=
      Env.wf_of ⟨⟨Mapped.keeps (frame_mapped (F := 48) hst (by decide)) hf3.kept, hfnw⟩,
        ⟨Mapped.keeps hmap hf3.kept, hnw⟩, trivial⟩ (List.pairwise_pair.mpr (Apart.symm' hapF))
    have hm3 : Match (frameEnv m0 st3.data 48 [(p, 328)]) reloadS st3.data :=
      match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hst (by decide) (by decide), rfl, nofun, trivial⟩
        (by rw [hf3.sp]; exact (eval_ptr rfl).symm) ⟨known_ptr rfl hX20', trivial⟩ trivial trivial
        trivial
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf3
      (hpc3.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.SpongeWAbsorb.b1_next])) hm3 fun st4 hm4 hpc4 => ?_
    obtain ⟨hmid4, hmem4, hx8', hx20'', hx19'', hx21'', hx22''⟩ := after_eq run_b2 ▸ ok_b2
    have hf4 : Frame m0 48 slots st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
    have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
    have hreg4 : ∀ r, (after b2 reloadS).reg r = some (.reg r) →
        st4.data.regs.getXReg r = st3.data.regs.getXReg r := fun r h ↦
      UInt64.toBitVec_inj.mp (hm4.regs r _ h)
    have hcnt3 : (frameEnv m0 st3.data 48 [(p, 328)]).load 1 296 8 =
        (sp.duplex.pending.size).toUInt64.toBitVec :=
      load_ofMachine (o := 296) rfl hsp3.n_pending
    have hdz : sp.duplex.pending.size = 0 := rfl
    simp only [PcOk] at hpc4
    sym_simp at hpc4
    rw [hcnt3, hdz] at hpc4
    simp only [show (Nat.toUInt64 0).toBitVec = 0#64 from rfl] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    rw [NativeRustcVmArm.Vm.SpongeWAbsorb.b2_length, NativeRustcVmArm.Vm.SpongeWAbsorb.b2Length] at hpc4
    have hX8' : st4.data.regs.X8.toNat = sp.duplex.pending.size := by
      show (st4.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [hm4.regs .X8 _ hx8', Sym.eval, hcnt3, hdz]; rfl
    have hreg : ∀ r, calleeSaved r = true → (after b1 callS).reg r = some (.reg r) →
        (after b2 reloadS).reg r = some (.reg r) → st4.data.regs.getXReg r = st1.data.regs.getXReg r :=
      fun r hr h1 h2 ↦ (hreg4 r h2).trans ((hsv3.1 r hr).trans (hreg2 r h1))
    have hX20'' : st4.data.regs.X20.toBitVec = p := by
      show (st4.data.regs.getXReg .X20).toBitVec = _
      rw [hm4.regs .X20 _ hx20'']; exact eval_ptr rfl
    have hso4 : SameOutside m0.dmem st4.data.dmem (Out m0) := fun q hq ↦ by
      simp only [not_or] at hq
      rw [hd4, hs3 q (fun h ↦ by
          rcases h with h | h
          · exact hq.1 h
          · exact hq.2 (hcal q h).1), hd2]
      exact hso1 q (by simp only [not_or]; exact hq)
    have := tail hp hst hmap' hnw' hapF (hpc4.trans (by rfl)) hf4 (by rw [hdz]; omega) hX8'
      ((hreg .X19 rfl hx19' hx19'').trans hX19) hX20''
      ((hreg .X21 rfl hx21' hx21'').trans hX21) ((hreg .X22 rfl hx22' hx22'').trans hX22)
      (hd4 ▸ hsp3) hso4
    refine Eventually.mono this fun st' ⟨hpc', hsp', hso', hsv'⟩ ↦ ⟨hpc', ?_, hso', hsv'⟩
    rw [absorb_eq (by unfold rateScalars; omega)]
    exact hsp'

end

end NativeRustcVmArm.Transcript.Absorb
