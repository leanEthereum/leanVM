module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.PowersRun

/-!
# `verify_stacked_opening`: the first term

`first_b15`: `b15` reads the ring switch's target, the scales' end, saves the out-of-domain claim's
address and calls `EW::mul` on the first scale and the target; `b16` keeps the product as the
target so far; no claim: `.LVerifyStackedOpening_21` (`AtB26`); else `b17` starts the loop over
the claims (`Tgt 0`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **From `b15`** to the target's loop, or past it with no claim. -/
theorem first_b15 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {R : MachineState → Prop}
    (cont : ∀ st, Tgt a s layout target cs value m0 0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset)⟩)
    (fin : ∀ st, AtB26 a s layout target cs value m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset)⟩)
    {st : MachineData} (hb : AtB15 a s layout cs m0 st) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b15Offset)⟩ := by
  have hP : placedOf layout cs cs.size ≤ 160 := (placedOf_le_self _).trans h.cl.len_le
  have hC : cntOf layout cs ≤ 162 := by unfold cntOf; omega
  have hC2 : 2 ≤ cntOf layout cs := by unfold cntOf; omega
  have hnw := h.sc_nw
  have hscb : scalesBytes = 2600 := rfl
  rw [hscb] at hnw
  have hS := h.hS
  have hrin := h.in_ok hb.fr mem_ring
  simp only at hrin
  have hrb : NativeRustcVm.Ring.ringWBytes = 1040 := rfl
  rw [hrb] at hrin
  -- `b15`
  let env := Env.ofMachine st [(base m0 512, 512), (m0.regs.X3.toBitVec, 16)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hb.fr.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) i hi),
        base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ hrin.1 i (by omega), NativeRustcVm.NoWrap.mono hrin.2.1 (by omega)⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        have := hrin.2.2
        show Apart (base m0 512) 512 m0.regs.X3.toBitVec 16
        unfold Apart at this ⊢
        omega))
  have hm : Match env ringS st :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.wt.1 (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hb.fr.sp]; simp [Sym.eval])
      ⟨by show (st.regs.getXReg .X24).toBitVec = _; rw [hb.x24]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have htg := NativeRustcVm.ewAt_iff.mp (NativeRustcVm.Layout.EWAt.of_same h.ring.1
    (h.same_in hb.fr mem_ring) (by show 16 ≤ 1040; omega))
  have hl0 : env.load 1 0 8 = target.c0.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero]; exact htg.1
  have hl8 : env.load 1 8 8 = target.c1.toBitVec := Ring.load_word htg.2
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk15 run_b15 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : VFr m0 st1.data := Fr.ofBlockW hb.fr hm hm1 hwf rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
    (writeOk_of (F := 512) (slots := slots) (wr := []) hm1 (by decide) (fun _ h ↦ by cases h))
  have hs1 : SameOutside st.dmem st1.data.dmem (InRange (base m0 512) 512) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦
      written_r0 hwf rfl (by decide) hq
  have k1 : ∀ r, (after b15 ringS).reg r = some (.reg r) →
      st1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦
    (rv hm1 (by rw [← after_eq run_b15]; exact hr)).trans rfl
  have hfw1 : FW st1.data.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (32, m0.regs.X5),
      (40, m0.regs.X6), (48, m0.regs.X2)] := by
    have hold := fw_block' hm1 hwf rfl [16, 24, 32, 48] rfl (by decide) hb.fw
    have h40 := fw_write (m0 := m0) hm1 rfl (o := 40) (by decide) (v := .reg .X20) (by decide)
    rw [show UInt64.ofBitVec ((Sym.reg XReg.X20).eval env) = m0.regs.X6 from hb.x20] at h40
    exact FW.cons (hold.get (by simp)) (FW.cons (hold.get (by simp)) (FW.cons (hold.get (by simp))
      (FW.cons h40 (FW.cons (hold.get (by simp)) (FW.nil _ _)))))
  have hscs1 := h.sc_keep hb.fr (N' := 0) (by rw [stack_eq]; decide) (o := 8)
    (NativeRustcVm.SameOutside.mono hs1 fun q hq ↦ .inr hq)
    (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf, hscb]; omega)
    (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf]; unfold cntOf; omega)
    hb.scs
  have hscw1 : NativeRustcVm.WordAt st1.data.dmem (scA m0) (cntOf layout cs).toUInt64 := by
    have := h.sc_keep hb.fr (N' := 0) (by rw [stack_eq]; decide) (o := 0)
      (bs := NativeRustcVm.wordBytes (cntOf layout cs).toUInt64)
      (NativeRustcVm.SameOutside.mono hs1 fun q hq ↦ .inr hq)
      (by rw [NativeRustcVm.length_wordBytes, hscb]; omega)
      (by rw [NativeRustcVm.length_wordBytes]; omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact hb.scw)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hts1 : TStateAt st1.data.dmem (tA m0) a (sq s).2 := h.ts_frame hb.ts (hm1.kept hwf) hs1
  have e1x21 : (st1.data.regs.getXReg .X21).toBitVec =
      scA m0 + BitVec.ofNat 64 (8 + 16 * cntOf layout cs) := by
    refine (hm1.regs .X21 _ rfl).trans ?_
    sym_simp
    show (st.regs.getXReg .X23).toBitVec + (st.regs.getXReg .X25).toBitVec <<< 4 = _
    rw [hb.x23, hb.x25, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, UInt64.toNat_toBitVec, BitVec.toNat_add, BitVec.toNat_ofNat,
      natCast_toUInt64_toNat (show cntOf layout cs < 2 ^ 64 by omega), Nat.shiftLeft_eq]
    omega
  have hcom1 : Common a s layout cs m0 st1.data :=
    ⟨hf1, hts1, hfw1, hscw1, hscs1, (k1 .X22 rfl).trans hb.x22, (k1 .X23 rfl) ▸ hb.x23,
      UInt64.toBitVec_inj.mp ((hm1.regs .X24 _ rfl).trans (by
        show m0.regs.X3.toBitVec + BitVec.ofInt 64 0 = _; simp)), (k1 .X25 rfl).trans hb.x25⟩
  refine mul_call h hmul hf1 hpc1 fun m2 hf2 h0 h1 hcs2 hs2 hk2 ↦ ?_
  have hcom2 := hcom1.call h hf2 (by rw [stack_eq]; decide) hs2 hk2 hcs2
  have e1 : (⟨st1.data.regs.X0, st1.data.regs.X1⟩ : EW) = (scalesOf s layout cs).getD 0 0 := by
    rw [show st1.data.regs.X0 = st.regs.getXReg .X0 from k1 .X0 rfl,
      show st1.data.regs.X1 = st.regs.getXReg .X1 from k1 .X1 rfl, hb.x0, hb.x1]
  have e2 : (⟨st1.data.regs.X2, st1.data.regs.X3⟩ : EW) = target := by
    rw [show st1.data.regs.X2 = UInt64.ofBitVec (env.load 1 0 8) from
        (rv hm1 (r := .X2) rfl).trans rfl,
      show st1.data.regs.X3 = UInt64.ofBitVec (env.load 1 8 8) from
        (rv hm1 (r := .X3) rfl).trans rfl,
      hl0, hl8]
  rw [e1, e2] at h0 h1
  have hacc : (⟨m2.regs.X0, m2.regs.X1⟩ : EW) =
      dotL ((scalesOf s layout cs).toList.take 1) ((valsOf layout target cs value).take 1) := by
    rw [dotL_take_one (by rw [Array.length_toList, size_scalesOf]; omega) (by simp [valsOf])]
    rw [h0, h1]
    simp only [valsOf, List.getElem_cons_zero]
    rw [show (scalesOf s layout cs).getD 0 0 = (scalesOf s layout cs).toList[0]'(by
      rw [Array.length_toList, size_scalesOf]; omega) by
      simp only [Array.getD, show 0 < (scalesOf s layout cs).size by rw [size_scalesOf]; omega]
      rfl]
    rfl
  -- `b16`
  have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hf2.regsBlock (st := ⟨m2, _⟩) hk16 run_b16 rfl rfl rfl rfl
    fun st3 hf3 hd3 hm3 hpc3 ↦ ?_
  have k3 : ∀ r, r ≠ .X27 → r ≠ .X26 → st3.data.regs.getXReg r = m2.regs.getXReg r :=
    fun r h27 h26 ↦ (rv hm3 (v := .reg r) (by cases r <;> first | rfl | exact absurd rfl h27 |
      exact absurd rfl h26)).trans rfl
  have hcom3 : Common a s layout cs m0 st3.data := hcom2.same hf3 hd3 fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k3 _ (by decide) (by decide)
  have hacc3 : (⟨st3.data.regs.getXReg .X27, st3.data.regs.getXReg .X26⟩ : EW) =
      dotL ((scalesOf s layout cs).toList.take 1) ((valsOf layout target cs value).take 1) := by
    rw [← hacc]
    rw [show st3.data.regs.getXReg .X27 = m2.regs.X0 from (rv hm3 (r := .X27) rfl).trans rfl,
      show st3.data.regs.getXReg .X26 = m2.regs.X1 from (rv hm3 (r := .X26) rfl).trans rfl]
  have kc : ∀ r, calleeSaved r = true → r ≠ .X27 → r ≠ .X26 →
      (after b15 ringS).reg r = some (.reg r) →
      st3.data.regs.getXReg r = st.regs.getXReg r := fun r hc h27 h26 hr ↦ by
    rw [k3 r h27 h26, hcs2 r hc, k1 r hr]
  have hx29 : (Env.ofMachine m2 []).regs .X29 = cs.size.toUInt64.toBitVec := by
    show (m2.regs.getXReg .X29).toBitVec = _
    rw [hcs2 .X29 rfl, k1 .X29 rfl, hb.x29]
  have hcs160 : cs.size ≤ 160 := h.cl.len_le
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [hx29] at hpc3
  have hx21 : (st3.data.regs.getXReg .X21).toBitVec =
      scA m0 + BitVec.ofNat 64 (8 + 16 * cntOf layout cs) := by
    rw [k3 .X21 (by decide) (by decide), hcs2 .X21 rfl]; exact e1x21
  have hx19 : (st3.data.regs.getXReg .X19).toBitVec = scA m0 + BitVec.ofNat 64 24 := by
    rw [k3 .X19 (by decide) (by decide), hcs2 .X19 rfl, k1 .X19 rfl]; exact hb.x19
  by_cases hz : cs.size = 0
  · have hc : (cs.size.toUInt64.toBitVec == 0#64) = true := by rw [hz]; rfl
    simp only [hc, ↓reduceIte] at hpc3
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_21 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_21_at]
      at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3
    subst hpc3
    have hP0 : placedOf layout cs cs.size = 0 := by unfold placedOf; rw [hz]; rfl
    exact fin d3 ⟨hcom3, by rw [hx19, hP0], hx21, by rw [hP0]; exact hacc3⟩
  · have hc : (cs.size.toUInt64.toBitVec == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have := congrArg BitVec.toNat he
      rw [UInt64.toNat_toBitVec, natCast_toUInt64_toNat (by omega)] at this
      exact hz this
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at hpc3
    -- `b17`
    have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b17Offset) := b17_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine hf3.regsBlock hk17 run_b17 hpc3 rfl rfl rfl fun st4 hf4 hd4 hm4 hpc4 ↦ ?_
    simp only [PcOk] at hpc4
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_17 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_17_at]
      at hpc4
    obtain ⟨d4, pc4⟩ := st4
    simp only at hpc4
    subst hpc4
    have k4 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28],
        d4.regs.getXReg r = st3.data.regs.getXReg r := fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (rv hm4 rfl).trans rfl
    have hP0 : placedOf layout cs 0 = 0 := rfl
    refine cont d4 ⟨hcom3.same hf4 hd4 fun r hr ↦ ?_, Nat.pos_of_ne_zero hz, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact k4 _ (by simp)
    · rw [k4 .X28 (by simp), k3 .X28 (by decide) (by decide), hcs2 .X28 rfl,
        k1 .X28 rfl, hb.x28]
    · refine (rv hm4 (r := .X29) rfl).trans ?_
      sym_simp
      show UInt64.ofBitVec ((st3.data.regs.getXReg .X29).toBitVec * BitVec.ofNat 64 608) = _
      rw [k3 .X29 (by decide) (by decide), hcs2 .X29 rfl, k1 .X29 rfl, hb.x29]
      apply UInt64.toBitVec_inj.mp
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, UInt64.toNat_toBitVec,
        BitVec.toNat_ofNat, natCast_toUInt64_toNat (show cs.size < 2 ^ 64 by omega),
        natCast_toUInt64_toNat (show 608 * (cs.size - 0) < 2 ^ 64 by omega)]
      omega
    · refine (hm4.regs .X20 _ rfl).trans ?_
      sym_simp
      show (st3.data.regs.getXReg .X22).toBitVec + BitVec.ofNat 64 120 = _
      rw [hcom3.x22]
    · rw [k4 .X19 (by simp), hx19, hP0]
    · rw [k4 .X21 (by simp), hx21]
    · rw [k4 .X27 (by simp), k4 .X26 (by simp), hP0]
      exact hacc3

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
