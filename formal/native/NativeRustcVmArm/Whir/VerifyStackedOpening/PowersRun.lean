module

public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Powers

/-!
# `verify_stacked_opening`: `powers`, the first scale

`powers_b11`: from `b11`, the count stored, `powers` into the scales, `b12` reading the count
back and saving the claims' address, `b13` reading the first scale: at `b15` (`AtB15`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening

@[expose] public section

/-- **At `b15`**: the scales written, the first in X0, X1, the next scale's address in X19. -/
structure AtB15 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (cs : Array ColumnClaimW)
    (m0 st : MachineData) : Prop where
  fr : VFr m0 st
  ts : TStateAt st.dmem (tA m0) a (sq s).2
  fw : FW st.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (32, m0.regs.X5), (48, m0.regs.X2)]
  scw : NativeRustcVm.WordAt st.dmem (scA m0) (cntOf layout cs).toUInt64
  scs : NativeRustcVm.EWsAt st.dmem (scA m0 + BitVec.ofNat 64 8) (scalesOf s layout cs).toList
  x0 : st.regs.getXReg .X0 = ((scalesOf s layout cs).getD 0 0).c0
  x1 : st.regs.getXReg .X1 = ((scalesOf s layout cs).getD 0 0).c1
  x19 : (st.regs.getXReg .X19).toBitVec = scA m0 + BitVec.ofNat 64 24
  x20 : st.regs.getXReg .X20 = m0.regs.X6
  x22 : st.regs.getXReg .X22 = m0.regs.X1
  x23 : (st.regs.getXReg .X23).toBitVec = scA m0 + BitVec.ofNat 64 8
  x24 : st.regs.getXReg .X24 = m0.regs.X3
  x25 : st.regs.getXReg .X25 = (cntOf layout cs).toUInt64
  x28 : (st.regs.getXReg .X28).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 8
  x29 : st.regs.getXReg .X29 = cs.size.toUInt64

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **From `b11` to `b15`.** -/
theorem powers_b11 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hpow : Spec (Labels.label NativeRustcVmArm.Vm.Powers.entryLabel) PowersPre PowersPost)
    {R : MachineState → Prop}
    (cont : ∀ st, AtB15 a s layout cs m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b15Offset)⟩)
    {st : MachineData} (hb : AtB11 a s layout cs m0 st) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b11Offset)⟩ := by
  have c := h.ctx
  have hP : placedOf layout cs cs.size ≤ 160 := (placedOf_le_self _).trans h.cl.len_le
  have hC : cntOf layout cs ≤ 162 := by unfold cntOf; omega
  have hC2 : 2 ≤ cntOf layout cs := by unfold cntOf; omega
  have hso := h.so.1
  have hnw := h.sc_nw
  have hscb : scalesBytes = 2600 := rfl
  rw [hscb] at hnw
  have hS := h.hS
  -- `b11`: the count, `powers`
  let env := Env.ofMachine st [(base m0 512, 512), (scA m0, 8)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hb.fr.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) i hi),
        base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ hb.fr.kept _ (hso.1 i (by rw [hscb]; omega)),
        NativeRustcVm.NoWrap.mono hnw (by omega)⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        have := h.sc_frame (o := 0) (n := 8) (by rw [hscb]; omega) (by omega)
        rw [NativeRustcVm.addr_add_zero] at this
        exact NativeRustcVm.Apart.symm this))
  have hm : Match env scS st :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.wt.1 (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hb.fr.sp]; simp [Sym.eval])
      ⟨by show (st.regs.getXReg .X26).toBitVec = _; rw [hb.x26]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk11 run_b11 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : VFr m0 st1.data := Fr.ofBlockW hb.fr hm hm1 hwf rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
    (writeOk_of (F := 512) (slots := slots) (wr := [1]) hm1 (by decide) (fun r hr b sz hb' i hi ↦ by
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [env, Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      exact .inr (.inl (NativeRustcVm.inRange_add (by rw [hscb]; omega) (by rw [hscb]; omega)))))
  have hs1 : SameOutside st.dmem st1.data.dmem (InRange (scA m0) 8) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦ by
      obtain ⟨w, hw, b', sz, hb', h1, h2⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw
      simp only [env, Env.ofMachine, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      dsimp only at h1 h2
      rw [Sym.inRange_iff (NativeRustcVm.NoWrap.mono hnw (by omega))]
      omega
  have hts1 : TStateAt st1.data.dmem (tA m0) a (sq s).2 :=
    h.ts_call hb.fr (N' := 0) (by rw [stack_eq]; decide) hb.ts (hm1.kept hwf)
      (NativeRustcVm.SameOutside.mono hs1 fun q hq ↦ .inr (NativeRustcVm.InRange.mono hq
        (NativeRustcVm.NoWrap.mono hnw (by omega)) (by rw [hscb]; exact hnw) (Nat.le_refl _)
        (by rw [hscb]; omega)))
  have k1 : ∀ r, (after b11 scS).reg r = some (.reg r) →
      st1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦
    (rv hm1 (by rw [← after_eq run_b11]; exact hr)).trans rfl
  have hscw1 : NativeRustcVm.WordAt st1.data.dmem (scA m0) (cntOf layout cs).toUInt64 := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm1 (r := 1) (o := 0) rfl (by decide)
      (v := .reg .X27) (by decide)
    rw [NativeRustcVm.addr_add_zero,
      show UInt64.ofBitVec ((Sym.reg XReg.X27).eval env) = _ from hb.x27] at this
    exact this
  have hfw1 : FW st1.data.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (48, m0.regs.X2)] :=
    fw_block' hm1 hwf rfl [16, 24, 48] rfl (by decide) hb.fw
  have e1x2 : st1.data.regs.X2.toBitVec = scA m0 + BitVec.ofNat 64 8 :=
    (hm1.regs .X2 _ rfl).trans rfl
  have e1x3 : st1.data.regs.X3 = (cntOf layout cs).toUInt64 := (rv hm1 (r := .X3) rfl).trans hb.x27
  have e1x19 : (st1.data.regs.getXReg .X19).toBitVec = scA m0 + BitVec.ofNat 64 8 :=
    (hm1.regs .X19 _ rfl).trans rfl
  have hCn : (cntOf layout cs).toUInt64.toNat = cntOf layout cs := natCast_toUInt64_toNat (by omega)
  have hP1 : PowersPre st1.data := by
    refine ⟨c.stackOk hf1 (by rw [stack_eq]; decide), ⟨⟨fun i hi ↦ ?_, ?_⟩, ?_⟩⟩
    · rw [e1x2, NativeRustcVm.addr_add_add]
      rw [e1x3, hCn] at hi
      exact hf1.kept _ (hso.1 _ (by rw [hscb]; omega))
    · rw [e1x2, e1x3, hCn]
      show (scA m0 + BitVec.ofNat 64 8).toNat + 16 * cntOf layout cs ≤ 2 ^ 64
      rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]
      unfold NoWrap at hnw
      omega
    · rw [e1x2, e1x3, hCn]
      exact h.sc_off hf1 (by rw [stack_eq]; decide) (by rw [hscb]; omega) (by omega)
  refine Fr.leafAt (N' := powersStack) hf1 h.hN (by rw [stack_eq]; decide) (fun _ h ↦ by cases h)
    slots_le
    c.frame_outs hpow hpc1 hP1 (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_,
      hq.2.2⟩) fun m2 hf2 hq2 hcs2 ↦ ?_
  · rcases hq' with hq' | hq'
    · refine .inr (.inr (.inl (NativeRustcVm.InRange.mono hq' ?_ (by rw [hscb]; exact hnw) ?_ ?_)))
      · rw [e1x2, e1x3, hCn]
        show (scA m0 + BitVec.ofNat 64 8).toNat + 16 * cntOf layout cs ≤ 2 ^ 64
        rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]
        unfold NoWrap at hnw
        omega
      · rw [e1x2, NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]
        omega
      · rw [e1x2, e1x3, hCn, NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega),
          hscb]
        omega
    · exact .inl hq'
  obtain ⟨hscs2, hch2, hsv2⟩ := hq2
  have e1x0 : st1.data.regs.X0 = (sq s).1.c0 := (k1 .X0 rfl).trans hb.x0
  have e1x1 : st1.data.regs.X1 = (sq s).1.c1 := (k1 .X1 rfl).trans hb.x1
  rw [e1x2, e1x3, hCn, e1x0, e1x1] at hscs2
  have hscs2' : NativeRustcVm.EWsAt m2.dmem (scA m0 + BitVec.ofNat 64 8)
      (scalesOf s layout cs).toList := hscs2
  rw [e1x2, e1x3, hCn] at hch2
  have hscw2 : NativeRustcVm.WordAt m2.dmem (scA m0) (cntOf layout cs).toUInt64 := by
    have hsb := h.sc_off hf1 (N' := powersStack) (by rw [stack_eq]; decide) (o := 0) (n := 8)
      (by rw [hscb]; omega) (by omega)
    rw [NativeRustcVm.addr_add_zero] at hsb
    refine hscw1.of_sameOutside hch2 fun i hi hq ↦ ?_
    rw [NativeRustcVm.length_wordBytes] at hi
    have hin := NativeRustcVm.inRange_add (a := scA m0) hi (by omega)
    rcases hq with hq | hq
    · rw [Sym.inRange_iff (by
        show (scA m0 + BitVec.ofNat 64 8).toNat + 16 * cntOf layout cs ≤ 2 ^ 64
        rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]
        unfold NoWrap at hnw; omega),
        NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega),
        NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)] at hq
      omega
    · exact NativeRustcVm.Apart.not_inRange hsb (NativeRustcVm.NoWrap.mono hnw (by omega))
        (by
          rw [stackBelow_eq hf1.sp (by have := h.hS; have : powersStack = 640 := rfl; omega)]
          exact NativeRustcVm.NoWrap.mono (base_noWrap (m0 := m0) (F := 512 + powersStack)
            (by have := h.hS; have : powersStack = 640 := rfl; omega)) (by omega)) hin hq
  have hts2 : TStateAt m2.dmem (tA m0) a (sq s).2 :=
    h.ts_call hf1 (N' := powersStack) (by rw [stack_eq]; decide) hts1 hsv2.2.2
      (NativeRustcVm.SameOutside.mono hch2 fun q hq ↦ by
        rcases hq with hq | hq
        · refine .inr (NativeRustcVm.InRange.mono hq ?_ (by rw [hscb]; exact hnw) ?_ ?_)
          · show (scA m0 + BitVec.ofNat 64 8).toNat + 16 * cntOf layout cs ≤ 2 ^ 64
            rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]
            unfold NoWrap at hnw; omega
          · rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]; omega
          · rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega), hscb]; omega
        · exact .inl hq)
  have hfw2 : FW m2.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (48, m0.regs.X2)] :=
    fw_call h hf1 (N' := powersStack) (by rw [stack_eq]; decide)
      (NativeRustcVm.SameOutside.mono hch2 fun q hq ↦ by
        rcases hq with hq | hq
        · refine .inr (.inr (.inl (NativeRustcVm.InRange.mono hq ?_
            (by rw [hscb]; exact hnw) ?_ ?_)))
          · show (scA m0 + BitVec.ofNat 64 8).toNat + 16 * cntOf layout cs ≤ 2 ^ 64
            rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]
            unfold NoWrap at hnw; omega
          · rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)]; omega
          · rw [NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega), hscb]; omega
        · exact .inl hq) (by simp) hfw1
  have kc2 : ∀ r, calleeSaved r = true → (after b11 scS).reg r = some (.reg r) →
      m2.regs.getXReg r = st.regs.getXReg r := fun r hc hr ↦ (hcs2 r hc).trans (k1 r hr)
  -- `b12`: the count back, the claims' address saved
  let env2 := Env.ofMachine m2 [(base m0 512, 512), (scA m0, 8)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hf2.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) i hi),
        base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ hf2.kept _ (hso.1 i (by rw [hscb]; omega)),
        NativeRustcVm.NoWrap.mono hnw (by omega)⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        have := h.sc_frame (o := 0) (n := 8) (by rw [hscb]; omega) (by omega)
        rw [NativeRustcVm.addr_add_zero] at this
        exact NativeRustcVm.Apart.symm this))
  have hm2 : Match env2 scS m2 :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.wt.1 (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hf2.sp]; simp [Sym.eval])
      ⟨by show (m2.regs.getXReg .X26).toBitVec = _; rw [hcs2 .X26 rfl, hm1.regs .X26 _ rfl]; rfl,
        trivial⟩ trivial trivial trivial
  have hl2 : env2.load 1 0 8 = (cntOf layout cs).toUInt64.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt m2.dmem (scA m0 + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero]
    exact hscw2
  have hult : ((cntOf layout cs).toUInt64.toBitVec).ult (BitVec.ofNat 64 163) = true := by
    rw [toBitVec_ult_ofNat (by decide), hCn]
    simp
    omega
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk12 run_b12 hwf2 hm2 fun st3 hm3 hpc3 ↦ ?_
  have hf3 : VFr m0 st3.data := Fr.ofBlockW hf2 hm2 hm3 hwf2 rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
    (writeOk_of (F := 512) (slots := slots) (wr := []) hm3 (by decide) (fun _ h ↦ by cases h))
  have hs3 : SameOutside m2.dmem st3.data.dmem (InRange (base m0 512) 512) :=
    NativeRustcVm.SameOutside.mono (hm3.sameOutside hwf2) fun q hq ↦
      written_r0 hwf2 rfl (by decide) hq
  have k3 : ∀ r, (after b12 scS).reg r = some (.reg r) →
      st3.data.regs.getXReg r = m2.regs.getXReg r := fun r hr ↦
    (rv hm3 (by rw [← after_eq run_b12]; exact hr)).trans rfl
  have hfw3 : FW st3.data.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (32, m0.regs.X5),
      (48, m0.regs.X2)] := by
    have hold := fw_block' hm3 hwf2 rfl [16, 24, 48] rfl (by decide) hfw2
    have h32 := fw_write (m0 := m0) hm3 rfl (o := 32) (by decide) (v := .reg .X21) (by decide)
    rw [show UInt64.ofBitVec ((Sym.reg XReg.X21).eval env2) = m0.regs.X5 from
      (kc2 .X21 rfl rfl).trans hb.x21] at h32
    exact FW.cons (hold.get (by simp)) (FW.cons (hold.get (by simp)) (FW.cons h32
      (FW.cons (hold.get (by simp)) (FW.nil _ _))))
  have e3x25 : st3.data.regs.getXReg .X25 = (cntOf layout cs).toUInt64 :=
    (rv hm3 (r := .X25) rfl).trans (by sym_simp; rw [hl2, hult]; rfl)
  have e3x23 : (st3.data.regs.getXReg .X23).toBitVec = scA m0 + BitVec.ofNat 64 8 := by
    refine (hm3.regs .X23 _ rfl).trans ?_
    sym_simp
    rw [hl2, hult]
    show (m2.regs.getXReg .X19).toBitVec = _
    rw [hcs2 .X19 rfl, e1x19]
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [hl2, hult] at hpc3
  have hne : ((cntOf layout cs).toUInt64.toBitVec == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    rw [UInt64.toNat_toBitVec, hCn] at this
    simp at this
  simp only [↓reduceIte, hne, Bool.false_eq_true] at hpc3
  -- `b13`: the first scale
  have hsc8 : (scA m0 + BitVec.ofNat 64 8).toNat = (scA m0).toNat + 8 :=
    NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)
  let env4 := Env.ofMachine st3.data [(scA m0 + BitVec.ofNat 64 8, 16)]
  have hwf4 : env4.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ by
        rw [NativeRustcVm.addr_add_add]; exact hf3.kept _ (hso.1 _ (by rw [hscb]; omega)),
      by show _ + 16 ≤ _; rw [hsc8]; unfold NoWrap at hnw; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm4 : Match env4 scaleS st3.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by show (st3.data.regs.getXReg .X23).toBitVec = _; rw [e3x23]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hscs3 : NativeRustcVm.EWsAt st3.data.dmem (scA m0 + BitVec.ofNat 64 8)
      (scalesOf s layout cs).toList :=
    h.sc_keep hf2 (N' := 0) (by rw [stack_eq]; decide)
      (NativeRustcVm.SameOutside.mono hs3 fun q hq ↦ .inr hq)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf, hscb]
          omega)
      (by rw [NativeRustcVm.length_ewsBytes, Array.length_toList, size_scalesOf]; omega)
      hscs2'
  have hscw3 : NativeRustcVm.WordAt st3.data.dmem (scA m0) (cntOf layout cs).toUInt64 := by
    have := h.sc_keep hf2 (N' := 0) (by rw [stack_eq]; decide) (o := 0)
      (bs := NativeRustcVm.wordBytes (cntOf layout cs).toUInt64)
      (NativeRustcVm.SameOutside.mono hs3 fun q hq ↦ .inr hq)
      (by rw [NativeRustcVm.length_wordBytes, hscb]; omega)
      (by rw [NativeRustcVm.length_wordBytes]; omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact hscw2)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hs0 : 0 < (scalesOf s layout cs).toList.length := by
    rw [Array.length_toList, size_scalesOf]; omega
  have he0 := NativeRustcVm.ewsAt_getElem hscs3 hs0
  rw [NativeRustcVm.addr_add_zero] at he0
  have he0' := NativeRustcVm.ewAt_iff.mp he0
  have hl40 : env4.load 0 0 8 = ((scalesOf s layout cs).toList[0]).c0.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st3.data.dmem (scA m0 + BitVec.ofNat 64 8 + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero]; exact he0'.1
  have hl48 : env4.load 0 8 8 = ((scalesOf s layout cs).toList[0]).c1.toBitVec := by
    refine Ring.load_word ?_
    exact he0'.2
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk13 run_b13 hwf4 hpc3 hm4 fun st4 hm4' hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_12 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b15Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b15Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_12_at]
    at hpc4
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4
  subst hpc4
  have hd4 : d4.dmem = st3.data.dmem := hm4'.dmem_eq hwf4 rfl
  have k4 : ∀ r, (after b13 scaleS).reg r = some (.reg r) →
      d4.regs.getXReg r = st3.data.regs.getXReg r := fun r hr ↦
    (rv hm4' (by rw [← after_eq run_b13]; exact hr)).trans rfl
  have kall : ∀ r, calleeSaved r = true → (after b11 scS).reg r = some (.reg r) →
      (after b12 scS).reg r = some (.reg r) → (after b13 scaleS).reg r = some (.reg r) →
      d4.regs.getXReg r = st.regs.getXReg r := fun r hc h1 h2 h3 ↦ by
    rw [k4 r h3, k3 r h2, kc2 r hc h1]
  have hg0 : (scalesOf s layout cs).getD 0 0 = (scalesOf s layout cs).toList[0] := by
    simp only [Array.getD, show 0 < (scalesOf s layout cs).size by rw [size_scalesOf]; omega,
      ↓reduceDIte]
    rfl
  exact cont d4 {
    fr := Fr.ofBlock hf3 hm4 hm4' hwf4 rfl rfl rfl (by simp)
    ts := by rw [hd4]; exact h.ts_frame (show TStateAt m2.dmem _ _ _ from hts2) (hm3.kept hwf2) hs3
    fw := by rw [hd4]; exact hfw3
    scw := by rw [hd4]; exact hscw3
    scs := by rw [hd4]; exact hscs3
    x0 := (rv hm4' (r := .X0) rfl).trans (by
      show UInt64.ofBitVec (env4.load 0 0 8) = _; rw [hl40, hg0])
    x1 := (rv hm4' (r := .X1) rfl).trans (by
      show UInt64.ofBitVec (env4.load 0 8 8) = _; rw [hl48, hg0])
    x19 := (hm4'.regs .X19 _ rfl).trans (by
      show scA m0 + BitVec.ofNat 64 8 + BitVec.ofInt 64 16 = _
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, NativeRustcVm.addr_add_add])
    x20 := (kall .X20 rfl rfl rfl rfl).trans hb.x20
    x22 := (kall .X22 rfl rfl rfl rfl).trans hb.x22
    x23 := (hm4'.regs .X23 _ rfl).trans (by
      show scA m0 + BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = _; simp)
    x24 := (kall .X24 rfl rfl rfl rfl).trans hb.x24
    x25 := by rw [k4 .X25 rfl]; exact e3x25
    x28 := (kall .X28 rfl rfl rfl rfl) ▸ hb.x28
    x29 := (kall .X29 rfl rfl rfl rfl).trans hb.x29 }

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
