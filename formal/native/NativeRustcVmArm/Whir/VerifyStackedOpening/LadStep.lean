module

public import NativeRustcVmArm.Code.Vm.Ladder.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.Ladder
public import NativeRustcVmArm.Spec.Layout

/-!
# `verify_stacked_opening`: the ladder's call

`ladder_b30`: from `b30` (`AtB30`), the `BasisW`'s words written and `ladder` called into the
frame's bytes 256 to 415; `b31` checks the result's tag: `None` (`fail_ladder`: X0 `0`, the
model's run `none`), else `AtB32`.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open LeanVM.Parameters

@[expose] public section

/-- What the function's contract asks of its exit. -/
abbrev Goal [Host] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (coefficients point : Array EW) (cs : Array ColumnClaimW) (z : Array EW) (value : EW)
    (m0 : MachineData) : MachineState → Prop :=
  fun st ↦ st.pc = retOf m0 ∧
    VerifyStackedOpeningPost a s layout target coefficients point cs z value m0 st.data

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

omit [Host] in
theorem size_claims_le [Labels]
    (h : Parts a s layout target coefficients point slices cs z value m0) :
    (stackClaims layout target point coefficients cs z value).size ≤ 512 := by
  rw [size_stackClaims]
  have := (placedOf_le_self (layout := layout) (cs := cs) cs.size).trans h.cl.len_le
  have : NativeRustcVm.Layout.claimCap = 160 := rfl
  omega

/-- **`None`** from the ladder: X0 `0`, the model's run `none`. -/
theorem fail_ladder (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hnone : Whir.ladder layout.stackLog m0.regs.X2.toNat = none) {st : MachineData}
    (hf : VFr m0 st) :
    Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b36Offset)⟩ := by
  have hrun : (verifyStackedOpening layout.stackLog m0.regs.X2.toNat
      (stackClaims layout target point coefficients cs z value)).run s = none := by
    rw [vso_run _ _ _ (size_claims_le h), hnone]
    rfl
  refine fail_b36 hp h hf fun m' h0 hd hS ↦ ⟨rfl, post_of (by rw [h0, hrun]; rfl)
    (by rw [hrun]; intro _ _ hx; cases hx) ?_ hS⟩
  rw [hd]
  exact NativeRustcVm.SameOutside.mono hf.same fun q hq ↦ hq.elim .inl fun hq ↦ .inr (outs_outsF hq)

omit [Host] in
/-- The ladder's tag, as `tbz w8, #0` reads it. -/
theorem lad_tag [Labels] {st : MachineData} {r : Option (List Whir.Level)}
    (hl : NativeRustcVm.Layout.LadderAt st.dmem (loc m0 256) r) :
    SBool.eval (Env.ofMachine st [(base m0 512, 512)]) (.not (.bit .W32 (.load 0 256 4) 0)) =
      r.isNone := by
  cases r with
  | none =>
    have hl' : (Env.ofMachine st [(base m0 512, 512)]).load 0 256 4 = BitVec.ofNat 64 0 :=
      Transcript.load4_of_tag (w := 0) (.inl rfl) hl
    show (!(low .W32 ((Env.ofMachine st [(base m0 512, 512)]).load 0 256 4)).getLsbD 0) = _
    rw [hl']; rfl
  | some ls =>
    have hl' : (Env.ofMachine st [(base m0 512, 512)]).load 0 256 4 = BitVec.ofNat 64 1 :=
      Transcript.load4_of_tag (w := 1) (.inr rfl) hl.1
    show (!(low .W32 ((Env.ofMachine st [(base m0 512, 512)]).load 0 256 4)).getLsbD 0) = _
    rw [hl']; rfl

/-- **From `b30`**: the `BasisW`'s words, `ladder`, its tag. -/
theorem ladder_b30 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hlad : Spec (Labels.label NativeRustcVmArm.Vm.Ladder.entryLabel) LadderPre LadderPost)
    (cont : ∀ st ls, AtB32 a s layout target cs value ls m0 st →
      Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0)
        ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b32Offset)⟩)
    {st : MachineData} (hb : AtB30 a s layout target cs value m0 st) :
    Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b30Offset)⟩ := by
  have hc := hb.com
  have hS := h.hS
  have hlin := h.in_ok hc.fr mem_lay
  simp only at hlin
  have hlb : NativeRustcVm.Layout.layoutBytes = 3912 := rfl
  rw [hlb] at hlin
  have hlay := NativeRustcVm.Tables.LayoutWAt.of_same h.lay (h.same_in hc.fr mem_lay)
  -- `b30`
  let env := Env.ofMachine st [(base m0 512, 512), (m0.regs.X1.toBitVec, 24)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hc.fr.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) i hi),
        base_noWrap (by omega)⟩,
      ⟨fun i hi ↦ hlin.1 i (by omega), NativeRustcVm.NoWrap.mono hlin.2.1 (by omega)⟩, trivial⟩
      (List.pairwise_pair.mpr (by
        have := hlin.2.2
        show Apart (base m0 512) 512 m0.regs.X1.toBitVec 24
        unfold Apart at this ⊢
        omega))
  have hb0 : env.base 0 = base m0 512 := rfl
  have hm : Match env ladS st :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.wt.1 (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hc.fr.sp]; simp [Sym.eval])
      ⟨by show (st.regs.getXReg .X22).toBitVec = _; rw [hc.x22]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  have hl16 : env.load 1 16 8 = layout.stackLog.toUInt64.toBitVec := Ring.load_word hlay.stack_log
  have hl24 : env.load 0 24 8 = m0.regs.X4.toBitVec := fw_load hb0 hc.fw (by simp)
  have hl48 : env.load 0 48 8 = m0.regs.X2.toBitVec := fw_load hb0 hc.fw (by simp)
  have hk30 : b30.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b30Offset) := b30_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk30 run_b30 hwf hm fun st1 hm1 hpc1 ↦ ?_
  have hf1 : VFr m0 st1.data := Fr.ofBlockW hc.fr hm hm1 hwf rfl rfl
    (fun _ h ↦ absurd h (by simp)) rfl (by rw [stack_eq]; decide) h.hN slots_le
    (writeOk_of (F := 512) (slots := slots) (wr := []) hm1 (by decide) (fun _ h ↦ by cases h))
  have hs1 : SameOutside st.dmem st1.data.dmem (InRange (base m0 512) 512) :=
    NativeRustcVm.SameOutside.mono (hm1.sameOutside hwf) fun q hq ↦
      written_r0 hwf rfl (by decide) hq
  have k1 : ∀ r ∈ [XReg.X23, .X24, .X25, .X26, .X27],
      st1.data.regs.getXReg r = st.regs.getXReg r := fun r hr ↦ by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact (rv hm1 rfl).trans rfl
  have e1x22 : st1.data.regs.getXReg .X22 = st.regs.getXReg .X22 :=
    (rv hm1 (r := .X22) rfl).trans (by
      show UInt64.ofBitVec (m0.regs.X1.toBitVec + BitVec.ofInt 64 0) = _
      rw [hc.x22]; simp)
  have hfw1 : FW st1.data.dmem m0 [(16, m0.regs.X0), (24, m0.regs.X4), (32, m0.regs.X5),
      (40, m0.regs.X6), (48, m0.regs.X2)] :=
    fw_block' hm1 hwf rfl [16, 24, 32, 40, 48] rfl (by decide) hc.fw
  have hc1 : Common a s layout cs m0 st1.data :=
    hc.frame h hf1 hs1 (hm1.kept hwf) hfw1 fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact e1x22
      all_goals exact k1 _ (by simp)
  have hwb : FW st1.data.dmem m0 (basisWords layout cs m0) := by
    have w56 := fw_write (m0 := m0) hm1 rfl (o := 56) (by decide) (v := .reg .X23) (by decide)
    have w64 := fw_write (m0 := m0) hm1 rfl (o := 64) (by decide) (v := .reg .X25) (by decide)
    have w72 := fw_write (m0 := m0) hm1 rfl (o := 72) (by decide) (v := .ptr 1 0) (by decide)
    have w80 := fw_write (m0 := m0) hm1 rfl (o := 80) (by decide) (v := .reg .X24) (by decide)
    have w88 := fw_write (m0 := m0) hm1 rfl (o := 88) (by decide) (v := .load 0 24 8) (by decide)
    have w96 := fw_write (m0 := m0) hm1 rfl (o := 96) (by decide) (v := .reg .X20) (by decide)
    have w104 := fw_write (m0 := m0) hm1 rfl (o := 104) (by decide) (v := .reg .X19) (by decide)
    rw [show UInt64.ofBitVec ((Sym.reg XReg.X23).eval env) = UInt64.ofBitVec (scA m0 +
      BitVec.ofNat 64 8) from congrArg UInt64.ofBitVec hc.x23] at w56
    rw [show UInt64.ofBitVec ((Sym.reg XReg.X25).eval env) = (cntOf layout cs).toUInt64 from
      hc.x25] at w64
    rw [show UInt64.ofBitVec ((Sym.ptr 1 0).eval env) = m0.regs.X1 by
      show UInt64.ofBitVec (m0.regs.X1.toBitVec + BitVec.ofInt 64 0) = _; simp] at w72
    rw [show UInt64.ofBitVec ((Sym.reg XReg.X24).eval env) = m0.regs.X3 from hc.x24] at w80
    rw [show UInt64.ofBitVec ((Sym.load 0 24 8).eval env) = m0.regs.X4 by
      show UInt64.ofBitVec (env.load 0 24 8) = _; rw [hl24]] at w88
    rw [show UInt64.ofBitVec ((Sym.reg XReg.X20).eval env) = m0.regs.X5 from hb.x20] at w96
    rw [show UInt64.ofBitVec ((Sym.reg XReg.X19).eval env) = m0.regs.X6 from hb.x19] at w104
    exact FW.cons w56 (FW.cons w64 (FW.cons w72 (FW.cons w80 (FW.cons w88 (FW.cons w96
      (FW.cons w104 (FW.nil _ _)))))))
  have e1x0 : (st1.data.regs.getXReg .X0).toBitVec = loc m0 256 :=
    (hm1.regs .X0 _ rfl).trans (by show base m0 512 + BitVec.ofInt 64 256 = _; rfl)
  have e1x19 : (st1.data.regs.getXReg .X19).toBitVec = loc m0 256 :=
    (hm1.regs .X19 _ rfl).trans (by show base m0 512 + BitVec.ofInt 64 256 = _; rfl)
  have e1x1 : st1.data.regs.X1 = layout.stackLog.toUInt64 :=
    (rv hm1 (r := .X1) rfl).trans (by show UInt64.ofBitVec (env.load 1 16 8) = _; rw [hl16])
  have e1x21 : st1.data.regs.getXReg .X21 = layout.stackLog.toUInt64 :=
    (rv hm1 (r := .X21) rfl).trans (by show UInt64.ofBitVec (env.load 1 16 8) = _; rw [hl16])
  have e1x2 : st1.data.regs.X2 = m0.regs.X2 :=
    (rv hm1 (r := .X2) rfl).trans (by show UInt64.ofBitVec (env.load 0 48 8) = _; rw [hl48])
  have e1x28 : st1.data.regs.getXReg .X28 = st.regs.X0 := (rv hm1 (r := .X28) rfl).trans rfl
  have e1x29 : st1.data.regs.getXReg .X29 = st.regs.X1 := (rv hm1 (r := .X29) rfl).trans rfl
  -- `ladder`
  have hpre : LadderPre st1.data := by
    refine ⟨h.rodataAt (fun _ hq ↦ outs_outsF hq) hf1 (by rw [stack_eq]; decide), ?_, ?_⟩
    · show Readable st1.data st1.data.regs.X0.toBitVec 160
      rw [show st1.data.regs.X0.toBitVec = loc m0 256 from e1x0]
      exact h.loc_readable hf1 (by omega)
    · show NativeRustcVm.RodataApart rodataAddr st1.data.regs.X0.toBitVec 160
      rw [show st1.data.regs.X0.toBitVec = loc m0 256 from e1x0]
      exact h.loc_rodata (by omega)
  refine Fr.leafIn (N' := 0) (lo := 256) (n := 160) hf1 h.hN (by rw [stack_eq]; decide)
    (by omega) (fun _ h ↦ by cases h) (by decide) h.ctx.frame_outs hlad hpc1 hpre
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq' ↦ ?_, hq.2.2⟩)
    fun m2 hf2 hq2 hcs2 ↦ ?_
  · rcases hq' with hq' | hq'
    · refine .inr (.inl ?_)
      rw [show st1.data.regs.X0.toBitVec = loc m0 256 from e1x0] at hq'
      exact hq'
    · exact .inl hq'
  obtain ⟨hL, hch, hsv⟩ := hq2
  rw [show st1.data.regs.X0.toBitVec = loc m0 256 from e1x0, e1x2,
    show st1.data.regs.X1.toNat = layout.stackLog by
      rw [e1x1]; exact natCast_toUInt64_toNat hlay.stack_log_lt] at hL
  have hch' : SameOutside st1.data.dmem m2.dmem (InRange (loc m0 256) 160) := by
    refine NativeRustcVm.SameOutside.mono hch fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [show st1.data.regs.X0.toBitVec = loc m0 256 from e1x0] at hq; exact hq
    · exact absurd hq (by unfold InRange; rw [show ladderStack = 0 from rfl]; omega)
  have hc2 : Common a s layout cs m0 m2 :=
    hc1.win h hf2 (by omega) (by omega) hch' hsv.2.2 fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hcs2 _ rfl
  have hwb2 := fw_win h hf1 (o' := 256) (n' := 160) (by omega) hch'
    (fun p hp ↦ by simp only [basisWords, List.mem_cons, List.not_mem_nil, or_false] at hp
                   rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hwb
  -- `b31`: the tag
  obtain ⟨hwf3, hm3⟩ := h.frame_env hf2
  have hk31 : b31.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b31Offset) := b31_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk31 run_b31 hwf3 hm3 fun st3 hm3' hpc3 ↦ ?_
  have hc3 : Common a s layout cs m0 st3.data := hc2.blk hm3 hm3' hwf3 rfl rfl (by decide)
  have hd3 : st3.data.dmem = m2.dmem := hm3'.dmem_eq hwf3 rfl
  have k3 : ∀ r, r ≠ .X8 → st3.data.regs.getXReg r = m2.regs.getXReg r :=
    fun r h8 ↦ (rv hm3' (v := .reg r) (by cases r <;> first | rfl | exact absurd rfl h8)).trans rfl
  simp only [PcOk, lad_tag hL] at hpc3
  cases hl : Whir.ladder layout.stackLog m0.regs.X2.toNat with
  | none =>
    simp only [hl, Option.isNone_none, ↓reduceIte] at hpc3
    rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_27 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b36Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b36Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_27_at]
      at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3
    subst hpc3
    exact fail_ladder hp h hl hc3.fr
  | some ls =>
    simp only [hl, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hpc3
    rw [hl] at hL
    obtain ⟨-, hlen, hcnt, hlv⟩ := hL
    have hb31 : b31.length = NativeRustcVmArm.Vm.VerifyStackedOpening.b31Length := NativeRustcVmArm.Vm.VerifyStackedOpening.b31_length
    rw [hb31] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only at hpc3
    subst hpc3
    refine cont d3 ls ⟨hc3, by rw [hd3]; exact hwb2, hl, hlen, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hd3]
      have : NativeRustcVm.Transcript.off (loc m0 256) 8 = loc m0 264 :=
        NativeRustcVm.addr_add_add _ _ _
      rw [this] at hlv
      exact hlv
    · rw [hd3]
      have : NativeRustcVm.Transcript.off (loc m0 256) 152 = loc m0 408 :=
        NativeRustcVm.addr_add_add _ _ _
      rw [this] at hcnt
      exact hcnt
    · rw [k3 .X19 (by decide), hcs2 .X19 rfl]; exact e1x19
    · rw [k3 .X21 (by decide), hcs2 .X21 rfl]; exact e1x21
    · rw [k3 .X28 (by decide), k3 .X29 (by decide), k3 .X27 (by decide), k3 .X26 (by decide),
        hcs2 .X28 rfl, hcs2 .X29 rfl, hcs2 .X27 rfl, hcs2 .X26 rfl, e1x28, e1x29,
        k1 .X27 (by simp), k1 .X26 (by simp)]
      exact hb.claim

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
