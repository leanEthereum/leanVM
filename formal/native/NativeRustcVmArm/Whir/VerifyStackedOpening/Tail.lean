module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.VerifyStackedOpening.Names
public import NativeRustcVmArm.Whir.VerifyStackedOpening.TgtLoop
public import NativeRustcVm.Top.Same

/-!
# `verify_stacked_opening`: the out-of-domain term

`tgt_run`: the target's loop to `b26`. `tail_b26`: at `b26` a scale is left (the count is
`placed + 2`), `b27` reads it, `b29` reloads the claims' and the out-of-domain claim's addresses
and calls `EW::mul` on the scale and the out-of-domain value: at `b30` the batched target is the
product plus X27, X26 (`AtB30`).
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening

@[expose] public section

/-- The batched target: the scales against the stack claims' values. -/
def claimOf (s : TState) (layout : LayoutW) (target : EW) (cs : Array ColumnClaimW) (value : EW) :
    EW :=
  dotL (scalesOf s layout cs).toList (valsOf layout target cs value)

/-- **At `b30`**: the last term in X0, X1, the others' sum in X27, X26, the claims' and the
out-of-domain claim's addresses in X20, X19. -/
structure AtB30 [Labels] (a : DecArea) (s : TState) (layout : LayoutW) (target : EW)
    (cs : Array ColumnClaimW) (value : EW) (m0 st : MachineData) : Prop where
  com : Common a s layout cs m0 st
  x19 : st.regs.getXReg .X19 = m0.regs.X6
  x20 : st.regs.getXReg .X20 = m0.regs.X5
  claim : (⟨st.regs.X0, st.regs.X1⟩ : EW) + ⟨st.regs.getXReg .X27, st.regs.getXReg .X26⟩ =
    claimOf s layout target cs value

end

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **The target's loop** to `b26`. -/
theorem tgt_run (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {R : MachineState → Prop}
    (fin : ∀ st, AtB26 a s layout target cs value m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset)⟩) :
    ∀ n i st, cs.size - i = n → Tgt a s layout target cs value m0 i st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b22Offset)⟩ := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro i st hn ht
    exact tgt_step hp h hmul ht (fun st' ht' ↦
      ih (cs.size - (i + 1)) (by have := ht.hi; omega) (i + 1) st' rfl ht') fin

omit [Host] in
/-- The last value is the out-of-domain claim's. -/
theorem vals_last (target value : EW) :
    (valsOf layout target cs value)[1 + placedOf layout cs cs.size]? = some value := by
  have hl : ((cs.toList.filterMap (·.onStack layout)).map (·.value)).length =
      placedOf layout cs cs.size := by
    simp [placedOf, List.take_of_length_le]
  rw [Nat.add_comm, valsOf, List.getElem?_cons_succ, List.getElem?_append_right (by omega), hl,
    Nat.sub_self]
  rfl

/-- **From `b26`** to `b30`: the out-of-domain term. -/
theorem tail_b26 (hp : Placed code k)
    (h : Parts a s layout target coefficients point slices cs z value m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {R : MachineState → Prop}
    (cont : ∀ st, AtB30 a s layout target cs value m0 st →
      Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b30Offset)⟩)
    {st : MachineData} (hb : AtB26 a s layout target cs value m0 st) :
    Eventually (step1 Host.exe) R ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset)⟩ := by
  have hc := hb.com
  have hP : placedOf layout cs cs.size ≤ 160 := (placedOf_le_self _).trans h.cl.len_le
  have hscb : scalesBytes = 2600 := rfl
  have hnw := h.sc_nw
  rw [hscb] at hnw
  have hsc : ∀ o, o < 2600 → (scA m0 + BitVec.ofNat 64 o).toNat = (scA m0).toNat + o :=
    fun o ho ↦ NativeRustcVm.toNat_add_ofNat (by unfold NoWrap at hnw; omega)
  have hS := h.hS
  -- `b26`: a scale is left
  have hk26 : b26.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b26Offset) := b26_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine hc.fr.regsBlock (st := ⟨st, _⟩) hk26 run_b26 rfl rfl rfl rfl
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  have k1 : ∀ r, st1.data.regs.getXReg r = st.regs.getXReg r := fun r ↦
    (rv hm1 (v := .reg r) (by cases r <;> rfl)).trans rfl
  have hc1 : Common a s layout cs m0 st1.data := hc.same hf1 hd1 fun r _ ↦ k1 r
  have hne : ((st.regs.getXReg .X19).toBitVec == (st.regs.getXReg .X21).toBitVec) = false := by
    rw [hb.x19, hb.x21]
    apply beq_eq_false_iff_ne.mpr
    intro he
    have := congrArg BitVec.toNat he
    rw [hsc _ (by omega), BitVec.toNat_add, BitVec.toNat_ofNat] at this
    unfold cntOf at this
    unfold NoWrap at hnw
    have h1 : 8 + 16 * (placedOf layout cs cs.size + 2) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h1] at this
    omega
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [Env.ofMachine_regs, hne, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b27`: the last scale
  obtain ⟨sa, hsad⟩ : ∃ sa, sa = scA m0 +
      BitVec.ofNat 64 (8 + 16 * (1 + placedOf layout cs cs.size)) := ⟨_, rfl⟩
  have hsaN : sa.toNat = (scA m0).toNat + (8 + 16 * (1 + placedOf layout cs cs.size)) := by
    rw [hsad]; exact hsc _ (by omega)
  let env2 := Env.ofMachine st1.data [(sa, 16)]
  have hwf2 : env2.WF :=
    Env.wf_of ⟨⟨fun j hj ↦ by
        rw [hsad, NativeRustcVm.addr_add_add]
        exact hc1.fr.kept _ (h.so.1.1 _ (by rw [hscb]; omega)),
      by show sa.toNat + 16 ≤ 2 ^ 64; rw [hsaN]; unfold NoWrap at hnw; omega⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm2 : Match env2 scale2S st1.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by show (st1.data.regs.getXReg .X19).toBitVec = _; rw [k1, hb.x19, hsad]; simp [Sym.eval],
        trivial⟩ trivial trivial trivial
  have hlen : 1 + placedOf layout cs cs.size < (scalesOf s layout cs).toList.length := by
    rw [Array.length_toList, size_scalesOf]; unfold cntOf; omega
  have hsce := NativeRustcVm.ewAt_iff.mp (NativeRustcVm.ewsAt_getElem hc1.scs hlen)
  rw [NativeRustcVm.addr_add_add, ← hsad] at hsce
  have hl0 : env2.load 0 0 8 =
      (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size].c0.toBitVec := by
    refine Ring.load_word ?_
    show NativeRustcVm.WordAt st1.data.dmem (sa + BitVec.ofNat 64 0) _
    rw [NativeRustcVm.addr_add_zero]; exact hsce.1
  have hl8 : env2.load 0 8 8 =
      (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size].c1.toBitVec :=
    Ring.load_word hsce.2
  have hk27 : b27.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b27Offset) := b27_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk27 run_b27 hwf2 hpc1 hm2 fun st2 hm2' hpc2 ↦ ?_
  have hc2 : Common a s layout cs m0 st2.data := hc1.blk hm2 hm2' hwf2 rfl rfl (by decide)
  have k2 : ∀ r ∈ [XReg.X26, .X27], st2.data.regs.getXReg r = st1.data.regs.getXReg r :=
    fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (rv hm2' rfl).trans rfl
  have e2x0 : st2.data.regs.X0 = (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size].c0 :=
    (rv hm2' (r := .X0) rfl).trans (by show UInt64.ofBitVec (env2.load 0 0 8) = _; rw [hl0])
  have e2x1 : st2.data.regs.X1 = (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size].c1 :=
    (rv hm2' (r := .X1) rfl).trans (by show UInt64.ofBitVec (env2.load 0 8 8) = _; rw [hl8])
  simp only [PcOk] at hpc2
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyStackedOpening.label_24 = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b29Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyStackedOpening.b29Offset) NativeRustcVmArm.Vm.VerifyStackedOpening.label_24_at]
    at hpc2
  -- `b29`: the out-of-domain value, `EW::mul`
  have hoin := h.in_ok hc2.fr mem_ood
  simp only at hoin
  have hob : NativeRustcVm.Layout.eqClaimBytes = 504 := rfl
  rw [hob] at hoin
  let env3 := Env.ofMachine st2.data [(base m0 512, 512), (m0.regs.X6.toBitVec, 504)]
  have hwf3 : env3.WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hc2.fr.kept _ (Ring.frame_mapped h.wt.1 (by rw [stack_eq]; decide) i hi),
        base_noWrap (by omega)⟩, ⟨hoin.1, hoin.2.1⟩, trivial⟩
      (List.pairwise_pair.mpr hoin.2.2)
  have hb0 : env3.base 0 = base m0 512 := rfl
  have hm3 : Match env3 oodS st2.data :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned h.wt.1 (by rw [stack_eq]; decide) rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hc2.fr.sp]; simp [Sym.eval]) trivial trivial trivial
      ⟨by
        show env3.load 0 40 8 = m0.regs.X6.toBitVec + BitVec.ofInt 64 0
        rw [fw_load (o := 40) (v := m0.regs.X6) hb0 hc2.fw (by simp)]
        simp, trivial⟩
  have hood := (NativeRustcVm.Top.EqClaimAt.of_same h.ood (h.same_in hc2.fr mem_ood)).2
  have hov := NativeRustcVm.ewAt_iff.mp hood
  have hv0 : env3.load 1 488 8 = value.c0.toBitVec := Ring.load_word hov.1
  have hv8 : env3.load 1 496 8 = value.c1.toBitVec := by
    refine Ring.load_word ?_
    have := hov.2
    rwa [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] at this
  have hk29 : b29.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyStackedOpening.b29Offset) := b29_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk29 run_b29 hwf3 hpc2 hm3 fun st3 hm3' hpc3 ↦ ?_
  have hc3 : Common a s layout cs m0 st3.data := hc2.blk hm3 hm3' hwf3 rfl rfl (by decide)
  have e3x20 : st3.data.regs.getXReg .X20 = m0.regs.X5 :=
    (rv hm3' (r := .X20) rfl).trans (by
      show UInt64.ofBitVec (env3.load 0 32 8) = _
      rw [fw_load (o := 32) (v := m0.regs.X5) hb0 hc2.fw (by simp)])
  have e3x19 : st3.data.regs.getXReg .X19 = m0.regs.X6 :=
    (rv hm3' (r := .X19) rfl).trans (by
      show UInt64.ofBitVec (env3.load 0 40 8) = _
      rw [fw_load (o := 40) (v := m0.regs.X6) hb0 hc2.fw (by simp)])
  have k3 : ∀ r ∈ [XReg.X26, .X27], st3.data.regs.getXReg r = st2.data.regs.getXReg r :=
    fun r hr ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (rv hm3' rfl).trans rfl
  have e3 : (⟨st3.data.regs.X0, st3.data.regs.X1⟩ : EW) =
      (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size] := by
    rw [show st3.data.regs.X0 = st2.data.regs.X0 from (rv hm3' (r := .X0) rfl).trans rfl,
      show st3.data.regs.X1 = st2.data.regs.X1 from (rv hm3' (r := .X1) rfl).trans rfl, e2x0,
      e2x1]
  have e3' : (⟨st3.data.regs.X2, st3.data.regs.X3⟩ : EW) = value := by
    rw [show st3.data.regs.X2 = UInt64.ofBitVec (env3.load 1 488 8) from
        (rv hm3' (r := .X2) rfl).trans rfl,
      show st3.data.regs.X3 = UInt64.ofBitVec (env3.load 1 496 8) from
        (rv hm3' (r := .X3) rfl).trans rfl, hv0, hv8]
  refine mul_call h hmul hc3.fr hpc3 fun m4 hf4 h0 h1 hcs4 hs4 hk4 ↦ ?_
  have hc4 := hc3.call h hf4 (by rw [stack_eq]; decide) hs4 hk4 hcs4
  rw [e3, e3'] at h0 h1
  have hlv : 1 + placedOf layout cs cs.size < (valsOf layout target cs value).length := by
    rw [length_valsOf]; omega
  have hvv : (valsOf layout target cs value)[1 + placedOf layout cs cs.size] = value := by
    have := vals_last (layout := layout) (cs := cs) target value
    rw [List.getElem?_eq_getElem hlv] at this
    exact Option.some.inj this
  refine cont m4 ⟨hc4, by rw [hcs4 .X19 rfl, e3x19], by rw [hcs4 .X20 rfl, e3x20], ?_⟩
  have hacc := hb.acc
  rw [hcs4 .X27 rfl, hcs4 .X26 rfl, k3 .X27 (by simp), k3 .X26 (by simp), k2 .X27 (by simp),
    k2 .X26 (by simp), k1, k1, hacc]
  have hfull : claimOf s layout target cs value =
      dotL ((scalesOf s layout cs).toList.take (1 + placedOf layout cs cs.size + 1))
        ((valsOf layout target cs value).take (1 + placedOf layout cs cs.size + 1)) := by
    unfold claimOf
    rw [List.take_of_length_le (by rw [Array.length_toList, size_scalesOf]; unfold cntOf; omega),
      List.take_of_length_le (by rw [length_valsOf]; omega)]
  have hterm : (⟨m4.regs.X0, m4.regs.X1⟩ : EW) =
      (scalesOf s layout cs).toList[1 + placedOf layout cs cs.size] * value := by
    rw [h0, h1]
    rfl
  rw [hterm, hfull, dotL_take_succ hlen hlv, hvv]
  exact ew_add_comm' _ _

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
