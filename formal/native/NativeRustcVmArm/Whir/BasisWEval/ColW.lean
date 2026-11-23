module

public import NativeRustcVmArm.Code.Vm.ColumnWeight.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.BasisWEval.Col

/-!
# `BasisW::eval`: a column claim's weight

From `AtB15` (`b15`): `column_weight` on the placement, the claim's point (at most 36 coordinates)
and the stack's log-size (at most 30), its `Option<EW>` at `sp + 24`, `Some` since
`36 + 30 ≤ 66`; `b16` falls into `b17`, which multiplies the weight by the scale; `b18` adds the
product to the sum: `AtB9 i` at `b9` (`col_weight`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak Placement)

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

omit [Host] in
/-- The areas `b15` reads, pairwise apart. -/
theorem b15_apart (h : In m0 ba b v) {i : Nat} (hi : i < v.cs.size) {c : Nat} (hc : c < 158) :
    [(base m0 144, 144), (cA ba i, 608), (pA ba c, 24), (ba.layout, 24)].Pairwise
      fun e e' ↦ Apart e.1 e.2 e'.1 e'.2 := by
  have hL := h.layoutIn
  have hC := h.claimsIn
  have hLC := h.aparts.2.2.2
  have hle := h.claims.len_le
  unfold claimCap at hle
  have a1 : Apart (cA ba i) 608 (pA ba c) 24 :=
    (apart_sub (o := 120 + 24 * c) (n' := 24) (o' := 8 + 608 * i) (m' := 608) hLC hL.1.2 hC.1.2
      (by unfold layoutBytes placementBytes columnCountW; omega)
      (by unfold claimsBytes columnClaimBytes claimCap; omega)).symm
  have a2 : Apart (cA ba i) 608 ba.layout 24 := by
    have := (apart_sub (o := 0) (o' := 8 + 608 * i) (n' := 24) (m' := 608) hLC hL.1.2 hC.1.2
      (by unfold layoutBytes; omega) (by unfold claimsBytes columnClaimBytes claimCap; omega)).symm
    rw [NativeRustcVm.Transcript.off_zero] at this
    exact this
  have a3 : Apart (pA ba c) 24 ba.layout 24 := by
    have := NativeRustcVm.apart_of_le (o := 120 + 24 * c) (n := 24) (o' := 0) (n' := 24) hL.1.2
      (by unfold layoutBytes placementBytes columnCountW; omega)
      (by unfold layoutBytes; omega) (by omega)
    rwa [NativeRustcVm.addr_add_zero] at this
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true]
  exact ⟨⟨(frame_apart h (h.claimIn hi)).symm, (frame_apart h (h.placeIn hc)).symm,
    (frame_apart h (WhirIn.mono hL (by unfold layoutBytes; omega))).symm⟩, ⟨a1, a2⟩, a3,
    fun _ h ↦ h.elim⟩

/-- **Column claim `i`'s weight**, from `b15` to `b9`. -/
theorem col_weight (hp : Placed code k) (h : In m0 ba b v)
    (hcw : Spec (Labels.label NativeRustcVmArm.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat} {pl : Placement}
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b15Offset)) (ha : AtB15 m0 ba b v i pl st.data)
    {R : MachineState → Prop}
    (hb9 : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b9Offset) → AtB9 m0 ba b v i st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hS := h.stackOk
  have hN := h.hN
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := stack_le
  have hf := ha.keep.fr
  have hi := ha.ilt
  have hc := ha.clt
  let env := Env.ofMachine st.data
    [(base m0 144, 144), (cA ba i, 608), (pA ba v.cs[i].column, 24), (ba.layout, 24)]
  obtain ⟨hfmap, hfnw⟩ := frame_of h hf
  have hwf : env.WF :=
    Env.wf_of ⟨⟨hfmap, hfnw⟩, mapped_of hf (h.claimIn hi), mapped_of hf (h.placeIn hc),
      mapped_of hf (WhirIn.mono h.layoutIn (by unfold layoutBytes; omega)), trivial⟩
      (b15_apart h hi hc)
  have hm : Match env cwS st.data := by
    refine match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hS hs6 rfl, rfl,
        fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) ⟨?_, ?_, ?_, trivial⟩ trivial trivial trivial
    · show st.data.regs.X20.toBitVec = _
      rw [ha.x20]; rfl
    · show st.data.regs.X8.toBitVec = _
      rw [ha.x8]; simp [Sym.eval]
    · show st.data.regs.X23.toBitVec = _
      rw [ha.keep.x23]; simp [Sym.eval]
  refine exec_at (inf hp b15_in_code (by simp [b15])) run_b15 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hf1 : Fr1 m0 st1.data :=
    Fr.ofBlock hf hm hm1 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have hca := h.claimAt hf hi
  obtain ⟨hplen, hpw, hpts⟩ := hca.point
  have hidx : v.cs[i].column < v.L.placements.size := by
    rw [h.layout.placements_size]; unfold columnCountW; omega
  have hpl : v.L.placements[v.cs[i].column] = some pl := by
    have := ha.pl
    rwa [Array.getElem?_eq_getElem hidx] at this
  have hLa := h.layoutAt hf
  have hplw := hLa.placements _ hidx
  rw [hpl] at hplw
  obtain ⟨-, hvc, hix, hwv, hwi⟩ := hplw
  have lLen : env.load 1 8 8 = v.cs[i].point.toList.length.toUInt64.toBitVec :=
    Ring.load_word (env := env) (r := 1) (off := 8) hpw
  have lVc : env.load 2 8 8 = pl.variableCount.toUInt64.toBitVec :=
    Ring.load_word (env := env) (r := 2) (off := 8) hwv
  have lIx : env.load 2 16 8 = pl.index.toUInt64.toBitVec :=
    Ring.load_word (env := env) (r := 2) (off := 16) hwi
  have lLog : env.load 3 16 8 = v.L.stackLog.toUInt64.toBitVec :=
    Ring.load_word (env := env) (r := 3) (off := 16) hLa.stack_log
  have lX3 : env.load 0 16 8 = m0.regs.X3.toBitVec :=
    Ring.load_word (env := env) (r := 0) (off := 16) (hf.slots (16, .X3) (by simp [slots, slots0]))
  have hlen : v.cs[i].point.toList.length ≤ 36 := hplen
  have hlen' : v.cs[i].point.toList.length.toUInt64.toNat = v.cs[i].point.toList.length :=
    natCast_toUInt64_toNat (by omega)
  have hlt := count_ult (N := 36) hlen (by decide)
  have hx0 : st1.data.regs.X0.toBitVec = base m0 144 + BitVec.ofNat 64 24 := by
    refine (hm1.regs .X0 _ rfl).trans ?_
    simp [Sym.eval]; rfl
  have hx1 : st1.data.regs.X1 = pl.variableCount.toUInt64 := reg_of hm1 (r := .X1) rfl lVc
  have hx2 : st1.data.regs.X2 = pl.index.toUInt64 := reg_of hm1 (r := .X2) rfl lIx
  have hx3 : st1.data.regs.X3 = UInt64.ofBitVec (cA ba i + BitVec.ofNat 64 16) := reg_eq <| by
    refine (hm1.regs .X3 _ rfl).trans ?_
    sym_simp
    rw [lLen, hlt]
    simp only [↓reduceIte]
    rfl
  have hx4 : st1.data.regs.X4 = v.cs[i].point.toList.length.toUInt64 := reg_eq <| by
    refine (hm1.regs .X4 _ rfl).trans ?_
    sym_simp
    rw [lLen, hlt]
    simp only [↓reduceIte]
    rfl
  have hx5 : st1.data.regs.X5 = v.L.stackLog.toUInt64 := reg_of hm1 (r := .X5) rfl lLog
  have hx6 : st1.data.regs.X6 = m0.regs.X2 :=
    (reg_of hm1 (r := .X6) (v := .reg .X21) rfl rfl).trans ha.keep.x21
  have hx7 : st1.data.regs.X7 = m0.regs.X3 := reg_of hm1 (r := .X7) rfl lX3
  have hpre : ColumnWeightPre st1.data := by
    refine ⟨hf1.stackOk hS (by decide) hs3, ?_, ?_, ?_, ?_⟩
    · unfold SliceOk
      rw [hx3, hx4, hlen', UInt64.toBitVec_ofBitVec]
      exact h.argOk hf1 (WhirIn.sub (h.claimIn hi) (by omega)) hs3
    · rw [hx6, hx7]; exact h.argOk hf1 h.point hs3
    · show Readable _ _ _ ∧ OffStack _ _ _ _
      rw [hx0]; exact frame_out h hf1 hs3
    · rw [hx4, hlen']; omega
  have hk1 : ∀ r, calleeSaved r = true → st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    cases r <;> simp [calleeSaved] at hr <;> first
      | exact reg_of hm1 rfl rfl
      | exact reg_of hm1 (r := .X20) (v := .ptr 1 16) rfl (by
          show _ = st.data.regs.X20.toBitVec
          rw [ha.x20]; rfl)
      | exact reg_of hm1 (r := .X23) (v := .ptr 3 0) rfl (by
          show env.base 3 + BitVec.ofInt 64 0 = st.data.regs.X23.toBitVec
          rw [ha.keep.x23, UInt64.toBitVec_ofBitVec, show BitVec.ofInt 64 0 = 0#64 from rfl,
            BitVec.add_zero]
          rfl)
  refine Fr.leafIn hf1 hN hs3 (lo := 24) (n := 24) (by decide) (fun _ h ↦ absurd h (by simp))
    (by decide) (fun _ h ↦ h.elim) hcw hpc1 hpre (fun m' hq ↦ ⟨?_, hq.2.2⟩)
    fun m2 hf2 hq2 hcs2 ↦ ?_
  · refine NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ ?_
    rcases hq with hq | hq
    · rw [hx0] at hq; exact .inr (.inl hq)
    · exact .inl hq
  have hlog := h.log
  have hcond : st1.data.regs.X4.toNat + (st1.data.regs.X5.toNat - st1.data.regs.X1.toNat) ≤ 66 := by
    rw [hx4, hx5, hlen', natCast_toUInt64_toNat (by omega)]
    omega
  have hpa : placementArg st1.data = pl :=
    placementArg_eq ⟨hvc, hix⟩ hx1 hx2
  have hpt : slice st1.data st1.data.regs.X3 st1.data.regs.X4 = v.cs[i].point := by
    unfold slice
    rw [hx3, hx4, hlen', UInt64.toBitVec_ofBitVec, hd1,
      show cA ba i + BitVec.ofNat 64 16 = NativeRustcVm.Transcript.off (cA ba i) 8 + 8#64 from
        (NativeRustcVm.Transcript.off_add _ 8 8).symm,
      NativeRustcVm.ewsOf_of_ewsAt hpts, Array.toArray_toList]
  have hw2 := hq2.1
  simp only [hcond, ↓reduceIte] at hw2
  rw [hx0, hpa, hpt, hx5, natCast_toUInt64_toNat (by omega), h.xpt_eq hf1 hx6 hx7] at hw2
  simp only [StackWeight.eval] at hw2
  set w := eqEval (stackPoint pl v.cs[i].point v.L.stackLog) (xpt m0) with hwdef
  obtain ⟨htag, hval⟩ := hw2
  have hval' := NativeRustcVm.ewAt_iff.mp hval
  have hc2 : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ (hcs2 r hr).trans (hk1 r hr)
  -- b16
  obtain ⟨hwf2, hm2⟩ := frame_env h hf2
  refine exec_at (inf hp b16_in_code (by simp [b16])) run_b16 hwf2 rfl hm2 fun st3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  rw [Ring.load_word htag] at hpc3
  simp only [show ((1 : UInt64).toBitVec == 0#64) = false from rfl, Bool.false_eq_true,
    ↓reduceIte] at hpc3
  have hf3 : Fr1 m0 st3.data :=
    Fr.ofBlock hf2 hm2 hm3 hwf2 rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have hd3 : st3.data.dmem = m2.dmem := hm3.dmem_eq hwf2 rfl
  have hk3 : ∀ r : XReg, r ≠ .X8 → st3.data.regs.getXReg r = m2.regs.getXReg r :=
    fun r h8 ↦ reg_of hm3 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  -- b17
  obtain ⟨hwf3, hm3'⟩ := frame_env h hf3
  refine exec_at (inf hp b17_in_code (by simp [b17])) run_b17 hwf3 hpc3 hm3' fun st4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  have hf4 : Fr1 m0 st4.data :=
    Fr.ofBlock hf3 hm3' hm4 hwf3 rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have hk4 : ∀ r : XReg, r ≠ .X0 → r ≠ .X1 → r ≠ .X2 → r ≠ .X3 → r ≠ .X30 →
      st4.data.regs.getXReg r = st3.data.regs.getXReg r := fun r h0 h1 h2 h3 h30 ↦
    reg_of hm4 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have hv1 : NativeRustcVm.WordAt st3.data.dmem (base m0 144 + BitVec.ofNat 64 32) w.c0 := by
    rw [hd3]; simpa [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] using hval'.1
  have hv2 : NativeRustcVm.WordAt st3.data.dmem (base m0 144 + BitVec.ofNat 64 40) w.c1 := by
    rw [hd3]; simpa [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] using hval'.2
  have g0 : st4.data.regs.X0 = (sAt b.scales (ws v (xpt m0) i).size).c0 :=
    (reg_of hm4 (r := .X0) rfl rfl).trans
      (((hk3 .X26 (by decide)).trans (hc2 .X26 rfl)).trans ha.x26)
  have g1 : st4.data.regs.X1 = (sAt b.scales (ws v (xpt m0) i).size).c1 :=
    (reg_of hm4 (r := .X1) rfl rfl).trans
      (((hk3 .X27 (by decide)).trans (hc2 .X27 rfl)).trans ha.x27)
  have g2 : st4.data.regs.X2 = w.c0 := reg_of hm4 (r := .X2) rfl (Ring.load_word hv1)
  have g3 : st4.data.regs.X3 = w.c1 := reg_of hm4 (r := .X3) rfl (Ring.load_word hv2)
  refine mul_call h slots_le hmul hf4 hpc4 fun m5 hf5 hy0 hy1 hcs5 ↦ ?_
  rw [g0, g1, g2, g3] at hy0 hy1
  have hc5 : ∀ r, calleeSaved r = true → m5.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ (hcs5 r hr).trans ((hk4 r (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)).trans
      ((hk3 r (by rintro rfl; simp [calleeSaved] at hr)).trans (hc2 r hr)))
  -- b18
  refine hf5.regsBlock (st := ⟨m5, _⟩) (k := k + NativeRustcVmArm.Vm.BasisWEval.b18Offset) (inf hp b18_in_code (by simp [b18])) run_b18
    rfl rfl rfl (by rfl) fun st6 hf6 hd6 hm6 hpc6 ↦ ?_
  simp only [PcOk] at hpc6
  rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b9Offset) NativeRustcVmArm.Vm.BasisWEval.label_6_at] at hpc6
  have hk6 : ∀ r : XReg, r ≠ .X24 → r ≠ .X25 → st6.data.regs.getXReg r = m5.regs.getXReg r :=
    fun r h24 h25 ↦ reg_of hm6 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have hws : ws v (xpt m0) (i + 1) = (ws v (xpt m0) i).push w := by
    rw [ws_succ _ _ hi, ha.pl]
  have hd := dot_push_c b.scales (ws v (xpt m0) i) w
  have e : ∀ r : XReg, r ≠ .X24 → r ≠ .X25 → calleeSaved r = true →
      st6.data.regs.getXReg r = st.data.regs.getXReg r := fun r h24 h25 hr ↦
    (hk6 r h24 h25).trans (hc5 r hr)
  refine hb9 st6 hpc6 {
    keep := ⟨hf6, (e .X21 (by decide) (by decide) rfl).trans ha.keep.x21,
      (e .X22 (by decide) (by decide) rfl).trans ha.keep.x22,
      (e .X23 (by decide) (by decide) rfl).trans ha.keep.x23⟩
    acc := ⟨?_, ?_, ?_, ?_⟩
    ilt := hi
    x19 := by
      rw [show st6.data.regs.X19 = st6.data.regs.getXReg .X19 from rfl,
        e .X19 (by decide) (by decide) rfl]; exact ha.x19
    x20 := by
      rw [show st6.data.regs.X20 = st6.data.regs.getXReg .X20 from rfl,
        e .X20 (by decide) (by decide) rfl, cA_16]; exact ha.x20 }
  · rw [hws, hd.1]
    refine (reg_of hm6 (r := .X24) rfl rfl).trans ?_
    simp only [Sym.eval, Sym.low_W64, Env.ofMachine_regs]
    rw [hc5 .X24 rfl, show st.data.regs.getXReg .X24 = st.data.regs.X24 from rfl, ha.x24,
      show m5.regs.getXReg .X0 = m5.regs.X0 from rfl, hy0]
    rfl
  · rw [hws, hd.2]
    refine (reg_of hm6 (r := .X25) rfl rfl).trans ?_
    simp only [Sym.eval, Sym.low_W64, Env.ofMachine_regs]
    rw [hc5 .X25 rfl, show st.data.regs.getXReg .X25 = st.data.regs.X25 from rfl, ha.x25,
      show m5.regs.getXReg .X1 = m5.regs.X1 from rfl, hy1]
    rfl
  · rw [hws, Array.size_push, show st6.data.regs.X28 = st6.data.regs.getXReg .X28 from rfl,
      e .X28 (by decide) (by decide) rfl]
    exact ha.x28
  · rw [show st6.data.regs.X29 = st6.data.regs.getXReg .X29 from rfl,
      e .X29 (by decide) (by decide) rfl]
    exact ha.x29

end

end NativeRustcVmArm.Whir.BasisWEval
