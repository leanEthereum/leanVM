module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEval.Names
public import NativeRustcVmArm.Whir.BasisWEval.Loop

/-!
# `BasisW::eval`: the out-of-domain claim and the result

From `End` (`b19`): the next scale (`b20`), or `0` once the scales run out (`b21`): `AtB22` at
`.LBasisWEval_17` (`ood_scale`). `b22` calls `eq_eval` on the out-of-domain point (at most 30
coordinates) and the point, `b23` multiplies its weight by the scale, `b24` adds the product to
the sum and stores `Some` of it at the output, `b25` restores the registers and returns
(`finish`). The sum is `BasisW.eval` (`eval_eq`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- **At `.LBasisWEval_17`** (`b22`): the sum over the weights met (X24, X25), the next scale
(X23, X26). -/
structure AtB22 (m0 : MachineData) (b : BasisW) (v : Vals) (st : MachineData) : Prop where
  fr : Fr1 m0 st
  x21 : st.regs.X21 = m0.regs.X2
  x22 : st.regs.X22 = m0.regs.X1
  x23 : st.regs.X23 = (sAt b.scales (ws v (xpt m0) v.cs.size).size).c0
  x26 : st.regs.X26 = (sAt b.scales (ws v (xpt m0) v.cs.size).size).c1
  x24 : st.regs.X24 = (dot b.scales (ws v (xpt m0) v.cs.size)).c0
  x25 : st.regs.X25 = (dot b.scales (ws v (xpt m0) v.cs.size)).c1

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

omit [Host] in
/-- **The value**: the scales against the weights met, then the out-of-domain claim's. -/
theorem eval_eq (h : In m0 ba b v) :
    b.eval (xpt m0) = dot b.scales ((ws v (xpt m0) v.cs.size).push (eqEval v.z (xpt m0))) := by
  obtain ⟨sc, cl⟩ := b
  have he : cl = stackClaims v.L v.target v.kp v.coeffs v.cs v.z v.value := h.eq
  subst he
  rw [basis_eval]
  simp [ws, ringW]

/-- **The out-of-domain claim's scale**, from `End` at `b19` to `b22`. -/
theorem ood_scale (hp : Placed code k) (h : In m0 ba b v) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b19Offset)) (he : End m0 ba b v st.data) {R : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b22Offset) → AtB22 m0 b v st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hf := he.keep.fr
  refine hf.regsBlock (inf hp b19_in_code (by simp [b19])) run_b19 hpc rfl rfl (by rfl)
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  have hk1 : ∀ r : XReg, st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r ↦
    reg_of hm1 (v := .reg r) (by cases r <;> rfl) rfl
  rw [Env.ofMachine_regs, Env.ofMachine_regs,
    show st.data.regs.getXReg .X28 = st.data.regs.X28 from rfl,
    show st.data.regs.getXReg .X29 = st.data.regs.X29 from rfl, he.acc.x28, he.acc.x29,
    h.scale_beq] at hpc1
  have hsz := h.pre.2.1.scales_size
  by_cases hj : ba.count ≤ (ws v (xpt m0) v.cs.size).size
  · simp only [hj, decide_true, ↓reduceIte] at hpc1
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b21Offset) NativeRustcVmArm.Vm.BasisWEval.label_16_at] at hpc1
    refine hf1.regsBlock (inf hp b21_in_code (by simp [b21])) run_b21 hpc1 rfl rfl (by rfl)
      fun st2 hf2 hd2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    have hk2 : ∀ r : XReg, r ≠ .X23 → r ≠ .X26 →
        st2.data.regs.getXReg r = st.data.regs.getXReg r := fun r h23 h26 ↦
      (reg_of hm2 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl).trans (hk1 r)
    have hs0 : sAt b.scales (ws v (xpt m0) v.cs.size).size = 0 := sAt_ge (by omega)
    refine cont st2 (hpc2.trans rfl) ⟨hf2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hk2 .X21 (by decide) (by decide)).trans he.keep.x21
    · exact (hk2 .X22 (by decide) (by decide)).trans he.keep.x22
    · rw [hs0]; exact reg_of hm2 (r := .X23) rfl rfl
    · rw [hs0]; exact reg_of hm2 (r := .X26) rfl rfl
    · exact (hk2 .X24 (by decide) (by decide)).trans he.acc.x24
    · exact (hk2 .X25 (by decide) (by decide)).trans he.acc.x25
  · simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmArm.Vm.BasisWEval.b19Offset + b19.length = k + NativeRustcVmArm.Vm.BasisWEval.b20Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b19_next]] at hpc1
    have hj' : (ws v (xpt m0) v.cs.size).size < ba.count := by omega
    have hsin := h.scaleIn hj'
    let env := Env.ofMachine st1.data
      [(ba.scales + BitVec.ofNat 64 (16 * (ws v (xpt m0) v.cs.size).size), 16)]
    have hwf : env.WF := Env.wf_of ⟨mapped_of hf1 hsin, trivial⟩ (List.pairwise_singleton _ _)
    have hm : Match env (scaleS .X28) st1.data :=
      match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
        ⟨by
          show st1.data.regs.X28.toBitVec = _
          rw [show st1.data.regs.X28 = st1.data.regs.getXReg .X28 from rfl, hk1 .X28,
            show st.data.regs.getXReg .X28 = st.data.regs.X28 from rfl, he.acc.x28,
            Nat.min_eq_left (by omega)]
          simp [Sym.eval], trivial⟩
        trivial trivial trivial
    refine exec_at (inf hp b20_in_code (by simp [b20])) run_b20 hwf hpc1 hm fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b22Offset) NativeRustcVmArm.Vm.BasisWEval.label_17_at] at hpc2
    have hf2 : Fr1 m0 st2.data :=
      Fr.ofBlock hf1 hm hm2 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
    have hk2 : ∀ r : XReg, r ≠ .X23 → r ≠ .X26 → r ≠ .X28 →
        st2.data.regs.getXReg r = st.data.regs.getXReg r := fun r h23 h26 h28 ↦
      (reg_of hm2 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl).trans (hk1 r)
    obtain ⟨w0, w8⟩ := h.scaleAt hf1 hj'
    refine cont st2 hpc2 ⟨hf2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hk2 .X21 (by decide) (by decide) (by decide)).trans he.keep.x21
    · exact (hk2 .X22 (by decide) (by decide) (by decide)).trans he.keep.x22
    · exact reg_of hm2 (r := .X23) rfl (Ring.load_word w0)
    · exact reg_of hm2 (r := .X26) rfl (Ring.load_word w8)
    · exact (hk2 .X24 (by decide) (by decide) (by decide)).trans he.acc.x24
    · exact (hk2 .X25 (by decide) (by decide) (by decide)).trans he.acc.x25

/-- **The out-of-domain claim and the result**, from `b22` to the return. -/
theorem finish (hp : Placed code k) (h : In m0 ba b v)
    (heq : Spec (Labels.label NativeRustcVmArm.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b22Offset)) (ha : AtB22 m0 b v st.data) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ BasisWEvalPost b m0 s.data) st := by
  have hS := h.stackOk
  have hN := h.hN
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := stack_le
  have hf := ha.fr
  let p := m0.regs.X1.toBitVec
  let env := Env.ofMachine st.data [(base m0 144, 144), (p, 56), (ba.ood, 8)]
  have hoin := h.oodIn
  have hO := NativeRustcVm.Layout.BufEWAt.of_same h.ood.1 (same_of hN hf hoin) (by decide)
  have hlen : v.z.toList.length ≤ 30 := hO.1
  have hfa := frame_apart h h.basis
  have ho8 : WhirIn m0 ba.ood 8 basisWEvalStack := WhirIn.mono hoin (by decide)
  have hfo := frame_apart h ho8
  have hbo : Apart m0.regs.X1.toBitVec 56 ba.ood 8 :=
    NativeRustcVm.Apart.mono h.aparts.2.2.1 (Nat.le_refl _) (by unfold basisBytes; omega)
      (Nat.le_refl _) (by unfold eqClaimBytes; omega)
  obtain ⟨hfmap, hfnw⟩ := frame_of h hf
  have hwf : env.WF := by
    refine Env.wf_of ⟨⟨hfmap, hfnw⟩, mapped_of hf h.basis, mapped_of hf ho8, trivial⟩ ?_
    refine List.pairwise_cons.mpr ⟨fun r hr ↦ ?_, List.pairwise_pair.mpr hbo⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hfa.symm
    · exact hfo.symm
  have wo : NativeRustcVm.WordAt st.data.dmem (p + BitVec.ofNat 64 48)
      (UInt64.ofBitVec ba.ood) := h.word hf 6 (by decide)
  have hm : Match env oodS st.data := by
    refine match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hS hs6 rfl, rfl,
        fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hf.sp]; simp [Sym.eval]) ⟨?_, trivial⟩ trivial trivial ⟨?_, trivial⟩
    · show st.data.regs.X22.toBitVec = _
      rw [ha.x22]; simp [Sym.eval]; rfl
    · simp only [Sym.eval]
      rw [Ring.load_word (env := env) (r := 1) (off := 48) wo]
      simp
  refine exec_at (inf hp b22_in_code (by simp [b22])) run_b22 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hf1 : Fr1 m0 st1.data :=
    Fr.ofBlock hf hm hm1 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have l2 : env.load 2 0 8 = v.z.toList.length.toUInt64.toBitVec :=
    Ring.load_word (by show NativeRustcVm.WordAt st.data.dmem (ba.ood + BitVec.ofNat 64 0) _
                       rw [NativeRustcVm.addr_add_zero]; exact hO.2.1)
  have l48 : env.load 1 48 8 = ba.ood := Ring.load_word (env := env) (r := 1) (off := 48) wo
  have l16 : env.load 0 16 8 = m0.regs.X3.toBitVec :=
    Ring.load_word (env := env) (r := 0) (off := 16) (hf.slots (16, .X3) (by simp [slots, slots0]))
  have l8 : env.load 0 8 8 = m0.regs.X0.toBitVec :=
    Ring.load_word (env := env) (r := 0) (off := 8) (hf.slots (8, .X0) (by simp [slots]))
  have hlt := count_ult (N := 30) hlen (by decide)
  have hlen' : v.z.toList.length.toUInt64.toNat = v.z.toList.length :=
    natCast_toUInt64_toNat (by omega)
  have hx0 : st1.data.regs.X0 = UInt64.ofBitVec (ba.ood + BitVec.ofNat 64 8) := reg_eq <| by
    refine (hm1.regs .X0 _ rfl).trans ?_
    sym_simp
    rw [l2, l48, hlt]
    simp only [↓reduceIte]
  have hx1 : st1.data.regs.X1 = v.z.toList.length.toUInt64 := reg_eq <| by
    refine (hm1.regs .X1 _ rfl).trans ?_
    sym_simp
    rw [l2, hlt]
    simp only [↓reduceIte]
    rfl
  have hx2 : st1.data.regs.X2 = m0.regs.X2 :=
    (reg_of hm1 (r := .X2) (v := .reg .X21) rfl rfl).trans ha.x21
  have hx3 : st1.data.regs.X3 = m0.regs.X3 := reg_of hm1 (r := .X3) rfl l16
  have hx27 : st1.data.regs.X27 = m0.regs.X0 := reg_of hm1 (r := .X27) rfl l8
  have hk1 : ∀ r ∈ [XReg.X23, .X24, .X25, .X26],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact reg_of hm1 (v := .reg _) rfl rfl
  have hpre : EqEvalPre st1.data := by
    refine ⟨hf1.stackOk hS (by decide) hs4, ?_, ?_⟩
    · unfold SliceOk
      rw [hx0, hx1, hlen', UInt64.toBitVec_ofBitVec]
      exact h.argOk hf1 (WhirIn.sub hoin (o := 8) (by unfold eqClaimBytes; omega)) hs4
    · rw [hx2, hx3]; exact h.argOk hf1 h.point hs4
  have hnil : ∀ q, ¬InRange (0 : BitVec 64) 0 q := fun q hq ↦ by unfold InRange at hq; omega
  refine Fr.leafAt hf1 hN hs4 (fun _ h ↦ absurd h (by simp)) slots_le (fun _ h ↦ h.elim) heq
    hpc1 hpre (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
      (fun hq ↦ absurd hq (hnil q)) .inl, hq.2.2⟩) fun m3 hf3 hq3 hcs3 ↦ ?_
  have hw : ewRet m3 = eqEval v.z (xpt m0) := by
    rw [hq3.1]
    have hzs : slice st1.data st1.data.regs.X0 st1.data.regs.X1 = v.z := by
      unfold slice
      rw [hx0, hx1, hlen', UInt64.toBitVec_ofBitVec, hd1,
        NativeRustcVm.ewsOf_of_ewsAt hO.2.2, Array.toArray_toList]
    rw [hzs, h.xpt_eq hf1 hx2 hx3]
  have hw0 : m3.regs.X0 = (eqEval v.z (xpt m0)).c0 := congrArg EW.c0 hw
  have hw1 : m3.regs.X1 = (eqEval v.z (xpt m0)).c1 := congrArg EW.c1 hw
  -- b23
  refine hf3.regsBlock (st := ⟨m3, _⟩) (k := k + NativeRustcVmArm.Vm.BasisWEval.b23Offset) (inf hp b23_in_code (by simp [b23]))
    run_b23 rfl rfl rfl (by rfl) fun st4 hf4 hd4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  have g0 : st4.data.regs.X0 = (sAt b.scales (ws v (xpt m0) v.cs.size).size).c0 :=
    (reg_of hm4 (r := .X0) rfl rfl).trans
      ((hcs3 .X23 rfl).trans ((hk1 .X23 (by simp)).trans ha.x23))
  have g1 : st4.data.regs.X1 = (sAt b.scales (ws v (xpt m0) v.cs.size).size).c1 :=
    (reg_of hm4 (r := .X1) rfl rfl).trans
      ((hcs3 .X26 rfl).trans ((hk1 .X26 (by simp)).trans ha.x26))
  have g2 : st4.data.regs.X2 = (eqEval v.z (xpt m0)).c0 :=
    (reg_of hm4 (r := .X2) rfl rfl).trans hw0
  have g3 : st4.data.regs.X3 = (eqEval v.z (xpt m0)).c1 :=
    (reg_of hm4 (r := .X3) rfl rfl).trans hw1
  refine mul_call h slots_le hmul hf4 hpc4 fun m5 hf5 hy0 hy1 hcs5 ↦ ?_
  rw [g0, g1, g2, g3] at hy0 hy1
  have h24 : m5.regs.X24 = (dot b.scales (ws v (xpt m0) v.cs.size)).c0 :=
    (hcs5 .X24 rfl).trans ((reg_of hm4 (r := .X24) (v := .reg .X24) rfl rfl).trans
      ((hcs3 .X24 rfl).trans ((hk1 .X24 (by simp)).trans ha.x24)))
  have h25 : m5.regs.X25 = (dot b.scales (ws v (xpt m0) v.cs.size)).c1 :=
    (hcs5 .X25 rfl).trans ((reg_of hm4 (r := .X25) (v := .reg .X25) rfl rfl).trans
      ((hcs3 .X25 rfl).trans ((hk1 .X25 (by simp)).trans ha.x25)))
  have h27 : m5.regs.X27 = m0.regs.X0 :=
    (hcs5 .X27 rfl).trans ((reg_of hm4 (r := .X27) (v := .reg .X27) rfl rfl).trans
      ((hcs3 .X27 rfl).trans hx27))
  -- b24, b25
  obtain ⟨hfmap5, hfnw5⟩ := frame_of h hf5
  have hwf5 : (Env.ofMachine m5 [(base m0 144, 144), (m0.regs.X0.toBitVec, 24)]).WF :=
    Env.wf_of ⟨⟨hfmap5, hfnw5⟩, mapped_of hf5 h.out, trivial⟩
      (List.pairwise_pair.mpr (frame_apart h h.out).symm)
  have hm5 : Match (Env.ofMachine m5 [(base m0 144, 144), (m0.regs.X0.toBitVec, 24)]) outS m5 :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hS hs6 rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by rw [hf5.sp]; simp [Sym.eval])
      ⟨by show m5.regs.X27.toBitVec = _; rw [h27]; simp [Sym.eval], trivial⟩
      trivial trivial trivial
  refine exec_at (st := ⟨m5, _⟩) (inf hp b24_in_code (by simp [b24])) run_b24 hwf5 rfl hm5
    fun st6 hm6 hpc6 ↦ ?_
  simp only [PcOk] at hpc6
  refine exec_at (inf hp b25_in_code (by simp [b25])) (exec_after run_b24 run_b25) hwf5 hpc6 hm6
    fun st7 hm7 hpc7 ↦ .done _ ?_
  simp only [PcOk] at hpc7
  obtain ⟨hret, hsaved⟩ := hf5.exit hm7 hwf5 (by decide)
  have hb1 : (Env.ofMachine m5 [(base m0 144, 144), (m0.regs.X0.toBitVec, 24)]).regions[1]? =
      some (m0.regs.X0.toBitVec, 24) := rfl
  refine ⟨hpc7.trans hret, ?_⟩
  show NativeRustcVm.Transcript.OptEWAt st7.data.dmem m0.regs.X0.toBitVec
      (some (b.eval (slice m0 m0.regs.X2 m0.regs.X3))) ∧
    ChangesIn m0 st7.data basisWEvalStack [⟨m0.regs.X0.toBitVec, 24⟩] ∧ Saved m0 st7.data
  refine ⟨⟨?_, ?_⟩, ?_, hsaved⟩
  · have := Match.wordAt_write hm7 hb1 (o := 0) (by decide) (v := .lit 1)
      (fun i hi ↦ by revert i; decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  · rw [show slice m0 m0.regs.X2 m0.regs.X3 = xpt m0 from rfl, eval_eq h, NativeRustcVm.ewAt_iff]
    have hd := dot_push_c b.scales (ws v (xpt m0) v.cs.size) (eqEval v.z (xpt m0))
    refine ⟨?_, ?_⟩
    · have := Match.wordAt_write hm7 hb1 (o := 8) (by decide)
        (v := .bin .eor .W64 (.reg .X0) (.reg .X24)) (fun i hi ↦ by revert i; decide)
      have e : UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg .X0) (.reg .X24)).eval
          (Env.ofMachine m5 [(base m0 144, 144), (m0.regs.X0.toBitVec, 24)])) =
          (dot b.scales ((ws v (xpt m0) v.cs.size).push (eqEval v.z (xpt m0)))).c0 := by
        rw [hd.1]
        simp only [Sym.eval, BinOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs]
        rw [show m5.regs.getXReg .X0 = m5.regs.X0 from rfl, hy0,
          show m5.regs.getXReg .X24 = m5.regs.X24 from rfl, h24]
        rfl
      rw [← e]
      exact this
    · have := Match.wordAt_write hm7 hb1 (o := 16) (by decide)
        (v := .bin .eor .W64 (.reg .X1) (.reg .X25)) (fun i hi ↦ by revert i; decide)
      have e : UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg .X1) (.reg .X25)).eval
          (Env.ofMachine m5 [(base m0 144, 144), (m0.regs.X0.toBitVec, 24)])) =
          (dot b.scales ((ws v (xpt m0) v.cs.size).push (eqEval v.z (xpt m0)))).c1 := by
        rw [hd.2]
        simp only [Sym.eval, BinOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs]
        rw [show m5.regs.getXReg .X1 = m5.regs.X1 from rfl, hy1,
          show m5.regs.getXReg .X25 = m5.regs.X25 from rfl, h25]
        rfl
      rw [← e, NativeRustcVm.Transcript.off_add]
      exact this
  · intro a ha
    rw [hm7.get?_mem0 hwf5 fun hw ↦ ha (.inl ⟨_, List.mem_singleton_self _,
      Written.inRange (r := 1) rfl h.out.1.2 (by decide) hw⟩)]
    exact hf5.same a fun h' ↦ ha (h'.elim .inr False.elim)

end

end NativeRustcVmArm.Whir.BasisWEval
