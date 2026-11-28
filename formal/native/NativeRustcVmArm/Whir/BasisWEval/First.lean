module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Whir.BasisWEval.Ring

/-!
# `BasisW::eval`: the first product

After `ring_claim_weight` (`Some` at `sp + 24`): `b5` falls into `b6`, which saves the output's
address at `sp + 8`, sets X29 to the scales' end and multiplies the first scale by the weight;
`b7` keeps the product (X24, X25) and reads the column claims' count: none, `End` at `b19`; else
`b8` sets X20 16 bytes into the first claim, `Loop 0` at `b10` (`first`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak Placement)

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

omit [Host] in
theorem mul608 {n : Nat} (hn : n ≤ claimCap) :
    (n.toUInt64.toBitVec * 608#64).toNat = 608 * n := by
  have e : n.toUInt64.toBitVec.toNat = n := by
    rw [UInt64.toNat_toBitVec]; exact natCast_toUInt64_toNat (by unfold claimCap at hn; omega)
  rw [BitVec.toNat_mul, e, show (608#64).toNat = 608 from rfl]
  unfold claimCap at hn
  omega

omit [Host] in
theorem slots0_le : ∀ p ∈ slots0, p.1 + 8 ≤ 144 := by decide
omit [Host] in
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 144 := by decide

/-- **The first product**, from `b5` to `Loop 0` or `End`. -/
theorem first (hp : Placed code k) (h : In m0 ba b v)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {st0 : MachineState} (ha : At4 m0 ba b v st0.data)
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b5Offset))
    (hw : NativeRustcVm.Transcript.OptEWAt st.data.dmem (base m0 144 + BitVec.ofNat 64 24)
      (some (ringW v (xpt m0))))
    (hf : Fr0 m0 st.data)
    (hcs : ∀ r, calleeSaved r = true → st.data.regs.getXReg r = st0.data.regs.getXReg r)
    {R : MachineState → Prop}
    (hloop : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b10Offset) → Loop m0 ba b v 0 st'.data →
      Eventually (step1 Host.exe) R st')
    (hend : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b19Offset) → End m0 ba b v st'.data →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hN := h.hN
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := stack_le
  obtain ⟨hwf, hm⟩ := frame_env h hf
  obtain ⟨htag, hval⟩ := hw
  have hval' := NativeRustcVm.ewAt_iff.mp hval
  -- b5
  refine exec_at (inf hp b5_in_code (by simp [b5])) run_b5 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [Ring.load_word htag] at hpc1
  simp only [show ((1 : UInt64).toBitVec == 0#64) = false from rfl, Bool.false_eq_true,
    ↓reduceIte] at hpc1
  have hf1 : Fr0 m0 st1.data :=
    Fr.ofBlock hf hm hm1 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have hk1 : ∀ r : XReg, r ≠ .X8 → st1.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r h8 ↦ reg_of hm1 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  -- b6
  obtain ⟨hwf1, hm1'⟩ := frame_env h hf1
  refine exec_at (inf hp b6_in_code (by simp [b6])) run_b6 hwf1 hpc1 hm1' fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hfw : frameWrites (after b6 frameS) 144 slots0 [] = true := by decide
  have hS2 := after_eq run_b6
  rw [hS2] at hfw
  have hf2a : Fr0 m0 st2.data :=
    Fr.ofBlockW hf1 hm1' hm2 hwf1 rfl rfl (fun _ h ↦ absurd h (by simp)) rfl hs6 hN slots0_le
      (writeOk_of hm2 hfw (fun _ h ↦ by cases h))
  have hslot := Match.wordAt_write hm2 (r := 0) (o := 8) rfl (by decide) (v := .reg .X27)
    (fun i hi ↦ by revert i; decide)
  have h27 : st1.data.regs.X27 = m0.regs.X0 :=
    ((hk1 .X27 (by decide)).trans (hcs .X27 rfl)).trans ha.x27
  have hf2 : Fr1 m0 st2.data := Fr.addSlot hf2a (o := 8) (r := .X0) (by
    have e : UInt64.ofBitVec ((Sym.reg .X27).eval (Env.ofMachine st1.data [(base m0 144, 144)])) =
        m0.regs.getXReg .X0 := by
      show UInt64.ofBitVec st1.data.regs.X27.toBitVec = _
      rw [h27]; rfl
    rw [← e]; exact hslot)
  have hk2 : ∀ r : XReg, r ≠ .X0 → r ≠ .X1 → r ≠ .X2 → r ≠ .X3 → r ≠ .X29 → r ≠ .X30 →
      st2.data.regs.getXReg r = st1.data.regs.getXReg r := fun r h0 h1 h2 h3 h29 h30 ↦
    reg_of hm2 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have hv1 : NativeRustcVm.WordAt st1.data.dmem (base m0 144 + BitVec.ofNat 64 32)
      (ringW v (xpt m0)).c0 := by
    rw [hd1]; simpa [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] using hval'.1
  have hv2 : NativeRustcVm.WordAt st1.data.dmem (base m0 144 + BitVec.ofNat 64 40)
      (ringW v (xpt m0)).c1 := by
    rw [hd1]; simpa [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add] using hval'.2
  have l32 := Ring.load_word (env := Env.ofMachine st1.data [(base m0 144, 144)]) (r := 0)
    (off := 32) hv1
  have l40 := Ring.load_word (env := Env.ofMachine st1.data [(base m0 144, 144)]) (r := 0)
    (off := 40) hv2
  have g0 : st2.data.regs.X0 = (sAt b.scales 0).c0 :=
    (reg_of hm2 (r := .X0) rfl rfl).trans
      (((hk1 .X25 (by decide)).trans (hcs .X25 rfl)).trans ha.x25)
  have g1 : st2.data.regs.X1 = (sAt b.scales 0).c1 :=
    (reg_of hm2 (r := .X1) rfl rfl).trans
      (((hk1 .X24 (by decide)).trans (hcs .X24 rfl)).trans ha.x24)
  have g2 : st2.data.regs.X2 = (ringW v (xpt m0)).c0 := reg_of hm2 (r := .X2) rfl l32
  have g3 : st2.data.regs.X3 = (ringW v (xpt m0)).c1 := reg_of hm2 (r := .X3) rfl l40
  have g29 : st2.data.regs.X29.toBitVec = ba.scales + BitVec.ofNat 64 (16 * ba.count) := by
    refine (reg_val hm2 (r := .X29) rfl).trans ?_
    simp only [Sym.eval, Env.ofMachine_regs]
    have e19 : st1.data.regs.X19 = UInt64.ofBitVec ba.scales :=
      (hk1 .X19 (by decide)).trans ((hcs .X19 rfl).trans ha.x19)
    have e20 : st1.data.regs.X20 = ba.count.toUInt64 :=
      (hk1 .X20 (by decide)).trans ((hcs .X20 rfl).trans ha.x20)
    rw [show st1.data.regs.getXReg .X19 = st1.data.regs.X19 from rfl,
      show st1.data.regs.getXReg .X20 = st1.data.regs.X20 from rfl, e19, e20]
    simp only [BinOp.apply, UnOp.apply, shiftW, Sym.ext_W64, Sym.low_W64, Nat.toUInt64]
    rw [show (UInt64.ofNat ba.count).toBitVec = BitVec.ofNat 64 ba.count from rfl, shl4]
  have hc2 : ∀ r, calleeSaved r = true → r ≠ .X29 →
      st2.data.regs.getXReg r = st0.data.regs.getXReg r := fun r hr h29 ↦
    ((hk2 r (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)
      (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr) h29
      (by rintro rfl; simp [calleeSaved] at hr)).trans
      (hk1 r (by rintro rfl; simp [calleeSaved] at hr))).trans (hcs r hr)
  refine mul_call h slots_le hmul hf2 hpc2 fun m3 hf3 hy0 hy1 hcs3 ↦ ?_
  rw [g0, g1, g2, g3] at hy0 hy1
  have hc3 : ∀ r, calleeSaved r = true → r ≠ .X29 → m3.regs.getXReg r = st0.data.regs.getXReg r :=
    fun r hr h29 ↦ (hcs3 r hr).trans (hc2 r hr h29)
  have h29 : m3.regs.X29.toBitVec = ba.scales + BitVec.ofNat 64 (16 * ba.count) := by
    rw [show m3.regs.X29 = m3.regs.getXReg .X29 from rfl, hcs3 .X29 rfl]; exact g29
  have h22 : m3.regs.X22 = m0.regs.X1 := (hc3 .X22 rfl (by decide)).trans ha.x22
  -- b7
  have hcl := h.claimsAt hf3
  have hcin := h.claimsIn
  have hc8 : WhirIn m0 ba.claims 8 basisWEvalStack :=
    WhirIn.mono hcin (by unfold claimsBytes; omega)
  have hbc : Apart m0.regs.X1.toBitVec 56 ba.claims 8 :=
    NativeRustcVm.Apart.mono h.aparts.2.1 (Nat.le_refl _) (by unfold basisBytes; omega)
      (Nat.le_refl _) (by unfold claimsBytes; omega)
  let env3 := Env.ofMachine m3 [(m0.regs.X1.toBitVec, 56), (ba.claims, 8)]
  have hwf3 : env3.WF :=
    Env.wf_of ⟨mapped_of hf3 h.basis, mapped_of hf3 hc8, trivial⟩ (List.pairwise_pair.mpr hbc)
  have wc : NativeRustcVm.WordAt m3.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 40)
      (UInt64.ofBitVec ba.claims) := h.word hf3 5 (by decide)
  have l40 : env3.load 0 40 8 = ba.claims := Ring.load_word (env := env3) (r := 0) (off := 40) wc
  have hm3 : Match env3 claimsS m3 := by
    refine match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl,
        fun h ↦ absurd h (by decide), trivial⟩ rfl ⟨?_, trivial⟩ trivial trivial ⟨?_, trivial⟩
    · show m3.regs.X22.toBitVec = _
      rw [h22]; simp [Sym.eval]
    · simp only [Sym.eval]
      rw [l40]
      simp
  have hpc3 : (⟨m3, Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b6Offset + b6.length)⟩ : MachineState).pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b7Offset) :=
    rfl
  refine exec_at (inf hp b7_in_code (by simp [b7])) run_b7 hwf3 hpc3 hm3 fun st4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  have hf4 : Fr1 m0 st4.data :=
    Fr.ofBlock hf3 hm3 hm4 hwf3 rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have l0 : env3.load 1 0 8 = v.cs.size.toUInt64.toBitVec :=
    Ring.load_word (env := env3) (r := 1) (off := 0) (by
      show NativeRustcVm.WordAt m3.dmem (ba.claims + BitVec.ofNat 64 0) _
      rw [NativeRustcVm.addr_add_zero]; exact hcl.len)
  have hle := hcl.len_le
  have hcs4 : ∀ r : XReg, r ∉ [XReg.X8, .X9, .X10, .X19, .X22, .X24, .X25] →
      st4.data.regs.getXReg r = m3.regs.getXReg r := fun r hr ↦
    reg_of hm4 (v := .reg r) (by cases r <;> simp at hr <;> rfl) rfl
  have hlt : (v.cs.size.toUInt64.toBitVec).ult (BitVec.ofNat 64 161) = true :=
    count_ult (N := 160) hle (by decide)
  have hsz : v.cs.size.toUInt64.toNat = v.cs.size :=
    natCast_toUInt64_toNat (by unfold claimCap at hle; omega)
  have keep4 : Keep m0 ba st4.data := {
    fr := hf4
    x21 := (hcs4 .X21 (by simp)).trans ((hc3 .X21 rfl (by decide)).trans ha.x21)
    x22 := reg_eq <| by
      refine (hm4.regs .X22 _ rfl).trans ?_
      simp [Sym.eval]; rfl
    x23 := (hcs4 .X23 (by simp)).trans ((hc3 .X23 rfl (by decide)).trans ha.x23) }
  have hW0 : dot b.scales (ws v (xpt m0) 0) = EW.mul (sAt b.scales 0) (ringW v (xpt m0)) := by
    rw [ws_zero, dot_single]
  have acc4 : Acc ba b (ws v (xpt m0) 0) st4.data := {
    x24 := by rw [hW0]; exact (reg_of hm4 (r := .X24) rfl rfl).trans hy0
    x25 := by rw [hW0]; exact (reg_of hm4 (r := .X25) rfl rfl).trans hy1
    x28 := by
      rw [show st4.data.regs.X28 = st4.data.regs.getXReg .X28 from rfl,
        hcs4 .X28 (by simp), hc3 .X28 rfl (by decide)]
      exact ha.x28
    x29 := by
      rw [show st4.data.regs.X29 = st4.data.regs.getXReg .X29 from rfl, hcs4 .X29 (by simp)]
      exact h29 }
  have hcond : SBool.eval env3 (SBool.cmp CmpOp.eq RegWidth.W64
      (Sym.ite (SBool.cmp CmpOp.ult RegWidth.W64 (Sym.load 1 0 8) (Sym.lit 161))
        (Sym.bin BinOp.mul RegWidth.W64 (Sym.load 1 0 8) (Sym.lit 608)) (Sym.lit 0))
      (Sym.lit 0)) = decide (v.cs.size = 0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, l0, hlt, ↓reduceIte, BinOp.apply,
      Sym.ext_W64, Sym.low_W64, bv_beq_toNat]
    rw [mul608 hle]
    simp
  rw [hcond] at hpc4
  have h19 : (st4.data.regs.getXReg .X19).toNat = 608 * v.cs.size := by
    rw [← UInt64.toNat_toBitVec, reg_val hm4 (r := .X19) rfl]
    simp only [SBool.eval, Sym.eval, CmpOp.apply, l0, hlt, ↓reduceIte, BinOp.apply,
      Sym.ext_W64, Sym.low_W64]
    exact mul608 hle
  have h8 : st4.data.regs.X8.toBitVec = ba.claims + BitVec.ofNat 64 8 := by
    refine (reg_val hm4 (r := .X8) rfl).trans ?_
    simp only [Sym.eval, SBool.eval, CmpOp.apply, l0, Sym.low_W64, hlt, ↓reduceIte, l40,
      BinOp.apply, Sym.ext_W64]
  by_cases hc0 : v.cs.size = 0
  · simp only [hc0, decide_true, ↓reduceIte] at hpc4
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b19Offset) NativeRustcVmArm.Vm.BasisWEval.label_14_at] at hpc4
    exact hend st4 hpc4 ⟨keep4, by
      rw [show ws v (xpt m0) v.cs.size = ws v (xpt m0) 0 by rw [hc0]]; exact acc4⟩
  · simp only [decide_eq_false hc0, Bool.false_eq_true, ↓reduceIte] at hpc4
    rw [show k + NativeRustcVmArm.Vm.BasisWEval.b7Offset + b7.length = k + NativeRustcVmArm.Vm.BasisWEval.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b7_next]] at hpc4
    refine keep4.fr.regsBlock (inf hp b8_in_code (by simp [b8])) run_b8 hpc4 rfl rfl (by rfl)
      fun st5 hf5 hd5 hm5 hpc5 ↦ ?_
    simp only [PcOk] at hpc5
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b10Offset) NativeRustcVmArm.Vm.BasisWEval.label_7_at] at hpc5
    have hk5 : ∀ r : XReg, r ≠ .X20 → st5.data.regs.getXReg r = st4.data.regs.getXReg r :=
      fun r h20 ↦ reg_of hm5 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
    refine hloop st5 hpc5 {
      keep := ⟨hf5, (hk5 .X21 (by decide)).trans keep4.x21, (hk5 .X22 (by decide)).trans keep4.x22,
        (hk5 .X23 (by decide)).trans keep4.x23⟩
      acc := ⟨(hk5 .X24 (by decide)).trans acc4.x24, (hk5 .X25 (by decide)).trans acc4.x25,
        by rw [show st5.data.regs.X28 = st5.data.regs.getXReg .X28 from rfl, hk5 .X28 (by decide)]
           exact acc4.x28,
        by rw [show st5.data.regs.X29 = st5.data.regs.getXReg .X29 from rfl, hk5 .X29 (by decide)]
           exact acc4.x29⟩
      ilt := Nat.pos_of_ne_zero hc0
      x19 := by
        rw [show st5.data.regs.X19 = st5.data.regs.getXReg .X19 from rfl, hk5 .X19 (by decide), h19]
        simp
      x20 := by
        refine (reg_val hm5 (r := .X20) rfl).trans ?_
        simp only [Sym.eval, Env.ofMachine_regs, BinOp.apply, Sym.ext_W64, Sym.low_W64]
        rw [show st4.data.regs.getXReg .X8 = st4.data.regs.X8 from rfl, h8,
          NativeRustcVm.addr_add_add] }

end

end NativeRustcVmArm.Whir.BasisWEval
