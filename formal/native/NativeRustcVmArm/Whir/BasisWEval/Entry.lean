module

public import NativeRustcVmArm.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmArm.Whir.BasisWEval.Defs

/-!
# `BasisW::eval`: the entry

The prologue (`b0`) saves the registers and the point's length, loads the scales' slice (X19, X20)
and the layout's address (X23) from the `BasisW`, and calls `LayoutW::placement` on `QKECCAK`;
`b1` keeps the placement (X2, X6) and takes the first scale (`b2`, X25 and X24, X28 past it) or
`0` without scales (`b3`): `At4` at `.LBasisWEval_3` (`entry`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak)

@[expose] public section

/-- **At `.LBasisWEval_3`** (`b4`): the placement of `QKECCAK` (X2, X6), the scales' slice (X19,
X20), the point (X21), the `BasisW` (X22), the layout (X23), the output (X27), the first scale
(X25, X24) and the next one's address (X28). -/
structure At4 (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (st : MachineData) :
    Prop where
  fr : Fr0 m0 st
  x2 : st.regs.X2 = (v.L.placement qkeccak).variableCount.toUInt64
  x6 : st.regs.X6 = (v.L.placement qkeccak).index.toUInt64
  x19 : st.regs.X19 = UInt64.ofBitVec ba.scales
  x20 : st.regs.X20 = ba.count.toUInt64
  x21 : st.regs.X21 = m0.regs.X2
  x22 : st.regs.X22 = m0.regs.X1
  x23 : st.regs.X23 = UInt64.ofBitVec ba.layout
  x27 : st.regs.X27 = m0.regs.X0
  x28 : st.regs.X28.toBitVec = ba.scales + BitVec.ofNat 64 (16 * min 1 ba.count)
  x25 : st.regs.X25 = (sAt b.scales 0).c0
  x24 : st.regs.X24 = (sAt b.scales 0).c1

end

public section

theorem inf [Host] {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals}

/-- Word `i` of the `BasisW` in a state of the frame. -/
theorem In.word (h : In m0 ba b v) {F : Nat} {sl : List (Nat × XReg)} {st : MachineData}
    (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) (i : Nat) (hi : i < 7) :
    NativeRustcVm.WordAt st.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * i))
      ([UInt64.ofBitVec ba.scales, ba.count.toUInt64, UInt64.ofBitVec ba.layout,
        UInt64.ofBitVec ba.ring, UInt64.ofBitVec ba.keccak, UInt64.ofBitVec ba.claims,
        UInt64.ofBitVec ba.ood][i]'(by simpa using hi)) :=
  (h.wordsAt hf).getElem (by simpa using hi)

/-- The scales in a state of the frame. -/
theorem In.scalesAt (h : In m0 ba b v) {F : Nat} {sl : List (Nat × XReg)} {st : MachineData}
    (hf : Fr m0 F basisWEvalStack sl [] (fun _ ↦ False) st) :
    NativeRustcVm.EWsAt st.dmem ba.scales b.scales.toList :=
  NativeRustcVm.Tables.EWsAt.of_same h.pre.2.1.scales (same_of h.hN hf h.scales)
    (by rw [Array.length_toList, h.pre.2.1.scales_size])

theorem count_lt (h : In m0 ba b v) : ba.count < 2 ^ 64 := h.pre.2.1.count_lt

variable [Host] {k : Nat}

/-- **The entry**, to `.LBasisWEval_3`. -/
theorem entry (hp : Placed code k) (h : In m0 ba b v)
    (hpl : ∀ L, Spec (Labels.label NativeRustcVmArm.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    {R : MachineState → Prop}
    (cont : ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b4Offset) → At4 m0 ba b v st.data →
      Eventually (step1 Host.exe) R st) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b0Offset)⟩ := by
  have hS := h.stackOk
  have hN := h.hN
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := stack_le
  have hcl := count_lt h
  let p := m0.regs.X1.toBitVec
  let env := Env.ofMachine m0 [(base m0 144, 144), (p, 56)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨frame_mapped hS hs6, base_noWrap (by omega)⟩, ⟨h.basis.1.1, h.basis.1.2⟩, trivial⟩
      (List.pairwise_pair.mpr (frame_apart h h.basis).symm)
  have hm : Match env entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hS hs6 rfl, rfl,
        fun h ↦ absurd h (by decide), trivial⟩
      (by simp [Sym.eval, base]) ⟨by simp [Sym.eval, p]; rfl, trivial⟩ trivial trivial trivial
  have hw0 : ∀ i (hi : i < 7), NativeRustcVm.WordAt env.mem0 (env.base 1 + BitVec.ofNat 64 (8 * i))
      ([UInt64.ofBitVec ba.scales, ba.count.toUInt64, UInt64.ofBitVec ba.layout,
        UInt64.ofBitVec ba.ring, UInt64.ofBitVec ba.keccak, UInt64.ofBitVec ba.claims,
        UInt64.ofBitVec ba.ood][i]'(by simpa using hi)) :=
    fun i hi ↦ h.pre.2.1.words.getElem (by simpa using hi)
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hf1 : Fr0 m0 st1.data :=
    Fr.ofPrologue hN hs6 hm1 hwf rfl (by decide) (by decide) (by decide)
      (fun _ h ↦ absurd h (by simp))
  have hx0 : st1.data.regs.X0 = UInt64.ofBitVec ba.layout :=
    reg_of hm1 (r := .X0) rfl (Ring.load_word (hw0 2 (by decide)))
  have hx1 : st1.data.regs.X1 = 4 := reg_of hm1 (r := .X1) rfl rfl
  have hx19 : st1.data.regs.X19 = UInt64.ofBitVec ba.scales :=
    reg_of hm1 (r := .X19) rfl (by
      have := Ring.load_word (hw0 0 (by decide)); simpa [Sym.eval] using this)
  have hx20 : st1.data.regs.X20 = ba.count.toUInt64 :=
    reg_of hm1 (r := .X20) rfl (Ring.load_word (hw0 1 (by decide)))
  have hx21 : st1.data.regs.X21 = m0.regs.X2 := reg_of hm1 (r := .X21) rfl rfl
  have hx22 : st1.data.regs.X22 = m0.regs.X1 := reg_of hm1 (r := .X22) rfl (by simp [Sym.eval]; rfl)
  have hx23 : st1.data.regs.X23 = UInt64.ofBitVec ba.layout :=
    reg_of hm1 (r := .X23) rfl (Ring.load_word (hw0 2 (by decide)))
  have hx27 : st1.data.regs.X27 = m0.regs.X0 := reg_of hm1 (r := .X27) rfl rfl
  have hpre : LayoutWPlacementPre v.L st1.data := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hx1]; decide
    · rw [hx0, UInt64.toBitVec_ofBitVec]; exact h.layoutAt hf1
    · rw [hx0, UInt64.toBitVec_ofBitVec]; exact mapped_of hf1 h.layoutIn
  refine Fr.leaf hf1 hN hs5 (fun _ h ↦ absurd h (by simp)) (by decide) (fun _ h ↦ h.elim)
    (hpl v.L) (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ h.elim, hq.2.2.2⟩)
    hpc1 hpre
    fun m2 hf2 hq2 hcs2 ↦ ?_
  obtain ⟨hy0, hy1, -, -⟩ := hq2
  rw [hx1] at hy0 hy1
  rw [show k + NativeRustcVmArm.Vm.BasisWEval.b0Offset + b0.length = k + NativeRustcVmArm.Vm.BasisWEval.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b0_next]]
  refine hf2.regsBlock (inf hp b1_in_code (by simp [b1])) run_b1 rfl rfl rfl (by rfl)
    fun st3 hf3 hd3 hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  have hq4 : (4 : UInt64).toNat = qkeccak := rfl
  rw [hq4] at hy0 hy1
  have hk3 : ∀ r : XReg, r ≠ .X2 → r ≠ .X6 → st3.data.regs.getXReg r = m2.regs.getXReg r :=
    fun r h2 h6 ↦ reg_of hm3 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have hc3 : ∀ r : XReg, calleeSaved r = true →
      st3.data.regs.getXReg r = st1.data.regs.getXReg r := fun r hr ↦
    (hk3 r (by rintro rfl; simp [calleeSaved] at hr)
        (by rintro rfl; simp [calleeSaved] at hr)).trans
      (hcs2 r hr)
  have h2 : st3.data.regs.X2 = (v.L.placement qkeccak).variableCount.toUInt64 :=
    (reg_of hm3 (r := .X2) rfl rfl).trans hy0
  have h6 : st3.data.regs.X6 = (v.L.placement qkeccak).index.toUInt64 :=
    (reg_of hm3 (r := .X6) rfl rfl).trans hy1
  have h19 : st3.data.regs.X19 = UInt64.ofBitVec ba.scales := (hc3 .X19 rfl).trans hx19
  have h20 : st3.data.regs.X20 = ba.count.toUInt64 := (hc3 .X20 rfl).trans hx20
  have h21 : st3.data.regs.X21 = m0.regs.X2 := (hc3 .X21 rfl).trans hx21
  have h22 : st3.data.regs.X22 = m0.regs.X1 := (hc3 .X22 rfl).trans hx22
  have h23 : st3.data.regs.X23 = UInt64.ofBitVec ba.layout := (hc3 .X23 rfl).trans hx23
  have h27 : st3.data.regs.X27 = m0.regs.X0 := (hc3 .X27 rfl).trans hx27
  have hsz := h.pre.2.1.scales_size
  have hz : ((Env.ofMachine m2 []).regs XReg.X20 == 0#64) = decide (ba.count = 0) := by
    show ((m2.regs.getXReg .X20).toBitVec == 0#64) = _
    rw [hcs2 .X20 rfl]
    show (st1.data.regs.X20.toBitVec == 0#64) = _
    rw [hx20, toBitVec_beq_zero]
    by_cases hc0 : ba.count = 0
    · simp [hc0]
    · have := natCast_toUInt64_toNat hcl
      simp only [hc0, decide_false, decide_eq_false_iff_not]
      intro h0
      rw [h0] at this
      exact hc0 this.symm
  rw [hz] at hpc3
  by_cases hc0 : ba.count = 0
  · simp only [hc0, decide_true, ↓reduceIte] at hpc3
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b3Offset) NativeRustcVmArm.Vm.BasisWEval.label_2_at] at hpc3
    refine hf3.regsBlock (inf hp b3_in_code (by simp [b3])) run_b3 hpc3 rfl rfl (by rfl)
      fun st4 hf4 hd4 hm4 hpc4 ↦ ?_
    simp only [PcOk] at hpc4
    have hk4 : ∀ r : XReg, r ≠ .X24 → r ≠ .X25 → r ≠ .X28 →
        st4.data.regs.getXReg r = st3.data.regs.getXReg r :=
      fun r h24 h25 h28 ↦ reg_of hm4 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
    have hs0 : sAt b.scales 0 = 0 := by
      rw [sAt, Array.getElem?_eq_none (by omega)]; rfl
    refine cont st4 (hpc4.trans (by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b3_next])) {
      fr := hf4
      x2 := (hk4 .X2 (by decide) (by decide) (by decide)).trans h2
      x6 := (hk4 .X6 (by decide) (by decide) (by decide)).trans h6
      x19 := (hk4 .X19 (by decide) (by decide) (by decide)).trans h19
      x20 := (hk4 .X20 (by decide) (by decide) (by decide)).trans h20
      x21 := (hk4 .X21 (by decide) (by decide) (by decide)).trans h21
      x22 := (hk4 .X22 (by decide) (by decide) (by decide)).trans h22
      x23 := (hk4 .X23 (by decide) (by decide) (by decide)).trans h23
      x27 := (hk4 .X27 (by decide) (by decide) (by decide)).trans h27
      x28 := by
        show (st4.data.regs.getXReg .X28).toBitVec = _
        rw [reg_val hm4 (r := .X28) rfl, hc0]
        show (st3.data.regs.X19).toBitVec = _
        rw [h19]; simp
      x25 := by rw [hs0]; exact reg_of hm4 (r := .X25) rfl rfl
      x24 := by rw [hs0]; exact reg_of hm4 (r := .X24) rfl rfl }
  · simp only [decide_eq_false hc0, Bool.false_eq_true, ↓reduceIte] at hpc3
    rw [show k + NativeRustcVmArm.Vm.BasisWEval.b1Offset + b1.length = k + NativeRustcVmArm.Vm.BasisWEval.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b1_next]] at hpc3
    have hsc := h.scalesAt hf3
    have hm16 := mapped_of hf3 h.scales
    let env2 := Env.ofMachine st3.data [(ba.scales, 16)]
    have hwf2 : env2.WF :=
      Env.wf_of ⟨⟨NativeRustcVm.Mapped.mono hm16.1 (by omega),
        NativeRustcVm.NoWrap.mono hm16.2 (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _)
    have hm2' : Match env2 (scaleS .X19) st3.data :=
      match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
        ⟨by show st3.data.regs.X19.toBitVec = _; rw [h19]; simp [Sym.eval], trivial⟩
        trivial trivial trivial
    refine exec_at (inf hp b2_in_code (by simp [b2])) run_b2 hwf2 hpc3 hm2'
      fun st4 hm4 hpc4 ↦ ?_
    simp only [PcOk] at hpc4
    have hf4 : Fr0 m0 st4.data :=
      Fr.ofBlock hf3 hm2' hm4 hwf2 rfl rfl rfl (fun _ h ↦ absurd h (by simp))
    have hk4 : ∀ r : XReg, r ≠ .X24 → r ≠ .X25 → r ≠ .X28 → r ≠ .X19 →
        st4.data.regs.getXReg r = st3.data.regs.getXReg r :=
      fun r h24 h25 h28 h19 ↦
        reg_of hm4 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
    have hpos : 0 < b.scales.toList.length := by simp; omega
    have he := NativeRustcVm.ewAt_iff.mp (hsc.getElem hpos)
    have e1 : NativeRustcVm.WordAt st3.data.dmem (ba.scales + BitVec.ofNat 64 0)
        b.scales[0].c0 := by simpa using he.1
    have e2 : NativeRustcVm.WordAt st3.data.dmem (ba.scales + BitVec.ofNat 64 8)
        b.scales[0].c1 := by simpa using he.2
    have hs0 : sAt b.scales 0 = b.scales[0] := by
      rw [sAt, Array.getElem?_eq_getElem (by omega), Option.getD_some]
    refine cont st4 (by rw [hpc4, hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b4Offset) NativeRustcVmArm.Vm.BasisWEval.label_3_at]) {
      fr := hf4
      x2 := (hk4 .X2 (by decide) (by decide) (by decide) (by decide)).trans h2
      x6 := (hk4 .X6 (by decide) (by decide) (by decide) (by decide)).trans h6
      x19 := by
        rw [← h19]
        refine reg_of hm4 (r := .X19) rfl ?_
        simp [Sym.eval]; rw [h19]; rfl
      x20 := (hk4 .X20 (by decide) (by decide) (by decide) (by decide)).trans h20
      x21 := (hk4 .X21 (by decide) (by decide) (by decide) (by decide)).trans h21
      x22 := (hk4 .X22 (by decide) (by decide) (by decide) (by decide)).trans h22
      x23 := (hk4 .X23 (by decide) (by decide) (by decide) (by decide)).trans h23
      x27 := (hk4 .X27 (by decide) (by decide) (by decide) (by decide)).trans h27
      x28 := by
        show (st4.data.regs.getXReg .X28).toBitVec = _
        rw [reg_val hm4 (r := .X28) rfl, show min 1 ba.count = 1 by omega]
        rfl
      x25 := by
        rw [hs0]
        exact reg_of hm4 (r := .X25) rfl (Ring.load_word e1)
      x24 := by
        rw [hs0]
        exact reg_of hm4 (r := .X24) rfl (Ring.load_word e2) }

end

end NativeRustcVmArm.Whir.BasisWEval
