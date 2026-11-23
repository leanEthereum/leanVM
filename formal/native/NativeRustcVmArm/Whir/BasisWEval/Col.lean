module

public import NativeRustcVmArm.Whir.BasisWEval.First

/-!
# `BasisW::eval`: a column claim, up to its weight's call

From `Loop i` (`b10`): a column of `158` or more has no placement, `b10` jumps to `b9`; else `b11`
reads the placement entry, `b9` for none; else `b12` compares the next scale's address with the
scales' end and takes the scale (`b13`) or `0` (`b14`): `AtB15` at `b15` (`col_head`).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model LeanVM.Parameters
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVm.Layout NativeRustcVm.Ring
open NativeRustcVm.KeccakGkr NativeRustcVmArm.Vm.BasisWEval
open LeanVM.Protocol.Verifier (qkeccak Placement)

@[expose] public section

/-- Column claim `i`'s address. -/
def cA (ba : BasisAddrs) (i : Nat) : BitVec 64 := ba.claims + BitVec.ofNat 64 (8 + 608 * i)

/-- The placement entry of column `c`. -/
def pA (ba : BasisAddrs) (c : Nat) : BitVec 64 := ba.layout + BitVec.ofNat 64 (120 + 24 * c)

/-- **At `b15`**: column claim `i` has the placement `pl`, the scale `j = |ws i|` in X26, X27. -/
structure AtB15 (m0 : MachineData) (ba : BasisAddrs) (b : BasisW) (v : Vals) (i : Nat)
    (pl : Placement) (st : MachineData) : Prop where
  keep : Keep m0 ba st
  ilt : i < v.cs.size
  pl : (v.L.placements[v.cs[i].column]?).getD none = some pl
  clt : v.cs[i].column < 158
  x24 : st.regs.X24 = (dot b.scales (ws v (xpt m0) i)).c0
  x25 : st.regs.X25 = (dot b.scales (ws v (xpt m0) i)).c1
  x26 : st.regs.X26 = (sAt b.scales (ws v (xpt m0) i).size).c0
  x27 : st.regs.X27 = (sAt b.scales (ws v (xpt m0) i).size).c1
  x28 : st.regs.X28.toBitVec =
    ba.scales + BitVec.ofNat 64 (16 * min ((ws v (xpt m0) i).size + 1) ba.count)
  x29 : st.regs.X29.toBitVec = ba.scales + BitVec.ofNat 64 (16 * ba.count)
  x8 : st.regs.X8.toBitVec = pA ba v.cs[i].column
  x19 : st.regs.X19.toNat = 608 * (v.cs.size - i)
  x20 : st.regs.X20.toBitVec = cA ba i + BitVec.ofNat 64 16

end

public section

variable {m0 : MachineData} {ba : BasisAddrs} {b : BasisW} {v : Vals} [Host] {k : Nat}

omit [Host] in
theorem In.claimIn (h : In m0 ba b v) {i : Nat} (hi : i < v.cs.size) :
    WhirIn m0 (cA ba i) 608 basisWEvalStack := by
  have hle := h.claims.len_le
  unfold claimCap at hle
  exact WhirIn.sub h.claimsIn (by unfold claimsBytes columnClaimBytes claimCap; omega)

omit [Host] in
theorem In.claimAt (h : In m0 ba b v) {sl : List (Nat × XReg)} {st : MachineData}
    (hf : Fr m0 144 basisWEvalStack sl [] (fun _ ↦ False) st) {i : Nat} (hi : i < v.cs.size) :
    ColumnClaimAt st.dmem (cA ba i) v.cs[i] := (h.claimsAt hf).claims i hi

omit [Host] in
theorem In.placeIn (h : In m0 ba b v) {c : Nat} (hc : c < 158) :
    WhirIn m0 (pA ba c) 24 basisWEvalStack :=
  WhirIn.sub h.layoutIn (by unfold layoutBytes placementBytes columnCountW; omega)

omit [Host] in
/-- `Loop` depends on the frame and nine registers only. -/
theorem Loop.mono {i : Nat} {st st' : MachineData} (hl : Loop m0 ba b v i st) (hf : Fr1 m0 st')
    (hr : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X28, .X29],
      st'.regs.getXReg r = st.regs.getXReg r) : Loop m0 ba b v i st' where
  keep := ⟨hf, (hr .X21 (by simp)).trans hl.keep.x21, (hr .X22 (by simp)).trans hl.keep.x22,
    (hr .X23 (by simp)).trans hl.keep.x23⟩
  acc := ⟨(hr .X24 (by simp)).trans hl.acc.x24, (hr .X25 (by simp)).trans hl.acc.x25,
    by rw [show st'.regs.X28 = st'.regs.getXReg .X28 from rfl, hr .X28 (by simp)]; exact hl.acc.x28,
    by rw [show st'.regs.X29 = st'.regs.getXReg .X29 from rfl, hr .X29 (by simp)]; exact hl.acc.x29⟩
  ilt := hl.ilt
  x19 := by rw [show st'.regs.X19 = st'.regs.getXReg .X19 from rfl, hr .X19 (by simp)]; exact hl.x19
  x20 := by rw [show st'.regs.X20 = st'.regs.getXReg .X20 from rfl, hr .X20 (by simp)]; exact hl.x20

omit [Host] in
theorem cA_16 (ba : BasisAddrs) (i : Nat) :
    ba.claims + BitVec.ofNat 64 (24 + 608 * i) = cA ba i + BitVec.ofNat 64 16 := by
  rw [cA, NativeRustcVm.addr_add_add, show 8 + 608 * i + 16 = 24 + 608 * i by omega]

omit [Host] in
/-- `AtB15` from `Loop`, the scale and its next address. -/
theorem AtB15.of {i : Nat} {st st' : MachineData} (hl : Loop m0 ba b v i st) (hf : Fr1 m0 st')
    (hr : ∀ r ∈ [XReg.X8, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X29],
      st'.regs.getXReg r = st.regs.getXReg r) (hi : i < v.cs.size) {pl : Placement}
    (hgd : (v.L.placements[v.cs[i].column]?).getD none = some pl) (hc : v.cs[i].column < 158)
    (hx8 : st.regs.X8.toBitVec = pA ba v.cs[i].column)
    (h26 : st'.regs.X26 = (sAt b.scales (ws v (xpt m0) i).size).c0)
    (h27 : st'.regs.X27 = (sAt b.scales (ws v (xpt m0) i).size).c1)
    (h28 : st'.regs.X28.toBitVec =
      ba.scales + BitVec.ofNat 64 (16 * min ((ws v (xpt m0) i).size + 1) ba.count)) :
    AtB15 m0 ba b v i pl st' where
  keep := ⟨hf, (hr .X21 (by simp)).trans hl.keep.x21, (hr .X22 (by simp)).trans hl.keep.x22,
    (hr .X23 (by simp)).trans hl.keep.x23⟩
  ilt := hi
  pl := hgd
  clt := hc
  x24 := (hr .X24 (by simp)).trans hl.acc.x24
  x25 := (hr .X25 (by simp)).trans hl.acc.x25
  x26 := h26
  x27 := h27
  x28 := h28
  x29 := by
    rw [show st'.regs.X29 = st'.regs.getXReg .X29 from rfl, hr .X29 (by simp)]; exact hl.acc.x29
  x8 := by rw [show st'.regs.X8 = st'.regs.getXReg .X8 from rfl, hr .X8 (by simp)]; exact hx8
  x19 := by rw [show st'.regs.X19 = st'.regs.getXReg .X19 from rfl, hr .X19 (by simp)]; exact hl.x19
  x20 := by
    rw [show st'.regs.X20 = st'.regs.getXReg .X20 from rfl, hr .X20 (by simp), ← cA_16]
    exact hl.x20

omit [Host] in
/-- `Loop i` to `AtB9 i` when column claim `i` has no placement. -/
theorem none_step {i : Nat} {st : MachineData} (hl : Loop m0 ba b v i st) (hi : i < v.cs.size)
    (hnone : (v.L.placements[v.cs[i].column]?).getD none = none) : AtB9 m0 ba b v i st := by
  have hw : ws v (xpt m0) (i + 1) = ws v (xpt m0) i := by
    rw [ws_succ _ _ hi, hnone]
  exact ⟨hl.keep, hw ▸ hl.acc, hl.ilt, hl.x19, hl.x20⟩

/-- From `b12`: the scale. -/
theorem col_scale (hp : Placed code k) (h : In m0 ba b v) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b12Offset)) (hl : Loop m0 ba b v i st.data) (hi : i < v.cs.size)
    (hc : v.cs[i].column < 158) {pl : Placement}
    (hgd : (v.L.placements[v.cs[i].column]?).getD none = some pl)
    (hx8 : st.data.regs.X8.toBitVec = pA ba v.cs[i].column)
    {R : MachineState → Prop}
    (hb15 : ∀ st' : MachineState, ∀ pl, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b15Offset) →
      AtB15 m0 ba b v i pl st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hf := hl.keep.fr
  refine hf.regsBlock (inf hp b12_in_code (by simp [b12])) run_b12 hpc rfl rfl (by rfl)
    fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  have hk1 : ∀ r : XReg, st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r ↦
    reg_of hm1 (v := .reg r) (by cases r <;> rfl) rfl
  rw [Env.ofMachine_regs, Env.ofMachine_regs,
    show st.data.regs.getXReg .X28 = st.data.regs.X28 from rfl,
    show st.data.regs.getXReg .X29 = st.data.regs.X29 from rfl, hl.acc.x28, hl.acc.x29,
    h.scale_beq] at hpc1
  have hsz := h.pre.2.1.scales_size
  by_cases hj : ba.count ≤ (ws v (xpt m0) i).size
  · simp only [hj, decide_true, ↓reduceIte] at hpc1
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b14Offset) NativeRustcVmArm.Vm.BasisWEval.label_11_at] at hpc1
    refine hf1.regsBlock (inf hp b14_in_code (by simp [b14])) run_b14 hpc1 rfl rfl (by rfl)
      fun st2 hf2 hd2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    have hk2 : ∀ r : XReg, r ≠ .X26 → r ≠ .X27 → r ≠ .X28 →
        st2.data.regs.getXReg r = st.data.regs.getXReg r := fun r h26 h27 h28 ↦
      (reg_of hm2 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl).trans (hk1 r)
    have hs0 : sAt b.scales (ws v (xpt m0) i).size = 0 := sAt_ge (by omega)
    refine hb15 st2 pl (hpc2.trans rfl) (AtB15.of hl hf2
      (fun r hr ↦ hk2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> decide)) hi hgd hc hx8 ?_ ?_ ?_)
    · rw [hs0]; exact reg_of hm2 (r := .X26) rfl rfl
    · rw [hs0]; exact reg_of hm2 (r := .X27) rfl rfl
    · rw [show st2.data.regs.X28 = st2.data.regs.getXReg .X28 from rfl,
        reg_val hm2 (r := .X28) rfl, show min ((ws v (xpt m0) i).size + 1) ba.count = ba.count
        by omega]
      show st1.data.regs.X29.toBitVec = _
      rw [show st1.data.regs.X29 = st1.data.regs.getXReg .X29 from rfl, hk1 .X29]
      exact hl.acc.x29
  · simp only [hj, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmArm.Vm.BasisWEval.b12Offset + b12.length = k + NativeRustcVmArm.Vm.BasisWEval.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b12_next]] at hpc1
    have hj' : (ws v (xpt m0) i).size < ba.count := by omega
    have hsin := h.scaleIn hj'
    let env := Env.ofMachine st1.data
      [(ba.scales + BitVec.ofNat 64 (16 * (ws v (xpt m0) i).size), 16)]
    have hwf : env.WF := Env.wf_of ⟨mapped_of hf1 hsin, trivial⟩ (List.pairwise_singleton _ _)
    have hm : Match env (scaleS .X28) st1.data :=
      match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
        ⟨by
          show st1.data.regs.X28.toBitVec = _
          rw [show st1.data.regs.X28 = st1.data.regs.getXReg .X28 from rfl, hk1 .X28]
          rw [show st.data.regs.getXReg .X28 = st.data.regs.X28 from rfl, hl.acc.x28,
            Nat.min_eq_left (by omega)]
          simp [Sym.eval], trivial⟩
        trivial trivial trivial
    refine exec_at (inf hp b13_in_code (by simp [b13])) run_b13 hwf hpc1 hm fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b15Offset) NativeRustcVmArm.Vm.BasisWEval.label_12_at] at hpc2
    have hf2 : Fr1 m0 st2.data :=
      Fr.ofBlock hf1 hm hm2 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
    have hk2 : ∀ r : XReg, r ≠ .X26 → r ≠ .X27 → r ≠ .X28 →
        st2.data.regs.getXReg r = st.data.regs.getXReg r := fun r h26 h27 h28 ↦
      (reg_of hm2 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl).trans (hk1 r)
    obtain ⟨w0, w8⟩ := h.scaleAt hf1 hj'
    refine hb15 st2 pl hpc2 (AtB15.of hl hf2
      (fun r hr ↦ hk2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> decide)) hi hgd hc hx8 ?_ ?_ ?_)
    · exact reg_of hm2 (r := .X26) rfl (Ring.load_word w0)
    · exact reg_of hm2 (r := .X27) rfl (Ring.load_word w8)
    · rw [show st2.data.regs.X28 = st2.data.regs.getXReg .X28 from rfl,
        reg_val hm2 (r := .X28) rfl, Nat.min_eq_left (by omega)]
      show _ + BitVec.ofInt 64 16 = _
      rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl]
      show ba.scales + BitVec.ofNat 64 (16 * (ws v (xpt m0) i).size) + _ = _
      rw [NativeRustcVm.addr_add_add, Nat.mul_succ]

/-- From `b11`: the placement entry, then the scale. -/
theorem col_place (hp : Placed code k) (h : In m0 ba b v) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b11Offset)) (hl : Loop m0 ba b v i st.data) (hi : i < v.cs.size)
    (hc : v.cs[i].column < 158)
    (hx8 : (st.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 v.cs[i].column)
    {R : MachineState → Prop}
    (hb9 : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b9Offset) → AtB9 m0 ba b v i st'.data →
      Eventually (step1 Host.exe) R st')
    (hb15 : ∀ st' : MachineState, ∀ pl, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b15Offset) →
      AtB15 m0 ba b v i pl st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hf := hl.keep.fr
  have hpin := h.placeIn hc
  have hidx : v.cs[i].column < v.L.placements.size := by
    rw [h.layout.placements_size]; unfold columnCountW; omega
  have hpw : PlacementWAt st.data.dmem (pA ba v.cs[i].column) v.L.placements[v.cs[i].column] :=
    (h.layoutAt hf).placements _ hidx
  let env := Env.ofMachine st.data [(pA ba v.cs[i].column, 24)]
  have hwf : env.WF := Env.wf_of ⟨mapped_of hf hpin, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env placeS st.data := by
    refine match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl trivial trivial trivial
      ⟨?_, trivial⟩
    simp only [placeSym, Sym.eval, BinOp.apply, Sym.ext_W64, Sym.low_W64, Env.ofMachine_regs]
    rw [hx8, show (st.data.regs.getXReg .X23) = st.data.regs.X23 from rfl, hl.keep.x23]
    show _ = pA ba v.cs[i].column + BitVec.ofInt 64 0
    have hc' := hc
    generalize v.cs[i].column = c at hc' ⊢
    rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, pA, UInt64.toBitVec_ofBitVec,
      show BitVec.ofNat 64 c * 24#64 = BitVec.ofNat 64 (24 * c) by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
        omega,
      BitVec.add_comm (BitVec.ofNat 64 (24 * c)), BitVec.add_assoc, ← BitVec.ofNat_add]
  refine exec_at (inf hp b11_in_code (by simp [b11])) run_b11 hwf hpc hm fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  have hf2 : Fr1 m0 st2.data :=
    Fr.ofBlock hf hm hm2 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have hk2 : ∀ r : XReg, r ≠ .X8 → r ≠ .X9 → r ≠ .X10 →
      st2.data.regs.getXReg r = st.data.regs.getXReg r := fun r h8 h9 h10 ↦
    reg_of hm2 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have hl2 : Loop m0 ba b v i st2.data :=
    hl.mono hf2 fun r hr ↦ hk2 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  sym_simp at hpc2
  have hpw' : PlacementWAt st.data.dmem (env.base 0 + BitVec.ofNat 64 0)
      v.L.placements[v.cs[i].column] := by
    rw [NativeRustcVm.addr_add_zero]; exact hpw
  cases hpl : v.L.placements[v.cs[i].column] with
  | none =>
    rw [hpl] at hpw'
    rw [Ring.load_word (env := env) hpw', show ((0 : UInt64).toBitVec == 0#64) = true from rfl]
      at hpc2
    simp only [↓reduceIte] at hpc2
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b9Offset) NativeRustcVmArm.Vm.BasisWEval.label_6_at] at hpc2
    refine hb9 st2 hpc2 (none_step hl2 hi ?_)
    rw [Array.getElem?_eq_getElem hidx, hpl]; rfl
  | some pl =>
    rw [hpl] at hpw'
    obtain ⟨htag, hvc, hix, hwv, hwi⟩ := hpw'
    rw [Ring.load_word (env := env) htag, show ((1 : UInt64).toBitVec == 0#64) = false from rfl]
      at hpc2
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
    rw [show k + NativeRustcVmArm.Vm.BasisWEval.b11Offset + b11.length = k + NativeRustcVmArm.Vm.BasisWEval.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b11_next]] at hpc2
    have hx8' : st2.data.regs.X8.toBitVec = pA ba v.cs[i].column := by
      refine (reg_val hm2 (r := .X8) rfl).trans ?_
      show placeSym.eval env = _
      rw [hm.aliases placeSym 0 0 rfl, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
      rfl
    have hgd : (v.L.placements[v.cs[i].column]?).getD none = some pl := by
      rw [Array.getElem?_eq_getElem hidx, hpl]; rfl
    exact col_scale hp h hpc2 hl2 hi hc hgd hx8' hb15

/-- **Column claim `i`**, from `b10` to `b9` (no placement) or `b15`. -/
theorem col_head (hp : Placed code k) (h : In m0 ba b v) {i : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b10Offset)) (hl : Loop m0 ba b v i st.data)
    {R : MachineState → Prop}
    (hb9 : ∀ st' : MachineState, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b9Offset) → AtB9 m0 ba b v i st'.data →
      Eventually (step1 Host.exe) R st')
    (hb15 : ∀ st' : MachineState, ∀ pl, st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BasisWEval.b15Offset) →
      AtB15 m0 ba b v i pl st'.data → Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hf := hl.keep.fr
  have hi := hl.ilt
  have hcin := h.claimIn hi
  have hca := h.claimAt hf hi
  -- b10
  let env := Env.ofMachine st.data [(cA ba i, 608)]
  have hwf : env.WF :=
    Env.wf_of ⟨mapped_of hf hcin, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match env colS st.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
      ⟨by show st.data.regs.X20.toBitVec = _; rw [hl.x20, cA_16]; rfl, trivial⟩
      trivial trivial trivial
  refine exec_at (inf hp b10_in_code (by simp [b10])) run_b10 hwf hpc hm fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hf1 : Fr1 m0 st1.data :=
    Fr.ofBlock hf hm hm1 hwf rfl rfl rfl (fun _ h ↦ absurd h (by simp))
  have l0 : env.load 0 0 8 = v.cs[i].column.toUInt64.toBitVec :=
    Ring.load_word (env := env) (r := 0) (off := 0) (by
      show NativeRustcVm.WordAt st.data.dmem (cA ba i + BitVec.ofNat 64 0) _
      rw [NativeRustcVm.addr_add_zero]; exact hca.column)
  have hc64 := hca.column_lt
  have hk1 : ∀ r : XReg, r ≠ .X8 → r ≠ .X20 → st1.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r h8 h20 ↦ reg_of hm1 (v := .reg r) (by cases r <;> first | rfl | contradiction) rfl
  have hx20 : st1.data.regs.X20 = st.data.regs.X20 := reg_eq <| by
    refine (hm1.regs .X20 _ rfl).trans ?_
    rw [hl.x20, cA_16]; rfl
  sym_simp at hpc1
  rw [l0, toBitVec_ult_ofNat (by decide), natCast_toUInt64_toNat hc64] at hpc1
  have hl1 : Loop m0 ba b v i st1.data := {
    keep := ⟨hf1, (hk1 .X21 (by decide) (by decide)).trans hl.keep.x21,
      (hk1 .X22 (by decide) (by decide)).trans hl.keep.x22,
      (hk1 .X23 (by decide) (by decide)).trans hl.keep.x23⟩
    acc := ⟨(hk1 .X24 (by decide) (by decide)).trans hl.acc.x24,
      (hk1 .X25 (by decide) (by decide)).trans hl.acc.x25,
      by rw [show st1.data.regs.X28 = st1.data.regs.getXReg .X28 from rfl,
           hk1 .X28 (by decide) (by decide)]; exact hl.acc.x28,
      by rw [show st1.data.regs.X29 = st1.data.regs.getXReg .X29 from rfl,
           hk1 .X29 (by decide) (by decide)]; exact hl.acc.x29⟩
    ilt := hi
    x19 := by
      rw [show st1.data.regs.X19 = st1.data.regs.getXReg .X19 from rfl,
        hk1 .X19 (by decide) (by decide)]; exact hl.x19
    x20 := by rw [hx20]; exact hl.x20 }
  have hx8 : (st1.data.regs.getXReg .X8).toBitVec = BitVec.ofNat 64 v.cs[i].column := by
    rw [reg_val hm1 (r := .X8) rfl]
    simp only [Sym.eval]
    rw [l0]; rfl
  by_cases hc : v.cs[i].column < 158
  · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmArm.Vm.BasisWEval.b10Offset + b10.length = k + NativeRustcVmArm.Vm.BasisWEval.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BasisWEval.b10_next]] at hpc1
    exact col_place hp h hpc1 hl1 hi hc hx8 hb9 hb15
  · simp only [hc, decide_false, Bool.not_false, ↓reduceIte] at hpc1
    rw [hp.label (j := NativeRustcVmArm.Vm.BasisWEval.b9Offset) NativeRustcVmArm.Vm.BasisWEval.label_6_at] at hpc1
    have hnone : (v.L.placements[v.cs[i].column]?).getD none = none := by
      rw [Array.getElem?_eq_none (by rw [h.layout.placements_size]; unfold columnCountW; omega)]
      rfl
    exact hb9 st1 hpc1 (none_step hl1 hi hnone)

end

end NativeRustcVmArm.Whir.BasisWEval
