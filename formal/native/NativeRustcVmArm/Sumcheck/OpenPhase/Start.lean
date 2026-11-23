module

public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Sumcheck.OpenPhase.Entry

/-!
# `open_phase`: the climbs' start

At `.L8` (`Checked`): `b10` stores the openings' address in the frame and, without openings,
leaves for `.L17` (`exit_rows`); else `b11` (the width bound) and `b12` (the root's words, `8 w`,
the counters) reach the climbs' loop head `.L11` (`CInv`, `start_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

@[expose] public section

/-- **The climbs' invariant** at `.L11`, `j < |P|` climbs checked. -/
structure CInv [Labels] (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (R : Digest)
    (h w j : Nat) (m : MachineData) : Prop where
  fr : FrO m0 m
  lt : j < P.size
  x19 : m.regs.getXReg .X19 = m0.regs.X0
  x20 : (m.regs.getXReg .X20).toBitVec = phO m0 + BitVec.ofNat 64 (1544 * j)
  x21 : m.regs.getXReg .X21 = w.toUInt64
  x22 : m.regs.getXReg .X22 = h.toUInt64
  x23 : m.regs.getXReg .X23 = P.size.toUInt64
  x24 : (m.regs.getXReg .X24).toNat = P.size - j
  x25 : (m.regs.getXReg .X25).toNat = 395264 - 1544 * j
  x26 : m.regs.getXReg .X26 = R.toList[0]'(by simp)
  x27 : m.regs.getXReg .X27 = R.toList[1]'(by simp)
  x28 : m.regs.getXReg .X28 = R.toList[2]'(by simp)
  x29 : m.regs.getXReg .X29 = R.toList[3]'(by simp)
  w0 : NativeRustcVm.WordAt m.dmem (base m0 176 + BitVec.ofNat 64 0)
    (UInt64.ofBitVec (off (phO m0) 24))
  w8 : NativeRustcVm.WordAt m.dmem (base m0 176 + BitVec.ofNat 64 8) (8 * w).toUInt64
  shape : ShapeOk P Q h w m0.regs.X2.toNat m0.regs.X3.toNat
  pos : PositionsOk P Q P.size
  climbs : ClimbsOk R P j

end

public section

/-- The model, the checks passed: the climbs decide. -/
theorem openPhase_climbs {R : Digest} {height width : Nat} {Q : Array UInt64} {P : Array OpeningW}
    {d : Mem 64} {b : BitVec 64} {h w : Nat} (hph : PhaseHW d b P h w)
    (hsh : ShapeOk P Q h w height width) (hpos : PositionsOk P Q P.size) :
    openPhase R height width Q P =
      if ClimbsOk R P P.size then some (P.map (·.leaf)) else none := by
  rw [openPhase_eq hph.shape, ite_eq_left ⟨hsh.1, hsh.2, hpos⟩]

/-- The leaf words of opening `j`, read in place from the openings' address. -/
theorem leaf_words {d : Mem 64} {b : BitVec 64} {P : Array OpeningW} {h w : Nat}
    (hph : PhaseHW d b P h w) :
    ∀ j (hj : j < P.size), P[j].leaf.size = w ∧
      NativeRustcVm.WordsAt d (off (off b 24) (8 * (1 + j * openingWords))) P[j].leaf.toList := by
  intro j hj
  have ho := hph.2.2.2.2.2.2 j hj
  refine ⟨ho.1, ?_⟩
  have := ho.2.2.2.2.1
  rw [off_off] at this ⊢
  rwa [show 24 + 8 * (1 + j * openingWords) = 8 * (3 + j * openingWords) + 8 by ring]

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}

/-- `frTest`, the memory kept too. -/
theorem frTestD (hpre : OpenPhasePre P R Q m0) {m : MachineData} (hf : FrO m0 m)
    {ds : List Directive} {S' : SState} {x : Exit} {j : Nat} (hk : ds.IsInfixAt Host.prog j)
    (hx : exec ds frS = some (S', x)) (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (hregs : ∀ r, S'.reg r = some (.reg r)) {Rs : MachineState → Prop}
    (cont : ∀ st : MachineState, FrO m0 st.data →
      (∀ r, st.data.regs.getXReg r = m.regs.getXReg r) → st.data.dmem = m.dmem →
      PcOk (Env.ofMachine m [(base m0 176, 176)]) x (Host.addrOf (j + ds.length)) st →
      Eventually (step1 Host.exe) Rs st) :
    Eventually (step1 Host.exe) Rs ⟨m, Host.addrOf j⟩ := by
  have hS := hpre.1
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hf.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hf.sp
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ cont st ?_ ?_ (hm'.dmem_eq hwf hmem) hpc
  · exact Fr.ofBlock hf hm hm' hwf rfl hmem (by rw [hsp]; rfl) fun r hr ↦ nomatch hr
  · exact fun r ↦ UInt64.toBitVec_inj.mp ((hm'.regs r _ (hregs r)).trans rfl)

/-- **The climbs' start**: from `.L8`, the exit (with the rows when the phase has no openings),
or the loop head with nothing climbed. -/
theorem start_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {h w : Nat}
    (hph : PhaseHW m0.dmem (phO m0) P h w) {m : MachineData} (hc : Checked m0 P Q h w m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b13Offset) ∧ CInv m0 P Q R h w 0 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset)⟩ := by
  have hS := hpre.1
  obtain ⟨-, -, -, hrw, -, -, -, hnwp, hnwr, -, -, -, -, hapr, -⟩ := id hpre
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b10Offset) := b10_in_code.trans hp.1 (by simp [b10])
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b11Offset) := b11_in_code.trans hp.1 (by simp [b11])
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b12Offset) := b12_in_code.trans hp.1 (by simp [b12])
  have hl17 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_17 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b21Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b21Offset) NativeRustcVmArm.Vm.OpenPhase.label_17_at
  have hl18 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_18 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b22Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b22Offset) NativeRustcVmArm.Vm.OpenPhase.label_18_at
  have hml : wireMaxLeafWords = 64 := rfl
  have hmq : wireMaxQueries = 256 := rfl
  have hw64 : w ≤ 64 := hph.2.1
  have hsz : P.size ≤ 256 := hph.2.2.1
  -- `b10`: the openings' address at `0`.
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hc.fr.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hc.fr.sp
  refine exec_then hk10 run_b10 hwf hm fun st hm' hpc ↦ ?_
  have hmA : Match (Env.ofMachine m [(base m0 176, 176)]) (after b10 frS) st.data := by
    rw [after_eq run_b10]; exact hm'
  have hfr : FrO m0 st.data :=
    Bus.Fr.block hc.fr (hN hpre) (by decide) hmA hwf (by rw [after_eq run_b10])
      (by rw [after_eq run_b10]; decide +kernel) (fun r hr ↦ nomatch hr) (by decide)
  have hw0 : NativeRustcVm.WordAt st.data.dmem (base m0 176 + BitVec.ofNat 64 0)
      (UInt64.ofBitVec (off (phO m0) 24)) := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm' (r := 0) (o := 0) rfl (by decide)
      (v := .bin .add .W64 (.reg .X20) (.lit 24)) (by decide +kernel)
    convert this using 2
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
    show off (phO m0) 24 = (m.regs.getXReg .X20).toBitVec + BitVec.ofInt 64 24
    rw [hc.regs.x20]; rfl
  have hsame : ∀ r, r ≠ .X8 → st.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    UInt64.toBitVec_inj.mp ((hm'.regs r (.reg r) (by
      cases r <;> first | rfl | exact absurd rfl hr)).trans rfl)
  have hc0 : (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X23) (.lit 0)).eval
      (Env.ofMachine m [(base m0 176, 176)]) = (P.size == 0) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    show ((m.regs.getXReg .X23).toBitVec == 0#64) = _
    rw [hc.regs.x23]
    exact toUInt64_eq_iff (by omega) 0
  simp only [PcOk] at hpc
  rw [hc0] at hpc
  by_cases h0 : P.size = 0
  · simp only [h0, beq_self_eq_true, ↓reduceIte] at hpc
    obtain ⟨d, pc⟩ := st
    have hpc' : pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b21Offset) := hpc.trans hl17
    subst hpc'
    refine Eventually.mono (exit_rows hp hpre hfr ((hsame .X19 (by decide)).trans hc.regs.x19)
      hph.2.1 hph.2.2.1 hw0 ((hsame .X23 (by decide)).trans hc.regs.x23)
      ((hsame .X21 (by decide)).trans hc.regs.x21) (fun j hj ↦ absurd hj (by omega)) ?_)
      fun st h ↦ .inl h
    have hcl : ClimbsOk R P P.size := by rw [h0]; exact climbsOk_zero R P
    rw [openPhase_climbs hph hc.shape hc.pos, ite_eq_left hcl]
  simp only [show (P.size == 0) = false by simpa using h0, Bool.false_eq_true, ↓reduceIte] at hpc
  obtain ⟨d, pc⟩ := st
  simp only at hpc
  subst hpc
  -- `b11`: the width is at most `192`.
  refine frTestD hpre hfr hk11 run_b11 rfl rfl (fun r ↦ by cases r <;> rfl)
    fun st1 hf1 he1 hd1 hpc1 ↦ ?_
  have he : ∀ r, r ≠ .X8 → st1.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    (he1 r).trans (hsame r hr)
  have hc11 : (((SBool.cmp CmpOp.ult RegWidth.W64 (.reg .X21) (.lit 192)).not.and
      (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X21) (.lit 192)).not).eval
      (Env.ofMachine d [(base m0 176, 176)])) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    show ((!(BitVec.ult (d.regs.getXReg .X21).toBitVec (BitVec.ofInt 64 192))) &&
      !((d.regs.getXReg .X21).toBitVec == BitVec.ofInt 64 192)) = false
    rw [hsame .X21 (by decide), hc.regs.x21]
    have : BitVec.ult w.toUInt64.toBitVec (BitVec.ofInt 64 192) = true := by
      rw [BitVec.ult_eq_decide]
      simp only [decide_eq_true_eq]
      show w.toUInt64.toNat < 192
      simp [Nat.toUInt64]; omega
    rw [this]; rfl
  simp only [PcOk] at hpc1
  rw [hc11] at hpc1
  simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b12`: the root's words, `8 w`, the counters.
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1
  subst hpc1
  have hx1 : (d1.regs.getXReg .X1).toBitVec = rootO m0 := by
    rw [he .X1 (by decide), hc.regs.x1]
  have hrd : Readable m0 (d1.regs.getXReg .X1).toBitVec 32 := by
    rw [hx1]
    have := NativeRustcVm.WordsAt.mapped hrw
    simp only [Vector.length_toList] at this
    exact ⟨this, hnwr⟩
  have hwf12 := Bus.wf_frame2 (F := 176) hS (by decide) hf1.kept hrd (by rw [hx1]; exact hapr)
  have hm12 := Bus.match_frame2 (r := .X1) (n := 32) hS (by decide) (by decide) hf1.sp
  refine exec_then hk12 run_b12 hwf12 hm12 fun st2 hm2 hpc2 ↦ ?_
  have hm2A : Match (Env.ofMachine d1 [(base m0 176, 176), ((d1.regs.getXReg .X1).toBitVec, 32)])
      (after b12 rootS) st2.data := by rw [after_eq run_b12]; exact hm2
  have hfr2 : FrO m0 st2.data :=
    Bus.Fr.block (F := 176) hf1 (hN hpre) (by decide) hm2A hwf12 (by rw [after_eq run_b12])
      (by rw [after_eq run_b12]; decide +kernel) (fun r hr ↦ nomatch hr) (by decide)
  have hb1 : (Env.ofMachine d1 [(base m0 176, 176), ((d1.regs.getXReg .X1).toBitVec, 32)]).base 1 =
      rootO m0 := hx1
  have hroot : ∀ i (hi : i < 4), (Env.ofMachine d1 [(base m0 176, 176),
      ((d1.regs.getXReg .X1).toBitVec, 32)]).load 1 (8 * i) 8 =
      (R.toList[i]'(by simpa using hi)).toBitVec := by
    intro i hi
    have hw := (NativeRustcVm.wordsAt_iff.1 hrw) i (by simpa using hi)
    refine load_word ?_
    rw [hb1]
    exact keepWord hpre hf1 (n := 32) hnwr hapr (by omega) hw
  have hreg : ∀ r v, (after b12 rootS).reg r = some v → st2.data.regs.getXReg r =
      UInt64.ofBitVec (v.eval (Env.ofMachine d1 [(base m0 176, 176),
        ((d1.regs.getXReg .X1).toBitVec, 32)])) :=
    fun r v hv ↦ UInt64.toBitVec_inj.mp (hm2A.regs r v hv)
  have hw8 : NativeRustcVm.WordAt st2.data.dmem (base m0 176 + BitVec.ofNat 64 8)
      (8 * w).toUInt64 := by
    have := NativeRustcVmArm.Sumcheck.Match.wordAt_write hm2 (r := 0) (o := 8) rfl (by decide)
      (v := .un (.ubfm 61 60) .W64 (.reg .X21)) (by decide +kernel)
    convert this using 2
    show _ = UnOp.apply (.ubfm 61 60) .W64 (d1.regs.getXReg .X21).toBitVec
    rw [lsl3, he .X21 (by decide), hc.regs.x21]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.toUInt64]
  have hw0' : NativeRustcVm.WordAt st2.data.dmem (base m0 176 + BitVec.ofNat 64 0)
      (UInt64.ofBitVec (off (phO m0) 24)) :=
    Bus.wordAt_keep (r := 0) (o := 0) (b := base m0 176) (sz := 176) hm2 rfl (by decide)
      (by decide +kernel) (by show NativeRustcVm.WordAt d1.dmem _ _; rw [hd1]; exact hw0)
  have hk2 : ∀ r, (after b12 rootS).reg r = some (.reg r) →
      st2.data.regs.getXReg r = d1.regs.getXReg r := fun r hv ↦ hreg r _ hv
  have hl : ∀ i (hi : i < 4), (after b12 rootS).reg (([XReg.X26, .X27, .X28, .X29])[i]'(by
      simpa using hi)) = some (.load 1 (8 * i) 8) := by
    intro i hi
    rw [after_eq run_b12]
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  have hroot' : ∀ i (hi : i < 4), st2.data.regs.getXReg (([XReg.X26, .X27, .X28, .X29])[i]'(by
      simpa using hi)) = R.toList[i]'(by simpa using hi) := fun i hi ↦
    (hreg _ _ (hl i hi)).trans (by
      show UInt64.ofBitVec (Env.load _ 1 (8 * i) 8) = _
      rw [hroot i hi])
  have hd : ∀ r, (after b12 rootS).reg r = some (.reg r) → r ≠ .X8 →
      st2.data.regs.getXReg r = m.regs.getXReg r := fun r hv hr ↦ (hk2 r hv).trans (he r hr)
  refine Eventually.done _ (.inr ⟨hpc2, hfr2, Nat.pos_of_ne_zero h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hroot' 0 (by decide), hroot' 1 (by decide), hroot' 2 (by decide), hroot' 3 (by decide), hw0',
    hw8, hc.shape, hc.pos, climbsOk_zero R P⟩)
  · rw [hd .X19 (by rw [after_eq run_b12]; rfl) (by decide)]; exact hc.regs.x19
  · rw [hd .X20 (by rw [after_eq run_b12]; rfl) (by decide), hc.regs.x20]; simp
  · rw [hd .X21 (by rw [after_eq run_b12]; rfl) (by decide)]; exact hc.regs.x21
  · rw [hd .X22 (by rw [after_eq run_b12]; rfl) (by decide)]; exact hc.regs.x22
  · rw [hd .X23 (by rw [after_eq run_b12]; rfl) (by decide)]; exact hc.regs.x23
  · rw [hreg .X24 (.reg .X23) (by rw [after_eq run_b12]; rfl)]
    show (d1.regs.getXReg .X23).toNat = _
    rw [he .X23 (by decide), hc.regs.x23]
    simp [Nat.toUInt64]; omega
  · rw [hreg .X25 (.lit 395264) (by rw [after_eq run_b12]; rfl)]
    rfl


end

end NativeRustcVmArm.Sumcheck.OpenPhase
