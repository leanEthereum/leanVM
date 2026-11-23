module

public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Sumcheck.OpenPhase.Path

/-!
# `open_phase`: a climb's check

At `b16` (`Climbed`), `b16` to `b19` test the path's top word by word against the root's (X26
to X29; `test_spec`): a mismatch leaves for `.L18` (`exit_fail`, the climbs fail); `b20` steps
the counters: back to `.L11` with one climb more (`CInv`), or after the last one `.L17`
(`exit_rows`) (`round_spec`).
-/

namespace NativeRustcVmArm.Sumcheck.OpenPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.OpenPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Sumcheck
open LeanVM.Protocol LeanVM.Protocol.Compile NativeVm

public section

variable [Host] {P : Array OpeningW} {R : Digest} {Q : Array UInt64} {m0 : MachineData} {k : Nat}

/-- **A test of the path's top**: `ds` loads its word `i` (the frame's `o = 16 + 8 i`) into X8
and leaves for `.L18` where it is not the root's word `i` (in `r`). -/
theorem test_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {h w : Nat}
    (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat} {m : MachineData}
    (hc : Climbed m0 P Q R h w j m) {ds : List Directive} {S' : SState} {a i o : Nat} {r : XReg}
    (hi4 : i < 4) (ho : o = 16 + 8 * i) (hk : ds.IsInfixAt Host.prog a)
    (hx : exec ds frS = some (S', .cond (SBool.not (SBool.cmp CmpOp.eq RegWidth.W64
      (.load 0 o 8) (.reg r))) NativeRustcVmArm.Vm.OpenPhase.label_18))
    (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (hregs : ∀ r, r ≠ .X8 → S'.reg r = some (.reg r))
    (hr : m.regs.getXReg r = R.toList[i]'(by simpa using hi4)) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (a + ds.length) ∧ Climbed m0 P Q R h w j st.data ∧
          (climb (hashWords (P[j]'hc.inv.lt).leaf) (P[j]'hc.inv.lt).leafIndex
            (P[j]'hc.inv.lt).path).toList[i]'(by simpa using hi4) =
            R.toList[i]'(by simpa using hi4)))
      ⟨m, Host.addrOf a⟩ := by
  have hS := hpre.1
  have hlt := hc.inv.lt
  have hl18 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_18 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b22Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b22Offset) NativeRustcVmArm.Vm.OpenPhase.label_18_at
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hc.inv.fr.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hc.inv.fr.sp
  refine exec_then hk hx hwf hm fun st hm' hpc ↦ ?_
  have hf' : FrO m0 st.data :=
    Fr.ofBlock hc.inv.fr hm hm' hwf rfl hmem (by rw [hsp]; rfl) fun r hr ↦ nomatch hr
  have hd : st.data.dmem = m.dmem := hm'.dmem_eq hwf hmem
  have hsame : ∀ r, r ≠ .X8 → st.data.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
    UInt64.toBitVec_inj.mp ((hm'.regs r _ (hregs r hr)).trans rfl)
  obtain ⟨T, hT⟩ : ∃ T, T = climb (hashWords (P[j]'hlt).leaf) (P[j]'hlt).leafIndex
      (P[j]'hlt).path := ⟨_, rfl⟩
  have htop := hc.top
  rw [← hT] at htop
  have hwi : NativeRustcVm.WordAt m.dmem (base m0 176 + BitVec.ofNat 64 o)
      (T.toList[i]'(by simpa using hi4)) := by
    have := htop.getElem (i := i) (by simpa using hi4)
    rwa [NativeRustcVm.addr_add_add, ← ho] at this
  have hl : (Env.ofMachine m [(base m0 176, 176)]).load 0 o 8 =
      (T.toList[i]'(by simpa using hi4)).toBitVec := load_word hwi
  have hev : (SBool.not (SBool.cmp CmpOp.eq RegWidth.W64 (.load 0 o 8) (.reg r))).eval
      (Env.ofMachine m [(base m0 176, 176)]) =
      !((T.toList[i]'(by simpa using hi4)).toBitVec == (R.toList[i]'(by simpa using hi4)).toBitVec) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    show (!((Env.ofMachine m [(base m0 176, 176)]).load 0 o 8 ==
      (m.regs.getXReg r).toBitVec)) = _
    rw [hl, hr]
  simp only [PcOk] at hpc
  rw [hev] at hpc
  by_cases heq : T.toList[i]'(by simpa using hi4) = R.toList[i]'(by simpa using hi4)
  · rw [heq] at hpc
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc
    have htop' : NativeRustcVm.WordsAt st.data.dmem (base m0 176 + BitVec.ofNat 64 16)
        (climb (hashWords (P[j]'hlt).leaf) (P[j]'hlt).leafIndex (P[j]'hlt).path).toList := by
      rw [hd]; exact hc.top
    have hkd : ∀ {o' : Nat} {bs : List UInt8}, o' + bs.length ≤ 16 →
        NativeRustcVm.BytesAt m.dmem (base m0 176 + BitVec.ofNat 64 o') bs →
        NativeRustcVm.BytesAt st.data.dmem (base m0 176 + BitVec.ofNat 64 o') bs :=
      fun _ h ↦ by rw [hd]; exact h
    refine Eventually.done _ (.inr ⟨hpc, ⟨hc.inv.keep hf' (fun r' hr' ↦ hsame r' ?_) hkd, htop'⟩,
      by subst hT; exact heq⟩)
    rintro rfl
    exact absurd hr' (by decide)
  · have hne : ((T.toList[i]'(by simpa using hi4)).toBitVec ==
        (R.toList[i]'(by simpa using hi4)).toBitVec) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h' ↦ heq (UInt64.toBitVec_inj.mp h')
    rw [hne] at hpc
    simp only [Bool.not_false, ↓reduceIte] at hpc
    obtain ⟨d, pc⟩ := st
    simp only at hpc
    rw [hl18] at hpc
    subst hpc
    refine Eventually.mono (exit_fail hp hpre hf' ((hsame .X19 (by decide)).trans hc.inv.x19) ?_)
      fun st h ↦ .inl h
    rw [openPhase_climbs hph hc.inv.shape hc.inv.pos]
    refine ite_eq_right fun hcl ↦ heq ?_
    rw [hT, hcl j hlt hlt]

/-- **A climb's check**: from `b16`, the exit (a mismatch, or the rows after the last climb) or
`.L11` with one climb more. -/
theorem round_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0) {h w : Nat}
    (hph : PhaseHW m0.dmem (phO m0) P h w) {j : Nat} {m : MachineData}
    (hc : Climbed m0 P Q R h w j m) :
    Eventually (step1 Host.exe)
      (fun st ↦ (st.pc = retOf m0 ∧ OpenPhasePost P R Q m0 st.data) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b13Offset) ∧ CInv m0 P Q R h w (j + 1) st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b16Offset)⟩ := by
  have hS := hpre.1
  have hlt := hc.inv.lt
  have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b16Offset) := b16_in_code.trans hp.1 (by simp [b16])
  have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b17Offset) := b17_in_code.trans hp.1 (by simp [b17])
  have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b18Offset) := b18_in_code.trans hp.1 (by simp [b18])
  have hk19 : b19.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b19Offset) := b19_in_code.trans hp.1 (by simp [b19])
  have hk20 : b20.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.OpenPhase.b20Offset) := b20_in_code.trans hp.1 (by simp [b20])
  have hl11 : Labels.label NativeRustcVmArm.Vm.OpenPhase.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.OpenPhase.b13Offset) := hp.label (j := NativeRustcVmArm.Vm.OpenPhase.b13Offset) NativeRustcVmArm.Vm.OpenPhase.label_11_at
  have how : openingWords = 193 := rfl
  have hpw : phaseWords = 49411 := rfl
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hw64 : w ≤ 64 := hph.2.1
  -- `b16` to `b19`: the path's top is the root.
  refine Eventually.bind (test_spec hp hpre hph hc (i := 0) (by decide) rfl hk16 run_b16 rfl rfl
    (fun r hr ↦ by cases r <;> first | rfl | exact absurd rfl hr) hc.inv.x26) fun st1 h1 ↦ ?_
  rcases h1 with h1 | ⟨hpc1, hc1, e0⟩
  · exact Eventually.done _ (.inl h1)
  obtain ⟨d1, pc1⟩ := st1
  simp only at hpc1
  subst hpc1
  refine Eventually.bind (test_spec hp hpre hph hc1 (i := 1) (by decide) rfl hk17 run_b17 rfl rfl
    (fun r hr ↦ by cases r <;> first | rfl | exact absurd rfl hr) hc1.inv.x27) fun st2 h2 ↦ ?_
  rcases h2 with h2 | ⟨hpc2, hc2, e1⟩
  · exact Eventually.done _ (.inl h2)
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2
  subst hpc2
  refine Eventually.bind (test_spec hp hpre hph hc2 (i := 2) (by decide) rfl hk18 run_b18 rfl rfl
    (fun r hr ↦ by cases r <;> first | rfl | exact absurd rfl hr) hc2.inv.x28) fun st3 h3 ↦ ?_
  rcases h3 with h3 | ⟨hpc3, hc3, e2⟩
  · exact Eventually.done _ (.inl h3)
  obtain ⟨d3, pc3⟩ := st3
  simp only at hpc3
  subst hpc3
  refine Eventually.bind (test_spec hp hpre hph hc3 (i := 3) (by decide) rfl hk19 run_b19 rfl rfl
    (fun r hr ↦ by cases r <;> first | rfl | exact absurd rfl hr) hc3.inv.x29) fun st4 h4 ↦ ?_
  rcases h4 with h4 | ⟨hpc4, hc4, e3⟩
  · exact Eventually.done _ (.inl h4)
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4
  subst hpc4
  have hTR : climb (hashWords (P[j]'hlt).leaf) (P[j]'hlt).leafIndex (P[j]'hlt).path = R :=
    Vector.toList_inj.mp (List.ext_getElem (by simp) fun n h1 _ ↦ by
      simp only [Vector.length_toList] at h1
      match n, h1 with
      | 0, _ => exact e0
      | 1, _ => exact e1
      | 2, _ => exact e2
      | 3, _ => exact e3)
  have hcl : ClimbsOk R P (j + 1) := (climbsOk_succ hlt).2 ⟨hc.inv.climbs, hTR⟩
  -- `b20`: the counters.
  have hi := hc4.inv
  have hwf := Bus.wf_frame (F := 176) hS (by decide) hi.fr.kept
  have hm := Bus.match_frame hS (F := 176) (by decide) (by decide) hi.fr.sp
  refine exec_then hk20 run_b20 hwf hm fun st5 hm5 hpc5 ↦ ?_
  have hf5 : FrO m0 st5.data :=
    Fr.ofBlock hi.fr hm hm5 hwf rfl rfl rfl fun r hr ↦ nomatch hr
  have hd5 : st5.data.dmem = d4.dmem := hm5.dmem_eq hwf rfl
  have hs5 : ∀ r, r ≠ .X20 → r ≠ .X24 → r ≠ .X25 →
      st5.data.regs.getXReg r = d4.regs.getXReg r := fun r h1 h2 h3 ↦
    UInt64.toBitVec_inj.mp ((hm5.regs r (.reg r) (by
      cases r <;> first | rfl | exact absurd rfl h1 | exact absurd rfl h2 | exact absurd rfl h3)).trans
      rfl)
  have h24 : (d4.regs.getXReg .X24).toBitVec.toNat = P.size - j := hi.x24
  have hev : (SBool.not (SBool.cmp CmpOp.eq RegWidth.W64 (.reg .X24) (.lit 1))).eval
      (Env.ofMachine d4 [(base m0 176, 176)]) = !(j + 1 == P.size) := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Sym.low_W64]
    show (!((d4.regs.getXReg .X24).toBitVec == 1#64)) = _
    by_cases hj1 : j + 1 = P.size
    · have e : (d4.regs.getXReg .X24).toBitVec = 1#64 :=
        BitVec.eq_of_toNat_eq (by rw [h24]; simp; omega)
      simp [e, hj1]
    · have e1 : ((d4.regs.getXReg .X24).toBitVec == 1#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro e
        rw [e] at h24
        have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
        omega
      have e2 : (j + 1 == P.size) = false := by simpa using hj1
      rw [e1, e2]
  simp only [PcOk] at hpc5
  rw [hev] at hpc5
  have hw0 : NativeRustcVm.WordAt st5.data.dmem (base m0 176 + BitVec.ofNat 64 0)
      (UInt64.ofBitVec (off (phO m0) 24)) := by rw [hd5]; exact hi.w0
  by_cases hj1 : j + 1 = P.size
  · -- after the last climb: the rows.
    simp only [hj1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    obtain ⟨d5, pc5⟩ := st5
    simp only at hpc5
    subst hpc5
    refine Eventually.mono (exit_rows hp hpre hf5 ((hs5 .X19 (by decide) (by decide)
      (by decide)).trans hi.x19) hph.2.1 hph.2.2.1 hw0
      ((hs5 .X23 (by decide) (by decide) (by decide)).trans hi.x23)
      ((hs5 .X21 (by decide) (by decide) (by decide)).trans hi.x21) (fun j' hj' ↦ ?_) ?_)
      fun st h ↦ .inl h
    · obtain ⟨hl, hws⟩ := leaf_words hph j' hj'
      refine ⟨hl, ?_⟩
      rw [off_off, off] at hws ⊢
      exact ph_keep hpre hf5 (by rw [hpw, how]; omega) (n := 8 * w) (by rw [hpw, how]; omega)
        (le_of_eq (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList, hl])) hws
    · rw [openPhase_climbs hph hi.shape hi.pos, ite_eq_left (hj1 ▸ hcl)]
  · -- one climb more.
    have hb : (j + 1 == P.size) = false := by simpa using hj1
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc5
    have hj1' : j + 1 < P.size := by omega
    have hx20 : (st5.data.regs.getXReg .X20).toBitVec =
        phO m0 + BitVec.ofNat 64 (1544 * (j + 1)) := by
      rw [hm5.regs .X20 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      show (d4.regs.getXReg .X20).toBitVec + BitVec.ofInt 64 1544 = _
      rw [hi.x20, show BitVec.ofInt 64 1544 = BitVec.ofNat 64 1544 from rfl,
        NativeRustcVm.addr_add_add, show 1544 * j + 1544 = 1544 * (j + 1) by ring]
    have hx24 : (st5.data.regs.getXReg .X24).toNat = P.size - (j + 1) := by
      rw [UInt64.toNat, hm5.regs .X24 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      show ((d4.regs.getXReg .X24).toBitVec - 1#64).toNat = _
      have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h24, h1]; omega), h24, h1]
      omega
    have hx25 : (st5.data.regs.getXReg .X25).toNat = 395264 - 1544 * (j + 1) := by
      have h25 : (d4.regs.getXReg .X25).toBitVec.toNat = 395264 - 1544 * j := hi.x25
      rw [UInt64.toNat, hm5.regs .X25 _ rfl]
      simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
      show ((d4.regs.getXReg .X25).toBitVec - 1544#64).toNat = _
      have h1 : (1544#64 : BitVec 64).toNat = 1544 := rfl
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h25, h1]; omega), h25, h1]
      omega
    refine Eventually.done _ (.inr ⟨hpc5.trans hl11, hf5, hj1',
      (hs5 .X19 (by decide) (by decide) (by decide)).trans hi.x19, hx20,
      (hs5 .X21 (by decide) (by decide) (by decide)).trans hi.x21,
      (hs5 .X22 (by decide) (by decide) (by decide)).trans hi.x22,
      (hs5 .X23 (by decide) (by decide) (by decide)).trans hi.x23, hx24, hx25,
      (hs5 .X26 (by decide) (by decide) (by decide)).trans hi.x26,
      (hs5 .X27 (by decide) (by decide) (by decide)).trans hi.x27,
      (hs5 .X28 (by decide) (by decide) (by decide)).trans hi.x28,
      (hs5 .X29 (by decide) (by decide) (by decide)).trans hi.x29, hw0,
      by rw [hd5]; exact hi.w8, hi.shape, hi.pos, hcl⟩)

end

end NativeRustcVmArm.Sumcheck.OpenPhase
