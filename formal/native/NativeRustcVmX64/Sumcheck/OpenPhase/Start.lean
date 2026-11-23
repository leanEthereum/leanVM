module

public import NativeRustcVmX64.Sumcheck.OpenPhase.Check

/-!
# `open_phase`: the climbs' start (x86-64)

At `b10` (`Checked`): the output's address and the height stored in the frame; without openings,
`NativeRustcVmX64.Vm.OpenPhase.label_13` (`exit_rows`); else `b11` (the width bound, never above `192`) and `b12` (the
root's words into the frame, the counters) reach the climbs' loop head `NativeRustcVmX64.Vm.OpenPhase.label_7` (`CInv`,
`start_spec`).
-/

namespace NativeRustcVmX64.Sumcheck.OpenPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.OpenPhase NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Sumcheck LeanVM.Protocol LeanVM.Protocol.Compile

@[expose] public section

/-- The frame's bytes from `16` to `64` (the output's address, the root, the height) kept. -/
def LowKept (m0 m m' : MachineData) : Prop :=
  ∀ j, 16 ≤ j → j < 64 → m'.dmem.get? (off (fa m0) j) = m.dmem.get? (off (fa m0) j)

/-- **The climbs' invariant** at `NativeRustcVmX64.Vm.OpenPhase.label_7` (`b13`), `j < |P|` climbs checked. -/
structure CInv (m0 : MachineData) (P : Array OpeningW) (Q : Array UInt64) (R : Digest)
    (h w j : Nat) (m : MachineData) : Prop where
  fr : FrO m0 8 m
  lt : j < P.size
  shape : ShapeOk P Q h w (reg m0 .rdx).toNat (reg m0 .rcx).toNat
  pos : PositionsOk P Q P.size
  climbs : ClimbsOk R P j
  r12 : (reg m .r12).toNat = j
  r13 : reg m .r13 = P.size.toUInt64.toBitVec
  r14 : reg m .r14 = w.toUInt64.toBitVec
  r15 : reg m .r15 = off (phO m0) (544 + 1544 * j)
  rbp : reg m .rbp = off (phO m0) 24
  w16 : NativeRustcVm.WordAt m.dmem (off (fa m0) 16) (UInt64.ofBitVec (outO m0))
  w56 : NativeRustcVm.WordAt m.dmem (off (fa m0) 56) h.toUInt64
  root : ∀ i (hi : i < 4), NativeRustcVm.WordAt m.dmem (off (fa m0) (48 - 8 * i))
    (R.toList[i]'(by simpa using hi))

end

public section

variable {m0 m m' : MachineData} {P : Array OpeningW} {Q : Array UInt64} {R : Digest}
  {h w : Nat}

theorem LowKept.trans {m'' : MachineData} (h1 : LowKept m0 m m') (h2 : LowKept m0 m' m'') :
    LowKept m0 m m'' := fun j a b ↦ (h2 j a b).trans (h1 j a b)

/-- Words of the frame from `16` to `64` kept. -/
theorem LowKept.word (hl : LowKept m0 m m') {o : Nat} {v : UInt64} (h1 : 16 ≤ o) (h2 : o + 8 ≤ 64)
    (hv : NativeRustcVm.WordAt m.dmem (off (fa m0) o) v) :
    NativeRustcVm.WordAt m'.dmem (off (fa m0) o) v :=
  bytesAt_congr hv fun t ht ↦ by
    rw [NativeRustcVm.length_wordBytes] at ht
    rw [off_add]
    exact hl _ (by omega) (by omega)

/-- The output's address loaded from the frame's `16`. -/
theorem w16_load [Labels] {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
    {ret : BitVec 64}
    (hv : NativeRustcVm.WordAt m.dmem (off (fa m0) 16) (UInt64.ofBitVec (outO m0))) :
    (frameEnv m0 m 176 rest vars ret).load 0 16 8 = outO m0 :=
  load_ofMachine (o := 16) rfl hv

variable {j : Nat}

/-- **The climbs' invariant kept** by a step keeping RBP, R12 to R15 and the frame's bytes from
`16` to `64`. -/
theorem CInv.keep (hi : CInv m0 P Q R h w j m) (hf : FrO m0 8 m')
    (hr : ∀ r, r = .rbp ∨ r = .r12 ∨ r = .r13 ∨ r = .r14 ∨ r = .r15 → reg m' r = reg m r)
    (hl : LowKept m0 m m') : CInv m0 P Q R h w j m' :=
  ⟨hf, hi.lt, hi.shape, hi.pos, hi.climbs, by rw [hr _ (by simp)]; exact hi.r12,
    (hr _ (by simp)).trans hi.r13, (hr _ (by simp)).trans hi.r14, (hr _ (by simp)).trans hi.r15,
    (hr _ (by simp)).trans hi.rbp, hl.word (by omega) (by omega) hi.w16,
    hl.word (by omega) (by omega) hi.w56,
    fun i hi4 ↦ hl.word (by omega) (by omega) (hi.root i hi4)⟩

section
variable [Labels]

/-- A block writing the frame only below `16`: its bytes from `16` to `64` kept. -/
theorem lowKept_block {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {S : SState} (hwf : (frameEnv m0 m 176 rest vars ret).WF)
    (hm : Match (frameEnv m0 m 176 rest vars ret) S m') (hin : writesIn S = true)
    (hW : ∀ w ∈ S.mem, w.r = 0 → w.off + w.n ≤ 16) : LowKept m0 m m' :=
  fun j h1 h2 ↦ hm.get?_mem0 hwf (not_written0 hwf hm hin (by omega) fun w hw hr ↦
    Or.inl (by have := hW w hw hr; omega))

end

/-- A call writing 32 bytes of the frame from `o ≥ 64`: its bytes from `16` to `64` kept. -/
theorem lowKept_call {o : Nat} (ho : 64 ≤ o) (hk : ∀ j, j < 184 → (j < o ∨ o + 32 ≤ j) →
      m'.dmem.get? (off (fa m0) j) = m.dmem.get? (off (fa m0) j)) : LowKept m0 m m' :=
  fun j _ h2 ↦ hk j (by omega) (.inl (by omega))

/-- The model, the checks passed: the climbs decide. -/
theorem climbs_none {d : Mem 64} {b : BitVec 64} (hph : PhaseHW d b P h w)
    (hsh : ShapeOk P Q h w (reg m0 .rdx).toNat (reg m0 .rcx).toNat) (hpos : PositionsOk P Q P.size)
    (hn : ¬ ClimbsOk R P P.size) :
    openPhase R (reg m0 .rdx).toNat (reg m0 .rcx).toNat Q P = none := by
  rw [openPhase_climbs hph hsh hpos, ite_eq_right hn]

theorem climbs_some {d : Mem 64} {b : BitVec 64} (hph : PhaseHW d b P h w)
    (hsh : ShapeOk P Q h w (reg m0 .rdx).toNat (reg m0 .rcx).toNat) (hpos : PositionsOk P Q P.size)
    (hn : ClimbsOk R P P.size) :
    openPhase R (reg m0 .rdx).toNat (reg m0 .rcx).toNat Q P = some (P.map (·.leaf)) := by
  rw [openPhase_climbs hph hsh hpos, ite_eq_left hn]

/-- The leaf words of opening `j`, read in place from the openings' address. -/
theorem leaf_words [Labels] (hpre : OpenPhasePre P R Q m0) (hph : PhaseHW m0.dmem (phO m0) P h w)
    (hs : NativeRustcVm.SameOutside m0.dmem m.dmem (Stk m0)) :
    ∀ j (hj : j < P.size), P[j].leaf.size = w ∧
      NativeRustcVm.WordsAt m.dmem (off (off (phO m0) 24) (8 * (1 + j * openingWords)))
        P[j].leaf.toList := by
  intro j hj
  have ho := hph.2.2.2.2.2.2 j hj
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hw : w ≤ 64 := hph.2.1
  have how : openingWords = 193 := rfl
  have hpw : phaseWords = 49411 := rfl
  refine ⟨ho.1, ?_⟩
  have := ho.2.2.2.2.1
  rw [off_off] at this ⊢
  rw [show 24 + 8 * (1 + j * openingWords) = 8 * (3 + j * openingWords) + 8 by omega]
  refine ph_keep hpre hs (by rw [how]; omega) ?_ this
  rw [NativeRustcVm.length_wordsBytes, Array.length_toList, ho.1, how]
  omega

variable [Host] {k : Nat}

/-- **The climbs' start**: from `b10`, the exit (with the rows when the phase has no openings),
or the loop head with nothing climbed. -/
theorem start_spec (hp : Placed code k) (hpre : OpenPhasePre P R Q m0)
    (hph : PhaseHW m0.dmem (phO m0) P h w) (hc : Checked m0 P Q h w m) :
    Eventually (step1 Host.exe)
      (fun st ↦ Done P R Q m0 st ∨ (st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b13Offset) ∧ CInv m0 P Q R h w 0 st.data))
      ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b10Offset)⟩ := by
  have hst := hpre.1
  have hwm : w ≤ 64 := hph.2.1
  have hsz : P.size ≤ 256 := hph.2.2.1
  have hhm : h ≤ 32 := hph.1
  -- `b10`: the output's address and the height into the frame.
  have hwf := wf0 hst hc.fr (ret := 0)
  refine exec_then (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf nofun
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hc.fr.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hW1, hw16, hw56, hk1⟩ := ok_b10
  have hf1 : FrO m0 8 st1.data := FrO.block hst hc.fr hwf hm1 hmid1 hW1
  have hk1' : ∀ r, r ≠ .rsp → reg st1.data r = reg m r :=
    fun r h1 ↦ KeepBut.regs hk1 hm1 h1 rfl
  have w16 : NativeRustcVm.WordAt st1.data.dmem (off (fa m0) 16) (UInt64.ofBitVec (outO m0)) :=
    wordAt_written hm1 (r := 0) rfl (by omega) hw16 hc.regs.rdi
  have w56 : NativeRustcVm.WordAt st1.data.dmem (off (fa m0) 56) h.toUInt64 :=
    wordAt_written hm1 (r := 0) rfl (by omega) hw56 hc.regs.r10
  have hc10 : (isZero (.reg .r13)).eval (frameEnv m0 m 176 [] (fun _ ↦ 0) 0) =
      decide (P.size = 0) := by
    rw [isZero_eval]
    show (reg m .r13 == 0#64) = _
    rw [hc.regs.r13, beq_zero_toUInt64 (by omega)]
  simp only [PcOk, hc10] at hpc1
  by_cases h0 : P.size = 0
  · simp only [h0, decide_true, ↓reduceIte] at hpc1
    obtain ⟨d1, pc1⟩ := st1
    have hpc1' : pc1 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b21Offset) := hpc1.trans (hp.label NativeRustcVmX64.Vm.OpenPhase.label_13_at)
    subst hpc1'
    refine Eventually.mono (exit_rows hp hpre hf1 w16 hph.2.1 hph.2.2.1
      ((hk1' _ (by decide)).trans hc.rbp) ((hk1' _ (by decide)).trans hc.regs.r13)
      ((hk1' _ (by decide)).trans hc.regs.r14) (leaf_words hpre hph hf1.same) ?_) fun st h ↦ .inl h
    exact climbs_some hph hc.shape hc.pos (by rw [h0]; exact climbsOk_zero R P)
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  obtain ⟨d1, pc1⟩ := st1
  have hpc1' : pc1 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b11Offset) := hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b10_next)
  subst hpc1'
  -- `b11`: the width is at most `192`.
  obtain ⟨hmid11, hmem11, hk11⟩ := ok_b11
  refine frTest hst hf1 (infix_of b11_in_code (by simp [b11]) hp) exit_b11 nofun hmid11 hmem11
    hk11 fun st2 hf2 hd2 hk2 hm2 hpc2 ↦ ?_
  have hc11 : c11.eval (frameEnv m0 d1 176 [] (fun _ ↦ 0) 0) = false := by
    simp only [c11, SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [show d1.regs.get64 .r14 = w.toUInt64.toBitVec from
      (hk1' _ (by decide)).trans hc.regs.r14]
    have : BitVec.ult w.toUInt64.toBitVec (BitVec.ofNat 64 192) = true := by
      rw [BitVec.ult_eq_decide, toUInt64_toNat (by omega)]
      simp only [BitVec.toNat_ofNat, decide_eq_true_eq]
      omega
    rw [this]
    rfl
  simp only [PcOk, hc11, Bool.false_eq_true, ↓reduceIte] at hpc2
  obtain ⟨d2, pc2⟩ := st2
  have hpc2' : pc2 = Host.addrOf (k + NativeRustcVmX64.Vm.OpenPhase.b12Offset) := hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b11_next)
  subst hpc2'
  have hk2' : ∀ r, r ≠ .rsp → reg d2 r = reg m r :=
    fun r h1 ↦ (hk2 r h1 rfl).trans (hk1' r h1)
  -- `b12`: the root's words, the counters.
  obtain ⟨-, -, -, -, hrw, -, -, -, -, hnwr, -, -, -, -, hapr, -⟩ := id hpre
  have hrm : NativeRustcVm.Mapped m0.dmem (rootO m0) 32 := by
    have := NativeRustcVm.WordsAt.mapped hrw
    simpa using this
  have hwf12 := wf1 hst hf2 (ret := 0) (Mapped.keeps hrm hf2.frame.kept) hnwr hapr
  have hrsi : reg d2 .rsi = rootO m0 := (hk2' _ (by decide)).trans hc.regs.rsi
  refine exec_then (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf12 nofun
    (match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf2.frame.rsp_eval, known_ptr rfl hrsi, trivial⟩
      trivial trivial trivial) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hW3, hr0, hr1, hr2, hr3, h12, h15, hk3⟩ := ok_b12
  have hW3' : ∀ w ∈ (after b12 rootS).mem, w.r = 0 ∧ w.off + w.n ≤ 176 :=
    fun w hw ↦ ⟨(hW3 w hw).1, by have := (hW3 w hw).2.2; omega⟩
  have hf3 : FrO m0 8 st3.data := FrO.block hst hf2 hwf12 hm3 hmid3 hW3'
  have hk3' : ∀ r, r ≠ .rsp → [Reg64.rax, .rsi, .r12, .r15].contains r = false →
      reg st3.data r = reg d2 r := fun r h1 h2 ↦ KeepBut.regs hk3 hm3 h1 h2
  have hroot : ∀ i (hi : i < 4), (frameEnv m0 d2 176 [(rootO m0, 32)] (fun _ ↦ 0) 0).load 1
      (8 * i) 8 = (R.toList[i]'(by simpa using hi)).toBitVec := by
    intro i hi
    refine load_ofMachine (o := 8 * i) rfl ?_
    have := hrw.getElem (i := i) (by simpa using hi)
    exact keepB hst hf2.same (n := 8)
      (NativeRustcVm.NoWrap.sub hnwr (by omega))
      (by
        unfold NativeRustcVm.Apart
        have h' : (rootO m0).toNat + 32 ≤ (stackBelow m0 openPhaseStack).toNat ∨
            (stackBelow m0 openPhaseStack).toNat + (openPhaseStack + 8) ≤ (rootO m0).toNat := hapr
        have hn' : (rootO m0).toNat + 32 ≤ 2 ^ 64 := hnwr
        have h'' : (reg m0 .rsi).toNat + 32 ≤ (stackBelow m0 openPhaseStack).toNat ∨
            (stackBelow m0 openPhaseStack).toNat + (openPhaseStack + 8) ≤ (reg m0 .rsi).toNat :=
          hapr
        have hn'' : (reg m0 .rsi).toNat + 32 ≤ 2 ^ 64 := hnwr
        rw [toNat_off (by omega)]
        omega)
      (by rw [NativeRustcVm.length_wordBytes]) this
  have hin3 := writesIn_of_mid hmid3
  have hmiss : ∀ {o : Nat}, o + 8 ≤ 24 ∨ 56 ≤ o → ∀ w ∈ (after b12 rootS).mem, w.r = 0 →
      w.off + w.n ≤ o ∨ o + (8 : Nat) ≤ w.off := by
    intro o ho w hw _
    have := hW3 w hw
    omega
  refine .done _ (.inr ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.OpenPhase.b12_next), ?_⟩)
  refine ⟨hf3, Nat.pos_of_ne_zero h0, hc.shape, hc.pos, climbsOk_zero R P, ?_, ?_, ?_, ?_, ?_,
    keepW hwf12 hm3 hin3 (by omega) (hmiss (.inl (by omega))) (by
      rw [show d2.dmem = d1.dmem from hd2]; exact w16),
    keepW hwf12 hm3 hin3 (by omega) (hmiss (.inr (by omega))) (by
      rw [show d2.dmem = d1.dmem from hd2]; exact w56), fun i hi ↦ ?_⟩
  · rw [show reg st3.data .r12 = _ from hm3.regs .r12 _ h12]; rfl
  · rw [hk3' _ (by decide) (by decide), hk2' _ (by decide)]; exact hc.regs.r13
  · rw [hk3' _ (by decide) (by decide), hk2' _ (by decide)]; exact hc.regs.r14
  · rw [show reg st3.data .r15 = _ from hm3.regs .r15 _ h15]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show d2.regs.get64 .r15 = phO m0 from (hk2' _ (by decide)).trans hc.regs.r15,
      BitVec.add_comm]
  · rw [hk3' _ (by decide) (by decide), hk2' _ (by decide)]; exact hc.rbp
  · have hv : ∀ i (hi : i < 4), WordW 0 (48 - 8 * i) (.load 1 (8 * i) 8) (after b12 rootS) := by
      intro i hi
      match i, hi with
      | 0, _ => exact hr0
      | 1, _ => exact hr1
      | 2, _ => exact hr2
      | 3, _ => exact hr3
    exact wordAt_written hm3 (r := 0) rfl (by omega) (hv i hi) (hroot i hi)

end

end NativeRustcVmX64.Sumcheck.OpenPhase
