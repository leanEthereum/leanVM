module

public import NativeRustcVmX64.Bus.BusLayout.Offsets

/-!
# `bus_layout`'s placements (x86-64)

The loop head `NativeRustcVmX64.Vm.BusLayout.label_19` (`b26`, `PInv j`): size `j` and offset `j` loaded; a framework
placement pushed (`b27`, `b28`), or a table's (`b30`, `b31`); the count (`b25`): back at the head,
or out (`NativeRustcVmX64.Vm.BusLayout.label_26`, `PEnd`) after the last (`place_step`, `place_run`).
-/

namespace NativeRustcVmX64.Bus.BusLayout

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Bus NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVmX64.Vm.BusLayout
open LeanVM.Protocol.Verifier (Placement)

public section

/-- At `NativeRustcVmX64.Vm.BusLayout.label_26`: every placement pushed. -/
structure PEnd (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (st : MachineData) : Prop where
  bd : Body m0 1808 busLayoutStack slots 8 st
  rbx : reg st .rbx = reg m0 .rdi
  rdx : reg st .rdx = BitVec.ofNat 64 (nf m0)
  part : Part st.dmem L bl m0 (nf m0 + bl.length)

/-- A word of the frame, loaded at an index. -/
theorem load_idx [Labels] {m0 d : MachineData} {vars : Nat → BitVec 64} {ret : BitVec 64}
    {o j : Nat} {w : UInt64} (h : NativeRustcVm.WordAt d.dmem (off (fb m0) (o + 8 * j)) w)
    (hc : d.regs.get64 .rcx = BitVec.ofNat 64 j) (hj : j < 54) :
    (Sym.loadx 0 o (.bin .mul .W64 (.reg .rcx) (.lit 8)) 8).eval
      (Env.ofMachine d [(fb m0, 1808 + 8)] vars ret) = w.toBitVec := by
  show (Env.ofMachine d _ vars ret).load 0 (o + (BinOp.mul.apply .W64 (d.regs.get64 .rcx)
    (BitVec.ofNat 64 8)).toNat) 8 = _
  have : (BinOp.mul.apply .W64 (d.regs.get64 .rcx) (BitVec.ofNat 64 8)).toNat = 8 * j := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_mul, hc]
    rw [toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)]
    omega
  rw [this]
  exact load_ofMachine rfl h

/-- Placement words of the frame kept where memory changed only in a range apart from them. -/
theorem placementAt_keep {m0 : MachineData} {d d' : DataMem} {a n o : Nat} {p : Placement}
    (hst : StackOk m0 busLayoutStack) (ho : o + 16 ≤ 1808)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off (fb m0) a) n))
    (hd : o + 16 ≤ a ∨ a + n ≤ o) (han : a + n ≤ 1808)
    (h : PlacementAt d (off (fb m0) o) p) : PlacementAt d' (off (fb m0) o) p :=
  ⟨h.1, h.2.1, frameWord_keep hst (by omega) hs (by omega) han h.2.2.1, by
    rw [off_off]
    exact frameWord_keep hst (by omega) hs (by omega) han (by rw [← off_off]; exact h.2.2.2)⟩

theorem part_keep {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d d' : DataMem} {i a n : Nat} (hst : StackOk m0 busLayoutStack)
    (hnf : nf m0 ≤ 3) (hbl : bl.length ≤ 51) (hi : i ≤ nf m0 + bl.length)
    (h : Part d L bl m0 i)
    (hs : NativeRustcVm.SameOutside d d' (NativeRustcVm.InRange (off (fb m0) a) n))
    (hd : 80 + 16 * (i - nf m0) ≤ a ∨ (min i (nf m0) = i ∧ 24 + 16 * i ≤ a ∧ a + n ≤ 72))
    (han : a + n ≤ 1808) : Part d' L bl m0 i where
  depth := frameWord_keep hst (by omega) hs (by omega) han h.depth
  tlen := frameWord_keep hst (by omega) hs (by omega) han h.tlen
  fw j hj := placementAt_keep hst (by omega) hs (by
    have : j < min i (nf m0) := hj
    have : min i (nf m0) ≤ nf m0 := Nat.min_le_right _ _
    rcases hd with hd | ⟨h1, h2, h3⟩ <;> omega) han (h.fw j hj)
  tb j hj := placementAt_keep hst (by omega) hs (by
    rcases hd with hd | ⟨h1, h2, h3⟩
    · omega
    · have : i ≤ nf m0 := by rw [← h1]; exact Nat.min_le_right _ _
      omega) han (h.tb j hj)

theorem Part.push_fw {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d : DataMem} {j : Nat} (h : Part d L bl m0 j) (hj : j < nf m0)
    (hp : PlacementAt d (off (fb m0) (24 + 16 * j)) (P L bl m0 j)) : Part d L bl m0 (j + 1) where
  depth := h.depth
  tlen := by rw [show j + 1 - nf m0 = j - nf m0 by omega]; exact h.tlen
  fw j' hj' := by
    rcases Nat.lt_or_ge j' j with h' | h'
    · exact h.fw j' (by omega)
    · obtain rfl : j' = j := by omega
      exact hp
  tb j' hj' := absurd hj' (by omega)

theorem Part.push_tb {L : LayoutW} {bl : List NativeRustcVm.Data.Block} {m0 : MachineData}
    {d d' : DataMem} {j : Nat} (h : Part d L bl m0 j) (hj : nf m0 ≤ j)
    (hdepth : NativeRustcVm.WordAt d' (off (fb m0) 8) (O L bl m0).2.toUInt64)
    (htlen : NativeRustcVm.WordAt d' (off (fb m0) 72) (j + 1 - nf m0).toUInt64)
    (hfw : ∀ j' < min j (nf m0), PlacementAt d (off (fb m0) (24 + 16 * j')) (P L bl m0 j') →
      PlacementAt d' (off (fb m0) (24 + 16 * j')) (P L bl m0 j'))
    (htb : ∀ j' < j - nf m0, PlacementAt d (off (fb m0) (80 + 16 * j')) (P L bl m0 (nf m0 + j')) →
      PlacementAt d' (off (fb m0) (80 + 16 * j')) (P L bl m0 (nf m0 + j')))
    (hp : PlacementAt d' (off (fb m0) (80 + 16 * (j - nf m0))) (P L bl m0 j)) :
    Part d' L bl m0 (j + 1) where
  depth := hdepth
  tlen := htlen
  fw j' hj' := hfw j' (by omega) (h.fw j' (by omega))
  tb j' hj' := by
    rcases Nat.lt_or_ge j' (j - nf m0) with h' | h'
    · exact htb j' h' (h.tb j' h')
    · obtain rfl : j' = j - nf m0 := by omega
      rw [show nf m0 + (j - nf m0) = j by omega]
      exact hp

theorem toNat_ofNat_lt' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n :=
  toNat_ofNat_lt h

/-- The frame's region at offset `o`, `n` bytes, below the slots. -/
theorem frame_region {m0 d : MachineData} (hst : StackOk m0 busLayoutStack)
    (hk : Kept m0.dmem d.dmem) {o n : Nat} (hon : o + n ≤ 1808) :
    NativeRustcVm.Mapped d.dmem (off (fb m0) o) n ∧ NativeRustcVm.NoWrap (off (fb m0) o) n := by
  have hN : 1808 ≤ busLayoutStack := by decide
  have hrsp := hst.1
  have htop := hst.2.1
  have hb : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hoff : (off (fb m0) o).toNat = (fb m0).toNat + o := toNat_off (by omega)
  exact ⟨fun t ht ↦ by rw [off_add]; exact hk _ (frame_mapped hst hN (o + t) (by omega)),
    by unfold NativeRustcVm.NoWrap; rw [hoff]; omega⟩

variable [Host] {k : Nat}

/-- **A turn of the placements' loop.** -/
theorem place_step (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b26Offset)) (hI : PInv L bl m0 j st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b33Offset) ∧ PEnd L bl m0 st'.data)
      ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b26Offset) ∧ PInv L bl m0 (j + 1) st'.data)) st := by
  have hst := hpre.1
  have hN : 1808 ≤ busLayoutStack := by decide
  have hn54 := pre_n hpre
  have hnf3 : nf m0 ≤ 3 := hpre.2.1
  have hmb : bl.length ≤ 51 := hpre.2.2.2.2.2.1
  have hrsp := hst.1
  have htop := hst.2.1
  have hbase : (fb m0).toNat = (rspOf m0).toNat - 1808 := stackBelow_toNat (by omega)
  have hjl := hI.lt
  have hbd := hI.bd
  have hrv : ∀ (st' st'' : MachineData), (∀ r, calleeSaved r = true →
      slots.any (·.2 == r) = false → reg st'' r = reg st' r) := fun _ _ r h h' ↦ regs_vac r h h'
  -- `b26`: size `j`, offset `j`.
  have hwf0 := wf0 (d := st.data) hst hN hbd.fr.kept (vars := fun _ ↦ 0) (ret := 0)
  have hax0 : reg st.data .rax = (Sym.ptr 0 24).eval
      (frameEnv m0 st.data 1808 [] (fun _ ↦ 0) 0) := hI.rax.trans (eval_ptr0 24).symm
  refine exec_at (infix_of b26_in_code (by simp [b26]) hp) run_b26 hwf0 nofun hpc
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hbd.fr.rsp_eval, hax0, trivial⟩ trivial
      ⟨by show (reg st.data .rcx).toNat < 54; rw [hI.rcx, toNat_ofNat_lt (by omega)]; omega,
        trivial⟩ trivial)
    fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hdi1, hsi1, hk1, hax1⟩ := after_eq run_b26 ▸ ok_b26
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf0 hmem1
  have bd1 : Body m0 1808 busLayoutStack slots 8 st1.data :=
    ⟨Frame.of_block hbd.fr hwf0 hm1 hmid1 slots_le, by rw [hd1]; exact hbd.same⟩
  have hcx : reg st.data .rcx = BitVec.ofNat 64 j := hI.rcx
  have hsz : reg st1.data .rdi = ((S L bl m0).getD j 0).toUInt64.toBitVec := by
    rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ hdi1]
    exact load_idx (hI.sizes j hjl) hcx (by omega)
  have hof : reg st1.data .rsi = ((O L bl m0).1.getD j 0).toUInt64.toBitVec := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hsi1]
    exact load_idx (hI.offs j hjl) hcx (by omega)
  have K1 : ∀ r ∈ [Reg64.rcx, .rdx, .rbx, .r14, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ hk1.reg' hm1 hr
  have e1ax : reg st1.data .rax = off (fb m0) 24 :=
    (hm1.regs .rax _ hax1).trans (eval_ptr0 24)
  simp only [PcOk] at hpc1
  change st1.pc = if (SBool.cmp .ult .W64 (.reg .rcx) (.reg .r14)).not.eval
    (Env.ofMachine st.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = true then _
    else _ at hpc1
  have hc1 : (SBool.cmp .ult .W64 (.reg .rcx) (.reg .r14)).not.eval
      (Env.ofMachine st.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) =
      decide (nf m0 ≤ j) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
    rw [ult_of_toNat (show (st.data.regs.get64 .rcx).toNat = j by
      rw [show st.data.regs.get64 .rcx = _ from hcx]; exact toNat_ofNat_lt (by omega))
      (show (st.data.regs.get64 .r14).toNat = nf m0 by
        rw [show st.data.regs.get64 .r14 = _ from hI.r14])]
    by_cases h : nf m0 ≤ j
    · simp [h]
    · simp [h]; omega
  rw [hc1] at hpc1
  -- From `NativeRustcVmX64.Vm.BusLayout.label_18` on: the count, back at the head or out.
  have tail : ∀ st5 : MachineState, st5.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b25Offset) →
      Body m0 1808 busLayoutStack slots 8 st5.data →
      reg st5.data .rbx = reg m0 .rdi → reg st5.data .r14 = reg m0 .rdx →
      (reg st5.data .r15).toNat = nf m0 + bl.length → reg st5.data .rax = off (fb m0) 24 →
      reg st5.data .rcx = BitVec.ofNat 64 j →
      reg st5.data .rdx = BitVec.ofNat 64 (min (j + 1) (nf m0)) →
      SizesAt st5.data.dmem L bl m0 (nf m0 + bl.length) → OffsAt st5.data.dmem L bl m0 →
      Part st5.data.dmem L bl m0 (j + 1) →
      Eventually (step1 Host.exe) (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b33Offset) ∧
        PEnd L bl m0 st'.data) ∨ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b26Offset) ∧
          PInv L bl m0 (j + 1) st'.data)) st5 := by
    intro st5 hpc5 bd5 h5bx h5_14 h5_15 h5ax h5cx h5dx hsz5 hof5 hpt5
    have hwf5 := wf0 (d := st5.data) hst hN bd5.fr.kept (vars := fun _ ↦ 0) (ret := 0)
    have hax5 : reg st5.data .rax = (Sym.ptr 0 24).eval
        (frameEnv m0 st5.data 1808 [] (fun _ ↦ 0) 0) := h5ax.trans (eval_ptr0 24).symm
    refine exec_at (infix_of b25_in_code (by simp [b25]) hp) run_b25 hwf5 nofun hpc5
      (match_ofMachine ⟨rfl, trivial⟩ ⟨bd5.fr.rsp_eval, hax5, trivial⟩ trivial
        ⟨by show (reg st5.data .rcx).toNat < 54; rw [h5cx, toNat_ofNat_lt (by omega)]; omega,
          trivial⟩ trivial)
      fun st6 hm6 hpc6 ↦ ?_
    obtain ⟨hmid6, hmem6, hcx6, hk6, hax6⟩ := after_eq run_b25 ▸ ok_b25
    have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwf5 hmem6
    have bd6 : Body m0 1808 busLayoutStack slots 8 st6.data :=
      ⟨Frame.of_block bd5.fr hwf5 hm6 hmid6 slots_le, by rw [hd6]; exact bd5.same⟩
    have e6cx : reg st6.data .rcx = BitVec.ofNat 64 (j + 1) := by
      rw [show reg st6.data .rcx = _ from hm6.regs .rcx _ hcx6]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st5.data.regs.get64 .rcx = _ from h5cx, ← BitVec.ofNat_add]
    simp only [PcOk] at hpc6
    change st6.pc = if (SBool.cmp .eq .W64 (.reg .r15) (.bin .add .W64 (.reg .rcx) (.lit 1))).eval
      (Env.ofMachine st5.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = true then _
      else _ at hpc6
    have hc6 : (SBool.cmp .eq .W64 (.reg .r15) (.bin .add .W64 (.reg .rcx) (.lit 1))).eval
        (Env.ofMachine st5.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) =
        decide (nf m0 + bl.length = j + 1) := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64,
        Env.ofMachine_regs]
      rw [show st5.data.regs.get64 .rcx = _ from h5cx, ← BitVec.ofNat_add]
      exact beq_of_toNat h5_15 (toNat_ofNat_lt (by omega))
    rw [hc6] at hpc6
    have K6 : ∀ r ∈ [Reg64.rdx, .rbx, .r14, .r15], reg st6.data r = reg st5.data r :=
      fun r hr ↦ hk6.reg' hm6 hr
    by_cases hend : nf m0 + bl.length = j + 1
    · rw [decide_eq_true hend] at hpc6
      simp only [↓reduceIte] at hpc6
      refine .done _ (Or.inl ⟨hpc6.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_26_at), bd6,
        (K6 .rbx (by simp)).trans h5bx, (K6 .rdx (by simp)).trans (h5dx.trans (by
          rw [Nat.min_eq_right (by omega)])), ?_⟩)
      rw [hd6, hend]; exact hpt5
    · rw [decide_eq_false hend] at hpc6
      simp only [Bool.false_eq_true, ↓reduceIte] at hpc6
      refine .done _ (Or.inr ⟨hpc6.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b25_next)), bd6, (K6 .rbx (by simp)).trans h5bx,
        (K6 .r14 (by simp)).trans h5_14, by rw [K6 .r15 (by simp)]; exact h5_15,
        (hm6.regs .rax _ hax6).trans (eval_ptr0 24), e6cx, (K6 .rdx (by simp)).trans h5dx,
        by omega, by rw [hd6]; exact hsz5, by rw [hd6]; exact hof5, by rw [hd6]; exact hpt5⟩)
  have e1cx : reg st1.data .rcx = BitVec.ofNat 64 j := (K1 .rcx (by simp)).trans hcx
  by_cases hfw : nf m0 ≤ j
  · -- A table's placement: `b30`, `b31`.
    rw [decide_eq_true hfw] at hpc1
    simp only [↓reduceIte] at hpc1
    set t := j - nf m0 with ht
    have htl : t < bl.length := by omega
    have hwf1 := wf0 (d := st1.data) hst hN bd1.fr.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_at (infix_of b30_in_code (by simp [b30]) hp) run_b30 hwf1 nofun
      (hpc1.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_22_at))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨bd1.fr.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨hmid2, hmem2, h8_2, hk2⟩ := after_eq run_b30 ▸ ok_b30
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
    have bd2 : Body m0 1808 busLayoutStack slots 8 st2.data :=
      ⟨Frame.of_block bd1.fr hwf1 hm2 hmid2 slots_le, by rw [hd2]; exact bd1.same⟩
    have e2_8 : reg st2.data .r8 = (t.toUInt64).toBitVec := by
      rw [show reg st2.data .r8 = _ from hm2.regs .r8 _ h8_2]
      exact load_ofMachine rfl (by rw [hd1]; exact hI.part.tlen)
    simp only [PcOk] at hpc2
    change st2.pc = if (SBool.cmp .ult .W64 (.load 0 72 8) (.lit 51)).not.eval
      (Env.ofMachine st1.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = true then _
      else _ at hpc2
    have hc2 : (SBool.cmp .ult .W64 (.load 0 72 8) (.lit 51)).not.eval
        (Env.ofMachine st1.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = false := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64]
      rw [ult_of_toNat (show ((Env.ofMachine st1.data [(stackBelow m0 1808, 1808 + 8)]
        (fun _ ↦ 0) 0).load 0 72 8).toNat = t by
          show ((Sym.load 0 72 8).eval (frameEnv m0 st1.data 1808 [] (fun _ ↦ 0) 0)).toNat = t
          rw [← hm2.regs .r8 _ h8_2, show st2.data.regs.get64 .r8 = _ from e2_8]
          exact toNat_toUInt64' (by omega))
        (toNat_ofNat_lt (by decide))]
      simp only [decide_eq_true (show t < 51 by omega), Bool.not_true]
    rw [hc2] at hpc2
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
    -- `b31`, first part: the placement written.
    have hreg := frame_region hst bd2.fr.kept (o := 24 + 16 * t) (n := 72) (by omega)
    have hwf3 : (Env.ofMachine st2.data [(off (fb m0) (24 + 16 * t), 72)] (fun _ ↦ 0) 0).WF :=
      Env.wf_of ⟨hreg, trivial⟩ (List.pairwise_singleton _ _)
    have K2 : ∀ r ∈ [Reg64.rax, .rcx, .rdx, .rdi, .rsi, .rbx, .r14, .r15],
        reg st2.data r = reg st1.data r := fun r hr ↦ hk2.reg' hm2 hr
    have e2ax : reg st2.data .rax = off (fb m0) 24 := by
      rw [hk2.reg' hm2 (by simp)]; exact e1ax
    have hkeyT : keyT.eval (Env.ofMachine st2.data [(off (fb m0) (24 + 16 * t), 72)]
        (fun _ ↦ 0) 0) = (Env.ofMachine st2.data [(off (fb m0) (24 + 16 * t), 72)]
        (fun _ ↦ 0) 0).base 0 + BitVec.ofInt 64 ((0 : Nat) : Int) := by
      rw [Env.base_ofMachine _ _ _ _ rfl]
      simp only [keyT, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .rax = _ from e2ax, show st2.data.regs.get64 .r8 = _ from e2_8,
        Nat.cast_zero, ofInt_zero64, BitVec.add_zero, off, off]
      have hsc : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := by decide
      rw [hsc, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, toNat_toUInt64' (by omega),
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    refine exec_at (infix_of ((infix_take b31 4).trans b31_in_code (by simp [b31])) (by simp [b31])
      hp) run_b31a hwf3 nofun (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b30_next)))
      (match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨hkeyT, trivial⟩)
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hw3, hwr3, hk3⟩ := after_eq run_b31a ▸ ok_b31a
    have hs3 := sameOutside_sub hwf3 hm3 (r := 0) rfl (show 72 ≤ 72 by omega) (lo := 56) hw3
    rw [off_off, show 72 - 56 = 16 by rfl] at hs3
    have bd3 := Body.of_sub hst hN bd2 (a := 24 + 16 * t + 56) (n := 16) (by omega)
      (fun p hp ↦ by have := slots_lo p hp; omega) slots_le hs3 (hk3.reg' hm3 (by simp))
      (hm3.kept hwf3) (hrv _ _)
    have hpt3 : PlacementAt st3.data.dmem (off (fb m0) (80 + 16 * t)) (P L bl m0 j) := by
      refine ⟨(pre_P_ok hpre j).1, (pre_P_ok hpre j).2, ?_, ?_⟩
      · have := wordAt_write_eq hm3 (b := off (fb m0) (24 + 16 * t)) (o := 56) rfl (by omega)
          (.reg .rdi) (hwr3.find (by simp)) ((K2 .rdi (by simp)).trans hsz)
        rwa [off_off, show 24 + 16 * t + 56 = 80 + 16 * t by omega] at this
      · have := wordAt_write_eq hm3 (b := off (fb m0) (24 + 16 * t)) (o := 64) rfl (by omega)
          (.reg .rsi) (hwr3.find (by simp)) ((K2 .rsi (by simp)).trans hof)
        rw [off_off] at this
        rw [off_off, show 80 + 16 * t + 8 = 24 + 16 * t + 64 by omega]
        exact this
    -- `b31`, second part: the count.
    have hwf4 := wf0 (d := st3.data) hst hN bd3.fr.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_at (infix_of ((infix_drop b31 4).trans b31_in_code (by simp [b31])) (by simp [b31])
      hp) run_b31b hwf4 nofun (hpc3.trans (congrArg Host.addrOf (by
        have : (b31.take 4).length = 4 := rfl; omega)))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨bd3.fr.rsp_eval, trivial⟩ trivial trivial trivial)
      fun st4 hm4 hpc4 ↦ ?_
    obtain ⟨hmid4, hw4, hwr4, hbd4, hk4⟩ := after_eq run_b31b ▸ ok_b31b
    have bd4 := Body.of_block hst hN bd3 hwf4 hm4 hmid4 hw4 slots_le
    have hs4 := sameOutside_sub hwf4 hm4 (r := 0) rfl (show 80 ≤ 1808 + 8 by omega) (lo := 72)
      fun w hw ↦ ⟨hw4 w hw, hbd4 w hw⟩
    rw [show 80 - 72 = 8 by rfl] at hs4
    have K4 : ∀ r ∈ [Reg64.rcx, .rdx, .rbx, .r14, .r15], reg st4.data r = reg st.data r := by
      intro r hr
      have h4 : reg st4.data r = reg st3.data r := hk4.reg' hm4 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h <;> simp [h])
      have h3 : reg st3.data r = reg st2.data r := hk3.reg' hm3 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h <;> simp [h])
      have h2 : reg st2.data r = reg st1.data r := K2 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h | h <;> simp [h])
      exact h4.trans (h3.trans (h2.trans (K1 r hr)))
    have hpart := hI.part
    have hpart3 := part_keep hst hnf3 hmb (by omega) (show Part st2.data.dmem L bl m0 j by
      rw [hd2, hd1]; exact hpart) hs3 (.inl (by omega)) (by omega)
    simp only [PcOk] at hpc4
    refine tail st4 (hpc4.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_18_at)) bd4 ((K4 .rbx (by simp)).trans hI.rbx)
      ((K4 .r14 (by simp)).trans hI.r14) (by rw [K4 .r15 (by simp)]; exact hI.r15)
      ((hk4.reg' hm4 (by simp)).trans ((hk3.reg' hm3 (by simp)).trans e2ax))
      ((K4 .rcx (by simp)).trans hcx)
      ((K4 .rdx (by simp)).trans (hI.rdx.trans (by rw [Nat.min_eq_right hfw,
        Nat.min_eq_right (by omega)])))
      (sizes_keep' hst (sizes_keep' hst (show SizesAt st2.data.dmem L bl m0 _ by
        rw [hd2, hd1]; exact hI.sizes) hn54 (.inl (by omega)) (by omega) hs3) hn54
        (.inl (by omega)) (by omega) hs4)
      (offs_keep hst hn54 (offs_keep hst hn54 (show OffsAt st2.data.dmem L bl m0 by
        rw [hd2, hd1]; exact hI.offs) (by omega) (by omega) hs3) (by omega) (by omega) hs4) ?_
    refine hpart3.push_tb hfw (frameWord_keep hst (by omega) hs4 (by omega) (by omega)
      hpart3.depth) ?_ (fun j' hj' h ↦ placementAt_keep hst (by omega) hs4
        (by have : j' < nf m0 := lt_of_lt_of_le hj' (Nat.min_le_right _ _); omega) (by omega) h)
      (fun j' hj' h ↦ placementAt_keep hst (by omega) hs4 (by omega) (by omega) h)
      (placementAt_keep hst (by omega) hs4 (by omega) (by omega) hpt3)
    refine wordAt_write_eq hm4 (b := fb m0) (o := 72) rfl (by omega)
      (.bin .add .W64 (.reg .r8) (.lit 1)) (hwr4.find (by simp)) ?_
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st3.data.regs.get64 .r8 = _ from (hk3.reg' hm3 (by simp)).trans e2_8]
    apply BitVec.eq_of_toNat_eq
    have h64 : (2 : Nat) ^ Width.W64.bits = 2 ^ 64 := rfl
    rw [BitVec.toNat_add, toNat_toUInt64' (by omega), toNat_toUInt64' (by omega),
      BitVec.toNat_ofNat, h64]
    omega
  · -- A framework placement: `b27`, `b28`.
    rw [decide_eq_false hfw] at hpc1
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc1
    have hwf1 := wf0 (d := st1.data) hst hN bd1.fr.kept (vars := fun _ ↦ 0) (ret := 0)
    have hax1' : reg st1.data .rax = (Sym.ptr 0 24).eval
        (frameEnv m0 st1.data 1808 [] (fun _ ↦ 0) 0) := e1ax.trans (eval_ptr0 24).symm
    refine exec_at (infix_of b27_in_code (by simp [b27]) hp) run_b27 hwf1 nofun
      (hpc1.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b26_next)))
      (match_ofMachine ⟨rfl, trivial⟩ ⟨bd1.fr.rsp_eval, hax1', trivial⟩ trivial
        ⟨by show (reg st1.data .rcx).toNat < 54; rw [e1cx, toNat_ofNat_lt (by omega)]; omega,
          trivial⟩ trivial)
      fun st2 hm2 hpc2 ↦ ?_
    obtain ⟨hmid2, hmem2, hk2, hax2⟩ := after_eq run_b27 ▸ ok_b27
    have hd2 : st2.data.dmem = st1.data.dmem := hm2.dmem_eq hwf1 hmem2
    have bd2 : Body m0 1808 busLayoutStack slots 8 st2.data :=
      ⟨Frame.of_block bd1.fr hwf1 hm2 hmid2 slots_le, by rw [hd2]; exact bd1.same⟩
    have e1dx : reg st1.data .rdx = BitVec.ofNat 64 j := by
      rw [K1 .rdx (by simp), hI.rdx, Nat.min_eq_left (by omega)]
    simp only [PcOk] at hpc2
    change st2.pc = if (SBool.cmp .ult .W64 (.reg .rdx) (.lit 3)).not.eval
      (Env.ofMachine st1.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = true then _
      else _ at hpc2
    have hc2 : (SBool.cmp .ult .W64 (.reg .rdx) (.lit 3)).not.eval
        (Env.ofMachine st1.data [(stackBelow m0 1808, 1808 + 8)] (fun _ ↦ 0) 0) = false := by
      simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, Env.ofMachine_regs]
      rw [ult_of_toNat (show (st1.data.regs.get64 .rdx).toNat = j by
        rw [show st1.data.regs.get64 .rdx = _ from e1dx]; exact toNat_ofNat_lt (by omega))
        (toNat_ofNat_lt (by decide))]
      simp only [decide_eq_true (show j < 3 by omega), Bool.not_true]
    rw [hc2] at hpc2
    simp only [Bool.false_eq_true, ↓reduceIte] at hpc2
    -- `b28`: the placement written.
    have hreg := frame_region hst bd2.fr.kept (o := 24 + 16 * j) (n := 16) (by omega)
    have hwf3 : (Env.ofMachine st2.data [(off (fb m0) (24 + 16 * j), 16)] (fun _ ↦ 0) 0).WF :=
      Env.wf_of ⟨hreg, trivial⟩ (List.pairwise_singleton _ _)
    have K2 : ∀ r ∈ [Reg64.rcx, .rdx, .rdi, .rsi, .rbx, .r14, .r15],
        reg st2.data r = reg st1.data r := fun r hr ↦ hk2.reg' hm2 hr
    have e2ax : reg st2.data .rax = off (fb m0) 24 := (hm2.regs .rax _ hax2).trans (eval_ptr0 24)
    have hkeyF : keyF.eval (Env.ofMachine st2.data [(off (fb m0) (24 + 16 * j), 16)]
        (fun _ ↦ 0) 0) = (Env.ofMachine st2.data [(off (fb m0) (24 + 16 * j), 16)]
        (fun _ ↦ 0) 0).base 0 + BitVec.ofInt 64 ((0 : Nat) : Int) := by
      rw [Env.base_ofMachine _ _ _ _ rfl]
      simp only [keyF, Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st2.data.regs.get64 .rax = _ from e2ax,
        show st2.data.regs.get64 .rdx = _ from (K2 .rdx (by simp)).trans e1dx,
        Nat.cast_zero, ofInt_zero64, BitVec.add_zero, off, off]
      have hsc : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := by decide
      rw [hsc, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, toNat_ofNat_lt (by omega),
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega
    refine exec_at (infix_of b28_in_code (by simp [b28]) hp) run_b28 hwf3 nofun
      (hpc2.trans (congrArg Host.addrOf (by rw [Nat.add_assoc]; exact congrArg (k + ·) NativeRustcVmX64.Vm.BusLayout.b27_next)))
      (match_ofMachine ⟨rfl, trivial⟩ trivial trivial trivial ⟨hkeyF, trivial⟩)
      fun st3 hm3 hpc3 ↦ ?_
    obtain ⟨hw3, hwr3, hk3, hdx3⟩ := after_eq run_b28 ▸ ok_b28
    have hs3 := sameOutside_sub hwf3 hm3 (r := 0) rfl (show 16 ≤ 16 by omega) (lo := 0)
      fun w hw ↦ ⟨(hw3 w hw).1, Nat.zero_le _, (hw3 w hw).2⟩
    rw [off_zero, show 16 - 0 = 16 by rfl] at hs3
    have bd3 := Body.of_sub hst hN bd2 (a := 24 + 16 * j) (n := 16) (by omega)
      (fun p hp ↦ by have := slots_lo p hp; omega) slots_le hs3 (hk3.reg' hm3 (by simp))
      (hm3.kept hwf3) (hrv _ _)
    have hpt3 : PlacementAt st3.data.dmem (off (fb m0) (24 + 16 * j)) (P L bl m0 j) := by
      refine ⟨(pre_P_ok hpre j).1, (pre_P_ok hpre j).2, ?_, ?_⟩
      · have := wordAt_write_eq hm3 (b := off (fb m0) (24 + 16 * j)) (o := 0) rfl (by omega)
          (.reg .rdi) (hwr3.find (by simp)) ((K2 .rdi (by simp)).trans hsz)
        rwa [off_zero] at this
      · exact wordAt_write_eq hm3 (b := off (fb m0) (24 + 16 * j)) (o := 8) rfl (by omega)
          (.reg .rsi) (hwr3.find (by simp)) ((K2 .rsi (by simp)).trans hof)
    have K3 : ∀ r ∈ [Reg64.rcx, .rbx, .r14, .r15], reg st3.data r = reg st.data r := by
      intro r hr
      have h3 : reg st3.data r = reg st2.data r := hk3.reg' hm3 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h <;> simp [h])
      have h2 : reg st2.data r = reg st1.data r := K2 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h <;> simp [h])
      exact h3.trans (h2.trans (K1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with h | h | h | h <;> simp [h])))
    simp only [PcOk] at hpc3
    refine tail st3 (hpc3.trans (hp.label NativeRustcVmX64.Vm.BusLayout.label_18_at)) bd3 ((K3 .rbx (by simp)).trans hI.rbx)
      ((K3 .r14 (by simp)).trans hI.r14) (by rw [K3 .r15 (by simp)]; exact hI.r15)
      ((hk3.reg' hm3 (by simp)).trans e2ax) ((K3 .rcx (by simp)).trans hcx) ?_
      (sizes_keep' hst (show SizesAt st2.data.dmem L bl m0 _ by rw [hd2, hd1]; exact hI.sizes)
        hn54 (.inl (by omega)) (by omega) hs3)
      (offs_keep hst hn54 (show OffsAt st2.data.dmem L bl m0 by rw [hd2, hd1]; exact hI.offs)
        (by omega) (by omega) hs3)
      ((part_keep hst hnf3 hmb (by omega) (show Part st2.data.dmem L bl m0 j by
        rw [hd2, hd1]; exact hI.part) hs3 (.inr ⟨Nat.min_eq_left (by omega), by omega, by omega⟩)
        (by omega)).push_fw (by omega) hpt3)
    rw [show reg st3.data .rdx = _ from hm3.regs .rdx _ hdx3]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [show st2.data.regs.get64 .rdx = _ from (K2 .rdx (by simp)).trans e1dx, ← BitVec.ofNat_add,
      Nat.min_eq_left (by omega)]

/-- **The placements**: from the loop head, every placement pushed. -/
theorem place_run (hp : Placed code k) {L : LayoutW} {bl : List NativeRustcVm.Data.Block}
    {m0 : MachineData} (hpre : BusLayoutPre L bl m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b26Offset)) (hI : PInv L bl m0 0 st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b33Offset) ∧
      PEnd L bl m0 st'.data) st :=
  Sym.loop (fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.BusLayout.b26Offset) ∧ ∃ j, nf m0 + bl.length - j = n ∧
    PInv L bl m0 j st.data) (fun n st ⟨hpc, j, hn, hI⟩ ↦ Eventually.mono
      (place_step hp hpre hpc hI) fun st' h ↦ by
        rcases h with h | ⟨hpc', hI'⟩
        · exact Or.inl h
        · exact Or.inr ⟨nf m0 + bl.length - (j + 1), by have := hI.lt; omega, hpc', j + 1, rfl,
            hI'⟩)
    ⟨hpc, 0, rfl, hI⟩

end

end NativeRustcVmX64.Bus.BusLayout
