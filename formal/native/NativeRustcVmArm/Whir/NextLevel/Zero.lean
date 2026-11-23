module

public import NativeRustcVmArm.Whir.NextLevel.Queries

/-!
# `next_level`: the zeroing loop

`.LNextLevel_9` (`b17`) zeroes the frame's 64 bytes at `4368 + 64 i` (X10 + X9, X9 = `64 i`)
for `i < 57` (`zero_step`, `zero_loop`): to `b18` with `H17 … 57`. Nothing it writes is read
again.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

public section

theorem facts_keep [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
    {rounds : Array FoldRoundW} {m0 : MachineData} (h : NextLevelPre a s level w rounds m0)
    {d d' : Mem 64} {o' n' : Nat} (ho' : o' + n' ≤ 8192)
    (hs : SameOutside d d' (InRange (loc m0 o') n')) {l : List (Nat × List UInt8)} {lo n : Nat}
    (hl : Within l lo n) (hn : lo + n ≤ 8192) (hd : lo + n ≤ o' ∨ o' + n' ≤ lo)
    (hf : Facts m0 d l) : Facts m0 d' l := fun p hp ↦ by
  have g := geo h
  have := hl p hp
  refine NativeRustcVm.BytesAt.of_sameOutside (hf p hp) hs fun i hi hq ↦ ?_
  rw [NativeRustcVm.addr_add_add] at hq
  have h1 := loc_nat h ho' hq
  have h2 := loc_toNat (m0 := m0) (o := p.1 + i) (hN8 h) (by omega)
  rw [h2] at h1
  omega

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat} {xs ood : Array EW} {v lam : EW}
  {qs : Array UInt64} {s8 : TState}

/-- **A turn of the zeroing loop.** -/
theorem zero_step (hp : Placed code k) (h : NextLevelPre a s level w rounds m0) {i : Nat}
    (hi : i < 57) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b17Offset))
    (hI : H17 a level m0 xs ood v lam qs s8 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b17Offset) ∧ i + 1 < 57 ∧
        H17 a level m0 xs ood v lam qs s8 (i + 1) st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b18Offset) ∧ H17 a level m0 xs ood v lam qs s8 57 st'.data)) st := by
  have g := geo h
  have hf := hI.fr
  have hmu30 : m0.regs.X5.toNat ≤ 30 := h.2.2.2.2.2.2.2.2.2.2.1
  have hf6 : level.fold ≤ 6 := h.2.2.2.2.2.1
  set o := 4368 + 64 * i with ho
  have hl := loc_toNat (m0 := m0) (o := o) (hN8 h) (by omega)
  have hnw : NoWrap (loc m0 o) 64 := by
    show _ ≤ _; rw [hl]; have := g.hsp; omega
  have hmap : Mapped st.data.dmem (loc m0 o) 64 := fun j hj ↦ by
    have := frMapped h hf (o + j) (by omega)
    rwa [NativeRustcVm.addr_add_add]
  have hwf : (Env.ofMachine st.data [(loc m0 o, 64)]).WF :=
    Env.wf_of ⟨⟨hmap, hnw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hx9b : st.data.regs.X9.toBitVec = BitVec.ofNat 64 (64 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [UInt64.toNat_toBitVec, hI.x9, BitVec.toNat_ofNat]
    omega
  have hx910 : (st.data.regs.getXReg .X10).toBitVec + (st.data.regs.getXReg .X9).toBitVec =
      loc m0 o := by
    show st.data.regs.X10.toBitVec + st.data.regs.X9.toBitVec = _
    rw [hI.x10, hx9b, NativeRustcVm.addr_add_add]
  have hm : Match (Env.ofMachine st.data [(loc m0 o, 64)]) zeroS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs,
          Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
        rw [hx910, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  refine exec_at (inf hp b17_in_code (by simp [b17])) run_b17 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hso : SameOutside st.data.dmem st'.data.dmem (InRange (loc m0 o) 64) := fun q hq ↦
    hm'.sameOutside hwf q fun hw ↦ hq (Sumcheck.Written.inRange (r := 0) rfl hnw (by decide) hw)
  have hfr : NFr m0 st'.data := by
    refine hf.step (W := InRange (loc m0 o) 64) (Match.sp_eq hm hm' rfl) (fun _ h ↦ by cases h)
      (hm'.kept hwf) hso (fun q hq ↦ .inl ?_) fun p hp j hj hq ↦ ?_
    · have := loc_nat h (by omega) hq
      rw [Sym.inRange_iff (base_noWrap (by rw [stack_eq]; exact g.hN)),
        base_toNat (by rw [stack_eq]; exact g.hN), stack_eq]
      omega
    · have := loc_nat h (by omega) hq
      have hsl := slots_le p hp
      have e : (base m0 8192 + BitVec.ofNat 64 p.1 + BitVec.ofNat 64 j).toNat =
          m0.regs.SP.toNat - 8192 + (p.1 + j) := by
        rw [NativeRustcVm.addr_add_add]; exact loc_toNat (hN8 h) (by omega)
      rw [e] at this
      omega
  have kr : ∀ r ∈ [XReg.X8, .X10, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26],
      st'.data.regs.getXReg r = st.data.regs.getXReg r :=
    sameRegs_ok hm hm' (by decide)
  have x9 : (st'.data.regs.getXReg .X9).toBitVec =
      (st.data.regs.getXReg .X9).toBitVec + BitVec.ofNat 64 64 := by
    rw [reg_val hm' (r := .X9) rfl, ev_add]
  have x9n : st'.data.regs.X9.toNat = 64 * (i + 1) := by
    rw [← UInt64.toNat_toBitVec]
    show (st'.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [x9, BitVec.toNat_add]
    show (st.data.regs.X9.toBitVec.toNat + _) % _ = _
    rw [UInt64.toNat_toBitVec, hI.x9]
    simp only [BitVec.toNat_ofNat]
    omega
  have hW := within17 (m0 := m0) (xs := xs) (ood := ood) (v := v) (lam := lam)
    (by rw [hI.size]; exact hf6) (by rw [hI.osize]; exact hmu30)
  have hI' : ∀ j, j ≤ 57 → st'.data.regs.X9.toNat = 64 * j →
      H17 a level m0 xs ood v lam qs s8 j st'.data := fun j hj e ↦
    ⟨hfr, (kr .X19 (by simp)).trans hI.x19, (kr .X20 (by simp)).trans hI.x20,
      (kr .X21 (by simp)).trans hI.x21, (kr .X22 (by simp)).trans hI.x22,
      by rw [show st'.data.regs.X23 = st.data.regs.X23 from kr .X23 (by simp)]; exact hI.x23,
      by rw [show st'.data.regs.X24 = st.data.regs.X24 from kr .X24 (by simp)]; exact hI.x24,
      (kr .X25 (by simp)).trans hI.x25, (kr .X26 (by simp)).trans hI.x26,
      (kr .X8 (by simp)).trans hI.x8, e,
      by rw [show st'.data.regs.X10 = st.data.regs.X10 from kr .X10 (by simp)]; exact hI.x10,
      facts_keep h (by omega) hso hW (by decide) (by omega) hI.facts, hI.size, hI.osize,
      qbuf_keep h hso (fun q hq ↦ by
        have := loc_nat h (by omega) hq; have := g.pS; have := g.hN; omega)
        hI.qbuf,
      ts_keep h (hm'.kept hwf) hso (fun q hq ↦ by
        have := loc_nat h (by omega) hq; have := g.tS; have := g.aS; have := g.hN; omega)
        hI.ts, hj⟩
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  simp only [Env.ofMachine_regs] at hpc'
  simp only [show (st.data.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (64 * i) from hx9b]
    at hpc'
  by_cases hlast : i + 1 = 57
  · have : BitVec.ofNat 64 (64 * i) + 64#64 = 3648#64 := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    simp only [this, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    exact .done _ (.inr ⟨hpc'.trans (by rw [show k + NativeRustcVmArm.Vm.NextLevel.b17Offset + b17.length = k + NativeRustcVmArm.Vm.NextLevel.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.NextLevel.b17_next]]),
      hI' 57 (le_refl _) (by rw [x9n]; omega)⟩)
  · have hne : (BitVec.ofNat 64 (64 * i) + 64#64 == 3648#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      have := congrArg BitVec.toNat e
      simp at this
      omega
    simp only [hne, Bool.not_false, ite_true] at hpc'
    exact .done _ (.inl ⟨hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.NextLevel.b17Offset) NativeRustcVmArm.Vm.NextLevel.label_9_at), by omega,
      hI' (i + 1) (by omega) x9n⟩)

/-- **The zeroing loop**, to its end. -/
theorem zero_loop (hp : Placed code k) (h : NextLevelPre a s level w rounds m0) {i : Nat}
    (hi : i < 57) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b17Offset))
    (hI : H17 a level m0 xs ood v lam qs s8 i st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b18Offset) ∧
      H17 a level m0 xs ood v lam qs s8 57 st'.data) st :=
  Sym.loop (fun n st ↦ ∃ i, n = 57 - i ∧ i < 57 ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b17Offset) ∧
      H17 a level m0 xs ood v lam qs s8 i st.data)
    (fun _ st ⟨i, hn, hi, hpc, hI⟩ ↦ (zero_step hp h hi hpc hI).mono fun st' h ↦ by
      rcases h with ⟨hpc', hi', hI'⟩ | h
      · exact Or.inr ⟨57 - (i + 1), by omega, i + 1, rfl, hi', hpc', hI'⟩
      · exact Or.inl h)
    ⟨i, rfl, hi, hpc, hI⟩

end

end

end NativeRustcVmArm.Whir.NextLevel
