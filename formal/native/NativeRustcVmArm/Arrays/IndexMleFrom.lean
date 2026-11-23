module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.IndexMleFrom.Names
public import NativeRustcVmArm.Arrays.IndexMleFrom.Exec
public import NativeRustcVm.Arrays.Folds

/-!
# `index_mle_from` on AArch64

**`indexMleFrom_spec`**: rustc's `index_mle_from(GEN, point)` (the generator power specialised to
its only caller's `GEN`), placed anywhere in the program, meets `IndexMleFromPre`/
`IndexMleFromPost` given `EW::mul`'s contract: `indexMleFrom gen point`. The prologue (`b0`)
saves X19-X24 and X30 in its 64-byte frame; at `|point| = 0` it returns `1` (`b7`, `b8`); else the
loop (`b2`-`b5`, three calls of `EW::mul`) keeps the accumulator in X21, X19 and the power in X23,
X22 (`Inv`, the model's fold after `i` coordinates), and the epilogue (`b8`) returns the
accumulator.
-/

namespace NativeRustcVmArm.Arrays.IndexMleFrom

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.IndexMleFrom NativeVm.Model
open NativeRustcVm (ewsOf ewOf)

public section

/-- The point at the entry. -/
abbrev pts (m : MachineData) : List EW := ewsOf m.dmem m.regs.X0.toBitVec m.regs.X1.toNat
/-- Its length. -/
abbrev len (m : MachineData) : Nat := m.regs.X1.toNat

/-- The model's step. -/
def f (acc : EW × EW) (r : EW) : EW × EW := (acc.1 * (1 + r * (1 + acc.2)), acc.2 * acc.2)

/-- The model's fold after `i` coordinates. -/
def st (m : MachineData) (i : Nat) : EW × EW := ((pts m).take i).foldl f (1, gen)

theorem indexMleFrom_eq_st (m : MachineData) :
    indexMleFrom gen (slice m m.regs.X0 m.regs.X1) = (st m (len m)).1 := by
  unfold slice st indexMleFrom
  rw [← Array.foldl_toList, List.take_of_length_le (by simp)]
  rfl

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (pts m).length := by
  simp only [pts, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem st_succ (m : MachineData) {i : Nat} (h : i < len m) :
    st m (i + 1) = f (st m i) ((pts m)[i]'(lt_len h)) :=
  NativeRustcVm.foldl_take_succ _ _ _ _

/-- **The loop head** `.LIndexMleFrom_2`, `i` coordinates folded. -/
structure Inv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : Body m0 64 indexMleFromStack slots 0 0 s
  lt : i < len m0
  x20 : s.regs.X20.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * i)
  x24 : s.regs.X24.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * len m0)
  acc : (⟨s.regs.X21, s.regs.X19⟩ : EW) = (st m0 i).1
  pow : (⟨s.regs.X23, s.regs.X22⟩ : EW) = (st m0 i).2

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.IndexMleFrom.b8Offset) :=
  b8_in_code.trans hp.1 (by simp [b8])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.IndexMleFrom.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.IndexMleFrom.entryOffset) NativeRustcVmArm.Vm.IndexMleFrom.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.IndexMleFrom.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.IndexMleFrom.b2Offset) NativeRustcVmArm.Vm.IndexMleFrom.label_2_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.IndexMleFrom.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.IndexMleFrom.b7Offset) NativeRustcVmArm.Vm.IndexMleFrom.label_3_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.IndexMleFrom.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b8Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.IndexMleFrom.b8Offset) NativeRustcVmArm.Vm.IndexMleFrom.label_4_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ IndexMleFromPost m0 s.data

/-- **The epilogue** `b8`: the accumulator (X21, X19) returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : IndexMleFromPre m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b8Offset)) (hb : Body m0 64 indexMleFromStack slots 0 0 s.data)
    (hacc : (⟨s.data.regs.X21, s.data.regs.X19⟩ : EW) = (st m0 (len m0)).1) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hwf, hm⟩ := hb.exit_match hpre.1 (by decide) rfl
  refine exec_at (hb8 hp) run_b8 hwf hpc hm fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩)
    (after_eq run_b8 ▸ b8_restores) rfl
  refine ⟨?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · rw [indexMleFrom_eq_st, ← hacc]
    have h0 := hm'.regs .X0 _ rfl
    have h1 := hm'.regs .X1 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h0 h1
    exact congr (congrArg EW.mk (UInt64.toBitVec_inj.mp h0)) (UInt64.toBitVec_inj.mp h1)
  · intro p hp'
    rw [hdm]
    exact hb.same p hp'

/-- **A turn of the loop**: `r·(1 + power)`, `acc·(1 + ·)`, `power²`, back at the head or out of
the loop and returned. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : IndexMleFromPre m0) {i : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b2Offset)) (hI : Inv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b2Offset) ∧ Inv m0 (i + 1) s'.data)) s := by
  obtain ⟨hS, hrP, hoP⟩ := hpre
  have hlt := hI.lt
  have hL : len m0 = m0.regs.X1.toNat := rfl
  have hnw : m0.regs.X0.toBitVec.toNat + 16 * m0.regs.X1.toNat ≤ 2 ^ 64 := hrP.2
  obtain ⟨s, pc⟩ := s
  -- `r`, `r·(1 + power)`
  refine load_step (lo := .X0) (hi' := .X1) (hb2 hp) run_b2 rfl rfl
    (after_eq run_b2 ▸ b2_facts.1) _ (after_eq run_b2 ▸ b2_facts.2) hI.body hS hrP hoP
    (apart_zero _ _) noWrap_zero (show i < m0.regs.X1.toNat from hlt) hpc
    (by
      show s.regs.X20.toBitVec = _
      rw [hI.x20]
      exact (BitVec.add_zero _).symm)
    fun s2 hm2 hpc2 bd2 hR e2 ↦ ?_
  simp only [NativeRustcVmArm.Vm.IndexMleFrom.b2_length, NativeRustcVmArm.Vm.IndexMleFrom.b2Length] at hpc2
  have hpow : (⟨s2.data.regs.X2, s2.data.regs.X3⟩ : EW) = 1 + (st m0 i).2 := by
    rw [← hI.pow, one_add]
    have h2 := reg_of hm2 (r := .X2) rfl
    have h3 := reg_of hm2 (r := .X3) rfl
    sym_simp at h2 h3
    simp only [Env.ofMachine_regs] at h2 h3
    show (⟨s2.data.regs.getXReg .X2, s2.data.regs.getXReg .X3⟩ : EW) = _
    rw [h2, h3]
    rfl
  refine call_then hpc2 hmul (bd2.ewMulPre hS (by decide) (by decide)) fun s3 hpc3 hpost3 ↦ ?_
  have bd3 := bd2.call hS (by decide) (by decide) hpost3
  have ht : (⟨s3.data.regs.X0, s3.data.regs.X1⟩ : EW) =
      (pts m0)[i]'(lt_len hlt) * (1 + (st m0 i).2) := by
    rw [hpost3.1, hpost3.2.1, ← hR, ← hpow]
    rfl
  -- `acc·(1 + t)`
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) hpc3 (match_nil _) fun s4 hm4 hpc4 ↦ ?_
  have bd4 := bd3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  simp only [NativeRustcVmArm.Vm.IndexMleFrom.b3_length, NativeRustcVmArm.Vm.IndexMleFrom.b3Length] at hpc4
  refine call_then hpc4 hmul (bd4.ewMulPre hS (by decide) (by decide)) fun s5 hpc5 hpost5 ↦ ?_
  have bd5 := bd4.call hS (by decide) (by decide) hpost5
  have e19 : s3.data.regs.getXReg .X19 = s.regs.getXReg .X19 :=
    (hpost3.2.2.2.1 .X19 rfl).trans (e2 .X19 (by simp))
  have e21 : s3.data.regs.getXReg .X21 = s.regs.getXReg .X21 :=
    (hpost3.2.2.2.1 .X21 rfl).trans (e2 .X21 (by simp))
  have e22 : s3.data.regs.getXReg .X22 = s.regs.getXReg .X22 :=
    (hpost3.2.2.2.1 .X22 rfl).trans (e2 .X22 (by simp))
  have e23 : s3.data.regs.getXReg .X23 = s.regs.getXReg .X23 :=
    (hpost3.2.2.2.1 .X23 rfl).trans (e2 .X23 (by simp))
  have e24 : s3.data.regs.getXReg .X24 = s.regs.getXReg .X24 :=
    (hpost3.2.2.2.1 .X24 rfl).trans (e2 .X24 (by simp))
  have hacc' : (⟨s5.data.regs.X0, s5.data.regs.X1⟩ : EW) = (st m0 (i + 1)).1 := by
    rw [st_succ m0 hlt, hpost5.1, hpost5.2.1]
    have h0 := reg_of hm4 (r := .X0) rfl
    have h1 := reg_of hm4 (r := .X1) rfl
    have h2 := reg_of hm4 (r := .X2) rfl
    have h3 := reg_of hm4 (r := .X3) rfl
    sym_simp at h0 h1 h2 h3
    simp only [Env.ofMachine_regs] at h0 h1 h2 h3
    have hA : (⟨s4.data.regs.X0, s4.data.regs.X1⟩ : EW) = (st m0 i).1 := by
      rw [← hI.acc]
      show (⟨s4.data.regs.getXReg .X0, s4.data.regs.getXReg .X1⟩ : EW) = _
      rw [h0, h1, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec, e21, e19]
      rfl
    have hB : (⟨s4.data.regs.X2, s4.data.regs.X3⟩ : EW) =
        1 + (pts m0)[i]'(lt_len hlt) * (1 + (st m0 i).2) := by
      rw [← ht, one_add]
      show (⟨s4.data.regs.getXReg .X2, s4.data.regs.getXReg .X3⟩ : EW) = _
      rw [h2, h3, UInt64.ofBitVec_toBitVec]
      rfl
    rw [hA, hB]
    rfl
  -- `power²`
  refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) hpc5 (match_nil _) fun s6 hm6 hpc6 ↦ ?_
  have bd6 := bd5.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps)
  simp only [NativeRustcVmArm.Vm.IndexMleFrom.b4_length, NativeRustcVmArm.Vm.IndexMleFrom.b4Length] at hpc6
  refine call_then hpc6 hmul (bd6.ewMulPre hS (by decide) (by decide)) fun s7 hpc7 hpost7 ↦ ?_
  have bd7 := bd6.call hS (by decide) (by decide) hpost7
  have e4 : ∀ r ∈ [XReg.X22, .X23, .X24], s5.data.regs.getXReg r = s.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hpost5.2.2.2.1 _ rfl).trans ((Match.reg_eq (match_nil _) hm4 rfl rfl).trans e22)
    · exact (hpost5.2.2.2.1 _ rfl).trans ((Match.reg_eq (match_nil _) hm4 rfl rfl).trans e23)
    · exact (hpost5.2.2.2.1 _ rfl).trans ((Match.reg_eq (match_nil _) hm4 rfl rfl).trans e24)
  have h21 := reg_of hm6 (r := .X21) rfl
  have h19 := reg_of hm6 (r := .X19) rfl
  have h0 := reg_of hm6 (r := .X0) rfl
  have h1 := reg_of hm6 (r := .X1) rfl
  have h2 := reg_of hm6 (r := .X2) rfl
  have h3 := reg_of hm6 (r := .X3) rfl
  sym_simp at h21 h19 h0 h1 h2 h3
  simp only [Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at h21 h19 h0 h1 h2 h3
  have hsq : (⟨s7.data.regs.X0, s7.data.regs.X1⟩ : EW) = (st m0 (i + 1)).2 := by
    rw [st_succ m0 hlt, hpost7.1, hpost7.2.1]
    have hP : (⟨s6.data.regs.X0, s6.data.regs.X1⟩ : EW) = (st m0 i).2 := by
      show (⟨s6.data.regs.getXReg .X0, s6.data.regs.getXReg .X1⟩ : EW) = _
      rw [h0, h1, e4 .X23 (by simp), e4 .X22 (by simp)]
      exact hI.pow
    have hQ : (⟨s6.data.regs.X2, s6.data.regs.X3⟩ : EW) = (st m0 i).2 := by
      show (⟨s6.data.regs.getXReg .X2, s6.data.regs.getXReg .X3⟩ : EW) = _
      rw [h2, h3, e4 .X23 (by simp), e4 .X22 (by simp)]
      exact hI.pow
    rw [hP, hQ]
    rfl
  have hacc7 : (⟨s7.data.regs.X21, s7.data.regs.X19⟩ : EW) = (st m0 (i + 1)).1 := by
    rw [← hacc']
    show (⟨s7.data.regs.getXReg .X21, s7.data.regs.getXReg .X19⟩ : EW) = _
    rw [hpost7.2.2.2.1 .X21 rfl, hpost7.2.2.2.1 .X19 rfl, h21, h19]
    rfl
  -- the loop test
  refine exec_at (hb5 hp) run_b5 (Env.wf_nil _) hpc7 (match_nil _) fun s8 hm8 hpc8 ↦ ?_
  have bd8 := bd7.of_block (match_nil _) hm8 (Env.wf_nil _) rfl (after_eq run_b5 ▸ b5_keeps)
  have h23 := reg_of hm8 (r := .X23) rfl
  have h22 := reg_of hm8 (r := .X22) rfl
  sym_simp at h23 h22
  simp only [Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at h23 h22
  have hpow8 : (⟨s8.data.regs.X23, s8.data.regs.X22⟩ : EW) = (st m0 (i + 1)).2 := by
    rw [← hsq]
    show (⟨s8.data.regs.getXReg .X23, s8.data.regs.getXReg .X22⟩ : EW) = _
    rw [h23, h22]
    rfl
  have hacc8 : (⟨s8.data.regs.X21, s8.data.regs.X19⟩ : EW) = (st m0 (i + 1)).1 := by
    rw [← hacc7]
    show (⟨s8.data.regs.getXReg .X21, s8.data.regs.getXReg .X19⟩ : EW) = _
    rw [Match.reg_eq (match_nil _) hm8 rfl rfl, Match.reg_eq (r := .X19) (match_nil _) hm8 rfl rfl]
    rfl
  -- X20 after the post-index, X24 kept
  have hx20 : (s7.data.regs.getXReg .X20).toBitVec =
      m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [hpost7.2.2.2.1 .X20 rfl, Match.reg_eq (r := .X20) (match_nil _) hm6 rfl rfl,
      hpost5.2.2.2.1 .X20 rfl, Match.reg_eq (r := .X20) (match_nil _) hm4 rfl rfl,
      hpost3.2.2.2.1 .X20 rfl]
    have h := hm2.regs .X20 _ rfl
    simp only [Sym.eval, base0] at h
    rw [h, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_add]
    congr 2
  have hx24 : (s7.data.regs.getXReg .X24).toBitVec =
      m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * len m0) := by
    rw [hpost7.2.2.2.1 .X24 rfl, Match.reg_eq (r := .X24) (match_nil _) hm6 rfl rfl,
      e4 .X24 (by simp)]
    exact hI.x24
  simp only [PcOk] at hpc8
  sym_simp at hpc8
  have hpc8' := pc_ne hpc8
  have heq : (s7.data.regs.getXReg .X20).toBitVec = (s7.data.regs.getXReg .X24).toBitVec ↔
      i + 1 = len m0 := by
    rw [hx20, hx24]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
      omega
    · intro h; rw [h]
  have e8 : ∀ r ∈ [XReg.X20, .X24], s8.data.regs.getXReg r = s7.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq (match_nil _) hm8 rfl rfl
  by_cases hlast : i + 1 = len m0
  · have hpc8 := hpc8'.2 (heq.mpr hlast)
    simp only [NativeRustcVmArm.Vm.IndexMleFrom.b5_length, NativeRustcVmArm.Vm.IndexMleFrom.b5Length] at hpc8
    refine exec_at (hb6 hp) run_b6 (Env.wf_nil _) hpc8 (match_nil _) fun s9 hm9 hpc9 ↦ ?_
    have bd9 := bd8.of_block (match_nil _) hm9 (Env.wf_nil _) rfl (after_eq run_b6 ▸ b6_keeps)
    simp only [PcOk] at hpc9
    refine Eventually.mono (finish hp ⟨hS, hrP, hoP⟩ (hpc9.trans (lbl_4 hp)) bd9 ?_)
      fun _ h ↦ Or.inl h
    rw [← hlast, ← hacc8]
    show (⟨s9.data.regs.getXReg .X21, s9.data.regs.getXReg .X19⟩ : EW) = _
    rw [Match.reg_eq (match_nil _) hm9 rfl rfl, Match.reg_eq (r := .X19) (match_nil _) hm9 rfl rfl]
    rfl
  · have hpc8 := hpc8'.1 (fun h ↦ hlast (heq.mp h))
    refine .done _ (Or.inr ⟨hpc8.trans (lbl_2 hp), bd8, by omega, ?_, ?_, hacc8, hpow8⟩)
    · show (s8.data.regs.getXReg .X20).toBitVec = _
      rw [e8 .X20 (by simp), hx20]
    · show (s8.data.regs.getXReg .X24).toBitVec = _
      rw [e8 .X24 (by simp), hx24]

/-- **`index_mle_from` meets its contract.** -/
theorem indexMleFrom_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.IndexMleFrom.entryLabel) IndexMleFromPre IndexMleFromPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hS, hrP, hoP⟩ := hpre
  have h64 : 64 ≤ indexMleFromStack := by decide
  obtain ⟨hwf, hm⟩ := entry_match hS h64 rfl
  refine exec_then (hb0 hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.IndexMleFrom.b0_length, NativeRustcVmArm.Vm.IndexMleFrom.b0Length] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `|point| = 0`: `1`.
    have hpc1 := hpc1'.1 (by
      show ((m0.regs.getXReg .X1).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      exact hz)
    refine exec_at (hb7 hp) (exec_after run_b0 run_b7) hwf (hpc1.trans (lbl_3 hp)) hm1
      fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.IndexMleFrom.b7_length, NativeRustcVmArm.Vm.IndexMleFrom.b7Length] at hpc2
    obtain ⟨hw, hmem, hregs⟩ := after_eq run_b7 ▸ b7_frame
    refine finish hp ⟨hS, hrP, hoP⟩ hpc2 (Body.of_entry hS h64 hm2 rfl hw hregs hmem) ?_
    have h21 := reg_of hm2 (r := .X21) rfl
    have h19 := reg_of hm2 (r := .X19) rfl
    sym_simp at h21 h19
    rw [hz]
    show (⟨s2.data.regs.getXReg .X21, s2.data.regs.getXReg .X19⟩ : EW) = _
    rw [h21, h19]
    rfl
  · have hpc1 := hpc1'.2 (by
      show ¬((m0.regs.getXReg .X1).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      intro h
      exact hz (congrArg BitVec.toNat h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.IndexMleFrom.b1_length, NativeRustcVmArm.Vm.IndexMleFrom.b1Length] at hpc2
    obtain ⟨hw, hmem, hregs⟩ := after_eq run_b1 ▸ b1_frame
    have hI : Inv m0 0 s2.data := by
      have h19 := reg_of hm2 (r := .X19) rfl
      have h20 := reg_of hm2 (r := .X20) rfl
      have h21 := reg_of hm2 (r := .X21) rfl
      have h22 := reg_of hm2 (r := .X22) rfl
      have h23 := reg_of hm2 (r := .X23) rfl
      have h24 := hm2.regs .X24 _ rfl
      simp only [Sym.eval, UnOp.apply, shiftW, Sym.ext_W64, Sym.low_W64, shl4] at h24
      sym_simp at h19 h20 h21 h22 h23 h24
      simp only [Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at h20 h24
      refine ⟨Body.of_entry hS h64 hm2 rfl hw hregs hmem, Nat.pos_of_ne_zero hz, ?_, ?_, ?_, ?_⟩
      · show (s2.data.regs.getXReg .X20).toBitVec = _
        rw [h20, Nat.mul_zero, add_ofNat_zero]
        rfl
      · show (s2.data.regs.getXReg .X24).toBitVec = _
        rw [h24]
        rfl
      · show (⟨s2.data.regs.getXReg .X21, s2.data.regs.getXReg .X19⟩ : EW) = _
        rw [h21, h19]
        rfl
      · show (⟨s2.data.regs.getXReg .X23, s2.data.regs.getXReg .X22⟩ : EW) = _
        rw [h23, h22]
        rfl
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.IndexMleFrom.b2Offset) ∧ ∃ i, len m0 - i = n ∧
      Inv m0 i s.data) (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul ⟨hS, hrP, hoP⟩ hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Arrays.IndexMleFrom
