module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.PaddingWeight.Names
public import NativeRustcVmArm.Arrays.PaddingWeight.Exec
public import NativeRustcVm.Arrays.Folds

/-!
# `padding_weight` on AArch64

**`paddingWeight_spec`**: rustc's `padding_weight(point, n)`, placed anywhere in the program,
meets `PaddingWeightPre`/`PaddingWeightPost` given `EW::mul`'s contract. The prologue (`b0`) saves
X19-X30 and `|point|` in its 112-byte frame; the loop (`b2`-`b4`, two calls of `EW::mul`) keeps
`pad` in X23, X21 (`Inv`, the model's fold over `point.zipIdx` after `k` coordinates; `bit_e` is
`lsr`, `mvn`, `and #1`, `1 - b`, for `k < 64`), and `.LPaddingWeight_4` (`b7`) restores the
registers and tail-calls `EW::mul` for `(1 + bit_e(n, |point|))·pad` (`tail_mul`).
-/

namespace NativeRustcVmArm.Arrays.PaddingWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PaddingWeight NativeVm.Model
open NativeRustcVm (ewsOf ewOf)

public section

/-- The point at the entry. -/
abbrev pts (m : MachineData) : List EW := ewsOf m.dmem m.regs.X0.toBitVec m.regs.X1.toNat
/-- Its length. -/
abbrev len (m : MachineData) : Nat := m.regs.X1.toNat
/-- `n`. -/
abbrev nn (m : MachineData) : Nat := m.regs.X2.toNat

/-- The model's step. -/
def g (n : Nat) (pad : EW) (p : EW × Nat) : EW :=
  (1 + EW.ofNat ((n >>> p.2) % 2)) * p.1 + (1 + EW.ofNat ((n >>> p.2) % 2) + p.1) * pad

/-- The model's fold after `i` coordinates. -/
def pad (m : MachineData) (i : Nat) : EW := (((pts m).zipIdx).take i).foldl (g (nn m)) 1

theorem paddingWeight_eq_pad (m : MachineData) :
    paddingWeight (slice m m.regs.X0 m.regs.X1) (nn m) =
      (1 + EW.ofNat ((nn m >>> len m) % 2)) * pad m (len m) := by
  unfold slice pad paddingWeight
  rw [← Array.foldl_toList, Array.toList_zipIdx, List.take_of_length_le (by simp)]
  simp only [List.size_toArray, NativeRustcVm.length_ewsOf]
  rfl

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (pts m).length := by
  simp only [pts, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem pad_succ (m : MachineData) {i : Nat} (h : i < len m) :
    pad m (i + 1) = g (nn m) (pad m i) ((pts m)[i]'(lt_len h), i) := by
  unfold pad
  rw [NativeRustcVm.foldl_take_succ _ _ _ (by rw [List.length_zipIdx]; exact lt_len h),
    List.getElem_zipIdx,
    Nat.zero_add]

/-- **The loop head** `.LPaddingWeight_2`, `i` coordinates folded. -/
structure Inv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : Body m0 112 paddingWeightStack slots 0 0 s
  lt : i < len m0
  x19 : s.regs.X19 = m0.regs.X2
  x20 : s.regs.X20.toNat = i
  x22 : s.regs.X22.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * i)
  x29 : s.regs.X29.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * len m0)
  pad : (⟨s.regs.X23, s.regs.X21⟩ : EW) = pad m0 i

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b0Offset) :=
  b0_in_code.trans hp.1 (by simp [b0])
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b6Offset) :=
  b6_in_code.trans hp.1 (by simp [b6])
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.PaddingWeight.b7Offset) :=
  b7_in_code.trans hp.1 (by simp [b7])

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.PaddingWeight.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.PaddingWeight.entryOffset) NativeRustcVmArm.Vm.PaddingWeight.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.PaddingWeight.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b2Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.PaddingWeight.b2Offset) NativeRustcVmArm.Vm.PaddingWeight.label_2_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.PaddingWeight.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.PaddingWeight.b6Offset) NativeRustcVmArm.Vm.PaddingWeight.label_3_at
theorem lbl_4 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.PaddingWeight.label_4 = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b7Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.PaddingWeight.b7Offset) NativeRustcVmArm.Vm.PaddingWeight.label_4_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ PaddingWeightPost m0 s.data

/-- **`.LPaddingWeight_4`** (`b7`): `1 + bit_e(n, |point|)`, the epilogue, the tail call. -/
theorem finish (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PaddingWeightPre m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b7Offset)) (hb : Body m0 112 paddingWeightStack slots 0 0 s.data)
    (hx19 : s.data.regs.X19 = m0.regs.X2)
    (hpad : (⟨s.data.regs.X23, s.data.regs.X21⟩ : EW) = pad m0 (len m0)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hS, h64, -⟩ := hpre
  obtain ⟨hwf, hm⟩ := hb.exit_match hS (by decide) rfl
  refine exec_at (hb7 hp) run_b7 hwf hpc hm fun s' hm' hpc' ↦ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hb.saved hm' hwf (List.mem_map.mpr ⟨(24, .X30), by simp [slots], rfl⟩)
    (after_eq run_b7 ▸ b7_restores) rfl
  simp only [PcOk] at hpc'
  obtain ⟨s', pc'⟩ := s'
  simp only at hpc' hsaved hx30 hdm
  have hc : Changes m0 s' paddingWeightStack 0 0 := fun p hp' ↦ by rw [hdm]; exact hb.same p hp'
  refine Eventually.mono (tail_mul hmul hS (by decide) hsaved hx30 hc hpc') fun r ⟨hr1, hr2, hr3, hr4⟩ ↦
    ⟨hr1, ?_, hr3, hr4⟩
  rw [paddingWeight_eq_pad]
  show (⟨r.data.regs.X0, r.data.regs.X1⟩ : EW) = _
  rw [hr2]
  have hlen := slot_load (r := 0) (o := 8) (x := .X1) (env := frameEnv m0 s.data 112)
    (by rw [base0]; exact hb.frame) (by simp [slots])
  have h0 := hm'.regs .X0 _ rfl
  have h1 := hm'.regs .X1 _ rfl
  have h2 := hm'.regs .X2 _ rfl
  have h3 := hm'.regs .X3 _ rfl
  simp only [Sym.eval] at h0
  rw [hlen, nbit_eval _ _ (by exact h64)] at h0
  sym_simp at h1 h2 h3
  simp only [Env.ofMachine_regs] at h0 h2 h3
  have hP : (⟨s'.regs.X2, s'.regs.X3⟩ : EW) = pad m0 (len m0) := by
    rw [← hpad]
    exact congr (congrArg EW.mk (UInt64.toBitVec_inj.mp h2)) (UInt64.toBitVec_inj.mp h3)
  have hB : (⟨s'.regs.X0, s'.regs.X1⟩ : EW) = 1 + EW.ofNat ((nn m0 >>> len m0) % 2) := by
    rw [← one_add_bit _ (Nat.mod_lt _ (by decide))]
    show (⟨s'.regs.getXReg .X0, s'.regs.getXReg .X1⟩ : EW) = _
    rw [toBitVec_eq h0, toBitVec_eq h1]
    have e : (s.data.regs.getXReg .X19).toBitVec.toNat = nn m0 := congrArg UInt64.toNat hx19
    rw [e]
    rfl
  rw [hP, hB]
  rfl

/-- **A turn of the loop**: `(1 + b)·r + (1 + b + r)·pad`, back at the head or out of the loop. -/
theorem step (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : PaddingWeightPre m0) {i : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b2Offset)) (hI : Inv m0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ Post m0 s' ∨
      (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b2Offset) ∧ Inv m0 (i + 1) s'.data)) s := by
  obtain ⟨hS, h64, hrP, hoP⟩ := hpre
  have hlt := hI.lt
  have hL : len m0 = m0.regs.X1.toNat := rfl
  have hnw : m0.regs.X0.toBitVec.toNat + 16 * m0.regs.X1.toNat ≤ 2 ^ 64 := hrP.2
  obtain ⟨s, pc⟩ := s
  have hx20 : (s.regs.getXReg .X20).toBitVec.toNat = i := hI.x20
  have hx19 : (s.regs.getXReg .X19).toBitVec.toNat = nn m0 := congrArg UInt64.toNat hI.x19
  -- `1 + b`, `r`, `(1 + b)·r`
  refine load_step (lo := .X24) (hi' := .X25) (hb2 hp) run_b2 rfl rfl
    (after_eq run_b2 ▸ b2_facts.1) _ (after_eq run_b2 ▸ b2_facts.2) hI.body hS hrP hoP
    (apart_zero _ _) noWrap_zero (show i < m0.regs.X1.toNat from hlt) hpc
    (by
      show s.regs.X22.toBitVec = _
      rw [hI.x22]
      exact (BitVec.add_zero _).symm)
    fun s2 hm2 hpc2 bd2 hR e2 ↦ ?_
  simp only [NativeRustcVmArm.Vm.PaddingWeight.b2_length, NativeRustcVmArm.Vm.PaddingWeight.b2Length] at hpc2
  have hbit : (⟨s2.data.regs.X0, s2.data.regs.X1⟩ : EW) = 1 + EW.ofNat ((nn m0 >>> i) % 2) := by
    rw [← one_add_bit _ (Nat.mod_lt _ (by decide))]
    have h0 := hm2.regs .X0 _ rfl
    have h1 := hm2.regs .X1 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at h0
    rw [nbit_eval _ _ (by rw [hx20]; omega), hx20, hx19] at h0
    sym_simp at h1
    show (⟨s2.data.regs.getXReg .X0, s2.data.regs.getXReg .X1⟩ : EW) = _
    rw [toBitVec_eq h0, toBitVec_eq h1]
    rfl
  have h26 := hm2.regs .X26 _ rfl
  simp only [Sym.eval, Env.ofMachine_regs] at h26
  rw [nbit_eval _ _ (by rw [hx20]; omega), hx20, hx19] at h26
  have hR2 : (⟨s2.data.regs.X2, s2.data.regs.X3⟩ : EW) = (pts m0)[i]'(lt_len hlt) := by
    rw [← hR]
    have h2 := hm2.regs .X2 _ rfl
    have h3 := hm2.regs .X3 _ rfl
    have h24 := hm2.regs .X24 _ rfl
    have h25 := hm2.regs .X25 _ rfl
    show (⟨s2.data.regs.getXReg .X2, s2.data.regs.getXReg .X3⟩ : EW) = _
    rw [toBitVec_eq h2, toBitVec_eq h3, ← h24, ← h25]
  refine call_then hpc2 hmul (bd2.ewMulPre hS (by decide) (by decide)) fun s3 hpc3 hpost3 ↦ ?_
  have bd3 := bd2.call hS (by decide) (by decide) hpost3
  have ht1 : (⟨s3.data.regs.X0, s3.data.regs.X1⟩ : EW) =
      (1 + EW.ofNat ((nn m0 >>> i) % 2)) * (pts m0)[i]'(lt_len hlt) := by
    rw [hpost3.1, hpost3.2.1, ← hbit, ← hR2]
    rfl
  -- `(1 + b + r)·pad`
  refine exec_at (hb3 hp) run_b3 (Env.wf_nil _) hpc3 (match_nil _) fun s4 hm4 hpc4 ↦ ?_
  have bd4 := bd3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl (after_eq run_b3 ▸ b3_keeps)
  simp only [NativeRustcVmArm.Vm.PaddingWeight.b3_length, NativeRustcVmArm.Vm.PaddingWeight.b3Length] at hpc4
  refine call_then hpc4 hmul (bd4.ewMulPre hS (by decide) (by decide)) fun s5 hpc5 hpost5 ↦ ?_
  have bd5 := bd4.call hS (by decide) (by decide) hpost5
  have k3 : ∀ r, calleeSaved r = true → s3.data.regs.getXReg r = s2.data.regs.getXReg r :=
    hpost3.2.2.2.1
  have ht2 : (⟨s5.data.regs.X0, s5.data.regs.X1⟩ : EW) =
      (1 + EW.ofNat ((nn m0 >>> i) % 2) + (pts m0)[i]'(lt_len hlt)) * pad m0 i := by
    rw [hpost5.1, hpost5.2.1]
    have h0 := hm4.regs .X0 _ rfl
    have h1 := hm4.regs .X1 _ rfl
    have h2 := hm4.regs .X2 _ rfl
    have h3 := hm4.regs .X3 _ rfl
    sym_simp at h0 h1 h2 h3
    simp only [Env.ofMachine_regs] at h0 h1 h2 h3
    rw [k3 .X24 rfl, k3 .X26 rfl, h26] at h0
    rw [k3 .X25 rfl] at h1
    rw [k3 .X23 rfl, e2 .X23 (by simp)] at h2
    rw [k3 .X21 rfl, e2 .X21 (by simp)] at h3
    have hA : (⟨s4.data.regs.X0, s4.data.regs.X1⟩ : EW) =
        1 + EW.ofNat ((nn m0 >>> i) % 2) + (pts m0)[i]'(lt_len hlt) := by
      rw [← one_add_bit _ (Nat.mod_lt _ (by decide)), ← hR]
      show (⟨s4.data.regs.getXReg .X0, s4.data.regs.getXReg .X1⟩ : EW) = _
      rw [toBitVec_eq h0, toBitVec_eq h1]
      show (⟨_, _⟩ : EW) = ⟨_ ^^^ _, 0 ^^^ _⟩
      rw [UInt64.zero_xor]
      congr 1
      apply UInt64.toBitVec_inj.mp
      simp only [UInt64.toBitVec_xor]
      exact BitVec.xor_comm _ _
    have hB : (⟨s4.data.regs.X2, s4.data.regs.X3⟩ : EW) = pad m0 i := by
      rw [← hI.pad]
      show (⟨s4.data.regs.getXReg .X2, s4.data.regs.getXReg .X3⟩ : EW) = _
      rw [toBitVec_eq h2, toBitVec_eq h3]
      rfl
    rw [hA, hB]
    rfl
  -- the sum, the loop test
  refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) hpc5 (match_nil _) fun s6 hm6 hpc6 ↦ ?_
  have bd6 := bd5.of_block (match_nil _) hm6 (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps)
  have k5 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X29],
      s5.data.regs.getXReg r = s3.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hpost5.2.2.2.1 _ rfl).trans (Match.reg_eq (match_nil _) hm4 rfl rfl)
  have hpad' : (⟨s6.data.regs.X23, s6.data.regs.X21⟩ : EW) = pad m0 (i + 1) := by
    rw [pad_succ m0 hlt]
    have h23 := hm6.regs .X23 _ rfl
    have h21 := hm6.regs .X21 _ rfl
    sym_simp at h23 h21
    simp only [Env.ofMachine_regs] at h23 h21
    rw [hpost5.2.2.2.1 .X27 rfl] at h23
    rw [hpost5.2.2.2.1 .X28 rfl] at h21
    have q27 := hm4.regs .X27 _ rfl
    have q28 := hm4.regs .X28 _ rfl
    simp only [Sym.eval, Env.ofMachine_regs] at q27 q28
    rw [q27] at h23
    rw [q28] at h21
    show (⟨s6.data.regs.getXReg .X23, s6.data.regs.getXReg .X21⟩ : EW) = _
    rw [toBitVec_eq h23, toBitVec_eq h21]
    unfold g
    rw [← ht1, ← ht2]
    show (⟨_, _⟩ : EW) = ⟨_ ^^^ _, _ ^^^ _⟩
    congr 1 <;> exact UInt64.xor_comm _ _
  have kk : ∀ r ∈ [XReg.X19, .X20, .X22, .X29], s6.data.regs.getXReg r = s2.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact (Match.reg_eq (match_nil _) hm6 rfl rfl).trans ((k5 _ (by simp)).trans (k3 _ rfl))
  have hx22 : (s2.data.regs.getXReg .X22).toBitVec =
      m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * (i + 1)) := by
    have h := hm2.regs .X22 _ rfl
    simp only [Sym.eval, base0] at h
    rw [h, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_add]
    congr 2
  have hx29 : (s2.data.regs.getXReg .X29).toBitVec =
      m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * len m0) := by
    rw [e2 .X29 (by simp)]; exact hI.x29
  have hx20' : (s2.data.regs.getXReg .X20).toBitVec.toNat = i + 1 := by
    have h := hm2.regs .X20 _ rfl
    sym_simp at h
    simp only [Env.ofMachine_regs] at h
    rw [h, BitVec.toNat_add, hx20]
    simp only [BitVec.toNat_ofNat]
    omega
  simp only [PcOk] at hpc6
  sym_simp at hpc6
  have hpc6' := pc_ne hpc6
  have heq : (s5.data.regs.getXReg .X22).toBitVec = (s5.data.regs.getXReg .X29).toBitVec ↔
      i + 1 = len m0 := by
    rw [k5 .X22 (by simp), k5 .X29 (by simp), k3 .X22 rfl, k3 .X29 rfl, hx22, hx29]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h'
      omega
    · intro h; rw [h]
  by_cases hlast : i + 1 = len m0
  · have hpc6 := hpc6'.2 (heq.mpr hlast)
    simp only [NativeRustcVmArm.Vm.PaddingWeight.b4_length, NativeRustcVmArm.Vm.PaddingWeight.b4Length] at hpc6
    refine exec_at (hb5 hp) run_b5 (Env.wf_nil _) hpc6 (match_nil _) fun s7 hm7 hpc7 ↦ ?_
    have bd7 := bd6.of_block (match_nil _) hm7 (Env.wf_nil _) rfl (after_eq run_b5 ▸ b5_keeps)
    simp only [PcOk] at hpc7
    refine Eventually.mono (finish hp hmul ⟨hS, h64, hrP, hoP⟩ (hpc7.trans (lbl_4 hp)) bd7 ?_ ?_)
      fun _ h ↦ Or.inl h
    · have q : s7.data.regs.getXReg .X19 = s6.data.regs.getXReg .X19 :=
        Match.reg_eq (match_nil _) hm7 rfl rfl
      rw [kk .X19 (by simp), e2 .X19 (by simp)] at q
      exact q.trans hI.x19
    · rw [← hlast, ← hpad']
      show (⟨s7.data.regs.getXReg .X23, s7.data.regs.getXReg .X21⟩ : EW) = _
      rw [Match.reg_eq (match_nil _) hm7 rfl rfl, Match.reg_eq (r := .X21) (match_nil _) hm7 rfl rfl]
      rfl
  · have hpc6 := hpc6'.1 (fun h ↦ hlast (heq.mp h))
    refine .done _ (Or.inr ⟨hpc6.trans (lbl_2 hp), bd6, by omega, ?_, ?_, ?_, ?_, hpad'⟩)
    · have q := kk .X19 (by simp)
      rw [e2 .X19 (by simp)] at q
      exact q.trans hI.x19
    · show (s6.data.regs.getXReg .X20).toBitVec.toNat = _
      rw [kk .X20 (by simp)]; exact hx20'
    · show (s6.data.regs.getXReg .X22).toBitVec = _
      rw [kk .X22 (by simp)]; exact hx22
    · show (s6.data.regs.getXReg .X29).toBitVec = _
      rw [kk .X29 (by simp)]; exact hx29

/-- **`padding_weight` meets its contract.** -/
theorem paddingWeight_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  obtain ⟨hS, h64, hrP, hoP⟩ := hpre
  have h112 : 112 ≤ paddingWeightStack := by decide
  obtain ⟨hwf, hm⟩ := entry_match hS h112 rfl
  refine exec_then (hb0 hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, NativeRustcVmArm.Vm.PaddingWeight.b0_length, NativeRustcVmArm.Vm.PaddingWeight.b0Length] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  by_cases hz : len m0 = 0
  · -- `|point| = 0`: `pad = 1`.
    have hpc1 := hpc1'.1 (by
      show ((m0.regs.getXReg .X1).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      exact hz)
    refine exec_at (hb6 hp) (exec_after run_b0 run_b6) hwf (hpc1.trans (lbl_3 hp)) hm1
      fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.PaddingWeight.b6_length, NativeRustcVmArm.Vm.PaddingWeight.b6Length] at hpc2
    obtain ⟨hw, hmem, hregs⟩ := after_eq run_b6 ▸ b6_frame
    refine finish hp hmul ⟨hS, h64, hrP, hoP⟩ hpc2 (Body.of_entry hS h112 hm2 rfl hw hregs hmem)
      ?_ ?_
    · exact UInt64.toBitVec_inj.mp (hm2.regs .X19 _ rfl)
    · have h21 := reg_of hm2 (r := .X21) rfl
      have h23 := reg_of hm2 (r := .X23) rfl
      sym_simp at h21 h23
      rw [hz]
      show (⟨s2.data.regs.getXReg .X23, s2.data.regs.getXReg .X21⟩ : EW) = _
      rw [h21, h23]
      rfl
  · have hpc1 := hpc1'.2 (by
      show ¬((m0.regs.getXReg .X1).toBitVec == 0#64) = true
      rw [beq_iff_eq]
      intro h
      exact hz (congrArg BitVec.toNat h))
    refine exec_at (hb1 hp) (exec_after run_b0 run_b1) hwf hpc1 hm1 fun s2 hm2 hpc2 ↦ ?_
    simp only [PcOk, NativeRustcVmArm.Vm.PaddingWeight.b1_length, NativeRustcVmArm.Vm.PaddingWeight.b1Length] at hpc2
    obtain ⟨hw, hmem, hregs⟩ := after_eq run_b1 ▸ b1_frame
    have hI : Inv m0 0 s2.data := by
      have h19 := hm2.regs .X19 _ rfl
      have h20 := reg_of hm2 (r := .X20) rfl
      have h21 := reg_of hm2 (r := .X21) rfl
      have h22 := reg_of hm2 (r := .X22) rfl
      have h23 := reg_of hm2 (r := .X23) rfl
      have h29 := hm2.regs .X29 _ rfl
      simp only [Sym.eval, UnOp.apply, shiftW, Sym.ext_W64, Sym.low_W64, shl4] at h29
      sym_simp at h19 h20 h21 h22 h23 h29
      simp only [Env.ofMachine_regs, UInt64.ofBitVec_toBitVec] at h19 h22 h29
      refine ⟨Body.of_entry hS h112 hm2 rfl hw hregs hmem, Nat.pos_of_ne_zero hz,
        UInt64.toBitVec_inj.mp h19, ?_, ?_, ?_, ?_⟩
      · show (s2.data.regs.getXReg .X20).toNat = 0
        rw [h20]; rfl
      · show (s2.data.regs.getXReg .X22).toBitVec = _
        rw [h22, Nat.mul_zero, add_ofNat_zero]
        rfl
      · show (s2.data.regs.getXReg .X29).toBitVec = _
        rw [h29]
        rfl
      · show (⟨s2.data.regs.getXReg .X23, s2.data.regs.getXReg .X21⟩ : EW) = _
        rw [h21, h23]
        rfl
    refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PaddingWeight.b2Offset) ∧ ∃ i, len m0 - i = n ∧
      Inv m0 i s.data) (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc2, 0, rfl, hI⟩
    refine Eventually.mono (step hp hmul ⟨hS, h64, hrP, hoP⟩ hpc hI) fun s' h ↦ ?_
    rcases h with h | ⟨hpc', hI'⟩
    · exact Or.inl h
    · exact Or.inr ⟨len m0 - (i + 1), by have := hI'.lt; omega, hpc', i + 1, rfl, hI'⟩

end

end NativeRustcVmArm.Arrays.PaddingWeight
