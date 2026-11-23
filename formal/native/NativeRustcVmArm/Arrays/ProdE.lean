module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.ProdE.Names
public import NativeRustcVmArm.Arrays.ProdE.Exec
public import NativeRustcVm.Arrays.Folds

/-!
# `prod_e` on AArch64

**`prodE_spec`**: rustc's `prod_e(values)`, placed anywhere in the program, meets
`ProdEPre`/`ProdEPost` given `EW::mul`'s contract. rustc specialised the body to `2 ≤ len ≤ 4`:
the prologue (`b0a`) saves X19, X20 and X30 in its 32-byte frame, then each element is loaded and
multiplied into the product (`b0b`: `1·values[0]`; `b1`, `b3`: `mul_step`), the length tests
(`b2`, `b4`) leave through the epilogue (`b5`, `finish`) at lengths `2` and `3`, and at length `4`
the last product is a tail call (`b6a`, `b6b`, `tail_mul`).
-/

namespace NativeRustcVmArm.Arrays.ProdE

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ProdE NativeVm.Model
open NativeRustcVm (ewsOf ewOf)

public section

/-- The values at the entry. -/
abbrev vals (m : MachineData) : List EW := ewsOf m.dmem m.regs.X0.toBitVec m.regs.X1.toNat
/-- Their number. -/
abbrev len (m : MachineData) : Nat := m.regs.X1.toNat

/-- The product of the first `i` values. -/
def acc (m : MachineData) (i : Nat) : EW := ((vals m).take i).foldl (· * ·) 1

theorem prodE_eq_acc (m : MachineData) : prodE (slice m m.regs.X0 m.regs.X1) = acc m (len m) := by
  unfold slice acc
  rw [NativeRustcVm.prodE_eq, List.take_of_length_le (by simp)]

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (vals m).length := by
  simp only [vals, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem acc_succ (m : MachineData) {i : Nat} (h : i < len m) :
    acc m (i + 1) = acc m i * (vals m)[i]'(lt_len h) :=
  NativeRustcVm.foldl_take_succ _ _ _ _

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) :
    b0a.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b0Offset) ∧ b0b.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b0Offset + 3) := by
  have h := b0_in_code.trans hp.1 (by simp [b0])
  rw [← List.take_append_drop 3 b0] at h
  exact h.append
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b1Offset) :=
  b1_in_code.trans hp.1 (by simp [b1])
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b2Offset) :=
  b2_in_code.trans hp.1 (by simp [b2])
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b3Offset) :=
  b3_in_code.trans hp.1 (by simp [b3])
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b4Offset) :=
  b4_in_code.trans hp.1 (by simp [b4])
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b5Offset) :=
  b5_in_code.trans hp.1 (by simp [b5])
theorem hb6 (hp : Placed code k) :
    b6a.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b6Offset) ∧ b6b.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.ProdE.b6Offset + 2) := by
  have h := b6_in_code.trans hp.1 (by simp [b6])
  rw [← List.take_append_drop 2 b6] at h
  exact h.append

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ProdE.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.ProdE.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ProdE.entryOffset) NativeRustcVmArm.Vm.ProdE.entry_at
theorem lbl_2 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ProdE.label_2 = Host.addrOf (k + NativeRustcVmArm.Vm.ProdE.b5Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ProdE.b5Offset) NativeRustcVmArm.Vm.ProdE.label_2_at
theorem lbl_3 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.ProdE.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.ProdE.b6Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.ProdE.b6Offset) NativeRustcVmArm.Vm.ProdE.label_3_at

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ ProdEPost m0 s.data

/-- The body's invariant after `i` values: the frame, the slice in X19, X20, the product in X0,
X1. -/
structure Inv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  body : Body m0 32 prodEStack slots 0 0 s
  x19 : s.regs.X19 = m0.regs.X0
  x20 : s.regs.X20 = m0.regs.X1
  acc : (⟨s.regs.X0, s.regs.X1⟩ : EW) = acc m0 i

/-- **The epilogue** `b5`: the product returned. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hS : StackOk m0 prodEStack)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ProdE.b5Offset)) (hI : Inv m0 (len m0) s.data) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨hwf, hm⟩ := hI.body.exit_match hS (by decide) rfl
  refine exec_at (hb5 hp) run_b5 hwf hpc hm fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := hI.body.saved hm' hwf
    (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩) (after_eq run_b5 ▸ b5_restores) rfl
  have h0 := hm'.regs .X0 _ rfl
  have h1 := hm'.regs .X1 _ rfl
  simp only [Sym.eval, Env.ofMachine_regs] at h0 h1
  refine ⟨?_, ?_, ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · rw [prodE_eq_acc, ← hI.acc]
    show (⟨s'.data.regs.getXReg .X0, s'.data.regs.getXReg .X1⟩ : EW) = _
    rw [UInt64.toBitVec_inj.mp h0, UInt64.toBitVec_inj.mp h1]
    rfl
  · intro p hp'
    rw [hdm]
    exact hI.body.same p hp'

/-- **A value multiplied in** (`b1`, `b3`): `values[i]` loaded through X19, `EW::mul`. -/
theorem mul_step (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {m0 : MachineData}
    (hpre : ProdEPre m0) {ds : List Directive} {kk : Nat} {o : Int} {S' : SState}
    (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds (ldS .X19 o) = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hlo : S'.reg .X2 = some (.load 0 0 8)) (hhi : S'.reg .X3 = some (.load 0 8 8))
    (hkeep : keepsAll (ldS .X19 o) S' keptRegs = true)
    (hrs : ([XReg.X0, .X1, .X19, .X20].all fun q ↦ ((ldS .X19 o).reg q).isSome &&
      S'.reg q == (ldS .X19 o).reg q) = true)
    {i : Nat} (hi : i < len m0)
    (ho : m0.regs.X0.toBitVec = m0.regs.X0.toBitVec + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 o)
    {s : MachineState} (hpc : s.pc = Host.addrOf kk) (hI : Inv m0 i s.data)
    {R : MachineState → Prop}
    (cont : ∀ s', s'.pc = Host.addrOf (kk + ds.length) → Inv m0 (i + 1) s'.data →
      Eventually (step1 Host.exe) R s') :
    Eventually (step1 Host.exe) R s := by
  obtain ⟨hS, -, -, hrV, hoV⟩ := hpre
  obtain ⟨s, pc⟩ := s
  refine load_step (lo := .X2) (hi' := .X3) hk hx hlo hhi hkeep _ hrs hI.body hS hrV hoV
    (apart_zero _ _) noWrap_zero (show i < m0.regs.X1.toNat from hi) hpc
    (by show s.regs.X19.toBitVec = _; rw [hI.x19]; exact ho)
    fun s2 hm2 hpc2 bd2 hR e2 ↦ ?_
  refine call_then hpc2 hmul (bd2.ewMulPre hS (by decide) (by decide)) fun s3 hpc3 hpost3 ↦
    cont s3 hpc3 ⟨bd2.call hS (by decide) (by decide) hpost3, ?_, ?_, ?_⟩
  · show s3.data.regs.getXReg .X19 = _
    rw [hpost3.2.2.2.1 .X19 rfl, e2 .X19 (by simp)]; exact hI.x19
  · show s3.data.regs.getXReg .X20 = _
    rw [hpost3.2.2.2.1 .X20 rfl, e2 .X20 (by simp)]; exact hI.x20
  · rw [hpost3.1, hpost3.2.1, acc_succ m0 hi, ← hI.acc, ← hR]
    show EW.mul ⟨s2.data.regs.getXReg .X0, s2.data.regs.getXReg .X1⟩ _ = _
    rw [e2 .X0 (by simp), e2 .X1 (by simp)]
    rfl

omit [Host] in
theorem ofInt_neg (a : BitVec 64) (c : Nat) (hc : c < 2 ^ 63) :
    a = a + BitVec.ofNat 64 c + BitVec.ofInt 64 (-(c : Int)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have := a.isLt
  have e : ((-(c : Int)) % ((2 ^ 64 : Nat) : Int)).toNat = (2 ^ 64 - c) % 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · simp
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  rw [e]
  omega

/-- **`prod_e` meets its contract.** -/
theorem prodE_spec (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.ProdE.entryLabel) ProdEPre ProdEPost := by
  intro m0 hpre
  rw [lbl_entry hp]
  have hpre' := hpre
  obtain ⟨hS, h2, h4, hrV, hoV⟩ := hpre
  have h32 : 32 ≤ prodEStack := by decide
  have hL : len m0 = m0.regs.X1.toNat := rfl
  obtain ⟨hwf, hm⟩ := entry_match hS h32 rfl
  refine exec_then (hb0 hp).1 run_b0a hwf hm fun s1 hm1 hpc1 ↦ ?_
  simp only [PcOk, show b0a.length = 3 from rfl] at hpc1
  obtain ⟨hw, hmem, hregs⟩ := after_eq run_b0a ▸ b0a_frame
  have bd1 : Body m0 32 prodEStack slots 0 0 s1.data := Body.of_entry hS h32 hm1 rfl hw hregs hmem
  have e1 : ∀ r ∈ [XReg.X0, .X1], s1.data.regs.getXReg r = m0.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  -- `1·values[0]`
  obtain ⟨s1, pc1⟩ := s1
  refine load_step (lo := .X2) (hi' := .X3) (i := 0) (hb0 hp).2 run_b0b rfl rfl
    (after_eq run_b0b ▸ b0b_facts.1) _ (after_eq run_b0b ▸ b0b_facts.2) bd1 hS hrV hoV
    (apart_zero _ _) noWrap_zero (show 0 < m0.regs.X1.toNat by omega) hpc1
    (by
      show (s1.regs.getXReg .X0).toBitVec = _
      rw [e1 .X0 (by simp)]
      show m0.regs.X0.toBitVec = _
      simp)
    fun s2 hm2 hpc2 bd2 hR _ ↦ ?_
  have h0 := hm2.regs .X0 _ rfl
  have h1 := hm2.regs .X1 _ rfl
  have h19 := hm2.regs .X19 _ rfl
  have h20 := hm2.regs .X20 _ rfl
  sym_simp at h0 h1 h19 h20
  simp only [Env.ofMachine_regs] at h19 h20
  refine call_then hpc2 hmul (bd2.ewMulPre hS (by decide) (by decide)) fun s3 hpc3 hpost3 ↦ ?_
  have hI1 : Inv m0 1 s3.data := by
    refine ⟨bd2.call hS (by decide) (by decide) hpost3, ?_, ?_, ?_⟩
    · show s3.data.regs.getXReg .X19 = _
      rw [hpost3.2.2.2.1 .X19 rfl]
      apply UInt64.toBitVec_inj.mp
      rw [h19]
      simp
    · show s3.data.regs.getXReg .X20 = _
      rw [hpost3.2.2.2.1 .X20 rfl, toBitVec_eq h20, UInt64.ofBitVec_toBitVec, e1 .X1 (by simp)]
      rfl
    · rw [hpost3.1, hpost3.2.1, acc_succ m0 (by omega), ← hR]
      show EW.mul ⟨s2.data.regs.getXReg .X0, s2.data.regs.getXReg .X1⟩ _ = _ * _
      rw [toBitVec_eq h0, toBitVec_eq h1]
      rfl
  -- `values[1]`
  refine mul_step hmul hpre' (hb1 hp) run_b1 rfl rfl (after_eq run_b1 ▸ b1_facts.1)
    (after_eq run_b1 ▸ b1_facts.2) (i := 1) (by omega) (ofInt_neg _ 16 (by decide)) hpc3 hI1
    fun s4 hpc4 hI2 ↦ ?_
  simp only [NativeRustcVmArm.Vm.ProdE.b1_length, NativeRustcVmArm.Vm.ProdE.b1Length] at hpc4
  -- `len = 2`?
  refine exec_at (hb2 hp) run_b2 (Env.wf_nil _) hpc4 (match_nil _) fun s5 hm5 hpc5 ↦ ?_
  have bd5 := hI2.body.of_block (match_nil _) hm5 (Env.wf_nil _) rfl (after_eq run_b2 ▸ b2_keeps)
  have e5 : ∀ r, s5.data.regs.getXReg r = s4.data.regs.getXReg r := fun r ↦ by
    cases r <;> exact Match.reg_eq (match_nil _) hm5 rfl rfl
  have hI2' : Inv m0 2 s5.data := ⟨bd5, (e5 .X19).trans hI2.x19, (e5 .X20).trans hI2.x20,
    by show (⟨s5.data.regs.getXReg .X0, s5.data.regs.getXReg .X1⟩ : EW) = _
       rw [e5, e5]; exact hI2.acc⟩
  have hx20 : (s4.data.regs.getXReg .X20).toBitVec.toNat = len m0 := congrArg UInt64.toNat hI2.x20
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  have hpc5' := pc_cond hpc5
  by_cases hl2 : len m0 = 2
  · refine finish hp hS ((hpc5'.1 ?_).trans (lbl_2 hp)) (hl2 ▸ hI2')
    show ((s4.data.regs.getXReg .X20).toBitVec == BitVec.ofNat 64 2) = true
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [hx20, hl2]; rfl
  have hpc5 := hpc5'.2 (by
    show ¬((s4.data.regs.getXReg .X20).toBitVec == BitVec.ofNat 64 2) = true
    rw [beq_iff_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [hx20] at this
    exact hl2 this)
  simp only [NativeRustcVmArm.Vm.ProdE.b2_length, NativeRustcVmArm.Vm.ProdE.b2Length] at hpc5
  -- `values[2]`
  refine mul_step hmul hpre' (hb3 hp) run_b3 rfl rfl (after_eq run_b3 ▸ b3_facts.1)
    (after_eq run_b3 ▸ b3_facts.2) (i := 2) (by omega) (ofInt_neg _ 32 (by decide)) hpc5 hI2'
    fun s6 hpc6 hI3 ↦ ?_
  simp only [NativeRustcVmArm.Vm.ProdE.b3_length, NativeRustcVmArm.Vm.ProdE.b3Length] at hpc6
  -- `len = 3`?
  refine exec_at (hb4 hp) run_b4 (Env.wf_nil _) hpc6 (match_nil _) fun s7 hm7 hpc7 ↦ ?_
  have bd7 := hI3.body.of_block (match_nil _) hm7 (Env.wf_nil _) rfl (after_eq run_b4 ▸ b4_keeps)
  have e7 : ∀ r, s7.data.regs.getXReg r = s6.data.regs.getXReg r := fun r ↦ by
    cases r <;> exact Match.reg_eq (match_nil _) hm7 rfl rfl
  have hI3' : Inv m0 3 s7.data := ⟨bd7, (e7 .X19).trans hI3.x19, (e7 .X20).trans hI3.x20,
    by show (⟨s7.data.regs.getXReg .X0, s7.data.regs.getXReg .X1⟩ : EW) = _
       rw [e7, e7]; exact hI3.acc⟩
  have hx20' : ((Env.ofMachine s6.data []).regs XReg.X20).toNat = len m0 :=
    congrArg UInt64.toNat hI3.x20
  simp only [PcOk] at hpc7
  sym_simp at hpc7
  have hpc7' := pc_ne hpc7
  by_cases hl3 : len m0 = 3
  · refine finish hp hS ?_ (hl3 ▸ hI3')
    have := hpc7'.2 (by
      apply BitVec.eq_of_toNat_eq
      rw [hx20', hl3]; rfl)
    simp only [NativeRustcVmArm.Vm.ProdE.b4_length, NativeRustcVmArm.Vm.ProdE.b4Length] at this
    exact this
  have hpc7 := (hpc7'.1 fun h ↦ hl3 (by
    have := congrArg BitVec.toNat h
    rw [hx20'] at this
    exact this)).trans (lbl_3 hp)
  have hl4 : len m0 = 4 := by omega
  -- `values[3]`, the tail call
  obtain ⟨s7, pc7⟩ := s7
  refine load_step (lo := .X2) (hi' := .X3) (i := 3) (hb6 hp).1 run_b6a rfl rfl
    (after_eq run_b6a ▸ b6a_facts.1) _ (after_eq run_b6a ▸ b6a_facts.2) bd7 hS hrV hoV
    (apart_zero _ _) noWrap_zero (show 3 < m0.regs.X1.toNat by omega) hpc7
    (by show s7.regs.X19.toBitVec = _; rw [hI3'.x19]; exact ofInt_neg _ 48 (by decide))
    fun s8 hm8 hpc8 bd8 hR e8 ↦ ?_
  simp only [PcOk, show b6a.length = 2 from rfl] at hpc8
  obtain ⟨hwf9, hm9⟩ := bd8.exit_match hS (by decide) rfl
  refine exec_at (hb6 hp).2 run_b6b hwf9 hpc8 hm9 fun s9 hm9' hpc9 ↦ ?_
  obtain ⟨hsaved, hx30, hdm⟩ := bd8.saved hm9' hwf9
    (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩) (after_eq run_b6b ▸ b6b_restores) rfl
  simp only [PcOk] at hpc9
  obtain ⟨s9, pc9⟩ := s9
  simp only at hpc9 hsaved hx30 hdm
  have hc : Changes m0 s9 prodEStack 0 0 := fun p hp' ↦ by rw [hdm]; exact bd8.same p hp'
  refine Eventually.mono (tail_mul hmul hS (by decide) hsaved hx30 hc hpc9)
    fun r ⟨hr1, hr2, hr3, hr4⟩ ↦ ⟨hr1, ?_, hr3, hr4⟩
  show (⟨r.data.regs.X0, r.data.regs.X1⟩ : EW) = _
  rw [hr2, prodE_eq_acc, hl4, acc_succ m0 (by omega), ← hI3'.acc, ← hR]
  have q0 := hm9'.regs .X0 _ rfl
  have q1 := hm9'.regs .X1 _ rfl
  have q2 := hm9'.regs .X2 _ rfl
  have q3 := hm9'.regs .X3 _ rfl
  simp only [Sym.eval, Env.ofMachine_regs] at q0 q1 q2 q3
  show EW.mul ⟨s9.regs.getXReg .X0, s9.regs.getXReg .X1⟩ ⟨s9.regs.getXReg .X2, s9.regs.getXReg .X3⟩ = _
  rw [UInt64.toBitVec_inj.mp q0, UInt64.toBitVec_inj.mp q1, UInt64.toBitVec_inj.mp q2,
    UInt64.toBitVec_inj.mp q3, e8 .X0 (by simp), e8 .X1 (by simp)]
  rfl

end

end NativeRustcVmArm.Arrays.ProdE
