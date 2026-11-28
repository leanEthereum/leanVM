module

public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Arrays.SumE.Exec
public import NativeRustcVm.Arrays.Folds

/-!
# `sum_e` on AArch64

**`sumE_spec`**: rustc's `sum_e(values)`, placed anywhere in the program, meets
`SumEPre`/`SumEPost`. No stack, no memory written, no callee-saved register touched (`Base`).
`E` addition is the lanes' `xor`. At `len = 0` it returns `0` (`b3`); below `4` the tail loop
(`b9`, `b10`: `TInv`) adds every element; from `4` on (`len ≤ 16`) the unrolled blocks (`b4`-`b7`)
`xor` four elements each into four pairs of lane accumulators (`UInv`: the four accumulators of a
lane `xor` to the lane of the sum so far) for the `len & 28 = 4·⌊len/4⌋` first elements, `b8`
combines them, and the tail loop adds the rest; `b11` returns.
-/

namespace NativeRustcVmArm.Arrays.SumE

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SumE NativeVm.Model
open NativeRustcVm (ewsOf ewOf wordOf)

public section

/-- The values' address. -/
abbrev addr (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec
/-- Their number. -/
abbrev len (m : MachineData) : Nat := m.regs.X1.toNat
/-- The values at the entry. -/
abbrev xs (m : MachineData) : List EW := ewsOf m.dmem (addr m) (len m)

/-- The sum of the first `i` values. -/
def acc (m : MachineData) (i : Nat) : EW := ((xs m).take i).foldl (· + ·) 0

theorem sumE_eq_acc (m : MachineData) : sumE (slice m m.regs.X0 m.regs.X1) = acc m (len m) := by
  unfold slice acc
  rw [NativeRustcVm.sumE_eq, List.take_of_length_le (by simp)]

theorem lt_len {m : MachineData} {i : Nat} (h : i < len m) : i < (xs m).length := by
  simp only [xs, len, NativeRustcVm.length_ewsOf] at h ⊢; exact h

theorem acc_succ (m : MachineData) {i : Nat} (h : i < len m) :
    acc m (i + 1) = acc m i + (xs m)[i]'(lt_len h) :=
  NativeRustcVm.foldl_take_succ _ _ _ _

/-- The low lane of a sum. -/
theorem c0_add (a b : EW) : (a + b).c0.toBitVec = a.c0.toBitVec ^^^ b.c0.toBitVec := rfl
/-- The high lane of a sum. -/
theorem c1_add (a b : EW) : (a + b).c1.toBitVec = a.c1.toBitVec ^^^ b.c1.toBitVec := rfl

theorem elem_c0 (m : MachineData) {k : Nat} (h : k < len m) :
    ((xs m)[k]'(lt_len h)).c0.toBitVec =
      (wordOf m.dmem (addr m + BitVec.ofNat 64 (16 * k))).toBitVec := by
  rw [NativeRustcVm.getElem_ewsOf]; rfl

theorem elem_c1 (m : MachineData) {k : Nat} (h : k < len m) :
    ((xs m)[k]'(lt_len h)).c1.toBitVec =
      (wordOf m.dmem (addr m + BitVec.ofNat 64 (16 * k + 8))).toBitVec := by
  rw [NativeRustcVm.getElem_ewsOf, ← NativeRustcVm.addr_add]; rfl

/-- What every block keeps: the arguments, X30, the saved registers, memory. -/
structure Base (m0 s : MachineData) : Prop where
  x0 : s.regs.X0 = m0.regs.X0
  x1 : s.regs.X1 = m0.regs.X1
  x30 : s.regs.X30 = m0.regs.X30
  saved : Saved m0 s
  dmem : s.dmem = m0.dmem

theorem Base.step [Labels] {m0 s s' : MachineData} {env : Env} {S₀ S₁ : SState}
    (hb : Base m0 s) (hm₀ : Match env S₀ s) (hm : Match env S₁ s') (hwf : env.WF)
    (hd : s.dmem = env.mem0) (hk : keepsAll S₀ S₁ keptRegs = true) : Base m0 s' := by
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk
  obtain ⟨⟨hr, hsp⟩, hmem⟩ := hk
  have e : ∀ r ∈ keptRegs, s'.regs.getXReg r = s.regs.getXReg r := fun r hr' ↦ by
    obtain ⟨hs, he⟩ := hr r hr'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq hm₀ hm hv (he.trans hv)
  have hdm : s'.dmem = s.dmem := (hm.dmem_eq hwf hmem).trans hd.symm
  exact ⟨(e .X0 (by simp [keptRegs])).trans hb.x0, (e .X1 (by simp [keptRegs])).trans hb.x1,
    (e .X30 (by simp [keptRegs])).trans hb.x30,
    hb.saved.trans ⟨fun r hr ↦ e r (List.mem_append_left _ (mem_calleeRegs hr)),
      Match.sp_eq hm₀ hm hsp, by rw [hdm]; exact fun _ h ↦ h⟩, hdm.trans hb.dmem⟩

/-- A block of registers only from a base. -/
theorem Base.regs [Labels] {m0 s s' : MachineData} {S₁ : SState} (hb : Base m0 s)
    (hm : Match (Env.ofMachine s []) S₁ s') (hk : keepsAll regsS S₁ keptRegs = true) :
    Base m0 s' :=
  hb.step (match_nil _) hm (Env.wf_nil _) rfl hk

theorem Base.entry (m0 : MachineData) : Base m0 m0 :=
  ⟨rfl, rfl, rfl, Saved.refl _, rfl⟩

variable [Host] {k : Nat}

theorem hb (hp : Placed code k) {b : List Directive} {j : Nat} (hj : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hj.trans hp.1 hne

/-- The postcondition, reached. -/
abbrev Post (m0 : MachineData) (s : MachineState) : Prop :=
  s.pc = retOf m0 ∧ SumEPost m0 s.data

/-- **A return** (`b11`, `b3`): X0, X1 the sum's lanes. -/
theorem ret_of {b : List Directive} {kb : Nat} {S : SState} (hk : b.IsInfixAt Host.prog kb)
    (hx : exec b regsS = some (S, .ret)) {v0 v1 : Sym} (h0 : S.reg .X0 = some v0)
    (h1 : S.reg .X1 = some v1) (hkeep : keepsAll regsS S retRegs = true)
    {m0 : MachineData} {s : MachineState} (hpc : s.pc = Host.addrOf kb) (hB : Base m0 s.data)
    (hv : (⟨UInt64.ofBitVec (v0.eval (Env.ofMachine s.data [])),
      UInt64.ofBitVec (v1.eval (Env.ofMachine s.data []))⟩ : EW) = acc m0 (len m0)) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine exec_at hk hx (Env.wf_nil _) hpc (match_nil _) fun s' hm' hpc' ↦ .done _ ?_
  have hk' := hkeep
  simp only [keepsAll, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.isEmpty_iff] at hk'
  obtain ⟨⟨hr, hsp⟩, hmem⟩ := hk'
  have e : ∀ r ∈ retRegs, s'.data.regs.getXReg r = s.data.regs.getXReg r := fun r hr' ↦ by
    obtain ⟨hs, he⟩ := hr r hr'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Match.reg_eq (match_nil _) hm' hv (he.trans hv)
  have hdm : s'.data.dmem = s.data.dmem := hm'.dmem_eq (Env.wf_nil _) hmem
  refine ⟨?_, ?_, fun p _ ↦ by rw [hdm, hB.dmem], hB.saved.trans ⟨fun r hr ↦
    e r (List.mem_append_left _ (mem_calleeRegs hr)), Match.sp_eq (match_nil _) hm' hsp,
    by rw [hdm]; exact fun _ h ↦ h⟩⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf]
    rw [show s'.data.regs.X30 = s.data.regs.X30 from e .X30 (by simp [retRegs]), hB.x30]
  · rw [sumE_eq_acc, ← hv]
    show (⟨s'.data.regs.getXReg .X0, s'.data.regs.getXReg .X1⟩ : EW) = _
    rw [toBitVec_eq (hm'.regs .X0 _ h0), toBitVec_eq (hm'.regs .X1 _ h1)]

/-- **The tail loop's head** `.LSumE_10`, `i` values added. -/
structure TInv (m0 : MachineData) (i : Nat) (s : MachineData) : Prop where
  base : Base m0 s
  lt : i < len m0
  x10 : s.regs.X10.toNat = len m0 - i
  x11 : s.regs.X11.toBitVec = addr m0 + BitVec.ofNat 64 (16 * i + 8)
  acc : (⟨s.regs.X9, s.regs.X8⟩ : EW) = acc m0 i

/-- **The tail loop** `b10`, then the return `b11`. -/
theorem tail (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) {i : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumE.b10Offset)) (hI : TInv m0 i s.data) :
    Eventually (step1 Host.exe) (Post m0) s := by
  obtain ⟨h16, hrV⟩ := hpre
  refine Sym.loop (fun n s ↦ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumE.b10Offset) ∧ ∃ i, len m0 - i = n ∧ TInv m0 i s.data)
    (fun n s ⟨hpc, i, hn, hI⟩ ↦ ?_) ⟨hpc, i, rfl, hI⟩
  have hlt := hI.lt
  have hL : len m0 = m0.regs.X1.toNat := rfl
  obtain ⟨hmA, hnA⟩ := elem_mapped hrV (by rw [hI.base.dmem]; exact fun _ h ↦ h) hlt
  have hwf := wf_one hmA hnA (m := s.data)
  have hm : Match (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * i), 16)]) tailS s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show s.data.regs.X11.toBitVec = _ + BitVec.ofInt 64 8
        rw [hI.x11, base0, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl,
          NativeRustcVm.addr_add],
       trivial⟩ trivial trivial trivial
  refine exec_at (hb hp b10_in_code (by simp [b10])) run_b10 hwf hpc hm fun s' hm' hpc' ↦ ?_
  have hB := hI.base.step hm hm' hwf rfl (after_eq run_b10 ▸ b10_keeps)
  have hE := ewOf_loads (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 (16 * i), 16)]) 0 0
  simp only [Env.ofMachine_mem0, base0, add_ofNat_zero, Nat.zero_add] at hE
  rw [hI.base.dmem, ← NativeRustcVm.getElem_ewsOf (h := lt_len hlt)] at hE
  have hacc : (⟨s'.data.regs.X9, s'.data.regs.X8⟩ : EW) = acc m0 (i + 1) := by
    rw [acc_succ m0 hlt, ← hI.acc, hE]
    have h9 := hm'.regs .X9 _ rfl
    have h8 := hm'.regs .X8 _ rfl
    sym_simp at h9 h8
    simp only [Env.ofMachine_regs] at h9 h8
    show (⟨s'.data.regs.getXReg .X9, s'.data.regs.getXReg .X8⟩ : EW) = _
    rw [toBitVec_eq h9, toBitVec_eq h8]
    show (⟨_, _⟩ : EW) = ⟨_ ^^^ _, _ ^^^ _⟩
    congr 1 <;> apply UInt64.toBitVec_inj.mp <;> simp only [UInt64.toBitVec_xor] <;>
      exact BitVec.xor_comm _ _
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  have hpc'' := pc_cond hpc'
  have hx10 : (s.data.regs.getXReg .X10).toNat = len m0 - i := hI.x10
  by_cases hM : i + 1 < len m0
  · refine .done _ (Or.inr ⟨len m0 - (i + 1), by omega, ?_, i + 1, rfl, hB, hM, ?_, ?_, hacc⟩)
    · refine (hpc''.1 ?_).trans (hp.label (j := NativeRustcVmArm.Vm.SumE.b10Offset) NativeRustcVmArm.Vm.SumE.label_10_at)
      show (!((s.data.regs.getXReg .X10).toBitVec == 1#64)) = true
      rw [Bool.not_eq_true', beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      rw [UInt64.toNat_toBitVec, hx10] at this
      simp at this
      omega
    · show (s'.data.regs.getXReg .X10).toNat = _
      have h := hm'.regs .X10 _ rfl
      sym_simp at h
      simp only [Env.ofMachine_regs] at h
      rw [← UInt64.toNat_toBitVec, h, BitVec.toNat_sub]
      simp only [UInt64.toNat_toBitVec, BitVec.toNat_ofNat, hx10]
      omega
    · show (s'.data.regs.getXReg .X11).toBitVec = _
      rw [hm'.regs .X11 _ rfl]
      show addr m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 24 = _
      rw [show BitVec.ofInt 64 24 = BitVec.ofNat 64 24 from rfl, NativeRustcVm.addr_add,
        show 16 * i + 24 = 16 * (i + 1) + 8 by omega]
  · have hpc2 := hpc''.2 ?_
    · refine Eventually.mono (ret_of (hb hp b11_in_code (by simp [b11])) run_b11 rfl rfl
        (after_eq run_b11 ▸ b11_keeps) hpc2 hB ?_) fun s h ↦ Or.inl h
      rw [show len m0 = i + 1 by omega, ← hacc]
      rfl
    · show ¬(!((s.data.regs.getXReg .X10).toBitVec == 1#64)) = true
      rw [Bool.not_eq_true', Bool.not_eq_false, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [UInt64.toNat_toBitVec, hx10]
      simp
      omega


/-- **`.LSumE_9`** (`b9`): the tail from value `i`, then the return. -/
theorem fromL9 (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) {i : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumE.b9Offset)) (hB : Base m0 s.data)
    (hlt : i < len m0) (hx10 : s.data.regs.X10.toNat = i)
    (hacc : (⟨s.data.regs.X9, s.data.regs.X8⟩ : EW) = acc m0 i) :
    Eventually (step1 Host.exe) (Post m0) s := by
  have hrV := hpre.2
  have hnw : (addr m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hrV.2
  refine exec_at (hb hp b9_in_code (by simp [b9])) run_b9 (Env.wf_nil _) hpc (match_nil _)
    fun s' hm' hpc' ↦ ?_
  have hB' := hB.regs hm' (after_eq run_b9 ▸ b9_keeps)
  have e : ∀ r ∈ [XReg.X8, .X9], s'.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Match.reg_eq (match_nil _) hm' rfl rfl
  simp only [PcOk] at hpc'
  refine tail hp hpre hpc' ⟨hB', hlt, ?_, ?_, ?_⟩
  · show (s'.data.regs.getXReg .X10).toNat = _
    have h := hm'.regs .X10 _ rfl
    sym_simp at h
    simp only [Env.ofMachine_regs] at h
    rw [← UInt64.toNat_toBitVec, h, BitVec.toNat_sub]
    have h1 : (s.data.regs.getXReg .X1).toBitVec.toNat = len m0 := by
      show s.data.regs.X1.toBitVec.toNat = _; rw [hB.x1]; rfl
    have h10 : (s.data.regs.getXReg .X10).toBitVec.toNat = i := hx10
    rw [h1, h10]
    omega
  · show (s'.data.regs.getXReg .X11).toBitVec = _
    have h := hm'.regs .X11 _ rfl
    simp only [Sym.eval, UnOp.apply, shiftW, Sym.ext_W64, Sym.low_W64, shl4, BinOp.apply,
      Env.ofMachine_regs] at h
    rw [h]
    have h0 : (s.data.regs.getXReg .X0).toBitVec = addr m0 := by
      show s.data.regs.X0.toBitVec = _; rw [hB.x0]
    have h10 : (s.data.regs.getXReg .X10).toBitVec.toNat = i := hx10
    rw [h0, h10, show BitVec.ofNat 64 8 = BitVec.ofNat 64 8 from rfl, NativeRustcVm.addr_add]
  · show (⟨s'.data.regs.getXReg .X9, s'.data.regs.getXReg .X8⟩ : EW) = _
    rw [e .X9 (by simp), e .X8 (by simp)]
    exact hacc

/-- The unrolled loop's state after `t` blocks: the four accumulators of each lane `xor` to the
lane of the sum of the first `4·t` values. -/
structure UInv (m0 : MachineData) (t : Nat) (s : MachineData) : Prop where
  base : Base m0 s
  x10 : s.regs.X10.toNat = 4 * (len m0 / 4)
  le : 4 * t ≤ len m0
  lo : s.regs.X8.toBitVec ^^^ s.regs.X9.toBitVec ^^^ s.regs.X11.toBitVec ^^^ s.regs.X13.toBitVec =
    (acc m0 (4 * t)).c0.toBitVec
  hi : s.regs.X12.toBitVec ^^^ s.regs.X14.toBitVec ^^^ s.regs.X15.toBitVec ^^^
    s.regs.X16.toBitVec = (acc m0 (4 * t)).c1.toBitVec

/-- **`.LSumE_8`** (`b8`): the lanes combined, then the return or the tail. -/
theorem fromL8 (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) {t : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumE.b8Offset)) (hI : UInv m0 t s.data)
    (hx : s.data.regs.X10.toNat = 4 * t) :
    Eventually (step1 Host.exe) (Post m0) s := by
  refine exec_at (hb hp b8_in_code (by simp [b8])) run_b8 (Env.wf_nil _) hpc (match_nil _)
    fun s' hm' hpc' ↦ ?_
  have hB' := hI.base.regs hm' (after_eq run_b8 ▸ b8_keeps)
  have hacc : (⟨s'.data.regs.X9, s'.data.regs.X8⟩ : EW) = acc m0 (4 * t) := by
    have h9 := hm'.regs .X9 _ rfl
    have h8 := hm'.regs .X8 _ rfl
    sym_simp at h9 h8
    simp only [Env.ofMachine_regs] at h9 h8
    show (⟨s'.data.regs.getXReg .X9, s'.data.regs.getXReg .X8⟩ : EW) = _
    rw [toBitVec_eq h9, toBitVec_eq h8]
    have lo := hI.lo
    have hi := hI.hi
    show (⟨_, _⟩ : EW) = ⟨(acc m0 (4 * t)).c0, (acc m0 (4 * t)).c1⟩
    congr 1
    · apply UInt64.toBitVec_inj.mp
      rw [UInt64.toBitVec_ofBitVec, ← lo]
      show _ = (s.data.regs.getXReg .X8).toBitVec ^^^ (s.data.regs.getXReg .X9).toBitVec ^^^
        (s.data.regs.getXReg .X11).toBitVec ^^^ (s.data.regs.getXReg .X13).toBitVec
      ac_rfl
    · apply UInt64.toBitVec_inj.mp
      rw [UInt64.toBitVec_ofBitVec, ← hi]
      show _ = (s.data.regs.getXReg .X12).toBitVec ^^^ (s.data.regs.getXReg .X14).toBitVec ^^^
        (s.data.regs.getXReg .X15).toBitVec ^^^ (s.data.regs.getXReg .X16).toBitVec
      ac_rfl
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  have hpc'' := pc_cond hpc'
  have h1 : (s.data.regs.getXReg .X1).toBitVec.toNat = len m0 := by
    show s.data.regs.X1.toBitVec.toNat = _; rw [hI.base.x1]; rfl
  have h10 : (s.data.regs.getXReg .X10).toBitVec.toNat = 4 * t := hx
  by_cases hE : len m0 = 4 * t
  · refine ret_of (hb hp b11_in_code (by simp [b11])) run_b11 rfl rfl
      (after_eq run_b11 ▸ b11_keeps) ((hpc''.1 ?_).trans (hp.label (j := NativeRustcVmArm.Vm.SumE.b11Offset) NativeRustcVmArm.Vm.SumE.label_11_at)) hB' ?_
    · show ((s.data.regs.getXReg .X1).toBitVec == (s.data.regs.getXReg .X10).toBitVec) = true
      rw [beq_iff_eq]
      apply BitVec.eq_of_toNat_eq
      rw [h1, h10, hE]
    · rw [hE, ← hacc]; rfl
  · have hpc2 := hpc''.2 (by
      show ¬((s.data.regs.getXReg .X1).toBitVec == (s.data.regs.getXReg .X10).toBitVec) = true
      rw [beq_iff_eq]
      intro h
      have := congrArg BitVec.toNat h
      rw [h1, h10] at this
      exact hE this)
    exact fromL9 hp hpre hpc2 hB' (by have := hI.le; omega)
      (by show (s'.data.regs.getXReg .X10).toNat = _
          rw [Match.reg_eq (match_nil _) hm' rfl rfl]; exact hx) hacc

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

omit [Host] in
/-- A word of an unrolled block's region is a lane of a value. -/
theorem load_c0 {m0 s : MachineData} (hd : s.dmem = m0.dmem) {o off i : Nat}
    (h : o + off = 16 * i) (hi : i < len m0) :
    (Env.ofMachine s [(addr m0 + BitVec.ofNat 64 o, 64)]).load 0 off 8 =
      ((xs m0)[i]'(lt_len hi)).c0.toBitVec := by
  rw [load8_eq, elem_c0 m0 hi]
  simp only [Env.ofMachine_mem0, base0, hd, NativeRustcVm.addr_add, h]

omit [Host] in
theorem load_c1 {m0 s : MachineData} (hd : s.dmem = m0.dmem) {o off i : Nat}
    (h : o + off = 16 * i + 8) (hi : i < len m0) :
    (Env.ofMachine s [(addr m0 + BitVec.ofNat 64 o, 64)]).load 0 off 8 =
      ((xs m0)[i]'(lt_len hi)).c1.toBitVec := by
  rw [load8_eq, elem_c1 m0 hi]
  simp only [Env.ofMachine_mem0, base0, hd, NativeRustcVm.addr_add, h]

omit [Host] in
theorem acc4 (m0 : MachineData) (t : Nat) (h : 4 * t + 4 ≤ len m0) :
    acc m0 (4 * (t + 1)) = acc m0 (4 * t) + (xs m0)[4 * t]'(lt_len (by omega)) +
      (xs m0)[4 * t + 1]'(lt_len (by omega)) + (xs m0)[4 * t + 1 + 1]'(lt_len (by omega)) +
      (xs m0)[4 * t + 1 + 1 + 1]'(lt_len (by omega)) := by
  rw [show 4 * (t + 1) = 4 * t + 1 + 1 + 1 + 1 by omega, acc_succ m0 (by omega),
    acc_succ m0 (by omega), acc_succ m0 (by omega), acc_succ m0 (by omega)]

/-- **An unrolled block** (`b5`-`b7`): four more values `xor`ed into the accumulators. -/
theorem ublock {m0 : MachineData} (hpre : SumEPre m0) {ds : List Directive}
    {kk : Nat} {o t : Nat} {S' : SState} {x : Exit} (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds (blkS (-(o : Int))) = some (S', x))
    (g : S'.reg .X8 = some (.bin .eor .W64 (.load 0 0 8) (.reg .X8)) ∧
      S'.reg .X12 = some (.bin .eor .W64 (.load 0 8 8) (.reg .X12)) ∧
      S'.reg .X9 = some (.bin .eor .W64 (.load 0 16 8) (.reg .X9)) ∧
      S'.reg .X14 = some (.bin .eor .W64 (.load 0 24 8) (.reg .X14)) ∧
      S'.reg .X11 = some (.bin .eor .W64 (.load 0 32 8) (.reg .X11)) ∧
      S'.reg .X15 = some (.bin .eor .W64 (.load 0 40 8) (.reg .X15)) ∧
      S'.reg .X13 = some (.bin .eor .W64 (.load 0 48 8) (.reg .X13)) ∧
      S'.reg .X16 = some (.bin .eor .W64 (.load 0 56 8) (.reg .X16)) ∧
      S'.reg .X10 = some (.reg .X10))
    (hkeep : keepsAll (blkS (-(o : Int))) S' keptRegs = true) (ho : o = 64 * t)
    (hle : 4 * t + 4 ≤ len m0) {s : MachineState} (hpc : s.pc = Host.addrOf kk)
    (hI : UInv m0 t s.data) {R : MachineState → Prop}
    (cont : ∀ s', PcOk (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 o, 64)]) x
      (Host.addrOf (kk + ds.length)) s' → UInv m0 (t + 1) s'.data → Eventually (step1 Host.exe) R s') :
    Eventually (step1 Host.exe) R s := by
  have hrV := hpre.2
  have hnw : (addr m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hrV.2
  have hB := hI.base
  have aL : m0.regs.X1.toNat = len m0 := rfl
  have hmA : Mapped s.data.dmem (addr m0 + BitVec.ofNat 64 o) 64 := fun j hj ↦ by
    rw [NativeRustcVm.addr_add, hB.dmem]; exact hrV.1 _ (by omega)
  have hnA : NoWrap (addr m0 + BitVec.ofNat 64 o) 64 := by
    unfold NoWrap; rw [toNat_add_ofNat' (by omega)]; omega
  have hwf := wf_one hmA hnA (m := s.data)
  have h16 : m0.regs.X1.toNat ≤ 16 := hpre.1
  have ho63 : o < 2 ^ 63 := by omega
  have hm : Match (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 o, 64)]) (blkS (-(o : Int)))
      s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show s.data.regs.X0.toBitVec = _
        rw [hB.x0]
        exact ofInt_neg _ o ho63,
       trivial⟩ trivial trivial trivial
  refine exec_at hk hx hwf hpc hm fun s' hm' hpc' ↦ cont s' hpc' ?_
  have hB' := hB.step hm hm' hwf rfl hkeep
  obtain ⟨g8, g12, g9, g14, g11, g15, g13, g16, g10⟩ := g
  have hd := hB.dmem
  have r : ∀ (q : XReg) (off : Nat), S'.reg q = some (.bin .eor .W64 (.load 0 off 8) (.reg q)) →
      (s'.data.regs.getXReg q).toBitVec =
        (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 o, 64)]).load 0 off 8 ^^^
          (s.data.regs.getXReg q).toBitVec := fun q off h ↦ by
    rw [hm'.regs q _ h]
    sym_simp
    rfl
  refine ⟨hB', ?_, by omega, ?_, ?_⟩
  · show (s'.data.regs.getXReg .X10).toNat = _
    rw [Match.reg_eq hm hm' rfl g10]; exact hI.x10
  · show (s'.data.regs.getXReg .X8).toBitVec ^^^ (s'.data.regs.getXReg .X9).toBitVec ^^^
      (s'.data.regs.getXReg .X11).toBitVec ^^^ (s'.data.regs.getXReg .X13).toBitVec = _
    rw [r _ _ g8, r _ _ g9, r _ _ g11, r _ _ g13, acc4 m0 t hle, c0_add, c0_add, c0_add, c0_add,
      ← hI.lo, load_c0 hd (i := 4 * t) (by omega) (by omega), load_c0 hd (i := 4 * t + 1) (by omega) (by omega),
      load_c0 hd (i := 4 * t + 1 + 1) (by omega) (by omega), load_c0 hd (i := 4 * t + 1 + 1 + 1) (by omega) (by omega)]
    ac_rfl
  · show (s'.data.regs.getXReg .X12).toBitVec ^^^ (s'.data.regs.getXReg .X14).toBitVec ^^^
      (s'.data.regs.getXReg .X15).toBitVec ^^^ (s'.data.regs.getXReg .X16).toBitVec = _
    rw [r _ _ g12, r _ _ g14, r _ _ g15, r _ _ g16, acc4 m0 t hle, c1_add, c1_add, c1_add, c1_add,
      ← hI.hi, load_c1 hd (i := 4 * t) (by omega) (by omega), load_c1 hd (i := 4 * t + 1) (by omega) (by omega),
      load_c1 hd (i := 4 * t + 1 + 1) (by omega) (by omega), load_c1 hd (i := 4 * t + 1 + 1 + 1) (by omega) (by omega)]
    ac_rfl


omit [Host] in
theorem ult_false {x : BitVec 64} {c : Nat} (h : c ≤ x.toNat) (hc : c < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 c) = false := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, decide_eq_false_iff_not]
  omega

omit [Host] in
theorem ult_true {x : BitVec 64} {c : Nat} (h : x.toNat < c) (hc : c < 2 ^ 64) :
    x.ult (BitVec.ofNat 64 c) = true := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, decide_eq_true_eq]
  omega

omit [Host] in
theorem and28 : ∀ n, n ≤ 16 → n &&& 28 = 4 * (n / 4) := by decide

/-- **The first unrolled block** `b4`: four values loaded into the accumulators. -/
theorem first (hp : Placed code k) {m0 : MachineData} (hpre : SumEPre m0) (h4 : 4 ≤ len m0)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SumE.b4Offset)) (hB : Base m0 s.data)
    {R : MachineState → Prop}
    (cont : ∀ s', PcOk (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 0, 64)])
      (.cond (.cmp .eq .W64 (.bin .and .W64 (.reg .X1) (.lit 28)) (.lit 4)) NativeRustcVmArm.Vm.SumE.label_8)
      (Host.addrOf (k + NativeRustcVmArm.Vm.SumE.b4Offset + 8)) s' → UInv m0 1 s'.data → Eventually (step1 Host.exe) R s') :
    Eventually (step1 Host.exe) R s := by
  have hrV := hpre.2
  have h16 : m0.regs.X1.toNat ≤ 16 := hpre.1
  have aL : m0.regs.X1.toNat = len m0 := rfl
  have hnw : (addr m0).toNat + 16 * len m0 ≤ 2 ^ 64 := hrV.2
  have hmA : Mapped s.data.dmem (addr m0 + BitVec.ofNat 64 0) 64 := fun j hj ↦ by
    rw [NativeRustcVm.addr_add, hB.dmem]; exact hrV.1 _ (by omega)
  have hnA : NoWrap (addr m0 + BitVec.ofNat 64 0) 64 := by
    unfold NoWrap; rw [toNat_add_ofNat' (by omega)]; omega
  have hwf := wf_one hmA hnA (m := s.data)
  have hm : Match (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 0, 64)]) (blkS 0) s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show s.data.regs.X0.toBitVec = (addr m0 + BitVec.ofNat 64 0) + BitVec.ofInt 64 0
        rw [hB.x0, add_ofNat_zero]
        exact (BitVec.add_zero _).symm,
       trivial⟩ trivial trivial trivial
  refine exec_at (hb hp b4_in_code (by simp [b4])) run_b4 hwf hpc hm fun s' hm' hpc' ↦
    cont s' hpc' ?_
  have hB' := hB.step hm hm' hwf rfl (after_eq run_b4 ▸ b4_keeps)
  have hd := hB.dmem
  have r : ∀ (q : XReg) (off : Nat), (after b4 (blkS 0)).reg q = some (.load 0 off 8) →
      (s'.data.regs.getXReg q).toBitVec =
        (Env.ofMachine s.data [(addr m0 + BitVec.ofNat 64 0, 64)]).load 0 off 8 :=
    fun q off h ↦ by rw [hm'.regs q _ ((after_eq run_b4) ▸ h)]; rfl
  have z0 : (acc m0 (4 * 0)).c0.toBitVec = 0#64 := rfl
  have z1 : (acc m0 (4 * 0)).c1.toBitVec = 0#64 := rfl
  refine ⟨hB', ?_, by omega, ?_, ?_⟩
  · show (s'.data.regs.getXReg .X10).toNat = _
    rw [← UInt64.toNat_toBitVec, hm'.regs .X10 _ rfl]
    sym_simp
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    show (s.data.regs.X1.toNat &&& _) = _
    rw [hB.x1]
    exact and28 _ h16
  · show (s'.data.regs.getXReg .X8).toBitVec ^^^ (s'.data.regs.getXReg .X9).toBitVec ^^^
      (s'.data.regs.getXReg .X11).toBitVec ^^^ (s'.data.regs.getXReg .X13).toBitVec = _
    rw [r .X8 0 rfl, r .X9 16 rfl, r .X11 32 rfl, r .X13 48 rfl, acc4 m0 0 (by omega), c0_add,
      c0_add, c0_add, c0_add, z0, BitVec.zero_xor,
      load_c0 hd (i := 4 * 0) (by omega) (by omega), load_c0 hd (i := 4 * 0 + 1) (by omega) (by omega),
      load_c0 hd (i := 4 * 0 + 1 + 1) (by omega) (by omega),
      load_c0 hd (i := 4 * 0 + 1 + 1 + 1) (by omega) (by omega)]
  · show (s'.data.regs.getXReg .X12).toBitVec ^^^ (s'.data.regs.getXReg .X14).toBitVec ^^^
      (s'.data.regs.getXReg .X15).toBitVec ^^^ (s'.data.regs.getXReg .X16).toBitVec = _
    rw [r .X12 8 rfl, r .X14 24 rfl, r .X15 40 rfl, r .X16 56 rfl, acc4 m0 0 (by omega), c1_add,
      c1_add, c1_add, c1_add, z1, BitVec.zero_xor,
      load_c1 hd (i := 4 * 0) (by omega) (by omega), load_c1 hd (i := 4 * 0 + 1) (by omega) (by omega),
      load_c1 hd (i := 4 * 0 + 1 + 1) (by omega) (by omega),
      load_c1 hd (i := 4 * 0 + 1 + 1 + 1) (by omega) (by omega)]

omit [Host] in
/-- `cmp x10, #c; b.eq`: by the count of the unrolled values. -/
theorem x10_eq {m0 s : MachineData} (h : s.regs.X10.toNat = 4 * (len m0 / 4)) (c : Nat)
    (hc : c < 2 ^ 64) :
    ((s.regs.getXReg .X10).toBitVec == BitVec.ofNat 64 c) = true ↔ 4 * (len m0 / 4) = c := by
  rw [beq_iff_eq]
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc] at this
    exact h ▸ this
  · intro e
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
    exact h.trans e

/-- **`sum_e` meets its contract.** -/
theorem sumE_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.SumE.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.SumE.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.SumE.entryOffset) NativeRustcVmArm.Vm.SumE.entry_at]
  have h16 : m0.regs.X1.toNat ≤ 16 := hpre.1
  have aL : m0.regs.X1.toNat = len m0 := rfl
  refine exec_then (hb hp b0_in_code (by simp [b0])) run_b0 (Env.wf_nil _) (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hB1 := (Base.entry m0).regs hm1 (after_eq run_b0 ▸ b0_keeps)
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  have hpc1' := pc_cond hpc1
  have hx1 : (m0.regs.getXReg .X1).toBitVec.toNat = len m0 := rfl
  by_cases hz : len m0 = 0
  · have hpc := (hpc1'.1 (by
      show ((m0.regs.getXReg .X1).toBitVec == BitVec.ofNat 64 0) = true
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [hx1, hz]; rfl)).trans (hp.label (j := NativeRustcVmArm.Vm.SumE.b3Offset) NativeRustcVmArm.Vm.SumE.label_3_at)
    exact ret_of (hb hp b3_in_code (by simp [b3])) run_b3 rfl rfl (after_eq run_b3 ▸ b3_keeps) hpc
      hB1 (by rw [hz]; rfl)
  have hpc2 := hpc1'.2 (by
    show ¬((m0.regs.getXReg .X1).toBitVec == BitVec.ofNat 64 0) = true
    rw [beq_iff_eq]; intro h; have := congrArg BitVec.toNat h; rw [hx1] at this; exact hz this)
  have hs1 : (s1.data.regs.getXReg .X1).toBitVec.toNat = len m0 := by
    show s1.data.regs.X1.toBitVec.toNat = _; rw [hB1.x1]; rfl
  refine exec_at (hb hp b1_in_code (by simp [b1])) run_b1 (Env.wf_nil _) hpc2 (match_nil _)
    fun s2 hm2 hpc3 ↦ ?_
  have hB2 := hB1.regs hm2 (after_eq run_b1 ▸ b1_keeps)
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  have hpc3' := pc_cond hpc3
  by_cases h4 : 4 ≤ len m0
  · have hpc := (hpc3'.1 (by
      show (!(s1.data.regs.getXReg .X1).toBitVec.ult (BitVec.ofNat 64 4)) = true
      rw [Bool.not_eq_true', ult_false (by rw [hs1]; exact h4) (by decide)])).trans
      (hp.label (j := NativeRustcVmArm.Vm.SumE.b4Offset) NativeRustcVmArm.Vm.SumE.label_4_at)
    refine first hp hpre h4 hpc hB2 fun s3 hpc4 hI1 ↦ ?_
    simp only [PcOk] at hpc4
    sym_simp at hpc4
    have hpc4' := pc_cond hpc4
    have hs2 : (s2.data.regs.getXReg .X1).toBitVec.toNat = len m0 := by
      show s2.data.regs.X1.toBitVec.toNat = _; rw [hB2.x1]; rfl
    have hand : ((s2.data.regs.getXReg .X1).toBitVec &&& 28#64 == 4#64) = true ↔
        4 * (len m0 / 4) = 4 := by
      rw [beq_iff_eq]
      constructor
      · intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_and, hs2] at this
        rw [← and28 _ (by omega)]
        exact this
      · intro e
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_and, hs2]
        exact (and28 _ (by omega)).trans e
    by_cases e4 : 4 * (len m0 / 4) = 4
    · exact fromL8 hp hpre ((hpc4'.1 (hand.mpr e4)).trans (hp.label (j := NativeRustcVmArm.Vm.SumE.b8Offset) NativeRustcVmArm.Vm.SumE.label_8_at)) hI1
        (hI1.x10.trans e4)
    have hpc5 := hpc4'.2 (fun h ↦ e4 (hand.mp h))
    refine ublock hpre (hb hp b5_in_code (by simp [b5])) (o := 64) (t := 1) run_b5
      (by decide +kernel) (after_eq run_b5 ▸ b5_keeps) rfl (by omega) hpc5 hI1
      fun s4 hpc6 hI2 ↦ ?_
    simp only [PcOk] at hpc6
    sym_simp at hpc6
    have hpc6' := pc_cond hpc6
    by_cases e8 : 4 * (len m0 / 4) = 8
    · exact fromL8 hp hpre ((hpc6'.1 ((x10_eq hI1.x10 8 (by decide)).mpr e8)).trans
        (hp.label (j := NativeRustcVmArm.Vm.SumE.b8Offset) NativeRustcVmArm.Vm.SumE.label_8_at)) hI2 (hI2.x10.trans e8)
    have hpc7 := hpc6'.2 (fun h ↦ e8 ((x10_eq hI1.x10 8 (by decide)).mp h))
    refine ublock hpre (hb hp b6_in_code (by simp [b6])) (o := 128) (t := 2) run_b6
      (by decide +kernel) (after_eq run_b6 ▸ b6_keeps) rfl (by omega) hpc7 hI2
      fun s5 hpc8 hI3 ↦ ?_
    simp only [PcOk] at hpc8
    sym_simp at hpc8
    have hpc8' := pc_cond hpc8
    by_cases e12 : 4 * (len m0 / 4) = 12
    · exact fromL8 hp hpre ((hpc8'.1 ((x10_eq hI2.x10 12 (by decide)).mpr e12)).trans
        (hp.label (j := NativeRustcVmArm.Vm.SumE.b8Offset) NativeRustcVmArm.Vm.SumE.label_8_at)) hI3 (hI3.x10.trans e12)
    have hpc9 := hpc8'.2 (fun h ↦ e12 ((x10_eq hI2.x10 12 (by decide)).mp h))
    refine ublock hpre (hb hp b7_in_code (by simp [b7])) (o := 192) (t := 3) run_b7
      (by decide +kernel) (after_eq run_b7 ▸ b7_keeps) rfl (by omega) hpc9 hI3
      fun s6 hpc10 hI4 ↦ ?_
    simp only [PcOk] at hpc10
    exact fromL8 hp hpre hpc10 hI4 (by rw [hI4.x10]; omega)
  · have hpc := hpc3'.2 (by
      show ¬(!(s1.data.regs.getXReg .X1).toBitVec.ult (BitVec.ofNat 64 4)) = true
      rw [Bool.not_eq_true', ult_true (by rw [hs1]; omega) (by decide)]
      exact Bool.true_eq_false.mp.mt id)
    refine exec_at (hb hp b2_in_code (by simp [b2])) run_b2 (Env.wf_nil _) hpc (match_nil _)
      fun s3 hm3 hpc4 ↦ ?_
    have hB3 := hB2.regs hm3 (after_eq run_b2 ▸ b2_keeps)
    simp only [PcOk] at hpc4
    refine fromL9 (i := 0) hp hpre (hpc4.trans (hp.label (j := NativeRustcVmArm.Vm.SumE.b9Offset) NativeRustcVmArm.Vm.SumE.label_9_at)) hB3 (by omega) ?_ ?_
    · show (s3.data.regs.getXReg .X10).toNat = 0
      rw [← UInt64.toNat_toBitVec, hm3.regs .X10 _ rfl]; rfl
    · show (⟨s3.data.regs.getXReg .X9, s3.data.regs.getXReg .X8⟩ : EW) = _
      rw [toBitVec_eq (hm3.regs .X9 _ rfl), toBitVec_eq (hm3.regs .X8 _ rfl)]
      rfl

end

end NativeRustcVmArm.Arrays.SumE
