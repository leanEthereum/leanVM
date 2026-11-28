module

public import NativeRustcVmArm.KeccakGkr.SlotWeights.Pro

/-!
# `slot_weights`: the rows zeroed

`.LSlotWeights_2` (`b3`) zeroes row `r` (1024 bytes at X9), X8 counting the bytes left
(`zero_step`, `zero_loop`); `b4` loads segment `first`'s kernel entry and starts the first
segment's loop at bit `0` (`to_segA`).
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Vm.SlotWeights NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- **The rows zeroed**. -/
structure ZeroDone [Labels] (m0 : MachineData) (c : KeccakClaimW) (st : MachineData) : Prop where
  body : Body m0 st
  keep : Keep m0 st
  loc : Loc m0 c st
  rows : ElemsAt st.dmem (rowsA m0) (fun _ ↦ 0) 4096

end

public section

/-- `b3` writes zero words over its 1024 bytes. -/
theorem zero_writes [Labels] {S : SState} {x : Exit} (h : exec b3 zeroS = some (S, x)) :
    ∀ q < 128, ∀ i < 8, findWrite 0 (8 * q + i) S.mem = some (.lit 0, i) := by
  rw [e3] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  decide +kernel

variable [NativeRustcArm.Host] {c : KeccakClaimW} {m0 : MachineData} {k : Nat}

/-- **A turn of the zeroing loop**. -/
theorem zero_step (hp : Placed code k) (hpre : SlotWeightsPre c m0) {r : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b3Offset)) (hI : ZeroInv m0 c r s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b3Offset) ∧
        ZeroInv m0 c (r + 1) s'.data) ∨ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b4Offset) ∧ ZeroDone m0 c s'.data))
      s := by
  have hS := hpre.1
  have hr := hI.r_lt
  have hrok := rows_ok hpre
  obtain ⟨hrm, hrn⟩ := sub_ok hrok (o := 1024 * r) (n := 1024)
    (by show 1024 * r + 1024 ≤ 65536; omega)
  have hwf := wf_one (m := s.data) (Mapped.kept' hrm hI.body.kept) hrn
  have hm : Match (Env.ofMachine s.data [(rowsA m0 + BitVec.ofNat 64 (1024 * r), 1024)]) zeroS
      s.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s.data.regs.getXReg .X9).toBitVec = _ + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl, NativeRustcVm.addr_add_zero]
        exact hI.x9, trivial⟩ trivial trivial trivial
  refine exec_at (b3_in_code.trans hp.1 (by simp [b3])) e3 hwf hpc hm fun s' hm' hpc' ↦ ?_
  have hwr : ∀ p, Written (Env.ofMachine s.data [(rowsA m0 + BitVec.ofNat 64 (1024 * r), 1024)])
      (after b3 zeroS) p → InRange (rowsA m0 + BitVec.ofNat 64 (1024 * r)) 1024 p := by
    rw [after_eq e3]
    exact fun p hw ↦ Written.inRange (r := 0) rfl hrn (by decide +kernel) hw
  rw [after_eq e3] at hwr
  have hb : Body m0 s'.data :=
    hI.body.write hS (by decide) slots_le' (wsOff hpre) hm hm' hwf rfl all_slots (by decide)
      fun p hw ↦ ⟨⟨rowsA m0, rowsBytes⟩, by simp,
        inRange_mono (hwr p hw) (by show 1024 * r + 1024 ≤ 65536; omega)⟩
  have hso : SameOutside s.data.dmem s'.data.dmem
      (InRange (rowsA m0 + BitVec.ofNat 64 (1024 * r)) 1024) := fun p hp ↦
    hm'.sameOutside hwf p fun hw ↦ hp (hwr p hw)
  have kp := KeccakGkr.Match.regs_keep hm hm' [.X19, .X20, .X21, .X22] (by decide)
  have hkeep : Keep m0 s'.data :=
    ⟨(kp .X19 (by simp)).trans hI.keep.x19, (kp .X20 (by simp)).trans hI.keep.x20,
      (kp .X21 (by simp)).trans hI.keep.x21, (kp .X22 (by simp)).trans hI.keep.x22⟩
  have hloc : Loc m0 c s'.data :=
    hI.loc.keep hso fun i hi ↦ loc_not_rows hpre (o := 1024 * r) (n := 1024) (by
      show 1024 * r + 1024 ≤ 65536; omega) hi
  have hz := zero_writes e3
  have hrows : ElemsAt s'.data.dmem (rowsA m0) (fun _ ↦ 0) (64 * r + 64) := by
    refine hI.rows.grow (k := 64)
      (show (rowsA m0).toNat + 16 * (64 * r + 64) ≤ 2 ^ 64 from Nat.le_trans
        (Nat.add_le_add_left (show 16 * (64 * r + 64) ≤ 16 * 4096 by omega) _) (rows_ok hpre).2)
      (by rw [show 16 * (64 * r) = 1024 * r by omega]; exact hso)
      fun j hj ↦ ?_
    have h := KeccakGkr.Match.ewAt_write hm' (r := 0) (o := 16 * j) rfl (by omega)
      (fun i hi ↦ by rw [show 16 * j + i = 8 * (2 * j) + i by omega]; exact hz _ (by omega) i hi)
      (fun i hi ↦ by rw [show 16 * j + 8 + i = 8 * (2 * j + 1) + i by omega]; exact hz _ (by omega) i hi)
    rw [NativeRustcVm.addr_add_add, show 1024 * r + 16 * j = 16 * (64 * r + j) by omega] at h
    exact h
  have h8 := hm'.regs .X8 _ rfl
  have h9 := hm'.regs .X9 _ rfl
  have hx8 : (s.data.regs.getXReg .X8).toBitVec.toNat = 65536 - 1024 * r := hI.x8
  simp only [PcOk, NativeRustcVmArm.Vm.SlotWeights.b3_length, NativeRustcVmArm.Vm.SlotWeights.b3Length] at hpc'
  sym_simp at hpc'
  simp only [Env.ofMachine_regs] at hpc'
  by_cases hlast : r = 63
  · subst hlast
    have : (s.data.regs.getXReg .X8).toBitVec = 1024#64 := BitVec.eq_of_toNat_eq (by rw [hx8]; rfl)
    simp only [this, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    exact .done _ (Or.inr ⟨hpc', hb, hkeep, hloc, hrows⟩)
  · have hne : ((s.data.regs.getXReg .X8).toBitVec == 1024#64) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := congrArg BitVec.toNat h
      rw [hx8] at this
      simp at this
      omega
    simp only [hne, Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b3Offset) NativeRustcVmArm.Vm.SlotWeights.label_2_at), hb, hkeep, hloc, by omega, ?_, ?_,
      by rw [show 64 * (r + 1) = 64 * r + 64 by omega]; exact hrows⟩)
    · show (s'.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [h8]
      sym_simp
      simp only [Env.ofMachine_regs]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hx8]; simp; omega), hx8]
      simp
      omega
    · show (s'.data.regs.getXReg .X9).toBitVec = _
      rw [h9]
      show rowsA m0 + BitVec.ofNat 64 (1024 * r) + BitVec.ofInt 64 1024 = _
      rw [show BitVec.ofInt 64 1024 = BitVec.ofNat 64 1024 from rfl, NativeRustcVm.addr_add_add]
      congr 2

/-- **The zeroing loop**, to its end. -/
theorem zero_loop (hp : Placed code k) (hpre : SlotWeightsPre c m0) {r : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b3Offset)) (hI : ZeroInv m0 c r s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b4Offset) ∧ ZeroDone m0 c s'.data)
      s :=
  Sym.loop (fun n s ↦ ∃ r, n = 64 - r ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b3Offset) ∧ ZeroInv m0 c r s.data)
    (fun _ s ⟨r, hn, hpc, hI⟩ ↦ (zero_step hp hpre hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨64 - (r + 1), by have := hI.r_lt; omega, r + 1, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨r, rfl, hpc, hI⟩

/-- **`b4`**: the first segment's loop at bit `0`. -/
theorem to_segA (hp : Placed code k) (hpre : SlotWeightsPre c m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b4Offset)) (hI : ZeroDone m0 c s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SlotWeights.b6Offset) ∧ SegA m0 c 0 s'.data)
      s := by
  have hS := hpre.1
  have h176 : 176 ≤ slotWeightsStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h176
  have hwf := wf_one (m := s.data) (Mapped.kept' hmap hI.body.kept) hnw
  have hm : Match (Env.ofMachine s.data [(fbA m0, 176)]) bodyS s.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h176 rfl, trivial⟩
      (by rw [hI.body.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b4_in_code.trans hp.1 (by simp [b4])) e4 hwf hpc hm fun s' hm' hpc' ↦ ?_
  have hb : Body m0 s'.data := hI.body.of_block hm hm' hwf rfl all_slots (by decide)
  have kp := KeccakGkr.Match.regs_keep hm hm' [.X19, .X20, .X21, .X22] (by decide)
  have hd : s'.data.dmem = s.data.dmem := hm'.dmem_eq hwf rfl
  have hloc : Loc m0 c s'.data :=
    hI.loc.keep (R := fun _ ↦ False) (fun p _ ↦ by rw [hd]) fun _ _ h ↦ h
  have hf := first_le hpre
  obtain ⟨w0, w1⟩ := NativeRustcVm.ewAt_iff.mp hI.loc.s0
  rw [NativeRustcVm.addr_add_add] at w1
  have l0 := load_word (env := Env.ofMachine s.data [(fbA m0, 176)]) (r := 0) (off := 16) w0
  have l1 := load_word (env := Env.ofMachine s.data [(fbA m0, 176)]) (r := 0) (off := 16 + 8) w1
  have x21 := hI.keep.x21
  have x22 := hI.keep.x22
  refine .done _ ⟨hpc'.trans (hp.label (j := NativeRustcVmArm.Vm.SlotWeights.b6Offset) NativeRustcVmArm.Vm.SlotWeights.label_5_at), ⟨hb, ⟨(kp .X19 (by simp)).trans hI.keep.x19,
    (kp .X20 (by simp)).trans hI.keep.x20, (kp .X21 (by simp)).trans x21,
    (kp .X22 (by simp)).trans x22⟩, hloc, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply UInt64.toBitVec_inj.mp
    show (s'.data.regs.getXReg .X24).toBitVec = _
    rw [hm'.regs .X24 _ rfl]; exact l0
  · apply UInt64.toBitVec_inj.mp
    show (s'.data.regs.getXReg .X25).toBitVec = _
    rw [hm'.regs .X25 _ rfl]; exact l1
  · show (s'.data.regs.getXReg .X26).toBitVec.toNat = 0
    rw [hm'.regs .X26 _ rfl]; rfl
  · show (s'.data.regs.getXReg .X27).toBitVec.toNat = _
    rw [hm'.regs .X27 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    have e : s.data.regs.getXReg .X22 = m0.regs.X4 := x22
    rw [e, BitVec.toNat_mul]
    simp
    omega
  · show (s'.data.regs.getXReg .X28).toBitVec = _
    rw [hm'.regs .X28 _ rfl]
    sym_simp
    simp only [Env.ofMachine_regs]
    have e : s.data.regs.getXReg .X21 = m0.regs.X3 := x21
    rw [e]
  · show (s'.data.regs.getXReg .X29).toBitVec.toNat = _
    rw [hm'.regs .X29 _ rfl]; rfl
  · intro i hi
    have := hI.rows i hi
    rw [hd]
    simp only [prog, Nat.add_zero]
    rw [ite_eq_right (by omega)]
    exact this

end

end NativeRustcVmArm.KeccakGkr.SlotWeights
