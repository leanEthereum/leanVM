module

public import NativeRustcVmArm.Layout.PlacementsOf.Store
public import NativeRustcVmArm.Layout.PlacementsOf.Exec2

/-!
# `placements_of`: the third loop (`b20` to `b27`)

At `.L17` (`I3 c`): `b22` loads column `c`'s slot byte and log-size. A `q_keccak` slot `s`
(`b23`, `b24`) places it at `offsets[4] + (s << κ)` (`b21`); else `b26` loads its output byte: an
output lane is `none` (`b27`), a stacked column at `offsets[c]` (`b20`, `b21`).
-/

namespace NativeRustcVmArm.Layout.PlacementsOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PlacementsOf
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier NativeVm.Math.Layout
open NativeRustcVm (WordAt WordsAt wordOf addr_add_add addr_add_zero toNat_add_ofNat)
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)
open NativeRustcVmArm.Layout.BuildLayout (toNat_toUInt64')

public section

/-- The registers a block's run keeps, from its literal result. -/
theorem regs_of {S' : SState} {m m' : MachineData}
    (h : ∀ r, S'.reg r = some (.reg r) → m'.regs.getXReg r = m.regs.getXReg r) (rs : List XReg)
    (hrs : rs.all (fun r ↦ S'.reg r == some (.reg r)) = true) :
    ∀ r ∈ rs, m'.regs.getXReg r = m.regs.getXReg r := fun r hr ↦
  h r (beq_iff_eq.mp (List.all_eq_true.mp hrs r hr))

section
variable [Labels]

theorem I3.mono {m0 st st' : MachineData} {c : Nat} (h : I3 m0 c st) (hb : Bd m0 st')
    (hd : st'.dmem = st.dmem)
    (e : ∀ r ∈ [XReg.X8, .X9, .X10, .X19, .X20, .X21, .X23, .X24, .X25],
      st'.regs.getXReg r = st.regs.getXReg r) : I3 m0 c st' := by
  refine ⟨hb, h.le, ?_, ?_, ?_, h.keep.of (e .X19 (by simp)) (e .X20 (by simp))
    (e .X23 (by simp)) (e .X24 (by simp)), ?_, ?_, hd ▸ h.offs, hd ▸ h.pl⟩
  · rw [show st'.regs.X9 = st.regs.X9 from e .X9 (by simp)]; exact h.x9
  · rw [show st'.regs.X10 = st.regs.X10 from e .X10 (by simp)]; exact h.x10
  · rw [show st'.regs.X8 = st.regs.X8 from e .X8 (by simp)]; exact h.x8
  · rw [show st'.regs.X21 = st.regs.X21 from e .X21 (by simp)]; exact h.x21
  · rw [show st'.regs.X25 = st.regs.X25 from e .X25 (by simp)]; exact h.x25

end

theorem plF_slot {κ : Nat → Nat} {c s : Nat} (h : slotF c = some s) :
    plF κ c = some ⟨κ c, sumF κ (keyF κ 4) + s * 2 ^ κ c⟩ := by
  unfold plF; rw [h]

theorem plF_block {κ : Nat → Nat} {c : Nat} (h : slotF c = none) (ho : outF c = false) :
    plF κ c = some ⟨κ c, sumF κ (keyF κ c)⟩ := by
  unfold plF; rw [h]; simp [ho]

theorem plF_out {κ : Nat → Nat} {c : Nat} (h : slotF c = none) (ho : outF c = true) :
    plF κ c = none := by
  unfold plF; rw [h]; simp [ho]

/-- `lslv`'s value without overflow. -/
theorem shl_toNat {x y : BitVec 64} {a b : Nat} (hx : x.toNat = a) (hy : y.toNat = b)
    (hb : b < 64) (hlt : a * 2 ^ b < 2 ^ 64) :
    (x <<< (y.toNat % RegWidth.W64.bits)).toNat = a * 2 ^ b := by
  rw [show y.toNat % RegWidth.W64.bits = b from by rw [hy]; exact Nat.mod_eq_of_lt hb,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hx]
  exact Nat.mod_eq_of_lt hlt

/-- `adds` without a carry. -/
theorem carry_ok {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (!(BitVec.unsigned (x + y) != BitVec.unsigned x + BitVec.unsigned y)) = true := by
  simp only [BitVec.unsigned, BitVec.toNat_add, Nat.mod_eq_of_lt h, Int.natCast_add,
    bne_self_eq_false, Bool.not_false]

variable [Host] {k : Nat}

/-- Where a turn of the third loop ends. -/
abbrev Next3 (k : Nat) (m0 : MachineData) (c : Nat) (s : MachineState) : Prop :=
  (c + 1 < 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b22Offset) ∧ I3 m0 (c + 1) s.data) ∨
    (c + 1 = 158 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b28Offset) ∧ I3 m0 158 s.data)

/-- **A `q_keccak` slot** `s` (`b23`, `b24`, `b21`). -/
theorem slot3 (hp : Placed code k) {m0 : MachineData} (hF : Facts m0) {c s : Nat} (hc : c < 158)
    (hs : slotF c = some s) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.PlacementsOf.b23Offset))
    (hI : I3 m0 c st.data) (x11 : st.data.regs.X11.toNat = κ m0 c)
    (x12 : st.data.regs.X12.toNat = s) :
    Eventually (step1 Host.exe) (Next3 k m0 c) st := by
  have hκ := hF.κ_le hc
  have hs64 := slotF_lt hs
  -- `b23`: the log-size below `64`
  refine regs_step (infix_of b23_in_code (by simp [b23]) hp) run_b23 (rk run_b23) hI.body hpc
    fun st1 hm1 hpc1 hb1 hd1 hr1 ↦ ?_
  have hI1 := hI.mono hb1 hd1 (regs_of hr1 _ rfl)
  have e11 : (Env.ofMachine st.data []).regs .X11 = BitVec.ofNat 64 (κ m0 c) := by
    apply BitVec.eq_of_toNat_eq
    show st.data.regs.X11.toNat = _
    rw [x11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  rw [e11, ofNat_ult' (by omega) (by decide)] at hpc1
  have hpc1' := pc_of ((Arrays.pc_cond hpc1).2
    (by rw [decide_eq_true (by omega : κ m0 c < 64)]; decide))
    (show k + NativeRustcVmArm.Vm.PlacementsOf.b23Offset + b23.length = k + NativeRustcVmArm.Vm.PlacementsOf.b24Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.PlacementsOf.b23_next])
  -- `b24`: the index
  refine regs_step (infix_of b24_in_code (by simp [b24]) hp) run_b24 (rk run_b24) hb1 hpc1'
    fun st2 hm2 hpc2 hb2 hd2 hr2 ↦ ?_
  have hI2 := hI1.mono hb2 hd2 (regs_of hr2 _ rfl)
  have g12 := hm2.regs .X12 _ rfl
  sym_simp at g12
  simp only [PcOk] at hpc2
  sym_simp at hpc2
  have v8 : ((Env.ofMachine st1.data []).regs .X8).toNat = sumF (κ m0) (keyF (κ m0) 4) :=
    hI1.x8
  have v11 : ((Env.ofMachine st1.data []).regs .X11).toNat = κ m0 c := by
    show (st1.data.regs.getXReg .X11).toBitVec.toNat = _; rw [hr1 .X11 rfl]; exact x11
  have v12 : ((Env.ofMachine st1.data []).regs .X12).toNat = s := by
    show (st1.data.regs.getXReg .X12).toBitVec.toNat = _; rw [hr1 .X12 rfl]; exact x12
  have hp36 : 2 ^ κ m0 c ≤ 2 ^ 36 := Nat.pow_le_pow_right (by decide) hκ
  have hmul : s * 2 ^ κ m0 c ≤ 63 * 2 ^ 36 := Nat.mul_le_mul (by omega) hp36
  have hsh := shl_toNat (x := (Env.ofMachine st1.data []).regs .X12)
    (y := (Env.ofMachine st1.data []).regs .X11) v12 v11 (by omega) (by omega)
  have h4 := hF.sumF_le (keyF (κ m0) 4)
  have hsum : ((Env.ofMachine st1.data []).regs .X8).toNat + ((Env.ofMachine st1.data []).regs
      .X12 <<< (((Env.ofMachine st1.data []).regs .X11).toNat % RegWidth.W64.bits)).toNat <
      2 ^ 64 := by rw [v8, hsh]; omega
  have hpc3 := ((Arrays.pc_cond hpc2).1 (carry_ok hsum)).trans (hp.label (j := NativeRustcVmArm.Vm.PlacementsOf.b21Offset) NativeRustcVmArm.Vm.PlacementsOf.label_16_at)
  refine store21 hp hF hc hpc3 hI2 (idx := sumF (κ m0) (keyF (κ m0) 4) + s * 2 ^ κ m0 c)
    (by omega) ?_ ?_ (plF_slot hs)
  · rw [show st2.data.regs.X11 = st.data.regs.X11 from (hr2 .X11 rfl).trans (hr1 .X11 rfl)]
    exact x11
  · show (st2.data.regs.getXReg .X12).toBitVec.toNat = _
    rw [g12, BitVec.toNat_add, Nat.mod_eq_of_lt hsum, v8, hsh]

end

end NativeRustcVmArm.Layout.PlacementsOf
