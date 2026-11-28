module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Layout.BuildLayout.Base

/-!
# `build_layout`: the stores of the sizes, heights and rows (`b9` to `b14`)

From `.L` after the checks (`b9`): the memory's and the bytecode's log-sizes at bytes `0` and `8`,
then for each of the first five tables its height (`bit_length` of its row count less one, the
previous call's result) at `24 + 8 t` and its row count at `72 + 8 t` (`blk`, six times), the sixth
row count's `bit_length` left in X0 (`stores`).
-/

namespace NativeRustcVmArm.Layout.BuildLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BuildLayout
open NativeVm.Model NativeRustcVm.Layout LeanVM.Protocol.Verifier
open NativeRustcVmArm.Arrays (Body calleeRegs inSlots keepsAll restores)

public section

variable [Host] {k : Nat}

omit [Host] in
theorem u64_eq {x : UInt64} {n : Nat} (h : x.toNat = n) : x = n.toUInt64 := by
  subst h; apply UInt64.toNat.inj; simp

/-- The height word of a row count held in a register. -/
abbrev hw (x : UInt64) : UInt64 := (bitLength (x.toNat - 1)).toUInt64

omit [Host] in
theorem cs_callee : ∀ r ∈ cs, calleeSaved r = true := by decide
omit [Host] in
theorem cs21_callee : ∀ r ∈ XReg.X21 :: cs, calleeSaved r = true := by decide

omit [Host] in
theorem lay_match [Labels] {m0 : MachineData} {st : MachineData} (h22 : st.regs.getXReg .X22 = m0.regs.X3) {o : Int}
    (h21 : (st.regs.getXReg .X21).toBitVec = ll m0 + BitVec.ofInt 64 o) :
    Match (Env.ofMachine st [(ll m0, 120)]) (layS o) st :=
  match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by show _ = ll m0 + BitVec.ofInt 64 0; rw [Layout.ofInt_zero, BitVec.add_zero]
        exact congrArg UInt64.toBitVec h22, h21, trivial⟩ trivial trivial trivial

/-- **The stores** `b9` to `b14`. -/
theorem stores (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost) {bc : Array UInt64}
    {m0 : MachineData} (hF : Facts bc m0) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b9Offset))
    (hbd : Bd m0 st.data) (h22 : st.data.regs.getXReg .X22 = m0.regs.X3) {R : MachineState → Prop}
    (cont : ∀ st6 : MachineState, st6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.BuildLayout.b15Offset) → Bd m0 st6.data →
      st6.data.regs.getXReg .X22 = m0.regs.X3 →
      (st6.data.regs.getXReg .X21).toBitVec = ll m0 + BitVec.ofInt 64 24 →
      (∀ r ∈ [XReg.X19, .X20, .X23], st6.data.regs.getXReg r = st.data.regs.getXReg r) →
      st6.data.regs.X0.toNat = bitLength ((st.data.regs.getXReg .X23).toNat - 1) →
      Ws st6.data.dmem (ll m0)
        [(56, hw (st.data.regs.getXReg .X24)), (104, st.data.regs.getXReg .X24),
         (48, hw (st.data.regs.getXReg .X25)), (96, st.data.regs.getXReg .X25),
         (40, hw (st.data.regs.getXReg .X26)), (88, st.data.regs.getXReg .X26),
         (32, hw (st.data.regs.getXReg .X27)), (80, st.data.regs.getXReg .X27),
         (24, hw (st.data.regs.getXReg .X28)), (72, st.data.regs.getXReg .X28),
         (0, st.data.regs.getXReg .X19), (8, st.data.regs.getXReg .X20)] →
      Eventually (step1 Host.exe) R st6) :
    Eventually (step1 Host.exe) R st := by
  -- `b9`
  obtain ⟨k9, i9, r9, w9a, w9b, m9⟩ := Arrays.after_eq run_b9 ▸ b9_facts
  have hm9 : Match (Env.ofMachine st.data [(ll m0, 120)]) lay9S st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by show _ = ll m0 + BitVec.ofInt 64 0; rw [Layout.ofInt_zero, BitVec.add_zero]
          exact congrArg UInt64.toBitVec h22, trivial⟩ trivial trivial trivial
  refine blk hbl hF (infix_of b9_in_code (by simp [b9]) hp) run_b9 k9 i9 r9 cs_callee
    (ws := []) nofun m9 (by omega) (by omega) w9a w9b (rr := .X28) rfl rfl hpc hbd hm9 (Ws.nil _ _)
    fun s1 hpc1 hb1 hW1 hk1 hx1 h21 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.BuildLayout.b9Offset + b9.length = k + NativeRustcVmArm.Vm.BuildLayout.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b9_next]] at hpc1
  have e1 := u64_eq (x := s1.data.regs.getXReg .X0) hx1
  -- `b10`
  obtain ⟨k10, i10, r10, w10a, w10b, m10⟩ := Arrays.after_eq run_b10 ▸ b10_facts
  refine blk hbl hF (infix_of b10_in_code (by simp [b10]) hp) run_b10 k10 i10 r10 cs_callee
    (by simp) (by exact m10) (by omega) (by omega) w10a w10b (rr := .X27) rfl rfl hpc1 hb1
    (lay_match ((hk1 .X22 (by simp [cs])).trans h22) h21) hW1
    fun s2 hpc2 hb2 hW2 hk2 hx2 h21 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.BuildLayout.b10Offset + b10.length = k + NativeRustcVmArm.Vm.BuildLayout.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b10_next]] at hpc2
  have e2 := u64_eq (x := s2.data.regs.getXReg .X0) hx2
  rw [e1, hk1 .X28 (by simp [cs])] at hW2
  -- `b11`
  obtain ⟨k11, i11, r11, w11a, w11b, m11⟩ := Arrays.after_eq run_b11 ▸ b11_facts
  refine blk hbl hF (infix_of b11_in_code (by simp [b11]) hp) run_b11 k11 i11 r11 cs21_callee
    (by simp) (by exact m11) (by omega) (by omega) w11a w11b (rr := .X26) rfl rfl hpc2 hb2
    (lay_match ((hk2 .X22 (by simp [cs])).trans ((hk1 .X22 (by simp [cs])).trans h22)) h21) hW2
    fun s3 hpc3 hb3 hW3 hk3 hx3 h21 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.BuildLayout.b11Offset + b11.length = k + NativeRustcVmArm.Vm.BuildLayout.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b11_next]] at hpc3
  have e3 := u64_eq (x := s3.data.regs.getXReg .X0) hx3
  rw [e2, hk2 .X27 (by simp [cs]), hk1 .X27 (by simp [cs])] at hW3
  -- `b12`
  obtain ⟨k12, i12, r12, w12a, w12b, m12⟩ := Arrays.after_eq run_b12 ▸ b12_facts
  refine blk hbl hF (infix_of b12_in_code (by simp [b12]) hp) run_b12 k12 i12 r12 cs21_callee
    (by simp) (by exact m12) (by omega) (by omega) w12a w12b (rr := .X25) rfl rfl hpc3 hb3
    (lay_match ((hk3 .X22 (by simp [cs])).trans ((hk2 .X22 (by simp [cs])).trans
      ((hk1 .X22 (by simp [cs])).trans h22))) h21) hW3
    fun s4 hpc4 hb4 hW4 hk4 hx4 h21 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.BuildLayout.b12Offset + b12.length = k + NativeRustcVmArm.Vm.BuildLayout.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b12_next]] at hpc4
  have e4 := u64_eq (x := s4.data.regs.getXReg .X0) hx4
  rw [e3, hk3 .X26 (by simp [cs]), hk2 .X26 (by simp [cs]), hk1 .X26 (by simp [cs])] at hW4
  -- `b13`
  obtain ⟨k13, i13, r13, w13a, w13b, m13⟩ := Arrays.after_eq run_b13 ▸ b13_facts
  refine blk hbl hF (infix_of b13_in_code (by simp [b13]) hp) run_b13 k13 i13 r13 cs21_callee
    (by simp) (by exact m13) (by omega) (by omega) w13a w13b (rr := .X24) rfl rfl hpc4 hb4
    (lay_match ((hk4 .X22 (by simp [cs])).trans ((hk3 .X22 (by simp [cs])).trans
      ((hk2 .X22 (by simp [cs])).trans ((hk1 .X22 (by simp [cs])).trans h22)))) h21) hW4
    fun s5 hpc5 hb5 hW5 hk5 hx5 h21 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.BuildLayout.b13Offset + b13.length = k + NativeRustcVmArm.Vm.BuildLayout.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b13_next]] at hpc5
  have e5 := u64_eq (x := s5.data.regs.getXReg .X0) hx5
  rw [e4, hk4 .X25 (by simp [cs]), hk3 .X25 (by simp [cs]), hk2 .X25 (by simp [cs]),
    hk1 .X25 (by simp [cs])] at hW5
  -- `b14`
  obtain ⟨k14, i14, r14, w14a, w14b, m14⟩ := Arrays.after_eq run_b14 ▸ b14_facts
  refine blk hbl hF (infix_of b14_in_code (by simp [b14]) hp) run_b14 k14 i14 r14 cs21_callee
    (by simp) (by exact m14) (by omega) (by omega) w14a w14b (rr := .X23) rfl rfl hpc5 hb5
    (lay_match ((hk5 .X22 (by simp [cs])).trans ((hk4 .X22 (by simp [cs])).trans
      ((hk3 .X22 (by simp [cs])).trans ((hk2 .X22 (by simp [cs])).trans
        ((hk1 .X22 (by simp [cs])).trans h22))))) h21) hW5
    fun s6 hpc6 hb6 hW6 hk6 hx6 h21 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.BuildLayout.b14Offset + b14.length = k + NativeRustcVmArm.Vm.BuildLayout.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.BuildLayout.b14_next]] at hpc6
  have kk : ∀ r ∈ XReg.X21 :: cs, r ≠ .X21 →
      s6.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr hne ↦ by
    have hr' : r ∈ cs := by simpa [hne] using hr
    rw [hk6 r hr, hk5 r hr, hk4 r hr, hk3 r hr, hk2 r hr', hk1 r hr']
  rw [e5, hk5 .X24 (by simp [cs]), hk4 .X24 (by simp [cs]), hk3 .X24 (by simp [cs]), hk2 .X24 (by simp [cs]),
    hk1 .X24 (by simp [cs])] at hW6
  rw [hk5 .X23 (by simp [cs]), hk4 .X23 (by simp [cs]), hk3 .X23 (by simp [cs]),
    hk2 .X23 (by simp [cs]), hk1 .X23 (by simp [cs])] at hx6
  refine cont s6 hpc6 hb6 ((kk .X22 (by simp [cs]) (by decide)).trans h22) h21 ?_ hx6 hW6
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact kk _ (by simp [cs]) (by decide)

end

end NativeRustcVmArm.Layout.BuildLayout
