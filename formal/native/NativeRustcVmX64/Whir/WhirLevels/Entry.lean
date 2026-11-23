module

public import NativeRustcVmX64.Whir.WhirLevels.Exit

/-!
# `whir_levels`: the entry (x86-64)

`b0` (in `argEnv`: the frame, the return address, the state's address above it) pushes RBX, RBP,
R12 to R15 (`Frame.of_prologueA`), keeps the arguments in the frame's words `24` to `56` and the
loop's registers (RBX the levels, R12 `24 n`, R13 `-1`, R15 the `TState`, RBP the state, loaded
from the stack argument), and falls to the loop's head: `Head 0` (`entry`).
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmX64.Whir.Levels
open NativeRustcVmX64.Sumcheck NativeRustcVmX64.Vm.WhirLevels

public section

section
variable [Labels] (env : Env)

theorem v24_eval {n : Nat} (h : (env.regs .r9).toNat = n) (hn : 1 ≤ n) :
    v24.eval env = BitVec.ofNat 64 (n - 1) := by
  simp only [v24, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
  have : (env.regs .r9).ult (BitVec.ofNat 64 1) = false := by
    simp only [BitVec.ult, decide_eq_false_iff_not]; simp; omega
  simp only [this, Bool.not_false, ite_true]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp
  omega

theorem v48_eval {n : Nat} (h : (env.regs .r9).toNat = n) (hn : 1 ≤ n) :
    v48.eval env = 1#64 - env.regs .r9 := by
  simp only [v48, Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  have : (env.regs .r9).ult (BitVec.ofNat 64 1) = false := by
    simp only [BitVec.ult, decide_eq_false_iff_not]; simp; omega
  simp only [this, Bool.false_eq_true, ite_false]

theorem v12_eval {n : Nat} (h : (env.regs .r9).toNat = n) :
    v12.eval env = BitVec.ofNat 64 (levelBytes * n) := by
  simp only [v12, Sym.eval, BinOp.apply, low_W64, ext_W64]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, h,
    levelBytes, shiftCount, show (2 : Nat) ^ Width.W64.bits = 2 ^ 64 from rfl]
  rw [Nat.shiftLeft_eq, show (BitVec.toNat (low Width.W8 3#64) &&& shiftMask Width.W64) = 3 from
    by decide]
  omega

end

variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- **The entry**: the prologue, then `Head 0` at the loop's head. -/
theorem entry (hp : Placed code k0) (c : Ctx a s0 levels ba b claim m0 rate) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b1Offset) ∧
      Head a s0 levels b claim m0 0 s0 ⟨claim, #[], #[]⟩ st.data) ⟨m0, Host.addrOf (k0 + NativeRustcVmX64.Vm.WhirLevels.b0Offset)⟩ := by
  have hl := c.len_le
  have hlen := c.len
  let env0 := argEnv m0 m0 112 8 []
  have hwf0 : env0.WF := argEnv_wf (c.region_ok fun _ h ↦ h) (by simp)
    (List.pairwise_singleton _ _)
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rspA, trivial⟩ trivial trivial trivial
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 nofun hm0
    fun st1 hm1 hpc1 ↦ .done _ ⟨?_, ?_⟩
  · simp only [PcOk] at hpc1
    exact hpc1
  obtain ⟨hpro, hw, h24, h32, h40, h48, h56, hrbx, hr12, hr13, hr15, hrbp⟩ := ok_b0
  have hfr : Frame m0 112 slots 8 st1.data :=
    Frame.of_prologueA Frame.entry hwf0 hm1 hpro slots_le slots_cs
  have hs : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange (fa m0) 112) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by omega) hw
  have hf : Fr m0 8 st1.data :=
    ⟨hfr, NativeRustcVm.SameOutside.mono hs fun q hq ↦ Or.inl (c.frame_stack le_rfl hq)⟩
  have hr9 : (env0.regs .r9).toNat = levels.length := hlen.symm
  have hw' : ∀ (o : Nat) (v : Sym) (u : UInt64), o + 8 ≤ 112 → WordW 0 o v (after b0 entryS) →
      v.eval env0 = u.toBitVec → NativeRustcVm.WordAt st1.data.dmem (off (fa m0) o) u :=
    fun o v u ho hW hv ↦ wordAt_written hm1 (r := 0) rfl (by omega) hW hv
  refine ⟨⟨hf, ?_, ?_, ?_, ?_, ?_, hw' 24 _ _ (by omega) h24 ?_, hw' 32 _ _ (by omega) h32 rfl,
    hw' 40 _ _ (by omega) h40 rfl, hw' 48 _ _ (by omega) h48 ?_, hw' 56 _ _ (by omega) h56 rfl⟩,
    c.ts_frame (by omega) (hm1.kept hwf0) hs c.ts0,
    WhirStateAt.of_same c.ws0 fun j hj ↦ c.same_frame (by omega) hs j
      (by unfold stateBytes at hj; unfold whirBytes; omega), by omega, rfl, rfl,
    by have := c.roots0; omega, by rw [List.drop_zero]⟩
  · rw [show reg st1.data .rbx = _ from hm1.regs .rbx _ hrbx]
    simp only [Nat.mul_zero, NativeRustcVm.addr_add_zero]
    rfl
  · rw [show reg st1.data .r12 = _ from hm1.regs .r12 _ hr12, v12_eval env0 hr9]
    simp
  · rw [show reg st1.data .r13 = _ from hm1.regs .r13 _ hr13]
    rfl
  · exact hm1.regs .r15 _ hr15
  · rw [show reg st1.data .rbp = _ from hm1.regs .rbp _ hrbp]
    obtain ⟨v, hv⟩ := NativeRustcVm.Wire.exists_wordAt (a := rspOf m0 + 8#64) (d := m0.dmem)
      fun i hi ↦ c.args.1 i (by omega)
    have hpv : pA m0 = v.toBitVec := by
      show (NativeRustcVm.wordOf m0.dmem (rspOf m0 + BitVec.ofNat 64 (8 + 8 * 0))).toBitVec = _
      rw [show rspOf m0 + BitVec.ofNat 64 (8 + 8 * 0) = rspOf m0 + 8#64 from rfl,
        NativeRustcVm.wordOf_of_wordAt hv]
    rw [hpv]
    exact load_argA (F := 112) (A := 8) (i := 0) hv
  · rw [v24_eval env0 hr9 (by omega)]
    rfl
  · rw [v48_eval env0 hr9 (by omega)]
    rfl

end

end NativeRustcVmX64.Whir.Levels.WL
