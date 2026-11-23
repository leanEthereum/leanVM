module

public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Whir.FinalLevel.Frame
public import NativeRustcVmArm.Whir.FinalLevel.Ok
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# `final_level`: the entry and the folded lane

`entry`: the prologue and the `μ` checks (`b0`, `b1`, both passed under the precondition), the
folded lane read (`b4`, `read_scalars`), its verdict (`b5`, `None` to the epilogue).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.FinalLevel
open NativeRustcVmArm.Transcript (known_ptr load_ofMachine eval_ptr)

public section

theorem lslv_one {x : BitVec 64} (hx : x.toNat < 64) :
    (BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) x).toNat = 2 ^ x.toNat := by
  sym_simp
  rw [BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt hx]
  simp only [BitVec.toNat_ofNat, Nat.one_mod, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hx)

section
variable [Labels]

/-- The entry's environment: the frame, the level. -/
abbrev E0 (m0 : MachineData) : Env := Env.ofMachine m0 [(base m0 2672, 2672), (lvA m0, 24)]

/-- `2 ^ μ`, as `b1` computes it. -/
abbrev s19 : Sym := .bin .lslv .W64 (.lit 1) (.reg .X3)
/-- `2 ^ μ` plus the level's fold, as `b1` computes it. -/
abbrev s23 : Sym := .bin .add .W64 (.load 1 0 8) s19

variable {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData}

namespace Ctx

variable (c : Ctx a s0 level ba b w rounds m0)
include c

theorem e0_wf : (E0 m0).WF :=
  Env.wf_of ⟨⟨frame_mapped c.stack (by rw [stack_eq]; decide),
    base_noWrap (by have := c.hN'; omega)⟩, ⟨c.lin.1.1, c.lin.1.2⟩, trivial⟩
    (List.pairwise_pair.mpr (NativeRustcVm.Apart.symm (NativeRustcVmArm.Ring.apart_frame
      c.hN (by rw [stack_eq]; decide) c.lin.2)))

theorem e0_match : Match (E0 m0) entryS m0 :=
  match_ofMachine ⟨rfl, fun _ ↦ c.aligned, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
        Option.getD_some]; rw [show BitVec.ofInt 64 2672 = BitVec.ofNat 64 2672 from rfl,
        base_add_eq])
    ⟨known_ptr (i := 1) rfl rfl, trivial⟩ trivial trivial trivial

/-- The level's words, as the entry's environment loads them. -/
theorem e0_load :
    (E0 m0).load 1 0 8 = level.fold.toUInt64.toBitVec ∧
      (E0 m0).load 1 8 8 = level.logInvRate.toUInt64.toBitVec := by
  obtain ⟨-, -, -, hw⟩ := c.lv
  refine ⟨load_ofMachine (r := 1) (o := 0) rfl ?_, load_ofMachine (r := 1) (o := 8) rfl ?_⟩
  · simpa [off_zero] using NativeRustcVm.wordsAt_getElem hw (i := 0) (by simp)
  · simpa [off] using NativeRustcVm.wordsAt_getElem hw (i := 1) (by simp)

theorem two_mu_le : 2 ^ mu m0 + level.fold ≤ 64 := c.fold

theorem ev19 : s19.eval (E0 m0) = BitVec.ofNat 64 (2 ^ mu m0) := by
  apply BitVec.eq_of_toNat_eq
  have h := lslv_one (x := m0.regs.X3.toBitVec) c.mu64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) c.mu64)]
  exact h

theorem ev23 : s23.eval (E0 m0) = BitVec.ofNat 64 (2 ^ mu m0 + level.fold) := by
  have h := c.two_mu_le
  show BinOp.apply .add .W64 ((E0 m0).load 1 0 8) (s19.eval (E0 m0)) = _
  rw [c.ev19, c.e0_load.1]
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat,
    UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
  omega

end Ctx

end

variable [Host] {a : DecArea} {s0 : TState} {level : Whir.Level} {ba : BasisAddrs} {b : BasisW}
  {w : WhirStateW} {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **The entry and the folded lane.** -/
theorem entry (hp : Placed code k) (c : Ctx a s0 level ba b w rounds m0)
    (hrsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (cont : ∀ (st : MachineState) (folded : Array EW) (s1 : TState),
      st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b6Offset) → Base m0 st.data →
      st.data.regs.X22 = m0.regs.X0 → st.data.regs.X24 = m0.regs.X1 →
      st.data.regs.X26 = m0.regs.X2 → st.data.regs.X23.toNat = 2 ^ mu m0 + level.fold →
      st.data.regs.X25.toNat = level.logInvRate → folded.size = 2 ^ mu m0 + level.fold →
      NativeRustcVm.EWsAt st.data.dmem (loc m0 40) folded.toList →
      TStateAt st.data.dmem (tA m0) a s1 →
      runF s0 level b w rounds m0 =
        (C1 m0.regs.X1.toNat level (mu m0) m0.regs.X4.toNat b w rounds folded).run s1 →
      Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) st) :
    Eventually (step1 Host.exe) (Goal a s0 level b w rounds m0) ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.FinalLevel.b0Offset)⟩ := by
  have hwf := c.e0_wf
  have hN := c.hN'
  have hmu : m0.regs.X3.toNat < 64 := c.mu64
  have hfo := c.two_mu_le
  have hf64 : level.fold < 2 ^ 64 := c.lv.1
  have hr64 : level.logInvRate < 2 ^ 64 := c.lv.2.1
  have h2 : 2 ^ mu m0 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hmu
  -- `b0`: the prologue, `μ ≤ 63`.
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf c.e0_match fun st1 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b0Offset + b0.length = k + NativeRustcVmArm.Vm.FinalLevel.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b0_next]] at hpc1
  split at hpc1
  · rename_i h
    sym_simp at h
    simp only [bv_ult_toNat, bv_beq_toNat] at h
    have : ((E0 m0).regs .X3).toNat = m0.regs.X3.toNat := rfl
    simp only [this, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    omega
  -- `b1`: `2 ^ μ` plus the fold at most `64`.
  refine exec_at (inf hp b1_in_code (by simp [b1])) (exec_after run_b0 run_b1e) hwf hpc1 hm1
    fun st2 hm2 hpc2 ↦ ?_
  simp only [PcOk] at hpc2
  split at hpc2
  case isFalse h =>
    simp only [SBool.eval, c.ev23, c.ev19] at h
    simp only [Sym.eval, CmpOp.apply, Sym.low_W64, bv_ult_toNat, bv_beq_toNat,
      BitVec.toNat_ofNat] at h
    simp only [Nat.mod_eq_of_lt (show 2 ^ mu m0 + level.fold < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt h2] at h
    simp at h
    omega
  rw [hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b4Offset) NativeRustcVmArm.Vm.FinalLevel.label_4_at] at hpc2
  -- `b4`: `read_scalars` into the frame at `40`.
  refine exec_at (inf hp b4_in_code (by simp [b4])) (exec_after run_b1e run_b4e) hwf hpc2 hm2
    fun st3 hm3 hpc3 ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.FinalLevel.b4Offset + b4.length = k + NativeRustcVmArm.Vm.FinalLevel.b5Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b4_next]] at hpc3
  obtain ⟨hsl, hmem⟩ := after_eq run_b4e ▸ ok_e4
  have hf3 : FFr m0 st3.data :=
    Fr.ofPrologue c.hN (by rw [stack_eq]; decide) hm3 hwf rfl hsl slots_le hmem
      (fun _ h ↦ by cases h)
  have hts3 : TStateAt st3.data.dmem (tA m0) a s0 :=
    c.ts_block (st := m0) (rs := [(lvA m0, 24)]) hm3 hwf hmem c.ts0
  have x0 : st3.data.regs.X0.toBitVec = tA m0 := reg_val hm3 (r := .X0) (v := .reg .X0) rfl
  have x1 : st3.data.regs.X1.toBitVec = loc m0 40 := reg_val hm3 (r := .X1) (v := .ptr 0 40) rfl
  have x2 : st3.data.regs.X2.toNat = 2 ^ mu m0 + level.fold := by
    have := (reg_val hm3 (r := .X2) (v := s23) rfl).trans c.ev23
    rw [← UInt64.toNat_toBitVec, show st3.data.regs.X2.toBitVec = _ from this, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  have hle : 2672 + readScalarsStack ≤ finalLevelStack := by decide
  have hn : 40 + 16 * (2 ^ mu m0 + level.fold) ≤ 2576 := by omega
  refine c.call hf3 (lo := 40) (n := 16 * (2 ^ mu m0 + level.fold)) hle hn (hrsc a s0) hpc3
    ?_ (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.2.1 fun q h ↦ ?_, hq.2.2.2.2⟩)
    fun m2 hf2 hq hcs ↦ ?_
  · refine ⟨c.stackOk' hf3 hle, c.rcAt' hf3 hle, ?_, ?_, ?_⟩
    · show TStateAt st3.data.dmem st3.data.regs.X0.toBitVec a s0
      rw [x0]; exact hts3
    · show TStateOk st3.data st3.data.regs.X0.toBitVec a readScalarsStack
      rw [x0]; exact c.tstateOk' hf3 hle
    · show OutOk st3.data st3.data.regs.X0.toBitVec a st3.data.regs.X1.toBitVec
        (16 * st3.data.regs.X2.toNat) readScalarsStack
      rw [x0, x1, x2]; exact c.localOk' hf3 hle (by omega)
  · rcases h with h | h | h
    · rw [x1, x2] at h; exact .inr (.inl h)
    · rw [x0] at h; exact .inr (.inr (.inr h))
    · exact .inl h
  -- `b5`: the verdict.
  obtain ⟨h0, hxs, hnext, -, -⟩ := hq
  rw [x2] at h0 hxs hnext
  rw [x1] at hxs
  rw [x0] at hnext
  have hwf5 := c.fwf hf2
  refine exec_at (inf hp b5_in_code (by simp [b5])) run_b5 hwf5 rfl (c.fmatch hf2)
    fun st5 hm5 hpc5 ↦ ?_
  simp only [PcOk] at hpc5
  rw [cbz_ok (show (fenv m0 m2 []).regs .X0 = _ from congrArg UInt64.toBitVec h0)] at hpc5
  have hf5 : FFr m0 st5.data :=
    Fr.ofBlock hf2 (c.fmatch hf2) hm5 hwf5 rfl rfl rfl (fun _ h ↦ by cases h)
  have hd5 : st5.data.dmem = m2.dmem := hm5.dmem_eq hwf5 rfl
  have k5 : ∀ r, st5.data.regs.getXReg r = m2.regs.getXReg r := fun r ↦
    reg_of hm5 (r := r) (v := .reg r) (by cases r <;> rfl) rfl
  cases hr : (readScalars (2 ^ mu m0 + level.fold)).run s0 with
  | none =>
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte,
      hp.label (j := NativeRustcVmArm.Vm.FinalLevel.b3Offset) NativeRustcVmArm.Vm.FinalLevel.label_3_at] at hpc5
    have hnone : runF s0 level b w rounds m0 = none := by
      rw [runF, finalLevelM_eq]; exact run_bind_none hr
    refine exit3 hp c hpc5 hf5 ?_ ?_
    · rw [hnone, show st5.data.regs.X0 = m2.regs.X0 from k5 .X0]; rw [hr] at h0; exact h0
    · rw [hnone]; intro _ _ h; cases h
  | some p =>
    obtain ⟨folded, s1⟩ := p
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      show k + NativeRustcVmArm.Vm.FinalLevel.b5Offset + b5.length = k + NativeRustcVmArm.Vm.FinalLevel.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.FinalLevel.b5_next]] at hpc5
    have kc : ∀ r, calleeSaved r = true → st5.data.regs.getXReg r = st3.data.regs.getXReg r :=
      fun r hr ↦ (k5 r).trans (hcs r hr)
    have v19 := (reg_val hm3 (r := .X19) (v := s19) rfl).trans c.ev19
    have v23 := (reg_val hm3 (r := .X23) (v := s23) rfl).trans c.ev23
    have v25 : (st3.data.regs.getXReg .X25).toBitVec = level.logInvRate.toUInt64.toBitVec :=
      (reg_val hm3 (r := .X25) (v := .load 1 8 8) rfl).trans c.e0_load.2
    refine cont st5 folded s1 hpc5 ⟨hf5, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_
      (by rw [hd5]; exact hxs folded s1 hr) (by rw [hd5]; exact hnext folded s1 hr) ?_
    · rw [show st5.data.regs.X19 = _ from kc .X19 rfl, ← UInt64.toNat_toBitVec,
        show (st3.data.regs.getXReg .X19).toBitVec = _ from v19,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2]
    · exact (kc .X20 rfl).trans (reg_of hm3 (r := .X20) (v := .reg .X3) rfl rfl)
    · exact (kc .X21 rfl).trans (reg_of hm3 (r := .X21) (v := .reg .X5) rfl rfl)
    · exact (kc .X27 rfl).trans (reg_of hm3 (r := .X27) (v := .reg .X6) rfl rfl)
    · exact (kc .X28 rfl).trans (reg_of hm3 (r := .X28) (v := .reg .X4) rfl rfl)
    · exact (kc .X22 rfl).trans (reg_of hm3 (r := .X22) (v := .reg .X0) rfl rfl)
    · exact (kc .X24 rfl).trans (reg_of hm3 (r := .X24) (v := .reg .X1) rfl rfl)
    · exact (kc .X26 rfl).trans (UInt64.toBitVec_inj.mp
        ((reg_val hm3 (r := .X26) (v := .ptr 1 0) rfl).trans (eval_ptr rfl)))
    · rw [show st5.data.regs.X23 = _ from kc .X23 rfl, ← UInt64.toNat_toBitVec,
        show (st3.data.regs.getXReg .X23).toBitVec = _ from v23,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [show st5.data.regs.X25 = _ from kc .X25 rfl, ← UInt64.toNat_toBitVec,
        show (st3.data.regs.getXReg .X25).toBitVec = _ from v25]
      simp only [UInt64.toNat_toBitVec, Nat.toUInt64, UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt hr64
    · exact NativeRustcVm.Sumcheck.readScalars_size hr
    · rw [runF, finalLevelM_eq]; exact run_bind_some hr

end

end NativeRustcVmArm.Whir.FinalLevel
