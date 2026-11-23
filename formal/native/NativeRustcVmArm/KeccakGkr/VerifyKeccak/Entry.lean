module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.KeccakGkr.VerifyKeccak.Pre

/-!
# `verify_keccak`: the prologue and the grind

`b0`: the registers saved, the arguments into X19 to X29, `logSteps - 4` (saturating) into the
frame's word at 88, `bit_length(5)`; `b1`: `grind(bit_length - 3)`. What the code keeps from here
to the inputs' opening (`Mid`): the frame, the registers X20 to X27 (`Regs`), the word at 88.
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak
open NativeRustcVm.KeccakGkr (scratchBytes outBytes)
open NativeRustcVm (Region)

@[expose] public section

/-- The registers the prologue sets and the code keeps up to the inputs' opening. -/
structure Regs (m0 m : MachineData) : Prop where
  x20 : m.regs.getXReg .X20 = m0.regs.X0
  x21 : m.regs.getXReg .X21 = m0.regs.X1
  x22 : m.regs.getXReg .X22 = m0.regs.X5
  x23 : m.regs.getXReg .X23 = m0.regs.X6
  x24 : m.regs.getXReg .X24 = m0.regs.X2
  x25 : (m.regs.getXReg .X25).toNat = m0.regs.X3.toNat - 4
  x26 : (m.regs.getXReg .X26).toBitVec =
    if m0.regs.X3.toNat < 4 then 8#64 else ipA m0 + 64#64
  x27 : (m.regs.getXReg .X27).toNat = min m0.regs.X3.toNat 4

/-- `logSteps - 4`, saturating. -/
def packW (m0 : MachineData) : UInt64 := (m0.regs.X1.toNat - 4).toUInt64

/-- **Between the prologue and the inputs' opening**: the frame, `Regs`, `packW` at 88. -/
structure Mid (m0 m : MachineData) : Prop where
  fr : VFr m0 m
  regs : Regs m0 m
  pk : NativeRustcVm.WordAt m.dmem (loc m0 88) (packW m0)

/-- The registers `Regs` names. -/
def regsL : List XReg := [.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27]

/-- A block keeps them: their symbolic values the start's. -/
def keepsL (S : SState) : Bool := regsL.all fun r ↦ S.reg r == some (.reg r)

end

public section

variable {m0 : MachineData}

theorem Regs.of_eq {m m' : MachineData} (h : Regs m0 m)
    (he : ∀ r ∈ regsL, m'.regs.getXReg r = m.regs.getXReg r) : Regs m0 m' := by
  have e : ∀ r ∈ regsL, m'.regs.getXReg r = m.regs.getXReg r := he
  simp only [regsL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e20, e21, e22, e23, e24, e25, e26, e27⟩ := e
  exact ⟨e20 ▸ h.x20, e21 ▸ h.x21, e22 ▸ h.x22, e23 ▸ h.x23, e24 ▸ h.x24, e25 ▸ h.x25,
    e26 ▸ h.x26, e27 ▸ h.x27⟩

theorem Regs.call {m m' : MachineData} (h : Regs m0 m)
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r) : Regs m0 m' :=
  h.of_eq fun r hr ↦ hcs r (by
    simp only [regsL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem Regs.block [Labels] {env : Env} {S0 S : SState} {m m' : MachineData} (h : Regs m0 m)
    (hm0 : Match env S0 m) (hm : Match env S m')
    (h0 : regsL.all (fun r ↦ (S0.reg r).isSome && S.reg r == S0.reg r) = true) : Regs m0 m' :=
  h.of_eq (Match.regs_keep hm0 hm regsL h0)

/-- `Mid` after a call that keeps the callee-saved registers and the frame's word at 88. -/
theorem Mid.call [Labels] {a : DecArea} {inst : Array EW} (hn : Nums a inst m0)
    {m m' : MachineData} {R : BitVec 64 → Prop} (h : Mid m0 m) (hfr : VFr m0 m')
    (hcs : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r)
    (hs : SameOutside m.dmem m'.dmem R)
    (hR : ∀ q, R q → q.toNat < m0.regs.SP.toNat - 3360 + 88 ∨
      m0.regs.SP.toNat - 3360 + 96 ≤ q.toNat) : Mid m0 m' :=
  ⟨hfr, h.regs.call hcs, word_keep h.pk hs (by
    have := hn.hN; have := m0.regs.SP.toNat_lt; rw [loc_toNat hn.hN (by omega)]; omega)
    (by rw [loc_toNat hn.hN (by omega)]; exact hR)⟩

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak

namespace NativeRustcVmArm.KeccakGkr.VerifyKeccak

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVm.Transcript NativeRustcVmArm.Vm.VerifyKeccak

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {cs : Array ColumnClaimW}
  {inst output : Array EW} {m0 : MachineData}

omit [Host] in
/-- No write. -/
theorem wOk_nil {env : Env} {S : SState} (h : S.mem = []) :
    ∀ w ∈ S.mem, WriteOk env 3360 slots (outs m0) w := by
  rw [h]; intro w hw; cases hw

/-- **The prologue, `bit_length(5)`, the grind** (`b0`, `b1`). -/
theorem stepEntry (hp : Placed code k) (h : P0 a s cs inst output m0) (hn : Nums a inst m0)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    {R : MachineState → Prop}
    (cont : ∀ m2, Mid m0 m2 → m2.regs.getXReg .X19 = m0.regs.X4 →
      m2.regs.getXReg .X28 = m0.regs.X3 → m2.regs.getXReg .X29 = m0.regs.X7 →
      m2.regs.X0 = okWord ((grind gBits).run s).isSome →
      NextAt m2.dmem (tA m0) a ((grind gBits).run s) →
      NativeRustcVm.Layout.ClaimsWAt m2.dmem (clA m0) cs →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b2Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.VerifyKeccak.b0Offset)⟩ := by
  have hN : verifyKeccakStack ≤ m0.regs.SP.toNat := by rw [stack_eq]; exact hn.hN
  have hN' := hn.hN
  have hSP := m0.regs.SP.toNat_lt
  have hwf : (Env.ofMachine m0 [(fb m0, 3360)]).WF :=
    Env.wf_of ⟨⟨frame_mapped hn.stk (by decide), base_noWrap (by omega)⟩, trivial⟩
      (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m0 [(fb m0, 3360)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hn.stk (by decide) (by decide), trivial⟩
      (by
        show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (3360 : Nat)
        rw [BitVec.ofInt_natCast, base_add_eq])
      trivial trivial trivial trivial
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : VFr m0 st.data :=
    Fr.ofPrologue (rs := []) hN (by rw [stack_eq]; decide) hm1 hwf rfl (by decide) slots_le
      (by decide) (fun r hr ↦ by cases hr)
  have hregs1 : Regs m0 st.data := by
    refine ⟨reg_of hm1 (v := .reg .X0) rfl rfl, reg_of hm1 (v := .reg .X1) rfl rfl,
      reg_of hm1 (v := .reg .X5) rfl rfl, reg_of hm1 (v := .reg .X6) rfl rfl,
      reg_of hm1 (v := .reg .X2) rfl rfl, ?_, ?_, ?_⟩
    · rw [← UInt64.toNat_toBitVec, hm1.regs .X25 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs, gx3, ult_ofNat _ (show 4 < 2 ^ 64 by decide),
        decide_eq_true_eq, UInt64.toNat_toBitVec]
      split <;> rename_i hc
      · simp only [BitVec.toNat_ofNat]; omega
      · rw [BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]; omega)]
        simp
    · rw [hm1.regs .X26 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs, gx2, gx3, ipA, ult_ofNat _ (show 4 < 2 ^ 64 by decide),
        decide_eq_true_eq, UInt64.toNat_toBitVec]
    · rw [← UInt64.toNat_toBitVec, hm1.regs .X27 _ rfl]
      sym_simp
      simp only [Env.ofMachine_regs, gx3, ult_ofNat _ (show 4 < 2 ^ 64 by decide),
        decide_eq_true_eq, UInt64.toNat_toBitVec]
      split <;> rename_i hc
      · simp only [UInt64.toNat_toBitVec]; omega
      · simp only [BitVec.toNat_ofNat]; omega
  have hpk1 : NativeRustcVm.WordAt st.data.dmem (loc m0 88) (packW m0) := by
    have := Sumcheck.Match.wordAt_write hm1 (r := 0) (o := 88)
      (v := .ite (.cmp .ult .W64 (.reg .X1) (.lit 4)) (.lit 0) (.bin .sub .W64 (.reg .X1) (.lit 4)))
      rfl (by decide) (by decide)
    convert this using 1
    apply UInt64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    sym_simp
    simp only [Env.ofMachine_regs, gx1,
      ult_ofNat _ (show 4 < 2 ^ 64 by decide), decide_eq_true_eq, UInt64.toNat_toBitVec]
    simp only [packW, Nat.toUInt64, UInt64.toNat_ofNat']
    have := m0.regs.X1.toNat_lt
    split <;> rename_i hc
    · simp only [BitVec.toNat_ofNat]; omega
    · rw [BitVec.toNat_sub_of_le
        (by rw [BitVec.le_def, BitVec.toNat_ofNat, UInt64.toNat_toBitVec]; omega)]
      simp; omega
  have hSPn : (fb m0).toNat = m0.regs.SP.toNat - 3360 := fb_toNat hn.hN
  have hd1 := written_nat hn hm1 hwf (L := 3360) (by decide)
  have := hn.tS; have := hn.wS; have := hn.cS; have := hn.txc; have := hn.c_w
  have hts1 : TStateAt st.data.dmem (tA m0) a s :=
    ts_keep hn h.ts (hm1.kept hwf) hd1 fun q hq ↦ ⟨by omega, by omega⟩
  have hcl1 : NativeRustcVm.Layout.ClaimsWAt st.data.dmem (clA m0) cs :=
    cls_keep hn h.cls hd1 fun q hq ↦ by omega
  have hx5 : st.data.regs.getXReg .X0 = 5 := reg_of hm1 (v := .lit 5) rfl rfl
  -- `bit_length(5)`
  refine Fr.leafAt hfr1 hN (N' := 0) (by rw [stack_eq]; decide) (fun r hr ↦ by cases hr)
    slots_le (outs_frame hn) hbl hpc trivial
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q h ↦ .inl h, hq.2.2⟩)
    fun m2 hfr2 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b0Offset + b0.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b0_next]]
  obtain ⟨hbl2, hs2, hsv2⟩ := hq
  have hvac : ∀ q, InRange (stackBelow st.data bitLengthStack) bitLengthStack q → False :=
    fun q hq ↦ by unfold InRange at hq; simp [bitLengthStack] at hq
  have hx0 : m2.regs.X0 = 3 := by
    apply UInt64.toNat_inj.mp
    rw [hbl2, show st.data.regs.X0 = 5 from hx5]
    decide
  have hmid2 : Mid m0 m2 :=
    Mid.call hn ⟨hfr1, hregs1, hpk1⟩ hfr2 hcs hs2 fun q hq ↦ (hvac q hq).elim
  have hts2 : TStateAt m2.dmem (tA m0) a s :=
    ts_keep hn hts1 hsv2.2.2 hs2 fun q hq ↦ (hvac q hq).elim
  have hcl2 : NativeRustcVm.Layout.ClaimsWAt m2.dmem (clA m0) cs :=
    cls_keep hn hcl1 hs2 fun q hq ↦ (hvac q hq).elim
  have h19 : m2.regs.getXReg .X19 = m0.regs.X4 :=
    (hcs .X19 rfl).trans (reg_of hm1 (v := .reg .X4) rfl rfl)
  have h28 : m2.regs.getXReg .X28 = m0.regs.X3 :=
    (hcs .X28 rfl).trans (reg_of hm1 (v := .reg .X3) rfl rfl)
  have h29 : m2.regs.getXReg .X29 = m0.regs.X7 :=
    (hcs .X29 rfl).trans (reg_of hm1 (v := .reg .X7) rfl rfl)
  -- `grind`
  have hwf2 := envM_wf hn hfr2
  refine callStep hn (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hfr2 (matchM hn hfr2) hwf2
    rfl (wOk_nil rfl) (N' := grindStack) (lo := 0) (n := 0) (by decide) (by decide) (hgr a s)
    (fun st2 hm2 hfr3 ↦ ?_) (fun st2 m3 hm2 hfr3 hq ↦ ?_) fun st2 m3 hm2 hfr3 hq hfr4 hcs3 ↦ ?_
  · have e0 : st2.regs.X0 = m0.regs.X0 :=
      (reg_of hm2 (r := .X0) (v := .reg .X20) rfl rfl).trans hmid2.regs.x20
    have hd : st2.dmem = m2.dmem := hm2.dmem_eq hwf2 rfl
    refine ⟨stackOk_of hn hfr3 (by decide), rcAt_of h hn hfr3 (by decide), ?_, ?_, ?_⟩
    · show TStateAt _ st2.regs.X0.toBitVec a s
      rw [e0, hd]; exact hts2
    · show TStateOk _ st2.regs.X0.toBitVec a _
      rw [e0]; exact tok_of hn hfr3 (by decide)
    · have : st2.regs.getXReg .X1 = 0 := reg_of hm2 (r := .X1)
        (v := .ite (.cmp .ult .W32 (.reg .X0) (.lit 3)) (.lit 0) (.bin .sub .W32 (.reg .X0)
            (.lit 3)))
        rfl (by sym_simp; simp only [Env.ofMachine_regs, gx0, hx0]; decide)
      unfold grindBits; rw [← gx1, this]; decide
  · have e0 : st2.regs.X0 = m0.regs.X0 :=
      (reg_of hm2 (r := .X0) (v := .reg .X20) rfl rfl).trans hmid2.regs.x20
    obtain ⟨-, -, hs3, hsv3⟩ := hq
    refine ⟨NativeRustcVm.SameOutside.mono hs3 fun q hq ↦ ?_, hsv3⟩
    rcases hq with hq | hq
    · exact .inr (.inr (.inl (by rw [e0] at hq; exact hq)))
    · exact .inl hq
  · rw [show k + NativeRustcVmArm.Vm.VerifyKeccak.b1Offset + b1.length = k + NativeRustcVmArm.Vm.VerifyKeccak.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.VerifyKeccak.b1_next]]
    have e0 : st2.regs.X0 = m0.regs.X0 :=
      (reg_of hm2 (r := .X0) (v := .reg .X20) rfl rfl).trans hmid2.regs.x20
    have hd : st2.dmem = m2.dmem := hm2.dmem_eq hwf2 rfl
    have hgb : grindBits st2 = gBits := by
      have : st2.regs.getXReg .X1 = 0 := reg_of hm2 (r := .X1)
        (v := .ite (.cmp .ult .W32 (.reg .X0) (.lit 3)) (.lit 0) (.bin .sub .W32 (.reg .X0)
            (.lit 3)))
        rfl (by sym_simp; simp only [Env.ofMachine_regs, gx0, hx0]; decide)
      unfold grindBits; rw [← gx1, this, gBits_eq]; rfl
    obtain ⟨hq0, hqn, hs3, hsv3⟩ := hq
    rw [hgb] at hq0 hqn
    have hmidS : Mid m0 st2 :=
      ⟨hfr3, hmid2.regs.block (matchM hn hfr2) hm2 (by decide), by rw [hd]; exact hmid2.pk⟩
    have hR : ∀ q, (InRange st2.regs.X0.toBitVec tstateBytes q ∨
        InRange (stackBelow st2 grindStack) grindStack q) →
        ((tA m0).toNat ≤ q.toNat ∧ q.toNat < (tA m0).toNat + 760) ∨
          (m0.regs.SP.toNat - 3360 - grindStack ≤ q.toNat ∧ q.toNat < m0.regs.SP.toNat - 3360) := by
      intro q hq
      rcases hq with hq | hq
      · rw [e0] at hq
        exact .inl (inR_nat (n := tstateBytes) hn.tW hq)
      · exact .inr (stk_nat hn hfr3 (by decide) hq)
    have hgs : grindStack = 544 := rfl
    refine cont m3 (Mid.call hn hmidS hfr4 hcs3 hs3 fun q hq ↦ ?_) ?_ ?_ ?_ hq0 ?_ ?_
    · rcases hR q hq with h1 | h1
      · have := hn.tS; omega
      · omega
    · rw [hcs3 .X19 rfl, Match.reg_eq (matchM hn hfr2) hm2 (r := .X19) rfl rfl, h19]
    · rw [hcs3 .X28 rfl, Match.reg_eq (matchM hn hfr2) hm2 (r := .X28) rfl rfl, h28]
    · rw [hcs3 .X29 rfl, Match.reg_eq (matchM hn hfr2) hm2 (r := .X29) rfl rfl, h29]
    · rw [e0] at hqn; exact hqn
    · rw [hd] at hs3
      refine cls_keep hn hcl2 hs3 fun q hq ↦ ?_
      rcases hR q hq with h1 | h1
      · have := hn.txc; omega
      · have := hn.cS; have := hn.hN; omega

end

end NativeRustcVmArm.KeccakGkr.VerifyKeccak
