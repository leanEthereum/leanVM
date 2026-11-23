module

public import NativeRustcVmX64.Field.EWSqIter.Exec
public import NativeRustcVmX64.Field.Call
public import NativeRustcVmX64.Field.W32
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names

/-!
# `EW::sq_iter` on x86-64

`ewSqIter_spec`: rustc's `EW::sq_iter(k, x)`, placed anywhere in the program, given `EW::mul`'s
contract, returns `EW.sqIter k x` (`x^(2^k)`). Its first block (`b0`) moves `x` to RAX, RCX and
returns at once for `k = 0` (through `b5`); else, from the state it leaves (`m0`, the entry's but
for RAX and RCX), the push of RBX keeps the count in RBX, the loop's head (`Inv`) holds the
element squared `i` times in RAX, RCX and `k - i` in RBX, and the pop (`b4`) and `b5` return it
in RAX, RDX (`Post`).
-/

namespace NativeRustcVmX64.Field.EWSqIter

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.EWSqIter
open NativeVm.Model (EW)

@[expose] public section

/-- The pushed registers' slots. -/
def slots : List (Reg64 × Nat) := [(.rbx, 8)]

/-- The callee-saved registers it uses. -/
def used : List Reg64 := [.rbx]

/-- The element in RAX, RCX. -/
def elt (m : MachineData) : EW := ⟨.ofBitVec (reg m .rax), .ofBitVec (reg m .rcx)⟩

/-- The result, from the state after `b0`. -/
def target (m0 : MachineData) : EW := EW.sqIter (reg m0 .rdi).toNat (elt m0)

end

public section

variable [Host] {k : Nat}

theorem hb (hp : Placed code k) {ds : List Directive} {j : Nat} (h : ds.IsInfixAt code j)
    (hne : ds ≠ []) : ds.IsInfixAt Host.prog (k + j) :=
  h.trans hp.1 hne

/-- **The loop's head** `NativeRustcVmX64.Vm.EWSqIter.label_2`, `j ≥ 1` squarings left. -/
structure Inv (m0 m1 : MachineData) (k j : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EWSqIter.b2Offset)
  pos : 0 < j
  fr : Fr m0 m1 16 ewSqIterStack 8 used st.data
  rbx : (reg st.data .rbx).toNat = j
  val : EW.sqIter j (elt st.data) = target m0

/-- The return, from the state after `b0`. -/
abbrev Post (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
    reg st.data .rax = (target m0).c0.toBitVec ∧ reg st.data .rdx = (target m0).c1.toBitVec ∧
    SameOutside m0.dmem st.data.dmem (InRange (stackBelow m0 ewSqIterStack) ewSqIterStack) ∧
    Saved m0 st.data

/-- From the pop, with the result in RAX, RCX. -/
theorem finish (hp : Placed code k) {m0 m1 d : MachineData} (g : Geo m0 16 ewSqIterStack)
    (hsl : Slots m0 m1 16 slots) (hF : Fr m0 m1 16 ewSqIterStack 8 used d)
    (hv : elt d = target m0) :
    Eventually (step1 Host.exe) (Post m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.EWSqIter.b4Offset)⟩ := by
  refine Eventually.bind (epilogue g hF hsl (vars := fun _ ↦ 0)
    (hb hp b4_in_code (List.cons_ne_nil _ _)) run_b4 (by decide +kernel) rfl)
    fun st ⟨hm, hpc, hso, hsv⟩ ↦ ?_
  simp only [PcOk] at hpc
  obtain ⟨d4, pc4⟩ := st
  simp only [show k + NativeRustcVmX64.Vm.EWSqIter.b4Offset + b4.length = k + NativeRustcVmX64.Vm.EWSqIter.b5Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EWSqIter.b4_next]] at hpc
  subst hpc
  simp only at hm hso hsv
  have hrsp : rspOf d4 = rspOf m0 := (hm.regs .rsp _ rfl).trans frame_top
  refine Eventually.mono (ret_blk (StackOk.mono g.ok (by decide)) hrsp hsv.2 (g.ret_same hso)
    (vars := fun _ ↦ 0) (hb hp b5_in_code (List.cons_ne_nil _ _)) run_b5 rfl (by decide +kernel)
    rfl) fun st ⟨hm5, hret, hrsp5, hd5, hsv5⟩ ↦ ⟨hret, hrsp5, ?_, ?_, ?_, hsv.trans hsv5⟩
  · rw [show reg st.data .rax = reg d4 .rax from hm5.regs .rax _ rfl,
      show reg d4 .rax = reg d .rax from hm.regs .rax _ rfl, ← hv]
    rfl
  · rw [show reg st.data .rdx = reg d4 .rcx from hm5.regs .rdx _ rfl,
      show reg d4 .rcx = reg d .rcx from hm.regs .rcx _ rfl, ← hv]
    rfl
  · intro p hp'
    rw [hd5]
    exact hso p hp'

/-- **One squaring**: from the loop's head, back to it or returned. -/
theorem step (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 m1 : MachineData} (g : Geo m0 16 ewSqIterStack) (hsl : Slots m0 m1 16 slots) {j : Nat}
    {st : MachineState} (hI : Inv m0 m1 k j st) :
    Eventually (step1 Host.exe) (fun st' ↦ Post m0 st' ∨ Inv m0 m1 k (j - 1) st') st := by
  obtain ⟨d, pc⟩ := st
  obtain ⟨hpc, hj, hF, hbx, hv⟩ := hI
  simp only at hpc hF hbx hv
  subst hpc
  refine block g hF (vars := fun _ ↦ 0) (hb hp b2_in_code (List.cons_ne_nil _ _)) run_b2 (o := 0)
    rfl (by decide) (by decide +kernel) fun st1 hm1 hpc1 hF1 ↦ ?_
  have h1di : reg st1.data .rdi = reg d .rax := hm1.regs .rdi _ rfl
  have h1si : reg st1.data .rsi = reg d .rcx := hm1.regs .rsi _ rfl
  have h1dx : reg st1.data .rdx = reg d .rax := hm1.regs .rdx _ rfl
  have h1cx : reg st1.data .rcx = reg d .rcx := hm1.regs .rcx _ rfl
  have h1bx : reg st1.data .rbx = reg d .rbx := hm1.regs .rbx _ rfl
  refine call g hF1 hpc1 (S := ewMulStack) (by decide) hmul id (fun _ _ h ↦ h.2.2)
    fun st2 hpc2 hq hF2 ↦ ?_
  have hsq : (⟨.ofBitVec (reg st2.data .rax), .ofBitVec (reg st2.data .rdx)⟩ : EW) =
      elt d * elt d := by
    rw [hq.1, hq.2.1, h1di, h1si, h1dx, h1cx, UInt64.ofBitVec_toBitVec,
      UInt64.ofBitVec_toBitVec]
    rfl
  have h2bx : reg st2.data .rbx = reg d .rbx := (hq.2.2.2.1 .rbx rfl).trans h1bx
  obtain ⟨d2, pc2⟩ := st2
  simp only [show k + NativeRustcVmX64.Vm.EWSqIter.b2Offset + b2.length = k + NativeRustcVmX64.Vm.EWSqIter.b3Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EWSqIter.b2_next]] at hpc2
  subst hpc2
  simp only at hF2 hsq h2bx
  refine block g hF2 (vars := fun _ ↦ 0) (hb hp b3_in_code (List.cons_ne_nil _ _)) run_b3 (o := 8)
    rfl (by decide) (by decide +kernel) fun st3 hm3 hpc3 hF3 ↦ ?_
  have hb2 : (reg d2 .rbx).toNat = j := (congrArg BitVec.toNat h2bx).trans hbx
  have h3bx : (reg st3.data .rbx).toNat = j - 1 := by
    rw [show reg st3.data .rbx = _ from hm3.regs .rbx _ rfl]
    show (BinOp.apply .sub .W64 (reg d2 .rbx) (BitVec.ofNat 64 1)).toNat = _
    rw [sub64_toNat (by omega), hb2]
  have hv' : EW.sqIter (j - 1) (elt st3.data) = target m0 := by
    rw [show elt st3.data = elt d * elt d by
      rw [← hsq, elt, show reg st3.data .rax = reg d2 .rax from hm3.regs .rax _ rfl,
        show reg st3.data .rcx = reg d2 .rdx from hm3.regs .rcx _ rfl], ← hv]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rfl
  simp only [PcOk] at hpc3
  have hc : (SBool.not (.cmp .eq .W64 (.bin .sub .W64 (.reg .rbx) (.lit 1)) (.lit 0))).eval
      (frameEnv m0 d2 16 (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.EWSqIter.b3Offset + b3.length)).toBitVec) =
      !decide (j = 1) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, eq64_zero]
    rw [sub64_toNat (show 1 ≤ (d2.regs.get64 .rbx).toNat by
      show 1 ≤ (reg d2 .rbx).toNat; omega)]
    rw [show (d2.regs.get64 .rbx).toNat = j from hb2]
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega
  rw [hc] at hpc3
  by_cases hlast : j = 1
  · simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ite_false] at hpc3
    obtain ⟨d3, pc3⟩ := st3
    simp only [show k + NativeRustcVmX64.Vm.EWSqIter.b3Offset + b3.length = k + NativeRustcVmX64.Vm.EWSqIter.b4Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EWSqIter.b3_next]] at hpc3
    subst hpc3
    simp only at hF3 hv'
    refine Eventually.mono (finish hp g hsl hF3 ?_) fun _ h ↦ Or.inl h
    rw [← hv', hlast]
    rfl
  · simp only [hlast, decide_false, Bool.not_false, ite_true] at hpc3
    exact .done _ (Or.inr ⟨hpc3.trans (hp.label NativeRustcVmX64.Vm.EWSqIter.label_2_at), by omega, hF3, h3bx, hv'⟩)

/-- **`EW::sq_iter` squares `k` times.** -/
theorem ewSqIter_spec (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) :
    Spec (Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.EWSqIter.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.EWSqIter.b0Offset) from hp.label NativeRustcVmX64.Vm.EWSqIter.entry_at]
  have h16 : StackOk m0 16 := StackOk.mono hpre (by decide)
  have hwf := frame_wf (m := m0) (vars := fun _ ↦ 0) (ret := 0) h16 fun _ h ↦ h
  refine exec_then (hb hp b0_in_code (List.cons_ne_nil _ _)) run_b0 hwf nofun match_frame
    fun st0 hm0 hpc0 ↦ ?_
  have hd0 : st0.data.dmem = m0.dmem := hm0.dmem_eq hwf rfl
  have hrsp0 : rspOf st0.data = rspOf m0 := (hm0.regs .rsp _ rfl).trans frame_top
  have hsv0 : Saved m0 st0.data := Match.saved match_frame hm0 hwf rfl (by decide +kernel)
  have h0ax : reg st0.data .rax = reg m0 .rsi := hm0.regs .rax _ rfl
  have h0cx : reg st0.data .rcx = reg m0 .rdx := hm0.regs .rcx _ rfl
  have h0di : reg st0.data .rdi = reg m0 .rdi := hm0.regs .rdi _ rfl
  have htarget : target st0.data =
      EW.sqIter (reg m0 .rdi).toNat ⟨.ofBitVec (reg m0 .rsi), .ofBitVec (reg m0 .rdx)⟩ := by
    rw [target, elt, h0ax, h0cx, h0di]
  have hsb : stackBelow st0.data ewSqIterStack = stackBelow m0 ewSqIterStack := by
    simp only [stackBelow, hrsp0]
  have hret0 : retOf st0.data = retOf m0 := retOf_eq hrsp0 fun _ _ ↦ by rw [hd0]
  -- From the state after `b0`, its postcondition is the entry's.
  have conv : ∀ st, Post st0.data st → st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧
      EWSqIterPost m0 st.data := fun st ⟨hpc, hrsp, hax, hdx, hso, hsv⟩ ↦
    ⟨hpc.trans hret0, hrsp.trans (by rw [hrsp0]), hax.trans (by rw [htarget]),
      hdx.trans (by rw [htarget]), fun p hp' ↦ by rw [hso p (hsb ▸ hp'), hd0], hsv0.trans hsv⟩
  simp only [PcOk] at hpc0
  have hc : (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdi) (.reg .rdi)) (.lit 0)).eval
      (frameEnv m0 m0 16 (fun _ ↦ 0)) = decide ((reg m0 .rdi).toNat = 0) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs, and_self_apply, eq64_zero]
  rw [hc] at hpc0
  have hk0 : Kept m0.dmem st0.data.dmem := by rw [hd0]; exact fun _ h ↦ h
  by_cases hz : (reg m0 .rdi).toNat = 0
  · simp only [hz, decide_true, ite_true] at hpc0
    obtain ⟨d0, pc0⟩ := st0
    simp only at hpc0
    rw [hp.label NativeRustcVmX64.Vm.EWSqIter.label_4_at] at hpc0
    subst hpc0
    simp only at hd0 hrsp0 hsv0 h0ax h0cx hk0 conv
    refine Eventually.mono (ret_blk h16 hrsp0 hk0 (fun _ _ ↦ by rw [hd0]) (vars := fun _ ↦ 0)
      (hb hp b5_in_code (List.cons_ne_nil _ _)) run_b5 rfl (by decide +kernel) rfl)
      fun st ⟨hm5, hret, hrsp5, hd5, hsv5⟩ ↦ ⟨hret, hrsp5, ?_, ?_, ?_, hsv0.trans hsv5⟩
    · rw [show reg st.data .rax = reg d0 .rax from hm5.regs .rax _ rfl, h0ax, hz]
      rfl
    · rw [show reg st.data .rdx = reg d0 .rcx from hm5.regs .rdx _ rfl, h0cx, hz]
      rfl
    · intro p _
      rw [hd5, hd0]
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false] at hpc0
    obtain ⟨d0, pc0⟩ := st0
    simp only [show k + NativeRustcVmX64.Vm.EWSqIter.b0Offset + b0.length = k + NativeRustcVmX64.Vm.EWSqIter.b1Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EWSqIter.b0_next]] at hpc0
    subst hpc0
    simp only at hd0 hrsp0 hsv0 h0di hk0 conv
    have g : Geo d0 16 ewSqIterStack :=
      ⟨StackOk.transfer hpre hrsp0 hk0, by decide, by decide⟩
    refine Eventually.mono ?_ conv
    refine prologue (used := used) (slots := slots) (vars := fun _ ↦ 0) g
      (hb hp b1_in_code (List.cons_ne_nil _ _)) run_b1 (o := 8) rfl (by decide +kernel)
      (by decide +kernel) (by decide +kernel) fun st1 hm1 hpc1 hF1 hsl ↦ ?_
    simp only [PcOk, show k + NativeRustcVmX64.Vm.EWSqIter.b1Offset + b1.length = k + NativeRustcVmX64.Vm.EWSqIter.b2Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EWSqIter.b1_next]] at hpc1
    have hI : Inv d0 st1.data k (reg d0 .rdi).toNat st1 := by
      refine ⟨hpc1, Nat.pos_of_ne_zero (by rw [h0di]; exact hz), hF1, ?_, ?_⟩
      · rw [show reg st1.data .rbx = reg d0 .rdi from hm1.regs .rbx _ rfl]
      · rw [elt, show reg st1.data .rax = reg d0 .rax from hm1.regs .rax _ rfl,
          show reg st1.data .rcx = reg d0 .rcx from hm1.regs .rcx _ rfl]
        rfl
    exact Sym.loop (fun μ st ↦ ∃ j, μ = j ∧ Inv d0 st1.data k j st)
      (fun _ _ ⟨j, hμ, hI⟩ ↦ Eventually.mono (step hp hmul g hsl hI) fun st' h ↦
        h.imp_right fun h' ↦ ⟨j - 1, by have := hI.pos; omega, j - 1, rfl, h'⟩)
      ⟨_, rfl, hI⟩

end

end NativeRustcVmX64.Field.EWSqIter
