module

public import NativeRustcVmArm.Code.Vm.Find.Names
public import NativeRustcVmArm.Wire.Find.Exec
public import NativeRustcVmArm.Wire.Common
public import NativeRustcVmArm.Spec.Wire
public import NativeRustcVm.Wire.WordsFacts

/-!
# `find` meets its contract

`find_spec`: the loop (`b2`, `b3`, `HInv`) reads node `i`'s key at `a + 40 i`; the key found, the
index back (`b5`); past the last node, `None` (`b4`). The keys are any words the caller names at
those addresses (`Miss`: no word there is the key).
-/

namespace NativeRustcVmArm.Wire.Find

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm.Wire
open NativeRustcVm (WordAt WordsAt)
open NativeRustcVmArm.Vm.Find

public section

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

/-- `x + (x << 2)` then `<< 3`: `40 x`. -/
theorem times40 {x : BitVec 64} (h : 40 * x.toNat < 2 ^ 64) :
    (UnOp.apply (.ubfm 61 60) .W64 (BinOp.apply .add .W64 x
      (UnOp.apply (.shift .LSL 2) .W64 x))).toNat = 40 * x.toNat := by
  rw [ubfm_lsl3]
  simp only [UnOp.apply, BinOp.apply, Sym.ext_W64, Sym.low_W64, shiftW, BitVec.toNat_shiftLeft,
    BitVec.toNat_add, Nat.shiftLeft_eq]
  omega

variable {m : MachineData}

/-- The nodes' address. -/
abbrev arr (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec

/-- Node `i`'s address, its key's. -/
abbrev nd (m : MachineData) (i : Nat) : BitVec 64 := arr m + BitVec.ofNat 64 (40 * i)

/-- The nodes' count. -/
abbrev cnt (m : MachineData) : Nat := m.regs.X1.toNat

/-- The keys before node `i` are not the key. -/
def Miss (m : MachineData) (i : Nat) : Prop := ∀ j < i, ∀ w, WordAt m.dmem (nd m j) w → w ≠ m.regs.X2

/-- What `find` reaches: its postcondition at the return address. -/
abbrev Post (m : MachineData) (st : MachineState) : Prop := st.pc = retOf m ∧ FindPost m st.data

/-- **The postcondition**, the key at node `i` (`some i`) or at none of the nodes (`none`). -/
theorem post_of {m' : MachineData} {o : Option Nat} (hsv : Saved m m') (hd : m'.dmem = m.dmem)
    (ho : match o with
      | some i => i < cnt m ∧ Miss m i ∧ (∀ w, WordAt m.dmem (nd m i) w → w = m.regs.X2) ∧
          m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = i
      | none => Miss m (cnt m) ∧ m'.regs.X0 = 0) :
    FindPost m m' := by
  refine ⟨fun ks hl hw ↦ ?_, hd, hsv⟩
  have hl' : ks.length = cnt m := hl
  have hne : ∀ j (hj : j < ks.length), Miss m (j + 1) → (ks[j] == m.regs.X2) = false :=
    fun j hj hM ↦ by simpa using hM j (by omega) _ (hw j hj)
  cases o with
  | some i =>
    obtain ⟨hi, hM, hk, h0, h1⟩ := ho
    have hi' : i < ks.length := by omega
    rw [(List.findIdx?_eq_some_iff_getElem).mpr ⟨hi', by simpa using hk _ (hw i hi'),
      fun j hj ↦ by simpa using hM j hj _ (hw j (by omega))⟩]
    exact ⟨h0, h1⟩
  | none =>
    obtain ⟨hM, h0⟩ := ho
    rw [List.findIdx?_eq_none_iff.mpr fun x hx ↦ by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      exact hne j hj fun j' hj' ↦ hM j' (by omega)]
    exact h0

variable [Host] (k : Nat) (m)

/-- The loop's head (`b2`) at node `i < n`. -/
structure HInv (i : Nat) (st : MachineState) : Prop where
  pc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Find.b2Offset)
  sv : Saved m st.data
  d : st.data.dmem = m.dmem
  x0 : st.data.regs.getXReg .X0 = 1
  x1 : (st.data.regs.getXReg .X1).toNat = i
  x2 : st.data.regs.getXReg .X2 = m.regs.getXReg .X2
  x8 : (st.data.regs.getXReg .X8).toBitVec = nd m i
  x9 : (st.data.regs.getXReg .X9).toNat = 40 * (cnt m - i)
  x30 : st.data.regs.getXReg .X30 = m.regs.getXReg .X30
  lt : i < cnt m
  miss : Miss m i

variable {k m}

section
variable (hp : Placed code k) (hok : NativeRustcVm.Region.Ok m.dmem ⟨arr m, 40 * cnt m⟩)
include hp hok

omit hok in
/-- **The return** (`b5`) from a state that keeps `m`'s X30, callee-saved registers and SP. -/
theorem ret_spec {o : Option Nat} {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Find.b5Offset))
    (hsv : Saved m st.data) (hd : st.data.dmem = m.dmem)
    (h30 : st.data.regs.getXReg .X30 = m.regs.getXReg .X30)
    (ho : match o with
      | some i => i < cnt m ∧ Miss m i ∧ (∀ w, WordAt m.dmem (nd m i) w → w = m.regs.X2) ∧
          st.data.regs.X0 = 1 ∧ st.data.regs.X1.toNat = i
      | none => Miss m (cnt m) ∧ st.data.regs.X0 = 0) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hwf := Env.wf_nil st.data
  have hm := match_nil st.data
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) run_b5 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hd' : st'.data.dmem = st.data.dmem := hm'.dmem_eq hwf rfl
  have hr : ∀ r, st'.data.regs.getXReg r = st.data.regs.getXReg r := fun r ↦
    Match.reg_eq hm hm' (v := .reg r) (by cases r <;> rfl) (by cases r <;> rfl)
  refine .done _ ⟨by rw [hpc', retOf, retOf, show st'.data.regs.X30 = m.regs.X30 from
    (hr .X30).trans h30], post_of (o := o) (hsv.trans (Match.saved hm hm' hwf rfl (by decide)))
    (hd'.trans hd) ?_⟩
  cases o with
  | some i => exact ho.imp_right fun h ↦ h.imp_right fun h ↦ h.imp_right fun h ↦
      ⟨(hr .X0).trans h.1, (congrArg UInt64.toNat (hr .X1)).trans h.2⟩
  | none => exact ⟨ho.1, (hr .X0).trans ho.2⟩

omit hok in
/-- **`None`** (`b4`, then the return): no node's key the key. -/
theorem none_spec {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.Find.b4Offset))
    (hsv : Saved m st.data) (hd : st.data.dmem = m.dmem)
    (h30 : st.data.regs.getXReg .X30 = m.regs.getXReg .X30) (hM : Miss m (cnt m)) :
    Eventually (step1 Host.exe) (Post m) st := by
  have hwf := Env.wf_nil st.data
  have hm := match_nil st.data
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) run_b4 hwf hpc hm fun st' hm' hpc' ↦ ?_
  simp only [PcOk] at hpc'
  exact ret_spec hp (o := none) (hpc'.trans (congrArg Host.addrOf rfl))
    (hsv.trans (Match.saved hm hm' hwf rfl (by decide))) ((hm'.dmem_eq hwf rfl).trans hd)
    ((Match.reg_eq hm hm' (v := .reg .X30) rfl rfl).trans h30)
    ⟨hM, UInt64.toBitVec_inj.mp (hm'.regs .X0 _ rfl)⟩

omit [Host] hp in
theorem nd_mapped {i : Nat} (hi : i < cnt m) : NativeRustcVm.Mapped m.dmem (nd m i) 8 :=
  hok.1.sub (o := 40 * i) (m := 8) (show 40 * i + 8 ≤ 40 * cnt m by omega)

/-- **A step of the loop** (`b2`, then `b5` or `b3`): node `i`'s key, the key or not. -/
theorem step_spec {i : Nat} {st : MachineState} (hI : HInv m k i st) :
    Eventually (step1 Host.exe)
      (fun st' ↦ Post m st' ∨ ∃ n' < cnt m - i, ∃ i', n' = cnt m - i' ∧ HInv m k i' st') st := by
  have hnw : NativeRustcVm.NoWrap (arr m) (40 * cnt m) := hok.2
  have hmap := nd_mapped hok hI.lt
  have hwf : (Env.ofMachine st.data [(nd m i, 8)]).WF :=
    Env.wf_of ⟨⟨by show NativeRustcVm.Mapped st.data.dmem (nd m i) 8; rw [hI.d]; exact hmap,
      hnw.sub (o := 40 * i) (by have := hI.lt; omega)⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine st.data [(nd m i, 8)]) headS st.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl trivial trivial trivial
      ⟨by
        show (st.data.regs.getXReg .X8).toBitVec = nd m i + BitVec.ofInt 64 0
        rw [hI.x8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero], trivial⟩
  obtain ⟨w, hw⟩ := NativeRustcVm.Wire.exists_wordAt hmap
  have hld : (Env.ofMachine st.data [(nd m i, 8)]).load 0 0 8 = w.toBitVec :=
    load_word (by
      rw [Env.base_ofMachine _ _ _ (b := nd m i) (n := 8) rfl, NativeRustcVm.addr_add_zero,
        Env.ofMachine_mem0, hI.d]
      exact hw)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) run_b2 hwf hI.pc hm fun s2 hm2 hpc2 ↦ ?_
  have hd2 : s2.data.dmem = st.data.dmem := hm2.dmem_eq hwf rfl
  have hsv2 : Saved m s2.data := hI.sv.trans (Match.saved hm hm2 hwf rfl (by decide))
  have h30 : s2.data.regs.getXReg .X30 = m.regs.getXReg .X30 :=
    (Match.reg_eq hm hm2 (v := .reg .X30) rfl rfl).trans hI.x30
  have hc : (SBool.cmp .eq .W64 (.load 0 0 8) (.reg .X2)).eval
      (Env.ofMachine st.data [(nd m i, 8)]) = decide (w = m.regs.X2) := by
    simp only [SBool.eval, eq_apply, Sym.eval, hld, Env.ofMachine_regs, hI.x2]
    by_cases h : w = m.regs.X2
    · simp [h]; rfl
    · simp only [h, decide_false, decide_eq_false_iff_not]
      exact fun h' ↦ h (UInt64.toNat_inj.mp h')
  simp only [PcOk, hc] at hpc2
  by_cases hk : w = m.regs.X2
  · -- found: `b5`
    simp only [hk, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Find.b5Offset) NativeRustcVmArm.Vm.Find.label_5_at] at hpc2
    refine Eventually.mono (ret_spec hp (o := some i) hpc2 hsv2 (hd2.trans hI.d) h30
      ⟨hI.lt, hI.miss, fun w' hw' ↦ (hw'.unique hw).trans hk, ?_, ?_⟩) fun _ h ↦ .inl h
    · exact (Match.reg_eq hm hm2 (v := .reg .X0) rfl rfl).trans hI.x0
    · exact (congrArg UInt64.toNat (Match.reg_eq hm hm2 (v := .reg .X1) rfl rfl)).trans hI.x1
  simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc2
  have hM : Miss m (i + 1) := fun j hj w' hw' ↦ by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | rfl
    · exact hI.miss j h w' hw'
    · rw [hw'.unique hw]; exact hk
  have r3 := run_b3
  rw [after_eq run_b2] at r3
  refine exec_at (infix_of b3_in_code (by simp [b3]) hp) r3 hwf hpc2 hm2 fun s3 hm3 hpc3 ↦ ?_
  have hd3 : s3.data.dmem = st.data.dmem := hm3.dmem_eq hwf rfl
  have hsv3 : Saved m s3.data := hI.sv.trans (Match.saved hm hm3 hwf rfl (by decide))
  have h30' : s3.data.regs.getXReg .X30 = m.regs.getXReg .X30 :=
    (Match.reg_eq hm hm3 (v := .reg .X30) rfl rfl).trans hI.x30
  have hlt := hI.lt
  have hn40 : 40 * cnt m < 2 ^ 64 := by unfold NativeRustcVm.NoWrap at hnw; omega
  have e9 : ((Sym.reg .X9).eval (Env.ofMachine st.data [(nd m i, 8)])).toNat =
      40 * (cnt m - i) := hI.x9
  have e40 : ((Sym.lit 40).eval (Env.ofMachine st.data [(nd m i, 8)])).toNat = 40 := rfl
  have hc3 : (SBool.cmp .eq .W64 (.reg .X9) (.lit 40)).not.eval
      (Env.ofMachine st.data [(nd m i, 8)]) = decide (i + 1 ≠ cnt m) := by
    simp only [SBool.eval, eq_apply]
    rw [e9, e40]
    by_cases h : i + 1 = cnt m
    · rw [decide_eq_true (show 40 * (cnt m - i) = 40 by omega),
        decide_eq_false (show ¬(i + 1 ≠ cnt m) from not_not.mpr h)]
      rfl
    · rw [decide_eq_false (show ¬40 * (cnt m - i) = 40 by omega), decide_eq_true h]
      rfl
  simp only [PcOk, hc3] at hpc3
  by_cases hend : i + 1 = cnt m
  · -- past the last node: `b4`
    simp only [hend, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      at hpc3
    exact Eventually.mono (none_spec hp (hpc3.trans (congrArg Host.addrOf rfl)) hsv3
      (hd3.trans hI.d) h30' (hend ▸ hM)) fun _ h ↦ .inl h
  simp only [ne_eq, hend, not_false_eq_true, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Find.b2Offset) NativeRustcVmArm.Vm.Find.label_2_at]
    at hpc3
  refine .done _ (.inr ⟨_, by omega, i + 1, rfl, ⟨hpc3, hsv3, hd3.trans hI.d, ?_, ?_,
    (Match.reg_eq hm hm3 (v := .reg .X2) rfl rfl).trans hI.x2, ?_, ?_, h30', by omega, hM⟩⟩)
  · exact (Match.reg_eq hm hm3 (v := .reg .X0) rfl rfl).trans hI.x0
  · show (s3.data.regs.getXReg .X1).toBitVec.toNat = _
    rw [hm3.regs .X1 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (st.data.regs.getXReg .X1).toBitVec.toNat = i := hI.x1
    omega
  · rw [hm3.regs .X8 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs]
    rw [hI.x8, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · show (s3.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [hm3.regs .X9 _ rfl]
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs,
      BitVec.toNat_sub, BitVec.toNat_ofNat]
    have : (st.data.regs.getXReg .X9).toBitVec.toNat = 40 * (cnt m - i) := hI.x9
    omega

/-- **From the entry** (`b0`): `None` for no nodes, else the loop from node `0` (`b1`). -/
theorem entry_spec : Eventually (step1 Host.exe) (Post m) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.Find.b0Offset)⟩ := by
  have hnw : NativeRustcVm.NoWrap (arr m) (40 * cnt m) := hok.2
  have hn40 : 40 * cnt m < 2 ^ 64 := by unfold NativeRustcVm.NoWrap at hnw; omega
  have hwf := Env.wf_nil m
  have hm := match_nil m
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) run_b0 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hd1 : s1.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have hsv1 : Saved m s1.data := Match.saved hm hm1 hwf rfl (by decide)
  have hr1 : ∀ r, s1.data.regs.getXReg r = m.regs.getXReg r := fun r ↦
    Match.reg_eq hm hm1 (v := .reg r) (by cases r <;> rfl) (by cases r <;> rfl)
  have hc : (SBool.cmp .eq .W64 (.reg .X1) (.lit 0)).eval (Env.ofMachine m []) =
      decide (cnt m = 0) := by
    simp only [SBool.eval, eq_apply]
    rfl
  simp only [PcOk, hc] at hpc1
  by_cases h0 : cnt m = 0
  · simp only [h0, decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Find.b4Offset) NativeRustcVmArm.Vm.Find.label_4_at] at hpc1
    exact none_spec hp hpc1 hsv1 hd1 (hr1 .X30) (h0 ▸ fun _ h ↦ absurd h (Nat.not_lt_zero _))
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hwf2 := Env.wf_nil s1.data
  have hm2 := match_nil s1.data
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf2
    (hpc1.trans (congrArg Host.addrOf rfl)) hm2 fun s2 hm2' hpc2 ↦ ?_
  have hd2 : s2.data.dmem = s1.data.dmem := hm2'.dmem_eq hwf2 rfl
  have hr2 : ∀ r ∈ [XReg.X2, .X30], s2.data.regs.getXReg r = m.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (Match.reg_eq hm2 hm2' (v := .reg .X2) rfl rfl).trans (hr1 .X2)
    · exact (Match.reg_eq hm2 hm2' (v := .reg .X30) rfl rfl).trans (hr1 .X30)
  simp only [PcOk] at hpc2
  refine Sym.loop (fun n st ↦ ∃ i, n = cnt m - i ∧ HInv m k i st)
    (fun n st ⟨i, hn', hI⟩ ↦ hn' ▸ step_spec hp hok hI)
    ⟨0, rfl, hpc2.trans (congrArg Host.addrOf rfl),
      hsv1.trans (Match.saved hm2 hm2' hwf2 rfl (by decide)), hd2.trans hd1, ?_, ?_,
      hr2 .X2 (by simp), ?_, ?_, hr2 .X30 (by simp), by omega,
      fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  · exact UInt64.toBitVec_inj.mp (hm2'.regs .X0 _ rfl)
  · show (s2.data.regs.getXReg .X1).toBitVec.toNat = 0
    rw [hm2'.regs .X1 _ rfl]
    rfl
  · rw [hm2'.regs .X8 _ rfl]
    show (s1.data.regs.getXReg .X0).toBitVec = m.regs.X0.toBitVec + BitVec.ofNat 64 (40 * 0)
    rw [hr1 .X0, show BitVec.ofNat 64 (40 * 0) = 0#64 from rfl, BitVec.add_zero]
    rfl
  · show (s2.data.regs.getXReg .X9).toBitVec.toNat = _
    rw [hm2'.regs .X9 _ rfl]
    have h1 : (s1.data.regs.getXReg .X1).toBitVec.toNat = cnt m := by rw [hr1 .X1]; rfl
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [times40 (by rw [h1]; exact hn40), h1, Nat.sub_zero]

end

/-- **`find` meets its contract.** -/
theorem find_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmArm.Vm.Find.entryLabel) FindPre FindPost := by
  intro m ⟨_, hok⟩
  rw [hp.label (j := NativeRustcVmArm.Vm.Find.entryOffset) NativeRustcVmArm.Vm.Find.entry_at]
  exact entry_spec hp hok

end

end NativeRustcVmArm.Wire.Find
