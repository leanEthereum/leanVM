module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Ring.Coeff.Env
public import NativeRustcVmArm.Ring.Coeff.Model

/-!
# `ring_coefficients`: the loop's blocks

Each block of turn `p` from the loop's environment (`midS`), checked by `decide` on its literal
result: the head (`b1`, `stepHead`: `f_p`, the counter saved, `f_p · G_0`), a product block
(`b2` to `b8`, `stepMul`), the first Frobenius block (`b9`, `stepSq0`: the last product stored,
`G_0`'s image), a Frobenius block (`b10` to `b16`, `stepSq`).
-/

namespace NativeRustcVmArm.Ring.Coeff

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- **The head**: `f_p` in X0, X1 and X24, X25, `G_0` in X2, X3, the counter (X10) saved. -/
def headOk (S : SState) : Bool :=
  S.reg .X0 == some (.load 2 0 8) && S.reg .X1 == some (.load 2 8 8) &&
    S.reg .X24 == some (.load 2 0 8) && S.reg .X25 == some (.load 2 8 8) &&
    S.reg .X2 == some (gLoc 0).1 && S.reg .X3 == some (gLoc 0).2 && ptrsOk S && gKeep 8 S &&
    locSet 176 S (.reg .X10) cntLoc && wrOk 128 128 S

/-- **The first Frobenius block**: the last product stored at row byte `112`, `G_0` squared. -/
def sq0Ok (S : SState) : Bool :=
  S.reg .X0 == some (.lit 8) && S.reg .X1 == some (gLoc 0).1 && S.reg .X2 == some (gLoc 0).2 &&
    S.reg .X24 == some (.reg .X24) && S.reg .X25 == some (.reg .X25) && ptrsOk S &&
    gKeep 8 S && locKeep 176 S cntLoc && rowSet 112 S && wrOk 112 128 S

end

public section

variable {m0 : MachineData} {p : Nat}

/-! ## Facts the steps share -/

theorem reg_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

theorem mulQ : ∀ m m', EWMulPost m m' → SameOutside m.dmem m'.dmem
    (fun q ↦ InRange (stackBelow m ewMulStack) ewMulStack q ∨ InRange (oA m0) 1024 q) ∧
      Saved m m' :=
  fun _ _ h ↦ ⟨NativeRustcVm.SameOutside.mono h.2.2.1 fun _ hq ↦ .inl hq, h.2.2.2⟩

theorem sqQ : ∀ m m', EWSqIterPost m m' → SameOutside m.dmem m'.dmem
    (fun q ↦ InRange (stackBelow m ewSqIterStack) ewSqIterStack q ∨ InRange (oA m0) 1024 q) ∧
      Saved m m' :=
  fun _ _ h ↦ ⟨NativeRustcVm.SameOutside.mono h.2.2.1 fun _ hq ↦ .inl hq, h.2.2.2⟩

theorem keep_nil : ∀ r ∈ ([] : List XReg), calleeSaved r = true := by simp

/-- `f`'s words are the entry's in every state of the frame. -/
theorem f_word (h : P m0) {m : MachineData} (hfr : CFr m0 m) {o : Nat} (ho : o + 8 ≤ 128) :
    NativeRustcVm.wordOf m.dmem (fA m0 + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (fA m0 + BitVec.ofNat 64 o) :=
  NativeRustcVm.wordOf_congr fun i hi ↦ by
    apply hfr.same
    rw [NativeRustcVm.addr_add_add]
    rintro (hq | hq)
    · exact NativeRustcVm.Apart.not_inRange_add h.fs h.fw
        (base_noWrap h.hN) (i := o + i) (by omega) hq
    · exact NativeRustcVm.Apart.not_inRange_add h.of.symm h.fw h.ow (i := o + i) (by omega) hq

/-- The row's element `j` is `out`'s element `8 p + j`. -/
theorem row_addr {j : Nat} :
    rowA m0 p + BitVec.ofNat 64 (16 * j) = oA m0 + BitVec.ofNat 64 (16 * (8 * p + j)) := by
  rw [rowA, NativeRustcVm.addr_add_add]
  congr 2
  omega

/-- **A stored element**: X0, X1 (of `m`) stored at the row's bytes `16 j`, `16 j + 8`. -/
theorem row_elt [Labels] {m m' : MachineData} {S' : SState}
    (hm1 : Match (envB m0 p m) S' m') {j : Nat} (hj : j < 8) (hs : rowSet (16 * j) S' = true) :
    NativeRustcVm.EWAt m'.dmem (oA m0 + BitVec.ofNat 64 (16 * (8 * p + j)))
      ⟨m.regs.getXReg .X0, m.regs.getXReg .X1⟩ := by
  simp only [rowSet, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hs
  have w0 := hm1.bytesAt_write (r := 1) (o := 16 * j) (n := 8) (b := rowA m0 p) (sz := 128) rfl
    (by omega) (v := .reg .X0) fun i hi ↦ (hs i hi).1
  have w1 := hm1.bytesAt_write (r := 1) (o := 16 * j + 8) (n := 8) (b := rowA m0 p) (sz := 128)
    rfl (by omega) (v := .reg .X1) fun i hi ↦ (hs i hi).2
  rw [wordBytes_reg] at w0 w1
  rw [← row_addr, NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
  exact ⟨w0, w1⟩

variable [Host]

/-! ## The head -/

/-- **The head** (`b1`): `f_p · G_0`. -/
theorem stepHead (h : P m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat}
    {ds : List Directive} {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hS : headOk S' = true) {m : MachineData}
    (hH : Head m0 p m) {R : MachineState → Prop}
    (cont : ∀ m2, MulD m0 p 0 m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := body_wf h hH.toBody
  refine exec_then hk hrun hwf (body_match h hH.toBody) fun st hm1 hpc ↦ ?_
  simp only [headOk, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h24⟩, h25⟩, h2⟩, h3⟩, hptr⟩, hg⟩, hc⟩, hwr⟩ := hS
  obtain ⟨hB1, hout1⟩ := after_block h hH.toBody hm1 hptr hwr (le_refl _) (le_refl _)
  have hp := hH.lt
  have hfE0 : (Sym.load 2 0 8).eval (envB m0 p m) = (fE m0 p).c0.toBitVec := by
    simp only [Sym.eval]
    rw [load_eq_wordOf, NativeRustcVm.addr_add_zero]
    show _ = (NativeRustcVm.wordOf m0.dmem _).toBitVec
    rw [show (envB m0 p m).base 2 = fA m0 + BitVec.ofNat 64 (16 * p) from rfl,
      show (envB m0 p m).mem0 = m.dmem from rfl, f_word h hH.fr (by omega)]
  have hfE1 : (Sym.load 2 8 8).eval (envB m0 p m) = (fE m0 p).c1.toBitVec := by
    simp only [Sym.eval]
    rw [load_eq_wordOf]
    show _ = (NativeRustcVm.wordOf m0.dmem _).toBitVec
    rw [show (envB m0 p m).base 2 = fA m0 + BitVec.ofNat 64 (16 * p) from rfl,
      show (envB m0 p m).mem0 = m.dmem from rfl, NativeRustcVm.addr_add_add,
      f_word h hH.fr (by omega), ← NativeRustcVm.addr_add_add]
  have hx0 : st.data.regs.X0 = (fE m0 p).c0 := reg_of hm1 h0 hfE0
  have hx1 : st.data.regs.X1 = (fE m0 p).c1 := reg_of hm1 h1 hfE1
  have hx2 : st.data.regs.X2 = (gG m0 p 0).c0 := reg_of hm1 h2 (by
    rw [eval_gLoc1, ← hH.g 0 (by decide)]; rfl)
  have hx3 : st.data.regs.X3 = (gG m0 p 0).c1 := reg_of hm1 h3 (by
    rw [eval_gLoc2, ← hH.g 0 (by decide)]; rfl)
  have hgv : ∀ b < 8, gv m0 st.data b = gG m0 p b := by
    intro b hb
    simp only [gKeep, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Bool.and_eq_true] at hg
    rcases hg b hb with hb8 | ⟨k1, k2⟩
    · omega
    rw [← hH.g b hb]
    simp only [gv]
    rw [locVal_keep hm1 k1, locVal_keep hm1 k2]
  have hcnt : locVal (fb m0) 176 st.data cntLoc = (8 - p : Nat).toUInt64 := by
    rw [locVal_set hm1 hc]
    simp only [Sym.eval]
    rw [Env.ofMachine_regs, hH.x10]
  refine Fr.leaf hB1.fr h.hN (by decide) keep_nil slots_le (out_frame h) hmul mulQ hpc
    (hB1.fr.stackOk h.st (by decide) (by decide)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  obtain ⟨q0, q1, hs, -⟩ := hq
  obtain ⟨hB2, hloc, hout⟩ := after_call h hB1 (N' := ewMulStack) (by decide) hcs
    (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ .inl hq) hfr2
  rw [hx0, hx1, hx2, hx3] at q0 q1
  exact {
    toBody := hB2
    cnt := by rw [hloc _ rfl, hcnt]
    x24 := by rw [hcs .X24 rfl]; exact reg_of hm1 h24 hfE0
    x25 := by rw [hcs .X25 rfl]; exact reg_of hm1 h25 hfE1
    g := fun b hb ↦ by
      simp only [gv]
      rw [hloc _ (gLoc_cs b).1, hloc _ (gLoc_cs b).2]
      exact hgv b hb
    x0 := q0
    x1 := q1
    out := by
      rw [show prods m0 p 0 = [] from rfl, List.append_nil]
      refine hout _ (by rw [rc_length1 (by omega)]; omega) (hout1 _ ?_ hH.out)
      rw [rc_length1 (by omega)]; omega }

/-! ## A product -/

/-- **A product block** (`b2` to `b8`): the last product stored, `f_p · G_b`. -/
theorem stepMul (h : P m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i b : Nat}
    {ds : List Directive} {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hS : mulOk (b + 1) S' = true)
    (hb : b + 1 < 8) {m : MachineData} (hM : MulD m0 p b m) {R : MachineState → Prop}
    (cont : ∀ m2, MulD m0 p (b + 1) m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := body_wf h hM.toBody
  refine exec_then hk hrun hwf (body_match h hM.toBody) fun st hm1 hpc ↦ ?_
  simp only [mulOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h24⟩, h25⟩, hptr⟩, hg⟩, hc⟩, hrow⟩, hwr⟩ := hS
  obtain ⟨hB1, hout1⟩ := after_block h hM.toBody hm1 hptr hwr (by omega) (by omega)
  have hp := hM.lt
  have hx0 : st.data.regs.X0 = (fE m0 p).c0 := reg_of hm1 h0 (by
    simp only [Sym.eval, Env.ofMachine_regs, hM.x24])
  have hx1 : st.data.regs.X1 = (fE m0 p).c1 := reg_of hm1 h1 (by
    simp only [Sym.eval, Env.ofMachine_regs, hM.x25])
  have hx2 : st.data.regs.X2 = (gG m0 p (b + 1)).c0 := reg_of hm1 h2 (by
    rw [eval_gLoc1, ← hM.g (b + 1) hb]; rfl)
  have hx3 : st.data.regs.X3 = (gG m0 p (b + 1)).c1 := reg_of hm1 h3 (by
    rw [eval_gLoc2, ← hM.g (b + 1) hb]; rfl)
  have hgv : ∀ b' < 8, gv m0 st.data b' = gG m0 p b' := by
    intro b' hb'
    simp only [gKeep, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Bool.and_eq_true] at hg
    rcases hg b' hb' with hb8 | ⟨k1, k2⟩
    · omega
    rw [← hM.g b' hb']
    simp only [gv]
    rw [locVal_keep hm1 k1, locVal_keep hm1 k2]
  have hnew := row_elt hm1 (j := b) (by omega) hrow
  rw [hM.x0, hM.x1] at hnew
  have hlen : ((rc m0 p).1.toList ++ prods m0 p b).length = 8 * p + b := by
    rw [List.length_append, rc_length1 (by omega), prods_length]
  have hout2 : NativeRustcVm.EWsAt st.data.dmem (oA m0) ((rc m0 p).1.toList ++ prods m0 p (b + 1)) := by
    rw [prods_succ, ← List.append_assoc, NativeRustcVm.ewsAt_append_iff, hlen,
      NativeRustcVm.ewsAt_singleton_iff]
    exact ⟨hout1 _ (by rw [hlen]; omega) hM.out, hnew⟩
  refine Fr.leaf hB1.fr h.hN (by decide) keep_nil slots_le (out_frame h) hmul mulQ hpc
    (hB1.fr.stackOk h.st (by decide) (by decide)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  obtain ⟨q0, q1, hs, -⟩ := hq
  obtain ⟨hB2, hloc, hout⟩ := after_call h hB1 (N' := ewMulStack) (by decide) hcs
    (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ .inl hq) hfr2
  rw [hx0, hx1, hx2, hx3] at q0 q1
  exact {
    toBody := hB2
    cnt := by rw [hloc _ rfl, locVal_keep hm1 hc, hM.cnt]
    x24 := by rw [hcs .X24 rfl]; exact reg_of hm1 h24 (by simp [Sym.eval, hM.x24])
    x25 := by rw [hcs .X25 rfl]; exact reg_of hm1 h25 (by simp [Sym.eval, hM.x25])
    g := fun b' hb' ↦ by
      simp only [gv]
      rw [hloc _ (gLoc_cs b').1, hloc _ (gLoc_cs b').2]
      exact hgv b' hb'
    x0 := q0
    x1 := q1
    out := hout _ (by rw [List.length_append, rc_length1 (by omega), prods_length]; omega) hout2 }

/-! ## The Frobenius images -/

/-- **The first Frobenius block** (`b9`): the last product stored, `G_0`'s image. -/
theorem stepSq0 (h : P m0) (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    {i : Nat} {ds : List Directive} {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWSqIter.entryLabel)) (hS : sq0Ok S' = true)
    {m : MachineData} (hM : MulD m0 p 7 m) {R : MachineState → Prop}
    (cont : ∀ m2, SqD m0 p 0 m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := body_wf h hM.toBody
  refine exec_then hk hrun hwf (body_match h hM.toBody) fun st hm1 hpc ↦ ?_
  simp only [sq0Ok, Bool.and_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h24⟩, h25⟩, hptr⟩, hg⟩, hc⟩, hrow⟩, hwr⟩ := hS
  obtain ⟨hB1, hout1⟩ := after_block h hM.toBody hm1 hptr hwr (by omega) (by omega)
  have hp := hM.lt
  have hx0 : st.data.regs.X0 = 8 := reg_of hm1 h0 rfl
  have hx1 : st.data.regs.X1 = (gG m0 p 0).c0 := reg_of hm1 h1 (by
    rw [eval_gLoc1, ← hM.g 0 (by decide)]; rfl)
  have hx2 : st.data.regs.X2 = (gG m0 p 0).c1 := reg_of hm1 h2 (by
    rw [eval_gLoc2, ← hM.g 0 (by decide)]; rfl)
  have hgv : ∀ b' < 8, gv m0 st.data b' = gG m0 p b' := by
    intro b' hb'
    simp only [gKeep, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Bool.and_eq_true] at hg
    rcases hg b' hb' with hb8 | ⟨k1, k2⟩
    · omega
    rw [← hM.g b' hb']
    simp only [gv]
    rw [locVal_keep hm1 k1, locVal_keep hm1 k2]
  have hnew := row_elt hm1 (j := 7) (by omega) hrow
  rw [hM.x0, hM.x1] at hnew
  have hlen : ((rc m0 p).1.toList ++ prods m0 p 7).length = 8 * p + 7 := by
    rw [List.length_append, rc_length1 (by omega), prods_length]
  have hout2 : NativeRustcVm.EWsAt st.data.dmem (oA m0) (rc m0 (p + 1)).1.toList := by
    rw [rc_succ_fst hp, show prods m0 p 8 = prods m0 p 7 ++ [fE m0 p * gG m0 p 7] from prods_succ _ _,
      ← List.append_assoc, NativeRustcVm.ewsAt_append_iff, hlen,
      NativeRustcVm.ewsAt_singleton_iff]
    exact ⟨hout1 _ (by rw [hlen]; omega) hM.out, hnew⟩
  refine Fr.leaf hB1.fr h.hN (by decide) keep_nil slots_le (out_frame h) hsq sqQ hpc
    (hB1.fr.stackOk h.st (by decide) (by decide)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  obtain ⟨q0, q1, hs, -⟩ := hq
  obtain ⟨hB2, hloc, hout⟩ := after_call h hB1 (N' := ewSqIterStack) (by decide) hcs
    (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ .inl hq) hfr2
  rw [hx0, hx1, hx2] at q0 q1
  exact {
    toBody := hB2
    cnt := by rw [hloc _ rfl, locVal_keep hm1 hc, hM.cnt]
    x24 := by rw [hcs .X24 rfl]; exact reg_of hm1 h24 (by simp [Sym.eval, hM.x24])
    x25 := by rw [hcs .X25 rfl]; exact reg_of hm1 h25 (by simp [Sym.eval, hM.x25])
    g := fun b' hb' ↦ by
      simp only [gv, Nat.not_lt_zero, ite_false]
      rw [hloc _ (gLoc_cs b').1, hloc _ (gLoc_cs b').2]
      exact hgv b' hb'
    x0 := q0
    x1 := q1
    out := hout _ (by rw [rc_length1 (by omega)]; omega) hout2 }

/-- **A Frobenius block** (`b10` to `b16`): `G_(b)`'s image stored, `G_(b+1)`'s. -/
theorem stepSq (h : P m0) (hsq : Spec (Labels.label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost)
    {i b : Nat} {ds : List Directive} {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWSqIter.entryLabel)) (hS : sqOk (b + 1) S' = true)
    (hb : b + 1 < 8) {m : MachineData} (hQ : SqD m0 p b m) {R : MachineState → Prop}
    (cont : ∀ m2, SqD m0 p (b + 1) m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := body_wf h hQ.toBody
  refine exec_then hk hrun hwf (body_match h hQ.toBody) fun st hm1 hpc ↦ ?_
  simp only [sqOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, hs1⟩, hs2⟩, h24⟩, h25⟩, hptr⟩, hg⟩, hc⟩, hwr⟩ := hS
  obtain ⟨hB1, hout1⟩ := after_block h hQ.toBody hm1 hptr hwr (le_refl _) (le_refl _)
  have hp := hQ.lt
  have hx0 : st.data.regs.X0 = 8 := reg_of hm1 h0 rfl
  have hgb : gv m0 m (b + 1) = gG m0 p (b + 1) := by
    have := hQ.g (b + 1) hb
    simpa [show ¬b + 1 < b by omega] using this
  have hx1 : st.data.regs.X1 = (gG m0 p (b + 1)).c0 := reg_of hm1 h1 (by
    rw [eval_gLoc1, ← hgb]; rfl)
  have hx2 : st.data.regs.X2 = (gG m0 p (b + 1)).c1 := reg_of hm1 h2 (by
    rw [eval_gLoc2, ← hgb]; rfl)
  have hgv : ∀ b' < 8, gv m0 st.data b' =
      if b' < b + 1 then frobenius8 (gG m0 p b') 1 else gG m0 p b' := by
    intro b' hb'
    by_cases hbb : b' = b
    · subst hbb
      simp only [Nat.lt_succ_self, ite_true, gv]
      rw [locVal_set hm1 hs1, locVal_set hm1 hs2]
      simp only [Sym.eval, Env.ofMachine_regs, hQ.x0, hQ.x1]
    simp only [gKeep, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Bool.and_eq_true] at hg
    rcases hg b' hb' with hb8 | ⟨k1, k2⟩
    · exact absurd hb8 hbb
    have := hQ.g b' hb'
    simp only [gv] at this ⊢
    rw [locVal_keep hm1 k1, locVal_keep hm1 k2, this]
    by_cases hlt : b' < b
    · simp [hlt, show b' < b + 1 by omega]
    · simp [hlt, show ¬b' < b + 1 by omega]
  refine Fr.leaf hB1.fr h.hN (by decide) keep_nil slots_le (out_frame h) hsq sqQ hpc
    (hB1.fr.stackOk h.st (by decide) (by decide)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  obtain ⟨q0, q1, hs, -⟩ := hq
  obtain ⟨hB2, hloc, hout⟩ := after_call h hB1 (N' := ewSqIterStack) (by decide) hcs
    (NativeRustcVm.SameOutside.mono hs fun _ hq ↦ .inl hq) hfr2
  rw [hx0, hx1, hx2] at q0 q1
  exact {
    toBody := hB2
    cnt := by rw [hloc _ rfl, locVal_keep hm1 hc, hQ.cnt]
    x24 := by rw [hcs .X24 rfl]; exact reg_of hm1 h24 (by simp [Sym.eval, hQ.x24])
    x25 := by rw [hcs .X25 rfl]; exact reg_of hm1 h25 (by simp [Sym.eval, hQ.x25])
    g := fun b' hb' ↦ by
      simp only [gv]
      rw [hloc _ (gLoc_cs b').1, hloc _ (gLoc_cs b').2]
      exact hgv b' hb'
    x0 := q0
    x1 := q1
    out := hout _ (by rw [rc_length1 (by omega)]; omega)
      (hout1 _ (by rw [rc_length1 (by omega)]; omega) hQ.out) }

end

end NativeRustcVmArm.Ring.Coeff
