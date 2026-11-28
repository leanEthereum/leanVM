module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Ring.Psi.Basic

/-!
# `ring_psi`: the turns between calls

Blocks `2j` (`1 ≤ j ≤ 6`, `stepEven`) and `2j + 1` (`stepOdd`) from the state after the previous
call (`midS`, `g` region 0 at X19): the product `g_j · v^(2^j)`, then the sum and the squaring.
-/

namespace NativeRustcVmArm.Ring.Psi

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

public section

variable {m0 : MachineData}

/-! ## The entry's facts -/

theorem stackOk_of (hpre : RingPsiPre m0) : StackOk m0 ringPsiStack := hpre.1

theorem stack_le (hpre : RingPsiPre m0) : ringPsiStack ≤ m0.regs.SP.toNat := hpre.1.2.1

theorem g_mapped (hpre : RingPsiPre m0) : Mapped m0.dmem (gA m0) 128 := hpre.2.1.1

theorem g_noWrap (hpre : RingPsiPre m0) : NoWrap (gA m0) 128 := hpre.2.1.2

theorem g_apart (hpre : RingPsiPre m0) :
    Apart (gA m0) 128 (base m0 ringPsiStack) ringPsiStack := hpre.2.2

/-! ## `g` -/

/-- `g`'s words are the entry's in every state of the frame. -/
theorem gword (hpre : RingPsiPre m0) {m : MachineData} (hfr : PFr m0 m) {o : Nat}
    (ho : o + 8 ≤ 128) :
    NativeRustcVm.wordOf m.dmem (gA m0 + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (gA m0 + BitVec.ofNat 64 o) :=
  NativeRustcVm.wordOf_congr fun i hi ↦ by
    apply hfr.same
    rintro (h | h)
    · rw [NativeRustcVm.addr_add_add] at h
      exact NativeRustcVm.Apart.not_inRange_add (g_apart hpre) (g_noWrap hpre)
        (base_noWrap (stack_le hpre)) (i := o + i) (by omega) h
    · exact h

theorem gE_c0 (j : Nat) :
    (gE m0 j).c0 = NativeRustcVm.wordOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * j)) := rfl

theorem gE_c1 (j : Nat) :
    (gE m0 j).c1 = NativeRustcVm.wordOf m0.dmem (gA m0 + BitVec.ofNat 64 (16 * j + 8)) := by
  rw [← NativeRustcVm.addr_add_add]
  rfl

theorem gl_length : (gl m0).length = 8 := NativeRustcVm.length_ewsOf ..

theorem gl_getElem {j : Nat} (hj : j < (gl m0).length) : (gl m0)[j] = gE m0 j :=
  NativeRustcVm.getElem_ewsOf ..

theorem ps_succ {j : Nat} (hj : j < 8) : ps m0 (j + 1) = psiStep (ps m0 j) (gE m0 j) := by
  unfold ps
  rw [psi_take_succ _ _ (by rw [gl_length]; exact hj), gl_getElem]

/-! ## The environment between calls -/

/-- Between calls: region 0 `g`. -/
abbrev envM (m0 m : MachineData) : Env := Env.ofMachine m [(gA m0, 128)]

theorem mid_wf (hpre : RingPsiPre m0) {m : MachineData} (hfr : PFr m0 m) : (envM m0 m).WF :=
  Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (g_mapped hpre i hi), g_noWrap hpre⟩, trivial⟩
    (List.pairwise_singleton _ _)

theorem mid_match [Labels] {m : MachineData} (hM : Mid m0 m) : Match (envM m0 m) midS m :=
  match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl
    ⟨by show (m.regs.getXReg .X19).toBitVec = _; rw [hM.x19]; simp [Sym.eval, gA], trivial⟩
    trivial trivial trivial

theorem gload0 [Labels] (hpre : RingPsiPre m0) {m : MachineData} (hfr : PFr m0 m) {j : Nat}
    (hj : j < 8) :
    (Sym.load 0 (16 * j) 8).eval (envM m0 m) = (gE m0 j).c0.toBitVec := by
  simp only [Sym.eval]
  rw [load_eq_wordOf, gE_c0]
  exact congrArg UInt64.toBitVec (gword hpre hfr (by omega))

theorem gload1 [Labels] (hpre : RingPsiPre m0) {m : MachineData} (hfr : PFr m0 m) {j : Nat}
    (hj : j < 8) :
    (Sym.load 0 (16 * j + 8) 8).eval (envM m0 m) = (gE m0 j).c1.toBitVec := by
  simp only [Sym.eval]
  rw [load_eq_wordOf, gE_c1]
  exact congrArg UInt64.toBitVec (gword hpre hfr (by omega))

/-- A register a block set. -/
theorem reg_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

theorem keep_cs : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 48 := by decide

theorem mulQ : ∀ m m', EWMulPost m m' → SameOutside m.dmem m'.dmem
    (fun q ↦ InRange (stackBelow m ewMulStack) ewMulStack q ∨ False) ∧ Saved m m' :=
  fun _ _ h ↦ ⟨NativeRustcVm.SameOutside.mono h.2.2.1 fun _ hq ↦ .inl hq, h.2.2.2⟩

theorem keepRegs_ok {S : SState} (h : regsAre S keepRegs = true) :
    ∀ r ∈ keep, ∃ v, midS.reg r = some v ∧ S.reg r = some v := by
  simp only [regsAre, keepRegs, keep, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h24, h25, h26, h27, h28, h29⟩ := h
  intro r hr
  simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, h24⟩
  · exact ⟨_, rfl, h25⟩
  · exact ⟨_, rfl, h26⟩
  · exact ⟨_, rfl, h27⟩
  · exact ⟨_, rfl, h28⟩
  · exact ⟨_, rfl, h29⟩

theorem regsAre_append {S : SState} {l l' : List (XReg × Sym)} :
    regsAre S (l ++ l') = (regsAre S l && regsAre S l') := List.all_append

variable [Host]

/-! ## The turns -/

/-- **Block `2j`**: the product `g_j · v^(2^j)`. -/
theorem stepEven (hpre : RingPsiPre m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {i j : Nat} {ds : List Directive} {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hS : regsAre S' (evenRegs j) = true)
    (hsp : S'.sp = .sp) (hmem : S'.mem = []) (hj : j < 8) {m : MachineData} (hE : Even m0 j m)
    {R : MachineState → Prop}
    (cont : ∀ m2, Odd m0 j m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := mid_wf hpre hE.fr
  have hm := mid_match hE.toMid
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  rw [evenRegs, regsAre_append] at hS
  simp only [Bool.and_eq_true] at hS
  obtain ⟨hS, hK⟩ := hS
  simp only [regsAre, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hS
  obtain ⟨h0, h1, h2, h3, h19, h20, h21, h22, h23⟩ := hS
  have hfr1 : PFr m0 st.data := hE.fr.ofBlock hm hm1 hwf rfl hmem hsp (keepRegs_ok hK)
  refine Fr.leaf hfr1 (stack_le hpre) (le_refl _) keep_cs slots_le (fun _ h ↦ h.elim) hmul mulQ
    hpc (hfr1.stackOk (stackOk_of hpre) (by decide) (le_refl _)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  have e0 := reg_of hm1 h0 (gload0 hpre hE.fr hj)
  have e1 := reg_of hm1 h1 (gload1 hpre hE.fr hj)
  have e2 := reg_of hm1 h2 (w := (ps m0 j).2.c0) (by simp [Sym.eval, hE.x0])
  have e3 := reg_of hm1 h3 (w := (ps m0 j).2.c1) (by simp [Sym.eval, hE.x1])
  have hx0 : st.data.regs.X0 = (gE m0 j).c0 := e0
  have hx1 : st.data.regs.X1 = (gE m0 j).c1 := e1
  have hx2 : st.data.regs.X2 = (ps m0 j).2.c0 := e2
  have hx3 : st.data.regs.X3 = (ps m0 j).2.c1 := e3
  obtain ⟨q0, q1, -⟩ := hq
  rw [hx0, hx1, hx2, hx3] at q0 q1
  exact {
    fr := hfr2
    x19 := by rw [hcs .X19 rfl]; exact reg_of hm1 h19 (by simp [Sym.eval, gA])
    x0 := q0
    x1 := q1
    x20 := by rw [hcs .X20 rfl]; exact reg_of hm1 h20 (by simp [Sym.eval, hE.x0])
    x21 := by rw [hcs .X21 rfl]; exact reg_of hm1 h21 (by simp [Sym.eval, hE.x1])
    x22 := by rw [hcs .X22 rfl]; exact reg_of hm1 h22 (by simp [Sym.eval, hE.x22])
    x23 := by rw [hcs .X23 rfl]; exact reg_of hm1 h23 (by simp [Sym.eval, hE.x23]) }

/-- **Block `2j + 1`**: the sum, and the power squared. -/
theorem stepOdd (hpre : RingPsiPre m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {i j : Nat} {ds : List Directive} {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hS : regsAre S' oddRegs = true)
    (hsp : S'.sp = .sp) (hmem : S'.mem = []) (hj : j < 8) {m : MachineData} (hO : Odd m0 j m)
    {R : MachineState → Prop}
    (cont : ∀ m2, Even m0 (j + 1) m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := mid_wf hpre hO.fr
  have hm := mid_match hO.toMid
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  rw [oddRegs, regsAre_append] at hS
  simp only [Bool.and_eq_true] at hS
  obtain ⟨hS, hK⟩ := hS
  simp only [regsAre, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hS
  obtain ⟨h0, h1, h2, h3, h19, h22, h23⟩ := hS
  have hfr1 : PFr m0 st.data := hO.fr.ofBlock hm hm1 hwf rfl hmem hsp (keepRegs_ok hK)
  refine Fr.leaf hfr1 (stack_le hpre) (le_refl _) keep_cs slots_le (fun _ h ↦ h.elim) hmul mulQ
    hpc (hfr1.stackOk (stackOk_of hpre) (by decide) (le_refl _)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  have hx0 : st.data.regs.X0 = (ps m0 j).2.c0 := reg_of hm1 h0 (by simp [Sym.eval, hO.x20])
  have hx1 : st.data.regs.X1 = (ps m0 j).2.c1 := reg_of hm1 h1 (by simp [Sym.eval, hO.x21])
  have hx2 : st.data.regs.X2 = (ps m0 j).2.c0 := reg_of hm1 h2 (by simp [Sym.eval, hO.x20])
  have hx3 : st.data.regs.X3 = (ps m0 j).2.c1 := reg_of hm1 h3 (by simp [Sym.eval, hO.x21])
  obtain ⟨q0, q1, -⟩ := hq
  rw [hx0, hx1, hx2, hx3] at q0 q1
  have hps := ps_succ (m0 := m0) hj
  exact {
    fr := hfr2
    x19 := by rw [hcs .X19 rfl]; exact reg_of hm1 h19 (by simp [Sym.eval, gA])
    x0 := by rw [hps]; exact q0
    x1 := by rw [hps]; exact q1
    x22 := by
      rw [hcs .X22 rfl, hps]
      refine reg_of hm1 h22 ?_
      simp [Sym.eval, BinOp.apply, hO.x0, hO.x22, psiStep, EW.add_def]
      rw [BitVec.xor_comm]; rfl
    x23 := by
      rw [hcs .X23 rfl, hps]
      refine reg_of hm1 h23 ?_
      simp [Sym.eval, BinOp.apply, hO.x1, hO.x23, psiStep, EW.add_def]
      rw [BitVec.xor_comm]; rfl }

end

end NativeRustcVmArm.Ring.Psi
