module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Ring.Psi.Steps

/-!
# `ring_psi`: the prologue, the first turn, the last, the epilogue

- `stepEntry` (`b0`): the frame saved, the product `g_0 · v` (`First`);
- `stepFirst` (`b1`): the sum `g_0 · v`, the square `v²` (`Even 1`);
- `stepLast` (`b14`): the product `g_7 · v^(2^7)` (`Last`);
- `stepExit` (`b15`): the sum, `ringPsi v g`, returned.
-/

namespace NativeRustcVmArm.Ring.Psi

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring

@[expose] public section

/-- After the first call: `g_0 · v` in X0, X1, `v` in X21, X20. -/
structure First (m0 m : MachineData) : Prop extends Mid m0 m where
  x0 : m.regs.getXReg .X0 = (EW.mul (gE m0 0) (vOf m0)).c0
  x1 : m.regs.getXReg .X1 = (EW.mul (gE m0 0) (vOf m0)).c1
  x21 : m.regs.getXReg .X21 = m0.regs.X0
  x20 : m.regs.getXReg .X20 = m0.regs.X1

/-- After the last call: `g_7 · v^(2^7)` in X0, X1, the sum of the first seven terms in X22,
X23. -/
structure Last (m0 m : MachineData) : Prop extends Mid m0 m where
  x0 : m.regs.getXReg .X0 = (EW.mul (gE m0 7) (ps m0 7).2).c0
  x1 : m.regs.getXReg .X1 = (EW.mul (gE m0 7) (ps m0 7).2).c1
  x22 : m.regs.getXReg .X22 = (ps m0 7).1.c0
  x23 : m.regs.getXReg .X23 = (ps m0 7).1.c1

/-- What `b1` sets. -/
def firstRegs : List (XReg × Sym) :=
  [(.X0, .reg .X21), (.X1, .reg .X20), (.X2, .reg .X21), (.X3, .reg .X20), (.X19, .ptr 0 0),
    (.X22, .reg .X0), (.X23, .reg .X1)] ++ keepRegs

/-- What `b14` sets. -/
def lastRegs : List (XReg × Sym) :=
  [(.X0, .load 0 (16 * 7) 8), (.X1, .load 0 (16 * 7 + 8) 8), (.X2, .reg .X0), (.X3, .reg .X1),
    (.X19, .ptr 0 0), (.X22, .reg .X22), (.X23, .reg .X23)] ++ keepRegs

end

public section

variable {m0 : MachineData}

theorem ps_zero : ps m0 0 = (0, vOf m0) := rfl

theorem ps_eight : ps m0 8 = ((gl m0).foldl psiStep (0, vOf m0)) := by
  unfold ps
  rw [List.take_of_length_le (by rw [gl_length])]

/-! ## The frame's region -/

theorem frame_mapped (hpre : RingPsiPre m0) : Mapped m0.dmem (base m0 48) 48 := by
  obtain ⟨-, hN, hmap⟩ := stackOk_of hpre
  intro i hi
  have := hmap (592 + i) (by show 592 + i < 48 + 592; omega)
  rwa [show m0.regs.SP.toBitVec - BitVec.ofNat 64 ringPsiStack = base m0 ringPsiStack from rfl,
    ← NativeRustcVm.addr_add_add,
    show (BitVec.ofNat 64 592 : BitVec 64) = BitVec.ofNat 64 (ringPsiStack - 48) from rfl,
    base_add (F := 48) (by decide) hN] at this

theorem frame_aligned (hpre : RingPsiPre m0) : (base m0 48).toNat % 16 = 0 := by
  obtain ⟨hal, hN, -⟩ := stackOk_of hpre
  rw [base_toNat (by have : ringPsiStack = 640 := rfl; omega)]
  omega

theorem frame_g_apart (hpre : RingPsiPre m0) : Apart (base m0 48) 48 (gA m0) 128 := by
  have h := g_apart hpre
  have hN := stack_le hpre
  have h640 : ringPsiStack = 640 := rfl
  have h1 := base_toNat (m0 := m0) (F := 48) (by omega)
  have h2 := base_toNat (m0 := m0) (F := ringPsiStack) hN
  unfold Apart at *
  omega

/-- At the entry: region 0 the frame, region 1 `g`. -/
abbrev env0 (m0 : MachineData) : Env := Env.ofMachine m0 [(base m0 48, 48), (gA m0, 128)]

theorem frame_noWrap (hpre : RingPsiPre m0) : NoWrap (base m0 48) 48 := by
  have := stack_le hpre
  have h640 : ringPsiStack = 640 := rfl
  exact base_noWrap (by omega)

theorem entry_wf (hpre : RingPsiPre m0) : (env0 m0).WF :=
  Env.wf_of ⟨⟨frame_mapped hpre, frame_noWrap hpre⟩, ⟨g_mapped hpre, g_noWrap hpre⟩, trivial⟩
    (List.pairwise_pair.mpr (frame_g_apart hpre))

theorem entry_match [Labels] (hpre : RingPsiPre m0) : Match (env0 m0) entryS m0 :=
  match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hpre, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by
      show m0.regs.SP.toBitVec = base m0 48 + BitVec.ofInt 64 (48 : Nat)
      rw [BitVec.ofInt_natCast, base_add_eq])
    ⟨by simp [Sym.eval, gA]; rfl, trivial⟩ trivial trivial trivial

/-- At the epilogue: region 0 the frame. -/
abbrev envX (m0 m : MachineData) : Env := Env.ofMachine m [(base m0 48, 48)]

variable [Host]

/-- **The prologue and the first product.** -/
theorem stepEntry (hpre : RingPsiPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat}
    (hk : Vm.RingPsi.b0.IsInfixAt Host.prog i) {R : MachineState → Prop}
    (cont : ∀ m2, First m0 m2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + Vm.RingPsi.b0.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf i⟩ := by
  have hwf := entry_wf hpre
  refine exec_then hk run_b0 hwf (entry_match hpre) fun st hm1 hpc ↦ ?_
  have hN := stack_le hpre
  have hfr1 : PFr m0 st.data :=
    Fr.ofPrologue hN (by decide) hm1 hwf rfl (by decide) slots_le (by decide)
      (fun r hr ↦ by
        simp only [keep, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  refine Fr.leaf hfr1 hN (le_refl _) keep_cs slots_le (fun _ h ↦ h.elim) hmul mulQ
    hpc (hfr1.stackOk (stackOk_of hpre) (by decide) (le_refl _)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  have hx0 : st.data.regs.X0 = (gE m0 0).c0 := reg_of hm1 (r := .X0) (v := .load 1 0 8) rfl (by
    simp only [Sym.eval]; rw [load_eq_wordOf]; simp [gE_c0])
  have hx1 : st.data.regs.X1 = (gE m0 0).c1 := reg_of hm1 (r := .X1) (v := .load 1 8 8) rfl (by
    simp only [Sym.eval]; rw [load_eq_wordOf]; simp [gE_c1])
  have hx2 : st.data.regs.X2 = m0.regs.X0 :=
    reg_of hm1 (r := .X2) (v := .reg .X0) rfl (by simp [Sym.eval]; rfl)
  have hx3 : st.data.regs.X3 = m0.regs.X1 :=
    reg_of hm1 (r := .X3) (v := .reg .X1) rfl (by simp [Sym.eval]; rfl)
  obtain ⟨q0, q1, -⟩ := hq
  rw [hx0, hx1, hx2, hx3] at q0 q1
  exact {
    fr := hfr2
    x19 := by rw [hcs .X19 rfl]; exact reg_of hm1 (v := .ptr 1 0) rfl (by simp [Sym.eval, gA])
    x0 := q0
    x1 := q1
    x21 := by rw [hcs .X21 rfl]; exact reg_of hm1 (v := .reg .X0) rfl (by simp [Sym.eval]; rfl)
    x20 := by rw [hcs .X20 rfl]; exact reg_of hm1 (v := .reg .X1) rfl (by simp [Sym.eval]; rfl) }

/-- **The first sum and square** (`b1`). -/
theorem stepFirst (hpre : RingPsiPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat} {ds : List Directive}
    {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hS : regsAre S' firstRegs = true)
    (hsp : S'.sp = .sp) (hmem : S'.mem = []) {m : MachineData} (hF : First m0 m)
    {R : MachineState → Prop}
    (cont : ∀ m2, Even m0 1 m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := mid_wf hpre hF.fr
  have hm := mid_match hF.toMid
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  rw [firstRegs, regsAre_append] at hS
  simp only [Bool.and_eq_true] at hS
  obtain ⟨hS, hK⟩ := hS
  simp only [regsAre, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hS
  obtain ⟨h0, h1, h2, h3, h19, h22, h23⟩ := hS
  have hfr1 : PFr m0 st.data := hF.fr.ofBlock hm hm1 hwf rfl hmem hsp (keepRegs_ok hK)
  refine Fr.leaf hfr1 (stack_le hpre) (le_refl _) keep_cs slots_le (fun _ h ↦ h.elim) hmul mulQ
    hpc (hfr1.stackOk (stackOk_of hpre) (by decide) (le_refl _)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  have hx0 : st.data.regs.X0 = m0.regs.X0 := reg_of hm1 h0 (by simp [Sym.eval, hF.x21])
  have hx1 : st.data.regs.X1 = m0.regs.X1 := reg_of hm1 h1 (by simp [Sym.eval, hF.x20])
  have hx2 : st.data.regs.X2 = m0.regs.X0 := reg_of hm1 h2 (by simp [Sym.eval, hF.x21])
  have hx3 : st.data.regs.X3 = m0.regs.X1 := reg_of hm1 h3 (by simp [Sym.eval, hF.x20])
  obtain ⟨q0, q1, -⟩ := hq
  rw [hx0, hx1, hx2, hx3] at q0 q1
  have hps : ps m0 1 = psiStep (0, vOf m0) (gE m0 0) := ps_succ (j := 0) (by decide)
  exact {
    fr := hfr2
    x19 := by rw [hcs .X19 rfl]; exact reg_of hm1 h19 (by simp [Sym.eval, gA])
    x0 := by rw [hps]; exact q0
    x1 := by rw [hps]; exact q1
    x22 := by
      rw [hcs .X22 rfl, hps]
      refine reg_of hm1 h22 ?_
      simp only [psiStep, EW.zero_add']
      simp [Sym.eval, hF.x0]
      rfl
    x23 := by
      rw [hcs .X23 rfl, hps]
      refine reg_of hm1 h23 ?_
      simp only [psiStep, EW.zero_add']
      simp [Sym.eval, hF.x1]
      rfl }

/-- **The last product** (`b14`). -/
theorem stepLast (hpre : RingPsiPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {i : Nat} {ds : List Directive}
    {S' : SState} (hk : ds.IsInfixAt Host.prog i)
    (hrun : exec ds midS = some (S', .call NativeRustcVmArm.Vm.EWMul.entryLabel)) (hS : regsAre S' lastRegs = true)
    (hsp : S'.sp = .sp) (hmem : S'.mem = []) {m : MachineData} (hE : Even m0 7 m)
    {R : MachineState → Prop}
    (cont : ∀ m2, Last m0 m2 → Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (i + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i⟩ := by
  have hwf := mid_wf hpre hE.fr
  have hm := mid_match hE.toMid
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  rw [lastRegs, regsAre_append] at hS
  simp only [Bool.and_eq_true] at hS
  obtain ⟨hS, hK⟩ := hS
  simp only [regsAre, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hS
  obtain ⟨h0, h1, h2, h3, h19, h22, h23⟩ := hS
  have hfr1 : PFr m0 st.data := hE.fr.ofBlock hm hm1 hwf rfl hmem hsp (keepRegs_ok hK)
  refine Fr.leaf hfr1 (stack_le hpre) (le_refl _) keep_cs slots_le (fun _ h ↦ h.elim) hmul mulQ
    hpc (hfr1.stackOk (stackOk_of hpre) (by decide) (le_refl _)) fun m2 hfr2 hq hcs ↦ cont m2 ?_
  have hx0 : st.data.regs.X0 = (gE m0 7).c0 := reg_of hm1 h0 (gload0 hpre hE.fr (by decide))
  have hx1 : st.data.regs.X1 = (gE m0 7).c1 := reg_of hm1 h1 (gload1 hpre hE.fr (by decide))
  have hx2 : st.data.regs.X2 = (ps m0 7).2.c0 := reg_of hm1 h2 (by simp [Sym.eval, hE.x0])
  have hx3 : st.data.regs.X3 = (ps m0 7).2.c1 := reg_of hm1 h3 (by simp [Sym.eval, hE.x1])
  obtain ⟨q0, q1, -⟩ := hq
  rw [hx0, hx1, hx2, hx3] at q0 q1
  exact {
    fr := hfr2
    x19 := by rw [hcs .X19 rfl]; exact reg_of hm1 h19 (by simp [Sym.eval, gA])
    x0 := q0
    x1 := q1
    x22 := by rw [hcs .X22 rfl]; exact reg_of hm1 h22 (by simp [Sym.eval, hE.x22])
    x23 := by rw [hcs .X23 rfl]; exact reg_of hm1 h23 (by simp [Sym.eval, hE.x23]) }

/-- **The epilogue** (`b15`): the last sum returned, the registers restored. -/
theorem stepExit (hpre : RingPsiPre m0) {i : Nat} (hk : Vm.RingPsi.b15.IsInfixAt Host.prog i)
    {m : MachineData} (hL : Last m0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = retOf m0 ∧ RingPsiPost m0 st.data)
      ⟨m, Host.addrOf i⟩ := by
  have hN := stack_le hpre
  have h640 : ringPsiStack = 640 := rfl
  have hwf : (envX m0 m).WF :=
    Env.wf_of ⟨⟨fun j hj ↦ hL.fr.kept _ (frame_mapped hpre j hj), base_noWrap (by omega)⟩,
      trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (envX m0 m) exitS m :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hpre, trivial⟩
      (by
        show m.regs.SP.toBitVec = base m0 48 + BitVec.ofInt 64 (0 : Nat)
        rw [hL.fr.sp]
        simp)
      trivial trivial trivial trivial
  refine exec_then hk run_b15 hwf hm fun st hm1 hpc ↦ ?_
  obtain ⟨hret, hsaved⟩ := hL.fr.exit hm1 hwf (by decide)
  have hpc' : st.pc = retOf m0 := by simp only [PcOk] at hpc; rw [hpc, hret]
  refine .done _ ⟨hpc', ?_, ?_, hsaved⟩
  · have e0 : st.data.regs.getXReg .X0 = (ps m0 8).1.c0 := by
      refine reg_of hm1 (v := .bin .eor .W64 (.reg .X0) (.reg .X22)) rfl ?_
      rw [ps_succ (j := 7) (by decide)]
      simp [Sym.eval, BinOp.apply, hL.x0, hL.x22, psiStep, EW.add_def]
      rw [BitVec.xor_comm]; rfl
    have e1 : st.data.regs.getXReg .X1 = (ps m0 8).1.c1 := by
      refine reg_of hm1 (v := .bin .eor .W64 (.reg .X1) (.reg .X23)) rfl ?_
      rw [ps_succ (j := 7) (by decide)]
      simp [Sym.eval, BinOp.apply, hL.x1, hL.x23, psiStep, EW.add_def]
      rw [BitVec.xor_comm]; rfl
    show (⟨st.data.regs.getXReg .X0, st.data.regs.getXReg .X1⟩ : EW) = _
    rw [e0, e1, ps_eight, arr, ringWidth, ← ringPsi_toArray]
    rfl
  · have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
    intro p hp
    rw [hd]
    refine hL.fr.same p fun h ↦ hp ?_
    rcases h with h | h
    · exact .inr h
    · exact h.elim

end

end NativeRustcVmArm.Ring.Psi
