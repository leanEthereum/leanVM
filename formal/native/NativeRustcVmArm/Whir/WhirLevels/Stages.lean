module

public import NativeRustcVmArm.Code.Vm.FinalLevel.Names
public import NativeRustcVmArm.Code.Vm.FoldRounds.Names
public import NativeRustcVmArm.Code.Vm.NextLevel.Names
public import NativeRustcVmArm.Code.Vm.WhirLevels.Names
public import NativeRustcVmArm.Whir.WhirLevels.Steps

/-!
# `whir_levels`: the stages of a level, run

`fold_stage`, `w_stage`, `next_stage`, `cmp_stage`, `jump_final` (see `Steps`), each from a block
whose literal end state passes its check.
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Layout.Ladder
open NativeRustcVmArm.Vm.WhirLevels

@[expose] public section

/-- The block jumping to the tail call: X23 becomes `v`, the other registers `final_level` reads
kept. -/
def JumpOk (v : Sym) (S : SState) : Bool :=
  S.mem.isEmpty && S.sp == .sp && S.reg .X23 == some v &&
    [XReg.X5, .X19, .X20, .X21, .X22, .X24, .X25, .X29].all fun r ↦ S.reg r == some (.reg r)

end

public section

theorem keepR_x29 {S₀ S : SState} (h : keepR S₀ S = true) (h0 : S₀.reg .X29 = some (.reg .X29)) :
    S.reg .X29 = some (.reg .X29) := by
  simp only [keepR, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact (h .X29 (by simp)).2.trans h0

theorem lvS_x29 (n : Nat) : (lvS n).reg .X29 = some (.reg .X29) := rfl
theorem wS_x29 : wS.reg .X29 = some (.reg .X29) := rfl

theorem ofNat_61152 {x : UInt64} (h : x.toNat = 61152) :
    x.toBitVec = BitVec.ofNat 64 roundsOff := by
  apply BitVec.eq_of_toNat_eq
  rw [show x.toBitVec.toNat = x.toNat from rfl, h]
  rfl

section
variable [Host] {a : DecArea} {s0 : TState} {levels : List Whir.Level} {ba : BasisAddrs}
  {b : BasisW} {claim : EW} {m0 : MachineData} {rate : Nat} {k0 : Nat}

/-- The levels' first `n` bytes, in a state of the frame. -/
theorem levels_region (c : Ctx a s0 levels ba b claim m0 rate) {st : MachineData}
    (hf : WFr m0 st) {n : Nat} (hn : n ≤ levelBytes * levels.length) :
    NativeRustcVm.Mapped st.dmem (lvA m0) n ∧ NoWrap (lvA m0) n :=
  ⟨fun i hi ↦ hf.kept _ (c.lin.1.1 i (by omega)), NativeRustcVm.NoWrap.mono c.lin.1.2 hn⟩

/-- **The fold rounds' stage** of level `k`: the call block, the call, the `None` test. -/
theorem fold_stage (hp : Placed code k0)
    (hfr : ∀ a s w, Spec (Labels.label NativeRustcVmArm.Vm.FoldRounds.entryLabel) (FoldRoundsPre a s w)
      (FoldRoundsPost a s w))
    (c : Ctx a s0 levels ba b claim m0 rate) {k j n : Nat} {ds : List Directive}
    (hds : ds.IsInfixAt code j) (hne : ds ≠ []) (hcz : b2.IsInfixAt code (j + ds.length))
    {S' : SState} (hx : exec ds (lvS n) = some (S', .call NativeRustcVmArm.Vm.FoldRounds.entryLabel))
    (hok : FoldOk k n S' = true) (hn : n ≤ 24 * (k + 1))
    {s : TState} {w : WhirStateW} {st : MachineState}
    (hh : Head a s0 levels b claim m0 k s w st.data)
    (hx26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + j))
    (cont : ∀ st', st'.pc = Host.addrOf (k0 + (j + ds.length + 1)) → ∀ s' w' rs,
      Mid a s0 levels b claim m0 rate k s' w' rs st'.data →
      Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hk := hh.lt
  have hn' : n ≤ levelBytes * levels.length := by unfold levelBytes; omega
  obtain ⟨hmap, hnw⟩ := levels_region c hh.fr hn'
  have hok' := hok
  simp only [FoldOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨hmem, hsp⟩, hkr⟩, h26⟩, h0⟩, h1⟩, h2⟩, h3⟩ := hok'
  refine readBlock hh.fr (inf hp hds hne) hx hpc (by rw [hh.regs.x23]) hmap hnw hmem hsp
    ⟨rfl, keepR_x29 hkr (lvS_x29 n)⟩ fun st1 hf1 hd1 hm0 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hr1 := hh.regs.ofKeep hm0 hm1 hkr
  have hlv := load_level c hh.fr (n := n) hk
  have e0 : st1.data.regs.X0 = m0.regs.X0 := (reg_of hm1 h0 rfl).trans hh.regs.x21
  have e1 : st1.data.regs.X1.toNat = foldAt k := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl, ← hlv.1]
    exact congrArg BitVec.toNat (reg_val hm1 h1)
  have e2 : st1.data.regs.X2 = m0.regs.X6 := (reg_of hm1 h2 rfl).trans hh.regs.x19
  have e3 : st1.data.regs.X3.toBitVec = pA m0 + BitVec.ofNat 64 roundsOff := by
    rw [show st1.data.regs.X3 = st1.data.regs.getXReg .X3 from rfl, reg_val hm1 h3,
      eval_add_regs]
    simp only [Env.ofMachine_regs]
    rw [hh.regs.x19, ofNat_61152 hh.regs.x28]
  have e26 : X26Ok m0 levels.length k st1.data := by
    unfold X26Ok
    split
    · rename_i hk5'
      simp only [hk5', ↓reduceIte] at h26
      rw [Match.reg_eq hm0 hm1 rfl h26]
      exact hx26
    · rename_i hk5'
      simp only [hk5', ↓reduceIte] at h26
      rw [reg_val hm1 h26]
      exact eval_ptr0 120
  refine fold_call hfr c ⟨hf1, hr1, by rw [hd1]; exact hh.ts, by rw [hd1]; exact hh.ws, hk,
    hh.alphas, hh.glued, hh.roots, hh.run⟩ hpc1 e0 e1 e2 e3 e26 fun m2 hf2 hr2 hres ↦ ?_
  have hx01 : m2.regs.X0 = 0 ∨ m2.regs.X0 = 1 := by
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  refine cbz_step hp hcz (st := ⟨m2, Host.addrOf (k0 + j + ds.length)⟩) hf2
    (by rw [Nat.add_assoc]) hx01 (fun h0 st' hpc' hf' _ _ ↦ ?_)
    fun h1 st' hpc' hf' hd' he' ↦ ?_
  · rcases hres with ⟨-, hnone⟩ | ⟨h, -⟩
    · exact exit_none hp c hf' hpc' hnone
    · rw [h0] at h; cases h
  · rcases hres with ⟨h, -⟩ | ⟨-, s', w', rs, hmid⟩
    · rw [h1] at h; cases h
    · refine cont st' hpc' s' w' rs ⟨hf', hmid.regs.congr he', ?_, by rw [hd']; exact hmid.ts,
        by rw [hd']; exact hmid.wa, hmid.lt, hmid.alphas, hmid.glued, hmid.roots, hmid.fin,
        hmid.nxt⟩
      have := hmid.x26
      unfold X26Ok at this ⊢
      rw [he' .X26]
      exact this

omit [Host] in
/-- `Mid` across a change keeping the memory, `Regs` and X26. -/
theorem Mid.congr {k : Nat} {s : TState} {w : WhirStateW} {rs : Array FoldRoundW}
    {st st' : MachineData} (hm : Mid a s0 levels b claim m0 rate k s w rs st) (hf : WFr m0 st')
    (hd : st'.dmem = st.dmem) (hr : Regs m0 levels.length st')
    (h26 : st'.regs.getXReg .X26 = st.regs.getXReg .X26) :
    Mid a s0 levels b claim m0 rate k s w rs st' := by
  refine ⟨hf, hr, ?_, by rw [hd]; exact hm.ts, by rw [hd]; exact hm.wa, hm.lt, hm.alphas,
    hm.glued, hm.roots, hm.fin, hm.nxt⟩
  have := hm.x26
  unfold X26Ok at this ⊢
  rw [h26]
  exact this

omit [Host] in
/-- `Head` across a change keeping the memory and `Regs`. -/
theorem Head.congr {k : Nat} {s : TState} {w : WhirStateW} {st st' : MachineData}
    (hh : Head a s0 levels b claim m0 k s w st) (hf : WFr m0 st') (hd : st'.dmem = st.dmem)
    (hr : Regs m0 levels.length st') : Head a s0 levels b claim m0 k s w st' :=
  ⟨hf, hr, by rw [hd]; exact hh.ts, by rw [hd]; exact hh.ws, hh.lt, hh.alphas, hh.glued,
    hh.roots, hh.run⟩

/-- **The `μ` stage** of level `k`: X5 becomes `logN` minus the `α` count. -/
theorem w_stage (hp : Placed code k0) (c : Ctx a s0 levels ba b claim m0 rate) {k j : Nat}
    {ds : List Directive} (hds : ds.IsInfixAt code j) (hne : ds ≠ []) {S' : SState} {x : Exit}
    (hx : exec ds wS = some (S', x)) (hok : WOk S' = true) {s : TState} {w : WhirStateW}
    {rs : Array FoldRoundW} {st : MachineState}
    (hm : Mid a s0 levels b claim m0 rate k s w rs st.data) (hpc : st.pc = Host.addrOf (k0 + j))
    {R : MachineState → Prop}
    (cont : ∀ st', Mid a s0 levels b claim m0 rate k s w rs st'.data →
      st'.data.regs.X5.toNat = logN m0 - w.alphas.size →
      Match (Env.ofMachine st.data [(pA m0, 24)]) S' st'.data →
      PcOk (Env.ofMachine st.data [(pA m0, 24)]) x (Host.addrOf (k0 + j + ds.length)) st' →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok' := hok
  simp only [WOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok'
  obtain ⟨⟨⟨⟨hmem, hsp⟩, hkr⟩, h26⟩, h5⟩ := hok'
  have hmap : NativeRustcVm.Mapped st.data.dmem (pA m0) 24 :=
    fun i hi ↦ hm.fr.kept _ (c.pout.1.1 i (by unfold whirBytes; omega))
  have hnw : NoWrap (pA m0) 24 := NativeRustcVm.NoWrap.mono c.pout.1.2.1 (by decide)
  refine readBlock hm.fr (inf hp hds hne) hx hpc (by rw [hm.regs.x19]) hmap hnw hmem hsp
    ⟨rfl, keepR_x29 hkr wS_x29⟩ fun st1 hf1 hd1 hm0 hm1 hpc1 ↦ ?_
  refine cont st1 (hm.congr hf1 hd1 (hm.regs.ofKeep hm0 hm1 hkr) (Match.reg_eq hm0 hm1 rfl h26))
    ?_ hm1 hpc1
  rw [show st1.data.regs.X5 = st1.data.regs.getXReg .X5 from rfl]
  rw [show (st1.data.regs.getXReg .X5).toNat = (muSym.eval _).toNat from
    congrArg BitVec.toNat (reg_val hm1 h5), eval_muSym]
  simp only [Env.ofMachine_regs]
  rw [hm.regs.x25]
  obtain ⟨hle, hw, -⟩ := hm.wa.1.alphas
  rw [load_at (n := 24) (o := 16) hw]
  congr 1
  show w.alphas.toList.length.toUInt64.toNat = _
  have : w.alphas.toList.length ≤ 30 := hle
  simp only [Array.length_toList, Nat.toUInt64, UInt64.toNat_ofNat']
  rw [Array.length_toList] at this
  exact Nat.mod_eq_of_lt (by omega)

/-- **`next_level`'s stage** of level `k`: the call block, the call. -/
theorem next_stage (hp : Placed code k0)
    (hnl : ∀ a s level w rounds, Spec (Labels.label NativeRustcVmArm.Vm.NextLevel.entryLabel)
      (NextLevelPre a s level w rounds) (NextLevelPost a s level w rounds))
    (c : Ctx a s0 levels ba b claim m0 rate) {k j n : Nat} {ds : List Directive}
    (hds : ds.IsInfixAt code j) (hne : ds ≠ []) {S' : SState}
    (hx : exec ds (lvS n) = some (S', .call NativeRustcVmArm.Vm.NextLevel.entryLabel)) {v2 : Sym}
    (hok : NextOk k n v2 S' = true)
    (hv2 : ∀ st : MachineData, Regs m0 levels.length st →
      v2.eval (Env.ofMachine st [(lvA m0, n)]) = lvA m0 + BitVec.ofNat 64 (levelBytes * k))
    (hn : n ≤ 24 * (k + 2)) {s : TState} {w : WhirStateW} {rs : Array FoldRoundW}
    {st : MachineState} (hm : Mid a s0 levels b claim m0 rate k s w rs st.data)
    (hk1 : k + 1 < levels.length) (hx5 : st.data.regs.X5.toNat = logN m0 - w.alphas.size)
    (hpc : st.pc = Host.addrOf (k0 + j)) {R : MachineState → Prop}
    (cont : ∀ st', st'.pc = Host.addrOf (k0 + j + ds.length) → WFr m0 st'.data →
      Regs m0 levels.length st'.data →
      (st'.data.regs.getXReg .X26).toNat = levels.length →
      (st'.data.regs.X0 = 0 ∧ runAll s0 levels b claim m0 = none) ∨
        (st'.data.regs.X0 = 1 ∧ ∃ s' w', Head a s0 levels b claim m0 (k + 1) s' w' st'.data) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hl6 := c.len_le.2
  have hn' : n ≤ levelBytes * levels.length := by unfold levelBytes; omega
  obtain ⟨hmap, hnw⟩ := levels_region c hm.fr hn'
  have hx26 := hm.x26
  unfold X26Ok at hx26
  simp only [show k < 5 by omega, ↓reduceIte] at hx26
  have hok' := hok
  simp only [NextOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hmem, hsp⟩, hkr⟩, h26⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hok'
  refine readBlock hm.fr (inf hp hds hne) hx hpc (by rw [hm.regs.x23]) hmap hnw hmem hsp
    ⟨rfl, keepR_x29 hkr (lvS_x29 n)⟩ fun st1 hf1 hd1 hm0 hm1 hpc1 ↦ ?_
  simp only [PcOk] at hpc1
  have hr1 := hm.regs.ofKeep hm0 hm1 hkr
  have hlv := load_level c hm.fr (n := n) hk1
  have hm1' := hm.congr hf1 hd1 hr1 (Match.reg_eq hm0 hm1 rfl h26)
  have e0 : st1.data.regs.X0 = m0.regs.X0 := (reg_of hm1 h0 rfl).trans hm.regs.x21
  have e1 : st1.data.regs.X1.toNat = k := by
    rw [show st1.data.regs.X1 = st1.data.regs.getXReg .X1 from rfl,
      show (st1.data.regs.getXReg .X1).toNat = _ from congrArg BitVec.toNat (reg_val hm1 h1)]
    simp only [Sym.eval, BitVec.toNat_ofNat]
    omega
  have e2 : st1.data.regs.X2.toBitVec = lvA m0 + BitVec.ofNat 64 (levelBytes * k) := by
    rw [show st1.data.regs.X2 = st1.data.regs.getXReg .X2 from rfl, reg_val hm1 h2]
    exact hv2 _ hm.regs
  have e3 : st1.data.regs.X3.toNat = foldAt (k + 1) := by
    rw [show st1.data.regs.X3 = st1.data.regs.getXReg .X3 from rfl, ← hlv.1]
    exact congrArg BitVec.toNat (reg_val hm1 h3)
  have e4 : st1.data.regs.X4.toNat = rate + 3 * (k + 1) := by
    rw [show st1.data.regs.X4 = st1.data.regs.getXReg .X4 from rfl, ← hlv.2]
    exact congrArg BitVec.toNat (reg_val hm1 h4)
  have e5 : st1.data.regs.X5.toNat = logN m0 - w.alphas.size := by
    rw [← hx5]
    exact congrArg UInt64.toNat (Match.reg_eq (r := .X5) hm0 hm1 rfl h5)
  have e6 : st1.data.regs.X6 = m0.regs.X6 := (reg_of hm1 h6 rfl).trans hm.regs.x19
  have e26 : (st1.data.regs.getXReg .X26).toNat = levels.length := by
    rw [Match.reg_eq hm0 hm1 rfl h26]; exact hx26
  refine next_call hnl c hm1' hk1 hpc1 e0 e1 e2 e3 e4 e5 e6
    fun m2 hf2 hr2 h26' hres ↦ cont ⟨m2, _⟩ rfl hf2 hr2 (by rw [h26']; exact e26) hres

/-- **The `None` test after `next_level`**: to the epilogue on `0`, to level `k + 1`'s fold
rounds on `1`. -/
theorem cbz_next (hp : Placed code k0) (c : Ctx a s0 levels ba b claim m0 rate) {j k : Nat}
    (hcz : b2.IsInfixAt code j) {st : MachineState} (hf : WFr m0 st.data)
    (hr : Regs m0 levels.length st.data)
    (hx26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + j))
    (hres : (st.data.regs.X0 = 0 ∧ runAll s0 levels b claim m0 = none) ∨
      (st.data.regs.X0 = 1 ∧ ∃ s' w', Head a s0 levels b claim m0 (k + 1) s' w' st.data))
    (cont : ∀ st', st'.pc = Host.addrOf (k0 + (j + 1)) → ∀ s' w',
      Head a s0 levels b claim m0 (k + 1) s' w' st'.data →
      (st'.data.regs.getXReg .X26).toNat = levels.length →
      Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hx01 : st.data.regs.X0 = 0 ∨ st.data.regs.X0 = 1 := by
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  refine cbz_step hp hcz hf hpc hx01 (fun h0 st' hpc' hf' _ _ ↦ ?_)
    fun h1 st' hpc' hf' hd' he' ↦ ?_
  · rcases hres with ⟨-, hnone⟩ | ⟨h, -⟩
    · exact exit_none hp c hf' hpc' hnone
    · rw [h0] at h; cases h
  · rcases hres with ⟨h, -⟩ | ⟨-, s', w', hh⟩
    · rw [h1] at h; cases h
    · exact cont st' hpc' s' w' (hh.congr hf' hd' (hr.congr he'))
        (by rw [he' .X26]; exact hx26)

/-- **The comparison of the next level with the count** (`cmp x26, #(k + 1)`, never equal), then
the `None` test. -/
theorem cmp_stage (hp : Placed code k0) (c : Ctx a s0 levels ba b claim m0 rate) {j k : Nat}
    {ds : List Directive} (hds : ds.IsInfixAt code j) (hne : ds ≠ [])
    (hcz : b2.IsInfixAt code (j + ds.length)) {S' : SState}
    (hx : exec ds regsS = some (S', .cond (.cmp .eq .W64 (.reg .X26) (.lit (k + 1)))
      NativeRustcVmArm.Vm.WhirLevels.label_27)) (hok : RegsOk S' = true) (hk1 : k + 1 < levels.length)
    {st : MachineState} (hf : WFr m0 st.data) (hr : Regs m0 levels.length st.data)
    (hx26 : (st.data.regs.getXReg .X26).toNat = levels.length)
    (hpc : st.pc = Host.addrOf (k0 + j))
    (hres : (st.data.regs.X0 = 0 ∧ runAll s0 levels b claim m0 = none) ∨
      (st.data.regs.X0 = 1 ∧ ∃ s' w', Head a s0 levels b claim m0 (k + 1) s' w' st.data))
    (cont : ∀ st', st'.pc = Host.addrOf (k0 + (j + ds.length + 1)) → ∀ s' w',
      Head a s0 levels b claim m0 (k + 1) s' w' st'.data →
      (st'.data.regs.getXReg .X26).toNat = levels.length →
      Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st') :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hok' := hok
  simp only [RegsOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hok'
  obtain ⟨⟨⟨⟨hmem, hsp⟩, hkr⟩, h26⟩, h0⟩ := hok'
  have hm0 := match_nil st.data
  refine hf.regsBlock (inf hp hds hne) hx hpc hmem hsp (by
    simp only [keptRegs, keep, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq]
    exact keepR_x29 hkr rfl) fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  have hl6 := c.len_le.2
  simp only [PcOk] at hpc1
  rw [eval_cmp_eq _ _ (by omega)] at hpc1
  simp only [Env.ofMachine_regs] at hpc1
  have hc : ¬(st.data.regs.getXReg .X26).toBitVec.toNat = k + 1 := fun h ↦ by
    have : (st.data.regs.getXReg .X26).toNat = k + 1 := h
    omega
  simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have he : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X27, .X28, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦ keepR_reg hm0 hm1 hkr hr
  have h26' : st1.data.regs.getXReg .X26 = st.data.regs.getXReg .X26 :=
    Match.reg_eq hm0 hm1 rfl h26
  have e0 : st1.data.regs.X0 = st.data.regs.X0 := Match.reg_eq (r := .X0) hm0 hm1 rfl h0
  have hr1 := hr.congr' he
  refine cbz_next hp c hcz hf1 hr1 (by rw [h26']; exact hx26) (by rw [hpc1, Nat.add_assoc]) ?_
    cont
  rcases hres with ⟨h, hn⟩ | ⟨h, s', w', hh⟩
  · exact .inl ⟨e0.trans h, hn⟩
  · exact .inr ⟨e0.trans h, s', w', hh.congr hf1 hd1 hr1⟩

/-- **The jump to the tail call** at the last level `k`: X23 becomes level `k`'s address, then
`final_level`. -/
theorem final_stage (hp : Placed code k0)
    (hfl : ∀ a s level ba b w rounds, Spec (Labels.label NativeRustcVmArm.Vm.FinalLevel.entryLabel)
      (FinalLevelPre a s level ba b w rounds) (FinalLevelPost a s level b w rounds))
    (c : Ctx a s0 levels ba b claim m0 rate) {k j : Nat} {ds : List Directive}
    (hds : ds.IsInfixAt code j) (hne : ds ≠ []) {S' : SState} {v : Sym}
    (hx : exec ds regsS = some (S', .jump NativeRustcVmArm.Vm.WhirLevels.label_3)) (hok : JumpOk v S' = true)
    {s : TState} {w : WhirStateW} {rs : Array FoldRoundW} {st : MachineState}
    (hv : v.eval (Env.ofMachine st.data []) = lvA m0 + BitVec.ofNat 64 (levelBytes * k))
    (hm : Mid a s0 levels b claim m0 rate k s w rs st.data) (hk : k + 1 = levels.length)
    (hx5 : st.data.regs.X5.toNat = logN m0 - w.alphas.size)
    (hpc : st.pc = Host.addrOf (k0 + j)) :
    Eventually (step1 Host.exe) (Goal a s0 levels b claim m0) st := by
  have hok' := hok
  simp only [JumpOk, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.all_eq_true] at hok'
  obtain ⟨⟨⟨hmem, hsp⟩, h23⟩, hall⟩ := hok'
  have hm0 := match_nil st.data
  refine hm.fr.regsBlock (inf hp hds hne) hx hpc hmem hsp (by
    simp only [keptRegs, keep, List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq]
    exact hall .X29 (by simp)) fun st1 hf1 hd1 hm1 hpc1 ↦ ?_
  have hk' : ∀ r ∈ [XReg.X5, .X19, .X20, .X21, .X22, .X24, .X25, .X29],
      st1.data.regs.getXReg r = st.data.regs.getXReg r := fun r hr ↦
    Match.reg_eq hm0 hm1 (by cases r <;> rfl) (hall r hr)
  simp only [PcOk] at hpc1
  rw [hp.label (j := NativeRustcVmArm.Vm.WhirLevels.b4Offset) NativeRustcVmArm.Vm.WhirLevels.label_3_at] at hpc1
  have hr := hm.regs
  refine final_tail hp hfl c hf1 hpc1 (by rw [hd1]; exact hm.ts) (by rw [hd1]; exact hm.wa) hk
    hm.alphas ((hm.fin hk).trans (by rfl)) ((hk' .X19 (by simp)).trans hr.x19)
    ((hk' .X20 (by simp)).trans hr.x20) ((hk' .X21 (by simp)).trans hr.x21)
    ((hk' .X22 (by simp)).trans hr.x22) ((reg_val hm1 h23).trans hv) ?_ ?_
  · rw [hk' .X24 (by simp), hr.x24]; omega
  · rw [show st1.data.regs.X5 = st1.data.regs.getXReg .X5 from rfl, hk' .X5 (by simp)]
    exact hx5

end

end

end NativeRustcVmArm.Whir.WhirLevels
