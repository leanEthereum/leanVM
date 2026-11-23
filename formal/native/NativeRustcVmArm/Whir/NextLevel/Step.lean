module

public import NativeRustcVmArm.Whir.NextLevel.Basic
public import NativeRustcVmArm.Whir.Frame

/-!
# `next_level`: blocks, calls, exits

The environments of the blocks (`envF` the frame, `envL` with the level, `envW` with the `WhirW`)
and their symbolic states' matches (`mF`, `mL`, `mB`, `mR`). `blk`: a block whose writes are in
the frame off the slots; `ncall`: a call writing its stack, a range of the frame and the outputs.
`epi`: the epilogue (`b27`); `none_exit`: `None` returned there.
-/

namespace NativeRustcVmArm.Whir.NextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir LeanVM.Parameters NativeRustcVmArm.Vm.NextLevel

@[expose] public section

/-- The frame. -/
abbrev envF (m0 st : MachineData) : Env := Env.ofMachine st [(base m0 8192, 8192)]
/-- The frame and the level. -/
abbrev envL (m0 st : MachineData) : Env := Env.ofMachine st [(base m0 8192, 8192), (lA m0, 24)]
/-- The frame and the `WhirW`. -/
abbrev envW (m0 st : MachineData) : Env :=
  Env.ofMachine st [(base m0 8192, 8192), (pA m0, 63200)]

/-- The model's run. -/
abbrev runN (level : Whir.Level) (w : WhirStateW) (rounds : Array FoldRoundW) (m0 : MachineData)
    (s : TState) : Option (WhirStateW × TState) :=
  (nextLevelM m0.regs.X1.toNat level ⟨m0.regs.X3.toNat, m0.regs.X4.toNat, 0⟩ m0.regs.X5.toNat w
    rounds).run s

/-- `next_level`'s postcondition, reached. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (level : Whir.Level) (w : WhirStateW)
    (rounds : Array FoldRoundW) (m0 : MachineData) (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ NextLevelPost a s level w rounds m0 st.data

end

public section

theorem inf [Host] {k : Nat} (hp : Placed code k) {b : List Directive} {j : Nat}
    (hb : b.IsInfixAt code j) (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

theorem fw_r0 {S : SState} {F : Nat} {sl : List (Nat × XReg)} (h : frameWrites S F sl [] = true) :
    ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ F := by
  intro w hw
  simp only [frameWrites, List.all_eq_true] at h
  have := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_nil, Bool.false_and, Bool.false_eq_true, or_false] at this
  exact this.1

section
variable [Labels] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData}

theorem hN8 (h : NextLevelPre a s level w rounds m0) : 8192 ≤ m0.regs.SP.toNat := by
  have := (geo h).hN; omega

theorem frNoWrap (h : NextLevelPre a s level w rounds m0) : NoWrap (base m0 8192) 8192 :=
  base_noWrap (hN8 h)

theorem frMapped (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st) :
    Mapped st.dmem (base m0 8192) 8192 :=
  fun i hi ↦ hf.kept _ (frame_mapped h.1.1 (by rw [stack_eq]; decide) i hi)

theorem frAligned (h : NextLevelPre a s level w rounds m0) : (base m0 8192).toNat % 16 = 0 :=
  frame_aligned h.1.1 (by rw [stack_eq]; decide) rfl

theorem lvlIn (h : NextLevelPre a s level w rounds m0) :
    Readable m0 (lA m0) levelBytes ∧ OffStack m0 (lA m0) levelBytes nextLevelStack :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem whirOut (h : NextLevelPre a s level w rounds m0) :
    WhirOut m0 (tA m0) a (pA m0) whirBytes nextLevelStack :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem wfF (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st) :
    (envF m0 st).WF :=
  Env.wf_of ⟨⟨frMapped h hf, frNoWrap h⟩, trivial⟩ (List.pairwise_singleton _ _)

theorem wfL (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st) :
    (envL m0 st).WF := by
  have g := geo h
  have hb := base_nat (m0 := m0) (F := 8192) (hN8 h)
  refine Env.wf_of ⟨⟨frMapped h hf, frNoWrap h⟩, ⟨fun i hi ↦ hf.kept _ ((lvlIn h).1.1 i hi),
    (lvlIn h).1.2⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  show Apart (base m0 8192) 8192 (lA m0) 24
  unfold Apart; rw [hb]; have := g.lS; have := g.hN; omega

theorem wfW (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st) :
    (envW m0 st).WF := by
  have g := geo h
  have hb := base_nat (m0 := m0) (F := 8192) (hN8 h)
  have ho := (whirOut h).1
  refine Env.wf_of ⟨⟨frMapped h hf, frNoWrap h⟩, ⟨fun i hi ↦ hf.kept _ (ho.1 i hi),
    ho.2.1⟩, trivial⟩ (List.pairwise_pair.mpr ?_)
  show Apart (base m0 8192) 8192 (pA m0) 63200
  unfold Apart; rw [hb]; have := g.pS; have := g.hN; omega

theorem mF (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    {rs : List (BitVec 64 × Nat)} : Match (Env.ofMachine st ((base m0 8192, 8192) :: rs)) fS st :=
  match_ofMachine ⟨rfl, fun _ ↦ frAligned h, trivial⟩ (by rw [hf.sp]; simp [Sym.eval]) trivial
    trivial trivial trivial

theorem mL (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    (h28 : st.regs.X28 = m0.regs.X2) : Match (envL m0 st) levelS st :=
  match_ofMachine ⟨rfl, fun _ ↦ frAligned h, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hf.sp]; simp [Sym.eval])
    ⟨by show (st.regs.getXReg .X28).toBitVec = _; simp [Sym.eval]
        exact congrArg UInt64.toBitVec h28, trivial⟩ trivial trivial trivial

theorem mB (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    (h19 : st.regs.X19 = m0.regs.X6)
    (h28 : st.regs.X28.toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 61352) :
    Match (envW m0 st) bufS st :=
  match_ofMachine ⟨rfl, fun _ ↦ frAligned h, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hf.sp]; simp [Sym.eval])
    ⟨by show (st.regs.getXReg .X19).toBitVec = _; simp [Sym.eval]
        exact congrArg UInt64.toBitVec h19, trivial⟩ trivial trivial
    ⟨by show (st.regs.getXReg .X28).toBitVec = _; simp; exact h28, trivial⟩

theorem mR (h : NextLevelPre a s level w rounds m0) {st : MachineData} (hf : NFr m0 st)
    (h19 : st.regs.X19 = m0.regs.X6)
    (h24 : st.regs.X24.toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 57344) :
    Match (envW m0 st) rowsS st :=
  match_ofMachine ⟨rfl, fun _ ↦ frAligned h, rfl, fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hf.sp]; simp [Sym.eval])
    ⟨by show (st.regs.getXReg .X19).toBitVec = _; simp [Sym.eval]
        exact congrArg UInt64.toBitVec h19, trivial⟩ trivial trivial
    ⟨by show (st.regs.getXReg .X24).toBitVec = _; simp; exact h24, trivial⟩

end

/-! ## Blocks and calls -/

section
variable [Host] {a : DecArea} {s : TState} {level : Whir.Level} {w : WhirStateW}
  {rounds : Array FoldRoundW} {m0 : MachineData} {k : Nat}

/-- **A block** whose writes are in the frame off the slots. -/
theorem blk (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    {rs : List (BitVec 64 × Nat)} {S0 S' : SState} {x : Exit} {ds : List Directive} {j : Nat}
    (hk : ds.IsInfixAt code j) (hne : ds ≠ []) (hx : exec ds S0 = some (S', x))
    {st : MachineState} (hwf : (Env.ofMachine st.data ((base m0 8192, 8192) :: rs)).WF)
    (hm : Match (Env.ofMachine st.data ((base m0 8192, 8192) :: rs)) S0 st.data)
    (hfw : frameWrites S' 8192 slots [] = true) (hsp : S'.sp = S0.sp)
    (hf : NFr m0 st.data) (hpc : st.pc = Host.addrOf (k + j)) {R : MachineState → Prop}
    (cont : ∀ st', Match (Env.ofMachine st.data ((base m0 8192, 8192) :: rs)) S' st'.data →
      PcOk (Env.ofMachine st.data ((base m0 8192, 8192) :: rs)) x
        (Host.addrOf (k + j + ds.length)) st' →
      NFr m0 st'.data → SameOutside st.data.dmem st'.data.dmem (InRange (base m0 8192) 8192) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st :=
  exec_at (inf hp hk hne) hx hwf hpc hm fun st' hm' hpc' ↦ cont st' hm' hpc'
    (Fr.ofBlockW hf hm hm' hwf rfl hsp (fun _ h ↦ by cases h) rfl (by rw [stack_eq]; decide)
      (by rw [stack_eq]; exact (geo h).hN) slots_le'
      (writeOk_of hm' hfw (fun r hr ↦ by cases hr)))
    (NativeRustcVm.SameOutside.mono (hm'.sameOutside hwf) fun q hq ↦
      written_r0 hwf rfl (fw_r0 hfw) hq)

/-- **A call** writing its stack, the frame's `n` bytes at `o` and the outputs. -/
theorem ncall (c : TCtx m0 8192 nextLevelStack (tA m0) a (outs m0)) {st : MachineState}
    (hf : NFr m0 st.data) {l : Label} {P : MachineData → Prop}
    {Q : MachineData → MachineData → Prop} {N' o n : Nat} {next : Int64} {R : MachineState → Prop}
    (hle : 8192 + N' ≤ nextLevelStack) (hon : o + n ≤ 8096) (hspec : Spec (Labels.label l) P Q)
    (hpc : st.pc = Labels.label l ∧ retOf st.data = next) (hP : P st.data)
    (hQ : ∀ m', Q st.data m' → SameOutside st.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow st.data N') N' q ∨ InRange (loc m0 o) n q ∨ outs m0 q) ∧
      Saved st.data m')
    (cont : ∀ m2, NFr m0 m2 → Q st.data m2 → SameOutside st.data.dmem m2.dmem (fun q ↦
      InRange (stackBelow st.data N') N' q ∨ InRange (loc m0 o) n q ∨ outs m0 q) →
      (∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r) →
      Eventually (step1 Host.exe) R ⟨m2, next⟩) :
    Eventually (step1 Host.exe) R st :=
  Fr.callW hf c.hN hle (fun _ h ↦ by cases h) slots_le' c.frame_outs (o := o) (n := n) (by omega)
    (fun p hp ↦ Or.inl (by have := slots_le p hp; omega)) (spec_with hspec (· = st.data))
    (fun m m' ⟨hq, he⟩ ↦ by subst he; exact hQ m' hq) hpc ⟨hP, rfl⟩
    fun m2 hf2 ⟨hq, _⟩ hcs ↦ cont m2 hf2 hq (hQ m2 hq).1 hcs

/-- **The epilogue** (`b27`): the entry's return address and callee-saved registers, X0 and the
memory kept. -/
theorem epi (hp : Placed code k) (h : NextLevelPre a s level w rounds m0)
    {outs' : BitVec 64 → Prop} {st : MachineState}
    (hf : Fr m0 8192 nextLevelStack slots [] outs' st.data)
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NextLevel.b27Offset)) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = retOf m0 ∧
      st'.data.regs.X0 = st.data.regs.X0 ∧ st'.data.dmem = st.data.dmem ∧
        Saved m0 st'.data) st := by
  have hwf : (envF m0 st.data).WF :=
    Env.wf_of ⟨⟨fun i hi ↦ hf.kept _ (frame_mapped h.1.1 (by rw [stack_eq]; decide) i hi),
      frNoWrap h⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (envF m0 st.data) fS st.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frAligned h, trivial⟩ (by rw [hf.sp]; simp [Sym.eval]) trivial
      trivial trivial trivial
  refine exec_at (inf hp b27_in_code (by simp [b27])) run_b27 hwf hpc hm fun st' hm' hpc' ↦ ?_
  have hok : exitOk (after b27 fS) 8192 slots [] = true := by rw [after_eq run_b27]; decide
  have hmem : (after b27 fS).mem = [] := by rw [after_eq run_b27]
  have hx0 : (after b27 fS).reg .X0 = some (.reg .X0) := by rw [after_eq run_b27]; rfl
  rw [after_eq run_b27] at hok hmem hx0
  obtain ⟨hret, hsv⟩ := hf.exit hm' hwf hok
  simp only [PcOk] at hpc'
  exact .done _ ⟨hpc'.trans hret, reg_of hm' hx0 rfl, hm'.dmem_eq hwf hmem, hsv⟩

end

end

end NativeRustcVmArm.Whir.NextLevel
