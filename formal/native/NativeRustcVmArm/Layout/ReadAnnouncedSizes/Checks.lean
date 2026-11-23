module

public import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmArm.Layout.ReadAnnouncedSizes.Exec
public import NativeRustcVmArm.Layout.Frame
public import NativeRustcVmArm.Transcript.Stack
public import NativeRustcVm.Transcript.Update
public import NativeRustcVm.Tables.Same
public import NativeRustcVm.Sumcheck.RoundPoly
public import NativeVm.Math.Layout

/-!
# `read_announced_sizes`: the body and the high limbs' checks

The prologue (`b0`) saves X30, X19-X21 in its 208-byte frame (`Fr`, the outputs the layout and the
`TState`), keeps `layout` in X19 and `bytecode_len` in X20 and reads the eight scalars into
`announced` (frame bytes `0`-`128`). After them (`Mid`), `b2`-`b9` check the high limbs (`checks`:
any nonzero, return `0` with `fail14`/`fail16`).
-/

namespace NativeRustcVmArm.Layout.ReadAnnouncedSizes

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReadAnnouncedSizes NativeVm.Model
open NativeRustcVm.Layout NativeRustcVm.Transcript
open NativeRustcVmArm.Arrays (calleeRegs inSlots keepsAll restores entry_match load8_eq)
open NativeRustcVm (wordOf wordsOf WordAt WordsAt EWsAt wordOf_of_wordAt)
open NativeVm.Math.Layout (tailP readAnnouncedSizes_run)

public section

/-- The stack. -/
abbrev N : Nat := readAnnouncedSizesStack
/-- The `TState`. -/
abbrev tt (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec
/-- The layout. -/
abbrev ll (m : MachineData) : BitVec 64 := m.regs.X2.toBitVec
/-- The outputs. -/
@[expose] def Rout (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (ll m0) layoutBytes q ∨ InRange (tt m0) tstateBytes q
/-- The body. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 208 N slots (Rout m0) st

theorem le_rs : 208 + readScalarsStack ≤ N := by
  show _ ≤ 208 + max _ _; omega
theorem le_bl : 208 + buildLayoutStack ≤ N := by
  show _ ≤ 208 + max _ _; omega

/-- The registers the body keeps: the layout in X19, the bytecode's length in X20. -/
structure Regs (m0 st : MachineData) : Prop where
  x19 : st.regs.X19 = m0.regs.X2
  x20 : st.regs.X20 = m0.regs.X1

variable [Host] {k : Nat}

theorem lbl_entry (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.ReadAnnouncedSizes.entryOffset) NativeRustcVmArm.Vm.ReadAnnouncedSizes.entry_at
theorem lbl_12 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.label_12 = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b14Offset) := hp.label (j := NativeRustcVmArm.Vm.ReadAnnouncedSizes.b14Offset) NativeRustcVmArm.Vm.ReadAnnouncedSizes.label_12_at
theorem lbl_13 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b15Offset) := hp.label (j := NativeRustcVmArm.Vm.ReadAnnouncedSizes.b15Offset) NativeRustcVmArm.Vm.ReadAnnouncedSizes.label_13_at
theorem lbl_14 (hp : Placed code k) :
    Labels.label NativeRustcVmArm.Vm.ReadAnnouncedSizes.label_14 = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b16Offset) := hp.label (j := NativeRustcVmArm.Vm.ReadAnnouncedSizes.b16Offset) NativeRustcVmArm.Vm.ReadAnnouncedSizes.label_14_at

/-- The postcondition, reached. -/
abbrev Post (bc : Array UInt64) (a : DecArea) (s : TState) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ ReadAnnouncedSizesPost bc a s m0 st.data

/-- In the body: the frame (region 0), SP its base. -/
theorem fr_match {m0 st : MachineData} (hpre : StackOk m0 N) (hb : Fr m0 st) :
    (Env.ofMachine st [(fbase m0 208, 208)]).WF ∧
      Match (Env.ofMachine st [(fbase m0 208, 208)]) frS st := by
  obtain ⟨hmap, hnw, -⟩ := Arrays.frame_ok hpre (show 208 ≤ N by have := le_rs; omega)
  refine ⟨Arrays.wf_one (fun i hi ↦ hb.kept _ (hmap i hi)) hnw,
    match_ofMachine ⟨rfl, fun _ ↦ Arrays.frame_aligned hpre (show 208 ≤ N by have := le_rs; omega)
      rfl, trivial⟩ ?_ trivial trivial trivial trivial⟩
  rw [hb.sp]; simp [Sym.eval]

/-- **An epilogue** (`b14`, `b15`, `b16`): the entry's registers restored, memory unchanged,
X0, X1 as the block sets them. -/
theorem exit_block {ds : List Directive} {kk : Nat} {S1 : SState}
    (hk : ds.IsInfixAt Host.prog kk) (hx : exec ds frS = some (S1, .ret))
    (hres : restores slots 208 S1 = true) (hmem : S1.mem = [])
    {m0 : MachineData} (hpre : StackOk m0 N) {st : MachineState} (hpc : st.pc = Host.addrOf kk)
    (hb : Fr m0 st.data) {Q : MachineState → Prop}
    (hQ : ∀ s, s.pc = retOf m0 → Saved m0 s.data → s.data.dmem = st.data.dmem →
      Match (Env.ofMachine st.data [(fbase m0 208, 208)]) S1 s.data → Q s) :
    Eventually (step1 Host.exe) Q st := by
  obtain ⟨hwf, hm⟩ := fr_match hpre hb
  refine exec_at hk hx hwf hpc hm fun s hm' hpc' ↦ .done _ ?_
  obtain ⟨hsaved, hx30⟩ := Frame.saved hb hm' hwf (by simp [slots]) hres
  refine hQ s ?_ hsaved (hm'.dmem_eq hwf hmem) hm'
  simp only [PcOk] at hpc'
  rw [hpc']; simp only [retOf, hx30]

omit [Host] in
/-- **A failure's return** (`b14`-`b16` with X0 = `0`). -/
theorem fail_post {bc : Array UInt64} {a : DecArea} {s : TState} {m0 : MachineData}
    {st : MachineState} (hb : Fr m0 st.data) (hr : (readAnnouncedSizes bc).run s = none)
    (s' : MachineState) (hpc : s'.pc = retOf m0) (hsaved : Saved m0 s'.data)
    (hd : s'.data.dmem = st.data.dmem) (hx0 : s'.data.regs.X0 = 0) : Post bc a s m0 s' := by
  refine ⟨hpc, ?_⟩
  unfold ReadAnnouncedSizesPost
  refine ⟨by rw [hx0, hr]; rfl, fun L rate s1 h ↦ (by rw [hr] at h; cases h), ?_, hsaved⟩
  intro q hq
  rw [hd]
  exact hb.same q fun h ↦ hq (by
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h))

/-- `b16` with X0 = `0`. -/
theorem fail16 (hp : Placed code k) {bc : Array UInt64} {a : DecArea} {s : TState}
    {m0 : MachineData} (hpre : StackOk m0 N) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b16Offset)) (hb : Fr m0 st.data) (hx0 : st.data.regs.X0 = 0)
    (hr : (readAnnouncedSizes bc).run s = none) :
    Eventually (step1 Host.exe) (Post bc a s m0) st := by
  obtain ⟨-, -, -, -, h16, h16m⟩ := restores_b14_b16
  refine exit_block (infix_of b16_in_code (by simp [b16]) hp) run_b16 h16 h16m hpre hpc hb
    fun s' hpc' hsaved hd hm ↦ fail_post hb hr s' hpc' hsaved hd ?_
  rw [← hx0]
  exact UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl)

/-- `b14` with X0 = `0`. -/
theorem fail14 (hp : Placed code k) {bc : Array UInt64} {a : DecArea} {s : TState}
    {m0 : MachineData} (hpre : StackOk m0 N) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b14Offset)) (hb : Fr m0 st.data) (hx0 : st.data.regs.X0 = 0)
    (hr : (readAnnouncedSizes bc).run s = none) :
    Eventually (step1 Host.exe) (Post bc a s m0) st := by
  obtain ⟨h14, h14m, -⟩ := restores_b14_b16
  refine exit_block (infix_of b14_in_code (by simp [b14]) hp) run_b14 h14 h14m hpre hpc hb
    fun s' hpc' hsaved hd hm ↦ fail_post hb hr s' hpc' hsaved hd ?_
  rw [← hx0]
  exact UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl)

/-- `b15`: X0 = `0`. -/
theorem fail15 (hp : Placed code k) {bc : Array UInt64} {a : DecArea} {s : TState}
    {m0 : MachineData} (hpre : StackOk m0 N) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b15Offset)) (hb : Fr m0 st.data)
    (hr : (readAnnouncedSizes bc).run s = none) :
    Eventually (step1 Host.exe) (Post bc a s m0) st := by
  obtain ⟨-, -, h15, h15m, -⟩ := restores_b14_b16
  refine exit_block (infix_of b15_in_code (by simp [b15]) hp) run_b15 h15 h15m hpre hpc hb
    fun s' hpc' hsaved hd hm ↦ fail_post hb hr s' hpc' hsaved hd ?_
  exact UInt64.toBitVec_inj.mp (hm.regs .X0 _ rfl)

/-- A block of the body writing nothing keeps it. -/
theorem fr_step {m0 st st' : MachineData} {S1 : SState} (hpre : StackOk m0 N) (hb : Fr m0 st)
    (hm : Match (Env.ofMachine st [(fbase m0 208, 208)]) frS st)
    (hm' : Match (Env.ofMachine st [(fbase m0 208, 208)]) S1 st')
    (hwf : (Env.ofMachine st [(fbase m0 208, 208)]).WF)
    (hk : keepsAll frS { S1 with mem := [] } keptRegs = true) (hmem : S1.mem = []) :
    Fr m0 st' ∧ st'.dmem = st.dmem := by
  have hd : st'.dmem = st.dmem := hm'.dmem_eq hwf hmem
  exact ⟨Frame.of_block hb hpre (by have := le_rs; omega) hm hm' hwf hk (fun p _ ↦ by rw [hd])
    (fun _ _ _ _ ↦ by rw [hd]), hd⟩

/-- **After the scalars**: the body, X0 `0`, X19, X20 kept, the eight scalars in `announced`. -/
structure Mid (m0 : MachineData) (xs : Array EW) (D : Mem 64) (st : MachineData) : Prop where
  fr : Fr m0 st
  dm : st.dmem = D
  regs : Regs m0 st
  x0 : st.regs.X0 = 0
  mem : EWsAt st.dmem (fbase m0 208) xs.toList
  size : xs.size = 8

omit [Host] in
/-- Limb `c` of scalar `i`. -/
theorem Mid.word {m0 st : MachineData} {xs : Array EW} {D : Mem 64} (h : Mid m0 xs D st) {i : Nat}
    (hi : i < 8) :
    WordAt st.dmem (fbase m0 208 + BitVec.ofNat 64 (16 * i)) (xs[i]'(by rw [h.size]; exact hi)).c0 ∧
    WordAt st.dmem (fbase m0 208 + BitVec.ofNat 64 (16 * i + 8))
      (xs[i]'(by rw [h.size]; exact hi)).c1 := by
  have := NativeRustcVm.ewsAt_getElem h.mem (i := i) (by simp only [Array.length_toList, h.size]; exact hi)
  rw [NativeRustcVm.ewAt_iff] at this
  simp only [Array.getElem_toList] at this
  refine ⟨this.1, ?_⟩
  rw [← NativeRustcVm.addr_add]
  exact this.2

omit [Host] in
theorem load_frame {st : MachineData} {fb : BitVec 64} {o : Nat} {v : UInt64}
    (h : WordAt st.dmem (fb + BitVec.ofNat 64 o) v) :
    (Env.ofMachine st [(fb, 208)]).load 0 o 8 = v.toBitVec :=
  load_word (env := Env.ofMachine st [(fb, 208)]) h

/-- **A check of a high limb** (`ldr x8, [sp, #o]`, `cbnz x8, l`). -/
theorem c1_check {ds : List Directive} {kk o : Nat} {l : Label} {S1 : SState}
    (hk : ds.IsInfixAt Host.prog kk)
    (hx : exec ds frS = some (S1, .cond (.not (.cmp .eq .W64 (.load 0 o 8) (.lit 0))) l))
    (hkeep : keepsAll frS { S1 with mem := [] } keptRegs = true) (hmem : S1.mem = [])
    (hregs : ([XReg.X0, .X19, .X20].all fun r ↦ (frS.reg r).isSome && S1.reg r == frS.reg r) = true)
    {m0 : MachineData} (hpre : StackOk m0 N) {xs : Array EW} {D : Mem 64} {st : MachineState}
    (hpc : st.pc = Host.addrOf kk) (hM : Mid m0 xs D st.data) {v : UInt64}
    (hw : WordAt st.data.dmem (fbase m0 208 + BitVec.ofNat 64 o) v) {R : MachineState → Prop}
    (hne : ∀ s, s.pc = Labels.label l → Mid m0 xs D s.data → v ≠ 0 → Eventually (step1 Host.exe) R s)
    (heq : ∀ s, s.pc = Host.addrOf (kk + ds.length) → Mid m0 xs D s.data → v = 0 →
      Eventually (step1 Host.exe) R s) : Eventually (step1 Host.exe) R st := by
  obtain ⟨hwf, hm⟩ := fr_match hpre hM.fr
  refine exec_at hk hx hwf hpc hm fun s hm' hpc' ↦ ?_
  obtain ⟨hfr, hd⟩ := fr_step hpre hM.fr hm hm' hwf hkeep hmem
  have he := Arrays.regs_eq_of hm hm' _ hregs
  have hM' : Mid m0 xs D s.data := ⟨hfr, hd.trans hM.dm, ⟨(he .X19 (by simp)).trans hM.regs.x19,
    (he .X20 (by simp)).trans hM.regs.x20⟩, (he .X0 (by simp)).trans hM.x0, hd ▸ hM.mem, hM.size⟩
  simp only [PcOk] at hpc'
  sym_simp at hpc'
  rw [load_frame hw] at hpc'
  obtain ⟨hy, hn⟩ := pc_ne' hpc'
  by_cases hv : v = 0
  · exact heq s (hn (by rw [hv]; rfl)) hM' hv
  · exact hne s (hy fun h ↦ hv (UInt64.toNat_inj.mp (by simpa using h))) hM' hv

omit [Host] in
/-- A nonzero high limb: `None`. -/
theorem run_none_c1 {bc : Array UInt64} {s s1 : TState} {xs : Array EW}
    (hrs : (readScalars 8).run s = some (xs, s1)) {i : Nat} (hi : i < xs.size)
    (h : xs[i].c1 ≠ 0) : (readAnnouncedSizes bc).run s = none := by
  rw [readAnnouncedSizes_run, show 2 + nTables = 8 from rfl, hrs]
  have : (xs.all fun x ↦ x.c1 == 0) = false := by
    rw [Bool.eq_false_iff]
    intro ha
    rw [Array.all_eq_true] at ha
    exact h (by simpa using ha i hi)
  simp only [Option.bind_some, tailP, this, Bool.false_eq_true, ↓reduceIte,
    Option.map_none]

/-- **The high limbs' checks** `b2`-`b9`: any nonzero, `None`; else on to `b10`. -/
theorem checks (hp : Placed code k) {bc : Array UInt64} {a : DecArea} {s s1 : TState}
    {m0 : MachineData} (hpre : StackOk m0 N) {xs : Array EW}
    (hrs : (readScalars 8).run s = some (xs, s1)) {D : Mem 64} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b2Offset)) (hM : Mid m0 xs D st.data)
    (h10 : ∀ s', s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b10Offset) → Mid m0 xs D s'.data →
      (∀ i (hi : i < xs.size), xs[i].c1 = 0) → Eventually (step1 Host.exe) (Post bc a s m0) s') :
    Eventually (step1 Host.exe) (Post bc a s m0) st := by
  have hsz := hM.size
  obtain ⟨-, -, k2, m2, k3, m3, k4, m4, k5, m5, k6, m6, k7, m7, k8, m8, k9, m9, -⟩ := keeps_b1_b9
  refine c1_check (infix_of b2_in_code (by simp [b2]) hp) run_b2 k2 m2 rfl hpre
    hpc hM (hM.word (i := 0) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail16 hp hpre (hpc'.trans (lbl_14 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h0 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b3Offset) := hpc
  refine c1_check (infix_of b3_in_code (by simp [b3]) hp) run_b3 k3 m3 rfl hpre
    hpc hM (hM.word (i := 1) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail16 hp hpre (hpc'.trans (lbl_14 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h1 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b4Offset) := hpc
  refine c1_check (infix_of b4_in_code (by simp [b4]) hp) run_b4 k4 m4 rfl hpre
    hpc hM (hM.word (i := 2) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail16 hp hpre (hpc'.trans (lbl_14 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h2 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b5Offset) := hpc
  refine c1_check (infix_of b5_in_code (by simp [b5]) hp) run_b5 k5 m5 rfl hpre
    hpc hM (hM.word (i := 3) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail16 hp hpre (hpc'.trans (lbl_14 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h3 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b6Offset) := hpc
  refine c1_check (infix_of b6_in_code (by simp [b6]) hp) run_b6 k6 m6 rfl hpre
    hpc hM (hM.word (i := 4) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail16 hp hpre (hpc'.trans (lbl_14 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h4 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b7Offset) := hpc
  refine c1_check (infix_of b7_in_code (by simp [b7]) hp) run_b7 k7 m7 rfl hpre
    hpc hM (hM.word (i := 5) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail16 hp hpre (hpc'.trans (lbl_14 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h5 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b8Offset) := hpc
  refine c1_check (infix_of b8_in_code (by simp [b8]) hp) run_b8 k8 m8 rfl hpre
    hpc hM (hM.word (i := 6) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail16 hp hpre (hpc'.trans (lbl_14 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h6 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b9Offset) := hpc
  refine c1_check (infix_of b9_in_code (by simp [b9]) hp) run_b9 k9 m9 rfl hpre
    hpc hM (hM.word (i := 7) (by decide)).2 (fun s' hpc' hM' hv ↦
      fail14 hp hpre (hpc'.trans (lbl_12 hp)) hM'.fr hM'.x0 (run_none_c1 hrs (by omega) hv))
    fun st hpc hM h7 ↦ ?_
  replace hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.ReadAnnouncedSizes.b10Offset) := hpc
  refine h10 st hpc hM fun i hi ↦ ?_
  have hi8 : i < 8 := by omega
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals assumption

end

end NativeRustcVmArm.Layout.ReadAnnouncedSizes
