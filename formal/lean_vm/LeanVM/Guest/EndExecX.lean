module

public import LeanVM.Guest.EndExec
public import LeanVM.Guest.EndExecXOp
public import LeanVM.Guest.Bridge.AlignTrack
public import LeanVM.Guest.Bridge.StepRule
public import LeanVM.Guest.Memory.HonestX
public import LeanVM.Guest.Memory.HintsIn
public import LeanVM.Guest.Bytecode
public import LeanVM.Guest.EndExecEntry
public import LeanVM.Guest.Bridge.ProgAlData
public import LeanVM.Guest.Check
public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.Exact.Every
import all Statement.Data.Bytecode
import all Statement.Data.AdviceHints

/-!
# The honest reference and the tree track along it

The hint tracks read a reference run through the honest tree it is the memory of: `RefD` (the
reader `rd0` B1's tree is valid on, the honest tree `T`, the heap words `X` its hints write) and
`RefH L d r`, what the hint tracks take of it, on the aligned layout `L` (`Lay`: frame sizes, the
per-callee alignment flag `al`, headers, frame cells, certificate cells; b2c's
`Memory/{AllocA, MemoryA, HonestX}`). A family `D : Ref → RefD` picks the data of each reference, so
the reference runs the hint fields are proved on are `RefH L (D r) r` (b2c's `ref_exists` builds
them).

`RefTrack L D A r`: the tree track (`Bridge.RefOk`) on `r`'s honest tree, its instances placed by
the aligned allocator (`honestInstsA`), against `r`'s memory, at the entries and alignment `A`
gives. `traceRef`: from `main`'s entry, a trace of track states along `r`'s run, under the
program's alignments (`ProgAl`) and the jumps' cells (`JumpCells`). `posAt`: past the prologue,
the executor's registers are those the run from `main`'s entry reaches (from route's `Trace` and the
prologue's run, `RefH.pro`); `trackAt`: there the track has a state at the executor's pc and frame.

`YU r s`: the cells the executor touched lie within the reference's `2^κ`, the hint tracks' part
`usedY` reads; `initY_used` and `keepY_used` start and keep it, given that the hints keep it
(`HintsUsed`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The honest reference -/

/-- **The guest's aligned layout**: frame sizes, whether a callee's frames are allocated aligned,
callee headers, frame cells and certificate cells (b2c's `B2C.fs`, `al`, `H`, `C`, `cert`). -/
structure Lay where
  fs : String → ℕ
  al : String → Bool
  H : Inst → ℕ → E × E
  C : Inst → List (ℕ × E)
  cert : String → V → ℕ

/-- **The honest data behind a reference run**: the reader `rd0` B1's tree is valid on, the honest
tree `T`, and the heap words `X` its hints write. -/
structure RefD where
  rd0 : Reader
  T : Tree
  X : List Write

/-- The header of a node's frame `0`: the public input's words. -/
abbrev Ref.hdr (r : Ref) : E × E := (r.input.word0, r.input.word1)

/-- The honest instances of `d`'s tree, aligned. -/
noncomputable abbrev instsOf (L : Lay) (d : RefD) (r : Ref) : List Inst :=
  honestInstsA coreProgram L.fs L.al L.H r.hdr d.T

/-- The honest memory of `d`'s tree, extended by `X`. -/
noncomputable abbrev imgOf (L : Lay) (d : RefD) (r : Ref) :
    MemoryImage (logMem (d.T.wordsA L.fs coreProgram.loop L.al)) :=
  honestX coreProgram L.fs L.al L.H L.C r.hdr d.T d.X

/-- **The hint-only cells of compiled function `j`**: its alignment's (`Bridge.alignExtras`, the
core route's data; `Bridge.extraOf`). -/
noncomputable def exA (j : ℕ) : List (ℕ × ℕ) := (LeanVM.Guest.Check.getF LeanVM.Guest.Bridge.alignExtras j).getD []

/-- **A reference run of the honest tree**: its memory is `d`'s honest memory extended by `X`,
honest on the aligned layout, `main`'s tree, whose prologue runs straight into `main`'s entry and
whose pops on `rd0` are the honest pushes, stream by stream; the tree exact on `rd0`, and each
instance's hint-only values (`exA`) at their cells. -/
structure RefH (L : Lay) (d : RefD) (r : Ref) : Prop where
  /-- The memory's log-size is the honest tree's. -/
  κ : r.κ = logMem (d.T.wordsA L.fs coreProgram.loop L.al)
  /-- The memory reads as the extended honest memory. -/
  img : ∀ a, r.img.read a = (imgOf L d r).read a
  /-- `main`'s tree. -/
  name : d.T.name = "main"
  /-- Honest on the aligned layout, placed from word `0`, with its extension. -/
  honest : ∃ rd, HonestAtA coreProgram L.fs L.al L.H L.C r.hdr d.T L.cert rd [] [] ∧
    HonestX coreProgram L.fs L.al L.H L.C r.hdr d.T rd [] [] d.X
  /-- The prologue runs pc by pc in frame `0` into `main`'s entry. -/
  pro : ∀ i ≤ proLen, run guestProgram r.img i Registers.initial = some (regs i 0)
  /-- The memory holds each heap word the tree's hints write, as `rd0` does. -/
  hintWords : ∀ a ∈ hintWords coreProgram L.fs L.al L.H r.hdr d.T, ∃ v, d.rd0 a = some v ∧
    r.img.read a = some v
  /-- The tree pops the honest pushes, stream by stream. -/
  pops : SameStreams (d.T.pops coreProgram d.rd0)
    (Prover.honestPushes (bytecodeWords guestProgram) r.seed r.s r.w)
  /-- Every node exact on `rd0`: each computed hint writes the executor's formula. -/
  exact : d.T.Every (ExactAt coreProgram d.rd0)
  /-- The memory holds each instance's hint-only values at their cells. -/
  extra : ∀ I ∈ instsOf L d r, ∀ f σ bufs kids, I.t = .node f σ bufs kids →
    ∀ v ∈ (I.t.events coreProgram).flatMap Ev.uses, ∀ c, (exA ((B2C.idxOf f).getD 0)).lookup v.idx = some c →
      I.fp + c < 2 ^ 30 ∧ r.img.read (addressOfIndex (I.fp + c)) = some (σ v)

/-- **The tree track against `r`'s run**, at the entries and alignment `A` gives. -/
abbrev RefTrack (L : Lay) (D : Ref → RefD) (A : String → FnAl) (r : Ref) :
    ℕ → ℕ → List Pop × List Ent → Prop :=
  Bridge.RefOk coreProgram (D r).rd0 (instsOf L (D r) r) (D r).T (memOf r.img) (entOf A) (alOf A)

/-- **What each frame's jumps read**, on every reference run of the honest tree. -/
def JumpCellsAt (L : Lay) (D : Ref → RefD) (A : String → FnAl) : Prop :=
  ∀ r, RefH L (D r) r → r.Ok → ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) →
    JumpCells r.img A e pc

/-- **The alignments at the compiled functions**: each function's alignment is at its compiled
function's entry, over at most its instructions. -/
def AlLayout (A : String → FnAl) : Prop :=
  ∀ f fn, coreProgram.find? f = some fn → ∃ cf ∈ Data.functions, entOf A f = cf.entryPc ∧
    (A f).code.length ≤ cf.instructionCount

section

variable {L : Lay} {D : Ref → RefD} {A : String → FnAl}

/-- **The honest instances are closed under callees**, each at its callee frame. -/
theorem honestA_closed {hdr : E × E} {T : Tree} :
    ∀ I ∈ honestInstsA coreProgram L.fs L.al L.H hdr T, ∀ (i : ℕ) (k : Tree), I.t.kids[i]? = some k →
      ∃ J ∈ honestInstsA coreProgram L.fs L.al L.H hdr T, J.t = k ∧ I.kidFps[i]? = some J.fp :=
  fun _ hI _ _ hk ↦
    let ⟨J, hJ, h1, h2, _⟩ := honestA_kid hI hk
    ⟨J, hJ, h1, h2⟩

theorem RefH.log {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) :
    logMem ((D r).T.wordsA L.fs coreProgram.loop L.al) ≤ 28 :=
  hR.κ ▸ hr.log

/-- **An honest instance's frame is below `maxCells`.** -/
theorem inst_fp_lt {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) {I : Inst} (hI : I ∈ instsOf L (D r) r) :
    I.fp < maxCells := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  have h2 := hH.cells.two_le I hI
  have hw := honestA_within hI (by omega)
  have hle := le_two_pow_logMem ((D r).T.wordsA L.fs coreProgram.loop L.al)
  have h28 : 2 ^ logMem ((D r).T.wordsA L.fs coreProgram.loop L.al) ≤ 2 ^ 28 :=
    Nat.pow_le_pow_right (by norm_num) (hR.log hr)
  unfold maxCells
  omega

/-- **The track at `main`'s entry**: `main`'s frame at its body, at frame `0`, nothing done, and
`main`'s instance. -/
theorem refTrack_main (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen)
    {r : Ref} (hR : RefH L (D r) r) :
    ∃ I fn, RefTrack L D A r proLen 0 ([], [Ent.enter coreProgram I fn]) := by
  obtain ⟨rd, hH, -⟩ := hR.honest
  obtain ⟨I, hI, hIt, hfp, -⟩ := rootA_inst (P := coreProgram) (fs := L.fs) (al := L.al) (H := L.H)
    (hdr := r.hdr) (T := (D r).T)
  have hv := hH.valid
  rw [← hIt] at hv
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? I.t.name = some fn := by
    rcases hIt' : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hIt'] at hv
      obtain ⟨fn, hf, -⟩ := hv
      exact ⟨fn, hf⟩
    · rw [hIt'] at hv; exact hv.elim
  have htr := trackOk_init (rd := (D r).rd0) hI hf hv
  rw [hIt] at htr
  have hname : I.t.name = "main" := by rw [hIt]; exact hR.name
  have hal0 : alOf A "main" 0 = some fn.body := by
    rw [hname] at hf
    change alignAt (A "main").X (A "main").body (A "main").code (A "main").d 0 = some fn.body
    rw [alignAt_zero (hP.ok _ _ hf), hP.body _ _ hf]
  have h0 := refOk_init (M := memOf r.img) (ent := entOf A) (al := alOf A) htr hfp (by rw [hname]; exact hal0)
  rw [hname, hmain] at h0
  exact ⟨I, fn, h0⟩

/-- **The trace along a reference run**, from `main`'s entry: a track state at the run's registers
after each of its `N` steps to the final registers but the last. -/
theorem traceRef (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen) {r : Ref}
    (hR : RefH L (D r) r) (hJ : ∀ pc fp done e st, RefTrack L D A r pc fp (done, e :: st) → JumpCells r.img A e pc)
    {N : ℕ} (hN : run guestProgram r.img N (regs proLen 0) = some (Registers.final guestProgram)) :
    ∃ tr : ℕ → ℕ × ℕ × (List Pop × List Ent), ∀ k < N,
      run guestProgram r.img k (regs proLen 0) = some (regs (tr k).1 (tr k).2.1) ∧
        RefTrack L D A r (tr k).1 (tr k).2.1 (tr k).2.2 := by
  obtain ⟨I, fn, h0⟩ := refTrack_main hP hmain hR
  obtain ⟨tr, -, htr', -⟩ := refTrace (stepRule_of hP honestA_closed hJ) hN h0
  exact ⟨tr, htr'⟩

/-! ## The functions' layout -/

/-- **Consecutive functions**: an entry within a function's instructions is that function's
entry. -/
theorem consecutive_entry : ∀ {s e : ℕ} {fns : List CompiledFunction}, consecutive s fns e = true →
    ∀ f ∈ fns, ∀ f' ∈ fns, f.entryPc ≤ f'.entryPc → f'.entryPc < f.entryPc + f.instructionCount →
      f'.entryPc = f.entryPc
  | _, _, [], _, _, hf, _, _, _, _ => absurd hf List.not_mem_nil
  | _, _, f0 :: gs, h, f, hf, f', hf', h1, h2 => by
    simp only [consecutive, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hg, hgs⟩ := h
    rcases List.mem_cons.mp hf with rfl | hfs <;> rcases List.mem_cons.mp hf' with rfl | hfs'
    · rfl
    · have := (consecutive_bounds hgs f' hfs').1
      omega
    · have := (consecutive_bounds hgs f hfs).1
      omega
    · exact consecutive_entry hgs f hfs f' hfs' h1 h2

/-- **A frame at a pc of the track is within the program**, and when that pc is a guest function's
entry, the frame's function is entered there. -/
theorem entry_of_atPc (hP : ProgAl guestProgram coreProgram A) (hL : AlLayout A)
    {Is : List Inst} {e : Ent} (hE : EntOk coreProgram Is e) {pc : ℕ} (hat : AtPc (entOf A) (alOf A) e pc) :
    pc < 2 ^ guestProgram.logSize - 1 ∧
      ∀ f' ∈ Data.functions, f'.entryPc = pc → entOf A e.I.t.name = pc := by
  obtain ⟨off, rfl, p, hal, -⟩ := hat
  obtain ⟨cf, hcf, hent, hlen⟩ := hL _ _ hE.find
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) (show alignAt _ _ _ _ off = some p from hal)
  have hoff : off < cf.instructionCount :=
    lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hins).1 hlen
  refine ⟨by rw [hent]; exact guest_pc_lt hcf hoff, fun f' hf' hpc ↦ ?_⟩
  rw [hent] at hpc
  have := consecutive_entry functions_consecutive cf hcf f' hf' (by omega) (by omega)
  rw [hent]
  omega

/-! ## The prologue's code -/

/-- **The prologue's instructions are `SET`s**, as `main`'s certificate's `MainOk` reads them. -/
theorem pro_set {Km : Mode.Cert} {E0 : Mode.Env} (hM : MainOk Km E0) {i : ℕ} (hi : i < proLen) :
    ∃ o k0 k1, Data.f0.instructionAt i = .set o k0 k1 :=
  let ⟨k0, k1, h, _⟩ := hM.slots i hi
  ⟨_, k0, k1, h⟩

/-! ## The executor's registers along the reference -/

theorem regs_eq (i j : ℕ) : regs i j = (⟨g ^ i, g ^ j⟩ : Registers K) := by
  simp only [regs, addressOfIndex]

/-- **The executor's registers along the reference**: in the prologue at pc `steps` of frame `0`,
past it those the run from `main`'s entry reaches in `steps - proLen` steps. -/
theorem posAt {r : Ref} (hR : RefH L (D r) r) {s : St} (hT : Trace guestProgram r.img s)
    (hpc : s.pc < 2 ^ 62) (hfp : s.fp < maxCells) :
    (s.steps < proLen → s.pc = s.steps ∧ s.fp = 0) ∧
      (proLen ≤ s.steps → run guestProgram r.img (s.steps - proLen) (regs proLen 0) =
        some ⟨g ^ s.pc, g ^ s.fp⟩) := by
  unfold Trace at hT
  refine ⟨fun hlt ↦ ?_, fun hge ↦ ?_⟩
  · rw [hR.pro s.steps hlt.le, regs_eq, Option.some.injEq] at hT
    have hp : proLen < 2 ^ 62 := by decide +kernel
    have hm : maxCells < 2 ^ 62 := by unfold maxCells; norm_num
    exact ⟨(gpow_inj (by omega) (by omega) (congrArg Registers.pc hT)).symm,
      (gpow_inj (by omega) (by norm_num) (by rw [pow_zero]; exact (congrArg Registers.fp hT).symm))⟩
  · have h := run_add guestProgram r.img proLen (s.steps - proLen) Registers.initial
    rw [show proLen + (s.steps - proLen) = s.steps by omega, hT, hR.pro proLen le_rfl,
      Option.bind_some] at h
    exact h.symm

/-- The reference run through a state's registers takes a step from them. -/
theorem onRef_step {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {s : St}
    (hon : OnRef prog img n s) :
    ∃ r1 k, n - s.steps = k + 1 ∧ (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog ∧
      step prog img ⟨g ^ s.pc, g ^ s.fp⟩ = some r1 ∧ run prog img k r1 = some (Registers.final prog) := by
  obtain ⟨hlt, hrun⟩ := hon
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  rw [hk] at hrun
  have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
    rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, hrun1⟩ := hrun
  exact ⟨r1, k, hk, hne, hstep, hrun1⟩

/-- Past the prologue, the run from `main`'s entry reaches the final registers. -/
theorem run_main {r : Ref} {s : St} (hon : OnRef guestProgram r.img r.n s)
    (hrun : run guestProgram r.img (s.steps - proLen) (regs proLen 0) = some ⟨g ^ s.pc, g ^ s.fp⟩) :
    run guestProgram r.img (s.steps - proLen + (r.n - s.steps)) (regs proLen 0) =
      some (Registers.final guestProgram) := by
  rw [run_add, hrun]
  exact hon.2

/-- **The tree track at a state on the reference**, past the prologue: a state of the track at the
state's own pc and frame. -/
theorem trackAt (hP : ProgAl guestProgram coreProgram A) (hmain : entOf A "main" = proLen)
    (hJ : JumpCellsAt L D A) (hL : AlLayout A) {r : Ref} (hR : RefH L (D r) r) (hr : r.Ok) {s : St}
    (hT : Trace guestProgram r.img s) (hs : Fine (refMem r.img) s) (hon : OnRef guestProgram r.img r.n s)
    (hge : proLen ≤ s.steps) (hpc : s.pc < 2 ^ guestProgram.logSize) :
    ∃ done e st, RefTrack L D A r s.pc s.fp (done, e :: st) := by
  have hpc62 : s.pc < 2 ^ 62 := by rw [guest_logSize] at hpc; omega
  have hpc63 : s.pc < 2 ^ 63 := by omega
  have hrun := (posAt hR hT hpc62 hs.fp).2 hge
  obtain ⟨tr, htr⟩ := traceRef hP hmain hR (hJ r hR hr) (run_main hon hrun)
  obtain ⟨h1, h2⟩ := htr (s.steps - proLen) (by have := hon.1; omega)
  rw [hrun, regs_eq, Option.some.injEq] at h1
  obtain ⟨e, st', hst, hE, hfp, hat⟩ := h2.top
  have hlt := (entry_of_atPc hP hL hE hat).1
  have hfpe := inst_fp_lt hR hr hE.mem
  have hpcE : s.pc = (tr (s.steps - proLen)).1 :=
    gpow_inj hpc63 (by rw [guest_logSize] at hlt; omega) (congrArg Registers.pc h1)
  have hfpE : s.fp = (tr (s.steps - proLen)).2.1 := by
    have := hs.fp
    rw [hfp] at hfpe
    unfold maxCells at this hfpe
    exact gpow_inj (by omega) (by omega) (congrArg Registers.fp h1)
  refine ⟨(tr (s.steps - proLen)).2.2.1, e, st', ?_⟩
  rw [hpcE, hfpE, ← hst]
  exact h2

end

/-! ## The cells the run touches -/

/-- **The cells touched lie within the reference's `2^κ`.** -/
def YU (r : Ref) (s : St) : Prop := s.mem.used ≤ 2 ^ r.κ

/-- **The hints keep the cells used within the reference's `2^κ`**, from each state the hint
tracks `Y` hold at. -/
def HintsUsed (R : Ref → Prop) (Y : Ref → St → Prop) : Prop :=
  ∀ r, R r → r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s s1, OnRun (XOf Y) r s →
    ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 → Moves (refMem r.img) s s1 →
      s1.mem.used ≤ 2 ^ r.κ

/-- **The executor's initial state touches the cells below `2^23`.** -/
theorem initY_used {r : Ref} (hR : 23 ≤ r.κ) {C : Ctx} {m : Mem}
    (hm : initMem r.adv r.input = .ok m) : YU r (initSt C r.adv m) := by
  show m.used ≤ _
  unfold initMem at hm
  obtain ⟨m0, h0, h1⟩ := bind_ok.mp hm
  rw [put_used h1, put_used h0]
  have h23 : 2 ^ 23 ≤ 2 ^ r.κ := Nat.pow_le_pow_right (by norm_num) hR
  have hmf : r.adv.mainFrame < 2 ^ 23 := (by decide +kernel : Data.adviceMainFrame < 2 ^ 23)
  norm_num at h23 hmf ⊢
  omega

/-- An instruction from a state on the reference touches only cells within the reference's `2^κ`. -/
theorem used_step {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s s1 s' : St} {op : Op}
    (hon : OnRef prog img n s) (hop : C.ops[s.pc]? = some op) (hm : Moves (refMem img) s s1)
    (e : runOp C s1 op = .ok s') (hu : s1.mem.used ≤ 2 ^ κ) : s'.mem.used ≤ 2 ^ κ := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  obtain ⟨r1, k, -, -, hstep, -⟩ := onRef_step hon
  have hex := hstep
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hex
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hex hdec
  have hex' : executeWith img.read ⟨g ^ s1.pc, g ^ s1.fp⟩ ins = some r1 := by
    rw [hm.pc, hm.fp]; exact hex
  exact runOp_used hκ hm.fine hdec e hex' hu

/-- **Each step keeps the cells used within the reference's `2^κ`**, given that the hints do. -/
theorem keepY_used {R : Ref → Prop} {Y : Ref → St → Prop} (hU : HintsUsed R Y) {r : Ref} (hR : R r)
    (hr : r.Ok) {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s op s1 s'}
    (hon : OnRun (XOf Y) r s) (hop : C.ops[s.pc]? = some op)
    (e1 : ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1) (hm : Moves (refMem r.img) s s1)
    (e : runOp C s1 op = .ok s') : YU r { s' with steps := s'.steps + 1 } :=
  show s'.mem.used ≤ _ from used_step hr.log hC hon.2.2 hop hm e (hU r hR hr C hC s s1 hon e1 hm)

end

end LeanVM.Guest.EndExec
