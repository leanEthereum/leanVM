/-
  LeanVM.Guest.EndExecX

  `ExecGaps` with the tracks' invariant `X` concrete: each state at its step of the reference run,
  the cells it touched within the reference's memory, and the hint tracks' invariant.
-/

module

public import LeanVM.Guest.EndExecXOp
public import LeanVM.Guest.EndExecXTrace
public import LeanVM.Guest.EndExecParts
import all LeanVM.Guest.Data.Functions
import all Statement.Data.AdviceHints

/-!
# The tracks' invariant

`XOf Y r s`: the state `s` is at its step of `r`'s reference run (`PosAt`: in the prologue at pc
`steps` of `__jump_tables` in frame `0`, past it at the registers the run from `main`'s entry
reaches in `steps - proLen` steps), the cells it touched are within the reference's `2^κ`, and the
hint tracks' invariant `Y` (the witness streams' cursor, the bump pointer) holds.

Discharged from it: `init`'s part (`init_X`), `used`, `keepOp` (`keep_X`: the executor's step goes
to the reference step's registers, `runOp_complete` on its reads, `reads_of_runOp`, and the
reference's part of its modedness; it touches only cells the reference reads, `runOp_used`), the
taken `JUMP`'s part of `ref` (`ptrPow_X`: the next state's frame is a frame of the tree track,
an honest instance, below `maxCells`), and a frame of the track at a function's entry is an
instance of it (`trackAt_X`: the track's state at a state's own pc and frame).

What is left, besides the fields left to other tracks: the program's
alignments (`ProgAl`, `AlLayout`), the jumps' cells on the track (`JumpCellsAt`), no certificate at
pc `0`, a `DEREF`'s address (`DerefPow`, what the reference step reads: `derefPow_all`), the
hints' cells within the reference
(`HintsUsed`), and `Y` initially and kept (`InitY`, `KeepY`; trivial for `Y` true).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode
open LeanVM.Guest.Bridge (FnAl ProgAl JumpCells entOf alOf)
open LeanVM.Guest.End (mainEntry)
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The invariant -/

/-- **A state at its step of the reference run**: in the prologue, at pc `steps` of
`__jump_tables` in frame `0`; past it, at the registers the run from `main`'s entry reaches in
`steps - proLen` steps. -/
def PosAt (r : Ref) (s : St) : Prop :=
  (s.steps < proLen ∧ s.pc = s.steps ∧ s.fp = 0) ∨
    (proLen ≤ s.steps ∧
      run guestProgram r.img (s.steps - proLen) (Bridge.regs mainEntry 0) =
        some ⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩)

/-- **The tracks' invariant**: the state at its step of the reference run, the cells it touched
within the reference's `2^κ`, and the hint tracks' invariant `Y`. -/
def XOf (Y : Ref → St → Prop) (r : Ref) (s : St) : Prop :=
  PosAt r s ∧ s.mem.used ≤ 2 ^ r.κ ∧ Y r s

/-! ## What is left open -/

/-- **What each frame's jumps read**, on every node's reference run. -/
def JumpCellsAt (A : String → FnAl) : Prop :=
  ∀ r : Ref, r.Ok → ∀ pc fp done e st, RefTrack A r pc fp (done, e :: st) → JumpCells r.img A e pc

/-- **A `DEREF`'s pointer times `g^o` is a power below `maxCells`** on the reference, at each state
of the tracks. -/
def DerefPow (Y : Ref → St → Prop) : Prop :=
  ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s a o c mode, OnRun (XOf Y) r s →
    C.ops[s.pc]? = some (.deref a o c mode) →
      ∃ b < maxCells, (refMem r.img (s.fp + a)).limb 0 * Parameters.g ^ o = Parameters.g ^ b

/-- **The hints keep the cells used within the reference's `2^κ`**, from each state of the tracks. -/
def HintsUsed (Y : Ref → St → Prop) : Prop :=
  ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s s1, OnRun (XOf Y) r s →
    ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 → Moves (refMem r.img) s s1 →
      s1.mem.used ≤ 2 ^ r.κ

/-- **Each step keeps the hint tracks' invariant.** -/
def KeepY (Y : Ref → St → Prop) : Prop :=
  ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s1 s', OnRun (XOf Y) r s →
    C.ops[s.pc]? = some op → ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 →
    Moves (refMem r.img) s s1 → runOp C s1 op = .ok s' → Y r { s' with steps := s'.steps + 1 }

/-- **The hint tracks' invariant at the executor's initial state.** -/
def InitY (Y : Ref → St → Prop) : Prop :=
  ∀ r, r.Ok → ∀ C m, Ctx.of guestProgram r.adv = .ok C → initMem r.adv r.input = .ok m →
    Y r (initSt C r.adv m)

/-! ## The reference step -/

/-- The reference run through a state's registers takes a step from them. -/
theorem onRef_step {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {s : St}
    (hon : OnRef prog img n s) :
    ∃ r1 k, n - s.steps = k + 1 ∧ (⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ : Registers K) ≠ Registers.final prog ∧
      step prog img ⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ = some r1 ∧
        run prog img k r1 = some (Registers.final prog) := by
  obtain ⟨hlt, hrun⟩ := hon
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  rw [hk] at hrun
  have hne : (⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
    rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, hrun1⟩ := hrun
  exact ⟨r1, k, hk, hne, hstep, hrun1⟩

/-- A taken `JUMP`'s next frame is its frame cell's word. -/
theorem jump_fp {prog : LeanIsaProgram} {adv : Advice} {κ : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s : St} (hs : Fine (refMem img) s) {c d f : ℕ}
    (hop : C.ops[s.pc]? = some (.jump c d f)) {r1 : Registers K}
    (hstep : step prog img ⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ = some r1) (hnz : refMem img (s.fp + c) ≠ 0) :
    r1.fp = (refMem img (s.fp + f)).limb 0 := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hsm := ctx_small hC s.pc hpc
  rw [hop'] at hsm
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  generalize prog.instructions ⟨s.pc, hpc2⟩ = ins at hstep hdec
  have hrd := refRd_img hκ img
  cases ins <;> simp only [OpOf] at hdec
  obtain ⟨rfl, rfl, rfl⟩ := hdec
  simp only [executeWith, Option.bind_eq_bind, Option.bind_eq_some_iff] at hstep
  obtain ⟨vc, hc, vd, -, vf, hf, -, -, e⟩ := hstep
  have hcM := (hrd.at hs.fp hsm.1 hc).2
  have hfM := (hrd.at hs.fp hsm.2.2 hf).2
  rw [hcM] at hnz
  rw [ite_eq_right_of_eq_false _ _ (eq_false hnz)] at e
  obtain rfl : (⟨vd.limb 0, vf.limb 0⟩ : Registers K) = r1 := Option.some.inj e
  rw [hfM]

/-- Past the prologue, the run from `main`'s entry reaches the final registers. -/
theorem run_main {Y : Ref → St → Prop} {r : Ref} {s : St} (hon : OnRun (XOf Y) r s)
    (hrun : run guestProgram r.img (s.steps - proLen) (Bridge.regs mainEntry 0) =
      some ⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩) :
    run guestProgram r.img (s.steps - proLen + (r.n - s.steps)) (Bridge.regs mainEntry 0) =
      some (Registers.final guestProgram) := by
  rw [run_add, hrun, Option.bind_eq_bind, Option.bind_some]
  exact hon.2.2.2

/-- **An instruction along the reference**: moded, from a state on the reference run, it goes to
the reference step's registers, and keeps the cells used within the reference's image. -/
theorem step_ref {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s s' : St} {op : Op} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) (hop : C.ops[s.pc]? = some op) (hmo : OpModed (refMem img) s op)
    (e : runOp C s op = .ok s') (hu : s.mem.used ≤ 2 ^ κ) :
    s'.steps = s.steps ∧ (⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ : Registers K) ≠ Registers.final prog ∧
      step prog img ⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ = some ⟨Parameters.g ^ s'.pc, Parameters.g ^ s'.fp⟩ ∧
      s'.mem.used ≤ 2 ^ κ := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  have hsm := ctx_small hC s.pc hpc
  rw [hop'] at hsm
  obtain ⟨r1, k, -, hne, hstep, hrun1⟩ := onRef_step hon
  have hex := hstep
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hex
  obtain ⟨s2, e2, d2⟩ := runOp_complete hs (refRd_img hκ img) hdec hsm hpc hsz (nextOk_of_run hsize hrun1) hex hmo
  rw [e] at e2
  cases e2
  exact ⟨d2.steps, hne, by rw [hstep, d2.regs], runOp_used hκ hs hdec e hex hu⟩

/-! ## The pointers -/

/-- **A taken `JUMP`'s frame is a power**, at each state of the tracks: the next frame of the tree
track, an honest instance's. -/
theorem ptrPow_X {Y : Ref → St → Prop} {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) (hJ : JumpCellsAt A) {r : Ref} (hr : r.Ok) {C : Ctx}
    (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {op : Op} (hon : OnRun (XOf Y) r s)
    (hop : C.ops[s.pc]? = some op) : PtrPow (refMem r.img) s op := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  cases op with
  | jump c d f =>
    intro hnz
    rcases hon.1.1 with ⟨hlt, hpc, -⟩ | ⟨hge, hrun⟩
    · obtain ⟨k0, t, hset, -⟩ := op_pro hC (show s.pc < proLen by omega)
      rw [hop] at hset
      cases hset
    obtain ⟨r1, k, hk, hne, hstep, hrun1⟩ := onRef_step hon.2.2
    have hfp1 := jump_fp hκ hC hon.2.1 hop hstep hnz
    cases k with
    | zero =>
      have h1 : r1.fp = fpFinal := congrArg Registers.fp (Option.some.inj hrun1)
      exact ⟨0, by norm_num, by rw [← hfp1, h1, pow_zero]⟩
    | succ k =>
      obtain ⟨tr, htr⟩ := traceRef hP hmain hr (hJ r hr) (run_main hon hrun)
      obtain ⟨h1, h2⟩ := htr (s.steps - proLen + 1) (by omega)
      rw [Bridge.run_of_step hrun hne hstep, Option.some.injEq] at h1
      obtain ⟨e, st', hst, hE, hfp, -⟩ := h2.top
      have := inst_fp_lt hr hE.mem
      refine ⟨(tr (s.steps - proLen + 1)).2.1, by unfold maxCells at this; omega, ?_⟩
      rw [← hfp1, h1]
  | _ => trivial

/-- **`RefOk` at each state of the tracks.** -/
theorem refOk_X {Y : Ref → St → Prop} {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) (hJ : JumpCellsAt A) (hD : DerefPow Y) {r : Ref} (hr : r.Ok) {C : Ctx}
    (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {op : Op} (hon : OnRun (XOf Y) r s)
    (hop : C.ops[s.pc]? = some op) : RefOk (refMem r.img) s op := by
  cases op with
  | deref a o c mode => exact hD r hr C hC s a o c mode hon hop
  | _ =>
    exact refOk_of_pow (logMemorySize_le_28 (e := r.exec) hr.size) hC hon.2.1 hon.2.2 hop
      (ptrPow_X hP hmain hJ hr hC hon hop)

/-! ## The step -/

/-- **Each step keeps the tracks' invariant**: the executor's instruction goes to the reference
step's registers and touches only cells it reads. -/
theorem keep_X {Y : Ref → St → Prop} {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) (hJ : JumpCellsAt A) (hD : DerefPow Y) (hU : HintsUsed Y)
    (hY : KeepY Y) {r : Ref} (hr : r.Ok) {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {op : Op}
    {s1 s' : St} (hon : OnRun (XOf Y) r s) (hop : C.ops[s.pc]? = some op)
    (e1 : ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1) (hm : Moves (refMem r.img) s s1)
    (e : runOp C s1 op = .ok s') : XOf Y r { s' with steps := s'.steps + 1 } := by
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hmo : OpModed (refMem r.img) s1 op :=
    opModed_of hm.fine.agree (reads_of_runOp e) ((refOk_X hP hmain hJ hD hr hC hon hop).congr hm.fp)
  obtain ⟨hst1, hne, hstep, hu⟩ := step_ref hκ hC hm.fine (onRef_moves hm hon.2.2) (by rw [hm.pc]; exact hop) hmo e
    (hU r hr C hC s s1 hon e1 hm)
  refine ⟨?_, hu, hY r hr C hC s op s1 s' hon hop e1 hm e⟩
  have hst : s'.steps = s.steps := hst1.trans hm.steps
  have hpc1 : s1.pc < C.ops.size := (Array.getElem?_eq_some_iff.mp (show C.ops[s1.pc]? = some op by
    rw [hm.pc]; exact hop)).1
  rcases hon.1.1 with ⟨hlt, hpc, hfp⟩ | ⟨hge, hrun⟩
  · obtain ⟨k0, t, hset, -⟩ := op_pro hC (show s.pc < proLen by omega)
    rw [hop] at hset
    cases hset
    obtain ⟨hpc', hfp', -⟩ := runOp_next (⟨hm.fine.agree.wf, hm.fine.dl⟩ : s1.Good) hm.fine.fp hpc1 e
      (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    rw [hm.pc] at hpc'
    rw [hm.fp] at hfp'
    by_cases hlast : s.steps + 1 < proLen
    · exact Or.inl ⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega⟩
    · refine Or.inr ⟨by dsimp only; omega, ?_⟩
      have h1 : s'.steps + 1 - proLen = 0 := by omega
      have h2 : s'.pc = mainEntry := by show s'.pc = proLen; omega
      dsimp only
      rw [h1, run_zero, h2, hfp', hfp]
  · refine Or.inr ⟨by dsimp only; omega, ?_⟩
    dsimp only
    rw [show s'.steps + 1 - proLen = s.steps - proLen + 1 by omega]
    rw [hm.pc, hm.fp] at hstep hne
    exact Bridge.run_of_step hrun hne hstep

/-! ## The rest -/

/-- **The tracks' invariant at the executor's initial state.** -/
theorem init_X {Y : Ref → St → Prop} (hY : InitY Y) {r : Ref} (hr : r.Ok) {C : Ctx} {m : Mem}
    (hC : Ctx.of guestProgram r.adv = .ok C) (hm : initMem r.adv r.input = .ok m) : XOf Y r (initSt C r.adv m) := by
  refine ⟨Or.inl ⟨proLen_pos, rfl, rfl⟩, ?_, hY r hr C m hC hm⟩
  show m.used ≤ _
  unfold initMem at hm
  obtain ⟨m0, h0, h1⟩ := bind_ok.mp hm
  rw [put_used h1, put_used h0]
  have h23 : 2 ^ 23 ≤ 2 ^ r.κ := Nat.pow_le_pow_right (by norm_num) (Memory.twentyThree_le_logMem _)
  have hmf : r.adv.mainFrame < 2 ^ 23 := (by decide : Data.adviceMainFrame < 2 ^ 23)
  norm_num at h23 hmf ⊢
  omega

/-- **The tree track at a state of the tracks**, past the prologue: a state of the track at the
state's own pc and frame. -/
theorem trackAt_X {Y : Ref → St → Prop} {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) (hJ : JumpCellsAt A) (hL : AlLayout A) {r : Ref} (hr : r.Ok) {s : St}
    (hon : OnRun (XOf Y) r s) (hge : proLen ≤ s.steps) (hpc : s.pc < 2 ^ guestProgram.logSize) :
    ∃ done e st, RefTrack A r s.pc s.fp (done, e :: st) := by
  rcases hon.1.1 with ⟨hlt, -, -⟩ | ⟨-, hrun⟩
  · omega
  obtain ⟨tr, htr⟩ := traceRef hP hmain hr (hJ r hr) (run_main hon hrun)
  obtain ⟨h1, h2⟩ := htr (s.steps - proLen) (by have := hon.2.2.1; omega)
  rw [hrun, Option.some.injEq] at h1
  obtain ⟨e, st', hst, hE, hfp, hat⟩ := h2.top
  have hlt := (entry_of_atPc hP hL hE hat).1
  have hfpe := inst_fp_lt hr hE.mem
  have hpcE : s.pc = (tr (s.steps - proLen)).1 :=
    gpow_inj (by rw [guest_logSize] at hpc; omega) (by rw [guest_logSize] at hlt; omega)
      (congrArg Registers.pc h1)
  have hfpE : s.fp = (tr (s.steps - proLen)).2.1 := by
    have := hon.2.1.fp
    unfold maxCells at this hfpe
    exact gpow_inj (by omega) (by omega) (congrArg Registers.fp h1)
  refine ⟨(tr (s.steps - proLen)).2.2.1, e, st', ?_⟩
  rw [hpcE, hfpE, ← hst]
  exact h2

/-! ## The assembly -/

end

end LeanVM.Guest.EndExec
