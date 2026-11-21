/-
  LeanVM.Guest.EndExecYKeep

  The witness streams' track holds initially and each step keeps it.
-/

module

public import LeanVM.Guest.EndExecY

/-!
# The witness streams' track along the run

`initY_cur`: the executor starts with every cursor at `0`. `keepY_cur`: a step keeps `YCur`. In the
prologue there are no hints; at its last step the run enters `main` at frame `0`, where the track
starts with nothing done (`refTrack_main`). Past it, the reference step from the state's registers
(`step_done`, `step_ref` with the instruction's `OpDone`) is the track's (`Bridge.stepD_of`), whose
entries done grow by those of the atoms the hints at the pc compile, which is what the hints move the
cursor by (`count_pairs`, `filter_flow`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec
open LeanVM.Guest.End (mainEntry)

public section

/-- **The track at `main`'s entry**: `main`'s frame at its body, at frame `0`, nothing done. -/
theorem refTrack_main {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) {r : Ref} (hr : r.Ok) : ∃ st, RefTrack A r mainEntry 0 ([], st) := by
  obtain ⟨rd, hH, -⟩ := hr.honest
  obtain ⟨I, hI, hIt, hfp, -⟩ := root_inst (P := coreProgram) (fs := B2C.fs) (H := B2C.H) (hdr := r.hdr)
    (T := r.T)
  have hv := hH.valid
  rw [← hIt] at hv
  obtain ⟨fn, hf⟩ : ∃ fn, coreProgram.find? I.t.name = some fn := by
    rcases hIt' : I.t with ⟨f, σ, bufs, kids⟩ | ⟨f, σ⟩
    · rw [hIt'] at hv
      obtain ⟨fn, hf, -⟩ := hv
      exact ⟨fn, hf⟩
    · rw [hIt'] at hv; exact hv.elim
  have htr := trackOk_init (rd := r.rd0) hI hf hv
  rw [hIt] at htr
  have hname : I.t.name = "main" := by rw [hIt]; exact hr.name
  have hal0 : alOf A "main" 0 = some fn.body := by
    rw [hname] at hf
    change alignAt (A "main").X (A "main").body (A "main").code (A "main").d 0 = some fn.body
    rw [alignAt_zero (hP.ok _ _ hf), hP.body _ _ hf]
  have h0 := refOk_init (M := memOf r.img) (ent := entOf A) (al := alOf A) htr hfp (by rw [hname]; exact hal0)
  rw [hname, hmain] at h0
  exact ⟨_, h0⟩

/-- **An instruction along the reference, with what it leaves**: from a state on the reference run,
moded, the executor's instruction goes to the reference step's registers, a state fine against the
reference with its pc in the program. -/
theorem step_done {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s s' : St} {op : Op} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) (hop : C.ops[s.pc]? = some op) (hmo : OpModed (refMem img) s op)
    (e : runOp C s op = .ok s') :
    ∃ r1 k, n - s.steps = k + 1 ∧ step prog img ⟨Parameters.g ^ s.pc, Parameters.g ^ s.fp⟩ = some r1 ∧
      run prog img k r1 = some (Registers.final prog) ∧ OpDone C (refMem img) s s' r1 := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  have hdec := hdecC s.pc hpc2 hpc
  rw [hop'] at hdec
  have hsm := ctx_small hC s.pc hpc
  rw [hop'] at hsm
  obtain ⟨r1, k, hk, -, hstep, hrun1⟩ := onRef_step hon
  have hex := hstep
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hex
  obtain ⟨s2, e2, d2⟩ := runOp_complete hs (refRd_img hκ img) hdec hsm hpc hsz (nextOk_of_run hsize hrun1) hex hmo
  rw [e] at e2
  cases e2
  exact ⟨r1, k, hk, hstep, hrun1, d2⟩

/-- **The executor starts with every cursor at `0`.** -/
theorem initY_cur (A : String → FnAl) : InitY (YCur A) := by
  intro r hr C m hC hm
  refine ⟨fun _ S ↦ Std.HashMap.getD_empty, fun h ↦ ?_⟩
  exact absurd h (by show ¬ proLen ≤ 0; rw [proLen_eq]; norm_num)

/-- **Each step keeps the witness streams' track.** -/
theorem keepY_cur {A : String → FnAl} (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = mainEntry) (hJ : JumpCellsAt A) (hL : AlLayout A) (hAd : AdvAl A)
    {Y : Ref → St → Prop} (hD : DerefPow Y) (hY : ∀ r s, Y r s → YCur A r s) :
    ∀ r, r.Ok → ∀ C, Ctx.of guestProgram r.adv = .ok C → ∀ s op s1 s', OnRun (XOf Y) r s →
      C.ops[s.pc]? = some op → ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1 →
      Moves (refMem r.img) s s1 → runOp C s1 op = .ok s' → YCur A r { s' with steps := s'.steps + 1 } := by
  intro r hr C hC s op s1 s' hon hop e1 hm e
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  have hYs := hY r s hon.1.2.2
  have hmo : OpModed (refMem r.img) s1 op :=
    Mode.opModed_of hm.fine.agree (reads_of_runOp e) ((refOk_X hP hmain hJ hD hr hC hon hop).congr hm.fp)
  obtain ⟨r1, k, hk, hstep, hrun1, hd⟩ :=
    step_done hκ hC hm.fine (Mode.onRef_moves hm hon.2.2) (by rw [hm.pc]; exact hop) hmo e
  have hst : s'.steps = s.steps := hd.steps.trans hm.steps
  rw [hm.steps] at hk
  rw [hm.pc, hm.fp] at hstep
  have hpcS : s.pc < C.ops.size := (Array.getElem?_eq_some_iff.mp hop).1
  have hsize := (ctx_of_spec hC).1
  have hcur : ∀ S, s'.cursor.getD S 0 =
      s.cursor.getD S 0 + (((C.hints[s.pc]?).getD []).filter (popsOn S)).length := fun S ↦ by
    rw [runOp_cursor e]; exact hints_cursor S _ s s1 e1
  refine ⟨fun hlt S ↦ ?_, fun hge hn ↦ ?_⟩
  · have hs : s.steps < proLen := by dsimp only at hlt; omega
    have hpc : s.pc < proLen := by
      rcases hon.1.1 with ⟨-, hpc, -⟩ | ⟨h, -⟩
      · omega
      · omega
    show s'.cursor.getD S 0 = 0
    rw [hcur, hYs.1 hs S, hints_pro hC rfl hpc]
    rfl
  dsimp only at hge hn ⊢
  have hne1 : r1 ≠ Registers.final guestProgram := by
    rintro rfl
    cases k with
    | zero => omega
    | succ k' =>
      rw [run_succ_of_eq rfl] at hrun1
      cases hrun1
  by_cases hpro : s.steps < proLen
  · obtain ⟨hpc, hfp⟩ : s.pc = s.steps ∧ s.fp = 0 := by
      rcases hon.1.1 with ⟨-, hpc, hfp⟩ | ⟨h, -⟩
      · exact ⟨hpc, hfp⟩
      · omega
    obtain ⟨k0, t, hset, -⟩ := op_pro hC (show s.pc < proLen by omega)
    rw [hop] at hset
    cases hset
    obtain ⟨hpc', hfp', -⟩ := Mode.runOp_next (⟨hm.fine.agree.wf, hm.fine.dl⟩ : s1.Good) hm.fine.fp
      (by rw [hm.pc]; exact hpcS) e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    obtain ⟨st, htr⟩ := refTrack_main hP hmain hr
    have h2 : s'.pc = mainEntry := by show s'.pc = proLen; rw [hpc', hm.pc]; omega
    refine ⟨[], st, ?_, fun S _ ↦ ?_⟩
    · rw [h2, hfp', hm.fp, hfp]; exact htr
    · rw [hcur, hYs.1 hpro S, hints_pro hC rfl (by omega)]
      rfl
  obtain ⟨done, st, htr, hc⟩ := hYs.2 (by omega) hon.2.2.1
  obtain ⟨e0, st', rfl, hE, -, hat⟩ := htr.top
  obtain ⟨off, hpc, p, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal'
  obtain ⟨as, hpair, pc', fp', ts', hr', -, hts', hdone⟩ :=
    stepD_of hP honest_closed htr (hJ r hr _ _ _ _ _ htr) hstep hne1
  rw [← hd.regs] at hr'
  obtain ⟨e2, st2, -, hE2, hfp2, hat2⟩ := hts'.top
  have hpc2 := (entry_of_atPc hP hL hE2 hat2).1
  have hfpl := inst_fp_lt hr hE2.mem
  have hspc := hd.pc
  have hsfp := hd.fine.fp
  rw [hsize, guest_logSize] at hspc
  rw [guest_logSize] at hpc2
  rw [hfp2] at hfpl
  unfold maxCells at hfpl hsfp
  have e_pc : s'.pc = pc' := gpow_inj (by omega) (by omega) (congrArg Registers.pc hr')
  have e_fp : s'.fp = fp' := gpow_inj (by omega) (by omega) (congrArg Registers.fp hr')
  refine ⟨ts'.1, ts'.2, by rw [e_pc, e_fp]; exact hts', fun S hS ↦ ?_⟩
  have hpcE : s.pc = (A e0.I.t.name).X.entry + off := hpc
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (by rw [← hsize]; exact hpcS)
  rw [hpcE, hAd _ _ hE.find off ins hins, ← hpcE, ← hh] at hpair
  rw [hcur, hc S hS, hdone, List.filter_append, List.length_append, flatMap_flow, count_pairs _ _ S hpair,
    filter_flow hS (hints_adv hC rfl s.pc)]

end

end LeanVM.Guest.EndExec
