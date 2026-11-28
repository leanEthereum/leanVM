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
starts with nothing done (`refTrack_main`, `EndExecX`). Past it, the reference step from the state's registers
(`step_done`, `step_ref` with the instruction's `OpDone`) is the track's (`Bridge.stepD_of`), whose
entries done grow by those of the atoms the hints at the pc compile, which is what the hints move the
cursor by (`count_pairs`, `filter_flow`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Memory
open LeanVM.Guest.Core hiding Hint
open LeanVM.Guest.Bridge hiding St
open LeanVM.Prover.Exec

public section

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
theorem initY_cur (L : Lay) (D : Ref → RefD) (A : String → FnAl) {r : Ref} {C : Ctx} {m : Mem} :
    YCur L D A r (initSt C r.adv m) := by
  refine ⟨fun _ S ↦ Std.HashMap.getD_empty, fun h ↦ ?_⟩
  exact absurd h (by show ¬ proLen ≤ 0; have := proLen_pos; omega)

/-- **Each step keeps the witness streams' track.** -/
theorem keepY_cur {L : Lay} {D : Ref → RefD} {A : String → FnAl} {Km : Mode.Cert} {E0 : Mode.Env}
    (hMain : MainOk Km E0) (hP : ProgAl guestProgram coreProgram A)
    (hmain : entOf A "main" = proLen) (hJ : JumpCellsAt L D A) (hL : AlLayout A) (hAd : AdvAl A)
    {Y : Ref → St → Prop} (hY : ∀ r s, Y r s → YCur L D A r s) {r : Ref} (hR : RefH L (D r) r)
    (hr : r.Ok) {C : Ctx} (hC : Ctx.of guestProgram r.adv = .ok C) {s : St} {op : Op} {s1 s' : St}
    (hon : OnRun (XOf Y) r s) (hop : C.ops[s.pc]? = some op)
    (e1 : ((C.hints[s.pc]?).getD []).foldlM (runHint C) s = .ok s1) (hm : Moves (refMem r.img) s s1)
    (hmo : OpModed (refMem r.img) s1 op) (e : runOp C s1 op = .ok s') :
    YCur L D A r { s' with steps := s'.steps + 1 } := by
  have hκ : r.κ ≤ 28 := hr.log
  have hYs := hY r s hon.1.2
  obtain ⟨r1, k, hk, hstep, hrun1, hd⟩ :=
    step_done hκ hC hm.fine (Mode.onRef_moves hm hon.2.2) (by rw [hm.pc]; exact hop) hmo e
  have hst : s'.steps = s.steps := hd.steps.trans hm.steps
  rw [hm.steps] at hk
  rw [hm.pc, hm.fp] at hstep
  have hpcS : s.pc < C.ops.size := (Array.getElem?_eq_some_iff.mp hop).1
  have hsize := (ctx_of_spec hC).1
  have hpc62 : s.pc < 2 ^ 62 := by rw [hsize, guest_logSize] at hpcS; omega
  have hpos := posAt hR hon.1.1 hpc62 hon.2.1.fp
  have hcur : ∀ S, s'.cursor.getD S 0 =
      s.cursor.getD S 0 + (((C.hints[s.pc]?).getD []).filter (popsOn S)).length := fun S ↦ by
    rw [runOp_cursor e]; exact hints_cursor S _ s s1 e1
  refine ⟨fun hlt S ↦ ?_, fun hge hn ↦ ?_⟩
  · have hs : s.steps < proLen := by dsimp only at hlt; omega
    have hpc : s.pc < proLen := by rw [(hpos.1 hs).1]; exact hs
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
  · obtain ⟨hpc, hfp⟩ := hpos.1 hpro
    obtain ⟨o0, k0, k1, hins0⟩ := pro_set hMain (show s.pc < proLen by omega)
    have hset := op_pro hC (show s.pc < proLen by omega) hins0
    rw [hop] at hset
    cases hset
    obtain ⟨hpc', hfp', -⟩ := Mode.runOp_next (⟨hm.fine.agree.wf, hm.fine.dl⟩ : s1.Good) hm.fine.fp
      (by rw [hm.pc]; exact hpcS) e (fun _ _ _ ↦ nofun) (fun _ _ _ _ _ ↦ nofun)
    obtain ⟨I, fn, htr⟩ := refTrack_main hP hmain hR
    have h2 : s'.pc = proLen := by rw [hpc', hm.pc]; omega
    refine ⟨[], [Ent.enter coreProgram I fn], ?_, fun S ↦ ?_⟩
    · rw [h2, hfp', hm.fp, hfp]; exact htr
    · rw [hcur, hYs.1 hpro S, hints_pro hC rfl (by omega)]
      rfl
  obtain ⟨done, st, htr, hc⟩ := hYs.2 (by omega) hon.2.2.1
  obtain ⟨e0, st', rfl, hE, -, hat⟩ := htr.top
  obtain ⟨off, hpc, p, hal', -, -, -⟩ := hat
  obtain ⟨ins, -, -, -, -, hins, -⟩ := alignAt_step (hP.ok _ _ hE.find) hal'
  obtain ⟨as, hpair, pc', fp', ts', hr', -, hts', hdone⟩ :=
    stepD_of hP honestA_closed htr (hJ r hR hr _ _ _ _ _ htr) (by rw [regs_eq]; exact hstep) hne1
  rw [← hd.regs] at hr'
  obtain ⟨e2, st2, -, hE2, hfp2, hat2⟩ := hts'.top
  have hpc2 := (entry_of_atPc hP hL hE2 hat2).1
  have hfpl := inst_fp_lt hR hr hE2.mem
  have hspc := hd.pc
  have hsfp := hd.fine.fp
  rw [hsize, guest_logSize] at hspc
  rw [guest_logSize] at hpc2
  rw [hfp2] at hfpl
  unfold maxCells at hfpl hsfp
  rw [regs_eq] at hr'
  have e_pc : s'.pc = pc' := gpow_inj (by omega) (by omega) (congrArg Registers.pc hr')
  have e_fp : s'.fp = fp' := gpow_inj (by omega) (by omega) (congrArg Registers.fp hr')
  refine ⟨ts'.1, ts'.2, by rw [e_pc, e_fp]; exact hts', fun S ↦ ?_⟩
  have hpcE : s.pc = (A e0.I.t.name).X.entry + off := hpc
  have hh : (C.hints[s.pc]?).getD [] = Mode.hintsAt Data.adviceHints s.pc :=
    Mode.ctx_hints hC Mode.adviceHints_incr (by rw [← hsize]; exact hpcS)
  rw [hpcE, hAd _ _ hE.find off ins hins, ← hpcE, ← hh] at hpair
  rw [hcur, hc S, hdone, List.filter_append, List.length_append, flatMap_flow, count_pairs _ _ S hpair,
    filter_flow]

end

end LeanVM.Guest.EndExec
