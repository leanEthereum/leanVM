/-
  Rv64mc.Final.Transfer

  From total correctness at Lprog to a halting run of the statement's machine: the total
  counterpart of `Bridge.lean` and machine-checked's `SafeN.of_lift`, in the other direction.

  `halts_of_total`: a state of the lifted program simulated by a machine state (machine-checked's
  `Sim`), total at Lprog under `stmtCtx` for the obligation `WinOk` and a `Q` that holds only at
  a state inside the program whose `a0` satisfies `H`, has the machine take `n` steps of the
  statement's `step` to the halting `ECALL` with `a0` satisfying `H` (`Halts`). By induction on
  the judgement, reusing machine-checked's simulation step by step (`Sim.split`, `back_instr`,
  `trap_instr`), which is about SP1's context `sp1Ctx`:

  * `stmtCtx` and `sp1Ctx` differ only at an `Lext`, and a total state is never at an `Lext`
    it steps from, since `stmtCtx` traps there (`step_stmt_iff`). So each Lprog step of the
    judgement is one of `sp1Ctx`, and machine-checked's lemmas apply.
  * A total state at an instruction neither traps nor goes `wrong`, so SP1's machine steps
    (`trap_instr`), and to a state simulated by a successor (`back_instr`); not to a returned
    program, where `Q` does not hold.
  * That machine step is one of the statement's `step` (`step_of_stepSp1`): the instruction is
    not an `ECALL`, and its access is in a window, by `WinOk` at the Lprog state
    (`winOk_of_opWin`).
  * An accepting state inside the program is at an `Lext`, so the machine is at an `ECALL`
    (`ecall_of_sim`), with `t0 = 0` by `stmtCtx`'s acceptance: `Halts` after `0` steps.

  `halts_of_lift` starts it at a function's entry, as `SafeN.of_lift` does.

  ## Main results

  * `step_of_stepSp1`, `step_stmt_iff`, `ecall_of_sim`
  * `halts_of_total`, `halts_of_lift`
-/

import Rv64mc.Core.HoldsT
import Rv64mc.Bridge
import MachineChecked.RiscV.Lift.Transfer

namespace Rv64mc

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Lift MachineChecked.RiscV.Sym Lprog Lprog.RiscV
  Lprog.RiscV.Machine
open Lprog.Ascent (Outcome)

/-! ## The statement's step from SP1's -/

/-- The statement's window check of an instruction's memory access. -/
def winOk (t : MachineState) (i : Instr) : Bool :=
  match memAccess t i with
  | none => true
  | some (a, w, _) => inWindow a w

/-- **A step of SP1's machine is one of the statement's**, at an instruction other than `ECALL` whose access is in a
    window. -/
theorem step_of_stepSp1 {t t' : MachineState} {i : Instr} (h : stepSp1 t = some t') (hc : t.code t.pc = some i)
    (he : i ≠ .ECALL) (hw : winOk t i = true) : step t = some t' := by
  unfold stepSp1 at h
  unfold step
  rw [hc] at h ⊢
  cases i <;> simp_all [memOk, winOk, memOkSp1, memAccess, Instr.isMemAccess]

/-- An operation's window obligation is its instruction's window check, on an agreeing machine. -/
theorem winOk_of_opWin {regs : Reg → Word} {m t : MachineState} (hag : Agree (ofParts regs m) t) {i : Instr}
    (hop : opnOk i = true) (hw : opWin (opOf i) regs) : winOk t i = true := by
  cases i <;> simp_all [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, opOf, opWin, winOk, memAccess, addr,
    se12, Expr.eval, BinOp.eval, rv_eval_of_agree hag, Width.bytes]

/-- An instruction that is not an operation accesses no memory. -/
theorem winOk_of_not_opnOk {t : MachineState} {i : Instr} (hop : opnOk i = false) : winOk t i = true := by
  cases i <;> simp_all [opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS, winOk, memAccess]

/-- `n` steps from a successor are `n + 1` from its predecessor. -/
theorem Halts.of_step {s t : MachineState} {n : Nat} {v : Word} (h : step s = some t) (ht : Halts t n v) :
    Halts s (n + 1) v := by
  obtain ⟨u, hu, h1, h2, h3⟩ := ht
  exact ⟨u, by simp only [steps, h, Option.bind_some, hu], h1, h2, h3⟩

/-! ## `stmtCtx` and `sp1Ctx` -/

theorem fetch_some {p : Lprog (Op Reg) Reg} {fr : Frame} {rest : List Frame} {regs : Reg → Word}
    {m : MachineState} {i : LinstrR (Op Reg) Reg} (h : rvIsa.fetch p ⟨fr :: rest, regs, m⟩ = some i) :
    ∃ fd, p[fr.fn]? = some fd ∧ fd.body[fr.pc]? = some i := by
  simpa [Isa.fetch, Option.bind_eq_some_iff] using h

/-- **Away from an `Lext`, the two contexts step alike.** -/
theorem step_stmt_iff {p : Lprog (Op Reg) Reg} {s : State rvIsa} (h : ∀ k, rvIsa.fetch p s ≠ some (.Lext k))
    (o : Outcome (State rvIsa × List Unit)) : rvIsa.step p stmtCtx s o ↔ rvIsa.step p sp1Ctx s o := by
  obtain ⟨stack, regs, m⟩ := s
  cases stack with
  | nil => exact Iff.rfl
  | cons fr rest =>
    cases hf : p[fr.fn]? with
    | none => simp [Isa.step, hf]
    | some fd =>
      cases hi : fd.body[fr.pc]? with
      | none => simp [Isa.step, hf, hi]
      | some i =>
        rw [SafeN.step_eq hf hi, SafeN.step_eq hf hi]
        cases i with
        | Lext k => exact absurd (SafeN.fetch_eq hf hi) (h k)
        | _ => exact Iff.rfl

/-- A state at an `Lext` traps under `stmtCtx`. -/
theorem step_stmt_trap {p : Lprog (Op Reg) Reg} {s : State rvIsa} {k : Nat}
    (h : rvIsa.fetch p s = some (.Lext k)) : rvIsa.step p stmtCtx s .trap := by
  obtain ⟨stack, regs, m⟩ := s
  cases stack with
  | nil => cases h
  | cons fr rest =>
    obtain ⟨fd, hf, hi⟩ := fetch_some h
    exact (SafeN.step_eq (c := stmtCtx) (rest := rest) (regs := regs) (m := m) hf hi .trap).2 rfl

/-! ## The machine at an `Lext` -/

theorem liftI_ecall {fs : List Fn} {len k : Nat} {pc : Word} {prev : Option Instr} :
    liftI fs len k pc prev .ECALL = .Lext 0 := by
  simp [liftI, liftCtl, opnOk, isPure, isStraight, Instr.isMemAccess, isCSRS]

/-- **A simulated state at an external call has the machine at an `ECALL`.** -/
theorem ecall_of_sim {fs : List Fn} {exit : Word} {s : State rvIsa} {t : MachineState}
    (hs : Sim fs exit s t) {k : Nat} (h : rvIsa.fetch (liftProg fs) s = some (.Lext k)) :
    t.code t.pc = some .ECALL := by
  obtain ⟨stack, regs, m⟩ := s
  cases stack with
  | nil => exact absurd rfl hs.ne
  | cons fr rest =>
    rcases hs.split with ⟨f, j, hAt⟩ | ⟨f, j, hAt, -, -⟩ | hw
    · rw [SafeN.fetch_eq (fd := liftFn fs f) (getElem?_liftProg hAt.hf) hAt.body.2] at h
      rw [hAt.fetch, liftI_eq_ext (Option.some.inj h)]
    · have hf : fs[fr.fn]? = some f := by simpa using hAt.hf
      have hpc : fr.pc = 2 * j := by have := hAt.hpc; simp at this; omega
      rw [SafeN.fetch_eq (fd := liftFn fs f) (getElem?_liftProg hf) (hpc ▸ body_even fs f hAt.hk)] at h
      cases h
    · obtain ⟨fd, hf, hi⟩ := fetch_some h
      exact (sp1Ctx_ext_ne_wrong
        ((SafeN.step_eq (c := sp1Ctx) (rest := rest) (regs := regs) (m := m) hf hi .wrong).1 hw)).elim

/-! ## The transfer theorem -/

/-- **Total correctness at Lprog gives a halting run of the statement's machine.** A state simulated by `t`, total
    under `stmtCtx` for `WinOk`, where `Q` holds only inside the program and with `a0` satisfying `H`, has `t` halt
    with `a0` satisfying `H`. -/
theorem halts_of_total {fs : List Fn} (hok : ProgOk fs) {exit : Word} {H : Word → Prop}
    {Q : State rvIsa → Prop} (hQ : ∀ s, Q s → s.stack ≠ [] ∧ H (s.regs .x10)) {s : State rvIsa}
    (h : rvIsa.Total (liftProg fs) stmtCtx (WinOk (liftProg fs)) Q s) :
    ∀ {t : MachineState}, Sim fs exit s t → ∃ n v, Halts t n v ∧ H v := by
  induction h with
  | done _ ha hq =>
    intro t hs
    obtain ⟨hne, hH⟩ := hQ _ hq
    rcases ha with hnil | ⟨k, hk, hacc⟩
    · exact absurd hnil hne
    · refine ⟨0, _, ⟨t, rfl, ecall_of_sim hs hk, ?_, ?_⟩, hH⟩
      · rw [← hs.agree.regs .x5, getReg_ofParts]; exact hacc
      · rw [← hs.agree.regs .x10, getReg_ofParts]; rfl
  | @next s hg hnt hnw _ hnext ih =>
    intro t hs
    have hnoext : ∀ k, rvIsa.fetch (liftProg fs) s ≠ some (.Lext k) := fun k hk => hnt (step_stmt_trap hk)
    have hconv : ∀ s', rvIsa.step (liftProg fs) sp1Ctx s (.ok (s', [])) →
        Ascent.erase (rvIsa.step (liftProg fs) stmtCtx) s (.ok s') :=
      fun s' h' => ⟨[], (step_stmt_iff hnoext _).2 h'⟩
    have hL : ¬ (lsys fs).step s .wrong := fun hw => hnw ((step_stmt_iff hnoext _).2 hw)
    obtain ⟨stack, regs, m⟩ := s
    cases stack with
    | nil => exact absurd rfl hs.ne
    | cons fr rest =>
      rcases hs.split with ⟨f, j, hAt⟩ | ⟨f, j, hAt, -, hst⟩ | hw
      · have hfe := SafeN.fetch_eq (fd := liftFn fs f) (rest := rest) (regs := regs) (m := m)
          (getElem?_liftProg hAt.hf) hAt.body.2
        have hfetch := hAt.fetch
        generalize f.prog[j]'hAt.hk = i at hfe hfetch
        have hine : i ≠ .ECALL := by
          rintro rfl
          exact hnoext 0 (by rw [hfe, liftI_ecall])
        cases hstep : stepSp1 t with
        | none =>
          rcases trap_instr hAt hstep (not_accepted_of_code hfetch hine) with hw | ⟨-, htr⟩
          · exact absurd hw hL
          · exact absurd ((step_stmt_iff hnoext _).2 htr) hnt
        | some t' =>
          obtain ⟨s', hs' | hret, hst⟩ := (back_instr hok hL hAt).1 t' hstep
          · obtain ⟨n, v, hh, hv⟩ := ih s' (hconv s' hst) hs'
            have hwin : winOk t i = true := by
              cases hop : opnOk i
              · exact winOk_of_not_opnOk hop
              · exact winOk_of_opWin hAt.sim.agree hop (hg _ (by rw [hfe]; simp [liftI, hop]))
            exact ⟨n + 1, v, Halts.of_step (step_of_stepSp1 hstep hfetch hine hwin) hh, hv⟩
          · obtain ⟨stk, r', m'⟩ := s'
            obtain ⟨hnil, -⟩ := hret
            simp only at hnil
            subst hnil
            exact absurd rfl (hQ _ (Total.of_nil (hnext _ (hconv _ hst)))).1
      · exact ih _ (hconv _ ((hst _).2 rfl)) hAt.sim
      · exact absurd hw hL

/-- **From a function's entry**: a machine at the entry of function `g` of a lifted program it holds halts with `a0`
    satisfying `H`, if the call `⟨g, 0, ra, sp⟩` is total at Lprog for a `Q` that holds only inside the program and
    with `a0` satisfying `H`. -/
theorem halts_of_lift {fs : List Fn} (hok : ProgOk fs) {g : Nat} {fn : Fn} (hg : fs[g]? = some fn)
    {t : MachineState} (hpc : t.pc = fn.base) (hcode : ∀ f ∈ fs, CodeAt f.base (f.prog.map some) t)
    {H : Word → Prop} {Q : State rvIsa → Prop} (hQ : ∀ s, Q s → s.stack ≠ [] ∧ H (s.regs .x10))
    (hL : rvIsa.Total (liftProg fs) stmtCtx (WinOk (liftProg fs)) Q
      ⟨[⟨g, 0, t.getReg .x1, t.getReg .x2⟩], regsOf t, t⟩) :
    ∃ n v, Halts t n v ∧ H v :=
  halts_of_total (exit := t.getReg .x1) hok hQ hL
    ⟨agree_ofParts_regsOf t, hcode, ⟨⟨fn, hg, Nat.zero_le _, by simp [hpc]⟩, nofun, rfl⟩, by simp⟩

end Rv64mc
