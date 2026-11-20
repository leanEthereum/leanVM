module

public import LeanVM.Guest.Mode.InvDefs

/-!
# One step, along the reference

`onRef_next`: an instruction the executor runs along the reference leaves it on the reference, or in
the final state. `stepOk_conj`: what the instruction gives past all its hints joins a step's
obligations.
-/

namespace LeanVM.Guest.Mode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest
open LeanVM.Prover.Exec

@[expose] public section

/-! ## The reference -/

theorem onRef_moves {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {M : ℕ → E} {s s1 : St}
    (hm : Moves M s s1) (h : OnRef prog img n s) : OnRef prog img n s1 := by
  unfold OnRef
  rw [hm.steps, hm.pc, hm.fp]
  exact h

theorem onRef_not_halted {prog : LeanIsaProgram} {κ n : ℕ} {img : MemoryImage κ} {s : St}
    (h : OnRef prog img n s) : ¬Halted prog s := by
  intro hH
  obtain ⟨hlt, hrun⟩ := h
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  unfold Halted at hH
  rw [hk, run_succ, ite_eq_left hH] at hrun
  cases hrun

theorem halted_of {prog : LeanIsaProgram} {s : St} (hpc : s.pc = 2 ^ prog.logSize - 1) (hfp : s.fp = 0) :
    Halted prog s := by
  unfold Halted Registers.final LeanIsaProgram.pcFinal
  rw [hpc, hfp, pow_zero]

/-- **The next state is on the reference**, or final: an instruction the executor runs, moded,
from a state on the reference. -/
theorem onRef_next {prog : LeanIsaProgram} {adv : Advice} {κ n : ℕ} {img : MemoryImage κ} {C : Ctx}
    (hκ : κ ≤ 28) (hC : Ctx.of prog adv = .ok C) {s s' : St} {op : Op} (hs : Fine (refMem img) s)
    (hon : OnRef prog img n s) (hop : C.ops[s.pc]? = some op) (hmo : OpModed (refMem img) s op)
    (e : runOp C s op = .ok s') :
    OnRef prog img n { s' with steps := s'.steps + 1 } ∨ Halted prog s' := by
  obtain ⟨hsize, hdecC⟩ := ctx_of_spec hC
  have hsz : C.ops.size ≤ 2 ^ 30 := hsize ▸ Nat.pow_le_pow_right (by norm_num) prog.logSize_le
  obtain ⟨hlt, hrun⟩ := hon
  obtain ⟨hpc, hop'⟩ := Array.getElem?_eq_some_iff.mp hop
  subst hop'
  have hpc2 : s.pc < 2 ^ prog.logSize := hsize ▸ hpc
  obtain ⟨k, hk⟩ : ∃ k, n - s.steps = k + 1 := ⟨n - s.steps - 1, by omega⟩
  rw [hk] at hrun
  have hne : (⟨g ^ s.pc, g ^ s.fp⟩ : Registers K) ≠ Registers.final prog := fun h ↦ by
    rw [run_succ, ite_eq_left h] at hrun; cases hrun
  rw [run_succ_of_ne_final hne, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
  obtain ⟨r1, hstep, hrun1⟩ := hrun
  rw [step_of_fetch_eq_some (prog.fetch_gpow ⟨s.pc, hpc2⟩), LeanVM.Semantics.execute] at hstep
  obtain ⟨s2, e2, d2⟩ := runOp_complete hs (refRd_img hκ img) (hdecC s.pc hpc2 hpc) (ctx_small hC s.pc hpc)
    hpc hsz (nextOk_of_run hsize hrun1) hstep hmo
  rw [e] at e2
  cases e2
  cases k with
  | zero =>
    right
    rw [run_zero, Option.some.injEq] at hrun1
    exact d2.regs.trans hrun1
  | succ k =>
    left
    refine ⟨by dsimp only; rw [d2.steps]; omega, ?_⟩
    dsimp only
    rw [d2.steps, show n - (s.steps + 1) = k + 1 by omega, d2.regs]
    exact hrun1

/-- The reference's part of an instruction's modedness reads only the frame. -/
theorem RefOk.congr {M : ℕ → E} {s s1 : St} (hfp : s1.fp = s.fp) {op : Op} (h : RefOk M s op) :
    RefOk M s1 op := by
  cases op with
  | mul a b c => simpa only [RefOk, hfp] using h
  | deref a o c mode => simpa only [RefOk, hfp] using h
  | jump c d f => simpa only [RefOk, hfp] using h
  | _ => trivial

/-! ## A predicate the step preserves -/

/-- **What the step's instruction gives, past its hints**, joined to the step's obligations. -/
theorem stepOk_conj {C : Ctx} {M : ℕ → E} {op : Op} {I J : St → Prop} (s0 : St) :
    ∀ (l : List Hint) (s : St), Moves M s0 s →
      (∀ s1 s', l.foldlM (runHint C) s = .ok s1 → Moves M s0 s1 → runOp C s1 op = .ok s' → Fine M s' →
        I { s' with steps := s'.steps + 1 } → J { s' with steps := s'.steps + 1 }) →
      StepOk C M I op l s → StepOk C M J op l s
  | [], s, hm, hJ, ⟨h1, h2⟩ => ⟨h1, fun s' e hf hle ↦ hJ s s' rfl hm e hf (h2 s' e hf hle)⟩
  | x :: l, s, hm, hJ, ⟨h1, h2⟩ => ⟨h1, fun s' e m ↦
      stepOk_conj s0 l s' (hm.trans m)
        (fun s1 s'' e1 m1 e2 hf hI ↦ hJ s1 s'' (by rw [List.foldlM_cons, e, ok_bind]; exact e1) m1 e2 hf hI)
        (h2 s' e m)⟩

end

end LeanVM.Guest.Mode
