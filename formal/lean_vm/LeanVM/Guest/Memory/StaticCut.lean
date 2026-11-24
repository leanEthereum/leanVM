/-
  LeanVM.Guest.Memory.StaticCut

  A family's check of a guest function from its walk's result, the walk cut into ranges
  (`StaticRun`): the steps of either family (`chkS`, `chkV`).
-/

module

public import LeanVM.Guest.Memory.StaticRun
public import LeanVM.Guest.Memory.Family

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The step of function `j`'s check in a scalar family (`chkS`). -/
noncomputable def stepS (α : Bool) (cert : ℕ → Cert) (om : ℕ → ℕ) (j : ℕ) (fn : Fn) :
    Stmt → Env × BEnv → Option (Acc × Option (Env × BEnv)) :=
  (cert j).guard (stmtR (lookS cert j) (omLookS om j) α (cert j).ks fn.params fn.name)

/-- The step of function `j`'s check in a vector family (`chkV`). -/
noncomputable def stepV (cert : ℕ → CertV) (j : ℕ) (fn : Fn) :
    Stmt → Env × BEnv → Option (AccV × Option (Env × BEnv)) :=
  (cert j).guard (stmtRV (lookV cert j) (cert j).ks fn.params fn.name)

theorem chkS_of_run {α : Bool} {cert : ℕ → Cert} {om : ℕ → ℕ} {j : ℕ} {fn : Fn} {r : Acc}
    (ht : (cert j).tail fn = true)
    (hb : runB Acc.add Acc.zero (stepS α cert om j fn) ((cert j).walk fn) ([], []) = some r)
    (hc : (cert j).final (om j) r = true) : chkS α cert om j fn = true :=
  chkFn_of_run ht hb hc

theorem chkV_of_run {cert : ℕ → CertV} {om : ℕ → Vec} {j : ℕ} {fn : Fn} {r : AccV}
    (ht : (cert j).tail fn = true)
    (hb : runB AccV.add AccV.zero (stepV cert j fn) ((cert j).walk fn) ([], []) = some r)
    (hc : (cert j).final (om j) r = true) : chkV cert om j fn = true :=
  chkFnV_of_run ht hb hc

/-- **A function's vector check split at its first top-level selector** (`selSplit`). -/
theorem chkV_of_split {cert : ℕ → CertV} {om : ℕ → Vec} {j : ℕ} {fn : Fn} {x n : ℕ}
    {pre : List (ℕ × ℕ)} {b : AffV} {ks : List (V × ℕ)} (hj : cert j = .stat pre b ks)
    (hs : topSel fn.body = some (x, n))
    (hc : (Nat.blt 0 n && Nat.blt n 4611686018427387904 && armLeL x n fn.body) = true)
    (harms : ∀ r < n, ∃ acc, runB AccV.add AccV.zero (stepV cert j fn) (selL x r fn.body) ([], []) = some acc ∧
      (cert j).final (om j) acc = true) : chkV cert om j fn = true := by
  unfold chkV chkFnV
  rw [hj]
  dsimp only
  rw [Bool.or_eq_true]; right
  unfold selSplit
  rw [hs]
  dsimp only
  rw [hc, Bool.true_and, List.all_eq_true]
  intro r hr
  obtain ⟨acc, hrun, hfin⟩ := harms r (List.mem_range.mp hr)
  simp only [stepV, hj, CertV.guard, CertV.ks] at hrun
  rw [hj] at hfin
  unfold statBV
  rw [blockRV_run, hrun]
  exact hfin

end
end LeanVM.Guest.Memory
