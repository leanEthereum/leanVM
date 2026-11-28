/-
  LeanVM.Guest.Memory.FamilyHand

  A certificate family with hand functions, checked by the kernel in ranges like any family: each
  function its certificate's check, a hand function its inner check over its virtual parameters, a
  loop hand its iteration's, an absent function none (`chkHJ`). Its ranges covering the core IR
  give the check with hand functions (`checkedH_of_chkHJ`) and each loop hand's iteration check
  (`loopHand_checked`).
-/

module

public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.Memory.FamilySound
public import LeanVM.Guest.Memory.StaticCut

/-!
# Families with hand functions

A hand function is checked over virtual parameters (`Memory/StaticSound.lean`'s `Hand`, `chkHand`):
its inner certificate's check, its callees' certificates the family's, so a hand function's callers
see its outer certificate, the family's. A **loop hand** is a loop helper whose iteration's bound
reads values of the iteration (`chkHandL`): its iteration (`loopShape`) is checked over its
parameters and virtual ones; a run's bound is the sum of its iterations', which no certificate of
its arguments states, so a loop hand is left out of `CheckedH` (with the absent functions) and
bounded apart. `chkHJ` is the family's check; `chkHJ_of_hand_run`, `chkHJ_of_hand_split`,
`chkHJ_of_loop_run`, `chkHJ_of_chkS` give it from a walk cut into ranges (`StaticCut`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The hand of no virtual parameter and no bound. -/
def Hand.zero : Hand := ⟨[], [], ⟨0, []⟩, []⟩

/-- **The check of function `j` in a family with hand functions**: none if absent, a loop hand's
iteration, a hand's inner check, else its certificate's. -/
noncomputable def chkHJ (α : Bool) (cert : ℕ → Cert) (hand : ℕ → Option Hand)
    (lh : ℕ → Option (Hand × Option ℕ)) (abs : ℕ → Bool) (om : ℕ → ℕ) (j : ℕ) (fn : Fn) : Bool :=
  abs j || match lh j with
    | some (h, endc) => chkHandL (lookS cert j) (omLookS om j) α h endc (om j) fn
    | none => match hand j with
      | some h => chkHand (lookS cert j) (omLookS om j) α h (om j) fn
      | none => chkS α cert om j fn

/-- The step of hand function `j`'s inner check. -/
noncomputable def stepHJ (α : Bool) (cert : ℕ → Cert) (hand : ℕ → Option Hand) (om : ℕ → ℕ) (j : ℕ)
    (fn : Fn) : Stmt → Env × BEnv → Option (Acc × Option (Env × BEnv)) :=
  stmtR (lookS cert j) (omLookS om j) α ((hand j).getD .zero).ks (fn.params ++ ((hand j).getD .zero).vps) fn.name

/-- The step of loop hand `j`'s iteration check. -/
noncomputable def stepLJ (α : Bool) (cert : ℕ → Cert) (lh : ℕ → Option (Hand × Option ℕ)) (om : ℕ → ℕ)
    (j : ℕ) (fn : Fn) : Stmt → Env × BEnv → Option (Acc × Option (Env × BEnv)) :=
  stmtR (lookS cert j) (omLookS om j) α ((lh j).getD (.zero, none)).1.ks
    (fn.params ++ ((lh j).getD (.zero, none)).1.vps) fn.name

variable {α : Bool} {cert : ℕ → Cert} {hand : ℕ → Option Hand} {lh : ℕ → Option (Hand × Option ℕ)}
  {abs : ℕ → Bool} {om : ℕ → ℕ} {j : ℕ} {fn : Fn}

/-- A certified function's check is its family check. -/
theorem chkHJ_of_chkS (habs : abs j = false) (hlh : lh j = none) (hh : hand j = none)
    (hc : chkS α cert om j fn = true) : chkHJ α cert hand lh abs om j fn = true := by
  unfold chkHJ; rw [habs, hlh, hh]; exact hc

/-- **A hand function's check from its walk.** -/
theorem chkHJ_of_hand_run {r : Acc} (habs : abs j = false) (hlh : lh j = none)
    (hh : (hand j).isSome = true)
    (hb : runB Acc.add Acc.zero (stepHJ α cert hand om j fn) fn.body ([], []) = some r)
    (hc : (Cert.stat ((hand j).getD .zero).pre ((hand j).getD .zero).b ((hand j).getD .zero).ks).final (om j) r = true) :
    chkHJ α cert hand lh abs om j fn = true := by
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hh
  unfold chkHJ; rw [habs, hlh, hh]
  simp only [Bool.false_or]
  unfold chkHand
  rw [Bool.or_eq_true]; left
  simp only [stepHJ, hh, Option.getD_some] at hb hc
  rw [← blockR_run] at hb
  unfold statB
  simp only [Fn.withVps]
  rw [hb]
  exact hc

/-- **A hand function's check split at its first top-level selector.** -/
theorem chkHJ_of_hand_split {x n : ℕ} (habs : abs j = false) (hlh : lh j = none)
    (hh : (hand j).isSome = true) (hs : topSel fn.body = some (x, n))
    (hc : (Nat.blt 0 n && Nat.blt n 4611686018427387904 && armLeL x n fn.body) = true)
    (harms : ∀ r < n, ∃ acc, runB Acc.add Acc.zero (stepHJ α cert hand om j fn) (selL x r fn.body) ([], []) =
      some acc ∧ (Cert.stat ((hand j).getD .zero).pre ((hand j).getD .zero).b
        ((hand j).getD .zero).ks).final (om j) acc = true) :
    chkHJ α cert hand lh abs om j fn = true := by
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hh
  unfold chkHJ; rw [habs, hlh, hh]
  simp only [Bool.false_or]
  unfold chkHand
  rw [Bool.or_eq_true]; right
  unfold selSplit
  rw [hs]
  dsimp only
  rw [hc, Bool.true_and, List.all_eq_true]
  intro r hr
  obtain ⟨acc, hrun, hfin⟩ := harms r (List.mem_range.mp hr)
  simp only [stepHJ, hh, Option.getD_some] at hrun hfin
  unfold statB
  rw [blockR_run]
  simp only [Fn.withVps]
  rw [hrun]
  exact hfin

/-- **A loop hand's check from its iteration's walk**, guarded against `ret`. -/
theorem chkHJ_of_loop_run {h : Hand} {endc : Option ℕ} {r : Acc} (habs : abs j = false)
    (hlh : lh j = some (h, endc)) (ht : (loopTail fn endc).isSome = true)
    (hb : runB Acc.add Acc.zero (guardRet (stepLJ α cert lh om j fn)) (loopBody fn) ([], []) = some r)
    (hc : (Cert.stat h.pre h.b h.ks).final (om j) r = true) : chkHJ α cert hand lh abs om j fn = true := by
  unfold chkHJ; rw [habs, hlh]
  simp only [Bool.false_or]
  simp only [stepLJ, hlh, Option.getD_some] at hb
  obtain ⟨hn, hb⟩ := runB_guard (stmtR_stops _ _ _ _ _ _) hb
  rw [← blockR_run] at hb
  unfold chkHandL
  rw [loopShape_of ht hn]
  simp only
  rw [hb]
  exact hc

/-- **A family with hand functions whose ranges pass** gives the check with hand functions, the
absent functions and the loop hands left out. -/
theorem checkedH_of_chkHJ (hr : RangeOk (chkHJ α cert hand lh abs om) 0 coreProgram.length)
    {ω : String → ℕ} (hω : ∀ j (hj : j < coreProgram.length), ω coreProgram[j].name = om j) :
    CheckedH coreProgram α (fun g => cert (coreIdx g)) ω (fun g => hand (coreIdx g))
      (fun g => abs (coreIdx g) = true ∨ (lh (coreIdx g)).isSome = true) := by
  intro fn hfn hA
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  have hc := RangeOk.all hr hj
  simp only [coreIdx_getElem hj] at hA ⊢
  refine ⟨lookS cert j, omLookS om j, lookS_ok cert j, omLookS_ok hω j, ?_⟩
  have habs : abs j = false := by cases h : abs j <;> simp_all
  have hlh : lh j = none := by cases h : lh j <;> simp_all
  unfold chkHJ at hc
  rw [habs, hlh, Bool.false_or] at hc
  rw [hω j hj]
  cases hh : hand j with
  | none => rw [hh] at hc; exact hc
  | some h => rw [hh] at hc; exact hc

/-- **A loop hand's iteration checks.** -/
theorem loopHand_checked (hr : RangeOk (chkHJ α cert hand lh abs om) 0 coreProgram.length)
    (hj : j < coreProgram.length) {h : Hand} {endc : Option ℕ} (hlh : lh j = some (h, endc))
    (habs : abs j = false) :
    chkHandL (lookS cert j) (omLookS om j) α h endc (om j) coreProgram[j] = true := by
  have hc := RangeOk.all hr hj
  unfold chkHJ at hc
  rw [habs, hlh, Bool.false_or] at hc
  exact hc

end
end LeanVM.Guest.Memory
