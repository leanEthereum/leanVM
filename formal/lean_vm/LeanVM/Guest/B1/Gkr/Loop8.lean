/-
  LeanVM.Guest.B1.Gkr.Loop8

  `verify_bus_gkr`'s last loop `__loop7`: the final point copied from its row to `zeta`.
-/

module

public import LeanVM.Guest.B1.Gkr.Fs

/-!
# The final point's copy (`__loop7`, G:2092-2094)

`__loop7(x, g^depth, zeta, row)` asserts `zeta[x] = row[x]` and runs on to `x·g` below the bound:
from `x = 1`, the point of `depth` coordinates at `row` is at `zeta` (`l8_loop`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `__loop7`'s body. -/
def l8Body : List Stmt :=
  [.atom (.mul (.n 4) (.n 3) (.n 0)), .atom (.load (.n 5) (.n 4) 0),
    .atom (.mul (.n 6) (.n 2) (.n 0)), .atom (.load (.n 5) (.n 6) 0),
    .atom (.const (.n 7) (word 2 0)), .atom (.mul (.n 8) (.n 0) (.n 7)),
    .atom (.add (.n 9) (.n 8) (.n 1)), .atom (.const (.n 10) (word 2 0)),
    .atom (.mul (.n 11) (.n 0) (.n 10)),
    .callIf (.n 9) "__loop7" [.n 11, .n 1, .n 2, .n 3], .ret []]

noncomputable def l8Check : Bool :=
  match coreProgram.find? "__loop7" with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3]) && tbStmtsEqb fn.body l8Body
  | none => false

theorem l8Check_eq : l8Check = true := by decide +kernel

theorem l8Found : ∃ fn : Fn, coreProgram.find? "__loop7" = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3] ∧ fn.body = l8Body := by
  have h := l8Check_eq
  unfold l8Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- **An iteration of `__loop7`**: the word at `row·x` is the one at `zeta·x`. -/
theorem l8_step {rd : Reader} {N zeta row : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) "__loop7" (x :: [N, zeta, row]) []) :
    (∀ w, LoadHolds rd (row * x) 0 w → LoadHolds rd (zeta * x) 0 w) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d "__loop7" (x * gen :: [N, zeta, row]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := l8Found
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb] at hbody
  simp only [l8Body, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hbody
  obtain ⟨m4, l5, m6, l5', c7, m8, a9, c10, m11, ⟨-, hc, -⟩⟩ := hbody
  rw [tb_word_gen] at c7 c10
  refine ⟨fun w hw => ?_, fun hne => ?_⟩
  · rw [← m4] at hw
    rw [← m6, ← tb_loadHolds_unique l5 hw]
    exact l5'
  · have := hc (by rw [a9, m8, c7]; exact hne)
    rw [m11, c10] at this
    exact this

/-- **`__loop7` from `1` below `g^m`**: the point at `row` is at `zeta`. -/
theorem l8_loop {rd : Reader} {N zeta row : E} {m : ℕ} (hN : N = gen ^ m) (hm : 0 < m)
    (hmb : m < 2 ^ 62) (h : coreProgram.Rel rd "__loop7" [1, N, zeta, row] [])
    {pt : List E} (hl : pt.length = m) (hpt : TbReadsAt rd row pt) : TbReadsAt rd zeta pt := by
  rw [← pow_zero gen] at h
  obtain ⟨m', -, hN', hall⟩ := tb_loop_sound (B := fun x ↦ ∀ w, LoadHolds rd (row * x) 0 w →
    LoadHolds rd (zeta * x) 0 w) (fun d x hx => l8_step d x hx) 0 h
  have hmm : m ≤ m' := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) (hN.symm.trans hN')
    omega
  intro k hk
  have := hall k (by omega) (by omega) pt[k]
    (by rw [tb_loadHolds_mul_gen_pow, Nat.add_zero]; exact hpt k hk)
  rw [tb_loadHolds_mul_gen_pow, Nat.add_zero] at this
  exact this

end
end LeanVM.Guest.B1.Tables
