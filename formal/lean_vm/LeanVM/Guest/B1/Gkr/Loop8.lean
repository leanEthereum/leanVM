/-
  LeanVM.Guest.B1.Gkr.Loop8

  `verify_bus_gkr`'s last loop `verify_bus_gkr_loop0`: the final point copied from its row to
  `zeta`.
-/

module

public import LeanVM.Guest.B1.Gkr.Fs
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData
import LeanVM.Guest.B1.Common.Vc
import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_bus_gkr_loop0»

/-!
# The final point's copy (`verify_bus_gkr_loop0`)

`verify_bus_gkr_loop0(x, g^depth, zeta, row)` asserts `zeta[x] = row[x]` and runs on to `x·g` below
the bound: from `x = 1`, the point of `depth` coordinates at `row` is at `zeta` (`l8_loop`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- `verify_bus_gkr_loop0`'s body. -/
def l8Body : List Stmt :=
  [.atom (.mul (.n (val% «verify_bus_gkr_loop0» "s0#0")) (.n (val% «verify_bus_gkr_loop0» "final_point_row")) (.n (val% «verify_bus_gkr_loop0» "xt"))), .atom (.load (.n (val% «verify_bus_gkr_loop0» "s0#1")) (.n (val% «verify_bus_gkr_loop0» "s0#0")) 0),
    .atom (.mul (.n (val% «verify_bus_gkr_loop0» "s0#2")) (.n (val% «verify_bus_gkr_loop0» "zeta")) (.n (val% «verify_bus_gkr_loop0» "xt"))), .atom (.load (.n (val% «verify_bus_gkr_loop0» "s0#1")) (.n (val% «verify_bus_gkr_loop0» "s0#2")) 0),
    .atom (.const (.n (val% «verify_bus_gkr_loop0» "s2#0")) (word 2 0)), .atom (.mul (.n (val% «verify_bus_gkr_loop0» "s2#1")) (.n (val% «verify_bus_gkr_loop0» "xt")) (.n (val% «verify_bus_gkr_loop0» "s2#0"))),
    .atom (.add (.n (val% «verify_bus_gkr_loop0» "s2#2")) (.n (val% «verify_bus_gkr_loop0» "s2#1")) (.n (val% «verify_bus_gkr_loop0» "bound"))), .atom (.const (.n (val% «verify_bus_gkr_loop0» "s2#3")) (word 2 0)),
    .atom (.mul (.n (val% «verify_bus_gkr_loop0» "s2#4")) (.n (val% «verify_bus_gkr_loop0» "xt")) (.n (val% «verify_bus_gkr_loop0» "s2#3"))),
    .callIf (.n (val% «verify_bus_gkr_loop0» "s2#2")) name% «verify_bus_gkr_loop0» [.n (val% «verify_bus_gkr_loop0» "s2#4"), .n (val% «verify_bus_gkr_loop0» "bound"), .n (val% «verify_bus_gkr_loop0» "zeta"), .n (val% «verify_bus_gkr_loop0» "final_point_row")], .ret []]

noncomputable def l8Check : Bool :=
  match coreProgram.find? name% «verify_bus_gkr_loop0» with
  | some fn => decide (fn.params = [.n (val% «verify_bus_gkr_loop0» "xt"), .n (val% «verify_bus_gkr_loop0» "bound"), .n (val% «verify_bus_gkr_loop0» "zeta"), .n (val% «verify_bus_gkr_loop0» "final_point_row")]) && stmtsEqb fn.body l8Body
  | none => false

theorem l8Check_eq : l8Check = true := by decide +kernel

theorem l8Found : ∃ fn : Fn, coreProgram.find? name% «verify_bus_gkr_loop0» = some fn ∧
    fn.params = [.n (val% «verify_bus_gkr_loop0» "xt"), .n (val% «verify_bus_gkr_loop0» "bound"), .n (val% «verify_bus_gkr_loop0» "zeta"), .n (val% «verify_bus_gkr_loop0» "final_point_row")] ∧ fn.body = l8Body := by
  have h := l8Check_eq
  unfold l8Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, stmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

/-- **An iteration of `verify_bus_gkr_loop0`**: the word at `row·x` is the one at `zeta·x`. -/
theorem l8_step {rd : Reader} {N zeta row : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «verify_bus_gkr_loop0» (x :: [N, zeta, row]) []) :
    (∀ w, LoadHolds rd (row * x) 0 w → LoadHolds rd (zeta * x) 0 w) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «verify_bus_gkr_loop0» (x * gen :: [N, zeta,
          row]) []) := by
  revert h
  rw [B1.relN_succ_iff_fnSem (coreProgram_find?_at (j := idx% «verify_bus_gkr_loop0») rfl)]
  vc [B1.word_gen]
  rintro ⟨w, hr, hz, -, hc, -⟩
  exact ⟨fun w' hw => loadHolds_unique hr hw ▸ hz, hc⟩

/-- **`verify_bus_gkr_loop0` from `1` below `g^m`**: the point at `row` is at `zeta`. -/
theorem l8_loop {rd : Reader} {N zeta row : E} {m : ℕ} (hN : N = gen ^ m) (hm : 0 < m)
    (hmb : m < 2 ^ 62) (h : coreProgram.Rel rd name% «verify_bus_gkr_loop0» [1, N, zeta, row] [])
    {pt : List E} (hl : pt.length = m) (hpt : ReadsAt rd row pt) : ReadsAt rd zeta pt := by
  rw [← pow_zero gen] at h
  obtain ⟨m', -, hN', hall⟩ := tb_loop_sound (B := fun x ↦ ∀ w, LoadHolds rd (row * x) 0 w →
    LoadHolds rd (zeta * x) 0 w) (fun d x hx => l8_step d x hx) 0 h
  have hmm : m ≤ m' := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) (hN.symm.trans hN')
    omega
  intro k hk
  have := hall k (by omega) (by omega) pt[k]
    (by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hpt k hk)
  rw [loadHolds_mul_gen_pow, Nat.add_zero] at this
  exact this

end
end LeanVM.Guest.B1.Tables
