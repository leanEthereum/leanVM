/-
  LeanVM.Guest.B1.Gkr.Loop29

  `verify_bus_gkr`'s inner loop `verify_bus_gkr_loop0_loop0`: two GKR rounds an iteration, from
  one round record to the next.
-/

module

public import LeanVM.Guest.B1.Gkr.Rounds
public import LeanVM.Guest.B1.Sumcheck.Gkr
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.CoreData

/-!
# `verify_bus_gkr_loop0_loop0` (G:1967-1989)

`for y in mul_range(1, x_pair)` in a layer of `verify_bus_gkr`: the record at `rd = head·y`, the
point row `pt = point_row·y²`, two rounds, and the record at `rd·g` written. Its body is B1-a's
`gkPre true 2` (the rounds with the cursor loaded from the record), renamed (`l29Sh`: the record,
the row, the cursor and the window table to the iteration's, the capacity three values on, the
others four), after the pointers and before the guard and the next call (`l29Body`, by kernel
evaluation). `l29_step`: an iteration is `TbGkrRoundsOut 2 1` from its record; `l29_loop`: the loop
from `g^0` to `x_pair = g^h` is `TbGkrRoundsOut (2h) h` from the first record.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1

@[expose] public section

/-- `gkPre true 2`'s values in an iteration: the record `head·y` (`5`), the row `ptrow·y²` (`7`),
the cursor (`13`), the window table (`4`), the capacity three on, the others four on. -/
def l29Sh (v : V) : V :=
  if v.idx = 0 then .n 5 else if v.idx = 1 then .n 7 else if v.idx = 2 then .n 13
  else if v.idx < 5 then .n 4 else if v.idx < 10 then .n (v.idx + 3) else .n (v.idx + 4)

/-- The iteration's pointers. -/
def l29Pre : List Stmt :=
  [.atom (.mul (.n 5) (.n 2) (.n 0)), .atom (.mul (.n 6) (.n 3) (.n 0)),
    .atom (.mul (.n 7) (.n 6) (.n 0))]

/-- The guard and the next call's argument. -/
def l29Post : List Stmt :=
  [.atom (.const (.n 97) (word 2 0)), .atom (.mul (.n 98) (.n 0) (.n 97)),
    .atom (.add (.n 99) (.n 98) (.n 1)), .atom (.const (.n 100) (word 2 0)),
    .atom (.mul (.n 101) (.n 0) (.n 100))]

/-- The iteration's atoms. -/
def l29A : List Stmt := l29Pre ++ Stmt.renameList l29Sh (gkPre true 2) ++ l29Post

/-- `verify_bus_gkr_loop0_loop0`'s body. -/
def l29Body : List Stmt :=
  l29A ++ [.callIf (.n 99) name% «verify_bus_gkr_loop0_loop0» [.n 101, .n 1, .n 2, .n 3, .n 4],
    .ret []]

noncomputable def l29Check : Bool :=
  match coreProgram.find? name% «verify_bus_gkr_loop0_loop0» with
  | some fn => decide (fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4]) && tbStmtsEqb fn.body l29Body
  | none => false

set_option maxRecDepth 100000 in
theorem l29Check_eq : l29Check = true := by decide +kernel

theorem l29Found : ∃ fn : Fn, coreProgram.find? name% «verify_bus_gkr_loop0_loop0» = some fn ∧
    fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4] ∧ fn.body = l29Body := by
  have h := l29Check_eq
  unfold l29Check at h
  split at h
  · rename_i fn hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fn, hf, h.1, tbStmtsEqb_sound h.2⟩
  · exact absurd h (by simp)

section Sem

variable {rd : Reader}

/-- B1-a's rounds, on the cursor the record carries, are the rounds between records. -/
theorem tbGkrRoundsOut_of_out {n : ℕ} {rec pt cur : E}
    (h : GkrRoundsOut n rd rec pt cur) (hc : LoadHolds rd rec (5 * gkCap) cur) :
    TbGkrRoundsOut n 1 rd rec pt ∧ (n % 2 = 1 → LoadHolds rd pt (42 + n) 0) := by
  obtain ⟨cap, claim, cs, es, h1, h3, h4, h5, h6, h7, h8, h9, hpad, h10, h11, h12⟩ := h
  exact ⟨⟨cap, cur, claim, cs, es, h1, hc, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hpad⟩

/-- **An iteration of `verify_bus_gkr_loop0_loop0`**: two rounds from the record at `head·x`. -/
theorem l29_step {N head ptrow tabs : E} (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) name% «verify_bus_gkr_loop0_loop0» (x :: [N, head, ptrow,
        tabs]) []) :
    TbGkrRoundsOut 2 1 rd (head * x) (ptrow * x * x) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d name% «verify_bus_gkr_loop0_loop0» (x * gen :: [N,
          head, ptrow, tabs]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hp, hb⟩ := l29Found
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hp] at hpar
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, l29Body, l29A, holdsList_append, holdsList_append, holdsList_append,
    Stmt.holdsList_rename] at hbody
  simp only [l29Pre, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at hbody
  obtain ⟨h5, h6, h7, hmid⟩ := hbody
  obtain ⟨hout, hcur, htl⟩ := gk_pre_sound true 2 (by norm_num) (by norm_num) hmid
  simp only [l29Post, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at htl
  obtain ⟨c97, m98, a99, c100, m101, -, hnext, -⟩ := htl
  have e0 : (σ ∘ l29Sh) (.n 0) = σ (.n 5) := rfl
  have e1 : (σ ∘ l29Sh) (.n 1) = σ (.n 7) := rfl
  have e2 : (σ ∘ l29Sh) (.n 2) = σ (.n 13) := rfl
  rw [e0, e1, e2] at hout
  rw [e0, e2] at hcur
  refine ⟨?_, fun hne => ?_⟩
  · have := (tbGkrRoundsOut_of_out hout (hcur rfl)).1
    rwa [h5, h7, h6] at this
  · have := hnext (by rw [a99, m98, c97, tb_word_gen]; exact hne)
    rw [m101, c100, tb_word_gen] at this
    exact this

/-- No rounds: a record's facts. -/
theorem gkrRoundsOut_zero {rd : Reader} {rec pt : E} {cap : List E} {cur claim : E}
    (hc : TbCapAt rd rec 0 gkCap cap)
    (hcur : LoadHolds rd rec (5 * gkCap) cur) (hcl : LoadHolds rd rec (6 * gkCap) claim) :
    TbGkrRoundsOut 0 0 rd rec pt :=
  ⟨cap, cur, claim, [], [], hc, hcur, hcl, rfl, by simp, tbReadsAt_nil _ _, rfl,
    tbReadsAt_nil _ _, tbReadsAt_nil _ _, by simpa [gkrRun] using hc,
    by simpa using hcur, by simpa [gkrRun] using hcl⟩

/-- **`verify_bus_gkr_loop0_loop0` behind its guard**: from the record at `head`, `x_pair = g^h`
iterations are the `2h` rounds to the record at `head·g^h`. -/
theorem l29_loop {rd : Reader} {xp head ptrow tabs : E} {h : ℕ} (hh : xp = gen ^ h)
    (hhb : h < 2 ^ 62)
    (hcall : 1 + xp ≠ 0 → coreProgram.Rel rd name% «verify_bus_gkr_loop0_loop0» [1, xp, head,
        ptrow, tabs] [])
    (h0 : TbGkrRoundsOut 0 0 rd head ptrow) : TbGkrRoundsOut (2 * h) h rd head ptrow := by
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · simpa using h0
  have hne : 1 + xp ≠ 0 := by
    rw [hh]
    intro h0'
    have := gen_pow_inj (by omega) (by decide) ((e_add_eq_zero_iff.mp h0').symm.trans
      (pow_zero gen).symm)
    omega
  have hrun := hcall hne
  rw [← pow_zero gen] at hrun
  obtain ⟨m, -, hN, hall⟩ := tb_loop_sound (B := fun x ↦ TbGkrRoundsOut 2 1 rd (head * x)
    (ptrow * x * x)) (fun d x hx => l29_step d x hx) 0 hrun
  have hmh : h ≤ m := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) (hh.symm.trans hN)
    omega
  have key : ∀ i ≤ h, TbGkrRoundsOut (2 * i) i rd head ptrow := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have hb := hall i (by omega) (by omega)
      rw [mul_assoc, ← pow_add, ← two_mul] at hb
      rw [show 2 * (i + 1) = 2 * i + 2 by ring]
      exact gkrRoundsOut_append (ih (by omega)) hb
  exact key h le_rfl

end Sem

end
end LeanVM.Guest.B1.Tables
