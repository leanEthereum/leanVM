/-
  LeanVM.Guest.B1.Gkr.GlLoop

  The loop of `gkr_layer__L{p}_L{o}`: eight GKR rounds an iteration, from one round record to
  the next, soundly.
-/

module

public import LeanVM.Guest.B1.Gkr.GlRounds
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»
import LeanVM.Guest.B1.Tables.Basic

/-!
# The layer's loop, soundly

`for y in mul_range(1, x_m)` in `gkr_layer__L{p}_L{o}` (`glLoopBody`, the same for the eight):
the record at `head·y^7`, the rows `qrow·y^8` and `nqrow·y^8`, eight rounds, and the next record
(`7` words on) written. `gl_loop_step`: an iteration is `TbGkrRoundsOut 8 1` from its record when
`nqrow = qrow·g^42`; `gl_loop`: the loop from `g^0` to `x_m = g^m` is `TbGkrRoundsOut (8m) m`
from the first record.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem glLoopPre_noRet : Stmt.noRetList glLoopPre = true := by decide

section Sem

variable {rd : Reader}

/-- **An iteration of the layer's loop**: eight rounds from the record at `head·x^7`. -/
theorem gl_loop_step {p o : ℕ} (hp : p < 4) (ho : o < 2) {N head qrow nqrow tabs : E}
    (hq : nqrow = qrow * gen ^ 42) (d : ℕ) (x : E)
    (h : coreProgram.relN rd (d + 1) (glLoopName p o) (x :: [N, head, qrow, nqrow, tabs]) []) :
    TbGkrRoundsOut 8 1 rd (head * x ^ 7) (qrow * x ^ 8) ∧
      (x * gen + N ≠ 0 → coreProgram.relN rd d (glLoopName p o)
        (x * gen :: [N, head, qrow, nqrow, tabs]) []) := by
  obtain ⟨fn, hf, σ, hpar, hbody⟩ := h
  obtain ⟨fn', hf', hps, hb⟩ := glIs_sound (glIs_loops p hp o ho)
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  rw [hps] at hpar
  simp only [glLoopParams, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true] at hpar
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hpar
  rw [hb, glLoopBody, List.append_assoc, holdsList_append, holdsList_noRet _ glLoopPre_noRet,
    holdsList_append, holdsList_noRet glLoopRounds (glRounds_noRet ..)] at hbody
  obtain ⟨hpre, hrounds, hpost⟩ := hbody
  rw [glLoopPre, tb_holdsList_append_noRet (by decide), tb_holdsList_append_noRet (by decide),
    tb_holdsList_mapAtoms] at hpre
  obtain ⟨⟨hptr, hcap⟩, hrec⟩ := hpre
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hptr hrec hcap
  obtain ⟨a6, a7, a8, a9, m6, m7, m8, m9, m10, m11⟩ := hptr
  obtain ⟨l17, l18⟩ := hrec
  have e9 : σ (.n (valf% «gkr_layer» «_loop0» "y8")) = σ (.n (valf% «gkr_layer» «_loop0» "y")) ^ 8 := by rw [m9, m8, m7]; ring
  have hnpt : σ (.n (valf% «gkr_layer» «_loop0» "npt")) * gen ^ 0 = σ (.n (valf% «gkr_layer» «_loop0» "pt")) * gen ^ 42 := by
    rw [m11, m10, hq, pow_zero, mul_one]; ring
  have R := glRounds_sound (rd := rd) 8 hrounds hnpt
  simp only [glCapAfter, glClaimAfter, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.reduceMul,
    Nat.reduceAdd, Nat.reduceSub] at R
  rw [glLoopPost, holdsList_append, holdsList_noRet _ (by decide), tb_holdsList_mapAtoms] at hpost
  obtain ⟨hcap', hpost⟩ := hpost
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hpost hcap'
  obtain ⟨c339, m340, l340, l338, c341, m342, a343, c344, m345, _hk, hnext, -⟩ := hpost
  rw [word_two_pow (by norm_num)] at c339
  rw [word_gen] at c341 c344
  refine ⟨?_, fun hne => ?_⟩
  · have e7 : σ (.n (valf% «gkr_layer» «_loop0» "head")) * σ (.n (valf% «gkr_layer» «_loop0» "y")) ^ 7 = σ (.n (valf% «gkr_layer» «_loop0» "rd")) := by
      rw [m6, a9, a8, a7, a6]; ring
    rw [e7, show σ (.n (valf% «gkr_layer» «_loop0» "qrow")) * σ (.n (valf% «gkr_layer» «_loop0» "y")) ^ 8 = σ (.n (valf% «gkr_layer» «_loop0» "pt")) by rw [m10, e9]]
    refine glOut_of_run (capAt_glCap (off := 0) (fun k hk => by simpa using hcap k hk))
      (by exact l17) (by exact l18) R (capAt_glCap (fun k hk => by simpa using hcap' k hk)) ?_
      (by simpa using l338)
    rw [show σ (.n (valf% «gkr_layer» «_loop0» "cur")) * gen ^ (4 * 8) = σ (.n (valf% «gkr_layer» «_loop0» "s12#1")) by rw [m340, c339]]
    simpa using l340
  · have := hnext (by rw [a343, m342, c341]; exact hne)
    rw [m345, c344] at this
    exact this

/-- **The layer's loop behind its guard, every record**: from the record at `head`, the first
`i ≤ m` iterations are the `8i` rounds to the record at `head·g^(7i)`. -/
theorem gl_loop_all {p o : ℕ} (hp : p < 4) (ho : o < 2) {xm head qrow nqrow tabs : E} {m : ℕ}
    (hm : xm = gen ^ m) (hmb : m < 2 ^ 62) (hq : nqrow = qrow * gen ^ 42)
    (hcall : 1 + xm ≠ 0 → coreProgram.Rel rd (glLoopName p o) [1, xm, head, qrow, nqrow, tabs] [])
    (h0 : TbGkrRoundsOut 0 0 rd head qrow) : ∀ i ≤ m, TbGkrRoundsOut (8 * i) i rd head qrow := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · intro i hi; obtain rfl : i = 0 := by omega
    simpa using h0
  have hne : 1 + xm ≠ 0 := by
    rw [hm]
    intro h0'
    have := gen_pow_inj (by omega) (by decide) ((e_add_eq_zero_iff.mp h0').symm.trans
      (pow_zero gen).symm)
    omega
  have hrun := hcall hne
  rw [← pow_zero gen] at hrun
  obtain ⟨m', -, hN, hall⟩ := tb_loop_sound (B := fun x ↦ TbGkrRoundsOut 8 1 rd (head * x ^ 7)
    (qrow * x ^ 8)) (fun d x hx => gl_loop_step hp ho hq d x hx) 0 hrun
  have hmm : m ≤ m' := by
    by_contra hc
    have := gen_pow_inj (by omega) (by omega) (hm.symm.trans hN)
    omega
  have key : ∀ i ≤ m, TbGkrRoundsOut (8 * i) i rd head qrow := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have hb := hall i (by omega) (by omega)
      rw [← pow_mul, ← pow_mul, mul_comm i 7, mul_comm i 8] at hb
      rw [show 8 * (i + 1) = 8 * i + 8 by ring]
      exact gkrRoundsOut_append (ih (by omega)) hb
  exact key

/-- **The layer's loop behind its guard**: from the record at `head`, `x_m = g^m` iterations are
the `8m` rounds to the record at `head·g^(7m)`. -/
theorem gl_loop {p o : ℕ} (hp : p < 4) (ho : o < 2) {xm head qrow nqrow tabs : E} {m : ℕ}
    (hm : xm = gen ^ m) (hmb : m < 2 ^ 62) (hq : nqrow = qrow * gen ^ 42)
    (hcall : 1 + xm ≠ 0 → coreProgram.Rel rd (glLoopName p o) [1, xm, head, qrow, nqrow, tabs] [])
    (h0 : TbGkrRoundsOut 0 0 rd head qrow) : TbGkrRoundsOut (8 * m) m rd head qrow :=
  gl_loop_all hp ho hm hmb hq hcall h0 m le_rfl

end Sem

end
end LeanVM.Guest.B1.Tables
