/-
  LeanVM.Guest.B1.Gkr.GlCurs

  The stream cursors of a radix-four layer's body (`gkr_layer__L{p}_L{o}`): its records' and its
  next slot's, from the slot's cursor.
-/

module

public import LeanVM.Guest.B1.Gkr.GlLayer
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»

/-!
# A layer's cursors

`gl_curs`: on `glBody p o nm`'s statements, at `x_m = g^m`, `x_j = g^j` (`j = 4m + p`),
`start_g = g^(2 - o)`, from the cursor `cur` of the slot of `L = 2j + 2 - o`: the slot's cursor is
value `21`; the head record (`53`) holds `cur·g^(8p)`, and the loop is called on it; the record
`head·g^i`, `i ≤ m`, holds `cur·g^(8p + 32i)`; the tail's cursor (`76 + glD p`) is
`cur·g^(8p + 32m)`; and the next slot holds `cur·g^(4L + 12)`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section Sem

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A layer's cursors.** -/
theorem gl_curs (hC : CallRel.Le C (coreProgram.Rel rd)) {p o : ℕ} (hp : p < 4) (ho : o < 2)
    (h : Stmt.HoldsList C rd σ (glBody p o (glLoopName p o)) False kret) {m : ℕ}
    (hxm : σ (.n (valf% «gkr_layer» "x_m")) = gen ^ m) (hxj : σ (.n (valf% «gkr_layer» "x_j")) = gen ^ (4 * m + p))
    (hsg : σ (.n (valf% «gkr_layer» "start_g")) = gen ^ (2 - o)) (hj : 4 * m + p < 2 ^ 30) {cur : E}
    (hcur : LoadHolds rd (σ (.n (valf% «gkr_layer» "layers"))) (10 * (2 * (4 * m + p) + 2 - o) + 5) cur) :
    σ (.n (valf% «gkr_layer» "s4#0")) = cur ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "head"))) 4310 (cur * gen ^ (8 * p)) ∧
      (1 + σ (.n (valf% «gkr_layer» "x_m")) ≠ 0 → C (glLoopName p o) [1, σ (.n (valf% «gkr_layer» "x_m")), σ (.n (valf% «gkr_layer» "head")), σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p),
        σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p) * gen ^ 42, σ (.n (valf% «gkr_layer» "tabs"))] []) ∧
      (∀ i ≤ m, LoadHolds rd (σ (.n (valf% «gkr_layer» "head")) * gen ^ i) 4310 (cur * gen ^ (8 * p + 32 * i))) ∧
      σ (.n (76 + glD p)) = cur * gen ^ (8 * p + 32 * m) ∧
      LoadHolds rd (σ (.n (valf% «gkr_layer» "layers"))) (10 * (2 * (4 * m + p) + 2 - o + 2) + 5)
        (cur * gen ^ (4 * (2 * (4 * m + p) + 2 - o) + 12)) := by
  set j := 4 * m + p with hjdef
  set L := 2 * j + 2 - o with hL
  rw [glBody] at h
  simp only [List.append_assoc] at h
  rw [holdsList_append, holdsList_noRet _ glPre_noRet, holdsList_append,
    holdsList_noRet (glHeadRounds p) (glRounds_noRet ..), holdsList_append,
    holdsList_noRet _ (glHeadStore_noRet p), holdsList_append,
    holdsList_noRet _ (glLoopCall_noRet p _), holdsList_append,
    holdsList_noRet _ (glTailSetup_noRet p), holdsList_append,
    holdsList_noRet (glTailRounds p o) (glRounds_noRet ..), holdsList_append,
    holdsList_noRet _ (glPad_noRet p o), Stmt.holdsList_rename, glTail, holdsList_append,
    holdsList_noRet _ (glTailPre_noRet _)] at h
  obtain ⟨hPre, -, hHS, hLC, hTS, -, -, hTail, -⟩ := h
  -- the slot and the head
  have hnr := glPre_noRet
  have a := fun n a heq => tb_holds_atom (C := C) (rd := rd) (σ := σ) (kret := kret) hnr hPre n a heq
  have m9 := a 0 (.mul (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "x_j")) (.n (valf% «gkr_layer» "x_j"))) (by decide +kernel)
  have m10 := a 1 (.mul (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer~0")) (.n (valf% «gkr_layer» "start_g"))) (by decide +kernel)
  have m11 := a 2 (.mul (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "x_layer")) (.n (valf% «gkr_layer» "x_layer"))) (by decide +kernel)
  have m12 := a 3 (.mul (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "layer~0")) (.n (valf% «gkr_layer» "layer~0"))) (by decide +kernel)
  have m13 := a 4 (.mul (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~1")) (.n (valf% «gkr_layer» "x_layer"))) (by decide +kernel)
  have m14 := a 5 (.mul (.n (valf% «gkr_layer» "layer~3")) (.n (valf% «gkr_layer» "layer~2")) (.n (valf% «gkr_layer» "layer~2"))) (by decide +kernel)
  have m15 := a 6 (.mul (.n (valf% «gkr_layer» "layer")) (.n (valf% «gkr_layer» "layers")) (.n (valf% «gkr_layer» "layer~3"))) (by decide +kernel)
  have l21 := a 12 (.load (.n (valf% «gkr_layer» "s4#0")) (.n (valf% «gkr_layer» "layer")) 5) (by decide +kernel)
  have c23 := a 14 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[1]")) (word 0 0)) (by decide +kernel)
  have c24 := a 15 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[2]")) (word 0 0)) (by decide +kernel)
  have c25 := a 16 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[3]")) (word 0 0)) (by decide +kernel)
  have c26 := a 17 (.const (.n (valf% «gkr_layer» "s4.i1:fs_grind_squeeze.s0.t.s0.i0:fs_perm.s1.t.s0#0[4]")) (word 0 0)) (by decide +kernel)
  simp only [Atom.Holds, tb_word_zero] at m9 m10 m11 m12 m13 m14 m15 l21 c23 c24 c25 c26
  have e10 : σ (.n (valf% «gkr_layer» "x_layer")) = gen ^ L := by
    rw [m10, m9, hxj, hsg, ← pow_add, ← pow_add, show j + j + (2 - o) = L by omega]
  have e15 : σ (.n (valf% «gkr_layer» "layer")) = σ (.n (valf% «gkr_layer» "layers")) * gen ^ (10 * L) := by
    rw [m15, m14, m13, m12, m11, e10, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  have e21 : σ (.n (valf% «gkr_layer» "s4#0")) = cur := by
    rw [e15, tb_loadHolds_mul_gen_pow] at l21
    exact tb_loadHolds_unique l21 hcur
  obtain ⟨hsc, hscur, hscl⟩ := gl_headStore hp hHS
  rw [e21, show 4 * (2 * p) = 8 * p by ring] at hscur
  have hcall := gl_loopCall hp hLC
  -- the loop's records
  have R0 := gkrRoundsOut_zero (pt := σ (.n (valf% «gkr_layer» "point_row")) * gen ^ (2 * p)) hsc hscur hscl
  have RL := gl_loop_all hp ho (head := σ (.n (valf% «gkr_layer» "head"))) (tabs := σ (.n (valf% «gkr_layer» "tabs"))) hxm (by omega) rfl
    (fun hne => hC _ _ _ (hcall hne)) R0
  have hrec : ∀ i ≤ m, LoadHolds rd (σ (.n (valf% «gkr_layer» "head")) * gen ^ i) 4310 (cur * gen ^ (8 * p + 32 * i)) := by
    intro i hi
    obtain ⟨cap1, cap2, cur1, cl1, cl2, hc1, hcur1, -, -, -, hcur2, -⟩ := glRun_of_out (RL i hi)
    obtain rfl := tb_loadHolds_unique hcur1 hscur
    rw [tb_loadHolds_mul_gen_pow]
    convert hcur2 using 1
    ring
  -- the tail's cursor
  obtain ⟨-, -, -, htcur, -⟩ := gl_tailSetup hp hTS
  rw [hxm, tb_loadHolds_mul_gen_pow] at htcur
  have e77 : σ (.n (76 + glD p)) = cur * gen ^ (8 * p + 32 * m) := by
    have := hrec m le_rfl
    rw [tb_loadHolds_mul_gen_pow] at this
    exact tb_loadHolds_unique htcur this
  -- the next slot
  set τ := σ ∘ glRho p o with hτ
  have tz : ∀ k, k < 58 → τ (.n k) = σ (.n k) := fun k hk => by
    simp only [hτ, Function.comp_apply, glRho_lo hk]
  obtain ⟨-, -, -, -, -, -, tcur, -⟩ := gl_tail (τ := τ) (by omega) hTail
    (by rw [tz 23 (by omega)]; exact c23) (by rw [tz 24 (by omega)]; exact c24)
    (by rw [tz 25 (by omega)]; exact c25) (by rw [tz 26 (by omega)]; exact c26)
  have t77 : τ (.n 76) = σ (.n (76 + glD p)) := by
    show σ (glRho p o (.n 76)) = _
    rw [glRho_mid (by omega) (by omega)]
  rw [tz 15 (by omega), e15, tb_loadHolds_mul_gen_pow, t77, e77, mul_assoc, ← pow_add] at tcur
  refine ⟨e21, hscur, hcall, hrec, e77, ?_⟩
  rw [show 10 * (L + 2) + 5 = 10 * L + 25 by ring]
  convert tcur using 2
  congr 1
  omega

end Sem

end
end LeanVM.Guest.B1.Tables
