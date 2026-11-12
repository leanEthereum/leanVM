/-
  LeanVM.Guest.B1.Da.OffLoopsComplete

  `da_column_offsets`' seven doubling loops, completely (G:4455-4459): each block holds on the words
  an honest run leaves in memory, so each loop runs to its end.
-/

module

public import LeanVM.Guest.B1.Da.LoopsComplete
public import LeanVM.Guest.B1.Da.OffsetsChk

/-!
# The offsets' loops, completely

`offLoops_body`: bit `b`'s loop (`core 423 + b`) is its atoms `offLoopA b` then the closing tail
call (kernel evaluation). `off_block`: its block at the counter `x` holds when, for each `j < 8`,
the region `offsets·x^8` holds a word at `j`, `steps` a word at `j`, and the region their sum at
`8·2^b + j`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

set_option maxRecDepth 100000 in
theorem offLoops_body : ∀ b < 7, stmtsEqb (Fn.body (coreProgram.getD (423 + b) default))
    ((offLoopA b).map Stmt.atom ++ tailAt (offLoopName b) 32 3) = true := by
  decide +kernel

theorem find_off {b : ℕ} (hb : b < 7) :
    coreProgram.find? (offLoopName b) = some (coreProgram.getD (423 + b) default) :=
  find_of_idx (offLoop_idx b hb) (by rw [coreProgram_length]; omega)

/-- The words of the block's run: the counter's powers and the region, then each `j`'s source,
step and sum, then the step to the next counter. -/
def offVals (x N off st : E) (sv tv : ℕ → E) : List E :=
  [x, N, off, st, x * x, x * x * (x * x), x * x * (x * x) * (x * x * (x * x)),
    off * (x * x * (x * x) * (x * x * (x * x)))] ++
  (List.range 8).flatMap (fun j ↦ [sv j, tv j, sv j + tv j]) ++
  [word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0]

theorem offVals_mid {x N off st : E} {sv tv : ℕ → E} {j : ℕ} (hj : j < 8) :
    (offVals x N off st sv tv).getD (8 + 3 * j) 0 = sv j ∧
      (offVals x N off st sv tv).getD (9 + 3 * j) 0 = tv j ∧
      (offVals x N off st sv tv).getD (10 + 3 * j) 0 = sv j + tv j := by
  interval_cases j <;> exact ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
/-- **Bit `b`'s loop block**: `dst[j] = src[j] + steps[j]` for each `j < 8`, `dst` at `8·2^b`
past `src = offsets·x^8`. -/
theorem off_block {b : ℕ} (hb : b < 7) {x N off st : E} (sv tv : ℕ → E)
    (h1 : ∀ j < 8, LoadHolds rd (off * (x * x * (x * x) * (x * x * (x * x)))) j (sv j))
    (h2 : ∀ j < 8, LoadHolds rd st j (tv j))
    (h3 : ∀ j < 8, LoadHolds rd (off * (x * x * (x * x) * (x * x * (x * x)))) (8 * 2 ^ b + j)
      (sv j + tv j)) :
    LoopBlock rd (coreProgram.getD (423 + b) default) x N [off, st] := by
  have hok := offLoop_ok b hb
  simp only [offLoopOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hs, hl⟩, -⟩ := hok
  refine ⟨Val.ofArgs (offVals x N off st sv tv), by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body (stmtsEqb_sound (offLoops_body b hb)) (by
    simp only [List.all_map, List.all_eq_true]; intro a _; rfl)]
  intro s hs'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs'
  simp only [Stmt.Holds, and_true]
  simp only [offLoopA, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range] at ha
  rcases ha with ((rfl | rfl | rfl | rfl) | ⟨j, hj, rfl | rfl | rfl | rfl⟩) | (rfl | rfl | rfl | rfl | rfl)
  all_goals simp only [Atom.Holds, ofArgs_n]
  any_goals rfl
  · obtain ⟨e1, -, -⟩ := offVals_mid (x := x) (N := N) (off := off) (st := st) (sv := sv) (tv := tv) hj
    rw [e1]; exact h1 j hj
  · obtain ⟨-, e2, -⟩ := offVals_mid (x := x) (N := N) (off := off) (st := st) (sv := sv) (tv := tv) hj
    rw [e2]; exact h2 j hj
  · obtain ⟨e1, e2, e3⟩ := offVals_mid (x := x) (N := N) (off := off) (st := st) (sv := sv) (tv := tv) hj
    rw [e1, e2, e3]
  · obtain ⟨-, -, e3⟩ := offVals_mid (x := x) (N := N) (off := off) (st := st) (sv := sv) (tv := tv) hj
    rw [e3]; exact h3 j hj

end
end LeanVM.Guest.B1.Da
