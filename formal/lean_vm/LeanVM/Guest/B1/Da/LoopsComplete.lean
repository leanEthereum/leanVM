/-
  LeanVM.Guest.B1.Da.LoopsComplete

  `da_verify`'s loops over the blobs and its columns' row loop, completely (G:4342-4361,
  G:4384-4391): each block holds on the words an honest run leaves in memory, so each loop runs to
  its end.
-/

module

public import LeanVM.Guest.B1.Da.LoopsCChk
public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.B1.Da.ColumnChk
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Digest.LoopComplete
public import LeanVM.Guest.Value.KeccakConst

/-!
# The loops, completely

The blocks (`LoopBlock`) of `__loop21` (a blob's region at `rowbase[x]`, its running sum's first
word zero), `__loop23` (the sum zero at word `640`, the region's tree's root at `roots·x²`),
`__loop24` (a padding blob's root) and `__loop25` (a blob's cell in a column: its check, the
running sum's step at words `512 + j`, `513 + j`, its digest at the tree's leaf `2j`), each from
the memory words it reads and writes; `loopPre_of_body` reads a block off a body checked as a
block and its closing tail call. `loopF_complete` (`B1.Digest`) runs each to its end.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Main

@[expose] public section

variable {rd : Reader}

/-! ## Blocks off bodies -/

theorem splitLoopF_append {c : V} {f : String} {args : List V} :
    ∀ pre : List Stmt, pre.all Stmt.flat = true →
      splitLoopF (pre ++ [.callIf c f args, .ret []]) = some (pre, c, f, args)
  | [], _ => rfl
  | [s], h => by
    simp only [List.all_cons, List.all_nil, Bool.and_true] at h
    simp [splitLoopF, h]
  | s :: t :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := splitLoopF_append (c := c) (f := f) (args := args) (t :: rest)
      (by simp only [List.all_cons, Bool.and_eq_true]; exact h.2)
    obtain ⟨u, rest', hu⟩ : ∃ u rest', rest ++ [Stmt.callIf c f args, Stmt.ret []] = u :: rest' := by
      cases rest <;> exact ⟨_, _, rfl⟩
    simp only [List.cons_append, hu] at ih ⊢
    rw [show splitLoopF (s :: t :: u :: rest') = if Stmt.flat s then
        (splitLoopF (t :: u :: rest')).map (fun p => (s :: p.1, p.2)) else none from rfl,
      ite_pos' h.1, ih]
    rfl

theorem loopPre_of_body {fn : Fn} {pre : List Stmt} {c : V} {f : String} {args : List V}
    (h : fn.body = pre ++ [.callIf c f args, .ret []]) (hf : pre.all Stmt.flat = true) :
    loopPre fn = pre := by
  simp [loopPre, h, splitLoopF_append pre hf]

theorem find_l17 : coreProgram.find? "__loop21" = some (coreProgram.getD 387 default) :=
  find_of_idx dv_loops_idx.1 (by rw [coreProgram_length]; omega)

theorem find_l19 : coreProgram.find? "__loop23" = some (coreProgram.getD 389 default) :=
  find_of_idx dv_loops_idx.2.2.1 (by rw [coreProgram_length]; omega)

theorem find_l20 : coreProgram.find? "__loop24" = some (coreProgram.getD 390 default) :=
  find_of_idx dv_loops_idx.2.2.2 (by rw [coreProgram_length]; omega)

theorem find_l21 : coreProgram.find? "__loop25" = some (coreProgram.getD 403 default) :=
  find_of_idx l21_idx (by rw [coreProgram_length]; omega)

/-! ## The blocks -/

set_option maxRecDepth 20000 in
/-- **A blob's region** (`__loop21`): `rowbase[x] = blobs·x^641`, its running sum's first word
zero. -/
theorem l17_block {x N bl rb : E} (h1 : LoadHolds rd (rb * x) 0 (bl * x ^ 641))
    (h2 : LoadHolds rd (bl * x ^ 641) 512 0) :
    LoopBlock rd (coreProgram.getD 387 default) x N [bl, rb] := by
  obtain ⟨⟨hs, hl⟩, -⟩ := dv_loops_shape
  rw [← word_zero] at h2
  refine ⟨Val.ofArgs [x, N, bl, rb, x * x, x * x * (x * x), x * x * (x * x) * x,
    x ^ 10, x ^ 20, x ^ 40, x ^ 80, x ^ 160, x ^ 320, x ^ 640, x ^ 641, bl * x ^ 641, rb * x,
    word 0 0, word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0],
    by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body dv_loops_body.1 (by decide)]
  intro st hst
  simp only [l17Pre, l17Pows, stepAtC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  all_goals try ring1
  exacts [h1, h2]

set_option maxRecDepth 20000 in
/-- **A blob's tree** (`__loop23`): its region's sum zero at word `640`, its root at
`roots·x²`. -/
theorem l19_block {x N rb roots base c0 c1 : E} (h1 : LoadHolds rd (rb * x) 0 base)
    (h2 : LoadHolds rd base 640 0) (hc : coreProgram.Rel rd "da_levels__L128_L7" [base] [c0, c1])
    (h3 : LoadHolds rd (roots * (x * x)) 0 c0) (h4 : LoadHolds rd (roots * (x * x)) 1 c1) :
    LoopBlock rd (coreProgram.getD 389 default) x N [rb, roots] := by
  obtain ⟨-, ⟨hs, hl⟩, -⟩ := dv_loops_shape
  refine ⟨Val.ofArgs [x, N, rb, roots, rb * x, base, 0, word 0 0, c0, c1, x * x,
    roots * (x * x), word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0],
    by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body dv_loops_body.2.1 (by decide)]
  intro st hst
  simp only [l19Pre, stepAtC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, and_true]
  exacts [h1, h2, by rw [word_zero, zero_add], hc, h3, h4]

set_option maxRecDepth 20000 in
/-- **A padding blob's root** (`__loop24`) at `roots·n_blob²·x²`. -/
theorem l20_block {x N roots nb : E}
    (h0 : LoadHolds rd (roots * (nb * nb) * (x * x)) 0 (digestHalves daPadBlobDigest).1)
    (h1 : LoadHolds rd (roots * (nb * nb) * (x * x)) 1 (digestHalves daPadBlobDigest).2) :
    LoopBlock rd (coreProgram.getD 390 default) x N [roots, nb] := by
  obtain ⟨-, -, ⟨hs, hl⟩, -⟩ := dv_loops_shape
  have e := daPadBlob_cells
  simp only [Prod.ext_iff] at e
  rw [← e.1] at h0
  rw [← e.2] at h1
  refine ⟨Val.ofArgs [x, N, roots, nb, nb * nb, roots * (nb * nb), x * x,
    roots * (nb * nb) * (x * x), word 8002054802297438051 4108169256045952147,
    word 12830724869163462953 1721925254677230945, word 2 0, x * word 2 0,
    x * word 2 0 + N, word 2 0, x * word 2 0], by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body dv_loops_body.2.2.1 (by decide)]
  intro st hst
  simp only [l20Pre, stepAtC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, and_true]
  exacts [h0, h1]

set_option maxRecDepth 20000 in
/-- **A blob's cell in a column** (`__loop25`): the cell's check, the running sum's step from word
`512` to `513` at `base·xb`, the cell's digest at the leaf `base·xb2`. -/
theorem l21_block {x N lv rb xb xb2 d0 d1 s base prev : E}
    (hc : coreProgram.Rel rd "da_verify_cell" [lv] [d0, d1, s])
    (h1 : LoadHolds rd (rb * x) 0 base) (h2 : LoadHolds rd (base * xb) 512 prev)
    (h3 : LoadHolds rd (base * xb) 513 (prev + s)) (h4 : LoadHolds rd (base * xb2) 0 d0)
    (h5 : LoadHolds rd (base * xb2) 1 d1) :
    LoopBlock rd (coreProgram.getD 403 default) x N [lv, rb, xb, xb2] := by
  obtain ⟨-, -, -, hs, hl⟩ := dv_loops_shape
  refine ⟨Val.ofArgs [x, N, lv, rb, xb, xb2, d0, d1, s, rb * x, base, base * xb, prev, prev + s,
    base * xb2, word 2 0, x * word 2 0, x * word 2 0 + N, word 2 0, x * word 2 0],
    by rw [params_of_shape hs hl]; rfl, ?_⟩
  rw [loopPre_of_body dv_loops_body.2.2.2 (by decide)]
  intro st hst
  simp only [l21Pre, stepAtC, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals simp (config := {failIfUnchanged := false}) only [Stmt.Holds, Atom.Holds, ofArgs_n,
    List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, and_true]
  exacts [hc, h1, h2, h3, h4, h5]

end
end LeanVM.Guest.B1.Da
