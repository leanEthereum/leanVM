/-
  LeanVM.Guest.B1.Tables.GkrAt

  `verify_bus_gkr` complete in the uniform placed form (`CompleteGkrAt`).
-/

module

public import LeanVM.Guest.B1.Tables.GkrHolds
public import LeanVM.Guest.B1.Tables.FlockAt
public import LeanVM.Guest.B1.VerifySub.CompleteIface

/-!
# `verify_bus_gkr`, placed

The body is straight-line but for the odd layer's branch, taken when the depth is odd
(`completeAt_iteD`). Its five `HeapBuf`s hold the run's honest trace (`gkrOwn`), its two loops
are pure and complete on every memory agreeing with an honest one (`gkr_loop10`, `gkr_loop11`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The body's shape -/

/-- The statements before the branch. -/
def vbgPre : List Stmt := vbgP0 ++ (fsNextT (.n 17) (.n 18) (.n 2) 0 19 ++
  (fsNextT (.n 32) (.n 33) (.n 2) 1 34 ++ vbgP1))

/-- The odd layer's branch. -/
def vbgOdd : List Stmt := vbgO0 ++ (squeezeT (.n 128) (.n 129) 130 ++ (vbgO1 ++ (vbgOF ++ (vbgO2 ++
  (squeezeT (.n 248) (.n 249) 261 ++ vbgO3)))))

theorem vbg_body' : Fn.body Data.core10 = vbgPre ++ .ite (.n 127) [] vbgOdd ::
    (vbgQ ++ [.ret [.n 305, .n 306, .n 307, .n 308, .n 309, .n 310]]) := by
  rw [vbg_body]; simp only [vbgPre, vbgOdd, List.append_assoc]

/-- The straight block a branch walks. -/
def vbgLin (br : Bool) : List Stmt := vbgPre ++ (if br then [] else vbgOdd) ++ vbgQ

set_option maxRecDepth 100000 in
theorem vbg_straight : vbgPre.all Main.Stmt.straight = true ∧ vbgOdd.all Main.Stmt.straight = true ∧
    vbgQ.all Main.Stmt.straight = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_allocs (br : Bool) : (vbgLin br).filterMap Main.Stmt.allocSz =
    [(.n 10, .inr (.n 9)), (.n 11, .inl 3448), (.n 12, .inl 1640), (.n 56, .inl 33), (.n 57, .inl 33)] := by
  cases br <;> decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_addrs (br : Bool) : (vbgLin br).filterMap Main.Stmt.addrS = [] := by
  cases br <;> decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_calls (br : Bool) : (vbgLin br).filterMap Main.Stmt.callS =
    [(some (.n 290), "__loop10", [.n 291, .n 293, .n 57, .n 3, .n 10, .n 11], []),
      (some (.n 303), "__loop11", [.n 304, .n 3, .n 4, .n 301], [])] := by
  cases br <;> decide +kernel

/-- The body's loads: through which value, at which offsets. -/
def vbgLoadT (br : Bool) : List (ℕ × ℕ × ℕ) :=
  if br then [(2, 0, 2), (10, 0, 8), (56, 0, 33), (57, 0, 33), (124, 0, 1), (288, 0, 1), (292, 0, 1),
    (297, 0, 7)]
  else [(2, 0, 2), (10, 0, 16), (56, 0, 33), (57, 0, 33), (124, 0, 1), (144, 0, 6), (154, 0, 1),
    (288, 0, 1), (292, 0, 1), (297, 0, 7)]

def vbgLoadB (br : Bool) (q : V × ℕ) : Bool :=
  (vbgLoadT br).any fun t => q.1 == .n t.1 && decide (t.2.1 ≤ q.2) && decide (q.2 < t.2.2)

set_option maxRecDepth 100000 in
theorem vbg_loads (br : Bool) : ((vbgLin br).filterMap Stmt.loadS).all (vbgLoadB br) = true := by
  cases br <;> decide +kernel

set_option maxRecDepth 100000 in
theorem vbg_not_loop : coreProgram.loop "verify_bus_gkr" = false := by
  rw [Program.loop_of_find? find_verify_bus_gkr]; decide +kernel

set_option maxRecDepth 100000 in
theorem pure10 : coreProgram.PureIn ["__loop10", "__loop101", "sumcheck_round5"] := by
  intro g hg fn hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [find_loop10] at hfn; cases hfn; rw [core40_body]; decide +kernel
  · rw [find_loop101] at hfn; cases hfn; rw [core574_body]; decide +kernel
  · rw [find_sumcheck_round5] at hfn; cases hfn; decide +kernel

theorem pure11 : coreProgram.PureIn ["__loop11"] := by
  intro g hg fn hfn
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_loop11] at hfn; cases hfn; decide +kernel

end
end LeanVM.Guest.B1.VerifySub
