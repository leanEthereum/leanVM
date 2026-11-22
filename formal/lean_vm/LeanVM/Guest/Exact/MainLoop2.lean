/-
  LeanVM.Guest.Exact.MainLoop2

  `main_loop2` is exact for free: its body, checked by chunks, has no computed hint and calls only itself.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.CoreNames
import LeanVM.Guest.Exact.MainLoop2.C0
import LeanVM.Guest.Exact.MainLoop2.C1a
import LeanVM.Guest.Exact.MainLoop2.C1b
import LeanVM.Guest.Exact.MainLoop2.C2
import LeanVM.Guest.Exact.MainLoop2.C3
import LeanVM.Guest.Exact.MainLoop2.C4a
import LeanVM.Guest.Exact.MainLoop2.C4b
import LeanVM.Guest.Exact.MainLoop2.C5
import LeanVM.Guest.Exact.MainLoop2.C6

/-!
# `main_loop2`, exact for free

`main_loop2` (leanXMSS's check inline, its hints all witness entries) is too large for `exactFree`'s one kernel
evaluation. Its body is `c0 ++ … ++ c6`; each chunk has no computed hint and calls only `main_loop2`
(`Exact/MainLoop2/C*`, one kernel evaluation each, `c1` and `c4` in two), so `exactFreeG_of_atoms` applies.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

@[expose] public section

theorem main_loop2_exactFree : ExactFreeG name% «main_loop2» := by
  have hb : Stmt.atomsAll (fun a => !isComputed a) (fn% «main_loop2»).body = true ∧
      (Stmt.blockCallees (fn% «main_loop2»).body).all (· == name% «main_loop2») = true := by
    rw [show (fn% «main_loop2»).body = Fn.«main_loop2».core.c0 ++ Fn.«main_loop2».core.c1 ++
      Fn.«main_loop2».core.c2 ++ Fn.«main_loop2».core.c3 ++ Fn.«main_loop2».core.c4 ++
      Fn.«main_loop2».core.c5 ++ Fn.«main_loop2».core.c6 from rfl,
      ← List.take_append_drop 3 Fn.«main_loop2».core.c1, ← List.take_append_drop 3 Fn.«main_loop2».core.c4]
    simp only [Stmt.atomsAll_append, Stmt.blockCallees_append, List.all_append, main_loop2_c0.1, main_loop2_c0.2,
      main_loop2_c1a.1, main_loop2_c1a.2, main_loop2_c1b.1, main_loop2_c1b.2, main_loop2_c2.1, main_loop2_c2.2,
      main_loop2_c3.1, main_loop2_c3.2, main_loop2_c4a.1, main_loop2_c4a.2, main_loop2_c4b.1, main_loop2_c4b.2,
      main_loop2_c5.1, main_loop2_c5.2, main_loop2_c6.1, main_loop2_c6.2, Bool.and_self]
    exact ⟨trivial, trivial⟩
  have hidx : (calleeIdx (idx% «main_loop2») (name% «main_loop2»)).isSome = true := by decide +kernel
  exact exactFreeG_of_atoms (j := idx% «main_loop2») rfl rfl hb.1
    (fun g hg => by rw [beq_iff_eq.mp (List.all_eq_true.mp hb.2 g hg)]; exact hidx) (by decide +kernel)

end
end LeanVM.Guest.Memory
