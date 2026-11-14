/-
  LeanVM.Guest.Exact.FreeSpWots

  `sp_wots` is exact for free: its body, checked by pieces, has no computed hint and no call.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.CoreNames
import LeanVM.Guest.Exact.SpWots.C0a
import LeanVM.Guest.Exact.SpWots.C0b
import LeanVM.Guest.Exact.SpWots.C0c
import LeanVM.Guest.Exact.SpWots.C1

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem sp_wots_exactFree : ExactFreeG name% «sp_wots» := by
  have hb : (fn% «sp_wots»).body = Fn.«sp_wots».core.c0.take 51 ++ ((Fn.«sp_wots».core.c0.drop 51).take 40 ++
      Fn.«sp_wots».core.c0.drop 91) ++ Fn.«sp_wots».core.c1 := by
    rw [show Fn.«sp_wots».core.c0.drop 91 = (Fn.«sp_wots».core.c0.drop 51).drop 40 by rw [List.drop_drop],
      List.take_append_drop, List.take_append_drop]
    rfl
  refine exactFreeG_of_atoms (j := idx% «sp_wots») rfl rfl ?_ (fun g hg => ?_) (by decide +kernel)
  · rw [hb, Stmt.atomsAll_append, Stmt.atomsAll_append, Stmt.atomsAll_append, sp_wots_c0a.1, sp_wots_c0b.1,
      sp_wots_c0c.1, sp_wots_c1.1]; rfl
  · rw [hb, Stmt.blockCallees_append, Stmt.blockCallees_append, Stmt.blockCallees_append, sp_wots_c0a.2,
      sp_wots_c0b.2, sp_wots_c0c.2, sp_wots_c1.2] at hg; simp at hg

end
end LeanVM.Guest.Memory
