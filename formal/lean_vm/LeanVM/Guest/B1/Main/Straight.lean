/-
  LeanVM.Guest.B1.Main.Straight

  The path of a straight-line body, from `Memory/Straight.lean`, exported here under its names.
-/

module

public import LeanVM.Guest.Memory.Straight
public import LeanVM.Guest.Memory.Placed
public import LeanVM.Guest.B1.Main.Basic

namespace LeanVM.Guest.B1.Main

export LeanVM.Guest.Memory (Stmt.straight slEvs walk1_straight walk_straight Stmt.allocSz Stmt.addrS Stmt.callS mkCall slEvs_atom_alloc straight_parts)

end LeanVM.Guest.B1.Main
