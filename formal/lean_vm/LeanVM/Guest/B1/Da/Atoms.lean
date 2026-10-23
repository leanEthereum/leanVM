/-
  LeanVM.Guest.B1.Da.Atoms

  The path of a body of atoms then a return, and of straight runs around a fused dispatch, from
  `Memory/Straight.lean`, exported here under their names.
-/

module

public import LeanVM.Guest.Memory.Regions
public import LeanVM.Guest.Memory.GuestWf
public import LeanVM.Guest.B1.Main.Straight
public import LeanVM.Guest.B1.Digest.Common

namespace LeanVM.Guest.B1.Digest

export LeanVM.Guest.Memory (walk_atoms atomAllocB atomAddr? atomRun? atomLoad? allocDsts_atoms allocs_atoms addrs_atoms runs_atoms calls_atoms loadAddrs_atoms holds_atoms limb0_gen_pow gpow_add' stmtLoad? loadAddrs_straight stmtRun? runs_straight atom_holds_of_ok pick_eq walk_dispatch logG_gen_pow walk_straight_fall walk_dispatch_fall)

end LeanVM.Guest.B1.Digest
