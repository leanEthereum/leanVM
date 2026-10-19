/-
  LeanVM.Guest.B1.Da.RelIn

  `Program.RelIn` by an invariant on call instances, from `Memory/GuestRelIn.lean`, exported here
  under its names.
-/

module

public import LeanVM.Guest.B1.Da.Atoms
public import LeanVM.Guest.Memory.GuestRelIn

namespace LeanVM.Guest.B1.Digest

export LeanVM.Guest.Memory (mem_calls_taken relIn_of_inv holds_of_holdsList allocs_append allocDsts_append
  addrs_append runs_append calls_append loadAddrs_append RelInT callsTot kids_of_relInT relInT_of_inv
  RelInT.relIn relAtIn_of_relInT_pure)

end LeanVM.Guest.B1.Digest
