/-
  LeanVM.Guest.PackHash

  Which pack module holds a function's generated checks: a stable hash of its stable name.
-/

module

/-!
# Packs

A family's per-function checks are written into `K` pack modules, not one module per function:
module startup dominates small modules. A function goes into pack `packOf K key`, a hash of its
stable name `key` (`Data/NameStrings.lean`), so an added or removed function moves no other one;
a function too large for one module has modules of its own. The generators import this module.
-/

namespace LeanVM.Guest

@[expose] public section

/-- 32-bit FNV-1a of a string's UTF-8 bytes. -/
def packHash (s : String) : Nat :=
  s.toUTF8.foldl (fun h b => ((h ^^^ b.toNat) * 16777619) % 2 ^ 32) 2166136261

/-- The pack, of `K`, of the function of stable name `key`. -/
def packOf (K : Nat) (key : String) : Nat := packHash key % K

end
end LeanVM.Guest
