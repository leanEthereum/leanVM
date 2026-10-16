module

public import LeanVMCircuits.Rec.Builder

@[expose] public section

/-!
The claim union's constants (`rec::tree::union`), which `LeanVMCircuits.Rec.UnionRows` reads its rows with.

A pool is chunks of `chunk` items, each item one compression of a claim set's written form: its kind bits (`b0`,
`b1`, `pair`), its block of eight words, the counter word they give, and the chaining value, the parameter IV at a
run's start. Runs start at a pool's first item and at a chunk's first item whose begin bit is set; a one-hot over the
runs moves on at each begin, and a run's end item holds the digest of its run.
-/

namespace LeanVMCircuits.Rec.Model

/-- `union::CHUNK`. -/
def chunk : ℕ := 32

/-- `multiset::code`'s counter bits. -/
def codeMember : ℕ := 2
def codeEnd : ℕ := 4
def codePair : ℕ := 8

/-- Whether an item starts a run: never, always (the pool's first), or if the begin bit `bit` is set. -/
inductive Start where
  | no
  | yes
  | ifBit (bit : ℕ)
  deriving Repr, DecidableEq, Inhabited

end LeanVMCircuits.Rec.Model
