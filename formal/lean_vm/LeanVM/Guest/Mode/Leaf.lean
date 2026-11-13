module

public import LeanVM.Guest.Mode.Frame
public import LeanVM.Guest.Pack.«P0».Bundle

/-!
# The mode walk on a leaf (prototype)

`block_selector__L8`, a leaf of 82 instructions at `pc` 195516: three pointer arguments (frame
cells 2, 3, 4), two returned words (cells 5, 6). Entering with its header and arguments written and
the eight words behind each pointer written (its heap precondition, `pre`), the walk accepts its
code (`accepts`), its return `JUMP`'s cells written, and leaves its returned words written
(`returns`). `step` is the walk's step rule on it, as `InvRule` consumes it.
-/

namespace LeanVM.Guest.Mode.Leaf

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec LeanVM.Guest.Mode

@[expose] public section

/-- An offset-form instruction as the executor's instruction (a `KECCAK` left out here). -/
def opOfOff : OffsetInstruction → Option Op
  | .xor a b c => some (.xor a b c)
  | .mul a b c => some (.mul a b c)
  | .set o k0 k1 => some (.set o (OffsetInstruction.immediateWord k0 k1))
  | .deref a o c mode => some (.deref a o c mode)
  | .jump c d f => some (.jump c d f)
  | .keccak .. => none

/-- The leaf's instructions. -/
def ops : List Op := (Fn.«block_selector__L8».c0.mapM opOfOff).getD []

/-- Its heap precondition: words `0` to `7` behind each pointer argument. -/
def pre : List (ℕ × ℕ) := (List.range 8).flatMap fun o ↦ [(2, o), (3, o), (4, o)]

/-- What its walk knows at entry: the header, the arguments, the heap precondition. -/
def entry : Abs := ⟨[0, 1, 2, 3, 4], pre⟩

theorem length_ops : ops.length = 82 := by decide +kernel

/-- **The walk accepts the leaf.** -/
theorem accepts : (walkA entry ops).isSome = true := by decide +kernel

/-- Its returned words are written when it returns. -/
theorem returns : (walkA entry ops).map (fun B ↦ B.w.contains 5 && B.w.contains 6) = some true := by
  decide +kernel

/-- **The leaf's step rule**, on any executor context holding its code at its `pc`. -/
theorem step {C : Ctx} (hcode : ∀ k (hk : k < ops.length), C.ops[195516 + k]? = some ops[k])
    {s : St} {k : ℕ} {B : Abs} (hk : k < ops.length) (hpc : s.pc = 195516 + k)
    (hB : walkAt entry ops k = some B) (hs : s.Good) (hfp : s.fp < maxCells) (hH : Holds s B) :
    C.ops[s.pc]? = some ops[k] ∧ Reads s ops[k] ∧ ((∀ c d f, ops[k] ≠ .jump c d f) →
      ∀ s', runOp C s ops[k] = .ok s' → s'.pc = 195516 + (k + 1) ∧ s'.fp = s.fp ∧
        ∃ B', walkAt entry ops (k + 1) = some B' ∧ Holds s' B') :=
  walk_step hcode accepts hk hpc hB hs hfp hH

end

end LeanVM.Guest.Mode.Leaf
