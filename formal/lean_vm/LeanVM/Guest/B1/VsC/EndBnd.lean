/-
  LeanVM.Guest.B1.VsC.EndBnd

  The blocks and steps a placed callee's end is made of, bounded when every frame is small.
-/

module

public import LeanVM.Guest.B1.VsC.SlowA
public import LeanVM.Guest.B1.VsC.LoopLeafA

/-!
# Callees' ends, bounded

`FsSmall fs`: every frame below `2^16` (`B2C.fs`'s, by `fs_lt16`). Under it a fresh frame's step
`allocBase a c + fs f` is within `2^17` of `c` (`step_le`), a loop's block over `n` iterations within
`(n + 1)·2^16` (`lpB_le`, `llBlk_le`), and a loop of leaf calls' end within `n·2^17` (`llEnd_le`).
`EndLe c β e`: the end `e` within `2^β` of the cursor `c` when `c < 2^60`, the bound `verify_sub`'s
windows ask of its callees (`VsWinHyp`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- Every frame below `2^16`. -/
def FsSmall (fs : String → ℕ) : Prop := ∀ f, fs f < 2 ^ 16

/-- A callee's end `e` within `2^β` of its cursor `c`, when the cursor is below `2^60`. -/
def EndLe (c β e : ℕ) : Prop := c < 2 ^ 60 → e ≤ c + 2 ^ β

theorem EndLe.of_le {c β e : ℕ} (h : e ≤ c + 2 ^ β) : EndLe c β e := fun _ => h

variable {fs : String → ℕ} {al : String → Bool}

/-- A fresh frame's step from the cursor. -/
theorem step_le (hfs : FsSmall fs) (a : Bool) (f : String) (c : ℕ) : allocBase a c + fs f ≤ c + 2 ^ 17 := by
  have := allocBase_le a c
  have := hfs f
  omega

/-- A loop's block over its iterations. -/
theorem lpB_le (hfs : FsSmall fs) (self : String) (Q j : ℕ) : lpB fs self Q j ≤ (Q - j + 1) * 2 ^ 16 := by
  unfold lpB
  have h1 := hfs self
  have h2 := hfs (tailKey self)
  have : (Q - j) * fs self ≤ (Q - j) * 2 ^ 16 := Nat.mul_le_mul_left _ h1.le
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- A loop's block over its iterations. -/
theorem llBlk_le (hfs : FsSmall fs) (self : String) (q j : ℕ) : llBlk fs self q j ≤ (q - j + 1) * 2 ^ 16 :=
  lpB_le hfs self q j

/-- An iteration of a step within `2^17`. -/
theorem iterate_le {g : ℕ → ℕ} (hg : ∀ x, g x ≤ x + 2 ^ 17) (n c : ℕ) : g^[n] c ≤ c + n * 2 ^ 17 := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have := ih (g c)
    have := hg c
    rw [Nat.succ_mul]
    omega

/-- A loop of leaf calls' end. -/
theorem llEnd_le (hfs : FsSmall fs) (leaf : String) (q j c : ℕ) :
    llEnd fs al leaf q j c ≤ c + (q - j) * 2 ^ 17 := by
  unfold llEnd
  exact iterate_le (g := llStep fs al leaf) (fun x => step_le hfs _ leaf x) _ c

/-- A loop of `residual_query_slow` calls' end. -/
theorem lpE_le (hfs : FsSmall fs) (rq : String) (Q j c : ℕ) : lpE fs al rq Q j c ≤ c + (Q - j) * 2 ^ 17 := by
  unfold lpE
  exact iterate_le (g := lpStep fs al rq) (fun x => step_le hfs _ rq x) _ c

end
end LeanVM.Guest.B1.VsC
