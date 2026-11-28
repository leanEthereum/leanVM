/-
  LeanVM.Guest.Complete.EndBound

  Callees' ends, bounded: every compiled frame is below `2^16`, and a callee placed with an explicit
  end gives `AtEveryB`.
-/

module

public import LeanVM.Guest.Complete.MainCalleesA
public import LeanVM.Guest.Complete.LoopFA
public import LeanVM.Guest.Complete.FsSmall

/-!
# Callees' ends, bounded

Every frame size is below `2^16` (`fs_lt16`), so a callee's words past its cursor are bounded by its
loops' iterations. `AtEveryB.mono_post`. `lpBlk_le16`, `allocStep_le`: the blocks and steps the
producers' ends are made of.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Prover.Exec (allocBase)

@[expose] public section

/-- A loop helper's block over `n` iterations. -/
theorem lpBlk_le16 (f : String) (n : ℕ) : lpBlk B2C.fs f n ≤ n * 2 ^ 16 + 2 ^ 16 :=
  lpBlk_le16' fs_lt16 f n

/-- A fresh frame's cursor: its base and its frame. -/
theorem allocStep_le (a : Bool) (f : String) (c : ℕ) : allocBase a c + B2C.fs f ≤ c + 2 ^ 17 := by
  have := allocBase_le a c
  have := fs_lt16 f
  omega

variable {al : String → Bool} {k : ℕ} {f : String} {args rets : List E} {R : ℕ → Prop}
  {Pre : Reader → Prop} {Post : Reader → Tree → Prop} {B lo T β : ℕ}

theorem AtEveryB.mono_post {Q : Reader → Tree → Prop} (h : AtEveryB al k f args rets R Pre Post B lo T β)
    (hq : ∀ rd t, Post rd t → Q rd t) : AtEveryB al k f args rets R Pre Q B lo T β :=
  fun fp cur h1 h2 => let ⟨e, hb, he⟩ := h fp cur h1 h2
    ⟨e, hb, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h) fun rd t _ hq' => hq rd t hq'⟩

end
end LeanVM.Guest.Complete
