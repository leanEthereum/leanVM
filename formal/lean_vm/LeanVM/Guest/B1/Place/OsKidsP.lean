/-
  LeanVM.Guest.B1.Place.OsKidsP

  The callees of a straight-line body placed in sequence, per level a group of calls whose layout
  depends on where the group is placed (f128's `open_stacked`: the first squeeze's decoder and the
  squeeze loop).
-/

module

public import LeanVM.Guest.B1.Place.OsKidsB

/-!
# Callees in sequence, per level a placed group

`OsGroupD`, `OsGroupB`: a list of calls placed from any `b`, reading `Lin b` and claiming `Lout b` (within `B`
words).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A group of calls placed from any `b`**, reading `Lin b`, claiming `Lout b`. -/
def OsGroupD (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (cs : List Call)
    (Lin Lout : ℕ → Layout) : Prop :=
  ∀ b, ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧
    ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
      (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n (RegionL (Lout b))

/-- **`OsGroupD` within `B` words.** -/
def OsGroupB (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (σ : Val) (cs : List Call)
    (Lin Lout : ℕ → Layout) (B : ℕ) : Prop :=
  ∀ b, ∃ (n : ℕ) (Lown : Layout), Within (Lout b ++ Lown) b n ∧ DisjL (Lout b ++ Lown) ∧ n ≤ B ∧
    ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd → MemL rd (Lout b ++ Lown) → MemL rd (Lin b) →
      (∀ i, RegionL (Lin b) i → R i ∨ Dacc i) →
      KidsFromIn coreProgram fs cert rd σ R Dacc cs b n (RegionL (Lout b))

theorem OsGroupB.toD {κ : ℕ} {σ : Val} {cs : List Call} {Lin Lout : ℕ → Layout} {B : ℕ}
    (h : OsGroupB fs cert κ σ cs Lin Lout B) : OsGroupD fs cert κ σ cs Lin Lout := fun b ↦
  let ⟨n, Lown, hW, hD, _, hK⟩ := h b
  ⟨n, Lown, hW, hD, hK⟩

/-- A level's frames: the calls before the group, the group, the calls after it. -/
structure OsLvKP where
  A : List Call
  P : List Call
  B : List Call

/-- A level's frames in order. -/
def OsLvKP.calls (k : OsLvKP) : List Call := k.A ++ (k.P ++ k.B)

end
end LeanVM.Guest.B1
