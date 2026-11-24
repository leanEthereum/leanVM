/-
  LeanVM.Guest.Memory.UniformF

  The uniform placed completeness with the caller's words depending on the frame pointer
  (`CompleteAtF`), and a callee read at its frame pointer (`KidF`).
-/

module

public import LeanVM.Guest.Memory.Uniform

/-!
# Caller's words at the frame pointer

`CompleteAtD` fixes the caller's words `Lin` and quantifies over the frame pointer. A callee that
stores pointers into its own frame in its caller's memory (`keccak_layer` writes the addresses of
its buffers into its caller's record) reads caller's words that depend on where it is placed:
`CompleteAtF … Lin … Out`, with `Lin : ℕ → Layout` and the results' `Out` read at the frame
pointer (a caller ties its record's words to the callee's buffers there). `CompleteAtD` is the
constant case.

`kidsFromIn_of_kidsGB` (`B1/KeccakGkr/FlatGB.lean`) composes such callees along a caller's calls as
`kidsFromIn_of_kidsD` does, their frame pointers `fps` chosen before the memory, so the caller can
build its own words (the record) from them. A `KidF` is a callee read at its frame pointer
(`KidF.at`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **`f` is complete at every frame pointer `fp`, on disjoint layouts, reading the caller's words
`Lin fp`.** -/
def CompleteAtF (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Lin : ℕ → Layout) (args : List E) (Out : ℕ → List E → Layout → Prop) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out fp rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin fp) →
      RelAtIn coreProgram fs cert rd (RegionL (Lin fp)) (RegionL Lout) fp n f args rets

/-- A call whose caller's words depend on the callee's frame pointer. -/
structure KidF where
  f : String
  taken : Bool
  args : List E
  Lin : ℕ → Layout
  Out : ℕ → List E → Layout → Prop

/-- The call placed at `p`. -/
def KidF.at (k : KidF) (p : ℕ) : Kid := ⟨k.f, k.taken, k.args, k.Lin p, k.Out p⟩

variable {fs : String → ℕ} {cert : String → V → ℕ} {kfB : KidF → ℕ}

theorem CompleteAtF.mono {k k' : ℕ} {f : String} {Lin : ℕ → Layout} {args : List E}
    {Out : ℕ → List E → Layout → Prop} (h : CompleteAtF fs cert k' f Lin args Out) (hk : k' ≤ k) :
    CompleteAtF fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hm => hr rd (hl.mono hk) hm⟩

/-! ## Within bounds -/

/-- **`CompleteAtF` within `B` words**, before the memory. -/
def CompleteAtFB (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Lin : ℕ → Layout) (args : List E) (Out : ℕ → List E → Layout → Prop) (B : ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), n ≤ B ∧ Out fp rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin fp) →
      RelAtIn coreProgram fs cert rd (RegionL (Lin fp)) (RegionL Lout) fp n f args rets

theorem CompleteAtB.toFB {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtB fs cert k f Lin args Out B) :
    CompleteAtFB fs cert k f (fun _ => Lin) args (fun _ => Out) B := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩

end
end LeanVM.Guest.B1
