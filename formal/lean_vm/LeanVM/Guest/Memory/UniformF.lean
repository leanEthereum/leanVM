/-
  LeanVM.Guest.Memory.UniformF

  The uniform placed completeness with the caller's words depending on the frame pointer
  (`CompleteAtF`), and its composition along a caller's calls (`kidsFromIn_of_kidsF`).
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
constant case (`CompleteAtD.toF`).

`kidsFromIn_of_kidsF` composes such callees along a caller's calls as `kidsFromIn_of_kidsD`
does, and returns the callees' frame pointers `fps`, chosen before the memory, so the caller can
build its own words (the record) from them: the callees are `KidF.atAll ks fps`, each `KidF`
read at its frame pointer (`KidF.at`).
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

/-- The calls placed at `fps`. -/
def KidF.atAll (ks : List KidF) (fps : List ℕ) : List Kid := List.zipWith KidF.at ks fps

/-- A call with fixed caller's words. -/
def Kid.toF (k : Kid) : KidF := ⟨k.f, k.taken, k.args, fun _ => k.Lin, fun _ => k.Out⟩

theorem Kid.toF_at (k : Kid) (p : ℕ) : k.toF.at p = k := rfl

variable {fs : String → ℕ} {cert : String → V → ℕ} {kfB : KidF → ℕ}

theorem CompleteAtD.toF {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} (h : CompleteAtD fs cert k f Lin args Out) :
    CompleteAtF fs cert k f (fun _ => Lin) args (fun _ => Out) := h

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

theorem CompleteAtFB.toF {k : ℕ} {f : String} {Lin : ℕ → Layout} {args : List E}
    {Out : ℕ → List E → Layout → Prop} {B : ℕ} (h : CompleteAtFB fs cert k f Lin args Out B) :
    CompleteAtF fs cert k f Lin args Out := fun fp =>
  let ⟨n, Lown, rets, Lout, _, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩

theorem CompleteAtB.toFB {k : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} (h : CompleteAtB fs cert k f Lin args Out B) :
    CompleteAtFB fs cert k f (fun _ => Lin) args (fun _ => Out) B := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hr⟩

/-- The callees' words: an entered call's bound, another's frame. -/
def kidsFBound (fs : String → ℕ) (kfB : KidF → ℕ) : List KidF → ℕ
  | k :: ks => (if k.taken then kfB k else fs k.f) + kidsFBound fs kfB ks
  | [] => 0

end
end LeanVM.Guest.B1
