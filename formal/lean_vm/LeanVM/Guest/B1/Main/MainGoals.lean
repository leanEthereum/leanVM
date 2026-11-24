/-
  LeanVM.Guest.B1.Main.MainGoals

  `main`'s honest oracle and words on an honest run, which its callees' placed completeness reads
  (`hLmain`).
-/

module

public import LeanVM.Guest.B1.Main.MainHonest
public import LeanVM.Guest.Data.NameStrings

/-!
# `main`'s callees on an honest run

`hm`, `hLmain`: `main`'s honest oracle and words at `fp` (its buffers `hOwn`, then
`exponent_tables`' table). `completeAtD_lin_mono` moves a callee's completeness to a larger caller
layout.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (CompleteAtD Returns bufL)

@[expose] public section

/-- A callee's completeness reading fewer words holds reading more. -/
theorem completeAtD_lin_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin Lin' : B1.Main.Layout} {args : List E} {Out : List E → B1.Main.Layout → Prop}
    (hm : ∀ rd, B1.Main.MemL rd Lin' → B1.Main.MemL rd Lin)
    (hr : ∀ i, B1.Main.RegionL Lin i → B1.Main.RegionL Lin' i)
    (h : CompleteAtD fs cert κ f Lin args Out) : CompleteAtD fs cert κ f Lin' args Out := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hM => (hR rd hl ?_).mono hr⟩
  rw [B1.Main.memL_append] at hM ⊢
  exact ⟨hM.1, hm rd hM.2⟩

variable (fs : String → ℕ) (cert : String → V → ℕ) (fp : ℕ) (seed : Digest) (s : NodeStatement)
  (w : NodeWitness)

/-- `main`'s honest oracle at `fp`. -/
abbrev hm : MainIn := (hData seed s w).toIn fs fp

/-- **`main`'s honest words at `fp`**: its buffers, then `exponent_tables`' table. -/
abbrev hLmain : B1.Main.Layout :=
  bufL (fp + fs "main") (mSizes (hData seed s w)) (hOwn seed s w) ++ etL (hData seed s w) fs fp

end
end LeanVM.Guest.B1.Main
