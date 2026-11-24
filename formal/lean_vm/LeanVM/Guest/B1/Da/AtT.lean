/-
  LeanVM.Guest.B1.Da.AtT

  Helpers for `da_verify`'s honest shapes (`Budget.NodeHonest`): callees without predicates,
  the trivial predicates, data and layout monotonicity of the placed relations with trees.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.B1.Da.AtBase

/-!
# Helpers for honest shapes

`relAtInT_dmono`: as `relAtIn_dmono`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtDT)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem relAtInT_dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {T : Tree → Prop}
    (h : RelAtInT coreProgram fs cert rd R D fp n f args rets T) (hD : ∀ i, D' i → D i) :
    RelAtInT coreProgram fs cert rd R D' fp n f args rets T :=
  let ⟨t, ⟨hn, hv, hb, hp, ht, hl, hd⟩, hT⟩ := h
  ⟨t, ⟨hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi)⟩, hT⟩

end
end LeanVM.Guest.B1.Da
