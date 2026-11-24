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

`kidsT_true`: trivial predicates hold of any callees. `relAtInT_dmono`,
`completeAtDT_lin_mono`: as `relAtIn_dmono`, `completeAtD_lin_mono`.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Budget (NodeHonest)
open LeanVM.Guest.B1 (CompleteAtDT)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsT_true : ∀ (cs : List Call) (ks : List Tree) (n : ℕ),
    KidsT cs (List.replicate n fun _ => True) ks
  | [], _, _ => trivial
  | _ :: _, _, 0 => trivial
  | _ :: _, [], _ + 1 => trivial
  | _ :: cs, _ :: ks, n + 1 => ⟨fun _ => trivial, kidsT_true cs ks n⟩

theorem relAtInT_dmono {rd : Reader} {R D D' : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {T : Tree → Prop}
    (h : RelAtInT coreProgram fs cert rd R D fp n f args rets T) (hD : ∀ i, D' i → D i) :
    RelAtInT coreProgram fs cert rd R D' fp n f args rets T :=
  let ⟨t, ⟨hn, hv, hb, hp, ht, hl, hd⟩, hT⟩ := h
  ⟨t, ⟨hn, hv, hb, hp, ht, hl, fun i hi => hd i (hD i hi)⟩, hT⟩

/-- A callee's completeness reading fewer words holds reading more. -/
theorem completeAtDT_lin_mono {κ : ℕ} {f : String} {Lin Lin' : Layout} {args : List E}
    {Out : List E → Layout → Prop} {T : Tree → Prop}
    (hm : ∀ rd, MemL rd Lin' → MemL rd Lin) (hr : ∀ i, RegionL Lin i → RegionL Lin' i)
    (h : CompleteAtDT fs cert κ f Lin args Out T) : CompleteAtDT fs cert κ f Lin' args Out T := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun rd hl hM => ?_⟩
  obtain ⟨t, ⟨hn, hv, hb, hp, ht, hlo, hdd⟩, hT⟩ := hR rd hl (by
    rw [memL_append] at hM ⊢; exact ⟨hM.1, hm rd hM.2⟩)
  exact ⟨t, ⟨hn, hv, hb, hp, ht, loadsIn_mono t _ hr hlo, hdd⟩, hT⟩

end
end LeanVM.Guest.B1.Da
