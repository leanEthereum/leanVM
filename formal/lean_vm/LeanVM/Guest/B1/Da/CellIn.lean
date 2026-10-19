/-
  LeanVM.Guest.B1.Da.CellIn

  `da_verify_cell` loading from a region: the 256 words at `lvals`.
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Da.RelIn

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

/-- `da_verify_cell`'s atoms. -/
def vcAtoms : List Atom :=
  [.hint (.witness "da_symbols" (.stack ((List.range 256).map fun i => .n (i + 1))))] ++ vcPair0 ++
    (List.range 127).flatMap (fun e => vcPair (e + 1)) ++
    [.const (.n 1408) (word 13503953895743350343 11912009169889063794 0),
     .const (.n 1409) (word 11170449402626986623 6620516960021240235 0)] ++
    (List.range 32).flatMap vcBlk ++
    [.copy (.n 1506) (.n 1504), .copy (.n 1507) (.n 1505), .copy (.n 1508) (.n 1407)]

theorem vcBody_eq : vcBody = vcAtoms.map .atom ++ [.ret [.n 1506, .n 1507, .n 1508]] := rfl

theorem vc_loads : vcAtoms.filterMap atomLoad? = (List.range 256).map fun k => (.n 0, k) := by
  decide +kernel

/-- **`da_verify_cell(lvals)` loads the 256 words at `lvals`**, `lvals = g^l`: from a region holding
them it holds in that region. -/
theorem da_verify_cell_relIn {rd : Reader} {R : ℕ → Prop} {l : ℕ} (hR : ∀ k < 256, R (l + k))
    {rets : List E} (h : coreProgram.Rel rd "da_verify_cell" [gen ^ l] rets) :
    coreProgram.RelIn rd R "da_verify_cell" [gen ^ l] rets := by
  refine relIn_of_inv (fun f args => f = "da_verify_cell" ∧ args = [gen ^ l])
    (fun f args σ fn es vs hI hf hp hw _ => ?_) ⟨rfl, rfl⟩ h
  obtain ⟨rfl, rfl⟩ := hI
  rw [find_da_verify_cell, Option.some.injEq] at hf
  subst hf
  rw [vcBody_eq, walk_atoms] at hw
  obtain ⟨rfl, -⟩ : vcAtoms.map Ev.atom = es ∧ _ := by injection hw; exact ⟨by assumption, by assumption⟩
  have h0 : σ (.n 0) = gen ^ l := by simpa using hp
  refine ⟨fun A hA => ?_, fun c hc => absurd hc (by rw [calls_atoms]; simp)⟩
  rw [loadAddrs_atoms, vc_loads] at hA
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hA
  obtain ⟨k, hk, rfl⟩ := hA
  exact ⟨l + k, by rw [h0, limb0_gen_pow, gpow_add'], hR k hk⟩

end
end LeanVM.Guest.B1.Digest
