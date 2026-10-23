/-
  LeanVM.Guest.B1.Da.CellIn

  `da_verify_cell` loading from a region: the 256 words at `lvals`.
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Da.WeightIn

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

/-- An instance of `da_verify_cell(g^l)`: it loads `g^(l+k)`, `k < 256`, and calls and allocates
nothing. -/
theorem vc_inst {σ : Val} {fn : Fn} {es : List Ev} {vs : List V} {l : ℕ}
    (hf : coreProgram.find? "da_verify_cell" = some fn) (hp : fn.params.map σ = [gen ^ l])
    (hw : walk σ fn.body = .ret es vs) :
    (∀ A ∈ loadAddrs σ es, ∃ i, A = gpow i ∧ l ≤ i ∧ i < l + 256) ∧ calls es = [] ∧ allocs σ es = [] := by
  rw [find_da_verify_cell, Option.some.injEq] at hf
  subst hf
  rw [vcBody_eq, walk_atoms] at hw
  obtain ⟨rfl, -⟩ : vcAtoms.map Ev.atom = es ∧ _ := by injection hw; exact ⟨by assumption, by assumption⟩
  have h0 : σ (.n 0) = gen ^ l := by simpa using hp
  refine ⟨fun A hA => ?_, calls_atoms _, allocs_atoms σ (by decide +kernel)⟩
  rw [loadAddrs_atoms, vc_loads] at hA
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hA
  obtain ⟨k, hk, rfl⟩ := hA
  exact ⟨l + k, by rw [h0, limb0_gen_pow, gpow_add'], by omega, by omega⟩

/-- **`da_verify_cell(lvals)` loads the 256 words at `lvals`**, `lvals = g^l`: from a region holding
them it holds in that region, by a tree of its frame. -/
theorem da_verify_cell_relInT (fs : String → ℕ) {rd : Reader} {R : ℕ → Prop} {l : ℕ}
    (hR : ∀ k < 256, R (l + k)) {rets : List E} (h : coreProgram.Rel rd "da_verify_cell" [gen ^ l] rets) :
    RelInTW fs rd R (fs "da_verify_cell") "da_verify_cell" [gen ^ l] rets fun θ => θ "da_verify_cell" := by
  refine relInTW_of_inv fs (fun f args => f = "da_verify_cell" ∧ args = [gen ^ l]) (fun θ f _ => θ f)
    (fun f args σ fn es vs hI hf hp hw _ => ?_) ⟨rfl, rfl⟩ h
  obtain ⟨rfl, rfl⟩ := hI
  obtain ⟨hl, hc, ha⟩ := vc_inst hf hp hw
  refine ⟨fun A hA => ?_, fun c hc' => by rw [hc] at hc'; simp at hc', fun θ => by rw [hc, ha]; rfl⟩
  obtain ⟨i, hi, h1, h2⟩ := hl A hA
  exact ⟨i, hi, by have := hR (i - l) (by omega); rwa [show l + (i - l) = i by omega] at this⟩

end
end LeanVM.Guest.B1.Digest
