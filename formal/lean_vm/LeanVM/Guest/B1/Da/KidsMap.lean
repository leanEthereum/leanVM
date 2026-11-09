/-
  LeanVM.Guest.B1.Da.KidsMap

  Callees given as a map over a list (a function's loops, one per bit): their bounds, their frames'
  match, their regions.
-/

module

public import LeanVM.Guest.Budget.Bounded

/-!
# Callees over a list

`kidsDTB_map`: callees `kf i`, `i ∈ l`, each entered and complete within `B i` by a tree of `True`.
`kidsBoundL_map`: their bound is `Σ B i`. `callsMatch_map`: their frames match calls `cf i` whose
arguments are theirs and whose results are none. `regionsOk_map`: each reads within `R`.
`memL_lins_map`: what they read.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 (CompleteAtDTB KidsDTB kidsBoundL Kid CallsMatch OutsOk RegionsOk Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {ι : Type}

theorem kidsDTB_map {κ : ℕ} (kf : ι → Kid) (B : ι → ℕ) :
    ∀ l : List ι, (∀ i ∈ l, (kf i).taken = true →
      CompleteAtDTB fs cert κ (kf i).f (kf i).Lin (kf i).args (kf i).Out (fun _ => True) (B i)) →
      KidsDTB fs cert κ (l.map kf) (l.map fun _ => fun _ => True) (l.map B)
  | [], _ => trivial
  | i :: l, h => ⟨h i List.mem_cons_self, kidsDTB_map kf B l fun j hj => h j (List.mem_cons_of_mem _ hj)⟩

theorem kidsBoundL_map (kf : ι → Kid) (B : ι → ℕ) :
    ∀ l : List ι, (∀ i ∈ l, (kf i).taken = true) → kidsBoundL fs (l.map kf) (l.map B) = (l.map B).sum
  | [], _ => rfl
  | i :: l, h => by
    simp only [List.map_cons, kidsBoundL, h i List.mem_cons_self, ↓reduceIte, List.headD_cons,
      List.tail_cons, List.sum_cons]
    rw [kidsBoundL_map kf B l fun j hj => h j (List.mem_cons_of_mem _ hj)]

theorem callsMatch_map {σ : Val} (cf : ι → Call) (kf : ι → Kid) :
    ∀ (l : List ι) (outs : List (List E × Layout)), outs.length = l.length →
      OutsOk (l.map kf) outs →
      (∀ i ∈ l, (cf i).f = (kf i).f ∧ (cf i).taken = (kf i).taken ∧ (kf i).Out = Returns [] ∧
        (cf i).rets = [] ∧ ((kf i).taken = true → (cf i).args.map σ = (kf i).args)) →
      CallsMatch σ (l.map cf) (l.map kf) outs
  | [], [], _, _, _ => trivial
  | i :: l, o :: os, hlen, ⟨ho, hos⟩, h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h i List.mem_cons_self
    refine ⟨h1, h2, fun ht => ⟨h5 ht, ?_⟩, callsMatch_map cf kf l os (by simpa using hlen) hos
      fun j hj => h j (List.mem_cons_of_mem _ hj)⟩
    have := ho ht
    rw [h3] at this
    rw [h4, this.1]
    rfl
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen

theorem outsOk_length (kf : ι → Kid) : ∀ (l : List ι) (outs : List (List E × Layout)),
    OutsOk (l.map kf) outs → outs.length = l.length
  | [], [], _ => rfl
  | _ :: l, _ :: os, ⟨_, h⟩ => by simp [outsOk_length kf l os h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem regionsOk_map {R : ℕ → Prop} (kf : ι → Kid) :
    ∀ (l : List ι) (Dacc : ℕ → Prop) (outs : List (List E × Layout)),
      (∀ i ∈ l, ∀ j, RegionL (kf i).Lin j → R j) → RegionsOk R Dacc (l.map kf) outs
  | [], _, _, _ => trivial
  | _ :: _, _, [], _ => trivial
  | i :: l, _, _ :: os, h => ⟨fun _ j hj => Or.inl (h i List.mem_cons_self j hj),
      regionsOk_map kf l _ os fun k hk => h k (List.mem_cons_of_mem _ hk)⟩

theorem memL_lins_map {rd : Reader} (kf : ι → Kid) (l : List ι)
    (h : ∀ i ∈ l, MemL rd (kf i).Lin) : MemL rd (Kid.lins (l.map kf)) := by
  intro q hq
  simp only [Kid.lins, List.flatMap_map, List.mem_flatMap] at hq
  obtain ⟨i, hi, hq⟩ := hq
  exact h i hi q hq

end
end LeanVM.Guest.B1.Da
