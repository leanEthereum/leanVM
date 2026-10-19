/-
  LeanVM.Guest.Memory.SizeTransfer

  Words and weights of valid trees depend only on the frame sizes of the functions their paths
  call: bounds transfer between frame sizes agreeing there.
-/

module

public import LeanVM.Guest.Memory.SizeTotal

/-!
# Transferring bounds between frame sizes

A valid tree of a function of `S`, the paths of `S`'s functions calling only functions of `S`
(`CallsIn`), names only functions of `S`, its phantoms included. So its words and its weight are the
same at two frame sizes (two weights) agreeing on the functions of `S` in the program (a valid
tree's instances and phantoms are the program's) (`total_congr`, `weight_congr`), and
`TotalLe`, `TotalLeOn` and `WeightLe` transfer (`totalLe_transfer`, `totalLeOn_transfer`,
`weightLe_transfer`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {P : Core.Program} {S : String → Prop} {rd : Reader}

section Congr

variable {fs fs' : String → ℕ}

mutual
/-- **The words of a tree of `S` at two frame sizes agreeing on `S`.** -/
theorem total_congr (hc : CallsIn P S) (hS : ∀ g, S g → ∀ fn, P.find? g = some fn → fs g = fs' g) :
    ∀ (t : Tree) {args rets : List E}, S t.name → t.Valid P rd args rets → t.total fs = t.total fs'
  | .node f σ bufs kids, args, rets, hs, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      rw [Tree.total, Tree.total, hS f hs fn hf, totalKids_congr hc hS kids hk (hc f hs fn hf σ es vs hw)]
  | .phantom .., _, _, _, hv => hv.elim

theorem totalKids_congr (hc : CallsIn P S) (hS : ∀ g, S g → ∀ fn, P.find? g = some fn → fs g = fs' g) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValid P rd σ cs ks → (∀ c ∈ cs, S c.f) →
      Tree.totalKids fs ks = Tree.totalKids fs' ks
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      rw [Tree.totalKids, Tree.totalKids,
        totalKids_congr hc hS ks hv' fun c' h => hs c' (List.mem_cons_of_mem _ h)]
      congr 1
      have hkn : S k.name := hn ▸ hs c List.mem_cons_self
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        exact total_congr hc hS k hkn hk
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, fn', hfn', -⟩ := hk
        simp only [Tree.name] at hkn hfn'
        rw [Tree.total, Tree.total, hS f' hkn fn' hfn']
end

end Congr

section WCongr

variable {ω ω' : String → ℕ}

mutual
/-- **The weight of a tree of `S` at two weights agreeing on `S`.** -/
theorem weight_congr (hc : CallsIn P S) (hS : ∀ g, S g → ∀ fn, P.find? g = some fn → ω g = ω' g) :
    ∀ (t : Tree) {args rets : List E}, S t.name → t.Valid P rd args rets → t.weight ω = t.weight ω'
  | .node f σ bufs kids, args, rets, hs, hv => by
      obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv
      rw [Tree.weight, Tree.weight, hS f hs fn hf, weightKids_congr hc hS kids hk (hc f hs fn hf σ es vs hw)]
  | .phantom .., _, _, _, hv => hv.elim

theorem weightKids_congr (hc : CallsIn P S) (hS : ∀ g, S g → ∀ fn, P.find? g = some fn → ω g = ω' g) :
    ∀ (ks : List Tree) {σ : Val} {cs : List Call}, Tree.KidsValid P rd σ cs ks → (∀ c ∈ cs, S c.f) →
      Tree.weightKids ω ks = Tree.weightKids ω' ks
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, hv, _ => hv.elim
  | _ :: _, _, [], hv, _ => hv.elim
  | k :: ks, σ, c :: cs, hv, hs => by
      obtain ⟨hn, hk, hv'⟩ := hv
      rw [Tree.weightKids, Tree.weightKids,
        weightKids_congr hc hS ks hv' fun c' h => hs c' (List.mem_cons_of_mem _ h)]
      congr 1
      have hkn : S k.name := hn ▸ hs c List.mem_cons_self
      by_cases ht : c.taken = true
      · simp only [ht, ↓reduceIte] at hk
        exact weight_congr hc hS k hkn hk
      · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hk
        obtain ⟨⟨f', σ', rfl⟩, -⟩ := hk
        rfl
end

end WCongr

variable {fs fs' ω ω' : String → ℕ} {f : String}

/-- **`TotalLe` transfers** between frame sizes agreeing on `S`. -/
theorem totalLe_transfer (hc : CallsIn P S) (hS : ∀ g, S g → ∀ fn, P.find? g = some fn → fs g = fs' g) (hf : S f)
    {B : List E → ℕ} (h : TotalLe P fs f B) : TotalLe P fs' f B :=
  fun rd t args rets hn hv hb => by
    rw [← total_congr hc hS t (hn ▸ hf) hv]; exact h rd t args rets hn hv hb

/-- **`TotalLeOn` transfers** between frame sizes agreeing on `S`. -/
theorem totalLeOn_transfer (hc : CallsIn P S) (hS : ∀ g, S g → ∀ fn, P.find? g = some fn → fs g = fs' g) (hf : S f)
    {Pre : List E → Prop} {B : List E → ℕ} (h : TotalLeOn P fs f Pre B) : TotalLeOn P fs' f Pre B :=
  fun rd t args rets hn hp hv hb => by
    rw [← total_congr hc hS t (hn ▸ hf) hv]; exact h rd t args rets hn hp hv hb

/-- **`WeightLe` transfers** between weights agreeing on `S`. -/
theorem weightLe_transfer (hc : CallsIn P S) (hS : ∀ g, S g → ∀ fn, P.find? g = some fn → ω g = ω' g) (hf : S f)
    {B : List E → ℕ} (h : WeightLe P ω f B) : WeightLe P ω' f B :=
  fun rd t args rets hn hv hb => by
    rw [← weight_congr hc hS t (hn ▸ hf) hv]; exact h rd t args rets hn hv hb

end
end LeanVM.Guest.Memory
