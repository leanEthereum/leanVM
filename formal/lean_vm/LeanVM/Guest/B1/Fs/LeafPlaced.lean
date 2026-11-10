/-
  LeanVM.Guest.B1.Fs.LeafPlaced

  Leaf callees, placed and bounded (`CompleteRelB`), from their `Rel`-level meaning and the kernel's
  check of their bodies (`LeafSpecOk`).
-/

module

public import LeanVM.Guest.Budget.LiftB
public import LeanVM.Guest.B1.Bits.GrindPlaced

/-!
# Leaf callees, placed and bounded

`totalLe_leaf`: a leaf's trees are its frame alone. `completeRelB_of_leaf`: a leaf whose relation
is its meaning `M`, on a precondition `Pre` implying `M` and fixing every word the leaf loads (one
word per load, across the memories `Pre` holds on), is `CompleteRelB … Pre B` for any bound `B` of
its trees: the fixed words lie in the caller's (`forced_load_region`), so the regions lift
(`completeRelRegDB_of_iff`) applies.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A leaf's trees are its frame.** -/
theorem totalLe_leaf {f : String} {spec : List (ℕ × ℕ)} (hok : LeafSpecOk f spec) :
    TotalLe coreProgram fs f fun _ => fs f := by
  obtain ⟨fn, hf, -, hleaf⟩ := hok
  intro rd t args rets hn hv hb
  cases t with
  | phantom => exact hv.elim
  | node g σ bufs kids =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn', hf', -, es, vs, hw, -, -, hkv⟩ := hv
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    have hall := Lift.walk_leafOk (σ := σ) _ hleaf
    rw [hw] at hall
    have hpure : ∀ e ∈ es, e.pure [g] := by
      have := walk_pure (σ := σ) fn.body
        (Lift.pureIn_of_leafOk hf hleaf g (List.mem_singleton_self _) fn hf)
      rwa [hw] at this
    rw [Lift.calls_nil_of_leafOk hall] at hkv
    rw [Tree.BufsOk, events_node hf hw, allocs_pure hpure] at hb
    obtain ⟨rfl, -⟩ := hb
    match kids, hkv with
    | [], _ => simp [total_node, Tree.totalKids]

/-- **A leaf callee, placed and bounded**: its relation its meaning `M`, on a precondition implying
`M` and fixing each word the leaf loads. -/
theorem completeRelB_of_leaf {f : String} {spec : List (ℕ × ℕ)}
    {M Pre : Reader → List E → List E → Prop} (hok : LeafSpecOk f spec)
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ M rd args rets)
    (hM : ∀ rd args rets, Pre rd args rets → M rd args rets)
    (hpin : ∀ args rets, ∀ q ∈ spec, ∀ t < q.2, ∃ w, ∀ rd, Pre rd args rets →
      LoadHolds rd (args.getD q.1 0) t w)
    (κ : ℕ) {B : ℕ} (hT : TotalLe coreProgram fs f fun _ => B) :
    CompleteRelB fs cert κ f Pre B := by
  intro args rets Lin hpre
  by_cases hex : ∃ rd, LowDef κ rd ∧ MemL rd Lin
  · obtain ⟨rd0, h0, hL0⟩ := hex
    have hreg : RegPtrs spec args (RegionL Lin) := fun q hq t ht => by
      obtain ⟨w, hw⟩ := hpin args rets q hq t ht
      exact forced_load_region h0 hL0 fun rd hl hL => hw rd (hpre rd hl hL)
    exact (completeRelRegDB_of_iff hok hiff κ hT args rets Lin hreg
      fun rd hl hL => hM _ _ _ (hpre rd hl hL)).toCompleteAtB
  · intro fp
    exact ⟨0, [], rets, [], ⟨rfl, rfl⟩, by simp [Within], disj_nil, Nat.zero_le _,
      fun rd hl hL => absurd ⟨rd, hl, by simpa using hL⟩ hex⟩

/-- **A leaf callee, placed, within its frame.** -/
theorem completeRelB_of_leaf' {f : String} {spec : List (ℕ × ℕ)}
    {M Pre : Reader → List E → List E → Prop} (hok : LeafSpecOk f spec)
    (hiff : ∀ rd args rets, coreProgram.Rel rd f args rets ↔ M rd args rets)
    (hM : ∀ rd args rets, Pre rd args rets → M rd args rets)
    (hpin : ∀ args rets, ∀ q ∈ spec, ∀ t < q.2, ∃ w, ∀ rd, Pre rd args rets →
      LoadHolds rd (args.getD q.1 0) t w) (κ : ℕ) :
    CompleteRelB fs cert κ f Pre (fs f) :=
  completeRelB_of_leaf hok hiff hM hpin κ (totalLe_leaf hok)

end
end LeanVM.Guest.B1
