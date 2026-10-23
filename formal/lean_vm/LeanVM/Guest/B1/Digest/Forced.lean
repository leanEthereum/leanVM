/-
  LeanVM.Guest.B1.Digest.Forced

  Loads every memory holding the caller's words satisfies read those words; layout entries read
  back as cells.
-/

module

public import LeanVM.Guest.B1.Uniform
public import LeanVM.Guest.B1.Digest.Common

/-!
# Forced loads

`CompleteRel`'s precondition holds on every memory defined below `2^κ` and holding the caller's
words `Lin`. A load whose word the precondition pins (`forced_load`), or restricts to a predicate
some word fails (`forced_load_pred`), then reads `Lin`: a memory holding `Lin` and another word
there would fail the precondition. `load_agree`: such a word is the same in every such memory.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteRel CompleteRelD CompleteAtB Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## Forced loads -/

/-- **A forced load reads the layout**: if every memory defined below `2^κ` and holding `Lin` holds
at `p·g^k` a word of `Q`, some word is not in `Q`, and one such memory exists, the address is a
word of `Lin`: elsewhere a memory could hold the other word. -/
theorem forced_load_pred {κ : ℕ} {Lin : Layout} {p : E} {k : ℕ} {Q : E → Prop}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → ∃ v, LoadHolds rd p k v ∧ Q v) {x : E} (hx : ¬ Q x)
    {rd1 : Reader} (h1 : LowDef κ rd1) (h1' : MemL rd1 Lin) : ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i := by
  classical
  by_contra hne
  have hne' : ∀ i, p.limb 0 * gpow k = gpow i → ¬ RegionL Lin i := fun i h hr => hne ⟨i, h, hr⟩
  let rd' : Reader := Function.update rd1 (p.limb 0 * gpow k) (some x)
  have hl' : LowDef κ rd' := fun i hi => by
    by_cases h : gpow i = p.limb 0 * gpow k
    · simp only [rd', h, Function.update_self, Option.isSome_some]
    · simp only [rd', Function.update_of_ne h]; exact h1 i hi
  have hL' : MemL rd' Lin := fun q hq k' hk' => by
    have h0 := h1' q hq k' hk'
    refine ⟨h0.1, ?_⟩
    have hA : (ofK (gpow q.1)).limb 0 * gpow k' ≠ p.limb 0 * gpow k := by
      rw [Main.addr_ofK]
      exact fun h => hne' _ h.symm ⟨q, hq, by omega, by omega⟩
    simp only [rd', Function.update_of_ne hA]
    exact h0.2
  obtain ⟨v, hv, hq⟩ := hall rd' hl' hL'
  have h2 := hv.2
  simp only [rd', Function.update_self, Option.some.injEq] at h2
  exact hx (h2 ▸ hq)

/-- **A forced load reads the layout**: every memory defined below `2^κ` and holding `Lin` holds
`v` at `p·g^k`, and one such memory exists. -/
theorem forced_load {κ : ℕ} {Lin : Layout} {p : E} {k : ℕ} {v : E}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → LoadHolds rd p k v) {rd1 : Reader} (h1 : LowDef κ rd1)
    (h1' : MemL rd1 Lin) : ∃ i, p.limb 0 * gpow k = gpow i ∧ RegionL Lin i :=
  forced_load_pred (Q := (· = v)) (x := v + 1) (fun rd hl hL => ⟨v, hall rd hl hL, rfl⟩)
    (fun h => one_ne_zero (add_eq_left.mp h)) h1 h1'

/-- **A forced word is the same in every such memory**: at an address of `Lin`, both memories hold
`Lin`'s word. -/
theorem load_agree {Lin : Layout} {rd rd1 : Reader} (h : MemL rd Lin) (h1 : MemL rd1 Lin) {p : E} {k i : ℕ}
    (hi : p.limb 0 * gpow k = gpow i) (hR : RegionL Lin i) {v : E} (hv : LoadHolds rd1 p k v) :
    LoadHolds rd p k v :=
  ⟨hv.1, by rw [hi, Main.memL_agree h h1 i hR, ← hi]; exact hv.2⟩

/-- A layout entry of single words pinned at the addresses `p·g^k`. -/
theorem load_of_pin {rd : Reader} {L : Layout} (h : MemL rd L) {p : E} (hp : IsInK p) {k i : ℕ}
    (hi : p.limb 0 * gpow k = gpow i) {v : E} (hq : (i, [v]) ∈ L) : LoadHolds rd p k v := by
  have := (h _ hq 0 (by simp)).2
  rw [Main.addr_ofK, Nat.add_zero] at this
  exact ⟨hp, by rw [hi]; exact this⟩

/-- **`CompleteRel` is antitone in the precondition.** -/
theorem completeRel_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Pre Pre' : Reader → List E → List E → Prop} (h : CompleteRel fs cert κ f Pre)
    (hP : ∀ rd args rets, Pre' rd args rets → Pre rd args rets) : CompleteRel fs cert κ f Pre' :=
  fun args rets Lin hpre => h args rets Lin fun rd hl hL => hP rd args rets (hpre rd hl hL)

/-- **`CompleteRelD` is antitone in the precondition.** -/
theorem completeRel_monoD {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Pre Pre' : Reader → List E → List E → Prop} (h : CompleteRelD fs cert κ f Pre)
    (hP : ∀ rd args rets, Pre' rd args rets → Pre rd args rets) : CompleteRelD fs cert κ f Pre' :=
  fun args rets Lin hpre => h args rets Lin fun rd hl hL => hP rd args rets (hpre rd hl hL)

/-- Bounded `CompleteRel` is antitone in the precondition. -/
theorem completeRel_monoB {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Pre Pre' : Reader → List E → List E → Prop} {B : List E → ℕ}
    (h : ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → Pre rd args rets) →
      CompleteAtB fs cert κ f Lin args (Returns rets) (B args))
    (hP : ∀ rd args rets, Pre' rd args rets → Pre rd args rets) :
    ∀ (args rets : List E) (Lin : Layout), (∀ rd, LowDef κ rd → MemL rd Lin → Pre' rd args rets) →
      CompleteAtB fs cert κ f Lin args (Returns rets) (B args) :=
  fun args rets Lin hpre => h args rets Lin fun rd hl hL => hP rd args rets (hpre rd hl hL)

/-! ## Layout entries -/

theorem cells_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {x : ℕ} {cs : List E} (hq : (x, cs) ∈ L) :
    CellsAt rd (gen ^ x) cs := by
  rw [gen_pow_eq_ofK]; exact h _ hq

theorem load_of_memL {rd : Reader} {L : Layout} (h : MemL rd L) {x : ℕ} {v : E} (hq : (x, [v]) ∈ L) :
    LoadHolds rd (gen ^ x) 0 v :=
  cells_of_memL h hq 0 (by simp)

end
end LeanVM.Guest.B1.Digest
