/-
  LeanVM.Guest.B1.Da.LoopIn

  A `mul_range` loop helper calling only itself, loading from a region, by its iterations.
-/

module

public import LeanVM.Guest.B1.Da.RowsIn

/-!
# Self-calling loops by region

`loop_relInT`: a loop helper `f` whose body is a straight run ending in its tail `callIf`, on
arguments `g^j :: ps` for `j < n`: if every iteration's loads are in `R`, its tail is taken
exactly before the last and passes `g^(j+1) :: ps`, then from `g^j` it is `RelInT` of
`(n - j)` frames and the skipped tail's.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)

@[expose] public section

theorem loop_relInT (fs : String → ℕ) {rd : Reader} {R : ℕ → Prop} {f : String} {fn : Fn}
    (hf : coreProgram.find? f = some fn) {pre : List Stmt} (hb : fn.body = pre ++ [.ret []])
    (hs : pre.all Main.Stmt.straight = true) {c : V} {targs : List V}
    (hcs : pre.filterMap Main.Stmt.callS = [(some c, f, targs, [])])
    (hal : pre.filterMap Main.Stmt.allocSz = []) {ps : List E} {n : ℕ} (hn : n < 2 ^ 33)
    (hit : ∀ j < n, ∀ σ : Val, fn.params.map σ = gen ^ j :: ps →
      (∀ e ∈ pre.flatMap (Main.slEvs σ), e.Ok (coreProgram.Rel rd) rd σ) →
      (∀ A ∈ loadAddrs σ (pre.flatMap (Main.slEvs σ)), ∃ i, A = gpow i ∧ R i) ∧
        (σ c ≠ 0 ↔ j + 1 < n) ∧ targs.map σ = gen ^ (j + 1) :: ps)
    {j : ℕ} (hj : j < n) (h : coreProgram.Rel rd f (gen ^ j :: ps) []) :
    RelInTW fs rd R ((n - j) * fs f + fs f) f (gen ^ j :: ps) [] fun θ => (n - j) * θ f + θ f := by
  have key := relInTW_of_inv fs (R := R) (fun f' args => f' = f ∧ ∃ j < n, args = gen ^ j :: ps)
    (fun θ _ args => (n - logG (args.headD 0)) * θ f + θ f)
    (fun f' args σ fn' es vs hI hf' hp hw hok => ?_) ⟨rfl, j, hj, rfl⟩ h
  · simpa [logG_gen_pow (show j < 2 ^ 64 - 1 by omega)] using key
  obtain ⟨rfl, j, hj, rfl⟩ := hI
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  rw [hb, Main.walk_straight σ _ _ hs] at hw
  obtain ⟨rfl, -⟩ : pre.flatMap (Main.slEvs σ) = es ∧ _ := by injection hw; exact ⟨by assumption, by assumption⟩
  obtain ⟨-, hal', -, hcl⟩ := Main.straight_parts σ _ hs
  obtain ⟨hld, htk, hta⟩ := hit j hj σ hp hok
  have hcalls : calls (pre.flatMap (Main.slEvs σ)) = [⟨f', targs, [], decide (σ c ≠ 0)⟩] := by
    rw [hcl, hcs]; rfl
  refine ⟨hld, fun c' hc' ht => ?_, ?_⟩
  · rw [hcalls] at hc'
    obtain rfl := List.mem_singleton.mp hc'
    simp only [decide_eq_true_eq] at ht
    exact ⟨rfl, j + 1, htk.mp ht, hta⟩
  · intro θ
    rw [hcalls, hal', hal, callsTot]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, List.headD_cons, hta]
    rw [logG_gen_pow (show j < 2 ^ 64 - 1 by omega)]
    by_cases hj1 : j + 1 < n
    · simp only [htk.mpr hj1, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
      rw [logG_gen_pow (show j + 1 < 2 ^ 64 - 1 by omega), show n - j = (n - (j + 1)) + 1 by omega]
      ring
    · have : ¬ σ c ≠ 0 := fun h => hj1 (htk.mp h)
      simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show n - j = 1 by omega]
      ring

end
end LeanVM.Guest.B1.Digest
