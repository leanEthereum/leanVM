/-
  LeanVM.Guest.B1.Whir.CLoop

  `mul_range` loop helpers, honestly: a loop whose every iteration's body holds is a call.
-/

module

public import LeanVM.Guest.B1.Whir.Loops

/-!
# Loops, honestly

`allOk_relN`: a flat block holding under the program's relation holds at a finite depth.
`loop_complete`: a `mul_range` helper whose body (flat atoms and calls, then its tail's
`callIf` and `ret`) holds at every `g^j`, `j < n`, `0 < n < ord g`, with the guard `x·g + N` and the
next arguments `x·g :: N :: rest`, holds of `1 :: g^n :: rest` (its entry behind the guard).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **A flat block at a finite depth.** -/
theorem allOk_relN {σ : Val} : ∀ (A : List Stmt), A.all Stmt.flat = true →
    AllOk (coreProgram.Rel rd) rd σ A → ∃ D, AllOk (coreProgram.relN rd D) rd σ A
  | [], _, _ => ⟨0, allOk_nil⟩
  | s :: A, hf, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    rw [allOk_cons] at h
    obtain ⟨D, hD⟩ := allOk_relN A hf.2 h.2
    match s, hf.1, h.1 with
    | .atom a, _, ha => exact ⟨D, allOk_cons.mpr ⟨ha, hD⟩⟩
    | .call f args rets, _, ⟨d, hd⟩ =>
      exact ⟨max D d, allOk_cons.mpr ⟨relN_mono coreProgram (le_max_right D d) _ _ _ hd,
        allOk_mono (relN_mono coreProgram (le_max_left D d)) hD⟩⟩
    | .callIf c f args, _, ⟨hK, hc⟩ =>
      by_cases h0 : σ c ≠ 0
      · obtain ⟨d, hd⟩ := hc h0
        exact ⟨max D d, allOk_cons.mpr ⟨⟨hK, fun _ ↦ relN_mono coreProgram (le_max_right D d) _ _ _ hd⟩,
          allOk_mono (relN_mono coreProgram (le_max_left D d)) hD⟩⟩
      · exact ⟨D, allOk_cons.mpr ⟨⟨hK, fun h ↦ absurd h h0⟩, hD⟩⟩

/-- **A loop, honestly**: its body holding at every iteration, entered behind its guard. -/
theorem loop_complete {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {A : List Stmt} (hflat : A.all Stmt.flat = true) {c : ℕ} {args : List V}
    (hb : fn.body = A ++ [.callIf (.n c) f args, .ret []]) {N : E} {rest : List E} {n : ℕ}
    (hn0 : 0 < n) (hN : N = gen ^ n)
    (hstep : ∀ j < n, ∃ σ : Val, fn.params.map σ = gen ^ j :: N :: rest ∧
      AllOk (coreProgram.Rel rd) rd σ A ∧ σ (.n c) = gen ^ j * gen + N ∧
      args.map σ = gen ^ j * gen :: N :: rest) :
    IsInK (1 + N) ∧ (1 + N ≠ 0 → coreProgram.Rel rd f (1 :: N :: rest) []) := by
  have hK : ∀ j, IsInK (gen ^ j * gen + N) := fun j ↦ by
    rw [hN]; exact isInK_add (isInK_mul (gen_pow_isInK j) (by simpa using gen_pow_isInK 1))
      (gen_pow_isInK _)
  have key : ∀ i, i < n → ∃ d, coreProgram.relN rd d f (gen ^ (n - 1 - i) :: N :: rest) [] := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨σ, hp, hA, hc, ha⟩ := hstep (n - 1) (by omega)
      obtain ⟨D, hD⟩ := allOk_relN A hflat hA
      refine ⟨D + 1, (relN_succ_iff hf D _ _).mpr ⟨σ, hp, ?_⟩⟩
      rw [hb, show A ++ [.callIf (.n c) f args, .ret []] = (A ++ [.callIf (.n c) f args]) ++ [.ret []]
        by simp, holdsList_flat_ret _ (by simp [hflat, Stmt.flat])]
      refine ⟨allOk_append.mpr ⟨hD, ?_⟩, rfl⟩
      have h0 : σ (.n c) = 0 := by
        rw [hc, hN, gen_pow_mul_gen, show n - 1 + 1 = n by omega]
        exact CharTwo.add_self_eq_zero _
      refine allOk_cons.mpr ⟨⟨by rw [hc]; exact hK _, fun h ↦ absurd h0 h⟩, allOk_nil⟩
    | succ i ih =>
      intro hi
      obtain ⟨d', hd'⟩ := ih (by omega)
      obtain ⟨σ, hp, hA, hc, ha⟩ := hstep (n - 1 - (i + 1)) (by omega)
      obtain ⟨D, hD⟩ := allOk_relN A hflat hA
      refine ⟨max D d' + 1, (relN_succ_iff hf (max D d') _ _).mpr ⟨σ, hp, ?_⟩⟩
      rw [hb, show A ++ [.callIf (.n c) f args, .ret []] = (A ++ [.callIf (.n c) f args]) ++ [.ret []]
        by simp, holdsList_flat_ret _ (by simp [hflat, Stmt.flat])]
      refine ⟨allOk_append.mpr ⟨allOk_mono (relN_mono coreProgram (le_max_left D d')) hD, ?_⟩, rfl⟩
      refine allOk_cons.mpr ⟨⟨by rw [hc]; exact hK _, fun _ ↦ ?_⟩, allOk_nil⟩
      rw [ha, gen_pow_mul_gen, show n - 1 - (i + 1) + 1 = n - 1 - i by omega]
      exact relN_mono coreProgram (le_max_right D d') _ _ _ hd'
  refine ⟨by
    rw [hN]; exact isInK_add (by rw [← pow_zero gen]; exact gen_pow_isInK 0) (gen_pow_isInK n),
    fun _ ↦ ?_⟩
  obtain ⟨d, hd⟩ := key (n - 1) (by omega)
  rw [show n - 1 - (n - 1) = 0 by omega, pow_zero] at hd
  exact ⟨d, hd⟩

end
end LeanVM.Guest.B1.Whir
