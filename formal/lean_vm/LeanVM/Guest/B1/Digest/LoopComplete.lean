/-
  LeanVM.Guest.B1.Digest.LoopComplete

  A `mul_range` loop helper, completely: its block holding at every counter `g^j`, `j < m`, gives
  the loop's relation to its end `g^m`.
-/

module

public import LeanVM.Guest.B1.Digest.Loops

/-!
# Loops, completely

`loopF_complete`: a helper of `loopShapeF` shape (a flat block, then `callIf (x·g + N) self
[x·g, N, …]`, `ret []`) holds at `g^k`, `k < m`, when `N = g^m` and its block holds at every
`g^j`, `k ≤ j < m` (the converse of `loop_stepF`). `guard_complete`: the guard of its call site,
`callIf (1 + N) f [1, N, …]`.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- **A flat block holds**, each statement holding, then the continuation. -/
theorem holdsList_flat_of {C : CallRel} {σ : Val} :
    ∀ (ss : List Stmt), ss.all Stmt.flat = true → ∀ (next : Prop) (kret : List E → Prop),
      (∀ s ∈ ss, Stmt.Holds C rd σ s True kret) → next → Stmt.HoldsList C rd σ ss next kret
  | [], _, _, _, _, hn => hn
  | s :: ss, hf, next, kret, h, hn => by
    simp only [List.all_cons, Bool.and_eq_true] at hf
    simp only [Stmt.HoldsList]
    rw [holds_flat_iff hf.1]
    exact ⟨h s List.mem_cons_self,
      holdsList_flat_of ss hf.2 next kret (fun t ht => h t (List.mem_cons_of_mem _ ht)) hn⟩

/-- A loop's block at the counter `x`, the end `N` and the other parameters `rest`. -/
def LoopBlock (rd : Reader) (fn : Fn) (x N : E) (rest : List E) : Prop :=
  ∃ σ : Val, fn.params.map σ = x :: N :: rest ∧
    ∀ s ∈ loopPre fn, Stmt.Holds (coreProgram.Rel rd) rd σ s True (fun rs => rs = [])

theorem gen_pow_add_isInK (a b : ℕ) : IsInK (gen ^ a + gen ^ b) :=
  isInK_add (gen_pow_isInK a) (gen_pow_isInK b)

/-- **A loop runs to its end** `g^m`, its block holding at every counter on the way. -/
theorem loopF_complete {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) {N : E} {rest : List E} {m : ℕ} (hN : N = gen ^ m)
    (hblk : ∀ j < m, LoopBlock rd fn (gen ^ j) N rest) :
    ∀ k < m, coreProgram.Rel rd f (gen ^ k :: N :: rest) [] := by
  simp only [loopShapeF, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h2, hpar⟩, hok⟩ := hok
  split at hok
  · rename_i pre c g args hsl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨hgf, hlen⟩, htail⟩, hg⟩, hc⟩ := hok
    obtain ⟨hbody, hflat⟩ := splitLoopF_eq hsl
    have hpre : loopPre fn = pre := by simp [loopPre, hsl]
    split at hc
    · rename_i p q hpq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hp', rfl⟩ := hc
      obtain ⟨n, hn⟩ : ∃ n, fn.params.length = n + 2 := ⟨fn.params.length - 2, by omega⟩
      have key : ∀ t k, k + 1 + t = m → coreProgram.Rel rd f (gen ^ k :: N :: rest) [] := by
        intro t
        induction t with
        | zero => ?_
        | succ t ih => ?_
        all_goals
          intro k hk
          obtain ⟨σ, hp, hs⟩ := hblk k (by omega)
          rw [hpre] at hs
          have hat := atoms_of_flat hs
          have hx0 : σ (V.n 0) = gen ^ k := by
            have := congrArg List.head? hp
            rw [hpar, hn, List.range_succ_eq_map] at this
            simpa using this
          have hx1 : σ (V.n 1) = N := by
            have := congrArg (fun l => l.tail.head?) hp
            rw [hpar, hn, List.range_succ_eq_map, List.range_succ_eq_map] at this
            simpa using this
          have hcv : σ c = gen ^ k * gen + N := by
            rw [addOf_sound hpq hat, genMul_sound hp' hat, hx0, hx1]
          have hargs : args.map σ = gen ^ k * gen :: N :: rest := by
            obtain ⟨a0, rs, rfl⟩ : ∃ a0 rs, args = a0 :: rs := by
              cases args with
              | nil => simp at hlen; omega
              | cons a0 rs => exact ⟨a0, rs, rfl⟩
            simp only [List.headD_cons] at hg
            simp only [List.tail_cons] at htail
            have hps : fn.params.tail.map σ = N :: rest := by
              have := congrArg List.tail hp
              rwa [← List.map_tail] at this
            rw [List.map_cons, genMul_sound hg hat, hx0, htail, hps]
          refine (rel_iff_sem hf _ _).mpr ⟨σ, hp, ?_⟩
          rw [hbody, holdsList_append]
          refine holdsList_flat_of pre hflat _ _ hs ?_
          simp only [Stmt.HoldsList, Stmt.Holds]
          refine ⟨by rw [hcv, gen_pow_mul_gen, hN]; exact gen_pow_add_isInK _ _, fun hne => ?_, rfl⟩
          rw [hargs, gen_pow_mul_gen, hgf]
        · exfalso
          apply hne
          rw [hcv, gen_pow_mul_gen, hN, show k + 1 = m by omega]
          exact e_add_eq_zero_iff.mpr rfl
        · exact ih (k + 1) (by omega)
      intro k hk
      exact key (m - k - 1) k (by omega)
    · exact absurd hc (by simp)
  · exact absurd hok (by simp)

/-- **A guarded loop runs** (`callIf (1 + g^m) f [1, g^m, …]`), its block holding at every
counter below `m`. -/
theorem guard_complete {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hok : loopShapeF fn f = true) {rest : List E} {m : ℕ}
    (hblk : ∀ j < m, LoopBlock rd fn (gen ^ j) (gen ^ m) rest) :
    IsInK (1 + gen ^ m) ∧ (1 + gen ^ m ≠ 0 → coreProgram.Rel rd f (1 :: gen ^ m :: rest) []) := by
  refine ⟨by rw [← pow_zero gen]; exact gen_pow_add_isInK _ _, fun hne => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact absurd (e_add_eq_zero_iff.mpr (pow_zero gen).symm) hne
  · have := loopF_complete hf hok rfl hblk 0 hm0
    rwa [pow_zero] at this

end
end LeanVM.Guest.B1.Digest
