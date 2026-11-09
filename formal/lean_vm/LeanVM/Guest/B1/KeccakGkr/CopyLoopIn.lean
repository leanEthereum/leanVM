/-
  LeanVM.Guest.B1.KeccakGkr.CopyLoopIn

  `verify_keccak`'s copy loops, completely and with their loads placed.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.CopyLoop
public import LeanVM.Guest.B1.KeccakGkr.RecIn

/-!
# The copy loops, completely

A copy loop from `x = 1` to `N = g^m` stores at `dst·g^j` the word at `src·g^j`, `j < m`. With
those words in memory (`hcp`) and both addresses in a region `R` at every counter (`hR`), the loop
runs loading from `R` (`copyLoop_relIn`): per iteration the valuation is written out
(`copyStepσ`), one tree per iteration, the next one its only callee.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- An iteration's statements before its return. -/
def copyPre (name : String) : List Stmt := (copyLoopT name).dropLast

theorem copyLoopT_split (name : String) : copyLoopT name = copyPre name ++ [.ret []] := rfl

theorem copy_straight (name : String) : (copyPre name).all Stmt.straight = true := rfl

theorem copy_loads (name : String) :
    (copyPre name).filterMap Stmt.loadS = [(.n 4, 0), (.n 6, 0)] := rfl

theorem copy_calls (name : String) :
    (copyPre name).filterMap Stmt.callS = [(some (.n 9), name, [.n 11, .n 1, .n 2, .n 3], [])] :=
  rfl

/-- An iteration's valuation at `x`, copying `v`. -/
noncomputable def copyStepσ (x N dst src v : E) : Val :=
  B1.Val.ofArgs [x, N, dst, src, src * x, v, dst * x, word 2 0 0, x * word 2 0 0,
    x * word 2 0 0 + N, word 2 0 0, x * word 2 0 0]

/-- **One iteration on its loads' region**, the next one (if any) given. -/
theorem copyLoop_relIn_step {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3])
    {rd : Reader} {R : ℕ → Prop} {dst src : E} {m k : ℕ} (hk : k < m)
    (hcp : ∃ v, LoadHolds rd (src * gen ^ k) 0 v ∧ LoadHolds rd (dst * gen ^ k) 0 v)
    (hR : InR R (src * gen ^ k) 0 ∧ InR R (dst * gen ^ k) 0)
    (hnext : k + 1 < m → coreProgram.RelIn rd R name [gen ^ (k + 1), gen ^ m, dst, src] []) :
    coreProgram.RelIn rd R name [gen ^ k, gen ^ m, dst, src] [] := by
  obtain ⟨v, hs, hd⟩ := hcp
  set σ := copyStepσ (gen ^ k) (gen ^ m) dst src v with hσ
  have hw : walk σ fn.body = .ret ((copyPre name).flatMap (slEvs σ)) [] := by
    rw [hb, copyLoopT_split]
    exact walk_straight σ [] _ (copy_straight name)
  have e2 : word 2 0 0 = gen := word_gen
  refine relIn_of_walk coreProgram_wf hf (by rw [hpar]; rfl) hw rfl
    (fun e he ↦ ?_) (fun A hA ↦ ?_) (fun c hc ht ↦ ?_)
  · simp only [copyPre, copyLoopT, List.dropLast, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, slEvs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show σ (.n 4) = σ (.n 3) * σ (.n 0); rfl
    · show LoadHolds rd (σ (.n 4)) 0 (σ (.n 5)); exact hs
    · show σ (.n 6) = σ (.n 2) * σ (.n 0); rfl
    · show LoadHolds rd (σ (.n 6)) 0 (σ (.n 5)); exact hd
    · rfl
    · show σ (.n 8) = σ (.n 0) * σ (.n 7); rfl
    · show σ (.n 9) = σ (.n 8) + σ (.n 1); rfl
    · rfl
    · show σ (.n 11) = σ (.n 0) * σ (.n 10); rfl
    · show IsInK (σ (.n 9))
      show IsInK (gen ^ k * word 2 0 0 + gen ^ m)
      rw [e2, ← pow_succ]
      exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
    · split <;> trivial
  · rw [loadAddrs_straight σ _ (copy_straight name), copy_loads] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · exact hR.1
    · exact hR.2
  · rw [(straight_parts σ _ (copy_straight name)).2.2.2, copy_calls] at hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    simp only [mkCall, decide_eq_true_eq] at ht
    have hk1 : k + 1 < m := by
      by_contra hge
      apply ht
      show gen ^ k * word 2 0 0 + gen ^ m = 0
      rw [e2, ← pow_succ, show k + 1 = m by omega]
      exact e_add_eq_zero_iff.mpr rfl
    show coreProgram.RelIn rd R name [gen ^ k * word 2 0 0, gen ^ m, dst, src] []
    rw [e2, ← pow_succ]
    exact hnext hk1

/-- **A copy loop runs on its loads' region** from `x = 1`, with `N = g^m`. -/
theorem copyLoop_relIn {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3])
    {rd : Reader} {R : ℕ → Prop} {dst src : E} {m : ℕ}
    (hcp : ∀ j < m, ∃ v, LoadHolds rd (src * gen ^ j) 0 v ∧ LoadHolds rd (dst * gen ^ j) 0 v)
    (hR : ∀ j < m, InR R (src * gen ^ j) 0 ∧ InR R (dst * gen ^ j) 0) :
    IsInK (1 + gen ^ m) ∧
      (1 + gen ^ m ≠ 0 → coreProgram.RelIn rd R name [1, gen ^ m, dst, src] []) := by
  refine ⟨by rw [← pow_zero gen]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _), fun hne ↦ ?_⟩
  have key : ∀ t k, k + 1 + t = m →
      coreProgram.RelIn rd R name [gen ^ k, gen ^ m, dst, src] [] := by
    intro t
    induction t with
    | zero =>
      intro k hk
      exact copyLoop_relIn_step hf hb hpar (by omega) (hcp k (by omega)) (hR k (by omega))
        (fun h ↦ absurd h (by omega))
    | succ t ih =>
      intro k hk
      exact copyLoop_relIn_step hf hb hpar (by omega) (hcp k (by omega)) (hR k (by omega))
        (fun _ ↦ ih (k + 1) (by omega))
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exact absurd (e_add_eq_zero_iff.mpr (pow_zero gen).symm) hne
  · have := key (m - 1) 0 (by omega)
    rwa [pow_zero] at this

end
end LeanVM.Guest.B1.VerifySub
