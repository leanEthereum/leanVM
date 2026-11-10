/-
  LeanVM.Guest.B1.Opening.QueriesMain

  `opening_queries`' templates by kind (their atoms, calls and conditional calls), its loop's
  guard and its start.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesSound

/-!
# `opening_queries`' blocks

* `oqQueryT_flatC`, `oqLoop1A_flatC`, `oqLoop0A_flatC`, `oqMainA_flatC`: the blocks are atoms
  and calls.
* `oqLoop1_hc`, `oqLoop0_hc`: an iteration's guard is `x·g + N` and its next call's arguments
  `x·g :: N :: …`.
* `oqMainA_basic`: the function's start: the loop's guard `1 + N` and start `1`, and at an even
  count the chain's first word `0`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The loop's parameters. -/
def oqLoopParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9]

theorem oqXorT_atoms (s : Oq) (b pr kL k c : ℕ) : AllAtoms (oqXorT s b pr kL k c) := by
  unfold oqXorT
  dsimp only
  split
  · exact allAtoms_cons allAtoms_nil
  · split
    · exact allAtoms_cons (allAtoms_cons allAtoms_nil)
    · exact allAtoms_cons allAtoms_nil

theorem oqBlockT_atoms (s : Oq) (b pr kL k : ℕ) : AllAtoms (oqBlockT s b pr kL k) := by
  unfold oqBlockT
  split
  · exact allAtoms_cons allAtoms_nil
  · exact allAtoms_append (allAtoms_map_flatten fun _ _ => oqXorT_atoms _ _ _ _ _ _)
      (allAtoms_cons allAtoms_nil)

theorem oqLeafT_atoms (s : Oq) (b pr kL : ℕ) : AllAtoms (oqLeafT s b pr kL) :=
  allAtoms_map_flatten fun _ _ => oqBlockT_atoms _ _ _ _ _

theorem flatC_atoms {ss : List Stmt} (h : AllAtoms ss) : FlatC ss := flatC_of_flat (flat_of_atoms h)

theorem oqQueryT_flatC (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ)
    (walk : String) : FlatC (oqQueryT s x bp cap flags coefs hs b emit pr walk) := by
  unfold oqQueryT
  refine flatC_append (flatC_append (flatC_append (flatC_atoms (allAtoms_append (allAtoms_append
    (oqPrepT_atoms _ _) ?_) (oqLeafT_atoms _ _ _ _))) (flatC_call _ _ _))
    (flatC_atoms (oqFoldT_atoms _ _ _ _ _))) (flatC_atoms ?_)
  · split
    · exact oqPadT_atoms _
    · exact allAtoms_nil
  · split
    · exact oqFinT_atoms _ _ _ _
    · exact allAtoms_nil

theorem oqGuardA_atoms (g : ℕ) : AllAtoms (oqGuardA g) := by unfold oqGuardA; atoms_lit

theorem oqLoop1A_flatC (s : Oq) (odd : ℕ) (walk : String) : FlatC (oqLoop1A s odd walk) := by
  unfold oqLoop1A
  dsimp only
  refine flatC_append (flatC_append (flatC_append (flatC_append (flatC_append (flatC_atoms ?_)
    (oqQueryT_flatC _ _ _ _ _ _ _ _ _ _ _)) (flatC_atoms ?_)) (oqQueryT_flatC _ _ _ _ _ _ _ _ _ _ _))
    (flatC_atoms ?_)) (flatC_atoms (oqGuardA_atoms _))
  · atoms_lit
  · atoms_lit
  · split
    · exact allAtoms_nil
    · atoms_lit

theorem oqLoop0A_flatC (s : Oq) (walk : String) : FlatC (oqLoop0A s walk) := by
  unfold oqLoop0A
  dsimp only
  refine flatC_append (flatC_append (flatC_append (flatC_atoms ?_) (oqQueryT_flatC _ _ _ _ _ _ _ _ _ _ _))
    (flatC_atoms ?_)) (flatC_atoms (oqGuardA_atoms _))
  · atoms_lit
  · split
    · exact allAtoms_nil
    · atoms_lit

theorem oqMainA_flatC (s : Oq) (odd : ℕ) (walk : String) : FlatC (oqMainA s odd walk) := by
  unfold oqMainA
  dsimp only
  refine flatC_append (flatC_append (flatC_atoms ?_) ?_) (flatC_atoms ?_)
  · atoms_lit
  · split
    · exact flatC_append (flatC_append (flatC_atoms (allAtoms_cons (allAtoms_cons allAtoms_nil)))
        (oqQueryT_flatC _ _ _ _ _ _ _ _ _ _ _)) (flatC_atoms (allAtoms_cons (allAtoms_cons allAtoms_nil)))
    · exact flatC_atoms (allAtoms_cons (allAtoms_cons allAtoms_nil))
  · atoms_lit

/-! ## The loops' guards -/

/-- An iteration's guard and next call from its guard's atoms. -/
theorem oqGuard_hc {C : CallRel} {τ : Val} {A : List Stmt} {g : ℕ} {x Nv : E} {rest : List E}
    (hA : BlockOkC C rd τ A) (hsub : ∀ a, Stmt.atom a ∈ oqGuardA g → Stmt.atom a ∈ A)
    (h0 : τ (.n 0) = x) (h1 : τ (.n 1) = Nv)
    (hr : [τ (.n 2), τ (.n 3), τ (.n 4), τ (.n 5), τ (.n 6), τ (.n 7), τ (.n 8), τ (.n 9)] = rest) :
    τ (.n (g + 2)) = x * gen + Nv ∧
      ([.n (g + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map τ =
        x * gen :: Nv :: rest := by
  have a0 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.const (.n g) (word 2 0)) ∈ _)
  have a1 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.mul (.n (g + 1)) (.n 0) (.n g)) ∈ _)
  have a2 := hA.atom (hsub _ (by simp [oqGuardA]) :
    Stmt.atom (.add (.n (g + 2)) (.n (g + 1)) (.n 1)) ∈ _)
  have a3 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.const (.n (g + 3)) (word 2 0)) ∈ _)
  have a4 := hA.atom (hsub _ (by simp [oqGuardA]) :
    Stmt.atom (.mul (.n (g + 4)) (.n 0) (.n (g + 3))) ∈ _)
  simp only [Atom.Holds] at a0 a1 a2 a3 a4
  subst hr
  refine ⟨by rw [a2, a1, a0, word_gen, h0, h1], ?_⟩
  simp [a4, a3, word_gen, h0, h1]

theorem oqLoop1_hc {C : CallRel} {s : Oq} {odd : ℕ} {walk : String} {fl : Fn}
    (hpl : fl.params = oqLoopParams) {Nv : E} {rest : List E} (τ : Val) (x : E)
    (hp : fl.params.map τ = x :: Nv :: rest) (hA : BlockOkC C rd τ (oqLoop1A s odd walk)) :
    τ (.n (oqG1 s + 2)) = x * gen + Nv ∧
      ([.n (oqG1 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map τ =
        x * gen :: Nv :: rest := by
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  exact oqGuard_hc hA (fun a h ↦ by unfold oqLoop1A; exact List.mem_append_right _ h) h0 h1 hr

theorem oqLoop0_hc {C : CallRel} {s : Oq} {walk : String} {fl : Fn}
    (hpl : fl.params = oqLoopParams) {Nv : E} {rest : List E} (τ : Val) (x : E)
    (hp : fl.params.map τ = x :: Nv :: rest) (hA : BlockOkC C rd τ (oqLoop0A s walk)) :
    τ (.n (oqG0 s + 2)) = x * gen + Nv ∧
      ([.n (oqG0 s + 4), .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9] : List V).map τ =
        x * gen :: Nv :: rest := by
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  exact oqGuard_hc hA (fun a h ↦ by unfold oqLoop0A; exact List.mem_append_right _ h) h0 h1 hr

/-- An iteration's parameters, from the loop's parameters. -/
theorem loop_params {fl : Fn} (hpl : fl.params = oqLoopParams) {τ : Val} {x : E} {ps : List E}
    (hp : fl.params.map τ = x :: ps) :
    τ (.n 0) = x ∧ ps = [τ (.n 1), τ (.n 2), τ (.n 3), τ (.n 4), τ (.n 5), τ (.n 6), τ (.n 7),
      τ (.n 8), τ (.n 9)] := by
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil, List.cons.injEq] at hp
  exact ⟨hp.1, hp.2.symm⟩

/-! ## The function's start -/

/-- What the start of the function gives: the loop's guard `1 + N` and start `1`, and at an even
count the chain's first word `0`. -/
theorem oqMainA_basic {C : CallRel} {s : Oq} {odd : ℕ} {walk : String} {σ : Val}
    (hA : BlockOkC C rd σ (oqMainA s odd walk)) :
    σ (.n (oqMK s odd + 1)) = 1 + σ (.n 7) ∧ σ (.n (oqMK s odd + 2)) = 1 ∧
      (odd ≠ 1 → LoadHolds rd (σ (.n 10)) 0 0) := by
  set k := oqMK s odd with hk
  have m2 := hA.atom (by simp [oqMainA, ← hk] : Stmt.atom (.const (.n k) (word 1 0)) ∈ _)
  have m3 := hA.atom (by simp [oqMainA, ← hk] : Stmt.atom (.add (.n (k + 1)) (.n k) (.n 7)) ∈ _)
  have m4 := hA.atom (by simp [oqMainA, ← hk] : Stmt.atom (.const (.n (k + 2)) (word 1 0)) ∈ _)
  simp only [Atom.Holds] at m2 m3 m4
  refine ⟨by rw [m3, m2, word_one], by rw [m4, word_one], fun h1 => ?_⟩
  have c1 := hA.atom (by simp [oqMainA, h1] : Stmt.atom (.const (.n 11) (word 0 0)) ∈ _)
  have c2 := hA.atom (by simp [oqMainA, h1] : Stmt.atom (.load (.n 11) (.n 10) 0) ∈ _)
  simp only [Atom.Holds] at c1 c2
  rw [c1, word_zero] at c2
  exact c2

end
end LeanVM.Guest.B1
