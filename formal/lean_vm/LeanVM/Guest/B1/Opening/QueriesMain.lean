/-
  LeanVM.Guest.B1.Opening.QueriesMain

  `opening_queries`' blocks: flat but for the start's odd-query branch at level 0, its loop's guard
  and its start.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesSound

/-!
# `opening_queries`' blocks

* `oqQueryT_flat`, `oqLoop1A_flat`, `oqLoop0A_flat`, `oqOddT_flat`: the blocks are atoms and
  matches of atoms (`walk_path` is inline).
* `holdsList_oqMainA`: the function's start holds as `OqStartOk`: its atoms, and at level 0 the
  branch on `odd_g + 1` between the even start (`chain[0] = 0`) and the odd first query.
* `oqLoop1_hc`, `oqLoop0_hc`: an iteration's guard is `x·g + N` and its next call's arguments
  `x·g :: N :: …`.
* `oqMainA_basic`: the loop's guard `1 + N` and start `1`; deeper, the chain's first word `0`;
  `oqStart1_facts`: at level 0, the branch's word, the loop's moved positions and windows, and
  each branch's statements.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The loop helper's parameters. -/
def oqLoopParams : List V :=
  [.n oqX, .n oqN, .n oqPos, .n oqQp, .n oqCap, .n oqFlags, .n oqCoefs, .n oqHs, .n oqChainP, .n oqLamInv]

/-- The function's parameters. -/
def oqMainParams : List V :=
  [.n oqMCap, .n oqMFlags, .n oqMLamInv, .n oqMCoefs, .n oqMHs, .n oqMPos, .n oqMQp, .n oqMN, .n oqMOdd]

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

theorem oqQueryT_flat (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ) :
    Flat (oqQueryT s x bp cap flags coefs hs b emit pr) := by
  unfold oqQueryT
  refine flat_append (flat_append (flat_append (flat_of_atoms (allAtoms_append (allAtoms_append
    (oqPrepT_atoms _ _) ?_) (oqLeafT_atoms _ _ _ _))) (oqWalkT_flat _ _ _ _ _ _ _))
    (flat_of_atoms (oqFoldT_atoms _ _ _ _ _))) (flat_of_atoms ?_)
  · split
    · exact oqPadT_atoms _
    · exact allAtoms_nil
  · split
    · exact oqFinT_atoms _ _ _ _
    · exact allAtoms_nil

theorem oqQueryT_flatC (s : Oq) (x bp cap flags coefs hs : V) (b : ℕ) (emit : Bool) (pr : ℕ) :
    FlatC (oqQueryT s x bp cap flags coefs hs b emit pr) :=
  flatC_of_flat (oqQueryT_flat _ _ _ _ _ _ _ _ _ _)

theorem oqGuardA_atoms (g : ℕ) : AllAtoms (oqGuardA g) := by unfold oqGuardA; atoms_lit

theorem oqLoop1A_flat (s : Oq) : Flat (oqLoop1A s) := by
  unfold oqLoop1A
  dsimp only
  refine flat_append (flat_append (flat_append (flat_append (flat_append (flat_of_atoms ?_)
    (oqQueryT_flat _ _ _ _ _ _ _ _ _ _)) (flat_of_atoms ?_)) (oqQueryT_flat _ _ _ _ _ _ _ _ _ _))
    (flat_of_atoms ?_)) (flat_of_atoms (oqGuardA_atoms _))
  · atoms_lit
  · atoms_lit
  · split
    · exact allAtoms_nil
    · atoms_lit

theorem oqLoop1A_flatC (s : Oq) : FlatC (oqLoop1A s) := flatC_of_flat (oqLoop1A_flat s)

theorem oqLoop0A_flat (s : Oq) : Flat (oqLoop0A s) := by
  unfold oqLoop0A
  dsimp only
  refine flat_append (flat_append (flat_append (flat_of_atoms ?_) (oqQueryT_flat _ _ _ _ _ _ _ _ _ _))
    (flat_of_atoms ?_)) (flat_of_atoms (oqGuardA_atoms _))
  · atoms_lit
  · split
    · exact allAtoms_nil
    · atoms_lit

theorem oqLoop0A_flatC (s : Oq) : FlatC (oqLoop0A s) := flatC_of_flat (oqLoop0A_flat s)

theorem oqOddT_flat (s : Oq) : Flat (oqOddT s) := by
  unfold oqOddT
  exact flat_append (flat_append (flat_of_atoms (by atoms_lit)) (oqQueryT_flat _ _ _ _ _ _ _ _ _ _))
    (flat_of_atoms (by atoms_lit))

/-! ## The function's start -/

/-- The start's statements before level 0's branch: the chain allocated, the branch's word
`odd_g + 1`. -/
def oqMainPre : List Stmt :=
  [.atom (.const (.n 9) (word 2 0)), .atom (.mul (.n 10) (.n oqMN) (.n 9)),
    .atom (.hint (.allocDyn (.n 11) (.n 10))), .atom (.const (.n 12) (word 1 0)),
    .atom (.add (.n 13) (.n oqMOdd) (.n 12))]

/-- The even start's branch: `chain[0] = 0`. -/
def oqEvenT : List Stmt := [.atom (.const (.n 14) (word 0 0)), .atom (.load (.n 14) (.n 11) 0)]

/-- The start's statements after level 0's branch: the loop's positions and windows moved past
the odd query, the loop's guard and start. -/
def oqMainPost (s : Oq) : List Stmt :=
  [.atom (.mul (.n (oqMK s - 2)) (.n oqMPos) (.n oqMOdd)),
    .atom (.mul (.n (oqMK s - 1)) (.n oqMQp) (.n oqMOdd)), .atom (.const (.n (oqMK s)) (word 1 0)),
    .atom (.add (.n (oqMK s + 1)) (.n (oqMK s)) (.n oqMN)), .atom (.const (.n (oqMK s + 2)) (word 1 0))]

theorem oqMainPre_atoms : AllAtoms oqMainPre := by unfold oqMainPre; atoms_lit

theorem oqEvenT_atoms : AllAtoms oqEvenT := by unfold oqEvenT; atoms_lit

theorem oqMainPost_atoms (s : Oq) : AllAtoms (oqMainPost s) := by unfold oqMainPost; atoms_lit

theorem oqMainA_one {s : Oq} (hb : s.base = 1) :
    oqMainA s = oqMainPre ++ .ite (.n 13) oqEvenT (oqOddT s) :: oqMainPost s := by
  simp [oqMainA, hb, oqMainPre, oqEvenT, oqMainPost]

theorem oqMainA_flat {s : Oq} (hb : s.base ≠ 1) : Flat (oqMainA s) := by
  unfold oqMainA
  simp only [hb, ↓reduceIte]
  exact flat_of_atoms (by atoms_lit)

/-- **What the function's start asks**: deeper, its atoms; at level 0 its atoms around the branch
on `odd_g + 1`, the even start's when it is `0`, the odd first query's otherwise. -/
def OqStartOk (C : CallRel) (rd : Reader) (σ : Val) (s : Oq) : Prop :=
  if s.base = 1 then
    BlockOkC C rd σ (oqMainPre ++ oqMainPost s) ∧ IsInK (σ (.n 13)) ∧
      (σ (.n 13) = 0 → BlockOkC C rd σ oqEvenT) ∧ (σ (.n 13) ≠ 0 → BlockOkC C rd σ (oqOddT s))
  else BlockOkC C rd σ (oqMainA s)

/-- **The function's start holds** exactly when `OqStartOk` does, then its continuation. -/
theorem holdsList_oqMainA {C : CallRel} {σ : Val} (s : Oq) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (oqMainA s) next kret ↔ OqStartOk C rd σ s ∧ next := by
  unfold OqStartOk
  by_cases hb : s.base = 1
  · simp only [hb, ↓reduceIte]
    rw [oqMainA_one hb, holdsList_append, holdsList_flatC (flatC_atoms oqMainPre_atoms)]
    simp only [Stmt.HoldsList, Stmt.Holds]
    rw [holdsList_flatC (flatC_atoms oqEvenT_atoms), holdsList_flatC (flatC_of_flat (oqOddT_flat s)),
      holdsList_flatC (flatC_atoms (oqMainPost_atoms s)), blockOkC_append]
    by_cases h0 : σ (.n 13) = 0
    · constructor
      · rintro ⟨hp, hk, hz, -⟩
        obtain ⟨he, hpo, hn⟩ := hz h0
        exact ⟨⟨⟨hp, hpo⟩, hk, fun _ => he, fun h => absurd h0 h⟩, hn⟩
      · rintro ⟨⟨⟨hp, hpo⟩, hk, he, -⟩, hn⟩
        exact ⟨hp, hk, fun h => ⟨he h, hpo, hn⟩, fun h => absurd h0 h⟩
    · constructor
      · rintro ⟨hp, hk, -, hz⟩
        obtain ⟨ho, hpo, hn⟩ := hz h0
        exact ⟨⟨⟨hp, hpo⟩, hk, fun h => absurd h h0, fun _ => ho⟩, hn⟩
      · rintro ⟨⟨⟨hp, hpo⟩, hk, -, ho⟩, hn⟩
        exact ⟨hp, hk, fun h => absurd h h0, fun h => ⟨ho h, hpo, hn⟩⟩
  · simp only [hb, ↓reduceIte]
    exact holdsList_flatC (flatC_of_flat (oqMainA_flat hb)) next kret

/-- The atoms of the start shared by both bases: the chain's allocation and the loop's guard and
start. -/
theorem OqStartOk.guard {C : CallRel} {σ : Val} {s : Oq} (h : OqStartOk C rd σ s) {a : Atom}
    (ha : Stmt.atom a ∈ [Stmt.atom (.const (.n (oqMK s)) (word 1 0)),
      .atom (.add (.n (oqMK s + 1)) (.n (oqMK s)) (.n oqMN)), .atom (.const (.n (oqMK s + 2)) (word 1 0))]) :
    a.Holds rd σ := by
  unfold OqStartOk at h
  by_cases hb : s.base = 1
  · simp only [hb, ↓reduceIte] at h
    refine h.1.atom (List.mem_append_right _ ?_)
    simp only [oqMainPost, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
    tauto
  · simp only [hb, ↓reduceIte] at h
    refine h.atom ?_
    simp only [oqMainA, hb, ↓reduceIte, List.mem_append]
    exact Or.inr ha

/-- What the start gives: the loop's guard `1 + N` and start `1`, and deeper the chain's first
word `0`. -/
theorem oqMainA_basic {C : CallRel} {s : Oq} {σ : Val} (hA : OqStartOk C rd σ s) :
    σ (.n (oqMK s + 1)) = 1 + σ (.n oqMN) ∧ σ (.n (oqMK s + 2)) = 1 ∧
      (s.base ≠ 1 → LoadHolds rd (σ (.n 11)) 0 0) := by
  have m2 := hA.guard (a := .const (.n (oqMK s)) (word 1 0)) (by simp)
  have m3 := hA.guard (a := .add (.n (oqMK s + 1)) (.n (oqMK s)) (.n oqMN)) (by simp)
  have m4 := hA.guard (a := .const (.n (oqMK s + 2)) (word 1 0)) (by simp)
  simp only [Atom.Holds] at m2 m3 m4
  refine ⟨by rw [m3, m2, word_one], by rw [m4, word_one], fun h1 => ?_⟩
  unfold OqStartOk at hA
  simp only [h1, ↓reduceIte] at hA
  have c1 := hA.atom (by simp [oqMainA, h1] : Stmt.atom (.const (.n 12) (word 0 0)) ∈ _)
  have c2 := hA.atom (by simp [oqMainA, h1] : Stmt.atom (.load (.n 12) (.n 11) 0) ∈ _)
  simp only [Atom.Holds] at c1 c2
  rw [c1, word_zero] at c2
  exact c2

/-- **Level 0's start**: the branch's word `odd_g + 1`, the loop's positions and windows
`positions·odd_g`, `qptrs·odd_g`, the even start's `chain[0] = 0`, the odd query's statements. -/
theorem oqStart1_facts {C : CallRel} {s : Oq} {σ : Val} (hb : s.base = 1) (hA : OqStartOk C rd σ s) :
    σ (.n 13) = σ (.n oqMOdd) + 1 ∧ σ (.n (oqMK s - 2)) = σ (.n oqMPos) * σ (.n oqMOdd) ∧
      σ (.n (oqMK s - 1)) = σ (.n oqMQp) * σ (.n oqMOdd) ∧
      (σ (.n 13) = 0 → LoadHolds rd (σ (.n 11)) 0 0) ∧
      (σ (.n 13) ≠ 0 → BlockOkC C rd σ (oqOddT s)) := by
  unfold OqStartOk at hA
  simp only [hb, ↓reduceIte] at hA
  obtain ⟨hA, -, he, ho⟩ := hA
  have a1 := hA.atom (by simp [oqMainPre] : Stmt.atom (.const (.n 12) (word 1 0)) ∈ _)
  have a2 := hA.atom (by simp [oqMainPre] : Stmt.atom (.add (.n 13) (.n oqMOdd) (.n 12)) ∈ _)
  have a3 := hA.atom (by simp [oqMainPost] : Stmt.atom (.mul (.n (oqMK s - 2)) (.n oqMPos) (.n oqMOdd)) ∈ _)
  have a4 := hA.atom (by simp [oqMainPost] : Stmt.atom (.mul (.n (oqMK s - 1)) (.n oqMQp) (.n oqMOdd)) ∈ _)
  simp only [Atom.Holds] at a1 a2 a3 a4
  refine ⟨by rw [a2, a1, word_one], a3, a4, fun h0 => ?_, ho⟩
  have e := he h0
  have c1 := e.atom (by simp [oqEvenT] : Stmt.atom (.const (.n 14) (word 0 0)) ∈ _)
  have c2 := e.atom (by simp [oqEvenT] : Stmt.atom (.load (.n 14) (.n 11) 0) ∈ _)
  simp only [Atom.Holds] at c1 c2
  rw [c1, word_zero] at c2
  exact c2

/-! ## The loops' guards -/

/-- The loop's next call's arguments from the guard at `g`. -/
def oqNextArgs (g : ℕ) : List V :=
  [.n (g + 4), .n oqN, .n oqPos, .n oqQp, .n oqCap, .n oqFlags, .n oqCoefs, .n oqHs, .n oqChainP, .n oqLamInv]

theorem oqNextT_eq (g : ℕ) (name : String) :
    oqNextT g name = [.callIf (.n (g + 2)) name (oqNextArgs g), .ret []] := rfl

/-- An iteration's parameters, from the loop's parameters. -/
theorem loop_params {fl : Fn} (hpl : fl.params = oqLoopParams) {τ : Val} {x : E} {ps : List E}
    (hp : fl.params.map τ = x :: ps) :
    τ (.n oqX) = x ∧ ps = [τ (.n oqN), τ (.n oqPos), τ (.n oqQp), τ (.n oqCap), τ (.n oqFlags),
      τ (.n oqCoefs), τ (.n oqHs), τ (.n oqChainP), τ (.n oqLamInv)] := by
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil, List.cons.injEq] at hp
  exact ⟨hp.1, hp.2.symm⟩

/-- An iteration's guard and next call from its guard's atoms. -/
theorem oqGuard_hc {C : CallRel} {τ : Val} {A : List Stmt} {g : ℕ} {fl : Fn}
    (hpl : fl.params = oqLoopParams) {x Nv : E} {rest : List E}
    (hp : fl.params.map τ = x :: Nv :: rest)
    (hA : BlockOkC C rd τ A) (hsub : ∀ a, Stmt.atom a ∈ oqGuardA g → Stmt.atom a ∈ A) :
    τ (.n (g + 2)) = x * gen + Nv ∧ (oqNextArgs g).map τ = x * gen :: Nv :: rest := by
  obtain ⟨h0, hr⟩ := loop_params hpl hp
  simp only [List.cons.injEq] at hr
  obtain ⟨h1, hr⟩ := hr
  have a0 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.const (.n g) (word 2 0)) ∈ _)
  have a1 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.mul (.n (g + 1)) (.n oqX) (.n g)) ∈ _)
  have a2 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.add (.n (g + 2)) (.n (g + 1)) (.n oqN)) ∈ _)
  have a3 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.const (.n (g + 3)) (word 2 0)) ∈ _)
  have a4 := hA.atom (hsub _ (by simp [oqGuardA]) : Stmt.atom (.mul (.n (g + 4)) (.n oqX) (.n (g + 3))) ∈ _)
  simp only [Atom.Holds] at a0 a1 a2 a3 a4
  subst hr
  refine ⟨by rw [a2, a1, a0, word_gen, h0, h1], ?_⟩
  simp [oqNextArgs, a4, a3, word_gen, h0, h1]

theorem oqLoop1_hc {C : CallRel} {s : Oq} {fl : Fn} (hpl : fl.params = oqLoopParams) {Nv : E}
    {rest : List E} (τ : Val) (x : E) (hp : fl.params.map τ = x :: Nv :: rest)
    (hA : BlockOkC C rd τ (oqLoop1A s)) :
    τ (.n (oqG1 s + 2)) = x * gen + Nv ∧ (oqNextArgs (oqG1 s)).map τ = x * gen :: Nv :: rest :=
  oqGuard_hc hpl hp hA (fun a h ↦ by unfold oqLoop1A; exact List.mem_append_right _ h)

theorem oqLoop0_hc {C : CallRel} {s : Oq} {fl : Fn} (hpl : fl.params = oqLoopParams) {Nv : E}
    {rest : List E} (τ : Val) (x : E) (hp : fl.params.map τ = x :: Nv :: rest)
    (hA : BlockOkC C rd τ (oqLoop0A s)) :
    τ (.n (oqG0 s + 2)) = x * gen + Nv ∧ (oqNextArgs (oqG0 s)).map τ = x * gen :: Nv :: rest :=
  oqGuard_hc hpl hp hA (fun a h ↦ by unfold oqLoop0A; exact List.mem_append_right _ h)

end
end LeanVM.Guest.B1
