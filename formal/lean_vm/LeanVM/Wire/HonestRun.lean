/-
  LeanVM.Wire.HonestRun

  The honest prover's run, for a strategy that wins (`Strategy.AcceptsFrom`) against a program
  whose openings are within the wire bounds (`Wired`): its phases are openings of one committed
  tree each, within the bounds, and its stream is as long as the program's cost allows.
-/

module

public import LeanVM.Protocol.Compile.Rom.Prover
public import LeanVM.Wire.HonestTree
public import LeanVM.Wire.HonestShape

/-!
# The honest prover's run

From a history whose strategy wins (`S.AcceptsFrom p hist`), with its commitments well shaped
and `p` wired from their shapes (`Wired`, `LeanVM.Wire.HonestShape`):

* `proveFrom_phases`: every phase of the honest prover's output (`proveFrom`) is the openings of
  one committed word's tree at positions within the bounds (`QueryShape`), at most as many phases
  as openings were left;
* `proveFrom_stream_le`: its stream is at most the program's cost (`VerifierProgram.Costs`), a
  read, a nonce and a root half each costing at least one.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.MerkleTree
open LeanVM.Prover (Tree buildTreeWithHash leafDigestsWithHash parentsWithHash levelsWithHash
  powStepM searchM findNonceM)

/-- The shapes (height, width) of a list of commitments. -/
def shapesOf (cs : List (ℕ × ℕ × Word)) : List (ℕ × ℕ) := cs.map fun c ↦ (c.1, c.2.1)

theorem commits_append_single_of {hist : List Ev} {e : Ev} (he : commits [e] = []) :
    commits (hist ++ [e]) = commits hist := by
  rw [commits_append, he, List.append_nil]

/-! ## The phases and the stream -/

section Pure

variable (h : Bytes → Digest) (F : KeccakState → KeccakState) (S : Strategy) (fuel : ℕ)

/-- **The honest prover's phases**: each opens one committed word's tree at positions within the
wire bounds, the word well shaped, and there are at most as many as openings left. -/
theorem proveFrom_phases :
    ∀ (p : VerifierProgram Bool) (sp : Sponge) (hist : List Ev) (n : ℕ)
      {Q : Bool → List (ℕ × ℕ) → ℕ → Prop} {xs : List E} {os : List (List Opening)},
      S.AcceptsFrom p hist → (∀ c ∈ commits hist, WellShaped c.2.1 c.2.2) →
      Wired p (shapesOf (commits hist)) n Q →
      proveFrom h F S fuel p sp hist = some (xs, os) →
      os.length ≤ n ∧ ∀ phase ∈ os, ∃ (ht w : ℕ) (word : Word) (ps : List ℕ),
        phase = ps.map (openingAt h ht word) ∧ WellShaped w word ∧ QueryShape (ht, w) ps := by
  intro p
  induction p with
  | ret b =>
    intro sp hist n Q xs os _ _ _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    simp
  | fail =>
    intro sp hist n Q xs os _ _ _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    simp
  | read k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have hc := commits_append_single_of (hist := hist) (e := Ev.read (S.msg hist)) rfl
    refine ih _ _ _ n hacc (hc ▸ hws) (hc ▸ hw (S.msg hist)) hp
  | sample k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom] at hp
    have hc := commits_append_single_of (hist := hist) (e := Ev.sample (squeezeI F sp).1) rfl
    exact ih _ _ _ n (hacc _) (hc ▸ hws) (hc ▸ hw _) hp
  | grind bits k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom] at hp
    split at hp
    · cases hp
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hc := commits_append_single_of (hist := hist) (e := Ev.grind bits) rfl
      exact ih _ _ n hacc (hc ▸ hws) (hc ▸ hw) hp
  | commit ht w k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have hc : commits (hist ++ [Ev.commit ht w (S.word hist)]) =
        commits hist ++ [(ht, w, S.word hist)] := by
      rw [commits_append]; rfl
    refine ih _ _ n (Q := Q) hacc.2 (fun c hcm ↦ ?_) ?_ hp
    · rw [hc] at hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · exact hws c hcm
      · simp only [List.mem_singleton] at hcm
        subst hcm
        exact hacc.1
    · rw [hc, shapesOf, List.map_append]
      exact hw
  | query i ps k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    obtain ⟨rows, hrows, hacc'⟩ := hacc
    simp only [proveFrom] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, rfl⟩ := hp
      simp
    · next ht w' word hci =>
      simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hrows' : rows = ps.map fun q ↦ word (q % 2 ^ ht) := by
        simp only [answer, hci, Option.map_some, Option.some.injEq] at hrows
        exact hrows.symm
      subst hrows'
      have hshape : (shapesOf (commits hist)).getD i (0, 0) = (ht, w') := by
        simp [shapesOf, List.getD_eq_getElem?_getD, hci]
      obtain ⟨hn, hq, hk⟩ := hw
      have hc := commits_append_single_of (hist := hist)
        (e := Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))) rfl
      obtain ⟨hlen, hph⟩ := ih _ _ _ (n - 1) hacc' (hc ▸ hws) (hc ▸ hk _) hp
      refine ⟨by simp only [List.length_cons]; omega, fun phase hphase ↦ ?_⟩
      rcases List.mem_cons.mp hphase with rfl | hphase
      · exact ⟨ht, w', word, ps, rfl, hws _ (List.mem_of_getElem? hci), hshape ▸ hq⟩
      · exact hph phase hphase

/-- **The honest prover's stream is at most the program's cost.** -/
theorem proveFrom_stream_le {height : ℕ} {α : Type} :
    ∀ (p : VerifierProgram α) (sp : Sponge) (hist : List Ev) (n : ℕ) {Q : α → Prop}
      {xs : List E} {os : List (List Opening)},
      VerifierProgram.Costs height p n Q → proveFrom h F S fuel p sp hist = some (xs, os) →
      xs.length ≤ n := by
  intro p
  induction p with
  | ret b =>
    intro sp hist n Q xs os _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    simp
  | fail =>
    intro sp hist n Q xs os _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    simp
  | read k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have := ih _ _ _ _ (hc.2 _) hp
    simp only [List.length_cons]
    have := hc.1
    omega
  | sample k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom] at hp
    have := ih _ _ _ _ (hc.2 _) hp
    omega
  | grind bits k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom] at hp
    split at hp
    · cases hp
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      have := ih _ _ _ hc.2 hp
      simp only [List.length_cons]
      have := hc.1
      omega
  | commit ht w k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have := ih _ _ _ hc.2.2 hp
    simp only [List.length_cons]
    have := hc.2.1
    omega
  | query i ps k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      simp
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      have := ih _ _ _ _ (hc.2 _) hp
      omega

end Pure

end LeanVM.Wire

end
