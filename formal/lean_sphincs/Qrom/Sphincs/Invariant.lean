module

public import Qrom.Sphincs.Bridge

@[expose] public section

/-!
# What the revealed keys exclude

Every revealed key satisfies `Qrom.Sphincs.Inv`: the revealed keys never hold `SK.seed` nor
`SK.prf`, hold the randomizer of a message only once it is logged, a FORS secret only at a leaf a
logged digest opens, and a chain value only at or above the digit a logged signature opens at its
key (`Qrom.Sphincs.inv_of_mem_rev`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

open Classical in
/-- The FORS leaves the logged digests open. -/
def revealedLeaves (d : Data) (s : Log) : Disclosures := fun index κ ↦
  Finset.univ.filter fun leaf ↦ ∃ e ∈ s.1, digestIndex (digestH (hOf d) e.1) = index ∧
    digestLeaves (digestH (hOf d) e.1) κ = leaf

/-- The property every revealed key has. -/
def Inv (d : Data) (s : Log) : Option Key → Prop
  | none => False
  | some .prf => False
  | some (.rnd m) => ∃ e ∈ s.1, e.1 = m
  | some (.fts index κ leaf) => leaf ∈ revealedLeaves d s index κ
  | some (.ots lay tree leaf c) => ∃ e ∈ s.1, some (.ots lay tree leaf c) ∈ chainKeys (hOf d) e.1
  | some (.pos (.chain lay tree leaf c j)) =>
    (∃ e ∈ s.1, some (.ots lay tree leaf c) ∈ chainKeys (hOf d) e.1) ∨
      ∃ e ∈ s.1, ∃ j' : ChainStep, j'.val ≤ j.val ∧
        some (.pos (.chain lay tree leaf c j')) ∈ chainKeys (hOf d) e.1
  | some _ => True

theorem chainKey_cases (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)
    (digit : Digit) :
    chainKey lay tree leaf c digit = some (.ots lay tree leaf c) ∨
      ∃ j : ChainStep, chainKey lay tree leaf c digit = some (.pos (.chain lay tree leaf c j)) := by
  unfold chainKey
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem not_chain_of_treePosition (lay : Layer) (tree : TreeIndex) :
    ∀ l hl idx, ∀ lay' tree' leaf' c j, treePosition lay tree l hl idx ≠ .chain lay' tree' leaf' c j
  | 0, _, _ => by intros; simp [treePosition]
  | _ + 1, _, _ => by intros; simp [treePosition]

theorem not_chain_of_forsAt {index : Index} {p : Position} (hp : forsAt index p) :
    ∀ lay tree leaf c j, p ≠ .chain lay tree leaf c j := by
  intro lay tree leaf c j h
  subst h
  exact hp

theorem not_chain_of_treeAt {index : Index} {p : Position} (hp : treeAt index p) :
    ∀ lay tree leaf c j, p ≠ .chain lay tree leaf c j := by
  intro lay tree leaf c j h
  subst h
  exact hp

/-- The keys a logged signature reads have the property. -/
theorem inv_keysRead (d : Data) (s : Log) (e : Message × Option Signature) (he : e ∈ s.1)
    (q : Option Key) (hq : q ∈ keysRead (hOf d) e.1) : Inv d s q := by
  classical
  simp only [keysRead, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hq
  rcases hq with rfl | ((((⟨call, rfl⟩ | ⟨x, rfl⟩) | ⟨κ, rfl⟩) | ⟨⟨p, hp⟩, rfl⟩) | hq)
  · exact ⟨e, he, rfl⟩
  · trivial
  · trivial
  · simp only [Inv, revealedLeaves, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, he, rfl, rfl⟩
  · cases p with
    | chain lay tree leaf c j =>
      exact absurd rfl (hp.elim (fun h ↦ not_chain_of_forsAt h lay tree leaf c j)
        fun h ↦ not_chain_of_treeAt h lay tree leaf c j)
    | _ => trivial
  · -- a chain coordinate the signature opens
    have hq' := hq
    unfold chainKeys at hq'
    split at hq'
    · simp at hq'
    · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq'
      obtain ⟨⟨lay, c⟩, hx⟩ := hq'
      rcases chainKey_cases lay _ _ c _ with hk | ⟨j, hk⟩
      · rw [hk] at hx
        subst hx
        exact ⟨e, he, hk ▸ hq⟩
      · rw [hk] at hx
        subst hx
        exact Or.inr ⟨e, he, j, le_rfl, hk ▸ hq⟩

theorem topRootPos_not_chain : ∀ lay tree leaf c j, topRootPos ≠ .chain lay tree leaf c j :=
  not_chain_of_treePosition _ _ _ _ _

/-- **Every revealed key has the property.** -/
theorem inv_of_mem_rev (d : Data) (s : Log) (q : Option Key) (hq : q ∈ rev d s) : Inv d s q := by
  have hr := mem_rev.mp hq
  clear hq
  induction hr with
  | base hb =>
    simp only [baseKeys, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset] at hb
    rcases hb with hb | ⟨e, he, hb⟩
    · simp only [pubKeys, Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · trivial
      · simp only [Inv]
        split
        · rename_i h; simp at h
        · rename_i h; simp at h
        · rename_i h; simp at h
        · rename_i h; simp at h
        · rename_i h; simp at h
        · rename_i lay tree leaf c j h
          simp only [Option.some.injEq, Key.pos.injEq] at h
          exact absurd h (topRootPos_not_chain lay tree leaf c j)
        · trivial
    · exact inv_keysRead d s e he _ hb
  | @derive k hdeps ih =>
    cases k with
    | pkSeed => trivial
    | prf => exact ih none (by simp [deps])
    | ots => exact (ih none (by simp [deps])).elim
    | fts => exact (ih none (by simp [deps])).elim
    | rnd m => exact (ih (some .prf) (by simp [deps])).elim
    | pos p =>
      cases p with
      | chain lay tree leaf c j =>
        by_cases hj : j.val = 0
        · have h := ih (some (.ots lay tree leaf c)) (by simp [deps, secretDep, hj])
          exact Or.inl h
        · have hc : Position.chain lay tree leaf c ⟨j.val - 1, by omega⟩ ∈
              (Position.chain lay tree leaf c j).children := by
            simp [Position.children, show 0 < j.val by omega]
          have h := ih (some (.pos (.chain lay tree leaf c ⟨j.val - 1, by omega⟩)))
            (by simp only [deps, Finset.mem_insert, Finset.mem_union, List.mem_toFinset,
              List.mem_map]; exact Or.inr (Or.inr ⟨_, hc, rfl⟩))
          rcases h with h | ⟨e, he, j', hj', hm⟩
          · exact Or.inl h
          · exact Or.inr ⟨e, he, j', by simp only at hj'; omega, hm⟩
      | _ => trivial
    | enc => trivial
    | dig => trivial

end Qrom.Sphincs
