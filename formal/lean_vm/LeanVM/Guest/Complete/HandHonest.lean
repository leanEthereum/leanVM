/-
  LeanVM.Guest.Complete.HandHonest

  The honest pushes by stream, for the hand facts: every entry of `honestPushes` is a split of one of
  the node's lists (`signers_split`), the blob count of the checked matrix (`da_n_blobs`), a child's
  two lists' lengths (`child_meta`), or of a stream of none of these names (`honest_mem`).
-/

module

public import LeanVM.Guest.Complete.MainFinal
public import LeanVM.Guest.B1.Sig.XmssSigPops
public import LeanVM.Guest.B1.Sig.SphincsSigPops
public import LeanVM.Guest.Budget.HandPops
public import LeanVM.Guest.Complete.CoverageEq

/-!
# The honest pushes by stream

`honest_mem` classifies the entries of `honestPushes`: those of the streams the hand facts read
(`signers_split`, `da_n_blobs`, `child_meta`) by their words, the rest by their names (`Others`). With `Budget.every_pathIn_of_streams`, a node's hinted value in one of the three
streams is then such an entry, whatever the memory.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest.B1.Main

@[expose] public section

/-! ## Names -/

/-- The streams a raw signature's pushes name. -/
def rawNames : List String :=
  ["raw_index", "sp_raw_index", "lx_index", "lx_windows", "lx_path", "randomizer", "lx_digits", "chain_starts",
    "sp_rand", "sp_unused", "sp_fors_secrets", "sp_fors_nodes", "sp_counter", "digits", "siblings"]

/-- The streams a child's proof's hints name. -/
def chNames : List String :=
  ["stream_chunks", "stream", "table_logs", "link_shape", "stk_group_order", "split_values", "merkle_leaf_rows",
    "merkle_children", "merkle_caps", "merkle_cap_active"]

/-- A stream other than the three the hand facts read. -/
abbrev Others (a : String) : Prop := a ≠ "signers_split" ∧ a ≠ "da_n_blobs" ∧ a ≠ "child_meta"

theorem raw_others : ∀ a ∈ rawNames, Others a := by decide
theorem ch_others : ∀ a ∈ chNames, Others a := by decide

theorem xmssLayer_names (P : HashSig.PublicParameter) (lay : LeanXmss.Layer) (key : LeanXmss.KeyIndex)
    (M : List UInt8) (part : LeanXmss.LayerSignature) :
    ∀ p ∈ (Prover.xmssLayer P lay key M part).1, p.1 ∈ rawNames := by
  rw [Sig.xmssLayer_fst]
  intro p hp
  simp only [List.mem_append, List.mem_cons, Sig.lxPathPops, List.mem_map] at hp
  rcases hp with ⟨_, -, rfl⟩ | rfl | rfl | ⟨_, -, rfl⟩ <;> simp [rawNames]

theorem xmssHints_names (pk : HashSig.PublicKey) (m : HashSig.Message) (sig : LeanXmss.Signature) :
    ∀ p ∈ Prover.xmssHints pk m sig, p.1 ∈ rawNames := by
  rw [Sig.xmssHints_eq]
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [rawNames]
  rcases List.mem_cons.mp hp with rfl | hp
  · simp [rawNames]
  rcases List.mem_append.mp hp with hp | hp
  · exact xmssLayer_names _ _ _ _ _ p hp
  · exact xmssLayer_names _ _ _ _ _ p hp

theorem sphincsLayer_names (ps : HashSig.PublicParameter) (idx : Sphincs.Index) (σ : Sphincs.Signature)
    (layer : Sphincs.Layer) (signed : HashSig.Digest) :
    ∀ p ∈ (Prover.sphincsLayer ps idx σ layer signed).1, p.1 ∈ rawNames := by
  intro p hp
  simp only [Prover.sphincsLayer, Prover.digitGroups, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hp
  rcases hp with ((rfl | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩ <;> simp [rawNames]

theorem sphincsHints_names (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature) :
    ∀ p ∈ Prover.sphincsHints pk m sig, p.1 ∈ rawNames := by
  rw [Sig.sphincsHints_eq]
  refine names_append (names_append (names_append (names_append (names_append ?_ ?_) ?_)
    (sphincsLayer_names _ _ _ _ _)) (sphincsLayer_names _ _ _ _ _)) (sphincsLayer_names _ _ _ _ _)
  · simp [rawNames]
  · simp [rawNames]
  · intro p hp
    obtain ⟨c, -, hp⟩ := List.mem_flatMap.mp hp
    simp only [Prover.sphincsForsNodes, List.mem_map] at hp
    obtain ⟨_, -, rfl⟩ := hp
    simp [rawNames]

theorem levelHints_chNames (first : Bool) (depth count : ℕ) (phase : List LeanVM.Protocol.Compile.Opening) :
    ∀ p ∈ Prover.levelHints first depth count phase, p.1 ∈ chNames := by
  intro p hp
  simp only [Prover.levelHints, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with ⟨x, -, hx⟩ | rfl | rfl
  · obtain ⟨o, steps, r⟩ := x
    rcases hx with rfl | rfl <;> simp [chNames]
  · simp [chNames]
  · simp [chNames]

theorem merkleHints_chNames : ∀ (first : Bool) (qs : List (ℕ × List ℕ))
    (ps : List (List LeanVM.Protocol.Compile.Opening)), ∀ p ∈ Prover.merkleHints first qs ps, p.1 ∈ chNames
  | first, (d, pos) :: rest, ph :: phs => by
      intro p hp
      rw [Prover.merkleHints, List.mem_append] at hp
      rcases hp with hp | hp
      · exact levelHints_chNames first d pos.length ph p hp
      · exact merkleHints_chNames false rest phs p hp
  | _, [], _ => by intro p hp; simp [Prover.merkleHints] at hp
  | _, _ :: _, [] => by intro p hp; simp [Prover.merkleHints] at hp

theorem childHints_chNames (bc : List K) (seed : Digest) (c : Child) :
    ∀ p ∈ Prover.childHints bc seed c, p.1 ∈ chNames := by
  unfold Prover.childHints
  split
  · simp
  · dsimp only
    refine names_append (names_append (names_append (names_append (names_append ?_ ?_) ?_) ?_) ?_)
      (merkleHints_chNames _ _ _)
    · simp [chNames]
    · intro p hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      simp [chNames]
    · simp [chNames]
    · simp [Prover.stackHints, chNames]
    · simp [chNames]

/-! ## The entries -/

/-- **What an honest entry is**: of a stream of none of the three names, a split of one of the
node's or a child's lists, the checked matrix's blob count, or a child's two lists' lengths. -/
inductive HonestEntry (s : NodeStatement) (w : NodeWitness) : Pop → Prop where
  | other {p : Pop} : Others p.1 → HonestEntry s w p
  | split (n : ℕ) : (n = s.claims.xmss.length ∨ n = s.claims.sphincs.length ∨
      ∃ c ∈ w.children, n = c.statement.claims.xmss.length ∨ n = c.statement.claims.sphincs.length) →
      HonestEntry s w ("signers_split", Prover.listSplit n)
  | blobs (c : DaClaim) (mw : LeanVM.Da.MatrixWitness) : w.daMatrix = some (c, mw) →
      HonestEntry s w ("da_n_blobs", [Prover.count mw.rows.length])
  | childMeta (c : Child) : c ∈ w.children →
      HonestEntry s w ("child_meta", [Prover.count c.statement.claims.xmss.length,
        Prover.count c.statement.claims.sphincs.length])

/-- An entry of a named stream other than the three. -/
macro "hand_oth" : tactic => `(tactic| exact .other ⟨by simp, by simp, by simp⟩)

theorem honestEntry_append {s : NodeStatement} {w : NodeWitness} {l l' : List Pop}
    (h : ∀ p ∈ l, HonestEntry s w p) (h' : ∀ p ∈ l', HonestEntry s w p) : ∀ p ∈ l ++ l', HonestEntry s w p :=
  fun p hp => (List.mem_append.mp hp).elim (h p) (h' p)

theorem honestEntry_names {s : NodeStatement} {w : NodeWitness} {N : List String} {l : List Pop}
    (h : ∀ p ∈ l, p.1 ∈ N) (hN : ∀ a ∈ N, Others a) : ∀ p ∈ l, HonestEntry s w p :=
  fun p hp => .other (hN _ (h p hp))

theorem listPushes_entry {s : NodeStatement} {w : NodeWitness} {es : List Prover.Entry}
    (hn : es.length = s.claims.xmss.length ∨ es.length = s.claims.sphincs.length) :
    ∀ p ∈ Prover.listPushes "claims" es, HonestEntry s w p := by
  intro p hp
  unfold Prover.listPushes at hp
  rcases List.mem_append.mp hp with hp | hp
  · split_ifs at hp
    · simp at hp
    · rw [List.mem_singleton] at hp
      subst hp
      exact .split _ (hn.elim Or.inl fun h => Or.inr (Or.inl h))
  · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp
    hand_oth

theorem childSlotPushes_entry {s : NodeStatement} {w : NodeWitness} {os : List ℕ}
    (hn : ∃ c ∈ w.children, os.length = c.statement.claims.xmss.length ∨
      os.length = c.statement.claims.sphincs.length) :
    ∀ p ∈ Prover.childSlotPushes os, HonestEntry s w p := by
  intro p hp
  unfold Prover.childSlotPushes at hp
  split_ifs at hp
  · simp at hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact .split _ (Or.inr (Or.inr hn))
    rcases List.mem_cons.mp hp with rfl | hp
    · hand_oth
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp
    hand_oth
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact .split _ (Or.inr (Or.inr hn))
    rcases List.mem_cons.mp hp with rfl | hp
    · hand_oth
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp
    hand_oth

/-- A child's slots in a region have the length of one of the children's lists. -/
theorem childSlots_length {α : Type} [BEq α] {D R : List α} {cs : List Child}
    {f : Child → List α} {xs : List ℕ} (h : xs ∈ (Prover.coveragePlan D R (cs.map f)).childSlots) :
    ∃ c ∈ cs, xs.length = (f c).length := by
  have hm : xs.length ∈ (Prover.coveragePlan D R (cs.map f)).childSlots.map List.length := List.mem_map_of_mem h
  rw [(coveragePlan_eq D R _).2.2, Main.plan_children_lengths, List.map_map] at hm
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
  exact ⟨c, hc, he.symm⟩

/-- **Every honest entry is an `HonestEntry`.** -/
theorem honest_mem (s : NodeStatement) (w : NodeWitness) :
    ∀ p ∈ Prover.honestPushes guestBytecode guestSeed s w, HonestEntry s w p := by
  rw [honest_eq, mPreX_eq]
  refine honestEntry_append (honestEntry_append (honestEntry_append (honestEntry_append (honestEntry_append
    (honestEntry_append (honestEntry_append (honestEntry_append (honestEntry_append (honestEntry_append
      ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> hand_oth
  · exact listPushes_entry (Or.inl (List.length_map _))
  · exact listPushes_entry (Or.inr (List.length_map _))
  · intro p hp
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp
    hand_oth
  · intro p hp
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp hp
    hand_oth
  · intro p hp
    obtain ⟨cs, -, hp⟩ := List.mem_flatMap.mp hp
    rcases List.mem_cons.mp hp with rfl | hp
    · hand_oth
    · exact .other (raw_others _ (xmssHints_names _ _ _ p hp))
  · intro p hp
    obtain ⟨cs, -, hp⟩ := List.mem_flatMap.mp hp
    rcases List.mem_cons.mp hp with rfl | hp
    · hand_oth
    · exact .other (raw_others _ (sphincsHints_names _ _ _ p hp))
  · intro p hp
    obtain ⟨⟨⟨c, xs⟩, ss⟩, hm, hp⟩ := List.mem_flatMap.mp hp
    dsimp only at hp
    have hm1 := List.of_mem_zip hm
    have hm2 := List.of_mem_zip hm1.1
    have hx := childSlots_length (f := fun c : Child => c.statement.claims.xmss) hm2.2
    have hs := childSlots_length (f := fun c : Child => c.statement.claims.sphincs) hm1.2
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .childMeta c hm2.1
    refine honestEntry_append (honestEntry_append (honestEntry_append ?_ ?_) ?_)
      (honestEntry_names (childHints_chNames _ _ c) ch_others) p hp
    · obtain ⟨c', hc', he⟩ := hx
      exact childSlotPushes_entry ⟨c', hc', Or.inl he⟩
    · obtain ⟨c', hc', he⟩ := hs
      exact childSlotPushes_entry ⟨c', hc', Or.inr he⟩
    · intro q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl <;> hand_oth
  · intro p hp
    unfold mLA at hp
    split_ifs at hp
    · rw [List.mem_singleton] at hp; subst hp; hand_oth
    · simp only [Prover.batchPushes, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> hand_oth
  · intro p hp
    unfold mDA at hp
    cases hm : w.daMatrix with
    | none => simp [hm] at hp
    | some cm =>
      rw [hm] at hp
      simp only [Option.map_some, Option.getD_some, Prover.daHints, List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false, List.mem_flatMap, List.mem_map] at hp
      rcases hp with (rfl | rfl) | ⟨_, -, _, -, rfl⟩
      · hand_oth
      · exact .blobs cm.1 cm.2 hm
      · hand_oth
  · intro p hp
    rw [List.mem_singleton] at hp; subst hp; hand_oth

end
end LeanVM.Guest.Complete
