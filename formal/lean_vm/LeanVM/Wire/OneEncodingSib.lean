/-
  LeanVM.Wire.OneEncodingSib

  One encoding, the siblings: for a phase `readPhase` accepted, the paths it unprunes to, with any
  hash, are written back (`Prover.phaseToBytes`) with exactly the siblings the phase carried.
-/

module

public import LeanVM.Wire.OneEncodingRow
public import LeanVM.Wire.ReadDet
public import LeanVM.Wire.Unprune
import LeanVM.Wire.UnpruneList
import all LeanVM.Wire.OneEncodingRow
import Mathlib.Data.List.GetD

/-!
# One encoding: the siblings of a phase

Let `ph` be a phase `readPhase` accepted: its positions the distinct queries ascending, a leaf at
each, and at each level the siblings it carries keyed by the nodes of
`carriedSiblings (levelNodes ph.positions level)`, in order. Unprune it with any hash `h`
(`unprunePhaseWithHash (m := Id) h ph`). Then the siblings `Prover.phaseToBytes` writes back
(`phaseSiblingBytes`) are the carried digests, level by level, in order
(`phaseSiblingBytes_unprunePhase`):

- the unpruned paths at their distinct positions are one path per position, and a path's sibling
  at level `level` depends on its node `position >>> level` only, so the nodes the encoder climbs
  through at each level are `levelNodes ph.positions level`, and the ones whose sibling it writes
  are exactly `carriedSiblings` of them, the nodes the reader read a sibling for (the sibling count
  follows from the positions both ways);
- at such a node the climb's sibling is the carried one, since the node's sibling node is not one
  of the level's (`climbLevel`'s `siblingOf` falls back to the carried digest), so the encoder
  writes each carried digest back, in order.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

public section

/-! ## List facts -/

/-- On a list keyed by distinct keys, the values at its keys in order are its values in order. -/
theorem flatMap_lookup_of_nodup {β γ : Type} (f : β → List γ) (d : β) :
    ∀ {l : List (ℕ × β)}, (l.map Prod.fst).Nodup →
      (l.map Prod.fst).flatMap (fun n ↦ f ((l.lookup n).getD d)) = l.flatMap fun x ↦ f x.2
  | [], _ => rfl
  | (k, v) :: rest, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.flatMap_cons, List.lookup_cons, beq_self_eq_true,
      Option.getD_some]
    rw [← flatMap_lookup_of_nodup f d hnd.2]
    congr 1
    refine List.flatMap_congr fun n hn ↦ ?_
    have hne : n ≠ k := fun e ↦ hnd.1 (e ▸ hn)
    rw [beq_eq_false_iff_ne.2 hne]

/-- A `flatMap` over a list's indices is one over the list. -/
theorem flatMap_range_getD {α β : Type} (f : α → List β) (d : α) (l : List α) :
    (List.range l.length).flatMap (fun i ↦ f (l.getD i d)) = l.flatMap f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
      List.flatMap_append]
    congr 1
    · rw [← ih]
      refine List.flatMap_congr fun i hi ↦ ?_
      rw [List.getD_append _ _ _ _ (List.mem_range.1 hi)]
    · simp

/-! ## The climb at the carried nodes -/

section Climb

variable (h : Bytes → Digest) (positions : List ℕ)

/-- **The climb gives each carried node its carried sibling**: climbing from nodes keyed by
`levelNodes positions k`, with siblings carried keyed by `carriedSiblings` at each level, the
sibling given at level `k + j` to a carried node is the carried one. -/
theorem climbLevelsWithHash_carried (hpos : positions.Pairwise (· ≤ ·)) :
    ∀ (carried : List (List (ℕ × Digest))) (k : ℕ) (nodes : List (ℕ × Digest)),
      nodes.map Prod.fst = levelNodes positions k →
      (∀ j (hj : j < carried.length),
        carried[j].map Prod.fst = carriedSiblings (levelNodes positions (k + j))) →
      ∀ j < carried.length, ∀ n ∈ carriedSiblings (levelNodes positions (k + j)),
        (((climbLevelsWithHash (m := Id) h carried nodes).getD j []).lookup n).getD default =
          ((carried.getD j []).lookup n).getD default
  | [], _, _, _, _, j, hj, _, _ => absurd hj (by simp)
  | c :: above, k, nodes, hnodes, hcarried, j, hj, n, hn => by
    rw [climbLevelsWithHash]
    simp only [bind, pure]
    rw [climbLevelWithHash_id]
    rcases j with _ | j
    · -- the level itself
      simp only [Nat.add_zero, List.getD_cons_zero] at hn ⊢
      have hnn : n ∈ nodes.map Prod.fst := hnodes ▸ (List.mem_filter.1 hn).1
      have hsib : n ^^^ 1 ∉ nodes.map Prod.fst := by
        rw [hnodes]; simpa using (List.mem_filter.1 hn).2
      rw [show (nodes.map fun x ↦ (x.1, siblingAt nodes c x.1)) =
          (nodes.map Prod.fst).map fun n ↦ (n, siblingAt nodes c n) by simp,
        lookup_map_key _ hnn]
      simp [siblingAt, lookup_eq_none_of_not_mem hsib]
    · -- the levels above, from the parents
      simp only [List.getD_cons_succ]
      refine climbLevelsWithHash_carried hpos above (k + 1) _ ?_ (fun i hi ↦ ?_) j
        (by simpa using hj) n (by rwa [show k + 1 + j = k + (j + 1) by omega])
      · rw [List.map_map, ← levelNodes_succ hpos k, ← hnodes, List.filter_map, List.map_map]
        rfl
      · have := hcarried (i + 1) (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this

end Climb

/-! ## The siblings written back -/

/-- **The siblings of an unpruned phase, written back, are the ones it carried**: for a phase
whose positions are its distinct queries ascending, with a leaf at each, and whose carried siblings
are keyed, level by level, by `carriedSiblings (levelNodes ph.positions level)`, the siblings
`Prover.phaseToBytes` writes of the paths it unprunes to, with any hash `h`, are its carried
digests, level by level, in order. -/
theorem phaseSiblingBytes_unprunePhase_of (h : Bytes → Digest) (ph : PrunedPhase)
    (hpositions : ph.positions = distinctPositions ph.queries) (hne : ph.positions ≠ [])
    (hleaves : ph.leaves.length = ph.positions.length)
    (hkeys : ph.carried.map (·.map Prod.fst) =
      (List.range ph.height).map fun level ↦ carriedSiblings (levelNodes ph.positions level)) :
    phaseSiblingBytes (unprunePhaseWithHash (m := Id) h ph) =
      ph.carried.flatMap fun level ↦ level.flatMap fun carried ↦ digestBytes carried.2 := by
  set P := ph.positions
  set R := climbLevelsWithHash (m := Id) h ph.carried
    (P.zip (ph.leaves.map fun leaf ↦ h (leaf.flatMap K.toBytes)))
  set sib : ℕ → ℕ → Digest := fun level n ↦ ((R.getD level []).lookup n).getD default
  set mk : ℕ → Opening := fun query ↦
    ⟨query, ((P.zip ph.leaves).lookup query).getD [],
      (List.range ph.height).map fun level ↦ sib level (query >>> level)⟩ with hmk
  have hpaths : unprunePhaseWithHash (m := Id) h ph = ph.queries.map mk :=
    unprunePhaseWithHash_id ph
  have hlen : ph.carried.length = ph.height := by
    simpa using congrArg List.length hkeys
  have hkey : ∀ j (hj : j < ph.carried.length),
      ph.carried[j].map Prod.fst = carriedSiblings (levelNodes P j) := fun j hj ↦ by
    have := congrArg (fun l ↦ l[j]?) hkeys
    simp only [List.getElem?_map, List.getElem?_range (hlen ▸ hj), List.getElem?_eq_getElem hj,
      Option.map_some, Option.some.injEq] at this
    exact this
  have hlt : P.Pairwise (· < ·) := hpositions ▸ pairwise_lt_distinctPositions _
  -- the paths at their distinct positions
  obtain ⟨q₀, qs, hqs⟩ : ∃ q₀ qs, ph.queries = q₀ :: qs := by
    rcases hq : ph.queries with _ | ⟨q₀, qs⟩
    · exact absurd (by rw [hpositions, hq]; simp [distinctPositions, dedupByKey]) hne
    · exact ⟨q₀, qs, rfl⟩
  have hheight : ((ph.queries.map mk).head?.map fun path ↦ path.path.length).getD 0 =
      ph.height := by
    simp [hqs, hmk]
  have hdistinct : distinctPaths (ph.queries.map mk) = P.map mk := by
    unfold distinctPaths
    rw [← List.map_mergeSort (r := fun a b ↦ decide (a ≤ b)) (fun a _ b _ ↦ rfl),
      dedupByKey_map, hpositions]
    rfl
  -- level by level
  unfold phaseSiblingBytes
  simp only []
  rw [hpaths, hheight, hdistinct, ← hlen, ← flatMap_range_getD _ [] ph.carried]
  refine List.flatMap_congr fun level hlevel ↦ ?_
  have hl : level < ph.carried.length := List.mem_range.1 hlevel
  have hlh : level < ph.height := hlen ▸ hl
  set L := levelNodes P level with hL
  have hnodes : ((P.map mk).map fun path ↦ (path.leafIndex >>> level,
      path.path.getD level default)) =
      (P.map (· >>> level)).map fun n ↦ (n, sib level n) := by
    simp only [List.map_map]
    refine List.map_congr_left fun q _ ↦ ?_
    simp [hmk, List.getD_eq_getElem?_getD, hlh]
  rw [hnodes, dedupByKey_map]
  rw [show dedupByKey (fun n ↦ ((n, sib level n) : ℕ × Digest).1) (P.map (· >>> level)) = L
    from rfl]
  rw [show (L.map fun n ↦ (n, sib level n)).map Prod.fst = L by simp [Function.comp_def],
    List.filter_map, List.flatMap_map]
  have hcarriedL : L.filter (fun n ↦ decide (n ^^^ 1 ∉ L)) = carriedSiblings L := rfl
  simp only [Function.comp_def]
  rw [hcarriedL]
  -- the climb's sibling at a carried node is the carried one
  have hclimb : ∀ n ∈ carriedSiblings L,
      sib level n = ((ph.carried.getD level []).lookup n).getD default := by
    have := climbLevelsWithHash_carried h P (hlt.imp le_of_lt) ph.carried 0
      (P.zip (ph.leaves.map fun leaf ↦ h (leaf.flatMap K.toBytes)))
      (by rw [List.map_fst_zip (by simp [hleaves]), levelNodes_zero hlt])
      (fun j hj ↦ by rw [Nat.zero_add]; exact hkey j hj) level hl
    simpa only [Nat.zero_add] using this
  rw [show (carriedSiblings L).flatMap (fun n ↦ digestBytes (sib level n)) =
      (carriedSiblings L).flatMap
        (fun n ↦ digestBytes (((ph.carried.getD level []).lookup n).getD default)) from
    List.flatMap_congr fun n hn ↦ by rw [hclimb n hn]]
  -- the carried digests in order
  rw [List.getD_eq_getElem _ _ hl, hL, ← hkey level hl]
  refine flatMap_lookup_of_nodup digestBytes default ?_
  rw [hkey level hl]
  exact ((pairwise_lt_levelNodes (hlt.imp le_of_lt) level).filter _).imp ne_of_lt

/-- **The siblings of a phase `readPhase` accepted** (`PhaseRead`), unpruned with any hash `h`
and written back by `Prover.phaseToBytes`, are the siblings it carried, as `encodePhase` writes
them. -/
theorem PhaseRead.phaseSiblingBytes_unprunePhase {ph : PrunedPhase} (hr : PhaseRead ph)
    (h : Bytes → Digest) :
    phaseSiblingBytes (unprunePhaseWithHash (m := Id) h ph) = encodePhaseSiblings ph :=
  phaseSiblingBytes_unprunePhase_of h ph hr.positions_eq hr.positions_ne_nil hr.leaves_length
    hr.carried_keys

/-- **One encoding of a phase**: a phase `readPhase` accepted (`PhaseRead`), unpruned with any
hash `h`, is written back by `Prover.phaseToBytes` as the bytes it was read from
(`encodePhase`): its header and rows (`PhaseRead.phaseHeaderAndRows_unprunePhase`) and its carried
siblings (`PhaseRead.phaseSiblingBytes_unprunePhase`). -/
theorem PhaseRead.phaseToBytes_unprunePhase_eq {ph : PrunedPhase} (hr : PhaseRead ph)
    (h : Bytes → Digest) :
    Prover.phaseToBytes (unprunePhaseWithHash (m := Id) h ph) = encodePhase ph :=
  hr.phaseToBytes_unprunePhase h (hr.phaseSiblingBytes_unprunePhase h)

end

end LeanVM.Wire
