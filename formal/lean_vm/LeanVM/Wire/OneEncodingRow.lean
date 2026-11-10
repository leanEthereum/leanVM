/-
  LeanVM.Wire.OneEncodingRow

  One encoding, the header and the rows: for a phase `readPhase` accepted, the paths it unprunes
  to, with any hash, are written back (`Prover.phaseToBytes`) with the header and the rows read.
-/

module

public import LeanVM.Wire.ReadDet
public import LeanVM.Wire.Unprune
import LeanVM.Wire.UnpruneList

/-!
# One encoding: the header and the rows of a phase

`Prover.phaseToBytes paths` is the header and the rows (`phaseHeaderAndRows paths`: the queries'
count and positions, the height, the leaf width, the row width and the rows) followed by the
siblings (`phaseSiblingBytes paths`), `phaseToBytes_eq_append`; likewise `encodePhase phase` is
`encodePhaseHeaderAndRows phase ++ encodePhaseSiblings phase` (`encodePhase_eq_append`).

For a phase `readPhase` accepted (`PhaseRead phase`) and the paths it unprunes to with any hash
`h`, `unprunePhaseWithHash h phase`, the header and rows written are the phase's
(`PhaseRead.phaseHeaderAndRows_unprunePhase`): one path per query, at the query's position, so the
count and positions are the queries'; the first path has the phase's height and leaf width; the
paths at the distinct positions, ascending, are one per position (`distinctPaths`), each with the
phase's leaf there, so the common leading zeros, the row width and the rows are the phase's. The
row width is then the one read (`zeroPrefix_map_paddedLeaf`, `LeanVM.Wire.ReadDet`). The siblings
are `LeanVM.Wire.OneEncodingSib`'s; with them a phase is written as it was read
(`PhaseRead.phaseToBytes_unprunePhase`).

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

public section

/-! ## The split of `Prover.phaseToBytes` -/

/-- What `Prover.phaseToBytes paths` writes before the siblings: the queries' count and positions,
the height, the leaf width, the row width, and the rows. -/
def phaseHeaderAndRows (paths : List Opening) : Bytes :=
  let height := (paths.head?.map fun path ↦ path.path.length).getD 0
  let leafWords := (paths.head?.map fun path ↦ path.leaf.length).getD 0
  let distinct := distinctPaths paths
  let zeros := zeroPrefix (distinct.map Opening.leaf)
  Prover.u32Bytes paths.length ++ paths.flatMap (fun path ↦ Prover.u64Bytes path.leafIndex) ++
    Prover.u32Bytes height ++ Prover.u32Bytes leafWords ++ Prover.u32Bytes (leafWords - zeros) ++
    distinct.flatMap (fun path ↦ (path.leaf.drop zeros).flatMap K.toBytes)

/-- What `Prover.phaseToBytes paths` writes after the rows: level by level from the leaves, the
sibling of each node the distinct paths climb through (the first path's) whose sibling node is not
one of them, left to right. -/
def phaseSiblingBytes (paths : List Opening) : Bytes :=
  let height := (paths.head?.map fun path ↦ path.path.length).getD 0
  let distinct := distinctPaths paths
  (List.range height).flatMap fun level ↦
    let nodes := dedupByKey Prod.fst (distinct.map fun path ↦
      (path.leafIndex >>> level, path.path.getD level default))
    (nodes.filter fun (node, _) ↦ node ^^^ 1 ∉ nodes.map Prod.fst).flatMap
      fun (_, sibling) ↦ digestBytes sibling

/-- **The split**: a phase's encoding is its header and rows, then its siblings. -/
theorem phaseToBytes_eq_append (paths : List Opening) :
    Prover.phaseToBytes paths = phaseHeaderAndRows paths ++ phaseSiblingBytes paths := by
  unfold Prover.phaseToBytes phaseHeaderAndRows phaseSiblingBytes distinctPaths zeroPrefix
  simp only [List.append_assoc, List.map_map]
  rfl

/-! ## The split of `encodePhase` -/

/-- The header and rows of a pruned phase, as `encodePhase` writes them: the queries' count and
positions, the height, the leaf width, the row width (the leaf width less the leading zero words
every leaf has, `zeroPrefix`) and each leaf without them. -/
def encodePhaseHeaderAndRows (phase : PrunedPhase) : Bytes :=
  let zeros := zeroPrefix phase.leaves
  Prover.u32Bytes phase.queries.length ++ phase.queries.flatMap Prover.u64Bytes ++
    Prover.u32Bytes phase.height ++ Prover.u32Bytes phase.leafWords ++
    Prover.u32Bytes (phase.leafWords - zeros) ++
    phase.leaves.flatMap (fun leaf ↦ (leaf.drop zeros).flatMap K.toBytes)

/-- The siblings a pruned phase carries, as `encodePhase` writes them: their digests, level by
level, in order. -/
def encodePhaseSiblings (phase : PrunedPhase) : Bytes :=
  phase.carried.flatMap fun level ↦ level.flatMap fun carried ↦ digestBytes carried.2

/-- **The split** of a pruned phase's bytes: its header and rows, then its siblings. -/
theorem encodePhase_eq_append (phase : PrunedPhase) :
    encodePhase phase = encodePhaseHeaderAndRows phase ++ encodePhaseSiblings phase := by
  simp only [encodePhase, encodePhaseHeaderAndRows, encodePhaseSiblings, List.append_assoc]

/-! ## List facts -/

theorem dedupByKey_map {α β γ : Type} [DecidableEq γ] (g : α → β) (key : β → γ) :
    ∀ l : List α, dedupByKey key (l.map g) = (dedupByKey (fun a ↦ key (g a)) l).map g
  | [] => rfl
  | a :: rest => by
    rw [List.map_cons, dedupByKey, dedupByKey, dedupByKey_map g key rest]
    rcases dedupByKey (fun a ↦ key (g a)) rest with _ | ⟨b, kept⟩
    · rfl
    · by_cases hc : key (g a) = key (g b) <;> simp [hc]

/-- Looking up each key of a list without repeats, zipped with values, gives the values. -/
theorem map_lookup_zip {β : Type} (d : β) :
    ∀ (keys : List ℕ) (values : List β), keys.Nodup → values.length = keys.length →
      keys.map (fun key ↦ ((keys.zip values).lookup key).getD d) = values
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | k :: ks, v :: vs, hnd, hlen => by
    rw [List.nodup_cons] at hnd
    simp only [List.zip_cons_cons, List.map_cons, List.lookup_cons, beq_self_eq_true,
      Option.getD_some, List.cons.injEq, true_and]
    refine (List.map_congr_left fun key hkey ↦ ?_).trans
      (map_lookup_zip d ks vs hnd.2 (by simpa using hlen))
    have hne : key ≠ k := fun e ↦ hnd.1 (e ▸ hkey)
    simp [beq_eq_false_iff_ne.2 hne]

/-! ## The header and rows of the paths a phase unprunes to -/

/-- The header and rows of the paths `phase.queries.map g`, where `g q` opens position `q` with a
path of the phase's height, and the leaves at the phase's distinct positions are its leaves, each
of its leaf width. -/
theorem phaseHeaderAndRows_map (phase : PrunedPhase) (g : ℕ → Opening)
    (hidx : ∀ q, (g q).leafIndex = q) (hpath : ∀ q, (g q).path.length = phase.height)
    (hpos : phase.positions = distinctPositions phase.queries) (hne : phase.queries ≠ [])
    (hleaves : phase.positions.map (fun q ↦ (g q).leaf) = phase.leaves)
    (hwidth : ∀ leaf ∈ phase.leaves, leaf.length = phase.leafWords) :
    phaseHeaderAndRows (phase.queries.map g) = encodePhaseHeaderAndRows phase := by
  rcases phase with ⟨queries, height, leafWords, positions, leaves, carried⟩
  dsimp only at hpath hpos hne hleaves hwidth ⊢
  have hdist : distinctPaths (queries.map g) = positions.map g := by
    unfold distinctPaths
    rw [← List.map_mergeSort (r := fun a b ↦ decide (a ≤ b)) (fun a _ b _ ↦ by simp [hidx]),
      dedupByKey_map, show (fun a ↦ (g a).leafIndex) = id from funext hidx, hpos]
    rfl
  obtain ⟨q0, qs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hq0 : q0 ∈ positions := hpos ▸ mem_distinctPositions.2 List.mem_cons_self
  have hw0 : (g q0).leaf.length = leafWords :=
    hwidth _ (hleaves ▸ List.mem_map_of_mem (f := fun q ↦ (g q).leaf) hq0)
  have hmap : (positions.map g).map Opening.leaf = leaves := by
    rw [List.map_map]; exact hleaves
  unfold phaseHeaderAndRows encodePhaseHeaderAndRows
  simp only [hdist, hmap, List.length_map, List.head?_map, List.head?_cons, Option.map_some,
    Option.getD_some, hpath, hw0, List.flatMap_map, hidx]
  rw [← hleaves, List.flatMap_map]

/-- **The header and rows of an unpruned phase**: for a phase whose positions are its queries'
distinct ones, at least one, with a leaf of `leafWords` words at each, the paths it unprunes to
with any hash are written with its header and rows. -/
theorem phaseHeaderAndRows_unprunePhase_of (h : Bytes → Digest) {phase : PrunedPhase}
    (hpos : phase.positions = distinctPositions phase.queries) (hne : phase.queries ≠ [])
    (hlen : phase.leaves.length = phase.positions.length)
    (hwidth : ∀ leaf ∈ phase.leaves, leaf.length = phase.leafWords) :
    phaseHeaderAndRows (unprunePhaseWithHash (m := Id) h phase) =
      encodePhaseHeaderAndRows phase := by
  rw [unprunePhaseWithHash_id (h := h)]
  have hnd : phase.positions.Nodup := by
    rw [hpos]; exact (pairwise_lt_distinctPositions _).imp (ne_of_lt)
  exact phaseHeaderAndRows_map phase _ (fun _ ↦ rfl) (fun _ ↦ by simp) hpos hne
    (map_lookup_zip [] _ _ hnd hlen) hwidth

/-- **The header and rows of a read phase**: for a phase `readPhase` accepted (`PhaseRead`), the
paths it unprunes to with any hash `h` are written (`Prover.phaseToBytes`) with its header and rows
(`encodePhase`'s): as many queries at the same positions, its height, leaf width and row width, and
its leaves at its distinct positions. -/
theorem PhaseRead.phaseHeaderAndRows_unprunePhase {phase : PrunedPhase} (hr : PhaseRead phase)
    (h : Bytes → Digest) :
    phaseHeaderAndRows (unprunePhaseWithHash (m := Id) h phase) = encodePhaseHeaderAndRows phase :=
  phaseHeaderAndRows_unprunePhase_of h hr.positions_eq
    (fun hq ↦ hr.positions_ne_nil (by
      rw [hr.positions_eq, hq]; simp [distinctPositions, dedupByKey]))
    hr.leaves_length hr.leaf_length

/-- **One encoding, given the siblings**: for a phase `readPhase` accepted, if the siblings written
for the paths it unprunes to with `h` are the ones it carries (`LeanVM.Wire.OneEncodingSib`), the
paths are written as the phase's bytes. -/
theorem PhaseRead.phaseToBytes_unprunePhase {phase : PrunedPhase} (hr : PhaseRead phase)
    (h : Bytes → Digest)
    (hsib : phaseSiblingBytes (unprunePhaseWithHash (m := Id) h phase) =
      encodePhaseSiblings phase) :
    Prover.phaseToBytes (unprunePhaseWithHash (m := Id) h phase) = encodePhase phase := by
  rw [phaseToBytes_eq_append, encodePhase_eq_append, hr.phaseHeaderAndRows_unprunePhase h, hsib]

end

end LeanVM.Wire
