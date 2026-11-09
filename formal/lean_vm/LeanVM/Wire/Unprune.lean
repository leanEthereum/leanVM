/-
  LeanVM.Wire.Unprune

  The unpruning side of the round trip: a phase one Merkle tree opens unprunes from its pruned
  form back to its paths (`unprunePhase_prunePhase`).
-/

module

public import LeanVM.Wire.Spec
import LeanVM.Wire.UnpruneList

/-!
# Unpruning a pruned phase gives back its paths

For a phase `paths` one Merkle tree over `h` opens (`PhaseDecodable h paths height leafWords`),
`unprunePhaseWithHash h (prunePhase paths) = paths`. The climb keeps one invariant
(`NodesAt`): after `k` levels its nodes are `levelNodes positions k`, ascending, each with the
digest `climbTo h p k` of every path `p` through it. At each level the sibling it gives a node is
every path's sibling there (`SiblingsAt`): the level's node at `node ^^^ 1`, the digest of a path
through it (`PhaseDecodable.sibling_node`), or else the carried one, the first distinct path's
(`PhaseDecodable.same_node`); and its parents are the next level's nodes (`levelNodes_succ`),
each hashed as `climbTo` hashes. Each query then gets back its leaf (`same_position`) and its path.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

@[expose] public section

/-- The distinct paths of a phase `prunePhase` keeps: the first at each position, ascending. -/
def distinctPaths (paths : List Opening) : List Opening :=
  dedupByKey Opening.leafIndex (paths.mergeSort fun a b ↦ a.leafIndex ≤ b.leafIndex)

/-- The siblings `prunePhase` carries at level `level`. -/
def carriedAt (paths : List Opening) (level : ℕ) : List (ℕ × Digest) :=
  (carriedSiblings (levelNodes (distinctPositions (paths.map Opening.leafIndex)) level)).map
    fun node ↦ (node, (((distinctPaths paths).find? fun path ↦ path.leafIndex >>> level = node).map
      fun path ↦ path.path.getD level default).getD default)

theorem prunePhase_eq (paths : List Opening) :
    prunePhase paths =
      ⟨paths.map Opening.leafIndex, (paths.head?.map fun path ↦ path.path.length).getD 0,
        (paths.head?.map fun path ↦ path.leaf.length).getD 0,
        distinctPositions (paths.map Opening.leafIndex), (distinctPaths paths).map Opening.leaf,
        (List.range ((paths.head?.map fun path ↦ path.path.length).getD 0)).map
          (carriedAt paths)⟩ := rfl

/-! ## The distinct paths -/

theorem mem_of_mem_distinctPaths {paths : List Opening} {p : Opening}
    (h : p ∈ distinctPaths paths) : p ∈ paths :=
  List.mem_mergeSort.1 (mem_of_mem_dedupByKey _ h)

theorem exists_mem_distinctPaths {paths : List Opening} {p : Opening} (h : p ∈ paths) :
    ∃ q ∈ distinctPaths paths, q.leafIndex = p.leafIndex :=
  exists_mem_dedupByKey _ (List.mem_mergeSort.2 h)

theorem distinctPaths_map_leafIndex (paths : List Opening) :
    (distinctPaths paths).map Opening.leafIndex =
      distinctPositions (paths.map Opening.leafIndex) := by
  rw [distinctPaths, map_dedupByKey]
  have hsorted : ((paths.mergeSort fun a b ↦ a.leafIndex ≤ b.leafIndex).map
      Opening.leafIndex).Pairwise (· ≤ ·) :=
    List.pairwise_map.2 ((List.pairwise_mergeSort
      (le := fun a b : Opening ↦ decide (a.leafIndex ≤ b.leafIndex))
      (fun a b c hab hbc ↦ by simp only [decide_eq_true_eq] at *; omega)
      (fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) paths).imp
      fun h ↦ by simpa using h)
  exact eq_of_pairwise_lt_of_mem_iff (pairwise_lt_dedupByKey_id hsorted)
    (pairwise_lt_distinctPositions _) fun x ↦ by
      simp [mem_dedupByKey_id, mem_distinctPositions]

/-! ## The invariant of the climb -/

/-- After `k` levels: the nodes are `levelNodes positions k`, each with the digest every path
through it climbs to. -/
def NodesAt (h : Bytes → Digest) (paths : List Opening) (k : ℕ) (nodes : List (ℕ × Digest)) :
    Prop :=
  nodes.map Prod.fst = levelNodes (distinctPositions (paths.map Opening.leafIndex)) k ∧
    ∀ x ∈ nodes, ∀ p ∈ paths, p.leafIndex >>> k = x.1 → x.2 = climbTo h p k

/-- The siblings of level `k`: every path's sibling there, at its node. -/
def SiblingsAt (paths : List Opening) (k : ℕ) (siblings : List (ℕ × Digest)) : Prop :=
  ∀ p ∈ paths, siblings.lookup (p.leafIndex >>> k) = some (p.path.getD k default)

theorem mem_levelNodes_of_mem {paths : List Opening} {p : Opening} (hp : p ∈ paths) (k : ℕ) :
    p.leafIndex >>> k ∈ levelNodes (distinctPositions (paths.map Opening.leafIndex)) k :=
  mem_levelNodes.2 ⟨p.leafIndex, mem_distinctPositions.2 (List.mem_map_of_mem hp), rfl⟩

theorem exists_of_mem_levelNodes {paths : List Opening} {k n : ℕ}
    (hn : n ∈ levelNodes (distinctPositions (paths.map Opening.leafIndex)) k) :
    ∃ p ∈ paths, p.leafIndex >>> k = n := by
  obtain ⟨q, hq, rfl⟩ := mem_levelNodes.1 hn
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (mem_distinctPositions.1 hq)
  exact ⟨p, hp, rfl⟩

variable {h : Bytes → Digest} {paths : List Opening} {height leafWords : ℕ}

/-- The sibling `climbLevel` gives the node `node`. -/
def siblingAt (nodes carried : List (ℕ × Digest)) (node : ℕ) : Digest :=
  (nodes.lookup (node ^^^ 1)).getD ((carried.lookup node).getD default)

/-- The parent `climbLevel` hashes from the node `node`, its digest and its sibling. -/
def parentDigest (h : Bytes → Digest) (node : ℕ) (digest sibling : Digest) : Digest :=
  if node % 2 = 0 then h (digestBytes digest ++ digestBytes sibling)
  else h (digestBytes sibling ++ digestBytes digest)

theorem climbLevelWithHash_id (nodes carried : List (ℕ × Digest)) :
    climbLevelWithHash (m := Id) h nodes carried =
      (nodes.map fun x ↦ (x.1, siblingAt nodes carried x.1),
        (nodes.filter fun x ↦ x.1 % 2 = 0 ∨ x.1 ^^^ 1 ∉ nodes.map Prod.fst).map fun x ↦
          (x.1 >>> 1, parentDigest h x.1 x.2 (siblingAt nodes carried x.1))) := by
  unfold climbLevelWithHash
  refine Prod.ext ?_ ((List.idRun_mapM).trans (List.map_congr_left fun x _ ↦ ?_))
  · refine List.map_congr_left fun x _ ↦ ?_
    simp [siblingAt]
  · rcases x with ⟨node, digest⟩
    simp only [parentDigest, siblingAt]
    split <;> simp [*] <;> rfl

theorem lookup_map_fst_key {β : Type} (f : ℕ → Digest) {l : List (ℕ × β)} {a : ℕ}
    (ha : a ∈ l.map Prod.fst) : (l.map fun x ↦ (x.1, f x.1)).lookup a = some (f a) := by
  have : (l.map fun x ↦ (x.1, f x.1)) = (l.map Prod.fst).map fun n ↦ (n, f n) := by
    rw [List.map_map]; rfl
  rw [this]
  exact lookup_map_key f ha

theorem climbLevelsWithHash_cons_id (carried : List (ℕ × Digest))
    (above : List (List (ℕ × Digest))) (nodes : List (ℕ × Digest)) :
    climbLevelsWithHash (m := Id) h (carried :: above) nodes =
      (climbLevelWithHash (m := Id) h nodes carried).1 ::
        climbLevelsWithHash (m := Id) h above (climbLevelWithHash (m := Id) h nodes carried).2 :=
  rfl

theorem unprunePhaseWithHash_id (phase : PrunedPhase) :
    unprunePhaseWithHash (m := Id) h phase =
      phase.queries.map fun query ↦
        ⟨query, ((phase.positions.zip phase.leaves).lookup query).getD [],
          (List.range phase.height).map fun level ↦
            (((climbLevelsWithHash (m := Id) h phase.carried
              (phase.positions.zip (phase.leaves.map fun leaf ↦ h (leaf.flatMap K.toBytes)))).getD
                level []).lookup (query >>> level)).getD default⟩ := by
  unfold unprunePhaseWithHash
  rw [show (phase.leaves.mapM (m := Id) fun leaf ↦ h (leaf.flatMap K.toBytes)) =
    phase.leaves.map fun leaf ↦ h (leaf.flatMap K.toBytes) from List.idRun_mapM]
  rfl

section Climb

variable (hp : PhaseDecodable h paths height leafWords)
include hp

/-- The sibling the climb gives a path's node at a level is the path's sibling there. -/
theorem siblingAt_eq {k : ℕ} (hk : k < height) {nodes : List (ℕ × Digest)}
    (hn : NodesAt h paths k nodes) {p : Opening} (hpm : p ∈ paths) :
    siblingAt nodes (carriedAt paths k) (p.leafIndex >>> k) = p.path.getD k default := by
  unfold siblingAt
  by_cases hsib : (p.leafIndex >>> k) ^^^ 1 ∈ nodes.map Prod.fst
  · obtain ⟨x, hx, hx1, hlook⟩ := lookup_of_mem_map_fst hsib
    rw [hlook, Option.getD_some]
    rw [hn.1] at hsib
    obtain ⟨p', hp', hp'k⟩ := exists_of_mem_levelNodes hsib
    rw [hn.2 x hx p' hp' (hp'k.trans hx1.symm)]
    exact (hp.sibling_node p hpm p' hp' k hk hp'k.symm).symm
  · rw [lookup_eq_none_of_not_mem hsib, Option.getD_none]
    have hmem : p.leafIndex >>> k ∈
        carriedSiblings (levelNodes (distinctPositions (paths.map Opening.leafIndex)) k) := by
      rw [carriedSiblings, List.mem_filter, decide_eq_true_eq, ← hn.1]
      exact ⟨hn.1 ▸ mem_levelNodes_of_mem hpm k, hsib⟩
    unfold carriedAt
    rw [lookup_map_key _ hmem, Option.getD_some]
    obtain ⟨q, hq, hqi⟩ := exists_mem_distinctPaths hpm
    cases hfind : (distinctPaths paths).find?
        (fun path ↦ decide (path.leafIndex >>> k = p.leafIndex >>> k)) with
    | none =>
      exfalso
      have := List.find?_eq_none.1 hfind q hq
      simp [hqi] at this
    | some r =>
      have hr := List.mem_of_find?_eq_some hfind
      have hrp := List.find?_some hfind
      simp only [decide_eq_true_eq] at hrp
      simp only [Option.map_some, Option.getD_some]
      exact (hp.same_node r (mem_of_mem_distinctPaths hr) p hpm k hk hrp).2

/-- The parent the climb hashes at a first child is the digest every path through it climbs to. -/
theorem parentDigest_eq {k : ℕ} (hk : k < height) {nodes : List (ℕ × Digest)}
    (hn : NodesAt h paths k nodes) {x : ℕ × Digest} (hx : x ∈ nodes)
    (hfirst : x.1 % 2 = 0 ∨ x.1 ^^^ 1 ∉ nodes.map Prod.fst) {p : Opening} (hpm : p ∈ paths)
    (hpx : p.leafIndex >>> (k + 1) = x.1 >>> 1) :
    parentDigest h x.1 x.2 (siblingAt nodes (carriedAt paths k) x.1) = climbTo h p (k + 1) := by
  have hxns : x.1 ∈ levelNodes (distinctPositions (paths.map Opening.leafIndex)) k :=
    hn.1 ▸ List.mem_map_of_mem hx
  obtain ⟨p', hp', hp'k⟩ := exists_of_mem_levelNodes hxns
  have hsx : siblingAt nodes (carriedAt paths k) x.1 = p'.path.getD k default := by
    rw [← hp'k]; exact siblingAt_eq hp hk hn hp'
  have hdx : x.2 = climbTo h p' k := hn.2 x hx p' hp' hp'k
  rw [Nat.shiftRight_add, shiftRight_one_eq_iff] at hpx
  show _ = if (p.leafIndex >>> k) % 2 = 0 then
      h (digestBytes (climbTo h p k) ++ digestBytes (p.path.getD k default))
    else h (digestBytes (p.path.getD k default) ++ digestBytes (climbTo h p k))
  rcases hpx with hc | hc
  · have hsame := hp.same_node p' hp' p hpm k hk (hp'k.trans hc.symm)
    rw [parentDigest, hsx, hdx, hc, hsame.1, hsame.2]
  · have hne := mem_levelNodes_of_mem hpm k
    have heven : x.1 % 2 = 0 :=
      hfirst.resolve_right (by rw [hn.1, ← hc]; exact not_not.2 hne)
    have hc' : p.leafIndex >>> k = x.1 + 1 := by rw [hc, xor_one_eq]; simp only [heven, ↓reduceIte]
    have hs : siblingAt nodes (carriedAt paths k) x.1 = climbTo h p k :=
      hsx.trans (hp.sibling_node p' hp' p hpm k hk (by rw [hp'k, hc]))
    have hback : (p.leafIndex >>> k) ^^^ 1 = p'.leafIndex >>> k := by
      have hodd : ¬ (x.1 + 1) % 2 = 0 := by omega
      rw [hp'k, hc', xor_one_eq]
      simp only [hodd, ↓reduceIte]
      omega
    have hd : x.2 = p.path.getD k default :=
      hdx.trans (hp.sibling_node p hpm p' hp' k hk hback).symm
    have hodd : ¬ (p.leafIndex >>> k) % 2 = 0 := by omega
    simp only [parentDigest, heven, hodd, hs, hd, ↓reduceIte]

/-- **One level of the climb**: from the nodes of level `k`, the siblings are every path's at
level `k`, and the parents are the nodes of level `k + 1`. -/
theorem climbLevel_spec {k : ℕ} (hk : k < height) {nodes : List (ℕ × Digest)}
    (hn : NodesAt h paths k nodes) :
    SiblingsAt paths k (climbLevelWithHash (m := Id) h nodes (carriedAt paths k)).1 ∧
      NodesAt h paths (k + 1) (climbLevelWithHash (m := Id) h nodes (carriedAt paths k)).2 := by
  rw [climbLevelWithHash_id]
  refine ⟨fun p hpm ↦ ?_, ?_, ?_⟩
  · rw [lookup_map_fst_key _ (hn.1 ▸ mem_levelNodes_of_mem hpm k)]
    exact congrArg some (siblingAt_eq hp hk hn hpm)
  · rw [← levelNodes_succ ((pairwise_lt_distinctPositions _).imp le_of_lt) k, ← hn.1, List.map_map,
      List.filter_map, List.map_map]
    rfl
  · intro y hy p hpm hpy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have hx' := List.mem_filter.1 hx
    exact parentDigest_eq hp hk hn hx'.1 (by simpa using hx'.2) hpm hpy

/-- **The climb**: from the nodes of level `k`, the `i`-th level's siblings are every path's at
level `k + i`. -/
theorem climbLevels_spec : ∀ (r k : ℕ) (nodes : List (ℕ × Digest)), k + r ≤ height →
    NodesAt h paths k nodes → ∀ i < r, SiblingsAt paths (k + i)
      ((climbLevelsWithHash (m := Id) h ((List.range' k r).map (carriedAt paths)) nodes).getD
        i [])
  | 0, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | r + 1, k, nodes, hkr, hn, i, hi => by
    have hstep := climbLevel_spec hp (by omega : k < height) hn
    rw [List.range'_succ, List.map_cons, climbLevelsWithHash_cons_id]
    cases i with
    | zero => simpa using hstep.1
    | succ i =>
      have := climbLevels_spec r (k + 1) _ (by omega) hstep.2 i (by omega)
      rw [show k + (i + 1) = k + 1 + i by omega, List.getD_cons_succ]
      simpa using this

/-- The leaves' digests are the nodes of level `0`. -/
theorem nodesAt_zero :
    NodesAt h paths 0 ((distinctPositions (paths.map Opening.leafIndex)).zip
      (((distinctPaths paths).map Opening.leaf).map fun leaf ↦ h (leaf.flatMap K.toBytes))) := by
  rw [← distinctPaths_map_leafIndex, List.map_map, List.zip_map']
  refine ⟨?_, fun x hx p hpm hpx ↦ ?_⟩
  · rw [List.map_map, levelNodes_zero (pairwise_lt_distinctPositions _)]
    exact distinctPaths_map_leafIndex paths
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    simp only [Nat.shiftRight_zero] at hpx
    obtain rfl := hp.same_position p hpm q (mem_of_mem_distinctPaths hq) hpx
    rfl

end Climb

theorem range_map_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun i ↦ l.getD i d) = l := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
  simp [List.getD_eq_getElem?_getD, h₂]

/-- **Unpruning a pruned phase gives back its paths** (rtunprune). -/
theorem unprunePhase_prunePhase (hp : PhaseDecodable h paths height leafWords) :
    unprunePhaseWithHash (m := Id) h (prunePhase paths) = paths := by
  have hheight : (paths.head?.map fun path ↦ path.path.length).getD 0 = height := by
    cases paths with
    | nil => exact absurd rfl hp.nonempty
    | cons p _ => simp [(hp.shape p List.mem_cons_self).1]
  rw [unprunePhaseWithHash_id, prunePhase_eq]
  simp only [hheight]
  have hsib : ∀ level < height, SiblingsAt paths level
      ((climbLevelsWithHash (m := Id) h ((List.range height).map (carriedAt paths))
        ((distinctPositions (paths.map Opening.leafIndex)).zip
          (((distinctPaths paths).map Opening.leaf).map fun leaf ↦
            h (leaf.flatMap K.toBytes)))).getD level []) := by
    intro level hlevel
    have := climbLevels_spec hp height 0 _ (by omega) (nodesAt_zero hp) level hlevel
    rw [List.range_eq_range']
    simpa using this
  conv_rhs => rw [← List.map_id paths]
  rw [List.map_map]
  refine List.map_congr_left fun p hpm ↦ ?_
  have hleaf : (((distinctPositions (paths.map Opening.leafIndex)).zip
      ((distinctPaths paths).map Opening.leaf)).lookup p.leafIndex).getD [] = p.leaf := by
    rw [← distinctPaths_map_leafIndex, List.zip_map']
    obtain ⟨q, hq, hqi⟩ := exists_mem_distinctPaths hpm
    obtain ⟨x, hx, hx1, hlook⟩ := lookup_of_mem_map_fst (l := (distinctPaths paths).map
      fun a ↦ (a.leafIndex, a.leaf)) (a := p.leafIndex) (by
        rw [List.map_map]; exact List.mem_map.2 ⟨q, hq, hqi⟩)
    rw [hlook, Option.getD_some]
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    obtain rfl := hp.same_position r (mem_of_mem_distinctPaths hr) p hpm hx1
    rfl
  have hpath : (List.range height).map (fun level ↦
      (((climbLevelsWithHash (m := Id) h ((List.range height).map (carriedAt paths))
        ((distinctPositions (paths.map Opening.leafIndex)).zip
          (((distinctPaths paths).map Opening.leaf).map fun leaf ↦
            h (leaf.flatMap K.toBytes)))).getD level []).lookup (p.leafIndex >>> level)).getD
              default) = p.path := by
    conv_rhs => rw [← range_map_getD p.path default]
    rw [(hp.shape p hpm).1]
    refine List.map_congr_left fun level hlevel ↦ ?_
    rw [hsib level (List.mem_range.1 hlevel) p hpm, Option.getD_some]
  simp only [Function.comp, hleaf, hpath, id]

end

end LeanVM.Wire
