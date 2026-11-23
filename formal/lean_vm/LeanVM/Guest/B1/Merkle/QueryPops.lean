/-
  LeanVM.Guest.B1.Merkle.QueryPops

  At the honest values a query's entries are the honest hint generator's for its opening (`Hints.leafCells`, `Hints.climbSteps`), and a level's entries are `Hints.levelHints`', stream by stream.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPops
public import LeanVM.Guest.B1.Merkle.HintPath

/-!
# A query's and a level's entries are the generator's

* `QD.rowPop_eq`: at the honest values a query's row entry is `merkle_leaf_rows` of `Hints.leafCells` of the opened row;
* `WD.wpPops_eq`: an honest walk's entry is `merkle_children` of the generator's steps below the cap;
* `queryEntries`, `query_entries_eq`: an opening's two entries (`Hints.levelHints`' per-opening pushes) from an honest query and walk;
* `levelHints_eq`, `level_sameStreams`: a level's entries, the cap's and the flags' first (as `level_queries` pops them), are `Hints.levelHints`', stream by stream.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {σ : Val}

/-! ## The honest row -/

/-- **At the honest values a query's row is the opened row's leaf cells.** -/
theorem QD.rowPop_eq (d : QD) {first : Bool} (hfirst : d.s.base = 1 ↔ first = true)
    (hrow : d.row.length = rowLen d.s.base d.s.folds) (hv : d.Hv σ) (hI : d.b + d.s.I ≤ d.e) :
    rowPop σ d.b d.s.I = ("merkle_leaf_rows", Hints.leafCells first d.row) := by
  have hcells : (List.range d.s.I).map (fun j => σ (.n (d.b + j))) = (List.range d.s.I).map d.cell :=
    List.map_congr_left fun j hj => by
      have := List.mem_range.mp hj
      rw [hv _ (by omega) (by omega), d.val_row this]
  rw [rowPop, hcells]
  congr 1
  by_cases hb : d.s.base = 1
  · have hf : first = true := hfirst.mp hb
    subst hf
    rw [Hints.leafCells, ite_eq_left rfl]
    rw [rowLen, ite_eq_left hb] at hrow
    refine List.ext_getElem (by simp [Oq.I, hrow]) fun i h1 h2 => ?_
    simp [QD.cell, hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < d.row.length by simpa using h2)]
  · have hf : first = false := by cases first <;> simp_all
    subst hf
    rw [Hints.leafCells, ite_eq_right (by simp)]
    rw [rowLen, ite_eq_right hb] at hrow
    refine List.ext_getElem (by simp [Oq.I, hrow]) fun i h1 h2 => ?_
    simp [QD.cell, hb]

/-! ## The walk -/

/-- **An honest walk's entry is the generator's children below the cap**: its siblings the path's first `pd`, its leaf `q` of a depth-`D` tree, `pd ≤ D`. -/
theorem WD.wpPops_eq (w : WD) {D : ℕ} {path : List Digest} (hs : w.sibs = path.take w.pd) (hD : w.pd ≤ D)
    (hl : w.pd ≤ path.length) :
    w.wpPops = [("merkle_children", ((Hints.climbSteps (2 ^ D + w.q) w.leaf path).1.take w.pd).flatMap
      Hints.stepChildren)] := by
  rw [WD.wpPops, ← pathCells_eq_steps w.leaf path hD hl]
  congr 3
  funext k
  rw [WD.pc, hs]

/-! ## A level -/

/-- **An opening's two entries** in `Hints.levelHints`: its leaf's cells and its children below the cap. -/
def queryEntries (first : Bool) (depth pathDepth : ℕ) (o : Opening) : List (String × Hints.Entry) :=
  [("merkle_leaf_rows", Hints.leafCells first o.leaf),
    ("merkle_children", ((Hints.climbSteps (2 ^ depth + o.leafIndex) (merkleLeafDigest o.leaf) o.path).1.take
      pathDepth).flatMap Hints.stepChildren)]

/-- **An honest query's row and walk entries are its opening's**: the query's row the opening's leaf, its walk's leaf digest the leaf's, its position the leaf index, its siblings the path's first `pd` of a tree of depth `pd + cd`. -/
theorem query_entries_eq (d : QD) (w : WD) {first : Bool} (o : Opening) (hfirst : d.s.base = 1 ↔ first = true)
    (hrow : d.row.length = rowLen d.s.base d.s.folds) (hv : d.Hv σ) (hI : d.b + d.s.I ≤ d.e)
    (hro : d.row = o.leaf) (hleaf : w.leaf = merkleLeafDigest o.leaf) (hq : w.q = o.leafIndex)
    (hs : w.sibs = o.path.take w.pd) (hl : w.pd ≤ o.path.length) :
    rowPop σ d.b d.s.I :: w.wpPops = queryEntries first (w.pd + w.cd) w.pd o := by
  rw [d.rowPop_eq hfirst hrow hv hI, w.wpPops_eq (D := w.pd + w.cd) hs (by omega) hl, hro, hleaf, hq]
  rfl

/-- The pushes of a level's openings, in phase order. -/
def levelPushes (first : Bool) (depth count : ℕ) (phase : List Opening) : List (String × Hints.Entry) :=
  phase.flatMap (queryEntries first depth (depth - Hints.capDepthOf count depth))

/-- The cap's and the flags' pushes of a level. -/
def levelCapPushes (depth count : ℕ) (phase : List Opening) : List (String × Hints.Entry) :=
  let capDepth := Hints.capDepthOf count depth
  let pathDepth := depth - capDepth
  let climbs := phase.map fun o ↦
    (o, Hints.climbSteps (2 ^ depth + o.leafIndex) (merkleLeafDigest o.leaf) o.path)
  let capSteps := climbs.flatMap fun (_, steps, _) ↦ steps.drop pathDepth
  let nodes := capSteps.foldl (fun (a : Array Digest) step ↦
      (a.set! step.1 step.2.1).set! (step.1 ^^^ 1) step.2.2)
    (Array.replicate (2 * 2 ^ capDepth) (Vector.replicate 4 0))
  let nodes := climbs.foldl (fun (a : Array Digest) (_, _, root) ↦ a.set! 1 root) nodes
  let active := capSteps.foldl (fun (a : Array E) step ↦ a.set! (step.1 / 2) 1)
    (Array.replicate (2 ^ capDepth) 0)
  [("merkle_caps", nodes.toList.flatMap Hints.digestCells), ("merkle_cap_active", active.toList)]

theorem levelHints_eq (first : Bool) (depth count : ℕ) (phase : List Opening) :
    Hints.levelHints first depth count phase = levelPushes first depth count phase ++ levelCapPushes depth count phase := by
  simp only [Hints.levelHints, levelPushes, levelCapPushes, List.flatMap_map]
  rfl

/-- **A level's entries, the cap's and the flags' first, are `Hints.levelHints`'**, stream by stream. -/
theorem level_sameStreams (first : Bool) (depth count : ℕ) (phase : List Opening) :
    SameStreams (levelCapPushes depth count phase ++ levelPushes first depth count phase)
      (Hints.levelHints first depth count phase) := by
  rw [levelHints_eq]
  refine sameStreams_append_comm fun p hp r hr => ?_
  simp only [levelCapPushes, List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain ⟨o, -, hr⟩ := List.mem_flatMap.mp hr
  simp only [queryEntries, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hp with rfl | rfl <;> rcases hr with rfl | rfl <;> (dsimp only; decide)

end
end LeanVM.Guest.B1
