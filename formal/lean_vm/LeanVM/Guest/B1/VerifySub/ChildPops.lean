/-
  LeanVM.Guest.B1.VerifySub.ChildPops

  A child's in-guest verification pops what `Hints.childHints` pushes, stream by stream: `verify_sub`'s stream and heights, `certify_placement`'s column group order, `verify_tables`' block group order and round count, `open_stacked`'s Merkle entries; and the advised `HeapBuf` sizes are the honest buffers'.
-/

module

public import LeanVM.Guest.B1.VerifySub.NodePops
public import LeanVM.Guest.B1.VerifySub.C.Own
public import LeanVM.Guest.B1.VerifySub.GroupOrderCol
-- Private: `guest_const%` inserts literals.
import LeanVM.Guest.Data.Source

/-!
# A child's pops against its hints

* `childHints_some`: on an announced layout, `childHints` is its four advised sizes, the stream, `zc_tau_max`, the heights, the two group orders, then the Merkle entries;
* `childHints_heap`: the advised sizes are `verify_sub`'s `zeta` buffer (`vsSizes d`'s sixth, `d` the bus depth) and `verify_tables`' three round buffers, from the largest height;
* `heap_words`: a heap hint's words, read where the memory holds a buffer;
* `vsPops_honest`, `cpPop_honest`, `vtPops_honest`: the nodes' own entries on the honest buffers and values;
* `childPops_sameStreams`: those entries, and `open_stacked`'s, are `childHints`' past the sizes, stream by stream;
* `vs_child_pops`: a valid `verify_sub` node on the honest stream and `dims_g` pops them, given its `certify_placement`, `verify_tables` and `open_stacked` callees pop theirs.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The hints -/

/-- The entries `childHints` pushes past its advised sizes and before its Merkle entries. -/
def childMid (stream : List E) (layout : Layout) : List (String × Hints.Entry) :=
  [("stream", vsStreamW stream), ("zc_tau_max", [Hints.count (layout.tableLogHeights.foldl max 0)]),
    ("table_logs", layout.tableLogHeights.map Hints.count), ("col_group_order", Hints.colGroupOrder layout),
    ("block_group_order", Hints.blockGroupOrder layout)]

/-- The advised sizes `childHints` pushes. -/
def childHeap (layout : Layout) : List ℕ :=
  [(busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth,
    (layout.tableLogHeights.foldl max 0 + 1) * guest_const% ROUND_SLOTS, layout.tableLogHeights.foldl max 0 + 1,
    layout.tableLogHeights.foldl max 0 + 1]

theorem childHints_some {bytecode : List K} {seed : Digest} {c : Child} {layout : Layout} {r : ℕ}
    (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, r)) :
    Hints.childHints bytecode seed c = (childHeap layout).map (Hints.heapSizeEntry ∘ some) ++ childMid c.proof.stream layout ++
      Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings := by
  simp only [Hints.childHints, hann, childHeap, childMid, vsStreamW, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]

/-- **The advised sizes are the honest buffers'**: `verify_sub`'s `zeta`, of the bus depth `d`, and `verify_tables`'
round coefficients, products and prefixes, from the largest height `n`. -/
theorem childHints_heap {bytecode : List K} {seed : Digest} {c : Child} {layout : Layout} {r d n : ℕ}
    (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, r))
    (hd : (busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth = d)
    (hn : layout.tableLogHeights.foldl max 0 = n) :
    (Hints.childHints bytecode seed c).take 4 =
      [(vsSizes d).getD 5 0, 7 * (n + 1), n + 1, n + 1].map (Hints.heapSizeEntry ∘ some) := by
  rw [childHints_some hann, List.append_assoc ((childHeap layout).map _), List.take_left' (l₁ := (childHeap layout).map (Hints.heapSizeEntry ∘ some)) (by simp [childHeap]), childHeap, hd, hn]
  simp [vsSizes, Nat.mul_comm]

/-- **A child's pops are its hints past the sizes**, stream by stream: the stream and the heights, the column group
order, the block group order and the round count, then `open_stacked`'s, given those are the Merkle entries. -/
theorem childPops_sameStreams {bytecode : List K} {seed : Digest} {c : Child} {layout : Layout} {r : ℕ}
    (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, r)) {os : List Pop}
    (hos : SameStreams os (Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings)) :
    SameStreams ([("stream", vsStreamW c.proof.stream), ("table_logs", layout.tableLogHeights.map Hints.count)] ++
      [("col_group_order", Hints.colGroupOrder layout)] ++
      [("block_group_order", Hints.blockGroupOrder layout),
        ("zc_tau_max", [Hints.count (layout.tableLogHeights.foldl max 0)])] ++ os)
      ((Hints.childHints bytecode seed c).drop 4) := by
  rw [childHints_some hann, List.append_assoc ((childHeap layout).map _),
    List.drop_left' (l₁ := (childHeap layout).map (Hints.heapSizeEntry ∘ some)) (by simp [childHeap]), childMid]
  refine SameStreams.append ?_ hos
  have e : ∀ (a b c d e : Pop), [a, b] ++ [c] ++ [d, e] = [a] ++ ([b, c, d] ++ [e]) := fun _ _ _ _ _ => rfl
  rw [e, show ∀ (a b c d e : Pop), [a, b, c, d, e] = [a] ++ ([b] ++ [c, d, e]) from fun _ _ _ _ _ => rfl]
  refine (SameStreams.refl _).append (sameStreams_append_comm ?_)
  intro p hp q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
  rcases hp with rfl | rfl | rfl <;> (rw [hq]; dsimp only; decide)

/-! ## The honest entries -/

variable {rd : Reader} {σ : Val}

/-- **A heap hint's words** where the memory holds a buffer. -/
theorem heap_words {p : V} {b off len : ℕ} {ws : List E} (hp : σ p = ofK (addressOfIndex b))
    (h : ReadsAt rd (ofK (addressOfIndex b)) ws) (hl : off + len ≤ ws.length) :
    (Dest.heap p off len).words rd σ = (ws.drop off).take len := by
  refine List.ext_getElem (by simp [Dest.words]; omega) fun k h1 h2 => ?_
  simp only [Dest.words, List.length_map, List.length_range] at h1
  simp only [Dest.words, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, hp]
  rw [(h (off + k) (by omega)).2]
  rfl

/-- **`verify_sub`'s own entries on the honest buffers**: the stream padded, the heights. -/
theorem vsPops_honest {b1 b3 lm : ℕ} {stream : List E} {hs : List ℕ} (h1 : σ (.n 25) = ofK (addressOfIndex b1))
    (h3 : σ (.n 71) = ofK (addressOfIndex b3)) (hm1 : ReadsAt rd (ofK (addressOfIndex b1)) (vsStreamW stream))
    (hm3 : ReadsAt rd (ofK (addressOfIndex b3)) (vsDimsW lm hs)) (hst : stream.length ≤ Coverage.childStreamCap)
    (hl : hs.length = 6) :
    vsPops rd σ = [("stream", vsStreamW stream), ("table_logs", hs.map Hints.count)] := by
  have hw : (vsStreamW stream).length = 8192 := by
    simp only [vsStreamW, List.length_append, List.length_replicate]
    have : Coverage.childStreamCap = 8192 := rfl
    omega
  rw [vsPops, heap_words h1 hm1 (by omega), heap_words h3 hm3 (by simp [vsDimsW, hl]), List.drop_zero,
    List.take_of_length_le (by omega)]
  simp [vsDimsW, hl]

/-- **`certify_placement`'s entry on its group order's buffer.** -/
theorem cpPop_honest {b : ℕ} {ws : List E} (h : σ (.n 136) = ofK (addressOfIndex b))
    (hm : ReadsAt rd (ofK (addressOfIndex b)) ws) (hl : ws.length = 9) : cpPop rd σ = ("col_group_order", ws) := by
  rw [cpPop, heap_words h hm (by omega), List.drop_zero, List.take_of_length_le (by omega)]

/-- **`verify_tables`' entries on its block group order's buffer and its round count `g^n`.** -/
theorem vtPops_honest {b n : ℕ} {ws : List E} (h : σ (.n 36) = ofK (addressOfIndex b))
    (hm : ReadsAt rd (ofK (addressOfIndex b)) ws) (hl : ws.length = 24) (hz : σ (.n 2544) = gen ^ n)
    (hn : n < 2 ^ 64) : vtPops rd σ = [("block_group_order", ws), ("zc_tau_max", [Hints.count n])] := by
  rw [vtPops, heap_words h hm (by omega), List.drop_zero, List.take_of_length_le (by omega), hz,
    count_eq_gen hn]

/-! ## The node -/

/-- **A valid `verify_sub` node on the honest stream and `dims_g` pops `childHints` past its sizes**, stream by
stream, given its `certify_placement` callee pops the column group order, its `verify_tables` callee the block group
order and the round count, and its `open_stacked` callee the Merkle entries. -/
theorem vs_child_pops {bytecode : List K} {seed : Digest} {c : Child} {layout : Layout} {r : ℕ}
    (hann : announcedLayoutAndRate bytecode c.proof.stream = some (layout, r)) {bufs : List ℕ} {kids : List Memory.Tree}
    {args rets : List E} (hv : (Memory.Tree.node "verify_sub" σ bufs kids).Valid coreProgram rd args rets)
    {b1 b3 lm : ℕ} (h1 : σ (.n 25) = ofK (addressOfIndex b1)) (h3 : σ (.n 71) = ofK (addressOfIndex b3))
    (hm1 : ReadsAt rd (ofK (addressOfIndex b1)) (vsStreamW c.proof.stream))
    (hm3 : ReadsAt rd (ofK (addressOfIndex b3)) (vsDimsW lm layout.tableLogHeights))
    (hst : c.proof.stream.length ≤ Coverage.childStreamCap) (hl : layout.tableLogHeights.length = 6) :
    ∃ (tcp tvt tos : Memory.Tree) (i : ℕ), ∃ hi : i < vsOpen.length, σ (.n 278) = ofK (addressOfIndex i) ∧
      tcp.name = "certify_placement" ∧ tcp.Valid coreProgram rd [σ (.n 83), σ (.n 4)] [σ (.n 274), σ (.n 275)] ∧
      tvt.name = "verify_tables" ∧
      tvt.Valid coreProgram rd
        (([562, 563, 564, 565, 566, 567, 0, 1, 254, 253, 71, 26, 4, 335, 559, 6, 569, 568, 572, 570].map V.n).map σ)
        (((List.range 10).map fun k => V.n (573 + k)).map σ) ∧
      tos.name = vsOpen[i] ∧
      tos.Valid coreProgram rd (([66, 1370, 1371, 1372, 1373, 1374, 1917, 268, 271, 1919, 1921].map V.n).map σ)
        (((List.range 5).map fun k => V.n (1922 + k)).map σ) ∧ tcp ∈ kids ∧ tvt ∈ kids ∧ tos ∈ kids ∧
      (tcp.pops coreProgram rd = [("col_group_order", Hints.colGroupOrder layout)] →
        tvt.pops coreProgram rd = [("block_group_order", Hints.blockGroupOrder layout),
          ("zc_tau_max", [Hints.count (layout.tableLogHeights.foldl max 0)])] →
        SameStreams (tos.pops coreProgram rd)
          (Hints.merkleHints true (Hints.childQueries bytecode seed c) c.proof.openings) →
        SameStreams ((Memory.Tree.node "verify_sub" σ bufs kids).pops coreProgram rd)
          ((Hints.childHints bytecode seed c).drop 4)) := by
  obtain ⟨tcp, tvt, tos, i, hi, hx, ncp, vcp, nvt, vvt, nos, vos, icp, ivt, ios, e⟩ := vs_pops hv
  refine ⟨tcp, tvt, tos, i, hi, hx, ncp, vcp, nvt, vvt, nos, vos, icp, ivt, ios, fun ecp evt eos => ?_⟩
  rw [e, vsPops_honest h1 h3 hm1 hm3 hst hl, ecp, evt, List.append_assoc]
  exact childPops_sameStreams hann eos

end
end LeanVM.Guest.B1.VerifySub
