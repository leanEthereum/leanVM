/-
  LeanVM.Guest.B1.Main.HeapPushes

  The honest pushes on `heap_sizes`: `main`'s, the claim lists', the blob matrix's advised sizes
  (`Hints.nodeHeapSizes`), then each child's four.
-/

module

public import LeanVM.Guest.B1.Main.MainPushes
public import LeanVM.Guest.B1.Main.L5Segs
public import LeanVM.Guest.B1.VerifySub.ChildHeap

/-!
# The honest advised sizes

`childHeapH bytecode c`, `vsHeapH bytecode w c`: a child's advised sizes, its first four pushes' entries. `heapPushes_eq`:
the entries of `Hints.honestPushes` on `heap_sizes` are those of `Hints.nodeHeapSizes`, then each
child's; every other push is on another stream (`xmssHints_noHeap`, `sphincsHints_noHeap`,
`childHints_heap_filter` and the like).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Node
open LeanVM.Guest.B1.VerifySub (childHeapH)

@[expose] public section

/-- Pushes off the `heap_sizes` stream. -/
def NoHeap (l : List (String × Hints.Entry)) : Prop := ∀ p ∈ l, p.1 ≠ Hints.heapSizeStream

theorem filter_noHeap {l : List (String × Hints.Entry)} (h : NoHeap l) :
    l.filter (·.1 == Hints.heapSizeStream) = [] :=
  List.filter_eq_nil_iff.mpr fun p hp => by simpa using h p hp

theorem noHeap_append {a b : List (String × Hints.Entry)} (ha : NoHeap a) (hb : NoHeap b) : NoHeap (a ++ b) :=
  fun p hp => (List.mem_append.mp hp).elim (ha p) (hb p)

theorem noHeap_cons {q : String × Hints.Entry} {l : List (String × Hints.Entry)} (hq : q.1 ≠ Hints.heapSizeStream)
    (hl : NoHeap l) : NoHeap (q :: l) :=
  fun p hp => (List.mem_cons.mp hp).elim (fun e => e ▸ hq) (hl p)

theorem noHeap_flatMap {α : Type} {l : List α} {f : α → List (String × Hints.Entry)} (h : ∀ a ∈ l, NoHeap (f a)) :
    NoHeap (l.flatMap f) := fun p hp => by
  obtain ⟨a, ha, hp⟩ := List.mem_flatMap.mp hp
  exact h a ha p hp

theorem noHeap_names {l : List (String × Hints.Entry)} {L : List String} (h : ∀ p ∈ l, p.1 ∈ L)
    (hL : Hints.heapSizeStream ∉ L) : NoHeap l := fun p hp e => hL (e ▸ h p hp)

/-! ## The signatures' and the Merkle hints -/

theorem xmssLayer_noHeap (a : HashSig.PublicParameter) (b : LeanXmss.Layer) (c : LeanXmss.KeyIndex)
    (d : List UInt8) (e : LeanXmss.LayerSignature) : NoHeap (Hints.xmssLayer a b c d e).1 := by
  simp [NoHeap, Hints.xmssLayer, Hints.heapSizeStream, or_imp, forall_and, forall_exists_index, forall_eq]

theorem xmssHints_noHeap (pk : HashSig.PublicKey) (m : HashSig.Message) (σ : LeanXmss.Signature) :
    NoHeap (Hints.xmssHints pk m σ) := by
  unfold Hints.xmssHints
  dsimp only
  exact noHeap_cons (by simp [Hints.heapSizeStream]) (noHeap_cons (by simp [Hints.heapSizeStream])
    (noHeap_append (xmssLayer_noHeap _ _ _ _ _) (xmssLayer_noHeap _ _ _ _ _)))

theorem sphincsLayer_noHeap (a : HashSig.PublicParameter) (b : Sphincs.Index) (c : Sphincs.Signature)
    (d : Sphincs.Layer) (e : HashSig.Digest) : NoHeap (Hints.sphincsLayer a b c d e).1 := by
  simp [NoHeap, Hints.sphincsLayer, Hints.digitGroups, Hints.heapSizeStream, or_imp, forall_and, and_imp,
    forall_exists_index, forall_eq]

theorem sphincsHints_noHeap (pk : Sphincs.PublicKey) (m : HashSig.Message) (σ : Sphincs.Signature) :
    NoHeap (Hints.sphincsHints pk m σ) := by
  unfold Hints.sphincsHints
  dsimp only
  refine noHeap_append (noHeap_append (noHeap_append (noHeap_append (noHeap_append ?_ ?_) ?_)
    (sphincsLayer_noHeap _ _ _ _ _)) (sphincsLayer_noHeap _ _ _ _ _)) (sphincsLayer_noHeap _ _ _ _ _)
  · simp [NoHeap, Hints.heapSizeStream, or_imp, forall_and, forall_eq]
  · simp [NoHeap, Hints.heapSizeStream, forall_exists_index]
  · intro p hp
    obtain ⟨_, -, hp⟩ := List.mem_flatMap.mp hp
    simp only [Hints.sphincsForsNodes, List.mem_map] at hp
    obtain ⟨_, _, rfl⟩ := hp
    simp [Hints.heapSizeStream]

theorem levelHints_noHeap (first : Bool) (depth count : ℕ) (phase : List Opening) :
    NoHeap (Hints.levelHints first depth count phase) := by
  intro p hp
  simp only [Hints.levelHints, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with ⟨_, _, rfl | rfl⟩ | rfl | rfl <;> simp [Hints.heapSizeStream]

theorem merkleHints_noHeap : ∀ (first : Bool) (qs : List (ℕ × List ℕ)) (phases : List (List Opening)),
    NoHeap (Hints.merkleHints first qs phases)
  | first, (d, ps) :: rest, ph :: phs => by
    rw [Hints.merkleHints]
    exact noHeap_append (levelHints_noHeap first d ps.length ph) (merkleHints_noHeap false rest phs)
  | _, [], _ => by unfold Hints.merkleHints; exact fun _ h => by simp at h
  | _, _ :: _, [] => by unfold Hints.merkleHints; exact fun _ h => by simp at h

/-! ## A child's pushes -/

/-- **Child `c`'s advised sizes**, none past the children. -/
def vsHeapH (bytecode : List K) (w : NodeWitness) (c : ℕ) : List (List E) :=
  (w.children[c]?.map (childHeapH bytecode)).getD []

/-- **A child's pushes on `heap_sizes` are its first four.** -/
theorem childHints_heap_filter (bytecode : List K) (seed : Digest) (c : Child) :
    ((Hints.childHints bytecode seed c).filter (·.1 == Hints.heapSizeStream)).map (·.2) = childHeapH bytecode c := by
  rcases h : announcedLayoutAndRate bytecode c.proof.stream with _ | ⟨layout, r⟩
  · simp [Hints.childHints, childHeapH, h]
  · simp only [Hints.childHints, childHeapH, h]
    rw [List.append_assoc, List.filter_append, filter_noHeap (noHeap_append (fun p hp => ?_)
      (merkleHints_noHeap _ _ _)), List.append_nil, List.filter_eq_self.mpr fun p hp => ?_]
    · simp [Hints.heapSizeEntry]
    · obtain ⟨n, -, rfl⟩ := List.mem_map.mp hp
      simp [Hints.heapSizeEntry]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [Hints.heapSizeStream]

theorem childSlotPushes_noHeap (offsets : List ℕ) : NoHeap (Hints.childSlotPushes offsets) := by
  intro p hp
  unfold Hints.childSlotPushes at hp
  split at hp
  · simp at hp
  · simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [Hints.heapSizeStream]
    split at hp
    · simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨_, _, rfl⟩ <;> simp [Hints.heapSizeStream]
    · simp only [List.mem_cons, List.mem_map] at hp
      rcases hp with rfl | ⟨_, _, rfl⟩ <;> simp [Hints.heapSizeStream]

/-- **The children's pushes on `heap_sizes`**: each child's advised sizes, in order. -/
theorem childSeg_heap (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    ((childSeg bytecode seed s w).filter (·.1 == Hints.heapSizeStream)).map (·.2) =
      (List.range' 0 w.children.length).flatMap (vsHeapH bytecode w) := by
  have hx : (xPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (plan_children_lengths s.claims.xmss (w.xmssSignatures.map (·.1))
      (w.children.map (·.statement.claims.xmss)))
    simp only [List.length_map] at this
    exact this
  have hs : (sPlan s w).childSlots.length = w.children.length := by
    have := congrArg List.length (plan_children_lengths s.claims.sphincs (w.sphincsSignatures.map (·.1))
      (w.children.map (·.statement.claims.sphincs)))
    simp only [List.length_map] at this
    exact this
  have hlen : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots).length = w.children.length := by
    simp [hx, hs]
  rw [childSeg, flatMap_eq_range _ ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots), hlen,
    ← List.range_eq_range', List.filter_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun c hc => ?_
  have hc' : c < w.children.length := List.mem_range.mp hc
  have e : ((w.children.zip (xPlan s w).childSlots).zip (sPlan s w).childSlots)[c]? =
      some ((w.children[c], (xPlan s w).childSlots.getD c []), (sPlan s w).childSlots.getD c []) := by
    rw [List.getElem?_eq_getElem (by rw [hlen]; exact hc'), List.getElem_zip, List.getElem_zip,
      List.getD_eq_getElem _ _ (by rw [hx]; exact hc'), List.getD_eq_getElem _ _ (by rw [hs]; exact hc')]
  rw [e, Option.map_some, Option.getD_some, vsHeapH, List.getElem?_eq_getElem hc', Option.map_some,
    Option.getD_some, ← childHints_heap_filter bytecode seed]
  simp only [List.cons_append, List.filter_cons, List.filter_append, List.append_assoc]
  rw [filter_noHeap (childSlotPushes_noHeap _), filter_noHeap (childSlotPushes_noHeap _)]
  simp [Hints.heapSizeStream]

/-! ## A node's pushes -/

/-- **The honest pushes on `heap_sizes`**: `Hints.nodeHeapSizes`' entries, then each child's advised sizes. -/
theorem heapPushes_eq (bytecode : List K) (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    ((Hints.honestPushes bytecode seed s w).filter (·.1 == Hints.heapSizeStream)).map (·.2) =
      (Hints.nodeHeapSizes s w (xPlan s w).duplicates.length (sPlan s w).duplicates.length).map
        (fun o => (o.map Hints.count).toList) ++
      (List.range' 0 w.children.length).flatMap (vsHeapH bytecode w) := by
  have hH : Hints.honestPushes bytecode seed s w = [("meta", [Hints.count s.claims.xmss.length,
      Hints.count (xPlan s w).duplicates.length, Hints.count w.xmssSignatures.length, Hints.count s.claims.sphincs.length,
      Hints.count (sPlan s w).duplicates.length, Hints.count w.sphincsSignatures.length,
      Hints.count w.children.length, Hints.count ((w.daMatrix.map fun _ ↦ 1).getD 0)]),
      ("fs_seed", Hints.digestCells seed)] ++
    (Hints.nodeHeapSizes s w (xPlan s w).duplicates.length (sPlan s w).duplicates.length).map Hints.heapSizeEntry ++
    Hints.listPushes "claims" (s.claims.xmss.map fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2) ++
    Hints.listPushes "claims" (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2) ++
    ((xPlan s w).duplicates.map (fun c ↦ Hints.claimCells c.1.root c.1.parameter c.2) ++
      (sPlan s w).duplicates.map (fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2)).map ("dup_claims", ·) ++
    (w.xmssSignatures.zip (xPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("raw_index", [Hints.count slot]) :: Hints.xmssHints c.1.1 c.1.2 c.2) ++
    (w.sphincsSignatures.zip (sPlan s w).directSlots).flatMap
      (fun (c, slot) ↦ ("sp_raw_index", [Hints.count slot]) :: Hints.sphincsHints c.1.1 c.1.2 c.2) ++
    childSeg bytecode seed s w ++ leafSeg s w ++ daSeg w ++ [("da_pick", [Hints.count (Hints.daPick s w)])] := by
    rfl
  have hl : ∀ (item : String) (es : List Hints.Entry), item ≠ Hints.heapSizeStream → NoHeap (Hints.listPushes item es) := by
    intro item es hi p hp
    simp only [Hints.listPushes, List.mem_append, List.mem_map] at hp
    rcases hp with hp | ⟨_, _, rfl⟩
    · split at hp
      · simp at hp
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        simp [Hints.heapSizeStream]
    · exact hi
  have hleaf : NoHeap (leafSeg s w) := by
    intro p hp
    unfold leafSeg at hp
    split at hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; simp [Hints.heapSizeStream]
    · simp only [Hints.batchPushes, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [Hints.heapSizeStream]
  have hda : NoHeap (daSeg w) := noHeap_names daSeg_names (by decide)
  rw [hH]
  simp only [List.filter_append]
  rw [filter_noHeap (show NoHeap [("meta", _), ("fs_seed", _)] by
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [Hints.heapSizeStream]),
    List.filter_eq_self.mpr (fun p hp => by obtain ⟨n, -, rfl⟩ := List.mem_map.mp hp; simp [Hints.heapSizeEntry]),
    filter_noHeap (hl "claims" _ (by decide)), filter_noHeap (hl "claims" _ (by decide)),
    filter_noHeap (show NoHeap (List.map (fun e => ("dup_claims", e)) _) by
      intro p hp; obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp; simp [Hints.heapSizeStream]),
    filter_noHeap (noHeap_flatMap fun ⟨_, _⟩ _ => noHeap_cons (by simp [Hints.heapSizeStream])
      (xmssHints_noHeap _ _ _)),
    filter_noHeap (noHeap_flatMap fun ⟨_, _⟩ _ => noHeap_cons (by simp [Hints.heapSizeStream])
      (sphincsHints_noHeap _ _ _)),
    filter_noHeap hleaf, filter_noHeap hda, filter_noHeap (show NoHeap [("da_pick", _)] by
      intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp
      simp [Hints.heapSizeStream]), ← childSeg_heap bytecode seed s w]
  simp [List.map_map, Function.comp_def, Hints.heapSizeEntry]

end

end LeanVM.Guest.B1.Main
