/-
  LeanVM.Wire.Prune

  The encoder's side of the round trip: `readPhase` reads back what `Prover.phaseToBytes` writes
  of a decodable phase, `prunePhase`, and `readProof` what `Proof.toBytes` writes.
-/

module

public import LeanVM.Wire.Spec
public import LeanVM.Wire.PruneList
public import LeanVM.Wire.ReadWrite

/-!
# Reading back the pruned encoding

`readPhase (Prover.phaseToBytes paths ++ rest) = some (prunePhase paths, rest)` for a phase one
Merkle tree opens (`PhaseDecodable`), and `readProof proof.toBytes = some (proof.stream,
proof.openings.map prunePhase)` for a proof that survives its encoding (`WireDecodable`).

The written row width is the least that drops only zeros, so the minimality guard passes; the
siblings written at each level are those of `carriedSiblings (levelNodes positions level)`, in
order, as the reader recomputes them from the distinct positions; the positions are below
`2 ^ height ≤ 2 ^ 32`, so their 32-bit words read back; the distinct leaves padded back are the
leaves.

The pruning idea is scaraven's (https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Wire.PruneList

namespace Prune

/-- The two limbs of each stream element, in order. -/
def limbWords (s : List E) : List K :=
  s.flatMap fun x ↦ [x.limb 0, x.limb 1]

theorem limbWords_toBytes (s : List E) :
    (limbWords s).flatMap K.toBytes = s.flatMap E.toBytes := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    simp only [limbWords] at ih
    simp [limbWords, ih, E.toBytes]

theorem length_limbWords (s : List E) : (limbWords s).length = 2 * s.length := by
  induction s with
  | nil => rfl
  | cons x s ih => simp [limbWords] at ih ⊢; omega

/-- `readProof`'s regrouping of the stream's words gives the stream back. -/
theorem regroup_limbWords :
    ∀ s : List E, (List.range s.length).map (fun i ↦ E.ofLimbs ((limbWords s).getD (2 * i) 0)
      ((limbWords s).getD (2 * i + 1) 0)) = s
  | [] => rfl
  | x :: s => by
    have ih := regroup_limbWords s
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg₂ List.cons ?_ (Eq.trans ?_ ih)
    · simpa [limbWords] using (CompPoly.Extension.Ext.ext fun i ↦ by fin_cases i <;> rfl :
        E.ofLimbs (x.limb 0) (x.limb 1) = x)
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp, limbWords, List.flatMap_cons]
      have h2 : 2 * (i + 1) = 2 * i + 2 := by ring
      simp [List.getD_eq_getElem?_getD, h2, Nat.add_assoc]

/-- The stream's form of `readProof_toBytes`, from `readWords_toBytes` (`ReadWrite`'s
`streamOfWords`, `streamWords` are not exposed). -/
theorem readStream_of_readWords (s : List E) (rest : Bytes) : ∃ ws,
      readWords (2 * s.length) (s.flatMap E.toBytes ++ rest) = some (ws, rest) ∧
        (List.range s.length).map (fun i ↦
          E.ofLimbs (ws.getD (2 * i) 0) (ws.getD (2 * i + 1) 0)) = s :=
  ⟨limbWords s, by rw [← length_limbWords, ← limbWords_toBytes]; exact readWords_toBytes _ _,
    regroup_limbWords s⟩

theorem zip_map_self {α β : Type} (f : α → β) :
    ∀ l : List α, l.zip (l.map f) = l.map fun a ↦ (a, f a)
  | [] => rfl
  | a :: l => by simp [zip_map_self f l]

/-- The siblings a level writes: the filter of nodes paired with their values. -/
theorem filter_flatMap_pairs (N : List ℕ) (v : ℕ → Digest) (nodes : List (ℕ × Digest))
    (hnodes : nodes = N.map fun n ↦ (n, v n)) :
    (nodes.filter fun (node, _) ↦ node ^^^ 1 ∉ nodes.map Prod.fst).flatMap
        (fun (_, sibling) ↦ digestBytes sibling) =
      ((carriedSiblings N).map v).flatMap digestBytes := by
  subst hnodes
  simp [carriedSiblings, List.filter_map, List.flatMap_map, Function.comp_def]

/-- `readCarriedSiblings` reads back the carried siblings level by level, whatever their values. -/
theorem readCarriedSiblings_bytes (positions : List ℕ)
    (v : ℕ → ℕ → Digest) (rest : Bytes) :
    ∀ (remaining level : ℕ),
      readCarriedSiblings positions level remaining
          ((List.range' level remaining).flatMap
            (fun l ↦ ((carriedSiblings (levelNodes positions l)).map (v l)).flatMap digestBytes)
            ++ rest) =
        some ((List.range' level remaining).map
          (fun l ↦ (carriedSiblings (levelNodes positions l)).map fun n ↦ (n, v l n)), rest)
  | 0, level => by simp [readCarriedSiblings]
  | remaining + 1, level => by
    have ih := readCarriedSiblings_bytes positions v rest remaining (level + 1)
    have hd := readDigests_digestBytes
      ((carriedSiblings (levelNodes positions level)).map (v level))
      ((List.range' (level + 1) remaining).flatMap
            (fun l ↦ ((carriedSiblings (levelNodes positions l)).map (v l)).flatMap digestBytes)
            ++ rest)
    rw [List.length_map] at hd
    simp only [List.range'_succ, List.flatMap_cons, List.map_cons, List.append_assoc,
      readCarriedSiblings]
    rw [hd]
    simp only [Option.bind_eq_bind, Option.bind_some, ih, zip_map_self]

theorem guard_some {p : Prop} [Decidable p] (hp : p) : (guard p : Option Unit) = some () := by
  simp [guard, hp]

end Prune

open Prune

section Phase

namespace Prune

/-- The paths sorted by position. -/
abbrev sortedPaths (paths : List Opening) : List Opening :=
  paths.mergeSort fun a b ↦ a.leafIndex ≤ b.leafIndex

/-- The distinct paths, ascending, the first path at each position. -/
abbrev distinctPaths (paths : List Opening) : List Opening :=
  dedupByKey Opening.leafIndex (sortedPaths paths)

/-- The first path's height, as the encoder takes it. -/
def headHeight (paths : List Opening) : ℕ :=
  (paths.head?.map fun path ↦ path.path.length).getD 0

/-- The first path's leaf width, as the encoder takes it. -/
def headLeafWords (paths : List Opening) : ℕ :=
  (paths.head?.map fun path ↦ path.leaf.length).getD 0

/-- The leading zero words of a leaf. -/
abbrev leadingZeros (leaf : List K) : ℕ :=
  (leaf.takeWhile fun word ↦ decide (word = 0)).length

/-- The zero words every distinct leaf starts with, as the encoder counts them. -/
def zerosOf (paths : List Opening) : ℕ :=
  (((distinctPaths paths).map fun path ↦
    (path.leaf.takeWhile fun word ↦ decide (word = 0)).length).min?).getD 0

/-- The nodes of a level with the first distinct path's sibling at each, as the encoder pairs
them. -/
def levelPairs (paths : List Opening) (level : ℕ) : List (ℕ × Digest) :=
  dedupByKey Prod.fst ((distinctPaths paths).map fun path ↦
    (path.leafIndex >>> level, path.path.getD level default))

/-- The siblings the encoder writes at a level. -/
def levelBytes (paths : List Opening) (level : ℕ) : List UInt8 :=
  let nodes := levelPairs paths level
  (nodes.filter fun (node, _) ↦ node ^^^ 1 ∉ nodes.map Prod.fst).flatMap
    fun (_, sibling) ↦ digestBytes sibling

/-- The sibling `prunePhase` keys by a node of a level. -/
def valueAt (paths : List Opening) (level node : ℕ) : Digest :=
  (((distinctPaths paths).find? fun path ↦ path.leafIndex >>> level = node).map
    fun path ↦ path.path.getD level default).getD default

theorem phaseToBytes_eq (paths : List Opening) :
    Prover.phaseToBytes paths =
      Prover.u32Bytes paths.length ++ paths.flatMap (fun path ↦ Prover.u32Bytes path.leafIndex) ++
        Prover.u32Bytes (headHeight paths) ++ Prover.u32Bytes (headLeafWords paths) ++
        Prover.u32Bytes (headLeafWords paths - zerosOf paths) ++
        (distinctPaths paths).flatMap (fun path ↦ (path.leaf.drop (zerosOf paths)).flatMap
          K.toBytes) ++
        (List.range (headHeight paths)).flatMap (levelBytes paths) := rfl

theorem prunePhase_eq (paths : List Opening) :
    prunePhase paths =
      ⟨paths.map Opening.leafIndex, headHeight paths, headLeafWords paths,
        distinctPositions (paths.map Opening.leafIndex), (distinctPaths paths).map Opening.leaf,
        (List.range (headHeight paths)).map fun level ↦
          (carriedSiblings (levelNodes (distinctPositions (paths.map Opening.leafIndex)) level)).map
            fun node ↦ (node, valueAt paths level node)⟩ := rfl

theorem distinctPaths_positions (paths : List Opening) :
    (distinctPaths paths).map Opening.leafIndex =
      distinctPositions (paths.map Opening.leafIndex) := by
  rw [distinctPaths, map_dedupByKey Opening.leafIndex id Opening.leafIndex (fun _ ↦ rfl),
    sortedPaths, List.map_mergeSort (s := fun a b ↦ decide (a ≤ b)) (fun _ _ _ _ ↦ rfl)]
  rfl

theorem mem_paths_of_mem_distinctPaths {paths : List Opening} {p : Opening}
    (hp : p ∈ distinctPaths paths) : p ∈ paths :=
  List.mem_mergeSort.1 (mem_of_mem_dedupByKey hp)

theorem distinctPaths_ne_nil {paths : List Opening} (h : paths ≠ []) :
    distinctPaths paths ≠ [] := by
  apply dedupByKey_ne_nil
  intro hs
  simp only [sortedPaths] at hs
  have := (List.mergeSort_perm paths fun a b ↦ decide (a.leafIndex ≤ b.leafIndex)).length_eq
  rw [hs] at this
  exact h (List.eq_nil_of_length_eq_zero this.symm)

variable {h : Bytes → Digest} {paths : List Opening} {height leafWords : ℕ}

theorem headHeight_eq (hp : PhaseDecodable h paths height leafWords) :
    headHeight paths = height := by
  cases paths with
  | nil => exact absurd rfl hp.nonempty
  | cons p ps => simp [headHeight, (hp.shape p List.mem_cons_self).1]

theorem headLeafWords_eq (hp : PhaseDecodable h paths height leafWords) :
    headLeafWords paths = leafWords := by
  cases paths with
  | nil => exact absurd rfl hp.nonempty
  | cons p ps => simp [headLeafWords, (hp.shape p List.mem_cons_self).2]

theorem zerosOf_spec (hp : PhaseDecodable h paths height leafWords) :
    (∀ p ∈ distinctPaths paths, zerosOf paths ≤ leadingZeros p.leaf) ∧
      ∃ p ∈ distinctPaths paths, leadingZeros p.leaf = zerosOf paths := by
  have hne : ((distinctPaths paths).map fun path ↦ leadingZeros path.leaf) ≠ [] := by
    simpa using distinctPaths_ne_nil hp.nonempty
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (List.isSome_min?_of_ne_nil hne)
  have hzeq : zerosOf paths = z := by simp only [zerosOf]; rw [hz]; rfl
  rw [List.min?_eq_some_iff] at hz
  obtain ⟨hmem, hle⟩ := hz
  rw [hzeq]
  refine ⟨fun p hp' ↦ hle _ (List.mem_map_of_mem hp'), ?_⟩
  obtain ⟨p, hp', hpz⟩ := List.mem_map.1 hmem
  exact ⟨p, hp', hpz⟩

theorem leaf_length_of_mem (hp : PhaseDecodable h paths height leafWords) {p : Opening}
    (hmem : p ∈ distinctPaths paths) : p.leaf.length = leafWords :=
  (hp.shape p (mem_paths_of_mem_distinctPaths hmem)).2

theorem zerosOf_le (hp : PhaseDecodable h paths height leafWords) : zerosOf paths ≤ leafWords := by
  obtain ⟨p, hmem, hpz⟩ := (zerosOf_spec hp).2
  rw [← hpz, ← leaf_length_of_mem hp hmem]
  exact (List.takeWhile_sublist _).length_le

theorem valueAt_spec (hp : PhaseDecodable h paths height leafWords) {level : ℕ}
    (hlevel : level < height) {p : Opening} (hmem : p ∈ distinctPaths paths) :
    valueAt paths level (p.leafIndex >>> level) = p.path.getD level default := by
  have hsome : ((distinctPaths paths).find? fun path ↦
      path.leafIndex >>> level = p.leafIndex >>> level).isSome :=
    List.find?_isSome.2 ⟨p, hmem, by simp⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome
  have hqmem := List.mem_of_find?_eq_some hq
  have hqp : q.leafIndex >>> level = p.leafIndex >>> level := by simpa using List.find?_some hq
  simp only [valueAt, hq, Option.map_some, Option.getD_some]
  exact (hp.same_node q (mem_paths_of_mem_distinctPaths hqmem) p
    (mem_paths_of_mem_distinctPaths hmem) level hlevel hqp).2

theorem levelPairs_eq (hp : PhaseDecodable h paths height leafWords) {level : ℕ}
    (hlevel : level < height) :
    levelPairs paths level =
      (levelNodes (distinctPositions (paths.map Opening.leafIndex)) level).map
        fun n ↦ (n, valueAt paths level n) := by
  have hfst : (levelPairs paths level).map Prod.fst =
      levelNodes (distinctPositions (paths.map Opening.leafIndex)) level := by
    rw [levelPairs, map_dedupByKey Prod.fst id Prod.fst (fun _ ↦ rfl), levelNodes,
      ← distinctPaths_positions, List.map_map, List.map_map]
    rfl
  rw [← hfst, List.map_map]
  conv_lhs => rw [← List.map_id (levelPairs paths level)]
  apply List.map_congr_left
  intro x hx
  obtain ⟨p, hpmem, rfl⟩ := List.mem_map.1 (mem_of_mem_dedupByKey hx)
  simp [valueAt_spec hp hlevel hpmem]

theorem levelBytes_eq (hp : PhaseDecodable h paths height leafWords) {level : ℕ}
    (hlevel : level < height) :
    levelBytes paths level =
      ((carriedSiblings (levelNodes (distinctPositions (paths.map Opening.leafIndex)) level)).map
        (valueAt paths level)).flatMap digestBytes :=
  filter_flatMap_pairs _ _ _ (levelPairs_eq hp hlevel)

end Prune

variable {h : Bytes → Digest} {paths : List Opening} {height leafWords : ℕ}

/-- **`readPhase` reads back a decodable phase's encoding.** -/
theorem readPhase_phaseToBytes (h : Bytes → Digest)
    (hp : PhaseDecodable h paths height leafWords) (rest : Bytes) :
    readPhase (Prover.phaseToBytes paths ++ rest) = some (prunePhase paths, rest) := by
  have hH := headHeight_eq hp
  have hL := headLeafWords_eq hp
  have hz := zerosOf_spec hp
  have hzL := zerosOf_le hp
  have h32 : 2 ^ height ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hp.height_le
  have hqs : ∀ n ∈ paths.map Opening.leafIndex, n < 2 ^ height := by
    intro n hn
    obtain ⟨p, hpmem, rfl⟩ := List.mem_map.1 hn
    exact hp.position_lt p hpmem
  have hcount : paths.length < 2 ^ 32 :=
    lt_of_le_of_lt hp.queries_le (by norm_num [wireMaxQueries])
  -- the rows the encoder writes
  have hrowLen : ∀ r ∈ (distinctPaths paths).map (fun p ↦ p.leaf.drop (zerosOf paths)),
      r.length = leafWords - zerosOf paths := by
    intro r hr
    obtain ⟨p, hpmem, rfl⟩ := List.mem_map.1 hr
    simp [leaf_length_of_mem hp hpmem]
  have hrowCount : ((distinctPaths paths).map (fun p ↦ p.leaf.drop (zerosOf paths))).length =
      (distinctPositions (paths.map Opening.leafIndex)).length := by
    rw [← distinctPaths_positions, List.length_map, List.length_map]
  have hleaves : ((distinctPaths paths).map (fun p ↦ p.leaf.drop (zerosOf paths))).map
      (fun row ↦ paddedLeaf row leafWords) = (distinctPaths paths).map Opening.leaf := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p hpmem
    have hlen := leaf_length_of_mem hp hpmem
    simp only [Function.comp, paddedLeaf, List.length_drop, hlen, Nat.sub_sub_self hzL]
    exact replicate_append_drop _ _ (hz.1 p hpmem)
  have hminimal : ¬ (0 < leafWords - zerosOf paths ∧
      ∀ leaf ∈ (distinctPaths paths).map Opening.leaf,
        leaf.getD (leafWords - (leafWords - zerosOf paths)) 0 = 0) := by
    rintro ⟨hpos, hall⟩
    obtain ⟨p, hpmem, hpz⟩ := hz.2
    have hlen := leaf_length_of_mem hp hpmem
    simp only [leadingZeros] at hpz
    have hne := getD_ne_zero_of_takeWhile p.leaf (by omega)
    apply hne
    have := hall p.leaf (List.mem_map_of_mem hpmem)
    rwa [Nat.sub_sub_self hzL, ← hpz] at this
  have hlast : ∃ last ∈ (distinctPositions (paths.map Opening.leafIndex)).getLast?,
      last >>> height = 0 := by
    have hne : distinctPositions (paths.map Opening.leafIndex) ≠ [] := by
      rw [← distinctPaths_positions]
      simpa using distinctPaths_ne_nil hp.nonempty
    have hmemD : ∀ x ∈ distinctPositions (paths.map Opening.leafIndex), x < 2 ^ height := by
      intro x hx
      rw [← distinctPaths_positions] at hx
      obtain ⟨p, hpmem, rfl⟩ := List.mem_map.1 hx
      exact hp.position_lt p (mem_paths_of_mem_distinctPaths hpmem)
    refine ⟨_, List.getLast?_eq_some_getLast hne, ?_⟩
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (hmemD _ (List.getLast_mem hne))]
  have hsiblings : (List.range height).flatMap (levelBytes paths) =
      (List.range' 0 height).flatMap (fun l ↦ ((carriedSiblings (levelNodes
        (distinctPositions (paths.map Opening.leafIndex)) l)).map (valueAt paths l)).flatMap
          digestBytes) := by
    rw [← List.range_eq_range']
    simp only [List.flatMap]
    congr 1
    apply List.map_congr_left
    intro l hl
    exact levelBytes_eq hp (List.mem_range.1 hl)
  rw [phaseToBytes_eq, prunePhase_eq, hH, hL, hsiblings, List.range_eq_range',
    ← List.flatMap_map (f := Opening.leafIndex) (g := Prover.u32Bytes),
    show (distinctPaths paths).flatMap (fun path ↦ (path.leaf.drop (zerosOf paths)).flatMap
        K.toBytes) = ((distinctPaths paths).map (fun p ↦ p.leaf.drop (zerosOf paths))).flatMap
          (·.flatMap K.toBytes) by rw [List.flatMap_map]]
  simp only [List.append_assoc]
  rw [readPhase, readU32_u32Bytes hcount]
  have hqs32 : ∀ n ∈ paths.map Opening.leafIndex, n < 2 ^ 32 :=
    fun n hn ↦ lt_of_lt_of_le (hqs n hn) h32
  have hreadQueries : ∀ r, readU32s paths.length
      ((paths.map Opening.leafIndex).flatMap Prover.u32Bytes ++ r) =
        some (paths.map Opening.leafIndex, r) := fun r ↦ by
    have := readU32s_u32Bytes hqs32 r
    rwa [List.length_map] at this
  have hreadRows : ∀ r, readRows (leafWords - zerosOf paths)
      (distinctPositions (paths.map Opening.leafIndex)).length
      (((distinctPaths paths).map (fun p ↦ p.leaf.drop (zerosOf paths))).flatMap
        (·.flatMap K.toBytes) ++ r) =
        some ((distinctPaths paths).map (fun p ↦ p.leaf.drop (zerosOf paths)), r) := fun r ↦ by
    have := readRows_toBytes hrowLen r
    rwa [hrowCount] at this
  have hheight : height < 2 ^ 32 :=
    lt_of_le_of_lt hp.height_le (by norm_num [wireMaxHeight])
  have hleafWords : leafWords < 2 ^ 32 :=
    lt_of_le_of_lt hp.leafWords_le (by norm_num [wireMaxLeafWords])
  have hguard : height ≤ wireMaxHeight ∧ leafWords ≤ wireMaxLeafWords ∧
      leafWords - zerosOf paths ≤ leafWords ∧
      ∃ last ∈ (distinctPositions (paths.map Opening.leafIndex)).getLast?, last >>> height = 0 :=
    ⟨hp.height_le, hp.leafWords_le, Nat.sub_le _ _, hlast⟩
  simp only [Option.bind_eq_bind, Option.bind_some, guard_some hp.queries_le, hreadQueries,
    readU32_u32Bytes hheight, readU32_u32Bytes hleafWords,
    readU32_u32Bytes (lt_of_le_of_lt (Nat.sub_le leafWords (zerosOf paths)) hleafWords),
    guard_some hguard, hreadRows, hleaves, guard_some hminimal, readCarriedSiblings_bytes]

/-- `readPhases` reads back decodable phases' encodings. -/
theorem readPhases_flatMap :
    ∀ (phases : List (List Opening)),
      (∀ phase ∈ phases, ∃ height leafWords, PhaseDecodable h phase height leafWords) →
      ∀ rest : Bytes, readPhases phases.length (phases.flatMap Prover.phaseToBytes ++ rest) =
        some (phases.map prunePhase, rest)
  | [], _, rest => by simp [readPhases]
  | phase :: phases, hall, rest => by
    obtain ⟨height, leafWords, hp⟩ := hall phase List.mem_cons_self
    have ih := readPhases_flatMap phases (fun q hq ↦ hall q (List.mem_cons_of_mem _ hq))
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readPhases,
      readPhase_phaseToBytes _ hp, Option.bind_eq_bind, Option.bind_some, ih, List.map_cons]

/-- **`readProof` reads back the encoding of a proof that survives it.** -/
theorem readProof_toBytes {proof : Proof} (hw : WireDecodable h proof) :
    readProof proof.toBytes = some (proof.stream, proof.openings.map prunePhase) := by
  obtain ⟨ws, hws, hstream⟩ := readStream_of_readWords proof.stream
    (Prover.u32Bytes proof.openings.length ++ proof.openings.flatMap Prover.phaseToBytes)
  have hphases := readPhases_flatMap proof.openings hw.phases []
  rw [List.append_nil] at hphases
  have hcount : proof.openings.length < 2 ^ 32 :=
    lt_of_le_of_lt hw.phases_le (by norm_num [wireMaxPhases])
  simp only [readProof, Proof.toBytes, List.append_assoc]
  simp only [readU32_u32Bytes hw.stream_lt, Option.bind_eq_bind, Option.bind_some, hws,
    readU32_u32Bytes hcount, guard_some hw.phases_le, hphases, hstream,
    guard_some (show ([] : Bytes).isEmpty from rfl)]

end Phase

/-- The reader/writer inverses the pruning's round trip uses (`LeanVM.Wire.ReadWrite`), as one
hypothesis; kept for the modules stated against it before `ReadWrite` landed. -/
structure ReadWriteFacts : Prop where
  readU32_u32Bytes : ∀ (n : ℕ) (rest : Bytes), n < 2 ^ 32 →
    readU32 (Prover.u32Bytes n ++ rest) = some (n, rest)
  readU32s_u32Bytes : ∀ (ns : List ℕ) (rest : Bytes), (∀ n ∈ ns, n < 2 ^ 32) →
    readU32s ns.length (ns.flatMap Prover.u32Bytes ++ rest) = some (ns, rest)
  readDigests_digestBytes : ∀ (ds : List Digest) (rest : Bytes),
    readDigests ds.length (ds.flatMap digestBytes ++ rest) = some (ds, rest)
  readRows_toBytes : ∀ (w : ℕ) (rows : List (List K)) (rest : Bytes), (∀ r ∈ rows, r.length = w) →
    readRows w rows.length (rows.flatMap (·.flatMap K.toBytes) ++ rest) = some (rows, rest)
  readWords_toBytes : ∀ (ws : List K) (rest : Bytes),
    readWords ws.length (ws.flatMap K.toBytes ++ rest) = some (ws, rest)

/-- `readProof_toBytes` under the hypothesis `ReadWriteFacts`, which it no longer needs. -/
theorem ReadWriteFacts.readProof_toBytes (_F : ReadWriteFacts) {h : Bytes → Digest}
    {proof : Proof} (hw : WireDecodable h proof) :
    readProof proof.toBytes = some (proof.stream, proof.openings.map prunePhase) :=
  LeanVM.Wire.readProof_toBytes hw

end LeanVM.Wire

end
