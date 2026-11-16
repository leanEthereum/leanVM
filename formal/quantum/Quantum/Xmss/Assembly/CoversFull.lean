module

public import Quantum.Xmss.Assembly.MassesR0
public import Quantum.Xmss.Assembly.FullTable

@[expose] public section

/-!
# Runtime 1's table is covered by the hidden sets

Every cell of FullTable's `fullHw L` (the reads of the full honest computation `fullComp`) is a
cell of an honest path, of a seed path or of a randomizer-base path (`covers_fullHw`, through
MassesR0's `covers_r0`).

* **The queries** (`cellsOK_fullComp`): every query of `fullComp` is the seed derivation, the
  parameter's, a chain start's, a label's randomizer-base derivation (each one block,
  `cellsOK_hid`, `cellsOK_rbIn`), or the honest input of an in-table slot (`cellsOK_chainM`,
  `cellsOK_treeM` on the tabulated positions).
* **The slots** (`cellsOK_slot`): every read of an in-table slot's honest input is a cell of one of
  its realized ports (`exists_round_of_mem_spongeReads`), and every in-table slot is made public by
  a layer signature by an in-range key (`exists_layerSlots`).
* **The one-block inputs** (`mem_inputReads_of_blocks`): their reads are the `k`, `k'` and `h`
  cells of their first block, the seed paths' (`hidCell`) and the randomizer-base paths'
  (`coinCellK`).
-/

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma HashSig.OverPermutation

/-! ## The hidden sets -/

section sets

/-- The hidden `h`-cells: the honest paths', the seed paths' and the randomizer-base paths'. -/
def coverH (L : HonestTable) : Set Z := pathH L ∪ seedH L ∪ r0H L

/-- The hidden `k`-cells: the honest paths', the seed paths' and the randomizer-base paths'. -/
def coverK (L : HonestTable) : Set X := pathK L ∪ seedK L ∪ r0K L

/-- The hidden `k'`-cells: the honest paths', the seed paths' and the randomizer-base paths'. -/
def coverK' (L : HonestTable) : Set X := pathK' L ∪ seedK' L ∪ r0K' L

end sets

/-! ## The reads of a sponge evaluation -/

section reads

variable (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z)

/-- **Every read of a sponge evaluation is a read of one of its rounds.** -/
theorem exists_round_of_mem_spongeReads {e : SpongeRead X Z} (msg : List X) :
    e ∈ spongeReads π h k k' msg → ∃ j < msg.length,
      e ∈ roundReads π h k k' (Sponge.absorb (spongePerm (h, k, k') π) (msg.take j))
        (msg.getD j 0) := by
  induction msg using List.reverseRecOn with
  | nil =>
    intro he
    rw [spongeReads_nil] at he
    exact absurd he List.not_mem_nil
  | append_singleton msg b ih =>
    intro he
    rw [spongeReads_append_singleton, List.mem_append] at he
    rcases he with he | he
    · obtain ⟨j, hj, hje⟩ := ih he
      have hj' : j < (msg ++ [b]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      refine ⟨j, hj', ?_⟩
      have hg : (msg ++ [b]).getD j 0 = msg.getD j 0 := by
        rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj,
          List.getElem_append_left hj]
      rw [List.take_append_of_le_length hj.le, hg]
      exact hje
    · refine ⟨msg.length, by simp, ?_⟩
      have hg : (msg ++ [b]).getD msg.length 0 = b := by simp
      rw [List.take_left' rfl, hg]
      exact he

/-- **The reads of a one-block input**: the `k`, `k'` and `h` cells of its block. -/
theorem mem_inputReads_of_blocks (t : SpongeKeys X Z) {input : HashInput} {b : X}
    (hb : blocks input = [b]) {e : SpongeRead X Z} (he : e ∈ inputReads t π input) :
    e = .k b (t.2.1 b) ∨ e = .k' (rateOf t.2.1 π b) (t.2.2 (rateOf t.2.1 π b)) ∨
      e = .h (capOf t.2.1 t.2.2 π b) (t.1 (capOf t.2.1 t.2.2 π b)) := by
  rw [inputReads, hb, show [b] = ([] : List X) ++ [b] from rfl, spongeReads_append_singleton,
    spongeReads_nil, List.nil_append] at he
  simpa [roundReads, Sponge.absorb, rateOf, capOf] using he

end reads

/-! ## The covered reads -/

section covered

/-- A read whose cell is a path cell, a seed path's or a randomizer-base path's. -/
def ReadCovered (L : HonestTable) : SpongeRead X Z → Prop
  | .h z _ => (∃ a, HwProg.programH z a ∈ pathProgs L) ∨ z ∈ seedH L ∨ z ∈ r0H L
  | .k x _ => (∃ a, HwProg.programK x a ∈ pathProgs L) ∨ x ∈ seedK L ∨ x ∈ r0K L
  | .k' x _ => (∃ a, HwProg.programK' x a ∈ pathProgs L) ∨ x ∈ seedK' L ∨ x ∈ r0K' L

/-- Every read of hashing `input` at the table `L` is covered. -/
def CellsOK (L : HonestTable) (input : HashInput) : Prop :=
  ∀ e ∈ inputReads L.keys L.perm input, ReadCovered L e

variable (L : HonestTable)

/-- **A seed path's input** (one block, a hidden cell). -/
theorem cellsOK_hid {input : HashInput} (b : Option (Option CsIdx))
    (hb : blocks input = [hidCell L.param L.seed L.masterSeed b]) : CellsOK L input := by
  intro e he
  rcases mem_inputReads_of_blocks L.perm L.keys hb he with rfl | rfl | rfl
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact Or.inr (Or.inl ⟨b, rfl⟩)

/-- **A randomizer-base path's input** (one block, a label's cell). -/
theorem cellsOK_r0 {input : HashInput} (a : RLabel) (hb : blocks input = [coinCellK R0.rCell L a]) :
    CellsOK L input := by
  intro e he
  rcases mem_inputReads_of_blocks L.perm L.keys hb he with rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨a, rfl⟩)
  · exact Or.inr (Or.inr ⟨a, rfl⟩)
  · exact Or.inr (Or.inr ⟨a, rfl⟩)

/-- A label's randomizer-base derivation is one block (the message is at most `32` bytes). -/
theorem cellsOK_rbIn (lab : RLabel) : CellsOK L (rbIn lab L.param L.seed) := by
  have hr : rbIn lab L.param L.seed = rbInput R0.rLab lab L.param L.seed := rfl
  rw [hr]
  exact cellsOK_r0 L lab (blocks_of_lt _ (R0.length_rbInput lab L.param L.seed))

/-- **Every in-table slot is made public by a layer signature by an in-range key** (the converse of
`inTable_of_mem_layerSlots`). -/
theorem exists_layerSlots {s : Slot} (hs : InTable s) :
    ∃ (l : Layer) (e : KeyIndex) (w : Encoding), e.val < keyCount l ∧ s ∈ layerSlots l e w := by
  cases s with
  | chain l e step i =>
    refine ⟨l, e, fun _ ↦ ⟨0, by decide⟩, hs, List.mem_append_left _ (List.mem_flatMap.mpr ⟨i,
      List.mem_finRange i, List.mem_map.mpr ⟨step, List.mem_filter.mpr ⟨List.mem_finRange step,
        decide_eq_true (Nat.zero_le _)⟩, rfl⟩⟩)⟩
  | leaf l e =>
    exact ⟨l, e, fun _ ↦ ⟨0, by decide⟩, hs, List.mem_append_right _ List.mem_cons_self⟩
  | node l level index =>
    obtain ⟨h1, h2, h3⟩ := hs
    have hkb := le_keyBits l
    have hkb' := keyBits_le l
    have hlh : layerHeight = 16 := rfl
    have hlt : index * 2 ^ level < 2 ^ keyBits l := by
      have := Nat.mul_lt_mul_of_pos_right h3 (Nat.two_pow_pos level)
      rwa [← pow_add, Nat.sub_add_cancel (by omega)] at this
    have h32 : 2 ^ keyBits l ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hkb'
    have hlife : index * 2 ^ level < lifetime := lt_of_lt_of_le hlt h32
    refine ⟨l, ⟨index * 2 ^ level, hlife⟩, fun _ ↦ ⟨0, by decide⟩, hlt, List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨level - 1, List.mem_range.mpr (by omega), ?_⟩))⟩
    show Slot.node l (level - 1 + 1) (index * 2 ^ level / 2 ^ (level - 1 + 1)) = _
    rw [Nat.sub_add_cancel h1, Nat.mul_div_cancel _ (Nat.two_pow_pos level)]
  | _ => exact absurd hs id

/-- A realized port of an in-table slot is a port of the honest paths. -/
theorem realize_mem_pathProgs {s : Slot} (hs : InTable s) {p : LazyProg X Z HPos XD}
    (hp : p ∈ slotPorts (pubOf L) s) : p.realize (valueAt L) ∈ pathProgs L := by
  obtain ⟨l, e, w, he, hsl⟩ := exists_layerSlots hs
  exact ⟨l, e, w, s, he, hsl, p, hp, rfl⟩

/-- **An in-table slot's honest input**: its reads are the cells of its realized ports. -/
theorem cellsOK_slot {s : Slot} (hs : InTable s) :
    CellsOK L (slotInput (pubOf L) s (valuePos L)) := by
  intro e he
  obtain ⟨j, hj, hje⟩ := exists_round_of_mem_spongeReads L.perm L.keys.1 L.keys.2.1 L.keys.2.2 _ he
  rw [length_blocks_slotInput] at hj
  have hag := realize_eq_of_input (L := L) (s := s)
  simp only [roundReads, List.mem_cons, List.not_mem_nil, or_false] at hje
  rcases hje with rfl | rfl | rfl
  · have hmem := realize_mem_pathProgs L hs (p := .programK (inlSet (slotNeed s)) fun w ↦
      roundK (pubOf L) s (extendVals w) j)
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, List.mem_cons_self⟩)
    exact Or.inl ⟨_, (congrArg (fun x ↦ HwProg.programK x
      (roundK (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j).2 ∈
        pathProgs L) (cellK_congr (pubOf L) hag j)).mpr hmem⟩
  · have hmem := realize_mem_pathProgs L hs (p := .programK' (inlSet (slotNeed s)) fun w ↦
      roundK' (pubOf L) s (extendVals w) j)
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        List.mem_cons_of_mem _ List.mem_cons_self⟩)
    exact Or.inl ⟨_, (congrArg (fun x ↦ HwProg.programK' x
      (roundK' (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j).2 ∈
        pathProgs L) (cellK'_congr (pubOf L) hag j)).mpr hmem⟩
  · have hmem := realize_mem_pathProgs L hs (p := .programH (inlSet (slotNeed s)) fun w ↦
      roundH (pubOf L) s (extendVals w) j)
      (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
    have hc := cellH_congr (pubOf L) hag j
    unfold srcCellH at hc
    rw [roundH_fst, roundH_fst] at hc
    exact Or.inl ⟨_, (congrArg (fun z ↦ HwProg.programH z
      (roundH (pubOf L) s (extendVals (restrictTo (inlSet (slotNeed s)) (valueAt L))) j).2 ∈
        pathProgs L) ((roundH_fst _ _ _ _).trans hc.symm)).mp hmem⟩

end covered

/-! ## The queries of the full computation -/

section queries

variable {f : QueryImpl HashSpec Id} {P : HashInput → Prop}

theorem queriesSatisfy_hashQ_bind {β : Type} {input : HashInput}
    {k : HashOutput → OracleComp HashSpec β} (h : P input) (hk : QueriesSatisfy f P (k (f input))) :
    QueriesSatisfy f P (hashQ input >>= k) := by
  intro q hq
  rw [queries, hashQ, trace_query_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact (List.mem_singleton.mp hq) ▸ h
  · exact hk q hq

theorem queriesSatisfy_hashQ {input : HashInput} (h : P input) :
    QueriesSatisfy f P (hashQ input) := by
  rw [← bind_pure (hashQ input)]
  exact queriesSatisfy_hashQ_bind h (queriesSatisfy_pure _)

theorem queriesSatisfy_tabulate {ι β : Type} [Fintype ι] {c : ι → OracleComp HashSpec β}
    (h : ∀ i, QueriesSatisfy f P (c i)) : QueriesSatisfy f P (tabulate c) :=
  queriesSatisfy_bind (queriesSatisfy_sequenceFin fun _ ↦ h _) (queriesSatisfy_pure _)

variable (L : HonestTable)

/-- **A chain of an in-range key** hashes in-table slot inputs only. -/
theorem cellsOK_chainM {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) (i : ChainIndex) :
    ∀ j, QueriesSatisfy (spongeOut (spongePerm L.keys L.perm)) (CellsOK L)
      (chainM L.param (csHash L) l e i j)
  | 0 => queriesSatisfy_pure _
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · simp only [chainM, hj, ↓reduceDIte]
      refine queriesSatisfy_bind (cellsOK_chainM he i j)
        (queriesSatisfy_hashQ_bind ?_ (queriesSatisfy_pure _))
      have hin : thInput L.param (hashDomainFields (.chain l e ⟨j, hj⟩))
          (Verification.chainPayload i (evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm))
            (chainM L.param (csHash L) l e i j))) =
          slotInput (pubOf L) (.chain l e ⟨j, hj⟩ i) (valuePos L) := by
        rw [eval_chainM]
        show _ = thInput L.param _ (Verification.chainPayload i (L.chainValue l e i
          (j % chainLength)))
        rw [Nat.mod_eq_of_lt (by simp only [chainLength, winternitzBits] at hj ⊢; omega)]
        rfl
      exact (congrArg (CellsOK L) hin).mpr (cellsOK_slot L (s := .chain l e ⟨j, hj⟩ i) he)
    · simp only [chainM, hj, ↓reduceDIte]
      exact queriesSatisfy_pure _

/-- **A tree value in the table** hashes in-table slot inputs only. -/
theorem cellsOK_treeM (l : Layer) :
    ∀ level index, level ≤ layerHeight → index < 2 ^ (keyBits l - level) →
      QueriesSatisfy (spongeOut (spongePerm L.keys L.perm)) (CellsOK L)
        (treeM L.param (csHash L) l level index)
  | 0, index, _, hi => by
    have hkb' := keyBits_le l
    have hidx : index < lifetime :=
      lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num)
        (by simp only [layerCount, layerHeight]; omega))
    have hkey : (leafKey index).val = index := Nat.mod_eq_of_lt hidx
    have he : (leafKey index).val < keyCount l := by
      rw [hkey]
      exact hi
    simp only [treeM]
    refine queriesSatisfy_bind (queriesSatisfy_sequenceFin fun i ↦ cellsOK_chainM L he i _)
      (queriesSatisfy_hashQ_bind ?_ (queriesSatisfy_pure _))
    have hin : thInput L.param (hashDomainFields (.leaf l (leafKey index)))
        (digestsPayload (evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm))
          (sequenceFin fun i : ChainIndex ↦
            chainM L.param (csHash L) l (leafKey index) i (chainLength - 1)))) =
        slotInput (pubOf L) (.leaf l (leafKey index)) (valuePos L) := by
      rw [evalWithAnswerFn_sequenceFin]
      simp only [eval_chainM]
      rfl
    exact (congrArg (CellsOK L) hin).mpr (cellsOK_slot L (s := .leaf l (leafKey index)) he)
  | level + 1, index, hl, hi => by
    have hkb := le_keyBits l
    have hkb' := keyBits_le l
    have hlh : layerHeight = 16 := rfl
    have hsplit : 2 ^ (keyBits l - level) = 2 * 2 ^ (keyBits l - (level + 1)) := by
      rw [← pow_succ']
      exact congrArg (2 ^ ·) (by omega)
    have hc : 2 * index + 1 < 2 ^ (keyBits l - level) := by
      rw [hsplit]
      omega
    have h32 : 2 ^ (keyBits l - level) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp only [treeM]
    refine queriesSatisfy_bind (cellsOK_treeM l level (2 * index) (by omega) (by omega))
      (queriesSatisfy_bind (cellsOK_treeM l level (2 * index + 1) (by omega) hc)
        (queriesSatisfy_hashQ_bind ?_ (queriesSatisfy_pure _)))
    have hin : thInput L.param (hashDomainFields (.node l (level + 1) index))
        (nodePayload
          (evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm))
            (treeM L.param (csHash L) l level (2 * index)))
          (evalWithAnswerFn (spongeOut (spongePerm L.keys L.perm))
            (treeM L.param (csHash L) l level (2 * index + 1)))) =
        slotInput (pubOf L) (.node l (level + 1) index) (valuePos L) := by
      rw [eval_treeM, eval_treeM]
      show _ = thInput L.param _ (nodePayload (L.treeValue l ((level + 1 - 1) % (layerHeight + 1))
        ((2 * index) % 2 ^ 32)) (L.treeValue l ((level + 1 - 1) % (layerHeight + 1))
          ((2 * index + 1) % 2 ^ 32)))
      rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt (show level < layerHeight + 1 by omega),
        Nat.mod_eq_of_lt (show 2 * index < 2 ^ 32 by omega),
        Nat.mod_eq_of_lt (show 2 * index + 1 < 2 ^ 32 by omega)]
      rfl
    exact (congrArg (CellsOK L) hin).mpr
      (cellsOK_slot L (s := .node l (level + 1) index) ⟨by omega, hl, hi⟩)

/-- **A tabulated position's computation** hashes in-table slot inputs only. -/
theorem cellsOK_posM {q : ValPos} (hq : FullPos q) :
    QueriesSatisfy (spongeOut (spongePerm L.keys L.perm)) (CellsOK L)
      (posM q L.param (csHash L)) := by
  cases q with
  | chain l e i j =>
    show QueriesSatisfy _ _ (chainM L.param (csHash L) l e i j.val)
    rcases hq with h0 | he
    · rw [h0]
      exact queriesSatisfy_pure _
    · exact cellsOK_chainM L he i j.val
  | tree l level index =>
    exact cellsOK_treeM L l level.val index.val (by have := level.isLt; omega) hq

/-- **Every read of the full computation is covered.** -/
theorem cellsOK_fullComp :
    QueriesSatisfy (spongeOut (spongePerm L.keys L.perm)) (CellsOK L) (fullComp L.masterSeed) := by
  unfold fullComp
  refine queriesSatisfy_hashQ_bind (cellsOK_hid L none (blocks_seedInput L.masterSeed)) ?_
  rw [hash_seedIn_eq]
  refine queriesSatisfy_hashQ_bind (cellsOK_hid L (some none)
    (blocks_of_lt _ (by rw [length_paramInput]; norm_num))) ?_
  rw [truncateHash_paramInput_eq]
  unfold fullFrom
  refine queriesSatisfy_bind (queriesSatisfy_tabulate fun j ↦ queriesSatisfy_hashQ
    (cellsOK_hid L (some (some j)) (blocks_of_lt _ (by rw [length_csInput]; norm_num)))) ?_
  rw [eval_csTab]
  refine queriesSatisfy_bind (queriesSatisfy_tabulate fun p ↦ ?_) (queriesSatisfy_pure _)
  rcases p with q | lab
  · rw [fullVal_inl]
    split_ifs with hq
    · exact cellsOK_posM L hq
    · exact queriesSatisfy_pure _
  · rw [fullVal_inr]
    exact queriesSatisfy_hashQ_bind (cellsOK_rbIn L lab) (queriesSatisfy_pure _)

end queries

/-! ## Covers -/

section covers

variable {R : List (SpongeRead X Z)}

theorem exists_h_of_readsHw {z : Z} (hz : (readsHw R).1 z ≠ none) : ∃ a, SpongeRead.h z a ∈ R := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hz
  obtain ⟨e, he, hea⟩ := List.exists_of_findSome?_eq_some ha
  cases e with
  | h z' b =>
    simp only [SpongeRead.atH, Option.ite_none_right_eq_some, Option.some.injEq] at hea
    obtain ⟨rfl, -⟩ := hea
    exact ⟨b, he⟩
  | k _ _ => simp [SpongeRead.atH] at hea
  | k' _ _ => simp [SpongeRead.atH] at hea

theorem exists_k_of_readsHw {x : X} (hx : (readsHw R).2.1 x ≠ none) :
    ∃ a, SpongeRead.k x a ∈ R := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hx
  obtain ⟨e, he, hea⟩ := List.exists_of_findSome?_eq_some ha
  cases e with
  | k x' b =>
    simp only [SpongeRead.atK, Option.ite_none_right_eq_some, Option.some.injEq] at hea
    obtain ⟨rfl, -⟩ := hea
    exact ⟨b, he⟩
  | h _ _ => simp [SpongeRead.atK] at hea
  | k' _ _ => simp [SpongeRead.atK] at hea

theorem exists_k'_of_readsHw {x : X} (hx : (readsHw R).2.2 x ≠ none) :
    ∃ a, SpongeRead.k' x a ∈ R := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hx
  obtain ⟨e, he, hea⟩ := List.exists_of_findSome?_eq_some ha
  cases e with
  | k' x' b =>
    simp only [SpongeRead.atK', Option.ite_none_right_eq_some, Option.some.injEq] at hea
    obtain ⟨rfl, -⟩ := hea
    exact ⟨b, he⟩
  | h _ _ => simp [SpongeRead.atK'] at hea
  | k _ _ => simp [SpongeRead.atK'] at hea

/-- **Runtime 1's table is covered** (MassesR0's `covers_r0`): every cell the full honest
computation reads is an honest path's, a seed path's or a randomizer-base path's. -/
theorem covers_fullHw (L : HonestTable) : Covers (fullHw L) (coverH L) (coverK L) (coverK' L) := by
  have hR : ∀ e ∈ (honestEval L.keys L.perm (fullComp L.masterSeed)).2, ReadCovered L e := by
    intro e he
    rw [snd_honestEval] at he
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp he
    exact cellsOK_fullComp L q hq e he
  refine covers_r0 (fullHw L) L (fun z hz ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨b, hb⟩ := exists_h_of_readsHw
      (R := (honestEval L.keys L.perm (fullComp L.masterSeed)).2) hz
    exact hR _ hb
  · obtain ⟨b, hb⟩ := exists_k_of_readsHw
      (R := (honestEval L.keys L.perm (fullComp L.masterSeed)).2) hx
    exact hR _ hb
  · obtain ⟨b, hb⟩ := exists_k'_of_readsHw
      (R := (honestEval L.keys L.perm (fullComp L.masterSeed)).2) hx
    exact hR _ hb

end covers

end Quantum.Xmss.Assembly

end
