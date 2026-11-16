module

public import Quantum.Sphincs.Assembly.Template
public import Quantum.Sphincs.Hybrid.SchemeSeed
public import Quantum.Xmss.Assembly.FullTable

@[expose] public section

/-!
# Runtime 1 of leanSPHINCS with the full honest table hardwired

The honest computation `fullComp S` of every hidden value of a table from `SK.seed = S`: `SK.prf`,
`PK.seed`, then the values at every tabulated position (`FullPos`: the positions of the in-range
trees and keys of the hypertree, every FORS position) by `valM`, the randomizer
`R(M) = PRF_msg(SK.prf, PK.seed, M)` of **every message** and both `H_msg` calls of every message
at its randomizer, each tabulated over its (huge) finite index type (leanXMSS's `tabulate`, through
`Fintype.equivFin`, so that no enumeration is ever unfolded). Its cells `fullHw L` are runtime 1's
hardwired table.

* `fst_honestEval_fullComp`: the computation returns `(PK.seed, fullVals L)`; `fullVals L` is the
  table's hidden values `valueAt L` on the full coordinates (`FullCoord`: every coordinate but the
  untabulated positions), `fullVals_eq`.
* **The template's coordinates are full**: `fullPos_rootPos`, `fullPos_slotNeed` (in-table slots),
  `fullPos_forsNeed` (every FORS opening), `fullPos_layerNeed` and `fullPos_msgPos` (in-range keys,
  `KeyIn`; `keyIn_keyOf`), `fullCoord_valSet`.
* `readsT_full`: **every read of an in-table slot's honest input, and of an `H_msg` call's at the
  honest randomizer, is hardwired in `fullHw L` with its value** (`ReadIn`); `readIn_fullHw` for
  any query of the computation (`slotInput_mem_fullComp`, `hmsgInput_mem_fullComp`,
  `prfMessageInput_mem_fullComp`, `secretInput_mem_fullComp`, `keyDerivationInput_mem_fullComp`).
* `queriesSatisfy_fullComp`: conversely, every query of the computation is one of these inputs
  (`FullInput`).
* `winProb_eq_uavg_full`: **G0 is the table average of runtime 1 with `fullHw L` hardwired**,
  running any read game `gT (pubOf L) (valueAt L)` satisfying the contract `FullReads A gT`: it
  ignores the public keys, reads the hidden values only on full coordinates, and has the law of the
  generic read game `gameReads` against the honest functions. (G1 → G2 by `qrpm_game_eq_reads` with
  `overPermutation_schemeWithHash`, G2 → runtime 1 by `spongeEvalDistMap_eq_avg_runtime1` at
  `fullComp`, whose result determines `gT` by the contract.)
-/

open MeasureTheory
open scoped ENNReal

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common.SufCma
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput MasterSeed
  chainLength littleEndianBytes truncateHash digestsPayload sampleMasterSeed)
open HashSig.OverPermutation (sequenceFin nodePayload)
open Sphincs.KeyGenerationAndSigning (keyDerivationInput)
open Quantum.Xmss (X Z keccakStateEquiv evalWithAnswerFn_sequenceFin)
open Quantum.Xmss.Hybrid (uavg card_masterSeed)
open Quantum.Xmss.Assembly (hashQ eval_hashQ tabulate eval_tabulate mem_queries_bind_left
  mem_queries_bind_right mem_queries_hashQ_bind mem_queries_sequenceFin mem_queries_tabulate
  readsHw_fst_of_mem readsHw_snd_fst_of_mem readsHw_snd_snd_of_mem uavg_eq_avg3 keys₀ univK keysW
  queriesSatisfy_hashQ_pure)

namespace Quantum.Sphincs.Assembly

/-! ## Index arithmetic -/

section arith

theorem shiftRight_lt_two_pow {v a z : ℕ} (hv : v < 2 ^ a) (hz : z ≤ a) :
    v >>> z < 2 ^ (a - z) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
    Nat.sub_add_cancel hz]
  exact hv

/-- The children of a node `j < 2^(a - h)` at height `h ≥ 1` are below `2^(a - (h - 1))`. -/
theorem two_mul_add_one_lt_sub {j a h : ℕ} (hj : j < 2 ^ (a - h)) (h1 : 1 ≤ h) (ha : h ≤ a) :
    2 * j + 1 < 2 ^ (a - (h - 1)) := by
  have he : a - (h - 1) = a - h + 1 := by omega
  rw [he, pow_succ]
  omega

end arith

/-! ## The full honest computation -/

section full

/-- One hash query, truncated to a digest. -/
def digestQ (input : HashInput) : OracleComp SchemeHashSpec Digest :=
  hashQ input >>= fun o ↦ pure (truncateHash o)

/-- The input `PK.seed ‖ ADRS(d) ‖ SK.seed` of the secret of domain `d`. -/
def secretInput (P : PublicParameter) (S : MasterSeed) (d : KeygenDomain) : HashInput :=
  addressedHashInput P (keygenDomainFields d) (littleEndianBytes 32 S)

/-- Position `j` of chain `i` of the one-time key `(l, τ, e)` by hash queries, from `PK.seed = P`
and `SK.seed = S` (as `HonestTable.chainValue`). -/
def chainM (P : PublicParameter) (S : MasterSeed) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) : ℕ → OracleComp SchemeHashSpec Digest
  | 0 => digestQ (secretInput P S (.oneTimeChain l τ e i))
  | j + 1 => if hj : j < chainLength - 1 then
      chainM P S l τ e i j >>= fun d ↦
        digestQ (addressedHashInput P (hashDomainFields (.chain l τ e i ⟨j, hj⟩))
          (littleEndianBytes 16 d))
    else pure 0

/-- The value of tree `τ` of layer `l` at `level`, index `index`, by hash queries (as
`HonestTable.treeValue`). -/
def treeM (P : PublicParameter) (S : MasterSeed) (l : Layer) (τ : TreeIndex) :
    ℕ → ℕ → OracleComp SchemeHashSpec Digest
  | 0, index =>
      sequenceFin (fun i : ChainIndex ↦ chainM P S l τ (leafOfNat index) i (chainLength - 1)) >>=
        fun ends ↦ digestQ (addressedHashInput P (hashDomainFields (.leaf l τ (leafOfNat index)))
          (digestsPayload ends))
  | level + 1, index =>
      treeM P S l τ level (2 * index) >>= fun a ↦ treeM P S l τ level (2 * index + 1) >>= fun b ↦
        digestQ (addressedHashInput P (hashDomainFields (.node l τ (level + 1) index))
          (nodePayload a b))

/-- The value of FORS tree `κ` of instance `idx` at `height`, node `j`, by hash queries (as
`HonestTable.forsValue`). -/
def forsM (P : PublicParameter) (S : MasterSeed) (idx : Index) (κ : ForsTreeIndex) :
    ℕ → ℕ → OracleComp SchemeHashSpec Digest
  | 0, j => digestQ (secretInput P S (.forsSecret idx κ (forsLeafOfNat j))) >>= fun s ↦
      digestQ (addressedHashInput P (hashDomainFields (.forsLeaf idx κ (forsLeafOfNat j)))
        (littleEndianBytes 16 s))
  | h + 1, j =>
      forsM P S idx κ h (2 * j) >>= fun a ↦ forsM P S idx κ h (2 * j + 1) >>= fun b ↦
        digestQ (addressedHashInput P (hashDomainFields (.forsNode idx κ (h + 1) j))
          (nodePayload a b))

/-- The FORS public key of instance `idx` by hash queries (as `HonestTable.forsKey`). -/
def forsKeyM (P : PublicParameter) (S : MasterSeed) (idx : Index) :
    OracleComp SchemeHashSpec Digest :=
  sequenceFin (fun κ : ForsTreeIndex ↦ forsM P S idx κ forsTreeHeight 0) >>= fun roots ↦
    digestQ (addressedHashInput P (hashDomainFields (.forsRoots idx)) (digestsPayload roots))

/-- **The computation of a position's value** by hash queries (as `valuePos`). -/
def valM (P : PublicParameter) (S : MasterSeed) : ValPos → OracleComp SchemeHashSpec Digest
  | .chain l τ e i j => chainM P S l τ e i j.val
  | .tree l τ level index => treeM P S l τ level.val index.val
  | .forsSecret idx κ s => digestQ (secretInput P S (.forsSecret idx κ s))
  | .forsTree idx κ height node => forsM P S idx κ height.val node.val
  | .forsKey idx => forsKeyM P S idx

/-- **The tabulated positions**: the positions of the in-range trees and keys of the hypertree
(levels up to the layer's height, indices in range), every FORS secret and key, the FORS tree
positions with an index in range. -/
def FullPos : ValPos → Prop
  | .chain l τ e _ _ => τ.val < 2 ^ treeBits l ∧ e.val < 2 ^ layerHeight l
  | .tree l τ level index => τ.val < 2 ^ treeBits l ∧ level.val ≤ layerHeight l ∧
      index.val < 2 ^ (layerHeight l - level.val)
  | .forsSecret .. => True
  | .forsTree _ _ height node => node.val < 2 ^ (forsTreeHeight - height.val)
  | .forsKey _ => True

instance instDecidablePredFullPos : DecidablePred FullPos := fun p ↦ by
  cases p <;> unfold FullPos <;> infer_instance

/-- **The full coordinates**: the tabulated positions and every other hidden coordinate. -/
def FullCoord : HPos → Prop
  | .val p => FullPos p
  | _ => True

/-- A tabulated position's value by `valM`, `0` at the others. -/
def fullVal (P : PublicParameter) (S : MasterSeed) (p : ValPos) :
    OracleComp SchemeHashSpec Digest :=
  if FullPos p then valM P S p else pure 0

/-- Hidden values from the values at the positions, the randomizers and the `H_msg` outputs (the
stream and the marks `0`). -/
def hiddenOf (vals : ValPos → Digest) (rnds : Message → Randomizer)
    (digs : Message × DigestCall → HashOutput) : (s : HPos) → XD s
  | .val p => vals p
  | .rnd msg => rnds msg
  | .dig msg i => digs (msg, i)
  | .str _ _ => (0 : HashOutput)
  | .asg _ _ => ()

/-- The hidden values from `SK.seed = S`, `SK.prf = prf` and `PK.seed = P`: the tabulated
positions' values, then every message's randomizer, then both `H_msg` calls of every message at
its randomizer and the root. -/
noncomputable def fullFrom (S : MasterSeed) (prf : HashOutput) (P : PublicParameter) :
    OracleComp SchemeHashSpec (PublicParameter × ((s : HPos) → XD s)) :=
  tabulate (fullVal P S) >>= fun vals ↦
    tabulate (fun msg : Message ↦ digestQ (prfMessageInput prf P msg)) >>= fun rnds ↦
      tabulate (fun c : Message × DigestCall ↦
          hashQ (messageDigestInput (rnds c.1) P (vals rootPos) c.1 c.2)) >>= fun digs ↦
        pure (P, hiddenOf vals rnds digs)

/-- **The full honest computation** from `SK.seed = S`: `SK.prf`, `PK.seed`, and every hidden
value. -/
noncomputable def fullComp (S : MasterSeed) :
    OracleComp SchemeHashSpec (PublicParameter × ((s : HPos) → XD s)) :=
  hashQ (keyDerivationInput S 1) >>= fun prf ↦
    hashQ (keyDerivationInput S 0) >>= fun o ↦ fullFrom S prf (truncateHash o)

/-- **Runtime 1's table**: the cells the full honest computation reads, with their values. -/
noncomputable def fullHw (L : HonestTable) : Hw X Z :=
  readsHw (honestEval L.keys L.perm (fullComp L.secretSeed)).2

/-- The hidden values the full computation returns: the table's on the full coordinates, `0` at
the other positions. -/
def fullVals (L : HonestTable) : (s : HPos) → XD s :=
  hiddenOf (fun p ↦ if FullPos p then valuePos L p else 0) L.randomizer
    fun c ↦ L.digestOutput c.1 c.2

/-- **The full computation's values are the table's on the full coordinates.** -/
theorem fullVals_eq (L : HonestTable) {s : HPos} (hs : FullCoord s) :
    fullVals L s = valueAt L s := by
  cases s with
  | val p => exact ite_eq_left hs
  | rnd msg => rfl
  | dig msg i => rfl
  | str j i => rfl
  | asg msg j => rfl

end full

/-! ## The full computation returns the table's values -/

section eval

theorem eval_digestQ (f : QueryImpl SchemeHashSpec Id) (input : HashInput) :
    evalWithAnswerFn f (digestQ input) = truncateHash (f input) := by
  rw [digestQ, evalWithAnswerFn_bind, eval_hashQ, evalWithAnswerFn_pure]

variable (L : HonestTable)

theorem eval_chainM (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) : ∀ j,
    evalWithAnswerFn L.hash (chainM L.publicSeed L.secretSeed l τ e i j) = L.chainValue l τ e i j
  | 0 => eval_digestQ _ _
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · simp only [chainM, hj, ↓reduceDIte, evalWithAnswerFn_bind, eval_chainM l τ e i j,
        eval_digestQ]
      exact (L.chainValue_succ l τ e i ⟨j, hj⟩).symm
    · simp only [chainM, hj, ↓reduceDIte, evalWithAnswerFn_pure, HonestTable.chainValue]

theorem eval_treeM (l : Layer) (τ : TreeIndex) : ∀ level index,
    evalWithAnswerFn L.hash (treeM L.publicSeed L.secretSeed l τ level index) =
      L.treeValue l τ level index
  | 0, index => by
    simp only [treeM, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_chainM,
      eval_digestQ]
    rfl
  | level + 1, index => by
    simp only [treeM, evalWithAnswerFn_bind, eval_treeM l τ level, eval_digestQ]
    exact (L.treeValue_succ l τ level index).symm

theorem eval_forsM (idx : Index) (κ : ForsTreeIndex) : ∀ h j,
    evalWithAnswerFn L.hash (forsM L.publicSeed L.secretSeed idx κ h j) = L.forsValue idx κ h j
  | 0, j => by
    simp only [forsM, evalWithAnswerFn_bind, eval_digestQ]
    rfl
  | h + 1, j => by
    simp only [forsM, evalWithAnswerFn_bind, eval_forsM idx κ h, eval_digestQ]
    exact (L.forsValue_succ idx κ h j).symm

theorem eval_forsKeyM (idx : Index) :
    evalWithAnswerFn L.hash (forsKeyM L.publicSeed L.secretSeed idx) = L.forsKey idx := by
  simp only [forsKeyM, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_forsM,
    eval_digestQ]
  rfl

/-- **`valM` computes the table's value at every position.** -/
theorem eval_valM (p : ValPos) :
    evalWithAnswerFn L.hash (valM L.publicSeed L.secretSeed p) = valuePos L p := by
  cases p with
  | chain l τ e i j => exact eval_chainM L l τ e i j.val
  | tree l τ level index => exact eval_treeM L l τ level.val index.val
  | forsSecret idx κ s => exact eval_digestQ _ _
  | forsTree idx κ height node => exact eval_forsM L idx κ height.val node.val
  | forsKey idx => exact eval_forsKeyM L idx

theorem eval_fullVal (p : ValPos) :
    evalWithAnswerFn L.hash (fullVal L.publicSeed L.secretSeed p) =
      if FullPos p then valuePos L p else 0 := by
  unfold fullVal
  split_ifs
  · exact eval_valM L p
  · rfl

theorem hash_prfKey : L.hash (keyDerivationInput L.secretSeed 1) = L.prfKey :=
  rfl

theorem truncateHash_publicSeed :
    truncateHash (L.hash (keyDerivationInput L.secretSeed 0)) = L.publicSeed :=
  rfl

end eval

/-! ## The template's coordinates are full -/

section coords

/-- A key in range: its tree on its layer, its leaf in its tree. -/
def KeyIn (K : Key) : Prop :=
  K.2.1.val < 2 ^ treeBits K.1 ∧ K.2.2.val < 2 ^ layerHeight K.1

theorem keyIn_keyOf (l : Layer) (idx : Index) : KeyIn (keyOf l idx) := by
  have hi : idx.val < 67108864 := idx.isLt
  refine ⟨?_, leafOfIndex_lt l idx⟩
  fin_cases l
  · change idx.val / 256 < 262144
    omega
  · change idx.val / 65536 < 1024
    omega
  · change idx.val / 67108864 < 1
    omega

theorem fullPos_cpos {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} (hK : KeyIn (l, τ, e))
    (i : ChainIndex) (j : ℕ) : FullPos (cpos l τ e i j) :=
  hK

theorem fullPos_tpos {l : Layer} {τ : TreeIndex} (hτ : τ.val < 2 ^ treeBits l) {level index : ℕ}
    (hl : level ≤ layerHeight l) (hi : index < 2 ^ (layerHeight l - level)) :
    FullPos (tpos l τ level index) := by
  have h10 := layerHeight_le l
  have htop : layerHeight topLayer = 10 := rfl
  have hi' : index < 2 ^ layerHeight topLayer :=
    lt_of_lt_of_le (lt_two_pow_of_lt hi) (two_pow_layerHeight_le l)
  have hlv : level % (layerHeight topLayer + 1) = level := Nat.mod_eq_of_lt (by omega)
  refine ⟨hτ, ?_, ?_⟩
  · change level % (layerHeight topLayer + 1) ≤ layerHeight l
    rw [hlv]
    exact hl
  · change index % 2 ^ layerHeight topLayer <
      2 ^ (layerHeight l - level % (layerHeight topLayer + 1))
    rw [hlv, Nat.mod_eq_of_lt hi']
    exact hi

theorem fullPos_fpos (idx : Index) (κ : ForsTreeIndex) {height node : ℕ}
    (hh : height ≤ forsTreeHeight) (hn : node < 2 ^ (forsTreeHeight - height)) :
    FullPos (fpos idx κ height node) := by
  have h10 : forsTreeHeight = 10 := rfl
  have hn' : node < 2 ^ forsTreeHeight := lt_two_pow_of_lt hn
  change node % 2 ^ forsTreeHeight <
    2 ^ (forsTreeHeight - height % (forsTreeHeight + 1))
  rw [Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt (by omega : height < forsTreeHeight + 1)]
  exact hn

/-- `PK.root`'s position is tabulated. -/
theorem fullPos_rootPos : FullPos rootPos :=
  fullPos_tpos (Nat.two_pow_pos _) le_rfl (Nat.two_pow_pos _)

/-- **The coordinates of an in-table slot are tabulated.** -/
theorem fullPos_slotNeed {s : Slot} (hs : InTable s) {q : ValPos} (hq : q ∈ slotNeed s) :
    FullPos q := by
  cases s with
  | chain l τ e i step =>
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fullPos_cpos hs i _
    · rw [Finset.mem_singleton.mp hq]
      exact fullPos_cpos hs i _
  | leaf l τ e =>
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fullPos_tpos hs.1 (Nat.zero_le _) (by rw [Nat.sub_zero]; exact hs.2)
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
      exact fullPos_cpos hs i _
  | node l τ height index =>
    obtain ⟨hτ, h1, hh, hi⟩ := hs
    have hc := two_mul_add_one_lt_sub hi h1 hh
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fullPos_tpos hτ (by omega) (by omega)
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fullPos_tpos hτ (by omega) hc
    · rw [Finset.mem_singleton.mp hq]
      exact fullPos_tpos hτ hh hi
  | forsLeaf idx κ s =>
    rcases Finset.mem_insert.mp hq with rfl | hq
    · trivial
    · rw [Finset.mem_singleton.mp hq]
      exact fullPos_fpos idx κ (Nat.zero_le _) (by rw [Nat.sub_zero]; exact s.isLt)
  | forsNode idx κ height node =>
    obtain ⟨h1, hh, hi⟩ := hs
    have hc := two_mul_add_one_lt_sub hi h1 hh
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fullPos_fpos idx κ (by omega) (by omega)
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact fullPos_fpos idx κ (by omega) hc
    · rw [Finset.mem_singleton.mp hq]
      exact fullPos_fpos idx κ hh hi
  | forsRoots idx =>
    rcases Finset.mem_insert.mp hq with rfl | hq
    · trivial
    · obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hq
      exact fullPos_fpos idx κ le_rfl (Nat.two_pow_pos _)
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

theorem fullPos_slotOutPos {s : Slot} (hs : InTable s) : FullPos (slotOutPos s) :=
  fullPos_slotNeed hs (slotOutPos_mem_slotNeed hs)

theorem mem_needUnion {q : ValPos} : ∀ {ss : List Slot}, q ∈ needUnion ss →
    ∃ s ∈ ss, q ∈ slotNeed s
  | [], hq => absurd hq (Finset.notMem_empty q)
  | s :: ss, hq => by
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ⟨s, List.mem_cons_self, hq⟩
    · obtain ⟨s', hs', hq'⟩ := mem_needUnion hq
      exact ⟨s', List.mem_cons_of_mem _ hs', hq'⟩

/-- The slots of a FORS opening are in the table. -/
theorem inTable_of_mem_forsSlots {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {s : Slot}
    (hs : s ∈ forsSlots idx lv) : InTable s := by
  have h10 : forsTreeHeight = 10 := rfl
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨κ, -, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_cons.mp hs with rfl | hs
    · trivial
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hs
      have hh := List.mem_range.mp hh
      exact ⟨by omega, by omega, shiftRight_lt_two_pow (lv κ).isLt (by omega)⟩
  · rw [List.mem_singleton.mp hs]
    trivial

/-- The slots of a layer signature by an in-range key are in the table. -/
theorem inTable_of_mem_layerSlots {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    (hK : KeyIn (l, τ, e)) {s : Slot} (hs : s ∈ layerSlots l τ e x) : InTable s := by
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨i, -, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨step, -, rfl⟩ := List.mem_map.mp hs
    exact hK
  · rcases List.mem_cons.mp hs with rfl | hs
    · exact hK
    · obtain ⟨lev, hlev, rfl⟩ := List.mem_map.mp hs
      have hlev := List.mem_range.mp hlev
      exact ⟨hK.1, by omega, by omega, shiftRight_lt_two_pow hK.2 (by omega)⟩

/-- The coordinates of in-table slots and of tabulated sets are tabulated. -/
theorem fullPos_needUnion_union {ss : List Slot} (hss : ∀ s ∈ ss, InTable s)
    {B C : Finset ValPos} (hB : ∀ q ∈ B, FullPos q) (hC : ∀ q ∈ C, FullPos q) :
    ∀ q ∈ needUnion ss ∪ B ∪ C, FullPos q := by
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨s, hs, hqs⟩ := mem_needUnion hq
      exact fullPos_slotNeed (hss s hs) hqs
    · exact hB q hq
  · exact hC q hq

/-- **The coordinates a FORS opening reveals are tabulated.** (Stated without a named membership
hypothesis: the `constructorNameAsVariable` linter evaluates the concrete slot list.) -/
theorem fullPos_forsNeed {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} :
    ∀ q ∈ forsNeed idx lv, FullPos q :=
  fullPos_needUnion_union (fun _ hs ↦ inTable_of_mem_forsSlots hs)
    (fun q hq ↦ by
      obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hq
      trivial)
    fun q hq ↦ by
      obtain ⟨⟨κ, z⟩, -, rfl⟩ := Finset.mem_image.mp hq
      exact fullPos_fpos idx κ z.isLt.le (shiftRight_xor_lt (lv κ).isLt z.isLt)

/-- **The coordinates a layer signature by an in-range key reveals are tabulated.** -/
theorem fullPos_layerNeed {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex} {x : Encoding}
    (hK : KeyIn (l, τ, e)) {q : ValPos} (hq : q ∈ layerNeed l τ e x) : FullPos q := by
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨s, hs, hqs⟩ := mem_needUnion hq
      exact fullPos_slotNeed (inTable_of_mem_layerSlots hK hs) hqs
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hq
      exact fullPos_cpos hK i _
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hq
    exact fullPos_tpos hK.1 z.isLt.le (shiftRight_xor_lt hK.2 z.isLt)

/-- **The value an in-range key signs is at a tabulated position.** -/
theorem fullPos_msgPos {K : Key} (hK : KeyIn K) : FullPos (msgPos K) := by
  obtain ⟨l, τ, e⟩ := K
  obtain ⟨hτ, he⟩ := hK
  fin_cases l
  · trivial
  · change τ.val < 1024 at hτ
    change e.val < 256 at he
    refine fullPos_tpos (l := layerBelow 1) ?_ le_rfl (Nat.two_pow_pos _)
    change (τ.val * 256 + e.val) % 67108864 < 262144
    omega
  · change τ.val < 1 at hτ
    change e.val < 1024 at he
    refine fullPos_tpos (l := layerBelow 2) ?_ le_rfl (Nat.two_pow_pos _)
    change (τ.val * 1024 + e.val) % 67108864 < 1024
    omega

theorem fullCoord_valSet {T : Finset ValPos} (hT : ∀ q ∈ T, FullPos q) {s : HPos}
    (hs : s ∈ valSet T) : FullCoord s := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hs
  exact hT q hq

end coords

/-! ## The honest inputs are queries of the full computation -/

section queries

variable (L : HonestTable)

theorem mem_queries_hashQ (f : QueryImpl SchemeHashSpec Id) (input : HashInput) :
    input ∈ queries f (hashQ input) := by
  have h := mem_queries_hashQ_bind f input fun o ↦ pure o
  rwa [bind_pure] at h

theorem mem_queries_digestQ (f : QueryImpl SchemeHashSpec Id) (input : HashInput) :
    input ∈ queries f (digestQ input) :=
  mem_queries_hashQ_bind f input _

theorem valM_cpos (P : PublicParameter) (S : MasterSeed) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (i : ChainIndex) {j : ℕ} (hj : j < chainLength) :
    valM P S (cpos l τ e i j) = chainM P S l τ e i j := by
  change chainM P S l τ e i (j % chainLength) = _
  rw [Nat.mod_eq_of_lt hj]

theorem valM_tpos (P : PublicParameter) (S : MasterSeed) (l : Layer) (τ : TreeIndex)
    {level index : ℕ} (hl : level ≤ layerHeight topLayer) (hi : index < 2 ^ layerHeight topLayer) :
    valM P S (tpos l τ level index) = treeM P S l τ level index := by
  change treeM P S l τ (level % (layerHeight topLayer + 1)) (index % 2 ^ layerHeight topLayer) = _
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hl), Nat.mod_eq_of_lt hi]

theorem valM_fpos (P : PublicParameter) (S : MasterSeed) (idx : Index) (κ : ForsTreeIndex)
    {height node : ℕ} (hh : height ≤ forsTreeHeight) (hn : node < 2 ^ forsTreeHeight) :
    valM P S (fpos idx κ height node) = forsM P S idx κ height node := by
  change forsM P S idx κ (height % (forsTreeHeight + 1)) (node % 2 ^ forsTreeHeight) = _
  rw [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hh), Nat.mod_eq_of_lt hn]

/-- **An in-table slot's honest input is a query of the computation of its output position.** -/
theorem slotInput_mem_valM {s : Slot} (hs : InTable s) :
    slotInput L.publicSeed s (valuePos L) ∈
      queries L.hash (valM L.publicSeed L.secretSeed (slotOutPos s)) := by
  have h4 : chainLength = 4 := rfl
  have h10 : layerHeight topLayer = 10 := rfl
  have hf10 : forsTreeHeight = 10 := rfl
  cases s with
  | chain l τ e i step =>
    have hst := step.isLt
    change _ ∈ queries L.hash (valM _ _ (cpos l τ e i (step.val + 1)))
    rw [valM_cpos _ _ l τ e i (by omega), chainM, dite_eq_left step.isLt]
    refine mem_queries_bind_right _ _ _ ?_
    rw [eval_chainM]
    change addressedHashInput L.publicSeed (hashDomainFields (.chain l τ e i step))
      (littleEndianBytes 16 (valuePos L (cpos l τ e i step.val))) ∈ _
    rw [valuePos_cpos L l τ e i (by omega)]
    exact mem_queries_digestQ _ _
  | leaf l τ e =>
    change _ ∈ queries L.hash (valM _ _ (tpos l τ 0 e.val))
    rw [valM_tpos _ _ l τ (Nat.zero_le _) e.isLt, treeM]
    refine mem_queries_bind_right _ _ _ ?_
    rw [evalWithAnswerFn_sequenceFin]
    simp only [eval_chainM, leafOfNat_val]
    have hv : (fun i ↦ valuePos L (cpos l τ e i (chainLength - 1))) =
        fun i ↦ L.chainValue l τ e i (chainLength - 1) :=
      funext fun i ↦ valuePos_cpos L l τ e i (by omega)
    change addressedHashInput L.publicSeed (hashDomainFields (.leaf l τ e))
      (digestsPayload fun i ↦ valuePos L (cpos l τ e i (chainLength - 1))) ∈ _
    rw [hv]
    exact mem_queries_digestQ _ _
  | node l τ height index =>
    obtain ⟨-, h1, hh, hi⟩ := hs
    have hl := layerHeight_le l
    have hc := two_mul_add_one_lt_sub hi h1 hh
    have hc' : 2 * index + 1 < 2 ^ layerHeight topLayer :=
      lt_of_lt_of_le (lt_two_pow_of_lt hc) (two_pow_layerHeight_le l)
    obtain ⟨h', rfl⟩ : ∃ h', height = h' + 1 := ⟨height - 1, by omega⟩
    change _ ∈ queries L.hash (valM _ _ (tpos l τ (h' + 1) index))
    rw [valM_tpos _ _ l τ (by omega) (by omega), treeM]
    refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _ ?_)
    rw [eval_treeM, eval_treeM]
    change addressedHashInput L.publicSeed (hashDomainFields (.node l τ (h' + 1) index))
      (nodePayload (valuePos L (tpos l τ (h' + 1 - 1) (2 * index)))
        (valuePos L (tpos l τ (h' + 1 - 1) (2 * index + 1)))) ∈ _
    rw [Nat.add_sub_cancel, valuePos_tpos L l τ (by omega) (by omega),
      valuePos_tpos L l τ (by omega) hc']
    exact mem_queries_digestQ _ _
  | forsLeaf idx κ s =>
    change _ ∈ queries L.hash (valM _ _ (fpos idx κ 0 s.val))
    rw [valM_fpos _ _ idx κ (Nat.zero_le _) s.isLt, forsM]
    refine mem_queries_bind_right _ _ _ ?_
    rw [eval_digestQ, forsLeafOfNat_val]
    exact mem_queries_digestQ _ _
  | forsNode idx κ height node =>
    obtain ⟨h1, hh, hi⟩ := hs
    have hc := two_mul_add_one_lt_sub hi h1 hh
    have hc' : 2 * node + 1 < 2 ^ forsTreeHeight := lt_two_pow_of_lt hc
    obtain ⟨h', rfl⟩ : ∃ h', height = h' + 1 := ⟨height - 1, by omega⟩
    change _ ∈ queries L.hash (valM _ _ (fpos idx κ (h' + 1) node))
    rw [valM_fpos _ _ idx κ hh (lt_two_pow_of_lt hi), forsM]
    refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _ ?_)
    rw [eval_forsM, eval_forsM]
    change addressedHashInput L.publicSeed (hashDomainFields (.forsNode idx κ (h' + 1) node))
      (nodePayload (valuePos L (fpos idx κ (h' + 1 - 1) (2 * node)))
        (valuePos L (fpos idx κ (h' + 1 - 1) (2 * node + 1)))) ∈ _
    rw [Nat.add_sub_cancel, valuePos_fpos L idx κ (by omega) (by omega),
      valuePos_fpos L idx κ (by omega) hc']
    exact mem_queries_digestQ _ _
  | forsRoots idx =>
    change _ ∈ queries L.hash (forsKeyM _ _ idx)
    rw [forsKeyM]
    refine mem_queries_bind_right _ _ _ ?_
    rw [evalWithAnswerFn_sequenceFin]
    simp only [eval_forsM]
    have hv : (fun κ ↦ valuePos L (fpos idx κ forsTreeHeight 0)) =
        fun κ ↦ L.forsValue idx κ forsTreeHeight 0 :=
      funext fun κ ↦ valuePos_fpos L idx κ le_rfl (Nat.two_pow_pos _)
    change addressedHashInput L.publicSeed (hashDomainFields (.forsRoots idx))
      (digestsPayload fun κ ↦ valuePos L (fpos idx κ forsTreeHeight 0)) ∈ _
    rw [hv]
    exact mem_queries_digestQ _ _
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- The full computation's queries include those of `fullFrom` at the table's `SK.prf` and
`PK.seed`. -/
theorem mem_queries_fullComp {q : HashInput}
    (h : q ∈ queries L.hash (fullFrom L.secretSeed L.prfKey L.publicSeed)) :
    q ∈ queries L.hash (fullComp L.secretSeed) := by
  unfold fullComp
  refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _ ?_)
  rw [eval_hashQ, eval_hashQ, hash_prfKey, truncateHash_publicSeed]
  exact h

theorem mem_queries_fullComp_valM {p : ValPos} (hp : FullPos p) {q : HashInput}
    (h : q ∈ queries L.hash (valM L.publicSeed L.secretSeed p)) :
    q ∈ queries L.hash (fullComp L.secretSeed) := by
  refine mem_queries_fullComp L (mem_queries_bind_left _ _ _ (mem_queries_tabulate _ _ p ?_))
  rw [fullVal, ite_eq_left hp]
  exact h

/-- **Every in-table slot's honest input is hashed by the full computation.** -/
theorem slotInput_mem_fullComp {s : Slot} (hs : InTable s) :
    slotInput L.publicSeed s (valuePos L) ∈ queries L.hash (fullComp L.secretSeed) :=
  mem_queries_fullComp_valM L (fullPos_slotOutPos hs) (slotInput_mem_valM L hs)

/-- **Every `PRF_msg` input is hashed by the full computation.** -/
theorem prfMessageInput_mem_fullComp (msg : Message) :
    prfMessageInput L.prfKey L.publicSeed msg ∈ queries L.hash (fullComp L.secretSeed) := by
  refine mem_queries_fullComp L ?_
  unfold fullFrom
  exact mem_queries_bind_right _ _ _ (mem_queries_bind_left _ _ _
    (mem_queries_tabulate _ _ msg (mem_queries_digestQ _ _)))

/-- **Every `H_msg` call's honest input at the honest randomizer is hashed by the full
computation.** -/
theorem hmsgInput_mem_fullComp (msg : Message) (i : DigestCall) :
    slotInput L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L) ∈
      queries L.hash (fullComp L.secretSeed) := by
  refine mem_queries_fullComp L ?_
  unfold fullFrom
  refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _
    (mem_queries_bind_left _ _ _ (mem_queries_tabulate _ _ (msg, i) ?_)))
  simp only [eval_tabulate, eval_digestQ, eval_fullVal, ite_eq_left fullPos_rootPos]
  exact mem_queries_hashQ _ _

/-- **Every in-range secret's input is hashed by the full computation.** -/
theorem secretInput_mem_fullComp_chain {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    (hK : KeyIn (l, τ, e)) (i : ChainIndex) :
    secretInput L.publicSeed L.secretSeed (.oneTimeChain l τ e i) ∈
      queries L.hash (fullComp L.secretSeed) := by
  refine mem_queries_fullComp_valM L (fullPos_cpos hK i 0) ?_
  rw [valM_cpos _ _ l τ e i (by decide)]
  exact mem_queries_digestQ _ _

theorem secretInput_mem_fullComp_fors (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) :
    secretInput L.publicSeed L.secretSeed (.forsSecret idx κ s) ∈
      queries L.hash (fullComp L.secretSeed) :=
  mem_queries_fullComp_valM L (p := .forsSecret idx κ s) trivial (mem_queries_digestQ _ _)

/-- The key derivations `SK.prf` and `PK.seed` are hashed by the full computation. -/
theorem keyDerivationInput_mem_fullComp :
    keyDerivationInput L.secretSeed 1 ∈ queries L.hash (fullComp L.secretSeed) ∧
      keyDerivationInput L.secretSeed 0 ∈ queries L.hash (fullComp L.secretSeed) :=
  ⟨mem_queries_hashQ_bind _ _ _,
    mem_queries_bind_right _ _ _ (mem_queries_hashQ_bind _ _ _)⟩

end queries

/-! ## The honest reads are hardwired -/

section hw

/-- A read held by hardwired cells: its cell is hardwired with its value. -/
def ReadIn (W : Hw X Z) : SpongeRead X Z → Prop
  | .h z a => W.1 z = some a
  | .k x a => W.2.1 x = some a
  | .k' x a => W.2.2 x = some a

/-- The cells of reads answered by `t` hold every read. -/
theorem readIn_readsHw {R : List (SpongeRead X Z)} {t : SpongeKeys X Z}
    (hR : ∀ e ∈ R, e.AnsweredBy t) {e : SpongeRead X Z} (he : e ∈ R) : ReadIn (readsHw R) e := by
  cases e with
  | h z a => exact (readsHw_fst_of_mem hR he).trans (congrArg some (hR _ he))
  | k x a => exact (readsHw_snd_fst_of_mem hR he).trans (congrArg some (hR _ he))
  | k' x a => exact (readsHw_snd_snd_of_mem hR he).trans (congrArg some (hR _ he))

variable (L : HonestTable)

/-- **The reads of every query of the full computation are hardwired in `fullHw L`.** -/
theorem readIn_fullHw {input : HashInput} (hq : input ∈ queries L.hash (fullComp L.secretSeed))
    {e : SpongeRead X Z} (he : e ∈ inputReads L.keys L.perm input) : ReadIn (fullHw L) e :=
  readIn_readsHw (honestEval_answeredBy L.perm L.keys (fullComp L.secretSeed))
    (by
      rw [snd_honestEval]
      exact List.mem_flatMap.mpr ⟨input, hq, he⟩)

/-- **The reads of the template's table are hardwired in the full table**: every read of an
in-table slot's honest input, and of an `H_msg` call's at the honest randomizer, is a cell of
`fullHw L` with its value. -/
theorem readsT_full {s : Slot} (hs : InTable s ∨ ∃ msg i, s = .hmsg (L.randomizer msg) msg i)
    {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm (slotInput L.publicSeed s (valuePos L))) :
    ReadIn (fullHw L) e := by
  rcases hs with hs | ⟨msg, i, rfl⟩
  · exact readIn_fullHw L (slotInput_mem_fullComp L hs) he
  · exact readIn_fullHw L (hmsgInput_mem_fullComp L msg i) he

end hw

/-! ## Every query of the full computation is an honest input -/

section sat

/-- A secret's domain in range: a chain start of an in-range key, every FORS secret. -/
def SecretIn : KeygenDomain → Prop
  | .oneTimeChain l τ e _ => KeyIn (l, τ, e)
  | .forsSecret .. => True

/-- **The honest inputs of the full computation** at `L`: the key derivations, the in-range
secrets, the in-table slots' inputs, every message's `PRF_msg` input, and both `H_msg` calls of
every message at its honest randomizer. -/
def FullInput (L : HonestTable) (input : HashInput) : Prop :=
  (input = keyDerivationInput L.secretSeed 1 ∨ input = keyDerivationInput L.secretSeed 0) ∨
    (∃ d, SecretIn d ∧ input = secretInput L.publicSeed L.secretSeed d) ∨
    (∃ s, InTable s ∧ input = slotInput L.publicSeed s (valuePos L)) ∨
    (∃ msg, input = prfMessageInput L.prfKey L.publicSeed msg) ∨
    ∃ msg i, input = slotInput L.publicSeed (.hmsg (L.randomizer msg) msg i) (valuePos L)

variable (L : HonestTable)

theorem queriesSatisfy_hashQ {P : HashInput → Prop} {f : QueryImpl SchemeHashSpec Id}
    {input : HashInput} (h : P input) : QueriesSatisfy f P (hashQ input) := by
  have h' := queriesSatisfy_hashQ_pure (f := f) h fun o ↦ o
  rwa [bind_pure] at h'

theorem queriesSatisfy_digestQ {P : HashInput → Prop} {f : QueryImpl SchemeHashSpec Id}
    {input : HashInput} (h : P input) : QueriesSatisfy f P (digestQ input) :=
  queriesSatisfy_hashQ_pure (f := f) h _

theorem queriesSatisfy_tabulate {P : HashInput → Prop} {f : QueryImpl SchemeHashSpec Id}
    {ι β : Type} [Fintype ι] {c : ι → OracleComp SchemeHashSpec β}
    (h : ∀ i, QueriesSatisfy f P (c i)) : QueriesSatisfy f P (tabulate c) := by
  unfold tabulate
  exact queriesSatisfy_bind (queriesSatisfy_sequenceFin fun _ ↦ h _) (queriesSatisfy_pure _)

theorem fullInput_slot {s : Slot} (hs : InTable s) {input : HashInput}
    (h : input = slotInput L.publicSeed s (valuePos L)) : FullInput L input :=
  Or.inr (Or.inr (Or.inl ⟨s, hs, h⟩))

theorem queriesSatisfy_chainM {l : Layer} {τ : TreeIndex} {e : TreeLeafIndex}
    (hK : KeyIn (l, τ, e)) (i : ChainIndex) : ∀ j,
    QueriesSatisfy L.hash (FullInput L) (chainM L.publicSeed L.secretSeed l τ e i j)
  | 0 => queriesSatisfy_digestQ (Or.inr (Or.inl ⟨.oneTimeChain l τ e i, hK, rfl⟩))
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · rw [chainM, dite_eq_left hj]
      refine queriesSatisfy_bind (queriesSatisfy_chainM hK i j) ?_
      rw [eval_chainM]
      refine queriesSatisfy_digestQ (fullInput_slot L (s := .chain l τ e i ⟨j, hj⟩) hK ?_)
      change _ = addressedHashInput _ _ (littleEndianBytes 16 (valuePos L (cpos l τ e i j)))
      rw [valuePos_cpos L l τ e i (by omega)]
      rfl
    · rw [chainM, dite_eq_right hj]
      exact queriesSatisfy_pure _

theorem queriesSatisfy_treeM {l : Layer} {τ : TreeIndex} (hτ : τ.val < 2 ^ treeBits l) :
    ∀ level index, level ≤ layerHeight l → index < 2 ^ (layerHeight l - level) →
      QueriesSatisfy L.hash (FullInput L) (treeM L.publicSeed L.secretSeed l τ level index)
  | 0, index, _, hi => by
    have hi' : index < 2 ^ layerHeight topLayer :=
      lt_of_lt_of_le (lt_two_pow_of_lt hi) (two_pow_layerHeight_le l)
    have he : (leafOfNat index).val = index := Nat.mod_eq_of_lt hi'
    have hK : KeyIn (l, τ, leafOfNat index) := ⟨hτ, by rw [he]; simpa using hi⟩
    rw [treeM]
    refine queriesSatisfy_bind (queriesSatisfy_sequenceFin fun i ↦ queriesSatisfy_chainM L hK i _)
      ?_
    rw [evalWithAnswerFn_sequenceFin]
    simp only [eval_chainM]
    refine queriesSatisfy_digestQ (fullInput_slot L (s := .leaf l τ (leafOfNat index)) hK ?_)
    have hv : (fun i ↦ valuePos L (cpos l τ (leafOfNat index) i (chainLength - 1))) =
        fun i ↦ L.chainValue l τ (leafOfNat index) i (chainLength - 1) :=
      funext fun i ↦ valuePos_cpos L l τ _ i (by decide)
    change _ = addressedHashInput _ _
      (digestsPayload fun i ↦ valuePos L (cpos l τ (leafOfNat index) i (chainLength - 1)))
    rw [hv]
    rfl
  | level + 1, index, hl, hi => by
    have hc := two_mul_add_one_lt_sub hi (by omega) hl
    have hc' : 2 * index + 1 < 2 ^ layerHeight topLayer :=
      lt_of_lt_of_le (lt_two_pow_of_lt hc) (two_pow_layerHeight_le l)
    rw [Nat.add_sub_cancel] at hc
    have h10 := layerHeight_le l
    have htop : layerHeight topLayer = 10 := rfl
    rw [treeM]
    refine queriesSatisfy_bind (queriesSatisfy_treeM hτ level _ (by omega) (by omega))
      (queriesSatisfy_bind (queriesSatisfy_treeM hτ level _ (by omega) hc) ?_)
    rw [eval_treeM, eval_treeM]
    refine queriesSatisfy_digestQ
      (fullInput_slot L (s := .node l τ (level + 1) index) ⟨hτ, by omega, hl, hi⟩ ?_)
    change _ = addressedHashInput _ _
      (nodePayload (valuePos L (tpos l τ (level + 1 - 1) (2 * index)))
        (valuePos L (tpos l τ (level + 1 - 1) (2 * index + 1))))
    rw [Nat.add_sub_cancel, valuePos_tpos L l τ (by omega) (by omega),
      valuePos_tpos L l τ (by omega) hc']
    rfl

theorem queriesSatisfy_forsM (idx : Index) (κ : ForsTreeIndex) :
    ∀ h j, h ≤ forsTreeHeight → j < 2 ^ (forsTreeHeight - h) →
      QueriesSatisfy L.hash (FullInput L) (forsM L.publicSeed L.secretSeed idx κ h j)
  | 0, j, _, _ => by
    rw [forsM]
    refine queriesSatisfy_bind (queriesSatisfy_digestQ
      (Or.inr (Or.inl ⟨.forsSecret idx κ (forsLeafOfNat j), trivial, rfl⟩))) ?_
    rw [eval_digestQ]
    exact queriesSatisfy_digestQ
      (fullInput_slot L (s := .forsLeaf idx κ (forsLeafOfNat j)) trivial rfl)
  | h + 1, j, hh, hj => by
    have hf10 : forsTreeHeight = 10 := rfl
    have hc := two_mul_add_one_lt_sub hj (by omega) hh
    have hc' : 2 * j + 1 < 2 ^ forsTreeHeight := lt_two_pow_of_lt hc
    rw [Nat.add_sub_cancel] at hc
    rw [forsM]
    refine queriesSatisfy_bind (queriesSatisfy_forsM idx κ h _ (by omega) (by omega))
      (queriesSatisfy_bind (queriesSatisfy_forsM idx κ h _ (by omega) hc) ?_)
    rw [eval_forsM, eval_forsM]
    refine queriesSatisfy_digestQ
      (fullInput_slot L (s := .forsNode idx κ (h + 1) j) ⟨by omega, hh, hj⟩ ?_)
    change _ = addressedHashInput _ _
      (nodePayload (valuePos L (fpos idx κ (h + 1 - 1) (2 * j)))
        (valuePos L (fpos idx κ (h + 1 - 1) (2 * j + 1))))
    rw [Nat.add_sub_cancel, valuePos_fpos L idx κ (by omega) (by omega),
      valuePos_fpos L idx κ (by omega) hc']
    rfl

theorem queriesSatisfy_forsKeyM (idx : Index) :
    QueriesSatisfy L.hash (FullInput L) (forsKeyM L.publicSeed L.secretSeed idx) := by
  rw [forsKeyM]
  refine queriesSatisfy_bind (queriesSatisfy_sequenceFin fun κ ↦
    queriesSatisfy_forsM L idx κ _ _ le_rfl (Nat.two_pow_pos _)) ?_
  rw [evalWithAnswerFn_sequenceFin]
  simp only [eval_forsM]
  refine queriesSatisfy_digestQ (fullInput_slot L (s := .forsRoots idx) trivial ?_)
  have hv : (fun κ ↦ valuePos L (fpos idx κ forsTreeHeight 0)) =
      fun κ ↦ L.forsValue idx κ forsTreeHeight 0 :=
    funext fun κ ↦ valuePos_fpos L idx κ le_rfl (Nat.two_pow_pos _)
  change _ = addressedHashInput _ _
    (digestsPayload fun κ ↦ valuePos L (fpos idx κ forsTreeHeight 0))
  rw [hv]
  rfl

theorem queriesSatisfy_valM {p : ValPos} (hp : FullPos p) :
    QueriesSatisfy L.hash (FullInput L) (valM L.publicSeed L.secretSeed p) := by
  cases p with
  | chain l τ e i j => exact queriesSatisfy_chainM L hp i j.val
  | tree l τ level index => exact queriesSatisfy_treeM L hp.1 _ _ hp.2.1 hp.2.2
  | forsSecret idx κ s =>
    exact queriesSatisfy_digestQ (Or.inr (Or.inl ⟨.forsSecret idx κ s, trivial, rfl⟩))
  | forsTree idx κ height node =>
    exact queriesSatisfy_forsM L idx κ _ _ (Nat.lt_succ_iff.mp height.isLt) hp
  | forsKey idx => exact queriesSatisfy_forsKeyM L idx

/-- **Every query of the full computation is an honest input.** -/
theorem queriesSatisfy_fullComp :
    QueriesSatisfy L.hash (FullInput L) (fullComp L.secretSeed) := by
  unfold fullComp
  refine queriesSatisfy_bind (queriesSatisfy_hashQ (Or.inl (Or.inl rfl))) ?_
  refine queriesSatisfy_bind (queriesSatisfy_hashQ (Or.inl (Or.inr rfl))) ?_
  rw [eval_hashQ, eval_hashQ, hash_prfKey, truncateHash_publicSeed]
  unfold fullFrom
  refine queriesSatisfy_bind (queriesSatisfy_tabulate fun p ↦ ?_) ?_
  · unfold fullVal
    split_ifs with hp
    · exact queriesSatisfy_valM L hp
    · exact queriesSatisfy_pure _
  refine queriesSatisfy_bind
    (queriesSatisfy_tabulate fun msg ↦ queriesSatisfy_digestQ (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨msg, rfl⟩))))) ?_
  refine queriesSatisfy_bind (queriesSatisfy_tabulate fun c ↦ ?_) (queriesSatisfy_pure _)
  simp only [eval_tabulate, eval_digestQ, eval_fullVal, ite_eq_left fullPos_rootPos]
  exact queriesSatisfy_hashQ (Or.inr (Or.inr (Or.inr (Or.inr ⟨c.1, c.2, rfl⟩))))

end sat

/-! ## G0 is runtime 1 with the full table hardwired -/

section reads

/-- The full computation returns `PK.seed` and the full hidden values. -/
theorem fst_honestEval_fullComp (L : HonestTable) :
    (honestEval L.keys L.perm (fullComp L.secretSeed)).1 = (L.publicSeed, fullVals L) := by
  rw [fst_honestEval]
  change evalWithAnswerFn L.hash (fullComp L.secretSeed) = _
  simp only [fullComp, fullFrom, evalWithAnswerFn_bind, eval_hashQ, hash_prfKey,
    truncateHash_publicSeed, eval_tabulate, eval_digestQ, eval_fullVal, evalWithAnswerFn_pure,
    ite_eq_left fullPos_rootPos, valuePos_rootPos]
  rfl

/-- The honest table as `SK.seed`, permutation and keys. -/
def fullSplit : HonestTable ≃ MasterSeed × Equiv.Perm (X × Z) × SpongeKeys X Z where
  toFun L := (L.secretSeed, L.perm, L.keys)
  invFun x := ⟨x.2.2, x.2.1, x.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The seed is uniform over the `2^256` secret seeds. -/
theorem prEvent_sampleSeed (S0 : MasterSeed) :
    Pr{let s ← RandomPermutationModel.sufCmaScheme.sampleSeed}[s = S0] = (2 ^ 256)⁻¹ := by
  rw [show RandomPermutationModel.sufCmaScheme.sampleSeed = sampleMasterSeed from rfl,
    sampleMasterSeed,
    @SampleableType.prEvent_uniformSample MasterSeed (SampleableType.ofFintype MasterSeed) _
      (· = S0) _, Finset.filter_eq', ite_eq_left (Finset.mem_univ _),
    Finset.card_singleton, ← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec, Nat.cast_one,
    one_div, Nat.cast_pow, Nat.cast_ofNat]

variable (A : SAdversary)
  (gT : Pub → ((s : HPos) → XD s) → QComp (hwReadSpec X Z Unit) (QReg.of Unit) (QReg.of Unit) Bool)

/-- **The contract of a read game `gT` for runtime 1 with the full table** (SP-GT's grind-only
game): it does not read the public keys, it reads the hidden values only on the full coordinates,
and against the honest functions of every table it has the law of the generic read game
`gameReads` after honest key generation. -/
structure FullReads : Prop where
  keys : ∀ (seed : PublicParameter) (π : Equiv.Perm (X × Z)) (t t' : SpongeKeys X Z)
    (v : (s : HPos) → XD s), gT ⟨seed, π, t⟩ v = gT ⟨seed, π, t'⟩ v
  full : ∀ (pub : Pub) (v v' : (s : HPos) → XD s), (∀ s, FullCoord s → v s = v' s) →
    gT pub v = gT pub v'
  reads : ∀ L : HonestTable,
    (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (gameReads Unit L.perm RandomPermutationModel.sufCmaScheme schemeWithHash A
          (honestEval L.keys L.perm (schemeWithHash.keygen L.secretSeed))) (SubState.basis ())
        (fun p ↦ p.2.2) =
      (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (gT (pubOf L) (valueAt L)) (SubState.basis ()) (fun p ↦ p.2.2)

/-- **The read game from the full computation's result** and `π` (the keys are not read). -/
def yT (π : Equiv.Perm (X × Z))
    (b : (PublicParameter × ((s : HPos) → XD s)) × List (SpongeRead X Z)) :
    QComp (hwReadSpec X Z Unit) (QReg.of Unit) (QReg.of Unit) Bool :=
  gT ⟨b.1.1, π, keys₀⟩ b.1.2

/-- The law of runtime 1 with `fullHw L` hardwired, running the read game at `L`. -/
noncomputable def fullLaw (L : HonestTable) : Measure Bool :=
  (spongeHardwiredReadRuntime X Z (fullHw L) ()).evalDistMap .instruments
    (gT (pubOf L) (valueAt L)) (SubState.basis ()) fun p ↦ p.2.2

/-- `fullLaw` at the table of a secret seed, a permutation and keys. -/
noncomputable def fullLawPT (S0 : MasterSeed) (π : Equiv.Perm (X × Z)) (t : SpongeKeys X Z) :
    Measure Bool :=
  fullLaw gT ⟨t, π, S0⟩

/-- The win probability of runtime 1 with `fullHw L` hardwired, running the read game. -/
noncomputable def p1F (L : HonestTable) : ℝ≥0∞ :=
  fullLaw gT L {true}

variable {A gT}

theorem yT_honestEval (h : FullReads A gT) (L : HonestTable) :
    yT gT L.perm (honestEval L.keys L.perm (fullComp L.secretSeed)) = gT (pubOf L) (valueAt L) := by
  rw [yT, fst_honestEval_fullComp]
  exact (h.keys L.publicSeed L.perm keys₀ L.keys (fullVals L)).trans
    (h.full _ _ _ fun _ hs ↦ fullVals_eq L hs)

theorem readsLaw_eq (h : FullReads A gT) (L : HonestTable) :
    (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (gameReads Unit L.perm RandomPermutationModel.sufCmaScheme schemeWithHash A
          (honestEval L.keys L.perm (schemeWithHash.keygen L.secretSeed))) (SubState.basis ())
        (fun p ↦ p.2.2) =
      (spongeFnReadRuntime X Z L.keys (hwEmpty X Z) ()).evalDistMap .instruments
        (yT gT L.perm (honestEval L.keys L.perm (fullComp L.secretSeed))) (SubState.basis ())
        (fun p ↦ p.2.2) := by
  rw [yT_honestEval h]
  exact h.reads L

theorem hwLaw_eq (h : FullReads A gT) (L : HonestTable) :
    (spongeHardwiredReadRuntime X Z (readsHw (honestEval L.keys L.perm
        (fullComp L.secretSeed)).2) ()).evalDistMap .instruments
        (yT gT L.perm (honestEval L.keys L.perm (fullComp L.secretSeed))) (SubState.basis ())
        (fun p ↦ p.2.2) = fullLaw gT L := by
  rw [yT_honestEval h, fullLaw, fullHw]

/-- **G2 is runtime 1 with the full table**, at a secret seed and `π`: the average over `t` of the
read runtime on `gameReads` after honest key generation. -/
theorem sum_reads_eq_fullLaw (h : FullReads A gT) (S0 : MasterSeed) (π : Equiv.Perm (X × Z)) :
    ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) ()).evalDistMap .instruments
          (gameReads Unit π RandomPermutationModel.sufCmaScheme schemeWithHash A
            (honestEval t π (schemeWithHash.keygen S0)))
          (SubState.basis ()) (fun p ↦ p.2.2) =
      ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ • fullLaw gT ⟨t, π, S0⟩ :=
  calc _ = ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeFnReadRuntime X Z t (hwEmpty X Z) ()).evalDistMap .instruments
          (yT gT π (honestEval t π (fullComp S0))) (SubState.basis ()) (fun p ↦ p.2.2) :=
        Finset.sum_congr rfl fun t _ ↦ congrArg (HSMul.hSMul _) (readsLaw_eq h ⟨t, π, S0⟩)
    _ = ∑ t : SpongeKeys X Z, (Fintype.card (SpongeKeys X Z) : ℝ≥0∞)⁻¹ •
        (spongeHardwiredReadRuntime X Z (readsHw (honestEval t π (fullComp S0)).2) ()).evalDistMap
          .instruments (yT gT π (honestEval t π (fullComp S0))) (SubState.basis ())
          (fun p ↦ p.2.2) :=
        spongeEvalDistMap_eq_avg_runtime1 π (fullComp S0) () .instruments (yT gT π)
          (SubState.basis ()) fun p ↦ p.2.2
    _ = _ := Finset.sum_congr rfl fun t _ ↦ congrArg (HSMul.hSMul _) (hwLaw_eq h ⟨t, π, S0⟩)

/-- The win probability at a secret seed, as the average over `π` and `t` of `fullLawPT`. -/
theorem prob_game_eq_avg_fullLawPT (h : FullReads A gT) (S0 : MasterSeed) :
    qrpmEvalDistMap .instruments
        (game RandomPermutationModel.sufCmaScheme keccakStateEquiv S0 A) (SubState.basis ())
        (fun _ p ↦ p.2.2) {true} =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π ∈ Finset.univ,
        ∑ t ∈ univK π, keysW π t * fullLawPT gT S0 π t {true} := by
  have hμ : qrpmEvalDistMap .instruments
        (game RandomPermutationModel.sufCmaScheme keccakStateEquiv S0 A) (SubState.basis ())
        (fun _ p ↦ p.2.2) =
      (Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ • ∑ π ∈ Finset.univ,
        ∑ t ∈ univK π, keysW π t • fullLawPT gT S0 π t :=
    (qrpm_game_eq_reads (M := Unit) RandomPermutationModel.sufCmaScheme schemeWithHash
        overPermutation_schemeWithHash.symm () S0 A (SubState.basis ()) fun p ↦ p.2.2).trans
      (congrArg (HSMul.hSMul _) (Finset.sum_congr rfl fun π _ ↦
        (sum_reads_eq_fullLaw h S0 π).trans (Finset.sum_congr (rfl : Finset.univ = univK π)
          fun t _ ↦ congr_arg₂ HSMul.hSMul (rfl : _ = keysW π t)
            (rfl : fullLaw gT ⟨t, π, S0⟩ = fullLawPT gT S0 π t))))
  exact (congrArg (fun μ : Measure Bool ↦ μ {true}) hμ).trans
    (smul_sum_sum_smul_apply _ Finset.univ univK keysW (fullLawPT gT S0) {true})

/-- **G0 is the table average of runtime 1 with the full table hardwired**, running any read game
with the contract `FullReads`. -/
theorem winProb_eq_uavg_full (h : FullReads A gT) :
    winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A = uavg (fun L ↦
      (spongeHardwiredReadRuntime X Z (fullHw L) ()).evalDistMap .instruments
        (gT (pubOf L) (valueAt L)) (SubState.basis ()) (fun p ↦ p.2.2) {true}) :=
  calc winProb RandomPermutationModel.sufCmaScheme keccakStateEquiv A
      = (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ * ∑ S0 : MasterSeed,
          qrpmEvalDistMap .instruments
            (game RandomPermutationModel.sufCmaScheme keccakStateEquiv S0 A)
            (SubState.basis ()) (fun _ p ↦ p.2.2) {true} := by
        rw [winProb_eq_uniform _ _ prEvent_sampleSeed A, card_masterSeed, Nat.cast_pow,
          Nat.cast_ofNat]
    _ = (Fintype.card MasterSeed : ℝ≥0∞)⁻¹ * ∑ S0 : MasterSeed,
          ((Fintype.card (Equiv.Perm (X × Z)) : ℝ≥0∞)⁻¹ * ∑ π ∈ Finset.univ,
            ∑ t ∈ univK π, keysW π t * fullLawPT gT S0 π t {true}) :=
        congrArg (HMul.hMul _)
          (Finset.sum_congr rfl fun S0 _ ↦ prob_game_eq_avg_fullLawPT h S0)
    _ = uavg (p1F gT) :=
        (uavg_eq_avg3 fullSplit (p1F gT) univK keysW (fullLawPT gT) {true} (fun _ ↦ rfl)
          (fun _ _ ↦ rfl) fun s p k ↦ congrArg (fun μ : Measure Bool ↦ μ {true})
            (rfl : fullLawPT gT s p k = fullLaw gT (fullSplit.symm (s, p, k)))).symm

end reads

end Quantum.Sphincs.Assembly

end
