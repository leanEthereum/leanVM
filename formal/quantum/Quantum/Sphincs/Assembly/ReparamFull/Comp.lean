module

public import Quantum.Sphincs.Assembly.GameT
public import Quantum.Sphincs.Assembly.PathsDisjoint
public import Quantum.Sphincs.Assembly.PathBad
public import Quantum.Sphincs.Hybrid.SchemeSplit

@[expose] public section

/-!
# Computations hashing every in-table slot from the public data

SchemeSplit's good set is parametrized by computations `Q i P Cs` of `PK.seed = P` and the
secrets' hashes `Cs` (never `SK.seed`). `compQ` gives one per in-range tree of the hypertree (its
root) and one per FORS instance (its FORS key), recomputing the values by hash queries as
FullTable's `treeM`/`forsKeyM`, except that a secret of domain `d` is `truncateHash (Cs d)`, no
query (`chainC`, `treeC`, `forsC`, `forsKeyC`).

* `hashesSlots_compQ`: every in-table slot's honest input is a query of one of them.
* `cells_mem_compQ`: its paths' `k`-, `k'`- and `h`-cells are read by that computation.
* `length_honestEval_compQ`, `sum_compReads_le`: at most `compReads i` reads each (`3` per block:
  `603 · 2^h_l` per tree, `147396` per FORS instance), at most `2^44` in total.
-/

open Quantum.SufCma

open Quantum QuantumRuntime Quantum.Sponge Sphincs Common.SufCma
open HashSig (Digest HashOutput PublicParameter HashInput chainLength littleEndianBytes
  truncateHash digestsPayload)
open HashSig.OverPermutation (sequenceFin nodePayload)
open Quantum.Xmss (X Z blocks length_blocks evalWithAnswerFn_sequenceFin)
open Quantum.Xmss.Hybrid (hCells kCells k'Cells mem_hCells mem_kCells mem_k'Cells)
open Quantum.Xmss.Assembly (hashQ mem_queries_bind_left mem_queries_bind_right
  mem_queries_sequenceFin)
open Quantum.Sphincs.Hybrid (schemeData secHash secret_eq_secHash)

namespace Quantum.Sphincs.Assembly

/-! ## The computations from `PK.seed` and the secrets' hashes -/

section comp

/-- Position `j` of chain `i` of the one-time key `(l, τ, e)` by hash queries from `PK.seed = P`
and the secrets' hashes `Cs` (as `chainM`, the start without a query). -/
def chainC (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (l : Layer) (τ : TreeIndex)
    (e : TreeLeafIndex) (i : ChainIndex) : ℕ → OracleComp SchemeHashSpec Digest
  | 0 => pure (truncateHash (Cs (.oneTimeChain l τ e i)))
  | j + 1 => if hj : j < chainLength - 1 then
      chainC P Cs l τ e i j >>= fun d ↦
        digestQ (addressedHashInput P (hashDomainFields (.chain l τ e i ⟨j, hj⟩))
          (littleEndianBytes 16 d))
    else pure 0

/-- The value of tree `τ` of layer `l` at `level`, index `index`, by hash queries from `P` and
`Cs` (as `treeM`). -/
def treeC (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (l : Layer) (τ : TreeIndex) :
    ℕ → ℕ → OracleComp SchemeHashSpec Digest
  | 0, index =>
      sequenceFin (fun i : ChainIndex ↦ chainC P Cs l τ (leafOfNat index) i (chainLength - 1)) >>=
        fun ends ↦ digestQ (addressedHashInput P (hashDomainFields (.leaf l τ (leafOfNat index)))
          (digestsPayload ends))
  | level + 1, index =>
      treeC P Cs l τ level (2 * index) >>= fun a ↦ treeC P Cs l τ level (2 * index + 1) >>= fun b ↦
        digestQ (addressedHashInput P (hashDomainFields (.node l τ (level + 1) index))
          (nodePayload a b))

/-- The value of FORS tree `κ` of instance `idx` at `height`, node `j`, by hash queries from `P`
and `Cs` (as `forsM`, the secret without a query). -/
def forsC (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (idx : Index)
    (κ : ForsTreeIndex) : ℕ → ℕ → OracleComp SchemeHashSpec Digest
  | 0, j => digestQ (addressedHashInput P (hashDomainFields (.forsLeaf idx κ (forsLeafOfNat j)))
      (littleEndianBytes 16 (truncateHash (Cs (.forsSecret idx κ (forsLeafOfNat j))))))
  | h + 1, j =>
      forsC P Cs idx κ h (2 * j) >>= fun a ↦ forsC P Cs idx κ h (2 * j + 1) >>= fun b ↦
        digestQ (addressedHashInput P (hashDomainFields (.forsNode idx κ (h + 1) j))
          (nodePayload a b))

/-- The FORS public key of instance `idx` by hash queries from `P` and `Cs` (as `forsKeyM`). -/
def forsKeyC (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (idx : Index) :
    OracleComp SchemeHashSpec Digest :=
  sequenceFin (fun κ : ForsTreeIndex ↦ forsC P Cs idx κ forsTreeHeight 0) >>= fun roots ↦
    digestQ (addressedHashInput P (hashDomainFields (.forsRoots idx)) (digestsPayload roots))

theorem two_pow_treeBits_le (l : Layer) : 2 ^ treeBits l ≤ 2 ^ indexBits :=
  Nat.pow_le_pow_right (by norm_num) ((Nat.sub_le _ _).trans (Nat.sub_le _ _))

/-- **The computations**: the in-range trees of the hypertree (layer `l`, tree below
`2^treeBits l`) and the FORS instances. -/
abbrev CIdx : Type := (Σ l : Layer, Fin (2 ^ treeBits l)) ⊕ Index

instance instFintypeCIdx : Fintype CIdx :=
  inferInstanceAs (Fintype ((Σ l : Layer, Fin (2 ^ treeBits l)) ⊕ Index))

/-- **One computation per in-range tree** (its root) **and per FORS instance** (its key), from
`PK.seed = P` and the secrets' hashes `Cs`. -/
def compQ : CIdx → PublicParameter → (KeygenDomain → HashOutput) →
    OracleComp SchemeHashSpec Digest
  | .inl ⟨l, τ⟩, P, Cs => treeC P Cs l (Fin.castLE (two_pow_treeBits_le l) τ) (layerHeight l) 0
  | .inr idx, P, Cs => forsKeyC P Cs idx

end comp

/-! ## The computations return the table's values -/

section eval

variable (L : HonestTable)

theorem eval_chainC (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) : ∀ j,
    evalWithAnswerFn L.hash (chainC L.publicSeed (secHash L) l τ e i j) = L.chainValue l τ e i j
  | 0 => by
    rw [chainC, evalWithAnswerFn_pure]
    exact (secret_eq_secHash L _).symm
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · simp only [chainC, hj, ↓reduceDIte, evalWithAnswerFn_bind, eval_chainC l τ e i j,
        eval_digestQ]
      exact (L.chainValue_succ l τ e i ⟨j, hj⟩).symm
    · simp only [chainC, hj, ↓reduceDIte, evalWithAnswerFn_pure, HonestTable.chainValue]

theorem eval_treeC (l : Layer) (τ : TreeIndex) : ∀ level index,
    evalWithAnswerFn L.hash (treeC L.publicSeed (secHash L) l τ level index) =
      L.treeValue l τ level index
  | 0, index => by
    simp only [treeC, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, eval_chainC,
      eval_digestQ]
    rfl
  | level + 1, index => by
    simp only [treeC, evalWithAnswerFn_bind, eval_treeC l τ level, eval_digestQ]
    exact (L.treeValue_succ l τ level index).symm

theorem eval_forsC (idx : Index) (κ : ForsTreeIndex) : ∀ h j,
    evalWithAnswerFn L.hash (forsC L.publicSeed (secHash L) idx κ h j) = L.forsValue idx κ h j
  | 0, j => by
    simp only [forsC, eval_digestQ]
    rfl
  | h + 1, j => by
    simp only [forsC, evalWithAnswerFn_bind, eval_forsC idx κ h, eval_digestQ]
    exact (L.forsValue_succ idx κ h j).symm

end eval

/-! ## Every in-table slot's input is hashed -/

section queries

variable (f : QueryImpl SchemeHashSpec Id)

theorem mem_queries_chainC_le (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (l : Layer)
    (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) {j : ℕ} {q : HashInput}
    (h : q ∈ queries f (chainC P Cs l τ e i j)) :
    ∀ d, j + d ≤ chainLength - 1 → q ∈ queries f (chainC P Cs l τ e i (j + d))
  | 0, _ => h
  | d + 1, hd => by
    have ih := mem_queries_chainC_le P Cs l τ e i h d (by omega)
    have hj : j + d < chainLength - 1 := by omega
    show q ∈ queries f (chainC P Cs l τ e i (j + d + 1))
    rw [chainC, dite_eq_left hj]
    exact mem_queries_bind_left f _ _ ih

/-- **A subtree's queries are its ancestors'.** -/
theorem mem_queries_treeC_up (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (l : Layer)
    (τ : TreeIndex) : ∀ d lev index {q : HashInput}, q ∈ queries f (treeC P Cs l τ lev index) →
      q ∈ queries f (treeC P Cs l τ (lev + d) (index / 2 ^ d))
  | 0, lev, index, q, h => by simpa using h
  | d + 1, lev, index, q, h => by
    have ih := mem_queries_treeC_up P Cs l τ d lev index h
    have hdiv : index / 2 ^ d = 2 * (index / 2 ^ (d + 1)) + index / 2 ^ d % 2 := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      omega
    show q ∈ queries f (treeC P Cs l τ (lev + d + 1) (index / 2 ^ (d + 1)))
    simp only [treeC]
    rcases Nat.mod_two_eq_zero_or_one (index / 2 ^ d) with h0 | h1
    · rw [h0, add_zero] at hdiv
      rw [hdiv] at ih
      exact mem_queries_bind_left f _ _ ih
    · rw [h1] at hdiv
      rw [hdiv] at ih
      exact mem_queries_bind_right f _ _ (mem_queries_bind_left f _ _ ih)

/-- **A FORS subtree's queries are its ancestors'.** -/
theorem mem_queries_forsC_up (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (idx : Index)
    (κ : ForsTreeIndex) : ∀ d h j {q : HashInput}, q ∈ queries f (forsC P Cs idx κ h j) →
      q ∈ queries f (forsC P Cs idx κ (h + d) (j / 2 ^ d))
  | 0, h, j, q, hq => by simpa using hq
  | d + 1, h, j, q, hq => by
    have ih := mem_queries_forsC_up P Cs idx κ d h j hq
    have hdiv : j / 2 ^ d = 2 * (j / 2 ^ (d + 1)) + j / 2 ^ d % 2 := by
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      omega
    show q ∈ queries f (forsC P Cs idx κ (h + d + 1) (j / 2 ^ (d + 1)))
    simp only [forsC]
    rcases Nat.mod_two_eq_zero_or_one (j / 2 ^ d) with h0 | h1
    · rw [h0, add_zero] at hdiv
      rw [hdiv] at ih
      exact mem_queries_bind_left f _ _ ih
    · rw [h1] at hdiv
      rw [hdiv] at ih
      exact mem_queries_bind_right f _ _ (mem_queries_bind_left f _ _ ih)

/-- A query of an in-range tree's subtree is a query of a computation. -/
theorem mem_compQ_of_treeC {P : PublicParameter} {Cs : KeygenDomain → HashOutput} {l : Layer}
    {τ : TreeIndex} (hτ : τ.val < 2 ^ treeBits l) {lev index : ℕ} (hl : lev ≤ layerHeight l)
    (hi : index < 2 ^ (layerHeight l - lev)) {q : HashInput}
    (h : q ∈ queries f (treeC P Cs l τ lev index)) : ∃ i, q ∈ queries f (compQ i P Cs) := by
  refine ⟨.inl ⟨l, ⟨τ.val, hτ⟩⟩, ?_⟩
  have hu := mem_queries_treeC_up f P Cs l τ (layerHeight l - lev) lev index h
  rw [Nat.add_sub_cancel' hl, Nat.div_eq_of_lt hi] at hu
  exact hu

/-- A query of a FORS subtree is a query of a computation. -/
theorem mem_compQ_of_forsC {P : PublicParameter} {Cs : KeygenDomain → HashOutput} {idx : Index}
    {κ : ForsTreeIndex} {h j : ℕ} (hh : h ≤ forsTreeHeight) (hj : j < 2 ^ (forsTreeHeight - h))
    {q : HashInput} (hq : q ∈ queries f (forsC P Cs idx κ h j)) :
    ∃ i, q ∈ queries f (compQ i P Cs) := by
  refine ⟨.inr idx, ?_⟩
  have hu := mem_queries_forsC_up f P Cs idx κ (forsTreeHeight - h) h j hq
  rw [Nat.add_sub_cancel' hh, Nat.div_eq_of_lt hj] at hu
  exact mem_queries_bind_left f _ _ (mem_queries_sequenceFin f _ κ hu)

variable (L : HonestTable)

theorem slotInput_mem_chainC (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex)
    (step : HashSig.ChainStep) :
    slotInput L.publicSeed (.chain l τ e i step) (valuePos L) ∈
      queries L.hash (chainC L.publicSeed (secHash L) l τ e i (step.val + 1)) := by
  have h4 : chainLength = 4 := rfl
  have hst := step.isLt
  rw [chainC, dite_eq_left step.isLt]
  refine mem_queries_bind_right _ _ _ ?_
  rw [eval_chainC]
  change addressedHashInput L.publicSeed (hashDomainFields (.chain l τ e i step))
    (littleEndianBytes 16 (valuePos L (cpos l τ e i step.val))) ∈ _
  rw [valuePos_cpos L l τ e i (by omega)]
  exact mem_queries_digestQ _ _

theorem slotInput_mem_treeC_leaf (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    slotInput L.publicSeed (.leaf l τ e) (valuePos L) ∈
      queries L.hash (treeC L.publicSeed (secHash L) l τ 0 e.val) := by
  rw [treeC]
  refine mem_queries_bind_right _ _ _ ?_
  rw [evalWithAnswerFn_sequenceFin]
  simp only [eval_chainC, leafOfNat_val]
  have hv : (fun i ↦ valuePos L (cpos l τ e i (chainLength - 1))) =
      fun i ↦ L.chainValue l τ e i (chainLength - 1) :=
    funext fun i ↦ valuePos_cpos L l τ e i (by decide)
  change addressedHashInput L.publicSeed (hashDomainFields (.leaf l τ e))
    (digestsPayload fun i ↦ valuePos L (cpos l τ e i (chainLength - 1))) ∈ _
  rw [hv]
  exact mem_queries_digestQ _ _

theorem slotInput_mem_treeC_node {l : Layer} {τ : TreeIndex} {height index : ℕ}
    (hs : InTable (.node l τ height index)) :
    slotInput L.publicSeed (.node l τ height index) (valuePos L) ∈
      queries L.hash (treeC L.publicSeed (secHash L) l τ height index) := by
  obtain ⟨-, h1, hh, hi⟩ := hs
  have hl := layerHeight_le l
  have htop : layerHeight topLayer = 10 := rfl
  have hc := two_mul_add_one_lt_sub hi h1 hh
  have hc' : 2 * index + 1 < 2 ^ layerHeight topLayer :=
    lt_of_lt_of_le (lt_two_pow_of_lt hc) (two_pow_layerHeight_le l)
  obtain ⟨h', rfl⟩ : ∃ h', height = h' + 1 := ⟨height - 1, by omega⟩
  rw [treeC]
  refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _ ?_)
  rw [eval_treeC, eval_treeC]
  change addressedHashInput L.publicSeed (hashDomainFields (.node l τ (h' + 1) index))
    (nodePayload (valuePos L (tpos l τ (h' + 1 - 1) (2 * index)))
      (valuePos L (tpos l τ (h' + 1 - 1) (2 * index + 1)))) ∈ _
  rw [Nat.add_sub_cancel, valuePos_tpos L l τ (by omega) (by omega),
    valuePos_tpos L l τ (by omega) hc']
  exact mem_queries_digestQ _ _

theorem slotInput_mem_forsC_leaf (idx : Index) (κ : ForsTreeIndex) (s : ForsLeafIndex) :
    slotInput L.publicSeed (.forsLeaf idx κ s) (valuePos L) ∈
      queries L.hash (forsC L.publicSeed (secHash L) idx κ 0 s.val) := by
  rw [forsC, forsLeafOfNat_val]
  exact mem_queries_digestQ _ _

theorem slotInput_mem_forsC_node {idx : Index} {κ : ForsTreeIndex} {height node : ℕ}
    (hs : InTable (.forsNode idx κ height node)) :
    slotInput L.publicSeed (.forsNode idx κ height node) (valuePos L) ∈
      queries L.hash (forsC L.publicSeed (secHash L) idx κ height node) := by
  obtain ⟨h1, hh, hi⟩ := hs
  have hc := two_mul_add_one_lt_sub hi h1 hh
  have hc' : 2 * node + 1 < 2 ^ forsTreeHeight := lt_two_pow_of_lt hc
  obtain ⟨h', rfl⟩ : ∃ h', height = h' + 1 := ⟨height - 1, by omega⟩
  rw [forsC]
  refine mem_queries_bind_right _ _ _ (mem_queries_bind_right _ _ _ ?_)
  rw [eval_forsC, eval_forsC]
  change addressedHashInput L.publicSeed (hashDomainFields (.forsNode idx κ (h' + 1) node))
    (nodePayload (valuePos L (fpos idx κ (h' + 1 - 1) (2 * node)))
      (valuePos L (fpos idx κ (h' + 1 - 1) (2 * node + 1)))) ∈ _
  rw [Nat.add_sub_cancel, valuePos_fpos L idx κ (by omega) (by omega),
    valuePos_fpos L idx κ (by omega) hc']
  exact mem_queries_digestQ _ _

theorem slotInput_mem_forsKeyC (idx : Index) :
    slotInput L.publicSeed (.forsRoots idx) (valuePos L) ∈
      queries L.hash (forsKeyC L.publicSeed (secHash L) idx) := by
  rw [forsKeyC]
  refine mem_queries_bind_right _ _ _ ?_
  rw [evalWithAnswerFn_sequenceFin]
  simp only [eval_forsC]
  have hv : (fun κ ↦ valuePos L (fpos idx κ forsTreeHeight 0)) =
      fun κ ↦ L.forsValue idx κ forsTreeHeight 0 :=
    funext fun κ ↦ valuePos_fpos L idx κ le_rfl (Nat.two_pow_pos _)
  change addressedHashInput L.publicSeed (hashDomainFields (.forsRoots idx))
    (digestsPayload fun κ ↦ valuePos L (fpos idx κ forsTreeHeight 0)) ∈ _
  rw [hv]
  exact mem_queries_digestQ _ _

/-- **Every in-table slot's honest input is hashed by one of the computations.** -/
theorem hashesSlots_compQ (L : HonestTable) {s : Slot} (hs : InTable s) :
    ∃ i, slotInput L.publicSeed s (valuePos L) ∈
      queries L.hash (compQ i L.publicSeed (secHash L)) := by
  have hf10 : forsTreeHeight = 10 := rfl
  cases s with
  | chain l τ e i step =>
    have h4 : chainLength = 4 := rfl
    have hst := step.isLt
    have h3 := mem_queries_chainC_le L.hash L.publicSeed (secHash L) l τ e i
      (slotInput_mem_chainC L l τ e i step) (chainLength - 1 - (step.val + 1)) (by omega)
    rw [show step.val + 1 + (chainLength - 1 - (step.val + 1)) = chainLength - 1 by omega] at h3
    refine mem_compQ_of_treeC L.hash hs.1 (lev := 0) (index := e.val) (Nat.zero_le _)
      (by rw [Nat.sub_zero]; exact hs.2) ?_
    rw [treeC]
    refine mem_queries_bind_left _ _ _ (mem_queries_sequenceFin _ _ i ?_)
    rw [leafOfNat_val]
    exact h3
  | leaf l τ e =>
    exact mem_compQ_of_treeC L.hash hs.1 (Nat.zero_le _) (by rw [Nat.sub_zero]; exact hs.2)
      (slotInput_mem_treeC_leaf L l τ e)
  | node l τ height index =>
    exact mem_compQ_of_treeC L.hash hs.1 hs.2.2.1 hs.2.2.2 (slotInput_mem_treeC_node L hs)
  | forsLeaf idx κ s =>
    exact mem_compQ_of_forsC L.hash (Nat.zero_le _) (by rw [Nat.sub_zero]; exact s.isLt)
      (slotInput_mem_forsC_leaf L idx κ s)
  | forsNode idx κ height node =>
    exact mem_compQ_of_forsC L.hash hs.2.1 hs.2.2 (slotInput_mem_forsC_node L hs)
  | forsRoots idx => exact ⟨.inr idx, slotInput_mem_forsKeyC L idx⟩
  | enc => exact hs.elim
  | prf => exact hs.elim
  | hmsg => exact hs.elim
  | prfMsg => exact hs.elim
  | expand => exact hs.elim

/-- **An in-table slot's path cells are read by a computation**: the `k`-, `k'`- and `h`-cells of
every round of its honest input. -/
theorem cells_mem_compQ (L : HonestTable) {s : Slot} (hs : InTable s) :
    ∃ i, ∀ j < nBlk L.publicSeed s,
      sCellK (tabW L) L.keys.1 s (valuePos L) j ∈ kCells (schemeData compQ L i).2 ∧
      sCellR (tabW L) L.keys.1 s (valuePos L) j ∈ k'Cells (schemeData compQ L i).2 ∧
      sCellZ (tabW L) L.keys.1 s (valuePos L) j ∈ hCells (schemeData compQ L i).2 := by
  obtain ⟨i, hi⟩ := hashesSlots_compQ L hs
  refine ⟨i, fun j hj ↦ ?_⟩
  have hr : (schemeData compQ L i).2 =
      (queries L.hash (compQ i L.publicSeed (secHash L))).flatMap (inputReads L.keys L.perm) :=
    snd_honestEval L.keys L.perm _
  rw [hr]
  obtain ⟨hk, hk', hh⟩ := round_mem_inputReads L.keys L.perm
    (slotInput L.publicSeed s (valuePos L)) (j := j)
    (by rw [length_blocks_slotInput]; exact hj)
  exact ⟨mem_kCells.mpr ⟨_, List.mem_flatMap.mpr ⟨_, hi, hk⟩⟩,
    mem_k'Cells.mpr ⟨_, List.mem_flatMap.mpr ⟨_, hi, hk'⟩⟩,
    mem_hCells.mpr ⟨_, List.mem_flatMap.mpr ⟨_, hi, hh⟩⟩⟩

end queries

/-! ## Read bounds -/

section reads

variable (f : QueryImpl SchemeHashSpec Id) {ρ : Type} (g : HashInput → List ρ)

theorem trace_digestQ (input : HashInput) : trace f g (digestQ input) = g input := by
  rw [digestQ, hashQ, trace_query_bind, trace_pure, List.append_nil]

theorem length_trace_sequenceFin {β : Type} {B : ℕ} :
    ∀ {n : ℕ} {c : Fin n → OracleComp SchemeHashSpec β},
      (∀ i, (trace f g (c i)).length ≤ B) → (trace f g (sequenceFin c)).length ≤ n * B
  | 0, _, _ => by simp [sequenceFin, trace_pure]
  | n + 1, c, h => by
    have h1 := h 0
    have h2 := length_trace_sequenceFin (n := n) (c := fun i ↦ c i.succ) fun i ↦ h i.succ
    simp only [sequenceFin, trace_bind, trace_pure, List.length_append, List.length_nil,
      add_zero]
    rw [add_one_mul]
    omega

variable {g} (hg : ∀ (P : PublicParameter) (d : HashDomain) (payload : HashInput),
  (g (addressedHashInput P (hashDomainFields d) payload)).length =
    3 * ((48 + payload.length) / 136 + 1))
include hg

theorem length_trace_chainC (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (l : Layer)
    (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) :
    ∀ j, (trace f g (chainC P Cs l τ e i j)).length ≤ 3 * j
  | 0 => by
    rw [chainC, trace_pure]
    exact Nat.zero_le _
  | j + 1 => by
    by_cases hj : j < chainLength - 1
    · have ih := length_trace_chainC P Cs l τ e i j
      simp only [chainC, hj, ↓reduceDIte, trace_bind, List.length_append, trace_digestQ, hg,
        length_le16]
      omega
    · rw [chainC, dite_eq_right hj, trace_pure]
      exact Nat.zero_le _

theorem length_trace_treeC (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (l : Layer)
    (τ : TreeIndex) : ∀ level index,
      (trace f g (treeC P Cs l τ level index)).length + 3 ≤ 603 * 2 ^ level
  | 0, index => by
    have hs := length_trace_sequenceFin f g (B := 9)
      (c := fun i : ChainIndex ↦ chainC P Cs l τ (leafOfNat index) i (chainLength - 1))
      fun i ↦ length_trace_chainC f hg P Cs l τ _ i _
    simp only [treeC, trace_bind, List.length_append, trace_digestQ, hg, length_digestsPayload]
    simp only [chainCount] at hs ⊢
    omega
  | level + 1, index => by
    have h1 := length_trace_treeC P Cs l τ level (2 * index)
    have h2 := length_trace_treeC P Cs l τ level (2 * index + 1)
    simp only [treeC, trace_bind, List.length_append, trace_digestQ, hg, length_nodePayload]
    rw [pow_succ]
    omega

theorem length_trace_forsC (P : PublicParameter) (Cs : KeygenDomain → HashOutput) (idx : Index)
    (κ : ForsTreeIndex) : ∀ h j, (trace f g (forsC P Cs idx κ h j)).length + 3 ≤ 6 * 2 ^ h
  | 0, j => by
    simp only [forsC, trace_digestQ, hg, length_le16, pow_zero]
    norm_num
  | h + 1, j => by
    have h1 := length_trace_forsC P Cs idx κ h (2 * j)
    have h2 := length_trace_forsC P Cs idx κ h (2 * j + 1)
    simp only [forsC, trace_bind, List.length_append, trace_digestQ, hg, length_nodePayload]
    rw [pow_succ]
    omega

theorem length_trace_forsKeyC (P : PublicParameter) (Cs : KeygenDomain → HashOutput)
    (idx : Index) : (trace f g (forsKeyC P Cs idx)).length ≤ 147396 := by
  have hs := length_trace_sequenceFin f g (B := 6141)
    (c := fun κ : ForsTreeIndex ↦ forsC P Cs idx κ forsTreeHeight 0)
    fun κ ↦ by
      have := length_trace_forsC f hg P Cs idx κ forsTreeHeight 0
      rw [show 2 ^ forsTreeHeight = 1024 from rfl] at this
      omega
  simp only [forsKeyC, trace_bind, List.length_append, trace_digestQ, hg, length_digestsPayload]
  simp only [forsTreeCount] at hs ⊢
  omega

end reads

/-- **The reads of a computation**: `3` per block, `603 · 2^h_l` for a tree of layer `l`
(`64` chains of `3` one-block steps and an `8`-block leaf per key, a one-block node per inner
node), `147396` for a FORS key (`24` trees of `2^11 - 1` one-block calls, a `4`-block roots
compression). -/
def compReads : CIdx → ℕ
  | .inl ⟨l, _⟩ => 603 * 2 ^ layerHeight l
  | .inr _ => 147396

theorem length_inputReads_addressed (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (d : HashDomain) (payload : HashInput) :
    (inputReads t π (addressedHashInput P (hashDomainFields d) payload)).length =
      3 * ((48 + payload.length) / 136 + 1) := by
  rw [inputReads, length_spongeReads, length_blocks, length_addressedHashInput]

/-- **The reads of each computation are at most `compReads i`.** -/
theorem length_honestEval_compQ (i : CIdx) (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (Cs : KeygenDomain → HashOutput) :
    (honestEval t π (compQ i P Cs)).2.length ≤ compReads i := by
  rw [snd_honestEval, ← trace_eq_flatMap]
  have hg := length_inputReads_addressed t π
  rcases i with ⟨l, τ⟩ | idx
  · exact (Nat.le_add_right _ 3).trans (length_trace_treeC _ hg P Cs l _ (layerHeight l) 0)
  · exact length_trace_forsKeyC _ hg P Cs idx

theorem sum_layer (F : Layer → ℕ) : ∑ l, F l = F 0 + F 1 + F 2 :=
  Fin.sum_univ_three F

/-- **At most `2^44` reads in total** (about `2^43.18`, the FORS keys). -/
theorem sum_compReads_le : ∑ i, compReads i ≤ 2 ^ 44 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [compReads, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [sum_layer]
  have t0 : treeBits 0 = 18 := rfl
  have t1 : treeBits 1 = 10 := rfl
  have t2 : treeBits 2 = 0 := rfl
  have l0 : layerHeight 0 = 8 := rfl
  have l1 : layerHeight 1 = 8 := rfl
  have l2 : layerHeight 2 = 10 := rfl
  rw [t0, t1, t2, l0, l1, l2, indexBits]
  norm_num

end Quantum.Sphincs.Assembly

end
