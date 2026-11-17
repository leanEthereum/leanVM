module

public import Quantum.Qrom.Sphincs.GameTCalls
public import Quantum.Qrom.Sphincs.GameTFacts
public import Quantum.Qrom.Xmss.Hybrid
public import Quantum.Xmss.Assembly.CostRun

@[expose] public section

/-!
# The hidden-value hybrid of leanSPHINCS in the QROM (runtime 1 against runtime 2)

The QROM game is runtime 1 on the realized template at the digest policy `msgPol`, averaged over
the hidden values `θ` (`winProb_eq_uavg_runtime1R`). The graded hybrid
(`uavg_win_runtime1R_le_graded_total`) compares it with runtime 2 (`runtimeR`), at the cost of the
hidden masses of runtime 1's cells (`hidCells θ`, the cells of the table) at the calls of `F` and
at the reads; the stream reindexing (`uavg_gameT_msgPol_eq_strPol`) then moves runtime 2 to the
event side's policy `strPol`.

* **Positions from cells** (`slotF`, `pos_eq_of_cellOf_eq`): a cell names its slot whatever the
  key, hence its position, whatever the table.
* **Sources** (`cellSrc`, `srcVals`, `sourcesQ`): a hidden cell not hardwired in a state of the
  source invariant (`SrcInv`, GameTFacts) has its source coordinate `srcOf p` unrevealed, and the
  cell fixes the digest of that coordinate's pair (`srcDig`, `pairDigest_srcOf_eq`), so its mass
  is at most `2^-128` per call (`kappaQ`).
* **Calls of `F`** (`uavg_spongeMass_le`): at most `q · 2^-128` summed over the `q` calls.
* **Reads** (`uavg_readMass_le`): at most `clsCapQ · 2^-128` over the reads (`readRec_gameT`).
  Program and record ports cost nothing.
* **The hybrid** (`sqrt_win_runtime1_le_qrom`):
  `√winProb ≤ √(E p2Q strPol) + 2q·2^-64 + √(clsCapQ·2^-128)`.
-/

open Matrix IPFunctor MeasureTheory
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open HashSig.OverPermutation (nodePayload)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (keyDerivationInput)

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid
open Quantum.Sphincs (Slot messageDigestInput prfMessageInput littleEndianBytes_injective
  messageDigestInput_injective prfMessageInput_injective keyDerivationInput_injective
  length_toBytes)
open Quantum.Xmss (length_littleEndianBytes)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT runtime1R extCls Sources
  sum_totalWeight_portMass_runtimeR_le_inv isChargeBound_mono_charge)

attribute [local irreducible] sphincsRom

/-! ## Positions from cells -/

section cells

/-- The public key an input names: bytes `16` to `47` of an `H_msg` input, the first `16` bytes
otherwise. -/
def pkOfInput (input : HashInput) : PublicKey :=
  if input.length = 84 then ⟨leAt input 16 16, leDigest input 32⟩ else ⟨leAt input 0 16, 0⟩

/-- **An input's slot under some key is its slot under the key it names.** -/
theorem slotOfInput_pkOfInput {pk : PublicKey} {input : HashInput} {s : Slot}
    (h : slotOfInput pk input = some s) : slotOfInput (pkOfInput input) input = some s := by
  unfold slotOfInput at h ⊢
  by_cases h84 : input.length = 84
  · rw [ite_eq_left h84] at h ⊢
    have hp : pkOfInput input = ⟨leAt input 16 16, leDigest input 32⟩ := ite_eq_left h84
    unfold hmsgSlotOf at h ⊢
    split_ifs at h
    rw [hp, ite_eq_left ⟨rfl, rfl⟩]
    exact h
  · rw [ite_eq_right h84] at h ⊢
    by_cases h93 : input.length = 93
    · rw [ite_eq_left h93] at h ⊢
      exact h
    · rw [ite_eq_right h93] at h ⊢
      by_cases h44 : input.length = 44
      · rw [ite_eq_left h44] at h ⊢
        exact h
      · rw [ite_eq_right h44] at h ⊢
        split_ifs at h
        have hp : (pkOfInput input).publicSeed = leAt input 0 16 := by
          rw [pkOfInput, ite_eq_right h84]
        rw [ite_eq_left hp.symm]
        exact h

/-- **The slot of a point of the domain**, under the key its bytes name. -/
def slotF (z : Qrom.HashDomain) : Option Slot :=
  slotOfInput (pkOfInput (decodeInput z)) (decodeInput z)

theorem slotF_cellOf (S0 : MasterSeed) (v : QTable) (p : Pos) :
    slotF (cellOf S0 p v) = some (posSlot v p.1) :=
  slotOfInput_pkOfInput (slotOf_cell (v.expandedKey S0) v.root (slotInRange_posSlot v p)
    (posPayload v p.1))

/-- Positions with equal slots, at any two tables, are equal. -/
theorem posSlot_inj {v v' : QTable} {p q : RawPos} (h : posSlot v p = posSlot v' q) : p = q := by
  cases p <;> cases q <;>
    simp only [posSlot, reduceCtorEq, Slot.prf.injEq, KeygenDomain.oneTimeChain.injEq,
      KeygenDomain.forsSecret.injEq, Slot.chain.injEq, Slot.leaf.injEq, Slot.node.injEq,
      Slot.forsLeaf.injEq, Slot.forsNode.injEq, Slot.forsRoots.injEq, Slot.prfMsg.injEq,
      Slot.hmsg.injEq, Slot.expand.injEq, Nat.add_right_cancel_iff] at h <;>
    first
      | rfl
      | exact absurd h (by decide)
      | simp only [RawPos.chainStart.injEq, RawPos.chain.injEq, RawPos.leaf.injEq,
          RawPos.node.injEq, RawPos.forsSecret.injEq, RawPos.forsLeaf.injEq,
          RawPos.forsNode.injEq, RawPos.forsRoots.injEq, RawPos.prfMsg.injEq,
          RawPos.hmsg.injEq, Fin.ext_iff]
        omega
      | simp only [RawPos.chainStart.injEq, RawPos.chain.injEq, RawPos.leaf.injEq,
          RawPos.node.injEq, RawPos.forsSecret.injEq, RawPos.forsLeaf.injEq,
          RawPos.forsNode.injEq, RawPos.forsRoots.injEq,
          RawPos.hmsg.injEq, Fin.ext_iff]
        tauto

/-- **A cell names its position**, whatever the master seed and the table. -/
theorem pos_eq_of_cellOf_eq {S0 S0' : MasterSeed} {v v' : QTable} {p q : Pos}
    (h : cellOf S0 p v = cellOf S0' q v') : p = q := by
  have h1 := slotF_cellOf S0 v p
  rw [h, slotF_cellOf S0' v' q] at h1
  exact Subtype.ext (posSlot_inj (Option.some.inj h1).symm)

/-- **The hidden cells at `θ`**: the cells of runtime 1's table. -/
def hidCells (θ : TVals) : Set Qrom.HashDomain :=
  {z | ∃ p, cellQ θ p = z}

theorem covers_hwT (θ : TVals) : Covers (hwT θ) (hidCells θ) ∅ ∅ := by
  refine ⟨fun z hz ↦ ?_, fun _ hx ↦ absurd rfl hx, fun _ hx ↦ absurd rfl hx⟩
  by_contra h
  exact hz ((table (seedOf θ)).tableDb_of_forall_ne fun p hp ↦ h ⟨p, hp⟩)

end cells

/-! ## The digest a cell carries of its source -/

section srcDig

/-- **The digest of its source a position's input carries**: the chain value, chain `0`'s end, the
left child, the FORS secret, FORS tree `0`'s root, `SK.prf`'s and `R(M)`'s digests; the master
seed's for the positions keyed by it. -/
def srcDig (S0 : MasterSeed) (v : QTable) : RawPos → Digest
  | .chain l τ e i step => v.chainValue l τ e i step.val
  | .leaf l τ e => v.endpoints l τ e chainZero
  | .node l τ level index => v.treeValue l τ level.val (2 * index.val)
  | .forsLeaf idx κ s => v.forsSecret idx κ s
  | .forsNode idx κ level node => v.forsValue idx κ level.val (2 * node.val)
  | .forsRoots idx => v.forsRoot idx forsZero
  | .prfMsg _ => truncateHash v.prfKey
  | .hmsg m => v.randomizer m
  | _ => truncateHash S0

/-- An addressed input determines its payload, whatever its prefix. -/
theorem addressedHashInput_payload_eq {Q Q' : PublicParameter} {a a' : Address}
    {p p' : HashInput} (h : addressedHashInput Q a p = addressedHashInput Q' a' p') : p = p' := by
  unfold addressedHashInput hasherInput at h
  exact (List.append_inj h (by simp [length_littleEndianBytes, length_toBytes])).2

/-- **A cell determines the digest of its source.** -/
theorem srcDig_eq_of_cellOf_eq {S0 S0' : MasterSeed} {v v' : QTable} {p : Pos}
    (h : cellOf S0 p v = cellOf S0' p v') : srcDig S0 v p.1 = srcDig S0' v' p.1 := by
  have hi : posInput S0 v p.1 = posInput S0' v' p.1 :=
    encodeInput_injective (encodeInput_posInput S0 v p)
      ((encodeInput_posInput S0' v' p).trans (congrArg some h.symm))
  obtain ⟨q, hq⟩ := p
  cases q with
  | prfKey =>
    change keyDerivationInput S0 1 = keyDerivationInput S0' 1 at hi
    exact congrArg truncateHash (keyDerivationInput_injective hi).1
  | publicSeed =>
    change keyDerivationInput S0 0 = keyDerivationInput S0' 0 at hi
    exact congrArg truncateHash (keyDerivationInput_injective hi).1
  | chainStart l τ e i =>
    change addressedHashInput _ _ (littleEndianBytes 32 S0) =
      addressedHashInput _ _ (littleEndianBytes 32 S0') at hi
    exact congrArg truncateHash (littleEndianBytes_injective 32 (addressedHashInput_payload_eq hi))
  | forsSecret idx κ s =>
    change addressedHashInput _ _ (littleEndianBytes 32 S0) =
      addressedHashInput _ _ (littleEndianBytes 32 S0') at hi
    exact congrArg truncateHash (littleEndianBytes_injective 32 (addressedHashInput_payload_eq hi))
  | chain l τ e i step =>
    change addressedHashInput _ _ (littleEndianBytes 16 (v.chainValue l τ e i step.val)) =
      addressedHashInput _ _ (littleEndianBytes 16 (v'.chainValue l τ e i step.val)) at hi
    exact littleEndianBytes_injective 16 (addressedHashInput_payload_eq hi)
  | leaf l τ e =>
    change addressedHashInput _ _ (digestsPayload (v.endpoints l τ e)) =
      addressedHashInput _ _ (digestsPayload (v'.endpoints l τ e)) at hi
    exact congrFun (digestsPayload_injective (addressedHashInput_payload_eq hi)) chainZero
  | node l τ level index =>
    change addressedHashInput _ _ (nodePayload (v.treeValue l τ level.val (2 * index.val))
        (v.treeValue l τ level.val (2 * index.val + 1))) =
      addressedHashInput _ _ (nodePayload (v'.treeValue l τ level.val (2 * index.val))
        (v'.treeValue l τ level.val (2 * index.val + 1))) at hi
    exact (nodePayload_injective (addressedHashInput_payload_eq hi)).1
  | forsLeaf idx κ s =>
    change addressedHashInput _ _ (littleEndianBytes 16 (v.forsSecret idx κ s)) =
      addressedHashInput _ _ (littleEndianBytes 16 (v'.forsSecret idx κ s)) at hi
    exact littleEndianBytes_injective 16 (addressedHashInput_payload_eq hi)
  | forsNode idx κ level node =>
    change addressedHashInput _ _ (nodePayload (v.forsValue idx κ level.val (2 * node.val))
        (v.forsValue idx κ level.val (2 * node.val + 1))) =
      addressedHashInput _ _ (nodePayload (v'.forsValue idx κ level.val (2 * node.val))
        (v'.forsValue idx κ level.val (2 * node.val + 1))) at hi
    exact (nodePayload_injective (addressedHashInput_payload_eq hi)).1
  | forsRoots idx =>
    change addressedHashInput _ _ (digestsPayload (v.forsRoot idx)) =
      addressedHashInput _ _ (digestsPayload (v'.forsRoot idx)) at hi
    exact congrFun (digestsPayload_injective (addressedHashInput_payload_eq hi)) forsZero
  | prfMsg m =>
    change prfMessageInput v.prfKey v.publicSeed m = prfMessageInput v'.prfKey v'.publicSeed m
      at hi
    exact congrArg truncateHash (prfMessageInput_injective hi).1
  | hmsg m =>
    change messageDigestInput (v.randomizer m) v.publicSeed v.root m 0 =
      messageDigestInput (v'.randomizer m) v'.publicSeed v'.root m 0 at hi
    exact (messageDigestInput_injective hi).1

/-- The digest of an in-range position other than a digest cell, at the table of `θ`. -/
theorem dig_tabOf (θ : TVals) {q : RawPos} (hq : q.InRange) (hn : ∀ m, q ≠ .hmsg m) :
    (tabOf θ).dig q = pairDigest (pairAt θ (.val (some ⟨q, hq⟩))) := by
  unfold QTable.dig QTable.out
  rw [dite_eq_left hq]
  cases q with
  | hmsg m => exact absurd rfl (hn m)
  | _ => rfl

/-- **The input position of a position is in range.** -/
theorem inRange_of_inPos {p : Pos} {q : RawPos} (h : inPos p.1 = some q) : q.InRange := by
  obtain ⟨p, hp⟩ := p
  rcases inPos_spec h with ⟨l, τ, e, i, s, -, rfl, rfl⟩ | ⟨l, τ, e, i, s, s', -, rfl, rfl⟩ |
    ⟨l, τ, e, rfl, rfl⟩ | ⟨l, τ, k, j, hk, rfl, rfl⟩ |
    ⟨l, τ, k, k', j, j', hk, hj, rfl, rfl⟩ | ⟨idx, κ, s, rfl, rfl⟩ |
    ⟨idx, κ, k, j, hk, rfl, rfl⟩ | ⟨idx, κ, k, k', j, j', hk, hj, rfl, rfl⟩ | ⟨idx, rfl, rfl⟩ |
    ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩
  · exact hp
  · exact hp
  · exact hp
  · obtain ⟨hτ, hkl, hjl⟩ := hp
    have hl : layerHeight l ≤ 10 := by unfold layerHeight; split <;> omega
    have h2 := two_mul_lt_pow hkl hjl
    have h2' : 2 * j.val < 2 ^ 10 := two_mul_lt_1024 hl hkl hjl
    refine ⟨hτ, ?_⟩
    simp only [leafOfNat, layerHeight_topLayer, Nat.mod_eq_of_lt h2']
    rw [hk] at h2
    simpa using h2
  · obtain ⟨hτ, hkl, hjl⟩ := hp
    refine ⟨hτ, by omega, ?_⟩
    have h2 := two_mul_lt_pow hkl hjl
    rw [show layerHeight l - k.val = layerHeight l - (k'.val + 1) by omega] at h2
    rw [hj]
    exact h2
  · trivial
  · trivial
  · change j'.val < 2 ^ (forsTreeHeight - (k'.val + 1))
    have hjl : j.val < 2 ^ (forsTreeHeight - (k.val + 1)) := hp
    have h2 := two_mul_lt_pow k.isLt hjl
    rw [show forsTreeHeight - k.val = forsTreeHeight - (k'.val + 1) by omega] at h2
    rw [hj]
    exact h2
  · change (0 : ℕ) < 2 ^ (forsTreeHeight - (forsTreeHeight - 1 + 1))
    exact Nat.two_pow_pos _
  · trivial
  · trivial

/-- The source of a position with an in-range input position. -/
theorem srcOf_of_inPos {p : Pos} {q : RawPos} (h : inPos p.1 = some q) (hq : q.InRange) :
    srcOf p = .val (some ⟨q, hq⟩) := by
  unfold srcOf
  rw [h]
  exact dite_eq_left hq

/-- `inPos` never names a digest cell. -/
theorem inPos_ne_hmsg {p : RawPos} {q : RawPos} (h : inPos p = some q) (m : Message) :
    q ≠ .hmsg m := by
  rintro rfl
  rcases inPos_spec h with ⟨_, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, hr⟩ |
    ⟨_, _, hr⟩ | ⟨_, _, hr⟩ <;> cases hr

/-- **The carried digest is the input position's digest.** -/
theorem srcDig_eq_dig (S0 : MasterSeed) (v : QTable) {p q : RawPos} (h : inPos p = some q) :
    srcDig S0 v p = v.dig q := by
  rcases inPos_spec h with ⟨l, τ, e, i, s, hs, rfl, rfl⟩ | ⟨l, τ, e, i, s, s', hs, rfl, rfl⟩ |
    ⟨l, τ, e, rfl, rfl⟩ | ⟨l, τ, k, j, hk, rfl, rfl⟩ |
    ⟨l, τ, k, k', j, j', hk, hj, rfl, rfl⟩ | ⟨idx, κ, s, rfl, rfl⟩ |
    ⟨idx, κ, k, j, hk, rfl, rfl⟩ | ⟨idx, κ, k, k', j, j', hk, hj, rfl, rfl⟩ | ⟨idx, rfl, rfl⟩ |
    ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩
  · show v.chainValue l τ e i s.val = _
    rw [hs]
    rfl
  · show v.chainValue l τ e i s.val = _
    rw [hs]
    simp only [QTable.chainValue, dite_eq_left s'.isLt]
  · rfl
  · show v.treeValue l τ k.val (2 * j.val) = _
    rw [hk]
    rfl
  · show v.treeValue l τ k.val (2 * j.val) = _
    have hlt : 2 * j.val < 2 ^ layerHeight topLayer := hj ▸ j'.isLt
    obtain rfl : j' = ⟨2 * j.val, hlt⟩ := Fin.ext hj
    rw [hk]
    simp only [QTable.treeValue, dite_eq_left (show k'.val < layerHeight topLayer ∧
      2 * j.val < 2 ^ layerHeight topLayer from ⟨k'.isLt, hlt⟩)]
  · rfl
  · show v.forsValue idx κ k.val (2 * j.val) = _
    rw [hk]
    rfl
  · show v.forsValue idx κ k.val (2 * j.val) = _
    have hlt : 2 * j.val < 2 ^ forsTreeHeight := hj ▸ j'.isLt
    obtain rfl : j' = ⟨2 * j.val, hlt⟩ := Fin.ext hj
    rw [hk]
    simp only [QTable.forsValue, dite_eq_left (show k'.val < forsTreeHeight ∧
      2 * j.val < 2 ^ forsTreeHeight from ⟨k'.isLt, hlt⟩)]
  · rfl
  · rfl
  · rfl

/-- **The carried digest at the table of `θ` is the digest of the source's pair.** -/
theorem srcDig_tabOf (θ : TVals) (p : Pos) :
    srcDig (seedOf θ) (tabOf θ) p.1 = pairDigest (pairAt θ (srcOf p)) := by
  rcases hi : inPos p.1 with _ | q
  · have hs : srcOf p = .val none := by
      unfold srcOf
      rw [hi]
    rw [hs]
    obtain ⟨r, hr⟩ := p
    cases r with
    | prfKey => rfl
    | publicSeed => rfl
    | chainStart => rfl
    | forsSecret => rfl
    | node l τ level index =>
      simp only [inPos] at hi
      split_ifs at hi with h0 h1
      have hl : layerHeight l ≤ 10 := by unfold layerHeight; split <;> omega
      exact absurd (two_mul_lt_1024 hl hr.2.1 hr.2.2) h1
    | forsNode idx κ level node =>
      simp only [inPos] at hi
      split_ifs at hi with h0 h1
      exact absurd (lt_of_lt_of_le (two_mul_lt_pow level.isLt hr)
        (Nat.pow_le_pow_right (by norm_num) (by omega))) h1
    | chain =>
      simp only [inPos] at hi
      split_ifs at hi
    | _ => simp [inPos] at hi
  · have hq := inRange_of_inPos hi
    rw [srcOf_of_inPos hi hq, srcDig_eq_dig _ _ hi, dig_tabOf θ hq (inPos_ne_hmsg hi)]

/-- **A cell fixes the digest of its source's pair.** -/
theorem pairDigest_srcOf_eq {θ θ' : TVals} {p : Pos} (h : cellQ θ p = cellQ θ' p) :
    pairDigest (pairAt θ (srcOf p)) = pairDigest (pairAt θ' (srcOf p)) := by
  rw [← srcDig_tabOf θ p, ← srcDig_tabOf θ' p]
  exact srcDig_eq_of_cellOf_eq h

end srcDig

/-! ## The sources of the hidden cells -/

section sources

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-- **The source coordinates of a cell**: the source of the position it is a cell of (classical
decidability spelled out: the `Fintype` instance of `∃ p : Pos` would be evaluated). -/
noncomputable def cellSrc (z : Qrom.HashDomain) : Finset TPos :=
  @dite _ (∃ (p : Pos) (S0 : MasterSeed) (v : QTable), cellOf S0 p v = z)
    (Classical.propDecidable _) (fun h ↦ {srcOf h.choose}) fun _ ↦ ∅

theorem srcOf_mem_cellSrc (θ : TVals) (p : Pos) : srcOf p ∈ cellSrc (cellQ θ p) := by
  have h : ∃ (p' : Pos) (S0 : MasterSeed) (v : QTable), cellOf S0 p' v = cellQ θ p :=
    ⟨p, seedOf θ, tabOf θ, rfl⟩
  unfold cellSrc
  rw [dite_eq_left h, Finset.mem_singleton]
  obtain ⟨S0, v, hv⟩ := h.choose_spec
  rw [pos_eq_of_cellOf_eq hv]

theorem card_cellSrc_le_one (z : Qrom.HashDomain) : (cellSrc z).card ≤ 1 := by
  unfold cellSrc
  split
  · exact (Finset.card_singleton _).le
  · exact (Finset.card_empty).le.trans (Nat.zero_le _)

/-- The values of the coordinate `s`, the others as in `θ`, for which `z` is the cell of a
position whose source is `s`. -/
@[irreducible] noncomputable def srcVals (z : Qrom.HashDomain) (s : TPos) (θ : TVals) :
    Finset (TVal s) :=
  @Finset.filter _ (fun d ↦ ∃ p, srcOf p = s ∧ cellQ (Function.update θ s d) p = z)
    (fun _ ↦ Classical.propDecidable _) Finset.univ

theorem mem_srcVals {z : Qrom.HashDomain} {s : TPos} {θ : TVals} {d : TVal s} :
    d ∈ srcVals z s θ ↔ ∃ p, srcOf p = s ∧ cellQ (Function.update θ s d) p = z := by
  unfold srcVals
  exact (@Finset.mem_filter _ _ (fun _ ↦ Classical.propDecidable _) _ _).trans
    (and_iff_right (Finset.mem_univ _))

theorem srcVals_update (z : Qrom.HashDomain) (s : TPos) (θ : TVals) (d : TVal s) :
    srcVals z s (Function.update θ s d) = srcVals z s θ := by
  ext d'
  rw [mem_srcVals, mem_srcVals, Function.update_idem]

theorem self_mem_srcVals (θ : TVals) (p : Pos) :
    θ (srcOf p) ∈ srcVals (cellQ θ p) (srcOf p) θ :=
  mem_srcVals.2 ⟨p, rfl, by rw [Function.update_eq_self]⟩

/-- Two values of a source share their digest. -/
theorem pairDigest_eq_of_mem_srcVals {z : Qrom.HashDomain} {o : Option Pos} {θ : TVals}
    {d d' : TVal (.val o)} (hd : d ∈ srcVals z (.val o) θ) (hd' : d' ∈ srcVals z (.val o) θ) :
    pairDigest d = pairDigest d' := by
  obtain ⟨p, hs, hz⟩ := mem_srcVals.1 hd
  obtain ⟨p', -, hz'⟩ := mem_srcVals.1 hd'
  obtain rfl : p = p' := pos_eq_of_cellOf_eq (hz.trans hz'.symm)
  have h := pairDigest_srcOf_eq (hz.trans hz'.symm)
  rw [hs] at h
  simpa only [pairAt, Function.update_self] using h

/-- A set of pairs sharing one digest has at most `2^128 · 2^256` elements. -/
theorem card_le_of_pairDigest {F : Finset (HashOutput × HashOutput)}
    (h : ∀ d ∈ F, ∀ d' ∈ F, pairDigest d = pairDigest d') : F.card ≤ 2 ^ 128 * 2 ^ 256 := by
  rcases F.eq_empty_or_nonempty with he | ⟨d₀, hd₀⟩
  · rw [he, Finset.card_empty]
    exact Nat.zero_le _
  exact le_trans (Finset.card_le_card fun d hd ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _,
    h d hd d₀ hd₀⟩) (card_fiber_pairDigest_le (pairDigest d₀))

/-- **At most `2^128 · 2^256` values of a source**: they share one digest. -/
theorem card_srcVals_val_le (z : Qrom.HashDomain) (o : Option Pos) (θ : TVals) :
    (srcVals z (.val o) θ).card ≤ 2 ^ 128 * 2 ^ 256 :=
  card_le_of_pairDigest fun _ hd _ hd' ↦ pairDigest_eq_of_mem_srcVals hd hd'

theorem srcVals_eq_empty (z : Qrom.HashDomain) {s : TPos} (hs : ∀ o, s ≠ .val o) (θ : TVals) :
    srcVals z s θ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun d hd ↦ ?_
  obtain ⟨p, hp, -⟩ := mem_srcVals.1 hd
  obtain ⟨o, ho⟩ := srcOf_isVal p
  exact hs o (hp ▸ ho)

/-- **The mass per call**: one digest of a source per hidden cell. -/
noncomputable def kappaQ : ℝ≥0∞ :=
  (2 ^ 128 : ℝ≥0∞)⁻¹

theorem srcVals_frac_le (z : Qrom.HashDomain) (s : TPos) (θ : TVals) :
    ((srcVals z s θ).card : ℝ≥0∞) * (Fintype.card (TVal s) : ℝ≥0∞)⁻¹ ≤ kappaQ := by
  cases s with
  | val o =>
    have hc : Fintype.card (TVal (.val o)) = Fintype.card (HashOutput × HashOutput) :=
      Fintype.card_congr (Equiv.refl _)
    rw [hc, ← div_eq_mul_inv, kappaQ, ← pairFiber_div_card]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr (card_srcVals_val_le z o θ)) _
  | dig m =>
    rw [srcVals_eq_empty z (fun _ h ↦ by cases h) θ, Finset.card_empty, Nat.cast_zero,
      zero_mul]
    exact zero_le
  | str j =>
    rw [srcVals_eq_empty z (fun _ h ↦ by cases h) θ, Finset.card_empty, Nat.cast_zero,
      zero_mul]
    exact zero_le
  | asg m j =>
    rw [srcVals_eq_empty z (fun _ h ↦ by cases h) θ, Finset.card_empty, Nat.cast_zero,
      zero_mul]
    exact zero_le

theorem sum_cellSrc_le (z : Qrom.HashDomain) (θ : TVals) :
    ∑ s ∈ cellSrc z, ((srcVals z s θ).card : ℝ≥0∞) * (Fintype.card (TVal s) : ℝ≥0∞)⁻¹ ≤
      kappaQ := by
  refine (Finset.sum_le_card_nsmul _ _ kappaQ fun s _ ↦ srcVals_frac_le z s θ).trans ?_
  rw [nsmul_eq_mul]
  calc ((cellSrc z).card : ℝ≥0∞) * kappaQ ≤ 1 * kappaQ := by
        gcongr
        exact_mod_cast card_cellSrc_le_one z
    _ = kappaQ := one_mul _

theorem hh_sourcesQ (θ : TVals) (z : Qrom.HashDomain)
    (r : HwReg PairOut Qrom.HashDomain (Finset TPos × SelMem)) (hinv : SrcInv SelMem θ r)
    (hz : z ∈ hidCells θ) (hnone : r.2.1.1 z = none) :
    ∃ s ∈ cellSrc z, s ∉ r.2.2.1 ∧ θ s ∈ srcVals z s θ := by
  obtain ⟨p, rfl⟩ := hz
  exact ⟨srcOf p, srcOf_mem_cellSrc θ p, fun hp ↦ hinv p hp hnone, self_mem_srcVals θ p⟩

/-- **The sources of the hidden cells** on the states of the source invariant. -/
noncomputable def sourcesQ :
    Sources PairOut Qrom.HashDomain TPos SelMem TPos TVal (fun r ↦ r.2.2.1)
      (fun θ ↦ SrcInv SelMem θ) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ where
  sh z _ := cellSrc z
  sk _ _ := ∅
  sk' _ _ := ∅
  Fh z _ s θ := srcVals z s θ
  Fk _ _ _ _ := ∅
  Fk' _ _ _ _ := ∅
  hFh z _ s θ d := srcVals_update z s θ d
  hFk _ _ _ _ _ := rfl
  hFk' _ _ _ _ _ := rfl
  hh θ z r hinv hz hnone := hh_sourcesQ θ z r hinv hz hnone
  hk _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hk' _ _ _ _ hy := absurd hy (Set.notMem_empty _)
  hκh z _ θ := sum_cellSrc_le z θ
  hκk _ _ _ := by rw [Finset.sum_empty]; exact zero_le
  hκk' _ _ _ := by rw [Finset.sum_empty]; exact zero_le

end sources

/-! ## The masses of the game -/

section masses

/-- The canonical initial memory: nothing revealed, no selection recorded. -/
def m0H : Finset TPos × SelMem :=
  (∅, fun _ ↦ none)

/-- The initial state of the game and the register. -/
noncomputable def initH :
    Matrix (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × SelMem)))
      (QReg.of Unit × QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × SelMem))) ℂ :=
  (SubState.basis ()).matrix ⊗ₖ (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0H).init.matrix

theorem initH_posSemidef : initH.PosSemidef :=
  ((SubState.basis ()).prod (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0H).init).posSemidef

theorem ofReal_trace_initH_le_one : ENNReal.ofReal initH.trace.re ≤ 1 :=
  ENNReal.ofReal_le_one.mpr
    ((SubState.basis ()).prod
      (runtimeR (X := PairOut) (Z := Qrom.HashDomain) m0H).init).trace_re_le_one

/-- The read ports of runtime 2 with record ports. -/
def readPortQ : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → Bool
  | .inl (.inl (.inr _)) => true
  | _ => false

theorem hinvQ (pol : DigestPolicy) (hpol : pol.NoVal)
    (Q : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → Prop)
    (hQ : ∀ c, ¬Q (.inl (.inr c))) (hQ' : ∀ T, ¬Q (.inr T)) (A : SAdversary) (θ : TVals) :
    (runtimeR m0H).ForallQueries LocalSig.Interp.instruments
      (Quantum.Xmss.Assembly.invSupp (runtimeR m0H) Q (SrcInv SelMem θ)) (gameQ pol A θ) initH :=
  forallQueries_gameT cwUpd hpol hQ hQ' m0H A θ initH (querySupportedOn_init m0H rfl _)

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) signatureLimit)
include hhash hsign

/-- **The masses at the calls of `F`**: at most `q · 2^-128`, averaged over the hidden values. -/
theorem uavg_spongeMass_le :
    uavg (fun θ : TVals ↦ (runtimeR m0H).totalWeight .instruments
      (spongeMass (hidCells θ) ∅ ∅) (gameQ msgPol A θ) initH) ≤ q * kappaQ := by
  have hc : (fun i ↦ if (extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
      (recSpec TPos SelMem) i = false) then 1 else 0) =
      fun i ↦ if extCls PairOut Qrom.HashDomain (Finset TPos × SelMem) (recSpec TPos SelMem) i
        then 0 else 1 := by
    funext i
    rcases Bool.eq_false_or_eq_true (extCls PairOut Qrom.HashDomain (Finset TPos × SelMem)
      (recSpec TPos SelMem) i) with h | h <;> simp [h]
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments
    (fun i ↦ extCls PairOut Qrom.HashDomain (Finset TPos × SelMem) (recSpec TPos SelMem) i = false)
    m0H (fun r ↦ r.2.2.1) (fun θ ↦ gameQ msgPol A θ) (fun _ ↦ initH)
    (fun _ ↦ initH_posSemidef) (fun j ↦ viewByOn_gameT SelMem cwUpd msgPol A m0H initH j)
    (fun θ ↦ SrcInv SelMem θ)
    (fun θ ↦ hinvQ msgPol noVal_msgPol _ (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) A θ) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ by rw [hc]; exact advCalls_gameQ msgPol A hhash hsign θ)).trans ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one q

omit hhash hsign in
/-- The read mass is the hidden mass at the read ports. -/
theorem readMass_le_readPortQ (θ : TVals)
    (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port)
    (σ : Matrix ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
      QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × SelMem)))
      ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).In i ×
      QReg.of (HwReg PairOut Qrom.HashDomain (Finset TPos × SelMem))) ℂ) :
    readMass (hidCells θ) ∅ ∅ i σ ≤
      portMass (fun i ↦ readPortQ i = true) (hidCells θ) ∅ ∅ i σ := by
  rcases i with (((_ | _ | _) | (⟨z, u⟩ | ⟨y, u⟩ | ⟨y, u⟩)) | c) | T
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight,
      hiddenMass]
  · simp [readMass, portMass, Quantum.Xmss.Assembly.extWeight, Quantum.Xmss.Assembly.sumWeight]

/-- **At most `clsCapQ` reads** in the realized game. -/
theorem readCalls_gameQ (pol : DigestPolicy) (θ : TVals) :
    IFreeM.IsChargeBound (gameQ pol A θ)
      (portCharge fun i ↦ if readPortQ i = true then 1 else 0) clsCapQ := by
  refine isChargeBound_mono_charge (fun s a ↦ ?_) (readRec_gameT cwUpd pol A hhash hsign θ)
  rcases a with o | ⟨i, E, ℓ⟩
  · exact le_rfl
  · show (if readPortQ i = true then 1 else 0) ≤ (if readRecPortQ SelMem i = true then 1 else 0)
    rcases i with ((i | c) | c) | T <;> simp [readPortQ, readRecPortQ]

/-- **The read masses**: at most `clsCapQ · 2^-128`, averaged over the hidden values. -/
theorem uavg_readMass_le :
    uavg (fun θ : TVals ↦ (runtimeR m0H).totalWeight .instruments
      (readMass (hidCells θ) ∅ ∅) (gameQ msgPol A θ) initH) ≤ clsCapQ * kappaQ := by
  refine (uavg_mono fun θ ↦ totalWeight_le_totalWeight (runtimeR m0H) .instruments
    (fun i σ _ ↦ readMass_le_readPortQ θ i σ) (gameQ msgPol A θ) initH_posSemidef).trans ?_
  refine Quantum.Qrom.Xmss.uavg_le_of_sum_le _ _ ((sum_totalWeight_portMass_runtimeR_le_inv
    .instruments (fun i ↦ readPortQ i = true) m0H (fun r ↦ r.2.2.1) (fun θ ↦ gameQ msgPol A θ)
    (fun _ ↦ initH) (fun _ ↦ initH_posSemidef)
    (fun j ↦ viewByOn_gameT SelMem cwUpd msgPol A m0H initH j) (fun θ ↦ SrcInv SelMem θ)
    (fun θ ↦ hinvQ msgPol noVal_msgPol _ (fun _ h ↦ Bool.noConfusion h)
      (fun _ h ↦ Bool.noConfusion h) A θ) hidCells (fun _ ↦ ∅) (fun _ ↦ ∅) kappaQ sourcesQ
    (fun θ ↦ readCalls_gameQ A hhash hsign msgPol θ)).trans ?_)
  exact Quantum.Qrom.Xmss.sum_mul_trace_le kappaQ _ ofReal_trace_initH_le_one clsCapQ

end masses

/-! ## The hybrid -/

section hybrid

/-- The win observable of the game's leaves. -/
def winObsQ : (Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) → Bool :=
  fun p ↦ p.2.2

/-- **Runtime 1's win at the hidden values `θ`**: the table's cells hardwired from the start. -/
noncomputable def p1Q (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  (runtime1R PairOut Qrom.HashDomain (hwT θ) m0H).evalDistMap .instruments (gameQ msgPol A θ)
    (SubState.basis ()) winObsQ {true}

/-- **Runtime 2's win at the digest policy `pol` and the hidden values `θ`** (the quantity the
end slice bounds at `strPol`, averaged over `θ`). -/
noncomputable def p2Q (pol : DigestPolicy) (A : SAdversary) (θ : TVals) : ℝ≥0∞ :=
  (runtimeR m0H).evalDistMap .instruments (gameQ pol A θ) (SubState.basis ()) winObsQ {true}

/-- **The QROM game is runtime 1 on the realized template, averaged over the hidden values.** -/
theorem winProb_eq_uavg_p1Q (A : SAdversary) : SufCma.winProb sphincsRom A = uavg (p1Q A) :=
  winProb_eq_uavg_runtime1R cwUpd m0H A

/-- **The stream reindexing**: runtime 2's averaged win at `msgPol` is that at `strPol`. -/
theorem uavg_p2Q_msgPol_eq (A : SAdversary) : uavg (p2Q msgPol A) = uavg (p2Q strPol A) :=
  uavg_gameT_msgPol_eq_strPol cwUpd A (fun _ ↦ none) (SubState.basis ()) winObsQ
    (measurableSet_singleton true)

/-- **The hybrid term**: `√(4 q · q κ) + √(clsCapQ · κ)` (`= 2q·2^-64 + √(clsCapQ·2^-128)`). -/
noncomputable def hybTermQ (q : ℕ) : ℝ≥0∞ :=
  (4 * (q * (q * kappaQ))) ^ (2⁻¹ : ℝ) + (clsCapQ * kappaQ) ^ (2⁻¹ : ℝ)

variable (A : SAdversary) {q : ℕ}
  (hhash : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.hashCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (SufCma.cmdCharge SufCma.signCharge) signatureLimit)
include hhash hsign

/-- **The graded hybrid, averaged**: runtime 1 against runtime 2 at `msgPol`. -/
theorem uavg_p1Q_le :
    uavg (p1Q A) ≤ (uavg (p2Q msgPol A) ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 := by
  have h := uavg_win_runtime1R_le_graded_total .instruments hwT hidCells (fun _ ↦ ∅)
    (fun _ ↦ ∅) covers_hwT m0H (fun θ ↦ gameQ msgPol A θ) (fun _ ↦ SubState.basis ())
    (fun _ ↦ winObsQ) (measurableSet_singleton true) q
    (fun θ ↦ advCalls_gameQ msgPol A hhash hsign θ) (q * kappaQ) (clsCapQ * kappaQ)
    (uavg_spongeMass_le A hhash hsign) (uavg_readMass_le A hhash hsign)
  rw [add_assoc] at h
  exact h

/-- **The hybrid, squared**: `winProb ≤ (√(E p2Q strPol) + hybTermQ q)²`. -/
theorem winProb_le_hybrid_qrom :
    SufCma.winProb sphincsRom A ≤ (uavg (p2Q strPol A) ^ (2⁻¹ : ℝ) + hybTermQ q) ^ 2 := by
  rw [← uavg_p2Q_msgPol_eq]
  exact (winProb_eq_uavg_p1Q A).trans_le (uavg_p1Q_le A hhash hsign)

/-- **The hidden-value hybrid of leanSPHINCS in the QROM**: `√winProb ≤ √(E_θ p2Q strPol) +
2q·2^-64 + √(clsCapQ · 2^-128)`. -/
theorem sqrt_win_runtime1_le_qrom :
    SufCma.winProb sphincsRom A ^ (2⁻¹ : ℝ) ≤ uavg (p2Q strPol A) ^ (2⁻¹ : ℝ) + hybTermQ q :=
  (ENNReal.rpow_le_rpow (winProb_le_hybrid_qrom A hhash hsign) (by norm_num)).trans_eq
    (Quantum.Qrom.Xmss.sq_rpow_inv_two_eq _)

end hybrid

end Quantum.Qrom.Sphincs

end
