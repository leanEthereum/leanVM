module

public import Quantum.Qrom.Sphincs.Costs.Ports
public import Quantum.Qrom.Sphincs.GameTFacts
public import Quantum.Xmss.Assembly.CwReFail

@[expose] public section

/-!
# The counter searches of leanSPHINCS's challenge prefix, as moded programs

The modes of the counter searches of runtime 2: between searches (`rest`), or in the search of the
key `K` on the value `m`, before trial `j` (`grd`); both carry the keys whose search was started.
A reveal of the single coordinate `vcoord (msgPos K)` of a key of the signatures starts its search
from the revealed value; a trial read whose digest is a codeword ends it, otherwise the next trial
follows; the other calls (sponge calls, programs off the encoding slots, reveals without a key's
coordinate outside the started keys) happen only between searches.

* **The keys of the signatures** (`InRangeU`, `keyOfTU`): the coordinate a key signs names the key
  (`vcoord_msgPos_injU`), its value is the digest of the pair there (`valuePos_msgPosU`), and the
  publications reveal only coordinates of the keys just searched (`key_of_mem_forsRevealU`,
  `key_of_mem_layerRevealU`).
* `ModeU`, `ModeU.Rest`, the allowed calls and the next mode on runtime 1's ports (`srchOkR`,
  `srchNxR`), the template's (`srchOkT`, `srchNxT`) and runtime 2's (`srchOkZ`, `srchNxZ`).
* **`modedP_prefixQ`**: the realized challenge prefix `prefixQ pol A θ` is moded from `rest ∅`,
  its searches' trials under `PK.seed`, ending between searches.
-/

open Matrix IPFunctor
open scoped ENNReal
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

universe u v w

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key keyOf msgPos indexBelow layerBelow tpos treeBits)
open Quantum.Xmss.Hybrid (restrictTo LazyProg)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR realizeT revealThen progThen readLift
  readLiftQ RevealVals liftRead tmplLens readLens ModedP modedP_bind modedP₂_bind modedP_map
  modeCmdOk modeCmdNx realizeT_bind realizeT_bind₂ realizeT_substitute)

attribute [local irreducible] sphincsRom Fin.fintype

/-! ## The keys of the signatures and the values they sign -/

section keys

/-- **A key of the signatures**: `K_l(idx)` for some index. -/
def InRangeU (K : Key) : Prop :=
  ∃ (l : Layer) (idx : Index), keyOf l idx = K

theorem layer_casesU (l : Layer) : l = 0 ∨ l = 1 ∨ l = 2 := by
  obtain ⟨v, hv⟩ := l
  have hv' : v < 3 := hv
  rcases v with _ | _ | _ | v
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · omega

theorem msgPos_keyOf_zeroU (idx : Index) : msgPos (keyOf 0 idx) = .forsKey idx := by
  have hi : idx.val < 67108864 := idx.isLt
  change Quantum.Sphincs.ValPos.forsKey (indexBelow 0 (treeOfIndex 0 idx) (leafOfIndex 0 idx)) =
    .forsKey idx
  refine congrArg Quantum.Sphincs.ValPos.forsKey (Fin.ext ?_)
  change ((treeOfIndex 0 idx).val * 2 ^ 8 + (leafOfIndex 0 idx).val) % 2 ^ 26 = idx.val
  rw [Quantum.Sphincs.treeOfIndex_zero, Quantum.Sphincs.leafOfIndex_zero]
  change (idx.val / 256 * 256 + idx.val % 256) % 67108864 = idx.val
  omega

theorem msgPos_keyOf_oneU (idx : Index) :
    msgPos (keyOf 1 idx) =
      tpos 0 ⟨idx.val / 256, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩ 8 0 := by
  have hi : idx.val < 67108864 := idx.isLt
  change tpos 0 (indexBelow 1 (treeOfIndex 1 idx) (leafOfIndex 1 idx)) 8 0 = _
  refine congrArg (fun τ ↦ tpos 0 τ 8 0) (Fin.ext ?_)
  change (idx.val / 65536 * 256 + idx.val / 256 % 256) % 67108864 = idx.val / 256
  omega

theorem msgPos_keyOf_twoU (idx : Index) :
    msgPos (keyOf 2 idx) =
      tpos 1 ⟨idx.val / 65536, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩ 8 0 := by
  have hi : idx.val < 67108864 := idx.isLt
  change tpos 1 (indexBelow 2 (treeOfIndex 2 idx) (leafOfIndex 2 idx)) 8 0 = _
  refine congrArg (fun τ ↦ tpos 1 τ 8 0) (Fin.ext ?_)
  change (idx.val / 67108864 * 1024 + idx.val / 65536 % 1024) % 67108864 = idx.val / 65536
  omega

theorem keyOf_one_eqU {i i' : Index} (h : i.val / 256 = i'.val / 256) :
    keyOf 1 i = keyOf 1 i' := by
  refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · change i.val / 65536 = i'.val / 65536
    omega
  · change i.val / 256 % 256 = i'.val / 256 % 256
    rw [h]

theorem keyOf_two_eqU {i i' : Index} (h : i.val / 65536 = i'.val / 65536) :
    keyOf 2 i = keyOf 2 i' := by
  have hi : i.val < 67108864 := i.isLt
  have hi' : i'.val < 67108864 := i'.isLt
  refine Prod.ext rfl (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · change i.val / 67108864 = i'.val / 67108864
    omega
  · change i.val / 65536 % 1024 = i'.val / 65536 % 1024
    rw [h]

theorem treeOfIndex_oneU (idx : Index) : (treeOfIndex 1 idx).val = idx.val / 65536 :=
  rfl

/-- The raw position of a coordinate of the table. -/
def rawOfU : TPos → Option RawPos
  | .val (some p) => some p.1
  | _ => none

/-- A raw position in range and no digest cell has its own coordinate. -/
theorem rawC_of_inRangeU {q : RawPos} (hq : q.InRange) (hm : ∀ m, q ≠ .hmsg m) :
    rawC q = .val (some ⟨q, hq⟩) := by
  unfold rawC
  rw [dite_eq_left hq]
  unfold coordOf
  cases q with
  | hmsg m => exact absurd rfl (hm m)
  | _ => rfl

/-- **The coordinate of a hash call** is its own, `PK.seed`'s, or a digest coordinate. -/
theorem rawOfU_rawC (q : RawPos) :
    rawOfU (rawC q) = some q ∨ rawOfU (rawC q) = some .publicSeed ∨ rawOfU (rawC q) = none := by
  unfold rawC
  split_ifs with hq
  · unfold coordOf
    cases q with
    | hmsg m => exact .inr (.inr rfl)
    | _ => exact .inl rfl
  · exact .inr (.inl rfl)

theorem dig_tabOfU (θ : TVals) {r : RawPos} (hr : r.InRange) :
    (tabOf θ).dig r = pairDigest (pairAt θ (rawC r)) := by
  unfold QTable.dig QTable.out rawC
  rw [dite_eq_left hr, dite_eq_left hr]
  rfl

theorem node_inRangeU (l : Layer) (τ : TreeIndex) (hτ : τ.val < 2 ^ treeBits l)
    (hl : layerHeight l = 8) :
    (RawPos.node l τ ⟨7, by rw [layerHeight_topLayer]; norm_num⟩
      ⟨0, Nat.two_pow_pos _⟩).InRange :=
  ⟨hτ, by rw [hl]; norm_num, by rw [hl]; norm_num⟩

theorem vcoord_tpos_eightU (l : Layer) (τ : TreeIndex) :
    vcoord (tpos l τ 8 0) =
      rawC (.node l τ ⟨7, by rw [layerHeight_topLayer]; norm_num⟩ ⟨0, Nat.two_pow_pos _⟩) := by
  rfl

theorem valuePos_tpos_eightU (θ : TVals) (l : Layer) (τ : TreeIndex)
    (hr : (RawPos.node l τ ⟨7, by rw [layerHeight_topLayer]; norm_num⟩
      ⟨0, Nat.two_pow_pos _⟩).InRange) :
    (tabOf θ).valuePos (tpos l τ 8 0) = pairDigest (pairAt θ (vcoord (tpos l τ 8 0))) := by
  rw [vcoord_tpos_eightU, ← dig_tabOfU θ hr,
    QTable.valuePos_tpos _ l τ (by rw [layerHeight_topLayer]; norm_num) (Nat.two_pow_pos _)]
  show (if h : 7 < layerHeight topLayer ∧ 0 < 2 ^ layerHeight topLayer then
    (tabOf θ).dig (.node l τ ⟨7, h.1⟩ ⟨0, h.2⟩) else 0) = _
  rw [dite_eq_left ⟨by rw [layerHeight_topLayer]; norm_num, Nat.two_pow_pos _⟩]

theorem tree_one_ltU (idx : Index) :
    (⟨idx.val / 256, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩ : TreeIndex).val <
      2 ^ treeBits 0 := by
  have h := treeOfIndex_lt 0 idx
  rwa [Quantum.Sphincs.treeOfIndex_zero] at h

theorem tree_two_ltU (idx : Index) :
    (⟨idx.val / 65536, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩ : TreeIndex).val <
      2 ^ treeBits 1 := by
  have h := treeOfIndex_lt 1 idx
  rwa [treeOfIndex_oneU] at h

theorem layerHeight_zeroU : layerHeight (0 : Layer) = 8 :=
  rfl

theorem layerHeight_oneU : layerHeight (1 : Layer) = 8 :=
  rfl

/-- **The value a key of the signatures signs** is the digest of the pair at its coordinate. -/
theorem valuePos_msgPosU {K : Key} (hK : InRangeU K) (θ : TVals) :
    (tabOf θ).valuePos (msgPos K) = pairDigest (pairAt θ (vcoord (msgPos K))) := by
  obtain ⟨l, idx, rfl⟩ := hK
  rcases layer_casesU l with rfl | rfl | rfl
  · rw [msgPos_keyOf_zeroU]
    exact dig_tabOfU θ (r := .forsRoots idx) trivial
  · rw [msgPos_keyOf_oneU]
    exact valuePos_tpos_eightU θ 0 _ (node_inRangeU 0 _ (tree_one_ltU idx) layerHeight_zeroU)
  · rw [msgPos_keyOf_twoU]
    exact valuePos_tpos_eightU θ 1 _ (node_inRangeU 1 _ (tree_two_ltU idx) layerHeight_oneU)

theorem rawOf_msgPos_zeroU (idx : Index) :
    rawOfU (vcoord (msgPos (keyOf 0 idx))) = some (.forsRoots idx) := by
  rw [msgPos_keyOf_zeroU]
  show rawOfU (rawC (.forsRoots idx)) = _
  rw [rawC_of_inRangeU (q := .forsRoots idx) trivial (fun _ h ↦ by cases h)]
  rfl

theorem rawOf_msgPos_oneU (idx : Index) :
    rawOfU (vcoord (msgPos (keyOf 1 idx))) = some (.node 0
      ⟨idx.val / 256, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩
      ⟨7, by rw [layerHeight_topLayer]; norm_num⟩ ⟨0, Nat.two_pow_pos _⟩) := by
  rw [msgPos_keyOf_oneU, vcoord_tpos_eightU,
    rawC_of_inRangeU (node_inRangeU 0 _ (tree_one_ltU idx) layerHeight_zeroU)
      (fun _ h ↦ by cases h)]
  rfl

theorem rawOf_msgPos_twoU (idx : Index) :
    rawOfU (vcoord (msgPos (keyOf 2 idx))) = some (.node 1
      ⟨idx.val / 65536, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) idx.isLt⟩
      ⟨7, by rw [layerHeight_topLayer]; norm_num⟩ ⟨0, Nat.two_pow_pos _⟩) := by
  rw [msgPos_keyOf_twoU, vcoord_tpos_eightU,
    rawC_of_inRangeU (node_inRangeU 1 _ (tree_two_ltU idx) layerHeight_oneU)
      (fun _ h ↦ by cases h)]
  rfl

/-- The coordinate a key of the signatures signs is a table coordinate. -/
theorem rawOf_msgPos_isSomeU {K : Key} (hK : InRangeU K) :
    ∃ r, rawOfU (vcoord (msgPos K)) = some r ∧
      ((∃ idx, r = .forsRoots idx) ∨ ∃ l τ k j, r = .node l τ k j ∧ (l = 0 ∨ l = 1)) := by
  obtain ⟨l, idx, rfl⟩ := hK
  rcases layer_casesU l with rfl | rfl | rfl
  · exact ⟨_, rawOf_msgPos_zeroU idx, .inl ⟨idx, rfl⟩⟩
  · exact ⟨_, rawOf_msgPos_oneU idx, .inr ⟨0, _, _, _, rfl, .inl rfl⟩⟩
  · exact ⟨_, rawOf_msgPos_twoU idx, .inr ⟨1, _, _, _, rfl, .inr rfl⟩⟩

/-- **The coordinate a key of the signatures signs is a value coordinate.** -/
theorem msgPos_isValU {K : Key} (hK : InRangeU K) : ∃ q, vcoord (msgPos K) = .val q := by
  obtain ⟨r, hr, -⟩ := rawOf_msgPos_isSomeU hK
  generalize vcoord (msgPos K) = s at hr
  cases s with
  | val q => exact ⟨q, rfl⟩
  | _ => cases hr

/-- **The coordinate a key of the signatures signs names the key.** -/
theorem vcoord_msgPos_injU {K K' : Key} (hK : InRangeU K) (hK' : InRangeU K')
    (h : vcoord (msgPos K) = vcoord (msgPos K')) : K = K' := by
  obtain ⟨l, i, rfl⟩ := hK
  obtain ⟨l', i', rfl⟩ := hK'
  have hr := congrArg rawOfU h
  rcases layer_casesU l with rfl | rfl | rfl <;> rcases layer_casesU l' with rfl | rfl | rfl
  · rw [rawOf_msgPos_zeroU, rawOf_msgPos_zeroU] at hr
    cases Option.some.inj hr
    rfl
  · rw [rawOf_msgPos_zeroU, rawOf_msgPos_oneU] at hr
    cases Option.some.inj hr
  · rw [rawOf_msgPos_zeroU, rawOf_msgPos_twoU] at hr
    cases Option.some.inj hr
  · rw [rawOf_msgPos_oneU, rawOf_msgPos_zeroU] at hr
    cases Option.some.inj hr
  · rw [rawOf_msgPos_oneU, rawOf_msgPos_oneU] at hr
    injection Option.some.inj hr with h1 h2
    exact keyOf_one_eqU (congrArg Fin.val h2)
  · rw [rawOf_msgPos_oneU, rawOf_msgPos_twoU] at hr
    injection Option.some.inj hr with h1
    exact absurd h1 (by decide)
  · rw [rawOf_msgPos_twoU, rawOf_msgPos_zeroU] at hr
    cases Option.some.inj hr
  · rw [rawOf_msgPos_twoU, rawOf_msgPos_oneU] at hr
    injection Option.some.inj hr with h1
    exact absurd h1 (by decide)
  · rw [rawOf_msgPos_twoU, rawOf_msgPos_twoU] at hr
    injection Option.some.inj hr with h1 h2
    exact keyOf_two_eqU (congrArg Fin.val h2)

/-- A coordinate that is no key's signed coordinate. -/
def NotMcU (s : TPos) : Prop :=
  ∀ K, InRangeU K → s ≠ vcoord (msgPos K)

/-- The raw positions holding no key's signed value. -/
def NoMsgRawU : RawPos → Prop
  | .forsRoots _ => False
  | .node l _ _ _ => l ≠ 0 ∧ l ≠ 1
  | _ => True

theorem notMcU_of_rawOf {s : TPos} (hs : ∀ r, rawOfU s = some r → NoMsgRawU r) : NotMcU s := by
  intro K hK he
  obtain ⟨r, hr, hc⟩ := rawOf_msgPos_isSomeU hK
  rw [← he] at hr
  have h := hs r hr
  rcases hc with ⟨idx, rfl⟩ | ⟨l, τ, k, j, rfl, hl⟩
  · exact h
  · rcases hl with rfl | rfl
    · exact h.1 rfl
    · exact h.2 rfl

theorem notMcU_rawC {q : RawPos} (hq : NoMsgRawU q) : NotMcU (rawC q) := by
  refine notMcU_of_rawOf fun r hr ↦ ?_
  rcases rawOfU_rawC q with h | h | h <;> rw [h] at hr
  · rw [← Option.some.inj hr]
    exact hq
  · rw [← Option.some.inj hr]
    trivial
  · cases hr

theorem notMcU_seedC : NotMcU seedC :=
  notMcU_rawC (q := .publicSeed) trivial

theorem notMcU_rndC (msg : Message) : NotMcU (rndC msg) :=
  notMcU_rawC (q := .prfMsg msg) trivial

theorem notMcU_rootC : NotMcU rootC := by
  show NotMcU (if h : 9 < layerHeight topLayer ∧ 0 < 2 ^ layerHeight topLayer then
    rawC (.node topLayer 0 ⟨9, h.1⟩ ⟨0, h.2⟩) else seedC)
  split_ifs
  · exact notMcU_rawC ⟨by decide, by decide⟩
  · exact notMcU_seedC

theorem notMcU_chainC (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) :
    ∀ j, NotMcU (chainC l τ e i j)
  | 0 => notMcU_rawC (q := .chainStart l τ e i) trivial
  | j + 1 => by
    show NotMcU (if h : j < chainLength - 1 then rawC (.chain l τ e i ⟨j, h⟩) else seedC)
    split_ifs
    · exact notMcU_rawC trivial
    · exact notMcU_seedC

theorem notMcU_of_noVal {pol : DigestPolicy} (hpol : pol.NoVal) {L : Finset TPos}
    {msg : Message} {s : TPos} (hs : s ∈ pol.need L msg) : NotMcU s := by
  intro K hK he
  obtain ⟨q, hq⟩ := msgPos_isValU hK
  exact hpol L msg q (hq ▸ he ▸ hs)

/-! ### The coordinates a publication reveals -/

/-- Every raw position the coordinate `s` holds satisfies `P`. -/
def RawInU (P : RawPos → Prop) (s : TPos) : Prop :=
  ∀ r, rawOfU s = some r → P r

theorem rawInU_rawC {P : RawPos → Prop} {q : RawPos} (hq : P q) (hs : P .publicSeed) :
    RawInU P (rawC q) := by
  intro r hr
  rcases rawOfU_rawC q with h | h | h <;> rw [h] at hr
  · exact Option.some.inj hr ▸ hq
  · exact Option.some.inj hr ▸ hs
  · cases hr

theorem rawInU_coordOf {P : RawPos → Prop} {p : Pos} (hp : P p.1) : RawInU P (coordOf p) := by
  intro r hr
  obtain ⟨q, hq⟩ := p
  revert hr
  unfold coordOf
  cases q with
  | hmsg m => exact fun h ↦ by cases h
  | _ => exact fun h ↦ Option.some.inj h ▸ hp

/-- The raw positions of the tree `τ` of layer `l`, and `PK.seed`. -/
def LRawU (l : Layer) (τ : TreeIndex) : RawPos → Prop
  | .publicSeed => True
  | .chainStart l' τ' _ _ => l' = l ∧ τ' = τ
  | .chain l' τ' _ _ _ => l' = l ∧ τ' = τ
  | .leaf l' τ' _ => l' = l ∧ τ' = τ
  | .node l' τ' _ _ => l' = l ∧ τ' = τ
  | _ => False

/-- The raw positions of FORS instance `idx`, and `PK.seed`. -/
def FRawU (idx : Index) : RawPos → Prop
  | .publicSeed => True
  | .forsSecret i _ _ => i = idx
  | .forsLeaf i _ _ => i = idx
  | .forsNode i _ _ _ => i = idx
  | .forsRoots i => i = idx
  | _ => False

theorem rawInU_chainC (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) (i : ChainIndex) :
    ∀ j, RawInU (LRawU l τ) (chainC l τ e i j)
  | 0 => rawInU_rawC (q := .chainStart l τ e i) ⟨rfl, rfl⟩ trivial
  | j + 1 => by
    show RawInU _ (if h : j < chainLength - 1 then rawC (.chain l τ e i ⟨j, h⟩) else seedC)
    split_ifs
    · exact rawInU_rawC ⟨rfl, rfl⟩ trivial
    · exact rawInU_rawC (q := .publicSeed) trivial trivial

theorem rawInU_treeC (l : Layer) (τ : TreeIndex) : ∀ lev a, RawInU (LRawU l τ) (treeC l τ lev a)
  | 0, a => rawInU_rawC (q := .leaf l τ (leafOfNat a)) ⟨rfl, rfl⟩ trivial
  | lev + 1, a => by
    show RawInU _ (if h : lev < layerHeight topLayer ∧ a < 2 ^ layerHeight topLayer then
      rawC (.node l τ ⟨lev, h.1⟩ ⟨a, h.2⟩) else seedC)
    split_ifs
    · exact rawInU_rawC ⟨rfl, rfl⟩ trivial
    · exact rawInU_rawC (q := .publicSeed) trivial trivial

theorem rawInU_forsC (idx : Index) (κ : ForsTreeIndex) :
    ∀ h j, RawInU (FRawU idx) (forsC idx κ h j)
  | 0, j => rawInU_rawC (q := .forsLeaf idx κ (forsLeafOfNat j)) rfl trivial
  | h + 1, j => by
    show RawInU _ (if hh : h < forsTreeHeight ∧ j < 2 ^ forsTreeHeight then
      rawC (.forsNode idx κ ⟨h, hh.1⟩ ⟨j, hh.2⟩) else seedC)
    split_ifs
    · exact rawInU_rawC rfl trivial
    · exact rawInU_rawC (q := .publicSeed) trivial trivial

theorem rawInU_seedC {P : RawPos → Prop} (hs : P .publicSeed) : RawInU P seedC :=
  rawInU_rawC (q := .publicSeed) hs hs

/-- **A layer publication reveals coordinates of its tree.** -/
theorem rawInU_layerReveal {K : Key} {x : Encoding} {s : TPos} (h : s ∈ layerReveal K x) :
    RawInU (LRawU K.1 K.2.1) s := by
  unfold layerReveal at h
  rcases Finset.mem_union.1 h with h | h
  · rcases Finset.mem_union.1 h with h | h
    · obtain ⟨q, hq, hs⟩ := mem_needUnion h
      rcases Finset.mem_insert.1 hs with rfl | hs
      · refine rawInU_coordOf ?_
        rcases mem_layerPos_cases hq with ⟨i, st, -, hq1⟩ | hq1 | ⟨k, j, hq1, -, -⟩ <;>
          rw [hq1] <;> exact ⟨rfl, rfl⟩
      · rcases mem_layerPos_cases hq with ⟨i, st, -, hq1⟩ | hq1 | ⟨k, j, hq1, -, -⟩ <;>
          rw [hq1] at hs
        · simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact rawInU_seedC trivial
          · exact rawInU_chainC _ _ _ _ _
        · simp only [cellNeed, Finset.mem_insert, Finset.mem_image] at hs
          rcases hs with rfl | ⟨i, -, rfl⟩
          · exact rawInU_seedC trivial
          · exact rawInU_chainC _ _ _ _ _
        · simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl
          · exact rawInU_seedC trivial
          · exact rawInU_treeC _ _ _ _
          · exact rawInU_treeC _ _ _ _
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact rawInU_chainC _ _ _ _ _
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
    exact rawInU_treeC _ _ _ _

/-- **A FORS opening reveals coordinates of its instance.** -/
theorem rawInU_forsReveal {idx : Index} {lv : ForsTreeIndex → ForsLeafIndex} {s : TPos}
    (h : s ∈ forsReveal idx lv) : RawInU (FRawU idx) s := by
  unfold forsReveal at h
  rcases Finset.mem_union.1 h with h | h
  · rcases Finset.mem_union.1 h with h | h
    · obtain ⟨q, hq, hs⟩ := mem_needUnion h
      rcases Finset.mem_insert.1 hs with rfl | hs
      · refine rawInU_coordOf ?_
        rcases mem_forsPos_cases hq with ⟨κ, hq1⟩ | ⟨κ, k, j, hq1, -⟩ | hq1 <;>
          rw [hq1] <;> rfl
      · rcases mem_forsPos_cases hq with ⟨κ, hq1⟩ | ⟨κ, k, j, hq1, -⟩ | hq1 <;>
          rw [hq1] at hs
        · simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl
          · exact rawInU_seedC trivial
          · exact rawInU_rawC rfl trivial
        · simp only [cellNeed, Finset.mem_insert, Finset.mem_singleton] at hs
          rcases hs with rfl | rfl | rfl
          · exact rawInU_seedC trivial
          · exact rawInU_forsC _ _ _ _
          · exact rawInU_forsC _ _ _ _
        · simp only [cellNeed, Finset.mem_insert, Finset.mem_image] at hs
          rcases hs with rfl | ⟨κ, -, rfl⟩
          · exact rawInU_seedC trivial
          · exact rawInU_forsC _ _ _ _
    · obtain ⟨κ, -, rfl⟩ := Finset.mem_image.1 h
      exact rawInU_rawC rfl trivial
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 h
    exact rawInU_forsC _ _ _ _

/-- **The key coordinate a FORS opening reveals** is its instance's FORS key's. -/
theorem key_of_mem_forsRevealU {K : Key} (hK : InRangeU K) {idx : Index}
    {lv : ForsTreeIndex → ForsLeafIndex} (h : vcoord (msgPos K) ∈ forsReveal idx lv) :
    K = keyOf 0 idx := by
  have hr := rawInU_forsReveal h
  obtain ⟨l, i, rfl⟩ := hK
  rcases layer_casesU l with rfl | rfl | rfl
  · have h1 : i = idx := hr _ (rawOf_msgPos_zeroU i)
    rw [h1]
  · exact (hr _ (rawOf_msgPos_oneU i)).elim
  · exact (hr _ (rawOf_msgPos_twoU i)).elim

/-- **The key coordinate a layer publication reveals** is its tree's root, the value the key above
signs. -/
theorem key_of_mem_layerRevealU {K : Key} (hK : InRangeU K) {l : Layer} {idx : Index}
    {x : Encoding} (h : vcoord (msgPos K) ∈ layerReveal (keyOf l idx) x) :
    (l = 0 ∧ K = keyOf 1 idx) ∨ (l = 1 ∧ K = keyOf 2 idx) := by
  have hr := rawInU_layerReveal h
  obtain ⟨l', i, rfl⟩ := hK
  rcases layer_casesU l' with rfl | rfl | rfl
  · exact (hr _ (rawOf_msgPos_zeroU i)).elim
  · obtain ⟨h1, h2⟩ := hr _ (rawOf_msgPos_oneU i)
    subst h1
    refine .inl ⟨rfl, keyOf_one_eqU ?_⟩
    have h3 := congrArg Fin.val h2
    have h4 := Quantum.Sphincs.treeOfIndex_zero idx
    change i.val / 256 = (treeOfIndex 0 idx).val at h3
    omega
  · obtain ⟨h1, h2⟩ := hr _ (rawOf_msgPos_twoU i)
    subst h1
    refine .inr ⟨rfl, keyOf_two_eqU ?_⟩
    have h3 := congrArg Fin.val h2
    change i.val / 65536 = (treeOfIndex 1 idx).val at h3
    rw [treeOfIndex_oneU] at h3
    exact h3

theorem seedC_mem_forsRevealU (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex) :
    seedC ∈ forsReveal idx lv :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (progNeed_subset_needUnion
    (forsRoots_mem_forsPos (p := ⟨.forsRoots idx, trivial⟩) rfl)
    (cellNeed_subset_progNeed _ (seedC_mem_cellNeed _))))

theorem chainC_mem_layerRevealU (K : Key) (x : Encoding) (i : ChainIndex) :
    chainC K.1 K.2.1 K.2.2 i (x i).val ∈ layerReveal K x :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
    (fun i ↦ chainC K.1 K.2.1 K.2.2 i (x i).val) (Finset.mem_univ i)))

end keys

/-! ## The key of a reveal -/

section revKey

/-- **The key of a reveal of the single coordinate a key of the signatures signs** (decided
classically). -/
noncomputable def keyOfTU (T : Finset TPos) : Option Key :=
  @dite _ (∃ K, InRangeU K ∧ T = {vcoord (msgPos K)}) (Classical.propDecidable _)
    (fun h ↦ some h.choose) fun _ ↦ none

theorem keyOfTU_spec {T : Finset TPos} {K : Key} (h : keyOfTU T = some K) :
    InRangeU K ∧ T = {vcoord (msgPos K)} := by
  unfold keyOfTU at h
  split_ifs at h with h'
  obtain rfl := Option.some.inj h
  exact h'.choose_spec

theorem keyOfTU_eq {K : Key} (hK : InRangeU K) : keyOfTU {vcoord (msgPos K)} = some K := by
  unfold keyOfTU
  split_ifs with h'
  · obtain ⟨hK', he⟩ := h'.choose_spec
    exact congrArg some (vcoord_msgPos_injU hK' hK (Finset.singleton_injective he.symm))
  · exact absurd ⟨K, hK, rfl⟩ h'

theorem keyOfTU_eq_none {T : Finset TPos} {s : TPos} (hs : s ∈ T) (hn : NotMcU s) :
    keyOfTU T = none := by
  rcases h : keyOfTU T with _ | K
  · rfl
  · obtain ⟨hK, rfl⟩ := keyOfTU_spec h
    exact absurd (Finset.mem_singleton.1 hs) (hn K hK)

/-- **A reveal the searches allow between searches**, with the started keys `ks`: the coordinates
of keys of the signatures it reveals are of started keys. -/
def RevOkU (ks : Finset Key) (T : Finset TPos) : Prop :=
  ∀ K, InRangeU K → vcoord (msgPos K) ∈ T → K ∈ ks

theorem revOkU_of_notMc {ks : Finset Key} {T : Finset TPos} (h : ∀ s ∈ T, NotMcU s) :
    RevOkU ks T :=
  fun K hK hm ↦ absurd rfl (h _ hm K hK)

end revKey

/-! ## The modes -/

/-- **The modes of the counter searches**: between searches; in the search of the key `K` on the
value `m` before trial `j`. Both carry the keys whose search was started. -/
inductive ModeU
  | rest (ks : Finset Key)
  | grd (ks : Finset Key) (K : Key) (m : Digest) (j : ℕ)

/-- The keys whose search was started. -/
def ModeU.ks : ModeU → Finset Key
  | .rest ks => ks
  | .grd ks _ _ _ => ks

/-- A mode between searches: `rest`, or after the last trial. -/
def ModeU.Rest : ModeU → Prop
  | .rest _ => True
  | .grd _ _ _ j => j = encodingAttemptLimit

/-- **The mode after a reveal of `T`**, the values given by `val`: the search of its key from its
value, between searches otherwise. -/
noncomputable def revNxU (μ : ModeU) (T : Finset TPos) (val : Key → Digest) : ModeU :=
  match keyOfTU T with
  | some K => .grd (insert K μ.ks) K (val K) 0
  | none => .rest μ.ks

theorem revNxU_congr (μ : ModeU) {T : Finset TPos} {val val' : Key → Digest}
    (h : ∀ K, keyOfTU T = some K → val K = val' K) : revNxU μ T val = revNxU μ T val' := by
  unfold revNxU
  rcases hT : keyOfTU T with _ | K
  · rfl
  · exact congrArg (fun m ↦ ModeU.grd (insert K μ.ks) K m 0) (h K hT)

theorem revNxU_sing (μ : ModeU) {K : Key} (hK : InRangeU K) (val : Key → Digest) :
    revNxU μ {vcoord (msgPos K)} val = .grd (insert K μ.ks) K (val K) 0 := by
  unfold revNxU
  rw [keyOfTU_eq hK]

theorem revNxU_none (μ : ModeU) {T : Finset TPos} (h : keyOfTU T = none) (val : Key → Digest) :
    revNxU μ T val = .rest μ.ks := by
  unfold revNxU
  rw [h]

/-- The mode after a trial with the decoded digest `d`: between searches after a codeword, the
next trial otherwise. -/
def decNxU (ks : Finset Key) (K : Key) (m : Digest) (j : ℕ) : Option Encoding → ModeU
  | some _ => .rest ks
  | none => .grd ks K m (j + 1)

variable (P : PublicParameter)

/-- **The trial read a mode allows**: in the search of `K` on `m` before trial `j < 2^32`, the read
of trial `j`'s encoding cell under `PK.seed = P`. -/
def srchRdOkU : ModeU → HwRead PairOut Qrom.HashDomain QMem → Prop
  | .grd _ K m j, c => j < encodingAttemptLimit ∧ c = trialRead (trialCell P K m j) K
  | .rest _, _ => False

/-- **The mode after a read**: the decoded digest decides (`decNxU`). -/
def srchRdNxU {M' : Type} : ModeU → (c : HwRead PairOut Qrom.HashDomain M') → c.Result → ModeU
  | .grd ks K m j, .readH _ _, r =>
      decNxU ks K m j (TargetSum.decodeDigest (truncateHash (r.1.getD 0).1))
  | μ, _, _ => .rest μ.ks

/-- **A program the searches allow** at the hidden values `θ`: an `h`-cell off the encoding slots
under `pkQ θ`. -/
def ProgOkU (θ : TVals) (c : HwProg PairOut Qrom.HashDomain) : Prop :=
  ∃ z a, c = .programH z a ∧ ∀ K : Key, slotOf (pkQ θ) z ≠ some (.enc K.1 K.2.1 K.2.2)

/-- The calls the modes allow, on runtime 1's ports. -/
def srchOkR : ModeU → (hwReadSpec PairOut Qrom.HashDomain SelMem).Port → Prop
  | μ, .inl _ => μ.Rest
  | μ, .inr c => srchRdOkU P μ (liftRead (S := TPos) c)

/-- The mode after a call of runtime 1. -/
def srchNxR : ModeU → (i : (hwReadSpec PairOut Qrom.HashDomain SelMem).Port) →
    (hwReadSpec PairOut Qrom.HashDomain SelMem).Result i → ModeU
  | μ, .inr c, r => srchRdNxU μ c r
  | μ, .inl _, _ => .rest μ.ks

/-- The calls the modes allow, on the template's ports. -/
def srchOkT : ModeU → (SSpecQ SelMem).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOkU P μ c.1
  | μ, .inl (.inr p) => μ.Rest ∧ ∀ θ, ProgOkU θ (p.1.realize θ)
  | μ, .inr T => μ.Rest ∧ (keyOfTU T = none → RevOkU μ.ks T)

/-- The mode after a call of the template: a reveal of a key's coordinate starts its search. -/
noncomputable def srchNxT : ModeU → (i : (SSpecQ SelMem).Port) → (SSpecQ SelMem).Result i → ModeU
  | μ, .inl (.inl (.inr c)), r => srchRdNxU μ c.1 r
  | μ, .inr T, r => revNxU μ T fun K ↦ (tabR r.1).valuePos (msgPos K)
  | μ, _, _ => .rest μ.ks

/-- **The calls the modes allow**, on runtime 2's ports with record ports, at the hidden values
`θ`: the trials under `PK.seed`. -/
def srchOkZ (θ : TVals) : ModeU → (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port → Prop
  | μ, .inl (.inl (.inl _)) => μ.Rest
  | μ, .inl (.inl (.inr c)) => srchRdOkU (tabOf θ).publicSeed μ c
  | μ, .inl (.inr c) => μ.Rest ∧ ProgOkU θ c
  | μ, .inr T => μ.Rest ∧ (keyOfTU T = none → RevOkU μ.ks T)

/-- **The mode after a call** of runtime 2 with record ports, at the hidden values `θ`. -/
noncomputable def srchNxZ (θ : TVals) : ModeU →
    (i : (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Port) →
      (recHwSpec PairOut Qrom.HashDomain TPos SelMem).Result i → ModeU
  | μ, .inl (.inl (.inr c)), r => srchRdNxU μ c r
  | μ, .inr T, _ => revNxU μ T fun K ↦ (tabOf θ).valuePos (msgPos K)
  | μ, _, _ => .rest μ.ks

/-! ## Moded programs -/

theorem modedP_monoU {spec : QuantumOracleSpec.{0, 0}} {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {Mode : Type} {ok : Mode → spec.Port → Prop}
    {nx : Mode → (i : spec.Port) → spec.Result i → Mode} {fin fin' : (Σ u, Ω u) → Mode → Prop}
    (h : ∀ a μ, fin a μ → fin' a μ) {A : QReg} (y : IFreeM (QuantumComp.toIPFunctor L spec) Ω A) :
    ∀ μ, ModedP ok nx fin μ y → ModedP ok nx fin' μ y := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun μ hy ↦ h _ μ hy
  | liftBind _ c next ih => exact fun μ hy ↦ ⟨hy.1, fun b ↦ ih b _ (hy.2 b)⟩

/-- Sequencing two parts that keep the started keys between searches. -/
theorem modedP_bind_keepU {spec : QuantumOracleSpec.{0, 0}} {ok : ModeU → spec.Port → Prop}
    {nx : ModeU → (i : spec.Port) → spec.Result i → ModeU} {A B B' : QReg} {α β : Type}
    (x : QuantumComp₂ LocalSig.instruments spec A B α)
    (g : α → QuantumComp₂ LocalSig.instruments spec B B' β) {μ : ModeU}
    (hx : ModedP ok nx (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ x)
    (hg : ∀ a μ', μ'.Rest → μ.ks ⊆ μ'.ks →
      ModedP ok nx (fun _ μ'' ↦ μ''.Rest ∧ μ'.ks ⊆ μ''.ks) μ' (g a)) :
    ModedP ok nx (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ (x.bind g) :=
  modedP₂_bind (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks)
    (F' := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) x g hx fun a μ' h ↦
      modedP_monoU (fun _ _ h' ↦ ⟨h'.1, h.2.trans h'.2⟩) _ _ (hg a μ' h.1 h.2)

variable {P}

/-! ### Runtime 1's searches -/

theorem trialRead_defU (z : Qrom.HashDomain) (K : Key) :
    trialRead z K = liftRead (S := TPos) (.readH z (cwUpd K z)) :=
  rfl

theorem modedP_readCallU {μ : ModeU} {c : HwRead PairOut Qrom.HashDomain SelMem}
    (h : srchRdOkU P μ (liftRead (S := TPos) c)) (B : QReg) :
    ModedP (L := LocalSig.instruments) (srchOkR P) srchNxR
      (fun p μ' ↦ μ' = srchRdNxU μ c p.2.2) μ (readCall c B) :=
  ⟨h, fun _ ↦ ⟨trivial, fun _ ↦ rfl⟩⟩

/-- **The counter search** of `K` on `m`, from trial `j` to the last, ends between searches with
the started keys kept: after a codeword, or after the last trial. -/
theorem modedP_grindTU (B : QReg) (ks : Finset Key) (K : Key) (m : Digest) :
    ∀ n j, j + n = encodingAttemptLimit →
      ModedP (L := LocalSig.instruments) (srchOkR P) srchNxR
        (fun _ (μ : ModeU) ↦ μ.Rest ∧ μ.ks = ks) (.grd ks K m j)
        (grindT SelMem cwUpd P B K m n j)
  | 0, j, hn => ⟨(Nat.add_zero j).symm.trans hn, rfl⟩
  | n + 1, j, hn => by
    have hj : j < encodingAttemptLimit := by omega
    have ih := modedP_grindTU B ks K m n (j + 1) (by omega)
    rw [grindT]
    generalize hz : trialCell P K m j = z
    have hr : srchRdOkU P (.grd ks K m j) (liftRead (S := TPos) (.readH z (cwUpd K z))) :=
      ⟨hj, by rw [← hz]; rfl⟩
    refine ⟨hr, fun b ↦ ⟨trivial, fun _ ↦ ?_⟩⟩
    show ModedP _ _ _ (decNxU ks K m j (TargetSum.decodeDigest (truncateHash (b.down.1.getD 0).1)))
      (match TargetSum.decodeDigest (truncateHash (b.down.1.getD 0).1) with
        | some x => QuantumComp₂.pure (some (BitVec.ofNat counterBits j, x))
        | none => grindT SelMem cwUpd P B K m n (j + 1))
    generalize TargetSum.decodeDigest (truncateHash (b.down.1.getD 0).1) = dd
    cases dd with
    | none => exact ih
    | some x => exact ⟨trivial, rfl⟩

/-- **Lifting runtime 1's moded programs to templates.** -/
theorem modedP_readLiftU {Ω : QReg → Type} {A : QReg} {fin : (Σ u, Ω u) → ModeU → Prop}
    (y : QuantumComp LocalSig.instruments (hwReadSpec PairOut Qrom.HashDomain SelMem) Ω A)
    {μ : ModeU} (hy : ModedP (srchOkR P) srchNxR fin μ y) :
    ModedP (srchOkT P) srchNxT fin μ (readLift goodQ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (readLens goodQ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i | c, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      rcases c with ⟨z, u⟩ | ⟨x, u⟩ | ⟨y, u⟩ <;> rcases μ with ks | ⟨ks, K, m, j⟩ <;>
        exact ih _ (hy.2 (ULift.up (b.down.1, b.down.2.2)))

/-- A sponge program of runtime 1 runs between searches, the started keys kept. -/
theorem modedP_liftOrdinaryU {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (spongeSpec PairOut Qrom.HashDomain) Ω A) :
    ∀ μ : ModeU, μ.Rest → ModedP (srchOkR P) srchNxR (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (y.liftOrdinary (t := hwReadCmdSpec PairOut Qrom.HashDomain SelMem)) := by
  induction y using IFreeM.inductionOn with
  | pure _ a => exact fun _ h ↦ ⟨h, subset_rfl⟩
  | liftBind _ c next ih =>
    intro μ hμ
    show ModedP _ _ _ _ (IFreeM.mapLens QuantumComp.ordinaryLens (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨i, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ μ hμ⟩
    · exact ⟨hμ, fun b ↦ ih _ (.rest μ.ks) trivial⟩

/-! ### Realizing -/

theorem srchNxZ_rec_eq (θ : TVals) (μ : ModeU) (T : Finset TPos) (m : QMem) :
    srchNxZ θ μ (.inr T) m = srchNxT μ (.inr T) (restrictTo T θ, m) :=
  revNxU_congr μ fun K hK ↦ valuePos_tabOf_congr (msgPos K)
    (pairAt_extW_restrictTo (by rw [(keyOfTU_spec hK).2]; exact Finset.mem_singleton_self _)
      θ).symm

/-- **Realizing keeps the modes**, the trials under `PK.seed`. -/
theorem modedP_realizeTU (θ : TVals) {L : LocalSig.{u, v}} {Ω : QReg → Type w}
    {A : QReg} {fin : (Σ u, Ω u) → ModeU → Prop} (y : QuantumComp L (SSpecQ SelMem) Ω A)
    {μ : ModeU} (hy : ModedP (srchOkT (tabOf θ).publicSeed) srchNxT fin μ y) :
    ModedP (srchOkZ θ) (srchNxZ θ) fin μ (realizeT θ y) := by
  induction y using IFreeM.inductionOn generalizing μ with
  | pure _ a => exact hy
  | liftBind _ c next ih =>
    show ModedP _ _ _ μ (IFreeM.mapLens (tmplLens θ) (IFreeM.liftBind c next))
    rw [IFreeM.mapLens_liftBind]
    rcases c with o | ⟨((i | c) | ⟨p, hp⟩) | T, E, ℓ⟩
    · exact ⟨trivial, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · exact ⟨hy.1, fun b ↦ ih _ (hy.2 _)⟩
    · cases p <;> exact ⟨⟨hy.1.1, hy.1.2 θ⟩, fun b ↦ ih _ (hy.2 _)⟩
    · refine ⟨hy.1, fun b ↦ ?_⟩
      have h := ih _ (hy.2 (ULift.up (restrictTo T θ, b.down)))
      exact (congrArg (fun μ' ↦ ModedP (srchOkZ θ) (srchNxZ θ) fin μ' _)
        (srchNxZ_rec_eq θ μ T b.down)).mpr h

/-- **A realized reveal**: the record port, then the continuation at the values of `θ`. -/
theorem modedP_realizeT_revealThenU (θ : TVals) {B B' : QReg} {α : Type} {T : Finset TPos}
    {k : RevealVals TVal T × QMem → QComp (SSpecQ SelMem) B B' α} {F : α → ModeU → Prop}
    {μ : ModeU} (hok : srchOkZ θ μ (.inr T))
    (hk : ∀ mem, ModedP (srchOkZ θ) (srchNxZ θ) (fun p μ ↦ F p.2.2 μ)
      (srchNxZ θ μ (.inr T) mem) (realizeT θ (k (restrictTo T θ, mem)))) :
    ModedP (srchOkZ θ) (srchNxZ θ) (fun p μ ↦ F p.2.2 μ) μ
      (realizeT θ (revealThen goodQ T k)) := by
  have e : realizeT θ (revealThen goodQ T k) =
      QuantumComp₂.queryBind (L := LocalSig.instruments)
        (spec := recHwSpec PairOut Qrom.HashDomain TPos SelMem) (.inr T) B
        (Equiv.uniqueProd B Unit).symm fun mem ↦
          (QComp.act (A := QReg.of ((recHwSpec PairOut Qrom.HashDomain TPos SelMem).Out (.inr T) ×
            B)) (B := B) (SubInstrument.relabel (Equiv.uniqueProd B Unit))).bind fun _ ↦
              realizeT θ (k (restrictTo T θ, mem)) :=
    rfl
  rw [e]
  refine ⟨hok, fun b ↦ modedP₂_bind (F := fun _ μ' ↦ μ' = srchNxZ θ μ (.inr T) b.down) _ _
    ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_⟩
  subst h
  exact hk b.down

/-! ### The template's parts -/

variable (P) in
/-- **A template moded between searches**: from every mode between searches it ends between
searches, the started keys kept. -/
def SRestU {Ω : QReg → Type} {A : QReg}
    (y : QuantumComp LocalSig.instruments (SSpecQ SelMem) Ω A) : Prop :=
  ∀ μ : ModeU, μ.Rest → ModedP (srchOkT P) srchNxT (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ y

theorem sRestU_bind {A B B' : QReg} {α β : Type} (x : QComp (SSpecQ SelMem) A B α)
    (g : α → QComp (SSpecQ SelMem) B B' β) (hx : SRestU P x) (hg : ∀ a, SRestU P (g a)) :
    SRestU P (x.bind g) :=
  fun μ hμ ↦ modedP_bind_keepU x g (hx μ hμ) fun a μ' h _ ↦ hg a μ' h

theorem sRestU_pure {A : QReg} {α : Type} (a : α) :
    SRestU P (QuantumComp₂.pure (L := LocalSig.instruments) (spec := SSpecQ SelMem) (A := A) a) :=
  fun _ h ↦ ⟨h, subset_rfl⟩

/-- A template reveal: the reveal port, then the continuation. -/
theorem modedP_revealThenU {B B' : QReg} {α : Type} {T : Finset TPos} {F : α → ModeU → Prop}
    {k : RevealVals TVal T × QMem → QComp (SSpecQ SelMem) B B' α} {μ : ModeU}
    (hok : srchOkT P μ (.inr T))
    (hk : ∀ r, ModedP (srchOkT P) srchNxT (fun p μ ↦ F p.2.2 μ) (srchNxT μ (.inr T) r) (k r)) :
    ModedP (srchOkT P) srchNxT (fun p μ ↦ F p.2.2 μ) μ (revealThen goodQ T k) := by
  refine ⟨hok, fun b ↦ modedP₂_bind (F := fun _ μ' ↦ μ' = srchNxT μ (.inr T) b.down) _ _
    ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_⟩
  subst h
  exact hk b.down

/-- A reveal of no key's coordinate keeps the modes between searches. -/
theorem sRestU_revealThen {B B' : QReg} {α : Type} (T : Finset TPos)
    (hT : keyOfTU T = none) (hR : ∀ ks, RevOkU ks T)
    (k : RevealVals TVal T × QMem → QComp (SSpecQ SelMem) B B' α)
    (hk : ∀ r, SRestU P (k r)) : SRestU P (revealThen goodQ T k) := fun μ hμ ↦
  modedP_revealThenU (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) ⟨hμ, fun _ ↦ hR _⟩ fun r ↦ by
    rw [show srchNxT μ (.inr T) r = .rest μ.ks from revNxU_none μ hT _]
    exact hk r (.rest μ.ks) trivial

theorem sRestU_progThen {B B' : QReg} {α : Type} (p : LazyProg PairOut Qrom.HashDomain TPos TVal)
    (hp : ∀ θ, ProgOkU θ (p.realize θ)) (k : QComp (SSpecQ SelMem) B B' α) (hk : SRestU P k) :
    SRestU P (progThen p trivial k) := by
  intro μ hμ
  refine ⟨⟨hμ, hp⟩, fun _ ↦ ?_⟩
  refine modedP₂_bind (F := fun _ (μ' : ModeU) ↦ μ' = ModeU.rest μ.ks)
    (F' := fun _ (μ' : ModeU) ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) _ _ ?_ fun _ μ' h ↦ ?_
  · exact ⟨trivial, fun _ ↦ rfl⟩
  · subst h
    exact hk (.rest μ.ks) trivial

/-- **A table cell is programmed off the encoding slots.** -/
theorem progOkU_cellOf (θ : TVals) (p : Pos) (a : PairOut) :
    ProgOkU θ (.programH (cellOf (seedOf θ) p (tabOf θ)) a) := by
  have hsl : slotOf (pkQ θ) (cellOf (seedOf θ) p (tabOf θ)) = some (posSlot (tabOf θ) p.1) :=
    slotOf_cell ((tabOf θ).expandedKey (seedOf θ)) (tabOf θ).root
      (slotInRange_posSlot (tabOf θ) p) _
  refine ⟨_, _, rfl, fun K h ↦ ?_⟩
  rw [hsl] at h
  exact posSlot_ne_enc (tabOf θ) p.1 K.1 K.2.1 K.2.2 (Option.some.inj h)

theorem progOkU_progT {p : Pos} (hp : p.1.IsStruct) (θ : TVals) :
    ProgOkU θ ((progT p).realize θ) := by
  rw [realize_progT hp (seedOf θ) θ]
  exact progOkU_cellOf θ p _

theorem progOkU_digPort (pol : DigestPolicy) (L : Finset TPos) (msg : Message) (θ : TVals) :
    ProgOkU θ ((digPort pol L msg).realize θ) := by
  rw [realize_digPort, ← cellOf_digPos (seedOf θ)]
  exact progOkU_cellOf θ (digPos msg) _

theorem sRestU_progPos (B : QReg) :
    ∀ ps : List Pos, (∀ p ∈ ps, p.1.IsStruct) → SRestU P (progPos SelMem B ps)
  | [], _ => sRestU_pure _
  | p :: ps, h => sRestU_progThen _ (progOkU_progT (h p List.mem_cons_self)) _
      (sRestU_progPos B ps fun q hq ↦ h q (List.mem_cons_of_mem _ hq))

/-- **A key's counter search** reveals its coordinate, starts the key, and searches from the
revealed value. -/
theorem modedP_selectTU (B : QReg) {K : Key} (hK : InRangeU K) (μ : ModeU) (hμ : μ.Rest) :
    ModedP (srchOkT P) srchNxT (fun _ μ' ↦ μ'.Rest ∧ insert K μ.ks ⊆ μ'.ks) μ
      (selectT SelMem cwUpd P B K) := by
  unfold selectT
  refine modedP_revealThenU (F := fun _ μ' ↦ μ'.Rest ∧ insert K μ.ks ⊆ μ'.ks)
    ⟨hμ, fun h ↦ by rw [keyOfTU_eq hK] at h; cases h⟩ fun r ↦ ?_
  rw [show srchNxT μ (.inr {vcoord (msgPos K)}) r =
    .grd (insert K μ.ks) K ((tabR r.1).valuePos (msgPos K)) 0 from revNxU_sing μ hK _]
  exact modedP_monoU (fun _ μ' h ↦ ⟨h.1, by rw [h.2]⟩) _ _
    (modedP_readLiftU _ (modedP_grindTU B _ K _ _ 0 (Nat.zero_add _)))

/-- A layer publication of an index whose keys were started. -/
theorem modedP_publishTU (B : QReg) (l : Layer) (idx : Index) (c : EncodingCounter)
    (x : Encoding) (μ : ModeU) (hμ : μ.Rest) (hks : ∀ l', keyOf l' idx ∈ μ.ks) :
    ModedP (srchOkT P) srchNxT (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (publishT SelMem B (keyOf l idx) c x) := by
  have hT : keyOfTU (layerReveal (keyOf l idx) x) = none :=
    keyOfTU_eq_none (chainC_mem_layerRevealU _ x ⟨0, by decide⟩) (notMcU_chainC _ _ _ _ _)
  unfold publishT
  refine modedP_revealThenU (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks)
    ⟨hμ, fun _ K hK hm ↦ ?_⟩ fun r ↦ ?_
  · rcases key_of_mem_layerRevealU hK hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact hks _
  · rw [show srchNxT μ (.inr (layerReveal (keyOf l idx) x)) r = .rest μ.ks from
      revNxU_none μ hT _]
    exact sRestU_bind _ _ (sRestU_progPos B _ fun _ hp ↦ isStruct_of_mem_layerPos hp)
      (fun _ ↦ sRestU_pure _) (.rest μ.ks) trivial

/-- A FORS opening of an index whose keys were started. -/
theorem modedP_forsOpenTU (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (μ : ModeU) (hμ : μ.Rest) (hks : ∀ l', keyOf l' idx ∈ μ.ks) :
    ModedP (srchOkT P) srchNxT (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (forsOpenT SelMem B idx lv) := by
  have hT : keyOfTU (forsReveal idx lv) = none :=
    keyOfTU_eq_none (seedC_mem_forsRevealU idx lv) notMcU_seedC
  unfold forsOpenT
  refine modedP_revealThenU (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks)
    ⟨hμ, fun _ K hK hm ↦ ?_⟩ fun r ↦ ?_
  · rw [key_of_mem_forsRevealU hK hm]
    exact hks _
  · rw [show srchNxT μ (.inr (forsReveal idx lv)) r = .rest μ.ks from revNxU_none μ hT _]
    exact sRestU_bind _ _ (sRestU_progPos B _ fun _ hp ↦ isStruct_of_mem_forsPos hp)
      (fun _ ↦ sRestU_pure _) (.rest μ.ks) trivial

/-- **The publication** of an index whose keys were started. -/
theorem modedP_publishAllTU (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) (g₀ g₁ g₂ : Option (EncodingCounter × Encoding)) (μ : ModeU) (hμ : μ.Rest)
    (hks : ∀ l', keyOf l' idx ∈ μ.ks) :
    ModedP (srchOkT P) srchNxT (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (publishAllT SelMem B idx lv R g₀ g₁ g₂) := by
  rcases g₀ with _ | ⟨c₀, x₀⟩ <;> rcases g₁ with _ | ⟨c₁, x₁⟩ <;>
    rcases g₂ with _ | ⟨c₂, x₂⟩ <;> try exact ⟨hμ, subset_rfl⟩
  simp only [publishAllT]
  refine modedP_bind_keepU _ _ (modedP_forsOpenTU B idx lv μ hμ hks) fun _ μ₁ h₁ s₁ ↦ ?_
  refine modedP_bind_keepU _ _ (modedP_publishTU B 0 idx c₀ x₀ μ₁ h₁ fun l' ↦ s₁ (hks l'))
    fun _ μ₂ h₂ s₂ ↦ ?_
  refine modedP_bind_keepU _ _
    (modedP_publishTU B 1 idx c₁ x₁ μ₂ h₂ fun l' ↦ s₂ (s₁ (hks l'))) fun _ μ₃ h₃ s₃ ↦ ?_
  refine modedP_bind_keepU _ _
    (modedP_publishTU B 2 idx c₂ x₂ μ₃ h₃ fun l' ↦ s₃ (s₂ (s₁ (hks l')))) fun _ μ₄ h₄ _ ↦ ?_
  exact ⟨h₄, subset_rfl⟩

/-- **The three searches and the publication** of a signature. -/
theorem sRestU_selectsU (B : QReg) (idx : Index) (lv : ForsTreeIndex → ForsLeafIndex)
    (R : Randomizer) :
    SRestU P ((selectT SelMem cwUpd P B (keyOf 0 idx)).bind fun g₀ ↦
      (selectT SelMem cwUpd P B (keyOf 1 idx)).bind fun g₁ ↦
      (selectT SelMem cwUpd P B (keyOf 2 idx)).bind fun g₂ ↦
        publishAllT SelMem B idx lv R g₀ g₁ g₂) := by
  intro μ hμ
  refine modedP₂_bind
    (F := fun _ (μ' : ModeU) ↦ μ'.Rest ∧ insert (keyOf 0 idx) μ.ks ⊆ μ'.ks)
    (F' := fun _ (μ' : ModeU) ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) _ _ (modedP_selectTU B ⟨0, idx, rfl⟩ μ hμ)
    fun g₀ μ₁ h₁ ↦ ?_
  refine modedP₂_bind
    (F := fun _ (μ' : ModeU) ↦ μ'.Rest ∧ insert (keyOf 1 idx) μ₁.ks ⊆ μ'.ks)
    (F' := fun _ (μ' : ModeU) ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) _ _
    (modedP_selectTU B ⟨1, idx, rfl⟩ μ₁ h₁.1) fun g₁ μ₂ h₂ ↦ ?_
  refine modedP₂_bind
    (F := fun _ (μ' : ModeU) ↦ μ'.Rest ∧ insert (keyOf 2 idx) μ₂.ks ⊆ μ'.ks)
    (F' := fun _ (μ' : ModeU) ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) _ _
    (modedP_selectTU B ⟨2, idx, rfl⟩ μ₂ h₂.1) fun g₂ μ₃ h₃ ↦ ?_
  have hs : μ.ks ⊆ μ₃.ks := ((Finset.subset_insert _ _).trans h₁.2).trans
    (((Finset.subset_insert _ _).trans h₂.2).trans ((Finset.subset_insert _ _).trans h₃.2))
  have hks : ∀ l', keyOf l' idx ∈ μ₃.ks := by
    intro l'
    rcases layer_casesU l' with rfl | rfl | rfl
    · exact h₃.2 (Finset.mem_insert_of_mem (h₂.2 (Finset.mem_insert_of_mem
        (h₁.2 (Finset.mem_insert_self _ _)))))
    · exact h₃.2 (Finset.mem_insert_of_mem (h₂.2 (Finset.mem_insert_self _ _)))
    · exact h₃.2 (Finset.mem_insert_self _ _)
  exact modedP_monoU (fun _ _ h ↦ ⟨h.1, hs.trans h.2⟩) _ _
    (modedP_publishAllTU B idx lv R g₀ g₁ g₂ μ₃ h₃.1 hks)

/-! ### The realized challenge prefix -/

theorem modedP_realizeT_bindU (θ : TVals) {Ω Ω' : QReg → Type} {A : QReg}
    (x : QuantumComp LocalSig.instruments (SSpecQ SelMem) Ω A)
    (g : ∀ u, Ω u → QuantumComp LocalSig.instruments (SSpecQ SelMem) Ω' u)
    {fin : (Σ u, Ω u) → ModeU → Prop} {fin' : (Σ u, Ω' u) → ModeU → Prop} {μ : ModeU}
    (hx : ModedP (srchOkZ θ) (srchNxZ θ) fin μ (realizeT θ x))
    (hg : ∀ u a μ', fin ⟨u, a⟩ μ' → ModedP (srchOkZ θ) (srchNxZ θ) fin' μ'
      (realizeT θ (g u a))) :
    ModedP (srchOkZ θ) (srchNxZ θ) fin' μ (realizeT θ (x.bind g)) := by
  rw [realizeT_bind]
  exact modedP_bind _ _ hx hg

theorem modedP_realizeT_bind₂U (θ : TVals) {A B C : QReg} {α β : Type}
    (x : QComp (SSpecQ SelMem) A B α) (k : α → QComp (SSpecQ SelMem) B C β)
    {F : α → ModeU → Prop} {F' : β → ModeU → Prop} {μ : ModeU}
    (hx : ModedP (srchOkZ θ) (srchNxZ θ) (fun p μ ↦ F p.2.2 μ) μ (realizeT θ x))
    (hk : ∀ a μ', F a μ' → ModedP (srchOkZ θ) (srchNxZ θ) (fun p μ ↦ F' p.2.2 μ) μ'
      (realizeT θ (k a))) :
    ModedP (srchOkZ θ) (srchNxZ θ) (fun p μ ↦ F' p.2.2 μ) μ (realizeT θ (x.bind k)) := by
  rw [realizeT_bind₂]
  exact modedP₂_bind _ _ hx hk

theorem notMcU_sigReveal (msg : Message) : ∀ s ∈ ({seedC, rootC, rndC msg} : Finset TPos),
    NotMcU s := by
  intro s hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · exact notMcU_seedC
  · exact notMcU_rootC
  · exact notMcU_rndC msg

theorem notMcU_pkReveal : ∀ s ∈ pkReveal, NotMcU s := by
  intro s hs
  simp only [pkReveal, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl
  · exact notMcU_seedC
  · exact notMcU_rootC

/-- **A realized signature** is moded between searches: its first reveal fixes the searches'
`PK.seed`. -/
theorem modedP_signTU {pol : DigestPolicy} (hpol : pol.NoVal) (θ : TVals) (B : QReg)
    (msg : Message) (μ : ModeU) (hμ : μ.Rest) :
    ModedP (srchOkZ θ) (srchNxZ θ) (fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) μ
      (realizeT θ (signT SelMem cwUpd pol B msg)) := by
  have hT : keyOfTU {seedC, rootC, rndC msg} = none :=
    keyOfTU_eq_none (Finset.mem_insert_self _ _) notMcU_seedC
  rw [signT]
  refine modedP_realizeT_revealThenU (F := fun _ μ' ↦ μ'.Rest ∧ μ.ks ⊆ μ'.ks) θ
    ⟨hμ, fun _ ↦ revOkU_of_notMc (notMcU_sigReveal msg)⟩ fun mem ↦ ?_
  rw [show srchNxZ θ μ (.inr {seedC, rootC, rndC msg}) mem = .rest μ.ks from
    revNxU_none μ hT _]
  have hs₀ : (tabR (restrictTo {seedC, rootC, rndC msg} θ)).publicSeed = (tabOf θ).publicSeed :=
    sigTabD_publicSeed msg
  dsimp only
  rw [hs₀]
  refine modedP_realizeTU θ _ ?_
  exact sRestU_revealThen _ (keyOfTU_eq_none (pol.out_mem _ _)
      (notMcU_of_noVal hpol (pol.out_mem _ _)))
    (fun _ ↦ revOkU_of_notMc fun _ hs ↦ notMcU_of_noVal hpol hs) _
    (fun _ ↦ sRestU_progThen _ (progOkU_digPort pol _ msg) _ (sRestU_selectsU B _ _ _))
    (.rest μ.ks) trivial

/-- **The realized challenger** is moded between searches. -/
theorem modedP_challengeTU {pol : DigestPolicy} (hpol : pol.NoVal) (θ : TVals) (A : QReg)
    (c : QuantumComp.Cmd LocalSig.instruments.{0} sAdvSpec A) :
    ∀ μ : ModeU, μ.Rest → ModedP (srchOkZ θ) (srchNxZ θ) (fun _ μ' ↦ μ'.Rest) μ
      (realizeT θ (challengeT SelMem cwUpd pol A c)) := by
  intro μ hμ
  rcases c with o | ⟨_ | msg, E, ℓ⟩
  · exact modedP_realizeTU θ _ (modedP_readLiftU _
      (modedP_monoU (fun _ _ h ↦ h.1) _ _ (modedP_liftOrdinaryU _ μ hμ)))
  · exact modedP_realizeTU θ _ (modedP_readLiftU _
      (modedP_monoU (fun _ _ h ↦ h.1) _ _ (modedP_liftOrdinaryU _ μ hμ)))
  · dsimp only [challengeT]
    refine modedP_realizeT_bindU θ _ _ (fin := fun _ (μ' : ModeU) ↦ μ'.Rest) ?_
      fun _ _ _ h ↦ h
    unfold signAt
    refine modedP_realizeT_bind₂U θ _ _ (F := fun _ (μ' : ModeU) ↦ μ' = μ)
      (F' := fun _ (μ' : ModeU) ↦ μ'.Rest) ⟨trivial, fun _ ↦ rfl⟩ fun _ μ' h ↦ ?_
    subst h
    exact modedP_monoU (fun _ _ h ↦ h.1) _ _ (modedP_signTU hpol θ _ msg μ' hμ)

theorem modedP_castU {spec : QuantumOracleSpec.{0, 0}} {ok : ModeU → spec.Port → Prop}
    {nx : ModeU → (i : spec.Port) → spec.Result i → ModeU} {Ω : QReg → Type w}
    {fin : (Σ u, Ω u) → ModeU → Prop} {A A' : QReg} (e : A = A')
    (y : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) (μ : ModeU) :
    ModedP ok nx fin μ (e ▸ y) ↔ ModedP ok nx fin μ y := by
  subst e
  rfl

/-- Substituting trees moded between searches, on runtime 2. -/
theorem modedP_substituteU {spec : QuantumOracleSpec.{0, 0}} (θ : TVals)
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments spec)
      (QuantumComp.toIPFunctor LocalSig.instruments
        (recHwSpec PairOut Qrom.HashDomain TPos SelMem)))
    (hσ : ∀ A c, ∀ μ : ModeU, μ.Rest → ModedP (srchOkZ θ) (srchNxZ θ)
      (fun _ (μ : ModeU) ↦ μ.Rest) μ (σ A c)) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments spec) Ω A) :
    ∀ μ : ModeU, μ.Rest → ModedP (srchOkZ θ) (srchNxZ θ) (fun _ (μ : ModeU) ↦ μ.Rest) μ
      (x.substitute σ) := by
  induction x using IFreeM.inductionOn with
  | pure _ _ => exact fun _ h ↦ h
  | liftBind s c next ih =>
    intro μ hμ
    rw [IFreeM.substitute_liftBind]
    exact modedP_bind _ _ (hσ s c μ hμ) fun u ans μ' h ↦ (modedP_castU ans.2 _ _).mpr
      (ih ans.1 μ' h)

theorem modedP_realizeT_substituteU {spec : QuantumOracleSpec.{0, 0}} (θ : TVals)
    (σ : IPFunctor.CommandSubstitution (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec)
      (QuantumComp.toIPFunctor LocalSig.instruments.{0} (SSpecQ SelMem)))
    (hσ : ∀ A c, ∀ μ : ModeU, μ.Rest → ModedP (srchOkZ θ) (srchNxZ θ)
      (fun _ (μ : ModeU) ↦ μ.Rest) μ (realizeT θ (σ A c))) {Ω : QReg → Type}
    {A : QReg} (x : IFreeM (QuantumComp.toIPFunctor LocalSig.instruments.{0} spec) Ω A) :
    ∀ μ : ModeU, μ.Rest → ModedP (srchOkZ θ) (srchNxZ θ) (fun _ (μ : ModeU) ↦ μ.Rest) μ
      (realizeT θ (x.substitute σ)) := by
  intro μ hμ
  rw [realizeT_substitute]
  exact modedP_substituteU θ _ hσ x μ hμ

/-- **The realized challenge prefix is moded** from `rest ∅`, its searches' trials under
`PK.seed`, ending between searches. -/
theorem modedP_prefixQ {pol : DigestPolicy} (hpol : pol.NoVal) (A : SAdversary) (θ : TVals) :
    ModedP (srchOkZ θ) (srchNxZ θ) (fun _ (μ : ModeU) ↦ μ.Rest) (.rest ∅) (prefixQ pol A θ) := by
  have hT : keyOfTU pkReveal = none :=
    keyOfTU_eq_none (Finset.mem_insert_self _ _) notMcU_seedC
  unfold prefixQ prefixT
  refine modedP_realizeT_revealThenU (F := fun _ μ' ↦ μ'.Rest) θ
    ⟨trivial, fun _ ↦ revOkU_of_notMc notMcU_pkReveal⟩ fun mem ↦ ?_
  rw [show srchNxZ θ (.rest ∅) (.inr pkReveal) mem = .rest ∅ from revNxU_none _ hT _]
  dsimp only
  rw [realizeT_bind₂]
  refine modedP₂_bind (F := fun _ (μ' : ModeU) ↦ μ'.Rest) (F' := fun _ (μ' : ModeU) ↦ μ'.Rest)
    _ _ ?_ fun _ _ h ↦ h
  unfold challengedT
  exact modedP_realizeT_substituteU θ _ (fun A c ↦ modedP_challengeTU hpol θ A c) _ _ trivial

end Quantum.Qrom.Sphincs

end
