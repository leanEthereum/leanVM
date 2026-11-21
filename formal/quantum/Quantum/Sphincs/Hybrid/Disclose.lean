module

public import Quantum.Xmss.Hybrid.Disclose
public import Quantum.Sphincs.Hybrid.View
public import Quantum.Sphincs.Assembly.SrcBad

@[expose] public section

/-!
# Hidden masses of leanSPHINCS's cells under adaptive disclosures

`Quantum.Xmss.Hybrid.Disclose` gives the adaptive view lemma: under the lazy-sampling property
`ViewByOn`, hidden `k`-cells that each name an undisclosed coordinate, whose hidden value they
carry, weigh `1 / |D|` per call on average (`sum_queryWeight_hiddenMass_le`,
`sum_queryWeight_hiddenK_digest_le`). This file names leanSPHINCS's sources.

* `sum_queryWeight_hiddenK_src_le`: the same for hidden values of several types `D s` (the value
  positions' digests, the randomizers, the `H_msg` outputs): `κ` per call when `|D s|⁻¹ ≤ κ` for
  every coordinate `s`.
* `payloadHi`: bytes `64` to `79` of a block, an addressed input's second payload value
  (`Quantum.Sphincs.Assembly.payloadLo` is the first); `payloadLo_addressed`,
  `payloadHi_addressed`.
* `slotSrc T x s`, `cellSrc pk T x`: the position and value a first block names, for the disclosed
  positions `T`. A structural slot names its designated source (`Quantum.Sphincs.Assembly.dsrc`:
  the chain position a step leaves, the first chain end of a one-time leaf, the left child of a tree
  or FORS node, a FORS leaf's secret, the root of FORS tree `0` for the roots compression), or a
  node's right child when its left one is disclosed; an encoding trial `Enc(K, M, c)` names the
  position `msgPos K` of the one value `K` signs. `srcSet s`: the positions a slot's first block may
  name (`srcSet_subset_slotNeed`).
* `cellSrc_slotBlk`: an in-table slot's first block at the values `v` names a position
  `q ∈ srcSet s` and carries `v q`, and `q` is disclosed only if all of `srcSet s` is
  (`exists_cellSrc_of_not_subset`); `cellSrc_honestCell`: at `v = valuePos L`, the honest table's
  first blocks (`honestCell L s`, `slotOfBlock_honestCell`). `cellSrc_encCell`: an
  encoding trial's first block names `msgPos K` and carries the message it encodes.
* `sum_queryWeight_cellSrc_le`: hidden `k`-cells that each name, by `cellSrc`, an undisclosed
  position whose hidden value they carry weigh `2^-128` per call; `sum_queryWeight_hmsg_le`: the
  `H_msg` blocks of messages whose randomizer is undisclosed, `2^-128` per call.

The `2^-128` bound covers the first block of each input. The one-time leaf (`8` blocks) and the
FORS roots compression (`4` blocks) carry their other values in later blocks, whose `k`-cells are
covered through the hidden `h`-value of the previous round (`sum_queryWeight_hiddenKNext_le`, at
`|S| / |X|` per call), as for leanXMSS.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w

open Quantum Quantum.Sponge QuantumRuntime Sphincs
open HashSig (Digest Message PublicParameter Randomizer HashInput chainLength littleEndianBytes
  hasherInput)
open HashSig.OverPermutation (nodePayload)
open Quantum.Xmss (X Z rateSlice blockOf firstBlock length_littleEndianBytes)
open Quantum.Xmss.Hybrid (firstCell runtime2 hiddenMass ViewByOn sum_queryWeight_hiddenMass_le
  sum_queryWeight_hiddenK_digest_le)
open Quantum.Sphincs.Assembly (dsrc payloadLo payloadLo_slotBlk slotBlk slotBlk_zero
  slotInput_of_ne ne_hmsg_of_inTable slotOfBlock_slotBlk)

namespace Quantum.Sphincs.Hybrid

/-! ## Hidden coordinates of several types -/

section hw

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **Hidden `k`-cells naming one coordinate of any type.** If every hidden `k`-cell `y ∈ Hk v` that
is not hardwired names a coordinate `src y r`, undisclosed in the register, whose hidden value is
the value `val y r` the cell carries, the hidden mass is at most `κ` per call on average, where
`|D s|⁻¹ ≤ κ` for every coordinate `s`. -/
theorem sum_queryWeight_hiddenK_src_le {S : Type} [Fintype S] [DecidableEq S] {D : S → Type}
    [∀ s, Fintype (D s)] [∀ s, DecidableEq (D s)] [∀ s, Nonempty (D s)] (m₀ : M)
    (lab : HwReg X Z M → Finset S) (x : ((s : S) → D s) → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : ((s : S) → D s) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (D := D) (runtime2 X Z m₀) I (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hk : ((s : S) → D s) → Set X) (src : X → HwReg X Z M → S) (val : ∀ y r, D (src y r))
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none → src y r ∉ lab r ∧ v (src y r) = val y r)
    (κ : ℝ≥0∞) (hκ : ∀ s, (Fintype.card (D s) : ℝ≥0∞)⁻¹ ≤ κ) :
    ∑ v, (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ (Hk v) ∅) (x v) (ρ v) j ≤
      κ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenMass_le (D := D) I m₀ lab x ρ hρ j hview
    (fun _ ↦ ∅) Hk (fun _ ↦ ∅) (fun _ _ ↦ ∅) (fun y r ↦ {src y r}) (fun _ _ ↦ ∅)
    (fun _ _ _ _ ↦ ∅) (fun y r s _ ↦ if h : src y r = s then {h ▸ val y r} else ∅)
    (fun _ _ _ _ ↦ ∅) (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl)
    (fun _ _ _ hz ↦ hz.elim) (fun v y r hy hW ↦ ?_) (fun _ _ _ hy ↦ hy.elim) κ
    (fun _ _ _ ↦ by simp) (fun y r _ ↦ ?_) (fun _ _ _ ↦ by simp)
  · obtain ⟨h1, h2⟩ := hk v y r hy hW
    refine ⟨src y r, Finset.mem_singleton_self _, h1, ?_⟩
    rw [dite_eq_left rfl]
    exact Finset.mem_singleton.mpr h2
  · rw [Finset.sum_singleton, dite_eq_left rfl, Finset.card_singleton, Nat.cast_one, one_mul]
    exact hκ _

end hw

/-! ## The values a first block carries -/

section payload

/-- Bits `512` to `639` of a block (bytes `64` to `79`): an addressed input's second payload
value. -/
def payloadHi (x : X) : Digest :=
  rateSlice x 512 (8 * 16) (by norm_num)

/-- The first block of an addressed input carries its first payload value in bytes `48` to
`63`. -/
theorem payloadLo_addressed (P : PublicParameter) (a : Address) (d : Digest) (rest : HashInput) :
    payloadLo (firstCell (addressedHashInput P a (littleEndianBytes 16 d ++ rest))) = d := by
  refine rateSlice_firstBlock (a := littleEndianBytes 16 P ++ a.toBytes) (s := 384) (n := 16)
    ⟨rest, ?_⟩ ?_ _
  · show _ = hasherInput _ _ _
    rw [hasherInput, List.append_assoc]
  · rw [List.length_append, length_littleEndianBytes, length_toBytes]

/-- The first block of an addressed input carries its second payload value in bytes `64` to
`79`. -/
theorem payloadHi_addressed (P : PublicParameter) (a : Address) (d d' : Digest)
    (rest : HashInput) :
    payloadHi (firstCell (addressedHashInput P a
      (littleEndianBytes 16 d ++ littleEndianBytes 16 d' ++ rest))) = d' := by
  refine rateSlice_firstBlock (a := littleEndianBytes 16 P ++ a.toBytes ++ littleEndianBytes 16 d)
    (s := 512) (n := 16) ⟨rest, ?_⟩ ?_ _
  · show _ = hasherInput _ _ _
    simp only [hasherInput, List.append_assoc]
  · rw [List.length_append, List.length_append, length_littleEndianBytes, length_toBytes,
      Quantum.Sphincs.Assembly.length_le16]

/-- A tree node's first block carries its right child. -/
theorem payloadHi_slotBlk_node (P : PublicParameter) (v : ValPos → Digest) (l : Layer)
    (τ : TreeIndex) (height index : ℕ) :
    payloadHi (slotBlk P (.node l τ height index) v 0) =
      v (tpos l τ (height - 1) (2 * index + 1)) := by
  rw [slotBlk_zero]
  have h := payloadHi_addressed P (hashDomainFields (.node l τ height index))
    (v (tpos l τ (height - 1) (2 * index))) (v (tpos l τ (height - 1) (2 * index + 1))) []
  rwa [List.append_nil] at h

/-- A FORS node's first block carries its right child. -/
theorem payloadHi_slotBlk_forsNode (P : PublicParameter) (v : ValPos → Digest) (idx : Index)
    (κ : ForsTreeIndex) (height node : ℕ) :
    payloadHi (slotBlk P (.forsNode idx κ height node) v 0) =
      v (fpos idx κ (height - 1) (2 * node + 1)) := by
  rw [slotBlk_zero]
  have h := payloadHi_addressed P (hashDomainFields (.forsNode idx κ height node))
    (v (fpos idx κ (height - 1) (2 * node))) (v (fpos idx κ (height - 1) (2 * node + 1))) []
  rwa [List.append_nil] at h

end payload

/-! ## The source a first block names -/

section src

/-- **The positions a slot's first block may name**: a tree or FORS node's two children, an
encoding trial's signed value, else the designated source. -/
def srcSet : Slot → Finset ValPos
  | .node l τ height index =>
      {tpos l τ (height - 1) (2 * index), tpos l τ (height - 1) (2 * index + 1)}
  | .forsNode idx κ height node =>
      {fpos idx κ (height - 1) (2 * node), fpos idx κ (height - 1) (2 * node + 1)}
  | .enc l τ e => {msgPos (l, τ, e)}
  | s => {dsrc s}

/-- **The position and value the first block `x` of slot `s` names**, for the disclosed positions
`T`: a node's left child, or its right child when the left one is disclosed; an encoding trial's
signed value; else the designated source. The value is read from the block's payload bits. -/
def slotSrc (T : Finset ValPos) (x : X) : Slot → Option (ValPos × Digest)
  | .chain l τ e i step => some (cpos l τ e i step.val, payloadLo x)
  | .leaf l τ e => some (cpos l τ e ⟨0, by decide⟩ (chainLength - 1), payloadLo x)
  | .node l τ height index =>
      if tpos l τ (height - 1) (2 * index) ∈ T then
        some (tpos l τ (height - 1) (2 * index + 1), payloadHi x)
      else some (tpos l τ (height - 1) (2 * index), payloadLo x)
  | .enc l τ e => some (msgPos (l, τ, e), payloadLo x)
  | .forsLeaf idx κ s => some (.forsSecret idx κ s, payloadLo x)
  | .forsNode idx κ height node =>
      if fpos idx κ (height - 1) (2 * node) ∈ T then
        some (fpos idx κ (height - 1) (2 * node + 1), payloadHi x)
      else some (fpos idx κ (height - 1) (2 * node), payloadLo x)
  | .forsRoots idx => some (fpos idx ⟨0, by decide⟩ forsTreeHeight 0, payloadLo x)
  | _ => none

/-- **The position and value a first block names** for the key `pk` and the disclosed positions
`T`: those of the slot it names (`slotOfBlock`). -/
def cellSrc (pk : PublicKey) (T : Finset ValPos) (x : X) : Option (ValPos × Digest) :=
  (slotOfBlock pk x).bind (slotSrc T x)

/-- An in-table slot's first block names positions its honest path depends on. -/
theorem srcSet_subset_slotNeed {s : Slot} (hs : InTable s) : srcSet s ⊆ slotNeed s := by
  cases s with
  | chain l τ e i step =>
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  | leaf l τ e =>
    exact Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  | node l τ height index =>
    exact Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_self _ _,
      Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
  | forsLeaf idx κ s =>
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
  | forsNode idx κ height node =>
    exact Finset.insert_subset_iff.mpr ⟨Finset.mem_insert_self _ _,
      Finset.singleton_subset_iff.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
  | forsRoots idx =>
    exact Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  | _ => exact hs.elim

/-- **An in-table slot's first block names a source of its value**: at the values `v`, it names a
position `q ∈ srcSet s` and carries `v q`, and `q` is disclosed only if all of `srcSet s` is. -/
theorem cellSrc_slotBlk (P : PublicParameter) (root : Digest) (T : Finset ValPos)
    (v : ValPos → Digest) {s : Slot} (hs : InTable s) :
    ∃ q ∈ srcSet s, cellSrc ⟨P, root⟩ T (slotBlk P s v 0) = some (q, v q) ∧
      (q ∈ T → srcSet s ⊆ T) := by
  have hlo := payloadLo_slotBlk P v hs
  rw [cellSrc, slotOfBlock_slotBlk P root v hs, Option.bind_some]
  cases s with
  | chain l τ e i step =>
    exact ⟨_, Finset.mem_singleton_self _, by rw [slotSrc, hlo]; rfl,
      Finset.singleton_subset_iff.mpr⟩
  | leaf l τ e =>
    exact ⟨_, Finset.mem_singleton_self _, by rw [slotSrc, hlo]; rfl,
      Finset.singleton_subset_iff.mpr⟩
  | node l τ height index =>
    by_cases hT : tpos l τ (height - 1) (2 * index) ∈ T
    · refine ⟨tpos l τ (height - 1) (2 * index + 1),
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_, fun h ↦
          Finset.insert_subset_iff.mpr ⟨hT, Finset.singleton_subset_iff.mpr h⟩⟩
      rw [slotSrc, ite_eq_left hT, payloadHi_slotBlk_node]
    · refine ⟨tpos l τ (height - 1) (2 * index), Finset.mem_insert_self _ _, ?_,
        fun h ↦ absurd h hT⟩
      rw [slotSrc, ite_eq_right hT, hlo]
      rfl
  | forsLeaf idx κ s =>
    exact ⟨_, Finset.mem_singleton_self _, by rw [slotSrc, hlo]; rfl,
      Finset.singleton_subset_iff.mpr⟩
  | forsNode idx κ height node =>
    by_cases hT : fpos idx κ (height - 1) (2 * node) ∈ T
    · refine ⟨fpos idx κ (height - 1) (2 * node + 1),
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_, fun h ↦
          Finset.insert_subset_iff.mpr ⟨hT, Finset.singleton_subset_iff.mpr h⟩⟩
      rw [slotSrc, ite_eq_left hT, payloadHi_slotBlk_forsNode]
    · refine ⟨fpos idx κ (height - 1) (2 * node), Finset.mem_insert_self _ _, ?_,
        fun h ↦ absurd h hT⟩
      rw [slotSrc, ite_eq_right hT, hlo]
      rfl
  | forsRoots idx =>
    exact ⟨_, Finset.mem_singleton_self _, by rw [slotSrc, hlo]; rfl,
      Finset.singleton_subset_iff.mpr⟩
  | _ => exact hs.elim

/-- **A first block whose sources are not all disclosed names an undisclosed one.** -/
theorem exists_cellSrc_of_not_subset (P : PublicParameter) (root : Digest) (T : Finset ValPos)
    (v : ValPos → Digest) {s : Slot} (hs : InTable s) (hT : ¬srcSet s ⊆ T) :
    ∃ q, cellSrc ⟨P, root⟩ T (slotBlk P s v 0) = some (q, v q) ∧ q ∉ T := by
  obtain ⟨q, -, hq, himp⟩ := cellSrc_slotBlk P root T v hs
  exact ⟨q, hq, fun h ↦ hT (himp h)⟩

/-- The first block of the encoding trial `Enc(K, M, c)` under `PK.seed = P`. -/
def encCell (P : PublicParameter) (K : Key) (M : Digest) (c : EncodingCounter) : X :=
  firstCell (addressedHashInput P (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
    (littleEndianBytes 16 M ++ bigEndianBytes 4 c))

/-- **An encoding trial's first block names the value its key signs** and carries the message it
encodes. -/
theorem cellSrc_encCell (P : PublicParameter) (root : Digest) (T : Finset ValPos) (K : Key)
    (M : Digest) (c : EncodingCounter) :
    cellSrc ⟨P, root⟩ T (encCell P K M c) = some (msgPos K, M) := by
  obtain ⟨l, τ, e⟩ := K
  rw [cellSrc, encCell, firstCell, slotOfBlock_addressedHashInput, ite_eq_left rfl,
    slotOfAddress_hashDomainFields _ (by trivial), Option.bind_some]
  show some (msgPos (l, τ, e), payloadLo (firstCell _)) = _
  rw [payloadLo_addressed]

/-- The first block of an honest input. -/
def honestCell (L : HonestTable) (s : Slot) : X :=
  firstCell (slotInput L.publicSeed s (valuePos L))

theorem honestCell_eq_slotBlk (L : HonestTable) (s : Slot) :
    honestCell L s = slotBlk L.publicSeed s (valuePos L) 0 :=
  (slotBlk_zero _ _ _).symm

/-- **The first block of an honest input names its slot.** -/
theorem slotOfBlock_honestCell (L : HonestTable) {s : Slot} (hs : InTable s) :
    slotOfBlock L.publicKey (honestCell L s) = some s := by
  rw [honestCell_eq_slotBlk]
  exact slotOfBlock_slotBlk L.publicSeed L.root (valuePos L) hs

/-- **The honest table's first blocks name a source of their value**: a position `q ∈ srcSet s`
carrying the honest value, disclosed only if all of `srcSet s` is. -/
theorem cellSrc_honestCell (L : HonestTable) (T : Finset ValPos) {s : Slot} (hs : InTable s) :
    ∃ q ∈ srcSet s, cellSrc L.publicKey T (honestCell L s) = some (q, valuePos L q) ∧
      (q ∈ T → srcSet s ⊆ T) := by
  rw [honestCell_eq_slotBlk]
  exact cellSrc_slotBlk L.publicSeed L.root T (valuePos L) hs

end src

/-! ## leanSPHINCS's hidden masses -/

section bound

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **Hidden first blocks of the value positions.** If every hidden `k`-cell that is not hardwired
names, by `cellSrc` for the positions disclosed in the register, an undisclosed position whose
hidden value it carries (`exists_cellSrc_of_not_subset` for the in-table slots, `cellSrc_encCell`
for the encoding trials), the hidden mass is `2^-128` per call on average. -/
theorem sum_queryWeight_cellSrc_le (pk : PublicKey) (m₀ : M) (lab : HwReg X Z M → Finset ValPos)
    (x : (ValPos → Digest) → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : (ValPos → Digest) → Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ v, (ρ v).PosSemidef) (j : ℕ)
    (hview : ViewByOn (D := fun _ : ValPos ↦ Digest) (runtime2 X Z m₀) I
      (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hk : (ValPos → Digest) → Set X)
    (hk : ∀ v y r, y ∈ Hk v → r.2.1.2.1 y = none →
      ∃ q, cellSrc pk (lab r) y = some (q, v q) ∧ q ∉ lab r) :
    ∑ v, (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ (Hk v) ∅) (x v) (ρ v) j ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑ v, ENNReal.ofReal (ρ v).trace.re := by
  refine sum_queryWeight_hiddenK_digest_le I m₀ lab x ρ hρ j hview Hk
    (fun y r ↦ ((cellSrc pk (lab r) y).getD (rootPos, 0)).1)
    (fun y r ↦ ((cellSrc pk (lab r) y).getD (rootPos, 0)).2) fun v y r hy hW ↦ ?_
  obtain ⟨q, hq, hqT⟩ := hk v y r hy hW
  rw [hq]
  exact ⟨hqT, rfl⟩

/-- **Hidden `H_msg` blocks.** With the randomizers `w : Message → Randomizer` hidden and the
messages whose randomizer the register has disclosed `lab r`: if every hidden `k`-cell that is not
hardwired is the block of an `H_msg` call (`hmsgMsg`, `hmsgMsg_hmsgCell`) on a message whose
randomizer is undisclosed and which it holds (`rndOf_hmsgCell`), the hidden mass is `2^-128` per
call on average. -/
theorem sum_queryWeight_hmsg_le (pk : PublicKey) (m₀ : M) (lab : HwReg X Z M → Finset Message)
    (x : (Message → Randomizer) → QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : (Message → Randomizer) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ w, (ρ w).PosSemidef) (j : ℕ)
    (hview : ViewByOn (D := fun _ : Message ↦ Digest) (runtime2 X Z m₀) I
      (fun i ↦ i.isLeft = true) lab x ρ j)
    (Hk : (Message → Randomizer) → Set X)
    (hk : ∀ w y r, y ∈ Hk w → r.2.1.2.1 y = none →
      ∃ msg, hmsgMsg pk y = some msg ∧ msg ∉ lab r ∧ w msg = rndOf y) :
    ∑ w, (runtime2 X Z m₀).queryWeight I (hiddenMass ∅ (Hk w) ∅) (x w) (ρ w) j ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * ∑ w, ENNReal.ofReal (ρ w).trace.re := by
  refine sum_queryWeight_hiddenK_digest_le I m₀ lab x ρ hρ j hview Hk
    (fun y _ ↦ (hmsgMsg pk y).getD 0) (fun y _ ↦ rndOf y) fun w y r hy hW ↦ ?_
  obtain ⟨msg, hmsg, hT, hw⟩ := hk w y r hy hW
  rw [hmsg]
  exact ⟨hT, hw⟩

end bound

end Quantum.Sphincs.Hybrid

end
