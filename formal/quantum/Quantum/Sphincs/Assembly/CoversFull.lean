module

public import Quantum.Sphincs.Assembly.HmsgCovers
public import Quantum.Sphincs.Assembly.MassSources
public import Quantum.Sphincs.Assembly.FullTable
public import Quantum.Sphincs.Assembly.PathsDisjoint

@[expose] public section

/-!
# Runtime 1's table of leanSPHINCS is covered by the hidden sets

Every cell of FullTable's `fullHw L` (the reads of the full honest computation `fullComp`) is a cell
of an in-table path (MassSources' `tabPathH`), of an `SK.seed`-keyed derivation (`seedCovH`: the
key derivations of `SK.prf` and `PK.seed` and the secrets), of a `PRF_msg` call (`prfCovH`,
RStage's randomizer cells) or of an `H_msg` call at the table's randomizer (`hmCovH`)
(`covers_fullHw`).

* **The queries**: FullTable's `queriesSatisfy_fullComp` (every query is a `FullInput`).
* **One-block inputs** (`mem_inputReads_of_blocks`): their reads are the `k`, `k'` and `h` cells of
  their block; the `SK.seed`-keyed inputs (`skCell`), the `PRF_msg` inputs (`rCell`) and the
  `H_msg` inputs (`dLabCell`) are one block.
* **In-table slots** (PathsDisjoint's `point_of_mem_inputReads`): their reads are their paths'
  cells.
-/

open Quantum.SufCma

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput)
open Quantum.Xmss (X Z blocks)
open Quantum.Xmss.Hybrid (capOf rateOf Covers blocks_of_lt)
open Quantum.Xmss.Assembly (mem_inputReads_of_blocks exists_h_of_readsHw exists_k_of_readsHw
  exists_k'_of_readsHw)
open Quantum.Sphincs.Hybrid (DLab skCell SkIdx rCell rCellK rCellK' rCellH length_skInput_lt
  length_prfMessageInput_lt length_messageDigestInput_lt)

namespace Quantum.Sphincs.Assembly

/-! ## The hidden sets of the full table -/

section sets

/-- The `SK.seed`-keyed derivations' `h`-cells. -/
def seedCovH (L : HonestTable) : Set Z :=
  Set.range fun b : SkIdx ↦ capOf L.keys.2.1 L.keys.2.2 L.perm (skCell L.publicSeed L.secretSeed b)

/-- The `SK.seed`-keyed derivations' `k`-cells. -/
def seedCovK (L : HonestTable) : Set X :=
  Set.range fun b : SkIdx ↦ skCell L.publicSeed L.secretSeed b

/-- The `SK.seed`-keyed derivations' `k'`-cells. -/
def seedCovK' (L : HonestTable) : Set X :=
  Set.range fun b : SkIdx ↦ rateOf L.keys.2.1 L.perm (skCell L.publicSeed L.secretSeed b)

/-- The `PRF_msg` calls' `h`-cells. -/
def prfCovH (L : HonestTable) : Set Z :=
  Set.range (rCellH rCell L)

/-- The `PRF_msg` calls' `k`-cells. -/
def prfCovK (L : HonestTable) : Set X :=
  Set.range (rCellK rCell L)

/-- The `PRF_msg` calls' `k'`-cells. -/
def prfCovK' (L : HonestTable) : Set X :=
  Set.range (rCellK' rCell L)

/-- The `H_msg` calls' `h`-cells at the table's randomizers. -/
def hmCovH (L : HonestTable) : Set Z :=
  {z | ∃ (M : Message) (i : DigestCall), hmCellZ (pubOf L) L.root (L.randomizer M) (M, i) = z}

/-- The `H_msg` calls' `k`-cells at the table's randomizers. -/
def hmCovK (L : HonestTable) : Set X :=
  {x | ∃ (M : Message) (i : DigestCall), hmCellK (pubOf L) L.root (L.randomizer M) (M, i) = x}

/-- The `H_msg` calls' `k'`-cells at the table's randomizers. -/
def hmCovK' (L : HonestTable) : Set X :=
  {x | ∃ (M : Message) (i : DigestCall), hmCellR (pubOf L) L.root (L.randomizer M) (M, i) = x}

/-- **The hidden `h`-cells of the full table.** -/
def fullCovH (L : HonestTable) : Set Z :=
  tabPathH L ∪ seedCovH L ∪ prfCovH L ∪ hmCovH L

/-- **The hidden `k`-cells of the full table.** -/
def fullCovK (L : HonestTable) : Set X :=
  tabPathK L ∪ seedCovK L ∪ prfCovK L ∪ hmCovK L

/-- **The hidden `k'`-cells of the full table.** -/
def fullCovK' (L : HonestTable) : Set X :=
  tabPathK' L ∪ seedCovK' L ∪ prfCovK' L ∪ hmCovK' L

end sets

/-! ## The covered reads -/

section covered

/-- A read whose cell is a hidden cell of the full table. -/
def FullReadCov (L : HonestTable) : SpongeRead X Z → Prop
  | .h z _ => z ∈ fullCovH L
  | .k x _ => x ∈ fullCovK L
  | .k' x _ => x ∈ fullCovK' L

variable (L : HonestTable)

/-- **A one-block input's reads are covered** when its block's cells are. -/
theorem fullReadCov_of_blocks {input : HashInput} {b : X} (hb : blocks input = [b])
    (hK : b ∈ fullCovK L) (hR : rateOf L.keys.2.1 L.perm b ∈ fullCovK' L)
    (hH : capOf L.keys.2.1 L.keys.2.2 L.perm b ∈ fullCovH L) {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm input) : FullReadCov L e := by
  rcases mem_inputReads_of_blocks L.perm L.keys hb he with rfl | rfl | rfl
  · exact hK
  · exact hR
  · exact hH

/-- An `SK.seed`-keyed derivation's reads are covered. -/
theorem fullReadCov_seed (b : SkIdx) {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm
      (Quantum.Sphincs.Hybrid.skInput L.publicSeed L.secretSeed b)) : FullReadCov L e :=
  fullReadCov_of_blocks L (blocks_of_lt _ (length_skInput_lt _ _ b))
    (Or.inl (Or.inl (Or.inr ⟨b, rfl⟩))) (Or.inl (Or.inl (Or.inr ⟨b, rfl⟩)))
    (Or.inl (Or.inl (Or.inr ⟨b, rfl⟩))) he

/-- A `PRF_msg` call's reads are covered. -/
theorem fullReadCov_prf (M : Message) {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm (prfMessageInput L.prfKey L.publicSeed M)) :
    FullReadCov L e :=
  fullReadCov_of_blocks L (blocks_of_lt _ (length_prfMessageInput_lt _ _ M))
    (Or.inl (Or.inr ⟨M, rfl⟩)) (Or.inl (Or.inr ⟨M, rfl⟩)) (Or.inl (Or.inr ⟨M, rfl⟩)) he

/-- An `H_msg` call's reads at the table's randomizer are covered. -/
theorem fullReadCov_hmsg (M : Message) (i : DigestCall) {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm
      (slotInput L.publicSeed (.hmsg (L.randomizer M) M i) (valuePos L))) :
    FullReadCov L e := by
  have hin : slotInput L.publicSeed (.hmsg (L.randomizer M) M i) (valuePos L) =
      messageDigestInput (L.randomizer M) L.publicSeed L.root M i := by
    show messageDigestInput _ _ (valuePos L rootPos) _ _ = _
    rw [valuePos_rootPos]
  rw [hin] at he
  exact fullReadCov_of_blocks L (blocks_of_lt _ (length_messageDigestInput_lt _ _ _ M i))
    (Or.inr ⟨M, i, rfl⟩) (Or.inr ⟨M, i, rfl⟩) (Or.inr ⟨M, i, rfl⟩) he

/-- An in-table slot's reads are covered. -/
theorem fullReadCov_slot {s : Slot} (hs : InTable s) {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm (slotInput L.publicSeed s (valuePos L))) :
    FullReadCov L e := by
  obtain ⟨j, hj, h | h | h⟩ := point_of_mem_inputReads L s he <;> cases e <;> cases h
  · exact Or.inl (Or.inl (Or.inl ⟨s, hs, j, hj, rfl⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨s, hs, j, hj, rfl⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨s, hs, j, hj, rfl⟩))

/-- **Every honest input of the full computation has covered reads.** -/
theorem fullReadCov_of_fullInput {input : HashInput} (hi : FullInput L input)
    {e : SpongeRead X Z} (he : e ∈ inputReads L.keys L.perm input) : FullReadCov L e := by
  rcases hi with (rfl | rfl) | ⟨d, -, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨M, rfl⟩ | ⟨M, i, rfl⟩
  · exact fullReadCov_seed L none he
  · exact fullReadCov_seed L (some none) he
  · exact fullReadCov_seed L (some (some d)) he
  · exact fullReadCov_slot L hs he
  · exact fullReadCov_prf L M he
  · exact fullReadCov_hmsg L M i he

/-- **Runtime 1's table is covered**: every cell the full honest computation reads is an in-table
path's, an `SK.seed`-keyed derivation's, a `PRF_msg` call's or an `H_msg` call's. -/
theorem covers_fullHw : Covers (fullHw L) (fullCovH L) (fullCovK L) (fullCovK' L) := by
  have hR : ∀ e ∈ (honestEval L.keys L.perm (fullComp L.secretSeed)).2, FullReadCov L e := by
    intro e he
    rw [snd_honestEval] at he
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp he
    exact fullReadCov_of_fullInput L (queriesSatisfy_fullComp L q hq) he
  refine ⟨fun z hz ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨b, hb⟩ := exists_h_of_readsHw
      (R := (honestEval L.keys L.perm (fullComp L.secretSeed)).2) hz
    exact hR _ hb
  · obtain ⟨b, hb⟩ := exists_k_of_readsHw
      (R := (honestEval L.keys L.perm (fullComp L.secretSeed)).2) hx
    exact hR _ hb
  · obtain ⟨b, hb⟩ := exists_k'_of_readsHw
      (R := (honestEval L.keys L.perm (fullComp L.secretSeed)).2) hx
    exact hR _ hb

end covered

end Quantum.Sphincs.Assembly

end
