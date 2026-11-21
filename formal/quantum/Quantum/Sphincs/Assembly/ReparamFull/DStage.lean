module

public import Quantum.Sphincs.Assembly.ReparamFull.Table
public import Quantum.Sphincs.Assembly.ReparamFull.RateSep

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables: the digest stage after Reparam

The digest stage `dLast` (`Quantum.Sphincs.Assembly.ReparamFull.Coords`) runs on Reparam's
coordinates `y`, viewed as path-stage coordinates `yView y` (`DY`) with first blocks `dcY`: `H_msg`
call `i` on `M` at `PK.seed`, the hidden root (the value at `rootPos`) and the randomizer slot's
first `128` bits. Its labels are the true root's calls only. `zOf y` are the coordinates after the
path stages, where the labels' rates and capacities are read off the coin slots.

* **The charged labels** `dBX`: a label of smaller rank (`pB`), a randomizer-stage capacity
  (`rCapY`, from the randomizer stage's coins) or an `SK.seed`-keyed capacity (`sCapY`, from
  SeedStage's slots) at its capacity.
* **The good set** `DGoodYS y`: distinct rates of the labels' first blocks (`RateInjY`) and no
  round of an in-table path reading a label's cell at the coordinates `zOf y` (`PReadIn`; the
  in-table paths' reads `inReads` are those of PathBad's rounds `rnds xI (xLen P)`).
* **The stage on the good set** (`zOf_spec`): the keys keep their values off the labels' cells;
  the labels' capacities and rates are the paths'; a first label's slot holds the block's output.
  `rnAgree_zOf`: the in-table paths at the coordinates' keys are the paths at Reparam's keys.
  `dLast_h_eq`, `dLast_hiEq`: the final `h` is Reparam's off the labels' capacities and agrees with
  it from bit `256` on everywhere.
* **The table's data** (`FullD t`: the stage good set, `XGood`, `HRateSep`, `DGoodYS (yOf t)`):
  `pubP_kk`, `pubP_perm`, `pubP_seed`; `kPub_hmsg`, `k'Pub_hmsg`; `cells_pubP_eq` (an in-table
  path's cells at the public data are those at Reparam's public data); `hiEq_pubP`; `dig_fullE`
  (the hidden `H_msg` output of a first message at an uncharged label is the table's).
-/

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed truncateHash)
open Quantum.Xmss (X Z out256 trunc128)
open Quantum.Xmss.Hybrid (CoinSlots IsFirst capOf rateOf kCells k'Cells hCells mem_kCells
  mem_k'Cells mem_hCells exists_isFirst)
open Quantum.Xmss.Assembly (fwd fwd_fst_snd fwd_snd XW famK famR famZ rnds mem_rnds rnK rnR rnZ
  RnAgree rnK_congr rnR_congr rnZ_congr rnSt_succ)
open Quantum.Sphincs.Hybrid (PSt DLab dLabCell dLabOrd dLabCell_injective rCell rOrd skCell
  pStages pStages_spec pCellK pCellK' pCellH pB mem_pB pBX PReadGood Secret SeedKS SkIdx Tab
  posOf schemeSplit rB mem_rB rCellH rCellK rCellK' rSplit rSplit_coords rCell_injective
  skCell_ne_rCell rCell_ne_dLabCell skCell_ne_dLabCell seedKStages seedKStages_spec' seedCell
  rSplit_perm)

namespace Quantum.Sphincs.Assembly

/-! ## The digest stage's coordinates -/

section defs

/-- The randomizer stage's capacities at the digest stage's coordinates: from its coins. -/
def rCapY (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) (f : DFk) (M : Message) : Z :=
  (ω.1.2 (rCell M ω.2.1 f.2.2.1.2, f.2.1.1 M)).2 + f.2.1.2.1 M

/-- The `SK.seed`-keyed capacities at the digest stage's coordinates: from SeedStage's slots. -/
def sCapY (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) (f : DFk) (b : SkIdx) : Z :=
  (ω.1.2 (skCell ω.2.1 f.2.2.1.1 b, f.2.2.2.1.1 b)).2 + f.2.2.2.1.2 b

/-- The cells of two families, over abstract index types. Irreducible: its membership does not
unfold the enumeration of the indices. -/
@[irreducible]
noncomputable def famCells {A B : Type} [Fintype A] [Fintype B] (r : A → Z) (s : B → Z) :
    Finset Z :=
  Finset.univ.image r ∪ Finset.univ.image s

theorem card_famCells_le {A B : Type} [Fintype A] [Fintype B] (r : A → Z) (s : B → Z) :
    (famCells r s).card ≤ Fintype.card A + Fintype.card B := by
  unfold famCells
  exact (Finset.card_union_le _ _).trans (add_le_add
    (Finset.card_image_le.trans Finset.card_univ.le)
    (Finset.card_image_le.trans Finset.card_univ.le))

theorem mem_famCells_left {A B : Type} [Fintype A] [Fintype B] (r : A → Z) (s : B → Z) (a : A) :
    r a ∈ famCells r s := by
  unfold famCells
  exact Hybrid.mem_union_image_univ_left _ r a

theorem mem_famCells_right {A B : Type} [Fintype A] [Fintype B] (r : A → Z) (s : B → Z) (b : B) :
    s b ∈ famCells r s := by
  unfold famCells
  exact Hybrid.mem_union_image_univ_right _ s b

/-- The capacities the digest labels' must not take: the randomizer stage's and the
`SK.seed`-keyed ones. -/
noncomputable def dExtraY (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) (f : DFk) :
    Finset Z :=
  famCells (rCapY ω f) (sCapY ω f)

theorem card_dExtraY_le (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) (f : DFk) :
    (dExtraY ω f).card ≤ Fintype.card Message + Fintype.card SkIdx :=
  card_famCells_le _ _

/-- **The charged digest labels** at the coordinates after the path stages. -/
abbrev dBX (z : DY) : Set DLab :=
  pBX dcY dLabOrd dExtraY z

/-- The coordinates after the digest stage's path stages. -/
noncomputable abbrev zOf (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) : DY :=
  pStages dcY dLabOrd (yView y)

/-- The reads of the in-table paths' rounds at the public part `((t, π), (P, v))`: `k` at the
`k`-cell, `k'` at the `k'`-cell, `h` at the `h`-cell of every round of PathBad's family. -/
noncomputable def inReads (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) :
    List (SpongeRead X Z) :=
  (rnds xI (xLen ω.2.1)).toList.flatMap fun r ↦
    [SpongeRead.k (famK ω.1.2 (xBlk ω.2.1 ω.2.2) ω.1.1.1 ω.1.1.2.1 ω.1.1.2.2 r) 0,
      SpongeRead.k' (famR ω.1.2 (xBlk ω.2.1 ω.2.2) ω.1.1.1 ω.1.1.2.1 ω.1.1.2.2 r) 0,
      SpongeRead.h (famZ ω.1.2 (xBlk ω.2.1 ω.2.2) ω.1.1.1 ω.1.1.2.1 ω.1.1.2.2 r) 0]

/-- **No in-table round reads a digest label's cell.** -/
def PReadIn (z : DY) : Prop :=
  PReadGood dcY (fun _ : Unit ↦ inReads) z

/-- **The digest labels' first blocks have distinct rates** before the stage. -/
def RateInjY (x : DY) : Prop :=
  Function.Injective fun a ↦ rateOf x.1.1.1.1.2.1 x.1.1.1.2 (dcY x.1.1.2 x.2 a)

/-- **The digest stage's good set** at Reparam's coordinates. -/
def DGoodYS (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) : Prop :=
  RateInjY (yView y) ∧ PReadIn (zOf y)

theorem dcY_injective (e : DE) (f : DFk) : Function.Injective (dcY e f) := fun a b h ↦
  congrArg Prod.snd (dLabCell_injective e.1 (e.2 rootPos)
    (a₁ := (trunc128 (f.2.1.2.2 a.1), a)) (a₂ := (trunc128 (f.2.1.2.2 b.1), b)) h)

theorem famK_mem_inReads (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) {r : ValPos × ℕ}
    (hr : r ∈ rnds xI (xLen ω.2.1)) :
    famK ω.1.2 (xBlk ω.2.1 ω.2.2) ω.1.1.1 ω.1.1.2.1 ω.1.1.2.2 r ∈ kCells (inReads ω) :=
  mem_kCells.mpr ⟨0, List.mem_flatMap.mpr ⟨r, Finset.mem_toList.mpr hr, by simp⟩⟩

theorem famR_mem_inReads (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) {r : ValPos × ℕ}
    (hr : r ∈ rnds xI (xLen ω.2.1)) :
    famR ω.1.2 (xBlk ω.2.1 ω.2.2) ω.1.1.1 ω.1.1.2.1 ω.1.1.2.2 r ∈ k'Cells (inReads ω) :=
  mem_k'Cells.mpr ⟨0, List.mem_flatMap.mpr ⟨r, Finset.mem_toList.mpr hr, by simp⟩⟩

theorem famZ_mem_inReads (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) {r : ValPos × ℕ}
    (hr : r ∈ rnds xI (xLen ω.2.1)) :
    famZ ω.1.2 (xBlk ω.2.1 ω.2.2) ω.1.1.1 ω.1.1.2.1 ω.1.1.2.2 r ∈ hCells (inReads ω) :=
  mem_hCells.mpr ⟨0, List.mem_flatMap.mpr ⟨r, Finset.mem_toList.mpr hr, by simp⟩⟩

/-- A label whose capacity is an extra capacity is charged. -/
theorem mem_dBX_of_extra {z : DY} {a : DLab} (h : pCellH dcY z a ∈ dExtraY z.1.1 z.2) :
    a ∈ dBX z :=
  Or.inr h

/-- An uncharged label is first. -/
theorem isFirst_of_not_mem_dBX {z : DY} {a : DLab} (h : a ∉ dBX z) :
    IsFirst dLabOrd (pCellH dcY z) a :=
  not_not.mp fun h' ↦ h (Or.inl ((mem_pB _ _).mpr h'))

theorem rCapY_mem (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) (f : DFk) (M : Message) :
    rCapY ω f M ∈ dExtraY ω f :=
  mem_famCells_left _ _ M

theorem sCapY_mem (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) (f : DFk) (b : SkIdx) :
    sCapY ω f b ∈ dExtraY ω f :=
  mem_famCells_right _ _ b

/-- The digest labels' first blocks at Reparam's coordinates. -/
def dcYy (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) (a : DLab) : X :=
  dLabCell a y.1.1.2.1 (y.1.2 rootPos) (trunc128 (y.2.2.2.1.2.2 a.1))

/-- The path stages keep `π`, the kept data `E` and `F`. -/
theorem zOf_keep (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) :
    (zOf y).1.1.1.2 = y.1.1.2.2.1 ∧ (zOf y).1.1.2 = (y.1.1.2.1, y.1.2) ∧
      (zOf y).2 = (y.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2.1, y.2.2.2.2.2.2) :=
  Hybrid.pStages_keep dcY dLabOrd (yView y)

/-- The randomizer stage's capacities at the coordinates after the path stages. -/
theorem rCapY_zOf (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) (M : Message) :
    rCapY (zOf y).1.1 (zOf y).2 M =
      (y.1.1.2.2.1 (rCell M y.1.1.2.1 y.2.2.2.2.1.2, y.2.2.2.1.1 M)).2 + y.2.2.2.1.2.1 M := by
  obtain ⟨e1, e2, e3⟩ := zOf_keep y
  unfold rCapY
  rw [e1, e2, e3]

/-- The `SK.seed`-keyed capacities at the coordinates after the path stages. -/
theorem sCapY_zOf (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) (b : SkIdx) :
    sCapY (zOf y).1.1 (zOf y).2 b =
      (y.1.1.2.2.1 (skCell y.1.1.2.1 y.2.2.2.2.1.1 b, y.2.2.2.2.2.1.1 b)).2 +
        y.2.2.2.2.2.1.2 b := by
  obtain ⟨e1, e2, e3⟩ := zOf_keep y
  unfold sCapY
  rw [e1, e2, e3]

end defs

/-! ## The path stages on the good set, over the coordinates -/

section stage

/-- **The path stages at distinct rates**: the keys keep their values off the labels' cells read
off the coordinates after the stages; there the capacities and rates are the paths' at the keys
before; a first label's slot holds the block's output. -/
theorem pStages_dcY_spec (x : DY) (hrate : RateInjY x) :
    (∀ z, (∀ a, pCellH dcY (pStages dcY dLabOrd x) a ≠ z) →
      (pStages dcY dLabOrd x).1.1.1.1.1 z = x.1.1.1.1.1 z) ∧
    (∀ w, (∀ a, pCellK dcY (pStages dcY dLabOrd x) a ≠ w) →
      (pStages dcY dLabOrd x).1.1.1.1.2.1 w = x.1.1.1.1.2.1 w) ∧
    (∀ w, (∀ a, pCellK' dcY (pStages dcY dLabOrd x) a ≠ w) →
      (pStages dcY dLabOrd x).1.1.1.1.2.2 w = x.1.1.1.1.2.2 w) ∧
    (pStages dcY dLabOrd x).1.1.1.2 = x.1.1.1.2 ∧ (pStages dcY dLabOrd x).1.1.2 = x.1.1.2 ∧
    (pStages dcY dLabOrd x).2 = x.2 ∧
    (∀ a, pCellK dcY (pStages dcY dLabOrd x) a = dcY x.1.1.2 x.2 a) ∧
    (∀ a, pCellH dcY (pStages dcY dLabOrd x) a =
      capOf x.1.1.1.1.2.1 x.1.1.1.1.2.2 x.1.1.1.2 (dcY x.1.1.2 x.2 a)) ∧
    (∀ a, pShY dcY (pStages dcY dLabOrd x) a = rateOf x.1.1.1.1.2.1 x.1.1.1.2 (dcY x.1.1.2 x.2 a)) ∧
    ∀ a, IsFirst dLabOrd (pCellH dcY (pStages dcY dLabOrd x)) a →
      (pStages dcY dLabOrd x).1.2.2.2 a = rateOf x.1.1.1.1.2.1 x.1.1.1.2 (dcY x.1.1.2 x.2 a) +
        x.1.1.1.1.1 (capOf x.1.1.1.1.2.1 x.1.1.1.1.2.2 x.1.1.1.2 (dcY x.1.1.2 x.2 a)) := by
  obtain ⟨⟨⟨⟨t, π⟩, e⟩, cs⟩, f⟩ := x
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, f6, fs⟩ := pStages_spec dcY dLabOrd t π e cs f
  obtain ⟨f1, f2, f3, -, f5, f7⟩ := fs (dcY_injective e f) hrate
  rw [hE]
  have hcap : ∀ a, (π (dcY e f a, cs₂.1 a)).2 + cs₂.2.1 a = capOf t.2.1 t.2.2 π (dcY e f a) :=
    fun a ↦ by rw [f1 a, f2 a]; rfl
  have hfun : (fun b ↦ (π (dcY e f b, cs₂.1 b)).2 + cs₂.2.1 b) =
      fun b ↦ capOf t.2.1 t.2.2 π (dcY e f b) := funext hcap
  refine ⟨f6, f5, f7, rfl, rfl, rfl, fun _ ↦ rfl, hcap, fun a ↦ ?_, fun a ha ↦ ?_⟩
  · show (π (dcY e f a, cs₂.1 a)).1 = _
    rw [f1 a]
    rfl
  · have ha' : IsFirst dLabOrd (fun b ↦ capOf t.2.1 t.2.2 π (dcY e f b)) a := by
      rw [← hfun]
      exact ha
    exact f3 a ha'

/-- **The digest stage after the path stages** (`pFull_eq` at `dcY`): the final `h` is the path
stages' `h` off the first labels' capacities. At distinct rates the final `h` is the `h` before
off every label's capacity, and agrees with it from bit `256` on everywhere. -/
theorem pFull_dcY_h (x : DY) (hrate : RateInjY x) :
    ∃ (h₃ : Z → X) (hc₃ : DLab → X), pFull dcY dLabOrd x = setHC x h₃ hc₃ ∧
      (∀ a, out256 (hc₃ a) = out256 ((pStages dcY dLabOrd x).1.2.2.2 a)) ∧
      (∀ z, (∀ a, pCellH dcY (pStages dcY dLabOrd x) a ≠ z) → h₃ z = x.1.1.1.1.1 z) ∧
      ∀ z, HiEq (h₃ z) (x.1.1.1.1.1 z) := by
  obtain ⟨h₃, hc₃, e, f1, f2, f3⟩ := pFull_eq dcY dLabOrd x
  obtain ⟨s1, -, -, -, -, -, -, s8, s9, s10⟩ := pStages_dcY_spec x hrate
  refine ⟨h₃, hc₃, e, f1, fun z hz ↦ (f3 z fun a _ ↦ hz a).trans (s1 z hz), fun z ↦ ?_⟩
  by_cases hc : ∃ a, IsFirst dLabOrd (pCellH dcY (pStages dcY dLabOrd x)) a ∧
      pCellH dcY (pStages dcY dLabOrd x) a = z
  · obtain ⟨a, ha, rfl⟩ := hc
    rw [f2 a ha, s10 a ha, s9 a, add_add_cancel_X, s8 a]
    exact hiEq_hiMix _ _
  · have hz : ∀ a, pCellH dcY (pStages dcY dLabOrd x) a ≠ z := fun a h ↦ by
      obtain ⟨a', ha', he⟩ := exists_isFirst dLabOrd (pCellH dcY (pStages dcY dLabOrd x)) a
      exact hc ⟨a', ha', he.trans h⟩
    rw [f3 z fun a _ ↦ hz a, s1 z hz]
    exact HiEq.refl _

/-- **The in-table paths at the keys after the path stages are those at the keys before**: no
round reads a label's cell (`PReadIn`), and the keys keep their values off them. -/
theorem rnAgree_zOf (x : DY) (hrate : RateInjY x) (hr : PReadIn (pStages dcY dLabOrd x))
    {p : ValPos} (hp : p ∈ xI) {j : ℕ} (hj : j ≤ xLen x.1.1.2.1 p) :
    RnAgree x.1.1.1.2 (pStages dcY dLabOrd x).1.1.1.1.1 (pStages dcY dLabOrd x).1.1.1.1.2.1
      (pStages dcY dLabOrd x).1.1.1.1.2.2 x.1.1.1.1.1 x.1.1.1.1.2.1 x.1.1.1.1.2.2
      (xBlk x.1.1.2.1 x.1.1.2.2 p) j := by
  obtain ⟨s1, s2, s3, s4, s5, -⟩ := pStages_dcY_spec x hrate
  intro i hi
  have hmem : (p, i) ∈ rnds xI (xLen (pStages dcY dLabOrd x).1.1.2.1) := by
    rw [s5]
    exact mem_rnds.mpr ⟨hp, show i < xLen x.1.1.2.1 p by omega⟩
  have mk := famK_mem_inReads (pStages dcY dLabOrd x).1.1 hmem
  have mk' := famR_mem_inReads (pStages dcY dLabOrd x).1.1 hmem
  have mh := famZ_mem_inReads (pStages dcY dLabOrd x).1.1 hmem
  rw [s4, s5] at mk mk' mh
  refine ⟨(s2 _ fun a h ↦ (hr () a).1 (h ▸ mk)).symm,
    (s3 _ fun a h ↦ (hr () a).2.1 (h ▸ mk')).symm, (s1 _ fun a h ↦ (hr () a).2.2 (h ▸ mh)).symm⟩

/-- The in-table paths' `h`-cells at the keys before the stages avoid the labels' capacities. -/
theorem famZ_ne_pCellH (x : DY) (hrate : RateInjY x) (hr : PReadIn (pStages dcY dLabOrd x))
    {p : ValPos} (hp : p ∈ xI) {j : ℕ} (hj : j < xLen x.1.1.2.1 p) (a : DLab) :
    pCellH dcY (pStages dcY dLabOrd x) a ≠
      rnZ x.1.1.1.2 x.1.1.1.1.1 x.1.1.1.1.2.1 x.1.1.1.1.2.2 (xBlk x.1.1.2.1 x.1.1.2.2 p) j := by
  obtain ⟨-, -, -, s4, s5, -⟩ := pStages_dcY_spec x hrate
  have hA := rnAgree_zOf x hrate hr hp (j := j + 1) (by omega)
  have e : rnZ x.1.1.1.2 x.1.1.1.1.1 x.1.1.1.1.2.1 x.1.1.1.1.2.2 (xBlk x.1.1.2.1 x.1.1.2.2 p) j =
      rnZ x.1.1.1.2 (pStages dcY dLabOrd x).1.1.1.1.1 (pStages dcY dLabOrd x).1.1.1.1.2.1
        (pStages dcY dLabOrd x).1.1.1.1.2.2 (xBlk x.1.1.2.1 x.1.1.2.2 p) j :=
    rnZ_congr (fun i hi ↦ hA i (by omega)) (hA j (Nat.lt_succ_self j)).1
      (hA j (Nat.lt_succ_self j)).2.1
  have hmem : (p, j) ∈ rnds xI (xLen (pStages dcY dLabOrd x).1.1.2.1) := by
    rw [s5]
    exact mem_rnds.mpr ⟨hp, hj⟩
  have mh := famZ_mem_inReads (pStages dcY dLabOrd x).1.1 hmem
  rw [s4, s5] at mh
  intro h
  exact (hr () a).2.2 (by rw [h, e]; exact mh)

/-- `famZ_ne_pCellH` at Reparam's coordinates. -/
theorem famZ_ne_pCellH_y (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) (hy : DGoodYS y)
    {p : ValPos} (hp : p ∈ xI) {j : ℕ} (hj : j < xLen y.1.1.2.1 p) (a : DLab) :
    pCellH dcY (zOf y) a ≠
      rnZ y.1.1.2.2.1 y.1.1.1 y.1.1.2.2.2.1 y.1.1.2.2.2.2 (xBlk y.1.1.2.1 y.1.2 p) j :=
  famZ_ne_pCellH (yView y) hy.1 hy.2 hp hj a

/-- **The path stages at Reparam's coordinates**: the labels' capacities, and the first labels'
slots. -/
theorem zOf_spec (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF)
    (hrate : RateInjY (yView y)) :
    (∀ a, pCellH dcY (zOf y) a = capOf y.1.1.2.2.2.1 y.1.1.2.2.2.2 y.1.1.2.2.1 (dcYy y a)) ∧
    ∀ a, IsFirst dLabOrd (pCellH dcY (zOf y)) a → (zOf y).1.2.2.2 a =
      rateOf y.1.1.2.2.2.1 y.1.1.2.2.1 (dcYy y a) +
        y.1.1.1 (capOf y.1.1.2.2.2.1 y.1.1.2.2.2.2 y.1.1.2.2.1 (dcYy y a)) := by
  obtain ⟨-, -, -, -, -, -, -, s8, -, s10⟩ := pStages_dcY_spec (yView y) hrate
  exact ⟨s8, s10⟩

end stage

/-! ## The digest stage at Reparam's coordinates -/

section ys

/-- **The digest stage at Reparam's coordinates**: only `h` and the digest slots change; the slots
keep the first `256` bits of the path stages'; at distinct rates the final `h` is Reparam's off the
labels' capacities, and agrees with it from bit `256` on everywhere. -/
theorem dLast_spec (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF)
    (hrate : RateInjY (yView y)) :
    ∃ (h₃ : Z → X) (hc₃ : DLab → X),
      dLast y = (((h₃, y.1.1.2), y.1.2), (y.2.1, (y.2.2.1.1, y.2.2.1.2.1, hc₃), y.2.2.2)) ∧
      (∀ a, out256 (hc₃ a) = out256 ((zOf y).1.2.2.2 a)) ∧
      (∀ z, (∀ a, pCellH dcY (zOf y) a ≠ z) → h₃ z = y.1.1.1 z) ∧
      ∀ z, HiEq (h₃ z) (y.1.1.1 z) := by
  obtain ⟨h₃, hc₃, e, f1, f2, f3⟩ := pFull_dcY_h (yView y) hrate
  refine ⟨h₃, hc₃, ?_, f1, f2, f3⟩
  show yView.symm (pFull dcY dLabOrd (yView y)) = _
  rw [e]
  rfl

end ys

/-! ## The table's data at the coordinates -/

/-- The output cell of the honest outputs, as a round's `h`-cell. -/
theorem sOcap_eq (w : XW) (h : Z → X) (v : ValPos → Digest) (s : ValPos) :
    sO.cap w h v s = rnZ w.2.1 h w.2.2.1 w.2.2.2 (xBlk w.1 v s) (xLen w.1 s - 1) :=
  rfl

section table

/-- **The good set of the table's data**: the stage good set, Reparam's good set, `HRateSep` and
the digest stage's good set at Reparam's coordinates. -/
def FullD (t : FT) : Prop :=
  StageGood t ∧ XGood (phiE t).1 ∧ HRateSep (schemeSplit t.1.1.1.1.1) ∧ DGoodYS (yOf t)

variable {t : FT}

/-- The hidden randomizers are the first `128` bits of the randomizer slots. -/
theorem fullE_rnd (M : Message) :
    (fullE t).2.1 (.rnd M) = trunc128 ((phiE t).2.2.2.1.2.2 M) := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq (yOf t)
  show (psiE (dLast (yOf t))).2.1 (.rnd M) = _
  rw [e]
  rfl

/-- Reparam's coordinates of a padded table. -/
theorem yOf_eq (t : FT) : yOf t = (fwd sphFix sO (phiE t).1, (phiE t).2) :=
  rfl

/-- The composed reparametrization through the digest stage. -/
theorem fullE_eq (t : FT) : fullE t = psiE (dLast (yOf t)) :=
  rfl

theorem pubP_psiE (x : (((Z → X) × XW) × (ValPos → Digest)) × RestF) :
    pubP (psiE x).1 = sPub x.1.1.2 x.1.1.1 :=
  rfl

theorem psiE_dig (x : (((Z → X) × XW) × (ValPos → Digest)) × RestF) (M : Message)
    (i : DigestCall) : (psiE x).2.1 (.dig M i) = out256 (x.2.2.1.2.2 (M, i)) :=
  rfl

/-- Reparam's public data at the coordinates. -/
theorem yOf_xw : (yOf t).1.1.2 = (phiE t).1.2 := by
  rw [yOf_eq]
  exact Quantum.Xmss.Assembly.fwd_fst_snd sphFix sO _

/-- Reparam's public `h` at the coordinates. -/
theorem yOf_h : (yOf t).1.1.1 = (fwd sphFix sO (phiE t).1).1.1 := by
  rw [yOf_eq]

/-- Reparam's values at the coordinates. -/
theorem yOf_v : (yOf t).1.2 = (fwd sphFix sO (phiE t).1).2 := by
  rw [yOf_eq]

/-- The rest of the coordinates. -/
theorem yOf_snd : (yOf t).2 = (phiE t).2 := by
  rw [yOf_eq]

/-- The digest stage keeps the public data without `h`. -/
theorem dLast_xw (y : (((Z → X) × XW) × (ValPos → Digest)) × RestF) :
    (dLast y).1.1.2 = y.1.1.2 := by
  obtain ⟨h₃, hc₃, e⟩ := dLast_eq y
  rw [e]

/-- **The public data** at distinct digest rates: `h` agrees with Reparam's off the labels'
capacities, and from bit `256` on everywhere. -/
theorem pubP_fullE (hrate : RateInjY (yView (yOf t))) :
    ∃ h₃ : Z → X, pubP (fullE t).1 = sPub (phiE t).1.2 h₃ ∧
      (∀ z, (∀ a, pCellH dcY (zOf (yOf t)) a ≠ z) → h₃ z = (fwd sphFix sO (phiE t).1).1.1 z) ∧
      ∀ z, HiEq (h₃ z) ((fwd sphFix sO (phiE t).1).1.1 z) := by
  obtain ⟨h₃, hc₃, e, -, f2, f3⟩ := dLast_spec (yOf t) hrate
  rw [yOf_h] at f2 f3
  refine ⟨h₃, ?_, f2, f3⟩
  have hh : (dLast (yOf t)).1.1.1 = h₃ := by rw [e]
  rw [fullE_eq, pubP_psiE, dLast_xw, yOf_xw, hh]

/-- The public data without `h` at any digest rates. -/
theorem pubP_fullE_any : ∃ h₃ : Z → X, pubP (fullE t).1 = sPub (phiE t).1.2 h₃ := by
  refine ⟨(dLast (yOf t)).1.1.1, ?_⟩
  rw [fullE_eq, pubP_psiE, dLast_xw, yOf_xw]

/-- **The public data without `h`** are Reparam's. -/
theorem pubP_xw : (pubP (fullE t).1).xw = (phiE t).1.2 := by
  obtain ⟨h₃, e⟩ := pubP_fullE_any (t := t)
  rw [e, sPub_xw]

theorem pubP_kk : (pubP (fullE t).1).keys.2 = ((phiE t).1.2.2.2.1, (phiE t).1.2.2.2.2) := by
  obtain ⟨h₃, e⟩ := pubP_fullE_any (t := t)
  rw [e]
  rfl

/-- The public data's `π` is the table's. -/
theorem pubP_perm : (pubP (fullE t).1).perm = (tabOf t).perm := by
  obtain ⟨h₃, e⟩ := pubP_fullE_any (t := t)
  rw [e]
  exact wPub_perm

/-- The public data's `PK.seed` is the table's. -/
theorem pubP_seed (ht : StageGood t) : (pubP (fullE t).1).seed = (tabOf t).publicSeed := by
  obtain ⟨h₃, e⟩ := pubP_fullE_any (t := t)
  rw [e]
  exact wPub_seed ht

/-- **The public `h` agrees with the table's from bit `256` on.** -/
theorem hiEq_pubP (ht : FullD t) (z : Z) :
    HiEq ((pubP (fullE t).1).keys.1 z) ((tabOf t).keys.1 z) := by
  obtain ⟨h₃, e, -, f3⟩ := pubP_fullE ht.2.2.2.1
  rw [e, sPub_keys_fst]
  exact (f3 z).trans ((hiEq_fwd (phiE t).1 z).trans (by rw [hPre_eq]; exact dFull_hiEq ht.1.1 z))

/-- **The public `k` is the table's at every `H_msg` cell.** -/
theorem kPub_hmsg (ht : StageGood t) (a : DLab) (root : Digest) (R : Randomizer) :
    (phiE t).1.2.2.2.1 (dLabCell a (tabOf t).publicSeed root R) =
      (tabOf t).keys.2.1 (dLabCell a (tabOf t).publicSeed root R) :=
  kPub_eq ht _ (fun M h ↦ rCell_ne_dLabCell M _ _ a _ _ _ h)
    (fun b h ↦ skCell_ne_dLabCell _ _ b a _ _ _ h)

/-- **The public `k'` is the table's at every `H_msg` rate.** -/
theorem k'Pub_hmsg (ht : StageGood t) (hrs : HRateSep (schemeSplit t.1.1.1.1.1)) (a : DLab)
    (root : Digest) (R : Randomizer) :
    (phiE t).1.2.2.2.2
        (rateOf (tabOf t).keys.2.1 (tabOf t).perm (dLabCell a (tabOf t).publicSeed root R)) =
      (tabOf t).keys.2.2
        (rateOf (tabOf t).keys.2.1 (tabOf t).perm (dLabCell a (tabOf t).publicSeed root R)) := by
  have hsep := hRateSep_table (posOf_injective_of_dGood ht.1) hrs a root R
  exact k'Pub_eq ht _ (fun M h ↦ hsep.1 M h.symm) (fun b h ↦ hsep.2 b h.symm)

/-- An in-table slot's path at the public data is the path at Reparam's public data. -/
theorem cells_sPub_congr {w : XW} {h h' : Z → X} {b : ℕ → X} {j : ℕ}
    (hag : ∀ i ≤ j, h' (rnZ w.2.1 h w.2.2.1 w.2.2.2 b i) = h (rnZ w.2.1 h w.2.2.1 w.2.2.2 b i))
    (last : ℕ) (cor : X → X → X) :
    cellK (sPub w h') b j = cellK (sPub w h) b j ∧ cellK' (sPub w h') b j = cellK' (sPub w h) b j ∧
      cellH (sPub w h') b last cor j = cellH (sPub w h) b last cor j := by
  have hR : RnAgree w.2.1 h w.2.2.1 w.2.2.2 h' w.2.2.1 w.2.2.2 b (j + 1) :=
    fun i hi ↦ ⟨rfl, rfl, hag i (by omega)⟩
  have hRj : RnAgree w.2.1 h w.2.2.1 w.2.2.2 h' w.2.2.1 w.2.2.2 b j := fun i hi ↦ hR i (by omega)
  have eK := rnK_congr hRj
  have eR := rnR_congr hRj rfl
  have eZ := rnZ_congr hRj rfl rfl
  refine ⟨Prod.ext eK (congrArg w.2.2.1 eK), Prod.ext eR (congrArg w.2.2.2 eR),
    Prod.ext ((cellH_fst (sPub w h') b last cor j).trans
      (eZ.trans (cellH_fst (sPub w h) b last cor j).symm)) ?_⟩
  rw [cellH_snd, cellH_snd]
  have eH : h' (rnZ w.2.1 h' w.2.2.1 w.2.2.2 b j) = h (rnZ w.2.1 h w.2.2.1 w.2.2.2 b j) := by
    rw [eZ]
    exact hag j le_rfl
  split_ifs
  · show cor (rnR w.2.1 h' w.2.2.1 w.2.2.2 b j) (h' (rnZ w.2.1 h' w.2.2.1 w.2.2.2 b j)) =
      cor (rnR w.2.1 h w.2.2.1 w.2.2.2 b j) (h (rnZ w.2.1 h w.2.2.1 w.2.2.2 b j))
    rw [eR, eH]
  · exact eH

/-- **An in-table slot's cells at the public data are those at Reparam's public data**: the
public `h` is Reparam's on its path's `h`-cells. -/
theorem cells_pubP_eq (ht : FullD t) {s : Slot} (hs : InTable s) (cor : X → X → X) {j : ℕ}
    (hj : j < nBlk (phiE t).1.2.1 s) :
    cellK (pubP (fullE t).1) (slotBlk (phiE t).1.2.1 s (fwd sphFix sO (phiE t).1).2) j =
        cellK (sPub (phiE t).1.2 (fwd sphFix sO (phiE t).1).1.1)
          (slotBlk (phiE t).1.2.1 s (fwd sphFix sO (phiE t).1).2) j ∧
      cellK' (pubP (fullE t).1) (slotBlk (phiE t).1.2.1 s (fwd sphFix sO (phiE t).1).2) j =
        cellK' (sPub (phiE t).1.2 (fwd sphFix sO (phiE t).1).1.1)
          (slotBlk (phiE t).1.2.1 s (fwd sphFix sO (phiE t).1).2) j ∧
      cellH (pubP (fullE t).1) (slotBlk (phiE t).1.2.1 s (fwd sphFix sO (phiE t).1).2)
          (nBlk (phiE t).1.2.1 s - 1) cor j =
        cellH (sPub (phiE t).1.2 (fwd sphFix sO (phiE t).1).1.1)
          (slotBlk (phiE t).1.2.1 s (fwd sphFix sO (phiE t).1).2) (nBlk (phiE t).1.2.1 s - 1)
          cor j := by
  obtain ⟨-, -, -, hrate, hr⟩ := ht
  obtain ⟨h₃, e, f2, -⟩ := pubP_fullE hrate
  rw [e]
  have hp : slotOutPos s ∈ xI := mem_xI.mpr (inPos_slotOutPos hs)
  have hb : xBlk (phiE t).1.2.1 (fwd sphFix sO (phiE t).1).2 (slotOutPos s) =
      slotBlk (phiE t).1.2.1 s (fwd sphFix sO (phiE t).1).2 := by
    unfold xBlk
    rw [outSlot_slotOutPos hs]
  have hl : xLen (phiE t).1.2.1 (slotOutPos s) = nBlk (phiE t).1.2.1 s := by
    unfold xLen
    rw [outSlot_slotOutPos hs]
  refine cells_sPub_congr (fun i hi ↦ f2 _ fun a ↦ ?_) _ cor
  have h := famZ_ne_pCellH_y (yOf t) ⟨hrate, hr⟩ hp (j := i) (by
    rw [yOf_xw, hl]
    omega) a
  rw [yOf_xw] at h
  rw [yOf_v, yOf_h, hb] at h
  exact h

/-- SeedStage's slots in the rest of Reparam's coordinates. -/
theorem phiE_seedKS (t : FT) :
    (phiE t).2.2.2.2.2.1 =
      (seedKStages (((dFull t.1.1.1).1.1, (dFull t.1.1.1).2.2), t.1.1.2)).2 := by
  rw [phiE_apply, stagesE_apply]
  rfl

/-- **SeedStage's slots hold the table's `k` and `k'`** on the `SK.seed`-keyed paths. -/
theorem seedSlots_table (ht : StageGood t) (b : SkIdx) :
    (phiE t).2.2.2.2.2.1.1 b =
        (tabOf t).keys.2.1 (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) ∧
      (phiE t).2.2.2.2.2.1.2 b = (tabOf t).keys.2.2 (rateOf (tabOf t).keys.2.1 (tabOf t).perm
        (skCell (tabOf t).publicSeed (tabOf t).secretSeed b)) := by
  obtain ⟨k₂, k'₂, sk₂, hE, f1, -, f3⟩ :=
    seedKStages_spec' (((dFull t.1.1.1).1.1, (dFull t.1.1.1).2.2), t.1.1.2)
  have e : (phiE t).2.2.2.2.2.1 = sk₂ := by rw [phiE_seedKS, hE]
  have hcell : ∀ b, seedCell ((dFull t.1.1.1).1.1, (dFull t.1.1.1).2.2) b =
      skCell (tabOf t).publicSeed (tabOf t).secretSeed b := fun b ↦ by
    show skCell (trunc128 (dFull t.1.1.1).1.1.2.2.1) (dFull t.1.1.1).2.2.1 b = _
    rw [dFull_slot1 ht.1, dFull_secret]
  have hk : ∀ b, (dFull t.1.1.1).1.1.1.1.2.1 (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) =
      (tabOf t).keys.2.1 (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) := fun b ↦ by
    rw [dFull_kk']
    exact rSplit_k_of_dGood ht.1 _ fun M h ↦ skCell_ne_rCell _ _ b M _ h.symm
  have hr : ∀ b, rateOf (dFull t.1.1.1).1.1.1.1.2.1 (dFull t.1.1.1).1.1.1.2
      (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) =
      rateOf (tabOf t).keys.2.1 (tabOf t).perm
        (skCell (tabOf t).publicSeed (tabOf t).secretSeed b) := fun b ↦ by
    rw [dFull_kk', dFull_perm]
    have h := rateOf_rSplit_seed ht.1 b
    rw [rSplit_perm] at h
    exact h
  have hinj : Function.Injective fun b ↦ rateOf (dFull t.1.1.1).1.1.1.1.2.1
      (dFull t.1.1.1).1.1.1.2 (seedCell ((dFull t.1.1.1).1.1, (dFull t.1.1.1).2.2) b) :=
    fun b b' h ↦ (Quantum.Sphincs.Hybrid.seedKGood_paths ht.2).2.2.2
      (by simpa only [hcell, hr] using h)
  have hk' : (dFull t.1.1.1).1.1.1.1.2.2 (rateOf (tabOf t).keys.2.1 (tabOf t).perm
      (skCell (tabOf t).publicSeed (tabOf t).secretSeed b)) =
      (tabOf t).keys.2.2 (rateOf (tabOf t).keys.2.1 (tabOf t).perm
        (skCell (tabOf t).publicSeed (tabOf t).secretSeed b)) := by
    rw [dFull_kk']
    exact rSplit_k'_of_dGood ht.1 _ fun M ↦ rRate_ne_seedRate_of_dGood ht.1 M b
  rw [e]
  refine ⟨(f1 b).trans ?_, ((f3 hinj).1 b).trans ?_⟩
  · show (dFull t.1.1.1).1.1.1.1.2.1 (seedCell ((dFull t.1.1.1).1.1, (dFull t.1.1.1).2.2) b) = _
    rw [hcell, hk]
  · show (dFull t.1.1.1).1.1.1.1.2.2 (rateOf (dFull t.1.1.1).1.1.1.1.2.1 (dFull t.1.1.1).1.1.1.2
      (seedCell ((dFull t.1.1.1).1.1, (dFull t.1.1.1).2.2) b)) = _
    rw [hcell, hr, hk']

/-- The randomizer coin slots and the secret in the rest of Reparam's coordinates. -/
theorem phiE_rest (t : FT) :
    (phiE t).2.2.2.1 = (dFull t.1.1.1).2.1 ∧ (phiE t).2.2.2.2.1 = (dFull t.1.1.1).2.2 := by
  obtain ⟨k₂, k'₂, sk₂, -, he2, -⟩ := phiE_spec t
  rw [he2]
  exact ⟨rfl, rfl⟩

/-- **The hidden `H_msg` output of a first message at an uncharged label is the table's.** -/
theorem dig_fullE (ht : FullD t) (M : Message) (i : DigestCall)
    (hM : M ∉ rB rCell rOrd (tabOf t)) (ha : (M, i) ∉ dBX (zOf (yOf t))) :
    (fullE t).2.1 (.dig M i) = (tabOf t).digestOutput M i := by
  obtain ⟨hs, hθ, hrs, hrate, hr⟩ := ht
  obtain ⟨h₃, hc₃, e, f1, -, -⟩ := dLast_spec (yOf t) hrate
  obtain ⟨z8, z10⟩ := zOf_spec (yOf t) hrate
  have hrest := phiE_rest t
  set L := tabOf t with hL
  set b0 := dLabCell (M, i) L.publicSeed L.root (L.randomizer M) with hb0
  have hy1 : (yOf t).1.1.2 = (phiE t).1.2 := yOf_xw
  have hv := yOf_v (t := t)
  have hh0 := yOf_h (t := t)
  -- the label's first block is the table's `H_msg` cell
  have hroot : (fwd sphFix sO (phiE t).1).2 rootPos = L.root := by
    rw [Quantum.Xmss.Assembly.fwd_snd sphFix sO]
    exact (fullE_val rootPos).symm.trans (root_fullE hs)
  have hrnd : trunc128 ((phiE t).2.2.2.1.2.2 M) = L.randomizer M :=
    (fullE_rnd M).symm.trans (rnd_fullE hs M hM)
  have hc : dcYy (yOf t) (M, i) = b0 := by
    show dLabCell (M, i) (yOf t).1.1.2.1 ((yOf t).1.2 rootPos)
      (trunc128 ((yOf t).2.2.2.1.2.2 M)) = _
    rw [hy1, hv, yOf_snd, wPub_seed hs, hroot, hrnd]
  -- the keys before the stage at the cell are the table's
  have hπ : (phiE t).1.2.2.1 = L.perm := wPub_perm
  have hk := kPub_hmsg hs (M, i) L.root (L.randomizer M)
  have hk' := k'Pub_hmsg hs hrs (M, i) L.root (L.randomizer M)
  have hrate0 : rateOf (phiE t).1.2.2.2.1 (phiE t).1.2.2.1 b0 = rateOf L.keys.2.1 L.perm b0 := by
    unfold rateOf
    rw [hπ, hk]
  have hcap0 : capOf (phiE t).1.2.2.2.1 (phiE t).1.2.2.2.2 (phiE t).1.2.2.1 b0 =
      capOf L.keys.2.1 L.keys.2.2 L.perm b0 := by
    show ((phiE t).1.2.2.1 (b0, (phiE t).1.2.2.2.1 b0)).2 +
        (phiE t).1.2.2.2.2 (rateOf (phiE t).1.2.2.2.1 (phiE t).1.2.2.1 b0) = _
    rw [hrate0, hk', hπ, hk]
    rfl
  -- the label is first and uncharged
  have hfirst := isFirst_of_not_mem_dBX ha
  have hcapZ : pCellH dcY (zOf (yOf t)) (M, i) = capOf L.keys.2.1 L.keys.2.2 L.perm b0 := by
    rw [z8, hc, hy1]
    exact hcap0
  have hext : capOf L.keys.2.1 L.keys.2.2 L.perm b0 ∉
      dExtraY (zOf (yOf t)).1.1 (zOf (yOf t)).2 :=
    fun h ↦ ha (mem_dBX_of_extra (z := zOf (yOf t)) (a := (M, i)) (by rw [hcapZ]; exact h))
  -- the randomizer stage's capacities at the coordinates are the table's
  have hcoins := dFull_coins (θ := t.1.1.1)
  have hRco := rSplit_coords rCell_injective (rGood_of_dGood hs.1)
  have hrcap : ∀ M', rCapY (zOf (yOf t)).1.1 (zOf (yOf t)).2 M' = rCellH rCell L M' := by
    intro M'
    rw [rCapY_zOf, hy1, yOf_snd, hrest.1, hrest.2, hπ, wPub_seed hs, dFull_secret,
      hcoins.2.2.1, hcoins.2.2.2, hRco.2.1 M', hRco.2.2.1 M']
    rfl
  have hR : ∀ M', rCellH rCell L M' ≠ capOf L.keys.2.1 L.keys.2.2 L.perm b0 := fun M' h ↦
    hext (by rw [← h, ← hrcap M']; exact rCapY_mem _ _ M')
  -- the `SK.seed`-keyed capacities at the coordinates are the table's
  have hscap : ∀ b, sCapY (zOf (yOf t)).1.1 (zOf (yOf t)).2 b =
      posOf (schemeSplit t.1.1.1.1.1).1 (schemeSplit t.1.1.1.1.1).2 b := by
    intro b
    obtain ⟨g1, g2⟩ := seedSlots_table hs b
    rw [sCapY_zOf, hy1, yOf_snd, g1, g2, hrest.2, dFull_secret, wPub_seed hs, hπ,
      posOf_of_dGood hs.1]
    rfl
  have hS : ∀ b, posOf (schemeSplit t.1.1.1.1.1).1 (schemeSplit t.1.1.1.1.1).2 b ≠
      capOf L.keys.2.1 L.keys.2.2 L.perm b0 := fun b h ↦
    hext (by rw [← h, ← hscap b]; exact sCapY_mem _ _ b)
  -- the output caps of the in-table paths avoid the label's capacity
  have hO : ∀ s ∈ sO.I, sO.cap (phiE t).1.2 (phiE t).1.1.1
      (sO.val (phiE t).1.2 (phiE t).1.1.1 (phiE t).1.1.2) s ≠
        capOf L.keys.2.1 L.keys.2.2 L.perm b0 := fun s hs' h ↦ by
    rw [← Quantum.Xmss.Assembly.cap_fwd (F := sphFix) (good_of_xGood hθ) hs', sOcap_eq,
      Quantum.Xmss.Assembly.fwd_fst_snd sphFix sO] at h
    have hl := nBlk_pos (phiE t).1.2.1 (outSlot s)
    have h2 := famZ_ne_pCellH_y (yOf t) ⟨hrate, hr⟩ hs' (j := xLen (yOf t).1.1.2.1 s - 1)
      (by rw [yOf_xw]; unfold xLen; omega) (M, i)
    rw [yOf_xw, yOf_h, yOf_v] at h2
    exact h2 (hcapZ.trans h.symm)
  have hh : (fwd sphFix sO (phiE t).1).1.1 (capOf L.keys.2.1 L.keys.2.2 L.perm b0) =
      L.keys.1 (capOf L.keys.2.1 L.keys.2.2 L.perm b0) := by
    rw [Quantum.Xmss.Assembly.fwd_fst_fst_of_ne sphFix sO _ hO, hPre_eq]
    exact dFull_h_eq hs.1 _ hS hR
  -- the slot
  rw [fullE_eq, psiE_dig, e]
  show out256 (hc₃ (M, i)) = _
  rw [f1 (M, i), z10 (M, i) hfirst, hc, hy1, hh0, hrate0, hcap0, hh, HonestTable.digestOutput,
    Quantum.Sphincs.Hybrid.hash_of_lt _ _
      (Quantum.Sphincs.Hybrid.length_messageDigestInput_lt _ _ _ _ _)]
  rfl

/-- The template's values at the coordinates are Reparam's. -/
theorem valsOf_fullE : valsOf (fullE t).2.1 = (fwd sphFix sO (phiE t).1).2 := by
  rw [Quantum.Xmss.Assembly.fwd_snd sphFix sO]
  exact funext fun q ↦ fullE_val q

/-- **The public `h` is Reparam's on the in-table rounds' `h`-cells.** -/
theorem rnAgree_pubP (ht : FullD t) {h₃ : Z → X}
    (f2 : ∀ z, (∀ a, pCellH dcY (zOf (yOf t)) a ≠ z) → h₃ z = (fwd sphFix sO (phiE t).1).1.1 z)
    {p : ValPos} (hp : p ∈ xI) {j : ℕ} (hj : j ≤ xLen (phiE t).1.2.1 p) :
    RnAgree (phiE t).1.2.2.1 (fwd sphFix sO (phiE t).1).1.1 (phiE t).1.2.2.2.1
      (phiE t).1.2.2.2.2 h₃ (phiE t).1.2.2.2.1 (phiE t).1.2.2.2.2
      (xBlk (phiE t).1.2.1 (fwd sphFix sO (phiE t).1).2 p) j := by
  intro i hi
  refine ⟨rfl, rfl, f2 _ fun a ↦ ?_⟩
  have h := famZ_ne_pCellH_y (yOf t) ⟨ht.2.2.2.1, ht.2.2.2.2⟩ hp (j := i)
    (by rw [yOf_xw]; omega) a
  rw [yOf_xw, yOf_h, yOf_v] at h
  exact h

/-- **The template data avoid the output cells** (`PathsAvoid`). -/
theorem pathsAvoid_pubP (ht : FullD t) :
    PathsAvoid (pubP (fullE t).1).xw (pubP (fullE t).1).keys.1 (valsOf (fullE t).2.1) := by
  obtain ⟨h₃, e, f2, -⟩ := pubP_fullE ht.2.2.2.1
  rw [e, sPub_xw, sPub_keys_fst, valsOf_fullE]
  have hA := (xGoodPV_fwd ht.2.1).2
  rw [Quantum.Xmss.Assembly.fwd_fst_snd sphFix sO] at hA
  have hZ : ∀ p ∈ xI, ∀ j < xLen (phiE t).1.2.1 p,
      sCellZ (phiE t).1.2 h₃ (outSlot p) (fwd sphFix sO (phiE t).1).2 j =
        sCellZ (phiE t).1.2 (fwd sphFix sO (phiE t).1).1.1 (outSlot p)
          (fwd sphFix sO (phiE t).1).2 j := fun p hp j hj ↦
    rnZ_congr (rnAgree_pubP ht f2 hp hj.le) rfl rfl
  intro p hp q hq j hj
  have hj' : j < xLen (phiE t).1.2.1 p := by
    have : j + 1 < xLen (phiE t).1.2.1 p := hj
    omega
  have hlq : xLen (phiE t).1.2.1 q - 1 < xLen (phiE t).1.2.1 q := by
    have := nBlk_pos (phiE t).1.2.1 (outSlot q)
    unfold xLen
    omega
  have hO : sOutCap (phiE t).1.2 h₃ (outSlot q) (fwd sphFix sO (phiE t).1).2 =
      sOutCap (phiE t).1.2 (fwd sphFix sO (phiE t).1).1.1 (outSlot q)
        (fwd sphFix sO (phiE t).1).2 :=
    hZ q hq _ hlq
  rw [hZ p hp j hj', hO]
  exact hA p hp q hq j hj

end table

end Quantum.Sphincs.Assembly

end
