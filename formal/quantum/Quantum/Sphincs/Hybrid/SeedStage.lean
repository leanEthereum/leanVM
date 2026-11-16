module

public import Quantum.Sphincs.Hybrid.SchemeSplit
public import Quantum.Xmss.Hybrid.SeedStage

@[expose] public section

/-!
# The `SK.seed`-keyed paths' `k`- and `k'`-stages

The `SK.seed`-keyed paths (the derivations of `SK.prf` and `PK.seed` and the secrets' `PRF` calls,
indexed by `SkIdx`) read `k` at their first blocks `skCell P S b`, `k'` at their rates and `h` at
their capacities. `schemeSplit` hides the capacities' `h`-values, but the `k`- and `k'`-values stay
in the public keys, so the paths' rates and capacities are functions of public data and `SK.seed`:
for a fixed public part, a point is a capacity of these paths for an uncontrolled fraction of the
seeds. As for leanXMSS (`Quantum.Xmss.Hybrid.SeedStage`), two more exchanges move these values into
slots `SeedKS`, which join the never-revealed part:

* `stageS`: `k` at the paths' first blocks with the `k`-slots (the cells are distinct:
  `skCell_injective_idx`, so no guard is needed);
* `stageS'`: `k'` at the paths' rates with the `k'`-slots, when the rates are distinct.

`seedKStages` is an automorphism of `(Pub × Secret) × SeedKS` that keeps `h`, `π`, the public slots
and the secret (`seedKStages_spec`), so it composes with other stages on `Pub × Secret`;
`seedKSplit : Tab × SeedKS ≃ (Pub × Secret) × SeedKS` runs it directly after `schemeSplit`.

* **Coordinates on the good set** (`seedKGood cell Q`: `schemeGood Q`, the rates of the paths and of
  a label family `cell` jointly distinct (`SeedRateInj`), no computation reading a path's `k`- or
  `k'`-cell (`SeedReadGood`)): the slots hold the table's `k` and `k'` on the paths
  (`seedKSplit_coords`), and the challenger's data is a function of the public part
  (`schemeData_eq_pubData_seedKSplit`). The label family (`cell : J → PublicParameter → Secret → X`,
  leanSPHINCS's `PRF_msg` first blocks) only enters `SeedRateInj`, so that stages run after this one
  may assume their rates avoid the paths' rates.
* **The paths' cells over the slots** (`seedHSlots`, `seedK'Slots`; `seedKGood_subsets`): on the
  good set the table's `SK.seed`-keyed capacities and rates (`skCaps`, `skRates`) are these at
  `SK.seed` and the slots.
* **Multiplicities** (`sum_indicator_seedHSlots_le`, `sum_indicator_seedK'Slots_le`): a point is a
  path capacity for at most `|A| / |Z|` and a path rate (on a `PermGood π G`) for at most
  `|A| G / |Z|` of any never-revealed part with the slots, both at most
  `seedEps G = |A| (G + 1) / |Z|`, `A = SkIdx`.
* **The bad fraction** (`seedKGood_frac_le`, `seedKGood_frac_le_schemeGood`): `schemeGood`'s, the
  bad permutations, the rate collisions `|A ⊕ J|² / |X|` (averaged over `π`), and per computation
  `qsᵢ / 2^256` (reads of the paths' `k`-cells) plus `|A| G qᵢ / |Z|` (reads of their rates, the
  `k`-slots resampled).
* **At Keccak's sizes** (`G = 18`, `|J| ≤ 2^256`): `seedEps_le_keccak` (`seedEps 18 ≤ 2^-463`),
  `seedKGood_frac_le_keccak` (`2^-574` for the rate collisions, `qᵢ / 2^464` per computation).
-/

open scoped ENNReal

open Quantum.SufCma

open Quantum Quantum.Sponge Sphincs
open HashSig (HashOutput PublicParameter MasterSeed)
open Common.SufCma (SchemeHashSpec)
open Quantum.Xmss (X Z out256 trunc128)
open Quantum.Xmss.Hybrid (capOf rateOf stageN stageN_spec kCells k'Cells mem_kCells mem_k'Cells
  card_k'Cells_le card_mul_sum_equiv_prod_le card_mul_sum_not_injective_rate_le
  card_mul_sum_le_of_update sum_ite_comp_mem_le sum_ite_mem_le_card_filter card_sub_card_le_sum
  natCast_le_mul_div_of_mul_le card_masterSeed inv_mul_le_of_parts sum_add_sum_eq
  card_mul_sum_fst_eq card_mul_sum_fst_equiv_le card_mul_sum_equiv_le sum_ite_mem_zero_one_eq
  sum_fst_eq natCast_smul_eq_card_mul card_mul_sum_slot_equiv_le natCast_mul_succ KeysPerm)
open Quantum.Xmss.Assembly (le_div_mul_of_mul_le sum_indicator_capOf_eq_one
  card_filter_eq_sum_indicator)

namespace Quantum.Sphincs.Hybrid

/-! ## The stages -/

section stages

/-- The `SK.seed`-keyed paths' slots: their `k`-slots and their `k'`-slots. -/
abbrev SeedKS : Type := (SkIdx → Z) × (SkIdx → Z)

/-- A path slot is finite (named: the products of these slots are not found otherwise). -/
noncomputable instance instFintypeSkSlot : Fintype (SkIdx → Z) :=
  Pi.instFintype

noncomputable instance instFintypeSeedKS : Fintype SeedKS :=
  instFintypeProd _ _

noncomputable instance instFintypePubSecretSeedKS : Fintype ((Pub × Secret) × SeedKS) :=
  instFintypeProd _ _

noncomputable instance instFintypeTabSeedKS : Fintype (Tab × SeedKS) :=
  instFintypeProd _ _

/-- The public slots: the last `832` bits of slot `0`, slot `1` (`PK.seed`) and the secrets'
slots. -/
abbrev PubRest : Type := (Fin 832 → ZMod 2) × X × (KeygenDomain → X)

/-- The data the stages keep: `h`, the other key, `π`, the public slots, the secret, and the other
path slot. -/
abbrev RestS : Type :=
  (Z → X) × (X → Z) × Equiv.Perm (X × Z) × PubRest × Secret × (SkIdx → Z)

/-- The `k`-stage's view: `k` with the `k`-slots, and the rest. -/
def shufS : (Pub × Secret) × SeedKS ≃ ((X → Z) × (SkIdx → Z)) × RestS where
  toFun y := ((y.1.1.1.1.2.1, y.2.1),
    (y.1.1.1.1.1, y.1.1.1.1.2.2, y.1.1.1.2, y.1.1.2, y.1.2, y.2.2))
  invFun p := (((((p.2.1, p.1.1, p.2.2.1), p.2.2.2.1), p.2.2.2.2.1), p.2.2.2.2.2.1),
    (p.1.2, p.2.2.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `k'`-stage's view: `k'` with the `k'`-slots, and the rest. -/
def shufS' : (Pub × Secret) × SeedKS ≃ ((X → Z) × (SkIdx → Z)) × RestS where
  toFun y := ((y.1.1.1.1.2.2, y.2.2),
    (y.1.1.1.1.1, y.1.1.1.1.2.1, y.1.1.1.2, y.1.1.2, y.1.2, y.2.1))
  invFun p := (((((p.2.1, p.2.2.1, p.1.1), p.2.2.2.1), p.2.2.2.2.1), p.2.2.2.2.2.1),
    (p.2.2.2.2.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem shufS_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (sl : PubRest)
    (s : Secret) (κ κ' : SkIdx → Z) :
    shufS (((((h, k, k'), π), sl), s), (κ, κ')) = ((k, κ), (h, k', π, sl, s, κ')) :=
  rfl

theorem shufS_symm_apply (p : (X → Z) × (SkIdx → Z)) (h : Z → X) (k' : X → Z)
    (π : Equiv.Perm (X × Z)) (sl : PubRest) (s : Secret) (κ' : SkIdx → Z) :
    shufS.symm (p, (h, k', π, sl, s, κ')) = (((((h, p.1, k'), π), sl), s), (p.2, κ')) :=
  rfl

theorem shufS'_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (sl : PubRest)
    (s : Secret) (κ κ' : SkIdx → Z) :
    shufS' (((((h, k, k'), π), sl), s), (κ, κ')) = ((k', κ'), (h, k, π, sl, s, κ)) :=
  rfl

theorem shufS'_symm_apply (p : (X → Z) × (SkIdx → Z)) (h : Z → X) (k : X → Z)
    (π : Equiv.Perm (X × Z)) (sl : PubRest) (s : Secret) (κ : SkIdx → Z) :
    shufS'.symm (p, (h, k, π, sl, s, κ)) = (((((h, k, p.1), π), sl), s), (κ, p.2)) :=
  rfl

/-- The `k`-stage's cells: the paths' first blocks, for `PK.seed` from slot `1` and `SK.seed`. -/
def posS (w : RestS) (b : SkIdx) : X :=
  skCell (trunc128 w.2.2.2.1.2.1) w.2.2.2.2.1.1 b

/-- The `k'`-stage's cells: the paths' rates with the `k`-slots. -/
def posS' (w : RestS) (b : SkIdx) : X :=
  (w.2.2.1 (posS w b, w.2.2.2.2.2 b)).1

/-- **The `k`-stage**: `k` at the paths' first blocks takes the `k`-slots, which take its
values. -/
noncomputable def stageS : (Pub × Secret) × SeedKS ≃ (Pub × Secret) × SeedKS :=
  (shufS.trans (stageN posS fun _ _ ↦ (0 : Z))).trans shufS.symm

/-- **The `k'`-stage**: `k'` at the paths' rates takes the `k'`-slots, which take its values, when
the rates are distinct. -/
noncomputable def stageS' : (Pub × Secret) × SeedKS ≃ (Pub × Secret) × SeedKS :=
  (shufS'.trans (stageN posS' fun _ _ ↦ (0 : Z))).trans shufS'.symm

theorem stageS_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (sl : PubRest)
    (s : Secret) (κ κ' : SkIdx → Z) :
    ∃ (k₂ : X → Z) (κ₂ : SkIdx → Z),
      stageS (((((h, k, k'), π), sl), s), (κ, κ')) = (((((h, k₂, k'), π), sl), s), (κ₂, κ')) ∧
      (∀ b, κ₂ b = k (skCell (trunc128 sl.2.1) s.1 b)) ∧
      ∀ x, (∀ b, skCell (trunc128 sl.2.1) s.1 b ≠ x) → k₂ x = k x := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec posS (fun _ _ ↦ (0 : Z)) (k, κ) (h, k', π, sl, s, κ')
  obtain ⟨h1, h2⟩ := hsp (skCell_injective_idx (trunc128 sl.2.1) s.1)
  refine ⟨p'.1, p'.2, ?_, fun b ↦ (h1 b).trans (zero_add _), h2⟩
  rw [stageS, Equiv.trans_apply, Equiv.trans_apply, shufS_apply, hp', shufS_symm_apply]

theorem stageS'_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (sl : PubRest)
    (s : Secret) (κ κ' : SkIdx → Z) :
    ∃ (k'₂ : X → Z) (κ'₂ : SkIdx → Z),
      stageS' (((((h, k, k'), π), sl), s), (κ, κ')) = (((((h, k, k'₂), π), sl), s), (κ, κ'₂)) ∧
      (Function.Injective (fun b ↦ (π (skCell (trunc128 sl.2.1) s.1 b, κ b)).1) →
        (∀ b, κ'₂ b = k' (π (skCell (trunc128 sl.2.1) s.1 b, κ b)).1) ∧
          ∀ x, (∀ b, (π (skCell (trunc128 sl.2.1) s.1 b, κ b)).1 ≠ x) → k'₂ x = k' x) := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec posS' (fun _ _ ↦ (0 : Z)) (k', κ') (h, k, π, sl, s, κ)
  refine ⟨p'.1, p'.2, ?_, fun hinj ↦ ?_⟩
  · rw [stageS', Equiv.trans_apply, Equiv.trans_apply, shufS'_apply, hp', shufS'_symm_apply]
  · obtain ⟨h1, h2⟩ := hsp hinj
    exact ⟨fun b ↦ (h1 b).trans (zero_add _), h2⟩

/-- **The `SK.seed`-keyed paths' stages.** -/
noncomputable def seedKStages : (Pub × Secret) × SeedKS ≃ (Pub × Secret) × SeedKS :=
  stageS.trans stageS'

/-- The paths' first blocks read off the public part and the secret. -/
def seedCell (y : Pub × Secret) (b : SkIdx) : X :=
  skCell (pubParam y.1) y.2.1 b

/-- **The stages**: they keep `h`, `π`, the public slots and the secret. The `k`-slots take `k` at
the paths' first blocks, and `k` keeps its values off them; when the paths' rates are distinct,
the `k'`-slots take `k'` at them, and `k'` keeps its values off them. -/
theorem seedKStages_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (sl : PubRest)
    (s : Secret) (sk : SeedKS) :
    ∃ (k₂ k'₂ : X → Z) (sk₂ : SeedKS),
      seedKStages (((((h, k, k'), π), sl), s), sk) = (((((h, k₂, k'₂), π), sl), s), sk₂) ∧
      (∀ b, sk₂.1 b = k (skCell (trunc128 sl.2.1) s.1 b)) ∧
      (∀ x, (∀ b, skCell (trunc128 sl.2.1) s.1 b ≠ x) → k₂ x = k x) ∧
      (Function.Injective (fun b ↦ rateOf k π (skCell (trunc128 sl.2.1) s.1 b)) →
        (∀ b, sk₂.2 b = k' (rateOf k π (skCell (trunc128 sl.2.1) s.1 b))) ∧
        ∀ x, (∀ b, rateOf k π (skCell (trunc128 sl.2.1) s.1 b) ≠ x) → k'₂ x = k' x) := by
  obtain ⟨κ, κ'⟩ := sk
  obtain ⟨k₂, κ₂, e1, f1, f2⟩ := stageS_spec h k k' π sl s κ κ'
  obtain ⟨k'₂, κ'₂, e2, f3⟩ := stageS'_spec h k₂ k' π sl s κ₂ κ'
  refine ⟨k₂, k'₂, (κ₂, κ'₂), ?_, f1, f2, fun hr ↦ ?_⟩
  · rw [seedKStages, Equiv.trans_apply, e1, e2]
  · have hpr : ∀ b, (π (skCell (trunc128 sl.2.1) s.1 b, κ₂ b)).1 =
        rateOf k π (skCell (trunc128 sl.2.1) s.1 b) := fun b ↦ by rw [f1 b, rateOf]
    obtain ⟨g1, g2⟩ := f3 fun a b hab ↦ hr ((hpr a).symm.trans (hab.trans (hpr b)))
    exact ⟨fun b ↦ (g1 b).trans (congrArg k' (hpr b)),
      fun x hx ↦ g2 x fun b hb ↦ hx b ((hpr b).symm.trans hb)⟩

/-- `seedKStages_spec` in projections. -/
theorem seedKStages_spec' (y : (Pub × Secret) × SeedKS) :
    ∃ (k₂ k'₂ : X → Z) (sk₂ : SeedKS),
      seedKStages y = (((((y.1.1.1.1.1, k₂, k'₂), y.1.1.1.2), y.1.1.2), y.1.2), sk₂) ∧
      (∀ b, sk₂.1 b = y.1.1.1.1.2.1 (seedCell y.1 b)) ∧
      (∀ x, (∀ b, seedCell y.1 b ≠ x) → k₂ x = y.1.1.1.1.2.1 x) ∧
      (Function.Injective (fun b ↦ rateOf y.1.1.1.1.2.1 y.1.1.1.2 (seedCell y.1 b)) →
        (∀ b, sk₂.2 b = y.1.1.1.1.2.2 (rateOf y.1.1.1.1.2.1 y.1.1.1.2 (seedCell y.1 b))) ∧
        ∀ x, (∀ b, rateOf y.1.1.1.1.2.1 y.1.1.1.2 (seedCell y.1 b) ≠ x) →
          k'₂ x = y.1.1.1.1.2.2 x) := by
  obtain ⟨⟨⟨⟨⟨h, k, k'⟩, π⟩, sl⟩, s⟩, sk⟩ := y
  exact seedKStages_spec h k k' π sl s sk

/-- **The staged swap with the `SK.seed`-keyed paths' stages**: `schemeSplit`, then the stages. -/
noncomputable def seedKSplit : Tab × SeedKS ≃ (Pub × Secret) × SeedKS :=
  (schemeSplit.prodCongr (Equiv.refl SeedKS)).trans seedKStages

theorem seedKSplit_apply (x : Tab × SeedKS) :
    seedKSplit x = seedKStages (schemeSplit x.1, x.2) :=
  rfl

/-- **`seedKSplit` keeps everything `schemeSplit` gives but `k` and `k'`.** -/
theorem seedKSplit_spec (x : Tab × SeedKS) :
    ∃ (k₂ k'₂ : X → Z) (sk₂ : SeedKS),
      seedKSplit x = ((((((schemeSplit x.1).1.1.1.1, k₂, k'₂), (schemeSplit x.1).1.1.2),
        (schemeSplit x.1).1.2), (schemeSplit x.1).2), sk₂) ∧
      (∀ b, sk₂.1 b = (schemeSplit x.1).1.1.1.2.1 (seedCell (schemeSplit x.1) b)) ∧
      (∀ y, (∀ b, seedCell (schemeSplit x.1) b ≠ y) → k₂ y = (schemeSplit x.1).1.1.1.2.1 y) ∧
      (Function.Injective (fun b ↦ rateOf (schemeSplit x.1).1.1.1.2.1 (schemeSplit x.1).1.1.2
          (seedCell (schemeSplit x.1) b)) →
        (∀ b, sk₂.2 b = (schemeSplit x.1).1.1.1.2.2 (rateOf (schemeSplit x.1).1.1.1.2.1
          (schemeSplit x.1).1.1.2 (seedCell (schemeSplit x.1) b))) ∧
        ∀ y, (∀ b, rateOf (schemeSplit x.1).1.1.1.2.1 (schemeSplit x.1).1.1.2
            (seedCell (schemeSplit x.1) b) ≠ y) →
          k'₂ y = (schemeSplit x.1).1.1.1.2.2 y) := by
  rw [seedKSplit_apply]
  exact seedKStages_spec' _

/-- The stages keep the public slots. -/
theorem seedKSplit_slots (x : Tab × SeedKS) : (seedKSplit x).1.1.2 = (schemeSplit x.1).1.2 := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec x
  rw [hE]

/-- The stages keep `π`. -/
theorem seedKSplit_perm (x : Tab × SeedKS) : (seedKSplit x).1.1.1.2 = x.1.1.perm := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec x
  rw [hE]
  exact schemeSplit_perm x.1

/-- The stages keep `h`. -/
theorem seedKSplit_h (x : Tab × SeedKS) :
    (seedKSplit x).1.1.1.1.1 = (schemeSplit x.1).1.1.1.1 := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec x
  rw [hE]

/-- **The hidden coordinate is still `(SK.seed, SK.prf)`.** -/
theorem seedKSplit_secret (x : Tab × SeedKS) :
    (seedKSplit x).1.2 = (x.1.1.secretSeed, x.1.1.prfKey) := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec x
  rw [hE]
  exact schemeSplit_snd x.1

end stages

/-! ## The good set and the coordinate facts -/

section good

variable {J : Type} (cell : J → PublicParameter → Secret → X)

/-- The paths' first blocks read off the coordinates. -/
def seedCellK (y : (Pub × Secret) × SeedKS) (b : SkIdx) : X :=
  seedCell y.1 b

/-- The paths' rates read off the coordinates (with the `k`-slots). -/
def seedCellK' (y : (Pub × Secret) × SeedKS) (b : SkIdx) : X :=
  (y.1.1.1.2 (seedCellK y b, y.2.1 b)).1

variable {ι : Type} {β : ι → Type}

/-- No computation `Q i` from the public part reads a path's `k`- or `k'`-cell read off the
coordinates. -/
def SeedReadGood
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (y : (Pub × Secret) × SeedKS) : Prop :=
  ∀ i b, seedCellK y b ∉ kCells (pubData Q y.1.1 i).2 ∧
    seedCellK' y b ∉ k'Cells (pubData Q y.1.1 i).2

/-- The rates of the paths and of the labels' first blocks `cell`, after `schemeSplit`, are
distinct. -/
abbrev SeedRateInj (x : Pub × Secret) : Prop :=
  Function.Injective fun c : SkIdx ⊕ J ↦ rateOf x.1.1.1.2.1 x.1.1.2
    (Sum.elim (seedCell x) (fun a ↦ cell a (pubParam x.1) x.2) c)

/-- The paths' and the labels' first blocks are distinct. -/
theorem seed_sum_injective (hcell : ∀ P s, Function.Injective fun a ↦ cell a P s)
    (hsep : ∀ P s a b, skCell P s.1 b ≠ cell a P s) (P : PublicParameter) (s : Secret) :
    Function.Injective (Sum.elim (skCell P s.1) fun a ↦ cell a P s) :=
  Function.Injective.sumElim (skCell_injective_idx P s.1) (hcell P s) fun b a ↦ hsep P s a b

open scoped Classical in
/-- **The good set** of the stages: `schemeGood`, distinct path and label rates (`SeedRateInj`),
and no computation reading a path's `k`- or `k'`-cell (`SeedReadGood`). Irreducible: its membership
does not unfold to the enumeration of all tables. -/
@[irreducible]
noncomputable def seedKGood
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Finset (Tab × SeedKS) :=
  Finset.univ.filter fun x ↦
    x.1 ∈ schemeGood Q ∧ SeedRateInj cell (schemeSplit x.1) ∧ SeedReadGood Q (seedKSplit x)

variable {cell}

theorem mem_seedKGood
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {x : Tab × SeedKS} :
    x ∈ seedKGood cell Q ↔ x.1 ∈ schemeGood Q ∧ SeedRateInj cell (schemeSplit x.1) ∧
      SeedReadGood Q (seedKSplit x) := by
  unfold seedKGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

section coords

variable {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
  {x : Tab × SeedKS} (hx : x ∈ seedKGood cell Q)

include hx

/-- On the good set the paths' rates after `schemeSplit` are distinct. -/
theorem seedRate_injective :
    Function.Injective (fun b ↦ rateOf (schemeSplit x.1).1.1.1.2.1 (schemeSplit x.1).1.1.2
      (seedCell (schemeSplit x.1) b)) := fun b b' hb ↦
  Sum.inl_injective ((mem_seedKGood.mp hx).2.1 (a₁ := Sum.inl b) (a₂ := Sum.inl b') hb)

/-- **The paths through `schemeSplit`**: on the good set, the paths' first blocks read off
`schemeSplit` are the table's, its keys `k`, `k'` and `π` are the table's, and the table's path
rates are distinct. -/
theorem seedKGood_paths :
    (∀ b, seedCell (schemeSplit x.1) b = skCell x.1.1.publicSeed x.1.1.secretSeed b) ∧
    (schemeSplit x.1).1.1.1.2 = x.1.1.keys.2 ∧ (schemeSplit x.1).1.1.2 = x.1.1.perm ∧
    Function.Injective (fun b ↦
      rateOf x.1.1.keys.2.1 x.1.1.perm (skCell x.1.1.publicSeed x.1.1.secretSeed b)) := by
  obtain ⟨hinj, -⟩ := mem_schemeGood.mp (mem_seedKGood.mp hx).1
  have hP := (schemeSplit_transfer x.1 hinj).1
  have hS : (schemeSplit x.1).2.1 = x.1.1.secretSeed := by rw [schemeSplit_snd]
  have hks := schemeSplit_keys_snd x.1
  have hπ := schemeSplit_perm x.1
  have hc : ∀ b, seedCell (schemeSplit x.1) b = skCell x.1.1.publicSeed x.1.1.secretSeed b :=
    fun b ↦ by
      show skCell (pubParam (schemeSplit x.1).1) (schemeSplit x.1).2.1 b = _
      rw [hP, hS]
  refine ⟨hc, hks, hπ, fun b b' hb ↦ seedRate_injective hx ?_⟩
  change rateOf (schemeSplit x.1).1.1.1.2.1 (schemeSplit x.1).1.1.2 (seedCell (schemeSplit x.1) b) =
    rateOf (schemeSplit x.1).1.1.1.2.1 (schemeSplit x.1).1.1.2 (seedCell (schemeSplit x.1) b')
  rw [hks, hπ, hc, hc]
  exact hb

/-- **The coordinate facts**: on the good set, the slots hold the table's `k` at the paths' first
blocks and its `k'` at their rates. -/
theorem seedKSplit_coords :
    (∀ b, (seedKSplit x).2.1 b = x.1.1.keys.2.1 (skCell x.1.1.publicSeed x.1.1.secretSeed b)) ∧
    ∀ b, (seedKSplit x).2.2 b = x.1.1.keys.2.2 (rateOf x.1.1.keys.2.1 x.1.1.perm
      (skCell x.1.1.publicSeed x.1.1.secretSeed b)) := by
  obtain ⟨hc, hks, hπ, -⟩ := seedKGood_paths hx
  obtain ⟨k₂, k'₂, sk₂, hE, f1, -, f3⟩ := seedKSplit_spec x
  obtain ⟨f4, -⟩ := f3 (seedRate_injective hx)
  rw [hE]
  refine ⟨fun b ↦ (f1 b).trans ?_, fun b ↦ (f4 b).trans ?_⟩
  · rw [hks, hc b]
  · rw [hks, hπ, hc b]

/-- **On the good set, the challenger's data is a function of the public part.** -/
theorem schemeData_eq_pubData_seedKSplit :
    schemeData Q x.1.1 = pubData Q (seedKSplit x).1.1 := by
  obtain ⟨hs, -, hread⟩ := mem_seedKGood.mp hx
  rw [schemeData_eq_of_mem hs]
  obtain ⟨k₂, k'₂, sk₂, hE, f1, f2, f3⟩ := seedKSplit_spec x
  obtain ⟨-, f5⟩ := f3 (seedRate_injective hx)
  have hpd : pubData Q (seedKSplit x).1.1 = fun i ↦ honestEval
      ((schemeSplit x.1).1.1.1.1, k₂, k'₂) (schemeSplit x.1).1.1.2
      (Q i (pubParam (schemeSplit x.1).1) (pubSec (schemeSplit x.1).1)) := by
    rw [hE]
    rfl
  have hsc : ∀ b, seedCellK (seedKSplit x) b = seedCell (schemeSplit x.1) b := fun b ↦ by
    rw [hE]
    rfl
  have hsc' : ∀ b, seedCellK' (seedKSplit x) b = rateOf (schemeSplit x.1).1.1.1.2.1
      (schemeSplit x.1).1.1.2 (seedCell (schemeSplit x.1) b) := fun b ↦ by
    rw [hE]
    unfold seedCellK' rateOf
    rw [f1 b]
    rfl
  have hri := fun i b ↦ hread i b
  rw [hpd] at hri
  rw [hpd]
  funext i
  change honestEval (schemeSplit x.1).1.1.1 (schemeSplit x.1).1.1.2
      (Q i (pubParam (schemeSplit x.1).1) (pubSec (schemeSplit x.1).1)) = _
  refine honestEval_congr (t := ((schemeSplit x.1).1.1.1.1, k₂, k'₂))
    (t' := (schemeSplit x.1).1.1.1) (schemeSplit x.1).1.1.2 _ fun e he ↦ ?_
  have ha := honestEval_answeredBy (schemeSplit x.1).1.1.2
    ((schemeSplit x.1).1.1.1.1, k₂, k'₂) _ e he
  cases e with
  | h z v =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    exact ha
  | k y v =>
    have hy : ∀ b, seedCell (schemeSplit x.1) b ≠ y := fun b hb ↦ (hri i b).1 (by
      rw [hsc b, hb]
      exact mem_kCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← f2 y hy]
    exact ha
  | k' y v =>
    have hy : ∀ b, rateOf (schemeSplit x.1).1.1.1.2.1 (schemeSplit x.1).1.1.2
        (seedCell (schemeSplit x.1) b) ≠ y := fun b hb ↦ (hri i b).2 (by
      rw [hsc' b, hb]
      exact mem_k'Cells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← f5 y hy]
    exact ha

end coords

/-! ### The bad fraction -/

open scoped Classical

variable (cell) (G : ℕ)

variable [Fintype J] [DecidableEq J]

/-- A table outside `schemeGood`. -/
noncomputable def schemeBad
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (t : Tab) : ℕ :=
  if t ∈ schemeGood Q then 0 else 1

/-- A table with a bad permutation. -/
noncomputable def tabPermBad (t : Tab) : ℕ :=
  if ¬PermGood t.1.perm G then 1 else 0

/-- Colliding path or label rates (any permutation). -/
noncomputable def seedRateBad (x : Pub × Secret) : ℕ :=
  if ¬SeedRateInj cell x then 1 else 0

/-- The computation `Q i` reads `k` at the path `b`'s first block. -/
noncomputable def seedKHit
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (i : ι) (b : SkIdx) (y : (Pub × Secret) × SeedKS) : ℕ :=
  if seedCellK y b ∈ kCells (pubData Q y.1.1 i).2 then 1 else 0

/-- A good permutation and the computation `Q i` reading `k'` at the path `b`'s rate. -/
noncomputable def seedK'Hit
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (i : ι) (b : SkIdx) (y : (Pub × Secret) × SeedKS) : ℕ :=
  if PermGood y.1.1.1.2 G ∧ seedCellK' y b ∈ k'Cells (pubData Q y.1.1 i).2 then 1 else 0

/-- The paths' first blocks read by `Q i`. -/
noncomputable def seedReadK
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (i : ι) (y : (Pub × Secret) × SeedKS) : ℕ :=
  ∑ b, seedKHit Q i b y

/-- The paths' rates read by `Q i`. -/
noncomputable def seedReadK'
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (i : ι) (y : (Pub × Secret) × SeedKS) : ℕ :=
  ∑ b, seedK'Hit G Q i b y

omit [DecidableEq J] in
/-- The tables outside the good set: outside `schemeGood`, a bad permutation, colliding path or
label rates, or a computation reading a path's `k`- or `k'`-cell. -/
theorem card_sub_card_seedKGood_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Fintype.card (Tab × SeedKS) - (seedKGood cell Q).card ≤
      ∑ x : Tab × SeedKS, ((schemeBad Q x.1 + tabPermBad G x.1) +
        (seedRateBad cell (schemeSplit x.1) + ∑ i, (seedReadK Q i (seedKSplit x) +
          seedReadK' G Q i (seedKSplit x)))) := by
  refine card_sub_card_le_sum (seedKGood cell Q) _ fun x hx ↦ ?_
  rw [mem_seedKGood] at hx
  by_cases h0 : x.1 ∈ schemeGood Q
  · by_cases hG : PermGood x.1.1.perm G
    · by_cases hr : SeedRateInj cell (schemeSplit x.1)
      · have hread : ¬SeedReadGood Q (seedKSplit x) := fun h ↦ hx ⟨h0, hr, h⟩
        obtain ⟨i, b, hib⟩ : ∃ i b,
            ¬(seedCellK (seedKSplit x) b ∉ kCells (pubData Q (seedKSplit x).1.1 i).2 ∧
              seedCellK' (seedKSplit x) b ∉ k'Cells (pubData Q (seedKSplit x).1.1 i).2) := by
          by_contra hne
          exact hread fun i b ↦ by_contra fun h ↦ hne ⟨i, b, h⟩
        have hG' : PermGood (seedKSplit x).1.1.1.2 G := by
          rw [seedKSplit_perm]
          exact hG
        have h1 : 1 ≤ seedReadK Q i (seedKSplit x) + seedReadK' G Q i (seedKSplit x) := by
          change 1 ≤ (∑ b', seedKHit Q i b' (seedKSplit x)) +
            ∑ b', seedK'Hit G Q i b' (seedKSplit x)
          have hk : seedKHit Q i b (seedKSplit x) ≤ ∑ b', seedKHit Q i b' (seedKSplit x) :=
            Finset.single_le_sum (f := fun b' ↦ seedKHit Q i b' (seedKSplit x))
              (fun _ _ ↦ Nat.zero_le _) (by simp)
          have hk' : seedK'Hit G Q i b (seedKSplit x) ≤
              ∑ b', seedK'Hit G Q i b' (seedKSplit x) :=
            Finset.single_le_sum (f := fun b' ↦ seedK'Hit G Q i b' (seedKSplit x))
              (fun _ _ ↦ Nat.zero_le _) (by simp)
          by_cases m1 : seedCellK (seedKSplit x) b ∈ kCells (pubData Q (seedKSplit x).1.1 i).2
          · have : seedKHit Q i b (seedKSplit x) = 1 := ite_eq_left m1
            omega
          · have m2 : seedCellK' (seedKSplit x) b ∈
                k'Cells (pubData Q (seedKSplit x).1.1 i).2 :=
              by_contra fun m2 ↦ hib ⟨m1, m2⟩
            have : seedK'Hit G Q i b (seedKSplit x) = 1 := ite_eq_left ⟨hG', m2⟩
            omega
        have h2 : seedReadK Q i (seedKSplit x) + seedReadK' G Q i (seedKSplit x) ≤
            ∑ i', (seedReadK Q i' (seedKSplit x) + seedReadK' G Q i' (seedKSplit x)) :=
          Finset.single_le_sum (f := fun i' ↦ seedReadK Q i' (seedKSplit x) +
            seedReadK' G Q i' (seedKSplit x)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        omega
      · have : seedRateBad cell (schemeSplit x.1) = 1 := ite_eq_left hr
        omega
    · have : tabPermBad G x.1 = 1 := ite_eq_left hG
      omega
  · have : schemeBad Q x.1 = 1 := ite_eq_right h0
    omega

/-- The coordinates other than `π`: the keys, the public slots, and the secret. -/
abbrev RestPi : Type := SpongeKeys X Z × PubRest × Secret

noncomputable instance instFintypeRestPi : Fintype RestPi :=
  instFintypeProd _ _

/-- The public part and the secret as `(π, rest)`. -/
def coordPiS : Equiv.Perm (X × Z) × RestPi ≃ Pub × Secret where
  toFun c := (((c.2.1, c.1), c.2.2.1), c.2.2.2)
  invFun x := (x.1.1.2, (x.1.1.1, x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Path and label rate collisions, averaged over `π`**: at most `|A ⊕ J|² / |X|` of the
coordinates. -/
theorem card_mul_sum_seedRateBad_le (hcell : ∀ P s, Function.Injective fun a ↦ cell a P s)
    (hsep : ∀ P s a b, skCell P s.1 b ≠ cell a P s) :
    Fintype.card X * ∑ x, seedRateBad cell x ≤
      Fintype.card (Pub × Secret) * (Fintype.card (SkIdx ⊕ J) * Fintype.card (SkIdx ⊕ J)) :=
  card_mul_sum_equiv_prod_le coordPiS _ _ (seedRateBad cell) fun r ↦
    card_mul_sum_not_injective_rate_le
      (fun c ↦ (Sum.elim (skCell (trunc128 r.2.1.2.1) r.2.2.1)
          (fun a ↦ cell a (trunc128 r.2.1.2.1) r.2.2) c,
        r.1.2.1 (Sum.elim (skCell (trunc128 r.2.1.2.1) r.2.2.1)
          (fun a ↦ cell a (trunc128 r.2.1.2.1) r.2.2) c)))
      fun _ _ h ↦ seed_sum_injective cell hcell hsep _ _ (congrArg Prod.fst h)

/-- The coordinates with `SK.seed` first. -/
def seedES : MasterSeed × (KeysPerm × PubRest × HashOutput × SeedKS) ≃
    (Pub × Secret) × SeedKS where
  toFun c := (((c.2.1, c.2.2.1), (c.1, c.2.2.2.1)), c.2.2.2.2)
  invFun y := (y.1.2.1, (y.1.1.1, y.1.1.2, y.1.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinates with the `k`-slots first. -/
def seedEK : (SkIdx → Z) × ((Pub × Secret) × (SkIdx → Z)) ≃ (Pub × Secret) × SeedKS where
  toFun c := (c.2.1, (c.1, c.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype J] [DecidableEq J] in
/-- **The paths' first blocks are rarely read**: at most `qs / 2^256` of the coordinates, where
`qs` bounds the reads of `Q i` at `SK.seed`-keyed `k`-cells. -/
theorem card_mul_sum_seedReadK_le
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (qs : ι → ℕ)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i) (i : ι) :
    Fintype.card MasterSeed * ∑ y, seedReadK Q i y ≤
      Fintype.card ((Pub × Secret) × SeedKS) * qs i := by
  refine card_mul_sum_equiv_prod_le seedES _ _ (seedReadK Q i) fun r ↦
    Nat.mul_le_mul_left _ ?_
  change ∑ S : MasterSeed, ∑ b : SkIdx, (if skCell (trunc128 r.2.1.2.1) S b ∈
    kCells (honestEval r.1.1 r.1.2
      (Q i (trunc128 r.2.1.2.1) fun d ↦ out256 (r.2.1.2.2 d))).2 then 1 else 0) ≤ qs i
  rw [← Fintype.sum_prod_type']
  exact (sum_ite_mem_le_card_filter (fun p : MasterSeed × SkIdx ↦
    skCell (trunc128 r.2.1.2.1) p.1 p.2) (skCell_injective _) _
    (fun x ↦ ∃ S b, skCell (trunc128 r.2.1.2.1) S b = x) fun p ↦ ⟨p.1, p.2, rfl⟩).trans
    (hqs i _ _ _ _)

omit [Fintype J] [DecidableEq J] in
/-- **The paths' rates are rarely read**: at most `|A| G q / |Z|` of the coordinates, the
`k`-slots resampled. -/
theorem card_mul_sum_seedReadK'_le
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i) (i : ι) :
    Fintype.card Z * ∑ y, seedReadK' G Q i y ≤
      Fintype.card ((Pub × Secret) × SeedKS) * (Fintype.card SkIdx * G * q i) := by
  refine card_mul_sum_equiv_prod_le seedEK _ _ (seedReadK' G Q i) fun r ↦ ?_
  calc Fintype.card Z * ∑ κ, seedReadK' G Q i (seedEK (κ, r))
      = ∑ b, Fintype.card Z * ∑ κ, seedK'Hit G Q i b (seedEK (κ, r)) := by
        simp only [seedReadK']
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _b : SkIdx, Fintype.card (SkIdx → Z) * (q i * G) :=
        Finset.sum_le_sum fun b _ ↦ card_mul_sum_le_of_update
          (fun κ ↦ seedK'Hit G Q i b (seedEK (κ, r))) b _ fun κ ↦ by
            change ∑ w, (if PermGood r.1.1.1.2 G ∧ (r.1.1.1.2
              (seedCell r.1 b, Function.update κ b w b)).1 ∈ k'Cells (pubData Q r.1.1 i).2
              then 1 else 0) ≤ q i * G
            simp only [Function.update_self]
            by_cases hG : PermGood r.1.1.1.2 G
            · simp only [hG, true_and]
              exact (sum_ite_comp_mem_le (fun w ↦ (r.1.1.1.2 (seedCell r.1 b, w)).1) _ G
                fun x₂ ↦ hG.rate _ x₂).trans
                  (Nat.mul_le_mul_right _ ((card_k'Cells_le _).trans (hq i _ _ _ _)))
            · simp only [hG, false_and, ↓reduceIte, Finset.sum_const_zero]
              exact Nat.zero_le _
    _ = Fintype.card (SkIdx → Z) * (Fintype.card SkIdx * G * q i) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- **The bad fraction of the stages**: the fraction of tables outside `seedKGood cell Q` is at
most the fraction outside `schemeGood Q`, plus the fraction of permutations with a rate count above
`G`, plus the rate collisions `|A ⊕ J|² / |X|` (averaged over the permutation), plus per
computation `qsᵢ / 2^256 + |A| G qᵢ / |Z|`, `A = SkIdx`, where `qᵢ` bounds the reads of `Q i` and
`qsᵢ` its reads at `SK.seed`-keyed `k`-cells. The labels' first blocks are distinct for distinct
labels (`hcell`) and differ from the paths' (`hsep`). -/
theorem seedKGood_frac_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i)
    (hcell : ∀ P s, Function.Injective fun a ↦ cell a P s)
    (hsep : ∀ P s a b, skCell P s.1 b ≠ cell a P s) :
    (Fintype.card (Tab × SeedKS) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Tab × SeedKS) - (seedKGood cell Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
        ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z))) +
      ((Fintype.card (SkIdx ⊕ J) * Fintype.card (SkIdx ⊕ J) : ℕ) : ℝ≥0∞) / Fintype.card X +
      ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 +
        ((Fintype.card SkIdx * G * q i : ℕ) : ℝ≥0∞) / Fintype.card Z) := by
  refine inv_mul_le_of_parts Fintype.card_ne_zero
    ((card_sub_card_seedKGood_le cell G Q).trans_eq (sum_add_sum_eq _ _ _ _)) ?_ ?_ ?_ ?_
  · rw [Finset.sum_add_distrib, Nat.cast_add, mul_add]
    refine add_le_add (le_of_eq ?_) ?_
    · have hs : ∑ t : Tab, schemeBad Q t = Fintype.card Tab - (schemeGood Q).card :=
        sum_ite_mem_zero_one_eq (schemeGood Q)
      rw [sum_fst_eq (schemeBad Q), hs]
      exact natCast_smul_eq_card_mul _
    · exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
        (card_mul_sum_fst_eq (α := Tab) (γ := SeedKS) (tabPermBad G) _ _
          (card_mul_sum_tab_not_permGood G)).le
  · have hrate := card_mul_sum_seedRateBad_le cell hcell hsep
    rw [← Fintype.card_congr schemeSplit] at hrate
    exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_fst_equiv_le (γ := SeedKS) schemeSplit (seedRateBad cell) _ _ hrate)
  · intro i
    have h := natCast_le_mul_div_of_mul_le (Fintype.card_ne_zero (α := MasterSeed))
      (card_mul_sum_equiv_le seedKSplit (seedReadK Q i) _ _
        (card_mul_sum_seedReadK_le Q qs hqs i))
    rwa [card_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h
  · intro i
    exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le seedKSplit (seedReadK' G Q i) _ _
        (card_mul_sum_seedReadK'_le G Q q hq i))

/-- **The bad fraction of the stages with `schemeGood`'s expanded** (`schemeGood_frac_le`). -/
theorem seedKGood_frac_le_schemeGood [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i)
    (hcell : ∀ P s, Function.Injective fun a ↦ cell a P s)
    (hsep : ∀ P s a b, skCell P s.1 b ≠ cell a P s) :
    (Fintype.card (Tab × SeedKS) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Tab × SeedKS) - (seedKGood cell Q).card : ℕ) : ℝ≥0∞) ≤
      ((((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ((Fintype.card SkIdx * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + Fintype.card SkIdx * (G + 1) * q i / Fintype.card Z)) +
        ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z))) +
      ((Fintype.card (SkIdx ⊕ J) * Fintype.card (SkIdx ⊕ J) : ℕ) : ℝ≥0∞) / Fintype.card X +
      ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 +
        ((Fintype.card SkIdx * G * q i : ℕ) : ℝ≥0∞) / Fintype.card Z) :=
  (seedKGood_frac_le cell G Q q qs hq hqs hcell hsep).trans
    (add_le_add (add_le_add (add_le_add (schemeGood_frac_le G Q q qs hq hqs) le_rfl) le_rfl)
      le_rfl)

end good

/-! ## The paths' cells over a never-revealed part with the slots -/

section seedSlots

/-- The table's `SK.seed`-keyed capacities. -/
def skCaps (L : HonestTable) : Set Z :=
  Set.range fun b ↦ capOf L.keys.2.1 L.keys.2.2 L.perm (skCell L.publicSeed L.secretSeed b)

/-- The table's `SK.seed`-keyed rates. -/
def skRates (L : HonestTable) : Set X :=
  Set.range fun b ↦ rateOf L.keys.2.1 L.perm (skCell L.publicSeed L.secretSeed b)

/-- The paths' capacities at `SK.seed = S` and the slots: first block `skCell P S b`, `k`-value
`sk.1 b`, `k'`-value `sk.2 b`. -/
def seedHSlots (π : Equiv.Perm (X × Z)) (P : PublicParameter) (S : MasterSeed) (sk : SeedKS) :
    Set Z :=
  Set.range fun b ↦ capOf (fun _ ↦ sk.1 b) (fun _ ↦ sk.2 b) π (skCell P S b)

/-- The paths' rates at `SK.seed = S` and the slots, on a good permutation. -/
def seedK'Slots (G : ℕ) (π : Equiv.Perm (X × Z)) (P : PublicParameter) (S : MasterSeed)
    (sk : SeedKS) : Set X :=
  {x | PermGood π G ∧ ∃ b, (π (skCell P S b, sk.1 b)).1 = x}

/-- **The per-call multiplicity of the paths' rates and capacities**: `|A| (G + 1) / |Z|`,
`A = SkIdx`. -/
noncomputable def seedEps (G : ℕ) : ℝ≥0∞ :=
  (Fintype.card SkIdx : ℝ≥0∞) * (G + 1) / Fintype.card Z

variable {K W : Type} [Fintype K] [Fintype W]

/-- A never-revealed part with the slots and a pad, the `k'`-slots first. -/
def seedEH : (SkIdx → Z) × (K × ((SkIdx → Z) × W)) ≃ K × (SeedKS × W) where
  toFun y := (y.2.1, ((y.2.2.1, y.1), y.2.2.2))
  invFun k := (k.2.1.2, (k.1, (k.2.1.1, k.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A never-revealed part with the slots and a pad, the `k`-slots first. -/
def seedEK' : (SkIdx → Z) × (K × ((SkIdx → Z) × W)) ≃ K × (SeedKS × W) where
  toFun y := (y.2.1, ((y.1, y.2.2.1), y.2.2.2))
  invFun k := (k.2.1.1, (k.1, (k.2.1.2, k.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The paths' capacities**: a capacity is a path's for at most an `|A| / |Z| ≤ seedEps G`
fraction of a never-revealed part `K` (giving `SK.seed` as `sOf`) with the slots (the `k'`-slot
is uniform). -/
theorem sum_indicator_seedHSlots_le (sOf : K → MasterSeed) (G : ℕ) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (z : Z) :
    ∑ k : K × (SeedKS × W), (seedHSlots π P (sOf k.1) k.2.1).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) z ≤ seedEps G * Fintype.card (K × (SeedKS × W)) := by
  have hle : (Fintype.card SkIdx : ℝ≥0∞) * 1 / Fintype.card Z ≤ seedEps G :=
    ENNReal.div_le_div_right (mul_le_mul_of_nonneg_left le_add_self zero_le) _
  refine (le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _) (card_mul_sum_slot_equiv_le seedEH
      (fun k : K × (SeedKS × W) ↦ seedHSlots π P (sOf k.1) k.2.1) z
      (fun a r ↦ {w | capOf (fun _ ↦ r.2.1 a) (fun _ ↦ w) π (skCell P (sOf r.1) a) = z}) 1
      (fun _ hy ↦ hy) fun _ _ ↦ (sum_indicator_capOf_eq_one π _ _ z).le)).trans
    (mul_le_mul_of_nonneg_right hle zero_le)

/-- **The paths' rates**: on a `PermGood π G`, a cell is a path's rate for at most an
`|A| G / |Z| ≤ seedEps G` fraction of a never-revealed part with the slots (the `k`-slot is
uniform). -/
theorem sum_indicator_seedK'Slots_le (sOf : K → MasterSeed) (G : ℕ) (π : Equiv.Perm (X × Z))
    (P : PublicParameter) (x : X) :
    ∑ k : K × (SeedKS × W), (seedK'Slots G π P (sOf k.1) k.2.1).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) x ≤ seedEps G * Fintype.card (K × (SeedKS × W)) := by
  by_cases hG : PermGood π G
  · have hle : (Fintype.card SkIdx : ℝ≥0∞) * G / Fintype.card Z ≤ seedEps G :=
      ENNReal.div_le_div_right (mul_le_mul_of_nonneg_left le_self_add zero_le) _
    refine (le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _) (card_mul_sum_slot_equiv_le seedEK'
        (fun k : K × (SeedKS × W) ↦ seedK'Slots G π P (sOf k.1) k.2.1) x
        (fun a r ↦ {w | (π (skCell P (sOf r.1) a, w)).1 = x}) G
        (fun _ hy ↦ hy.2) fun _ _ ↦ ?_)).trans (mul_le_mul_of_nonneg_right hle zero_le)
    rw [← card_filter_eq_sum_indicator]
    exact_mod_cast hG.rate _ x
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem
      (fun h ↦ hG h.1) _) zero_le

/-- **The table's `SK.seed`-keyed capacities and rates on the good set** are the paths' cells at
`SK.seed` and the slots (the rates on a `PermGood π G`). -/
theorem seedKGood_subsets {J : Type} {cell : J → PublicParameter → Secret → X} {ι : Type}
    {β : ι → Type}
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    (G : ℕ) {x : Tab × SeedKS} (hx : x ∈ seedKGood cell Q) (hG : PermGood x.1.1.perm G) :
    skCaps x.1.1 ⊆ seedHSlots x.1.1.perm x.1.1.publicSeed x.1.1.secretSeed (seedKSplit x).2 ∧
      skRates x.1.1 ⊆
        seedK'Slots G x.1.1.perm x.1.1.publicSeed x.1.1.secretSeed (seedKSplit x).2 := by
  obtain ⟨c1, c2⟩ := seedKSplit_coords hx
  refine ⟨?_, ?_⟩
  · rintro _ ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    show capOf (fun _ ↦ (seedKSplit x).2.1 b) (fun _ ↦ (seedKSplit x).2.2 b) x.1.1.perm
      (skCell x.1.1.publicSeed x.1.1.secretSeed b) =
        capOf x.1.1.keys.2.1 x.1.1.keys.2.2 x.1.1.perm (skCell x.1.1.publicSeed x.1.1.secretSeed b)
    rw [c1 b, c2 b]
    rfl
  · rintro _ ⟨b, rfl⟩
    refine ⟨hG, b, ?_⟩
    show (x.1.1.perm (skCell x.1.1.publicSeed x.1.1.secretSeed b, (seedKSplit x).2.1 b)).1 =
      rateOf x.1.1.keys.2.1 x.1.1.perm (skCell x.1.1.publicSeed x.1.1.secretSeed b)
    rw [c1 b]
    rfl

end seedSlots

/-! ## At Keccak's sizes -/

section keccak

theorem card_skIdx_eq : Fintype.card SkIdx = 27 * 2 ^ 39 + 2 := by
  rw [card_skIdx, card_keygenDomain]
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The paths' multiplicity at Keccak's sizes** (`G = 18`): `seedEps 18 ≤ 2^-463`
(`19 |A| / |Z|`, `|A| = 27 · 2^39 + 2`). -/
theorem seedEps_le_keccak : seedEps 18 ≤ ENNReal.ofReal (1 / 2 ^ 463) := by
  unfold seedEps
  rw [natCast_mul_succ, Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ Fintype.card_pos]
  apply ENNReal.ofReal_le_ofReal
  rw [card_skIdx_eq, Quantum.Xmss.Hybrid.R0.card_cap]
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The rate collisions at Keccak's sizes**: `|A ⊕ J|² / |X| ≤ 2^-574` for `|J| ≤ 2^256`. -/
theorem seedRateTerm_le_keccak {J : Type} [Fintype J] (hJ : Fintype.card J ≤ 2 ^ 256) :
    ((Fintype.card (SkIdx ⊕ J) * Fintype.card (SkIdx ⊕ J) : ℕ) : ℝ≥0∞) / Fintype.card X ≤
      ENNReal.ofReal (1 / 2 ^ 574) := by
  have hA : Fintype.card (SkIdx ⊕ J) ≤ 2 ^ 257 := by
    rw [Fintype.card_sum, card_skIdx_eq]
    calc 27 * 2 ^ 39 + 2 + Fintype.card J ≤ 2 ^ 256 + 2 ^ 256 :=
          Nat.add_le_add (by norm_num) hJ
      _ = 2 ^ 257 := by norm_num
  have hn : Fintype.card (SkIdx ⊕ J) * Fintype.card (SkIdx ⊕ J) * 2 ^ 574 ≤ 2 ^ 1088 :=
    calc Fintype.card (SkIdx ⊕ J) * Fintype.card (SkIdx ⊕ J) * 2 ^ 574
        ≤ 2 ^ 257 * 2 ^ 257 * 2 ^ 574 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hA hA)
      _ = 2 ^ 1088 := by norm_num
  rw [Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ Fintype.card_pos,
    Quantum.Xmss.Hybrid.R0.card_rate]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hn

set_option exponentiation.threshold 4096 in
/-- **The rate reads at Keccak's sizes**: `18 |A| q / |Z| ≤ q / 2^464`. -/
theorem seedReadTerm_le_keccak (q : ℕ) :
    ((Fintype.card SkIdx * 18 * q : ℕ) : ℝ≥0∞) / Fintype.card Z ≤
      ENNReal.ofReal (q / 2 ^ 464) := by
  have hn : (27 * 2 ^ 39 + 2) * 18 * q * 2 ^ 464 ≤ q * 2 ^ 512 := by
    calc (27 * 2 ^ 39 + 2) * 18 * q * 2 ^ 464 = q * ((27 * 2 ^ 39 + 2) * 18 * 2 ^ 464) := by
          ring
      _ ≤ q * 2 ^ 512 := Nat.mul_le_mul_left q (by norm_num)
  rw [Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ Fintype.card_pos, card_skIdx_eq,
    Quantum.Xmss.Hybrid.R0.card_cap]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hn

/-- **The bad fraction of the stages at Keccak's sizes** (`G = 18`, `|J| ≤ 2^256`):
`schemeGood`'s fraction and the bad permutations, plus `2^-574` for the rate collisions, plus per
computation `qsᵢ / 2^256 + qᵢ / 2^464`. -/
theorem seedKGood_frac_le_keccak {J : Type} [Fintype J] [DecidableEq J]
    {cell : J → PublicParameter → Secret → X} {ι : Type} {β : ι → Type} [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs i)
    (hcell : ∀ P s, Function.Injective fun a ↦ cell a P s)
    (hsep : ∀ P s a b, skCell P s.1 b ≠ cell a P s) (hJ : Fintype.card J ≤ 2 ^ 256) :
    (Fintype.card (Tab × SeedKS) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Tab × SeedKS) - (seedKGood cell Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
        ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z))) +
      ENNReal.ofReal (1 / 2 ^ 574) +
      ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + ENNReal.ofReal (q i / 2 ^ 464)) :=
  (seedKGood_frac_le cell 18 Q q qs hq hqs hcell hsep).trans
    (add_le_add (add_le_add le_rfl (seedRateTerm_le_keccak hJ))
      (Finset.sum_le_sum fun i _ ↦ add_le_add le_rfl (seedReadTerm_le_keccak (q i))))

end keccak

end Quantum.Sphincs.Hybrid

end
