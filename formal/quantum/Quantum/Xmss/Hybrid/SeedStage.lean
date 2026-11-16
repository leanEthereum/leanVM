module

public import Quantum.Xmss.Assembly.MassesR0

@[expose] public section

/-!
# The seed paths' `k`- and `k'`-stages

The seed paths (the master seed's derivation, the parameter's and the chain starts', indexed by
`SeedIdx`, SchemeSplit's `posOf` index) read `k` at their first blocks `hidCell P S S₀ b`, `k'` at
their rates and `h` at their capacities. `schemeSplit` hides the capacities' `h`-values, but the
`k`- and `k'`-values stay in the public keys, so the paths' rates and capacities are functions of
public data and the seeds. Two more exchanges, composed after `r0Split` (R0Stage's stages over the
labels, so the `k`- and `k'`-stages run over `SeedIdx ⊕ J` in effect: r0-design, section 4,
"Optional, recommended"), move these values into slots `SeedKS`, which join the never-revealed
part:

* `stageS`: `k` at the seed paths' first blocks with the `k`-slots (the cells are distinct:
  `hidCell_injective`, so no guard is needed);
* `stageS'`: `k'` at the seed paths' rates with the `k'`-slots, when the rates are distinct.

`seedKSplit : CTab J × SeedKS ≃ (CPub J × MasterSeed) × SeedKS` composes them after `r0Split`. It
keeps everything `r0Split` produces except the keys `k`, `k'` at the seed paths' cells
(`seedKSplit_spec`, `seedKSplit_perm`, `seedKSplit_seed`, `seedKSplit_slots`, `seedKSplit_coins`,
...).

* **Coordinates on the good set** (`seedKGood`: `r0Good`, the seed and label rates distinct
  (`SeedRateInj`), no computation reading a seed path's `k`- or `k'`-cell (`SeedReadGood`)): the
  slots hold the table's `k` and `k'` on the seed paths (`seedKSplit_coords`), and the
  challenger's data is a function of the public part (`schemeData_eq_pubData_seedKSplit`).
* **The seed paths' cells over the slots** (`seedHSlots`, `seedK'Slots`; `seedKGood_subsets`): on
  the good set the table's seed capacities and rates (MassesR0's `seedH`, `seedK'`) are these at
  R0Stage's coordinates `rkOf` and the seed slots: MassesR0's `hseed`.
* **Multiplicities** (`sum_indicator_seedHSlots_le`, `sum_indicator_seedK'Slots_le`): a point is a
  seed capacity for at most `|A| / |Z|` and a seed rate (on a `PermGood π G`) for at most
  `|A| G / |Z|` of the never-revealed part with the seed slots, both at most
  `seedEps G = |A| (G + 1) / |Z|`, `A = SeedIdx`: MassesR0's `hA`, `hA'` with `εA = seedEps G`.
* **The bad fraction** (`seedKGood_frac_le`): `r0Good`'s, the bad permutations, the rate
  collisions `|A ⊕ J|² / |X|` (averaged over `π`), and per computation `(qs₀ᵢ + qs₁ᵢ) / 2^256`
  (reads of the seed paths' `k`-cells) plus `|A| G qᵢ / |Z|` (reads of their rates, the `k`-slots
  resampled).
* **At Keccak's sizes** (`G = 18`): `seedEps_le_keccak` (`seedEps 18 ≤ 2^-469`),
  `seedKGood_frac_le_keccak` (`2^-510` for the rate collisions, `qᵢ / 2^469` per computation).
-/

open scoped ENNReal

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Sponge

/-! ## A uniform slot, over abstract types -/

section slotCount

/-- **A uniform slot `κ`**: when a point lies in `T k` only if some coordinate `κ a` of the slot
lies in a set `F a r` of weight at most `c` (`r` the other coordinates), the point weighs at most
`|A| c / |β|`. -/
theorem card_mul_sum_slot_equiv_le {A R β α K : Type*} [Fintype A] [DecidableEq A] [Fintype R]
    [Fintype β] [Fintype K] (e : (A → β) × R ≃ K) (T : K → Set α) (x : α) (F : A → R → Set β)
    (c : ℝ≥0∞) (hT : ∀ y, x ∈ T (e y) → ∃ a, y.1 a ∈ F a y.2)
    (hF : ∀ a r, ∑ w, (F a r).indicator (fun _ ↦ (1 : ℝ≥0∞)) w ≤ c) :
    (Fintype.card β : ℝ≥0∞) * ∑ k, (T k).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      Fintype.card A * c * Fintype.card K := by
  rw [← Fintype.sum_equiv e (fun y ↦ (T (e y)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) _ fun _ ↦ rfl,
    ← Fintype.card_congr e]
  have hpt : ∀ y : (A → β) × R, (T (e y)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ≤
      ∑ a, (F a y.2).indicator (fun _ ↦ (1 : ℝ≥0∞)) (y.1 a) := fun y ↦ by
    by_cases hx : x ∈ T (e y)
    · obtain ⟨a, ha⟩ := hT y hx
      rw [Set.indicator_of_mem hx]
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun a ↦
        (F a y.2).indicator (fun _ ↦ (1 : ℝ≥0∞)) (y.1 a)) (fun _ _ ↦ zero_le) (Finset.mem_univ a))
      rw [Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  calc (Fintype.card β : ℝ≥0∞) * ∑ y : (A → β) × R, (T (e y)).indicator (fun _ ↦ 1) x
      ≤ Fintype.card β * ∑ y : (A → β) × R, ∑ a, (F a y.2).indicator (fun _ ↦ (1 : ℝ≥0∞)) (y.1 a) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ ↦ hpt y) zero_le
    _ = ∑ a, ∑ r, (Fintype.card β : ℝ≥0∞) *
          ∑ κ : A → β, (F a r).indicator (fun _ ↦ (1 : ℝ≥0∞)) (κ a) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
    _ = ∑ a, ∑ r, (∑ w, (F a r).indicator (fun _ ↦ (1 : ℝ≥0∞)) w) * Fintype.card (A → β) :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun r _ ↦
          Assembly.card_mul_sum_apply a _
    _ ≤ ∑ _a : A, ∑ _r : R, c * Fintype.card (A → β) :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun r _ ↦
          mul_le_mul_of_nonneg_right (hF a r) zero_le
    _ = Fintype.card A * c * Fintype.card ((A → β) × R) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Nat.cast_mul]
        ring

end slotCount

/-! ## The seed paths' stages on leanXMSS tables -/

section seed

open HashSig LeanXmss

/-- The seed paths: the master seed's derivation (`none`), the parameter's and the chain starts'
(SchemeSplit's `posOf` index). -/
abbrev SeedIdx : Type := Option (Option CsIdx)

/-- A seed slot is finite (named: the products of these slots are not found otherwise). -/
noncomputable instance instFintypeSeedSlot : Fintype (SeedIdx → Z) :=
  Pi.instFintype

/-- The seed paths' slots: their `k`-slots and their `k'`-slots. -/
abbrev SeedKS : Type := (SeedIdx → Z) × (SeedIdx → Z)

variable {J : Type}

/-- The data the seed stages keep: `h`, the other key, `π`, `S₀`, the public slots, the coin slots,
the scheme seed, and the other seed slot. -/
abbrev RestS (J : Type) : Type :=
  (Z → X) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed × PubSlots × CoinSlots J × MasterSeed ×
    (SeedIdx → Z)

/-- The `k`-stage's view: `k` with the `k`-slots, and the rest. -/
def shufS : (CPub J × MasterSeed) × SeedKS ≃ ((X → Z) × (SeedIdx → Z)) × RestS J where
  toFun y := ((y.1.1.1.1.keys.2.1, y.2.1), (y.1.1.1.1.keys.1, y.1.1.1.1.keys.2.2,
    y.1.1.1.1.perm, y.1.1.1.1.masterSeed, y.1.1.1.2, y.1.1.2, y.1.2, y.2.2))
  invFun p := ((((⟨(p.2.1, p.1.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2.1⟩, p.2.2.2.2.2.1),
    p.2.2.2.2.2.2.1), p.2.2.2.2.2.2.2.1), (p.1.2, p.2.2.2.2.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `k'`-stage's view: `k'` with the `k'`-slots, and the rest. -/
def shufS' : (CPub J × MasterSeed) × SeedKS ≃ ((X → Z) × (SeedIdx → Z)) × RestS J where
  toFun y := ((y.1.1.1.1.keys.2.2, y.2.2), (y.1.1.1.1.keys.1, y.1.1.1.1.keys.2.1,
    y.1.1.1.1.perm, y.1.1.1.1.masterSeed, y.1.1.1.2, y.1.1.2, y.1.2, y.2.1))
  invFun p := ((((⟨(p.2.1, p.2.2.1, p.1.1), p.2.2.2.1, p.2.2.2.2.1⟩, p.2.2.2.2.2.1),
    p.2.2.2.2.2.2.1), p.2.2.2.2.2.2.2.1), (p.2.2.2.2.2.2.2.2, p.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem shufS_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed) (κ κ' : SeedIdx → Z) :
    shufS ((((⟨(h, k, k'), π, S₀⟩, ps), cs), S), (κ, κ')) =
      ((k, κ), (h, k', π, S₀, ps, cs, S, κ')) :=
  rfl

theorem shufS_symm_apply (p : (X → Z) × (SeedIdx → Z)) (h : Z → X) (k' : X → Z)
    (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed)
    (κ' : SeedIdx → Z) :
    shufS.symm (p, (h, k', π, S₀, ps, cs, S, κ')) =
      ((((⟨(h, p.1, k'), π, S₀⟩, ps), cs), S), (p.2, κ')) :=
  rfl

theorem shufS'_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed) (κ κ' : SeedIdx → Z) :
    shufS' ((((⟨(h, k, k'), π, S₀⟩, ps), cs), S), (κ, κ')) =
      ((k', κ'), (h, k, π, S₀, ps, cs, S, κ)) :=
  rfl

theorem shufS'_symm_apply (p : (X → Z) × (SeedIdx → Z)) (h : Z → X) (k : X → Z)
    (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed)
    (κ : SeedIdx → Z) :
    shufS'.symm (p, (h, k, π, S₀, ps, cs, S, κ)) =
      ((((⟨(h, k, p.1), π, S₀⟩, ps), cs), S), (κ, p.2)) :=
  rfl

/-- The `k`-stage's cells: the seed paths' first blocks, for the parameter in slot `1`, the scheme
seed and the master seed. -/
def posS (w : RestS J) (b : SeedIdx) : X :=
  hidCell (trunc128 w.2.2.2.2.1.2.1) w.2.2.2.2.2.2.1 w.2.2.2.1 b

/-- The `k'`-stage's cells: the seed paths' rates with the `k`-slots. -/
def posS' (w : RestS J) (b : SeedIdx) : X :=
  (w.2.2.1 (posS w b, w.2.2.2.2.2.2.2 b)).1

/-- **The seed paths' `k`-stage**: `k` at the seed paths' first blocks takes the `k`-slots, which
take its values. -/
noncomputable def stageS : (CPub J × MasterSeed) × SeedKS ≃ (CPub J × MasterSeed) × SeedKS :=
  (shufS.trans (stageN (posS (J := J)) fun _ _ ↦ (0 : Z))).trans shufS.symm

/-- **The seed paths' `k'`-stage**: `k'` at the seed paths' rates takes the `k'`-slots, which take
its values, when the rates are distinct. -/
noncomputable def stageS' : (CPub J × MasterSeed) × SeedKS ≃ (CPub J × MasterSeed) × SeedKS :=
  (shufS'.trans (stageN (posS' (J := J)) fun _ _ ↦ (0 : Z))).trans shufS'.symm

theorem stageS_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed) (κ κ' : SeedIdx → Z) :
    ∃ (k₂ : X → Z) (κ₂ : SeedIdx → Z),
      stageS ((((⟨(h, k, k'), π, S₀⟩, ps), cs), S), (κ, κ')) =
        ((((⟨(h, k₂, k'), π, S₀⟩, ps), cs), S), (κ₂, κ')) ∧
      (∀ b, κ₂ b = k (hidCell (trunc128 ps.2.1) S S₀ b)) ∧
      ∀ x, (∀ b, hidCell (trunc128 ps.2.1) S S₀ b ≠ x) → k₂ x = k x := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec (posS (J := J)) (fun _ _ ↦ (0 : Z)) (k, κ)
    (h, k', π, S₀, ps, cs, S, κ')
  obtain ⟨h1, h2⟩ := hsp (hidCell_injective (trunc128 ps.2.1) S S₀)
  refine ⟨p'.1, p'.2, ?_, fun b ↦ (h1 b).trans (zero_add _), h2⟩
  rw [stageS, Equiv.trans_apply, Equiv.trans_apply, shufS_apply, hp', shufS_symm_apply]

theorem stageS'_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed) (κ κ' : SeedIdx → Z) :
    ∃ (k'₂ : X → Z) (κ'₂ : SeedIdx → Z),
      stageS' ((((⟨(h, k, k'), π, S₀⟩, ps), cs), S), (κ, κ')) =
        ((((⟨(h, k, k'₂), π, S₀⟩, ps), cs), S), (κ, κ'₂)) ∧
      (Function.Injective (fun b ↦ (π (hidCell (trunc128 ps.2.1) S S₀ b, κ b)).1) →
        (∀ b, κ'₂ b = k' (π (hidCell (trunc128 ps.2.1) S S₀ b, κ b)).1) ∧
          ∀ x, (∀ b, (π (hidCell (trunc128 ps.2.1) S S₀ b, κ b)).1 ≠ x) → k'₂ x = k' x) := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec (posS' (J := J)) (fun _ _ ↦ (0 : Z)) (k', κ')
    (h, k, π, S₀, ps, cs, S, κ)
  refine ⟨p'.1, p'.2, ?_, fun hinj ↦ ?_⟩
  · rw [stageS', Equiv.trans_apply, Equiv.trans_apply, shufS'_apply, hp', shufS'_symm_apply]
  · obtain ⟨h1, h2⟩ := hsp hinj
    exact ⟨fun b ↦ (h1 b).trans (zero_add _), h2⟩

/-- The seed paths' stages. -/
noncomputable def seedKStages : (CPub J × MasterSeed) × SeedKS ≃ (CPub J × MasterSeed) × SeedKS :=
  (stageS (J := J)).trans stageS'

/-- **The seed paths' stages**: they keep `h`, `π`, `S₀`, the public slots, the coin slots and the
scheme seed. The `k`-slots take `k` at the seed paths' first blocks, and `k` keeps its values off
them; when the seed paths' rates are distinct, the `k'`-slots take `k'` at them, and `k'` keeps its
values off them. -/
theorem seedKStages_spec (L : HonestTable) (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed)
    (sk : SeedKS) :
    ∃ (k₂ k'₂ : X → Z) (sk₂ : SeedKS),
      seedKStages ((((L, ps), cs), S), sk) =
        ((((⟨(L.keys.1, k₂, k'₂), L.perm, L.masterSeed⟩, ps), cs), S), sk₂) ∧
      (∀ b, sk₂.1 b = L.keys.2.1 (hidCell (trunc128 ps.2.1) S L.masterSeed b)) ∧
      (∀ x, (∀ b, hidCell (trunc128 ps.2.1) S L.masterSeed b ≠ x) → k₂ x = L.keys.2.1 x) ∧
      (Function.Injective (fun b ↦
          rateOf L.keys.2.1 L.perm (hidCell (trunc128 ps.2.1) S L.masterSeed b)) →
        (∀ b, sk₂.2 b =
          L.keys.2.2 (rateOf L.keys.2.1 L.perm (hidCell (trunc128 ps.2.1) S L.masterSeed b))) ∧
        ∀ x, (∀ b, rateOf L.keys.2.1 L.perm (hidCell (trunc128 ps.2.1) S L.masterSeed b) ≠ x) →
          k'₂ x = L.keys.2.2 x) := by
  obtain ⟨⟨h, k, k'⟩, π, S₀⟩ := L
  obtain ⟨κ, κ'⟩ := sk
  obtain ⟨k₂, κ₂, e1, f1, f2⟩ := stageS_spec h k k' π S₀ ps cs S κ κ'
  obtain ⟨k'₂, κ'₂, e2, f3⟩ := stageS'_spec h k₂ k' π S₀ ps cs S κ₂ κ'
  refine ⟨k₂, k'₂, (κ₂, κ'₂), ?_, f1, f2, fun hr ↦ ?_⟩
  · rw [seedKStages, Equiv.trans_apply, e1, e2]
  · have hpr : ∀ b, (π (hidCell (trunc128 ps.2.1) S S₀ b, κ₂ b)).1 =
        rateOf k π (hidCell (trunc128 ps.2.1) S S₀ b) := fun b ↦ by rw [f1 b, rateOf]
    obtain ⟨g1, g2⟩ := f3 fun a b hab ↦ hr ((hpr a).symm.trans (hab.trans (hpr b)))
    exact ⟨fun b ↦ (g1 b).trans (congrArg k' (hpr b)),
      fun x hx ↦ g2 x fun b hb ↦ hx b ((hpr b).symm.trans hb)⟩

variable (cell : J → PublicParameter → MasterSeed → X) (ord : J ↪ ℕ)

/-- **The staged swap with the randomizer-base and the seed paths' stages**: the table with the
scheme seed's, the coin and the seed slots as the public part with the coin slots, the scheme seed,
and the seed slots. -/
noncomputable def seedKSplit : CTab J × SeedKS ≃ (CPub J × MasterSeed) × SeedKS :=
  ((r0Split cell ord).prodCongr (Equiv.refl SeedKS)).trans seedKStages

theorem seedKSplit_apply (x : CTab J × SeedKS) :
    seedKSplit cell ord x = seedKStages (r0Split cell ord x.1, x.2) :=
  rfl

/-- The seed paths' first blocks read off the coordinates of `r0Split`. -/
def hidCellOf (y : CPub J × MasterSeed) (b : SeedIdx) : X :=
  hidCell (pubParam y.1.1) y.2 y.1.1.1.masterSeed b

/-- **The seed stages after `r0Split`**: they keep everything `r0Split` gives but `k` and `k'`;
the `k`-slots take `k` at the seed paths' first blocks, `k` keeps its values off them, and when the
seed paths' rates are distinct the `k'`-slots take `k'` at them and `k'` keeps its values off
them. -/
theorem seedKSplit_spec (x : CTab J × SeedKS) :
    ∃ (k₂ k'₂ : X → Z) (sk₂ : SeedKS),
      seedKSplit cell ord x =
        ((((⟨((r0Split cell ord x.1).1.1.1.keys.1, k₂, k'₂), (r0Split cell ord x.1).1.1.1.perm,
          (r0Split cell ord x.1).1.1.1.masterSeed⟩, (r0Split cell ord x.1).1.1.2),
          (r0Split cell ord x.1).1.2), (r0Split cell ord x.1).2), sk₂) ∧
      (∀ b, sk₂.1 b = (r0Split cell ord x.1).1.1.1.keys.2.1 (hidCellOf (r0Split cell ord x.1) b)) ∧
      (∀ y, (∀ b, hidCellOf (r0Split cell ord x.1) b ≠ y) →
        k₂ y = (r0Split cell ord x.1).1.1.1.keys.2.1 y) ∧
      (Function.Injective (fun b ↦ rateOf (r0Split cell ord x.1).1.1.1.keys.2.1
          (r0Split cell ord x.1).1.1.1.perm (hidCellOf (r0Split cell ord x.1) b)) →
        (∀ b, sk₂.2 b = (r0Split cell ord x.1).1.1.1.keys.2.2 (rateOf
          (r0Split cell ord x.1).1.1.1.keys.2.1 (r0Split cell ord x.1).1.1.1.perm
          (hidCellOf (r0Split cell ord x.1) b))) ∧
        ∀ y, (∀ b, rateOf (r0Split cell ord x.1).1.1.1.keys.2.1 (r0Split cell ord x.1).1.1.1.perm
            (hidCellOf (r0Split cell ord x.1) b) ≠ y) →
          k'₂ y = (r0Split cell ord x.1).1.1.1.keys.2.2 y) := by
  obtain ⟨k₂, k'₂, sk₂, hE, f1, f2, f3⟩ := seedKStages_spec (J := J)
    (r0Split cell ord x.1).1.1.1 (r0Split cell ord x.1).1.1.2 (r0Split cell ord x.1).1.2
    (r0Split cell ord x.1).2 x.2
  exact ⟨k₂, k'₂, sk₂, hE, f1, f2, f3⟩

theorem seedKSplit_perm (x : CTab J × SeedKS) :
    (seedKSplit cell ord x).1.1.1.1.perm = x.1.1.1.perm := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec cell ord x
  rw [hE]
  exact r0Split_perm cell ord x.1

/-- **The hidden coordinate is the scheme seed.** -/
theorem seedKSplit_seed (x : CTab J × SeedKS) : (seedKSplit cell ord x).1.2 = x.1.1.1.seed := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec cell ord x
  rw [hE]
  exact r0Split_snd cell ord x.1

theorem seedKSplit_masterSeed (x : CTab J × SeedKS) :
    (seedKSplit cell ord x).1.1.1.1.masterSeed = x.1.1.1.masterSeed := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec cell ord x
  rw [hE]
  exact r0Split_masterSeed cell ord x.1

/-- The seed stages keep the public slots. -/
theorem seedKSplit_slots (x : CTab J × SeedKS) :
    (seedKSplit cell ord x).1.1.1.2 = (r0Split cell ord x.1).1.1.2 := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec cell ord x
  rw [hE]

/-- The seed stages keep the coin slots. -/
theorem seedKSplit_coins (x : CTab J × SeedKS) :
    (seedKSplit cell ord x).1.1.2 = (r0Split cell ord x.1).1.2 := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec cell ord x
  rw [hE]

/-- The seed stages keep `h`. -/
theorem seedKSplit_h (x : CTab J × SeedKS) :
    (seedKSplit cell ord x).1.1.1.1.keys.1 = (r0Split cell ord x.1).1.1.1.keys.1 := by
  obtain ⟨_, _, _, hE, -⟩ := seedKSplit_spec cell ord x
  rw [hE]

/-- The seed paths' first blocks distinct from the labels'. -/
theorem seed_sum_injective
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) (P : PublicParameter)
    (S S₀ : MasterSeed) :
    Function.Injective (Sum.elim (hidCell P S S₀) fun a ↦ cell a P S) :=
  Function.Injective.sumElim (hidCell_injective P S S₀) (cell_injective_of hcell P S)
    fun b a ↦ hsep P S S₀ a b

/-! ### The good set and the coordinate facts -/

variable {ι : Type} {β : ι → Type}

/-- The seed paths' first blocks read off the coordinates of `seedKSplit`. -/
def seedCellK (y : (CPub J × MasterSeed) × SeedKS) (b : SeedIdx) : X :=
  hidCellOf y.1 b

/-- The seed paths' rates read off the coordinates of `seedKSplit` (with the `k`-slots). -/
def seedCellK' (y : (CPub J × MasterSeed) × SeedKS) (b : SeedIdx) : X :=
  (y.1.1.1.1.perm (seedCellK y b, y.2.1 b)).1

/-- No computation `Q i` from the public part reads a seed path's `k`- or `k'`-cell read off the
coordinates. -/
def SeedReadGood (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (y : (CPub J × MasterSeed) × SeedKS) : Prop :=
  ∀ i b, seedCellK y b ∉ kCells (pubData Q y.1.1.1 i).2 ∧
    seedCellK' y b ∉ k'Cells (pubData Q y.1.1.1 i).2

/-- The rates of the seed paths and of the labels' paths, after `schemeSplit`, are distinct. -/
abbrev SeedRateInj (x : Pub × MasterSeed) : Prop :=
  Function.Injective fun c : SeedIdx ⊕ J ↦ rateOf x.1.1.keys.2.1 x.1.1.perm
    (Sum.elim (hidCell (pubParam x.1) x.2 x.1.1.masterSeed) (fun a ↦ cell a (pubParam x.1) x.2) c)

variable [Fintype J] [DecidableEq J]

open scoped Classical in
/-- **The good set** of the seed stages: R0Stage's `r0Good`, distinct seed and label rates
(`SeedRateInj`), and no computation reading a seed path's `k`- or `k'`-cell (`SeedReadGood`).
Irreducible: its membership does not unfold to the enumeration of all tables. -/
@[irreducible]
noncomputable def seedKGood
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Finset (CTab J × SeedKS) :=
  Finset.univ.filter fun x ↦
    x.1 ∈ r0Good cell ord Q ∧ SeedRateInj cell (schemeSplit x.1.1) ∧
      SeedReadGood Q (seedKSplit cell ord x)

variable {cell ord}

theorem mem_seedKGood
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {x : CTab J × SeedKS} :
    x ∈ seedKGood cell ord Q ↔ x.1 ∈ r0Good cell ord Q ∧ SeedRateInj cell (schemeSplit x.1.1) ∧
      SeedReadGood Q (seedKSplit cell ord x) := by
  unfold seedKGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

section coords

variable {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
  (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
  (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S)
  {x : CTab J × SeedKS} (hx : x ∈ seedKGood cell ord Q)

include hcell hsep hx

/-- **The seed paths through `r0Split`**: on the good set, the seed paths' first blocks read off
`r0Split`'s coordinates are the table's, `r0Split`'s `k` and `k'` on the seed paths are the
table's, and the seed paths' rates are distinct. -/
theorem seedKGood_paths :
    (∀ b, hidCellOf (r0Split cell ord x.1) b =
      hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b) ∧
    (∀ b, (r0Split cell ord x.1).1.1.1.keys.2.1 (hidCellOf (r0Split cell ord x.1) b) =
      x.1.1.1.keys.2.1 (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)) ∧
    (∀ b, rateOf (r0Split cell ord x.1).1.1.1.keys.2.1 (r0Split cell ord x.1).1.1.1.perm
        (hidCellOf (r0Split cell ord x.1) b) =
      rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
        (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)) ∧
    (∀ b, (r0Split cell ord x.1).1.1.1.keys.2.2 (rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
        (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)) =
      x.1.1.1.keys.2.2 (rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
        (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b))) ∧
    Function.Injective (fun b ↦ rateOf (r0Split cell ord x.1).1.1.1.keys.2.1
      (r0Split cell ord x.1).1.1.1.perm (hidCellOf (r0Split cell ord x.1) b)) := by
  obtain ⟨hr0, hrate, -⟩ := mem_seedKGood.mp hx
  obtain ⟨⟨hinj, -⟩, ⟨hR, -⟩, -⟩ := mem_r0Good.mp hr0
  obtain ⟨hP, h1, -, -, -⟩ := r0Split_coords hcell hr0
  have hS := r0Split_snd cell ord x.1
  have hS₀ := r0Split_masterSeed cell ord x.1
  have hπ := r0Split_perm cell ord x.1
  obtain ⟨g4, g5, -⟩ := r0Split_keys_eq cell ord x.1 hcell hR
  have hks := schemeSplit_keys_snd x.1.1
  have hPs : pubParam (schemeSplit x.1.1).1 = x.1.1.1.param := (schemeSplit_transfer x.1.1 hinj).1
  have hrate' : Function.Injective fun c : SeedIdx ⊕ J ↦ rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
      (Sum.elim (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed)
        (fun a ↦ cell a x.1.1.1.param x.1.1.1.seed) c) := by
    have h : Function.Injective fun c : SeedIdx ⊕ J ↦ rateOf (schemeSplit x.1.1).1.1.keys.2.1
        (schemeSplit x.1.1).1.1.perm (Sum.elim (hidCell (pubParam (schemeSplit x.1.1).1)
          (schemeSplit x.1.1).2 (schemeSplit x.1.1).1.1.masterSeed)
          (fun a ↦ cell a (pubParam (schemeSplit x.1.1).1) (schemeSplit x.1.1).2) c) := hrate
    rwa [congrArg Prod.fst hks, schemeSplit_perm, hPs, schemeSplit_snd,
      schemeSplit_masterSeed] at h
  have hc : ∀ b, hidCellOf (r0Split cell ord x.1) b =
      hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b := fun b ↦ by
    unfold hidCellOf
    rw [hP, hS, hS₀]
  have hpk : ∀ a, pubCellK cell (r0Split cell ord x.1) a = cell a x.1.1.1.param x.1.1.1.seed :=
    fun a ↦ by
      unfold pubCellK
      rw [hP, hS]
  have hk : ∀ b, (r0Split cell ord x.1).1.1.1.keys.2.1 (hidCellOf (r0Split cell ord x.1) b) =
      x.1.1.1.keys.2.1 (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b) := fun b ↦ by
    rw [hc b, g4 _ fun a ha ↦ hsep _ _ _ a b (ha.symm.trans (hpk a)), congrArg Prod.fst hks]
  have hr : ∀ b, rateOf (r0Split cell ord x.1).1.1.1.keys.2.1 (r0Split cell ord x.1).1.1.1.perm
      (hidCellOf (r0Split cell ord x.1) b) = rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
        (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b) := fun b ↦ by
    unfold rateOf
    rw [hk b, hc b, hπ]
  have hpk' : ∀ a, pubCellK' cell (r0Split cell ord x.1) a =
      rateOf x.1.1.1.keys.2.1 x.1.1.1.perm (cell a x.1.1.1.param x.1.1.1.seed) := fun a ↦ by
    unfold pubCellK'
    rw [hpk a, h1 a, hπ]
    rfl
  refine ⟨hc, hk, hr, fun b ↦ ?_, fun b b' h ↦ Sum.inl_injective
    (hrate' (a₁ := Sum.inl b) (a₂ := Sum.inl b') ((hr b).symm.trans (h.trans (hr b'))))⟩
  rw [g5 (rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
      (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)) fun a ha ↦ Sum.inr_ne_inl
    (hrate' (a₁ := Sum.inr a) (a₂ := Sum.inl b) ((hpk' a).symm.trans ha)),
    congrArg Prod.snd hks]

/-- **The coordinate facts**: on the good set, the seed slots hold the table's `k` at the seed
paths' first blocks and its `k'` at their rates. -/
theorem seedKSplit_coords :
    (∀ b, (seedKSplit cell ord x).2.1 b =
      x.1.1.1.keys.2.1 (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)) ∧
    ∀ b, (seedKSplit cell ord x).2.2 b = x.1.1.1.keys.2.2 (rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
      (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)) := by
  obtain ⟨-, hk, hr, hk', hguard⟩ := seedKGood_paths hcell hsep hx
  obtain ⟨k₂, k'₂, sk₂, hE, f1, -, f3⟩ := seedKSplit_spec cell ord x
  obtain ⟨f4, -⟩ := f3 hguard
  rw [hE]
  exact ⟨fun b ↦ (f1 b).trans (hk b), fun b ↦ (f4 b).trans ((congrArg _ (hr b)).trans (hk' b))⟩

/-- **On the good set, the challenger's data is a function of the public part.** -/
theorem schemeData_eq_pubData_seedKSplit :
    schemeData Q x.1.1.1 = pubData Q (seedKSplit cell ord x).1.1.1 := by
  obtain ⟨hr0, -, hread⟩ := mem_seedKGood.mp hx
  obtain ⟨-, -, -, -, hguard⟩ := seedKGood_paths hcell hsep hx
  rw [schemeData_eq_pubData_r0Split hcell hr0]
  obtain ⟨k₂, k'₂, sk₂, hE, f1, f2, f3⟩ := seedKSplit_spec cell ord x
  obtain ⟨-, f5⟩ := f3 hguard
  have hpd : pubData Q (seedKSplit cell ord x).1.1.1 = fun i ↦ honestEval
      ((r0Split cell ord x.1).1.1.1.keys.1, k₂, k'₂) (r0Split cell ord x.1).1.1.1.perm
      (Q i (pubParam (r0Split cell ord x.1).1.1) (pubCs (r0Split cell ord x.1).1.1)) := by
    rw [hE]
    rfl
  rw [hpd]
  funext i
  change honestEval (r0Split cell ord x.1).1.1.1.keys (r0Split cell ord x.1).1.1.1.perm
      (Q i (pubParam (r0Split cell ord x.1).1.1) (pubCs (r0Split cell ord x.1).1.1)) = _
  refine honestEval_congr (t := ((r0Split cell ord x.1).1.1.1.keys.1, k₂, k'₂))
    (t' := (r0Split cell ord x.1).1.1.1.keys) (r0Split cell ord x.1).1.1.1.perm _ fun e he ↦ ?_
  have ha := honestEval_answeredBy (r0Split cell ord x.1).1.1.1.perm
    ((r0Split cell ord x.1).1.1.1.keys.1, k₂, k'₂) _ e he
  have hri := fun b ↦ hread i b
  rw [hpd] at hri
  cases e with
  | h z v =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    exact ha
  | k y v =>
    have hy : ∀ b, hidCellOf (r0Split cell ord x.1) b ≠ y := fun b hb ↦ (hri b).1 (by
      have hsc : seedCellK (seedKSplit cell ord x) b = hidCellOf (r0Split cell ord x.1) b := by
        rw [hE]
        rfl
      rw [hsc, hb]
      exact mem_kCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← f2 y hy]
    exact ha
  | k' y v =>
    have hy : ∀ b, rateOf (r0Split cell ord x.1).1.1.1.keys.2.1 (r0Split cell ord x.1).1.1.1.perm
        (hidCellOf (r0Split cell ord x.1) b) ≠ y := fun b hb ↦ (hri b).2 (by
      have hsc : seedCellK' (seedKSplit cell ord x) b = rateOf
          (r0Split cell ord x.1).1.1.1.keys.2.1 (r0Split cell ord x.1).1.1.1.perm
          (hidCellOf (r0Split cell ord x.1) b) := by
        rw [hE]
        unfold seedCellK' rateOf
        rw [f1 b]
        rfl
      rw [hsc, hb]
      exact mem_k'Cells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← f5 y hy]
    exact ha

end coords

/-! ### The bad fraction -/

open scoped Classical

variable (cell ord) (G : ℕ)

/-- A table outside R0Stage's good set. -/
noncomputable def r0Bad
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (θ : CTab J) : ℕ :=
  if θ ∈ r0Good cell ord Q then 0 else 1

/-- Colliding seed or label rates (any permutation). -/
noncomputable def seedRateBad (x : Pub × MasterSeed) : ℕ :=
  if ¬SeedRateInj cell x then 1 else 0

/-- The computation `Q i` reads `k` at the seed path `b`'s first block. -/
noncomputable def seedKHit
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (b : SeedIdx) (y : (CPub J × MasterSeed) × SeedKS) : ℕ :=
  if seedCellK y b ∈ kCells (pubData Q y.1.1.1 i).2 then 1 else 0

/-- A good permutation and the computation `Q i` reading `k'` at the seed path `b`'s rate. -/
noncomputable def seedK'Hit
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (b : SeedIdx) (y : (CPub J × MasterSeed) × SeedKS) : ℕ :=
  if PermGood y.1.1.1.1.perm G ∧ seedCellK' y b ∈ k'Cells (pubData Q y.1.1.1 i).2 then 1 else 0

/-- The seed paths' first blocks read by `Q i`. -/
noncomputable def seedReadK
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (y : (CPub J × MasterSeed) × SeedKS) : ℕ :=
  ∑ b, seedKHit Q i b y

/-- The seed paths' rates read by `Q i`. -/
noncomputable def seedReadK'
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (y : (CPub J × MasterSeed) × SeedKS) : ℕ :=
  ∑ b, seedK'Hit G Q i b y

/-- The tables outside the good set: outside `r0Good`, a bad permutation, colliding seed or label
rates, or a computation reading a seed path's `k`- or `k'`-cell. -/
theorem card_sub_card_seedKGood_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Fintype.card (CTab J × SeedKS) - (seedKGood cell ord Q).card ≤
      ∑ x : CTab J × SeedKS, ((r0Bad cell ord Q x.1 + permBad G x.1.1) +
        (seedRateBad cell (schemeSplit x.1.1) + ∑ i, (seedReadK Q i (seedKSplit cell ord x) +
          seedReadK' G Q i (seedKSplit cell ord x)))) := by
  refine card_sub_card_le_sum (seedKGood cell ord Q) _ fun x hx ↦ ?_
  rw [mem_seedKGood] at hx
  by_cases h0 : x.1 ∈ r0Good cell ord Q
  · by_cases hG : PermGood x.1.1.1.perm G
    · by_cases hr : SeedRateInj cell (schemeSplit x.1.1)
      · have hread : ¬SeedReadGood Q (seedKSplit cell ord x) := fun h ↦ hx ⟨h0, hr, h⟩
        obtain ⟨i, b, hib⟩ : ∃ i b,
            ¬(seedCellK (seedKSplit cell ord x) b ∉
                kCells (pubData Q (seedKSplit cell ord x).1.1.1 i).2 ∧
              seedCellK' (seedKSplit cell ord x) b ∉
                k'Cells (pubData Q (seedKSplit cell ord x).1.1.1 i).2) := by
          by_contra hne
          exact hread fun i b ↦ by_contra fun h ↦ hne ⟨i, b, h⟩
        have hG' : PermGood (seedKSplit cell ord x).1.1.1.1.perm G := by
          rw [seedKSplit_perm]
          exact hG
        have h1 : 1 ≤ seedReadK Q i (seedKSplit cell ord x) +
            seedReadK' G Q i (seedKSplit cell ord x) := by
          change 1 ≤ (∑ b', seedKHit Q i b' (seedKSplit cell ord x)) +
            ∑ b', seedK'Hit G Q i b' (seedKSplit cell ord x)
          have hk : seedKHit Q i b (seedKSplit cell ord x) ≤
              ∑ b', seedKHit Q i b' (seedKSplit cell ord x) :=
            Finset.single_le_sum (f := fun b' ↦ seedKHit Q i b' (seedKSplit cell ord x))
              (fun _ _ ↦ Nat.zero_le _) (by simp)
          have hk' : seedK'Hit G Q i b (seedKSplit cell ord x) ≤
              ∑ b', seedK'Hit G Q i b' (seedKSplit cell ord x) :=
            Finset.single_le_sum (f := fun b' ↦ seedK'Hit G Q i b' (seedKSplit cell ord x))
              (fun _ _ ↦ Nat.zero_le _) (by simp)
          by_cases m1 : seedCellK (seedKSplit cell ord x) b ∈
              kCells (pubData Q (seedKSplit cell ord x).1.1.1 i).2
          · have : seedKHit Q i b (seedKSplit cell ord x) = 1 := ite_eq_left m1
            omega
          · have m2 : seedCellK' (seedKSplit cell ord x) b ∈
                k'Cells (pubData Q (seedKSplit cell ord x).1.1.1 i).2 :=
              by_contra fun m2 ↦ hib ⟨m1, m2⟩
            have : seedK'Hit G Q i b (seedKSplit cell ord x) = 1 := ite_eq_left ⟨hG', m2⟩
            omega
        have h2 : seedReadK Q i (seedKSplit cell ord x) +
            seedReadK' G Q i (seedKSplit cell ord x) ≤
            ∑ i', (seedReadK Q i' (seedKSplit cell ord x) +
              seedReadK' G Q i' (seedKSplit cell ord x)) :=
          Finset.single_le_sum (f := fun i' ↦ seedReadK Q i' (seedKSplit cell ord x) +
            seedReadK' G Q i' (seedKSplit cell ord x)) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ i)
        omega
      · have : seedRateBad cell (schemeSplit x.1.1) = 1 := ite_eq_left hr
        omega
    · have : permBad G x.1.1 = 1 := ite_eq_left hG
      omega
  · have : r0Bad cell ord Q x.1 = 1 := ite_eq_right h0
    omega

/-- **Seed and label rate collisions, averaged over `π`**: at most `|A ⊕ J|² / |X|` of the
coordinates. -/
theorem card_mul_sum_seedRateBad_le
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    Fintype.card X * ∑ x, seedRateBad cell x ≤
      Fintype.card (Pub × MasterSeed) * (Fintype.card (SeedIdx ⊕ J) * Fintype.card (SeedIdx ⊕ J)) :=
  card_mul_sum_equiv_prod_le coordPi _ _ (seedRateBad cell) fun r ↦
    card_mul_sum_not_injective_rate_le
      (fun c ↦ (Sum.elim (hidCell (trunc128 r.2.2.1.2.1) r.2.2.2 r.2.1)
          (fun a ↦ cell a (trunc128 r.2.2.1.2.1) r.2.2.2) c,
        r.1.2.1 (Sum.elim (hidCell (trunc128 r.2.2.1.2.1) r.2.2.2 r.2.1)
          (fun a ↦ cell a (trunc128 r.2.2.1.2.1) r.2.2.2) c)))
      fun _ _ h ↦ seed_sum_injective cell hcell hsep _ _ _ (congrArg Prod.fst h)

/-- The keys and the permutation. -/
abbrev KeysPerm : Type := SpongeKeys X Z × Equiv.Perm (X × Z)

/-- The keys and the permutation are finite (named: the products with them are not found
otherwise). -/
noncomputable instance instFintypeKeysPerm : Fintype KeysPerm :=
  instFintypeProd _ _

/-- The coordinates with the master seed first. -/
def seedE0 : MasterSeed × (KeysPerm × PubSlots × CoinSlots J × MasterSeed × SeedKS) ≃
    (CPub J × MasterSeed) × SeedKS where
  toFun c := ((((⟨c.2.1.1, c.2.1.2, c.1⟩, c.2.2.1), c.2.2.2.1), c.2.2.2.2.1), c.2.2.2.2.2)
  invFun y := (y.1.1.1.1.masterSeed,
    ((y.1.1.1.1.keys, y.1.1.1.1.perm), y.1.1.1.2, y.1.1.2, y.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinates with the scheme seed first. -/
def seedES : MasterSeed × (KeysPerm × MasterSeed × PubSlots × CoinSlots J × SeedKS) ≃
    (CPub J × MasterSeed) × SeedKS where
  toFun c := ((((⟨c.2.1.1, c.2.1.2, c.2.2.1⟩, c.2.2.2.1), c.2.2.2.2.1), c.1), c.2.2.2.2.2)
  invFun y := (y.1.2,
    ((y.1.1.1.1.keys, y.1.1.1.1.perm), y.1.1.1.1.masterSeed, y.1.1.1.2, y.1.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinates with the `k`-slots first. -/
def seedEK : (SeedIdx → Z) × ((CPub J × MasterSeed) × (SeedIdx → Z)) ≃
    (CPub J × MasterSeed) × SeedKS where
  toFun c := (c.2.1, (c.1, c.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The seed paths' first blocks are rarely read**: at most `(qs₀ + qs₁) / 2^256` of the
coordinates, where `qs₀` bounds the reads of `Q i` at seed-shaped `k`-cells and `qs₁` at seed-keyed
cells. -/
theorem card_mul_sum_seedReadK_le
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (qs₀ qs₁ : ι → ℕ)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i) (i : ι) :
    Fintype.card MasterSeed * ∑ y, seedReadK (J := J) Q i y ≤
      Fintype.card ((CPub J × MasterSeed) × SeedKS) * (qs₀ i + qs₁ i) := by
  have hsplit : ∀ y : (CPub J × MasterSeed) × SeedKS,
      seedReadK Q i y = seedKHit Q i none y + ∑ c, seedKHit Q i (some c) y :=
    fun y ↦ Fintype.sum_option _
  rw [Finset.sum_congr rfl fun y _ ↦ hsplit y, Finset.sum_add_distrib, mul_add, mul_add]
  refine add_le_add ?_ ?_
  · refine card_mul_sum_equiv_prod_le seedE0 _ _ (fun y ↦ seedKHit Q i none y) fun r ↦
      Nat.mul_le_mul_left _ ?_
    change ∑ S₀ : MasterSeed, (if seedCell S₀ ∈ kCells (honestEval r.1.1 r.1.2
      (Q i (trunc128 r.2.1.2.1) fun j ↦ out256 (r.2.1.2.2 j))).2 then 1 else 0) ≤ qs₀ i
    exact (sum_ite_mem_le_card_filter seedCell seedCell_injective _ SeedShaped
      seedShaped_seedCell).trans (hqs₀ i _ _ _ _)
  · refine card_mul_sum_equiv_prod_le seedES _ _ (fun y ↦ ∑ c, seedKHit Q i (some c) y)
      fun r ↦ Nat.mul_le_mul_left _ ?_
    change ∑ S : MasterSeed, ∑ c : Option CsIdx, (if skCell (trunc128 r.2.2.1.2.1) S c ∈
      kCells (honestEval r.1.1 r.1.2
        (Q i (trunc128 r.2.2.1.2.1) fun j ↦ out256 (r.2.2.1.2.2 j))).2 then 1 else 0) ≤ qs₁ i
    rw [← Fintype.sum_prod_type']
    exact (sum_ite_mem_le_card_filter (fun p : MasterSeed × Option CsIdx ↦
      skCell (trunc128 r.2.2.1.2.1) p.1 p.2) (skCell_injective _) _
      (fun x ↦ ∃ S b, skCell (trunc128 r.2.2.1.2.1) S b = x) fun p ↦ ⟨p.1, p.2, rfl⟩).trans
      (hqs₁ i _ _ _ _)

/-- **The seed paths' rates are rarely read**: at most `|A| G q / |Z|` of the coordinates, the
`k`-slots resampled. -/
theorem card_mul_sum_seedReadK'_le
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i) (i : ι) :
    Fintype.card Z * ∑ y, seedReadK' (J := J) G Q i y ≤
      Fintype.card ((CPub J × MasterSeed) × SeedKS) * (Fintype.card SeedIdx * G * q i) := by
  refine card_mul_sum_equiv_prod_le seedEK _ _ (seedReadK' G Q i) fun r ↦ ?_
  calc Fintype.card Z * ∑ κ, seedReadK' G Q i (seedEK (κ, r))
      = ∑ b, Fintype.card Z * ∑ κ, seedK'Hit G Q i b (seedEK (κ, r)) := by
        simp only [seedReadK']
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _b : SeedIdx, Fintype.card (SeedIdx → Z) * (q i * G) :=
        Finset.sum_le_sum fun b _ ↦ card_mul_sum_le_of_update
          (fun κ ↦ seedK'Hit G Q i b (seedEK (κ, r))) b _ fun κ ↦ by
            change ∑ w, (if PermGood r.1.1.1.1.perm G ∧ (r.1.1.1.1.perm
              (hidCellOf r.1 b, Function.update κ b w b)).1 ∈ k'Cells (pubData Q r.1.1.1 i).2
              then 1 else 0) ≤ q i * G
            simp only [Function.update_self]
            by_cases hG : PermGood r.1.1.1.1.perm G
            · simp only [hG, true_and]
              exact (sum_ite_comp_mem_le (fun w ↦ (r.1.1.1.1.perm (hidCellOf r.1 b, w)).1) _ G
                fun x₂ ↦ hG.rate _ x₂).trans
                  (Nat.mul_le_mul_right _ ((card_k'Cells_le _).trans (hq i _ _ _ _)))
            · simp only [hG, false_and, ↓reduceIte, Finset.sum_const_zero]
              exact Nat.zero_le _
    _ = Fintype.card (SeedIdx → Z) * (Fintype.card SeedIdx * G * q i) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- **The bad fraction of the seed stages**: the fraction of tables outside `seedKGood cell ord Q`
is at most the fraction outside `r0Good cell ord Q`, plus the fraction of permutations with a rate
count above `G`, plus the rate collisions `|A ⊕ J|² / |X|` (averaged over the permutation), plus
per computation `(qs₀ᵢ + qs₁ᵢ) / 2^256 + |A| G qᵢ / |Z|`, `A = SeedIdx`, where `qᵢ` bounds the reads
of `Q i`, `qs₀ᵢ` its reads at seed-shaped `k`-cells and `qs₁ᵢ` at seed-keyed cells. The labels'
first blocks are distinct for distinct labels or seeds (`hcell`) and differ from the seed paths'
(`hsep`). -/
theorem seedKGood_frac_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₀ qs₁ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i)
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    (Fintype.card (CTab J × SeedKS) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (CTab J × SeedKS) - (seedKGood cell ord Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card (CTab J) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (CTab J) - (r0Good cell ord Q).card : ℕ) : ℝ≥0∞) +
        ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z))) +
      ((Fintype.card (SeedIdx ⊕ J) * Fintype.card (SeedIdx ⊕ J) : ℕ) : ℝ≥0∞) /
        Fintype.card X +
      ∑ i, (((qs₀ i + qs₁ i : ℕ) : ℝ≥0∞) / 2 ^ 256 +
        ((Fintype.card SeedIdx * G * q i : ℕ) : ℝ≥0∞) / Fintype.card Z) := by
  refine inv_mul_le_of_parts Fintype.card_ne_zero
    ((card_sub_card_seedKGood_le cell ord G Q).trans_eq (sum_add_sum_eq _ _ _ _)) ?_ ?_ ?_ ?_
  · rw [Finset.sum_add_distrib, Nat.cast_add, mul_add]
    refine add_le_add (le_of_eq ?_) ?_
    · have hs : ∑ θ : CTab J, r0Bad cell ord Q θ =
          Fintype.card (CTab J) - (r0Good cell ord Q).card :=
        sum_ite_mem_zero_one_eq (r0Good cell ord Q)
      rw [sum_fst_eq (r0Bad cell ord Q), hs]
      exact natCast_smul_eq_card_mul _
    · exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
        (card_mul_sum_fst_eq (α := CTab J) (γ := SeedKS) (fun θ ↦ permBad G θ.1) _ _
          (card_mul_sum_fst_eq (γ := CoinSlots J) (permBad G) _ _
            (card_mul_sum_tab_not_permGood G))).le
  · have hrate := card_mul_sum_seedRateBad_le cell hcell hsep
    rw [← Fintype.card_congr schemeSplit] at hrate
    exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_fst_equiv_le (γ := SeedKS) (Equiv.refl (CTab J))
        (fun θ ↦ seedRateBad cell (schemeSplit θ.1)) _ _
        (card_mul_sum_fst_equiv_le (γ := CoinSlots J) schemeSplit (seedRateBad cell) _ _ hrate))
  · intro i
    have h := natCast_le_mul_div_of_mul_le (Fintype.card_ne_zero (α := MasterSeed))
      (card_mul_sum_equiv_le (seedKSplit cell ord) (seedReadK Q i) _ _
        (card_mul_sum_seedReadK_le Q qs₀ qs₁ hqs₀ hqs₁ i))
    rwa [card_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h
  · intro i
    exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le (seedKSplit cell ord) (seedReadK' G Q i) _ _
        (card_mul_sum_seedReadK'_le G Q q hq i))

end seed

/-! ## The seed paths' cells over the never-revealed part with the seed slots -/

section seedSlots

open HashSig LeanXmss

/-- The seed paths' capacities at the never-revealed part `k = (S, S₀, κ, κ')` and the seed slots:
first block `hidCell P S S₀ b`, `k`-value `sk.1 b`, `k'`-value `sk.2 b`. -/
def seedHSlots (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : Assembly.RK) (sk : SeedKS) :
    Set Z :=
  Set.range fun b ↦ capOf (fun _ ↦ sk.1 b) (fun _ ↦ sk.2 b) π (hidCell P k.1 k.2.1 b)

/-- The seed paths' rates at the never-revealed part and the seed slots, on a good permutation. -/
def seedK'Slots (G : ℕ) (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : Assembly.RK)
    (sk : SeedKS) : Set X :=
  {x | PermGood π G ∧ ∃ b, (π (hidCell P k.1 k.2.1 b, sk.1 b)).1 = x}

/-- **The per-call multiplicity of the seed paths' rates and capacities**: `|A| (G + 1) / |Z|`,
`A = SeedIdx`. -/
noncomputable def seedEps (G : ℕ) : ℝ≥0∞ :=
  (Fintype.card SeedIdx : ℝ≥0∞) * (G + 1) / Fintype.card Z

variable {W : Type} [Fintype W]

/-- The never-revealed part with the seed slots and a pad, the `k'`-slots first. -/
def seedEH : (SeedIdx → Z) × (Assembly.RK × ((SeedIdx → Z) × W)) ≃ Assembly.RK × (SeedKS × W) where
  toFun y := (y.2.1, ((y.2.2.1, y.1), y.2.2.2))
  invFun k := (k.2.1.2, (k.1, (k.2.1.1, k.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The never-revealed part with the seed slots and a pad, the `k`-slots first. -/
def seedEK' : (SeedIdx → Z) × (Assembly.RK × ((SeedIdx → Z) × W)) ≃
    Assembly.RK × (SeedKS × W) where
  toFun y := (y.2.1, ((y.1, y.2.2.1), y.2.2.2))
  invFun k := (k.2.1.1, (k.1, (k.2.1.2, k.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The seed paths' capacities** (MassesR0's `hA`): a capacity is a seed path's for at most an
`|A| / |Z| ≤ seedEps G` fraction of the never-revealed part with the seed slots (the `k'`-slot is
uniform). -/
theorem sum_indicator_seedHSlots_le (G : ℕ) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (z : Z) :
    ∑ k : Assembly.RK × (SeedKS × W), (seedHSlots π P k.1 k.2.1).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) z ≤ seedEps G * Fintype.card (Assembly.RK × (SeedKS × W)) := by
  have hle : (Fintype.card SeedIdx : ℝ≥0∞) * 1 / Fintype.card Z ≤ seedEps G :=
    ENNReal.div_le_div_right (mul_le_mul_of_nonneg_left le_add_self zero_le) _
  refine (Assembly.le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _) (card_mul_sum_slot_equiv_le seedEH
      (fun k : Assembly.RK × (SeedKS × W) ↦ seedHSlots π P k.1 k.2.1) z
      (fun a r ↦ {w | capOf (fun _ ↦ r.2.1 a) (fun _ ↦ w) π (hidCell P r.1.1 r.1.2.1 a) = z}) 1
      (fun _ hy ↦ hy) fun _ _ ↦ (Assembly.sum_indicator_capOf_eq_one π _ _ z).le)).trans
    (mul_le_mul_of_nonneg_right hle zero_le)

/-- **The seed paths' rates** (MassesR0's `hA'`): on a `PermGood π G`, a cell is a seed path's rate
for at most an `|A| G / |Z| ≤ seedEps G` fraction of the never-revealed part with the seed slots
(the `k`-slot is uniform). -/
theorem sum_indicator_seedK'Slots_le (G : ℕ) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
    (x : X) :
    ∑ k : Assembly.RK × (SeedKS × W), (seedK'Slots G π P k.1 k.2.1).indicator
        (fun _ ↦ (1 : ℝ≥0∞)) x ≤ seedEps G * Fintype.card (Assembly.RK × (SeedKS × W)) := by
  by_cases hG : PermGood π G
  · have hle : (Fintype.card SeedIdx : ℝ≥0∞) * G / Fintype.card Z ≤ seedEps G :=
      ENNReal.div_le_div_right (mul_le_mul_of_nonneg_left le_self_add zero_le) _
    refine (Assembly.le_div_mul_of_mul_le (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _) (card_mul_sum_slot_equiv_le seedEK'
        (fun k : Assembly.RK × (SeedKS × W) ↦ seedK'Slots G π P k.1 k.2.1) x
        (fun a r ↦ {w | (π (hidCell P r.1.1 r.1.2.1 a, w)).1 = x}) G
        (fun _ hy ↦ hy.2) fun _ _ ↦ ?_)).trans (mul_le_mul_of_nonneg_right hle zero_le)
    rw [← Assembly.card_filter_eq_sum_indicator]
    exact_mod_cast hG.rate _ x
  · exact le_of_eq_of_le (Finset.sum_eq_zero fun k _ ↦ Set.indicator_of_notMem
      (fun h ↦ hG h.1) _) zero_le

/-- **MassesR0's `hseed` on the seed stages' good set**: the table's seed capacities and rates
(`seedH`, `seedK'`) are the seed paths' cells at R0Stage's coordinates `rkOf` and the seed slots
(the rates on a `PermGood π G`). -/
theorem seedKGood_subsets
    {ι : Type} {β : ι → Type}
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)} (G : ℕ)
    {x : CTab R0.RLabel × SeedKS} (hx : x ∈ seedKGood R0.rCell R0.rOrd Q)
    (hG : PermGood x.1.1.1.perm G) :
    Assembly.seedH x.1.1.1 ⊆ seedHSlots x.1.1.1.perm x.1.1.1.param (Assembly.rkOf x.1)
        (seedKSplit R0.rCell R0.rOrd x).2 ∧
      Assembly.seedK' x.1.1.1 ⊆ seedK'Slots G x.1.1.1.perm x.1.1.1.param (Assembly.rkOf x.1)
        (seedKSplit R0.rCell R0.rOrd x).2 := by
  obtain ⟨c1, c2⟩ := seedKSplit_coords R0.rCell_injective R0.hidCell_ne_rCell hx
  have hS : (Assembly.rkOf x.1).1 = x.1.1.1.seed := r0Split_snd R0.rCell R0.rOrd x.1
  have hS₀ : (Assembly.rkOf x.1).2.1 = x.1.1.1.masterSeed := rfl
  refine ⟨?_, ?_⟩
  · rintro _ ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    show capOf (fun _ ↦ (seedKSplit R0.rCell R0.rOrd x).2.1 b)
      (fun _ ↦ (seedKSplit R0.rCell R0.rOrd x).2.2 b) x.1.1.1.perm
      (hidCell x.1.1.1.param (Assembly.rkOf x.1).1 (Assembly.rkOf x.1).2.1 b) =
        capOf x.1.1.1.keys.2.1 x.1.1.1.keys.2.2 x.1.1.1.perm
          (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)
    rw [hS, hS₀, c1 b, c2 b]
    rfl
  · rintro _ ⟨b, rfl⟩
    refine ⟨hG, b, ?_⟩
    show (x.1.1.1.perm (hidCell x.1.1.1.param (Assembly.rkOf x.1).1 (Assembly.rkOf x.1).2.1 b,
      (seedKSplit R0.rCell R0.rOrd x).2.1 b)).1 =
        rateOf x.1.1.1.keys.2.1 x.1.1.1.perm
          (hidCell x.1.1.1.param x.1.1.1.seed x.1.1.1.masterSeed b)
    rw [hS, hS₀, c1 b]
    rfl

end seedSlots

/-! ## At Keccak's sizes -/

section keccak

open HashSig LeanXmss

theorem card_seedIdx : Fintype.card SeedIdx = 2 + 2 * 2 ^ 32 * 29 :=
  R0.card_hidIdx

/-- `n (G + 1)` cast, over abstract numbers. -/
theorem natCast_mul_succ (n G : ℕ) :
    (n : ℝ≥0∞) * ((G : ℝ≥0∞) + 1) = ((n * (G + 1) : ℕ) : ℝ≥0∞) := by
  push_cast
  ring

set_option exponentiation.threshold 4096 in
/-- **The seed paths' multiplicity at Keccak's sizes** (`G = 18`): `seedEps 18 ≤ 2^-469`
(`19 |A| / |Z|`, `|A| = 2 + 2^33 · 29`). -/
theorem seedEps_le_keccak : seedEps 18 ≤ ENNReal.ofReal (1 / 2 ^ 469) := by
  unfold seedEps
  rw [natCast_mul_succ, R0.natCast_div_eq_ofReal _ _ Fintype.card_pos]
  apply ENNReal.ofReal_le_ofReal
  rw [card_seedIdx, R0.card_cap]
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The rate collisions at Keccak's sizes**: `|A ⊕ J|² / |X| ≤ 2^-510`. -/
theorem seedRateTerm_le_keccak :
    ((Fintype.card (SeedIdx ⊕ R0.RLabel) * Fintype.card (SeedIdx ⊕ R0.RLabel) : ℕ) : ℝ≥0∞) /
      Fintype.card X ≤ ENNReal.ofReal (1 / 2 ^ 510) := by
  rw [R0.natCast_div_eq_ofReal _ _ Fintype.card_pos]
  apply ENNReal.ofReal_le_ofReal
  rw [Fintype.card_sum, card_seedIdx, R0.card_rLabel, R0.card_rate]
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The rate reads at Keccak's sizes**: `18 |A| q / |Z| ≤ q / 2^469`. -/
theorem seedReadTerm_le_keccak (q : ℕ) :
    ((Fintype.card SeedIdx * 18 * q : ℕ) : ℝ≥0∞) / Fintype.card Z ≤
      ENNReal.ofReal (q / 2 ^ 469) := by
  have hn : (2 + 2 * 2 ^ 32 * 29) * 18 * q * 2 ^ 469 ≤ q * 2 ^ 512 := by
    calc (2 + 2 * 2 ^ 32 * 29) * 18 * q * 2 ^ 469 =
          q * ((2 + 2 * 2 ^ 32 * 29) * 18 * 2 ^ 469) := by
          ring
      _ ≤ q * 2 ^ 512 := Nat.mul_le_mul_left q (by norm_num)
  rw [R0.natCast_div_eq_ofReal _ _ Fintype.card_pos, card_seedIdx, R0.card_cap]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hn

/-- **The bad fraction of the seed stages at Keccak's sizes** (`G = 18`): `r0Good`'s fraction and
the bad permutations, plus `2^-510` for the rate collisions, plus per computation
`(qs₀ᵢ + qs₁ᵢ) / 2^256 + qᵢ / 2^469`. -/
theorem seedKGood_frac_le_keccak {ι : Type} {β : ι → Type} [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₀ qs₁ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i) :
    (Fintype.card (CTab R0.RLabel × SeedKS) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (CTab R0.RLabel × SeedKS) - (seedKGood R0.rCell R0.rOrd Q).card : ℕ) :
          ℝ≥0∞) ≤
      ((Fintype.card (CTab R0.RLabel) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (CTab R0.RLabel) - (r0Good R0.rCell R0.rOrd Q).card : ℕ) : ℝ≥0∞) +
        ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z))) +
      ENNReal.ofReal (1 / 2 ^ 510) +
      ∑ i, (((qs₀ i + qs₁ i : ℕ) : ℝ≥0∞) / 2 ^ 256 + ENNReal.ofReal (q i / 2 ^ 469)) :=
  (seedKGood_frac_le R0.rCell R0.rOrd 18 Q q qs₀ qs₁ hq hqs₀ hqs₁ R0.rCell_injective
    R0.hidCell_ne_rCell).trans (add_le_add (add_le_add le_rfl seedRateTerm_le_keccak)
      (Finset.sum_le_sum fun i _ ↦ add_le_add le_rfl (seedReadTerm_le_keccak (q i))))

end keccak

end Quantum.Xmss.Hybrid

end
