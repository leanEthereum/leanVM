module

public import Quantum.Xmss.Hybrid.R0Stage
public import Quantum.Sphincs.Hybrid.SchemeSplit

@[expose] public section

/-!
# The randomizer stage: `PRF_msg`'s paths in public slots

leanSPHINCS's randomizer `R(M) = Trunc_16(H(SK.prf ‖ PK.seed ‖ M'))` is a one-block hash keyed by
the hidden `SK.prf` (`prfMessageInput`, 93 bytes). Its path reads `k` at the `SK.prf`-keyed first
block `rCell M P R`, `k'` at its rate and `h` at its capacity. As for leanXMSS's randomizer bases
(`Quantum.Xmss.Hybrid.R0Stage`), three exchanges composed after `schemeSplit` move these values into
slots: `k` at every label, `k'` at every label, and `h` at the capacity of each **first** label (no
label of smaller rank has the same capacity). The labels are the messages.

## The path stages, over abstract kept data (the interface DigestStage reuses)

* `PSt E F J := (((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × CoinSlots J) × F`: the keys, `π`,
  data `E` and `F` the stages keep (public slots, hidden values, earlier stages' slots), and the
  coin slots `(J → Z) × (J → Z) × (J → X)` of the labels `J`.
* A cell family `c : E → F → J → X` (the labels' first blocks, a function of kept data only) and a
  rank `ord : J ↪ ℕ` give `pStages c ord : PSt E F J ≃ PSt E F J`: `pStageK` (`k` at `c e f a`
  with the `k`-slots, when the cells are distinct), `pStageK'` (`k'` at the rates with the
  `k'`-slots, when the rates are distinct), `pStageHOn` (`h` at the capacities of the first labels
  with the `h`-slots, which take the blocks' outputs; no guard).
* `pStages_spec`: the stages keep `π`, `E`, `F`; when the cells and their rates are distinct, the
  `k`- and `k'`-slots hold `k`, `k'` at the paths' cells, the `h`-slot of a first label (by
  capacity) the block's output `rate + h (cap)`, that of a non-first label its old value, and the
  keys keep their values off the paths' cells.
* Read off the coordinates: `pCellK`, `pCellK'`, `pCellH` (the paths' cells), `pB` (the non-first
  labels, `mem_pB`), `PReadGood c rd` (no computation `rd i` of the public part `((t, π), e)` reads
  a path cell).
* Counts over `PSt E F J` (`pCoordC` splits off the coin slots): `card_mul_sum_pReadK_le` (reads of
  the first blocks, from a bound on the reads summed over `F`), `card_mul_sum_pReadKH_le` (reads of
  the rates and capacities: `|J| (G + 1) q / |Z|`, the `k`- and `k'`-slots resampled), and
  `card_mul_sum_pBInd_le` (a label is non-first for at most `|J| / |Z|` of the coordinates, its
  `k'`-slot resampled: the averaged charge of Mismatch's non-first labels).

DigestStage instantiates the path stages directly: `J := Message × DigestCall`, its own `E`, `F`
(with the randomizer stage's slots, so its cells may be keyed by the staged randomizer coordinate)
and `c`; it reads its `256`-bit coordinate off the `h`-slot with `outSplit` instead of
`r0SlotEquiv`, and follows the next section's good set and bad fraction with its own hidden key.

## The label stages on leanSPHINCS tables, over the labels

Stated over an abstract label type `J` with cells `cell : J → PublicParameter → HashOutput → X`
keyed by `PK.seed` and `SK.prf`, distinct over `(SK.prf, a)` (`hcell`) and apart from the
`SK.seed`-keyed cells (`hsep`); instantiated at `J = Message` only at the end. (At `Message`, a
`BitVec`, `∀`/`∃` over labels are decided by `BitVec`'s own instances, not `Fintype`'s, so
predicates restated there would not match the generic lemmas; the read bound is stated with the
named predicate `IsCell` for the same reason.)

* `rSplit cell ord : RTab J ≃ RPub J × Secret` (`RTab J = Tab × CoinSlots J`,
  `RPub J = Pub × CoinSlots J`): `schemeSplit`, then `pStages (cellP cell) ord`. The hidden part is
  still `(SK.seed, SK.prf)` (`rSplit_snd`).
* **The good set** `rGood cell ord Q`: `schemeGood`, no static collision of the labels' paths
  (`RColl`: distinct rates, capacities off the hidden capacities), and `PReadGood` for the
  computations `Q`. On it: `rSplit_coords` (the slots hold the table's path values; non-first
  labels keep the table's pad), `pB_rSplit` (the non-first labels read off the coordinates are the
  table's `rB`), `digest_eq_rCoord` (the digest of a first label's one-block input is `rCoord`, the
  first `128` bits of its `h`-slot), `schemeData_eq_pubData_rSplit` (the challenger's data is a
  function of the public part).
* **The bad fraction** `rGood_frac_le`: `schemeGood`'s, the bad permutations, the rate collisions
  `|J|² / |X|` (averaged over `π`), the capacity hits `|J| |A| (G + 1) / |Z|` (`A = SkIdx`), and
  per computation `qsᵢ / 2^256 + |J| (G + 1) qᵢ / |Z|`. `card_mul_sum_pBInd_rSplit_le`: a label is
  non-first for at most `|J| / |Z|` of the coordinates.

## The randomizer stage

* `rCell M P R`: the first block of `PRF_msg`; distinct over `(R, M)` (`rCell_injective`) and apart
  from the `SK.seed`-keyed cells (`skCell_ne_rCell`). `rOrd`: the rank `BitVec.toNat`.
* `randomizer_eq_rCoord`: on `rGood rCell rOrd Q`, the randomizer `R(M)` of a first message is
  `rCoord (rSplit rCell rOrd θ).1 M`.
* `rGood_frac_le_message`; at Keccak's sizes (`G = 18`, `|J| = 2^256`): `rGood_frac_le_keccak`,
  `2^-207` for the static collisions and `qsᵢ / 2^256 + qᵢ / 2^251` per computation.
-/

open scoped ENNReal

open Quantum.SufCma

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter MasterSeed HashInput truncateHash
  littleEndianBytes)
open Common.SufCma (SchemeHashSpec)
open Quantum.Xmss (X Z out256 trunc128 length_littleEndianBytes)
open Quantum.Xmss.Hybrid (CoinSlots stageN stageN_spec stageNOn stageNOn_spec IsFirst capOf rateOf
  firstCell kCells k'Cells hCells mem_kCells mem_k'Cells mem_hCells card_k'Cells_le card_hCells_le
  sum_ite_comp_mem_le sum_ite_add_mem_eq_card sum_ite_mem_le_card_filter sum_eq_sum_coords
  card_eq_coords sum_sum_le_mul card_mul_sum4_le_snd card_mul_sum4_le_upd card_mul_sum_le_of_update
  card_mul_sum_not_injective_rate_le card_mul_sum_equiv_prod_le card_mul_sum_capOf_cross_le
  card_mul_sum_fst_equiv_le card_mul_sum_equiv_le card_mul_sum_fst_eq natCast_smul_eq_card_mul
  sum_add_sum_eq sum_ite_mem_zero_one_eq sum_fst_eq inv_mul_le_of_parts card_sub_card_le_sum
  natCast_le_mul_div_of_mul_le card_masterSeed)

namespace Quantum.Sphincs.Hybrid

/-! ## The path stages, over abstract kept data -/

section pathStages

/-- **Path-stage coordinates**: the keys `(h, k, k')`, `π`, the data `E` and `F` the stages keep,
and the coin slots of the labels `J`. -/
abbrev PSt (E F J : Type) : Type :=
  (((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × CoinSlots J) × F

/-- The data the `k`- and `k'`-stages keep: `h`, the other key, `π`, `E`, the other two coin
slots, and `F`. -/
abbrev PRestK (E F J : Type) : Type :=
  (Z → X) × (X → Z) × Equiv.Perm (X × Z) × E × (J → Z) × (J → X) × F

/-- The data the `h`-stage keeps: `k`, `k'`, `π`, `E`, the `k`- and `k'`-coins, and `F`. -/
abbrev PRestH (E F J : Type) : Type :=
  (X → Z) × (X → Z) × Equiv.Perm (X × Z) × E × (J → Z) × (J → Z) × F

variable {E F J : Type}

/-- The `k`-stage's view: `k` with the `k`-coins, and the rest. -/
def pShufK : PSt E F J ≃ ((X → Z) × (J → Z)) × PRestK E F J where
  toFun x := ((x.1.1.1.1.2.1, x.1.2.1), (x.1.1.1.1.1, x.1.1.1.1.2.2, x.1.1.1.2, x.1.1.2,
    x.1.2.2.1, x.1.2.2.2, x.2))
  invFun y := (((((y.2.1, y.1.1, y.2.2.1), y.2.2.2.1), y.2.2.2.2.1),
    (y.1.2, y.2.2.2.2.2.1, y.2.2.2.2.2.2.1)), y.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `k'`-stage's view: `k'` with the `k'`-coins, and the rest. -/
def pShufK' : PSt E F J ≃ ((X → Z) × (J → Z)) × PRestK E F J where
  toFun x := ((x.1.1.1.1.2.2, x.1.2.2.1), (x.1.1.1.1.1, x.1.1.1.1.2.1, x.1.1.1.2, x.1.1.2,
    x.1.2.1, x.1.2.2.2, x.2))
  invFun y := (((((y.2.1, y.2.2.1, y.1.1), y.2.2.2.1), y.2.2.2.2.1),
    (y.2.2.2.2.2.1, y.1.2, y.2.2.2.2.2.2.1)), y.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `h`-stage's view: `h` with the `h`-coins, and the rest. -/
def pShufH : PSt E F J ≃ ((Z → X) × (J → X)) × PRestH E F J where
  toFun x := ((x.1.1.1.1.1, x.1.2.2.2), (x.1.1.1.1.2.1, x.1.1.1.1.2.2, x.1.1.1.2, x.1.1.2,
    x.1.2.1, x.1.2.2.1, x.2))
  invFun y := (((((y.1.1, y.2.1, y.2.2.1), y.2.2.2.1), y.2.2.2.2.1),
    (y.2.2.2.2.2.1, y.2.2.2.2.2.2.1, y.1.2)), y.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem pShufK_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (e : E)
    (kc k'c : J → Z) (hc : J → X) (f : F) :
    pShufK (((((h, k, k'), π), e), (kc, k'c, hc)), f) = ((k, kc), (h, k', π, e, k'c, hc, f)) :=
  rfl

theorem pShufK_symm_apply (p : (X → Z) × (J → Z)) (h : Z → X) (k' : X → Z)
    (π : Equiv.Perm (X × Z)) (e : E) (k'c : J → Z) (hc : J → X) (f : F) :
    pShufK.symm (p, (h, k', π, e, k'c, hc, f)) = (((((h, p.1, k'), π), e), (p.2, k'c, hc)), f) :=
  rfl

theorem pShufK'_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (e : E)
    (kc k'c : J → Z) (hc : J → X) (f : F) :
    pShufK' (((((h, k, k'), π), e), (kc, k'c, hc)), f) = ((k', k'c), (h, k, π, e, kc, hc, f)) :=
  rfl

theorem pShufK'_symm_apply (p : (X → Z) × (J → Z)) (h : Z → X) (k : X → Z)
    (π : Equiv.Perm (X × Z)) (e : E) (kc : J → Z) (hc : J → X) (f : F) :
    pShufK'.symm (p, (h, k, π, e, kc, hc, f)) = (((((h, k, p.1), π), e), (kc, p.2, hc)), f) :=
  rfl

theorem pShufH_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (e : E)
    (kc k'c : J → Z) (hc : J → X) (f : F) :
    pShufH (((((h, k, k'), π), e), (kc, k'c, hc)), f) = ((h, hc), (k, k', π, e, kc, k'c, f)) :=
  rfl

theorem pShufH_symm_apply (p : (Z → X) × (J → X)) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (e : E) (kc k'c : J → Z) (f : F) :
    pShufH.symm (p, (k, k', π, e, kc, k'c, f)) = (((((p.1, k, k'), π), e), (kc, k'c, p.2)), f) :=
  rfl

variable (c : E → F → J → X) (ord : J ↪ ℕ)

/-- The `k`-stage's cells: the labels' first blocks. -/
def pPosK (w : PRestK E F J) (a : J) : X :=
  c w.2.2.2.1 w.2.2.2.2.2.2 a

/-- The `k'`-stage's cells: the rates of the labels' first blocks with the `k`-coins. -/
def pPosK' (w : PRestK E F J) (a : J) : X :=
  (w.2.2.1 (c w.2.2.2.1 w.2.2.2.2.2.2 a, w.2.2.2.2.1 a)).1

/-- The `h`-stage's cells: the capacities of the labels' first blocks with the `k`- and
`k'`-coins. -/
def pPosH (w : PRestH E F J) (a : J) : Z :=
  (w.2.2.1 (c w.2.2.2.1 w.2.2.2.2.2.2 a, w.2.2.2.2.1 a)).2 + w.2.2.2.2.2.1 a

/-- The `h`-stage's shifts: the rates of the labels' first blocks with the `k`-coins. -/
def pShH (w : PRestH E F J) (a : J) : X :=
  (w.2.2.1 (c w.2.2.2.1 w.2.2.2.2.2.2 a, w.2.2.2.2.1 a)).1

/-- **The `k`-stage**: `k` at the labels' first blocks takes the `k`-coin slots, which take its
values, when the blocks are distinct. -/
noncomputable def pStageK : PSt E F J ≃ PSt E F J :=
  (pShufK.trans (stageN (pPosK c) fun _ _ ↦ 0)).trans pShufK.symm

/-- **The `k'`-stage**: `k'` at the paths' rates takes the `k'`-coin slots, which take its values,
when the rates are distinct. -/
noncomputable def pStageK' : PSt E F J ≃ PSt E F J :=
  (pShufK'.trans (stageN (pPosK' c) fun _ _ ↦ 0)).trans pShufK'.symm

/-- **The partial `h`-stage**: `h` at the capacity of each first label takes the label's `h`-slot,
which takes the block's output (rate plus `h`); the other slots stay. -/
noncomputable def pStageHOn : PSt E F J ≃ PSt E F J :=
  (pShufH.trans (stageNOn ord (pPosH c) (pShH c))).trans pShufH.symm

theorem pStageK_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (e : E)
    (kc k'c : J → Z) (hc : J → X) (f : F) :
    ∃ (k₂ : X → Z) (kc₂ : J → Z),
      pStageK c (((((h, k, k'), π), e), (kc, k'c, hc)), f) =
        (((((h, k₂, k'), π), e), (kc₂, k'c, hc)), f) ∧
      (Function.Injective (c e f) →
        (∀ a, kc₂ a = k (c e f a)) ∧ ∀ x, (∀ a, c e f a ≠ x) → k₂ x = k x) := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec (pPosK c) (fun _ _ ↦ (0 : Z)) (k, kc)
    (h, k', π, e, k'c, hc, f)
  refine ⟨p'.1, p'.2, ?_, fun hinj ↦ ?_⟩
  · rw [pStageK, Equiv.trans_apply, Equiv.trans_apply, pShufK_apply, hp', pShufK_symm_apply]
  · obtain ⟨h1, h2⟩ := hsp hinj
    exact ⟨fun a ↦ (h1 a).trans (zero_add _), h2⟩

theorem pStageK'_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (e : E)
    (kc k'c : J → Z) (hc : J → X) (f : F) :
    ∃ (k'₂ : X → Z) (k'c₂ : J → Z),
      pStageK' c (((((h, k, k'), π), e), (kc, k'c, hc)), f) =
        (((((h, k, k'₂), π), e), (kc, k'c₂, hc)), f) ∧
      (Function.Injective (fun a ↦ (π (c e f a, kc a)).1) →
        (∀ a, k'c₂ a = k' (π (c e f a, kc a)).1) ∧
          ∀ x, (∀ a, (π (c e f a, kc a)).1 ≠ x) → k'₂ x = k' x) := by
  obtain ⟨p', hp', hsp⟩ := stageN_spec (pPosK' c) (fun _ _ ↦ (0 : Z)) (k', k'c)
    (h, k, π, e, kc, hc, f)
  refine ⟨p'.1, p'.2, ?_, fun hinj ↦ ?_⟩
  · rw [pStageK', Equiv.trans_apply, Equiv.trans_apply, pShufK'_apply, hp', pShufK'_symm_apply]
  · obtain ⟨h1, h2⟩ := hsp hinj
    exact ⟨fun a ↦ (h1 a).trans (zero_add _), h2⟩

theorem pStageHOn_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (e : E)
    (kc k'c : J → Z) (hc : J → X) (f : F) :
    ∃ (h₂ : Z → X) (hc₂ : J → X),
      pStageHOn c ord (((((h, k, k'), π), e), (kc, k'c, hc)), f) =
        (((((h₂, k, k'), π), e), (kc, k'c, hc₂)), f) ∧
      (∀ a, IsFirst ord (fun b ↦ (π (c e f b, kc b)).2 + k'c b) a →
        hc₂ a = (π (c e f a, kc a)).1 + h ((π (c e f a, kc a)).2 + k'c a) ∧
        h₂ ((π (c e f a, kc a)).2 + k'c a) = hc a) ∧
      (∀ a, ¬IsFirst ord (fun b ↦ (π (c e f b, kc b)).2 + k'c b) a → hc₂ a = hc a) ∧
      ∀ z, (∀ a, (π (c e f a, kc a)).2 + k'c a ≠ z) → h₂ z = h z := by
  obtain ⟨p', hp', f1, f2, f3⟩ := stageNOn_spec ord (pPosH c) (pShH c) (h, hc)
    (k, k', π, e, kc, k'c, f)
  refine ⟨p'.1, p'.2, ?_, f1, f2, f3⟩
  rw [pStageHOn, Equiv.trans_apply, Equiv.trans_apply, pShufH_apply, hp', pShufH_symm_apply]

/-- **The path stages**: `k` and `k'` at every label, `h` at the first labels. -/
noncomputable def pStages : PSt E F J ≃ PSt E F J :=
  (pStageK c).trans ((pStageK' c).trans (pStageHOn c ord))

/-- **The path stages**: they keep `π`, `E` and `F`. When the labels' cells and their rates are
distinct, the `k`- and `k'`-slots take `k`, `k'` at the paths' cells; the `h`-slot of a first label
(by capacity) takes the block's output, that of another label stays; and the keys keep their values
off the paths' cells. -/
theorem pStages_spec (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (e : E) (cs : CoinSlots J)
    (f : F) :
    ∃ (h₂ : Z → X) (k₂ k'₂ : X → Z) (cs₂ : CoinSlots J),
      pStages c ord (((((t, π), e), cs), f)) = (((((h₂, k₂, k'₂), π), e), cs₂), f) ∧
      (∀ z, (∀ a, (π (c e f a, cs₂.1 a)).2 + cs₂.2.1 a ≠ z) → h₂ z = t.1 z) ∧
      (Function.Injective (c e f) →
        Function.Injective (fun a ↦ rateOf t.2.1 π (c e f a)) →
        (∀ a, cs₂.1 a = t.2.1 (c e f a)) ∧
        (∀ a, cs₂.2.1 a = t.2.2 (rateOf t.2.1 π (c e f a))) ∧
        (∀ a, IsFirst ord (fun b ↦ capOf t.2.1 t.2.2 π (c e f b)) a →
          cs₂.2.2 a = rateOf t.2.1 π (c e f a) + t.1 (capOf t.2.1 t.2.2 π (c e f a))) ∧
        (∀ a, ¬IsFirst ord (fun b ↦ capOf t.2.1 t.2.2 π (c e f b)) a → cs₂.2.2 a = cs.2.2 a) ∧
        (∀ x, (∀ a, c e f a ≠ x) → k₂ x = t.2.1 x) ∧
        ∀ x, (∀ a, (π (c e f a, cs₂.1 a)).1 ≠ x) → k'₂ x = t.2.2 x) := by
  obtain ⟨h, k, k'⟩ := t
  obtain ⟨kc, k'c, hc⟩ := cs
  obtain ⟨k₂, kc₂, eK, fK⟩ := pStageK_spec c h k k' π e kc k'c hc f
  obtain ⟨k'₂, k'c₂, eK', fK'⟩ := pStageK'_spec c h k₂ k' π e kc₂ k'c hc f
  obtain ⟨h₂, hc₂, eH, fH1, fH2, fH3⟩ := pStageHOn_spec c ord h k₂ k'₂ π e kc₂ k'c₂ hc f
  refine ⟨h₂, k₂, k'₂, (kc₂, k'c₂, hc₂), ?_, fH3, fun hx hr ↦ ?_⟩
  · rw [pStages, Equiv.trans_apply, Equiv.trans_apply, eK, eK', eH]
  · obtain ⟨fK1, fK2⟩ := fK hx
    have hpr : ∀ a, (π (c e f a, kc₂ a)).1 = rateOf k π (c e f a) := fun a ↦ by
      rw [fK1 a, rateOf]
    obtain ⟨fK'1, fK'2⟩ := fK' fun a b hab ↦ hr ((hpr a).symm.trans (hab.trans (hpr b)))
    have hpc : ∀ a, (π (c e f a, kc₂ a)).2 + k'c₂ a = capOf k k' π (c e f a) := fun a ↦ by
      rw [fK'1 a, fK1 a, capOf]
    have hfun : (fun b ↦ (π (c e f b, kc₂ b)).2 + k'c₂ b) = fun b ↦ capOf k k' π (c e f b) :=
      funext hpc
    rw [hfun] at fH1 fH2
    exact ⟨fK1, fun a ↦ (fK'1 a).trans (congrArg k' (hpr a)), fun a ha ↦ (fH1 a ha).1.trans
      (congrArg₂ (· + ·) (hpr a) (congrArg h (hpc a))), fH2, fK2, fK'2⟩

/-! ### Cells read off the coordinates -/

/-- The paths' `k`-cells read off the coordinates. -/
def pCellK (y : PSt E F J) (a : J) : X :=
  c y.1.1.2 y.2 a

/-- The paths' `k'`-cells read off the coordinates (with the `k`-coins). -/
def pCellK' (y : PSt E F J) (a : J) : X :=
  (y.1.1.1.2 (pCellK c y a, y.1.2.1 a)).1

/-- The paths' `h`-cells read off the coordinates (with the `k`- and `k'`-coins). -/
def pCellH (y : PSt E F J) (a : J) : Z :=
  (y.1.1.1.2 (pCellK c y a, y.1.2.1 a)).2 + y.1.2.2.1 a

/-- The capacities read off the coordinates are the `h`-stage's cells, for the data it keeps. -/
theorem pCellH_eq_pPosH (y : PSt E F J) : pCellH c y = pPosH c (pShufH y).2 :=
  rfl

/-- The non-first labels read off the coordinates: a label of smaller rank has the same capacity. -/
def pB (y : PSt E F J) : Set J :=
  {a | ∃ b, ord b < ord a ∧ pCellH c y b = pCellH c y a}

theorem mem_pB {y : PSt E F J} {a : J} : a ∈ pB c ord y ↔ ¬IsFirst ord (pCellH c y) a := by
  simp only [pB, Set.mem_ofPred_eq, IsFirst, not_forall, not_not, exists_prop]

variable {ι : Type}

/-- No computation `rd i` of the public part `((t, π), e)` reads a path cell read off the
coordinates. -/
def PReadGood (rd : ι → (SpongeKeys X Z × Equiv.Perm (X × Z)) × E → List (SpongeRead X Z))
    (y : PSt E F J) : Prop :=
  ∀ i a, pCellK c y a ∉ kCells (rd i y.1.1) ∧ pCellK' c y a ∉ k'Cells (rd i y.1.1) ∧
    pCellH c y a ∉ hCells (rd i y.1.1)

/-! ### Counts over the coordinates -/

section counts

variable (G : ℕ) (rd : ι → (SpongeKeys X Z × Equiv.Perm (X × Z)) × E → List (SpongeRead X Z))

/-- The computation `rd i` reads `k` at the path `a`'s first block. -/
noncomputable def pKHit (i : ι) (a : J) (y : PSt E F J) : ℕ :=
  if pCellK c y a ∈ kCells (rd i y.1.1) then 1 else 0

open scoped Classical in
/-- A good permutation and the computation `rd i` reading `k'` at the path `a`'s rate. -/
noncomputable def pK'Hit (i : ι) (a : J) (y : PSt E F J) : ℕ :=
  if PermGood y.1.1.1.2 G ∧ pCellK' c y a ∈ k'Cells (rd i y.1.1) then 1 else 0

/-- The computation `rd i` reads `h` at the path `a`'s capacity. -/
noncomputable def pHHit (i : ι) (a : J) (y : PSt E F J) : ℕ :=
  if pCellH c y a ∈ hCells (rd i y.1.1) then 1 else 0

/-- The paths' first blocks read by `rd i`. -/
noncomputable def pReadK [Fintype J] (i : ι) (y : PSt E F J) : ℕ :=
  ∑ a, pKHit c rd i a y

/-- The paths' rates and capacities read by `rd i`. -/
noncomputable def pReadKH [Fintype J] (i : ι) (y : PSt E F J) : ℕ :=
  ∑ a, (pK'Hit c G rd i a y + pHHit c rd i a y)

/-- The coordinates with the coin slots split off: the public part, the `h`-coins, `F`, the
`k`-coins and the `k'`-coins. -/
def pCoordC :
    (((((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) × F) × (J → Z)) × (J → Z) ≃
      PSt E F J where
  toFun c := ((c.1.1.1.1, (c.1.2, c.2, c.1.1.1.2)), c.1.1.2)
  invFun y := ((((y.1.1, y.1.2.2.2), y.2), y.1.2.1), y.1.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A count over four coordinates, the last resampled at one point. -/
theorem card_mul_sum4_le_upd_one {Ω S K B : Type*} [Fintype Ω] [Fintype S] [Fintype K]
    [Fintype B] [Fintype J] [DecidableEq J] (v : Ω → S → K → (J → B) → ℕ) (a : J) (d : ℕ)
    (hv : ∀ ω s k k', ∑ w, v ω s k (Function.update k' a w) ≤ d) :
    Fintype.card B * ∑ ω, ∑ s, ∑ k, ∑ k', v ω s k k' ≤
      Fintype.card Ω * Fintype.card S * (Fintype.card K * Fintype.card (J → B)) * d := by
  calc Fintype.card B * ∑ ω, ∑ s, ∑ k, ∑ k', v ω s k k'
      = ∑ ω, ∑ s, ∑ k, Fintype.card B * ∑ k', v ω s k k' := by simp only [Finset.mul_sum]
    _ ≤ ∑ _ω : Ω, ∑ _s : S, ∑ _k : K, Fintype.card (J → B) * d :=
        Finset.sum_le_sum fun ω _ ↦ Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun k _ ↦
          card_mul_sum_le_of_update (fun k' ↦ v ω s k k') a d fun k' ↦ hv ω s k k'
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

open scoped Classical in
/-- The label `a` is non-first at the coordinates `y`. -/
noncomputable def pBInd (a : J) (y : PSt E F J) : ℕ :=
  if a ∈ pB c ord y then 1 else 0

/-- The non-first indicator of `a` with its `k'`-coin at `w` is at most that of its capacity
hitting the other labels' capacities. -/
theorem pBInd_update_le [Fintype J] [DecidableEq J]
    (ω : ((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) (f : F) (kc k'c : J → Z) (a : J)
    (w : Z) :
    pBInd c ord a (pCoordC (((ω, f), kc), Function.update k'c a w)) ≤
      if (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + w ∈ (Finset.univ.filter fun b ↦ b ≠ a).image
        (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b) then 1 else 0 := by
  by_cases ha : a ∈ pB c ord (pCoordC (((ω, f), kc), Function.update k'c a w))
  · obtain ⟨b, hb, he⟩ := id ha
    have hba : b ≠ a := fun h ↦ (lt_irrefl _) (h ▸ hb)
    have hmem : (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + w ∈ (Finset.univ.filter fun b ↦ b ≠ a).image
        (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b) := by
      refine Finset.mem_image.mpr ⟨b, by simp [hba], ?_⟩
      have he' : (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + Function.update k'c a w b =
          (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + Function.update k'c a w a := he
      rwa [Function.update_of_ne hba, Function.update_self] at he'
    rw [pBInd, ite_eq_left ha, ite_eq_left hmem]
  · rw [pBInd, ite_eq_right ha]
    exact Nat.zero_le _

/-! The coordinates are finite (named: the products with the keys and `π` are not found
otherwise). -/

noncomputable instance instFintypeKeysPerm : Fintype (SpongeKeys X Z × Equiv.Perm (X × Z)) :=
  instFintypeProd _ _

noncomputable instance instFintypeKeysPermE [Fintype E] :
    Fintype ((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) :=
  instFintypeProd _ _

noncomputable instance instFintypeCoinSlots [Fintype J] [DecidableEq J] :
    Fintype (CoinSlots J) :=
  instFintypeProd _ _

noncomputable instance instFintypePStPub [Fintype E] [Fintype J] [DecidableEq J] :
    Fintype (((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × CoinSlots J) :=
  instFintypeProd _ _

noncomputable instance instFintypePSt [Fintype E] [Fintype F] [Fintype J] [DecidableEq J] :
    Fintype (PSt E F J) :=
  instFintypeProd _ _

noncomputable instance instFintypePCoord₁ [Fintype E] [Fintype J] [DecidableEq J] :
    Fintype (((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) :=
  instFintypeProd _ _

noncomputable instance instFintypePCoord₂ [Fintype E] [Fintype F] [Fintype J] [DecidableEq J] :
    Fintype ((((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) × F) :=
  instFintypeProd _ _

noncomputable instance instFintypePCoord₃ [Fintype E] [Fintype F] [Fintype J] [DecidableEq J] :
    Fintype (((((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) × F) × (J → Z)) :=
  instFintypeProd _ _

noncomputable instance instFintypePCoord₄ [Fintype E] [Fintype F] [Fintype J] [DecidableEq J] :
    Fintype ((((((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) × F) × (J → Z)) ×
      (J → Z)) :=
  instFintypeProd _ _

variable [Fintype E] [Fintype F] [Fintype J] [DecidableEq J]

/-- **The paths' first blocks are rarely read**: when the reads of `rd i` at the first blocks,
summed over `F`, are at most `B i`, they weigh at most `B i / |F|` of the coordinates. -/
theorem card_mul_sum_pReadK_le (B : ι → ℕ)
    (hB : ∀ i p, ∑ f, ∑ a, (if c p.2 f a ∈ kCells (rd i p) then 1 else 0) ≤ B i) (i : ι) :
    Fintype.card F * ∑ y, pReadK c rd i y ≤ Fintype.card (PSt E F J) * B i := by
  rw [sum_eq_sum_coords pCoordC (pReadK c rd i), card_eq_coords pCoordC]
  refine card_mul_sum4_le_snd _ (B i) fun ω _ _ ↦ ?_
  change ∑ f, ∑ a, (if c ω.1.2 f a ∈ kCells (rd i ω.1) then 1 else 0) ≤ B i
  exact hB i ω.1

/-- **The paths' rates and capacities are rarely read**: at most `|J| (G + 1) q / |Z|` of the
coordinates, the `k'`-coins resampled for the capacities and the `k`-coins for the rates. -/
theorem card_mul_sum_pReadKH_le (q : ι → ℕ) (hq : ∀ i p, (rd i p).length ≤ q i) (i : ι) :
    Fintype.card Z * ∑ y, pReadKH c G rd i y ≤
      Fintype.card (PSt E F J) * (Fintype.card J * (G + 1) * q i) := by
  rw [sum_eq_sum_coords pCoordC (pReadKH c G rd i), card_eq_coords pCoordC]
  have h := card_mul_sum4_le_upd
    (Ω := ((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) (S := F) (B := Z)
    (fun ω f kc k'c a ↦ pK'Hit c G rd i a (pCoordC (((ω, f), kc), k'c)))
    (fun ω f kc k'c a ↦ pHHit c rd i a (pCoordC (((ω, f), kc), k'c))) (q i * G) (q i)
    (fun ω f _ a kc ↦ by
      change ∑ w, (if PermGood ω.1.1.2 G ∧ (ω.1.1.2 (c ω.1.2 f a,
        Function.update kc a w a)).1 ∈ k'Cells (rd i ω.1) then 1 else 0) ≤ q i * G
      simp only [Function.update_self]
      by_cases hG : PermGood ω.1.1.2 G
      · simp only [hG, true_and]
        exact (sum_ite_comp_mem_le (fun w ↦ (ω.1.1.2 (c ω.1.2 f a, w)).1) _ G
          fun x₂ ↦ hG.rate _ x₂).trans
            (Nat.mul_le_mul_right _ ((card_k'Cells_le _).trans (hq i _)))
      · simp only [hG, false_and, ↓reduceIte, Finset.sum_const_zero]
        exact Nat.zero_le _)
    (fun ω f kc a k'c ↦ by
      change ∑ w, (if (ω.1.1.2 (c ω.1.2 f a, kc a)).2 +
        Function.update k'c a w a ∈ hCells (rd i ω.1) then 1 else 0) ≤ q i
      simp only [Function.update_self]
      rw [sum_ite_add_mem_eq_card]
      exact (card_hCells_le _).trans (hq i _))
  rw [show Fintype.card J * (q i * G + q i) = Fintype.card J * (G + 1) * q i by ring] at h
  exact h

/-- **A label is rarely non-first**: `a` is non-first (a label of smaller rank has its capacity)
for at most `|J| / |Z|` of the coordinates, its `k'`-coin resampled. -/
theorem card_mul_sum_pBInd_le (a : J) :
    Fintype.card Z * ∑ y, pBInd c ord a y ≤ Fintype.card (PSt E F J) * Fintype.card J := by
  rw [sum_eq_sum_coords pCoordC (pBInd c ord a), card_eq_coords pCoordC]
  refine card_mul_sum4_le_upd_one (fun ω f kc k'c ↦ pBInd c ord a (pCoordC (((ω, f), kc), k'c)))
    a _ fun ω f kc k'c ↦ ?_
  calc ∑ w, pBInd c ord a (pCoordC (((ω, f), kc), Function.update k'c a w))
      ≤ ∑ w : Z, (if (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + w ∈
          (Finset.univ.filter fun b ↦ b ≠ a).image
            (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b) then 1 else 0) :=
        Finset.sum_le_sum fun w _ ↦ pBInd_update_le c ord ω f kc k'c a w
    _ = ((Finset.univ.filter fun b ↦ b ≠ a).image
          (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b)).card :=
        sum_ite_add_mem_eq_card _ _
    _ ≤ Fintype.card J :=
        Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans_eq Finset.card_univ)

end counts

end pathStages

/-! ## The randomizer's first blocks -/

section cells

/-- The `SK.prf`-keyed first block of `PRF_msg` at the message `M` under the public seed `P`. -/
def rCell (M : Message) (P : PublicParameter) (R : HashOutput) : X :=
  firstCell (prfMessageInput R P M)

theorem length_prfMessageInput_lt (R : HashOutput) (P : PublicParameter) (M : Message) :
    (prfMessageInput R P M).length < 136 := by
  have h := length_prfMessageInput R P M
  omega

/-- **The randomizer cells are distinct**: a first block names its key `SK.prf` and its message. -/
theorem rCell_injective (P : PublicParameter) :
    Function.Injective fun q : HashOutput × Message ↦ rCell q.2 P q.1 := by
  rintro ⟨R, M⟩ ⟨R', M'⟩ h
  have h' := eq_of_firstCell_eq (length_prfMessageInput_lt R P M)
    (length_prfMessageInput_lt R' P M') h
  unfold prfMessageInput framedMessage at h'
  obtain ⟨h1, h2⟩ := List.append_inj h'
    (by simp only [List.length_append, length_littleEndianBytes])
  obtain ⟨hR, -⟩ := List.append_inj h1 (by simp only [length_littleEndianBytes])
  obtain ⟨-, hM⟩ := List.append_inj h2 rfl
  rw [littleEndianBytes_injective 32 hR, littleEndianBytes_injective 32 hM]

theorem rCell_injective_msg (P : PublicParameter) (R : HashOutput) :
    Function.Injective fun M ↦ rCell M P R := fun M M' h ↦
  congrArg Prod.snd (rCell_injective P (a₁ := (R, M)) (a₂ := (R, M')) h)

/-- **The randomizer cells are not `SK.seed`-keyed cells**: one-block inputs of other lengths. -/
theorem skCell_ne_rCell (P : PublicParameter) (S : MasterSeed) (b : SkIdx) (M : Message)
    (R : HashOutput) : skCell P S b ≠ rCell M P R := by
  intro h
  have hl := congrArg List.length (eq_of_firstCell_eq (length_skInput_lt P S b)
    (length_prfMessageInput_lt R P M) h)
  have h93 := length_prfMessageInput R P M
  rcases b with _ | _ | d <;>
    simp only [skInput, length_keyDerivationInput, length_prfInput] at hl <;> omega

/-- The rank of the messages. -/
def rOrd : Message ↪ ℕ :=
  ⟨BitVec.toNat, fun _ _ h ↦ BitVec.eq_of_toNat_eq h⟩

end cells

/-! ## The label stages on leanSPHINCS tables, over the labels -/

section rstage

variable {J : Type}

/-- The public slots of `Pub`: the bits of slot `0` beyond `SK.prf`, slot `1` and the secrets'. -/
abbrev PubSlots : Type := (Fin 832 → ZMod 2) × X × (KeygenDomain → X)

/-- The tables with the extra slots and the coin slots of the labels `J`. -/
abbrev RTab (J : Type) : Type := Tab × CoinSlots J

/-- The public part with the coin slots of the labels `J`. -/
abbrev RPub (J : Type) : Type := Pub × CoinSlots J

/-- The tables with the coin slots are finite (named: the product is not found otherwise). -/
noncomputable instance instFintypeRTab [Fintype J] [DecidableEq J] : Fintype (RTab J) :=
  instFintypeProd _ _

/-- The public part and the hidden part reordered with the coin slots. -/
def reorderR : (Pub × Secret) × CoinSlots J ≃ RPub J × Secret where
  toFun x := ((x.1.1, x.2), x.1.2)
  invFun y := ((y.1.1, y.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable (cell : J → PublicParameter → HashOutput → X) (ord : J ↪ ℕ)

/-- A `k`-cell is some label's first block under `P` (a named predicate: its decidability is the
classical one at every label type, so the read bounds stated with it match across instances). -/
def IsCell (P : PublicParameter) (x : X) : Prop :=
  ∃ a R, cell a P R = x

/-- The labels' first blocks in the path-stage form: `PK.seed` from slot `1`, `SK.prf` from the
hidden part. -/
def cellP (e : PubSlots) (s : Secret) (a : J) : X :=
  cell a (trunc128 e.2.1) s.2

/-- **The staged swap with the label stages**: the table with the extra slots and the coin slots
as the public part with the coin slots, and the hidden `(SK.seed, SK.prf)`. -/
noncomputable def rSplit : RTab J ≃ RPub J × Secret :=
  ((schemeSplit.prodCongr (Equiv.refl (CoinSlots J))).trans reorderR).trans
    (pStages (cellP cell) ord)

theorem rSplit_apply (θ : RTab J) :
    rSplit cell ord θ = pStages (cellP cell) ord (((((schemeSplit θ.1).1.1.1,
      (schemeSplit θ.1).1.1.2), (schemeSplit θ.1).1.2), θ.2), (schemeSplit θ.1).2) :=
  rfl

theorem rSplit_exists (θ : RTab J) : ∃ (h₂ : Z → X) (k₂ k'₂ : X → Z) (cs₂ : CoinSlots J),
    rSplit cell ord θ = (((((h₂, k₂, k'₂), (schemeSplit θ.1).1.1.2), (schemeSplit θ.1).1.2),
      cs₂), (schemeSplit θ.1).2) := by
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, -⟩ := pStages_spec (cellP cell) ord (schemeSplit θ.1).1.1.1
    (schemeSplit θ.1).1.1.2 (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  exact ⟨h₂, k₂, k'₂, cs₂, (rSplit_apply cell ord θ).trans hE⟩

/-- **The hidden coordinate is `(SK.seed, SK.prf)`.** -/
theorem rSplit_snd (θ : RTab J) :
    (rSplit cell ord θ).2 = (θ.1.1.secretSeed, θ.1.1.prfKey) := by
  obtain ⟨_, _, _, _, hE⟩ := rSplit_exists cell ord θ
  rw [hE]
  exact schemeSplit_snd θ.1

theorem rSplit_perm (θ : RTab J) : (rSplit cell ord θ).1.1.1.2 = θ.1.1.perm := by
  obtain ⟨_, _, _, _, hE⟩ := rSplit_exists cell ord θ
  rw [hE]
  exact schemeSplit_perm θ.1

/-- The label stages keep the public slots. -/
theorem rSplit_slots (θ : RTab J) : (rSplit cell ord θ).1.1.2 = (schemeSplit θ.1).1.2 := by
  obtain ⟨_, _, _, _, hE⟩ := rSplit_exists cell ord θ
  rw [hE]

/-- The coordinate of a label: the first `128` bits of its `h`-slot (`r0SlotEquiv`); the other
`960` bits are a pad. -/
def rCoord (y : RPub J) (a : J) : Digest :=
  trunc128 (y.2.2.2 a)

/-- The labels' `k`-cells of a table: their first blocks. -/
def rCellK (L : HonestTable) (a : J) : X :=
  cell a L.publicSeed L.prfKey

/-- The labels' `k'`-cells of a table: the rates of their first blocks. -/
def rCellK' (L : HonestTable) (a : J) : X :=
  rateOf L.keys.2.1 L.perm (rCellK cell L a)

/-- The labels' `h`-cells of a table: the capacities of their first blocks. -/
def rCellH (L : HonestTable) (a : J) : Z :=
  capOf L.keys.2.1 L.keys.2.2 L.perm (rCellK cell L a)

/-- **The non-first labels of a table**: a label of smaller rank has the same capacity. -/
def rB (L : HonestTable) : Set J :=
  {a | ∃ b, ord b < ord a ∧ rCellH cell L b = rCellH cell L a}

theorem mem_rB {L : HonestTable} {a : J} :
    a ∈ rB cell ord L ↔ ¬IsFirst ord (rCellH cell L) a := by
  simp only [rB, Set.mem_ofPred_eq, IsFirst, not_forall, not_not, exists_prop]

/-- The labels' rates of the staged swap's coordinates are distinct. -/
abbrev RateInj (x : Pub × Secret) : Prop :=
  Function.Injective fun a ↦ rateOf x.1.1.1.2.1 x.1.1.2 (cell a (pubParam x.1) x.2.2)

/-- The labels' capacities avoid the hidden capacities of `schemeSplit`. -/
abbrev CapSep (x : Pub × Secret) : Prop :=
  ∀ a b, capOf x.1.1.1.2.1 x.1.1.1.2.2 x.1.1.2 (cell a (pubParam x.1) x.2.2) ≠ posOf x.1 x.2 b

/-- **No static collisions of the labels' paths**: their rates are distinct and their capacities
avoid the hidden capacities. Their capacities may collide with each other. -/
def RColl (x : Pub × Secret) : Prop :=
  RateInj cell x ∧ CapSep cell x

theorem cell_injective_of {cell : J → PublicParameter → HashOutput → X}
    (hcell : ∀ P, Function.Injective fun s : HashOutput × J ↦ cell s.2 P s.1) (P : PublicParameter)
    (R : HashOutput) : Function.Injective fun a ↦ cell a P R :=
  fun a a' h ↦ congrArg Prod.snd (hcell P (a₁ := (R, a)) (a₂ := (R, a')) h)

/-- After `schemeSplit`, the labels' cells in the path-stage form are the table's. -/
theorem cellP_schemeSplit (t : Tab)
    (hinj : Function.Injective (posOf (schemeSplit t).1 (schemeSplit t).2)) :
    cellP cell (schemeSplit t).1.2 (schemeSplit t).2 = rCellK cell t.1 := by
  have hP := (schemeSplit_transfer t hinj).1
  funext a
  change cell a (pubParam (schemeSplit t).1) (schemeSplit t).2.2 = _
  rw [hP, schemeSplit_snd]
  rfl

/-- **The transfer facts**: when the hidden capacities are distinct, the labels' cells are
distinct and `RColl` holds, the public part gives `PK.seed`, the `k`- and `k'`-slots hold the
table's `k` and `k'` at the paths' cells, the `h`-slot of a first label holds the block's output,
and that of a non-first label the table's pad. -/
theorem rSplit_transfer (θ : RTab J)
    (hinj : Function.Injective (posOf (schemeSplit θ.1).1 (schemeSplit θ.1).2))
    (hcell : ∀ P, Function.Injective fun s : HashOutput × J ↦ cell s.2 P s.1)
    (hcoll : RColl cell (schemeSplit θ.1)) :
    pubParam (rSplit cell ord θ).1.1 = θ.1.1.publicSeed ∧
      (∀ a, (rSplit cell ord θ).1.2.1 a = θ.1.1.keys.2.1 (rCellK cell θ.1.1 a)) ∧
      (∀ a, (rSplit cell ord θ).1.2.2.1 a = θ.1.1.keys.2.2 (rCellK' cell θ.1.1 a)) ∧
      (∀ a, a ∉ rB cell ord θ.1.1 → (rSplit cell ord θ).1.2.2.2 a =
        rateOf θ.1.1.keys.2.1 θ.1.1.perm (rCellK cell θ.1.1 a) +
          θ.1.1.keys.1 (rCellH cell θ.1.1 a)) ∧
      ∀ a, a ∈ rB cell ord θ.1.1 → (rSplit cell ord θ).1.2.2.2 a = θ.2.2.2 a := by
  obtain ⟨hP, -, hh⟩ := schemeSplit_transfer θ.1 hinj
  have hc := cellP_schemeSplit cell θ.1 hinj
  have hk := schemeSplit_keys_snd θ.1
  have hπ := schemeSplit_perm θ.1
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, -, f⟩ := pStages_spec (cellP cell) ord (schemeSplit θ.1).1.1.1
    (schemeSplit θ.1).1.1.2 (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  rw [hc, hk, hπ] at f
  have hrK : Function.Injective fun a ↦
      rateOf θ.1.1.keys.2.1 θ.1.1.perm (rCellK cell θ.1.1 a) := by
    have h1 := hcoll.1
    change Function.Injective fun a ↦ rateOf (schemeSplit θ.1).1.1.1.2.1 (schemeSplit θ.1).1.1.2
      (cellP cell (schemeSplit θ.1).1.2 (schemeSplit θ.1).2 a) at h1
    rwa [hc, hk, hπ] at h1
  obtain ⟨f1, f2, f3, f4, -, -⟩ := f (cell_injective_of hcell _ _) hrK
  have hsep : ∀ a b, capOf θ.1.1.keys.2.1 θ.1.1.keys.2.2 θ.1.1.perm (rCellK cell θ.1.1 a) ≠
      posOf (schemeSplit θ.1).1 (schemeSplit θ.1).2 b := by
    intro a b
    have h2 := hcoll.2 a b
    change capOf (schemeSplit θ.1).1.1.1.2.1 (schemeSplit θ.1).1.1.1.2.2 (schemeSplit θ.1).1.1.2
      (cellP cell (schemeSplit θ.1).1.2 (schemeSplit θ.1).2 a) ≠ _ at h2
    rwa [hc, hk, hπ] at h2
  have hPr : pubParam (rSplit cell ord θ).1.1 = θ.1.1.publicSeed := by
    rw [← hP]
    exact congrArg (fun s : PubSlots ↦ trunc128 s.2.1) (rSplit_slots cell ord θ)
  rw [rSplit_apply, hE] at hPr ⊢
  refine ⟨hPr, f1, f2, fun a ha ↦ (f3 a (not_not.mp fun h ↦ ha ((mem_rB cell ord).mpr h))).trans
    ?_, fun a ha ↦ f4 a ((mem_rB cell ord).mp ha)⟩
  rw [hh _ fun b hb ↦ hsep a b hb.symm]
  rfl

/-- The keys of the public part agree with those after `schemeSplit` off the labels' cells read
off the coordinates. -/
theorem rSplit_keys_eq (θ : RTab J)
    (hcell : ∀ P, Function.Injective fun s : HashOutput × J ↦ cell s.2 P s.1)
    (hrate : RateInj cell (schemeSplit θ.1)) :
    (∀ x, (∀ a, pCellK (cellP cell) (rSplit cell ord θ) a ≠ x) →
        (rSplit cell ord θ).1.1.1.1.2.1 x = (schemeSplit θ.1).1.1.1.2.1 x) ∧
      (∀ x, (∀ a, pCellK' (cellP cell) (rSplit cell ord θ) a ≠ x) →
        (rSplit cell ord θ).1.1.1.1.2.2 x = (schemeSplit θ.1).1.1.1.2.2 x) ∧
      ∀ z, (∀ a, pCellH (cellP cell) (rSplit cell ord θ) a ≠ z) →
        (rSplit cell ord θ).1.1.1.1.1 z = (schemeSplit θ.1).1.1.1.1 z := by
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, f6, f⟩ := pStages_spec (cellP cell) ord (schemeSplit θ.1).1.1.1
    (schemeSplit θ.1).1.1.2 (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  obtain ⟨-, -, -, -, f4, f5⟩ := f (cell_injective_of hcell _ _) hrate
  rw [rSplit_apply, hE]
  exact ⟨f4, f5, f6⟩

/-! ### The good set and the coordinate facts -/

variable {ι : Type} {β : ι → Type}

/-- The computations' reads from the public part. -/
def qReads
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (i : ι) (p : Pub) : List (SpongeRead X Z) :=
  (pubData Q p i).2

variable [Fintype J] [DecidableEq J]

open scoped Classical in
/-- **The good set** of the label stages: `schemeGood`, no static collision of the labels' paths
(`RColl`), and no computation reading a label's cell (`PReadGood`). Irreducible: its membership
does not unfold to the enumeration of all tables. -/
@[irreducible]
noncomputable def rGood
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Finset (RTab J) :=
  Finset.univ.filter fun θ ↦
    GoodPS Q (schemeSplit θ.1) ∧ RColl cell (schemeSplit θ.1) ∧
      PReadGood (cellP cell) (qReads Q) (rSplit cell ord θ)

variable {cell ord}

theorem mem_rGood
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {θ : RTab J} :
    θ ∈ rGood cell ord Q ↔ GoodPS Q (schemeSplit θ.1) ∧ RColl cell (schemeSplit θ.1) ∧
      PReadGood (cellP cell) (qReads Q) (rSplit cell ord θ) := by
  unfold rGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

section coords

variable {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
  (hcell : ∀ P, Function.Injective fun s : HashOutput × J ↦ cell s.2 P s.1)
  {θ : RTab J} (hθ : θ ∈ rGood cell ord Q)

include hcell hθ

/-- **The coordinate facts**: on the good set, the public part gives `PK.seed`, the `k`- and
`k'`-slots hold the table's `k` and `k'` at the paths' cells, the `h`-slot of a first label holds
the block's output, and that of a non-first label the table's pad. -/
theorem rSplit_coords :
    pubParam (rSplit cell ord θ).1.1 = θ.1.1.publicSeed ∧
      (∀ a, (rSplit cell ord θ).1.2.1 a = θ.1.1.keys.2.1 (rCellK cell θ.1.1 a)) ∧
      (∀ a, (rSplit cell ord θ).1.2.2.1 a = θ.1.1.keys.2.2 (rCellK' cell θ.1.1 a)) ∧
      (∀ a, a ∉ rB cell ord θ.1.1 → (rSplit cell ord θ).1.2.2.2 a =
        rateOf θ.1.1.keys.2.1 θ.1.1.perm (rCellK cell θ.1.1 a) +
          θ.1.1.keys.1 (rCellH cell θ.1.1 a)) ∧
      ∀ a, a ∈ rB cell ord θ.1.1 → (rSplit cell ord θ).1.2.2.2 a = θ.2.2.2 a := by
  obtain ⟨⟨hinj, -⟩, hcoll, -⟩ := mem_rGood.mp hθ
  exact rSplit_transfer cell ord θ hinj hcell hcoll

/-- On the good set, the labels' cells read off the coordinates are the table's. -/
theorem pCellK_rSplit (a : J) :
    pCellK (cellP cell) (rSplit cell ord θ) a = rCellK cell θ.1.1 a := by
  have hP := (rSplit_coords hcell hθ).1
  change cell a (pubParam (rSplit cell ord θ).1.1) (rSplit cell ord θ).2.2 = _
  rw [hP, rSplit_snd]
  rfl

/-- On the good set, the capacities read off the coordinates are the table's. -/
theorem pCellH_rSplit (a : J) :
    pCellH (cellP cell) (rSplit cell ord θ) a = rCellH cell θ.1.1 a := by
  obtain ⟨-, h1, h2, -, -⟩ := rSplit_coords hcell hθ
  simp only [pCellH]
  rw [pCellK_rSplit hcell hθ, rSplit_perm, h1 a, h2 a]
  rfl

/-- **The non-first sets agree**: on the good set, the non-first labels read off the coordinates
(the `h`-stage's) are the table's `rB`. -/
theorem pB_rSplit : pB (cellP cell) ord (rSplit cell ord θ) = rB cell ord θ.1.1 := by
  ext a
  simp only [pB, rB, Set.mem_ofPred_eq, pCellH_rSplit hcell hθ]

/-- **The paths' hashes at the first labels**: on the good set, the hash of a label's one-block
input (first block `cell a P R`) is read off its `h`-slot, for a first label. -/
theorem rSplit_hash (inp : J → PublicParameter → HashOutput → HashInput)
    (hinp : ∀ a P R, firstCell (inp a P R) = cell a P R)
    (hlen : ∀ a P R, (inp a P R).length < 136) (a : J) (ha : a ∉ rB cell ord θ.1.1) :
    θ.1.1.hash (inp a θ.1.1.publicSeed θ.1.1.prfKey) =
      out256 ((rSplit cell ord θ).1.2.2.2 a) := by
  rw [hash_of_lt θ.1.1 _ (hlen _ _ _), hinp, (rSplit_coords hcell hθ).2.2.2.1 a ha]
  rfl

/-- **The digests at the first labels are the coordinates**: on the good set, the digest of a first
label's one-block input is its coordinate `rCoord`. -/
theorem digest_eq_rCoord (inp : J → PublicParameter → HashOutput → HashInput)
    (hinp : ∀ a P R, firstCell (inp a P R) = cell a P R)
    (hlen : ∀ a P R, (inp a P R).length < 136) (a : J) (ha : a ∉ rB cell ord θ.1.1) :
    θ.1.1.digest (inp a θ.1.1.publicSeed θ.1.1.prfKey) = rCoord (rSplit cell ord θ).1 a :=
  congrArg truncateHash (rSplit_hash hcell hθ inp hinp hlen a ha)

/-- **On the good set, the challenger's data is a function of the public part.** -/
theorem schemeData_eq_pubData_rSplit :
    schemeData Q θ.1.1 = pubData Q (rSplit cell ord θ).1.1 := by
  obtain ⟨hgood, hcoll, hread⟩ := mem_rGood.mp hθ
  rw [schemeData_eq_of_mem (mem_schemeGood.mpr hgood)]
  obtain ⟨g4, g5, g6⟩ := rSplit_keys_eq cell ord θ hcell hcoll.1
  have hsl := rSplit_slots cell ord θ
  have hπ : (rSplit cell ord θ).1.1.1.2 = (schemeSplit θ.1).1.1.2 :=
    (rSplit_perm cell ord θ).trans (schemeSplit_perm θ.1).symm
  have hP : pubParam (rSplit cell ord θ).1.1 = pubParam (schemeSplit θ.1).1 :=
    congrArg (fun s : PubSlots ↦ trunc128 s.2.1) hsl
  have hC : pubSec (rSplit cell ord θ).1.1 = pubSec (schemeSplit θ.1).1 :=
    congrArg (fun (s : PubSlots) (d : KeygenDomain) ↦ out256 (s.2.2 d)) hsl
  funext i
  change honestEval (schemeSplit θ.1).1.1.1 (schemeSplit θ.1).1.1.2
      (Q i (pubParam (schemeSplit θ.1).1) (pubSec (schemeSplit θ.1).1)) =
    honestEval (rSplit cell ord θ).1.1.1.1 (rSplit cell ord θ).1.1.1.2
      (Q i (pubParam (rSplit cell ord θ).1.1) (pubSec (rSplit cell ord θ).1.1))
  rw [← hP, ← hC, ← hπ]
  refine honestEval_congr (t := (rSplit cell ord θ).1.1.1.1) (t' := (schemeSplit θ.1).1.1.1)
    (rSplit cell ord θ).1.1.1.2 _ fun e he ↦ ?_
  have ha := honestEval_answeredBy (rSplit cell ord θ).1.1.1.2 (rSplit cell ord θ).1.1.1.1 _ e he
  cases e with
  | h z v =>
    have hz : ∀ a, pCellH (cellP cell) (rSplit cell ord θ) a ≠ z := fun a hza ↦
      (hread i a).2.2 (by rw [hza]; exact mem_hCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g6 z hz]
    exact ha
  | k x v =>
    have hx : ∀ a, pCellK (cellP cell) (rSplit cell ord θ) a ≠ x := fun a hxa ↦
      (hread i a).1 (by rw [hxa]; exact mem_kCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g4 x hx]
    exact ha
  | k' x v =>
    have hx : ∀ a, pCellK' (cellP cell) (rSplit cell ord θ) a ≠ x := fun a hxa ↦
      (hread i a).2.1 (by rw [hxa]; exact mem_k'Cells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g5 x hx]
    exact ha

end coords

/-! ### The bad fraction -/

variable (cell ord) (G : ℕ)

open scoped Classical in
/-- Colliding label rates (any permutation). -/
noncomputable def rateBadAll (x : Pub × Secret) : ℕ :=
  if ¬RateInj cell x then 1 else 0

open scoped Classical in
/-- A good permutation and a label capacity on a hidden capacity. -/
noncomputable def capSepBad (x : Pub × Secret) : ℕ :=
  if PermGood x.1.1.2 G ∧ ¬CapSep cell x then 1 else 0

/-- A static collision of the labels' paths. -/
noncomputable def rCollBad (x : Pub × Secret) : ℕ :=
  rateBadAll cell x + capSepBad cell G x

open scoped Classical in
/-- A table outside `schemeGood Q`. -/
noncomputable def rSchemeBad
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (t : Tab) : ℕ :=
  if t ∈ schemeGood Q then 0 else 1

open scoped Classical in
/-- A table with a bad permutation. -/
noncomputable def permBad (t : Tab) : ℕ :=
  if ¬PermGood t.1.perm G then 1 else 0

/-- The public part and the hidden part as `(π, rest)`. -/
def coordPi : Equiv.Perm (X × Z) × (SpongeKeys X Z × PubSlots × Secret) ≃ Pub × Secret where
  toFun c := (((c.2.1, c.1), c.2.2.1), c.2.2.2)
  invFun x := (x.1.1.2, (x.1.1.1, x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinates other than `π` are finite (named: the product is not found otherwise). -/
noncomputable instance instFintypeRRestPi : Fintype (SpongeKeys X Z × PubSlots × Secret) :=
  instFintypeProd _ _

/-- **Label rate collisions, averaged over `π`**: at most `|J|² / |X|` of the coordinates. -/
theorem card_mul_sum_rateBadAll_le
    (hcell : ∀ P, Function.Injective fun s : HashOutput × J ↦ cell s.2 P s.1) :
    Fintype.card X * ∑ x, rateBadAll cell x ≤
      Fintype.card (Pub × Secret) * (Fintype.card J * Fintype.card J) :=
  card_mul_sum_equiv_prod_le coordPi _ _ (rateBadAll cell) fun r ↦
    card_mul_sum_not_injective_rate_le
      (fun a ↦ (cell a (trunc128 r.2.1.2.1) r.2.2.2,
        r.1.2.1 (cell a (trunc128 r.2.1.2.1) r.2.2.2)))
      fun _ _ h ↦ cell_injective_of hcell _ _ (congrArg Prod.fst h)

omit [DecidableEq J] in
open scoped Classical in
theorem capSepBad_coordS (ω : Coord) (S : MasterSeed) (k k' : X → Z) :
    capSepBad cell G (coordS (((ω, S), k), k')) =
      (if PermGood ω.1 G ∧ ¬∀ a b, capOf k k' ω.1 (cell a (trunc128 ω.2.2.1.2.1) ω.2.2.2) ≠
        capOf k k' ω.1 (skCell (trunc128 ω.2.2.1.2.1) S b) then 1 else 0) :=
  rfl

omit [DecidableEq J] in
/-- **Label capacities on hidden capacities**: at most `|J| |A| (G + 1) / |Z|` of the
coordinates, `A = SkIdx`. -/
theorem card_mul_sum_capSepBad_le (hsep : ∀ P S b a R, skCell P S b ≠ cell a P R) :
    Fintype.card Z * ∑ x, capSepBad cell G x ≤
      Fintype.card Tab * (Fintype.card J * Fintype.card SkIdx * (G + 1)) := by
  rw [sum_eq_sum_coords coordS (capSepBad cell G), card_tab_eq]
  have h : Fintype.card Z * ∑ ω : Coord, ∑ S : MasterSeed, ∑ k : X → Z, ∑ k' : X → Z,
      capSepBad cell G (coordS (((ω, S), k), k')) =
        ∑ ω : Coord, ∑ S : MasterSeed, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
          capSepBad cell G (coordS (((ω, S), k), k')) := by
    simp only [Finset.mul_sum]
  rw [h]
  refine sum_sum_le_mul _ _ _ fun ω S ↦ ?_
  simp only [capSepBad_coordS]
  exact card_mul_sum_capOf_cross_le ω.1 G (fun a ↦ cell a (trunc128 ω.2.2.1.2.1) ω.2.2.2)
    (fun b ↦ skCell (trunc128 ω.2.2.1.2.1) S b) fun a b ↦ (hsep _ S b a _).symm

/-- Cancelling the cardinality of a coordinate the bound does not see. -/
theorem card_mul_le_of_card_prod_mul_le {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    {s n q : ℕ} (h : Fintype.card (A × B) * s ≤ n * (Fintype.card A * q)) :
    Fintype.card B * s ≤ n * q := by
  rw [Fintype.card_prod, mul_assoc, mul_left_comm n] at h
  exact Nat.le_of_mul_le_mul_left h Fintype.card_pos

open scoped Classical in
/-- **The labels' first blocks are rarely read**: at most `qsᵢ / 2^256` of the coordinates, where
`qsᵢ` bounds the reads of `Q i` at `k`-cells of the form `cell a P R`. -/
theorem card_mul_sum_readK_le
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (qs : ι → ℕ) (hcell : ∀ P, Function.Injective fun s : HashOutput × J ↦ cell s.2 P s.1)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsCell cell P)).card ≤
        qs i) (i : ι) :
    Fintype.card HashOutput * ∑ y, pReadK (cellP cell) (qReads Q) i y ≤
      Fintype.card (RPub J × Secret) * qs i := by
  refine card_mul_le_of_card_prod_mul_le (A := MasterSeed) ?_
  refine card_mul_sum_pReadK_le (cellP cell) (qReads Q) (fun i ↦ Fintype.card MasterSeed * qs i)
    (fun i p ↦ ?_) i
  have hS : ∀ S : MasterSeed, (∑ R : HashOutput, ∑ a,
      (if cellP cell p.2 (S, R) a ∈ kCells (qReads Q i p) then 1 else 0)) =
        ∑ R : HashOutput, ∑ a,
          (if cell a (trunc128 p.2.2.1) R ∈ kCells (qReads Q i p) then 1 else 0) :=
    fun _ ↦ rfl
  rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun S _ ↦ hS S, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  refine Nat.mul_le_mul_left _ ?_
  rw [← Fintype.sum_prod_type']
  exact (sum_ite_mem_le_card_filter
    (fun s : HashOutput × J ↦ cell s.2 (trunc128 p.2.2.1) s.1)
    (hcell _) _ (IsCell cell (trunc128 p.2.2.1)) fun s ↦ ⟨s.2, s.1, rfl⟩).trans (hqs i _ _ _ _)

open scoped Classical in
/-- The tables outside the good set: outside `schemeGood`, a bad permutation, a static collision
of the labels' paths, or a computation reading a label's cell. -/
theorem card_sub_card_rGood_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Fintype.card (RTab J) - (rGood cell ord Q).card ≤
      ∑ θ : RTab J, ((rSchemeBad Q θ.1 + permBad G θ.1) + (rCollBad cell G (schemeSplit θ.1) +
        ∑ i, (pReadK (cellP cell) (qReads Q) i (rSplit cell ord θ) +
          pReadKH (cellP cell) G (qReads Q) i (rSplit cell ord θ)))) := by
  refine card_sub_card_le_sum (rGood cell ord Q) _ fun θ hθ ↦ ?_
  rw [mem_rGood] at hθ
  set y := rSplit cell ord θ with hy
  by_cases hs : θ.1 ∈ schemeGood Q
  · by_cases hG : PermGood θ.1.1.perm G
    · by_cases hcoll : RColl cell (schemeSplit θ.1)
      · have hread : ¬PReadGood (cellP cell) (qReads Q) y :=
          fun h ↦ hθ ⟨mem_schemeGood.mp hs, hcoll, h⟩
        obtain ⟨i, a, hia⟩ : ∃ i a,
            ¬(pCellK (cellP cell) y a ∉ kCells (qReads Q i y.1.1) ∧
              pCellK' (cellP cell) y a ∉ k'Cells (qReads Q i y.1.1) ∧
              pCellH (cellP cell) y a ∉ hCells (qReads Q i y.1.1)) := by
          by_contra hne
          exact hread fun i a ↦ by_contra fun h ↦ hne ⟨i, a, h⟩
        have hG' : PermGood y.1.1.1.2 G := by
          rw [hy, rSplit_perm]
          exact hG
        have hk : pKHit (cellP cell) (qReads Q) i a y ≤ pReadK (cellP cell) (qReads Q) i y :=
          Finset.single_le_sum (f := fun a' ↦ pKHit (cellP cell) (qReads Q) i a' y)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        have hkh : pK'Hit (cellP cell) G (qReads Q) i a y + pHHit (cellP cell) (qReads Q) i a y ≤
            pReadKH (cellP cell) G (qReads Q) i y :=
          Finset.single_le_sum (f := fun a' ↦ pK'Hit (cellP cell) G (qReads Q) i a' y +
            pHHit (cellP cell) (qReads Q) i a' y) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        have h1 : 1 ≤ pReadK (cellP cell) (qReads Q) i y +
            pReadKH (cellP cell) G (qReads Q) i y := by
          by_cases m1 : pCellK (cellP cell) y a ∈ kCells (qReads Q i y.1.1)
          · have : pKHit (cellP cell) (qReads Q) i a y = 1 := ite_eq_left m1
            omega
          · by_cases m2 : pCellK' (cellP cell) y a ∈ k'Cells (qReads Q i y.1.1)
            · have : pK'Hit (cellP cell) G (qReads Q) i a y = 1 := ite_eq_left ⟨hG', m2⟩
              omega
            · have m3 : pCellH (cellP cell) y a ∈ hCells (qReads Q i y.1.1) :=
                by_contra fun m3 ↦ hia ⟨m1, m2, m3⟩
              have : pHHit (cellP cell) (qReads Q) i a y = 1 := ite_eq_left m3
              omega
        have h2 : pReadK (cellP cell) (qReads Q) i y + pReadKH (cellP cell) G (qReads Q) i y ≤
            ∑ i', (pReadK (cellP cell) (qReads Q) i' y +
              pReadKH (cellP cell) G (qReads Q) i' y) :=
          Finset.single_le_sum (f := fun i' ↦ pReadK (cellP cell) (qReads Q) i' y +
            pReadKH (cellP cell) G (qReads Q) i' y) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ i)
        omega
      · have hG' : PermGood (schemeSplit θ.1).1.1.2 G := by
          rw [schemeSplit_perm]
          exact hG
        have h1 : 1 ≤ rCollBad cell G (schemeSplit θ.1) := by
          by_cases hr : RateInj cell (schemeSplit θ.1)
          · have : capSepBad cell G (schemeSplit θ.1) = 1 :=
              ite_eq_left ⟨hG', fun hc ↦ hcoll ⟨hr, hc⟩⟩
            unfold rCollBad
            omega
          · have : rateBadAll cell (schemeSplit θ.1) = 1 := ite_eq_left hr
            unfold rCollBad
            omega
        omega
    · have : permBad G θ.1 = 1 := ite_eq_left hG
      omega
  · have : rSchemeBad Q θ.1 = 1 := ite_eq_right hs
    omega

open scoped Classical in
/-- **The bad fraction of the label stages**: the fraction of tables outside `rGood cell ord Q` is
at most the fraction outside `schemeGood Q`, plus the fraction of permutations with a rate count
above `G`, plus the rate collisions `|J|² / |X|` (averaged over the permutation), plus the capacity
hits `|J| |A| (G + 1) / |Z|` (`A = SkIdx`), plus per computation
`qsᵢ / 2^256 + |J| (G + 1) qᵢ / |Z|`, where `qᵢ` bounds the reads of `Q i` and `qsᵢ` its reads at
`k`-cells of the form `cell a P R`. The labels' first blocks are distinct for distinct labels or
keys `SK.prf` (`hcell`) and differ from the `SK.seed`-keyed cells (`hsep`). -/
theorem rGood_frac_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsCell cell P)).card ≤
        qs i)
    (hcell : ∀ P, Function.Injective fun s : HashOutput × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S b a R, skCell P S b ≠ cell a P R) :
    (Fintype.card (RTab J) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (RTab J) - (rGood cell ord Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        (((Fintype.card J * Fintype.card J : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((Fintype.card J * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z) +
        ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + Fintype.card J * (G + 1) * q i / Fintype.card Z) := by
  refine inv_mul_le_of_parts Fintype.card_ne_zero
    ((card_sub_card_rGood_le cell ord G Q).trans_eq (sum_add_sum_eq _ _ _ _)) ?_ ?_ ?_ ?_
  · rw [Finset.sum_add_distrib, Nat.cast_add, mul_add]
    refine add_le_add (le_of_eq ?_) ?_
    · have hs : ∑ t, rSchemeBad Q t = Fintype.card Tab - (schemeGood Q).card :=
        sum_ite_mem_zero_one_eq (schemeGood Q)
      rw [sum_fst_eq (rSchemeBad Q), hs]
      exact natCast_smul_eq_card_mul _
    · exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
        (card_mul_sum_fst_eq (γ := CoinSlots J) (permBad G) _ _
          (card_mul_sum_tab_not_permGood G)).le
  · have hrate := card_mul_sum_rateBadAll_le cell hcell
    rw [← Fintype.card_congr schemeSplit] at hrate
    have h1 := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_fst_equiv_le (γ := CoinSlots J) schemeSplit (rateBadAll cell) _ _ hrate)
    have h2 := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_fst_equiv_le (γ := CoinSlots J) schemeSplit (capSepBad cell G) _ _
        (card_mul_sum_capSepBad_le cell G hsep))
    calc ((∑ θ : RTab J, rCollBad cell G (schemeSplit θ.1) : ℕ) : ℝ≥0∞)
        = ((∑ θ : RTab J, rateBadAll cell (schemeSplit θ.1) : ℕ) : ℝ≥0∞) +
            ((∑ θ : RTab J, capSepBad cell G (schemeSplit θ.1) : ℕ) : ℝ≥0∞) := by
          rw [← Nat.cast_add, ← Finset.sum_add_distrib]
          rfl
      _ ≤ _ := (add_le_add h1 h2).trans_eq (mul_add _ _ _).symm
  · intro i
    have h := natCast_le_mul_div_of_mul_le (Fintype.card_ne_zero (α := HashOutput))
      (card_mul_sum_equiv_le (rSplit cell ord) (pReadK (cellP cell) (qReads Q) i) _ _
        (card_mul_sum_readK_le cell Q qs hcell hqs i))
    rwa [(card_masterSeed : Fintype.card HashOutput = 2 ^ 256), Nat.cast_pow,
      Nat.cast_ofNat] at h
  · intro i
    have h := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le (rSplit cell ord) (pReadKH (cellP cell) G (qReads Q) i) _ _
        (card_mul_sum_pReadKH_le (cellP cell) G (qReads Q) q
          (fun i p ↦ hq i p.1.1 p.1.2 (pubParam p) (pubSec p)) i))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    exact h

/-- **A label is rarely non-first**: over the coordinates of `rSplit`, a label is non-first for at
most a `|J| / |Z|` fraction (its `k'`-slot resampled): the averaged charge of Mismatch's non-first
labels. -/
theorem card_mul_sum_pBInd_rSplit_le (a : J) :
    Fintype.card Z * ∑ y : RPub J × Secret, pBInd (cellP cell) ord a y ≤
      Fintype.card (RPub J × Secret) * Fintype.card J :=
  card_mul_sum_pBInd_le (cellP cell) ord a

end rstage

/-! ## The randomizer stage: the messages' `PRF_msg` paths -/

section msg

variable {ι : Type} {β : ι → Type}

/-- **The randomizers of the first messages are the coordinates**: on the good set of the
randomizer stage, the randomizer `R(M)` of a first message is its coordinate `rCoord`. -/
theorem randomizer_eq_rCoord
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {θ : RTab Message} (hθ : θ ∈ rGood rCell rOrd Q) (M : Message)
    (hM : M ∉ rB rCell rOrd θ.1.1) :
    θ.1.1.randomizer M = rCoord (rSplit rCell rOrd θ).1 M :=
  digest_eq_rCoord rCell_injective hθ (fun M P R ↦ prfMessageInput R P M) (fun _ _ _ ↦ rfl)
    (fun M P R ↦ length_prfMessageInput_lt R P M) M hM

open scoped Classical in
/-- **The bad fraction of the randomizer stage.** -/
theorem rGood_frac_le_message [Fintype ι] (G : ℕ)
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsCell rCell P)).card ≤
        qs i) :
    (Fintype.card (RTab Message) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (RTab Message) - (rGood rCell rOrd Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        (((Fintype.card Message * Fintype.card Message : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((Fintype.card Message * Fintype.card SkIdx * (G + 1) : ℕ) : ℝ≥0∞) /
            Fintype.card Z) +
        ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + Fintype.card Message * (G + 1) * q i / Fintype.card Z) :=
  rGood_frac_le rCell rOrd G Q q qs hq hqs rCell_injective skCell_ne_rCell

/-! ### At Keccak's sizes -/

theorem card_message : Fintype.card Message = 2 ^ 256 :=
  card_masterSeed

set_option exponentiation.threshold 4096 in
/-- **The static collision terms at Keccak's sizes** (`G = 18`): the rate collisions
`|J|² / |X| = 2^-576` and the capacity hits `|J| |A| 19 / |Z| ≤ 19 · 2^-212`. -/
theorem rCollTerms_le_keccak :
    ((Fintype.card Message * Fintype.card Message : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((Fintype.card Message * Fintype.card SkIdx * (18 + 1) : ℕ) : ℝ≥0∞) /
          Fintype.card Z ≤ ENNReal.ofReal (1 / 2 ^ 207) := by
  have hA : Fintype.card Message * Fintype.card SkIdx * (18 + 1) ≤ 2 ^ 256 * 2 ^ 44 * 19 := by
    rw [card_message]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ card_skIdx_le)
  refine (add_le_add le_rfl (ENNReal.div_le_div_right (Nat.cast_le.mpr hA) _)).trans ?_
  rw [card_message, Quantum.Xmss.Hybrid.R0.card_rate, Quantum.Xmss.Hybrid.R0.card_cap,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity),
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity),
    ← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The read terms at Keccak's sizes** (`G = 18`): `|J| 19 q / |Z| ≤ q / 2^251`. -/
theorem rReadKHTerm_le_keccak (q : ℕ) :
    (Fintype.card Message : ℝ≥0∞) * ((18 : ℕ) + 1) * q / Fintype.card Z ≤
      ENNReal.ofReal (q / 2 ^ 251) := by
  have h : (Fintype.card Message : ℝ≥0∞) * ((18 : ℕ) + 1) * q =
      ((2 ^ 256 * 19 * q : ℕ) : ℝ≥0∞) := by
    rw [card_message]
    push_cast
    ring
  have hn : 2 ^ 256 * 19 * q * 2 ^ 251 ≤ q * 2 ^ 512 := by
    calc 2 ^ 256 * 19 * q * 2 ^ 251 = q * (2 ^ 256 * 19 * 2 ^ 251) := by ring
      _ ≤ q * 2 ^ 512 := Nat.mul_le_mul_left q (by norm_num)
  rw [h, Quantum.Xmss.Hybrid.R0.card_cap,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hn

open scoped Classical in
/-- **The bad fraction of the randomizer stage at Keccak's sizes** (`G = 18`): the fraction
outside `schemeGood` and the bad permutations, plus `2^-207` for the static collisions, plus per
computation `qsᵢ / 2^256 + qᵢ / 2^251`. -/
theorem rGood_frac_le_keccak [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsCell rCell P)).card ≤
        qs i) :
    (Fintype.card (RTab Message) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (RTab Message) - (rGood rCell rOrd Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        ENNReal.ofReal (1 / 2 ^ 207) +
        ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + ENNReal.ofReal (q i / 2 ^ 251)) :=
  (rGood_frac_le_message 18 Q q qs hq hqs).trans (add_le_add (add_le_add le_rfl
    rCollTerms_le_keccak) (Finset.sum_le_sum fun i _ ↦ add_le_add le_rfl
      (rReadKHTerm_le_keccak (q i))))

end msg

end Quantum.Sphincs.Hybrid

end
