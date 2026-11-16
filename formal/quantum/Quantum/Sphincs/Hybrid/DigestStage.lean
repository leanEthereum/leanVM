module

public import Quantum.Sphincs.Hybrid.RStage
public import Quantum.Sphincs.Hybrid.View

@[expose] public section

/-!
# The digest stage: `H_msg`'s paths in public slots

leanSPHINCS's message digest is two one-block hashes `H_msg(R, PK.seed, PK.root, M, i)`
(`messageDigestInput`, 84 bytes, `i : DigestCall`) whose randomizer `R = R(M)` is the hidden
`PRF_msg` value the randomizer stage (`Quantum.Sphincs.Hybrid.RStage`) moved into the `h`-slot of
`M`. A second application of the path stages (`pStages`), composed after `rSplit`, moves the digest
paths' values into slots: `k` at every label, `k'` at every label, and `h` at the capacity of each
first label, the slot taking the block's output, whose first `256` bits are the coordinate `dCoord`
(`outSplit`; the other `832` bits are a pad).

**The labels carry the root.** The cell of `H_msg` call `i` on `M` is keyed by `PK.root`, a value of
the whole table that the stage itself changes (it is computed from the keys), so it is not data the
stage keeps. The labels are therefore `(root, M, i)` over all roots (`DLab`, `2^385` labels);
the label of the table's `H_msg` call `i` on `M` is `(L.root, M, i)`. The counts below stay small
at this size (`|J| / |Z| ≤ 2^-127`).

## The charged labels and the path stages' counts, over abstract kept data

* `pBX c ord extra`: a label is charged when a label of smaller rank or a capacity of `extra` (cells
  of earlier stages, data the stage keeps) sits at its capacity; `card_mul_sum_pBXInd_le`: at most
  `(|J| + m) / |Z|` of the coordinates, `m` bounding `extra`.
* `card_mul_sum_pReadK_le_mul`: `card_mul_sum_pReadK_le` with a factor on the reads summed over `F`.
* `pStages_keep`: the path stages keep `π`, `E` and `F`.

## The digest stage over abstract label types

Over the randomizer stage's labels `I` (cells `rcell`, rank `rord`) and the digest stage's labels
`J` (cells `dcell a P R`, message `msg a`, rank `dord`):

* `dSplit : DTab I J ≃ DSt I J`: `rSplit`, then `pStages (dCellP dcell msg) dord` with the public
  slots `E = PubSlots` and the kept data `F = DF I = CoinSlots I × Secret` (the randomizer stage's
  slots and the hidden part). `dPre` is the coordinate system before the digest stage.
* `dBX`: the charged labels, read off the coordinates: a label of smaller rank, a randomizer-stage
  capacity (`dRCap`), or an `SK.seed`-keyed capacity (`dPos`) at its capacity.
* **The good set** `dGood`: `rGood`, the rates of the digest-stage, randomizer-stage and `SK.seed`
  first blocks distinct before the stage (`DRateInj`), and no computation of `Q` reading a digest
  path cell (`PReadGood`).
* `dSplit_transfer`: on the good set, the slot of an uncharged label holds the table's output of the
  block keyed by `PK.seed`, the randomizer coordinate `rCoord` of its message and the label.
  `schemeData_eq_pubData_dSplit`: the challenger's data is a function of the public part.
  `dSplit_snd`: the kept data is the randomizer stage's slots and `(SK.seed, SK.prf)`.
* **The bad fraction** `dGood_frac_le`: `rGood`'s, the bad permutations, the rate collisions
  `(|J| + |I| + |A|)² / |X|` (averaged over `π`, `A = SkIdx`), and per computation
  `qsᵢ / 2^128 + |J| (G + 1) qᵢ / |Z|` (`qsᵢ` its reads at digest-stage first blocks, averaged over
  the randomizer slots). `card_mul_sum_dBXInd_le`: a label is charged for at most
  `(|J| + |I| + |A|) / |Z|` of the tables (its `k'`-slot resampled): Mismatch's non-first charge.

## The digest stage

* `DLab = Digest × Message × DigestCall`, `dLabCell (root, M, i) P R = hmsgCell R P root M i`,
  distinct (`dLabCell_injective`) and apart from the randomizer and `SK.seed` cells.
* `digest_eq_dCoord`: on `dGood`, for a first message of the randomizer stage and an uncharged label
  `(L.root, M, i)`, `L.digestOutput M i = dCoord (dSplit θ) (L.root, M, i)`.
* At Keccak's sizes (`G = 18`): `dGood_frac_le_keccak` (`rGood_frac_le_keccak`'s terms, the bad
  permutations, `2^-316`, and `qsᵢ / 2^128 + qᵢ / 2^122` per computation) and
  `dBXInd_frac_le_keccak` (`2^-126` per label).
-/

open scoped ENNReal

open Quantum.SufCma

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer HashInput MasterSeed)
open Common.SufCma (SchemeHashSpec)
open Quantum.Xmss (X Z out256 trunc128 card_fiber_trunc128)
open Quantum.Xmss.Hybrid (CoinSlots IsFirst capOf rateOf firstCell kCells k'Cells hCells mem_kCells
  mem_k'Cells mem_hCells sum_ite_add_mem_eq_card sum_ite_mem_le_card_filter sum_eq_sum_coords
  card_eq_coords sum_comm_three card_mul_sum_le_of_update card_mul_sum_not_injective_rate_le
  card_mul_sum_equiv_prod_le card_mul_sum_equiv_le natCast_smul_eq_card_mul sum_add_sum_eq
  sum_ite_mem_zero_one_eq sum_fst_eq inv_mul_le_of_parts card_sub_card_le_sum
  natCast_le_mul_div_of_mul_le)

namespace Quantum.Sphincs.Hybrid

/-! ## The charged labels and the path stages' counts, over abstract kept data -/

section pathStagesX

variable {E F J : Type} (c : E → F → J → X) (ord : J ↪ ℕ)
  (extra : (SpongeKeys X Z × Equiv.Perm (X × Z)) × E → F → Finset Z)

/-- **The path stages keep `π`, `E` and `F`.** -/
theorem pStages_keep (x : PSt E F J) :
    (pStages c ord x).1.1.1.2 = x.1.1.1.2 ∧ (pStages c ord x).1.1.2 = x.1.1.2 ∧
      (pStages c ord x).2 = x.2 := by
  obtain ⟨_, _, _, _, hE, -⟩ := pStages_spec c ord x.1.1.1.1 x.1.1.1.2 x.1.1.2 x.1.2 x.2
  rw [show pStages c ord x = _ from hE]
  exact ⟨rfl, rfl, rfl⟩

/-- **The charged labels**: a label of smaller rank, or a capacity of `extra` (data the stages
keep), at the label's capacity read off the coordinates. -/
def pBX (y : PSt E F J) : Set J :=
  {a | a ∈ pB c ord y ∨ pCellH c y a ∈ extra y.1.1 y.2}

open scoped Classical in
/-- The label `a` is charged at the coordinates `y`. -/
noncomputable def pBXInd (a : J) (y : PSt E F J) : ℕ :=
  if a ∈ pBX c ord extra y then 1 else 0

/-- The charge of `a` with its `k'`-coin at `w` is at most that of its capacity hitting the other
labels' capacities or `extra`. -/
theorem pBXInd_update_le [Fintype J] [DecidableEq J]
    (ω : ((SpongeKeys X Z × Equiv.Perm (X × Z)) × E) × (J → X)) (f : F) (kc k'c : J → Z) (a : J)
    (w : Z) :
    pBXInd c ord extra a (pCoordC (((ω, f), kc), Function.update k'c a w)) ≤
      if (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + w ∈ (Finset.univ.filter fun b ↦ b ≠ a).image
        (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b) ∪ extra ω.1 f then 1 else 0 := by
  have hcap : pCellH c (pCoordC (((ω, f), kc), Function.update k'c a w)) a =
      (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + w := by
    change (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + Function.update k'c a w a = _
    rw [Function.update_self]
  by_cases ha : a ∈ pBX c ord extra (pCoordC (((ω, f), kc), Function.update k'c a w))
  · have hmem : (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + w ∈ (Finset.univ.filter fun b ↦ b ≠ a).image
        (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b) ∪ extra ω.1 f := by
      rcases ha with ⟨b, hb, he⟩ | hx
      · have hba : b ≠ a := fun h ↦ (lt_irrefl _) (h ▸ hb)
        refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, by simp [hba], ?_⟩)
        have he' : (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + Function.update k'c a w b =
            (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + Function.update k'c a w a := he
        rwa [Function.update_of_ne hba, Function.update_self] at he'
      · rw [hcap] at hx
        exact Finset.mem_union_right _ hx
    rw [pBXInd, ite_eq_left ha, ite_eq_left hmem]
  · rw [pBXInd, ite_eq_right ha]
    exact Nat.zero_le _

/-- **A label is rarely charged**: `a` is charged for at most `(|J| + m) / |Z|` of the coordinates,
its `k'`-coin resampled, when `extra` has at most `m` cells. -/
theorem card_mul_sum_pBXInd_le [Fintype E] [Fintype F] [Fintype J] [DecidableEq J] (m : ℕ)
    (hm : ∀ ω f, (extra ω f).card ≤ m) (a : J) :
    Fintype.card Z * ∑ y, pBXInd c ord extra a y ≤
      Fintype.card (PSt E F J) * (Fintype.card J + m) := by
  rw [sum_eq_sum_coords pCoordC (pBXInd c ord extra a), card_eq_coords pCoordC]
  refine card_mul_sum4_le_upd_one
    (fun ω f kc k'c ↦ pBXInd c ord extra a (pCoordC (((ω, f), kc), k'c))) a _
    fun ω f kc k'c ↦ ?_
  calc ∑ w, pBXInd c ord extra a (pCoordC (((ω, f), kc), Function.update k'c a w))
      ≤ ∑ w : Z, (if (ω.1.1.2 (c ω.1.2 f a, kc a)).2 + w ∈
          (Finset.univ.filter fun b ↦ b ≠ a).image
            (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b) ∪ extra ω.1 f then 1 else 0) :=
        Finset.sum_le_sum fun w _ ↦ pBXInd_update_le c ord extra ω f kc k'c a w
    _ = ((Finset.univ.filter fun b ↦ b ≠ a).image
          (fun b ↦ (ω.1.1.2 (c ω.1.2 f b, kc b)).2 + k'c b) ∪ extra ω.1 f).card :=
        sum_ite_add_mem_eq_card _ _
    _ ≤ Fintype.card J + m :=
        (Finset.card_union_le _ _).trans (add_le_add (Finset.card_image_le.trans
          ((Finset.card_filter_le _ _).trans_eq Finset.card_univ)) (hm _ _))

/-- A count over four coordinates whose sum over the second, times `d`, is at most `|S| c`. -/
theorem card_mul_sum4_le_snd_mul {Ω S K : Type*} [Fintype Ω] [Fintype S] [Fintype K]
    (f : Ω → S → K → K → ℕ) (d c : ℕ)
    (h : ∀ ω k k', d * ∑ s, f ω s k k' ≤ Fintype.card S * c) :
    d * ∑ ω, ∑ s, ∑ k, ∑ k', f ω s k k' ≤
      Fintype.card Ω * Fintype.card S * (Fintype.card K * Fintype.card K) * c := by
  calc d * ∑ ω, ∑ s, ∑ k, ∑ k', f ω s k k'
      = ∑ ω, ∑ k, ∑ k', d * ∑ s, f ω s k k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [sum_comm_three fun s k k' ↦ f ω s k k']
        simp only [Finset.mul_sum]
    _ ≤ ∑ _ω : Ω, ∑ _k : K, ∑ _k' : K, Fintype.card S * c :=
        Finset.sum_le_sum fun ω _ ↦ Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun k' _ ↦
          h ω k k'
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

variable {ι : Type}

/-- **The paths' first blocks are rarely read**, with a factor: when `d` times the reads of `rd i`
at the first blocks, summed over `F`, is at most `|F| B i`, then `d` times their weight is at most
`B i` of the coordinates. -/
theorem card_mul_sum_pReadK_le_mul [Fintype E] [Fintype F] [Fintype J] [DecidableEq J]
    (rd : ι → (SpongeKeys X Z × Equiv.Perm (X × Z)) × E → List (SpongeRead X Z)) (d : ℕ)
    (B : ι → ℕ)
    (hB : ∀ i p, d * ∑ f, ∑ a, (if c p.2 f a ∈ kCells (rd i p) then 1 else 0) ≤
      Fintype.card F * B i) (i : ι) :
    d * ∑ y, pReadK c rd i y ≤ Fintype.card (PSt E F J) * B i := by
  rw [sum_eq_sum_coords pCoordC (pReadK c rd i), card_eq_coords pCoordC]
  refine card_mul_sum4_le_snd_mul _ d (B i) fun ω _ _ ↦ ?_
  change d * ∑ f, ∑ a, (if c ω.1.2 f a ∈ kCells (rd i ω.1) then 1 else 0) ≤ _
  exact hB i ω.1

end pathStagesX

/-! ## Sums through one coordinate, over abstract types -/

section evalSums

/-- **A sum through a map with uniform fibers**: each fiber of `g` has `m` points. -/
theorem sum_comp_eq_mul_sum {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B] (g : A → B)
    (m : ℕ) (hm : ∀ b, (Finset.univ.filter fun a ↦ g a = b).card = m) (G : B → ℕ) :
    ∑ a, G (g a) = m * ∑ b, G b := by
  rw [← Finset.sum_fiberwise' Finset.univ g G, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_const, hm b, smul_eq_mul]

/-- A value of a map lies in the image of all points, on the right of a union. -/
theorem mem_union_image_univ_right {A B : Type*} [Fintype A] [DecidableEq B] (s : Finset B)
    (g : A → B) (a : A) : g a ∈ s ∪ Finset.univ.image g :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem g (Finset.mem_univ a))

/-- A value of a map lies in the image of all points, on the left of a union. -/
theorem mem_union_image_univ_left {A B : Type*} [Fintype A] [DecidableEq B] (s : Finset B)
    (g : A → B) (a : A) : g a ∈ Finset.univ.image g ∪ s :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem g (Finset.mem_univ a))

/-- **A sum through one value of a function-valued coordinate**: the value of the last component at
`m` is uniform. -/
theorem card_mul_sum_eval_le {A B S W I : Type*} [Fintype A] [Fintype B] [Fintype S] [Fintype W]
    [Fintype I] [DecidableEq I] (g : W → ℕ) (m : I) :
    Fintype.card W * ∑ f : (A × B × (I → W)) × S, g (f.1.2.2 m) ≤
      Fintype.card ((A × B × (I → W)) × S) * ∑ w, g w := by
  have h1 : Fintype.card W * ∑ hv : I → W, g (hv m) ≤ Fintype.card (I → W) * ∑ w, g w :=
    card_mul_sum_le_of_update (fun hv ↦ g (hv m)) m _ fun hv ↦ by
      simp only [Function.update_self, le_refl]
  have hs : ∑ f : (A × B × (I → W)) × S, g (f.1.2.2 m) =
      Fintype.card S * (Fintype.card A * (Fintype.card B * ∑ hv : I → W, g (hv m))) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Finset.mul_sum]
  rw [hs]
  calc Fintype.card W * (Fintype.card S * (Fintype.card A * (Fintype.card B *
        ∑ hv : I → W, g (hv m))))
      = Fintype.card S * (Fintype.card A * (Fintype.card B *
          (Fintype.card W * ∑ hv : I → W, g (hv m)))) := by ring
    _ ≤ Fintype.card S * (Fintype.card A * (Fintype.card B *
          (Fintype.card (I → W) * ∑ w, g w))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1))
    _ = _ := by
        rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
        ring

end evalSums

/-! ## The digest stage over abstract label types -/

section dstage

variable {I J : Type}

/-- The data the digest stage keeps besides the public slots: the randomizer stage's coin slots
(its `h`-slots hold the randomizers' outputs) and the hidden part. -/
abbrev DF (I : Type) : Type := CoinSlots I × Secret

/-- The digest stage's coordinates. -/
abbrev DSt (I J : Type) : Type := PSt PubSlots (DF I) J

/-- The tables with the randomizer stage's and the digest stage's coin slots. -/
abbrev DTab (I J : Type) : Type := RTab I × CoinSlots J

/-- The kept data is finite (named: the product is not found otherwise). -/
noncomputable instance instFintypeDF [Fintype I] [DecidableEq I] : Fintype (DF I) :=
  instFintypeProd _ _

/-- The tables with both stages' coin slots are finite (named). -/
noncomputable instance instFintypeDTab [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    Fintype (DTab I J) :=
  instFintypeProd _ _

/-- The coordinates after the randomizer stage, with the digest stage's coin slots, in the
path-stage form. -/
def reorderD : (RPub I × Secret) × CoinSlots J ≃ DSt I J where
  toFun x := ((x.1.1.1, x.2), (x.1.1.2, x.1.2))
  invFun y := (((y.1.1, y.2.1), y.2.2), y.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinates with `π` first. -/
def dCoordPi :
    Equiv.Perm (X × Z) × (SpongeKeys X Z × PubSlots × CoinSlots J × DF I) ≃ DSt I J where
  toFun c := ((((c.2.1, c.1), c.2.2.1), c.2.2.2.1), c.2.2.2.2)
  invFun x := (x.1.1.1.2, (x.1.1.1.1, x.1.1.2, x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinates other than `π` are finite (named). -/
noncomputable instance instFintypeDRestPi [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] : Fintype (SpongeKeys X Z × PubSlots × CoinSlots J × DF I) :=
  instFintypeProd _ _

variable (rcell : I → PublicParameter → HashOutput → X) (rord : I ↪ ℕ)
  (dcell : J → PublicParameter → Randomizer → X) (msg : J → I) (dord : J ↪ ℕ)

/-- The digest stage's first blocks in the path-stage form: `PK.seed` from slot `1`, and the
randomizer of the label's message from the first `128` bits of its randomizer-stage `h`-slot. -/
def dCellP (e : PubSlots) (f : DF I) (a : J) : X :=
  dcell a (trunc128 e.2.1) (trunc128 (f.1.2.2 (msg a)))

/-- **The coordinates before the digest stage**: `rSplit`, with the digest stage's coin slots. -/
noncomputable def dPre : DTab I J ≃ DSt I J :=
  ((rSplit rcell rord).prodCongr (Equiv.refl (CoinSlots J))).trans reorderD

/-- **The digest stage**: `rSplit`, then the path stages of the digest labels. -/
noncomputable def dSplit : DTab I J ≃ DSt I J :=
  (dPre rcell rord).trans (pStages (dCellP dcell msg) dord)

theorem dSplit_apply (θ : DTab I J) :
    dSplit rcell rord dcell msg dord θ = pStages (dCellP dcell msg) dord
      (((((rSplit rcell rord θ.1).1.1.1.1, (rSplit rcell rord θ.1).1.1.1.2),
        (rSplit rcell rord θ.1).1.1.2), θ.2),
        ((rSplit rcell rord θ.1).1.2, (rSplit rcell rord θ.1).2)) :=
  rfl

theorem dSplit_eq_pStages (θ : DTab I J) :
    dSplit rcell rord dcell msg dord θ = pStages (dCellP dcell msg) dord (dPre rcell rord θ) :=
  rfl

/-- **The kept data**: the randomizer stage's slots and the hidden `(SK.seed, SK.prf)`. -/
theorem dSplit_snd (θ : DTab I J) :
    (dSplit rcell rord dcell msg dord θ).2 =
      ((rSplit rcell rord θ.1).1.2, (θ.1.1.1.secretSeed, θ.1.1.1.prfKey)) := by
  rw [dSplit_eq_pStages, (pStages_keep _ _ _).2.2]
  change ((rSplit rcell rord θ.1).1.2, (rSplit rcell rord θ.1).2) = _
  rw [rSplit_snd]

theorem dSplit_perm (θ : DTab I J) :
    (dSplit rcell rord dcell msg dord θ).1.1.1.2 = (dPre rcell rord θ).1.1.1.2 := by
  rw [dSplit_eq_pStages, (pStages_keep _ _ _).1]

/-- The coordinate of a digest label: the hash output of its `h`-slot (`outSplit`); the other `832`
bits are a pad. -/
def dCoord (y : DSt I J) (a : J) : HashOutput :=
  (outSplit (y.1.2.2.2 a)).1

/-- The randomizer stage's capacities read off the public part and the kept data. -/
def dRCap (ω : Pub) (f : DF I) (b : I) : Z :=
  (ω.1.2 (rcell b (trunc128 ω.2.2.1) f.2.2, f.1.1 b)).2 + f.1.2.1 b

/-- The `SK.seed`-keyed capacities read off the public part and the kept data. -/
def dPos (ω : Pub) (f : DF I) (b : SkIdx) : Z :=
  capOf ω.1.1.2.1 ω.1.1.2.2 ω.1.2 (skCell (trunc128 ω.2.2.1) f.2.1 b)

/-- The capacities the digest stage's slots must not take: the randomizer stage's and the
`SK.seed`-keyed ones. -/
noncomputable def dExtra [Fintype I] (ω : Pub) (f : DF I) : Finset Z :=
  Finset.univ.image (dRCap rcell ω f) ∪ Finset.univ.image (dPos ω f)

theorem card_dExtra_le [Fintype I] (ω : Pub) (f : DF I) :
    (dExtra rcell ω f).card ≤ Fintype.card I + Fintype.card SkIdx :=
  (Finset.card_union_le _ _).trans (add_le_add (Finset.card_image_le.trans Finset.card_univ.le)
    (Finset.card_image_le.trans Finset.card_univ.le))

/-- **The digest stage's charged labels**, read off the coordinates. -/
abbrev dBX [Fintype I] (y : DSt I J) : Set J :=
  pBX (dCellP dcell msg) dord (dExtra rcell) y

/-- The points whose rates must be distinct: the digest stage's first blocks, the randomizer
stage's (with its `k`-coins) and the `SK.seed`-keyed cells, each with its `k`-value. -/
def dPairs (k : X → Z) (e : PubSlots) (f : DF I) : J ⊕ I ⊕ SkIdx → X × Z :=
  Sum.elim (fun a ↦ (dCellP dcell msg e f a, k (dCellP dcell msg e f a)))
    (Sum.elim (fun b ↦ (rcell b (trunc128 e.2.1) f.2.2, f.1.1 b))
      fun b ↦ (skCell (trunc128 e.2.1) f.2.1 b, k (skCell (trunc128 e.2.1) f.2.1 b)))

/-- **Distinct rates before the digest stage**: of its first blocks, the randomizer stage's and
the `SK.seed`-keyed ones. -/
abbrev DRateInj (x : DSt I J) : Prop :=
  Function.Injective fun j ↦ (x.1.1.1.2 (dPairs rcell dcell msg x.1.1.1.1.2.1 x.1.1.2 x.2 j)).1

variable {rcell dcell msg}

theorem dCellP_injective
    (hdcell : ∀ P, Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1) (e : PubSlots)
    (f : DF I) : Function.Injective (dCellP dcell msg e f) := fun a b h ↦
  congrArg Prod.snd (hdcell (trunc128 e.2.1) (a₁ := (trunc128 (f.1.2.2 (msg a)), a))
    (a₂ := (trunc128 (f.1.2.2 (msg b)), b)) h)

/-- **The pairs are distinct**: distinct cells within each family (`hcell`, `hdcell`, the
`SK.seed`-keyed cells), and no cell in two families (`hrd`, `hsd`, `hsep`). -/
theorem dPairs_injective (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hdcell : ∀ P, Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1)
    (hrd : ∀ b P R a P' R', rcell b P R ≠ dcell a P' R')
    (hsd : ∀ P S b a P' R, skCell P S b ≠ dcell a P' R)
    (hsep : ∀ P S b a R, skCell P S b ≠ rcell a P R) (k : X → Z) (e : PubSlots) (f : DF I) :
    Function.Injective (dPairs rcell dcell msg k e f) := by
  refine Function.Injective.sumElim
    (fun a b h ↦ dCellP_injective hdcell e f (congrArg Prod.fst h))
    (Function.Injective.sumElim (fun a b h ↦ cell_injective_of hcell _ _ (congrArg Prod.fst h))
      (fun a b h ↦ skCell_injective_idx _ _ (congrArg Prod.fst h))
      fun a b h ↦ hsep _ _ b a _ (congrArg Prod.fst h).symm) ?_
  intro a j
  rcases j with b | b
  · exact fun h ↦ hrd b _ _ a _ _ (congrArg Prod.fst h).symm
  · exact fun h ↦ hsd _ _ b a _ _ (congrArg Prod.fst h).symm

variable (rcell dcell msg)

/-! ### The good set and the coordinate facts -/

variable {ι : Type} {β : ι → Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

open scoped Classical in
/-- **The good set** of the digest stage: `rGood`, distinct rates before the stage (`DRateInj`),
and no computation reading a digest path cell (`PReadGood`). Irreducible: its membership does not
unfold to the enumeration of all tables. -/
@[irreducible]
noncomputable def dGood
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Finset (DTab I J) :=
  Finset.univ.filter fun θ ↦ θ.1 ∈ rGood rcell rord Q ∧
    DRateInj rcell dcell msg (dPre rcell rord θ) ∧
      PReadGood (dCellP dcell msg) (qReads Q) (dSplit rcell rord dcell msg dord θ)

theorem mem_dGood
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {θ : DTab I J} :
    θ ∈ dGood rcell rord dcell msg dord Q ↔ θ.1 ∈ rGood rcell rord Q ∧
      DRateInj rcell dcell msg (dPre rcell rord θ) ∧
        PReadGood (dCellP dcell msg) (qReads Q) (dSplit rcell rord dcell msg dord θ) := by
  unfold dGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The coordinate facts**: on the good set, the slot of an uncharged digest label holds the
table's output of the one-block hash with first block `dcell a PK.seed R`, where `R` is the
randomizer coordinate `rCoord` of the label's message. -/
theorem dSplit_transfer
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hdcell : ∀ P, Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1)
    (hrd : ∀ b P R a P' R', rcell b P R ≠ dcell a P' R')
    (hsd : ∀ P S b a P' R, skCell P S b ≠ dcell a P' R)
    (hsep : ∀ P S b a R, skCell P S b ≠ rcell a P R)
    {θ : DTab I J} (hθ : θ ∈ dGood rcell rord dcell msg dord Q) (a : J)
    (ha : a ∉ dBX rcell dcell msg dord (dSplit rcell rord dcell msg dord θ)) :
    (dSplit rcell rord dcell msg dord θ).1.2.2.2 a =
      rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm
          (dcell a θ.1.1.1.publicSeed (rCoord (rSplit rcell rord θ.1).1 (msg a))) +
        θ.1.1.1.keys.1 (capOf θ.1.1.1.keys.2.1 θ.1.1.1.keys.2.2 θ.1.1.1.perm
          (dcell a θ.1.1.1.publicSeed (rCoord (rSplit rcell rord θ.1).1 (msg a)))) := by
  obtain ⟨hθR, hrate, -⟩ := (mem_dGood rcell rord dcell msg dord).mp hθ
  obtain ⟨⟨hinj, -⟩, hcoll, -⟩ := mem_rGood.mp hθR
  have hcoords := rSplit_coords hcell hθR
  obtain ⟨hk, hk', hh⟩ := rSplit_keys_eq rcell rord θ.1 hcell hcoll.1
  have hst := (schemeSplit_transfer θ.1.1 hinj).2.2
  have hks := schemeSplit_keys_snd θ.1.1
  have hk1 : ∀ x, (schemeSplit θ.1.1).1.1.1.2.1 x = θ.1.1.1.keys.2.1 x := fun x ↦ by rw [hks]
  have hk2 : ∀ x, (schemeSplit θ.1.1).1.1.1.2.2 x = θ.1.1.1.keys.2.2 x := fun x ↦ by rw [hks]
  have hπ := rSplit_perm rcell rord θ.1
  have hsl := rSplit_slots rcell rord θ.1
  have hsnd := rSplit_snd rcell rord θ.1
  set yR := rSplit rcell rord θ.1 with hyR
  have hr : Function.Injective fun j ↦
      (yR.1.1.1.2 (dPairs rcell dcell msg yR.1.1.1.1.2.1 yR.1.1.2 (yR.1.2, yR.2) j)).1 := hrate
  have hrD : Function.Injective fun a ↦
      rateOf yR.1.1.1.1.2.1 yR.1.1.1.2 (dCellP dcell msg yR.1.1.2 (yR.1.2, yR.2) a) :=
    fun a b hab ↦ Sum.inl_injective (hr (a₁ := Sum.inl a) (a₂ := Sum.inl b) hab)
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, -, f⟩ := pStages_spec (dCellP dcell msg) dord yR.1.1.1.1
    yR.1.1.1.2 yR.1.1.2 θ.2 (yR.1.2, yR.2)
  obtain ⟨f1, f2, f3, -, f5, f6⟩ := f (dCellP_injective hdcell _ _) hrD
  have hD : dSplit rcell rord dcell msg dord θ =
      (((((h₂, k₂, k'₂), yR.1.1.1.2), yR.1.1.2), cs₂), (yR.1.2, yR.2)) :=
    (dSplit_apply rcell rord dcell msg dord θ).trans hE
  rw [hD] at ha ⊢
  set dc := dCellP dcell msg yR.1.1.2 (yR.1.2, yR.2) with hdc
  set π := yR.1.1.1.2 with hπdef
  set kR := yR.1.1.1.1.2.1 with hkRdef
  set k'R := yR.1.1.1.1.2.2 with hk'Rdef
  have hcapY : ∀ b, pCellH (dCellP dcell msg)
      (((((h₂, k₂, k'₂), π), yR.1.1.2), cs₂), (yR.1.2, yR.2)) b = capOf kR k'R π (dc b) := by
    intro b
    change (π (dc b, cs₂.1 b)).2 + cs₂.2.1 b = _
    rw [f1 b, f2 b]
    rfl
  have hfirst : IsFirst dord (fun b ↦ capOf kR k'R π (dc b)) a := by
    have h1 : IsFirst dord (pCellH (dCellP dcell msg)
        (((((h₂, k₂, k'₂), π), yR.1.1.2), cs₂), (yR.1.2, yR.2))) a :=
      not_not.mp fun h ↦ ha (Or.inl ((mem_pB _ _).mpr h))
    rwa [show pCellH (dCellP dcell msg) (((((h₂, k₂, k'₂), π), yR.1.1.2), cs₂), (yR.1.2, yR.2)) =
      fun b ↦ capOf kR k'R π (dc b) from funext hcapY] at h1
  have hext : capOf kR k'R π (dc a) ∉ dExtra rcell (((h₂, k₂, k'₂), π), yR.1.1.2)
      (yR.1.2, yR.2) := by
    rw [← hcapY a]
    exact fun h ↦ ha (Or.inr h)
  have hRc : ∀ M, pCellH (cellP rcell) yR M ≠ capOf kR k'R π (dc a) := fun M h ↦ hext (by
    rw [← h]
    exact mem_union_image_univ_left _ (dRCap rcell (((h₂, k₂, k'₂), π), yR.1.1.2)
      (yR.1.2, yR.2)) M)
  have hPc : ∀ b, dPos (((h₂, k₂, k'₂), π), yR.1.1.2) (yR.1.2, yR.2) b ≠
      capOf kR k'R π (dc a) := fun b h ↦ hext (by
    rw [← h]
    exact mem_union_image_univ_right _ (dPos (((h₂, k₂, k'₂), π), yR.1.1.2) (yR.1.2, yR.2)) b)
  -- the table's `k` at the digest cell
  have hkc : kR (dc a) = θ.1.1.1.keys.2.1 (dc a) :=
    (hk (dc a) fun M h ↦ hrd M _ _ a _ _ h).trans (hk1 _)
  have hrc : rateOf kR π (dc a) = rateOf θ.1.1.1.keys.2.1 θ.1.1.1.perm (dc a) := by
    unfold rateOf
    rw [hkc, hπ]
  -- the table's `k'` at its rate
  have hk'c : k'R (rateOf kR π (dc a)) = θ.1.1.1.keys.2.2 (rateOf kR π (dc a)) :=
    (hk' (rateOf kR π (dc a)) fun M h ↦
      Sum.inr_ne_inl (hr (a₁ := Sum.inr (Sum.inl M)) (a₂ := Sum.inl a) h)).trans
      (hk2 _)
  have hcap : capOf kR k'R π (dc a) =
      capOf θ.1.1.1.keys.2.1 θ.1.1.1.keys.2.2 θ.1.1.1.perm (dc a) := by
    change (π (dc a, kR (dc a))).2 + k'R (rateOf kR π (dc a)) = _
    rw [hk'c, hrc, hkc, hπ]
    rfl
  -- the hidden capacities read off the coordinates are `schemeSplit`'s
  have hpos : ∀ b, posOf (schemeSplit θ.1.1).1 (schemeSplit θ.1.1).2 b =
      dPos (((h₂, k₂, k'₂), π), yR.1.1.2) (yR.1.2, yR.2) b := by
    intro b
    have hP' : pubParam (schemeSplit θ.1.1).1 = trunc128 yR.1.1.2.2.1 := by
      rw [hsl]
      rfl
    have hS' : (schemeSplit θ.1.1).2.1 = yR.2.1 := by
      rw [hsnd, schemeSplit_snd]
    change capOf (schemeSplit θ.1.1).1.1.1.2.1 (schemeSplit θ.1.1).1.1.1.2.2
        (schemeSplit θ.1.1).1.1.2 (skCell (pubParam (schemeSplit θ.1.1).1)
          (schemeSplit θ.1.1).2.1 b) =
      capOf k₂ k'₂ π (skCell (trunc128 yR.1.1.2.2.1) yR.2.1 b)
    rw [hP', hS', schemeSplit_perm, ← hπ]
    set sk := skCell (trunc128 yR.1.1.2.2.1) yR.2.1 b with hsk
    have e1 : k₂ sk = kR sk := f5 sk fun a' h ↦ hsd _ _ b a' _ _ h.symm
    have e2 : kR sk = (schemeSplit θ.1.1).1.1.1.2.1 sk := hk sk fun M h ↦ hsep _ _ b M _ h.symm
    have e3 : k'₂ (rateOf kR π sk) = k'R (rateOf kR π sk) := f6 (rateOf kR π sk) fun a' h ↦ by
      rw [f1 a'] at h
      exact Sum.inl_ne_inr (hr (a₁ := Sum.inl a') (a₂ := Sum.inr (Sum.inr b)) h)
    have e4 : k'R (rateOf kR π sk) = (schemeSplit θ.1.1).1.1.1.2.2 (rateOf kR π sk) :=
      hk' (rateOf kR π sk) fun M h ↦ Sum.inl_ne_inr (Sum.inr_injective
        (hr (a₁ := Sum.inr (Sum.inl M)) (a₂ := Sum.inr (Sum.inr b)) h))
    change (π (sk, (schemeSplit θ.1.1).1.1.1.2.1 sk)).2 +
        (schemeSplit θ.1.1).1.1.1.2.2 (π (sk, (schemeSplit θ.1.1).1.1.1.2.1 sk)).1 =
      (π (sk, k₂ sk)).2 + k'₂ (π (sk, k₂ sk)).1
    rw [e1]
    change _ = (π (sk, kR sk)).2 + k'₂ (rateOf kR π sk)
    rw [e3, e4]
    unfold rateOf
    rw [e2]
  -- the table's `h` at the capacity
  have hhc : yR.1.1.1.1.1 (capOf kR k'R π (dc a)) = θ.1.1.1.keys.1 (capOf kR k'R π (dc a)) :=
    (hh _ hRc).trans (hst (capOf kR k'R π (dc a)) fun b h ↦ hPc b ((hpos b).symm.trans h))
  have hcT : dc a = dcell a θ.1.1.1.publicSeed (rCoord yR.1 (msg a)) := by
    change dcell a (pubParam yR.1.1) (rCoord yR.1 (msg a)) = _
    rw [hcoords.1]
  change cs₂.2.2 a = _
  rw [f3 a hfirst, hhc, hcap, hrc, hcT]

/-- **On the good set, the challenger's data is a function of the public part.** -/
theorem schemeData_eq_pubData_dSplit
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hdcell : ∀ P, Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1)
    {θ : DTab I J} (hθ : θ ∈ dGood rcell rord dcell msg dord Q) :
    schemeData Q θ.1.1.1 = pubData Q (dSplit rcell rord dcell msg dord θ).1.1 := by
  obtain ⟨hθR, hrate, hread⟩ := (mem_dGood rcell rord dcell msg dord).mp hθ
  rw [schemeData_eq_pubData_rSplit hcell hθR]
  set yR := rSplit rcell rord θ.1 with hyR
  have hr : Function.Injective fun j ↦
      (yR.1.1.1.2 (dPairs rcell dcell msg yR.1.1.1.1.2.1 yR.1.1.2 (yR.1.2, yR.2) j)).1 := hrate
  have hrD : Function.Injective fun a ↦
      rateOf yR.1.1.1.1.2.1 yR.1.1.1.2 (dCellP dcell msg yR.1.1.2 (yR.1.2, yR.2) a) :=
    fun a b hab ↦ Sum.inl_injective (hr (a₁ := Sum.inl a) (a₂ := Sum.inl b) hab)
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, f7, f⟩ := pStages_spec (dCellP dcell msg) dord yR.1.1.1.1
    yR.1.1.1.2 yR.1.1.2 θ.2 (yR.1.2, yR.2)
  obtain ⟨-, -, -, -, f5, f6⟩ := f (dCellP_injective hdcell _ _) hrD
  have hD : dSplit rcell rord dcell msg dord θ =
      (((((h₂, k₂, k'₂), yR.1.1.1.2), yR.1.1.2), cs₂), (yR.1.2, yR.2)) :=
    (dSplit_apply rcell rord dcell msg dord θ).trans hE
  rw [hD] at hread ⊢
  funext i
  change honestEval yR.1.1.1.1 yR.1.1.1.2 (Q i (pubParam yR.1.1) (pubSec yR.1.1)) =
    honestEval (h₂, k₂, k'₂) yR.1.1.1.2 (Q i (pubParam yR.1.1) (pubSec yR.1.1))
  refine honestEval_congr (t := (h₂, k₂, k'₂)) (t' := yR.1.1.1.1) yR.1.1.1.2 _ fun e he ↦ ?_
  have ha := honestEval_answeredBy yR.1.1.1.2 (h₂, k₂, k'₂) _ e he
  cases e with
  | h z v =>
    have hz : ∀ a, pCellH (dCellP dcell msg)
        (((((h₂, k₂, k'₂), yR.1.1.1.2), yR.1.1.2), cs₂), (yR.1.2, yR.2)) a ≠ z := fun a hza ↦
      (hread i a).2.2 (by rw [hza]; exact mem_hCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← f7 z hz]
    exact ha
  | k x v =>
    have hx : ∀ a, pCellK (dCellP dcell msg)
        (((((h₂, k₂, k'₂), yR.1.1.1.2), yR.1.1.2), cs₂), (yR.1.2, yR.2)) a ≠ x := fun a hxa ↦
      (hread i a).1 (by rw [hxa]; exact mem_kCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← f5 x hx]
    exact ha
  | k' x v =>
    have hx : ∀ a, pCellK' (dCellP dcell msg)
        (((((h₂, k₂, k'₂), yR.1.1.1.2), yR.1.1.2), cs₂), (yR.1.2, yR.2)) a ≠ x := fun a hxa ↦
      (hread i a).2.1 (by rw [hxa]; exact mem_k'Cells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← f6 x hx]
    exact ha

/-! ### The bad fraction -/

/-- A `k`-cell is some digest-stage first block under `P` (a named predicate, as `IsCell`). -/
def IsDCell (P : PublicParameter) (x : X) : Prop :=
  ∃ a R, dcell a P R = x

omit [DecidableEq J] in
open scoped Classical in
/-- **The digest stage's first blocks are rarely read**, averaged over the randomizer slots: `2^128`
times the reads of `K` at `dcell a P (trunc128 (slot of msg a))`, summed over the kept data, are at
most `|DF I|` times the number `n` of digest-stage first blocks in `K`. -/
theorem card_mul_sum_dcell_le (P : PublicParameter) (K : Finset X) (n : ℕ)
    (hinj : Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1)
    (hK : (K.filter (IsDCell dcell P)).card ≤ n) :
    2 ^ 128 * ∑ f : DF I, ∑ a, (if dcell a P (trunc128 (f.1.2.2 (msg a))) ∈ K then 1 else 0) ≤
      Fintype.card (DF I) * n := by
  have hfib : ∀ a, ∑ w : X, (if dcell a P (trunc128 w) ∈ K then 1 else 0) =
      2 ^ 960 * ∑ R : Randomizer, (if dcell a P R ∈ K then 1 else 0) := fun a ↦
    sum_comp_eq_mul_sum trunc128 _ card_fiber_trunc128 fun R ↦ if dcell a P R ∈ K then 1 else 0
  have hcount : ∑ a, ∑ R : Randomizer, (if dcell a P R ∈ K then 1 else 0) ≤ n := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    exact (sum_ite_mem_le_card_filter (fun s : Randomizer × J ↦ dcell s.2 P s.1) hinj K
      (IsDCell dcell P) fun s ↦ ⟨s.2, s.1, rfl⟩).trans hK
  have h1 : Fintype.card X *
      ∑ f : DF I, ∑ a, (if dcell a P (trunc128 (f.1.2.2 (msg a))) ∈ K then 1 else 0) ≤
        Fintype.card (DF I) * (2 ^ 960 * n) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    calc ∑ a, Fintype.card X *
          ∑ f : DF I, (if dcell a P (trunc128 (f.1.2.2 (msg a))) ∈ K then 1 else 0)
        ≤ ∑ a, Fintype.card (DF I) * (2 ^ 960 *
            ∑ R : Randomizer, (if dcell a P R ∈ K then 1 else 0)) :=
          Finset.sum_le_sum fun a _ ↦ (card_mul_sum_eval_le
            (fun w ↦ if dcell a P (trunc128 w) ∈ K then 1 else 0) (msg a)).trans_eq
              (congrArg (Fintype.card (DF I) * ·) (hfib a))
      _ = Fintype.card (DF I) * (2 ^ 960 *
            ∑ a, ∑ R : Randomizer, (if dcell a P R ∈ K then 1 else 0)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ Fintype.card (DF I) * (2 ^ 960 * n) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcount)
  have hX : Fintype.card X = 2 ^ 960 * 2 ^ 128 := by
    rw [Quantum.Xmss.Hybrid.R0.card_rate, ← pow_add]
  rw [hX, mul_assoc, mul_left_comm (Fintype.card (DF I))] at h1
  exact Nat.le_of_mul_le_mul_left h1 (by positivity)

open scoped Classical in
/-- **The digest stage's first blocks are rarely read**: at most `qsᵢ / 2^128` of the coordinates,
where `qsᵢ` bounds the reads of `Q i` at digest-stage first blocks. -/
theorem card_mul_sum_readKD_le
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (qs : ι → ℕ) (hdcell : ∀ P, Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsDCell dcell P)).card ≤ qs i) (i : ι) :
    2 ^ 128 * ∑ y, pReadK (dCellP dcell msg) (qReads Q) i y ≤ Fintype.card (DSt I J) * qs i :=
  card_mul_sum_pReadK_le_mul (dCellP dcell msg) (qReads Q) (2 ^ 128) qs (fun i p ↦
    card_mul_sum_dcell_le dcell msg (pubParam p) _ (qs i) (hdcell _)
      (hqs i p.1.1 p.1.2 (pubParam p) (pubSec p))) i

open scoped Classical in
/-- A table outside the randomizer stage's good set. -/
noncomputable def dRBad
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (θ : RTab I) : ℕ :=
  if θ ∈ rGood rcell rord Q then 0 else 1

open scoped Classical in
/-- Coordinates with a bad permutation. -/
noncomputable def dPermBad (G : ℕ) (x : DSt I J) : ℕ :=
  if ¬PermGood x.1.1.1.2 G then 1 else 0

open scoped Classical in
/-- Coordinates with colliding rates before the digest stage. -/
noncomputable def dRateBad (x : DSt I J) : ℕ :=
  if ¬DRateInj rcell dcell msg x then 1 else 0

open scoped Classical in
/-- The tables outside the good set: outside `rGood`, a bad permutation, colliding rates, or a
computation reading a digest path cell. -/
theorem card_sub_card_dGood_le [Fintype ι] (G : ℕ)
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Fintype.card (DTab I J) - (dGood rcell rord dcell msg dord Q).card ≤
      ∑ θ : DTab I J, (dRBad rcell rord Q θ.1 + ((dPermBad G (dPre rcell rord θ) +
        dRateBad rcell dcell msg (dPre rcell rord θ)) +
        ∑ i, (pReadK (dCellP dcell msg) (qReads Q) i (dSplit rcell rord dcell msg dord θ) +
          pReadKH (dCellP dcell msg) G (qReads Q) i (dSplit rcell rord dcell msg dord θ)))) := by
  refine card_sub_card_le_sum (dGood rcell rord dcell msg dord Q) _ fun θ hθ ↦ ?_
  rw [mem_dGood] at hθ
  set y := dSplit rcell rord dcell msg dord θ with hy
  by_cases hR : θ.1 ∈ rGood rcell rord Q
  · by_cases hG : PermGood (dPre rcell rord θ).1.1.1.2 G
    · by_cases hr : DRateInj rcell dcell msg (dPre rcell rord θ)
      · have hread : ¬PReadGood (dCellP dcell msg) (qReads Q) y := fun h ↦ hθ ⟨hR, hr, h⟩
        obtain ⟨i, a, hia⟩ : ∃ i a,
            ¬(pCellK (dCellP dcell msg) y a ∉ kCells (qReads Q i y.1.1) ∧
              pCellK' (dCellP dcell msg) y a ∉ k'Cells (qReads Q i y.1.1) ∧
              pCellH (dCellP dcell msg) y a ∉ hCells (qReads Q i y.1.1)) := by
          by_contra hne
          exact hread fun i a ↦ by_contra fun h ↦ hne ⟨i, a, h⟩
        have hG' : PermGood y.1.1.1.2 G := by
          rw [hy, dSplit_perm]
          exact hG
        have hk : pKHit (dCellP dcell msg) (qReads Q) i a y ≤
            pReadK (dCellP dcell msg) (qReads Q) i y :=
          Finset.single_le_sum (f := fun a' ↦ pKHit (dCellP dcell msg) (qReads Q) i a' y)
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        have hkh : pK'Hit (dCellP dcell msg) G (qReads Q) i a y +
            pHHit (dCellP dcell msg) (qReads Q) i a y ≤
              pReadKH (dCellP dcell msg) G (qReads Q) i y :=
          Finset.single_le_sum (f := fun a' ↦ pK'Hit (dCellP dcell msg) G (qReads Q) i a' y +
            pHHit (dCellP dcell msg) (qReads Q) i a' y) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ a)
        have h1 : 1 ≤ pReadK (dCellP dcell msg) (qReads Q) i y +
            pReadKH (dCellP dcell msg) G (qReads Q) i y := by
          by_cases m1 : pCellK (dCellP dcell msg) y a ∈ kCells (qReads Q i y.1.1)
          · have : pKHit (dCellP dcell msg) (qReads Q) i a y = 1 := ite_eq_left m1
            omega
          · by_cases m2 : pCellK' (dCellP dcell msg) y a ∈ k'Cells (qReads Q i y.1.1)
            · have : pK'Hit (dCellP dcell msg) G (qReads Q) i a y = 1 := ite_eq_left ⟨hG', m2⟩
              omega
            · have m3 : pCellH (dCellP dcell msg) y a ∈ hCells (qReads Q i y.1.1) :=
                by_contra fun m3 ↦ hia ⟨m1, m2, m3⟩
              have : pHHit (dCellP dcell msg) (qReads Q) i a y = 1 := ite_eq_left m3
              omega
        have h2 : pReadK (dCellP dcell msg) (qReads Q) i y +
            pReadKH (dCellP dcell msg) G (qReads Q) i y ≤
              ∑ i', (pReadK (dCellP dcell msg) (qReads Q) i' y +
                pReadKH (dCellP dcell msg) G (qReads Q) i' y) :=
          Finset.single_le_sum (f := fun i' ↦ pReadK (dCellP dcell msg) (qReads Q) i' y +
            pReadKH (dCellP dcell msg) G (qReads Q) i' y) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ i)
        omega
      · have : dRateBad rcell dcell msg (dPre rcell rord θ) = 1 := ite_eq_left hr
        omega
    · have : dPermBad G (dPre rcell rord θ) = 1 := ite_eq_left hG
      omega
  · have : dRBad rcell rord Q θ.1 = 1 := ite_eq_right hR
    omega

open scoped Classical in
/-- **Rates collide before the digest stage for at most `K² / |X|` of the coordinates**
(`K = |J| + |I| + |A|`, averaged over `π`). -/
theorem card_mul_sum_dRateBad_le
    (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hdcell : ∀ P, Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1)
    (hrd : ∀ b P R a P' R', rcell b P R ≠ dcell a P' R')
    (hsd : ∀ P S b a P' R, skCell P S b ≠ dcell a P' R)
    (hsep : ∀ P S b a R, skCell P S b ≠ rcell a P R) :
    Fintype.card X * ∑ x, dRateBad rcell dcell msg x ≤ Fintype.card (DSt I J) *
      ((Fintype.card J + (Fintype.card I + Fintype.card SkIdx)) *
        (Fintype.card J + (Fintype.card I + Fintype.card SkIdx))) := by
  have hK : Fintype.card (J ⊕ I ⊕ SkIdx) = Fintype.card J + (Fintype.card I + Fintype.card SkIdx) :=
    by rw [Fintype.card_sum, Fintype.card_sum]
  rw [← hK]
  exact card_mul_sum_equiv_prod_le dCoordPi _ _ (dRateBad rcell dcell msg) fun r ↦
    card_mul_sum_not_injective_rate_le (dPairs rcell dcell msg r.1.2.1 r.2.1 r.2.2.2)
      (dPairs_injective hcell hdcell hrd hsd hsep _ _ _)

open scoped Classical in
/-- **Bad permutations**: their fraction of the coordinates. -/
theorem card_mul_sum_dPermBad_le (G : ℕ) :
    Fintype.card (Equiv.Perm (X × Z)) * ∑ x : DSt I J, dPermBad G x ≤ Fintype.card (DSt I J) *
      (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card :=
  card_mul_sum_equiv_prod_le dCoordPi _ _ (dPermBad G) fun _ ↦
    Nat.mul_le_mul_left _ (Finset.card_filter _ _).ge

open scoped Classical in
/-- **The bad fraction of the digest stage**: the fraction of tables outside `dGood` is at most
the fraction outside `rGood`, plus the fraction of permutations with a rate count above `G`, plus
the rate collisions `K² / |X|` (`K = |J| + |I| + |A|`, `A = SkIdx`, averaged over `π`), plus per
computation `qsᵢ / 2^128 + |J| (G + 1) qᵢ / |Z|`, where `qᵢ` bounds the reads of `Q i` and `qsᵢ` its
reads at digest-stage first blocks. -/
theorem dGood_frac_le [Fintype ι] (G : ℕ)
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qs : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsDCell dcell P)).card ≤ qs i)
    (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hdcell : ∀ P, Function.Injective fun s : Randomizer × J ↦ dcell s.2 P s.1)
    (hrd : ∀ b P R a P' R', rcell b P R ≠ dcell a P' R')
    (hsd : ∀ P S b a P' R, skCell P S b ≠ dcell a P' R)
    (hsep : ∀ P S b a R, skCell P S b ≠ rcell a P R) :
    (Fintype.card (DTab I J) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (DTab I J) - (dGood rcell rord dcell msg dord Q).card : ℕ) : ℝ≥0∞) ≤
      (Fintype.card (RTab I) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (RTab I) - (rGood rcell rord Q).card : ℕ) : ℝ≥0∞) +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          (((Fintype.card J + (Fintype.card I + Fintype.card SkIdx)) *
            (Fintype.card J + (Fintype.card I + Fintype.card SkIdx)) : ℕ) : ℝ≥0∞) /
              Fintype.card X) +
        ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 128 + Fintype.card J * (G + 1) * q i / Fintype.card Z) := by
  refine inv_mul_le_of_parts Fintype.card_ne_zero
    ((card_sub_card_dGood_le rcell rord dcell msg dord G Q).trans_eq
      (sum_add_sum_eq _ _ _ _)) ?_ ?_ ?_ ?_
  · have hs : ∑ t, dRBad rcell rord Q t = Fintype.card (RTab I) - (rGood rcell rord Q).card :=
      sum_ite_mem_zero_one_eq (rGood rcell rord Q)
    rw [sum_fst_eq (dRBad rcell rord Q), hs]
    exact (natCast_smul_eq_card_mul _).le
  · have hP := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le (dPre rcell rord) (dPermBad (I := I) (J := J) G) _ _
        (card_mul_sum_dPermBad_le (I := I) (J := J) G))
    have hX := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le (dPre rcell rord) (dRateBad rcell dcell msg) _ _
        (card_mul_sum_dRateBad_le rcell dcell msg hcell hdcell hrd hsd hsep))
    calc ((∑ θ : DTab I J, (dPermBad G (dPre rcell rord θ) +
          dRateBad rcell dcell msg (dPre rcell rord θ)) : ℕ) : ℝ≥0∞)
        = ((∑ θ : DTab I J, dPermBad G (dPre rcell rord θ) : ℕ) : ℝ≥0∞) +
            ((∑ θ : DTab I J, dRateBad rcell dcell msg (dPre rcell rord θ) : ℕ) : ℝ≥0∞) := by
          rw [← Nat.cast_add, ← Finset.sum_add_distrib]
      _ ≤ _ := (add_le_add hP hX).trans_eq (mul_add _ _ _).symm
  · intro i
    have h := natCast_le_mul_div_of_mul_le (by positivity : (2 : ℕ) ^ 128 ≠ 0)
      (card_mul_sum_equiv_le (dSplit rcell rord dcell msg dord)
        (pReadK (dCellP dcell msg) (qReads Q) i) _ _
        (card_mul_sum_readKD_le dcell msg Q qs hdcell hqs i))
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  · intro i
    have h := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le (dSplit rcell rord dcell msg dord)
        (pReadKH (dCellP dcell msg) G (qReads Q) i) _ _
        (card_mul_sum_pReadKH_le (dCellP dcell msg) G (qReads Q) q
          (fun i p ↦ hq i p.1.1 p.1.2 (pubParam p) (pubSec p)) i))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    exact h

/-- **A digest label is rarely charged**: over the tables, `a` is charged for at most a
`(|J| + |I| + |A|) / |Z|` fraction (`A = SkIdx`, its `k'`-slot resampled): the averaged charge of
Mismatch's non-first labels. -/
theorem card_mul_sum_dBXInd_le (a : J) :
    Fintype.card Z * ∑ θ : DTab I J, pBXInd (dCellP dcell msg) dord (dExtra rcell) a
        (dSplit rcell rord dcell msg dord θ) ≤
      Fintype.card (DTab I J) * (Fintype.card J + (Fintype.card I + Fintype.card SkIdx)) :=
  card_mul_sum_equiv_le (dSplit rcell rord dcell msg dord)
    (pBXInd (dCellP dcell msg) dord (dExtra rcell) a) _ _
    (card_mul_sum_pBXInd_le (dCellP dcell msg) dord (dExtra rcell) _
      (card_dExtra_le rcell) a)

end dstage

/-! ## The digest stage: the messages' `H_msg` calls -/

section msg

/-- **The digest stage's labels**: the root, the message and the call. -/
abbrev DLab : Type := Digest × Message × DigestCall

/-- The first (only) block of `H_msg` call `i` on `M` under the root `root`. -/
def dLabCell (a : DLab) (P : PublicParameter) (R : Randomizer) : X :=
  hmsgCell R P a.1 a.2.1 a.2.2

/-- The message of a digest label. -/
def dLabMsg (a : DLab) : Message :=
  a.2.1

/-- A rank of the digest labels. -/
noncomputable def dLabOrd : DLab ↪ ℕ :=
  (Fintype.equivFin DLab).toEmbedding.trans Fin.valEmbedding

theorem length_messageDigestInput_lt (R : Randomizer) (P : PublicParameter) (root : Digest)
    (M : Message) (i : DigestCall) : (messageDigestInput R P root M i).length < 136 := by
  rw [length_messageDigestInput]
  norm_num

/-- **The digest cells are distinct**: a first block names its randomizer and its label. -/
theorem dLabCell_injective (P : PublicParameter) :
    Function.Injective fun s : Randomizer × DLab ↦ dLabCell s.2 P s.1 := by
  rintro ⟨R, root, M, i⟩ ⟨R', root', M', i'⟩ h
  obtain ⟨h1, -, h3, h4, h5⟩ := messageDigestInput_injective
    (eq_of_firstCell_eq (length_messageDigestInput_lt R P root M i)
      (length_messageDigestInput_lt R' P root' M' i') h)
  rw [h1, h3, h4, h5]

/-- **The digest cells are not randomizer cells**: one-block inputs of other lengths. -/
theorem rCell_ne_dLabCell (b : Message) (P : PublicParameter) (R : HashOutput) (a : DLab)
    (P' : PublicParameter) (R' : Randomizer) : rCell b P R ≠ dLabCell a P' R' := by
  intro h
  have hl := congrArg List.length (eq_of_firstCell_eq (length_prfMessageInput_lt R P b)
    (length_messageDigestInput_lt R' P' a.1 a.2.1 a.2.2) h)
  have h93 := length_prfMessageInput R P b
  have h84 := length_messageDigestInput R' P' a.1 a.2.1 a.2.2
  omega

/-- **The digest cells are not `SK.seed`-keyed cells**: one-block inputs of other lengths. -/
theorem skCell_ne_dLabCell (P : PublicParameter) (S : MasterSeed) (b : SkIdx) (a : DLab)
    (P' : PublicParameter) (R : Randomizer) : skCell P S b ≠ dLabCell a P' R := by
  intro h
  have hl := congrArg List.length (eq_of_firstCell_eq (length_skInput_lt P S b)
    (length_messageDigestInput_lt R P' a.1 a.2.1 a.2.2) h)
  rw [length_messageDigestInput] at hl
  rcases b with _ | _ | d <;>
    simp only [skInput, length_keyDerivationInput, length_prfInput] at hl <;> omega

variable {ι : Type} {β : ι → Type}

/-- **The digests of the first labels are the coordinates**: on the good set of the digest stage,
for a first message `M` of the randomizer stage and an uncharged label `(L.root, M, i)`, the output
of `H_msg` call `i` on `M` is its coordinate `dCoord`. -/
theorem digest_eq_dCoord
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {θ : DTab Message DLab} (hθ : θ ∈ dGood rCell rOrd dLabCell dLabMsg dLabOrd Q) (M : Message)
    (i : DigestCall) (hM : M ∉ rB rCell rOrd θ.1.1.1)
    (ha : (θ.1.1.1.root, M, i) ∉
      dBX rCell dLabCell dLabMsg dLabOrd (dSplit rCell rOrd dLabCell dLabMsg dLabOrd θ)) :
    θ.1.1.1.digestOutput M i =
      dCoord (dSplit rCell rOrd dLabCell dLabMsg dLabOrd θ) (θ.1.1.1.root, M, i) := by
  have hθR := ((mem_dGood rCell rOrd dLabCell dLabMsg dLabOrd).mp hθ).1
  have hR := randomizer_eq_rCoord hθR M hM
  have ht := dSplit_transfer rCell rOrd dLabCell dLabMsg dLabOrd rCell_injective
    dLabCell_injective rCell_ne_dLabCell skCell_ne_dLabCell skCell_ne_rCell hθ
    (θ.1.1.1.root, M, i) ha
  rw [dCoord, outSplit_fst, ht, HonestTable.digestOutput, hR,
    hash_of_lt _ _ (length_messageDigestInput_lt _ _ _ _ _)]
  rfl

/-! ### At Keccak's sizes -/

set_option exponentiation.threshold 4096 in
theorem card_dLab : Fintype.card DLab = 2 ^ 385 := by
  simp only [DLab, Fintype.card_prod, Fintype.card_fin, Quantum.Xmss.Hybrid.R0.card_bitVec_eq]
  norm_num [HashSig.digestBits, digestCallCount]

set_option exponentiation.threshold 4096 in
theorem card_dCharge_le :
    Fintype.card DLab + (Fintype.card Message + Fintype.card SkIdx) ≤ 2 ^ 386 := by
  have h := card_skIdx_le
  rw [card_dLab, card_message]
  calc 2 ^ 385 + (2 ^ 256 + Fintype.card SkIdx) ≤ 2 ^ 385 + (2 ^ 256 + 2 ^ 44) :=
        Nat.add_le_add_left (Nat.add_le_add_left h _) _
    _ ≤ 2 ^ 386 := by norm_num

set_option exponentiation.threshold 4096 in
/-- **The rate collisions at Keccak's sizes**: `K² / |X| ≤ 2^-316`. -/
theorem dRateTerm_le_keccak :
    (((Fintype.card DLab + (Fintype.card Message + Fintype.card SkIdx)) *
        (Fintype.card DLab + (Fintype.card Message + Fintype.card SkIdx)) : ℕ) : ℝ≥0∞) /
          Fintype.card X ≤ ENNReal.ofReal (1 / 2 ^ 316) := by
  have hK := Nat.mul_le_mul card_dCharge_le card_dCharge_le
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr hK) _).trans ?_
  rw [Quantum.Xmss.Hybrid.R0.card_rate,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The read terms at Keccak's sizes** (`G = 18`): `|J| 19 q / |Z| ≤ q / 2^122`. -/
theorem dReadKHTerm_le_keccak (q : ℕ) :
    (Fintype.card DLab : ℝ≥0∞) * ((18 : ℕ) + 1) * q / Fintype.card Z ≤
      ENNReal.ofReal (q / 2 ^ 122) := by
  have h : (Fintype.card DLab : ℝ≥0∞) * ((18 : ℕ) + 1) * q =
      ((2 ^ 385 * 19 * q : ℕ) : ℝ≥0∞) := by
    rw [card_dLab]
    push_cast
    ring
  have hn : 2 ^ 385 * 19 * q * 2 ^ 122 ≤ q * 2 ^ 512 := by
    calc 2 ^ 385 * 19 * q * 2 ^ 122 = q * (2 ^ 385 * 19 * 2 ^ 122) := by ring
      _ ≤ q * 2 ^ 512 := Nat.mul_le_mul_left q (by norm_num)
  rw [h, Quantum.Xmss.Hybrid.R0.card_cap,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hn

open scoped Classical in
/-- **The bad fraction of the digest stage at Keccak's sizes** (`G = 18`): the randomizer stage's
(`rGood_frac_le_keccak`, with `qrᵢ` the reads at randomizer cells), the bad permutations, `2^-316`
for the rate collisions, and per computation `qdᵢ / 2^128 + qᵢ / 2^122` (`qdᵢ` the reads at digest
cells). -/
theorem dGood_frac_le_keccak [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qr qd : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqr : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsCell rCell P)).card ≤ qr i)
    (hqd : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsDCell dLabCell P)).card ≤ qd i) :
    (Fintype.card (DTab Message DLab) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (DTab Message DLab) -
          (dGood rCell rOrd dLabCell dLabMsg dLabOrd Q).card : ℕ) : ℝ≥0∞) ≤
      (((Fintype.card Tab : ℝ≥0∞)⁻¹ *
            ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        ENNReal.ofReal (1 / 2 ^ 207) +
        ∑ i, ((qr i : ℝ≥0∞) / 2 ^ 256 + ENNReal.ofReal (q i / 2 ^ 251))) +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) + ENNReal.ofReal (1 / 2 ^ 316)) +
        ∑ i, ((qd i : ℝ≥0∞) / 2 ^ 128 + ENNReal.ofReal (q i / 2 ^ 122)) :=
  (dGood_frac_le rCell rOrd dLabCell dLabMsg dLabOrd 18 Q q qd hq hqd rCell_injective
    dLabCell_injective rCell_ne_dLabCell skCell_ne_dLabCell skCell_ne_rCell).trans
    (add_le_add (add_le_add (rGood_frac_le_keccak Q q qr hq hqr)
      (add_le_add le_rfl dRateTerm_le_keccak))
      (Finset.sum_le_sum fun i _ ↦ add_le_add le_rfl (dReadKHTerm_le_keccak (q i))))

set_option exponentiation.threshold 4096 in
/-- **A digest label is charged for at most `2^-126` of the tables**: Mismatch's non-first charge
at Keccak's sizes. -/
theorem dBXInd_frac_le_keccak (a : DLab) :
    (Fintype.card (DTab Message DLab) : ℝ≥0∞)⁻¹ *
        ((∑ θ : DTab Message DLab, pBXInd (dCellP dLabCell dLabMsg) dLabOrd (dExtra rCell) a
          (dSplit rCell rOrd dLabCell dLabMsg dLabOrd θ) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 2 ^ 126) := by
  have h := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
    (card_mul_sum_dBXInd_le rCell rOrd dLabCell dLabMsg dLabOrd a)
  have hN : (Fintype.card (DTab Message DLab) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_le_mul' le_rfl h).trans ?_
  rw [ENNReal.inv_mul_cancel_left hN (ENNReal.natCast_ne_top _)]
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr card_dCharge_le) _).trans ?_
  rw [Quantum.Xmss.Hybrid.R0.card_cap,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

end msg

end Quantum.Sphincs.Hybrid

end
