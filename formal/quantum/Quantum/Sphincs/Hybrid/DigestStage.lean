module

public import Quantum.Sphincs.Hybrid.RStage
public import Quantum.Sphincs.Hybrid.View

@[expose] public section

/-!
# The digest stage: the counts, and the coordinates before it

leanSPHINCS's message digest is two one-block hashes `H_msg(R, PK.seed, PK.root, M, i)`
(`messageDigestInput`, 84 bytes, `i : DigestCall`) whose randomizer `R = R(M)` is the hidden
`PRF_msg` value the randomizer stage (`Quantum.Sphincs.Hybrid.RStage`) moved into the `h`-slot of
`M`. The digest stage moves these paths' values into slots with the path stages (`pStages`). Its
first blocks are keyed by `PK.root`, so it runs where `PK.root` is a hidden value the stage keeps:
after Reparam's `fwd` (`Quantum.Sphincs.Assembly.ReparamFull`'s `dLast`). Its labels are therefore
the true root's calls `(M, i)` only (`DLab`, `2^257` labels). Here: the path stages' counts over
abstract kept data, the coordinates before the stage, and the labels.

## The charged labels and the path stages' counts, over abstract kept data

* `pBX c ord extra`: a label is charged when a label of smaller rank or a capacity of `extra` (data
  the stage keeps) sits at its capacity; `card_mul_sum_pBXInd_le`: at most `(|J| + m) / |Z|` of the
  coordinates, `m` bounding `extra`.
* `card_mul_sum_pReadK_le_mul`: `card_mul_sum_pReadK_le` with a factor on the reads summed over `F`.
* `pStages_keep`: the path stages keep `π`, `E` and `F`.

## The coordinates before the digest stage

* `dPre : DTab I J ≃ DSt I J`: `rSplit` with the digest stage's coin slots carried along.
* **The good set** `dGood`: `rGood`, and distinct rates of the randomizer stage's and the
  `SK.seed`-keyed first blocks (`RSRateInj`); `dGood_frac_le`: `rGood`'s fraction plus
  `(|I| + |A|)² / |X|`.

## The labels

* `DLab = Message × DigestCall`, `dLabCell (M, i) P root R = hmsgCell R P root M i`, distinct
  (`dLabCell_injective`) and apart from the randomizer and `SK.seed` cells.
* At Keccak's sizes: `dGood_frac_le_keccak` (`rGood_frac_le_keccak`'s terms and `2^-574`), and
  `dBXInd_frac_le_keccak` (a label is charged for at most `2^-254` of the coordinates when `extra`
  has at most `|Msg| + |A|` cells).
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

/-- **The coordinates before the digest stage**: `rSplit`, with the digest stage's coin slots
carried along (the digest stage itself runs after Reparam: `Quantum.Sphincs.Assembly.ReparamFull`,
`dLast`). -/
noncomputable def dPre : DTab I J ≃ DSt I J :=
  ((rSplit rcell rord).prodCongr (Equiv.refl (CoinSlots J))).trans reorderD

theorem dPre_apply (θ : DTab I J) :
    dPre rcell rord θ = ((((rSplit rcell rord θ.1).1.1.1, (rSplit rcell rord θ.1).1.1.2), θ.2),
      ((rSplit rcell rord θ.1).1.2, (rSplit rcell rord θ.1).2)) :=
  rfl

/-- The points whose rates must be distinct: the randomizer stage's first blocks (with its
`k`-coins) and the `SK.seed`-keyed cells (with their `k`-values). -/
def rsPairs (k : X → Z) (e : PubSlots) (f : DF I) : I ⊕ SkIdx → X × Z :=
  Sum.elim (fun b ↦ (rcell b (trunc128 e.2.1) f.2.2, f.1.1 b))
    fun b ↦ (skCell (trunc128 e.2.1) f.2.1 b, k (skCell (trunc128 e.2.1) f.2.1 b))

/-- **Distinct rates of the randomizer stage's and the `SK.seed`-keyed first blocks.** -/
abbrev RSRateInj (x : DSt I J) : Prop :=
  Function.Injective fun j ↦ (x.1.1.1.2 (rsPairs rcell x.1.1.1.1.2.1 x.1.1.2 x.2 j)).1

variable {rcell} in
/-- **The pairs are distinct**: distinct cells within each family, and no cell in both. -/
theorem rsPairs_injective
    (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hsep : ∀ P S b a R, skCell P S b ≠ rcell a P R) (k : X → Z) (e : PubSlots) (f : DF I) :
    Function.Injective (rsPairs rcell k e f) :=
  Function.Injective.sumElim (fun _ _ h ↦ cell_injective_of hcell _ _ (congrArg Prod.fst h))
    (fun _ _ h ↦ skCell_injective_idx _ _ (congrArg Prod.fst h))
    fun a b h ↦ hsep _ _ b a _ (congrArg Prod.fst h).symm

/-! ### The good set and its bad fraction -/

variable {ι : Type} {β : ι → Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

open scoped Classical in
/-- **The good set before the digest stage**: `rGood`, and distinct rates of the randomizer
stage's and the `SK.seed`-keyed first blocks (`RSRateInj`). Irreducible: its membership does not
unfold to the enumeration of all tables. -/
@[irreducible]
noncomputable def dGood
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Finset (DTab I J) :=
  Finset.univ.filter fun θ ↦ θ.1 ∈ rGood rcell rord Q ∧ RSRateInj rcell (dPre rcell rord θ)

theorem mem_dGood
    {Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)}
    {θ : DTab I J} :
    θ ∈ dGood rcell rord Q ↔ θ.1 ∈ rGood rcell rord Q ∧ RSRateInj rcell (dPre rcell rord θ) := by
  unfold dGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open scoped Classical in
/-- A table outside the randomizer stage's good set. -/
noncomputable def dRBad
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (θ : RTab I) : ℕ :=
  if θ ∈ rGood rcell rord Q then 0 else 1

open scoped Classical in
/-- Coordinates with colliding rates. -/
noncomputable def dRateBad (x : DSt I J) : ℕ :=
  if ¬RSRateInj rcell x then 1 else 0

open scoped Classical in
/-- The tables outside the good set: outside `rGood`, or colliding rates. -/
theorem card_sub_card_dGood_le
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i)) :
    Fintype.card (DTab I J) - (dGood (J := J) rcell rord Q).card ≤
      ∑ θ : DTab I J, (dRBad rcell rord Q θ.1 + dRateBad rcell (dPre rcell rord θ)) := by
  refine card_sub_card_le_sum (dGood rcell rord Q) _ fun θ hθ ↦ ?_
  rw [mem_dGood] at hθ
  by_cases hR : θ.1 ∈ rGood rcell rord Q
  · have : dRateBad rcell (dPre rcell rord θ) = 1 := ite_eq_left fun h ↦ hθ ⟨hR, h⟩
    omega
  · have : dRBad rcell rord Q θ.1 = 1 := ite_eq_right hR
    omega

open scoped Classical in
/-- **Rates collide for at most `K² / |X|` of the coordinates** (`K = |I| + |A|`, averaged over
`π`). -/
theorem card_mul_sum_dRateBad_le
    (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hsep : ∀ P S b a R, skCell P S b ≠ rcell a P R) :
    Fintype.card X * ∑ x : DSt I J, dRateBad rcell x ≤ Fintype.card (DSt I J) *
      ((Fintype.card I + Fintype.card SkIdx) * (Fintype.card I + Fintype.card SkIdx)) := by
  have hK : Fintype.card (I ⊕ SkIdx) = Fintype.card I + Fintype.card SkIdx := Fintype.card_sum
  rw [← hK]
  exact card_mul_sum_equiv_prod_le dCoordPi _ _ (dRateBad rcell) fun r ↦
    card_mul_sum_not_injective_rate_le (rsPairs rcell r.1.2.1 r.2.1 r.2.2.2)
      (rsPairs_injective hcell hsep _ _ _)

open scoped Classical in
/-- **The bad fraction before the digest stage**: the fraction of tables outside `dGood` is at
most the fraction outside `rGood`, plus the rate collisions `K² / |X|` (`K = |I| + |A|`,
`A = SkIdx`, averaged over `π`). -/
theorem dGood_frac_le
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (hcell : ∀ P, Function.Injective fun s : HashOutput × I ↦ rcell s.2 P s.1)
    (hsep : ∀ P S b a R, skCell P S b ≠ rcell a P R) :
    (Fintype.card (DTab I J) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (DTab I J) - (dGood (J := J) rcell rord Q).card : ℕ) : ℝ≥0∞) ≤
      (Fintype.card (RTab I) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (RTab I) - (rGood rcell rord Q).card : ℕ) : ℝ≥0∞) +
        (((Fintype.card I + Fintype.card SkIdx) * (Fintype.card I + Fintype.card SkIdx) : ℕ) :
          ℝ≥0∞) / Fintype.card X := by
  have hN : (Fintype.card (DTab I J) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hs : ∑ t, dRBad rcell rord Q t = Fintype.card (RTab I) - (rGood rcell rord Q).card :=
    sum_ite_mem_zero_one_eq (rGood rcell rord Q)
  have h1 : ((∑ θ : DTab I J, dRBad rcell rord Q θ.1 : ℕ) : ℝ≥0∞) ≤
      Fintype.card (DTab I J) * ((Fintype.card (RTab I) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (RTab I) - (rGood rcell rord Q).card : ℕ) : ℝ≥0∞)) := by
    rw [sum_fst_eq (dRBad rcell rord Q), hs]
    exact (natCast_smul_eq_card_mul _).le
  have h2 := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
    (card_mul_sum_equiv_le (dPre rcell rord) (dRateBad rcell (I := I) (J := J)) _ _
      (card_mul_sum_dRateBad_le rcell hcell hsep))
  have h3 : ((Fintype.card (DTab I J) - (dGood (J := J) rcell rord Q).card : ℕ) : ℝ≥0∞) ≤
      Fintype.card (DTab I J) * ((Fintype.card (RTab I) : ℝ≥0∞)⁻¹ *
          ((Fintype.card (RTab I) - (rGood rcell rord Q).card : ℕ) : ℝ≥0∞) +
        (((Fintype.card I + Fintype.card SkIdx) * (Fintype.card I + Fintype.card SkIdx) : ℕ) :
          ℝ≥0∞) / Fintype.card X) := by
    calc ((Fintype.card (DTab I J) - (dGood (J := J) rcell rord Q).card : ℕ) : ℝ≥0∞)
        ≤ ((∑ θ : DTab I J, (dRBad rcell rord Q θ.1 + dRateBad rcell (dPre rcell rord θ)) :
            ℕ) : ℝ≥0∞) := Nat.cast_le.mpr (card_sub_card_dGood_le rcell rord Q)
      _ = ((∑ θ : DTab I J, dRBad rcell rord Q θ.1 : ℕ) : ℝ≥0∞) +
            ((∑ θ : DTab I J, dRateBad rcell (dPre rcell rord θ) : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_add_distrib, Nat.cast_add]
      _ ≤ _ := (add_le_add h1 h2).trans_eq (mul_add _ _ _).symm
  calc (Fintype.card (DTab I J) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (DTab I J) - (dGood rcell rord Q).card : ℕ) : ℝ≥0∞)
      ≤ (Fintype.card (DTab I J) : ℝ≥0∞)⁻¹ * (Fintype.card (DTab I J) * _) :=
        mul_le_mul' le_rfl h3
    _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hN (ENNReal.natCast_ne_top _), one_mul]

end dstage

/-! ## The digest stage's labels: the messages' `H_msg` calls -/

section msg

/-- **The digest stage's labels**: the message and the call. The root is not a label: the digest
stage runs where `PK.root` is a hidden value it keeps. -/
abbrev DLab : Type := Message × DigestCall

/-- The first (only) block of `H_msg` call `i` on `M` under the root `root`, at the randomizer
`R`. -/
def dLabCell (a : DLab) (P : PublicParameter) (root : Digest) (R : Randomizer) : X :=
  hmsgCell R P root a.1 a.2

/-- A rank of the digest labels. -/
noncomputable def dLabOrd : DLab ↪ ℕ :=
  (Fintype.equivFin DLab).toEmbedding.trans Fin.valEmbedding

theorem length_messageDigestInput_lt (R : Randomizer) (P : PublicParameter) (root : Digest)
    (M : Message) (i : DigestCall) : (messageDigestInput R P root M i).length < 136 := by
  rw [length_messageDigestInput]
  norm_num

/-- **The digest cells are distinct**: a first block names its randomizer and its label. -/
theorem dLabCell_injective (P : PublicParameter) (root : Digest) :
    Function.Injective fun s : Randomizer × DLab ↦ dLabCell s.2 P root s.1 := by
  rintro ⟨R, M, i⟩ ⟨R', M', i'⟩ h
  obtain ⟨h1, -, -, h4, h5⟩ := messageDigestInput_injective
    (eq_of_firstCell_eq (length_messageDigestInput_lt R P root M i)
      (length_messageDigestInput_lt R' P root M' i') h)
  rw [h1, h4, h5]

/-- **The digest cells are not randomizer cells**: one-block inputs of other lengths. -/
theorem rCell_ne_dLabCell (b : Message) (P : PublicParameter) (R : HashOutput) (a : DLab)
    (P' : PublicParameter) (root : Digest) (R' : Randomizer) :
    rCell b P R ≠ dLabCell a P' root R' := by
  intro h
  have hl := congrArg List.length (eq_of_firstCell_eq (length_prfMessageInput_lt R P b)
    (length_messageDigestInput_lt R' P' root a.1 a.2) h)
  have h93 := length_prfMessageInput R P b
  have h84 := length_messageDigestInput R' P' root a.1 a.2
  omega

/-- **The digest cells are not `SK.seed`-keyed cells**: one-block inputs of other lengths. -/
theorem skCell_ne_dLabCell (P : PublicParameter) (S : MasterSeed) (b : SkIdx) (a : DLab)
    (P' : PublicParameter) (root : Digest) (R : Randomizer) :
    skCell P S b ≠ dLabCell a P' root R := by
  intro h
  have hl := congrArg List.length (eq_of_firstCell_eq (length_skInput_lt P S b)
    (length_messageDigestInput_lt R P' root a.1 a.2) h)
  rw [length_messageDigestInput] at hl
  rcases b with _ | _ | d <;>
    simp only [skInput, length_keyDerivationInput, length_prfInput] at hl <;> omega

/-! ### At Keccak's sizes -/

set_option exponentiation.threshold 4096 in
theorem card_dLab : Fintype.card DLab = 2 ^ 257 := by
  simp only [DLab, Fintype.card_prod, Fintype.card_fin, Quantum.Xmss.Hybrid.R0.card_bitVec_eq]
  norm_num [digestCallCount]

set_option exponentiation.threshold 4096 in
/-- **The rate collisions at Keccak's sizes**: `(|Msg| + |A|)² / |X| ≤ 2^-574`. -/
theorem rsRateTerm_le_keccak :
    (((Fintype.card Message + Fintype.card SkIdx) * (Fintype.card Message + Fintype.card SkIdx) :
        ℕ) : ℝ≥0∞) / Fintype.card X ≤ ENNReal.ofReal (1 / 2 ^ 574) := by
  have hK : Fintype.card Message + Fintype.card SkIdx ≤ 2 ^ 257 := by
    rw [card_message]
    have := card_skIdx_le
    omega
  refine (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul hK hK)) _).trans ?_
  rw [Quantum.Xmss.Hybrid.R0.card_rate,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

variable {ι : Type} {β : ι → Type}

open scoped Classical in
/-- **The bad fraction before the digest stage at Keccak's sizes** (`G = 18`): the randomizer
stage's (`rGood_frac_le_keccak`, with `qrᵢ` the reads at randomizer cells) and `2^-574` for the
rate collisions. -/
theorem dGood_frac_le_keccak [Fintype ι]
    (Q : ∀ i, PublicParameter → (KeygenDomain → HashOutput) → OracleComp SchemeHashSpec (β i))
    (q qr : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqr : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : KeygenDomain → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter (IsCell rCell P)).card ≤ qr i) :
    (Fintype.card (DTab Message DLab) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (DTab Message DLab) - (dGood (J := DLab) rCell rOrd Q).card : ℕ) :
          ℝ≥0∞) ≤
      (((Fintype.card Tab : ℝ≥0∞)⁻¹ *
            ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        ENNReal.ofReal (1 / 2 ^ 207) +
        ∑ i, ((qr i : ℝ≥0∞) / 2 ^ 256 + ENNReal.ofReal (q i / 2 ^ 251))) +
        ENNReal.ofReal (1 / 2 ^ 574) :=
  (dGood_frac_le rCell rOrd Q rCell_injective skCell_ne_rCell).trans
    (add_le_add (rGood_frac_le_keccak Q q qr hq hqr) rsRateTerm_le_keccak)

set_option exponentiation.threshold 4096 in
/-- The charge targets at Keccak's sizes: `|DLab| + |Msg| + |A| ≤ 2^258`. -/
theorem card_dCharge_le :
    Fintype.card DLab + (Fintype.card Message + Fintype.card SkIdx) ≤ 2 ^ 258 := by
  have h := card_skIdx_le
  rw [card_dLab, card_message]
  calc 2 ^ 257 + (2 ^ 256 + Fintype.card SkIdx) ≤ 2 ^ 257 + (2 ^ 256 + 2 ^ 44) :=
        Nat.add_le_add_left (Nat.add_le_add_left h _) _
    _ ≤ 2 ^ 258 := by norm_num

set_option exponentiation.threshold 4096 in
/-- **A digest label is charged for at most `2^-254` of the coordinates** (`card_mul_sum_pBXInd_le`
with `|DLab| + |Msg| + |A|` targets): Mismatch's per-label charge at Keccak's sizes. -/
theorem dBXInd_frac_le_keccak {E F : Type} [Fintype E] [Fintype F] [Nonempty E] [Nonempty F]
    (c : E → F → DLab → X)
    (extra : (SpongeKeys X Z × Equiv.Perm (X × Z)) × E → F → Finset Z)
    (hm : ∀ ω f, (extra ω f).card ≤ Fintype.card Message + Fintype.card SkIdx) (a : DLab) :
    (Fintype.card (PSt E F DLab) : ℝ≥0∞)⁻¹ *
        ((∑ y : PSt E F DLab, pBXInd c dLabOrd extra a y : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 2 ^ 254) := by
  have h := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
    (card_mul_sum_pBXInd_le c dLabOrd extra _ hm a)
  have hN : (Fintype.card (PSt E F DLab) : ℝ≥0∞) ≠ 0 :=
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
