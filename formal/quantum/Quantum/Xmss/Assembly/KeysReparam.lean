module

public import Quantum.Xmss.Assembly.KeyLazy
public import Quantum.Xmss.Assembly.ReparamR0

@[expose] public section

/-!
# The keys as coordinates: KeyLazy's averaging on ReparamR0's reparametrization

KeyLazy's `uavg_kTot_le` averages the fresh `k`, `k'` program flips over a reparametrization in
which the keys `k`, `k'` are coordinates and the hidden values are a function `val` of the hidden
data alone. ReparamR0's `r0E` has the keys as coordinates (Reparam's `w`), but its game congruence
`hgame_r0E` realizes the game at the table's randomizer bases on the labels, which are `r0E`'s
hidden coordinates only at the first labels.

* **The non-first labels' randomizer bases are functions of the public data and the hidden data**
  (`r0Val`, `valueAt_inr_eq_r0Val`): a label's base is `trunc128 (r + h c)` with `r` its rate and
  `c` its capacity (`hash_of_lt`), both read off `π`, the parameter and the never-revealed part
  `RK` (`r0Rate`, `r0Cap`). The first label `b` of the capacity class (`r0First`) has the `h`-slot
  `r_b + h c` (R0Stage's `r0Split_coords`), which `r0E` stores as the hidden coordinate `.inr b`
  and the pad (`r0Slot_r0E`). So the base is `trunc128 (r_a - r_b + slot_b)`. It depends on the
  public data (`π`, `P`), never on the keys `k`, `k'`.
* **KeyLazy's lemma with `val` depending on the public datum** (`uavg_kTot_le_dep`): the averaging
  fixes the public datum and the hidden data while summing over the keys, so `val` may read the
  public datum.
* **The reparametrization** (`keyE`): `r0E` with the keys split off the public data (`keySplit`),
  injective on `r0G treeQ 18` (`keyE_injOn`), `card_keyE_le`, `hgame_keyE`, `permK_keyE`, and the
  bad fraction `2^-174 ≤ 2^-170` (`keyE_bad_le`).
* `uavg_kTot_le_r0`: the averaged fresh flips are at most `progCap · 2^-301 + progCap · 2^-170`.
-/

open IPFunctor Matrix
open scoped ENNReal ComplexOrder

open Quantum.SufCma

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

attribute [local instance] badRDec

/-! ## KeyLazy's averaging with hidden values depending on the public datum -/

section dep

/-- **KeyLazy's `uavg_kTot_le` with `val` reading the public datum**: as `uavg_kTot_le`, with the
hidden values `val p x` a function of the public datum `p` and the hidden data `x`. -/
theorem uavg_kTot_le_dep {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (hq : q ≤ 2 ^ 64) {E Q V : Type} [Fintype E] [Nonempty E] [Fintype Q] [Fintype V]
    (e : HonestTable × E → Q × (((X → Z) × (X → Z)) × V)) (G : HonestTable × E → Prop)
    [DecidablePred G] (hinj : Set.InjOn e {t | G t})
    (hcard : Fintype.card Q * Fintype.card (((X → Z) × (X → Z)) × V) ≤
      Fintype.card (HonestTable × E))
    (par : Q → PublicParameter) (perm : Q → Equiv.Perm (X × Z)) (hk : Q → Z → X)
    (val : Q → V → HPos → Digest)
    (hgame : ∀ t, G t → gameR A t.1 = gameKK A (par (e t).1) (perm (e t).1) (hk (e t).1)
      (val (e t).1 (e t).2.2) (e t).2.1.1 (e t).2.1.2)
    (hπ : ∀ t, G t → perm (e t).1 = t.1.perm) :
    uavg (fun L ↦ if PermGood L.perm 18 then kTot A L else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * ((Fintype.card (HonestTable × E) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬G t).card) := by
  refine uavg_le_of_injOn e G hinj hcard _
    (fun p x ↦ if PermGood (perm p) 18 then (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
        (gameKK A (par p) (perm p) (hk p) (val p x.2) x.1.1 x.1.2) initR else 0)
    (fun t ht ↦ ?_) progCap (fun t _ ↦ ?_) ((2 ^ 301)⁻¹ * progCap) (fun p ↦ ?_)
  · by_cases hL : PermGood t.1.perm 18
    · have hp : PermGood (perm (e t).1) 18 := (hπ t ht).symm ▸ hL
      rw [ite_eq_left hL, ite_eq_left hp]
      refine (kTot_le_kfTot hperm hsign hq t.1).trans_eq ?_
      rw [hgame t ht, hπ t ht]
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hL : PermGood t.1.perm 18
    · rw [ite_eq_left hL]
      exact kTot_le_progCap hperm hsign t.1
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hp : PermGood (perm p) 18
    · refine (Finset.sum_congr rfl fun x _ ↦ ite_eq_left hp).trans_le ?_
      exact sum_pair_le (fun k k' w ↦ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW (perm p))))
          (gameKK A (par p) (perm p) (hk p) (val p w) k k') initR) _ _
        fun w ↦ sum_kfTot_le A (par p) (perm p) (hk p) (val p w) hperm hsign hp
    · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right hp]
      exact zero_le

end dep

/-! ## The randomizer bases off the first labels -/

section r0val

/-- A label's rate at the never-revealed part: the round of its `S`-keyed first block with its
`k`-slot. -/
def r0Rate (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) (a : RLabel) : X :=
  (π (R0.rCell a P k.1, k.2.2.1 a)).1

open scoped Classical in
/-- Every capacity class has a first label: a label of least rank with the capacity of `a`. -/
theorem exists_r0First (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) (a : RLabel) :
    ∃ b, r0Cap π P k b = r0Cap π P k a ∧
      ∀ c, R0.rOrd c < R0.rOrd b → r0Cap π P k c ≠ r0Cap π P k b := by
  have h : ∃ n, ∃ b, R0.rOrd b = n ∧ r0Cap π P k b = r0Cap π P k a := ⟨_, a, rfl, rfl⟩
  obtain ⟨b, hb, he⟩ := Nat.find_spec h
  exact ⟨b, he, fun c hc hce ↦ Nat.find_min h (hb ▸ hc) ⟨c, rfl, hce.trans he⟩⟩

/-- The first label of the capacity class of `a`. -/
noncomputable def r0First (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK)
    (a : RLabel) : RLabel :=
  Classical.choose (exists_r0First π P k a)

theorem r0First_spec (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK) (a : RLabel) :
    r0Cap π P k (r0First π P k a) = r0Cap π P k a ∧
      ∀ c, R0.rOrd c < R0.rOrd (r0First π P k a) →
        r0Cap π P k c ≠ r0Cap π P k (r0First π P k a) :=
  Classical.choose_spec (exists_r0First π P k a)

/-- **The randomizer base of a label read off the coordinates**: from the `h`-slot of the first
label `b` of its capacity class (the hidden coordinate `.inr b` with the pad), shifted by the
difference of the two labels' rates. -/
noncomputable def r0Val (π : Equiv.Perm (X × Z)) (P : PublicParameter) (k : RK)
    (v : HPos → Digest) (pad : RPad) (a : RLabel) : Digest :=
  trunc128 (r0Rate π P k a - r0Rate π P k (r0First π P k a) +
    r0SlotEquiv.symm (v (.inr (r0First π P k a)), pad (r0First π P k a)))

variable {ι : Type} {β : ι → Type}
  {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
  {θ : CTab R0.RLabel}

/-- **On R0Stage's good set, every label's randomizer base is read off the first label's
`h`-slot**: `R0(a) = trunc128 (r_a + h c) = trunc128 (r_a - r_b + (r_b + h c))`. -/
theorem valueAt_inr_eq_r0Slot (hθ : θ ∈ r0Good R0.rCell R0.rOrd Q) (a : RLabel) :
    valueAt θ.1.1 (.inr a) = trunc128
      (r0Rate θ.1.1.perm θ.1.1.param (rkOf θ) a -
        r0Rate θ.1.1.perm θ.1.1.param (rkOf θ) (r0First θ.1.1.perm θ.1.1.param (rkOf θ) a) +
        (r0Split R0.rCell R0.rOrd θ).1.2.2.2 (r0First θ.1.1.perm θ.1.1.param (rkOf θ) a)) := by
  obtain ⟨-, h1, -, h3, -⟩ := r0Split_coords R0.rCell_injective hθ
  have hS := r0Split_snd R0.rCell R0.rOrd θ
  obtain ⟨hcap, hmin⟩ := r0First_spec θ.1.1.perm θ.1.1.param (rkOf θ) a
  have hbB : r0First θ.1.1.perm θ.1.1.param (rkOf θ) a ∉ r0B R0.rCell R0.rOrd θ.1.1 := fun h ↦ by
    obtain ⟨a', ha', c, hc, he⟩ := mem_r0Bk.mp ((mem_r0B_iff hθ _).mp h)
    obtain rfl := Sum.inr_injective ha'
    exact hmin c hc he
  have hrate : ∀ c, r0Rate θ.1.1.perm θ.1.1.param (rkOf θ) c =
      rateOf θ.1.1.keys.2.1 θ.1.1.perm (coinCellK R0.rCell θ.1.1 c) := fun c ↦ by
    show (θ.1.1.perm (R0.rCell c θ.1.1.param (r0Split R0.rCell R0.rOrd θ).2,
      (r0Split R0.rCell R0.rOrd θ).1.2.1 c)).1 = _
    rw [h1 c, hS]
    rfl
  have hR : valueAt θ.1.1 (.inr a) = trunc128
      (rateOf θ.1.1.keys.2.1 θ.1.1.perm (coinCellK R0.rCell θ.1.1 a) +
        θ.1.1.keys.1 (coinCellH R0.rCell θ.1.1 a)) :=
    congrArg truncateHash (hash_of_lt θ.1.1 _ (R0.length_rbInput a θ.1.1.param θ.1.1.seed))
  rw [hR, h3 _ hbB, hrate, hrate, ← add_assoc, sub_add_cancel, coinCellH_eq_r0Cap hθ a,
    coinCellH_eq_r0Cap hθ, hcap]

end r0val

/-! ## The reparametrization with the keys split off -/

section reparam

/-- **The public data without the keys**: Reparam's `h''`, the parameter, `π`, and the public slot
bits. -/
abbrev KQ : Type := ((Z → X) × (PublicParameter × Equiv.Perm (X × Z))) × RS

open scoped Classical in
/-- The public data without the keys are finite. -/
noncomputable instance instFintypeKQ : Fintype KQ :=
  inferInstanceAs (Fintype (((Z → X) × (PublicParameter × Equiv.Perm (X × Z))) × RS))

/-- **The hidden data**: `r0E`'s hidden values and never-revealed part. -/
abbrev KV : Type := (HPos → Digest) × (RK × RW)

/-- The hidden data are finite. -/
noncomputable instance instFintypeKV : Fintype KV :=
  inferInstanceAs (Fintype ((HPos → Digest) × (RK × RW)))

/-- The keys split off the public data. -/
def keySplit (y : RP × KV) : KQ × (((X → Z) × (X → Z)) × KV) :=
  (((y.1.1.1, (y.1.1.2.1, y.1.1.2.2.1)), y.1.2), ((y.1.1.2.2.2.1, y.1.1.2.2.2.2), y.2))

/-- The keys joined back into the public data. -/
def keyJoin (x : KQ × (((X → Z) × (X → Z)) × KV)) : RP × KV :=
  (((x.1.1.1, (x.1.1.2.1, x.1.1.2.2, x.2.1.1, x.2.1.2)), x.1.2), x.2.2)

/-- Splitting off the keys is a bijection. -/
def keyEquiv : RP × KV ≃ KQ × (((X → Z) × (X → Z)) × KV) where
  toFun := keySplit
  invFun := keyJoin
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The reparametrization with the keys as coordinates**: `r0E`, then the keys split off. -/
noncomputable def keyE (t : HonestTable × RE) : KQ × (((X → Z) × (X → Z)) × KV) :=
  keySplit (r0E t)

/-- The parameter of the public data. -/
def parK (p : KQ) : PublicParameter :=
  p.1.2.1

/-- The permutation of the public data. -/
def permK (p : KQ) : Equiv.Perm (X × Z) :=
  p.1.2.2

/-- The `h` key of the public data. -/
def hkK (p : KQ) : Z → X :=
  p.1.1

/-- **The hidden values**: `r0E`'s at the positions, read off the first labels' `h`-slots at the
labels (`r0Val`). -/
noncomputable def valK (p : KQ) (v : KV) : HPos → Digest :=
  Sum.elim (fun q ↦ v.1 (.inl q)) (r0Val (permK p) (parK p) v.2.1 v.1 v.2.2.2)

/-- **`hinj`**: the reparametrization is injective on the good set. -/
theorem keyE_injOn : Set.InjOn keyE {t | r0G treeQ 18 t} :=
  fun _ h₁ _ h₂ he ↦ r0E_injOn treeQ 18 h₁ h₂ (keyEquiv.injective he)

/-- **`hcard`**: the coordinates are as many as the padded tables. -/
theorem card_keyE_le :
    Fintype.card KQ * Fintype.card (((X → Z) × (X → Z)) × KV) ≤
      Fintype.card (HonestTable × RE) := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr (keyEquiv.symm.trans (r0Psi.symm.trans
    (((rtabEquiv.prodCongr (Equiv.refl Rest)).prodCongr (Equiv.refl _)).trans r0Phi.symm)))).le

/-- **`hπ`**: the permutation of the public data is the table's. -/
theorem permK_keyE (t : HonestTable × RE) : permK (keyE t).1 = t.1.perm :=
  permR_r0E t

/-- The slot of a label is `r0E`'s hidden coordinate with its pad. -/
theorem r0Slot_r0E (t : HonestTable × RE) (c : RLabel) :
    r0SlotEquiv.symm ((r0E t).2.1 (.inr c), (r0E t).2.2.2.2 c) =
      (r0Split R0.rCell R0.rOrd (thetaOf t)).1.2.2.2 c := by
  show r0SlotEquiv.symm ((r0SlotEquiv ((seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.2.2.2 c)).1,
    (r0SlotEquiv ((seedKSplit R0.rCell R0.rOrd (xOf t)).1.1.2.2.2 c)).2) = _
  rw [Prod.mk.eta, Equiv.symm_apply_apply, seedKSplit_coins]
  rfl

variable {ι : Type} {β : ι → Type}
  {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)} {G : ℕ}
  {t : HonestTable × RE}

/-- **On the good set, the table's randomizer bases are `r0Val` at the coordinates.** -/
theorem valueAt_inr_eq_r0Val (ht : r0G Q G t) (a : RLabel) :
    valueAt t.1 (.inr a) = r0Val (permR (r0E t).1) (parR (r0E t).1) (r0E t).2.2.1 (r0E t).2.1
      (r0E t).2.2.2.2 a := by
  rw [permR_r0E, parR_r0E ht, rk_r0E]
  unfold r0Val
  rw [r0Slot_r0E]
  exact valueAt_inr_eq_r0Slot (mem_seedKGood.mp ht.1).1 a

/-- **`hgame`**: on the good set, the game at the table is KeyLazy's `gameKK` at the public data,
the hidden values `valK` and the keys. -/
theorem hgame_keyE (A : Adversary (X × Z)) {t : HonestTable × RE} (ht : r0G treeQ 18 t) :
    gameR A t.1 = gameKK A (parK (keyE t).1) (permK (keyE t).1) (hkK (keyE t).1)
      (valK (keyE t).1 (keyE t).2.2) (keyE t).2.1.1 (keyE t).2.1.2 :=
  realizeT_gameT_keys cwUpd A t.1 (r0Phi t).1.1 ht.2.2.1 (r0G_param ht) (r0Phi_perm t)
    (r0G_start ht) (r0G_keys hashesSlots_treeQ ht) _ (fun _ ↦ rfl)
    fun lab ↦ (valueAt_inr_eq_r0Val ht lab).symm

/-- `2^-174 ≤ 2^-170`. -/
theorem ofReal_174_le_170 : ENNReal.ofReal (1 / 2 ^ 174) ≤ (2 ^ 170 : ℝ≥0∞)⁻¹ := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
  exact ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-- **The bad fraction**: ReparamR0's `2^-174`, at most `2^-170`. -/
theorem keyE_bad_le :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card ≤ (2 ^ 170 : ℝ≥0∞)⁻¹ :=
  r0G_frac_le_keccak.trans ofReal_174_le_170

end reparam

/-! ## The fresh `k`, `k'` flips -/

/-- **KeyLazy's `hk` discharged**: averaged over the tables with `PermGood π 18`, the fresh `k`,
`k'` program flips are at most `progCap · 2^-301 + progCap · 2^-170` (`uavg_kTot_le_dep` on
`keyE`). -/
theorem uavg_kTot_le_r0 {q : ℕ} {A : Adversary (X × Z)}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
    (hq : q ≤ 2 ^ 64) :
    uavg (fun L ↦ if PermGood L.perm 18 then kTot A L else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * (2 ^ 170 : ℝ≥0∞)⁻¹ := by
  have h := uavg_kTot_le_dep (E := RE) (Q := KQ) (V := KV) hperm hsign hq keyE (r0G treeQ 18)
    keyE_injOn card_keyE_le parK permK hkK valK (fun _ ht ↦ hgame_keyE A ht)
    fun t _ ↦ permK_keyE t
  refine h.trans ?_
  gcongr
  exact keyE_bad_le

end Quantum.Xmss.Assembly

end
