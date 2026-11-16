module

public import Quantum.Sphincs.Assembly.ReparamFull

@[expose] public section

/-!
# The keys as coordinates of leanSPHINCS's composed reparametrization

The averaging of the fresh `k`, `k'` program flips (leanXMSS's `KeyLazy`, SP-PS2) runs over a
reparametrization in which the keys `k`, `k'` are coordinates and the hidden values are a function
of the hidden data alone. `fullE`'s public data carries the keys (`w = (PK.seed, π, k, k')`), and
its hidden values are a coordinate.

* `keyE`: `fullE` with the keys split off the public data (`keySplitS`); `keyE_injOn` on the good
  set, `card_keyE` (the coordinates are as many as the padded tables), `permK_keyE`.
* `hgame_keyE`: on the good set, the canonical game at the table is the canonical game at the public
  data with the keys (`pubK`), realized at hidden values agreeing with `valK` (the hidden data) off
  the charged coordinates `chgB t`.
* `keyE_bad_le`: the bad fraction (`fullG_frac_le_keccak`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (PublicParameter)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (Agree)

namespace Quantum.Sphincs.Assembly

/-- **The public data without the keys**: Reparam's `h''`, `PK.seed`, `π`, the public slot bits. -/
abbrev KQS : Type := ((Z → X) × (PublicParameter × Equiv.Perm (X × Z))) × PubR

/-- **The hidden data**: `fullE`'s hidden values and never-revealed part. -/
abbrev KVS : Type := ((s : HPos) → XD s) × KK

/-- The keys split off the public data. -/
def keySplitS (y : PP × KVS) : KQS × (((X → Z) × (X → Z)) × KVS) :=
  (((y.1.1.1, (y.1.1.2.1, y.1.1.2.2.1)), y.1.2), ((y.1.1.2.2.2.1, y.1.1.2.2.2.2), y.2))

/-- The keys joined back into the public data. -/
def keyJoinS (x : KQS × (((X → Z) × (X → Z)) × KVS)) : PP × KVS :=
  (((x.1.1.1, (x.1.1.2.1, x.1.1.2.2, x.2.1.1, x.2.1.2)), x.1.2), x.2.2)

/-- Splitting off the keys is a bijection. -/
def keyEquivS : PP × KVS ≃ KQS × (((X → Z) × (X → Z)) × KVS) where
  toFun := keySplitS
  invFun := keyJoinS
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The reparametrization with the keys as coordinates**: `fullE`, then the keys split off. -/
noncomputable def keyE (t : FT) : KQS × (((X → Z) × (X → Z)) × KVS) :=
  keySplitS (fullE t)

/-- The template's public data from the public data without the keys and the keys. -/
def pubK (q : KQS) (kk : (X → Z) × (X → Z)) : Pub :=
  ⟨q.1.2.1, q.1.2.2, (q.1.1, kk.1, kk.2)⟩

/-- The permutation of the public data. -/
def permK (q : KQS) : Equiv.Perm (X × Z) :=
  q.1.2.2

/-- **The hidden values**: the hidden data's (a function of the hidden data alone). -/
def valK (x : KVS) : (s : HPos) → XD s :=
  x.1

theorem pubK_keySplitS (y : PP × KVS) : pubK (keySplitS y).1 (keySplitS y).2.1 = pubP y.1 :=
  rfl

/-- **`hinj`**: the reparametrization is injective on the good set. -/
theorem keyE_injOn (S : PP → ((s : HPos) → XD s) → Prop) : Set.InjOn keyE {t | FullG S t} :=
  fun _ h₁ _ h₂ he ↦ fullE_injOn h₁.1.2.2.2 h₂.1.2.2.2 (keyEquivS.injective he)

open scoped Classical in
noncomputable instance instFintypeKQS : Fintype KQS :=
  inferInstanceAs (Fintype (((Z → X) × (PublicParameter × Equiv.Perm (X × Z))) × PubR))

noncomputable instance instFintypeKeysKVS : Fintype (((X → Z) × (X → Z)) × KVS) :=
  instFintypeProd _ _

/-- **`hcard`**: the coordinates are as many as the padded tables. -/
theorem card_keyE :
    Fintype.card KQS * Fintype.card (((X → Z) × (X → Z)) × KVS) = Fintype.card FT := by
  rw [← Fintype.card_prod, ← card_coords, ← Fintype.card_prod]
  exact Fintype.card_congr keyEquivS.symm

/-- **`hπ`**: the permutation of the public data is the table's. -/
theorem permK_keyE (t : FT) : permK (keyE t).1 = (tabOf t).perm :=
  pubP_perm

/-- **`hgame`**: on the good set, the canonical game at the table is the canonical game at the
public data with the keys, realized at hidden values agreeing with `valK` off the charged
coordinates. -/
theorem hgame_keyE (S : PP → ((s : HPos) → XD s) → Prop) (A : SAdversary) {t : FT}
    (ht : FullG S t) :
    ∃ v : (s : HPos) → XD s, Agree (Finset.univ \ chgB t) v (valK (keyE t).2.2) ∧
      gameR msgPol A (pubOf (tabOf t)) (valueAt (tabOf t)) =
        gameR msgPol A (pubK (keyE t).1 (keyE t).2.1) v := by
  rw [keyE, pubK_keySplitS]
  exact ((fullE_spec S A).2 t ht).1

open scoped Classical in
/-- **The bad fraction**: `fullG_frac_le_keccak`. -/
theorem keyE_bad_le (S : PP → ((s : HPos) → XD s) → Prop) :
    (Fintype.card FT : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun t ↦ ¬FullG S t).card ≤
      ENNReal.ofReal (1 / 2 ^ 77) + ENNReal.ofReal (1 / 2 ^ 400) +
        (Fintype.card YS : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y : YS ↦ ¬S (psiE y).1 (psiE y).2.1).card :=
  fullG_frac_le_keccak S

end Quantum.Sphincs.Assembly

end
