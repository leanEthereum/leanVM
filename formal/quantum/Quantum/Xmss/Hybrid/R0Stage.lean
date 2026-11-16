module

public import Quantum.Xmss.Hybrid.CoinStage
public import Quantum.Sponge.PermTail

@[expose] public section

/-!
# The randomizer-base stages: `k` and `k'` at every label, `h` at the first labels

`schemeSplit` hides the scheme seed `S`. The randomizer base `R0` of a label `a` (`rbInput`, one
block) reads `k` at the `S`-keyed cell `cell a P S`, `k'` at its rate, and `h` at its capacity.
Three exchanges, composed after `schemeSplit`, move these values into slots:

* `stageK` (CoinStage): `k` at the labels' cells with the `k`-slots (the cells are distinct for
  distinct labels);
* `stageK'` (CoinStage): `k'` at the labels' rates with the `k'`-slots, when the rates are distinct
  (`RateInj`);
* `stageHOn`: `h` at the capacity of each **first** label (`IsFirst`: no label of smaller rank has
  the same capacity) with its `h`-slot, which takes the block's output. The first labels have
  distinct capacities by construction, so this exchange needs no guard (`xchOn`, `stageNOn`). The
  slots of the other labels stay pads.

`r0Split : CTab J ≃ CPub J × MasterSeed` composes them after `schemeSplit`.

* **Coordinates on the good set** (`r0Good`: `schemeGood`, `R0Coll`, `ReadGood`; `r0Split_coords`):
  the `k`- and `k'`-slots hold the table's `k`, `k'` on the paths; the `h`-slot of a first label
  holds the block's output, so `r0Coord` (its first `128` bits, `r0SlotEquiv`) is the label's
  digest (`digest_eq_r0Coord`, `randomizerBase_eq_r0Coord`); the slot of a non-first label is the
  table's pad; the non-first set read off the coordinates (`pubB`, the `h`-stage's: `mem_pubB`) is
  the table's `r0B` (`pubB_r0Split`); the challenger's data is a function of the public part
  (`schemeData_eq_pubData_r0Split`).
* **The bad fraction** (`r0Good_frac_le`): `schemeGood`'s, the bad permutations, the rate
  collisions `|J|² / |X|` averaged over `π` (`card_mul_card_filter_rate_eq_le`), the capacity
  hits of the hidden cells `|J| |A| (G + 1) / |Z|`, and per computation
  `qs₂ᵢ / 2^256 + |J| (G + 1) qᵢ / |Z|`. `ReadGood` for the computations of the output paths is
  where the randomizer-base capacities avoid the output capacities and the intermediate
  `h`-cells, and the randomizer-base rates avoid the paths' `k'`-cells.
* `R0.RLabel`: the labels of leanXMSS's randomizer bases, `rbCell` injective on them
  (`rCell_injective`) and apart from the hidden cells (`hidCell_ne_rCell`);
  `r0Good_frac_le_rLabel`, and at Keccak's sizes (`G = 18`) `r0Good_frac_le_keccak`: `2^-181` for
  the static collisions plus `qs₂ᵢ / 2^256 + qᵢ / 2^219` per computation.
-/

open scoped ENNReal

open Quantum.SufCma

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Sponge

/-! ## Exchanges on a set of labels, over abstract types -/

section partialXch

variable {X Y J W : Type*}

/-- **An equivalence of some slots, extended**: `e` acts on `Y` and the slots of the labels in
`F`; the other slots stay. -/
def extendOn (F : J → Prop) [DecidablePred F] (e : Y × ({a // F a} → X) ≃ Y × ({a // F a} → X)) :
    Y × (J → X) ≃ Y × (J → X) :=
  ((Equiv.refl Y).prodCongr (Equiv.piEquivPiSubtypeProd F fun _ ↦ X)).trans
    ((Equiv.prodAssoc _ _ _).symm.trans ((e.prodCongr (Equiv.refl _)).trans
      ((Equiv.prodAssoc _ _ _).trans
        ((Equiv.refl Y).prodCongr (Equiv.piEquivPiSubtypeProd F fun _ ↦ X).symm))))

theorem extendOn_fst (F : J → Prop) [DecidablePred F]
    (e : Y × ({a // F a} → X) ≃ Y × ({a // F a} → X)) (p : Y × (J → X)) :
    (extendOn F e p).1 = (e (p.1, fun a ↦ p.2 a.1)).1 :=
  rfl

theorem extendOn_snd (F : J → Prop) [DecidablePred F]
    (e : Y × ({a // F a} → X) ≃ Y × ({a // F a} → X)) (p : Y × (J → X)) (a : J) :
    (extendOn F e p).2 a = if h : F a then (e (p.1, fun a ↦ p.2 a.1)).2 ⟨a, h⟩ else p.2 a :=
  rfl

variable {Z : Type*} [AddCommGroup X]

theorem xch_fst_pos (pos : J → Z) (hpos : Function.Injective pos) (sh : J → X)
    (p : (Z → X) × (J → X)) (a : J) : (xch pos hpos sh p).1 (pos a) = p.2 a := by
  change (match Function.partialInv pos (pos a) with
    | some a => p.2 a
    | none => p.1 (pos a)) = p.2 a
  rw [Function.partialInv_left hpos]

/-- **Exchange cells with slots on a set of labels**: for the labels in `F`, on which the cells
`pos` are distinct, the cells take the slot values and the slots the cell values shifted by `sh`;
the other slots and cells keep theirs. -/
noncomputable def xchOn (F : J → Prop) [DecidablePred F] (pos : J → Z)
    (hpos : ∀ a b, F a → F b → pos a = pos b → a = b) (sh : J → X) :
    (Z → X) × (J → X) ≃ (Z → X) × (J → X) :=
  extendOn F (xch (fun a : {a // F a} ↦ pos a.1)
    (fun a b h ↦ Subtype.ext (hpos a.1 b.1 a.2 b.2 h)) fun a ↦ sh a.1)

section xchOn

variable (F : J → Prop) [DecidablePred F] (pos : J → Z)
  (hpos : ∀ a b, F a → F b → pos a = pos b → a = b) (sh : J → X) (p : (Z → X) × (J → X))

theorem xchOn_snd_of_mem {a : J} (h : F a) : (xchOn F pos hpos sh p).2 a = sh a + p.1 (pos a) := by
  rw [xchOn, extendOn_snd, dite_eq_left h]
  rfl

theorem xchOn_snd_of_notMem {a : J} (h : ¬F a) : (xchOn F pos hpos sh p).2 a = p.2 a := by
  rw [xchOn, extendOn_snd, dite_eq_right h]

theorem xchOn_fst_of_mem {a : J} (h : F a) : (xchOn F pos hpos sh p).1 (pos a) = p.2 a := by
  rw [xchOn, extendOn_fst]
  exact xch_fst_pos (fun a : {a // F a} ↦ pos a.1) _ _ _ ⟨a, h⟩

theorem xchOn_fst_of_notMem {z : Z} (hz : ∀ a, F a → pos a ≠ z) :
    (xchOn F pos hpos sh p).1 z = p.1 z := by
  rw [xchOn, extendOn_fst]
  exact xch_fst_of_notMem _ _ _ _ fun a ↦ hz a.1 a.2

end xchOn

/-- **A first label**: no label of smaller rank has the same cell. -/
def IsFirst (ord : J ↪ ℕ) (pos : J → Z) (a : J) : Prop :=
  ∀ b, ord b < ord a → pos b ≠ pos a

/-- The first labels have distinct cells. -/
theorem isFirst_inj (ord : J ↪ ℕ) (pos : J → Z) :
    ∀ a b, IsFirst ord pos a → IsFirst ord pos b → pos a = pos b → a = b := by
  intro a b ha hb h
  rcases lt_trichotomy (ord a) (ord b) with hlt | heq | hgt
  · exact absurd h (hb a hlt)
  · exact ord.injective heq
  · exact absurd h.symm (ha b hgt)

/-- Every cell is the cell of a first label. -/
theorem exists_isFirst (ord : J ↪ ℕ) (pos : J → Z) (a : J) :
    ∃ b, IsFirst ord pos b ∧ pos b = pos a := by
  suffices h : ∀ n, ∀ a, ord a = n → ∃ b, IsFirst ord pos b ∧ pos b = pos a from h _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hn
    by_cases h : IsFirst ord pos a
    · exact ⟨a, h, rfl⟩
    · simp only [IsFirst, not_forall, not_not] at h
      obtain ⟨b, hb, hpos⟩ := h
      obtain ⟨c, hc, hcb⟩ := ih (ord b) (hn ▸ hb) b rfl
      exact ⟨c, hc, hcb.trans hpos⟩

open scoped Classical in
/-- **Exchange the first labels' cells with their slots, fiberwise**: for the data `w` the exchange
preserves, the cells `pos w a` of the first labels `a` take the slot values and the slots the cell
values shifted by `sh w a`; the other slots and cells keep theirs. -/
noncomputable def stageNOn (ord : J ↪ ℕ) (pos : W → J → Z) (sh : W → J → X) :
    ((Z → X) × (J → X)) × W ≃ ((Z → X) × (J → X)) × W :=
  fiberEquiv Prod.snd (fun w ↦ (xchOn (IsFirst ord (pos w)) (pos w) (isFirst_inj ord (pos w))
    (sh w)).prodCongr (Equiv.refl W)) fun _ _ ↦ rfl

/-- **The partial exchange**: it keeps the data `w`; the slot of a first label takes the cell
value shifted, and its cell the slot value; the other slots keep their values, and so do the cells
of no label. -/
theorem stageNOn_spec (ord : J ↪ ℕ) (pos : W → J → Z) (sh : W → J → X)
    (p : (Z → X) × (J → X)) (w : W) :
    ∃ p' : (Z → X) × (J → X), stageNOn ord pos sh (p, w) = (p', w) ∧
      (∀ a, IsFirst ord (pos w) a → p'.2 a = sh w a + p.1 (pos w a) ∧ p'.1 (pos w a) = p.2 a) ∧
      (∀ a, ¬IsFirst ord (pos w) a → p'.2 a = p.2 a) ∧
      ∀ z, (∀ a, pos w a ≠ z) → p'.1 z = p.1 z := by
  classical
  exact ⟨_, rfl, fun a ha ↦ ⟨xchOn_snd_of_mem _ _ _ _ _ ha, xchOn_fst_of_mem _ _ _ _ _ ha⟩,
    fun a ha ↦ xchOn_snd_of_notMem _ _ _ _ _ ha,
    fun z hz ↦ xchOn_fst_of_notMem _ _ _ _ _ fun a _ ↦ hz a⟩

end partialXch

/-! ## Rate collisions averaged over the permutation, over abstract types -/

section permRate

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

omit [DecidableEq Z] in
/-- The points of a rate. -/
theorem card_filter_fst_eq (x : X) :
    (Finset.univ.filter fun y : X × Z ↦ y.1 = x).card = Fintype.card Z := by
  have h : (Finset.univ.filter fun y : X × Z ↦ y.1 = x) =
      (Finset.univ : Finset Z).map ⟨fun z ↦ (x, z), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
    ext y
    obtain ⟨y₁, y₂⟩ := y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    exact ⟨fun h ↦ ⟨y₂, by subst h; rfl⟩, fun ⟨_, hz⟩ ↦ (congrArg Prod.fst hz).symm⟩
  rw [h, Finset.card_map, Finset.card_univ]

/-- Arithmetic of `card_mul_card_filter_rate_eq_le`. -/
theorem mul_le_of_mul_sub_le {x z n P : ℕ} (hx : 1 ≤ x) (h2 : 2 ≤ x * z)
    (h : n * (x * z - 1) ≤ P * (z - 1)) : x * n ≤ P := by
  have hz : x * (z - 1) ≤ x * z - 1 := by
    rw [Nat.mul_sub_one]
    generalize x * z = m at *
    omega
  refine Nat.le_of_mul_le_mul_right (c := x * z - 1) ?_ (by omega)
  calc x * n * (x * z - 1) = x * (n * (x * z - 1)) := Nat.mul_assoc _ _ _
    _ ≤ x * (P * (z - 1)) := Nat.mul_le_mul_left _ h
    _ = P * (x * (z - 1)) := by rw [Nat.mul_left_comm]
    _ ≤ P * (x * z - 1) := Nat.mul_le_mul_left _ hz

/-- **Two points rarely share their rate after a uniform permutation**: for distinct points, at
most `1 / |X|` of the permutations. -/
theorem card_mul_card_filter_rate_eq_le {a b : X × Z} (hab : a ≠ b) :
    Fintype.card X * (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ (π a).1 = (π b).1).card ≤
      Fintype.card (Equiv.Perm (X × Z)) := by
  have hb : b ∉ ({a} : Finset (X × Z)) := by
    rw [Finset.mem_singleton]
    exact hab.symm
  have h := card_filter_mem_mul_le Finset.univ {a} hb
    (fun π ↦ (Finset.univ.filter fun y : X × Z ↦ y.1 = (π a).1).erase (π a))
    (Fintype.card Z - 1) (fun _ _ _ _ ↦ Finset.mem_univ _)
    (fun π _ σ hσ ↦ by rw [hσ a (Finset.mem_singleton_self a)])
    (fun π _ ↦ by
      rw [Finset.card_erase_of_mem (by simp), card_filter_fst_eq])
  have hfilt : (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦
      π b ∈ (Finset.univ.filter fun y : X × Z ↦ y.1 = (π a).1).erase (π a)) =
        Finset.univ.filter fun π ↦ (π a).1 = (π b).1 :=
    Finset.filter_congr fun π _ ↦ by
      rw [Finset.mem_erase, Finset.mem_filter]
      exact ⟨fun h ↦ h.2.2.symm, fun h ↦ ⟨fun h' ↦ hab (π.injective h').symm, Finset.mem_univ _,
        h.symm⟩⟩
  rw [hfilt, Finset.card_univ, Finset.card_singleton, Fintype.card_prod] at h
  have h2 : 2 ≤ Fintype.card X * Fintype.card Z := by
    rw [← Fintype.card_prod, ← Finset.card_pair hab]
    exact Finset.card_le_univ _
  have hx : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr ⟨a.1⟩
  exact mul_le_of_mul_sub_le hx h2 h

open scoped Classical in
/-- **Distinct points rarely collide in rate after a uniform permutation**: the rates of the
images of the points `p a` (distinct) collide for at most `|J|² / |X|` of the permutations. -/
theorem card_mul_sum_not_injective_rate_le {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → X × Z) (hp : Function.Injective p) :
    Fintype.card X * ∑ π : Equiv.Perm (X × Z),
        (if ¬Function.Injective (fun a ↦ (π (p a)).1) then 1 else 0) ≤
      Fintype.card (Equiv.Perm (X × Z)) * (Fintype.card J * Fintype.card J) := by
  have hle : ∀ π : Equiv.Perm (X × Z),
      (if ¬Function.Injective (fun a ↦ (π (p a)).1) then 1 else 0) ≤
        ∑ a : J, ∑ b : J, (if a ≠ b ∧ (π (p a)).1 = (π (p b)).1 then 1 else 0) := by
    intro π
    by_cases h : Function.Injective (fun a ↦ (π (p a)).1)
    · rw [ite_eq_right (not_not.mpr h)]
      exact Nat.zero_le _
    · rw [ite_eq_left h]
      simp only [Function.Injective, not_forall] at h
      obtain ⟨a, b, hab, hne⟩ := h
      calc 1 = (if a ≠ b ∧ (π (p a)).1 = (π (p b)).1 then 1 else 0) :=
            (ite_eq_left ⟨hne, hab⟩).symm
        _ ≤ ∑ b' : J, (if a ≠ b' ∧ (π (p a)).1 = (π (p b')).1 then 1 else 0) :=
            Finset.single_le_sum (f := fun b' ↦
              (if a ≠ b' ∧ (π (p a)).1 = (π (p b')).1 then 1 else 0))
              (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ b)
        _ ≤ _ := Finset.single_le_sum (f := fun a' ↦ ∑ b' : J,
            (if a' ≠ b' ∧ (π (p a')).1 = (π (p b')).1 then 1 else 0))
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
  have hab : ∀ a b : J, Fintype.card X * ∑ π : Equiv.Perm (X × Z),
      (if a ≠ b ∧ (π (p a)).1 = (π (p b)).1 then 1 else 0) ≤
        Fintype.card (Equiv.Perm (X × Z)) := by
    intro a b
    by_cases h : a = b
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, true_and]
      rw [← Finset.card_filter]
      exact card_mul_card_filter_rate_eq_le (hp.ne h)
  calc Fintype.card X * ∑ π : Equiv.Perm (X × Z),
        (if ¬Function.Injective (fun a ↦ (π (p a)).1) then 1 else 0)
      ≤ Fintype.card X * ∑ π : Equiv.Perm (X × Z), ∑ a : J, ∑ b : J,
          (if a ≠ b ∧ (π (p a)).1 = (π (p b)).1 then 1 else 0) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun π _ ↦ hle π)
    _ = ∑ a : J, ∑ b : J, Fintype.card X * ∑ π : Equiv.Perm (X × Z),
          (if a ≠ b ∧ (π (p a)).1 = (π (p b)).1 then 1 else 0) := by
        rw [sum_comm_three (fun (π : Equiv.Perm (X × Z)) (a b : J) ↦
            if a ≠ b ∧ (π (p a)).1 = (π (p b)).1 then 1 else 0),
          Finset.mul_sum]
        simp only [Finset.mul_sum]
    _ ≤ ∑ _a : J, ∑ _b : J, Fintype.card (Equiv.Perm (X × Z)) :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hab a b
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- A count over pairs, bounded for each second coordinate. -/
theorem card_mul_sum_prod_le {P R : Type*} [Fintype P] [Fintype R] (c d : ℕ) (f : P → R → ℕ)
    (h : ∀ r, c * ∑ p, f p r ≤ Fintype.card P * d) :
    c * ∑ y : P × R, f y.1 y.2 ≤ Fintype.card (P × R) * d := by
  calc c * ∑ y : P × R, f y.1 y.2 = ∑ r, c * ∑ p, f p r := by
        rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _r : R, Fintype.card P * d := Finset.sum_le_sum fun r _ ↦ h r
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_prod]
        ring

/-- A count over a type in coordinates `(p, r)`, bounded for each second coordinate. -/
theorem card_mul_sum_equiv_prod_le {P R T : Type*} [Fintype P] [Fintype R] [Fintype T]
    (e : P × R ≃ T) (c d : ℕ) (F : T → ℕ) (h : ∀ r, c * ∑ p, F (e (p, r)) ≤ Fintype.card P * d) :
    c * ∑ t, F t ≤ Fintype.card T * d := by
  rw [← Fintype.sum_equiv e (fun y ↦ F (e y)) F fun _ ↦ rfl, ← Fintype.card_congr e]
  exact card_mul_sum_prod_le c d (fun p r ↦ F (e (p, r))) h

end permRate

/-! ## Capacity hits between two families of cells, over abstract types -/

section capCross

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

open scoped Classical

/-- **Two families of cells rarely share a capacity**: for a permutation with rate counts at most
`G` and cells `f a ≠ g b`, at most `|A| |B| (G + 1) / |Z|` of the keys `k, k'`. -/
theorem card_mul_sum_capOf_cross_le {A B : Type*} [Fintype A] [Fintype B]
    (π : Equiv.Perm (X × Z)) (G : ℕ) (f : A → X) (g : B → X) (hfg : ∀ a b, f a ≠ g b) :
    Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
        (if PermGood π G ∧ ¬∀ a b, capOf k k' π (f a) ≠ capOf k k' π (g b) then 1 else 0) ≤
      Fintype.card (X → Z) * Fintype.card (X → Z) *
        (Fintype.card A * Fintype.card B * (G + 1)) := by
  by_cases hG : PermGood π G
  · have hle : ∀ k k' : X → Z,
        (if PermGood π G ∧ ¬∀ a b, capOf k k' π (f a) ≠ capOf k k' π (g b) then 1 else 0) ≤
          ∑ a : A, ∑ b : B, (if capOf k k' π (f a) = capOf k k' π (g b) then 1 else 0) := by
      intro k k'
      split_ifs with h
      · obtain ⟨-, hn⟩ := h
        simp only [not_forall, not_not] at hn
        obtain ⟨a, b, hab⟩ := hn
        calc 1 = (if capOf k k' π (f a) = capOf k k' π (g b) then 1 else 0) :=
              (ite_eq_left hab).symm
          _ ≤ ∑ b' : B, (if capOf k k' π (f a) = capOf k k' π (g b') then 1 else 0) :=
              Finset.single_le_sum (f := fun b' ↦
                (if capOf k k' π (f a) = capOf k k' π (g b') then 1 else 0))
                (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ b)
          _ ≤ _ := Finset.single_le_sum (f := fun a' ↦ ∑ b' : B,
              (if capOf k k' π (f a') = capOf k k' π (g b') then 1 else 0))
              (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
      · exact Nat.zero_le _
    calc Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
          (if PermGood π G ∧ ¬∀ a b, capOf k k' π (f a) ≠ capOf k k' π (g b) then 1 else 0)
        ≤ Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z, ∑ a : A, ∑ b : B,
            (if capOf k k' π (f a) = capOf k k' π (g b) then 1 else 0) := by
          gcongr with k _ k' _
          exact hle k k'
      _ = ∑ a : A, ∑ b : B, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
            (if capOf k k' π (f a) = capOf k k' π (g b) then 1 else 0) := by
          rw [sum_comm_four]
          simp only [Finset.mul_sum]
      _ ≤ ∑ _a : A, ∑ _b : B, Fintype.card (X → Z) * Fintype.card (X → Z) * (G + 1) :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦
            card_mul_sum_capOf_eq_le π G hG (hfg a b)
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  · simp [hG]

end capCross

/-! ## The randomizer-base stages on leanXMSS tables -/

section r0

open HashSig LeanXmss

variable {J : Type} (cell : J → PublicParameter → MasterSeed → X) (ord : J ↪ ℕ)

/-- **The partial `h`-stage**: `h` at the capacity of each first label takes the label's `h`-slot,
which takes the block's output (rate plus `h`); the other slots stay. -/
noncomputable def stageHOn : CPub J × MasterSeed ≃ CPub J × MasterSeed :=
  (shufH.trans (stageNOn ord (posH cell) (shH cell))).trans shufH.symm

theorem stageHOn_spec (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (ps : PubSlots) (kc k'c : J → Z) (hc : J → X) (S : MasterSeed) :
    ∃ (h₂ : Z → X) (hc₂ : J → X),
      stageHOn cell ord (((⟨(h, k, k'), π, S₀⟩, ps), (kc, k'c, hc)), S) =
        (((⟨(h₂, k, k'), π, S₀⟩, ps), (kc, k'c, hc₂)), S) ∧
      (∀ a, IsFirst ord (fun b ↦ (π (cell b (trunc128 ps.2.1) S, kc b)).2 + k'c b) a →
        hc₂ a = (π (cell a (trunc128 ps.2.1) S, kc a)).1 +
          h ((π (cell a (trunc128 ps.2.1) S, kc a)).2 + k'c a) ∧
        h₂ ((π (cell a (trunc128 ps.2.1) S, kc a)).2 + k'c a) = hc a) ∧
      (∀ a, ¬IsFirst ord (fun b ↦ (π (cell b (trunc128 ps.2.1) S, kc b)).2 + k'c b) a →
        hc₂ a = hc a) ∧
      ∀ z, (∀ a, (π (cell a (trunc128 ps.2.1) S, kc a)).2 + k'c a ≠ z) → h₂ z = h z := by
  obtain ⟨p', hp', f1, f2, f3⟩ := stageNOn_spec ord (posH cell) (shH cell) (h, hc)
    (k, k', π, S₀, ps, kc, k'c, S)
  refine ⟨p'.1, p'.2, ?_, f1, f2, f3⟩
  rw [stageHOn, Equiv.trans_apply, Equiv.trans_apply, shufH_apply, hp', shufH_symm_apply]

/-- The randomizer-base stages: `k` and `k'` at every label, `h` at the first labels. -/
noncomputable def r0Stages : CPub J × MasterSeed ≃ CPub J × MasterSeed :=
  (stageK cell).trans ((stageK' cell).trans (stageHOn cell ord))

/-- **The randomizer-base stages**: they keep `π`, `S₀`, the public slots and the scheme seed.
When the labels' cells and their rates are distinct, the `k`- and `k'`-slots take `k`, `k'` at the
paths' cells; the `h`-slot of a first label (by capacity) takes the block's output, that of another
label stays; and the keys keep their values off the paths' cells. -/
theorem r0Stages_spec (L : HonestTable) (ps : PubSlots) (cs : CoinSlots J) (S : MasterSeed) :
    ∃ (h₂ : Z → X) (k₂ k'₂ : X → Z) (cs₂ : CoinSlots J),
      r0Stages cell ord (((L, ps), cs), S) =
        (((⟨(h₂, k₂, k'₂), L.perm, L.masterSeed⟩, ps), cs₂), S) ∧
      (∀ z, (∀ a, (L.perm (cell a (trunc128 ps.2.1) S, cs₂.1 a)).2 + cs₂.2.1 a ≠ z) →
        h₂ z = L.keys.1 z) ∧
      ∀ P, trunc128 ps.2.1 = P →
        Function.Injective (fun a ↦ cell a P S) →
        Function.Injective (fun a ↦ rateOf L.keys.2.1 L.perm (cell a P S)) →
        (∀ a, cs₂.1 a = L.keys.2.1 (cell a P S)) ∧
        (∀ a, cs₂.2.1 a = L.keys.2.2 (rateOf L.keys.2.1 L.perm (cell a P S))) ∧
        (∀ a, IsFirst ord (fun b ↦ capOf L.keys.2.1 L.keys.2.2 L.perm (cell b P S)) a →
          cs₂.2.2 a = rateOf L.keys.2.1 L.perm (cell a P S) +
            L.keys.1 (capOf L.keys.2.1 L.keys.2.2 L.perm (cell a P S))) ∧
        (∀ a, ¬IsFirst ord (fun b ↦ capOf L.keys.2.1 L.keys.2.2 L.perm (cell b P S)) a →
          cs₂.2.2 a = cs.2.2 a) ∧
        (∀ x, (∀ a, cell a P S ≠ x) → k₂ x = L.keys.2.1 x) ∧
        ∀ x, (∀ a, (L.perm (cell a P S, cs₂.1 a)).1 ≠ x) → k'₂ x = L.keys.2.2 x := by
  obtain ⟨⟨h, k, k'⟩, π, S₀⟩ := L
  obtain ⟨kc, k'c, hc⟩ := cs
  obtain ⟨k₂, kc₂, eK, fK⟩ := stageK_spec cell h k k' π S₀ ps kc k'c hc S
  obtain ⟨k'₂, k'c₂, eK', fK'⟩ := stageK'_spec cell h k₂ k' π S₀ ps kc₂ k'c hc S
  obtain ⟨h₂, hc₂, eH, fH1, fH2, fH3⟩ := stageHOn_spec cell ord h k₂ k'₂ π S₀ ps kc₂ k'c₂ hc S
  refine ⟨h₂, k₂, k'₂, (kc₂, k'c₂, hc₂), ?_, fH3, fun P hP hx hr ↦ ?_⟩
  · rw [r0Stages, Equiv.trans_apply, Equiv.trans_apply, eK, eK', eH]
  · subst hP
    obtain ⟨fK1, fK2⟩ := fK hx
    have hpr : ∀ a, (π (cell a (trunc128 ps.2.1) S, kc₂ a)).1 =
        rateOf k π (cell a (trunc128 ps.2.1) S) := fun a ↦ by rw [fK1 a, rateOf]
    obtain ⟨fK'1, fK'2⟩ := fK' fun a b hab ↦ hr ((hpr a).symm.trans (hab.trans (hpr b)))
    have hpc : ∀ a, (π (cell a (trunc128 ps.2.1) S, kc₂ a)).2 + k'c₂ a =
        capOf k k' π (cell a (trunc128 ps.2.1) S) := fun a ↦ by rw [fK'1 a, fK1 a, capOf]
    have hfun : (fun b ↦ (π (cell b (trunc128 ps.2.1) S, kc₂ b)).2 + k'c₂ b) =
        fun b ↦ capOf k k' π (cell b (trunc128 ps.2.1) S) := funext hpc
    rw [hfun] at fH1 fH2
    exact ⟨fK1, fun a ↦ (fK'1 a).trans (congrArg k' (hpr a)), fun a ha ↦ (fH1 a ha).1.trans
      (congrArg₂ (· + ·) (hpr a) (congrArg h (hpc a))), fH2, fK2, fK'2⟩

/-- **The staged swap with the randomizer-base stages**: the table with the scheme seed's and the
randomizer-base slots as the public part with the slots, and the scheme seed. -/
noncomputable def r0Split : CTab J ≃ CPub J × MasterSeed :=
  ((schemeSplit.prodCongr (Equiv.refl (CoinSlots J))).trans reorderC).trans (r0Stages cell ord)

theorem r0Split_apply (θ : CTab J) :
    r0Split cell ord θ = r0Stages cell ord
      ((((schemeSplit θ.1).1.1, (schemeSplit θ.1).1.2), θ.2), (schemeSplit θ.1).2) :=
  rfl

theorem r0Split_exists (θ : CTab J) : ∃ (h₂ : Z → X) (k₂ k'₂ : X → Z) (cs₂ : CoinSlots J),
    r0Split cell ord θ = (((⟨(h₂, k₂, k'₂), (schemeSplit θ.1).1.1.perm,
      (schemeSplit θ.1).1.1.masterSeed⟩, (schemeSplit θ.1).1.2), cs₂), (schemeSplit θ.1).2) := by
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, -⟩ := r0Stages_spec cell ord (schemeSplit θ.1).1.1
    (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  exact ⟨h₂, k₂, k'₂, cs₂, (r0Split_apply cell ord θ).trans hE⟩

/-- **The hidden coordinate is the scheme seed.** -/
theorem r0Split_snd (θ : CTab J) : (r0Split cell ord θ).2 = θ.1.1.seed := by
  obtain ⟨_, _, _, _, hE⟩ := r0Split_exists cell ord θ
  rw [hE]
  exact schemeSplit_snd θ.1

theorem r0Split_perm (θ : CTab J) : (r0Split cell ord θ).1.1.1.perm = θ.1.1.perm := by
  obtain ⟨_, _, _, _, hE⟩ := r0Split_exists cell ord θ
  rw [hE]
  exact schemeSplit_perm θ.1

theorem r0Split_masterSeed (θ : CTab J) :
    (r0Split cell ord θ).1.1.1.masterSeed = θ.1.1.masterSeed := by
  obtain ⟨_, _, _, _, hE⟩ := r0Split_exists cell ord θ
  rw [hE]
  exact schemeSplit_masterSeed θ.1

/-- The randomizer-base stages keep the public slots. -/
theorem r0Split_slots (θ : CTab J) : (r0Split cell ord θ).1.1.2 = (schemeSplit θ.1).1.2 := by
  obtain ⟨_, _, _, _, hE⟩ := r0Split_exists cell ord θ
  rw [hE]

/-- The randomizer-base coordinate of a label: the first `128` bits of its `h`-slot. The other
`960` bits are a pad. -/
def r0Coord (y : CPub J) (a : J) : Digest :=
  trunc128 (y.2.2.2 a)

/-- An `h`-slot split into its randomizer-base coordinate (the first `128` bits) and the pad. -/
def r0SlotEquiv : X ≃ Digest × (Fin 960 → ZMod 2) :=
  (Fin.appendEquiv 128 960).symm.trans ((bitsEquiv 128).symm.prodCongr (Equiv.refl _))

theorem r0SlotEquiv_fst (x : X) : (r0SlotEquiv x).1 = trunc128 x := by
  rw [trunc128_eq]
  rfl

/-- **The non-first labels of a table**: a label of smaller rank has the same randomizer-base
capacity. -/
def r0B (L : HonestTable) : Set J :=
  {a | ∃ b, ord b < ord a ∧ coinCellH cell L b = coinCellH cell L a}

theorem mem_r0B {L : HonestTable} {a : J} :
    a ∈ r0B cell ord L ↔ ¬IsFirst ord (coinCellH cell L) a := by
  simp only [r0B, Set.mem_ofPred_eq, IsFirst, not_forall, not_not, exists_prop]

/-- The non-first labels read off the coordinates, by the capacities `pubCellH` the `h`-stage
exchanges at. -/
def pubB (y : CPub J × MasterSeed) : Set J :=
  {a | ∃ b, ord b < ord a ∧ pubCellH cell y b = pubCellH cell y a}

/-- The capacities read off the coordinates are the `h`-stage's cells, for the data it keeps. -/
theorem pubCellH_eq_posH (y : CPub J × MasterSeed) : pubCellH cell y = posH cell (shufH y).2 :=
  rfl

/-- **The non-first labels read off the coordinates are the `h`-stage's non-first labels.** -/
theorem mem_pubB {y : CPub J × MasterSeed} {a : J} :
    a ∈ pubB cell ord y ↔ ¬IsFirst ord (posH cell (shufH y).2) a := by
  rw [← pubCellH_eq_posH]
  simp only [pubB, Set.mem_ofPred_eq, IsFirst, not_forall, not_not, exists_prop]

/-- The randomizer-base capacities avoid the hidden capacities of `schemeSplit`. -/
abbrev CapSep (x : Pub × MasterSeed) : Prop :=
  ∀ a b, capOf x.1.1.keys.2.1 x.1.1.keys.2.2 x.1.1.perm (cell a (pubParam x.1) x.2) ≠
    posOf x.1 x.2 b

/-- **No static collisions of the randomizer-base paths**: their rates are distinct and their
capacities avoid the hidden capacities. Their capacities may collide with each other. -/
def R0Coll (x : Pub × MasterSeed) : Prop :=
  RateInj cell x ∧ CapSep cell x

theorem cell_injective_of {cell : J → PublicParameter → MasterSeed → X}
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1) (P : PublicParameter)
    (S : MasterSeed) : Function.Injective fun a ↦ cell a P S :=
  fun a a' h ↦ congrArg Prod.snd (hcell P (a₁ := (S, a)) (a₂ := (S, a')) h)

/-- **The transfer facts**: when the hidden capacities are distinct, the labels' cells are
distinct and `R0Coll` holds, the public part gives the parameter, the `k`- and `k'`-slots hold the
table's `k` and `k'` at the paths' cells, the `h`-slot of a first label holds the block's output,
and that of a non-first label the table's pad. -/
theorem r0Split_transfer (θ : CTab J)
    (hinj : Function.Injective (posOf (schemeSplit θ.1).1 (schemeSplit θ.1).2))
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hcoll : R0Coll cell (schemeSplit θ.1)) :
    pubParam (r0Split cell ord θ).1.1 = θ.1.1.param ∧
      (∀ a, (r0Split cell ord θ).1.2.1 a = θ.1.1.keys.2.1 (coinCellK cell θ.1.1 a)) ∧
      (∀ a, (r0Split cell ord θ).1.2.2.1 a = θ.1.1.keys.2.2 (coinCellK' cell θ.1.1 a)) ∧
      (∀ a, a ∉ r0B cell ord θ.1.1 → (r0Split cell ord θ).1.2.2.2 a =
        rateOf θ.1.1.keys.2.1 θ.1.1.perm (coinCellK cell θ.1.1 a) +
          θ.1.1.keys.1 (coinCellH cell θ.1.1 a)) ∧
      ∀ a, a ∈ r0B cell ord θ.1.1 → (r0Split cell ord θ).1.2.2.2 a = θ.2.2.2 a := by
  obtain ⟨hP, -, hh⟩ := schemeSplit_transfer θ.1 hinj
  have hS := schemeSplit_snd θ.1
  have hk := schemeSplit_keys_snd θ.1
  have hπ := schemeSplit_perm θ.1
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, -, f⟩ := r0Stages_spec cell ord (schemeSplit θ.1).1.1
    (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  obtain ⟨f1, f2, f3, f4, -, -⟩ := f (pubParam (schemeSplit θ.1).1) rfl
    (cell_injective_of hcell _ _) hcoll.1
  have hcap : (fun b ↦ capOf (schemeSplit θ.1).1.1.keys.2.1 (schemeSplit θ.1).1.1.keys.2.2
      (schemeSplit θ.1).1.1.perm (cell b (pubParam (schemeSplit θ.1).1) (schemeSplit θ.1).2)) =
        coinCellH cell θ.1.1 := funext fun b ↦ by
    rw [hk, hπ, hP, hS]
    rfl
  rw [hcap] at f3 f4
  rw [r0Split_apply, hE]
  refine ⟨hP, fun a ↦ (f1 a).trans ?_, fun a ↦ (f2 a).trans ?_, fun a ha ↦
    (f3 a (not_not.mp fun h ↦ ha ((mem_r0B cell ord).mpr h))).trans ?_,
    fun a ha ↦ f4 a ((mem_r0B cell ord).mp ha)⟩
  · rw [hk, hP, hS]
    rfl
  · rw [hk, hπ, hP, hS]
    rfl
  · rw [hh _ fun b hb ↦ hcoll.2 a b hb.symm, hk, hπ, hP, hS]
    rfl

/-- The keys of the public part agree with those after `schemeSplit` off the randomizer-base
cells read off the public part. -/
theorem r0Split_keys_eq (θ : CTab J)
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hrate : RateInj cell (schemeSplit θ.1)) :
    (∀ x, (∀ a, pubCellK cell (r0Split cell ord θ) a ≠ x) →
        (r0Split cell ord θ).1.1.1.keys.2.1 x = (schemeSplit θ.1).1.1.keys.2.1 x) ∧
      (∀ x, (∀ a, pubCellK' cell (r0Split cell ord θ) a ≠ x) →
        (r0Split cell ord θ).1.1.1.keys.2.2 x = (schemeSplit θ.1).1.1.keys.2.2 x) ∧
      ∀ z, (∀ a, pubCellH cell (r0Split cell ord θ) a ≠ z) →
        (r0Split cell ord θ).1.1.1.keys.1 z = (schemeSplit θ.1).1.1.keys.1 z := by
  obtain ⟨h₂, k₂, k'₂, cs₂, hE, f6, f⟩ := r0Stages_spec cell ord (schemeSplit θ.1).1.1
    (schemeSplit θ.1).1.2 θ.2 (schemeSplit θ.1).2
  obtain ⟨-, -, -, -, f4, f5⟩ := f (pubParam (schemeSplit θ.1).1) rfl
    (cell_injective_of hcell _ _) hrate
  rw [r0Split_apply, hE]
  exact ⟨f4, f5, f6⟩

/-! ### The good set and the coordinate facts -/

variable {ι : Type} {β : ι → Type}

variable [Fintype J] [DecidableEq J]

open scoped Classical in
/-- **The good set** of the randomizer-base stages: `schemeGood`, no static collision of the
randomizer-base paths (`R0Coll`), and no computation reading a randomizer-base cell (`ReadGood`).
Irreducible: its membership does not unfold to the enumeration of all tables. -/
@[irreducible]
noncomputable def r0Good
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Finset (CTab J) :=
  Finset.univ.filter fun θ ↦
    GoodPS Q (schemeSplit θ.1) ∧ R0Coll cell (schemeSplit θ.1) ∧
      ReadGood cell Q (r0Split cell ord θ)

variable {cell ord}

theorem mem_r0Good
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab J} :
    θ ∈ r0Good cell ord Q ↔ GoodPS Q (schemeSplit θ.1) ∧ R0Coll cell (schemeSplit θ.1) ∧
      ReadGood cell Q (r0Split cell ord θ) := by
  unfold r0Good
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

section coords

variable {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
  (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
  {θ : CTab J} (hθ : θ ∈ r0Good cell ord Q)

include hcell hθ

/-- **The coordinate facts**: on the good set, the public part gives the parameter, the `k`- and
`k'`-slots hold the table's `k` and `k'` at the paths' cells, the `h`-slot of a first label holds
the block's output, and that of a non-first label the table's pad. -/
theorem r0Split_coords :
    pubParam (r0Split cell ord θ).1.1 = θ.1.1.param ∧
      (∀ a, (r0Split cell ord θ).1.2.1 a = θ.1.1.keys.2.1 (coinCellK cell θ.1.1 a)) ∧
      (∀ a, (r0Split cell ord θ).1.2.2.1 a = θ.1.1.keys.2.2 (coinCellK' cell θ.1.1 a)) ∧
      (∀ a, a ∉ r0B cell ord θ.1.1 → (r0Split cell ord θ).1.2.2.2 a =
        rateOf θ.1.1.keys.2.1 θ.1.1.perm (coinCellK cell θ.1.1 a) +
          θ.1.1.keys.1 (coinCellH cell θ.1.1 a)) ∧
      ∀ a, a ∈ r0B cell ord θ.1.1 → (r0Split cell ord θ).1.2.2.2 a = θ.2.2.2 a := by
  obtain ⟨⟨hinj, -⟩, hcoll, -⟩ := mem_r0Good.mp hθ
  exact r0Split_transfer cell ord θ hinj hcell hcoll

/-- On the good set, the capacities read off the coordinates are the table's randomizer-base
capacities. -/
theorem pubCellH_r0Split (a : J) :
    pubCellH cell (r0Split cell ord θ) a = coinCellH cell θ.1.1 a := by
  obtain ⟨hP, h1, h2, -, -⟩ := r0Split_coords hcell hθ
  simp only [pubCellH, pubCellK]
  rw [r0Split_perm, hP, r0Split_snd, h1 a, h2 a]
  rfl

/-- **The non-first sets agree**: on the good set, the non-first labels read off the coordinates
(the `h`-stage's) are the table's `r0B`. -/
theorem pubB_r0Split : pubB cell ord (r0Split cell ord θ) = r0B cell ord θ.1.1 := by
  ext a
  simp only [pubB, r0B, Set.mem_ofPred_eq, pubCellH_r0Split hcell hθ]

/-- **The paths' hashes at the first labels**: on the good set, the hash of a label's one-block
input (first block `cell a P S`) is read off its `h`-slot, for a first label. -/
theorem r0Split_hash (inp : J → PublicParameter → MasterSeed → HashInput)
    (hinp : ∀ a P S, firstCell (inp a P S) = cell a P S) (hlen : ∀ a P S, (inp a P S).length < 136)
    (a : J) (ha : a ∉ r0B cell ord θ.1.1) :
    θ.1.1.hash (inp a θ.1.1.param θ.1.1.seed) = out256 ((r0Split cell ord θ).1.2.2.2 a) := by
  rw [hash_of_lt θ.1.1 _ (hlen _ _ _), hinp, (r0Split_coords hcell hθ).2.2.2.1 a ha]
  rfl

/-- **The digests at the first labels are the coordinates**: on the good set, the digest of a first
label's one-block input is its coordinate `r0Coord`. -/
theorem digest_eq_r0Coord (inp : J → PublicParameter → MasterSeed → HashInput)
    (hinp : ∀ a P S, firstCell (inp a P S) = cell a P S) (hlen : ∀ a P S, (inp a P S).length < 136)
    (a : J) (ha : a ∉ r0B cell ord θ.1.1) :
    θ.1.1.digest (inp a θ.1.1.param θ.1.1.seed) = r0Coord (r0Split cell ord θ).1 a :=
  congrArg truncateHash (r0Split_hash hcell hθ inp hinp hlen a ha)

/-- **On the good set, the challenger's data is a function of the public part.** -/
theorem schemeData_eq_pubData_r0Split :
    schemeData Q θ.1.1 = pubData Q (r0Split cell ord θ).1.1 := by
  obtain ⟨hgood, hcoll, hread⟩ := mem_r0Good.mp hθ
  rw [schemeData_eq_of_mem (mem_schemeGood.mpr hgood)]
  obtain ⟨g4, g5, g6⟩ := r0Split_keys_eq cell ord θ hcell hcoll.1
  have hsl := r0Split_slots cell ord θ
  have hπ : (r0Split cell ord θ).1.1.1.perm = (schemeSplit θ.1).1.1.perm :=
    (r0Split_perm cell ord θ).trans (schemeSplit_perm θ.1).symm
  have hP : pubParam (r0Split cell ord θ).1.1 = pubParam (schemeSplit θ.1).1 :=
    congrArg (fun s : PubSlots ↦ trunc128 s.2.1) hsl
  have hC : pubCs (r0Split cell ord θ).1.1 = pubCs (schemeSplit θ.1).1 :=
    congrArg (fun (s : PubSlots) (j : CsIdx) ↦ out256 (s.2.2 j)) hsl
  funext i
  change honestEval (schemeSplit θ.1).1.1.keys (schemeSplit θ.1).1.1.perm
      (Q i (pubParam (schemeSplit θ.1).1) (pubCs (schemeSplit θ.1).1)) =
    honestEval (r0Split cell ord θ).1.1.1.keys (r0Split cell ord θ).1.1.1.perm
      (Q i (pubParam (r0Split cell ord θ).1.1) (pubCs (r0Split cell ord θ).1.1))
  rw [← hP, ← hC, ← hπ]
  refine honestEval_congr (t := (r0Split cell ord θ).1.1.1.keys)
    (t' := (schemeSplit θ.1).1.1.keys) (r0Split cell ord θ).1.1.1.perm _ fun e he ↦ ?_
  have ha := honestEval_answeredBy (r0Split cell ord θ).1.1.1.perm
    (r0Split cell ord θ).1.1.1.keys _ e he
  cases e with
  | h z v =>
    have hz : ∀ a, pubCellH cell (r0Split cell ord θ) a ≠ z := fun a hza ↦
      (hread i a).2.2 (by rw [hza]; exact mem_hCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g6 z hz]
    exact ha
  | k x v =>
    have hx : ∀ a, pubCellK cell (r0Split cell ord θ) a ≠ x := fun a hxa ↦
      (hread i a).1 (by rw [hxa]; exact mem_kCells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g4 x hx]
    exact ha
  | k' x v =>
    have hx : ∀ a, pubCellK' cell (r0Split cell ord θ) a ≠ x := fun a hxa ↦
      (hread i a).2.1 (by rw [hxa]; exact mem_k'Cells.mpr ⟨v, he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← g5 x hx]
    exact ha

end coords

/-! ### The bad fraction -/

open scoped Classical

variable (cell ord) (G : ℕ)

/-- Colliding randomizer-base rates (any permutation). -/
noncomputable def rateBadAll (x : Pub × MasterSeed) : ℕ :=
  if ¬RateInj cell x then 1 else 0

/-- A good permutation and a randomizer-base capacity on a hidden capacity. -/
noncomputable def capSepBad (x : Pub × MasterSeed) : ℕ :=
  if PermGood x.1.1.perm G ∧ ¬CapSep cell x then 1 else 0

/-- A static collision of the randomizer-base paths. -/
noncomputable def r0CollBad (x : Pub × MasterSeed) : ℕ :=
  rateBadAll cell x + capSepBad cell G x

/-- The coordinates other than `π`: the keys, `S₀`, the public slots, and the scheme seed. -/
abbrev RestPi : Type := SpongeKeys X Z × MasterSeed × PubSlots × MasterSeed

/-- The public part and the scheme seed as `(π, rest)`. -/
def coordPi : Equiv.Perm (X × Z) × RestPi ≃ Pub × MasterSeed where
  toFun c := ((⟨c.2.1, c.1, c.2.2.1⟩, c.2.2.2.1), c.2.2.2.2)
  invFun x := (x.1.1.perm, (x.1.1.keys, x.1.1.masterSeed, x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Randomizer-base rate collisions, averaged over `π`**: at most `|J|² / |X|` of the
coordinates. -/
theorem card_mul_sum_rateBadAll_le
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1) :
    Fintype.card X * ∑ x, rateBadAll cell x ≤
      Fintype.card (Pub × MasterSeed) * (Fintype.card J * Fintype.card J) := by
  exact card_mul_sum_equiv_prod_le coordPi _ _ (rateBadAll cell) fun r ↦
    card_mul_sum_not_injective_rate_le
      (fun a ↦ (cell a (trunc128 r.2.2.1.2.1) r.2.2.2,
        r.1.2.1 (cell a (trunc128 r.2.2.1.2.1) r.2.2.2)))
      fun a a' h ↦ cell_injective_of hcell _ _ (congrArg Prod.fst h)

omit [DecidableEq J] in
theorem capSepBad_coordS (ω : Coord) (S : MasterSeed) (k k' : X → Z) :
    capSepBad cell G (coordS (((ω, S), k), k')) =
      (if PermGood ω.1 G ∧ ¬∀ a b, capOf k k' ω.1 (cell a (trunc128 ω.2.2.1.2.1) S) ≠
        capOf k k' ω.1 (hidCell (trunc128 ω.2.2.1.2.1) S ω.2.2.2 b) then 1 else 0) :=
  rfl

omit [DecidableEq J] in
/-- **Randomizer-base capacities on hidden capacities**: at most `|J| |A| (G + 1) / |Z|` of the
coordinates, `A = Option (Option CsIdx)`. -/
theorem card_mul_sum_capSepBad_le (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    Fintype.card Z * ∑ x, capSepBad cell G x ≤
      Fintype.card Tab * (Fintype.card J * Fintype.card (Option (Option CsIdx)) * (G + 1)) := by
  rw [sum_eq_sum_coords coordS (capSepBad cell G), card_tab_eq]
  have h : Fintype.card Z * ∑ ω : Coord, ∑ S : MasterSeed, ∑ k : X → Z, ∑ k' : X → Z,
      capSepBad cell G (coordS (((ω, S), k), k')) =
        ∑ ω : Coord, ∑ S : MasterSeed, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
          (if PermGood ω.1 G ∧ ¬∀ a b, capOf k k' ω.1 (cell a (trunc128 ω.2.2.1.2.1) S) ≠
            capOf k k' ω.1 (hidCell (trunc128 ω.2.2.1.2.1) S ω.2.2.2 b) then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    simp only [capSepBad_coordS]
  rw [h]
  exact sum_sum_le_mul _ _ _ fun ω S ↦ card_mul_sum_capOf_cross_le ω.1 G _ _
    fun a b ↦ (hsep _ S ω.2.2.2 a b).symm

/-- The tables outside the good set: outside `schemeGood`, a bad permutation, a static collision
of the randomizer-base paths, or a computation reading a randomizer-base cell. -/
theorem card_sub_card_r0Good_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Fintype.card (CTab J) - (r0Good cell ord Q).card ≤
      ∑ θ : CTab J, ((schemeBad Q θ.1 + permBad G θ.1) + (r0CollBad cell G (schemeSplit θ.1) +
        ∑ i, (readK cell Q i (r0Split cell ord θ) + readKH cell G Q i (r0Split cell ord θ)))) := by
  refine card_sub_card_le_sum (r0Good cell ord Q) _ fun θ hθ ↦ ?_
  rw [mem_r0Good] at hθ
  by_cases hs : θ.1 ∈ schemeGood Q
  · by_cases hG : PermGood θ.1.1.perm G
    · by_cases hcoll : R0Coll cell (schemeSplit θ.1)
      · have hread : ¬ReadGood cell Q (r0Split cell ord θ) :=
          fun h ↦ hθ ⟨mem_schemeGood.mp hs, hcoll, h⟩
        obtain ⟨i, a, hia⟩ : ∃ i a,
            ¬(pubCellK cell (r0Split cell ord θ) a ∉
                kCells (pubData Q (r0Split cell ord θ).1.1 i).2 ∧
              pubCellK' cell (r0Split cell ord θ) a ∉
                k'Cells (pubData Q (r0Split cell ord θ).1.1 i).2 ∧
              pubCellH cell (r0Split cell ord θ) a ∉
                hCells (pubData Q (r0Split cell ord θ).1.1 i).2) := by
          by_contra hne
          exact hread fun i a ↦ by_contra fun h ↦ hne ⟨i, a, h⟩
        have hG' : PermGood (r0Split cell ord θ).1.1.1.perm G := by
          rw [r0Split_perm]
          exact hG
        have hk : kHit cell Q i a (r0Split cell ord θ) ≤ readK cell Q i (r0Split cell ord θ) :=
          Finset.single_le_sum (f := fun a' ↦ kHit cell Q i a' (r0Split cell ord θ))
            (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        have hkh : k'Hit cell G Q i a (r0Split cell ord θ) + hHit cell Q i a (r0Split cell ord θ) ≤
            readKH cell G Q i (r0Split cell ord θ) :=
          Finset.single_le_sum (f := fun a' ↦ k'Hit cell G Q i a' (r0Split cell ord θ) +
            hHit cell Q i a' (r0Split cell ord θ)) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
        have h1 : 1 ≤ readK cell Q i (r0Split cell ord θ) +
            readKH cell G Q i (r0Split cell ord θ) := by
          by_cases m1 : pubCellK cell (r0Split cell ord θ) a ∈
              kCells (pubData Q (r0Split cell ord θ).1.1 i).2
          · have : kHit cell Q i a (r0Split cell ord θ) = 1 := ite_eq_left m1
            omega
          · by_cases m2 : pubCellK' cell (r0Split cell ord θ) a ∈
                k'Cells (pubData Q (r0Split cell ord θ).1.1 i).2
            · have : k'Hit cell G Q i a (r0Split cell ord θ) = 1 := ite_eq_left ⟨hG', m2⟩
              omega
            · have m3 : pubCellH cell (r0Split cell ord θ) a ∈
                  hCells (pubData Q (r0Split cell ord θ).1.1 i).2 :=
                by_contra fun m3 ↦ hia ⟨m1, m2, m3⟩
              have : hHit cell Q i a (r0Split cell ord θ) = 1 := ite_eq_left m3
              omega
        have h2 : readK cell Q i (r0Split cell ord θ) + readKH cell G Q i (r0Split cell ord θ) ≤
            ∑ i', (readK cell Q i' (r0Split cell ord θ) +
              readKH cell G Q i' (r0Split cell ord θ)) :=
          Finset.single_le_sum (f := fun i' ↦ readK cell Q i' (r0Split cell ord θ) +
            readKH cell G Q i' (r0Split cell ord θ)) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ i)
        omega
      · have hG' : PermGood (schemeSplit θ.1).1.1.perm G := by
          rw [schemeSplit_perm]
          exact hG
        have h1 : 1 ≤ r0CollBad cell G (schemeSplit θ.1) := by
          by_cases hr : RateInj cell (schemeSplit θ.1)
          · have : capSepBad cell G (schemeSplit θ.1) = 1 :=
              ite_eq_left ⟨hG', fun hc ↦ hcoll ⟨hr, hc⟩⟩
            unfold r0CollBad
            omega
          · have : rateBadAll cell (schemeSplit θ.1) = 1 := ite_eq_left hr
            unfold r0CollBad
            omega
        omega
    · have : permBad G θ.1 = 1 := ite_eq_left hG
      omega
  · have : schemeBad Q θ.1 = 1 := ite_eq_right hs
    omega

/-- **The bad fraction of the randomizer-base stages**: the fraction of tables outside
`r0Good cell ord Q` is at most the fraction outside `schemeGood Q`, plus the fraction of
permutations with a rate count above `G`, plus the rate collisions `|J|² / |X|` (averaged over the
permutation), plus the capacity hits `|J| |A| (G + 1) / |Z|` (`A = Option (Option CsIdx)`), plus per
computation `qs₂ᵢ / 2^256 + |J| (G + 1) qᵢ / |Z|`, where `qᵢ` bounds the reads of `Q i` and `qs₂ᵢ`
its reads at `k`-cells of the form `cell a P S`. The labels' first blocks are distinct for distinct
labels or seeds (`hcell`) and differ from the hidden cells (`hsep`). -/
theorem r0Good_frac_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₂ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₂ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ a S, cell a P S = x).card ≤ qs₂ i)
    (hcell : ∀ P, Function.Injective fun s : MasterSeed × J ↦ cell s.2 P s.1)
    (hsep : ∀ P S S₀ a b, hidCell P S S₀ b ≠ cell a P S) :
    (Fintype.card (CTab J) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (CTab J) - (r0Good cell ord Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        (((Fintype.card J * Fintype.card J : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((Fintype.card J * Fintype.card (Option (Option CsIdx)) * (G + 1) : ℕ) : ℝ≥0∞) /
            Fintype.card Z) +
        ∑ i, ((qs₂ i : ℝ≥0∞) / 2 ^ 256 + Fintype.card J * (G + 1) * q i / Fintype.card Z) := by
  refine inv_mul_le_of_parts Fintype.card_ne_zero
    ((card_sub_card_r0Good_le cell ord G Q).trans_eq (sum_add_sum_eq _ _ _ _)) ?_ ?_ ?_ ?_
  · rw [Finset.sum_add_distrib, Nat.cast_add, mul_add]
    refine add_le_add (le_of_eq ?_) ?_
    · have hs : ∑ t, schemeBad Q t = Fintype.card Tab - (schemeGood Q).card :=
        sum_ite_mem_zero_one_eq (schemeGood Q)
      rw [sum_fst_eq (schemeBad Q), hs]
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
    calc ((∑ θ : CTab J, r0CollBad cell G (schemeSplit θ.1) : ℕ) : ℝ≥0∞)
        = ((∑ θ : CTab J, rateBadAll cell (schemeSplit θ.1) : ℕ) : ℝ≥0∞) +
            ((∑ θ : CTab J, capSepBad cell G (schemeSplit θ.1) : ℕ) : ℝ≥0∞) := by
          rw [← Nat.cast_add, ← Finset.sum_add_distrib]
          rfl
      _ ≤ _ := (add_le_add h1 h2).trans_eq (mul_add _ _ _).symm
  · intro i
    have h := natCast_le_mul_div_of_mul_le (Fintype.card_ne_zero (α := MasterSeed))
      (card_mul_sum_equiv_le (r0Split cell ord) (readK cell Q i) _ _
        (card_mul_sum_readK_le cell Q qs₂ hcell hqs₂ i))
    rwa [card_masterSeed, Nat.cast_pow, Nat.cast_ofNat] at h
  · intro i
    have h := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
      (card_mul_sum_equiv_le (r0Split cell ord) (readKH cell G Q i) _ _
        (card_mul_sum_readKH_le cell G Q q hq i))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    exact h

end r0

/-! ## leanXMSS's randomizer-base labels -/

namespace R0

open HashSig LeanXmss
open LeanVM.Protocol.KeccakHash (padBlock)

/-- A randomizer-base label: a bottom key with a request message, or a top key with a bottom
root. -/
abbrev RLabel : Type := (KeyIndex × Message) ⊕ (KeyIndex × Digest)

/-- The layer of a label. -/
def RLabel.layer : RLabel → Layer
  | .inl _ => bottomLayer
  | .inr _ => topLayer

/-- The key of a label. -/
def RLabel.key : RLabel → KeyIndex
  | .inl (e, _) => e
  | .inr (e, _) => e

/-- The message bytes of a label: `32` bytes at the bottom, `16` at the top. -/
def RLabel.msg : RLabel → HashInput
  | .inl (_, m) => littleEndianBytes 32 m
  | .inr (_, d) => littleEndianBytes 16 d

/-- A label as CoinStage's `(layer, key, message)`. -/
def rLab (a : RLabel) : Layer × KeyIndex × HashInput :=
  (a.layer, a.key, a.msg)

/-- A rank of the labels. -/
noncomputable def rOrd : RLabel ↪ ℕ :=
  (Fintype.equivFin RLabel).toEmbedding.trans Fin.valEmbedding

/-- The `S`-keyed first block of a label's randomizer-base derivation. -/
abbrev rCell : RLabel → PublicParameter → MasterSeed → X :=
  rbCell rLab

theorem leBytes_injective (n : ℕ) : Function.Injective (littleEndianBytes n) := by
  intro v w h
  apply BitVec.eq_of_getLsbD_eq
  intro j _
  have := congrArg (inputBit · j) h
  simp only [inputBit_littleEndianBytes] at this
  exact bitOf_injective this

theorem length_msg_le (a : RLabel) : a.msg.length ≤ 32 := by
  cases a with
  | inl x => exact (length_littleEndianBytes 32 x.2).le
  | inr x => exact (length_littleEndianBytes 16 x.2).le.trans (by norm_num)

/-- The coin slots of leanXMSS's labels are finite. -/
noncomputable instance instFintypeCoinSlotsRLabel : Fintype (CoinSlots RLabel) :=
  instFintypeProd _ _

theorem length_rbInput (a : RLabel) (P : PublicParameter) (S : MasterSeed) :
    (rbInput rLab a P S).length < 136 := by
  have h := length_msg_le a
  change (thInput P _ (littleEndianBytes 32 S ++ a.msg)).length < 136
  rw [length_thInput, List.length_append, length_littleEndianBytes]
  omega

theorem rCell_eq (a : RLabel) (P : PublicParameter) (S : MasterSeed) :
    rCell a P S = blockOf (padBlock (rbInput rLab a P S)) := by
  change blockOf (firstBlock _) = _
  rw [firstBlock_of_lt _ (length_rbInput a P S)]

theorem fieldsOfCell_rCell (a : RLabel) (P : PublicParameter) (S : MasterSeed) :
    fieldsOfCell (rCell a P S) = tweakFields 7 0 (layerHi a.layer 0) a.key :=
  fieldsOfCell_thInput _ _ _ (by rw [List.length_append, length_littleEndianBytes]; omega)

theorem not_seedShaped_rCell (a : RLabel) (P : PublicParameter) (S : MasterSeed) :
    ¬SeedShaped (rCell a P S) := by
  rw [rCell_eq]
  refine not_seedShaped_padBlock _ ?_ (length_rbInput a P S)
  change 40 < (thInput P _ (littleEndianBytes 32 S ++ a.msg)).length
  rw [length_thInput, List.length_append, length_littleEndianBytes]
  omega

/-- **The randomizer-base cells are distinct**: a label's first block names its seed and its
label. -/
theorem rCell_injective (P : PublicParameter) :
    Function.Injective fun s : MasterSeed × RLabel ↦ rCell s.2 P s.1 := by
  rintro ⟨S, a⟩ ⟨S', a'⟩ h
  have h' : rCell a P S = rCell a' P S' := h
  rw [rCell_eq, rCell_eq] at h'
  have h1 := padBlock_injective (length_rbInput a P S) (length_rbInput a' P S') h'
  obtain ⟨hf, hp⟩ := thInput_injective P h1
  obtain ⟨hS, hm⟩ := List.append_inj hp
    (by rw [length_littleEndianBytes, length_littleEndianBytes])
  have hl : a.layer = a'.layer := by
    have hhi : BitVec.ofNat 24 (layerHi a.layer 0) = BitVec.ofNat 24 (layerHi a'.layer 0) :=
      congrArg TweakFields.hi hf
    rw [← layerOf_layerHi a.layer 0 (by norm_num), hhi, layerOf_layerHi _ 0 (by norm_num)]
  have he : a.key = a'.key := by
    have hlo : BitVec.ofNat 32 a.key.val = BitVec.ofNat 32 a'.key.val := congrArg TweakFields.lo hf
    rw [← keyOf_ofNat a.key, hlo, keyOf_ofNat]
  have hm' : a.msg = a'.msg := hm
  have ha : a = a' := by
    rcases a with ⟨e, m⟩ | ⟨e, d⟩ <;> rcases a' with ⟨e', m'⟩ | ⟨e', d'⟩
    · have he' : e = e' := he
      rw [he', leBytes_injective 32 hm']
    · exact ((show bottomLayer ≠ topLayer by decide) hl).elim
    · exact ((show topLayer ≠ bottomLayer by decide) hl).elim
    · have he' : e = e' := he
      rw [he', leBytes_injective 16 hm']
  rw [leBytes_injective 32 hS, ha]

/-- **The randomizer-base cells are not hidden cells**: the seed derivation's cell is seed-shaped,
and the seed-keyed cells carry other tweak tags. -/
theorem hidCell_ne_rCell (P : PublicParameter) (S S₀ : MasterSeed) (a : RLabel)
    (b : Option (Option CsIdx)) : hidCell P S S₀ b ≠ rCell a P S := by
  intro h
  cases b with
  | none =>
    have h' : seedCell S₀ = rCell a P S := h
    exact not_seedShaped_rCell a P S (h' ▸ seedShaped_seedCell S₀)
  | some c =>
    have h' : skCell P S c = rCell a P S := h
    have hf := congrArg fieldsOfCell h'
    rw [fieldsOfCell_skCell, fieldsOfCell_rCell] at hf
    have ht := congrArg TweakFields.tag hf
    cases c <;> simp [keygenDomainFields, tweakFields] at ht

variable {ι : Type} {β : ι → Type}

/-- **The randomizer bases at the first labels are the coordinates**: on the good set, the
randomizer base `R0(l, e, M)` of a first label is its coordinate `r0Coord`. -/
theorem randomizerBase_eq_r0Coord
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)}
    {θ : CTab RLabel} (hθ : θ ∈ r0Good rCell rOrd Q) (a : RLabel)
    (ha : a ∉ r0B rCell rOrd θ.1.1) :
    θ.1.1.randomizerBase a.layer a.key a.msg = r0Coord (r0Split rCell rOrd θ).1 a :=
  digest_eq_r0Coord rCell_injective hθ (rbInput rLab) (fun _ _ _ ↦ rfl)
    (fun a P S ↦ length_rbInput a P S) a ha

/-- **The bad fraction of the randomizer-base stages for leanXMSS's labels.** -/
theorem r0Good_frac_le_rLabel [Fintype ι] (G : ℕ)
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₂ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₂ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ a S, rCell a P S = x).card ≤
        qs₂ i) :
    (Fintype.card (CTab RLabel) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (CTab RLabel) - (r0Good rCell rOrd Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        (((Fintype.card RLabel * Fintype.card RLabel : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((Fintype.card RLabel * Fintype.card (Option (Option CsIdx)) * (G + 1) : ℕ) : ℝ≥0∞) /
            Fintype.card Z) +
        ∑ i, ((qs₂ i : ℝ≥0∞) / 2 ^ 256 + Fintype.card RLabel * (G + 1) * q i / Fintype.card Z) :=
  r0Good_frac_le rCell rOrd G Q q qs₂ hq hqs₂ rCell_injective hidCell_ne_rCell

/-! ### At Keccak's sizes -/

theorem card_bitVec_eq (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]

set_option exponentiation.threshold 4096 in
theorem card_rLabel : Fintype.card RLabel = 2 ^ 288 + 2 ^ 160 := by
  simp only [RLabel, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_bitVec_eq]
  norm_num [lifetime, layerCount, layerHeight, digestBits]

theorem card_hidIdx : Fintype.card (Option (Option CsIdx)) = 2 + 2 * 2 ^ 32 * 29 := by
  simp only [Fintype.card_option, CsIdx, Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, lifetime, chainCount, layerHeight]

theorem card_rate : Fintype.card X = 2 ^ 1088 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_cap : Fintype.card Z = 2 ^ 512 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem natCast_div_eq_ofReal (a b : ℕ) (hb : 0 < b) :
    (a : ℝ≥0∞) / b = ENNReal.ofReal ((a : ℝ) / b) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

set_option exponentiation.threshold 4096 in
/-- **The static collision terms at Keccak's sizes** (`G = 18`): the rate collisions
`|J|² / |X| ≤ 2^-511` and the capacity hits `|J| |A| 19 / |Z| ≈ 2^-181.9`. -/
theorem r0CollTerms_le_keccak :
    ((Fintype.card RLabel * Fintype.card RLabel : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((Fintype.card RLabel * Fintype.card (Option (Option CsIdx)) * (18 + 1) : ℕ) : ℝ≥0∞) /
          Fintype.card Z ≤ ENNReal.ofReal (1 / 2 ^ 181) := by
  rw [card_rLabel, card_hidIdx, card_rate, card_cap, natCast_div_eq_ofReal _ _ (by positivity),
    natCast_div_eq_ofReal _ _ (by positivity),
    ← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The read terms at Keccak's sizes** (`G = 18`): `|J| 19 q / |Z| ≤ q / 2^219`. -/
theorem readKHTerm_le_keccak (q : ℕ) :
    (Fintype.card RLabel : ℝ≥0∞) * ((18 : ℕ) + 1) * q / Fintype.card Z ≤
      ENNReal.ofReal (q / 2 ^ 219) := by
  have h : (Fintype.card RLabel : ℝ≥0∞) * ((18 : ℕ) + 1) * q =
      (((2 ^ 288 + 2 ^ 160) * 19 * q : ℕ) : ℝ≥0∞) := by
    rw [card_rLabel]
    push_cast
    ring
  have hn : (2 ^ 288 + 2 ^ 160) * 19 * q * 2 ^ 219 ≤ q * 2 ^ 512 := by
    calc (2 ^ 288 + 2 ^ 160) * 19 * q * 2 ^ 219 = q * ((2 ^ 288 + 2 ^ 160) * 19 * 2 ^ 219) := by
          ring
      _ ≤ q * 2 ^ 512 := Nat.mul_le_mul_left q (by norm_num)
  rw [h, card_cap, natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast hn

/-- **The bad fraction of the randomizer-base stages at Keccak's sizes** (`G = 18`): the fraction
outside `schemeGood` and the bad permutations, plus `2^-181` for the static collisions, plus per
computation `qs₂ᵢ / 2^256 + qᵢ / 2^219`. -/
theorem r0Good_frac_le_keccak [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₂ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₂ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ a S, rCell a P S = x).card ≤
        qs₂ i) :
    (Fintype.card (CTab RLabel) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (CTab RLabel) - (r0Good rCell rOrd Q).card : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) +
          ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z))) +
        ENNReal.ofReal (1 / 2 ^ 181) +
        ∑ i, ((qs₂ i : ℝ≥0∞) / 2 ^ 256 + ENNReal.ofReal (q i / 2 ^ 219)) :=
  (r0Good_frac_le_rLabel 18 Q q qs₂ hq hqs₂).trans (add_le_add (add_le_add le_rfl
    r0CollTerms_le_keccak) (Finset.sum_le_sum fun i _ ↦ add_le_add le_rfl
      (readKHTerm_le_keccak (q i))))

end R0

end Quantum.Xmss.Hybrid

end
