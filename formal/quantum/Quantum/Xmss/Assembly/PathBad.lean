module

public import Quantum.Xmss.Assembly.Reparam
public import Quantum.Sponge.Keccak

@[expose] public section

/-!
# The path-collision event of leanXMSS's reparametrization

`Quantum.Xmss.Assembly.Reparam` leaves the fraction of public coordinates in `PathBad` open: the
leaf paths span `8` blocks, so their later cells depend on `k`, `k'` and `h` along the path and the
fixed-cell collision count does not apply. Here every in-table path is processed round by round.

**Over abstract types.** A path with blocks `b` under keys `h`, `k`, `k'` and the permutation `π`
has the states `rnSt` and, in round `j`, the `k`-cell `rnK` (state rate plus block), the `k'`-cell
`rnR` (the rate after `π`) and the `h`-cell `rnZ` (the capacity after `π` plus `k'`); `famK`,
`famR`, `famZ` index them by (path, round). The rounds form a downward-closed finite set `R`.

* `card_mul_sum_le_of_moving`: resampling a uniform function at a cell `c f` that does not depend
  on the value at `c f` (the involution `(f, b) ↦ (f[c f ↦ b], f (c f))` on the precondition).
* The three stages of round `j`, each assuming every earlier stage injective (`PreK`, `PreR`,
  `PreZ`): a new `k`-cell equals an earlier `k`-cell (`EvK`, fresh in `h` at the previous `h`-cell,
  `1 / |X|`, `card_mul_sum_evK_le`), a new `k'`-cell an earlier one (`EvR`, fresh in `k` at the
  `k`-cell, `G / |Z|` by the rate counts of `PermGood`, `card_mul_sum_evR_le`), a new `h`-cell an
  earlier one (`EvZ`, fresh in `k'` at the `k'`-cell, `1 / |Z|`, `card_mul_sum_evZ_le`).
  `preK_all`: without events, and with distinct first blocks, every stage is injective.
* `card_mul_sum_not_injOn_le`: the `h`-cells of all rounds collide for at most a fraction
  `|R|² (|Z| + (G + 1) |X|) / (|X| |Z|)` of the keys; `frac_pathColl_le`: through a coordinate
  equivalence, with `|R| ≤ N`, at most `N² / |X| + N² (G + 1) / |Z|`.

**leanXMSS.** The in-table outputs' slot inputs (`xBlk`, `xLen`): the paths' states are the
template's (`stateAt_eq_rnSt`), their `h`-cells are `roundH`'s and the output cells
(`roundH_fst_eq_rnZ`, `outCap_eq_rnZ`), first blocks name their slots (`xBlk_injOn`), and distinct
`h`-cells over all rounds give `LeafSep` and `PathsAvoid` (`not_injOn_of_pathBad`). With at most `8`
blocks per slot (`xLen_le`), `N = 8 |xI|`:

* `pathBad_good_frac_le`: `PermGood π G ∧ PathBad` for at most `N² / |X| + N² (G + 1) / |Z|`;
* `pathBad_frac_le`: `PathBad` for at most the bad permutations plus that bound;
* `pathBad_frac_le_keccak`: at most `2^-400` (`|xI| ≤ 498 · 2^32`, `G = 18`).
-/

open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## Over abstract types -/

section generic

/-! ### Counting helpers -/

/-- Indicator sums are monotone in the event. -/
theorem sum_ite_le_of_imp {B : Type*} [Fintype B] (P Q : B → Prop) [DecidablePred P]
    [DecidablePred Q] (h : ∀ b, P b → Q b) :
    ∑ b, (if P b then 1 else 0) ≤ ∑ b, (if Q b then (1 : ℕ) else 0) :=
  Finset.sum_le_sum fun b _ ↦ by
    by_cases hb : P b
    · rw [ite_eq_left hb, ite_eq_left (h b hb)]
    · rw [ite_eq_right hb]
      exact Nat.zero_le _

/-- An injective map hits a point at most once. -/
theorem sum_ite_eq_le_one {B C : Type*} [Fintype B] [DecidableEq C] (g : B → C)
    (hg : Function.Injective g) (c : C) : ∑ b, (if g b = c then 1 else 0) ≤ 1 := by
  classical
  by_cases hc : ∃ b₀, g b₀ = c
  · obtain ⟨b₀, hb₀⟩ := hc
    calc ∑ b, (if g b = c then 1 else 0) ≤ ∑ b, (if b = b₀ then 1 else 0) :=
          sum_ite_le_of_imp _ _ fun b hb ↦ hg (hb.trans hb₀.symm)
      _ = 1 := by simp
  · have h0 : ∀ b, ¬g b = c := fun b hb ↦ hc ⟨b, hb⟩
    simp [h0]

/-- A union bound over two events. -/
theorem card_filter_le_add_of_imp {Y : Type*} [Fintype Y] (P A B : Y → Prop) [DecidablePred P]
    [DecidablePred A] [DecidablePred B] (h : ∀ y, P y → A y ∨ B y) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter A).card + (Finset.univ.filter B).card := by
  classical
  refine (Finset.card_le_card fun y hy ↦ ?_).trans (Finset.card_union_le _ _)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy ⊢
  exact h y hy

/-- A positive term bounds a double sum from below. -/
theorem one_le_sum_sum_of {α : Type*} {R : Finset α} (F : α → α → ℕ) {a b : α} (ha : a ∈ R)
    (hb : b ∈ R) (h : 1 ≤ F a b) : 1 ≤ ∑ a ∈ R, ∑ b ∈ R, F a b :=
  h.trans ((Finset.single_le_sum (f := fun b ↦ F a b) (fun _ _ ↦ Nat.zero_le _) hb).trans
    (Finset.single_le_sum (f := fun a ↦ ∑ b ∈ R, F a b) (fun _ _ ↦ Nat.zero_le _) ha))

/-- **Resampling at a moving cell.** If on the precondition `Pre` the cell `c f` and `Pre` itself
do not depend on the value of `f` at `c f`, and resampling that value makes `Bad` hold for at most
`D` values, then `Pre ∧ Bad` (or any `E` inside it) holds for at most `D / |B|` of the functions. -/
theorem card_mul_sum_le_of_moving {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (E Pre Bad : (A → B) → Prop) [DecidablePred E] [DecidablePred Bad] (c : (A → B) → A)
    (D : ℕ) (hE : ∀ f, E f → Pre f ∧ Bad f)
    (hst : ∀ f, Pre f → ∀ b, Pre (Function.update f (c f) b) ∧
      c (Function.update f (c f) b) = c f)
    (hD : ∀ f, Pre f → ∑ b, (if Bad (Function.update f (c f) b) then 1 else 0) ≤ D) :
    Fintype.card B * ∑ f, (if E f then 1 else 0) ≤ Fintype.card (A → B) * D := by
  classical
  let φ : (A → B) × B → (A → B) × B := fun p ↦
    if Pre p.1 then (Function.update p.1 (c p.1) p.2, p.1 (c p.1)) else p
  have hφpos : ∀ f b, Pre f → φ (f, b) = (Function.update f (c f) b, f (c f)) :=
    fun f b hf ↦ ite_eq_left hf
  have hφneg : ∀ f b, ¬Pre f → φ (f, b) = (f, b) := fun f b hf ↦ ite_eq_right hf
  have hφ : Function.Involutive φ := by
    rintro ⟨f, b⟩
    by_cases hf : Pre f
    · obtain ⟨hg, hc⟩ := hst f hf b
      rw [hφpos f b hf, hφpos _ _ hg, hc, Function.update_idem, Function.update_eq_self,
        Function.update_self]
    · rw [hφneg f b hf, hφneg f b hf]
  have hsum : ∑ p : (A → B) × B,
      (if Pre p.1 ∧ Bad (Function.update p.1 (c p.1) p.2) then 1 else 0) =
      ∑ p : (A → B) × B, (if Pre p.1 ∧ Bad p.1 then 1 else 0) :=
    Fintype.sum_equiv hφ.toPerm _ _ fun p ↦ by
      obtain ⟨f, b⟩ := p
      by_cases hf : Pre f
      · obtain ⟨hg, -⟩ := hst f hf b
        show _ = (if Pre (φ (f, b)).1 ∧ Bad (φ (f, b)).1 then 1 else 0)
        rw [hφpos f b hf]
        simp only [hf, hg, true_and]
      · show _ = (if Pre (φ (f, b)).1 ∧ Bad (φ (f, b)).1 then 1 else 0)
        rw [hφneg f b hf]
        simp only [hf, false_and]
  have hL : ∑ p : (A → B) × B, (if Pre p.1 ∧ Bad p.1 then 1 else 0) =
      ∑ f : A → B, ∑ _b : B, (if Pre f ∧ Bad f then 1 else 0) :=
    Fintype.sum_prod_type' (fun f (_ : B) ↦ if Pre f ∧ Bad f then 1 else 0)
  have hR : ∑ p : (A → B) × B,
      (if Pre p.1 ∧ Bad (Function.update p.1 (c p.1) p.2) then 1 else 0) =
      ∑ f : A → B, ∑ b : B, (if Pre f ∧ Bad (Function.update f (c f) b) then 1 else 0) :=
    Fintype.sum_prod_type' (fun f b ↦ if Pre f ∧ Bad (Function.update f (c f) b) then 1 else 0)
  calc Fintype.card B * ∑ f, (if E f then 1 else 0)
      ≤ Fintype.card B * ∑ f, (if Pre f ∧ Bad f then 1 else 0) :=
        Nat.mul_le_mul_left _ (sum_ite_le_of_imp _ _ hE)
    _ = ∑ f : A → B, ∑ _b : B, (if Pre f ∧ Bad f then 1 else 0) := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.mul_sum]
    _ = ∑ f : A → B, ∑ b : B, (if Pre f ∧ Bad (Function.update f (c f) b) then 1 else 0) := by
        rw [← hL, ← hR, hsum]
    _ ≤ ∑ _f : A → B, D := Finset.sum_le_sum fun f _ ↦ by
        by_cases hf : Pre f
        · exact (sum_ite_le_of_imp _ _ fun b hb ↦ hb.2).trans (hD f hf)
        · refine (sum_ite_le_of_imp _ (fun _ ↦ False) fun b hb ↦ hf hb.1).trans ?_
          simp
    _ = Fintype.card (A → B) * D := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- A sum over key triples as an iterated sum. -/
theorem sum_triple {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] (F : A → B → C → ℕ) :
    ∑ t : A × B × C, F t.1 t.2.1 t.2.2 = ∑ a, ∑ b, ∑ c, F a b c :=
  (Fintype.sum_prod_type' (fun a (bc : B × C) ↦ F a bc.1 bc.2)).trans
    (Finset.sum_congr rfl fun a _ ↦ Fintype.sum_prod_type' (fun b c ↦ F a b c))

/-- A bound fresh in the first coordinate of a triple. -/
theorem card_mul_sum_triple_le₁ {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → C → ℕ) (n D : ℕ) (hF : ∀ b c, n * ∑ a, F a b c ≤ Fintype.card A * D) :
    n * ∑ t : A × B × C, F t.1 t.2.1 t.2.2 ≤
      Fintype.card A * Fintype.card B * Fintype.card C * D := by
  rw [sum_triple]
  calc n * ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ c, n * ∑ a, F a b c := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _b : B, ∑ _c : C, Fintype.card A * D :=
        Finset.sum_le_sum fun b _ ↦ Finset.sum_le_sum fun c _ ↦ hF b c
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- A bound fresh in the second coordinate of a triple. -/
theorem card_mul_sum_triple_le₂ {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → C → ℕ) (n D : ℕ) (hF : ∀ a c, n * ∑ b, F a b c ≤ Fintype.card B * D) :
    n * ∑ t : A × B × C, F t.1 t.2.1 t.2.2 ≤
      Fintype.card A * Fintype.card B * Fintype.card C * D := by
  rw [sum_triple]
  calc n * ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, n * ∑ b, F a b c := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _a : A, ∑ _c : C, Fintype.card B * D :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun c _ ↦ hF a c
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- A bound fresh in the third coordinate of a triple. -/
theorem card_mul_sum_triple_le₃ {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → C → ℕ) (n D : ℕ) (hF : ∀ a b, n * ∑ c, F a b c ≤ Fintype.card C * D) :
    n * ∑ t : A × B × C, F t.1 t.2.1 t.2.2 ≤
      Fintype.card A * Fintype.card B * Fintype.card C * D := by
  rw [sum_triple]
  calc n * ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ b, n * ∑ c, F a b c := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ ↦ Finset.mul_sum _ _ _
    _ ≤ ∑ _a : A, ∑ _b : B, Fintype.card C * D :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hF a b
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-! ### The rounds of a path -/

variable {X Z S : Type} [AddCommGroup X] [AddCommGroup Z]

/-- **The sponge state before round `j`** of a path with blocks `b`, under the keys `h`, `k`, `k'`
and the permutation `π`. -/
def rnSt (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (b : ℕ → X) : ℕ → X × Z
  | 0 => (0, 0)
  | j + 1 =>
    let s := rnSt π h k k' b j
    let m := π (s.1 + b j, s.2 + k (s.1 + b j))
    (m.1 + h (m.2 + k' m.1), m.2 + k' m.1)

variable (π : Equiv.Perm (X × Z))

/-- The `k`-cell of round `j`. -/
def rnK (h : Z → X) (k k' : X → Z) (b : ℕ → X) (j : ℕ) : X :=
  (rnSt π h k k' b j).1 + b j

/-- The state after `π` in round `j`. -/
def rnMid (h : Z → X) (k k' : X → Z) (b : ℕ → X) (j : ℕ) : X × Z :=
  π (rnK π h k k' b j, (rnSt π h k k' b j).2 + k (rnK π h k k' b j))

/-- The `k'`-cell of round `j`. -/
def rnR (h : Z → X) (k k' : X → Z) (b : ℕ → X) (j : ℕ) : X :=
  (rnMid π h k k' b j).1

/-- The `h`-cell of round `j`. -/
def rnZ (h : Z → X) (k k' : X → Z) (b : ℕ → X) (j : ℕ) : Z :=
  (rnMid π h k k' b j).2 + k' (rnR π h k k' b j)

theorem rnSt_succ (h : Z → X) (k k' : X → Z) (b : ℕ → X) (j : ℕ) :
    rnSt π h k k' b (j + 1) = (rnR π h k k' b j + h (rnZ π h k k' b j), rnZ π h k k' b j) :=
  rfl

theorem rnK_zero (h : Z → X) (k k' : X → Z) (b : ℕ → X) : rnK π h k k' b 0 = b 0 :=
  zero_add _

/-- Two key triples agree at the cells of a path's first `j` rounds. -/
def RnAgree (h : Z → X) (k k' : X → Z) (h₂ : Z → X) (k₂ k₂' : X → Z) (b : ℕ → X) (j : ℕ) :
    Prop :=
  ∀ i < j, k₂ (rnK π h k k' b i) = k (rnK π h k k' b i) ∧
    k₂' (rnR π h k k' b i) = k' (rnR π h k k' b i) ∧ h₂ (rnZ π h k k' b i) = h (rnZ π h k k' b i)

variable {π}

/-- **Agreeing keys give the same states.** -/
theorem rnSt_congr {h h₂ : Z → X} {k k' k₂ k₂' : X → Z} {b : ℕ → X} :
    ∀ {j}, RnAgree π h k k' h₂ k₂ k₂' b j → rnSt π h₂ k₂ k₂' b j = rnSt π h k k' b j
  | 0, _ => rfl
  | j + 1, hA => by
    obtain ⟨e1, e2, e3⟩ := hA j (Nat.lt_succ_self j)
    have ih : rnSt π h₂ k₂ k₂' b j = rnSt π h k k' b j :=
      rnSt_congr fun i hi ↦ hA i (Nat.lt_succ_of_lt hi)
    have hK : rnK π h₂ k₂ k₂' b j = rnK π h k k' b j := by
      unfold rnK
      rw [ih]
    have hM : rnMid π h₂ k₂ k₂' b j = rnMid π h k k' b j := by
      unfold rnMid
      rw [hK, ih, e1]
    have hR : rnR π h₂ k₂ k₂' b j = rnR π h k k' b j := by
      unfold rnR
      rw [hM]
    have hZ : rnZ π h₂ k₂ k₂' b j = rnZ π h k k' b j := by
      unfold rnZ
      rw [hM, hR, e2]
    rw [rnSt_succ, rnSt_succ, hR, hZ, e3]

theorem rnK_congr {h h₂ : Z → X} {k k' k₂ k₂' : X → Z} {b : ℕ → X} {j : ℕ}
    (hA : RnAgree π h k k' h₂ k₂ k₂' b j) : rnK π h₂ k₂ k₂' b j = rnK π h k k' b j := by
  unfold rnK
  rw [rnSt_congr hA]

theorem rnMid_congr {h h₂ : Z → X} {k k' k₂ k₂' : X → Z} {b : ℕ → X} {j : ℕ}
    (hA : RnAgree π h k k' h₂ k₂ k₂' b j)
    (e1 : k₂ (rnK π h k k' b j) = k (rnK π h k k' b j)) :
    rnMid π h₂ k₂ k₂' b j = rnMid π h k k' b j := by
  unfold rnMid
  rw [rnK_congr hA, rnSt_congr hA, e1]

theorem rnR_congr {h h₂ : Z → X} {k k' k₂ k₂' : X → Z} {b : ℕ → X} {j : ℕ}
    (hA : RnAgree π h k k' h₂ k₂ k₂' b j)
    (e1 : k₂ (rnK π h k k' b j) = k (rnK π h k k' b j)) :
    rnR π h₂ k₂ k₂' b j = rnR π h k k' b j := by
  unfold rnR
  rw [rnMid_congr hA e1]

theorem rnZ_congr {h h₂ : Z → X} {k k' k₂ k₂' : X → Z} {b : ℕ → X} {j : ℕ}
    (hA : RnAgree π h k k' h₂ k₂ k₂' b j)
    (e1 : k₂ (rnK π h k k' b j) = k (rnK π h k k' b j))
    (e2 : k₂' (rnR π h k k' b j) = k' (rnR π h k k' b j)) :
    rnZ π h₂ k₂ k₂' b j = rnZ π h k k' b j := by
  unfold rnZ
  rw [rnMid_congr hA e1, rnR_congr hA e1, e2]

/-! ### The rounds of all paths -/

variable (π) (blk : S → ℕ → X)

/-- The `k`-cell of a round (path, index). -/
def famK (h : Z → X) (k k' : X → Z) (a : S × ℕ) : X :=
  rnK π h k k' (blk a.1) a.2

/-- The `k'`-cell of a round. -/
def famR (h : Z → X) (k k' : X → Z) (a : S × ℕ) : X :=
  rnR π h k k' (blk a.1) a.2

/-- The `h`-cell of a round. -/
def famZ (h : Z → X) (k k' : X → Z) (a : S × ℕ) : Z :=
  rnZ π h k k' (blk a.1) a.2

omit [AddCommGroup X] [AddCommGroup Z] in
/-- A family is injective on the rounds of index below `J`. -/
def InjBelow {β : Type*} (R : Finset (S × ℕ)) (f : S × ℕ → β) (J : ℕ) : Prop :=
  ∀ a ∈ R, ∀ b ∈ R, a.2 < J → b.2 < J → f a = f b → a = b

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The rounds of a path are an initial segment. -/
def DownClosed (R : Finset (S × ℕ)) : Prop :=
  ∀ a ∈ R, ∀ i ≤ a.2, (a.1, i) ∈ R

/-- **Before the `k`-cells of round `j`**: all cells of earlier rounds injective. -/
def PreK (R : Finset (S × ℕ)) (h : Z → X) (k k' : X → Z) (j : ℕ) : Prop :=
  InjBelow R (famK π blk h k k') j ∧ InjBelow R (famR π blk h k k') j ∧
    InjBelow R (famZ π blk h k k') j

/-- **Before the `k'`-cells of round `j`**: also the `k`-cells of round `j` injective. -/
def PreR (R : Finset (S × ℕ)) (h : Z → X) (k k' : X → Z) (j : ℕ) : Prop :=
  PreK π blk R h k k' j ∧ InjBelow R (famK π blk h k k') (j + 1)

/-- **Before the `h`-cells of round `j`**: also the `k'`-cells of round `j` injective. -/
def PreZ (R : Finset (S × ℕ)) (h : Z → X) (k k' : X → Z) (j : ℕ) : Prop :=
  PreR π blk R h k k' j ∧ InjBelow R (famR π blk h k k') (j + 1)

/-- **A new `k`-cell collides**: round `a` (not the first) has an earlier or equal-round `k`-cell
`b`, all earlier stages injective. -/
def EvK (R : Finset (S × ℕ)) (a b : S × ℕ) (h : Z → X) (k k' : X → Z) : Prop :=
  (1 ≤ a.2 ∧ b.2 ≤ a.2 ∧ a ≠ b ∧ PreK π blk R h k k' a.2) ∧
    famK π blk h k k' a = famK π blk h k k' b

/-- **A new `k'`-cell collides.** -/
def EvR (R : Finset (S × ℕ)) (a b : S × ℕ) (h : Z → X) (k k' : X → Z) : Prop :=
  (b.2 ≤ a.2 ∧ a ≠ b ∧ PreR π blk R h k k' a.2) ∧ famR π blk h k k' a = famR π blk h k k' b

/-- **A new `h`-cell collides.** -/
def EvZ (R : Finset (S × ℕ)) (a b : S × ℕ) (h : Z → X) (k k' : X → Z) : Prop :=
  (b.2 ≤ a.2 ∧ a ≠ b ∧ PreZ π blk R h k k' a.2) ∧ famZ π blk h k k' a = famZ π blk h k k' b

variable {π blk}

omit [AddCommGroup X] [AddCommGroup Z] in
theorem injBelow_congr {β : Type*} {R : Finset (S × ℕ)} {f f₂ : S × ℕ → β} {J : ℕ}
    (hf : ∀ a ∈ R, a.2 < J → f₂ a = f a) (h : InjBelow R f J) : InjBelow R f₂ J :=
  fun a ha b hb haJ hbJ e ↦ h a ha b hb haJ hbJ (by rw [← hf a ha haJ, ← hf b hb hbJ]; exact e)

omit [AddCommGroup X] [AddCommGroup Z] in
theorem injBelow_succ {β : Type*} {R : Finset (S × ℕ)} {f : S × ℕ → β} {J : ℕ}
    (hJ : InjBelow R f J)
    (hnew : ∀ a ∈ R, ∀ b ∈ R, a.2 = J → b.2 ≤ J → a ≠ b → f a ≠ f b) :
    InjBelow R f (J + 1) := by
  intro a ha b hb haJ hbJ e
  by_contra hne
  rcases (show a.2 < J ∨ a.2 = J by omega) with ha' | ha'
  · rcases (show b.2 < J ∨ b.2 = J by omega) with hb' | hb'
    · exact hne (hJ a ha b hb ha' hb' e)
    · exact hnew b hb a ha hb' ha'.le (Ne.symm hne) e.symm
  · exact hnew a ha b hb ha' (by omega) hne e

/-- **Without events every stage is injective**, given distinct first blocks. -/
theorem preK_all {R : Finset (S × ℕ)} {h : Z → X} {k k' : X → Z}
    (hfirst : ∀ a ∈ R, ∀ b ∈ R, a.2 = 0 → b.2 = 0 → blk a.1 0 = blk b.1 0 → a.1 = b.1)
    (hno : ∀ a ∈ R, ∀ b ∈ R, ¬EvK π blk R a b h k k' ∧ ¬EvR π blk R a b h k k' ∧
      ¬EvZ π blk R a b h k k') :
    ∀ j, PreK π blk R h k k' j := by
  intro j
  induction j with
  | zero =>
    exact ⟨fun _ _ _ _ h0 _ _ ↦ absurd h0 (Nat.not_lt_zero _),
      fun _ _ _ _ h0 _ _ ↦ absurd h0 (Nat.not_lt_zero _),
      fun _ _ _ _ h0 _ _ ↦ absurd h0 (Nat.not_lt_zero _)⟩
  | succ j ih =>
    have hK : InjBelow R (famK π blk h k k') (j + 1) := injBelow_succ ih.1
      fun a ha b hb haj hbj hne e ↦ by
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · have hb0 : b.2 = 0 := by omega
          apply hne
          have e' : rnK π h k k' (blk a.1) 0 = rnK π h k k' (blk b.1) 0 := by
            have e2 : rnK π h k k' (blk a.1) a.2 = rnK π h k k' (blk b.1) b.2 := e
            rwa [haj, hb0] at e2
          rw [rnK_zero, rnK_zero] at e'
          exact Prod.ext (hfirst a ha b hb haj hb0 e') (haj.trans hb0.symm)
        · exact (hno a ha b hb).1 ⟨⟨by omega, by omega, hne, by rw [haj]; exact ih⟩, e⟩
    have hR : InjBelow R (famR π blk h k k') (j + 1) := injBelow_succ ih.2.1
      fun a ha b hb haj hbj hne e ↦
        (hno a ha b hb).2.1 ⟨⟨by omega, hne, by rw [haj]; exact ⟨ih, hK⟩⟩, e⟩
    have hZ : InjBelow R (famZ π blk h k k') (j + 1) := injBelow_succ ih.2.2
      fun a ha b hb haj hbj hne e ↦
        (hno a ha b hb).2.2 ⟨⟨by omega, hne, by rw [haj]; exact ⟨⟨ih, hK⟩, hR⟩⟩, e⟩
    exact ⟨hK, hR, hZ⟩

/-- A collision of `h`-cells comes with an event. -/
theorem exists_ev_of_not_injOn {R : Finset (S × ℕ)} {h : Z → X} {k k' : X → Z}
    (hfirst : ∀ a ∈ R, ∀ b ∈ R, a.2 = 0 → b.2 = 0 → blk a.1 0 = blk b.1 0 → a.1 = b.1)
    (hn : ¬Set.InjOn (famZ π blk h k k') R) :
    ∃ a ∈ R, ∃ b ∈ R, EvK π blk R a b h k k' ∨ EvR π blk R a b h k k' ∨
      EvZ π blk R a b h k k' := by
  by_contra hno
  push Not at hno
  have hall := preK_all hfirst hno
  exact hn fun a ha b hb e ↦ (hall (a.2 + b.2 + 1)).2.2 a (Finset.mem_coe.mp ha) b
    (Finset.mem_coe.mp hb) (by omega) (by omega) e

/-! ### The three stages -/

section stageK

variable [DecidableEq Z] {R : Finset (S × ℕ)} {h : Z → X} {k k' : X → Z} {p : S} {j₀ : ℕ}

/-- Resampling `h` at the `h`-cell of round `j₀` of path `p` keeps the cells of every path up to
a round whose earlier rounds avoid `(p, j₀)`. -/
theorem agree_h (hR : DownClosed R) (hp : (p, j₀) ∈ R)
    (hinj : InjBelow R (famZ π blk h k k') (j₀ + 1)) (β : X) {x : S × ℕ} (hx : x ∈ R)
    (hi : x.2 ≤ j₀ + 1) (hne : ∀ i' < x.2, (x.1, i') ≠ (p, j₀)) :
    RnAgree π h k k' (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (blk x.1) x.2 :=
  fun i' hi' ↦ ⟨rfl, rfl, Function.update_of_ne (fun e ↦ hne i' hi'
    (hinj (x.1, i') (hR x hx i' hi'.le) (p, j₀) hp (show i' < j₀ + 1 by omega)
      (show j₀ < j₀ + 1 by omega) e)) _ _⟩

/-- The cells of rounds up to `j₀` are unchanged. -/
theorem fam_eq_h (hR : DownClosed R) (hp : (p, j₀) ∈ R)
    (hinj : InjBelow R (famZ π blk h k k') (j₀ + 1)) (β : X) {x : S × ℕ} (hx : x ∈ R)
    (hi : x.2 ≤ j₀) :
    famK π blk (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' x = famK π blk h k k' x ∧
      famR π blk (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' x =
        famR π blk h k k' x ∧
      famZ π blk (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' x =
        famZ π blk h k k' x := by
  have hA := agree_h hR hp hinj β hx (by omega) fun i' hi' e ↦
    (show i' ≠ j₀ by omega) (congrArg Prod.snd e)
  exact ⟨rnK_congr hA, rnR_congr hA rfl, rnZ_congr hA rfl rfl⟩

open scoped Classical in
/-- **A new `k`-cell collides** for at most `1 / |X|` of `h`. -/
theorem card_mul_sum_evK_le [Fintype X] [Fintype Z] (hR : DownClosed R) {a b : S × ℕ}
    (ha : a ∈ R) (hb : b ∈ R) (k k' : X → Z) :
    Fintype.card X * ∑ h : Z → X, (if EvK π blk R a b h k k' then 1 else 0) ≤
      Fintype.card (Z → X) * 1 := by
  obtain ⟨p, j⟩ := a
  obtain ⟨q, i⟩ := b
  rcases j with _ | j₀
  · have h0 : ∀ h, ¬EvK π blk R (p, 0) (q, i) h k k' := fun _ hE ↦
      Nat.not_succ_le_zero 0 hE.1.1
    simp only [h0, ite_false, Finset.sum_const_zero, mul_zero]
    exact Nat.zero_le _
  · have hp : (p, j₀) ∈ R := hR _ ha j₀ (Nat.le_succ j₀)
    refine card_mul_sum_le_of_moving _
      (fun h ↦ i ≤ j₀ + 1 ∧ (p, j₀ + 1) ≠ (q, i) ∧ PreK π blk R h k k' (j₀ + 1))
      (fun h ↦ famK π blk h k k' (p, j₀ + 1) = famK π blk h k k' (q, i))
      (fun h ↦ rnZ π h k k' (blk p) j₀) 1 (fun h hE ↦ ⟨hE.1.2, hE.2⟩)
      (fun h hP β ↦ ?_) (fun h hP ↦ ?_)
    · have hf := fun (x : S × ℕ) (hx : x ∈ R) (hxj : x.2 < j₀ + 1) ↦
        fam_eq_h hR hp hP.2.2.2.2 β hx (by omega)
      exact ⟨⟨hP.1, hP.2.1, injBelow_congr (fun x hx hxj ↦ (hf x hx hxj).1) hP.2.2.1,
        injBelow_congr (fun x hx hxj ↦ (hf x hx hxj).2.1) hP.2.2.2.1,
        injBelow_congr (fun x hx hxj ↦ (hf x hx hxj).2.2) hP.2.2.2.2⟩,
        (fam_eq_h hR hp hP.2.2.2.2 β hp le_rfl).2.2⟩
    · have hinj := hP.2.2.2.2
      refine (sum_ite_le_of_imp _ (fun β ↦ rnR π h k k' (blk p) j₀ + β + blk p (j₀ + 1) =
        famK π blk h k k' (q, i)) fun β hβ ↦ ?_).trans
        (sum_ite_eq_le_one _ (fun β₁ β₂ e ↦ add_left_cancel (add_right_cancel e)) _)
      have hAp := agree_h hR hp hinj β hp (by omega) fun i' hi' e ↦
        (show i' ≠ j₀ by omega) (congrArg Prod.snd e)
      have hAq := agree_h hR hp hinj β hb hP.1 fun i' hi' e ↦ hP.2.1 (by
        have e1 : q = p := congrArg Prod.fst e
        have e2 : i' = j₀ := congrArg Prod.snd e
        subst e1
        exact Prod.ext rfl (show j₀ + 1 = i by omega))
      have hKa : famK π blk (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (p, j₀ + 1) =
          rnR π h k k' (blk p) j₀ + β + blk p (j₀ + 1) := by
        show (rnSt π (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (blk p) (j₀ + 1)).1 +
          blk p (j₀ + 1) = _
        rw [rnSt_succ, rnR_congr hAp rfl, rnZ_congr hAp rfl rfl, Function.update_self]
      have hKb : famK π blk (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (q, i) =
          famK π blk h k k' (q, i) := rnK_congr hAq
      show rnR π h k k' (blk p) j₀ + β + blk p (j₀ + 1) = famK π blk h k k' (q, i)
      rw [← hKa, ← hKb]
      exact hβ

end stageK

section stageR

variable [DecidableEq X] {R : Finset (S × ℕ)} {h : Z → X} {k k' : X → Z} {p : S} {j : ℕ}

/-- Resampling `k` at the `k`-cell of round `j` of path `p` keeps the cells of every path up to
a round whose earlier rounds avoid `(p, j)`. -/
theorem agree_k (hR : DownClosed R) (hp : (p, j) ∈ R)
    (hinj : InjBelow R (famK π blk h k k') (j + 1)) (β : Z) {x : S × ℕ} (hx : x ∈ R)
    (hi : x.2 ≤ j) :
    RnAgree π h k k' h (Function.update k (rnK π h k k' (blk p) j) β) k' (blk x.1) x.2 :=
  fun i' hi' ↦ ⟨Function.update_of_ne (fun e ↦ (show i' ≠ j by omega)
    (congrArg Prod.snd (hinj (x.1, i') (hR x hx i' hi'.le) (p, j) hp
      (show i' < j + 1 by omega) (show j < j + 1 by omega) e))) _ _, rfl, rfl⟩

/-- The `k`-cells of rounds up to `j` are unchanged, and the other cells of rounds up to `j` other
than `(p, j)`. -/
theorem fam_eq_k (hR : DownClosed R) (hp : (p, j) ∈ R)
    (hinj : InjBelow R (famK π blk h k k') (j + 1)) (β : Z) {x : S × ℕ} (hx : x ∈ R)
    (hi : x.2 ≤ j) :
    famK π blk h (Function.update k (rnK π h k k' (blk p) j) β) k' x = famK π blk h k k' x ∧
      (x ≠ (p, j) →
        famR π blk h (Function.update k (rnK π h k k' (blk p) j) β) k' x =
          famR π blk h k k' x ∧
        famZ π blk h (Function.update k (rnK π h k k' (blk p) j) β) k' x =
          famZ π blk h k k' x) := by
  have hA := agree_k hR hp hinj β hx hi
  refine ⟨rnK_congr hA, fun hxa ↦ ?_⟩
  have e1 : Function.update k (rnK π h k k' (blk p) j) β (rnK π h k k' (blk x.1) x.2) =
      k (rnK π h k k' (blk x.1) x.2) :=
    Function.update_of_ne (fun e ↦ hxa (hinj x hx (p, j) hp (by omega) (by omega) e)) _ _
  exact ⟨rnR_congr hA e1, rnZ_congr hA e1 rfl⟩

omit [AddCommGroup X] in
/-- `π` sends the points over `x0` into rate `r` at most `rateCount` times. -/
theorem sum_ite_rate_le [Fintype Z] (π : Equiv.Perm (X × Z)) (x0 : X) (s : Z) (r : X) :
    ∑ β : Z, (if (π (x0, s + β)).1 = r then 1 else 0) = rateCount π x0 r := by
  rw [rateCount, Finset.card_filter]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ fun _ ↦ rfl

open scoped Classical in
/-- **A new `k'`-cell collides** for at most `G / |Z|` of `k`, if every rate count is at most
`G`. -/
theorem card_mul_sum_evR_le [Fintype X] [Fintype Z] (hR : DownClosed R) {G : ℕ}
    (hG : ∀ x r, rateCount π x r ≤ G) {a b : S × ℕ} (ha : a ∈ R) (hb : b ∈ R) (h : Z → X)
    (k' : X → Z) :
    Fintype.card Z * ∑ k : X → Z, (if EvR π blk R a b h k k' then 1 else 0) ≤
      Fintype.card (X → Z) * G := by
  obtain ⟨p, j⟩ := a
  refine card_mul_sum_le_of_moving _
    (fun k ↦ b.2 ≤ j ∧ (p, j) ≠ b ∧ PreR π blk R h k k' j)
    (fun k ↦ famR π blk h k k' (p, j) = famR π blk h k k' b)
    (fun k ↦ rnK π h k k' (blk p) j) G (fun k hE ↦ ⟨hE.1, hE.2⟩)
    (fun k hP β ↦ ?_) (fun k hP ↦ ?_)
  · have hinj := hP.2.2.2
    have hf := fun (x : S × ℕ) (hx : x ∈ R) (hxj : x.2 ≤ j) ↦ fam_eq_k hR ha hinj β hx hxj
    have hne : ∀ x : S × ℕ, x.2 < j → x ≠ (p, j) := fun x hx e ↦ by
      rw [e] at hx
      exact lt_irrefl _ hx
    exact ⟨⟨hP.1, hP.2.1, ⟨injBelow_congr (fun x hx hxj ↦ (hf x hx hxj.le).1) hP.2.2.1.1,
      injBelow_congr (fun x hx hxj ↦ ((hf x hx hxj.le).2 (hne x hxj)).1) hP.2.2.1.2.1,
      injBelow_congr (fun x hx hxj ↦ ((hf x hx hxj.le).2 (hne x hxj)).2) hP.2.2.1.2.2⟩,
      injBelow_congr (fun x hx hxj ↦ (hf x hx (by omega)).1) hinj⟩,
      (fam_eq_k hR ha hinj β ha le_rfl).1⟩
  · have hinj := hP.2.2.2
    refine (sum_ite_le_of_imp _ (fun β ↦ (π (rnK π h k k' (blk p) j,
      (rnSt π h k k' (blk p) j).2 + β)).1 = famR π blk h k k' b) fun β hβ ↦ ?_).trans
      ((sum_ite_rate_le π _ _ _).trans_le (hG _ _))
    have hAp := agree_k hR ha hinj β ha le_rfl
    have hRa : famR π blk h (Function.update k (rnK π h k k' (blk p) j) β) k' (p, j) =
        (π (rnK π h k k' (blk p) j, (rnSt π h k k' (blk p) j).2 + β)).1 := by
      show (π (rnK π h (Function.update k (rnK π h k k' (blk p) j) β) k' (blk p) j,
        (rnSt π h (Function.update k (rnK π h k k' (blk p) j) β) k' (blk p) j).2 +
          Function.update k (rnK π h k k' (blk p) j) β
            (rnK π h (Function.update k (rnK π h k k' (blk p) j) β) k' (blk p) j))).1 = _
      rw [rnK_congr hAp, rnSt_congr hAp, Function.update_self]
    have hRb := ((fam_eq_k hR ha hinj β hb hP.1).2 (Ne.symm hP.2.1)).1
    show (π (rnK π h k k' (blk p) j, (rnSt π h k k' (blk p) j).2 + β)).1 = famR π blk h k k' b
    rw [← hRa, ← hRb]
    exact hβ

end stageR

section stageZ

variable [DecidableEq X] {R : Finset (S × ℕ)} {h : Z → X} {k k' : X → Z} {p : S} {j : ℕ}

/-- Resampling `k'` at the `k'`-cell of round `j` of path `p` keeps the cells of every path up to
a round whose earlier rounds avoid `(p, j)`. -/
theorem agree_k' (hR : DownClosed R) (hp : (p, j) ∈ R)
    (hinj : InjBelow R (famR π blk h k k') (j + 1)) (β : Z) {x : S × ℕ} (hx : x ∈ R)
    (hi : x.2 ≤ j) :
    RnAgree π h k k' h k (Function.update k' (rnR π h k k' (blk p) j) β) (blk x.1) x.2 :=
  fun i' hi' ↦ ⟨rfl, Function.update_of_ne (fun e ↦ (show i' ≠ j by omega)
    (congrArg Prod.snd (hinj (x.1, i') (hR x hx i' hi'.le) (p, j) hp
      (show i' < j + 1 by omega) (show j < j + 1 by omega) e))) _ _, rfl⟩

/-- The `k`- and `k'`-cells of rounds up to `j` are unchanged, and the `h`-cells other than
`(p, j)`. -/
theorem fam_eq_k' (hR : DownClosed R) (hp : (p, j) ∈ R)
    (hinj : InjBelow R (famR π blk h k k') (j + 1)) (β : Z) {x : S × ℕ} (hx : x ∈ R)
    (hi : x.2 ≤ j) :
    famK π blk h k (Function.update k' (rnR π h k k' (blk p) j) β) x = famK π blk h k k' x ∧
      famR π blk h k (Function.update k' (rnR π h k k' (blk p) j) β) x =
        famR π blk h k k' x ∧
      (x ≠ (p, j) →
        famZ π blk h k (Function.update k' (rnR π h k k' (blk p) j) β) x =
          famZ π blk h k k' x) := by
  have hA := agree_k' hR hp hinj β hx hi
  refine ⟨rnK_congr hA, rnR_congr hA rfl, fun hxa ↦ rnZ_congr hA rfl ?_⟩
  exact Function.update_of_ne (fun e ↦ hxa (hinj x hx (p, j) hp (by omega) (by omega) e)) _ _

open scoped Classical in
/-- **A new `h`-cell collides** for at most `1 / |Z|` of `k'`. -/
theorem card_mul_sum_evZ_le [Fintype X] [Fintype Z] (hR : DownClosed R) {a b : S × ℕ}
    (ha : a ∈ R) (hb : b ∈ R) (h : Z → X) (k : X → Z) :
    Fintype.card Z * ∑ k' : X → Z, (if EvZ π blk R a b h k k' then 1 else 0) ≤
      Fintype.card (X → Z) * 1 := by
  obtain ⟨p, j⟩ := a
  refine card_mul_sum_le_of_moving _
    (fun k' ↦ b.2 ≤ j ∧ (p, j) ≠ b ∧ PreZ π blk R h k k' j)
    (fun k' ↦ famZ π blk h k k' (p, j) = famZ π blk h k k' b)
    (fun k' ↦ rnR π h k k' (blk p) j) 1 (fun k' hE ↦ ⟨hE.1, hE.2⟩)
    (fun k' hP β ↦ ?_) (fun k' hP ↦ ?_)
  · have hinj := hP.2.2.2
    have hf := fun (x : S × ℕ) (hx : x ∈ R) (hxj : x.2 ≤ j) ↦ fam_eq_k' hR ha hinj β hx hxj
    have hne : ∀ x : S × ℕ, x.2 < j → x ≠ (p, j) := fun x hx e ↦ by
      rw [e] at hx
      exact lt_irrefl _ hx
    exact ⟨⟨hP.1, hP.2.1, ⟨⟨injBelow_congr (fun x hx hxj ↦ (hf x hx hxj.le).1)
      hP.2.2.1.1.1, injBelow_congr (fun x hx hxj ↦ (hf x hx hxj.le).2.1) hP.2.2.1.1.2.1,
      injBelow_congr (fun x hx hxj ↦ (hf x hx hxj.le).2.2 (hne x hxj)) hP.2.2.1.1.2.2⟩,
      injBelow_congr (fun x hx hxj ↦ (hf x hx (by omega)).1) hP.2.2.1.2⟩,
      injBelow_congr (fun x hx hxj ↦ (hf x hx (by omega)).2.1) hinj⟩,
      (fam_eq_k' hR ha hinj β ha le_rfl).2.1⟩
  · have hinj := hP.2.2.2
    refine (sum_ite_le_of_imp _ (fun β ↦ (rnMid π h k k' (blk p) j).2 + β =
      famZ π blk h k k' b) fun β hβ ↦ ?_).trans
      (sum_ite_eq_le_one _ (fun β₁ β₂ e ↦ add_left_cancel e) _)
    have hAp := agree_k' hR ha hinj β ha le_rfl
    have hZa : famZ π blk h k (Function.update k' (rnR π h k k' (blk p) j) β) (p, j) =
        (rnMid π h k k' (blk p) j).2 + β := by
      show (rnMid π h k (Function.update k' (rnR π h k k' (blk p) j) β) (blk p) j).2 +
        Function.update k' (rnR π h k k' (blk p) j) β
          (rnR π h k (Function.update k' (rnR π h k k' (blk p) j) β) (blk p) j) = _
      rw [rnMid_congr hAp rfl, rnR_congr hAp rfl, Function.update_self]
    have hZb := (fam_eq_k' hR ha hinj β hb hP.1).2.2 (Ne.symm hP.2.1)
    show (rnMid π h k k' (blk p) j).2 + β = famZ π blk h k k' b
    rw [← hZa, ← hZb]
    exact hβ

end stageZ

/-! ### The collision count -/

open scoped Classical in
/-- **The `h`-cells of all rounds collide** for at most a fraction
`|R|² (|Z| + (G + 1) |X|) / (|X| |Z|)` of the keys `h`, `k`, `k'`, if `π`'s rate counts are at
most `G` and the paths' first blocks are distinct. -/
theorem card_mul_sum_not_injOn_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {R : Finset (S × ℕ)} (hR : DownClosed R)
    (hfirst : ∀ a ∈ R, ∀ b ∈ R, a.2 = 0 → b.2 = 0 → blk a.1 0 = blk b.1 0 → a.1 = b.1)
    {G : ℕ} (hG : ∀ x r, rateCount π x r ≤ G) :
    Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if ¬Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R then 1 else 0) ≤
      Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
        (R.card * R.card * (Fintype.card Z + (G + 1) * Fintype.card X)) := by
  set M := Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z)
  set F : (Z → X) × (X → Z) × (X → Z) → S × ℕ → S × ℕ → ℕ := fun t a b ↦
    (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
      (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
      (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) with hF
  have hpt : ∀ t : (Z → X) × (X → Z) × (X → Z),
      (if ¬Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R then 1 else 0) ≤
        ∑ a ∈ R, ∑ b ∈ R, F t a b := by
    intro t
    by_cases hn : Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R
    · rw [ite_eq_right (not_not.mpr hn)]
      exact Nat.zero_le _
    · rw [ite_eq_left hn]
      obtain ⟨a, ha, b, hb, hev⟩ := exists_ev_of_not_injOn hfirst hn
      refine one_le_sum_sum_of (F t) ha hb ?_
      rcases hev with h1 | h2 | h3
      · exact le_add_right (le_add_right (by rw [ite_eq_left h1]))
      · exact le_add_right (le_add_left (by rw [ite_eq_left h2]))
      · exact le_add_left (by rw [ite_eq_left h3])
  have hab : ∀ a ∈ R, ∀ b ∈ R, Fintype.card X * Fintype.card Z * ∑ t, F t a b ≤
      M * (Fintype.card Z + (G + 1) * Fintype.card X) := by
    intro a ha b hb
    have hK : Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * 1 :=
      card_mul_sum_triple_le₁ (fun h k k' ↦ if EvK π blk R a b h k k' then 1 else 0) _ _
        fun k k' ↦ card_mul_sum_evK_le hR ha hb k k'
    have hRr : Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * G :=
      card_mul_sum_triple_le₂ (fun h k k' ↦ if EvR π blk R a b h k k' then 1 else 0) _ _
        fun h k' ↦ card_mul_sum_evR_le hR hG ha hb h k'
    have hZz : Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) ≤ M * 1 :=
      card_mul_sum_triple_le₃ (fun h k k' ↦ if EvZ π blk R a b h k k' then 1 else 0) _ _
        fun h k ↦ card_mul_sum_evZ_le hR ha hb h k
    simp only [hF, Finset.sum_add_distrib]
    calc Fintype.card X * Fintype.card Z * (∑ t : (Z → X) × (X → Z) × (X → Z),
          (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
          ∑ t : (Z → X) × (X → Z) × (X → Z),
            (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0) +
          ∑ t : (Z → X) × (X → Z) × (X → Z),
            (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0))
        = Fintype.card Z * (Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
            (if EvK π blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) +
          Fintype.card X * (Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
            (if EvR π blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) +
          Fintype.card X * (Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
            (if EvZ π blk R a b t.1 t.2.1 t.2.2 then 1 else 0)) := by ring
      _ ≤ Fintype.card Z * (M * 1) + Fintype.card X * (M * G) + Fintype.card X * (M * 1) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hK)
            (Nat.mul_le_mul_left _ hRr)) (Nat.mul_le_mul_left _ hZz)
      _ = M * (Fintype.card Z + (G + 1) * Fintype.card X) := by ring
  calc Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
        (if ¬Set.InjOn (famZ π blk t.1 t.2.1 t.2.2) R then 1 else 0)
      ≤ Fintype.card X * Fintype.card Z * ∑ t, ∑ a ∈ R, ∑ b ∈ R, F t a b :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun t _ ↦ hpt t)
    _ = ∑ a ∈ R, ∑ b ∈ R, Fintype.card X * Fintype.card Z * ∑ t, F t a b := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _a ∈ R, ∑ _b ∈ R, M * (Fintype.card Z + (G + 1) * Fintype.card X) :=
        Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum fun b hb ↦ hab a ha b hb
    _ = _ := by
        simp only [Finset.sum_const, smul_eq_mul]
        ring

/-! ### The rounds of finitely many paths, and the fraction -/

omit [AddCommGroup X] [AddCommGroup Z] in
/-- The rounds `(p, j)`, `p ∈ I`, `j < len p`. -/
def rnds [DecidableEq S] (I : Finset S) (len : S → ℕ) : Finset (S × ℕ) :=
  I.biUnion fun p ↦ (Finset.range (len p)).image fun j ↦ (p, j)

omit [AddCommGroup X] [AddCommGroup Z] in
theorem mem_rnds [DecidableEq S] {I : Finset S} {len : S → ℕ} {a : S × ℕ} :
    a ∈ rnds I len ↔ a.1 ∈ I ∧ a.2 < len a.1 := by
  simp only [rnds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨p, hp, j, hj, rfl⟩
    exact ⟨hp, hj⟩
  · rintro ⟨h1, h2⟩
    exact ⟨a.1, h1, a.2, h2, rfl⟩

omit [AddCommGroup X] [AddCommGroup Z] in
theorem card_rnds_le [DecidableEq S] (I : Finset S) (len : S → ℕ) {m : ℕ} (hm : ∀ p, len p ≤ m) :
    (rnds I len).card ≤ m * I.card :=
  calc (rnds I len).card ≤ ∑ p ∈ I, len p := Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le.trans (Finset.card_range _).le)
    _ ≤ ∑ _p ∈ I, m := Finset.sum_le_sum fun p _ ↦ hm p
    _ = m * I.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

omit [AddCommGroup X] [AddCommGroup Z] in
theorem downClosed_rnds [DecidableEq S] (I : Finset S) (len : S → ℕ) :
    DownClosed (rnds I len) := fun _a ha _i hi ↦
  mem_rnds.mpr ⟨(mem_rnds.mp ha).1, lt_of_le_of_lt hi (mem_rnds.mp ha).2⟩

open scoped Classical in
/-- **The path-collision fraction.** If the coordinates `Y` are `(q, (h, k, k'))`, each `q` fixing a
permutation `π q` and paths over `I` with distinct first blocks and at most `N` rounds in all, and
the event `Bd` gives a `PermGood (π q) G` permutation whose `h`-cells over all rounds collide, then
`Bd` holds for at most a fraction `N² / |X| + N² (G + 1) / |Z|` of `Y`. -/
theorem frac_pathColl_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq S]
    {Q Y : Type} [Fintype Q] [Nonempty Q] [Fintype Y] (e : Q × ((Z → X) × (X → Z) × (X → Z)) ≃ Y)
    (πf : Q → Equiv.Perm (X × Z)) (blk : Q → S → ℕ → X) (len : Q → S → ℕ) (I : Finset S)
    (hfirst : ∀ q, Set.InjOn (fun p ↦ blk q p 0) I) (G N : ℕ)
    (hN : ∀ q, (rnds I (len q)).card ≤ N) (Bd : Y → Prop) [DecidablePred Bd]
    (hBd : ∀ q t, Bd (e (q, t)) → PermGood (πf q) G ∧
      ¬Set.InjOn (famZ (πf q) (blk q) t.1 t.2.1 t.2.2) (rnds I (len q))) :
    (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card ≤
      ((N * N : ℕ) : ℝ≥0∞) / Fintype.card X + ((N * N * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z := by
  set T := Fintype.card ((Z → X) × (X → Z) × (X → Z))
  have hT : T = Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) := by
    simp only [T, Fintype.card_prod]
    ring
  have hq : ∀ q, Fintype.card X * Fintype.card Z * ∑ t, (if Bd (e (q, t)) then 1 else 0) ≤
      T * (N * N * (Fintype.card Z + (G + 1) * Fintype.card X)) := by
    intro q
    by_cases hG : PermGood (πf q) G
    · have hf : ∀ a ∈ rnds I (len q), ∀ b ∈ rnds I (len q), a.2 = 0 → b.2 = 0 →
          blk q a.1 0 = blk q b.1 0 → a.1 = b.1 := fun a ha b hb _ _ e' ↦
        hfirst q (Finset.mem_coe.mpr (mem_rnds.mp ha).1) (Finset.mem_coe.mpr (mem_rnds.mp hb).1) e'
      calc Fintype.card X * Fintype.card Z * ∑ t, (if Bd (e (q, t)) then 1 else 0)
          ≤ Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
              (if ¬Set.InjOn (famZ (πf q) (blk q) t.1 t.2.1 t.2.2) (rnds I (len q)) then 1
                else 0) :=
            Nat.mul_le_mul_left _ (sum_ite_le_of_imp _ _ fun t ht ↦ (hBd q t ht).2)
        _ ≤ Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
              ((rnds I (len q)).card * (rnds I (len q)).card *
                (Fintype.card Z + (G + 1) * Fintype.card X)) :=
            card_mul_sum_not_injOn_le (downClosed_rnds I (len q)) hf hG.rate
        _ ≤ T * (N * N * (Fintype.card Z + (G + 1) * Fintype.card X)) := by
            rw [hT]
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul (hN q) (hN q)))
    · have h0 : ∀ t, ¬Bd (e (q, t)) := fun t ht ↦ hG (hBd q t ht).1
      simp [h0]
  have hcount : (Finset.univ.filter Bd).card = ∑ q, ∑ t, (if Bd (e (q, t)) then 1 else 0) := by
    rw [Finset.card_filter, ← Fintype.sum_equiv e (fun x ↦ if Bd (e x) then 1 else 0) _
      (fun _ ↦ rfl)]
    exact Fintype.sum_prod_type _
  have hY : Fintype.card Y = Fintype.card Q * T := by
    rw [← Fintype.card_congr e, Fintype.card_prod]
  have hnat : Fintype.card X * Fintype.card Z * (Finset.univ.filter Bd).card ≤
      Fintype.card Y * (N * N * Fintype.card Z + N * N * (G + 1) * Fintype.card X) := by
    rw [hcount, Finset.mul_sum, hY]
    calc ∑ q, Fintype.card X * Fintype.card Z * ∑ t, (if Bd (e (q, t)) then 1 else 0)
        ≤ ∑ _q : Q, T * (N * N * (Fintype.card Z + (G + 1) * Fintype.card X)) :=
          Finset.sum_le_sum fun q _ ↦ hq q
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  have hX0 : (Fintype.card X : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ0 : (Fintype.card Z : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hY0 : (Fintype.card Y : ℝ≥0∞) ≠ 0 := by
    rw [hY, hT]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero Fintype.card_ne_zero (Nat.mul_ne_zero
      (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero) Fintype.card_ne_zero))
  have h1 := natCast_le_mul_div_of_mul_le
    (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero) hnat
  calc (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card
      ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ * (Fintype.card Y *
          (((N * N * Fintype.card Z + N * N * (G + 1) * Fintype.card X : ℕ) : ℝ≥0∞) /
            ((Fintype.card X * Fintype.card Z : ℕ) : ℝ≥0∞))) := by
        gcongr
    _ = ((N * N * Fintype.card Z + N * N * (G + 1) * Fintype.card X : ℕ) : ℝ≥0∞) /
          ((Fintype.card X * Fintype.card Z : ℕ) : ℝ≥0∞) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hY0 (ENNReal.natCast_ne_top _), one_mul]
    _ = _ := by
        push_cast
        rw [ENNReal.add_div, ENNReal.mul_div_mul_right _ _ hZ0 (ENNReal.natCast_ne_top _),
          mul_comm (Fintype.card X : ℝ≥0∞) (Fintype.card Z : ℝ≥0∞),
          ENNReal.mul_div_mul_right _ _ hX0 (ENNReal.natCast_ne_top _)]

end generic

/-! ## leanXMSS -/

section xmss

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-- The blocks of an in-table output's slot input, from the public parameter and the values. -/
def xBlk (P : PublicParameter) (v : ValPos → Digest) (p : ValPos) (j : ℕ) : X :=
  (blocks (thInput P (slotFields (outSlot p)) (slotPayload v (outSlot p)))).getD j 0

/-- The number of blocks of an in-table output's slot input. -/
def xLen (P : PublicParameter) (p : ValPos) : ℕ :=
  (blocks (thInput P (slotFields (outSlot p)) (slotPayload (fun _ ↦ 0) (outSlot p)))).length

theorem nBlocks_xPub_eq (w : XW) (h : Z → X) (p : ValPos) :
    nBlocks (xPub w h) (outSlot p) = xLen w.1 p :=
  rfl

/-- **The template's states are the path's states.** -/
theorem stateAt_eq_rnSt (w : XW) (h : Z → X) (msg : List X) :
    ∀ j, j ≤ msg.length →
      stateAt (xPub w h) msg j = rnSt w.2.1 h w.2.2.1 w.2.2.2 (fun i ↦ msg.getD i 0) j
  | 0, _ => rfl
  | j + 1, hj => by
    rw [stateAt_succ _ _ (by omega), stateAt_eq_rnSt w h msg j (by omega)]
    rfl

/-- **The template's `h`-cells are the path's.** -/
theorem roundH_fst_eq_rnZ (w : XW) (h : Z → X) (s : Slot) (v : ValPos → Digest) {j : ℕ}
    (hj : j < nBlocks (xPub w h) s) :
    (roundH (xPub w h) s v j).1 = rnZ w.2.1 h w.2.2.1 w.2.2.2
      (fun i ↦ (blocks (slotInput (xPub w h) s v)).getD i 0) j := by
  rw [roundH_fst, stateAt_eq_rnSt w h _ j (by rw [length_blocks_slotInput]; omega)]
  rfl

/-- **The output cell is the path's last `h`-cell.** -/
theorem outCap_eq_rnZ (w : XW) (h : Z → X) (s : Slot) (v : ValPos → Digest) :
    outCap (xPub w h) s v = rnZ w.2.1 h w.2.2.1 w.2.2.2
      (fun i ↦ (blocks (slotInput (xPub w h) s v)).getD i 0) (nBlocks (xPub w h) s - 1) := by
  unfold outCap outMid
  rw [stateAt_eq_rnSt w h _ _ (by rw [length_blocks_slotInput]; omega)]
  rfl

/-- The payload of an in-table output's slot: `32` bytes, or `928` for a leaf. -/
theorem length_slotPayload_outSlot (v : ValPos → Digest) (p : ValPos) :
    32 ≤ (slotPayload v (outSlot p)).length ∧ (slotPayload v (outSlot p)).length ≤ 928 := by
  cases p with
  | chain l e i j =>
    simp only [outSlot, slotPayload, Verification.chainPayload, List.length_append, length_le16,
      length_littleEndianBytes]
    omega
  | tree l level index =>
    by_cases hl : level.val = 0
    · rw [show outSlot (.tree l level index) = .leaf l (leafKey index.val) from ite_eq_left hl]
      simp only [slotPayload]
      rw [length_digestsPayload]
      simp only [chainCount]
      omega
    · rw [show outSlot (.tree l level index) = .node l level.val index.val from ite_eq_right hl]
      simp only [slotPayload, nodePayload, List.length_append, length_le16]
      omega

/-- At most `8` blocks per slot. -/
theorem xLen_le (P : PublicParameter) (p : ValPos) : xLen P p ≤ 8 := by
  have := (length_slotPayload_outSlot (fun _ ↦ 0) p).2
  unfold xLen
  rw [length_blocks, length_thInput]
  omega

/-- **An in-table output's first block names its slot.** -/
theorem slotOfBlock_xBlk (P : PublicParameter) (v : ValPos → Digest) {p : ValPos}
    (hp : InPos p) : slotOfBlock P (xBlk P v p 0) = some (outSlot p) := by
  have hlen := (length_slotPayload_outSlot v p).1
  have hs : slotOf P (absorbTail (Equiv.refl (X × Z))
      (blocks (thInput P (slotFields (outSlot p)) (slotPayload v (outSlot p))))) =
      some (outSlot p) := by
    cases p with
    | chain l e i j => exact slotOf_chain _ P l e _ i _
    | tree l level index =>
      by_cases hl : level.val = 0
      · rw [show outSlot (.tree l level index) = .leaf l (leafKey index.val) from ite_eq_left hl]
        exact slotOf_leaf _ P l _ _
      · rw [show outSlot (.tree l level index) = .node l level.val index.val from
          ite_eq_right hl]
        exact slotOf_node _ P l level.val index.val
          (lt_of_lt_of_le level.isLt (by simp only [layerHeight]; norm_num)) index.isLt _ _
  rw [slotOf_thInput _ _ _ _ _ hlen] at hs
  unfold xBlk
  rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, head?_blocks, Option.getD_some,
    slotOfBlock_thInput _ _ _ _ hlen]
  exact hs

/-- **Distinct in-table outputs have distinct first blocks.** -/
theorem xBlk_injOn (P : PublicParameter) (v : ValPos → Digest) :
    Set.InjOn (fun p ↦ xBlk P v p 0) xI := fun a ha b hb e ↦ by
  have ha' := mem_xI.mp (Finset.mem_coe.mp ha)
  have hb' := mem_xI.mp (Finset.mem_coe.mp hb)
  have h1 := slotOfBlock_xBlk P v ha'
  rw [show xBlk P v a 0 = xBlk P v b 0 from e, slotOfBlock_xBlk P v hb'] at h1
  have hab : outSlot a = outSlot b := (Option.some.inj h1).symm
  calc a = slotOutPos (outSlot a) := (slotOutPos_outSlot ha').symm
    _ = slotOutPos (outSlot b) := by rw [hab]
    _ = b := slotOutPos_outSlot hb'

/-- **Distinct `h`-cells over all rounds exclude `PathBad`.** -/
theorem not_injOn_of_pathBad {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hbad : PathBad ((h, w), v)) :
    ¬Set.InjOn (famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2) (rnds xI (xLen w.1)) := by
  intro hinj
  have hz : ∀ p, ∀ j < xLen w.1 p, (roundH (xPub w h) (outSlot p) v j).1 =
      famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, j) :=
    fun p j hj ↦ roundH_fst_eq_rnZ w h (outSlot p) v hj
  have hc : ∀ p, outCap (xPub w h) (outSlot p) v =
      famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, xLen w.1 p - 1) :=
    fun p ↦ outCap_eq_rnZ w h (outSlot p) v
  have hmem : ∀ p ∈ xI, ∀ j < xLen w.1 p,
      ((p, j) : ValPos × ℕ) ∈ (↑(rnds xI (xLen w.1)) : Set (ValPos × ℕ)) :=
    fun p hp j hj ↦ Finset.mem_coe.mpr (mem_rnds.mpr ⟨hp, hj⟩)
  have hpos : ∀ p, 1 ≤ xLen w.1 p := fun p ↦ nBlocks_pos (xPub w h) (outSlot p)
  rcases hbad with hL | hP
  · refine hL fun p hp _ q hq hne e ↦ hne ?_
    have e' : famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (q, xLen w.1 q - 1) =
        famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, xLen w.1 p - 1) :=
      (hc q).symm.trans (e.symm.trans (hc p))
    exact congrArg Prod.fst (hinj (hmem q hq _ (by have := hpos q; omega))
      (hmem p hp _ (by have := hpos p; omega)) e')
  · refine hP fun p hp q hq j hj e ↦ ?_
    have hj' : j + 1 < xLen w.1 p := hj
    have e' := (hz p j (by omega)).symm.trans (e.trans (hc q))
    have hpq := hinj (hmem p hp j (by omega)) (hmem q hq _ (by have := hpos q; omega)) e'
    have h1 : p = q := congrArg Prod.fst hpq
    have h2 : j = xLen w.1 q - 1 := congrArg Prod.snd hpq
    subst h1
    omega

/-- The coordinates other than the keys: the public parameter, `π`, the values. -/
abbrev RnQ : Type :=
  PublicParameter × Equiv.Perm (X × Z) × (ValPos → Digest)

/-- The public coordinates as `(q, (h, k, k'))`. -/
def rnEquiv : RnQ × ((Z → X) × (X → Z) × (X → Z)) ≃ ((Z → X) × XW) × (ValPos → Digest) where
  toFun x := ((x.2.1, (x.1.1, x.1.2.1, x.2.2.1, x.2.2.2)), x.1.2.2)
  invFun y := ((y.1.2.1, y.1.2.2.1, y.2), (y.1.1, y.1.2.2.2.1, y.1.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_rnds_xI_le (P : PublicParameter) : (rnds xI (xLen P)).card ≤ 8 * xI.card :=
  card_rnds_le xI (xLen P) (xLen_le P)

open scoped Classical in
/-- **The path-collision event on good permutations**: `PermGood π G ∧ PathBad` for at most a
fraction `N² / |X| + N² (G + 1) / |Z|` of the public coordinates, `N = 8 |xI|` the rounds of the
in-table paths. -/
theorem pathBad_good_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ PathBad y).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z :=
  frac_pathColl_le rnEquiv (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2) (fun q ↦ xLen q.1) xI
    (fun q ↦ xBlk_injOn q.1 q.2.2) G _ (fun q ↦ card_rnds_xI_le q.1) _ fun q t hb ↦
      ⟨hb.1, not_injOn_of_pathBad (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1) (v := q.2.2) hb.2⟩

open scoped Classical in
/-- **The path-collision fraction of leanXMSS**: `PathBad` for at most the bad permutations plus
`N² / |X| + N² (G + 1) / |Z|`, `N = 8 |xI|`. -/
theorem pathBad_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y ↦ PathBad y).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z) := by
  set N := Fintype.card (((Z → X) × XW) × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp (fun y ↦ PathBad y)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦ ¬PermGood (permEquiv y).1 G)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦ PermGood y.1.2.2.1 G ∧ PathBad y)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y ↦ PathBad y).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ PathBad y).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ PathBad y).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst permEquiv fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (pathBad_good_frac_le G)

/-! ### At Keccak's sizes -/

/-- Positions as tuples of their indices. -/
def vpCode : ValPos → (Layer × KeyIndex × ChainIndex × Fin chainLength) ⊕
    (Layer × Fin (layerHeight + 1) × Fin (2 ^ 32))
  | .chain l e i j => .inl (l, e, i, j)
  | .tree l level index => .inr (l, level, index)

theorem vpCode_injective : Function.Injective vpCode := by
  intro a b hab
  cases a <;> cases b <;> simp_all [vpCode]

theorem card_valPos_le : Fintype.card ValPos ≤ 498 * 2 ^ 32 := by
  refine (Fintype.card_le_of_injective _ vpCode_injective).trans ?_
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, lifetime, chainCount, chainLength, winternitzBits, layerHeight]

theorem card_xI_le : xI.card ≤ 498 * 2 ^ 32 :=
  (Finset.card_le_univ _).trans card_valPos_le

theorem rnCard_X : Fintype.card X = 2 ^ 1088 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem rnCard_Z : Fintype.card Z = 2 ^ 512 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem natCast_div_eq_ofReal (a b : ℕ) (hb : 0 < b) :
    (a : ℝ≥0∞) / b = ENNReal.ofReal ((a : ℝ) / b) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

set_option exponentiation.threshold 4096 in
/-- The collision terms at Keccak's sizes, for `n ≤ 498 · 2^32` paths and `G = 18`. -/
theorem collTerms_le {n cX cZ : ℕ} (hn : n ≤ 498 * 2 ^ 32) (hX : cX = 2 ^ 1088)
    (hZ : cZ = 2 ^ 512) :
    ((8 * n * (8 * n) : ℕ) : ℝ≥0∞) / cX + ((8 * n * (8 * n) * (18 + 1) : ℕ) : ℝ≥0∞) / cZ ≤
      ENNReal.ofReal (1 / 2 ^ 401) := by
  subst hX hZ
  have hNN : 8 * n * (8 * n) ≤ 2 ^ 88 := by
    have h8 : 8 * n ≤ 8 * (498 * 2 ^ 32) := Nat.mul_le_mul_left 8 hn
    calc 8 * n * (8 * n) ≤ 8 * (498 * 2 ^ 32) * (8 * (498 * 2 ^ 32)) := Nat.mul_le_mul h8 h8
      _ ≤ 2 ^ 88 := by norm_num
  have hNN' : 8 * n * (8 * n) * (18 + 1) ≤ 2 ^ 88 * 19 :=
    (Nat.mul_le_mul_right _ hNN).trans_eq (by norm_num)
  rw [natCast_div_eq_ofReal (8 * n * (8 * n)) (2 ^ 1088) (by positivity),
    natCast_div_eq_ofReal (8 * n * (8 * n) * (18 + 1)) (2 ^ 512) (by positivity),
    ← ENNReal.ofReal_add (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  apply ENNReal.ofReal_le_ofReal
  have hb : ((8 * n * (8 * n) : ℕ) : ℝ) / ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 88 / 2 ^ 1088 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hNN) (by positivity)
  have hc : ((8 * n * (8 * n) * (18 + 1) : ℕ) : ℝ) / ((2 ^ 512 : ℕ) : ℝ) ≤
      2 ^ 88 * 19 / 2 ^ 512 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hNN') (by positivity)
  calc _ ≤ 2 ^ 88 / 2 ^ 1088 + 2 ^ 88 * 19 / 2 ^ 512 := add_le_add hb hc
    _ ≤ 1 / 2 ^ 401 := by norm_num

/-- The bad permutations at Keccak's sizes: `2^-777`. -/
theorem permTerm_le_keccak :
    ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18).card : ℝ≥0∞) /
        Fintype.card (Equiv.Perm (X × Z)) ≤ ENNReal.ofReal (1 / 2 ^ 777) := by
  rw [natCast_div_eq_ofReal _ (Fintype.card (Equiv.Perm (X × Z))) Fintype.card_pos]
  exact ENNReal.ofReal_le_ofReal (prob_not_permGood_keccak rnCard_X rnCard_Z)

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The path-collision fraction at Keccak's sizes**: at most `2^-400` (with `G = 18`: the bad
permutations `2^-777`, the collisions `2^-401` from `|xI| ≤ 498 · 2^32`). -/
theorem pathBad_frac_le_keccak :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y ↦ PathBad y).card ≤ ENNReal.ofReal (1 / 2 ^ 400) := by
  refine ((pathBad_frac_le 18).trans (add_le_add permTerm_le_keccak
    (collTerms_le card_xI_le rnCard_X rnCard_Z))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777)
    (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 401)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end xmss

end Quantum.Xmss.Assembly

end
