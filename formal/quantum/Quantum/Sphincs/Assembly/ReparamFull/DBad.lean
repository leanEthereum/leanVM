module

public import Quantum.Sphincs.Assembly.ReparamFull.Game

@[expose] public section

/-!
# The composed reparametrization of leanSPHINCS's tables: the digest stage's bad fraction

The digest stage `dLast` runs on Reparam's coordinates `YS`; its good set `DGoodYS` asks for
distinct rates of the labels' first blocks (`RateInjY`) and that no round of an in-table path
reads a label's cell after the path stages (`PReadIn`). Both are counted over the coordinates
`DY` (`yView` and the path stages are bijections).

* **Rates** (`frac_not_rateInjY_le`): `|DLab|² / |X|`, averaged over `π`.
* **Rates and capacities read** (`frac_readKH_le`, RStage's `card_mul_sum_pReadKH_le`): the
  labels' `k`- and `k'`-coins resampled, `|DLab| (G + 1) q / |Z|` with `q = 24 |xI|` reads.
* **First blocks read** (`frac_kHitY_le`): an in-table round's `k`-cell is a label's first block.
  At the first round (`E0`) the round's block and the `H_msg` block share bits `128` to `383`, the
  address on one side and `PK.seed ‖ PK.root` on the other (`rateSlice_xBlk_lo`, `_hi`), so
  `(PK.seed, PK.root)` is one of `|xI|` pairs: `|xI| / 2^256` (`card_mul_card_filter_E0_le`,
  `frac_E0_le`). At a later
  round the `k`-cell moves with `h` at the previous `h`-cell (`card_mul_sum_kHit_le`, the
  `h`-cells distinct below it), `|DLab| / |X|` per round, unless the in-table `h`-cells collide
  (PathBad's count): `frac_readK_le` over abstract types.
* Bad's `frac_dGoodYS_le_keccak`: at most the bad permutations and `2^-198` of the coordinates.
* Counts at `DLab` go through generic lemmas whose instantiation is the statement verbatim
  (`frac_pReadKH_le`, `card_mul_card_filter_pair_le`), and membership in all labels' cells
  through the irreducible `imgCells`: the kernel evaluates closed card products otherwise.
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest HashOutput Message PublicParameter Randomizer MasterSeed)
open Quantum.Xmss (X Z out256 trunc128 rateSlice blockOf firstBlock inputBit)
open Quantum.Xmss.Hybrid (CoinSlots IsFirst capOf rateOf kCells k'Cells hCells mem_kCells
  sum_ite_add_mem_eq_card card_mul_sum_le_of_update card_mul_sum_equiv_prod_le
  card_mul_sum_not_injective_rate_le natCast_le_mul_div_of_mul_le)
open Quantum.Xmss.Assembly (fwd XW famK famR famZ rnds mem_rnds rnK rnR rnZ rnSt rnSt_succ
  rnK_zero RnAgree rnR_congr rnZ_congr InjBelow DownClosed downClosed_rnds injBelow_congr
  agree_h fam_eq_h card_mul_sum_le_of_moving sum_ite_le_of_imp card_mul_sum_triple_le₁
  card_mul_sum_not_injOn_le card_filter_le_add_of_imp inv_card_mul_card_filter_comp_fst)
open Quantum.Sphincs.Hybrid (PSt DLab dLabCell dLabOrd pStages pCellK pCellK' pCellH PReadGood
  pKHit pK'Hit pHHit pReadK pReadKH SkIdx card_dLab)

namespace Quantum.Sphincs.Assembly

/-! ## A later round's `k`-cell in a fixed set, over abstract types -/

section generic

variable {X Z S : Type} [AddCommGroup X] [AddCommGroup Z] {π : Equiv.Perm (X × Z)}
  {blk : S → ℕ → X}

open scoped Classical in
/-- **A later round's `k`-cell hits a fixed set** `D` for at most `|D| / |X|` of `h`, when the
`h`-cells of the earlier rounds are distinct. -/
theorem card_mul_sum_kHit_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {R : Finset (S × ℕ)}
    (hR : DownClosed R) {p : S} {j₀ : ℕ} (ha : (p, j₀ + 1) ∈ R) (D : Finset X) (k k' : X → Z) :
    Fintype.card X * ∑ h : Z → X, (if InjBelow R (famZ π blk h k k') (j₀ + 1) ∧
        famK π blk h k k' (p, j₀ + 1) ∈ D then 1 else 0) ≤
      Fintype.card (Z → X) * D.card := by
  have hp : (p, j₀) ∈ R := hR _ ha j₀ (Nat.le_succ j₀)
  refine card_mul_sum_le_of_moving _ (fun h ↦ InjBelow R (famZ π blk h k k') (j₀ + 1))
    (fun h ↦ famK π blk h k k' (p, j₀ + 1) ∈ D) (fun h ↦ rnZ π h k k' (blk p) j₀) D.card
    (fun _ hE ↦ hE) (fun h hP β ↦ ?_) (fun h hP ↦ ?_)
  · have hf := fun (x : S × ℕ) (hx : x ∈ R) (hxj : x.2 < j₀ + 1) ↦
      fam_eq_h hR hp hP β hx (by omega)
    exact ⟨injBelow_congr (fun x hx hxj ↦ (hf x hx hxj).2.2) hP,
      (fam_eq_h hR hp hP β hp le_rfl).2.2⟩
  · refine (sum_ite_le_of_imp _
      (fun β ↦ (rnR π h k k' (blk p) j₀ + blk p (j₀ + 1)) + β ∈ D) fun β hβ ↦ ?_).trans
      (sum_ite_add_mem_eq_card D _).le
    have hAp := agree_h hR hp hP β hp (by omega) fun i' hi' e ↦
      (show i' ≠ j₀ by omega) (congrArg Prod.snd e)
    have hKa : famK π blk (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (p, j₀ + 1) =
        rnR π h k k' (blk p) j₀ + β + blk p (j₀ + 1) := by
      show (rnSt π (Function.update h (rnZ π h k k' (blk p) j₀) β) k k' (blk p) (j₀ + 1)).1 +
        blk p (j₀ + 1) = _
      rw [rnSt_succ, rnR_congr hAp rfl, rnZ_congr hAp rfl rfl, Function.update_self]
    rw [hKa, add_right_comm] at hβ
    exact hβ

open scoped Classical in
/-- **The first-block read fraction.** If the coordinates `Y` are `(q, (h, k, k'))`, each `q`
fixing a permutation, paths over `I` with distinct first blocks and at most `N` rounds, and sets
`D q` of at most `m` cells, and the event `Bd` gives a `PermGood` permutation and either colliding
`h`-cells or a later round's `k`-cell in `D q` with distinct earlier `h`-cells, then `Bd` holds for
at most `N² / |X| + N² (G + 1) / |Z| + N m / |X|` of `Y`. -/
theorem frac_readK_le [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq S]
    {Q Y : Type} [Fintype Q] [Fintype Y] (e : Q × ((Z → X) × (X → Z) × (X → Z)) ≃ Y)
    (πf : Q → Equiv.Perm (X × Z)) (bl : Q → S → ℕ → X) (len : Q → S → ℕ) (I : Finset S)
    (hfirst : ∀ q, Set.InjOn (fun p ↦ bl q p 0) I) (G N : ℕ)
    (hN : ∀ q, (rnds I (len q)).card ≤ N) (D : Q → Finset X) (m : ℕ)
    (hD : ∀ q, (D q).card ≤ m) (Bd : Y → Prop) [DecidablePred Bd]
    (hBd : ∀ q t, Bd (e (q, t)) → PermGood (πf q) G ∧
      (¬Set.InjOn (famZ (πf q) (bl q) t.1 t.2.1 t.2.2) (rnds I (len q)) ∨
        ∃ p j₀, (p, j₀ + 1) ∈ rnds I (len q) ∧
          InjBelow (rnds I (len q)) (famZ (πf q) (bl q) t.1 t.2.1 t.2.2) (j₀ + 1) ∧
          famK (πf q) (bl q) t.1 t.2.1 t.2.2 (p, j₀ + 1) ∈ D q)) :
    (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card ≤
      ((N * N : ℕ) : ℝ≥0∞) / Fintype.card X + ((N * N * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ((N * m : ℕ) : ℝ≥0∞) / Fintype.card X := by
  set T := Fintype.card ((Z → X) × (X → Z) × (X → Z))
  have hT : T = Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) := by
    simp only [T, Fintype.card_prod]
    ring
  have hq : ∀ q, Fintype.card X * Fintype.card Z * ∑ t, (if Bd (e (q, t)) then 1 else 0) ≤
      T * (N * N * (Fintype.card Z + (G + 1) * Fintype.card X) + Fintype.card Z * (N * m)) := by
    intro q
    by_cases hG : PermGood (πf q) G
    · set R := rnds I (len q) with hRdef
      have hf : ∀ a ∈ R, ∀ b ∈ R, a.2 = 0 → b.2 = 0 → bl q a.1 0 = bl q b.1 0 → a.1 = b.1 :=
        fun a ha b hb _ _ e' ↦ hfirst q (Finset.mem_coe.mpr (mem_rnds.mp ha).1)
          (Finset.mem_coe.mpr (mem_rnds.mp hb).1) e'
      set F : (Z → X) → (X → Z) → (X → Z) → ℕ := fun h k k' ↦
        ∑ r ∈ R, (if 1 ≤ r.2 ∧ InjBelow R (famZ (πf q) (bl q) h k k') r.2 ∧
          famK (πf q) (bl q) h k k' r ∈ D q then 1 else 0) with hF
      have hpt : ∀ t : (Z → X) × (X → Z) × (X → Z), (if Bd (e (q, t)) then 1 else 0) ≤
          (if ¬Set.InjOn (famZ (πf q) (bl q) t.1 t.2.1 t.2.2) R then 1 else 0) +
            F t.1 t.2.1 t.2.2 := by
        intro t
        by_cases hb : Bd (e (q, t))
        · rw [ite_eq_left hb]
          rcases (hBd q t hb).2 with h1 | ⟨p, j₀, hr, hinj, hk⟩
          · rw [ite_eq_left h1]
            exact Nat.le_add_right _ _
          · refine le_add_left (le_trans ?_ (Finset.single_le_sum
              (f := fun r ↦ if 1 ≤ r.2 ∧ InjBelow R (famZ (πf q) (bl q) t.1 t.2.1 t.2.2) r.2 ∧
                famK (πf q) (bl q) t.1 t.2.1 t.2.2 r ∈ D q then 1 else 0)
              (fun _ _ ↦ Nat.zero_le _) hr))
            rw [ite_eq_left ⟨Nat.succ_pos j₀, hinj, hk⟩]
        · rw [ite_eq_right hb]
          exact Nat.zero_le _
      have hI := card_mul_sum_not_injOn_le (downClosed_rnds I (len q)) hf hG.rate
      have hK : Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z), F t.1 t.2.1 t.2.2 ≤
          Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) * (N * m) := by
        refine card_mul_sum_triple_le₁ F _ _ fun k k' ↦ ?_
        calc Fintype.card X * ∑ h, F h k k'
            = ∑ r ∈ R, Fintype.card X * ∑ h : Z → X, (if 1 ≤ r.2 ∧
                InjBelow R (famZ (πf q) (bl q) h k k') r.2 ∧
                famK (πf q) (bl q) h k k' r ∈ D q then 1 else 0) := by
              simp only [hF, Finset.mul_sum]
              exact Finset.sum_comm
          _ ≤ ∑ _r ∈ R, Fintype.card (Z → X) * m := Finset.sum_le_sum fun r hr ↦ by
              obtain ⟨p, j⟩ := r
              rcases j with _ | j₀
              · simp
              · simp only [Nat.le_add_left, true_and]
                exact (card_mul_sum_kHit_le (downClosed_rnds I (len q)) hr (D q) k k').trans
                  (Nat.mul_le_mul_left _ (hD q))
          _ = R.card * (Fintype.card (Z → X) * m) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ N * (Fintype.card (Z → X) * m) := Nat.mul_le_mul_right _ (hN q)
          _ = Fintype.card (Z → X) * (N * m) := by ring
      calc Fintype.card X * Fintype.card Z * ∑ t, (if Bd (e (q, t)) then 1 else 0)
          ≤ Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
              ((if ¬Set.InjOn (famZ (πf q) (bl q) t.1 t.2.1 t.2.2) R then 1 else 0) +
                F t.1 t.2.1 t.2.2) :=
            Nat.mul_le_mul_left _ (Finset.sum_le_sum fun t _ ↦ hpt t)
        _ = Fintype.card X * Fintype.card Z * ∑ t : (Z → X) × (X → Z) × (X → Z),
              (if ¬Set.InjOn (famZ (πf q) (bl q) t.1 t.2.1 t.2.2) R then 1 else 0) +
            Fintype.card Z * (Fintype.card X * ∑ t : (Z → X) × (X → Z) × (X → Z),
              F t.1 t.2.1 t.2.2) := by
            rw [Finset.sum_add_distrib]
            ring
        _ ≤ Fintype.card (Z → X) * Fintype.card (X → Z) * Fintype.card (X → Z) *
              (R.card * R.card * (Fintype.card Z + (G + 1) * Fintype.card X)) +
            Fintype.card Z * (Fintype.card (Z → X) * Fintype.card (X → Z) *
              Fintype.card (X → Z) * (N * m)) := Nat.add_le_add hI (Nat.mul_le_mul_left _ hK)
        _ ≤ T * (N * N * (Fintype.card Z + (G + 1) * Fintype.card X) +
              Fintype.card Z * (N * m)) := by
            rw [hT]
            refine le_of_le_of_eq (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
              (Nat.mul_le_mul (hN q) (hN q)))) le_rfl) (by ring)
    · have h0 : ∀ t, ¬Bd (e (q, t)) := fun t ht ↦ hG (hBd q t ht).1
      simp [h0]
  have hcount : (Finset.univ.filter Bd).card = ∑ q, ∑ t, (if Bd (e (q, t)) then 1 else 0) := by
    rw [Finset.card_filter, ← Fintype.sum_equiv e (fun x ↦ if Bd (e x) then 1 else 0) _
      (fun _ ↦ rfl)]
    exact Fintype.sum_prod_type _
  have hY : Fintype.card Y = Fintype.card Q * T := by
    rw [← Fintype.card_congr e, Fintype.card_prod]
  have hnat : Fintype.card X * Fintype.card Z * (Finset.univ.filter Bd).card ≤
      Fintype.card Y * (N * N * Fintype.card Z + N * N * (G + 1) * Fintype.card X +
        N * m * Fintype.card Z) := by
    rw [hcount, Finset.mul_sum, hY]
    calc ∑ q, Fintype.card X * Fintype.card Z * ∑ t, (if Bd (e (q, t)) then 1 else 0)
        ≤ ∑ _q : Q, T * (N * N * (Fintype.card Z + (G + 1) * Fintype.card X) +
            Fintype.card Z * (N * m)) :=
          Finset.sum_le_sum fun q _ ↦ hq q
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  rcases eq_or_ne (Fintype.card Y) 0 with hY | hY0
  · have h0 : (Finset.univ.filter Bd).card = 0 :=
      Nat.eq_zero_of_le_zero ((Finset.card_filter_le _ _).trans_eq (by rw [Finset.card_univ, hY]))
    rw [h0, Nat.cast_zero, mul_zero]
    exact zero_le
  have hX0 : (Fintype.card X : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ0 : (Fintype.card Z : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hY0 : (Fintype.card Y : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hY0
  have h1 := natCast_le_mul_div_of_mul_le
    (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero) hnat
  calc (Fintype.card Y : ℝ≥0∞)⁻¹ * (Finset.univ.filter Bd).card
      ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ * (Fintype.card Y *
          (((N * N * Fintype.card Z + N * N * (G + 1) * Fintype.card X +
            N * m * Fintype.card Z : ℕ) : ℝ≥0∞) /
            ((Fintype.card X * Fintype.card Z : ℕ) : ℝ≥0∞))) := by
        gcongr
    _ = ((N * N * Fintype.card Z + N * N * (G + 1) * Fintype.card X +
            N * m * Fintype.card Z : ℕ) : ℝ≥0∞) /
          ((Fintype.card X * Fintype.card Z : ℕ) : ℝ≥0∞) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hY0 (ENNReal.natCast_ne_top _), one_mul]
    _ = _ := by
        push_cast
        rw [ENNReal.add_div, ENNReal.add_div,
          ENNReal.mul_div_mul_right _ _ hZ0 (ENNReal.natCast_ne_top _),
          ENNReal.mul_div_mul_right _ _ hZ0 (ENNReal.natCast_ne_top _),
          mul_comm (Fintype.card X : ℝ≥0∞) (Fintype.card Z : ℝ≥0∞),
          ENNReal.mul_div_mul_right _ _ hX0 (ENNReal.natCast_ne_top _)]

/-- **Fixing one coordinate of a function**: at most `|A → B| / |B|` of the functions. -/
theorem card_mul_sum_apply_eq_le {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (c : A) (d : B) :
    Fintype.card B * ∑ f : A → B, (if f c = d then 1 else 0) ≤ Fintype.card (A → B) :=
  (card_mul_sum_le_of_update (fun f : A → B ↦ if f c = d then 1 else 0) c 1 fun f ↦ by
    simp [Function.update_self]).trans_eq (mul_one _)

/-- **An event forcing a pair to one of `|I|` values** holds for at most `|I| / (|P| |B|)` of
`P × V`, when the second part's value `rt` takes each value for at most `|V| / |B|` of `V`. -/
theorem card_mul_sum_pair_le {P V B ι : Type*} [Fintype P] [DecidableEq P] [Fintype V]
    [Fintype B] [DecidableEq B] (I : Finset ι) (lo : ι → P) (hi : ι → B) (rt : V → B)
    (hrt : ∀ b, Fintype.card B * ∑ v, (if rt v = b then 1 else 0) ≤ Fintype.card V)
    (E : P × V → Prop) [DecidablePred E] (hE : ∀ e, E e → ∃ p ∈ I, e.1 = lo p ∧ rt e.2 = hi p) :
    Fintype.card P * Fintype.card B * ∑ e : P × V, (if E e then 1 else 0) ≤
      Fintype.card (P × V) * I.card := by
  have hpt : ∀ e : P × V, (if E e then 1 else 0) ≤
      ∑ p ∈ I, (if e.1 = lo p then 1 else 0) * (if rt e.2 = hi p then 1 else 0) := by
    intro e
    by_cases h : E e
    · obtain ⟨p, hp, h1, h2⟩ := hE e h
      rw [ite_eq_left h]
      refine le_trans ?_ (Finset.single_le_sum (f := fun p ↦
        (if e.1 = lo p then 1 else 0) * (if rt e.2 = hi p then 1 else 0))
        (fun _ _ ↦ Nat.zero_le _) hp)
      rw [ite_eq_left h1, ite_eq_left h2]
    · rw [ite_eq_right h]
      exact Nat.zero_le _
  have hp : ∀ p, Fintype.card P * Fintype.card B * ∑ e : P × V,
      (if e.1 = lo p then 1 else 0) * (if rt e.2 = hi p then 1 else 0) ≤
        Fintype.card (P × V) := by
    intro p
    have hs : ∑ e : P × V, (if e.1 = lo p then 1 else 0) * (if rt e.2 = hi p then 1 else 0) =
        (∑ x : P, if x = lo p then 1 else 0) * ∑ v : V, (if rt v = hi p then 1 else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    rw [hs, Finset.sum_ite_eq' Finset.univ (lo p), ite_eq_left (Finset.mem_univ _), one_mul,
      Fintype.card_prod]
    calc Fintype.card P * Fintype.card B * ∑ v, (if rt v = hi p then 1 else 0)
        = Fintype.card P * (Fintype.card B * ∑ v, (if rt v = hi p then 1 else 0)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (hrt _)
  calc Fintype.card P * Fintype.card B * ∑ e : P × V, (if E e then 1 else 0)
      ≤ Fintype.card P * Fintype.card B * ∑ e : P × V, ∑ p ∈ I,
          (if e.1 = lo p then 1 else 0) * (if rt e.2 = hi p then 1 else 0) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun e _ ↦ hpt e)
    _ = ∑ p ∈ I, Fintype.card P * Fintype.card B * ∑ e : P × V,
          (if e.1 = lo p then 1 else 0) * (if rt e.2 = hi p then 1 else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ _p ∈ I, Fintype.card (P × V) := Finset.sum_le_sum fun p _ ↦ hp p
    _ = Fintype.card (P × V) * I.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **`card_mul_sum_pair_le` through an equivalence `W ≃ P × V`**, as a filter count. -/
theorem card_mul_card_filter_pair_le {W P V B ι : Type*} [Fintype W] [Fintype P] [DecidableEq P]
    [Fintype V] [Fintype B] [DecidableEq B] (e : W ≃ P × V) (I : Finset ι) (lo : ι → P)
    (hi : ι → B) (rt : V → B)
    (hrt : ∀ b, Fintype.card B * ∑ v, (if rt v = b then 1 else 0) ≤ Fintype.card V)
    (E : W → Prop) [DecidablePred E]
    (hE : ∀ w, E w → ∃ p ∈ I, (e w).1 = lo p ∧ rt (e w).2 = hi p) :
    Fintype.card P * Fintype.card B * (Finset.univ.filter E).card ≤
      Fintype.card W * I.card := by
  have h := card_mul_sum_pair_le I lo hi rt hrt (fun x ↦ E (e.symm x)) fun x hx ↦ by
    simpa using hE (e.symm x) hx
  have hc : (Finset.univ.filter E).card = ∑ x : P × V, (if E (e.symm x) then 1 else 0) := by
    rw [Finset.card_filter]
    exact (Fintype.sum_equiv e.symm _ _ fun _ ↦ rfl).symm
  rw [hc, Fintype.card_congr e]
  exact h

/-- `d a ≤ b c` gives `a / b ≤ c / d` in `ℝ≥0∞`. -/
theorem natCast_div_le_div_of_mul_le {a b c d : ℕ} (hd : d ≠ 0) (h : d * a ≤ b * c) :
    (a : ℝ≥0∞) / b ≤ (c : ℝ≥0∞) / d :=
  ENNReal.div_le_of_le_mul ((natCast_le_mul_div_of_mul_le hd h).trans_eq (mul_comm _ _))

/-- The image of all points. Irreducible: its membership does not unfold the enumeration of the
points. -/
@[irreducible]
noncomputable def imgCells {A B : Type*} [Fintype A] [DecidableEq B] (g : A → B) : Finset B :=
  Finset.univ.image g

theorem mem_imgCells {A B : Type*} [Fintype A] [DecidableEq B] (g : A → B) (a : A) :
    g a ∈ imgCells g := by
  unfold imgCells
  exact Finset.mem_image_of_mem g (Finset.mem_univ a)

theorem card_imgCells_le {A B : Type*} [Fintype A] [DecidableEq B] (g : A → B) :
    (imgCells g).card ≤ Fintype.card A := by
  unfold imgCells
  exact Finset.card_image_le.trans Finset.card_univ.le

/-- Four counts chained. -/
theorem nat_le_four {a b c b₁ b' b₂ b₃ d : ℕ} (h₄ : a ≤ b + c) (h₁ : b ≤ b₁ + b')
    (h₂ : b' ≤ b₂ + b₃) (hR : c ≤ d) : a ≤ b₁ + b₂ + b₃ + d := by
  omega

/-- **A count as a fraction**: `c ∑ F ≤ |T| d` gives `|T|⁻¹ ∑ F ≤ d / c`. -/
theorem frac_le_of_card_mul_sum_le {T : Type*} [Fintype T] (F : T → ℕ) {c d : ℕ} (hc : c ≠ 0)
    (h : c * ∑ t, F t ≤ Fintype.card T * d) :
    (Fintype.card T : ℝ≥0∞)⁻¹ * ((∑ t, F t : ℕ) : ℝ≥0∞) ≤ (d : ℝ≥0∞) / c := by
  rcases eq_or_ne (Fintype.card T) 0 with h0 | h0
  · have := Fintype.card_eq_zero_iff.mp h0
    simp
  have h1 := natCast_le_mul_div_of_mul_le hc h
  have hN : (Fintype.card T : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr h0
  refine (mul_le_mul' le_rfl h1).trans ?_
  rw [ENNReal.inv_mul_cancel_left hN (ENNReal.natCast_ne_top _)]

end generic

/-- **The rates and capacities read** (RStage's `card_mul_sum_pReadKH_le` at a constant read
bound `q`), as a fraction. -/
theorem frac_pReadKH_le {E F J ι : Type} [Fintype E] [Fintype F] [Fintype J] [DecidableEq J]
    (c : E → F → J → X) (G : ℕ)
    (rd : ι → (SpongeKeys X Z × Equiv.Perm (X × Z)) × E → List (SpongeRead X Z))
    (q : ℕ) (hq : ∀ i p, (rd i p).length ≤ q) (i : ι) :
    (Fintype.card (PSt E F J) : ℝ≥0∞)⁻¹ * ((∑ y, pReadKH c G rd i y : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card J * (G + 1) * q : ℕ) : ℝ≥0∞) / Fintype.card Z :=
  frac_le_of_card_mul_sum_le _ Fintype.card_ne_zero
    (Hybrid.card_mul_sum_pReadKH_le c G rd (fun _ ↦ q) hq i)

/-- A rate or capacity read at one label gives a read in the count. -/
theorem one_le_pReadKH {E F J ι : Type} [Fintype J] (c : E → F → J → X) (G : ℕ)
    (rd : ι → (SpongeKeys X Z × Equiv.Perm (X × Z)) × E → List (SpongeRead X Z)) (i : ι)
    (y : PSt E F J) (a : J)
    (h : (pCellK' c y a ∈ k'Cells (rd i y.1.1) ∧ PermGood y.1.1.1.2 G) ∨
      pCellH c y a ∈ hCells (rd i y.1.1)) :
    1 ≤ pReadKH c G rd i y := by
  have h2 : pK'Hit c G rd i a y + pHHit c rd i a y ≤ pReadKH c G rd i y :=
    Finset.single_le_sum (f := fun a' ↦ pK'Hit c G rd i a' y + pHHit c rd i a' y)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
  rcases h with ⟨hk', hG⟩ | hh
  · have h1 : pK'Hit c G rd i a y = 1 := ite_eq_left ⟨hG, hk'⟩
    omega
  · have h1 : pHHit c rd i a y = 1 := ite_eq_left hh
    omega

/-! ## The first round's block and the `H_msg` block -/

section bytes

/-- `length_le16` at the public parameter's type. -/
theorem length_le16P (a : PublicParameter) : (HashSig.littleEndianBytes 16 a).length = 16 :=
  Quantum.Xmss.length_littleEndianBytes 16 a

/-- Rate slices agreeing bit by bit are equal. -/
theorem rateSlice_congr {x y : X} {a n : ℕ} {h : a + n ≤ 1088}
    (hxy : ∀ j (hj : j < n), x ⟨a + j, by omega⟩ = y ⟨a + j, by omega⟩) :
    rateSlice x a n h = rateSlice y a n h := by
  unfold rateSlice
  congr 1
  funext j
  exact hxy j j.isLt

/-- **Bits `128` to `383` of an in-table slot's first block are its address**, whatever `PK.seed`
and the values. -/
theorem slotBlk_adrs_bit {s : Slot} (hs : InTable s) (P : PublicParameter) (v : ValPos → Digest)
    (i : ℕ) (h1 : 128 ≤ i) (h2 : i < 384) :
    slotBlk P s v 0 ⟨i, by omega⟩ =
      inputBit (hashDomainFields (slotDomain s)).toBytes (i - 128) := by
  rw [slotBlk_zero, slotInput_of_ne (ne_hmsg_of_inTable hs)]
  have hpre : HashSig.littleEndianBytes 16 P ++ (hashDomainFields (slotDomain s)).toBytes <+:
      addressedHashInput P (hashDomainFields (slotDomain s)) (slotPayload v s) :=
    List.prefix_append _ _
  have h := blockOf_firstBlock_of_prefix hpre (i - 128)
    (by rw [length_toBytes]; omega) (by rw [length_le16P, length_toBytes]; omega)
  have e : (⟨i, by omega⟩ : Fin 1088) =
      ⟨8 * (HashSig.littleEndianBytes 16 P).length + (i - 128), by rw [length_le16P]; omega⟩ :=
    Fin.ext (by simp only [length_le16P]; omega)
  rw [e]
  exact h

/-- The address bits `128` to `255` of an in-table output's first block. -/
def adrsLo (p : ValPos) : PublicParameter :=
  rateSlice (xBlk 0 (fun _ ↦ 0) p 0) 128 128 (by norm_num)

/-- The address bits `256` to `383` of an in-table output's first block. -/
def adrsHi (p : ValPos) : Digest :=
  rateSlice (xBlk 0 (fun _ ↦ 0) p 0) 256 128 (by norm_num)

theorem rateSlice_xBlk_lo {p : ValPos} (hp : p ∈ xI) (P : PublicParameter) (v : ValPos → Digest) :
    rateSlice (xBlk P v p 0) 128 128 (by norm_num) = adrsLo p := by
  have hs := inTable_outSlot (mem_xI.mp hp)
  exact rateSlice_congr fun j hj ↦
    (slotBlk_adrs_bit hs P v (128 + j) (by omega) (by omega)).trans
      (slotBlk_adrs_bit hs 0 (fun _ ↦ 0) (128 + j) (by omega) (by omega)).symm

theorem rateSlice_xBlk_hi {p : ValPos} (hp : p ∈ xI) (P : PublicParameter) (v : ValPos → Digest) :
    rateSlice (xBlk P v p 0) 256 128 (by norm_num) = adrsHi p := by
  have hs := inTable_outSlot (mem_xI.mp hp)
  exact rateSlice_congr fun j hj ↦
    (slotBlk_adrs_bit hs P v (256 + j) (by omega) (by omega)).trans
      (slotBlk_adrs_bit hs 0 (fun _ ↦ 0) (256 + j) (by omega) (by omega)).symm

theorem rateSlice_dLabCell_lo (a : DLab) (P : PublicParameter) (root : Digest) (R : Randomizer) :
    rateSlice (dLabCell a P root R) 128 128 (by norm_num) = P :=
  rateSlice_firstBlock (input := messageDigestInput R P root a.1 a.2)
    (a := HashSig.littleEndianBytes 16 R) (n := 16)
    (by simp [messageDigestInput, List.append_assoc]) (by rw [length_le16]) (by norm_num)

theorem rateSlice_dLabCell_hi (a : DLab) (P : PublicParameter) (root : Digest) (R : Randomizer) :
    rateSlice (dLabCell a P root R) 256 128 (by norm_num) = root :=
  rateSlice_firstBlock (input := messageDigestInput R P root a.1 a.2)
    (a := HashSig.littleEndianBytes 16 R ++ HashSig.littleEndianBytes 16 P) (n := 16)
    (by simp [messageDigestInput, List.append_assoc])
    (by rw [List.length_append, length_le16, length_le16P]) (by norm_num)

/-- **The first-round hit**: `(PK.seed, PK.root)` is an in-table output's address pair. -/
def E0 (e : DE) : Prop :=
  ∃ p ∈ xI, e.1 = adrsLo p ∧ e.2 rootPos = adrsHi p

/-- **An `H_msg` block is an in-table first block only at an address pair.** -/
theorem e0_of_eq {e : DE} {a : DLab} {R : Randomizer} {p : ValPos} (hp : p ∈ xI)
    (h : dLabCell a e.1 (e.2 rootPos) R = xBlk e.1 e.2 p 0) : E0 e :=
  ⟨p, hp, (rateSlice_dLabCell_lo a e.1 (e.2 rootPos) R).symm.trans
      ((congrArg (fun x ↦ rateSlice x 128 128 (by norm_num)) h).trans (rateSlice_xBlk_lo hp _ _)),
    (rateSlice_dLabCell_hi a e.1 (e.2 rootPos) R).symm.trans
      ((congrArg (fun x ↦ rateSlice x 256 128 (by norm_num)) h).trans (rateSlice_xBlk_hi hp _ _))⟩

end bytes

/-! ## The counts over the digest stage's coordinates -/

section counts

noncomputable instance instFintypeDE : Fintype DE :=
  instFintypeProd _ _

noncomputable instance instFintypeDFk : Fintype DFk :=
  instFintypeProd _ _

/-- The in-table rounds' reads: three per round. -/
theorem length_inReads_le (ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE) :
    (inReads ω).length ≤ 24 * xI.card := by
  have h : (inReads ω).length = 3 * (rnds xI (xLen ω.2.1)).card := by
    simp [inReads, List.length_flatMap, Finset.length_toList, mul_comm]
  rw [h]
  have := card_rnds_xI_le ω.2.1
  omega

/-- A `k`-cell read by an in-table round is a round's `k`-cell. -/
theorem exists_famK_of_mem {ω : (SpongeKeys X Z × Equiv.Perm (X × Z)) × DE} {x : X}
    (hx : x ∈ kCells (inReads ω)) : ∃ r ∈ rnds xI (xLen ω.2.1),
      famK ω.1.2 (xBlk ω.2.1 ω.2.2) ω.1.1.1 ω.1.1.2.1 ω.1.1.2.2 r = x := by
  obtain ⟨val, hv⟩ := mem_kCells.mp hx
  obtain ⟨r, hr, hm⟩ := List.mem_flatMap.mp hv
  refine ⟨r, Finset.mem_toList.mp hr, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, SpongeRead.k.injEq, reduceCtorEq] at hm
  exact hm.1.symm

/-- **A label's first block is read by an in-table round.** -/
def KHitY (z : DY) : Prop :=
  ∃ a, dcY z.1.1.2 z.2 a ∈ kCells (inReads z.1.1)

/-- The coordinates other than the keys. -/
abbrev QY : Type := Equiv.Perm (X × Z) × DE × CoinSlots DLab × DFk

noncomputable instance instFintypeQY : Fintype QY :=
  instFintypeProd _ _

/-- The coordinates as the rest and the keys. -/
def eKY : QY × ((Z → X) × (X → Z) × (X → Z)) ≃ DY where
  toFun x := (((((x.2.1, x.2.2.1, x.2.2.2), x.1.1), x.1.2.1), x.1.2.2.1), x.1.2.2.2)
  invFun z := ((z.1.1.1.2, z.1.1.2, z.1.2, z.2), z.1.1.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem eKY_apply (q : QY) (t : (Z → X) × (X → Z) × (X → Z)) :
    eKY (q, t) = (((((t.1, t.2.1, t.2.2), q.1), q.2.1), q.2.2.1), q.2.2.2) :=
  rfl

open scoped Classical in
/-- **First blocks read at later rounds**: `N² / |X| + 19 N² / |Z| + N |DLab| / |X|`,
`N = 8 |xI|`. -/
theorem frac_kHitY_le :
    (Fintype.card DY : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun z : DY ↦
        PermGood z.1.1.1.2 18 ∧ KHitY z ∧ ¬E0 z.1.1.2).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (18 + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ((8 * xI.card * Fintype.card DLab : ℕ) : ℝ≥0∞) / Fintype.card X := by
  refine frac_readK_le eKY (fun q ↦ q.1) (fun q ↦ xBlk q.2.1.1 q.2.1.2) (fun q ↦ xLen q.2.1.1) xI
    (fun q ↦ xBlk_injOn q.2.1.1 q.2.1.2) 18 (8 * xI.card) (fun q ↦ card_rnds_xI_le q.2.1.1)
    (fun q ↦ imgCells (dcY q.2.1 q.2.2.2)) (Fintype.card DLab)
    (fun _ ↦ card_imgCells_le _) _ fun q t hb ↦ ?_
  rw [eKY_apply] at hb
  obtain ⟨hG, ⟨a, ha⟩, hE⟩ := hb
  obtain ⟨⟨p, j⟩, hr, hx⟩ := exists_famK_of_mem ha
  dsimp only at hG hE hr hx
  refine ⟨hG, ?_⟩
  rcases j with _ | j₀
  · exact absurd (e0_of_eq (a := a) (R := trunc128 (q.2.2.2.2.1.2.2 a.1))
      (mem_rnds.mp hr).1 (hx.symm.trans (rnK_zero _ _ _ _ _))) hE
  · by_cases hI : Set.InjOn (famZ q.1 (xBlk q.2.1.1 q.2.1.2) t.1 t.2.1 t.2.2)
        (rnds xI (xLen q.2.1.1))
    · refine Or.inr ⟨p, j₀, hr, fun x hx' y hy _ _ e ↦ hI (Finset.mem_coe.mpr hx')
        (Finset.mem_coe.mpr hy) e, ?_⟩
      rw [hx]
      exact mem_imgCells _ a
    · exact Or.inl hI

open scoped Classical in
/-- **The first-round hits**: at most `|xI| / (|PK.seed| |Digest|)` of `DE`. -/
theorem card_mul_card_filter_E0_le :
    Fintype.card PublicParameter * Fintype.card Digest * (Finset.univ.filter E0).card ≤
      Fintype.card DE * xI.card :=
  card_mul_card_filter_pair_le (Equiv.refl DE) xI adrsLo adrsHi
    (fun v : ValPos → Digest ↦ v rootPos) (fun b ↦ card_mul_sum_apply_eq_le rootPos b) E0
    fun _ h ↦ h

/-- The coordinates as `DE` and the rest. -/
def eEY : DE × (((SpongeKeys X Z × Equiv.Perm (X × Z)) × CoinSlots DLab) × DFk) ≃ DY where
  toFun x := ((((x.2.1.1.1, x.2.1.1.2), x.1), x.2.1.2), x.2.2)
  invFun z := (z.1.1.2, (((z.1.1.1.1, z.1.1.1.2), z.1.2), z.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeRestEY :
    Fintype (((SpongeKeys X Z × Equiv.Perm (X × Z)) × CoinSlots DLab) × DFk) :=
  instFintypeProd _ _

open scoped Classical in
/-- **The first-round hits over the coordinates.** -/
theorem frac_E0_le :
    (Fintype.card DY : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun z : DY ↦ E0 z.1.1.2).card ≤
      (xI.card : ℝ≥0∞) / (Fintype.card PublicParameter * Fintype.card Digest : ℕ) :=
  (le_of_eq (inv_card_mul_card_filter_comp_fst eEY.symm E0)).trans
    (natCast_div_le_div_of_mul_le (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero)
      card_mul_card_filter_E0_le)

open scoped Classical in
/-- The rates of the labels' first blocks collide (named indicator). -/
noncomputable def rateBadY (x : DY) : ℕ :=
  if ¬RateInjY x then 1 else 0

/-- The coordinates with `π` first. -/
def ePY : Equiv.Perm (X × Z) × (SpongeKeys X Z × DE × CoinSlots DLab × DFk) ≃ DY where
  toFun c := ((((c.2.1, c.1), c.2.2.1), c.2.2.2.1), c.2.2.2.2)
  invFun x := (x.1.1.1.2, (x.1.1.1.1, x.1.1.2, x.1.2, x.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeRestPY : Fintype (SpongeKeys X Z × DE × CoinSlots DLab × DFk) :=
  instFintypeProd _ _

/-- **The labels' rates collide** for at most `|DLab|² / |X|` of the coordinates. -/
theorem frac_not_rateInjY_le :
    (Fintype.card DY : ℝ≥0∞)⁻¹ * ((∑ x : DY, rateBadY x : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card DLab * Fintype.card DLab : ℕ) : ℝ≥0∞) / Fintype.card X := by
  have h : Fintype.card X * ∑ x : DY, rateBadY x ≤
      Fintype.card DY * (Fintype.card DLab * Fintype.card DLab) :=
    card_mul_sum_equiv_prod_le ePY _ _ rateBadY fun r ↦ by
      refine le_trans (Nat.mul_le_mul_left _ (Finset.sum_le_sum fun π _ ↦ ?_))
        (card_mul_sum_not_injective_rate_le
          (fun a ↦ (dcY r.2.1 r.2.2.2 a, r.1.2.1 (dcY r.2.1 r.2.2.2 a)))
          fun a b hab ↦ dcY_injective r.2.1 r.2.2.2 (congrArg Prod.fst hab))
      exact ite_one_le_ite_one fun h ↦ h
  have h1 := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero h
  have hN : (Fintype.card DY : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_le_mul' le_rfl h1).trans ?_
  rw [ENNReal.inv_mul_cancel_left hN (ENNReal.natCast_ne_top _)]

/-- **The rates and capacities read**: `|DLab| 19 (24 |xI|) / |Z|` of the coordinates. -/
theorem frac_readKH_le :
    (Fintype.card DY : ℝ≥0∞)⁻¹ *
        ((∑ z : DY, pReadKH dcY 18 (fun _ : Unit ↦ inReads) () z : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card DLab * (18 + 1) * (24 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card Z :=
  frac_pReadKH_le dcY 18 (fun _ : Unit ↦ inReads) (24 * xI.card)
    (fun _ ω ↦ length_inReads_le ω) ()

open scoped Classical in
/-- **The reads of the labels' cells**: `PReadIn` fails for at most the bad permutations, the
later-round first-block hits, the first-round hits and the rates and capacities read. -/
theorem card_not_pReadIn_le :
    (Finset.univ.filter fun z : DY ↦ ¬PReadIn z).card ≤
      (Finset.univ.filter fun z : DY ↦ ¬PermGood z.1.1.1.2 18).card +
        (Finset.univ.filter fun z : DY ↦ PermGood z.1.1.1.2 18 ∧ KHitY z ∧ ¬E0 z.1.1.2).card +
        (Finset.univ.filter fun z : DY ↦ E0 z.1.1.2).card +
        ∑ z : DY, pReadKH dcY 18 (fun _ : Unit ↦ inReads) () z := by
  have hR : (Finset.univ.filter fun z : DY ↦
      1 ≤ pReadKH dcY 18 (fun _ : Unit ↦ inReads) () z).card ≤
      ∑ z : DY, pReadKH dcY 18 (fun _ : Unit ↦ inReads) () z := by
    rw [Finset.card_filter]
    exact Finset.sum_le_sum fun z _ ↦ by split_ifs with h <;> omega
  have hkh : ∀ z : DY, ∀ a, (pCellK' dcY z a ∈ k'Cells (inReads z.1.1) ∧
      PermGood z.1.1.1.2 18) ∨ pCellH dcY z a ∈ hCells (inReads z.1.1) →
      1 ≤ pReadKH dcY 18 (fun _ : Unit ↦ inReads) () z :=
    fun z a h ↦ one_le_pReadKH dcY 18 (fun _ : Unit ↦ inReads) () z a h
  have himp : ∀ z : DY, ¬PReadIn z → (¬PermGood z.1.1.1.2 18 ∨
      (PermGood z.1.1.1.2 18 ∧ KHitY z ∧ ¬E0 z.1.1.2) ∨ E0 z.1.1.2) ∨
      1 ≤ pReadKH dcY 18 (fun _ : Unit ↦ inReads) () z := by
    intro z hz
    by_cases hG : PermGood z.1.1.1.2 18
    · by_cases hE : E0 z.1.1.2
      · exact Or.inl (Or.inr (Or.inr hE))
      · by_cases hK : KHitY z
        · exact Or.inl (Or.inr (Or.inl ⟨hG, hK, hE⟩))
        · refine Or.inr (by_contra fun hR ↦ hz fun _ a ↦ ⟨fun hk ↦ hK ⟨a, hk⟩,
            fun hk' ↦ hR (hkh z a (Or.inl ⟨hk', hG⟩)), fun hh ↦ hR (hkh z a (Or.inr hh))⟩)
    · exact Or.inl (Or.inl hG)
  have h4 := card_filter_le_add_of_imp _ _ _ himp
  have h1 := card_filter_le_add_of_imp (fun z : DY ↦ ¬PermGood z.1.1.1.2 18 ∨
      (PermGood z.1.1.1.2 18 ∧ KHitY z ∧ ¬E0 z.1.1.2) ∨ E0 z.1.1.2)
    (fun z : DY ↦ ¬PermGood z.1.1.1.2 18)
    (fun z : DY ↦ (PermGood z.1.1.1.2 18 ∧ KHitY z ∧ ¬E0 z.1.1.2) ∨ E0 z.1.1.2) fun _ h ↦ h
  have h2 := card_filter_le_add_of_imp
    (fun z : DY ↦ (PermGood z.1.1.1.2 18 ∧ KHitY z ∧ ¬E0 z.1.1.2) ∨ E0 z.1.1.2)
    (fun z : DY ↦ PermGood z.1.1.1.2 18 ∧ KHitY z ∧ ¬E0 z.1.1.2)
    (fun z : DY ↦ E0 z.1.1.2) fun _ h ↦ h
  exact nat_le_four h4 h1 h2 hR

end counts

end Quantum.Sphincs.Assembly

end
