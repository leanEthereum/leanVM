module

public import Quantum.Sponge.Oracle.Hardwired.EventSplit
public import Quantum.Xmss.Assembly.CostRefined
public import Quantum.Xmss.Assembly.Depth.Ports

@[expose] public section

/-!
# The XMSS event against parallel programs with rounds of every sponge port

Corollary D of the parallel transition lemma: `TargetBad` is the union over the `h` cells `z` of
the events `TargetBadAt z` (bad, or a tail with a target ending at capacity `z` reaching it).
Goodness reads only `k` and `k'`, and a tail's output reads `h` only at its end, so `TargetBadAt z`
depends on the cell `z` of `h` and on `k`, `k'` (`mem_targetBadAt_congr`); a fresh `h` cell flips
it for at most `F` values (`card_targetBadAt_updateH_le`). On the hardwired register these are
the cell events `HwTargetBadAt` of `HwTargetBad`, with `h` rate `F / |X|`
(`freshAt_slice_hwTargetBadAt`), while the `k`, `k'` fields of `HwTargetBad` have the capacity
rates of `preimageRateBound` alone (`capRateBound`, `freshAt_k_slice_hwTargetBad`).

* **The XMSS event bound with depth** (`rpow_inv_two_eventWeight_runtimeR_par_le`): a parallel
  program over `parSpec (recHwSpec X Z HPos Selections) portR`, with `q_h` calls of `h` in `d_h`
  rounds, `n_k` calls of `k` and `k'`, `K` classical calls and no round mixing ports, run against
  `(runtimeR m0R).par portR`, ends in `BadR L progCap` with
  `√w ≤ √(6 · 2^-128 · d_h q_h) + n_k √(6 ε_c) + √(classical costs)`, the classical costs those of
  `ewPrefix_le_ref` (`dRref`, `dPof`), `ε_c = capRateBound (progCap + q_h + n_k + K + 1) 18`.
-/

open Matrix IPFunctor
open scoped Kronecker ENNReal

universe u v w

namespace Quantum.Sponge

open Quantum

/-! ## The cell events of `TargetBad` -/

section cells

variable {X Z Y : Type} [AddCommGroup X] [AddCommGroup Z] {π : Equiv.Perm (X × Z)}
  {out : X → Y} {tgt : List X → Option Y} {D D' : Dbs X Z}

variable (π out tgt) in
/-- The cell event of `z`: bad, or a tail with a target ending at capacity `z` reaches it. -/
def TargetBadAt (z : Z) : Set (Dbs X Z) :=
  {D | ¬ Good π D ∨ ∃ t xi w, IsHeadTail π D t z xi ∧ D.h z = some w ∧ tgt t = some (out (xi + w))}

theorem targetBadAt_subset (z : Z) : TargetBadAt π out tgt z ⊆ TargetBad π out tgt := by
  rintro D (h | ⟨t, xi, w, hht, hw, ht⟩)
  · exact .inl h
  · exact .inr ⟨t, _, ht, z, xi, w, hht, hw, rfl⟩

theorem exists_mem_targetBadAt (hD : D ∈ TargetBad π out tgt) :
    ∃ z, D ∈ TargetBadAt π out tgt z := by
  rcases hD with h | ⟨t, y, ht, z, xi, w, hht, hw, rfl⟩
  · exact ⟨0, .inl h⟩
  · exact ⟨z, .inr ⟨t, xi, w, hht, hw, ht⟩⟩

/-- **Locality**: the cell event of `z` reads `h` only at `z`. -/
theorem mem_targetBadAt_congr {z : Z} (hh : D'.h z = D.h z) (hk : D'.k = D.k)
    (hk' : D'.k' = D.k') : D' ∈ TargetBadAt π out tgt z ↔ D ∈ TargetBadAt π out tgt z := by
  have hE : Extends D D' := extends_refl_of_eq hk.symm hk'.symm
  have hE' : Extends D' D := extends_refl_of_eq hk hk'
  constructor
  · rintro (h | ⟨t, xi, w, hht, hw, ht⟩)
    · exact .inl fun hg ↦ h (hg.mono hE)
    · exact .inr ⟨t, xi, w, hht.mono hE, hh ▸ hw, ht⟩
  · rintro (h | ⟨t, xi, w, hht, hw, ht⟩)
    · exact .inl fun hg ↦ h (hg.mono hE')
    · exact .inr ⟨t, xi, w, hht.mono hE', hh.symm ▸ hw, ht⟩

theorem TargetBadAt.mono {z : Z} (hE : ExtendsAll D D') (hD' : D' ∈ TargetBadAt π out tgt z) :
    D ∈ TargetBadAt π out tgt z :=
  hD'.imp (fun hb hg ↦ hb (hg.of_extendsAll hE)) fun ⟨t, xi, w, hht, hw, ht⟩ ↦
    ⟨t, xi, w, hht.mono hE.1, hE.2 _ _ hw, ht⟩

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {F : ℕ}

omit [Fintype Z] [DecidableEq X] in
open scoped Classical in
/-- **A fresh `h` cell flips a cell event for at most `F` values**: the cell `z` itself, through
the unique head-tail of `z` in the good database with its one target; any other cell, never. -/
theorem card_targetBadAt_updateH_le [DecidableEq Y]
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {z : Z}
    (hD : D ∉ TargetBadAt π out tgt z) (z' : Z) :
    (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z' (some u) } ∈ TargetBadAt π out tgt z).card ≤ F := by
  by_cases hzz : z' = z
  · subst hzz
    have hG : Good π D := by
      by_contra h
      exact hD (.inl h)
    have key : ∀ u, { D with h := Function.update D.h z' (some u) } ∈ TargetBadAt π out tgt z' →
        ∃ t xi, IsHeadTail π D t z' xi ∧ tgt t = some (out (xi + u)) := by
      rintro u (h | ⟨t, xi, w, hht, hw, ht⟩)
      · exact absurd ((good_update_h_iff _).2 hG) h
      · simp only [Function.update_self, Option.some.injEq] at hw
        subst hw
        have hE : Extends D { D with h := Function.update D.h z' (some u) } :=
          extends_refl_of_eq rfl rfl
        exact ⟨t, xi, hht.mono hE, ht⟩
    rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun u : X ↦
        { D with h := Function.update D.h z' (some u) } ∈ TargetBadAt π out tgt z') with
      he | ⟨u0, hu0⟩
    · simp [he]
    obtain ⟨t0, xi0, hi0, ht0⟩ := key u0 (Finset.mem_filter.1 hu0).2
    refine card_le_of_out_translate hF xi0 (out (xi0 + u0)) fun u hu ↦ ?_
    obtain ⟨t, xi, hi, ht⟩ := key u (Finset.mem_filter.1 hu).2
    obtain ⟨rfl, rfl⟩ := hG.isHeadTail_unique hi hi0
    exact Option.some_injective _ (ht.symm.trans ht0)
  · rw [Finset.filter_false_of_mem fun u _ hu ↦
      hD ((mem_targetBadAt_congr (D' := { D with h := Function.update D.h z' (some u) })
        (Function.update_of_ne (Ne.symm hzz) _ _) rfl rfl).1 hu)]
    simp

end cells

/-! ## The cell events of the hardwired target events -/

section hw

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {Y M : Type} {π : Equiv.Perm (X × Z)} {out : X → Y}
  {tgt : Hw X Z → M → List X → Option Y} {N : ℕ}

variable (π out tgt N) in
/-- The cell event of `z` of the hardwired register: at most `N` hardwired cells per function, and
the union of the hardwired and database cells in `TargetBadAt z` for the targets of `(W, m)`. -/
def HwTargetBadAt (z : Z) : Set (HwReg X Z M) :=
  {x | dbGrade x.2.1 ≤ N ∧ union x.2.1 x.1 ∈ TargetBadAt π out (tgt x.2.1 x.2.2) z}

omit [DecidableEq X] [DecidableEq Z] in
theorem hwTargetBadAt_subset (z : Z) :
    HwTargetBadAt π out tgt N z ⊆ HwTargetBad π out tgt N :=
  fun _ hx ↦ ⟨hx.1, targetBadAt_subset z hx.2⟩

omit [DecidableEq X] [DecidableEq Z] in
theorem exists_mem_hwTargetBadAt {x : HwReg X Z M} (hx : x ∈ HwTargetBad π out tgt N) :
    ∃ z, x ∈ HwTargetBadAt π out tgt N z :=
  let ⟨z, hz⟩ := exists_mem_targetBadAt hx.2
  ⟨z, hx.1, hz⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- **Locality**: the cell event of `z` reads the database of `h` only at `z`. -/
theorem mem_hwTargetBadAt_congr (z : Z) (s s' : HwReg X Z M) (h₁ : s'.1.1 z = s.1.1 z)
    (h₂ : s'.1.2 = s.1.2) (h₃ : s'.2 = s.2) :
    s' ∈ HwTargetBadAt π out tgt N z ↔ s ∈ HwTargetBadAt π out tgt N z := by
  obtain ⟨D', W', m'⟩ := s'
  obtain ⟨D, W, m⟩ := s
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h₃
  refine and_congr_right fun _ ↦ mem_targetBadAt_congr ?_ ?_ ?_
  · change (W'.1 z).or (D'.1 z) = (W'.1 z).or (D.1 z)
    rw [h₁]
  · change (fun x ↦ (W'.2.1 x).or (D'.2.1 x)) = fun x ↦ (W'.2.1 x).or (D.2.1 x)
    rw [show D'.2.1 = D.2.1 from congrArg Prod.fst h₂]
  · change (fun x ↦ (W'.2.2 x).or (D'.2.2 x)) = fun x ↦ (W'.2.2 x).or (D.2.2 x)
    rw [show D'.2.2 = D.2.2 from congrArg Prod.snd h₂]

/-- Every slice of a cell event is upward closed. -/
theorem upClosed_slice_hwTargetBadAt (z : Z) (W : Hw X Z) (m : M) :
    UpClosed (slice (HwTargetBadAt π out tgt N z) W m) where
  h D hD z' u hz := ⟨hD.1, TargetBadAt.mono (extendsAll_union W (D := (D.h, D.k, D.k'))
    (D' := (Function.update D.h z' (some u), D.k, D.k')) (fun _ _ h ↦ update_some_of_none hz h)
    (fun _ _ h ↦ h) fun _ _ h ↦ h) hD.2⟩
  k D hD x u hx := ⟨hD.1, TargetBadAt.mono (extendsAll_union W (D := (D.h, D.k, D.k'))
    (D' := (D.h, Function.update D.k x (some u), D.k')) (fun _ _ h ↦ h)
    (fun _ _ h ↦ update_some_of_none hx h) fun _ _ h ↦ h) hD.2⟩
  k' D hD x u hx := ⟨hD.1, TargetBadAt.mono (extendsAll_union W (D := (D.h, D.k, D.k'))
    (D' := (D.h, D.k, Function.update D.k' x (some u))) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) fun _ _ h ↦ update_some_of_none hx h) hD.2⟩

open scoped Classical in
/-- **The `h` rate of a cell event**: `F / |X|` below any number of entries. -/
theorem freshAt_slice_hwTargetBadAt [DecidableEq Y] (z : Z)
    [DecidablePred (· ∈ HwTargetBadAt π out tgt N z)] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (T : ℕ) (W : Hw X Z) (m : M) :
    FreshAt (slice (HwTargetBadAt π out tgt N z) W m) T ((F : ℝ≥0∞) / Fintype.card X) .h := by
  intro D hD _ _ _ z' _
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hN hu.1]
    simp
  have hU : union W (D.h, D.k, D.k') ∉ TargetBadAt π out (tgt W m) z := fun h ↦ hD ⟨hN, h⟩
  rcases hWz : W.1 z' with _ | w
  · refine ENNReal.div_le_div_right (Nat.cast_le.2 ((Finset.card_le_card fun u hu ↦ ?_).trans
      (card_targetBadAt_updateH_le hF hU z'))) _
    have h2 : union W (Function.update D.h z' (some u), D.k, D.k') ∈
        TargetBadAt π out (tgt W m) z := (Finset.mem_filter.1 hu).2.2
    rw [union_updateH W hWz] at h2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
    · simp
    have h2 : union W (Function.update D.h z' (some u), D.k, D.k') ∈
        TargetBadAt π out (tgt W m) z := hu.2
    rwa [union_updateH_of_hw W hWz] at h2

variable (Z) in
/-- The capacity rates of `preimageRateBound` (the `k` and `k'` fractions) below `T` entries. -/
noncomputable def capRateBound (T G : ℕ) : ℝ≥0∞ :=
  max (((T + 1) * ((T + 1) * T + 2 * T) * G : ℕ) / Fintype.card Z : ℝ≥0∞)
    (((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T : ℕ) / Fintype.card Z : ℝ≥0∞)

omit [DecidableEq X] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z] in
/-- `preimageRateBound` is the larger of the `h` rate and the capacity rates. -/
theorem preimageRateBound_eq_max (T G F : ℕ) :
    preimageRateBound (X := X) (Z := Z) T G F =
      max ((F : ℕ) / Fintype.card X : ℝ≥0∞) (capRateBound Z T G) :=
  rfl

open scoped Classical in
/-- **The `k` rate of the hardwired target event**: the capacity rate only. -/
theorem freshAt_k_slice_hwTargetBad [DecidablePred (· ∈ HwTargetBad π out tgt N)] {G : ℕ}
    (hπ : PermGood π G) (T : ℕ) (W : Hw X Z) (m : M) :
    FreshAt (slice (HwTargetBad π out tgt N) W m) T (capRateBound Z (N + T) G) .k := by
  intro D hD _ hk hk' x hx
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hN hu.1]
    simp
  have hWk : W.2.1.size ≤ N := by simp only [dbGrade] at hN; omega
  have hWk' : W.2.2.size ≤ N := by simp only [dbGrade] at hN; omega
  have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
  rcases hWx : W.2.1 x with _ | w
  · have hUx : (union W (D.h, D.k, D.k')).k x = none := by
      change (W.2.1 x).or (D.k x) = none
      rw [hWx, hx]
      rfl
    refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
      ((Finset.card_le_card fun u hu ↦ ?_).trans (card_targetBad_updateK_le hπ hU
        ((size_or_le W.2.1 D.k).trans (by omega)) ((size_or_le W.2.2 D.k').trans (by omega))
        hUx))) _) (le_max_left _ _)
    have h2 : union W (D.h, Function.update D.k x (some u), D.k') ∈
        TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
    rw [union_updateK W hWx] at h2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
    · simp
    have h2 : union W (D.h, Function.update D.k x (some u), D.k') ∈
        TargetBad π out (tgt W m) := hu.2
    rwa [union_updateK_of_hw W hWx] at h2

open scoped Classical in
/-- **The `k'` rate of the hardwired target event**: the capacity rate only. -/
theorem freshAt_k'_slice_hwTargetBad [DecidablePred (· ∈ HwTargetBad π out tgt N)] {G : ℕ}
    (hπ : PermGood π G) (T : ℕ) (W : Hw X Z) (m : M) :
    FreshAt (slice (HwTargetBad π out tgt N) W m) T (capRateBound Z (N + T) G) .k' := by
  intro D hD hh hk hk' x hx
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hN hu.1]
    simp
  have hWh : W.1.size ≤ N := by simp only [dbGrade] at hN; omega
  have hWk : W.2.1.size ≤ N := by simp only [dbGrade] at hN; omega
  have hWk' : W.2.2.size ≤ N := by simp only [dbGrade] at hN; omega
  have hU : union W (D.h, D.k, D.k') ∉ TargetBad π out (tgt W m) := fun h ↦ hD ⟨hN, h⟩
  rcases hWx : W.2.2 x with _ | w
  · have hUx : (union W (D.h, D.k, D.k')).k' x = none := by
      change (W.2.2 x).or (D.k' x) = none
      rw [hWx, hx]
      rfl
    refine le_trans (ENNReal.div_le_div_right (Nat.cast_le.2
      ((Finset.card_le_card fun u hu ↦ ?_).trans (card_targetBad_updateK'_le hπ hU
        ((size_or_le W.1 D.h).trans (by omega)) ((size_or_le W.2.1 D.k).trans (by omega))
        ((size_or_le W.2.2 D.k').trans (by omega)) hUx))) _) (le_max_right _ _)
    have h2 : union W (D.h, D.k, Function.update D.k' x (some u)) ∈
        TargetBad π out (tgt W m) := (Finset.mem_filter.1 hu).2.2
    rw [union_updateK' W hWx] at h2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
    · simp
    have h2 : union W (D.h, D.k, Function.update D.k' x (some u)) ∈
        TargetBad π out (tgt W m) := hu.2
    rwa [union_updateK'_of_hw W hWx] at h2

end hw

/-- A port's fresh bound does not depend on the decidability instance of the event. -/
theorem FreshAt.of_eq {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {S S' : Set (Dbs X Z)} {_ : DecidablePred (· ∈ S)} {_ : DecidablePred (· ∈ S')} (hS : S = S')
    {t : ℕ} {ε : ℝ≥0∞} {i : SpongePort} (h : FreshAt S t ε i) : FreshAt S' t ε i := by
  subst hS
  convert h

end Quantum.Sponge

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par Quantum.Xmss LeanXmss

attribute [local instance] badRDec

/-! ## The XMSS event bound with depth -/

/-- **The cell events of `BadR`**: those of Events' `Bad`, the memory label ignored. -/
def ScR (L : HonestTable) (N : ℕ) (z : Z) : Set (HwReg X Z Mem) :=
  {r | (r.1, r.2.1, r.2.2.2) ∈ HwTargetBadAt L.perm trunc128 (xmssTgtHw L) N z}

/-- Membership in a cell event of `BadR`, decided classically. -/
noncomputable local instance scRDec (L : HonestTable) (N : ℕ) (z : Z) :
    DecidablePred (· ∈ ScR L N z) :=
  fun _ ↦ Classical.propDecidable _

/-- The `h` rate of the cell events of `BadR`: `2^960 / |X| = 2^-128`. -/
theorem freshAt_slice_scR (L : HonestTable) (N : ℕ) (z : Z) (T : ℕ) (W : Hw X Z) (m : Mem) :
    FreshAt (slice (ScR L N z) W m) T (2 ^ 128 : ℝ≥0∞)⁻¹ .h := by
  have : DecidablePred (· ∈ HwTargetBadAt L.perm trunc128 (xmssTgtHw L) N z) :=
    fun _ ↦ Classical.propDecidable _
  have h := freshAt_slice_hwTargetBadAt (π := L.perm) (out := trunc128) (tgt := xmssTgtHw L)
    (N := N) z (fun d ↦ by convert card_fiber_trunc128_le d) T W m.2
  rw [fiber_div_card_X] at h
  exact FreshAt.of_eq (Set.ext fun _ ↦ Iff.rfl) h

/-- The `k` rate of `BadR`: the capacity rate. -/
theorem freshAt_k_slice_badR (L : HonestTable) (hπ : PermGood L.perm 18) (T : ℕ) (W : Hw X Z)
    (m : Mem) :
    FreshAt (slice (BadR L progCap) W m) T (capRateBound Z (progCap + T) 18) .k := by
  have : DecidablePred (· ∈ Bad L progCap) := fun _ ↦ Classical.propDecidable _
  exact FreshAt.of_eq (Set.ext fun _ ↦ Iff.rfl) (freshAt_k_slice_hwTargetBad hπ T W m.2)

/-- The `k'` rate of `BadR`: the capacity rate. -/
theorem freshAt_k'_slice_badR (L : HonestTable) (hπ : PermGood L.perm 18) (T : ℕ) (W : Hw X Z)
    (m : Mem) :
    FreshAt (slice (BadR L progCap) W m) T (capRateBound Z (progCap + T) 18) .k' := by
  have : DecidablePred (· ∈ Bad L progCap) := fun _ ↦ Classical.propDecidable _
  exact FreshAt.of_eq (Set.ext fun _ ↦ Iff.rfl) (freshAt_k'_slice_hwTargetBad hπ T W m.2)

theorem capRateBound_ne_top (T G : ℕ) : capRateBound Z T G ≠ ⊤ := by
  have hZ : (Fintype.card Z : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact max_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ)
    (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hZ)

/-- **The XMSS event bound with depth.** A parallel program over
`parSpec (recHwSpec X Z HPos Selections) portR` with `q_h` calls of `h` in `d_h` rounds (a single
call counts as a round), `n_k` calls of `k` and `k'` (single or in rounds), `K` classical calls and
no round mixing ports, run against `(runtimeR m0R).par portR`, ends in `BadR L progCap` with
`√w ≤ √(6 · 2^-128 · d_h q_h) + n_k √(6 ε_c) + √(∑ classical costs)`, the classical costs those of
`ewPrefix_le_ref`. -/
theorem rpow_inv_two_eventWeight_runtimeR_par_le (L : HonestTable) (hπ : PermGood L.perm 18)
    {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xr : QReg → Type w} {A : QReg}
    (x : QuantumComp Λ (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)) Xr A)
    {qh dh nk K : ℕ}
    (hxq : IFreeM.IsChargeBound x (portCharge (portWidth (portR X Z HPos Selections) .h)) qh)
    (hxd : IFreeM.IsChargeBound x (portCharge (portDepth (portR X Z HPos Selections) .h)) dh)
    (hxk : IFreeM.IsChargeBound x (portCharge (capWidth (portR X Z HPos Selections))) nk)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z Mem (recSpec HPos Selections)))) K)
    (hxm : IFreeM.IsChargeBound x (portCharge (mixedRounds (portR X Z HPos Selections))) 0)
    (ρ : SubState A) :
    ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight I
        (hwProjector (BadR L progCap)) x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ^ (2⁻¹ : ℝ) ≤
      (6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * dh * qh) ^ (2⁻¹ : ℝ) +
        nk * (6 * capRateBound Z (progCap + (qh + nk + K + 1)) 18) ^ (2⁻¹ : ℝ) +
        ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight I
          (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref L) (dPof L)))) x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ^ (2⁻¹ : ℝ) := by
  have h := rpow_inv_two_eventWeight_extend_split_le (BadR L progCap) (ScR L progCap)
    (fun z _ hr ↦ hwTargetBadAt_subset z hr) (fun _ hr ↦ exists_mem_hwTargetBadAt hr)
    (fun z s s' h₁ h₂ h₃ ↦ mem_hwTargetBadAt_congr z (s.1, s.2.1, s.2.2.2)
      (s'.1, s'.2.1, s'.2.2.2) h₁ h₂ (by rw [h₃]))
    (fun z W m ↦ (upClosed_slice_hwTargetBadAt z W m.2).port .h)
    (fun W m ↦ upClosed_slice_bad W m.2) (hwEmpty X Z) m0R (empty_not_mem_bad m0)
    (ENNReal.inv_ne_top.2 (by positivity)) (capRateBound_ne_top _ _)
    (fun z W m ↦ freshAt_slice_scR L progCap z _ W m)
    (fun W m ↦ freshAt_k_slice_badR L hπ _ W m) (fun W m ↦ freshAt_k'_slice_badR L hπ _ W m)
    (dRref L) (dPof L)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadR L progCap) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadR L progCap) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    (Hybrid.initHw X Z m0R) (spongeHardwiredRuntime X Z (hwEmpty X Z) m0R).step rfl rfl
    (t := recSpec HPos Selections) recStep (fun _ _ ↦ 0)
    (fun T r n σ hσ ↦ querySupportedOn_recStep T r n σ hσ)
    (fun T σ hσ ↦ tsum_potential_recStep_le (BadR L progCap) (labelFree_badR L progCap) T σ hσ)
    (portR X Z HPos Selections) (fun _ ↦ rfl) I x hxq hxd hxk hxK hxm ρ
  refine h.trans_eq ?_
  congr 4
  funext i σ
  rcases i with i | j <;> rfl

/-- **The XMSS event bound with depth**, squared. -/
theorem eventWeight_runtimeR_par_le (L : HonestTable) (hπ : PermGood L.perm 18)
    {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xr : QReg → Type w} {A : QReg}
    (x : QuantumComp Λ (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)) Xr A)
    {qh dh nk K : ℕ}
    (hxq : IFreeM.IsChargeBound x (portCharge (portWidth (portR X Z HPos Selections) .h)) qh)
    (hxd : IFreeM.IsChargeBound x (portCharge (portDepth (portR X Z HPos Selections) .h)) dh)
    (hxk : IFreeM.IsChargeBound x (portCharge (capWidth (portR X Z HPos Selections))) nk)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z Mem (recSpec HPos Selections)))) K)
    (hxm : IFreeM.IsChargeBound x (portCharge (mixedRounds (portR X Z HPos Selections))) 0)
    (ρ : SubState A) :
    ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight I
        (hwProjector (BadR L progCap)) x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ≤
      ((6 * (2 ^ 128 : ℝ≥0∞)⁻¹ * dh * qh) ^ (2⁻¹ : ℝ) +
        nk * (6 * capRateBound Z (progCap + (qh + nk + K + 1)) 18) ^ (2⁻¹ : ℝ) +
        ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight I
          (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref L) (dPof L)))) x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := ENNReal.rpow_le_rpow (rpow_inv_two_eventWeight_runtimeR_par_le L hπ I x hxq hxd hxk
    hxK hxm ρ) (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

end Quantum.Xmss.Assembly

end
