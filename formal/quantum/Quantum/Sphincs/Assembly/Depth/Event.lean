module

public import Quantum.Xmss.Assembly.Depth.Event
public import Quantum.Sphincs.Assembly.CostRefined

@[expose] public section

/-!
# The leanSPHINCS event against parallel programs with rounds of every sponge port

leanXMSS's Corollary D (`Quantum.Xmss.Assembly.Depth.Event`) for Events' `Bad d N`, the union of
the Struct and Enc event `TgtBad` (out `trunc128`) and the coverage event `CovBadOf` (out
`covOut S★`), both hardwired target events. The cell event of `z` (`CellBad`) is the union of the
two cell events `HwTargetBadAt z`; it is local in the cell `z` of `h`, and its `h` rate is the sum
of the two: `covOut` has a small fiber only at its target `true`, so the cell bounds are taken with
fiber bounds at the targets only (`card_targetBadAt_updateH_le_of_tgt`,
`freshAt_slice_hwTargetBadAt_of_tgt`, as CovBad's `card_targetBad_updateH_le_of_tgt`). The `k`,
`k'` rates of `Bad` are twice the capacity rate (`freshAt_k_slice_bad`), through the per-port union
lemmas `upClosedAt_of_union`, `freshAt_of_union`.

* **The leanSPHINCS event bound with depth** (`rpow_inv_two_eventWeight_runtimeR_par_le`): a
  parallel program over `parSpec (recHwSpec X Z HPos Selections) portR`, with `q_h` calls of `h`
  in `d_h` rounds, `n_k` calls of `k` and `k'`, `K` classical calls and no round mixing ports, run
  against `(runtimeR m0R).par portR`, ends in `BadR p v progCap` with
  `√w ≤ √(6 ε_h d_h q_h) + n_k √(6 · 2 ε_c) + √(classical costs)`, `ε_h = epsHS v`
  (`2^960 / |X| + 2^838 coverMass S★(v) / |X|`), `ε_c = capRateBound (progCap + q_h + n_k + K + 1)
  18`, the classical costs those of EventRef's `ewPrefix_le_ref` (`dRref`, `dPof`).
-/

open Matrix IPFunctor
open scoped Kronecker ENNReal

universe u v w

namespace Quantum.Sphincs

open Quantum Quantum.Sponge

/-! ## Cell events with fiber bounds at the targets -/

section cells

variable {X Z Y : Type} [AddCommGroup X] [AddCommGroup Z] {π : Equiv.Perm (X × Z)}
  {out : X → Y} {tgt : List X → Option Y} {D : Dbs X Z}
  [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {F : ℕ}

omit [Fintype Z] [DecidableEq X] in
open scoped Classical in
/-- `card_targetBadAt_updateH_le` with fiber bounds at the targets only: the flipping values of
the cell `z` lie in one translate of the fiber of the target of its unique head-tail. -/
theorem card_targetBadAt_updateH_le_of_tgt [DecidableEq Y]
    (hF : ∀ t y, tgt t = some y → (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {z : Z}
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
    have hsub : ∀ u ∈ (Finset.univ.filter fun u : X ↦
        { D with h := Function.update D.h z' (some u) } ∈ TargetBadAt π out tgt z'),
        out (xi0 + u) = out (xi0 + u0) := by
      intro u hu
      obtain ⟨t, xi, hi, ht⟩ := key u (Finset.mem_filter.1 hu).2
      obtain ⟨rfl, rfl⟩ := hG.isHeadTail_unique hi hi0
      exact Option.some_injective _ (ht.symm.trans ht0)
    exact (Finset.card_le_card_of_injOn (xi0 + ·) (fun u hu ↦ by simp [hsub u hu])
      fun _ _ _ _ he ↦ add_left_cancel he).trans (hF t0 _ ht0)
  · rw [Finset.filter_false_of_mem fun u _ hu ↦
      hD ((mem_targetBadAt_congr (D' := { D with h := Function.update D.h z' (some u) })
        (Function.update_of_ne (Ne.symm hzz) _ _) rfl rfl).1 hu)]
    simp

end cells

section hw

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] {Y M : Type} {π : Equiv.Perm (X × Z)} {out : X → Y}
  {tgt : Hw X Z → M → List X → Option Y} {N : ℕ}

open scoped Classical in
/-- `freshAt_slice_hwTargetBadAt` with fiber bounds at the targets only. -/
theorem freshAt_slice_hwTargetBadAt_of_tgt [DecidableEq Y] (z : Z)
    [DecidablePred (· ∈ HwTargetBadAt π out tgt N z)] {F : ℕ}
    (hF : ∀ W m t y, tgt W m t = some y → (Finset.univ.filter fun x ↦ out x = y).card ≤ F)
    (T : ℕ) (W : Hw X Z) (m : M) :
    FreshAt (slice (HwTargetBadAt π out tgt N z) W m) T ((F : ℝ≥0∞) / Fintype.card X) .h := by
  intro D hD _ _ _ z' _
  by_cases hN : dbGrade W ≤ N
  swap
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hN hu.1]
    simp
  have hU : union W (D.h, D.k, D.k') ∉ TargetBadAt π out (tgt W m) z := fun h ↦ hD ⟨hN, h⟩
  rcases hWz : W.1 z' with _ | w
  · refine ENNReal.div_le_div_right (Nat.cast_le.2 ((Finset.card_le_card fun u hu ↦ ?_).trans
      (card_targetBadAt_updateH_le_of_tgt (hF W m) hU z'))) _
    have h2 : union W (Function.update D.h z' (some u), D.k, D.k') ∈
        TargetBadAt π out (tgt W m) z := (Finset.mem_filter.1 hu).2.2
    rw [union_updateH W hWz] at h2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩
  · rw [Finset.filter_false_of_mem fun u _ hu ↦ hU ?_]
    · simp
    have h2 : union W (Function.update D.h z' (some u), D.k, D.k') ∈
        TargetBadAt π out (tgt W m) z := hu.2
    rwa [union_updateH_of_hw W hWz] at h2

end hw

/-! ## One port's fields of a union of events -/

section union

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {S T U : Set (Dbs α β)}

omit [Fintype α] [Fintype β] in
/-- A port's field of upward closure of a union of events. -/
theorem upClosedAt_of_union (hU : ∀ D, D ∈ U ↔ D ∈ S ∨ D ∈ T) :
    ∀ {i : SpongePort}, UpClosedAt S i → UpClosedAt T i → UpClosedAt U i
  | .h, hS, hT => fun D hD z u hz ↦
    (hU _).2 (((hU D).1 hD).imp (hS D · z u hz) (hT D · z u hz))
  | .k, hS, hT => fun D hD x u hx ↦
    (hU _).2 (((hU D).1 hD).imp (hS D · x u hx) (hT D · x u hx))
  | .k', hS, hT => fun D hD x u hx ↦
    (hU _).2 (((hU D).1 hD).imp (hS D · x u hx) (hT D · x u hx))

/-- **A port's fresh bound of a union** is the sum of the two fresh bounds. -/
theorem freshAt_of_union {_ : DecidablePred (· ∈ S)} {_ : DecidablePred (· ∈ T)}
    {_ : DecidablePred (· ∈ U)} (hU : ∀ D, D ∈ U ↔ D ∈ S ∨ D ∈ T) {t : ℕ} {ε ε' : ℝ≥0∞} :
    ∀ {i : SpongePort}, FreshAt S t ε i → FreshAt T t ε' i → FreshAt U t (ε + ε') i
  | .h, hS, hT => fun D hD h₁ h₂ h₃ z hz ↦
    (natCast_div_le_add _ (card_filter_le_add fun _ hu ↦ (hU _).1 hu)).trans
      (add_le_add (hS D (fun h ↦ hD ((hU D).2 (.inl h))) h₁ h₂ h₃ z hz)
        (hT D (fun h ↦ hD ((hU D).2 (.inr h))) h₁ h₂ h₃ z hz))
  | .k, hS, hT => fun D hD h₁ h₂ h₃ x hx ↦
    (natCast_div_le_add _ (card_filter_le_add fun _ hu ↦ (hU _).1 hu)).trans
      (add_le_add (hS D (fun h ↦ hD ((hU D).2 (.inl h))) h₁ h₂ h₃ x hx)
        (hT D (fun h ↦ hD ((hU D).2 (.inr h))) h₁ h₂ h₃ x hx))
  | .k', hS, hT => fun D hD h₁ h₂ h₃ x hx ↦
    (natCast_div_le_add _ (card_filter_le_add fun _ hu ↦ (hU _).1 hu)).trans
      (add_le_add (hS D (fun h ↦ hD ((hU D).2 (.inl h))) h₁ h₂ h₃ x hx)
        (hT D (fun h ↦ hD ((hU D).2 (.inr h))) h₁ h₂ h₃ x hx))

end union

/-! ## The cell events of the leanSPHINCS event -/

section bad

open Quantum.Xmss (X Z trunc128 card_fiber_trunc128_le)

variable {S : Type} (d : EvData) (N : ℕ)

/-- **The cell event of `z` of `Bad d N`**: the cell events of `z` of Struct and Enc and of
coverage. -/
def CellBad (z : Z) : Set (HwReg X Z (Mem S)) :=
  HwTargetBadAt d.perm trunc128 d.sphTgtHw N z ∪
    HwTargetBadAt d.perm (covOut d.cover) (fun W (_ : Mem S) ↦ covTgt d.pk (d.covEx W)) N z

theorem cellBad_subset (z : Z) : CellBad (S := S) d N z ⊆ Bad d N :=
  Set.union_subset_union (hwTargetBadAt_subset z) (hwTargetBadAt_subset z)

variable {d N} in
theorem exists_mem_cellBad {x : HwReg X Z (Mem S)} (hx : x ∈ Bad d N) :
    ∃ z, x ∈ CellBad d N z := by
  rcases hx with h | h
  · obtain ⟨z, hz⟩ := exists_mem_hwTargetBadAt h
    exact ⟨z, .inl hz⟩
  · obtain ⟨z, hz⟩ := exists_mem_hwTargetBadAt h
    exact ⟨z, .inr hz⟩

/-- **Locality**: the cell event of `z` reads the database of `h` only at `z`. -/
theorem mem_cellBad_congr (z : Z) (s s' : HwReg X Z (Mem S)) (h₁ : s'.1.1 z = s.1.1 z)
    (h₂ : s'.1.2 = s.1.2) (h₃ : s'.2 = s.2) : s' ∈ CellBad d N z ↔ s ∈ CellBad d N z :=
  or_congr (mem_hwTargetBadAt_congr z s s' h₁ h₂ h₃) (mem_hwTargetBadAt_congr z s s' h₁ h₂ h₃)

/-- The `h` field of upward closure of every slice of a cell event. -/
theorem upClosedAt_slice_cellBad (z : Z) (W : Hw X Z) (m : Mem S) :
    UpClosedAt (slice (CellBad d N z) W m) .h :=
  upClosedAt_of_union (S := slice (HwTargetBadAt d.perm trunc128 d.sphTgtHw N z) W m)
    (T := slice (HwTargetBadAt d.perm (covOut d.cover)
      (fun W (_ : Mem S) ↦ covTgt d.pk (d.covEx W)) N z) W m) (fun _ ↦ Iff.rfl)
    ((upClosed_slice_hwTargetBadAt z W m).port .h) ((upClosed_slice_hwTargetBadAt z W m).port .h)

/-- **The `h` rate of a cell event**: `2^960 / |X|` (Struct and Enc) plus
`2^838 coverMass S★ / |X|` (coverage). -/
theorem freshAt_slice_cellBad (z : Z) [DecidablePred (· ∈ CellBad (S := S) d N z)] (T : ℕ)
    (W : Hw X Z) (m : Mem S) :
    FreshAt (slice (CellBad d N z) W m) T (((2 ^ 960 : ℕ) : ℝ≥0∞) / Fintype.card X +
      ((2 ^ 838 * coverMass d.cover : ℕ) : ℝ≥0∞) / Fintype.card X) .h := by
  classical
  exact freshAt_of_union (S := slice (HwTargetBadAt d.perm trunc128 d.sphTgtHw N z) W m)
    (T := slice (HwTargetBadAt d.perm (covOut d.cover)
      (fun W (_ : Mem S) ↦ covTgt d.pk (d.covEx W)) N z) W m) (fun _ ↦ Iff.rfl)
    (freshAt_slice_hwTargetBadAt_of_tgt z (fun _ _ _ y _ ↦ card_fiber_trunc128_le y) T W m)
    (freshAt_slice_hwTargetBadAt_of_tgt z
      (fun W _ ↦ card_covOut_tgt_le d.cover d.pk (d.covEx W)) T W m)

/-- **The `k` rate of `Bad`**: twice the capacity rate. -/
theorem freshAt_k_slice_bad [DecidablePred (· ∈ Bad (S := S) d N)] {G : ℕ}
    (hπ : PermGood d.perm G) (T : ℕ) (W : Hw X Z) (m : Mem S) :
    FreshAt (slice (Bad d N) W m) T (2 * capRateBound Z (N + T) G) .k := by
  classical
  rw [two_mul]
  exact freshAt_of_union (S := slice (TgtBad (S := S) d N) W m)
    (T := slice (CovBadOf (S := S) d N) W m) (fun _ ↦ Iff.rfl)
    (freshAt_k_slice_hwTargetBad hπ T W m) (freshAt_k_slice_hwTargetBad hπ T W m)

/-- **The `k'` rate of `Bad`**: twice the capacity rate. -/
theorem freshAt_k'_slice_bad [DecidablePred (· ∈ Bad (S := S) d N)] {G : ℕ}
    (hπ : PermGood d.perm G) (T : ℕ) (W : Hw X Z) (m : Mem S) :
    FreshAt (slice (Bad d N) W m) T (2 * capRateBound Z (N + T) G) .k' := by
  classical
  rw [two_mul]
  exact freshAt_of_union (S := slice (TgtBad (S := S) d N) W m)
    (T := slice (CovBadOf (S := S) d N) W m) (fun _ ↦ Iff.rfl)
    (freshAt_k'_slice_hwTargetBad hπ T W m) (freshAt_k'_slice_hwTargetBad hπ T W m)

end bad

end Quantum.Sphincs

namespace Quantum.Sphincs.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Par
open Quantum.Xmss (X Z)
open Quantum.Xmss.Assembly (recHwSpec recSpec runtimeR extWeight portR recStep
  querySupportedOn_recStep tsum_potential_recStep_le capRateBound_ne_top)

/- Instance search for `DecidableEq (Mem HPos)` (the read ports' memory) exceeds the default. -/
set_option synthInstance.maxSize 2000

/-! ## The leanSPHINCS event bound with depth -/

/-- **The `h` rate of the cell events of `BadR p v`**: `2^960 / |X| + 2^838 coverMass S★(v) / |X|`
(Struct and Enc, coverage). -/
noncomputable def epsHS (v : (s : HPos) → XD s) : ℝ≥0∞ :=
  ((2 ^ 960 : ℕ) : ℝ≥0∞) / Fintype.card X +
    ((2 ^ 838 * coverMass (coverOf v) : ℕ) : ℝ≥0∞) / Fintype.card X

theorem epsHS_ne_top (v : (s : HPos) → XD s) : epsHS v ≠ ⊤ := by
  have hX : (Fintype.card X : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hX,
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hX⟩

/-- **The cell events of `BadR`**: those of Events' `Bad` at `evData p v`. -/
def ScR (p : Pub) (v : (s : HPos) → XD s) (N : ℕ) (z : Z) : Set (HwReg X Z (Mem HPos)) :=
  CellBad (evData p v) N z

/-- Membership in a cell event of `BadR`, decided classically. -/
noncomputable local instance scRDec (p : Pub) (v : (s : HPos) → XD s) (N : ℕ) (z : Z) :
    DecidablePred (· ∈ ScR p v N z) :=
  fun _ ↦ Classical.propDecidable _

/-- The `h` rate of the cell events of `BadR`: `epsHS v`. -/
theorem freshAt_slice_scR (p : Pub) (v : (s : HPos) → XD s) (N : ℕ) (z : Z) (T : ℕ) (W : Hw X Z)
    (m : Mem HPos) : FreshAt (slice (ScR p v N z) W m) T (epsHS v) .h :=
  @freshAt_slice_cellBad HPos (evData p v) N z (scRDec p v N z) T W m

/-- The `k` rate of `BadR`: twice the capacity rate. -/
theorem freshAt_k_slice_badR (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    (T : ℕ) (W : Hw X Z) (m : Mem HPos) :
    FreshAt (slice (BadR p v progCap) W m) T (2 * capRateBound Z (progCap + T) 18) .k :=
  @freshAt_k_slice_bad HPos (evData p v) progCap (badRDec p v progCap) 18 hπ T W m

/-- The `k'` rate of `BadR`: twice the capacity rate. -/
theorem freshAt_k'_slice_badR (p : Pub) (v : (s : HPos) → XD s) (hπ : PermGood p.perm 18)
    (T : ℕ) (W : Hw X Z) (m : Mem HPos) :
    FreshAt (slice (BadR p v progCap) W m) T (2 * capRateBound Z (progCap + T) 18) .k' :=
  @freshAt_k'_slice_bad HPos (evData p v) progCap (badRDec p v progCap) 18 hπ T W m

/-- **The leanSPHINCS event bound with depth.** A parallel program over
`parSpec (recHwSpec X Z HPos Selections) portR` with `q_h` calls of `h` in `d_h` rounds (a single
call counts as a round), `n_k` calls of `k` and `k'` (single or in rounds), `K` classical calls and
no round mixing ports, run against `(runtimeR m0R).par portR`, ends in `BadR p v progCap` with
`√w ≤ √(6 epsHS v d_h q_h) + n_k √(6 · 2 ε_c) + √(∑ classical costs)`, the classical costs those
of `ewPrefix_le_ref`. -/
theorem rpow_inv_two_eventWeight_runtimeR_par_le (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xr : QReg → Type w}
    {A : QReg}
    (x : QuantumComp Λ (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)) Xr A)
    {qh dh nk K : ℕ}
    (hxq : IFreeM.IsChargeBound x (portCharge (portWidth (portR X Z HPos Selections) .h)) qh)
    (hxd : IFreeM.IsChargeBound x (portCharge (portDepth (portR X Z HPos Selections) .h)) dh)
    (hxk : IFreeM.IsChargeBound x (portCharge (capWidth (portR X Z HPos Selections))) nk)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z (Mem HPos) (recSpec HPos Selections)))) K)
    (hxm : IFreeM.IsChargeBound x (portCharge (mixedRounds (portR X Z HPos Selections))) 0)
    (ρ : SubState A) :
    ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight I
        (hwProjector (BadR p v progCap)) x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ^ (2⁻¹ : ℝ) ≤
      (6 * epsHS v * dh * qh) ^ (2⁻¹ : ℝ) +
        nk * (6 * (2 * capRateBound Z (progCap + (qh + nk + K + 1)) 18)) ^ (2⁻¹ : ℝ) +
        ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight I
          (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref p v) (dPof p v)))) x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ^ (2⁻¹ : ℝ) := by
  have h := rpow_inv_two_eventWeight_extend_split_le (BadR p v progCap) (ScR p v progCap)
    (fun z ↦ cellBad_subset (evData p v) progCap z) (fun _ hr ↦ exists_mem_cellBad hr)
    (fun z s s' h₁ h₂ h₃ ↦ mem_cellBad_congr (evData p v) progCap z s s' h₁ h₂ h₃)
    (fun z W m ↦ upClosedAt_slice_cellBad (evData p v) progCap z W m)
    (fun W m ↦ upClosed_slice_bad W m) (hwEmpty X Z) m0R (not_mem_bad_empty m0R)
    (epsHS_ne_top v) (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (capRateBound_ne_top _ _))
    (fun z W m ↦ freshAt_slice_scR p v progCap z _ W m)
    (fun W m ↦ freshAt_k_slice_badR p v hπ _ W m) (fun W m ↦ freshAt_k'_slice_badR p v hπ _ W m)
    (dRref p v) (dPof p v)
    (fun c σ hσ ↦ potential_hwReadKraus_le_refinedT (BadR p v progCap) c σ hσ)
    (fun c σ hσ ↦ potential_hwProgKraus_le (BadR p v progCap) (fun _ ↦ 0)
      (fun _ ↦ conjTranspose_zero) (fun _ ↦ mul_zero 0) c σ hσ)
    (Quantum.Xmss.Hybrid.initHw X Z m0R) (spongeHardwiredRuntime X Z (hwEmpty X Z) m0R).step
    rfl rfl (t := recSpec HPos Selections) recStep (fun _ _ ↦ 0)
    (fun T r n σ hσ ↦ querySupportedOn_recStep T r n σ hσ)
    (fun T σ hσ ↦ tsum_potential_recStep_le (BadR p v progCap) (labelFree_badR p v progCap) T σ
      hσ)
    (portR X Z HPos Selections) (fun _ ↦ rfl) I x hxq hxd hxk hxK hxm ρ
  refine h.trans_eq ?_
  congr 4
  funext i σ
  rcases i with i | j <;> rfl

/-- **The leanSPHINCS event bound with depth**, squared. -/
theorem eventWeight_runtimeR_par_le (p : Pub) (v : (s : HPos) → XD s)
    (hπ : PermGood p.perm 18) {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Xr : QReg → Type w}
    {A : QReg}
    (x : QuantumComp Λ (parSpec (recHwSpec X Z HPos Selections) (portR X Z HPos Selections)) Xr A)
    {qh dh nk K : ℕ}
    (hxq : IFreeM.IsChargeBound x (portCharge (portWidth (portR X Z HPos Selections) .h)) qh)
    (hxd : IFreeM.IsChargeBound x (portCharge (portDepth (portR X Z HPos Selections) .h)) dh)
    (hxk : IFreeM.IsChargeBound x (portCharge (capWidth (portR X Z HPos Selections))) nk)
    (hxK : IFreeM.IsChargeBound x (portCharge (clsCount (portR X Z HPos Selections)
      (hwExtCls X Z (Mem HPos) (recSpec HPos Selections)))) K)
    (hxm : IFreeM.IsChargeBound x (portCharge (mixedRounds (portR X Z HPos Selections))) 0)
    (ρ : SubState A) :
    ((runtimeR m0R).par (portR X Z HPos Selections)).eventWeight I
        (hwProjector (BadR p v progCap)) x
        (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ≤
      ((6 * epsHS v * dh * qh) ^ (2⁻¹ : ℝ) +
        nk * (6 * (2 * capRateBound Z (progCap + (qh + nk + K + 1)) 18)) ^ (2⁻¹ : ℝ) +
        ((runtimeR m0R).par (portR X Z HPos Selections)).totalWeight I
          (parWeight (portR X Z HPos Selections) (extWeight (hwCost (dRref p v) (dPof p v)))) x
          (ρ.matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m0R).init.matrix) ^ (2⁻¹ : ℝ)) ^ 2 := by
  have h := ENNReal.rpow_le_rpow (rpow_inv_two_eventWeight_runtimeR_par_le p v hπ I x hxq hxd hxk
    hxK hxm ρ) (by norm_num : (0 : ℝ) ≤ 2)
  rwa [rpow_inv_two_rpow_two, ENNReal.rpow_two] at h

end Quantum.Sphincs.Assembly

end
