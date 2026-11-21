module

public import Quantum.Sphincs.Assembly.EncPotential
public import Quantum.Xmss.Assembly.EncPorts

@[expose] public section

/-!
# The ports of leanSPHINCS's cross-key potential

EncPotential's `totalWeight_cntGW_le` bounds the joint count `cntGW` of the selecting reads along a
run of `runtimeR`, given port conditions `hS`, `hR`, `hPr` and `hnb` on the potential `encPot`.
This file discharges them for every run of `runtimeR` with bounded calls and states the joint
count with explicit charges (`totalWeight_cntGW_le_calls`), as leanXMSS's
`Quantum.Xmss.Assembly.EncPorts` does on its challenge prefix; the generic parts of that file
(two-sided fresh bounds `PortInst`, level sets `levSet`, `tsum_potential_sponge_layer_le`,
`tsum_potential_read_layer_le`, `tsum_potential_spongeH_le`, `readCost_le_of_keep`,
`keepE_le_of_portInst`, `progJump`, `tsum_potential_prog_le`, `progJump_le`) are reused.

* **The potential as a count** (`encPotU`, `encPotN`): on a good union, the codeword counts of the
  unselected keys; at most the union's `h` cells (`encPotU_le`, the keys share the encoding-slot
  cells), changing by at most one with one `h` cell (`encPot_update_h_le`), and only through
  `badAttachK`, `badCompleteOutK'` at fresh `k`, `k'` cells (`encPotN_updK_ne`,
  `encPotN_updK'_ne`), whence two-sided fresh bounds of its level sets (`portInst_levSet_k`,
  `portInst_levSet_k'`).
* **Programs** (`RecJ`, `KJump`, `encPot_progMap_le`): off the jump states a program raises the
  potential by at most one; the jump states are a hardwired cell with another value, a target-free
  fresh flip (`FlipK`, `FlipK'`) or `RecJ` (a bad union made bad by the database value at the
  programmed cell); inside the `k`, `k'` cells of a hardwired table (`HwLeK`, `ProgOfK`) they
  split into `kfW` and `recJW` (`kJumpW_le`).
* **The port invariant of a run** (`PortInv`, `forallQueries_portInv`): with at most `n` sponge,
  `K` classical and `P` program calls, and only `EncReadOk` reads (the trial reads and `k`, `k'`
  reads keeping the memory, charge `okChg` of budget `0`), every call has database grade at most
  `n + K`, hardwired grade at most `P`, and no decompressed `⊥`.
* **The ports** (`hS_port`, `hR_port`, `progJump_le_port`, `trialChg_le_port`, `readCharge_le`).
* **The joint count** (`totalWeight_cntGW_le_calls`): at most `2^15 (n + P)` plus `2^15` times
  `(3C + 3)` per unit of recorded mass (`massW`, `C = nW P + nD`), `kapS` per sponge call, `kapR`
  per classical call and `potCap` per unit of the program jump weight; the codeword flips along
  the run are `2^-128` of it (`totalWeight_encW_le`), the jump weight splits into the target-free
  flips and `RecJ` (`totalWeight_kJumpW_le`).
-/

universe u v w

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Assembly Quantum.Xmss.Hybrid Sphincs
open Quantum.Xmss (X Z trunc128 extProgCharge)

namespace Quantum.Sphincs.Assembly

/-! ## The potential as a count -/

section encN

/-- A key, for the potential's split at an arbitrary key. -/
def key₀ : Key :=
  (⟨0, by decide⟩, ⟨0, Nat.two_pow_pos _⟩, ⟨0, Nat.two_pow_pos _⟩)

open scoped Classical in
/-- **The cross-key potential of a union and a selection** as a count: on a good union, the
codeword counts of the unselected keys. -/
noncomputable def encPotU (d : EvData) (U : Dbs X Z) (g : Selections) : ℕ :=
  if Good d.perm U then
    ∑ K : Key, if g K = none then encCwCount d U K else 0
  else 0

theorem encPotU_congr (d : EvData) {U U' : Dbs X Z} (hk : U'.k = U.k) (hk' : U'.k' = U.k')
    (hh : ∀ z, U'.h z = U.h z) (g : Selections) : encPotU d U' g = encPotU d U g := by
  unfold encPotU
  by_cases hG : Good d.perm U
  · rw [ite_eq_left ((good_congr hk hk').2 hG), ite_eq_left hG]
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    rw [encCwCount_eq_tailOutCount, encCwCount_eq_tailOutCount,
      tailOutCount_congr_of_iff fun z ↦ outAt_congr hk hk' (hh z) _ _]
  · rw [ite_eq_right fun h ↦ hG ((good_congr hk hk').1 h), ite_eq_right hG]

theorem encPotU_congr_k' (d : EvData) {U U' : Dbs X Z} (hk' : U'.k' = U.k')
    (hk : U'.k = U.k) (hh : ∀ z, U'.h z = U.h z) (g : Selections) :
    encPotU d U' g = encPotU d U g :=
  encPotU_congr d hk hk' hh g

theorem encPotU_le (d : EvData) (U : Dbs X Z) (g : Selections) :
    encPotU d U g ≤ U.h.size := by
  unfold encPotU
  split_ifs with hG
  · exact (Finset.sum_le_sum (g := fun K : Key ↦ encCwCount d U K)
      fun K _ ↦ by split_ifs <;> simp).trans
        ((sum_encCwCount_le hG).trans (encSlotCount_le_size d U))
  · exact Nat.zero_le _

/-- **A `k` value outside `badAttachK` keeps the potential** of a good union. -/
theorem encPotU_updK_eq (d : EvData) {U : Dbs X Z} (hG : Good d.perm U) {x : X}
    (hx : U.k x = none) {u : Z} (hu : u ∉ badAttachK d.perm U x) (g : Selections) :
    encPotU d { U with k := Function.update U.k x (some u) } g = encPotU d U g := by
  unfold encPotU
  rw [ite_eq_left (updateK_tails hG hx hu).1, ite_eq_left hG]
  refine Finset.sum_congr rfl fun K _ ↦ ?_
  rw [encCwCount_eq_tailOutCount, encCwCount_eq_tailOutCount,
    tailOutCount_congr_of_iff fun z ↦ outAt_update_k_iff hG hx hu _ _ z]

/-- **A `k'` value outside `badCompleteOutK'` keeps the potential** of a good union. -/
theorem encPotU_updK'_eq (d : EvData) {U : Dbs X Z} (hG : Good d.perm U) {x : X}
    (hx : U.k' x = none) {u : Z} (hu : u ∉ badCompleteOutK' d.perm U x) (g : Selections) :
    encPotU d { U with k' := Function.update U.k' x (some u) } g = encPotU d U g := by
  unfold encPotU
  rw [ite_eq_left (updateK'_tails hG hx hu).1, ite_eq_left hG]
  refine Finset.sum_congr rfl fun K _ ↦ ?_
  rw [encCwCount_eq_tailOutCount, encCwCount_eq_tailOutCount,
    tailOutCount_congr_of_iff fun z ↦ outAt_update_k'_iff hG hx hu _ _ z]

theorem encPotU_of_not_good (d : EvData) {U : Dbs X Z} (hG : ¬ Good d.perm U)
    (g : Selections) : encPotU d U g = 0 := by
  unfold encPotU
  rw [ite_eq_right hG]

theorem encPotU_mono (d : EvData) {U U₀ : Dbs X Z} (hE : Extends U U₀)
    (hh : ∀ z, U₀.h z = U.h z) (hG : Good d.perm U) (g : Selections) :
    encPotU d U₀ g ≤ encPotU d U g := by
  unfold encPotU
  rw [ite_eq_left (Good.mono hE hG), ite_eq_left hG]
  refine Finset.sum_le_sum fun K _ ↦ ?_
  split_ifs
  · rw [encCwCount_eq_tailOutCount, encCwCount_eq_tailOutCount]
    exact tailOutCount_le_of_imp fun z ⟨t, xi, w, hP, hi, hw, hq⟩ ↦
      ⟨t, xi, w, hP, hi.mono hE, (hh z) ▸ hw, hq⟩
  · exact le_rfl

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)

/-- **The cross-key potential as a count** on the hardwired register. -/
noncomputable def encPotN (d : EvData) (s : HwReg X Z M) : ℕ :=
  encPotU d (union s.2.1 s.1) (get s.2.2)

omit [Fintype M] [DecidableEq M] in
theorem encPot_eq_encPotN (d : EvData) (s : HwReg X Z M) :
    encPot get d s = (encPotN get d s : ℝ) := by
  unfold encPot encPotN encPotU
  split_ifs
  · rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    rw [Nat.cast_ite, Nat.cast_zero]
  · rw [Nat.cast_zero]

omit [Fintype M] [DecidableEq M] in
theorem sqrt_encPot_eq (d : EvData) :
    (fun s : HwReg X Z M ↦ √(encPot get d s)) = fun s ↦ √(encPotN get d s : ℝ) :=
  funext fun s ↦ by rw [encPot_eq_encPotN]

omit [Fintype M] [DecidableEq M] in
/-- **The potential is at most the hardwired and database grades.** -/
theorem encPotN_le (d : EvData) (s : HwReg X Z M) :
    encPotN get d s ≤ dbGrade s.2.1 + dbGrade s.1 :=
  (encPotU_le d _ _).trans (size_unionH_le s.2.1 s.1)

omit [Fintype M] [DecidableEq M] in
open scoped Classical in
/-- **The potential changes by at most one with the union's `h` cell `z`**, the `k`, `k'` cells
and the selections kept. -/
theorem encPot_le_add_one_of_off (d : EvData) (z : Z) {s s' : HwReg X Z M}
    (hk : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk' : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k')
    (hh : ∀ b, b ≠ z → (union s'.2.1 s'.1).h b = (union s.2.1 s.1).h b)
    (hm : get s'.2.2 = get s.2.2) : encPot get d s' ≤ encPot get d s + 1 := by
  have hoff : ∀ K, encOff d z K s' = encOff d z K s := fun K ↦ by
    unfold encOff
    rw [tailOutOff_congr hk hk' hh]
    exact if_congr (good_congr hk hk') rfl rfl
  have hA : encA get d z key₀ s' = encA get d z key₀ s := by
    unfold encA
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    rw [hm, hoff K]
  have hB : encB get d z key₀ s' = encB get d z key₀ s := by
    unfold encB
    rw [hm, hoff key₀]
  have e' := encPot_eq get d z key₀ ((), s')
  have e := encPot_eq get d z key₀ ((), s)
  have h1 := ind_le_one (liftSet (encCSet get d z)) ((), s')
  have h0 := ind_nonneg (liftSet (encCSet get d z)) ((), s)
  simp only at e e'
  linarith

omit [Fintype M] [DecidableEq M] in
/-- **The potential is one-cell Lipschitz in the database's `h` cells.** -/
theorem encPot_update_h_le (d : EvData) (D : DbReg X Z) (b : Hw X Z × M) (z : Z)
    (v : Option X) :
    encPot get d ((Function.update D.1 z v, D.2.1, D.2.2), b) ≤ encPot get d (D, b) + 1 :=
  encPot_le_add_one_of_off get d z (union_k_of_h b.1 D _) (union_k'_of_h b.1 D _)
    (fun _ hy ↦ union_updH_off b.1 D hy v) rfl

omit [Fintype M] [DecidableEq M] in
/-- **The values of a fresh `k` cell changing the potential lie in `badAttachK`** of a good
union, the cell not hardwired. -/
theorem encPotN_updK_ne (d : EvData) {s : HwReg X Z M} {x : X} (hx : s.1.2.1 x = none)
    {u : Z} (hne : encPotN get d ((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2), s.2) ≠
      encPotN get d s) :
    s.2.1.2.1 x = none ∧ Good d.perm (union s.2.1 s.1) ∧
      u ∈ badAttachK d.perm (union s.2.1 s.1) x := by
  unfold encPotN at hne
  by_cases hW : s.2.1.2.1 x = none
  · have hUx : (union s.2.1 s.1).k x = none := union_k_none hW hx
    have hV : encPotU d (union s.2.1 (s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2))
        (get s.2.2) = encPotU d { union s.2.1 s.1 with
          k := Function.update (union s.2.1 s.1).k x (some u) } (get s.2.2) :=
      encPotU_congr (U' := union s.2.1 (s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2))
        (U := { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k x (some u) }) d
        (union_updK_of_none_with s.2.1 s.1 hW u) (union_k'_of_k s.2.1 s.1 _)
        (union_h_of_k s.2.1 s.1 _) _
    by_cases hG : Good d.perm (union s.2.1 s.1)
    · refine ⟨hW, hG, ?_⟩
      by_contra hu
      exact hne (hV.trans (encPotU_updK_eq d hG hUx hu _))
    · refine absurd ?_ hne
      rw [hV, encPotU_of_not_good d (fun h ↦ hG (Good.mono (extends_update_k hUx) h)),
        encPotU_of_not_good d hG]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hW
    exact absurd (encPotU_congr
      (U' := union s.2.1 (s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2))
      (U := union s.2.1 s.1) d (union_updK_of_some s.2.1 s.1 hb u)
      (union_k'_of_k s.2.1 s.1 _) (union_h_of_k s.2.1 s.1 _) (get s.2.2)) hne

omit [Fintype M] [DecidableEq M] in
/-- **The values of a fresh `k'` cell changing the potential lie in `badCompleteOutK'`** of a
good union, the cell not hardwired. -/
theorem encPotN_updK'_ne (d : EvData) {s : HwReg X Z M} {x : X} (hx : s.1.2.2 x = none)
    {u : Z} (hne : encPotN get d ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)), s.2) ≠
      encPotN get d s) :
    s.2.1.2.2 x = none ∧ Good d.perm (union s.2.1 s.1) ∧
      u ∈ badCompleteOutK' d.perm (union s.2.1 s.1) x := by
  unfold encPotN at hne
  by_cases hW : s.2.1.2.2 x = none
  · have hUx : (union s.2.1 s.1).k' x = none := union_k'_none hW hx
    have hV : encPotU d (union s.2.1 (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)))
        (get s.2.2) = encPotU d { union s.2.1 s.1 with
          k' := Function.update (union s.2.1 s.1).k' x (some u) } (get s.2.2) :=
      encPotU_congr (U' := union s.2.1 (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)))
        (U := { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' x (some u) }) d
        (union_k_of_k' s.2.1 s.1 _) (union_updK'_of_none_with s.2.1 s.1 hW u)
        (union_h_of_k' s.2.1 s.1 _) _
    by_cases hG : Good d.perm (union s.2.1 s.1)
    · refine ⟨hW, hG, ?_⟩
      by_contra hu
      exact hne (hV.trans (encPotU_updK'_eq d hG hUx hu _))
    · refine absurd ?_ hne
      rw [hV, encPotU_of_not_good d (fun h ↦ hG (Good.mono (extends_update_k' hUx) h)),
        encPotU_of_not_good d hG]
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hW
    exact absurd (encPotU_congr
      (U' := union s.2.1 (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)))
      (U := union s.2.1 s.1) d (union_k_of_k' s.2.1 s.1 _)
      (union_updK'_of_some s.2.1 s.1 hb u) (union_h_of_k' s.2.1 s.1 _) (get s.2.2)) hne

omit [Fintype M] [DecidableEq M] in
/-- **Two-sided fresh bounds of the level sets of the potential at `k`.** -/
theorem portInst_levSet_k (d : EvData) {G : ℕ} (hπ : PermGood d.perm G) (Nw n m : ℕ)
    (W : Hw X Z) (mm : M) :
    PortInst (slice (levSet (encPotN get d) Nw m) W mm) .k (n + 1)
      (ENNReal.ofReal (epsLev (Nw + n) G)) := by
  have h := portInst_k_of_card (levSet (encPotN get d) Nw m) W mm (n := n)
    (J := capKJ (Nw + n) G + capKJ' (Nw + n) G) fun s hD x hx ↦
      (card_levFlip_k_le (encPotN get d) d.perm hπ Nw m n s hD fun u hne ↦
        encPotN_updK_ne get d hx hne).trans (Nat.le_add_right _ _)
  exact h

omit [Fintype M] [DecidableEq M] in
/-- **Two-sided fresh bounds of the level sets of the potential at `k'`.** -/
theorem portInst_levSet_k' (d : EvData) {G : ℕ} (hπ : PermGood d.perm G) (Nw n m : ℕ)
    (W : Hw X Z) (mm : M) :
    PortInst (slice (levSet (encPotN get d) Nw m) W mm) .k' (n + 1)
      (ENNReal.ofReal (epsLev (Nw + n) G)) := by
  have h := portInst_k'_of_card (levSet (encPotN get d) Nw m) W mm (n := n)
    (J := capKJ (Nw + n) G + capKJ' (Nw + n) G) fun s hD x hx ↦
      (card_levFlip_k'_le (encPotN get d) d.perm hπ Nw m n s hD fun u hne ↦
        encPotN_updK'_ne get d hx hne).trans (Nat.le_add_left _ _)
  exact h

end encN

/-! ## Programs -/

section levels

variable {M : Type} [Fintype M] [DecidableEq M] (get : M → Selections)

/-- **A bad union made good by programming the cell**: the cell not hardwired, the union bad and
the union with the cell emptied good (the database records at the cell a value that breaks
goodness). -/
def RecJ (d : EvData) : HwProg X Z → HwReg X Z M → Prop
  | .programH _ _, _ => False
  | .programK y _, s => s.2.1.2.1 y = none ∧ ¬ Good d.perm (union s.2.1 s.1) ∧
      Good d.perm { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none }
  | .programK' y _, s => s.2.1.2.2 y = none ∧ ¬ Good d.perm (union s.2.1 s.1) ∧
      Good d.perm { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none }

/-- **The program states whose potential may jump**: none for `h`; for `k` (`k'`) a hardwired
cell with another value, a target-free fresh flip (`FlipK`, `FlipK'`) or `RecJ`. -/
def KJump (d : EvData) : HwProg X Z → HwReg X Z M → Prop
  | .programH _ _, _ => False
  | .programK y a, s => (s.2.1.2.1 y ≠ none ∧ s.2.1.2.1 y ≠ some a) ∨
      FlipK d.perm s.2.1 s.1 y a ∨ RecJ d (.programK y a) s
  | .programK' y a, s => (s.2.1.2.2 y ≠ none ∧ s.2.1.2.2 y ≠ some a) ∨
      FlipK' d.perm s.2.1 s.1 y a ∨ RecJ d (.programK' y a) s

/-- The jump states, decided classically. -/
noncomputable instance kJumpDec (d : EvData) (c : HwProg X Z) :
    DecidablePred (KJump (M := M) d c) :=
  Classical.decPred _

/-- The `RecJ` states, decided classically. -/
noncomputable instance recJDec (d : EvData) (c : HwProg X Z) :
    DecidablePred (RecJ (M := M) d c) :=
  Classical.decPred _

omit [Fintype M] [DecidableEq M] in
/-- **Off the jump states a program raises the potential by at most one.** -/
theorem encPot_progMap_le (d : EvData) (c : HwProg X Z) (s : HwReg X Z M)
    (h : ¬ KJump d c s) : encPot get d (progMap c s) ≤ encPot get d s + 1 := by
  cases c with
  | programH z v =>
    exact encPot_le_add_one_of_off get d z (s := s) (s' := progMap (.programH z v) s)
      (union_progMapH_k z v s) (union_progMapH_k' z v s) (fun _ hy ↦ union_progMapH_h z v s hy)
      (congrArg get (progMap_mem _ s))
  | programK y a =>
    have hle : encPotN get d (progMap (.programK y a) s) ≤ encPotN get d s := by
      have hW : s.2.1.2.1 y ≠ none → s.2.1.2.1 y = some a := fun h1 ↦ by
        by_contra h2
        exact h (.inl ⟨h1, h2⟩)
      have hF : ¬ FlipK d.perm s.2.1 s.1 y a := fun h' ↦ h (.inr (.inl h'))
      have hR : ¬ RecJ d (.programK y a) s := fun h' ↦ h (.inr (.inr h'))
      unfold encPotN
      rw [union_progMapK y a s, progMap_mem]
      by_cases hWn : s.2.1.2.1 y = none
      · by_cases hG : Good d.perm (union s.2.1 s.1)
        · have hG₀ : Good d.perm
              { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } :=
            Good.mono (extendsAll_eraseK (union s.2.1 s.1) y).1 hG
          have ha : a ∉ badAttachK d.perm
              { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } y :=
            not_and.mp (not_and.mp hF hWn) hG₀
          rw [encPotU_updK_eq d hG₀ (eraseK_k_self (union s.2.1 s.1) y) ha]
          exact encPotU_mono d (extendsAll_eraseK (union s.2.1 s.1) y).1 (fun _ ↦ rfl) hG _
        · have hG₀ : ¬ Good d.perm
              { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } :=
            fun h₀ ↦ hR ⟨hWn, hG, h₀⟩
          rw [encPotU_of_not_good d fun h' ↦ hG₀ (Good.mono
            (extends_update_k (eraseK_k_self (union s.2.1 s.1) y)) h')]
          exact Nat.zero_le _
      · exact le_of_eq (encPotU_congr d (reprogK_k (union_k_some (D := s.1) (hW hWn))) rfl
          (fun _ ↦ rfl) _)
    rw [encPot_eq_encPotN, encPot_eq_encPotN]
    exact (Nat.cast_le.mpr hle).trans (le_add_of_nonneg_right zero_le_one)
  | programK' y a =>
    have hle : encPotN get d (progMap (.programK' y a) s) ≤ encPotN get d s := by
      have hW : s.2.1.2.2 y ≠ none → s.2.1.2.2 y = some a := fun h1 ↦ by
        by_contra h2
        exact h (.inl ⟨h1, h2⟩)
      have hF : ¬ FlipK' d.perm s.2.1 s.1 y a := fun h' ↦ h (.inr (.inl h'))
      have hR : ¬ RecJ d (.programK' y a) s := fun h' ↦ h (.inr (.inr h'))
      unfold encPotN
      rw [union_progMapK' y a s, progMap_mem]
      by_cases hWn : s.2.1.2.2 y = none
      · by_cases hG : Good d.perm (union s.2.1 s.1)
        · have hG₀ : Good d.perm
              { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } :=
            Good.mono (extendsAll_eraseK' (union s.2.1 s.1) y).1 hG
          have ha : a ∉ badCompleteOutK' d.perm
              { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } y :=
            not_and.mp (not_and.mp hF hWn) hG₀
          rw [encPotU_updK'_eq d hG₀ (eraseK'_k'_self (union s.2.1 s.1) y) ha]
          exact encPotU_mono d (extendsAll_eraseK' (union s.2.1 s.1) y).1 (fun _ ↦ rfl) hG _
        · have hG₀ : ¬ Good d.perm
              { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } :=
            fun h₀ ↦ hR ⟨hWn, hG, h₀⟩
          rw [encPotU_of_not_good d fun h' ↦ hG₀ (Good.mono
            (extends_update_k' (eraseK'_k'_self (union s.2.1 s.1) y)) h')]
          exact Nat.zero_le _
      · exact le_of_eq (encPotU_congr_k' d (reprogK'_k' (union_k'_some (D := s.1) (hW hWn))) rfl
          (fun _ ↦ rfl) _)
    rw [encPot_eq_encPotN, encPot_eq_encPotN]
    exact (Nat.cast_le.mpr hle).trans (le_add_of_nonneg_right zero_le_one)

/-- **The weight of the jump states** of a program port. -/
noncomputable def kJumpW (d : EvData) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ q, (if KJump d c q.2 then (1 : ℝ) else 0) * (σ q q).re)

/-- **The weight of the `RecJ` states** of a program port. -/
noncomputable def recJW (d : EvData) (c : HwProg X Z)
    (σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ q, (if RecJ d c q.2 then (1 : ℝ) else 0) * (σ q q).re)

/-- **The target-free flip set of a `k` port at `y` with value `a`**: the facts `FlipK`, at most
`P` hardwired cells per function and at most `T - P` database entries. -/
def kfSet (π : Equiv.Perm (X × Z)) (P T : ℕ) (y : X) (a : Z) : Set (Unit × HwReg X Z M) :=
  {q | FlipK π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ P ∧ P + dbGrade q.2.1 ≤ T}

/-- **The target-free flip set of a `k'` port at `y` with value `a`.** -/
def kfSet' (π : Equiv.Perm (X × Z)) (P T : ℕ) (y : X) (a : Z) : Set (Unit × HwReg X Z M) :=
  {q | FlipK' π q.2.2.1 q.2.1 y a ∧ dbGrade q.2.2.1 ≤ P ∧ P + dbGrade q.2.1 ≤ T}

/-- **The target-free flip weights of the program ports.** -/
noncomputable def kfW (π : Equiv.Perm (X × Z)) (P T : ℕ) :
    HwProg X Z → Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ → ℝ≥0∞
  | .programK y a, σ => diagMass (kfSet π P T y a) σ
  | .programK' y a, σ => diagMass (kfSet' π P T y a) σ
  | .programH _ _, _ => 0

/-- **`W`'s hardwired `k`, `k'` cells are `Wt`'s**, with their values (`HwLe` without the `h`
cells). -/
def HwLeK (W Wt : Hw X Z) : Prop :=
  (∀ x a, W.2.1 x = some a → Wt.2.1 x = some a) ∧ ∀ x a, W.2.2 x = some a → Wt.2.2 x = some a

/-- **A program of a `k` or `k'` cell of `Wt` with its value**; `h` programs are free. -/
def ProgOfK (Wt : Hw X Z) : HwProg X Z → Prop
  | .programH _ _ => True
  | .programK x a => Wt.2.1 x = some a
  | .programK' x a => Wt.2.2 x = some a

omit [DecidableEq M] in
/-- **The jump states split**: at states whose hardwired `k`, `k'` cells are a table `Wt`'s, with a
port programming a `k`, `k'` cell with its `Wt` value, at most `P` hardwired cells per function and
at most `T - P` database entries, a jump state is a target-free fresh flip (`kfSet`, `kfSet'`) or a
`RecJ` state. -/
theorem kJumpW_le (d : EvData) {P T : ℕ} {Wt : Hw X Z} (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef)
    (hsupp : ∀ q, σ q q ≠ 0 → ProgOfK Wt c ∧ HwLeK q.2.2.1 Wt ∧
      dbGrade q.2.2.1 ≤ P ∧ P + dbGrade q.2.1 ≤ T) :
    kJumpW d c σ ≤ kfW d.perm P T c σ + recJW d c σ := by
  classical
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hsum : ∀ (p : Unit × HwReg X Z M → Prop) [DecidablePred p],
      ENNReal.ofReal (∑ q, (if p q then (1 : ℝ) else 0) * (σ q q).re) =
        ∑ q, ENNReal.ofReal ((if p q then (1 : ℝ) else 0) * (σ q q).re) := fun p _ ↦
    ENNReal.ofReal_sum_of_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> norm_num) (hre q)
  have key : ∀ S : Set (Unit × HwReg X Z M),
      (∀ q, σ q q ≠ 0 → KJump d c q.2 → q ∈ S ∨ RecJ d c q.2) →
      kJumpW d c σ ≤ diagMass S σ + recJW d c σ := fun S hS ↦ by
    unfold kJumpW recJW diagMass
    rw [hsum (fun q ↦ KJump d c q.2), hsum (fun q ↦ RecJ d c q.2), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases h0 : σ q q = 0
    · rw [h0, Complex.zero_re, mul_zero, ENNReal.ofReal_zero]
      exact zero_le
    · exact ofReal_ind_mul_le S (fun a ↦ ENNReal.ofReal (σ a a).re) q rfl (hS q h0)
  cases c with
  | programH z v =>
    refine (key ∅ fun _ _ h ↦ h.elim).trans_eq ?_
    show diagMass ∅ σ + _ = (0 : ℝ≥0∞) + _
    rw [diagMass_empty]
  | programK y a =>
    refine key (kfSet d.perm P T y a) fun q h0 h ↦ ?_
    obtain ⟨hc, hW, hg1, hg2⟩ := hsupp q h0
    rcases h with ⟨h1, h2⟩ | hF | hR
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
      have hc' : Wt.2.1 y = some a := hc
      have h3 : Wt.2.1 y = some b := hW.1 y b hb
      exact absurd (hb.trans (Option.some.inj (h3.symm.trans hc') ▸ rfl)) h2
    · exact .inl ⟨hF, hg1, hg2⟩
    · exact .inr hR
  | programK' y a =>
    refine key (kfSet' d.perm P T y a) fun q h0 h ↦ ?_
    obtain ⟨hc, hW, hg1, hg2⟩ := hsupp q h0
    rcases h with ⟨h1, h2⟩ | hF | hR
    · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
      have hc' : Wt.2.2 y = some a := hc
      have h3 : Wt.2.2 y = some b := hW.2 y b hb
      exact absurd (hb.trans (Option.some.inj (h3.symm.trans hc') ▸ rfl)) h2
    · exact .inl ⟨hF, hg1, hg2⟩
    · exact .inr hR

end levels

/-! ## The port invariant of a run -/

section portInv

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- **The reads whose costs are priced here**: a trial's selecting `h`-read, or a `k`, `k'` read
keeping the memory. -/
def EncReadOk : HwRead X Z (Finset S × M') → Prop
  | .readH z u => IsTrial updOf (.readH z u)
  | .readK _ u => ∀ m o, u m o = m
  | .readK' _ u => ∀ m o, u m o = m

/-- The read ports of `runtimeR` satisfy `Ok`; the other ports are free. -/
def OkPort (Ok : HwRead X Z (Finset S × M') → Prop) : (recHwSpec X Z S M').Port → Prop
  | .inl (.inl (.inr c)) => Ok c
  | _ => True

open scoped Classical in
/-- The charge of a port: `0` on the ports satisfying `OkPort`, `1` otherwise. -/
noncomputable def okChg (Ok : HwRead X Z (Finset S × M') → Prop) (i : (recHwSpec X Z S M').Port) :
    ℕ :=
  if OkPort Ok i then 0 else 1

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem okPort_of_okChg {Ok : HwRead X Z (Finset S × M') → Prop} {i : (recHwSpec X Z S M').Port}
    (h : okChg Ok i = 0) : OkPort Ok i := by
  by_contra hc
  rw [okChg, ite_eq_right hc] at h
  exact one_ne_zero h

/-- **The invariant at the calls of a run**: `OkPort` at the port, database grade at most `nD`,
hardwired grade at most `P`, no decompressed `⊥`. -/
def PortInv (Ok : HwRead X Z (Finset S × M') → Prop) (nD P : ℕ) (m₀ : Finset S × M')
    (i : (recHwSpec X Z S M').Port)
    (τ : Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
      ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ) : Prop :=
  OkPort Ok i ∧
    QuerySupportedOn (fun m : (recHwSpec X Z S M').In i × HwReg X Z (Finset S × M') ↦ m.2)
      {s | dbGrade s.1 ≤ nD ∧ dbGrade s.2.1 ≤ P} τ ∧
    QuerySupportedOn (fun m : (recHwSpec X Z S M').In i × HwReg X Z (Finset S × M') ↦ m.2)
      {s | NoBot s} (MatrixMap.conj ((1 : Matrix ((recHwSpec X Z S M').In i)
        ((recHwSpec X Z S M').In i) ℂ) ⊗ₖ compressReg X Z (Finset S × M')) τ)

/-- The initial state beside a basis state is at the empty register. -/
theorem querySupportedOn_basis_init {B : Type} [Fintype B] [DecidableEq B] (m₀ : Finset S × M')
    (u : B) {Y : Type} (g : HwReg X Z (Finset S × M') → Y) (T : Set Y)
    (h : g ((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀) ∈ T) :
    QuerySupportedOn (fun m : QReg.of B × (runtimeR (X := X) (Z := Z) m₀).D ↦ g m.2) T
      ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  intro m m' hm
  change ((SubState.basis u).matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty,
    Database.empty), hwEmpty X Z, m₀) : HwReg X Z (Finset S × M'))).matrix) m m' ≠ 0 at hm
  simp only [SubState.matrix_basis] at hm
  have h' := right_ne_zero_of_mul hm
  rw [Matrix.single_apply] at h'
  split_ifs at h' with he
  · exact ⟨show g m.2 ∈ T by rw [← he.1]; exact h, show g m'.2 ∈ T by rw [← he.2]; exact h⟩
  · exact False.elim (h' rfl)

/-- **The invariant holds at every call of a run** with at most `n` sponge, `K` classical and `P`
program calls and `okChg` of budget `0`, from a basis state beside the initial register
(CostRun's `forallQueries_of_charge_step` for the database and hardwired grades, EventSqrt's
`forallQueries_noBot`). -/
theorem forallQueries_portInv (Ok : HwRead X Z (Finset S × M') → Prop) (m₀ : Finset S × M')
    {Λ : LocalSig.{u, v}} (I : Λ.Interp) {Ω : QReg → Type w} {B : Type} [Fintype B]
    [DecidableEq B] (u : B) (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B))
    {n K P : ℕ}
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) K)
    (hok : IFreeM.IsChargeBound x (portCharge (okChg Ok)) 0)
    (hP : IFreeM.IsChargeBound x
      (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M'))) P) :
    ∃ Q : ∀ (i : (recHwSpec X Z S M').Port) (E : QReg),
      Matrix (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
        (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ →
          Prop, (∀ i E σ, Q i E σ → PortInv Ok (n + K) P m₀ i (MatrixMap.traceRight _ E σ)) ∧
      (runtimeR m₀).ForallQueries I Q x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  set κ : (recHwSpec X Z S M').Port → ℕ := fun i ↦
    (if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) +
      (if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) with hκ
  have hκ1 : ∀ i, κ i = 1 := fun i ↦ by
    rw [hκ]
    by_cases h : extCls X Z (Finset S × M') (recSpec S M') i = true <;> simp [h]
  have hx : IFreeM.IsChargeBound x (portCharge κ) (n + K) :=
    isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (hn.add hK)
  have h1 := forallQueries_of_charge_step (runtimeR m₀) (fun s ↦ dbGrade s.1) κ (okChg Ok)
    (fun i r t σ hσ ↦ (querySupportedOn_runtimeR_step' m₀ i r t σ hσ).mono
      (Set.Iic_subset_Iic.2 (by rw [hκ1]))) I x hx hok
    (querySupportedOn_basis_init m₀ u (fun s ↦ dbGrade s.1) (Set.Iic 0)
      (Set.mem_Iic.2 (by simp [dbGrade, Database.size_empty])))
  have h2 := forallQueries_of_charge_step (runtimeR m₀) (fun s ↦ dbGrade s.2.1)
    (extProgCharge X Z (Finset S × M') (recSpec S M')) (fun _ ↦ 0)
    (fun i r t σ hσ ↦ by
      rcases i with i | j
      · exact querySupportedOn_hw_step (hwEmpty X Z) m₀ i r t σ hσ
      · exact gradeSupp_recStep j r t σ hσ) I x hP
    (isChargeBound_mono_charge (fun _ a ↦ by cases a <;> exact le_rfl) (isChargeBound_zero x))
    (querySupportedOn_basis_init m₀ u (fun s ↦ dbGrade s.2.1) (Set.Iic 0)
      (Set.mem_Iic.2 (by simp [hwEmpty, dbGrade, Database.size_empty])))
  have h3 := forallQueries_noBot m₀ I x (noBot_init m₀ (SubState.basis u).matrix)
  refine ⟨_, fun i E σ hQ ↦ ?_, forallQueries_and (forallQueries_and h1 h2) h3⟩
  obtain ⟨⟨⟨hb, hg1⟩, ⟨-, hg2⟩⟩, hnb⟩ := hQ
  refine ⟨okPort_of_okChg hb, ?_, hnb⟩
  have g1 := (querySupportedOn_traceRight (q := fun a :
      (recHwSpec X Z S M').In i × HwReg X Z (Finset S × M') ↦ dbGrade a.2.1) hg1).imp
    (q' := fun a : (recHwSpec X Z S M').In i × HwReg X Z (Finset S × M') ↦ a.2)
    (S' := {s : HwReg X Z (Finset S × M') | dbGrade s.1 ≤ n + K}) fun a ha ↦ by
      have := Set.mem_Iic.mp ha
      show dbGrade a.2.1 ≤ n + K
      omega
  have g2 := (querySupportedOn_traceRight (q := fun a :
      (recHwSpec X Z S M').In i × HwReg X Z (Finset S × M') ↦ dbGrade a.2.2.1) hg2).imp
    (q' := fun a : (recHwSpec X Z S M').In i × HwReg X Z (Finset S × M') ↦ a.2)
    (S' := {s : HwReg X Z (Finset S × M') | dbGrade s.2.1 ≤ P}) fun a ha ↦ by
      have := Set.mem_Iic.mp ha
      show dbGrade a.2.2.1 ≤ P
      omega
  exact (querySupportedOn_inter g1 g2).imp fun _ h ↦ h

end portInv

/-! ## The ports -/

/-- The hardwired grade of the level sets: `P + 1` (a program call adds one cell). -/
def nW (P : ℕ) : ℕ := P + 1

/-- **The potential cap** on the states around the calls: `P + nD + 2`. -/
def potCap (nD P : ℕ) : ℕ := nW P + nD + 1

/-- The fresh-cell rate of the level sets: `epsLev (nW P + nD) 18`. -/
noncomputable def epsQ (nD P : ℕ) : ℝ := epsLev (nW P + nD) 18

/-- **The charge of a `k`, `k'` sponge call** per unit of trace: `potCap (2 √(6ε) + 6ε)`. -/
noncomputable def kapS (nD P : ℕ) : ℝ := potCap nD P * (2 * √(6 * epsQ nD P) + 6 * epsQ nD P)

/-- **The charge of a read call** per unit of trace: the `k`, `k'` reads'
`potCap (ε + 2/|X| + 2/|Z| + 2 √ε)`, plus the trial reads' cell charge `2/|X| + 4/|X|²`. -/
noncomputable def kapR (nD P : ℕ) : ℝ :=
  potCap nD P * (epsQ nD P + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ nD P)) +
    (2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2)

theorem epsQ_nonneg (nD P : ℕ) : 0 ≤ epsQ nD P := epsLev_nonneg _ _

theorem kapS_nonneg (nD P : ℕ) : 0 ≤ kapS nD P := by
  have := epsQ_nonneg nD P
  unfold kapS
  positivity

theorem kapR_nonneg (nD P : ℕ) : 0 ≤ kapR nD P := by
  have := epsQ_nonneg nD P
  unfold kapR
  positivity

section ports

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (get : Finset S × M' → Selections)
  (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')

/-- **The charge of a sponge call**: `0` at `h`, `kapS tr σ` at `k`, `k'`. -/
noncomputable def cSq (nD P : ℕ) : ∀ p : SpongePort,
    Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ → ℝ≥0∞
  | .h, _ => 0
  | .k, σ => ENNReal.ofReal (kapS nD P * σ.trace.re)
  | .k', σ => ENNReal.ofReal (kapS nD P * σ.trace.re)

/-- **The charge of a read call** other than a trial read: the `k`, `k'` reads'
`potCap (ε + 2/|X| + 2/|Z| + 2 √ε) tr σ`. -/
noncomputable def cRq (nD P : ℕ) (_c : HwRead X Z (Finset S × M'))
    (σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ) :
    ℝ≥0∞ :=
  (potCap nD P : ℝ≥0∞) * ENNReal.ofReal
    ((epsQ nD P + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ nD P)) * σ.trace.re)

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem encPotN_le_potCap (d : EvData) {nD P : ℕ} {s : HwReg X Z (Finset S × M')}
    (hW : dbGrade s.2.1 ≤ nW P) (hD : dbGrade s.1 ≤ nD + 1) :
    encPotN get d s ≤ potCap nD P :=
  (encPotN_le get d s).trans (by unfold potCap; omega)

/-- **`hS` at the calls**: the `h` port raises the potential by its trace, the `k`, `k'` ports
by their trace plus `kapS` per unit of trace (two-sided fresh bounds of the level sets). -/
theorem hS_port (Ok : HwRead X Z (Finset S × M') → Prop) (d : EvData) (hπ : PermGood d.perm 18)
    {nD P : ℕ} (m₀ : Finset S × M') (p : SpongePort)
    {σ : Matrix (spongeIn X Z p × HwReg X Z (Finset S × M'))
      (spongeIn X Z p × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv Ok nD P m₀ (.inl (.inl (.inl p))) σ) :
    ∑' _r : Unit, potential (diagPot fun s ↦ √(encPot get d s))
        (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U p) σ) ≤
      potential (diagPot fun s ↦ √(encPot get d s)) σ +
        (ENNReal.ofReal σ.trace.re + cSq nD P p σ) := by
  have hsupp : QuerySupportedOn (fun m : spongeIn X Z p × HwReg X Z (Finset S × M') ↦ m.2)
      {s | dbGrade s.1 ≤ nD ∧ dbGrade s.2.1 ≤ nW P} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hF : ∀ s : HwReg X Z (Finset S × M'), dbGrade s.2.1 ≤ nW P → dbGrade s.1 ≤ nD + 1 →
      encPotN get d s ≤ potCap nD P := fun s hW hD ↦ encPotN_le_potCap get d hW hD
  have hk : ∀ (i : SpongePort), (∀ (m : ℕ) (W : Hw X Z) (mm : Finset S × M'),
      PortInst (slice (levSet (encPotN get d) (nW P) m) W mm) i (nD + 1)
        (ENNReal.ofReal (epsQ nD P))) →
      ∀ {τ : Matrix (spongeIn X Z i × HwReg X Z (Finset S × M'))
        (spongeIn X Z i × HwReg X Z (Finset S × M')) ℂ},
      τ.PosSemidef → QuerySupportedOn (fun m : spongeIn X Z i × HwReg X Z (Finset S × M') ↦ m.2)
        {s | dbGrade s.1 ≤ nD ∧ dbGrade s.2.1 ≤ nW P} τ →
      ∑' _r : Unit, potential (diagPot fun s ↦ √(encPot get d s))
          (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m₀).U i) τ) ≤
        potential (diagPot fun s ↦ √(encPot get d s)) τ +
          (ENNReal.ofReal τ.trace.re + ENNReal.ofReal (kapS nD P * τ.trace.re)) := by
    intro i hε τ hτ hs
    rw [sqrt_encPot_eq]
    refine (tsum_potential_sponge_layer_le (encPotN get d) (nW P) nD (potCap nD P) hF
      (epsQ_nonneg nD P) (hwEmpty X Z) m₀ i hε hτ hs).trans (add_le_add le_rfl (le_add_left
        (le_of_eq (congrArg ENNReal.ofReal ?_))))
    unfold kapS
    ring
  cases p with
  | h =>
    refine (tsum_potential_spongeH_le (encPot_nonneg get d) (encPot_update_h_le get d)
      (hwEmpty X Z) m₀ hσ).trans (add_le_add le_rfl ?_)
    rw [cSq, add_zero]
  | k => exact hk .k (fun m W mm ↦ portInst_levSet_k get d hπ (nW P) nD m W mm) hσ hsupp
  | k' => exact hk .k' (fun m W mm ↦ portInst_levSet_k' get d hπ (nW P) nD m W mm) hσ hsupp

/-- **`hR` at the calls**: the reads other than the trial reads are `k`, `k'` reads keeping the
memory (`EncReadOk`); each raises the potential by at most `cRq` (two-sided fresh bounds of the
level sets through `keepE`, the recorded cells `2/|Y|`, the flip-recorded mass at most `tr σ`). -/
theorem hR_port (d : EvData) (hπ : PermGood d.perm 18) {nD P : ℕ} (m₀ : Finset S × M')
    (c : HwRead X Z (Finset S × M'))
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (ht : ¬ IsTrial updOf c) (hσ : σ.PosSemidef)
    (hI : PortInv (EncReadOk updOf) nD P m₀ (.inl (.inl (.inr c))) σ) :
    ∑' r, potential (diagPot fun s ↦ √(encPot get d s))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(encPot get d s)) σ + cRq nD P c σ := by
  have hok : EncReadOk updOf c := hI.1
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hsupp : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ m.2)
      {s | dbGrade s.1 ≤ nD ∧ dbGrade s.2.1 ≤ nW P} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hg : QuerySupportedOn (fun m : Unit × HwReg X Z (Finset S × M') ↦ dbGrade m.2.1)
      (Set.Iic nD) σ :=
    hI.2.1.imp fun _ h ↦ Set.mem_Iic.mpr h.1
  have hcost : ∀ m, (∀ W mm, PortInst (slice (levSet (encPotN get d) (nW P) m) W mm)
      (readPort c) (nD + 1) (ENNReal.ofReal (epsQ nD P))) → KeepUpd c →
      readCost (levSet (encPotN get d) (nW P) m) c σ ≤ ENNReal.ofReal
        ((epsQ nD P + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ nD P)) *
          σ.trace.re) :=
    fun m hε hk ↦ readCost_le_of_keep _ c hk hσ (epsQ_nonneg nD P)
      ((keepE_le_of_portInst _ ENNReal.ofReal_ne_top c hε hσ hg).trans_eq
        (by rw [ENNReal.toReal_ofReal (epsQ_nonneg nD P)]))
  rw [sqrt_encPot_eq]
  refine tsum_potential_read_layer_le (encPotN get d) (nW P) nD (potCap nD P)
    (fun s hW hD ↦ encPotN_le_potCap get d hW hD) c hσ hnb (fun m ↦ ?_) hsupp
  cases c with
  | readH z upd => exact absurd hok ht
  | readK x upd =>
    exact hcost m (fun W mm ↦ portInst_levSet_k get d hπ (nW P) nD m W mm) hok
  | readK' x upd =>
    exact hcost m (fun W mm ↦ portInst_levSet_k' get d hπ (nW P) nD m W mm) hok

omit [Fintype S] [Fintype M'] in
theorem dbGrade_progMap_le (c : HwProg X Z) (s : HwReg X Z (Finset S × M')) :
    dbGrade (progMap c s).1 ≤ dbGrade s.1 + 1 ∧ dbGrade (progMap c s).2.1 ≤ dbGrade s.2.1 + 1 := by
  have hK : hwProgKraus c (progIdx c s) ((), progMap c s) ((), s) ≠ 0 := by
    rw [hwProgKraus_apply c (progIdx c s) ((), progMap c s) ((), s), ite_eq_left ⟨rfl, rfl⟩]
    exact one_ne_zero
  exact ⟨dbGrade_le_of_hwProgKraus_ne_zero c _ () () s _ hK,
    dbGrade_hw_le_of_hwProgKraus_ne_zero c _ () () s _ hK⟩

/-- **The program jump at the calls**: at most `potCap` times the weight of the jump states
(`KJump`). -/
theorem progJump_le_port (Ok : HwRead X Z (Finset S × M') → Prop) (d : EvData) {nD P : ℕ}
    (m₀ : Finset S × M') (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv Ok nD P m₀ (.inl (.inr c)) σ) :
    progJump (encPot get d) c σ ≤ (potCap nD P : ℝ≥0∞) * kJumpW d c σ := by
  refine (progJump_le (encPot_nonneg get d) c (KJump d c)
    (fun s hs ↦ encPot_progMap_le get d c s hs) hσ (H := potCap nD P)
      fun a ha ↦ ?_).trans_eq ?_
  · have hs := (hI.2.1 a a ha).1
    obtain ⟨h1, h2⟩ := dbGrade_progMap_le c a.2
    rw [encPot_eq_encPotN]
    exact_mod_cast encPotN_le_potCap get d (h2.trans (Nat.add_le_add_right hs.2 1))
      (h1.trans (Nat.add_le_add_right hs.1 1))
  · rw [kJumpW, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
theorem encOff_le_grade (d : EvData) (z : Z) (K : Key) (s : HwReg X Z (Finset S × M')) :
    encOff d z K s ≤ dbGrade s.2.1 + dbGrade s.1 := by
  unfold encOff
  split_ifs
  · have h1 := tailOutCount_eq_off_add d.perm (union s.2.1 s.1) trunc128 (EncAt d K)
      Codeword.Valid z
    have h2 := (tailOutCount_le_tailCount d.perm (union s.2.1 s.1) trunc128 (EncAt d K)
      Codeword.Valid).trans ((tailCount_le_size d.perm (union s.2.1 s.1) (EncAt d K)).trans
        (size_unionH_le s.2.1 s.1))
    exact_mod_cast (Nat.le_add_right _ _).trans (h1 ▸ h2)
  · positivity

/-- **The trial charge at the calls**: `(3 C + 3) massW + (2/|X| + 4/|X|²) tr σ` with
`C = nW P + nD` (`trialChg_le_massW`, the count bounded by the grades). -/
theorem trialChg_le_port (Ok : HwRead X Z (Finset S × M') → Prop) (d : EvData) {nD P : ℕ}
    (m₀ : Finset S × M') (c : HwRead X Z (Finset S × M'))
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv Ok nD P m₀ (.inl (.inl (.inr c))) σ) :
    trialChg get updOf d c σ ≤
      ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ) + 3) * massW get updOf d c σ +
        ENNReal.ofReal ((2 / (Fintype.card X : ℝ) + (2 / (Fintype.card X : ℝ)) ^ 2) *
          σ.trace.re) := by
  by_cases ht : IsTrial updOf c
  · refine trialChg_le_massW get updOf d ht (Nat.cast_nonneg _) hσ fun a ↦ ?_
    by_cases h0 : σ a a = 0
    · exact .inr h0
    · have hs := (hI.2.1 a a h0).1
      refine .inl ((encOff_le_grade d _ _ a.2).trans ?_)
      have : dbGrade a.2.2.1 + dbGrade a.2.1 ≤ nW P + nD := by
        have h1 : dbGrade a.2.1 ≤ nD := hs.1
        have h2 : dbGrade a.2.2.1 ≤ P := hs.2
        unfold nW
        omega
      exact_mod_cast this
  · simp only [trialChg, ht, ↓reduceIte, zero_le]

/-- **The charge of a read call**: the trial charge and `cRq` together are at most
`(3C + 3) massW + kapR tr σ`. -/
theorem readCharge_le (Ok : HwRead X Z (Finset S × M') → Prop) (d : EvData) {nD P : ℕ}
    (m₀ : Finset S × M') (c : HwRead X Z (Finset S × M'))
    {σ : Matrix (Unit × HwReg X Z (Finset S × M')) (Unit × HwReg X Z (Finset S × M')) ℂ}
    (hσ : σ.PosSemidef) (hI : PortInv Ok nD P m₀ (.inl (.inl (.inr c))) σ) :
    trialChg get updOf d c σ + cRq nD P c σ ≤
      ENNReal.ofReal (3 * ((nW P + nD : ℕ) : ℝ) + 3) * massW get updOf d c σ +
        ENNReal.ofReal (kapR nD P) * ENNReal.ofReal σ.trace.re := by
  have htr : 0 ≤ σ.trace.re := (Complex.nonneg_iff.1 hσ.trace_nonneg).1
  have he := epsQ_nonneg nD P
  refine (add_le_add (trialChg_le_port get updOf Ok d m₀ c hσ hI) le_rfl).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  unfold cRq
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) htr)
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity) htr)),
    ← ENNReal.ofReal_mul (kapR_nonneg nD P)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold kapR
  ring

end ports

/-! ## The joint count along a run -/

section joint

variable {S : Type} [Fintype S] [DecidableEq S] {M' : Type} [Fintype M'] [DecidableEq M']
  (get : Finset S × M' → Selections)
  (updOf : TrialPt → Finset S × M' → Option X → Finset S × M')
  {Λ : LocalSig.{u, v}} {Ω : QReg → Type w}

/-- **The trace-weighted classical calls of a run**: with at most `K` classical calls (reads,
programs, records) on every path, the traces of the inputs of the read and program calls add up
to at most `K`. -/
theorem totalWeight_calls_le_basis (m₀ : Finset S × M') (I : Λ.Interp) {B : Type} [Fintype B]
    [DecidableEq B] (u : B) (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B))
    {K : ℕ} (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) K) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost
      (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ σ ↦ ENNReal.ofReal σ.trace.re)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤ K := by
  have hρ : ((SubState.basis u).matrix ⊗ₖ
      (runtimeR (X := X) (Z := Z) m₀).init.matrix).PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  refine (totalWeight_le_totalWeight (runtimeR m₀) I
    (w' := fun i σ ↦ ((if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0 : ℕ) :
      ℝ≥0∞) * ENNReal.ofReal σ.trace.re) (fun i σ _ ↦ ?_) x hρ).trans ?_
  · rcases i with ((p | c) | c) | T <;> simp [extWeight, sumWeight, hwCost, extCls, hwCls]
    all_goals exact le_of_eq rfl
  · exact (totalWeight_chargeTrace_le (runtimeR m₀) I _ x hK hρ).trans
      ((mul_le_mul_of_nonneg_left (ofReal_trace_basis_init m₀ u).le zero_le).trans_eq
        (mul_one _))

/-- **The joint count of the selecting reads along a run** (the restated `encJoint`): for a run
from a basis state beside the initial register with at most `n` sponge, `K` classical and `P`
program calls, only `EncReadOk` reads (`okChg` of budget `0`) and trial updates recording
codeword selections, at data with `PermGood π 18`, the joint count `cntGW` is at most
`2^15 (n + P)` plus `2^15` times the charges along the run: `(3C + 3)` per unit of recorded mass
(`massW`, with `C = nW P + nD` the count bound on the support, `nD = n + K`), `kapS` per sponge
call, `kapR` per classical call and `potCap` per unit of weight of the program jump states
(`kJumpW`). -/
theorem totalWeight_cntGW_le_calls (hu : CwTrialUpd get updOf)
    (hlab : ∀ (T T' : Finset S) (m : M'), get (T, m) = get (T', m)) (d : EvData)
    (hπ : PermGood d.perm 18) (m₀ : Finset S × M') (I : Λ.Interp) {B : Type} [Fintype B]
    [DecidableEq B] (u : B) (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B)) {n K P : ℕ}
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) K)
    (hok : IFreeM.IsChargeBound x (portCharge (okChg (EncReadOk updOf))) 0)
    (hP : IFreeM.IsChargeBound x
      (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M'))) P) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost (cntGW get updOf d) fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      2 ^ 15 * ((n + P : ℕ) : ℝ≥0∞) + 2 ^ 15 *
        (ENNReal.ofReal (3 * ((nW P + (n + K) : ℕ) : ℝ) + 3) *
            (runtimeR m₀).totalWeight I
              (extWeight (hwCost (massW get updOf d) fun _ _ ↦ 0)) x
              ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
          (n : ℝ≥0∞) * ENNReal.ofReal (kapS (n + K) P) +
          (K : ℝ≥0∞) * ENNReal.ofReal (kapR (n + K) P) +
          (potCap (n + K) P : ℝ≥0∞) * (runtimeR m₀).totalWeight I
            (extWeight (hwCost (fun _ _ ↦ 0) (kJumpW d))) x
            ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) := by
  set ρ := (SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix
  have hρ : ρ.PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  obtain ⟨Q, hQ, hx⟩ := forallQueries_portInv (EncReadOk updOf) m₀ I u x hn hK hok hP
  have h := totalWeight_cntGW_le get updOf hu hlab d m₀ Q
    (PortInv (EncReadOk updOf) (n + K) P m₀) hQ (cSq (n + K) P) (cRq (n + K) P)
    (progJump (encPot get d))
    (fun p _ hσ hI ↦ hS_port get (EncReadOk updOf) d hπ m₀ p hσ hI)
    (fun c _ ht hσ hI ↦ hR_port get updOf d hπ m₀ c ht hσ hI)
    (fun c _ _ hI ↦ readNoBot_of_noBot c hI.2.2)
    (fun c _ hσ _ ↦ tsum_potential_prog_le (encPot_nonneg get d) c hσ)
    I u x hn hP hx
  refine h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le))
  set C : ℝ := ((nW P + (n + K) : ℕ) : ℝ)
  set wM : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (massW get updOf d) fun _ _ ↦ 0)
  set wR : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0)
  set wJ : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (kJumpW d))
  set wS : ∀ i : (recHwSpec X Z S M').Port,
      Matrix ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D)
        ((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) ℂ → ℝ≥0∞ :=
    fun i σ ↦ ((if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re
  have hle := totalWeight_le_of_forallQueries (runtimeR m₀) I
    (PortInv (EncReadOk updOf) (n + K) P m₀) hQ
    (w := portCh X Z S M' (cSq (n + K) P)
      (fun c σ ↦ trialChg get updOf d c σ + cRq (n + K) P c σ)
      (progJump (encPot get d)))
    (w' := fun i σ ↦ (ENNReal.ofReal (3 * C + 3) * wM i σ +
        ENNReal.ofReal (kapS (n + K) P) * wS i σ) +
      (ENNReal.ofReal (kapR (n + K) P) * wR i σ + (potCap (n + K) P : ℝ≥0∞) * wJ i σ))
    (fun i σ hσ hI ↦ ?_) x hρ hx
  · have e := (totalWeight_add_weight (runtimeR m₀) I
      (fun i σ ↦ ENNReal.ofReal (3 * C + 3) * wM i σ + ENNReal.ofReal (kapS (n + K) P) * wS i σ)
      (fun i σ ↦ ENNReal.ofReal (kapR (n + K) P) * wR i σ + (potCap (n + K) P : ℝ≥0∞) * wJ i σ)
      x ρ).trans (congrArg₂ (· + ·)
        ((totalWeight_add_weight (runtimeR m₀) I
          (fun i σ ↦ ENNReal.ofReal (3 * C + 3) * wM i σ)
          (fun i σ ↦ ENNReal.ofReal (kapS (n + K) P) * wS i σ) x ρ).trans
          (congrArg₂ (· + ·)
            (totalWeight_const_mul_weight (runtimeR m₀) I _ wM x ρ)
            (totalWeight_const_mul_weight (runtimeR m₀) I _ wS x ρ)))
        ((totalWeight_add_weight (runtimeR m₀) I
          (fun i σ ↦ ENNReal.ofReal (kapR (n + K) P) * wR i σ)
          (fun i σ ↦ (potCap (n + K) P : ℝ≥0∞) * wJ i σ) x ρ).trans
          (congrArg₂ (· + ·)
            (totalWeight_const_mul_weight (runtimeR m₀) I _ wR x ρ)
            (totalWeight_const_mul_weight (runtimeR m₀) I _ wJ x ρ))))
    have hS : (runtimeR m₀).totalWeight I wS x ρ ≤ (n : ℝ≥0∞) :=
      (totalWeight_chargeTrace_le (runtimeR m₀) I
        (fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) x hn hρ).trans
          ((mul_le_mul_of_nonneg_left (ofReal_trace_basis_init m₀ u).le zero_le).trans_eq
            (mul_one _))
    have hR : (runtimeR m₀).totalWeight I wR x ρ ≤ K :=
      (totalWeight_le_totalWeight (runtimeR m₀) I
        (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ _ ↦ by
            rcases i with ((p | c) | c) | T
            · exact le_rfl
            · exact le_rfl
            · exact zero_le
            · exact le_rfl) x hρ).trans
        (totalWeight_calls_le_basis m₀ I u x hK)
    refine hle.trans (e.trans_le ((add_le_add (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hS zero_le)) (add_le_add (mul_le_mul_of_nonneg_left hR zero_le)
        le_rfl)).trans_eq ?_))
    ring
  · rcases i with ((p | c) | c) | T
    · show cSq (n + K) P p σ ≤ (ENNReal.ofReal (3 * C + 3) * 0 +
          ENNReal.ofReal (kapS (n + K) P) * (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)) +
          (ENNReal.ofReal (kapR (n + K) P) * 0 + (potCap (n + K) P : ℝ≥0∞) * 0)
      rw [Nat.cast_one, one_mul]
      rw [mul_zero, mul_zero, mul_zero, zero_add, zero_add, add_zero,
        ← ENNReal.ofReal_mul (kapS_nonneg (n + K) P)]
      cases p with
      | h => exact zero_le
      | k => exact le_rfl
      | k' => exact le_rfl
    · show trialChg get updOf d c σ + cRq (n + K) P c σ ≤
        (ENNReal.ofReal (3 * C + 3) * massW get updOf d c σ +
          ENNReal.ofReal (kapS (n + K) P) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)) +
        (ENNReal.ofReal (kapR (n + K) P) * ENNReal.ofReal σ.trace.re +
          (potCap (n + K) P : ℝ≥0∞) * 0)
      rw [Nat.cast_zero, zero_mul]
      rw [mul_zero, mul_zero, add_zero, add_zero]
      exact readCharge_le get updOf (EncReadOk updOf) d m₀ c hσ hI
    · show progJump (encPot get d) c σ ≤
        (ENNReal.ofReal (3 * C + 3) * 0 +
          ENNReal.ofReal (kapS (n + K) P) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re)) +
        (ENNReal.ofReal (kapR (n + K) P) * 0 + (potCap (n + K) P : ℝ≥0∞) * kJumpW d c σ)
      rw [Nat.cast_zero, zero_mul, mul_zero, mul_zero, mul_zero, add_zero, zero_add, zero_add]
      exact progJump_le_port get (EncReadOk updOf) d m₀ c hσ hI
    · exact zero_le

/-- **The codeword flips of a run against the joint count** (`encW_le_cntGW` at the calls): if
every state off `B'` with at most `P` hardwired cells per function has a good union (for `B'`
Events' `Bad d N` with `P ≤ N`: `good_of_not_mem_bad`), the codeword flips are at most `2^-128`
times the joint count. -/
theorem totalWeight_encW_le (B' : Set (HwReg X Z (Finset S × M'))) [DecidablePred (· ∈ B')]
    (d : EvData) (m₀ : Finset S × M') (I : Λ.Interp) {B : Type} [Fintype B]
    [DecidableEq B] (u : B) (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B))
    {n K P : ℕ}
    (hG : ∀ s : HwReg X Z (Finset S × M'), dbGrade s.2.1 ≤ P → s ∉ B' →
      Good d.perm (union s.2.1 s.1))
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) K)
    (hok : IFreeM.IsChargeBound x (portCharge (okChg (EncReadOk updOf))) 0)
    (hP : IFreeM.IsChargeBound x
      (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M'))) P) :
    (runtimeR m₀).totalWeight I
        (extWeight (hwCost (encW get updOf B' d) fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      ENNReal.ofReal (2 ^ 128)⁻¹ * (runtimeR m₀).totalWeight I
        (extWeight (hwCost (cntGW get updOf d) fun _ _ ↦ 0)) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  have hρ : ((SubState.basis u).matrix ⊗ₖ
      (runtimeR (X := X) (Z := Z) m₀).init.matrix).PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  obtain ⟨Q, hQ, hx⟩ := forallQueries_portInv (EncReadOk updOf) m₀ I u x hn hK hok hP
  refine (totalWeight_le_of_forallQueries (runtimeR m₀) I
    (PortInv (EncReadOk updOf) (n + K) P m₀) hQ
    (w' := fun i σ ↦ ENNReal.ofReal (2 ^ 128)⁻¹ *
      extWeight (hwCost (cntGW get updOf d) fun _ _ ↦ 0) i σ)
    (fun i σ hσ hI ↦ ?_) x hρ hx).trans_eq
      (totalWeight_const_mul_weight (runtimeR m₀) I _ _ x _)
  rcases i with ((p | c) | c) | T
  · exact zero_le
  · exact encW_le_cntGW get updOf B' c hσ fun a h0 hB ↦ hG a.2 (hI.2.1 a a h0).1.2 hB
  · exact zero_le
  · exact zero_le

omit [Fintype S] [DecidableEq S] [Fintype M'] [DecidableEq M'] in
/-- The program ports of `runtimeR` program `k`, `k'` cells of `Wt` with their values
(`ProgOfK`); the other ports, and the `h` programs, are free. -/
def ProgPort (Wt : Hw X Z) : (recHwSpec X Z S M').Port → Prop
  | .inl (.inr c) => ProgOfK Wt c
  | _ => True

/-- **The jump weight of a run splits** into the target-free fresh flips and the `RecJ` weight
(`kJumpW_le`): if the calls of the run stay inside the `k`, `k'` cells of a hardwired table `Wt`
(the presented operator vanishes where the port is no `ProgPort Wt` or the hardwired `k`, `k'`
cells are not `Wt`'s), with `P + n + K ≤ T`. -/
theorem totalWeight_kJumpW_le (d : EvData) (m₀ : Finset S × M') (I : Λ.Interp) {B : Type}
    [Fintype B] [DecidableEq B] (u : B) (x : QuantumComp Λ (recHwSpec X Z S M') Ω (QReg.of B))
    {n K P T : ℕ} (hT : P + (n + K) ≤ T) (Wt : Hw X Z)
    (hn : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 0 else 1) n)
    (hK : IFreeM.IsChargeBound x
      (portCharge fun i ↦ if extCls X Z (Finset S × M') (recSpec S M') i then 1 else 0) K)
    (hok : IFreeM.IsChargeBound x (portCharge (okChg (EncReadOk updOf))) 0)
    (hP : IFreeM.IsChargeBound x
      (portCharge (extProgCharge X Z (Finset S × M') (recSpec S M'))) P)
    (W : ∀ (i : (recHwSpec X Z S M').Port) (E : QReg),
      Matrix (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E)
        (((recHwSpec X Z S M').In i × (runtimeR (X := X) (Z := Z) m₀).D) × E) ℂ → Prop)
    (hW : ∀ i E σ, W i E σ → ∀ a, ¬(ProgPort Wt i ∧ HwLeK a.1.2.2.1 Wt) → σ a a = 0)
    (hxW : (runtimeR m₀).ForallQueries I W x
      ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) :
    (runtimeR m₀).totalWeight I (extWeight (hwCost (fun _ _ ↦ 0) (kJumpW d))) x
        ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) ≤
      (runtimeR m₀).totalWeight I (extWeight (hwCost (fun _ _ ↦ 0) (kfW d.perm P T))) x
          ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        (runtimeR m₀).totalWeight I (extWeight (hwCost (fun _ _ ↦ 0) (recJW d))) x
          ((SubState.basis u).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
  have hρ : ((SubState.basis u).matrix ⊗ₖ
      (runtimeR (X := X) (Z := Z) m₀).init.matrix).PosSemidef :=
    ((SubState.basis u).prod (runtimeR (X := X) (Z := Z) m₀).init).posSemidef
  obtain ⟨Q, hQ, hx⟩ := forallQueries_portInv (EncReadOk updOf) m₀ I u x hn hK hok hP
  refine (totalWeight_le_of_forallQueries (runtimeR m₀) I
    (fun i τ ↦ PortInv (EncReadOk updOf) (n + K) P m₀ i τ ∧
      ∀ a, ¬(ProgPort Wt i ∧ HwLeK a.2.2.1 Wt) → τ a a = 0)
    (P := fun i E σ ↦ Q i E σ ∧ W i E σ)
    (fun i E σ h ↦ ⟨hQ i E σ h.1, fun a ha ↦
      traceRight_diag_eq_zero fun e ↦ hW i E σ h.2 (a, e) ha⟩)
    (w' := fun i σ ↦ extWeight (hwCost (fun _ _ ↦ 0) (kfW d.perm P T)) i σ +
      extWeight (hwCost (fun _ _ ↦ 0) (recJW d)) i σ)
    (fun i σ hσ hI ↦ ?_) x hρ (forallQueries_and hx hxW)).trans_eq
      (totalWeight_add_weight (runtimeR m₀) I _ _ x _)
  rcases i with ((p | c) | c) | T'
  · exact zero_le
  · exact zero_le
  · refine kJumpW_le (Wt := Wt) d c hσ fun a ha ↦ ?_
    have hk : ProgPort Wt (.inl (.inr c) : (recHwSpec X Z S M').Port) ∧ HwLeK a.2.2.1 Wt := by
      by_contra h
      exact ha (hI.2 a h)
    refine ⟨hk.1, hk.2, (hI.1.2.1 a a ha).1.2, ?_⟩
    have h1 : dbGrade a.2.1 ≤ n + K := (hI.1.2.1 a a ha).1.1
    omega
  · exact zero_le

end joint

end Quantum.Sphincs.Assembly

end
