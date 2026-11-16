module

public import Quantum.Xmss.Assembly.Security

@[expose] public section

/-!
# The `RecJ` weight of the challenge prefix

EncPorts' `recJPre` sums, along the challenge prefix, the weight of the `RecJ` states at its `k`,
`k'` program calls: the programmed cell is not hardwired, the union is not good, and the union
with the cell erased is good. This file bounds it per table and on average over the good tables.

* **A potential weighted by the remaining program calls** (`hwKs`, `recPotN`): `N` minus the
  hardwired `k`, `k'` cells on a union that is not good, `0` on a good union. A `RecJ` state
  programs a fresh hardwired cell on a bad union, so the potential drops by one there
  (`recPotN_progK_add_one_le`); otherwise a program raises it only on a target-free fresh flip
  (KeyLazy's `FlipK`, `FlipK'`), by at most `N` (`recPotN_progK_le`).
* **The level sets** (`portInst_recLev_k`, `portInst_recLev_k'`, `portInst_recLev_h`): a fresh
  `k`, `k'` value changes the potential only through `badAttachK`, `badCompleteOutK'` of a good
  union (`recPotN_updK_ne`, `recPotN_updK'_ne`); `h` cells never change it (goodness reads only
  `k`, `k'`).
* **The ports** (`hS_rec`, `hR_rec`, `recJW_add_prog_le`): EncPorts' layer cake gives the sponge
  charge `recS q = N (2 √(6ε) + 6ε)` and the `k`, `k'` read charge `recR q = N (ε + 2/|X| + 2/|Z|
  + 2 √ε)` per unit of trace, `ε = epsQ q`; the randomizer trials' `h` reads keep the potential
  (`tsum_potential_readH_le`); a program pays its `RecJ` weight out of the potential and is charged
  `N kfW`.
* **The prefix** (`recJPre_le`): on `PermGood π 18`, `recJPre ≤ 6q recS + clsCap recR + N kfPre`.
* **The average** (`uavg_kfPre_le`, `uavg_recJPre_le`, `uavg_recJPre_le_two_pow`): KeyLazy's key
  averaging on KeysReparam's `keyE` gives `kfPre ≤ progCap 2^-301 + progCap 2^-170` on average, so
  the averaged `RecJ` weight over `GoodL` is at most `recCap q ≤ 2^-35` for `q ≤ 2^64`.

The bound is linear in the per-call flip amplitude `2 √(6ε) ≈ 2^-149` (`ε ≤ 2^-302` at database
grade `2^68`), weighted by the remaining program calls `N = 2 progCap + 1 ≈ 2^43.2` and summed over
the `6q + clsCap ≈ 2^67.6` calls. A bound summing per-call square roots (an event bound at each
program call) would reach about `progCap 2^-168`.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Xmss.Assembly

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss Quantum.Xmss.Hybrid HashSig LeanXmss
  LeanXmss.RandomPermutationModel Common Common.SufCma

/-! ## The potential weighted by the remaining program calls -/

section recGen

variable {X Z M : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The hardwired `k`, `k'` cells of a register state. -/
def hwKs (s : HwReg X Z M) : ℕ :=
  Database.size s.2.1.2.1 + Database.size s.2.1.2.2

open scoped Classical in
/-- **The `RecJ` potential**: on a union that is not good, `N` minus the hardwired `k`, `k'`
cells; on a good union, `0`. -/
noncomputable def recPotN (π : Equiv.Perm (X × Z)) (N : ℕ) (s : HwReg X Z M) : ℕ :=
  if Good π (union s.2.1 s.1) then 0 else N - hwKs s

omit [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem recPotN_le (π : Equiv.Perm (X × Z)) (N : ℕ) (s : HwReg X Z M) : recPotN π N s ≤ N := by
  unfold recPotN
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.sub_le _ _

omit [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem recPotN_of_good (π : Equiv.Perm (X × Z)) (N : ℕ) {s : HwReg X Z M}
    (h : Good π (union s.2.1 s.1)) : recPotN π N s = 0 :=
  ite_eq_left h

omit [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem recPotN_of_not_good (π : Equiv.Perm (X × Z)) (N : ℕ) {s : HwReg X Z M}
    (h : ¬ Good π (union s.2.1 s.1)) : recPotN π N s = N - hwKs s :=
  ite_eq_right h

omit [DecidableEq X] [Fintype Z] [DecidableEq Z] in
open scoped Classical in
/-- The potential sees only the union's `k`, `k'` cells and the hardwired `k`, `k'` count. -/
theorem recPotN_congr (π : Equiv.Perm (X × Z)) (N : ℕ) {s s' : HwReg X Z M}
    (hk : (union s'.2.1 s'.1).k = (union s.2.1 s.1).k)
    (hk' : (union s'.2.1 s'.1).k' = (union s.2.1 s.1).k') (hw : hwKs s' = hwKs s) :
    recPotN π N s' = recPotN π N s := by
  unfold recPotN
  rw [hw]
  exact if_congr (good_congr hk hk') rfl rfl

omit [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- The potential does not see the `h` cells nor the memory. -/
theorem recPotN_of_eq (π : Equiv.Perm (X × Z)) (N : ℕ) {s s' : HwReg X Z M}
    (hD : s'.1.2 = s.1.2) (hW : s'.2.1.2 = s.2.1.2) : recPotN π N s' = recPotN π N s := by
  refine recPotN_congr π N ?_ ?_ ?_
  · show (fun x ↦ (s'.2.1.2.1 x).or (s'.1.2.1 x)) = fun x ↦ (s.2.1.2.1 x).or (s.1.2.1 x)
    rw [hD, hW]
  · show (fun x ↦ (s'.2.1.2.2 x).or (s'.1.2.2 x)) = fun x ↦ (s.2.1.2.2 x).or (s.1.2.2 x)
    rw [hD, hW]
  · show Database.size s'.2.1.2.1 + Database.size s'.2.1.2.2 =
      Database.size s.2.1.2.1 + Database.size s.2.1.2.2
    rw [hW]

/-- **The values of a fresh `k` cell changing the potential lie in `badAttachK`** of a good
union, the cell not hardwired. -/
theorem recPotN_updK_ne (π : Equiv.Perm (X × Z)) (N : ℕ) {s : HwReg X Z M} {x : X}
    (hx : s.1.2.1 x = none) {u : Z}
    (hne : recPotN π N ((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2), s.2) ≠
      recPotN π N s) :
    s.2.1.2.1 x = none ∧ Good π (union s.2.1 s.1) ∧ u ∈ badAttachK π (union s.2.1 s.1) x := by
  set s' : HwReg X Z M := ((s.1.1, Function.update s.1.2.1 x (some u), s.1.2.2), s.2) with hs'
  by_cases hW : s.2.1.2.1 x = none
  · have hUx : (union s.2.1 s.1).k x = none := union_k_none hW hx
    have hk := union_updK_of_none_with s.2.1 s.1 hW u
    have hk' := union_k'_of_k s.2.1 s.1 (Function.update s.1.2.1 x (some u))
    by_cases hG : Good π (union s.2.1 s.1)
    · refine ⟨hW, hG, ?_⟩
      by_contra hu
      exact hne ((recPotN_of_good π N (s := s')
        ((good_congr hk hk').2 (updateK_tails hG hUx hu).1)).trans
        (recPotN_of_good π N hG).symm)
    · exact absurd ((recPotN_of_not_good π N (s := s') fun h ↦
        hG (Good.mono (extends_update_k hUx) ((good_congr hk hk').1 h))).trans
        (recPotN_of_not_good π N hG).symm) hne
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hW
    exact absurd (recPotN_congr π N (s := s) (s' := s') (union_updK_of_some s.2.1 s.1 hb u)
      (union_k'_of_k s.2.1 s.1 _) rfl) hne

/-- **The values of a fresh `k'` cell changing the potential lie in `badCompleteOutK'`** of a
good union, the cell not hardwired. -/
theorem recPotN_updK'_ne (π : Equiv.Perm (X × Z)) (N : ℕ) {s : HwReg X Z M} {x : X}
    (hx : s.1.2.2 x = none) {u : Z}
    (hne : recPotN π N ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)), s.2) ≠
      recPotN π N s) :
    s.2.1.2.2 x = none ∧ Good π (union s.2.1 s.1) ∧
      u ∈ badCompleteOutK' π (union s.2.1 s.1) x := by
  set s' : HwReg X Z M := ((s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)), s.2) with hs'
  by_cases hW : s.2.1.2.2 x = none
  · have hUx : (union s.2.1 s.1).k' x = none := union_k'_none hW hx
    have hk := union_k_of_k' s.2.1 s.1 (Function.update s.1.2.2 x (some u))
    have hk' := union_updK'_of_none_with s.2.1 s.1 hW u
    have hc := good_congr (π := π)
      (U := union s.2.1 (s.1.1, s.1.2.1, Function.update s.1.2.2 x (some u)))
      (U' := { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' x (some u) })
      hk hk'
    by_cases hG : Good π (union s.2.1 s.1)
    · refine ⟨hW, hG, ?_⟩
      by_contra hu
      exact hne ((recPotN_of_good π N (s := s')
        (hc.2 (updateK'_tails hG hUx hu).1)).trans
        (recPotN_of_good π N hG).symm)
    · exact absurd ((recPotN_of_not_good π N (s := s') fun h ↦
        hG (Good.mono (extends_update_k' hUx) (hc.1 h))).trans
        (recPotN_of_not_good π N hG).symm) hne
  · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hW
    exact absurd (recPotN_congr π N (s := s) (s' := s') (union_k_of_k' s.2.1 s.1 _)
      (union_updK'_of_some s.2.1 s.1 hb u) rfl) hne

/-- **Two-sided fresh bounds of the level sets at `k`.** -/
theorem portInst_recLev_k (π : Equiv.Perm (X × Z)) {G : ℕ} (hπ : PermGood π G) (N Nw n m : ℕ)
    (W : Hw X Z) (mm : M) :
    PortInst (slice (levSet (recPotN π N) Nw m) W mm) .k (n + 1)
      (ENNReal.ofReal (((capKJ (Nw + n) G + capKJ' (Nw + n) G : ℕ) : ℝ) / Fintype.card Z)) :=
  portInst_k_of_card (levSet (recPotN π N) Nw m) W mm (n := n)
    (J := capKJ (Nw + n) G + capKJ' (Nw + n) G) fun s hD _ hx ↦
      (card_levFlip_k_le (recPotN π N) π hπ Nw m n s hD fun _ hne ↦
        recPotN_updK_ne π N hx hne).trans (Nat.le_add_right _ _)

/-- **Two-sided fresh bounds of the level sets at `k'`.** -/
theorem portInst_recLev_k' (π : Equiv.Perm (X × Z)) {G : ℕ} (hπ : PermGood π G) (N Nw n m : ℕ)
    (W : Hw X Z) (mm : M) :
    PortInst (slice (levSet (recPotN π N) Nw m) W mm) .k' (n + 1)
      (ENNReal.ofReal (((capKJ (Nw + n) G + capKJ' (Nw + n) G : ℕ) : ℝ) / Fintype.card Z)) :=
  portInst_k'_of_card (levSet (recPotN π N) Nw m) W mm (n := n)
    (J := capKJ (Nw + n) G + capKJ' (Nw + n) G) fun s hD _ hx ↦
      (card_levFlip_k'_le (recPotN π N) π hπ Nw m n s hD fun _ hne ↦
        recPotN_updK'_ne π N hx hne).trans (Nat.le_add_left _ _)

/-- **The level sets at `h`**: an `h` cell never changes the potential. -/
theorem portInst_recLev_h (π : Equiv.Perm (X × Z)) (N Nw m : ℕ) (W : Hw X Z) (mm : M) (n : ℕ)
    (ε : ℝ≥0∞) : PortInst (slice (levSet (recPotN π N) Nw m) W mm) .h n ε := by
  intro D _ _ _ z _
  have he : ∀ u : X, (({ D with h := Function.update D.h z (some u) } : Dbs X Z) ∈
      slice (levSet (recPotN π N) Nw m) W mm ↔ D ∈ slice (levSet (recPotN π N) Nw m) W mm) :=
    fun u ↦ by
      show (dbGrade W ≤ Nw ∧
          m < recPotN π N ((Function.update D.h z (some u), D.k, D.k'), W, mm)) ↔
        (dbGrade W ≤ Nw ∧ m < recPotN π N ((D.h, D.k, D.k'), W, mm))
      rw [recPotN_of_eq π N (s := ((D.h, D.k, D.k'), W, mm))
        (s' := ((Function.update D.h z (some u), D.k, D.k'), W, mm)) rfl rfl]
  rw [Finset.filter_false_of_mem fun u _ ↦ not_not.mpr (he u), Finset.card_empty, Nat.cast_zero,
    ENNReal.zero_div]
  exact zero_le

omit [Fintype Z] [AddCommGroup Z] in
/-- Programming a fresh `k` cell adds one hardwired cell. -/
theorem hwKs_progK_none {s : HwReg X Z M} {y : X} (hW : s.2.1.2.1 y = none) (a : Z) :
    hwKs (progMap (.programK y a) s) = hwKs s + 1 := by
  show Database.size (Function.update s.2.1.2.1 y (some a)) + Database.size s.2.1.2.2 =
    Database.size s.2.1.2.1 + Database.size s.2.1.2.2 + 1
  rw [Database.size_update_some_of_eq_none hW]
  omega

omit [Fintype Z] [AddCommGroup Z] in
/-- Programming a fresh `k'` cell adds one hardwired cell. -/
theorem hwKs_progK'_none {s : HwReg X Z M} {y : X} (hW : s.2.1.2.2 y = none) (a : Z) :
    hwKs (progMap (.programK' y a) s) = hwKs s + 1 := by
  show Database.size s.2.1.2.1 + Database.size (Function.update s.2.1.2.2 y (some a)) =
    Database.size s.2.1.2.1 + Database.size s.2.1.2.2 + 1
  rw [Database.size_update_some_of_eq_none hW]
  omega

open scoped Classical in
/-- **A `k` program raises the potential only on a fresh flip**, by at most `N`, if a hardwired
cell already holds the programmed value. -/
theorem recPotN_progK_le (π : Equiv.Perm (X × Z)) (N : ℕ) (y : X) (a : Z) (s : HwReg X Z M)
    (hW : s.2.1.2.1 y ≠ none → s.2.1.2.1 y = some a) :
    recPotN π N (progMap (.programK y a) s) ≤
      recPotN π N s + if FlipK π s.2.1 s.1 y a then N else 0 := by
  by_cases hWn : s.2.1.2.1 y = none
  · by_cases hG' : Good π (union (progMap (.programK y a) s).2.1 (progMap (.programK y a) s).1)
    · rw [recPotN_of_good π N hG']
      exact Nat.zero_le _
    · rw [recPotN_of_not_good π N hG', hwKs_progK_none hWn]
      by_cases hG : Good π (union s.2.1 s.1)
      · have hG₀ : Good π
            { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } :=
          Good.mono (extendsAll_eraseK (union s.2.1 s.1) y).1 hG
        have ha : a ∈ badAttachK π
            { union s.2.1 s.1 with k := Function.update (union s.2.1 s.1).k y none } y := by
          by_contra ha
          refine hG' ?_
          rw [union_progMapK y a s]
          exact (updateK_tails hG₀ (eraseK_k_self (union s.2.1 s.1) y) ha).1
        rw [ite_eq_left (show FlipK π s.2.1 s.1 y a from ⟨hWn, hG₀, ha⟩)]
        exact (Nat.sub_le _ _).trans (Nat.le_add_left _ _)
      · rw [recPotN_of_not_good π N hG]
        exact (Nat.sub_le_sub_left (Nat.le_succ _) N).trans (Nat.le_add_right _ _)
  · have he : recPotN π N (progMap (.programK y a) s) = recPotN π N s := by
      refine recPotN_congr π N ?_ ?_ ?_
      · rw [union_progMapK y a s]
        exact reprogK_k (union_k_some (D := s.1) (hW hWn))
      · rfl
      · show Database.size (Function.update s.2.1.2.1 y (some a)) + Database.size s.2.1.2.2 =
          Database.size s.2.1.2.1 + Database.size s.2.1.2.2
        rw [Function.update_eq_self_iff.mpr (hW hWn).symm]
    rw [he]
    exact Nat.le_add_right _ _

open scoped Classical in
/-- **A `k'` program raises the potential only on a fresh flip**, by at most `N`. -/
theorem recPotN_progK'_le (π : Equiv.Perm (X × Z)) (N : ℕ) (y : X) (a : Z) (s : HwReg X Z M)
    (hW : s.2.1.2.2 y ≠ none → s.2.1.2.2 y = some a) :
    recPotN π N (progMap (.programK' y a) s) ≤
      recPotN π N s + if FlipK' π s.2.1 s.1 y a then N else 0 := by
  by_cases hWn : s.2.1.2.2 y = none
  · by_cases hG' : Good π (union (progMap (.programK' y a) s).2.1 (progMap (.programK' y a) s).1)
    · rw [recPotN_of_good π N hG']
      exact Nat.zero_le _
    · rw [recPotN_of_not_good π N hG', hwKs_progK'_none hWn]
      by_cases hG : Good π (union s.2.1 s.1)
      · have hG₀ : Good π
            { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } :=
          Good.mono (extendsAll_eraseK' (union s.2.1 s.1) y).1 hG
        have ha : a ∈ badCompleteOutK' π
            { union s.2.1 s.1 with k' := Function.update (union s.2.1 s.1).k' y none } y := by
          by_contra ha
          refine hG' ?_
          rw [union_progMapK' y a s]
          exact (updateK'_tails hG₀ (eraseK'_k'_self (union s.2.1 s.1) y) ha).1
        rw [ite_eq_left (show FlipK' π s.2.1 s.1 y a from ⟨hWn, hG₀, ha⟩)]
        exact (Nat.sub_le _ _).trans (Nat.le_add_left _ _)
      · rw [recPotN_of_not_good π N hG]
        exact (Nat.sub_le_sub_left (Nat.le_succ _) N).trans (Nat.le_add_right _ _)
  · have he : recPotN π N (progMap (.programK' y a) s) = recPotN π N s := by
      refine recPotN_congr π N ?_ ?_ ?_
      · rfl
      · rw [union_progMapK' y a s]
        exact reprogK'_k' (union_k'_some (D := s.1) (hW hWn))
      · show Database.size s.2.1.2.1 + Database.size (Function.update s.2.1.2.2 y (some a)) =
          Database.size s.2.1.2.1 + Database.size s.2.1.2.2
        rw [Function.update_eq_self_iff.mpr (hW hWn).symm]
    rw [he]
    exact Nat.le_add_right _ _

omit [Fintype Z] in
/-- **A `k` program of a fresh cell on a bad union lowers the potential by one** (the `RecJ`
states). -/
theorem recPotN_progK_add_one_le (π : Equiv.Perm (X × Z)) (N : ℕ) (y : X) (a : Z)
    {s : HwReg X Z M} (hks : hwKs s < N) (hWn : s.2.1.2.1 y = none)
    (hG : ¬ Good π (union s.2.1 s.1)) :
    recPotN π N (progMap (.programK y a) s) + 1 ≤ recPotN π N s := by
  rw [recPotN_of_not_good π N hG]
  have h : recPotN π N (progMap (.programK y a) s) ≤ N - (hwKs s + 1) := by
    unfold recPotN
    split_ifs
    · exact Nat.zero_le _
    · rw [hwKs_progK_none hWn]
  omega

omit [Fintype Z] in
/-- **A `k'` program of a fresh cell on a bad union lowers the potential by one.** -/
theorem recPotN_progK'_add_one_le (π : Equiv.Perm (X × Z)) (N : ℕ) (y : X) (a : Z)
    {s : HwReg X Z M} (hks : hwKs s < N) (hWn : s.2.1.2.2 y = none)
    (hG : ¬ Good π (union s.2.1 s.1)) :
    recPotN π N (progMap (.programK' y a) s) + 1 ≤ recPotN π N s := by
  rw [recPotN_of_not_good π N hG]
  have h : recPotN π N (progMap (.programK' y a) s) ≤ N - (hwKs s + 1) := by
    unfold recPotN
    split_ifs
    · exact Nat.zero_le _
    · rw [hwKs_progK'_none hWn]
  omega

omit [Fintype Z] in
/-- An `h` program keeps the potential. -/
theorem recPotN_progH (π : Equiv.Perm (X × Z)) (N : ℕ) (z : Z) (v : X) (s : HwReg X Z M) :
    recPotN π N (progMap (.programH z v) s) = recPotN π N s :=
  recPotN_of_eq π N rfl rfl

omit [DecidableEq X] [Fintype Z] [DecidableEq Z] in
/-- The potential does not see an `h` cell nor the memory. -/
theorem recPotN_offCell [Fintype M] [DecidableEq M] (π : Equiv.Perm (X × Z)) (N : ℕ) (z : Z) :
    OffCell z (fun s : HwReg X Z M ↦ (recPotN π N s : ℝ)) :=
  fun _ _ _ hD hW ↦ congrArg _ (recPotN_of_eq π N hD (congrArg Prod.snd hW))

/-- **A read of an `h` cell keeps a potential that sees neither the cell nor the memory.** -/
theorem tsum_potential_readH_le [AddCommGroup X] [Fintype M] [DecidableEq M] {φ : HwReg X Z M → ℝ}
    (hφ0 : ∀ s, 0 ≤ φ s) {z : Z} (hφ : OffCell z φ) (upd : M → Option X → M)
    {σ : Matrix (Unit × HwReg X Z M) (Unit × HwReg X Z M) ℂ} (hσ : σ.PosSemidef) :
    ∑' r, potential (diagPot fun s ↦ √(φ s)) (MatrixMap.conj (hwReadKraus (.readH z upd) r) σ) ≤
      potential (diagPot fun s ↦ √(φ s)) σ := by
  set K := diagPot fun s : HwReg X Z M ↦ √(φ s)
  have hΦ : (1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K) =
      diagonal fun q : Unit × HwReg X Z M ↦ (φ q.2 : ℂ) := by
    rw [diagPot_sqrt_gram hφ0, one_kronecker_diagPot]
  have hcomm : ∀ r, (1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K) * hwReadKraus (.readH z upd) r =
      hwReadKraus (.readH z upd) r * ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) := fun r ↦ by
    rw [hΦ]
    refine diagonal_mul_comm_of _ _ fun a a' h ↦ ?_
    obtain ⟨-, h'⟩ := one_kronecker_ne_zero (a := a.1) (a' := a'.1) (b := a.2) (b' := a'.2) h
    obtain ⟨h₁, h₂, h₃⟩ := readKrausH_ne_zero_rest z upd r h'
    rw [hφ a.2 a'.2 h₁ h₂ h₃]
  have hsum : ∑ r, (hwReadKraus (.readH z upd) r)ᴴ * ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) *
      hwReadKraus (.readH z upd) r = (1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K) := by
    rw [Finset.sum_congr rfl fun r _ ↦ show (hwReadKraus (.readH z upd) r)ᴴ *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) * hwReadKraus (.readH z upd) r =
        (hwReadKraus (.readH z upd) r)ᴴ * hwReadKraus (.readH z upd) r *
          ((1 : Matrix Unit Unit ℂ) ⊗ₖ (Kᴴ * K)) by
      rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc], ← Finset.sum_mul, sum_hwReadKraus,
      Matrix.one_mul]
  have hd := drop_of_posSemidef (hwReadKraus (.readH z upd)) K K 0 hσ (by
    rw [add_zero, hsum, sub_self]
    exact PosSemidef.zero)
  rw [Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re, ENNReal.ofReal_zero, add_zero,
    add_zero] at hd
  exact le_add_self.trans hd

end recGen

/-! ## A diagonal inequality -/

open scoped Classical in
/-- **Paying an indicator out of a diagonal potential**: if on the support an `R` state lowers the
potential by one, a state outside `S` does not raise it, and every state raises it by at most `N`,
then the `R` weight plus the potential after is at most the potential before plus `N` times the
weight of `S`. -/
theorem ofReal_ind_add_le {n : Type} [Fintype n] (d : n → ℝ) (hd : ∀ q, 0 ≤ d q)
    (R : n → Prop) [DecidablePred R] (S : Set n) (f f' : n → ℝ) (hf : ∀ q, 0 ≤ f q)
    (hf' : ∀ q, 0 ≤ f' q) (N : ℕ)
    (h1 : ∀ q, d q ≠ 0 → R q → f' q + 1 ≤ f q) (h2 : ∀ q, d q ≠ 0 → q ∉ S → f' q ≤ f q)
    (h3 : ∀ q, d q ≠ 0 → f' q ≤ f q + N) :
    ENNReal.ofReal (∑ q, (if R q then (1 : ℝ) else 0) * d q) + ENNReal.ofReal (∑ q, f' q * d q) ≤
      ENNReal.ofReal (∑ q, f q * d q) +
        (N : ℝ≥0∞) * ∑ q, S.indicator (fun q ↦ ENNReal.ofReal (d q)) q := by
  have hS : ENNReal.ofReal (∑ q, (if q ∈ S then (N : ℝ) else 0) * d q) ≤
      (N : ℝ≥0∞) * ∑ q, S.indicator (fun q ↦ ENNReal.ofReal (d q)) q := by
    rw [ENNReal.ofReal_sum_of_nonneg fun q _ ↦
      mul_nonneg (by split_ifs <;> positivity) (hd q), Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    by_cases hq : q ∈ S
    · rw [ite_eq_left hq, Set.indicator_of_mem hq, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    · rw [ite_eq_right hq, zero_mul, ENNReal.ofReal_zero]
      exact zero_le
  have hA : 0 ≤ ∑ q, (if R q then (1 : ℝ) else 0) * d q :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> positivity) (hd q)
  have hB : 0 ≤ ∑ q, f' q * d q := Finset.sum_nonneg fun q _ ↦ mul_nonneg (hf' q) (hd q)
  have hC : 0 ≤ ∑ q, f q * d q := Finset.sum_nonneg fun q _ ↦ mul_nonneg (hf q) (hd q)
  have hD : 0 ≤ ∑ q, (if q ∈ S then (N : ℝ) else 0) * d q :=
    Finset.sum_nonneg fun q _ ↦ mul_nonneg (by split_ifs <;> positivity) (hd q)
  rw [← ENNReal.ofReal_add hA hB]
  refine (ENNReal.ofReal_le_ofReal ?_).trans ((ENNReal.ofReal_add hC hD).trans_le
    (add_le_add le_rfl hS))
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  by_cases h0 : d q = 0
  · rw [h0]
    simp
  · have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    by_cases hR : R q
    · have := h1 q h0 hR
      rw [ite_eq_left hR]
      have hSq : 0 ≤ (if q ∈ S then (N : ℝ) else 0) := by split_ifs <;> positivity
      nlinarith [hd q]
    · rw [ite_eq_right hR, zero_mul, zero_add]
      by_cases hq : q ∈ S
      · rw [ite_eq_left hq, ← add_mul]
        exact mul_le_mul_of_nonneg_right (h3 q h0) (hd q)
      · rw [ite_eq_right hq, zero_mul, add_zero]
        exact mul_le_mul_of_nonneg_right (h2 q h0 hq) (hd q)

/-! ## The ports on the challenge prefix -/

/-- **The weight of the potential**: `2 progCap + 1`, more than the hardwired `k`, `k'` cells on
the prefix's calls. -/
def recN : ℕ := 2 * progCap + 1

/-- **The charge of a sponge call** per unit of trace: `recN (2 √(6ε) + 6ε)`, `ε = epsQ q`. -/
noncomputable def recS (q : ℕ) : ℝ := recN * (2 * √(6 * epsQ q) + 6 * epsQ q)

/-- **The charge of a `k`, `k'` read call** per unit of trace: `recN (ε + 2/|X| + 2/|Z| + 2 √ε)`. -/
noncomputable def recR (q : ℕ) : ℝ :=
  recN * (epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q))

theorem recS_nonneg (q : ℕ) : 0 ≤ recS q := by
  have := epsQ_nonneg q
  unfold recS
  positivity

theorem recR_nonneg (q : ℕ) : 0 ≤ recR q := by
  have := epsQ_nonneg q
  unfold recR
  positivity

section prefixPorts

variable {q : ℕ} (L : HonestTable)

theorem hwKs_lt_recN {s : HwReg X Z Mem} (h : dbGrade s.2.1 ≤ progCap) : hwKs s < recN := by
  have h1 : Database.size s.2.1.2.1 ≤ dbGrade s.2.1 := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : Database.size s.2.1.2.2 ≤ dbGrade s.2.1 := (le_max_right _ _).trans (le_max_right _ _)
  show Database.size s.2.1.2.1 + Database.size s.2.1.2.2 < 2 * progCap + 1
  omega

/-- **The sponge ports**: the potential rises by at most `recS q` per unit of trace (two-sided
fresh bounds of the level sets; none at `h`). -/
theorem hS_rec (hπ : PermGood L.perm 18) (p : SpongePort)
    {σ : Matrix (spongeIn X Z p × HwReg X Z Mem) (spongeIn X Z p × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inl p))) σ) :
    ∑' _r : Unit, potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ))
        (MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ) ≤
      potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ)) σ +
        ENNReal.ofReal (recS q * σ.trace.re) := by
  have hsupp : QuerySupportedOn (fun m : spongeIn X Z p × HwReg X Z Mem ↦ m.2)
      {s | dbGrade s.1 ≤ nD q ∧ dbGrade s.2.1 ≤ nW} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hε : ∀ (m : ℕ) (W : Hw X Z) (mm : Mem),
      PortInst (slice (levSet (recPotN L.perm recN) nW m) W mm) p (nD q + 1)
        (ENNReal.ofReal (epsQ q)) := fun m W mm ↦ by
    cases p with
    | h => exact portInst_recLev_h L.perm recN nW m W mm _ _
    | k => exact portInst_recLev_k L.perm hπ recN nW (nD q) m W mm
    | k' => exact portInst_recLev_k' L.perm hπ recN nW (nD q) m W mm
  refine (tsum_potential_sponge_layer_le (recPotN L.perm recN) nW (nD q) recN
    (fun s _ _ ↦ recPotN_le L.perm recN s) (epsQ_nonneg q) (hwEmpty X Z) m0R p hε hσ
    hsupp).trans (add_le_add le_rfl (le_of_eq (congrArg ENNReal.ofReal ?_)))
  unfold recS
  exact (mul_assoc _ _ _).symm

/-- **The read ports**: a `k`, `k'` read raises the potential by at most `recR q` per unit of
trace; a randomizer trial's `h` read keeps it. -/
theorem hR_rec (hπ : PermGood L.perm 18) (c : HwRead X Z Mem)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ}
    (hσ : σ.PosSemidef) (hI : PreInv q (.inl (.inl (.inr c))) σ) :
    ∑' r, potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ))
        (MatrixMap.conj (hwReadKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ)) σ +
        ENNReal.ofReal (recR q * σ.trace.re) := by
  by_cases ht : IsTrial trialUpd c
  · obtain ⟨zt, rfl⟩ := ht
    exact (tsum_potential_readH_le (fun s ↦ Nat.cast_nonneg _)
      (recPotN_offCell L.perm recN zt.1) _ hσ).trans le_self_add
  have hok : ReadOk c := readOk_of_okCharge hI.1
  have hnb : ReadNoBot c σ := readNoBot_of_noBot c hI.2.2
  have hsupp : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ m.2)
      {s | dbGrade s.1 ≤ nD q ∧ dbGrade s.2.1 ≤ nW} σ :=
    hI.2.1.imp fun _ h ↦ ⟨h.1, h.2.trans (Nat.le_succ _)⟩
  have hg : QuerySupportedOn (fun m : Unit × HwReg X Z Mem ↦ dbGrade m.2.1) (Set.Iic (nD q)) σ :=
    hI.2.1.imp fun _ h ↦ Set.mem_Iic.mpr h.1
  have hcost : ∀ m, (∀ W mm, PortInst (slice (levSet (recPotN L.perm recN) nW m) W mm)
      (readPort c) (nD q + 1) (ENNReal.ofReal (epsQ q))) → KeepUpd c →
      readCost (levSet (recPotN L.perm recN) nW m) c σ ≤ ENNReal.ofReal
        ((epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) * σ.trace.re) :=
    fun m hε hk ↦ readCost_le_of_keep _ c hk hσ (epsQ_nonneg q)
      ((keepE_le_of_portInst _ ENNReal.ofReal_ne_top c hε hσ hg).trans_eq
        (by rw [ENNReal.toReal_ofReal (epsQ_nonneg q)]))
  refine (tsum_potential_read_layer_le (recPotN L.perm recN) nW (nD q) recN
    (fun s _ _ ↦ recPotN_le L.perm recN s) c hσ hnb (b := ENNReal.ofReal
      ((epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q)) * σ.trace.re))
    (fun m ↦ ?_) hsupp).trans
    (add_le_add le_rfl (le_of_eq ?_))
  · rcases hok with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ht'
    · exact hcost m (fun W mm ↦ portInst_recLev_k L.perm hπ recN nW (nD q) m W mm)
        (fun _ _ ↦ rfl)
    · exact hcost m (fun W mm ↦ portInst_recLev_k' L.perm hπ recN nW (nD q) m W mm)
        (fun _ _ ↦ rfl)
    · exact absurd ht' ht
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    unfold recR
    exact congrArg ENNReal.ofReal (mul_assoc _ _ _).symm

open scoped Classical in
/-- **The program ports**: inside `tableHw L`, a program pays its `RecJ` weight out of the
potential, up to `recN` times the target-free fresh flips (KeyLazy's `kfW`). -/
theorem recJW_add_prog_le (c : HwProg X Z)
    {σ : Matrix (Unit × HwReg X Z Mem) (Unit × HwReg X Z Mem) ℂ} (hσ : σ.PosSemidef)
    (hc : ProgOf (tableHw L) c)
    (hsupp : ∀ q, σ q q ≠ 0 → Quantum.Sponge.HwLe q.2.2.1 (tableHw L) ∧
      dbGrade q.2.2.1 ≤ progCap ∧ progCap + dbGrade q.2.1 ≤ 2 ^ 68) :
    recJW L c σ + ∑' r, potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ))
        (MatrixMap.conj (hwProgKraus c r) σ) ≤
      potential (diagPot fun s ↦ √(recPotN L.perm recN s : ℝ)) σ +
        (recN : ℝ≥0∞) * kfW L.perm c σ := by
  have hφ0 : ∀ s : HwReg X Z Mem, 0 ≤ (recPotN L.perm recN s : ℝ) := fun s ↦ Nat.cast_nonneg _
  have hre : ∀ q, 0 ≤ (σ q q).re := fun q ↦ (Complex.nonneg_iff.1 hσ.diag_nonneg).1
  have hne : ∀ q : Unit × HwReg X Z Mem, (σ q q).re ≠ 0 → σ q q ≠ 0 :=
    fun q h h0 ↦ h (by rw [h0, Complex.zero_re])
  rw [tsum_potential_prog_eq hφ0 c hσ, potential_diagPot_sqrt hφ0]
  cases c with
  | programH z v =>
    refine (ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ L (.programH z v) q.2) ∅
      (fun q ↦ (recPotN L.perm recN q.2 : ℝ))
      (fun q ↦ (recPotN L.perm recN (progMap (.programH z v) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) recN (fun _ _ h ↦ h.elim) (fun q _ _ ↦ by
        rw [recPotN_progH]) (fun q _ ↦ by
        rw [recPotN_progH]
        exact le_add_of_nonneg_right (Nat.cast_nonneg _))).trans_eq ?_
    show _ + _ * diagMass ∅ σ = _ + _ * 0
    rw [diagMass_empty]
  | programK y a =>
    refine ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ L (.programK y a) q.2)
      (kfSet L.perm y a) (fun q ↦ (recPotN L.perm recN q.2 : ℝ))
      (fun q ↦ (recPotN L.perm recN (progMap (.programK y a) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) recN (fun q h0 hR ↦ ?_) (fun q h0 hq ↦ ?_) (fun q h0 ↦ ?_)
    all_goals
      obtain ⟨hW, hg1, hg2⟩ := hsupp q (hne q h0)
      have hWa : q.2.2.1.2.1 y ≠ none → q.2.2.1.2.1 y = some a := fun h1 ↦ by
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
        have h3 : (tableHw L).2.1 y = some b := hW.2.1 y b hb
        exact hb.trans (congrArg some (Option.some.inj (h3.symm.trans hc)))
      have hle := recPotN_progK_le L.perm recN y a q.2 hWa
    · exact_mod_cast recPotN_progK_add_one_le L.perm recN y a (hwKs_lt_recN hg1) hR.1 hR.2.1
    · rw [ite_eq_right fun hF ↦ hq (mem_kfSet.mpr ⟨hF, hg1, hg2⟩), add_zero] at hle
      exact_mod_cast hle
    · have : recPotN L.perm recN (progMap (.programK y a) q.2) ≤
          recPotN L.perm recN q.2 + recN :=
        hle.trans (Nat.add_le_add_left (by split_ifs <;> simp) _)
      exact_mod_cast this
  | programK' y a =>
    refine ofReal_ind_add_le (fun q ↦ (σ q q).re) hre (fun q ↦ RecJ L (.programK' y a) q.2)
      (kfSet' L.perm y a) (fun q ↦ (recPotN L.perm recN q.2 : ℝ))
      (fun q ↦ (recPotN L.perm recN (progMap (.programK' y a) q.2) : ℝ)) (fun q ↦ hφ0 q.2)
      (fun q ↦ hφ0 _) recN (fun q h0 hR ↦ ?_) (fun q h0 hq ↦ ?_) (fun q h0 ↦ ?_)
    all_goals
      obtain ⟨hW, hg1, hg2⟩ := hsupp q (hne q h0)
      have hWa : q.2.2.1.2.2 y ≠ none → q.2.2.1.2.2 y = some a := fun h1 ↦ by
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h1
        have h3 : (tableHw L).2.2 y = some b := hW.2.2 y b hb
        exact hb.trans (congrArg some (Option.some.inj (h3.symm.trans hc)))
      have hle := recPotN_progK'_le L.perm recN y a q.2 hWa
    · exact_mod_cast recPotN_progK'_add_one_le L.perm recN y a (hwKs_lt_recN hg1) hR.1 hR.2.1
    · rw [ite_eq_right fun hF ↦ hq (mem_kfSet'.mpr ⟨hF, hg1, hg2⟩), add_zero] at hle
      exact_mod_cast hle
    · have : recPotN L.perm recN (progMap (.programK' y a) q.2) ≤
          recPotN L.perm recN q.2 + recN :=
        hle.trans (Nat.add_le_add_left (by split_ifs <;> simp) _)
      exact_mod_cast this

end prefixPorts

/-! ## The prefix and the average -/

section prefixRec

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **The `RecJ` weight of the challenge prefix**: on a table with `PermGood π 18`, at most
`recS q` per sponge call, `recR q` per classical call and `recN` times the target-free fresh flips
`kfPre`. -/
theorem recJPre_le (hq : q ≤ 2 ^ 64) (L : HonestTable) (hπ : PermGood L.perm 18) :
    recJPre A L ≤ (ENNReal.ofReal (recS q) * ((6 * q : ℕ) : ℝ≥0∞) +
      ENNReal.ofReal (recR q) * (clsCap : ℝ≥0∞)) + (recN : ℝ≥0∞) * kfPre A L := by
  obtain ⟨P, hP, hx⟩ := forallQueries_preInv (q := q) hperm hsign L
  have hT := progCap_add_le hq
  have hφ0 : ∀ s : HwReg X Z Mem, 0 ≤ (recPotN L.perm recN s : ℝ) := fun s ↦ Nat.cast_nonneg _
  set K := diagPot fun s : HwReg X Z Mem ↦ √(recPotN L.perm recN s : ℝ) with hK
  set wS : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ := fun i σ ↦
    ((if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1 : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal σ.trace.re with hwS
  set wR : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re) fun _ _ ↦ 0) with hwR
  set wK : ∀ i : (recHwSpec X Z HPos Selections).Port,
      Matrix ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D)
        ((recHwSpec X Z HPos Selections).In i × (runtimeR (X := X) (Z := Z) m0R).D) ℂ →
          ℝ≥0∞ :=
    extWeight (hwCost (fun _ _ ↦ 0) (kfW L.perm)) with hwK
  have h := totalWeight_le_potential_of_forallQueries (runtimeR m0R) .instruments K
    (fun i E σ ↦ P i E σ ∧ hwSupp Selections m0R (tableHw L) i E σ)
    (fun i τ ↦ PreInv q i τ ∧ PortIn Selections (tableHw L) i ∧
      ∀ a, ¬ Quantum.Sponge.HwLe a.2.2.1 (tableHw L) → τ a a = 0)
    (fun i E σ h ↦ ⟨hP i E σ h.1, h.2.1, fun a ha ↦
      traceRight_diag_eq_zero fun e ↦ h.2.2 (a, e) ha⟩)
    (extWeight (hwCost (fun _ _ ↦ 0) (recJW L)))
    (fun i σ ↦ ENNReal.ofReal (recS q) * wS i σ +
      (ENNReal.ofReal (recR q) * wR i σ + (recN : ℝ≥0∞) * wK i σ))
    (fun i σ hσ hI ↦ ?_) (prefixR A L) initR_posSemidef
    (forallQueries_and hx (forallQueries_hwSupp_prefixR A L))
  · have hgood : Good L.perm (union (hwEmpty X Z)
        ((Database.empty, Database.empty, Database.empty) : DbReg X Z)) :=
      (good_congr (U := union (hwEmpty X Z)
        ((Database.empty, Database.empty, Database.empty) : DbReg X Z)) (U' := emptyDbs)
        (funext fun _ ↦ rfl) (funext fun _ ↦ rfl)).2 good_emptyDbs
    have h0 : potential K initR = 0 := (potential_basis_init m0R hφ0 ()).trans (by
      rw [recPotN_of_good L.perm recN (s := ((Database.empty, Database.empty, Database.empty),
        hwEmpty X Z, m0R)) hgood, Nat.cast_zero, ENNReal.ofReal_zero])
    have e := (totalWeight_add_weight (runtimeR m0R) .instruments
      (fun i σ ↦ ENNReal.ofReal (recS q) * wS i σ)
      (fun i σ ↦ ENNReal.ofReal (recR q) * wR i σ + (recN : ℝ≥0∞) * wK i σ)
      (prefixR A L) initR).trans (congrArg₂ (· + ·)
        (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wS (prefixR A L) initR)
        ((totalWeight_add_weight (runtimeR m0R) .instruments
          (fun i σ ↦ ENNReal.ofReal (recR q) * wR i σ)
          (fun i σ ↦ (recN : ℝ≥0∞) * wK i σ) (prefixR A L) initR).trans
          (congrArg₂ (· + ·)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wR (prefixR A L) initR)
            (totalWeight_const_mul_weight (runtimeR m0R) .instruments _ wK (prefixR A L)
              initR))))
    have hS : (runtimeR m0R).totalWeight .instruments wS (prefixR A L) initR ≤
        ((6 * q : ℕ) : ℝ≥0∞) :=
      (totalWeight_chargeTrace_le (runtimeR m0R) .instruments
        (fun i ↦ if extCls X Z Mem (recSpec HPos Selections) i then 0 else 1) (prefixR A L)
        (advCalls_prefixR hperm hsign L) initR_posSemidef).trans_eq
          ((congrArg (((6 * q : ℕ) : ℝ≥0∞) * ·) (ofReal_trace_basis_init m0R ())).trans
            (mul_one _))
    have hR : (runtimeR m0R).totalWeight .instruments wR (prefixR A L) initR ≤ clsCap :=
      (totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ σ ↦ ENNReal.ofReal σ.trace.re)
          fun _ σ ↦ ENNReal.ofReal σ.trace.re)) (fun i σ _ ↦ by
            rcases i with ((p | c) | c) | T
            · exact le_rfl
            · exact le_rfl
            · exact zero_le
            · exact le_rfl) (prefixR A L) initR_posSemidef).trans
        (totalWeight_calls_le (prefixR A L) (clsCalls_prefixR hperm hsign L))
    calc recJPre A L
        ≤ potential K initR + (runtimeR m0R).totalWeight .instruments
          (fun i σ ↦ ENNReal.ofReal (recS q) * wS i σ +
            (ENNReal.ofReal (recR q) * wR i σ + (recN : ℝ≥0∞) * wK i σ)) (prefixR A L) initR := h
      _ = ENNReal.ofReal (recS q) *
            (runtimeR m0R).totalWeight .instruments wS (prefixR A L) initR +
          (ENNReal.ofReal (recR q) *
            (runtimeR m0R).totalWeight .instruments wR (prefixR A L) initR +
            (recN : ℝ≥0∞) * (runtimeR m0R).totalWeight .instruments wK (prefixR A L) initR) := by
        rw [h0, zero_add, e]
      _ ≤ ENNReal.ofReal (recS q) * ((6 * q : ℕ) : ℝ≥0∞) +
          (ENNReal.ofReal (recR q) * (clsCap : ℝ≥0∞) + (recN : ℝ≥0∞) * kfPre A L) :=
        add_le_add (mul_le_mul_of_nonneg_left hS zero_le)
          (add_le_add (mul_le_mul_of_nonneg_left hR zero_le) le_rfl)
      _ = _ := (add_assoc _ _ _).symm
  · rcases i with ((p | c) | c) | T
    · have hb : ∀ r : Unit, ((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ =
          MatrixMap.conj ((spongeHardwired X Z (hwEmpty X Z) m0R).U p) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge (hwEmpty X Z) m0R p r) σ
      show (0 : ℝ≥0∞) +
          ∑' r, potential K (((runtimeR m0R).step (.inl (.inl (.inl p)))).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * 0 + (recN : ℝ≥0∞) * 0))
      simp only [Nat.cast_one, one_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (recS_nonneg q)]
      exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hS_rec L hπ p hσ hI.1)
    · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ =
          MatrixMap.conj (hwReadKraus c r) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_read (hwEmpty X Z) m0R c r) σ
      show (0 : ℝ≥0∞) +
          ∑' r, potential K (((runtimeR m0R).step (.inl (.inl (.inr c)))).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * ENNReal.ofReal σ.trace.re + (recN : ℝ≥0∞) * 0))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
      rw [← ENNReal.ofReal_mul (recR_nonneg q)]
      exact (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r))).trans (hR_rec L hπ c hσ hI.1)
    · have hb : ∀ r, ((runtimeR m0R).step (.inl (.inr c))).branch r σ =
          MatrixMap.conj (hwProgKraus c r) σ := fun r ↦
        LinearMap.congr_fun (spongeHardwiredRuntime_step_prog (hwEmpty X Z) m0R c r) σ
      show recJW L c σ + ∑' r, potential K (((runtimeR m0R).step (.inl (.inr c))).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * 0 + (recN : ℝ≥0∞) * kfW L.perm c σ))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
      refine (add_le_add le_rfl (le_of_eq (tsum_congr fun r ↦ congrArg _ (hb r)))).trans
        (recJW_add_prog_le L c hσ hI.2.1 fun a ha ↦ ⟨?_, (hI.1.2.1 a a ha).1.2, ?_⟩)
      · by_contra h
        exact ha (hI.2.2 a h)
      · have h1 : dbGrade a.2.1 ≤ nD q := (hI.1.2.1 a a ha).1.1
        unfold nD at h1
        omega
    · show (0 : ℝ≥0∞) + ∑' r, potential K (((runtimeR m0R).step (.inr T)).branch r σ) ≤
        potential K σ + (ENNReal.ofReal (recS q) * (((0 : ℕ) : ℝ≥0∞) * ENNReal.ofReal σ.trace.re) +
          (ENNReal.ofReal (recR q) * 0 + (recN : ℝ≥0∞) * 0))
      simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero]
      exact tsum_potential_recStep_diag hφ0 (fun _ _ _ _ _ ↦ rfl) T hσ

/-- **The target-free fresh flips of the prefix, averaged** (KeyLazy's key averaging on
KeysReparam's `keyE`): on the `PermGood` tables at most `progCap 2^-301 + progCap 2^-170`. -/
theorem uavg_kfPre_le :
    uavg (fun L ↦ if PermGood L.perm 18 then kfPre A L else 0) ≤
      (2 ^ 301)⁻¹ * progCap + progCap * (2 ^ 170 : ℝ≥0∞)⁻¹ := by
  refine (uavg_le_of_injOn keyE (r0G treeQ 18) keyE_injOn card_keyE_le _
    (fun p x ↦ if PermGood (permK p) 18 then (runtimeR m0R).totalWeight .instruments
      (extWeight (hwCost (fun _ _ ↦ 0) (kfW (permK p))))
        (gameKK A (parK p) (permK p) (hkK p) (valK p x.2) x.1.1 x.1.2) initR else 0)
    (fun t ht ↦ ?_) progCap (fun t _ ↦ ?_) ((2 ^ 301)⁻¹ * progCap) (fun p ↦ ?_)).trans ?_
  · by_cases hL : PermGood t.1.perm 18
    · have hp : PermGood (permK (keyE t).1) 18 := (permK_keyE t).symm ▸ hL
      rw [ite_eq_left hL, ite_eq_left hp]
      refine (kfPre_le A t.1).trans_eq ?_
      rw [hgame_keyE A ht, permK_keyE t]
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hL : PermGood t.1.perm 18
    · rw [ite_eq_left hL]
      refine (kfPre_le A t.1).trans ((totalWeight_le_totalWeight (runtimeR m0R) .instruments
        (w' := extWeight (hwCost (fun _ _ ↦ 0) fun _ σ ↦ ENNReal.ofReal σ.trace.re))
        (fun i σ hσ ↦ ?_) (gameR A t.1) initR_posSemidef).trans
        (totalWeight_progs_le (gameR A t.1) (progCalls_gameR hperm hsign t.1)))
      rcases i with ((p | c) | c) | T
      · exact le_rfl
      · exact le_rfl
      · dsimp only [extWeight, sumWeight, hwCost]
        cases c with
        | programH z u => exact zero_le
        | programK y a => exact diagMass_le_trace _ hσ
        | programK' y a => exact diagMass_le_trace _ hσ
      · exact le_rfl
    · rw [ite_eq_right hL]
      exact zero_le
  · by_cases hp : PermGood (permK p) 18
    · refine (Finset.sum_congr rfl fun x _ ↦ ite_eq_left hp).trans_le ?_
      exact sum_pair_le (fun k k' w ↦ (runtimeR m0R).totalWeight .instruments
        (extWeight (hwCost (fun _ _ ↦ 0) (kfW (permK p))))
          (gameKK A (parK p) (permK p) (hkK p) (valK p w) k k') initR) _ _
        fun w ↦ sum_kfTot_le A (parK p) (permK p) (hkK p) (valK p w) hperm hsign hp
    · rw [Finset.sum_eq_zero fun x _ ↦ ite_eq_right hp]
      exact zero_le
  · gcongr
    exact keyE_bad_le

/-- **The bound on the averaged `RecJ` weight**: the sponge and read charges and `recN` times the
averaged fresh flips. -/
noncomputable def recCap (q : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal (recS q) * ((6 * q : ℕ) : ℝ≥0∞) + ENNReal.ofReal (recR q) * (clsCap : ℝ≥0∞)) +
    (recN : ℝ≥0∞) * ((2 ^ 301)⁻¹ * progCap + progCap * (2 ^ 170 : ℝ≥0∞)⁻¹)

/-- **EncPorts' remaining lemma**: the `RecJ` weight of the challenge prefix, averaged over the
good tables, is at most `recCap q`. -/
theorem uavg_recJPre_le (hq : q ≤ 2 ^ 64) :
    uavg (fun L ↦ if GoodL L then recJPre A L else 0) ≤ recCap q :=
  uavg_ite_le_add_mul (fun L hL ↦ recJPre_le hperm hsign hq L hL.1.1)
    ((uavg_mono fun L ↦ by
      by_cases hL : GoodL L
      · rw [ite_eq_left hL, ite_eq_left hL.1.1]
      · rw [ite_eq_right hL]
        exact zero_le).trans (uavg_kfPre_le hperm hsign))

end prefixRec

/-! ## The constants at Keccak's sizes -/

section keccak

theorem capKJ_mono {T T' : ℕ} (h : T ≤ T') (G : ℕ) : capKJ T G ≤ capKJ T' G := by
  unfold capKJ
  gcongr

theorem capKJ'_mono {T T' : ℕ} (h : T ≤ T') (G : ℕ) : capKJ' T G ≤ capKJ' T' G := by
  unfold capKJ'
  gcongr

set_option exponentiation.threshold 4096 in
/-- **The fresh-cell rate of the prefix**: `epsQ q ≤ 2^-302` for `q ≤ 2^64`. -/
theorem epsQ_le {q : ℕ} (hq : q ≤ 2 ^ 64) : epsQ q ≤ (2 ^ 302 : ℝ)⁻¹ := by
  have hT : nW + nD q ≤ 2 ^ 68 + 1 := by
    have := progCap_add_le hq
    unfold nW nD
    omega
  have hc : capKJ (nW + nD q) 18 + capKJ' (nW + nD q) 18 ≤ 2 ^ 210 :=
    (Nat.add_le_add (capKJ_mono hT 18) (capKJ'_mono hT 18)).trans (by norm_num [capKJ, capKJ'])
  have hc' : ((capKJ (nW + nD q) 18 + capKJ' (nW + nD q) 18 : ℕ) : ℝ) ≤ 2 ^ 210 := by
    exact_mod_cast hc
  unfold epsQ epsLev
  rw [card_Z, div_le_iff₀ (by positivity)]
  refine hc'.trans (le_of_eq ?_)
  push_cast
  norm_num

theorem recN_le : (recN : ℝ) ≤ 2 ^ 44 := by
  unfold recN
  rw [progCap_eq]
  norm_num

set_option exponentiation.threshold 4096 in
/-- **The sponge charge**: `recS q ≤ 2^-103` for `q ≤ 2^64`. -/
theorem recS_le {q : ℕ} (hq : q ≤ 2 ^ 64) : recS q ≤ (2 ^ 103 : ℝ)⁻¹ := by
  have he := epsQ_le hq
  have he0 := epsQ_nonneg q
  have h6 : 6 * epsQ q ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by
    calc 6 * epsQ q ≤ 6 * (2 ^ 302 : ℝ)⁻¹ := by gcongr
      _ ≤ ((2 ^ 149 : ℝ)⁻¹) ^ 2 := by norm_num
  have hs : √(6 * epsQ q) ≤ (2 ^ 149 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt h6).trans_eq (Real.sqrt_sq (by positivity))
  unfold recS
  calc (recN : ℝ) * (2 * √(6 * epsQ q) + 6 * epsQ q)
      ≤ 2 ^ 44 * (2 * (2 ^ 149 : ℝ)⁻¹ + ((2 ^ 149 : ℝ)⁻¹) ^ 2) := by
        gcongr
        exact recN_le
    _ ≤ (2 ^ 103 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 4096 in
/-- **The read charge**: `recR q ≤ 2^-105` for `q ≤ 2^64`. -/
theorem recR_le {q : ℕ} (hq : q ≤ 2 ^ 64) : recR q ≤ (2 ^ 105 : ℝ)⁻¹ := by
  have he := epsQ_le hq
  have he0 := epsQ_nonneg q
  have he' : epsQ q ≤ ((2 ^ 151 : ℝ)⁻¹) ^ 2 := he.trans_eq (by norm_num)
  have hs : √(epsQ q) ≤ (2 ^ 151 : ℝ)⁻¹ :=
    (Real.sqrt_le_sqrt he').trans_eq (Real.sqrt_sq (by positivity))
  have hX : (2 : ℝ) / Fintype.card X ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_X]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  have hZ : (2 : ℝ) / Fintype.card Z ≤ (2 ^ 511 : ℝ)⁻¹ := by
    rw [card_Z]
    push_cast
    rw [div_le_iff₀ (by positivity)]
    norm_num
  unfold recR
  calc (recN : ℝ) * (epsQ q + (2 / Fintype.card X + 2 / Fintype.card Z) + 2 * √(epsQ q))
      ≤ 2 ^ 44 * ((2 ^ 302 : ℝ)⁻¹ + ((2 ^ 511 : ℝ)⁻¹ + (2 ^ 511 : ℝ)⁻¹) +
        2 * (2 ^ 151 : ℝ)⁻¹) := by
        gcongr
        exact recN_le
    _ ≤ (2 ^ 105 : ℝ)⁻¹ := by norm_num

set_option exponentiation.threshold 4096 in
/-- **`ε_rec` at Keccak's sizes**: `recCap q ≤ 2^-35` for `q ≤ 2^64`. -/
theorem recCap_le {q : ℕ} (hq : q ≤ 2 ^ 64) : recCap q ≤ (2 ^ 35 : ℝ≥0∞)⁻¹ := by
  have hcls : (clsCap : ℝ) ≤ 2 ^ 68 := by
    have := progCap_add_le (q := 0) (Nat.zero_le _)
    exact_mod_cast (by omega : clsCap ≤ 2 ^ 68)
  have h6q : ((6 * q : ℕ) : ℝ) ≤ 6 * 2 ^ 64 := by exact_mod_cast (by omega : 6 * q ≤ 6 * 2 ^ 64)
  have hpc : (progCap : ℝ) ≤ 2 ^ 43 := by
    rw [progCap_eq]
    norm_num
  have h1 : ENNReal.ofReal (recS q) * ((6 * q : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 ^ 103 : ℝ)⁻¹ * (6 * 2 ^ 64)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (recS_nonneg q)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul (recS_le hq) h6q (Nat.cast_nonneg _)
      (by positivity))
  have h2 : ENNReal.ofReal (recR q) * (clsCap : ℝ≥0∞) ≤
      ENNReal.ofReal ((2 ^ 105 : ℝ)⁻¹ * 2 ^ 68) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (recR_nonneg q)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul (recR_le hq) hcls (Nat.cast_nonneg _)
      (by positivity))
  have h3 : (recN : ℝ≥0∞) * ((2 ^ 301)⁻¹ * progCap + progCap * (2 ^ 170 : ℝ≥0∞)⁻¹) ≤
      ENNReal.ofReal (2 ^ 44 * (1 / 2 ^ 301 * 2 ^ 43 + 2 ^ 43 * (1 / 2 ^ 170))) := by
    rw [inv_two_pow_eq_ofReal 301, inv_two_pow_eq_ofReal 170, ← ENNReal.ofReal_natCast progCap,
      ← ENNReal.ofReal_natCast recN, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 301),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg progCap),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg recN)]
    refine ENNReal.ofReal_le_ofReal ?_
    gcongr
    exact recN_le
  refine (add_le_add (add_le_add h1 h2) h3).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), inv_two_pow_eq_ofReal 35]
  refine ENNReal.ofReal_le_ofReal ?_
  norm_num

end keccak

section prefixRec

variable {q : ℕ} {A : Adversary (X × Z)}
  (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
  (hsign : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) lifetime)
include hperm hsign

/-- **EncPorts' remaining lemma at Keccak's sizes**: for `q ≤ 2^64`, the averaged `RecJ` weight of
the challenge prefix over the good tables is at most `2^-35`. -/
theorem uavg_recJPre_le_two_pow (hq : q ≤ 2 ^ 64) :
    uavg (fun L ↦ if GoodL L then recJPre A L else 0) ≤ (2 ^ 35 : ℝ≥0∞)⁻¹ :=
  (uavg_recJPre_le hperm hsign hq).trans (recCap_le hq)

end prefixRec

end Quantum.Xmss.Assembly

end
