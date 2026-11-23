module

public import Quantum.Sponge.Combinatorics
public import Quantum.Sponge.Hash

@[expose] public section

/-!
# Msponge paths on total tables

Section 5.2 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731). The Msponge of a block list
`m = [t_1, …, t_j]` on tables `κ, κ' : X → Z`: from capacity `z_0 = 0`, round `i` is
`(x_i, zi_i) = π (t_i, z_{i-1} + κ t_i)`, `z_i = zi_i + κ' x_i`; the output is `x_j + h z_j`.

* `pathState π κ κ' m = (hd, zend)`: the rate of the last intermediate pair (`0` for `[]`) and the
  final capacity; `pathRates` lists the intermediate rates, the `κ'` cells the path reads (its `κ`
  cells are the blocks of `m`). `pathState_congr`: the path only depends on the cells it reads.
* `tab D` reads a partial table with `getD 0`. `isTail_iff`: a tail of a database is a block list
  whose path reads only recorded cells, ending at its capacity (`Recorded`); the last intermediate
  rate of a tail is `hd` (`IsTail.hd_eq`).
* `card_hd_mem_le`, `card_zend_mem_le`: the last hidden cell of a path, a `κ` cell at a fresh block
  or a `κ'` cell at a fresh intermediate rate, puts the path's last rate in a set `S` for at most
  `#S * G` of its values (`PermGood π G`), or its end capacity in a set `T` for at most `#T`.
* `absorb_eq_pathState`: on total `(h, k, k')` the sponge absorbs a nonempty `m` along the Msponge
  path of its tail `absorbTail`, its rate is `hd + h zend` (`msp`).
-/

namespace Quantum.Sponge

open Finset

section paths

variable {X Z : Type} [Zero X] [AddCommGroup Z] (π : Equiv.Perm (X × Z))

/-- One Msponge round from capacity `z` on block `x`: the intermediate rate and the next
capacity. -/
def roundT (κ κ' : X → Z) (z : Z) (x : X) : X × Z :=
  ((π (x, z + κ x)).1, (π (x, z + κ x)).2 + κ' (π (x, z + κ x)).1)

/-- The rate of the last intermediate pair (`0` for `[]`) and the capacity after the Msponge
path of `m`. -/
def pathState (κ κ' : X → Z) (m : List X) : X × Z :=
  m.foldl (fun s x ↦ roundT π κ κ' s.2 x) (0, 0)

/-- The capacity the path of `m` ends at. -/
def zend (κ κ' : X → Z) (m : List X) : Z :=
  (pathState π κ κ' m).2

/-- The rate of the last intermediate pair of the path of `m`, the Msponge's head. -/
def hd (κ κ' : X → Z) (m : List X) : X :=
  (pathState π κ κ' m).1

/-- The intermediate rates of the path of `m`, in order: the `κ'` cells it reads. -/
def pathRates (κ κ' : X → Z) (m : List X) : List X :=
  (m.foldl (fun p x ↦ (roundT π κ κ' p.1.2 x, p.2 ++ [(roundT π κ κ' p.1.2 x).1]))
    (((0, 0) : X × Z), ([] : List X))).2

/-- The Msponge's output on total tables: the head plus `h` of the end capacity. -/
def msp [Add X] (h : Z → X) (κ κ' : X → Z) (m : List X) : X :=
  hd π κ κ' m + h (zend π κ κ' m)

/-- A partial table read with `getD 0`. -/
def tab {Y : Type} [Zero Y] (D : Database X Y) : X → Y :=
  fun x ↦ (D x).getD 0

@[simp] theorem pathState_nil (κ κ' : X → Z) : pathState π κ κ' [] = (0, 0) :=
  rfl

@[simp] theorem pathRates_nil (κ κ' : X → Z) : pathRates π κ κ' [] = [] :=
  rfl

theorem pathState_append_singleton (κ κ' : X → Z) (m : List X) (x : X) :
    pathState π κ κ' (m ++ [x]) = roundT π κ κ' (zend π κ κ' m) x := by
  simp [pathState, zend, List.foldl_append]

omit [Zero X] in
private theorem foldl_rates_fst (κ κ' : X → Z) (m : List X) (p : (X × Z) × List X) :
    (m.foldl (fun p x ↦ (roundT π κ κ' p.1.2 x, p.2 ++ [(roundT π κ κ' p.1.2 x).1])) p).1 =
      m.foldl (fun s x ↦ roundT π κ κ' s.2 x) p.1 := by
  induction m generalizing p with
  | nil => rfl
  | cons x m ih => exact ih _

theorem pathRates_append_singleton (κ κ' : X → Z) (m : List X) (x : X) :
    pathRates π κ κ' (m ++ [x]) = pathRates π κ κ' m ++ [hd π κ κ' (m ++ [x])] := by
  simp only [pathRates, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [foldl_rates_fst, hd, pathState_append_singleton, zend, pathState]

theorem zend_append_singleton (κ κ' : X → Z) (m : List X) (x : X) :
    zend π κ κ' (m ++ [x]) =
      (π (x, zend π κ κ' m + κ x)).2 + κ' (π (x, zend π κ κ' m + κ x)).1 := by
  rw [zend, pathState_append_singleton]
  rfl

theorem hd_append_singleton (κ κ' : X → Z) (m : List X) (x : X) :
    hd π κ κ' (m ++ [x]) = (π (x, zend π κ κ' m + κ x)).1 := by
  rw [hd, pathState_append_singleton]
  rfl

@[simp] theorem zend_nil (κ κ' : X → Z) : zend π κ κ' [] = 0 :=
  rfl

@[simp] theorem hd_nil (κ κ' : X → Z) : hd π κ κ' [] = 0 :=
  rfl

theorem length_pathRates (κ κ' : X → Z) (m : List X) :
    (pathRates π κ κ' m).length = m.length := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m x ih => simp [pathRates_append_singleton, ih]

/-- **The path only depends on the cells it reads**: tables that agree on the blocks of `m` and on
its intermediate rates give the same path. -/
theorem pathState_congr {κ₁ κ₂ κ'₁ κ'₂ : X → Z} {m : List X} (hk : ∀ x ∈ m, κ₁ x = κ₂ x)
    (hk' : ∀ x ∈ pathRates π κ₁ κ'₁ m, κ'₁ x = κ'₂ x) :
    pathState π κ₁ κ'₁ m = pathState π κ₂ κ'₂ m ∧
      pathRates π κ₁ κ'₁ m = pathRates π κ₂ κ'₂ m := by
  induction m using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton m x ih =>
    rw [pathRates_append_singleton] at hk'
    obtain ⟨h1, h2⟩ := ih (fun y hy ↦ hk y (List.mem_append_left _ hy))
      fun y hy ↦ hk' y (List.mem_append_left _ hy)
    have hz : zend π κ₁ κ'₁ m = zend π κ₂ κ'₂ m := congrArg Prod.snd h1
    have hx : κ₁ x = κ₂ x := hk x (by simp)
    have hlast := hk' (hd π κ₁ κ'₁ (m ++ [x])) (by simp)
    rw [hd_append_singleton] at hlast
    refine ⟨?_, ?_⟩
    · rw [pathState_append_singleton, pathState_append_singleton, roundT, roundT, hz, hx, ← hx,
        ← hz, hlast]
    · rw [pathRates_append_singleton, pathRates_append_singleton, h2, hd_append_singleton,
        hd_append_singleton, hz, hx]

theorem zend_congr {κ₁ κ₂ κ'₁ κ'₂ : X → Z} {m : List X} (hk : ∀ x ∈ m, κ₁ x = κ₂ x)
    (hk' : ∀ x ∈ pathRates π κ₁ κ'₁ m, κ'₁ x = κ'₂ x) :
    zend π κ₁ κ'₁ m = zend π κ₂ κ'₂ m :=
  congrArg Prod.snd (pathState_congr π hk hk').1

theorem hd_congr {κ₁ κ₂ κ'₁ κ'₂ : X → Z} {m : List X} (hk : ∀ x ∈ m, κ₁ x = κ₂ x)
    (hk' : ∀ x ∈ pathRates π κ₁ κ'₁ m, κ'₁ x = κ'₂ x) :
    hd π κ₁ κ'₁ m = hd π κ₂ κ'₂ m :=
  congrArg Prod.fst (pathState_congr π hk hk').1

/-! ## Tails are recorded paths -/

/-- Every cell the path of `m` reads is recorded in `D`: the blocks in `D.k`, the intermediate
rates (on the tables `tab D.k`, `tab D.k'`) in `D.k'`. -/
def Recorded (D : Dbs X Z) (m : List X) : Prop :=
  (∀ x ∈ m, (D.k x).isSome) ∧ ∀ x ∈ pathRates π (tab D.k) (tab D.k') m, (D.k' x).isSome

theorem recorded_append_singleton {D : Dbs X Z} {m : List X} {x : X} :
    Recorded π D (m ++ [x]) ↔ Recorded π D m ∧ (D.k x).isSome ∧
      (D.k' (hd π (tab D.k) (tab D.k') (m ++ [x]))).isSome := by
  simp only [Recorded, List.mem_append, List.mem_singleton, pathRates_append_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun y hy ↦ h1 y (.inl hy), fun y hy ↦ h2 y (.inl hy)⟩, h1 x (.inr rfl),
      h2 _ (.inr rfl)⟩
  · rintro ⟨⟨h1, h2⟩, hx, hx'⟩
    exact ⟨fun y hy ↦ hy.elim (h1 y) fun h ↦ h ▸ hx, fun y hy ↦ hy.elim (h2 y) fun h ↦ h ▸ hx'⟩

/-- **A tail is a recorded path**: `t` is a tail of `z` in `D` iff its path reads only recorded
cells and ends at `z`. -/
theorem isTail_iff {D : Dbs X Z} {t : List X} {z : Z} :
    IsTail π D t z ↔ Recorded π D t ∧ zend π (tab D.k) (tab D.k') t = z := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨⟨by simp, by simp⟩, rfl⟩
    | @snoc t zp xp xi a zi b _ hka hπ hb ih =>
      obtain ⟨hr, rfl⟩ := ih
      have hpi : π (xp, zend π (tab D.k) (tab D.k') t + tab D.k xp) = (xi, zi) := by
        rw [tab, hka, Option.getD_some, hπ]
      refine ⟨recorded_append_singleton π |>.2 ⟨hr, by simp [hka], ?_⟩, ?_⟩
      · rw [hd_append_singleton, hpi]
        simp [hb]
      · rw [zend_append_singleton, hpi, tab, hb, Option.getD_some]
  · intro ⟨hr, hz⟩
    subst hz
    induction t using List.reverseRecOn with
    | nil => exact .nil
    | append_singleton t x ih =>
      obtain ⟨hr, hx, hx'⟩ := recorded_append_singleton π |>.1 hr
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hx
      rw [hd_append_singleton] at hx'
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hx'
      have hka : tab D.k x = a := by rw [tab, ha, Option.getD_some]
      rw [hka] at hb
      have hkb : tab D.k' (π (x, zend π (tab D.k) (tab D.k') t + a)).1 = b := by
        change (D.k' _).getD 0 = b
        rw [hb, Option.getD_some]
      rw [zend_append_singleton, hka, hkb]
      exact .snoc (ih hr) ha rfl hb

/-- The last intermediate rate of a tail is its head. -/
theorem IsTail.hd_eq {D : Dbs X Z} {t : List X} {zp : Z} {xp xi : X} {a zi : Z}
    (ht : IsTail π D t zp) (hka : D.k xp = some a) (hπ : π (xp, zp + a) = (xi, zi)) :
    hd π (tab D.k) (tab D.k') (t ++ [xp]) = xi := by
  rw [hd_append_singleton, (isTail_iff π |>.1 ht).2, tab, hka, Option.getD_some, hπ]

/-- An extension reads a recorded path the same way. -/
theorem Recorded.pathState_eq {D D' : Dbs X Z} (hDD : Extends D' D) {m : List X}
    (hr : Recorded π D m) :
    pathState π (tab D.k) (tab D.k') m = pathState π (tab D'.k) (tab D'.k') m ∧
      pathRates π (tab D.k) (tab D.k') m = pathRates π (tab D'.k) (tab D'.k') m := by
  refine pathState_congr π (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (hr.1 x hx)
    simp [tab, ha, hDD.1 x a ha]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hr.2 x hx)
    simp [tab, hb, hDD.2 x b hb]

theorem Recorded.mono {D D' : Dbs X Z} (hDD : Extends D' D) {m : List X}
    (hr : Recorded π D m) : Recorded π D' m := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (hr.1 x hx)
    simp [hDD.1 x a ha]
  · rw [← (hr.pathState_eq π hDD).2] at hx
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hr.2 x hx)
    simp [hDD.2 x b hb]

/-- The head of a tail is the same in every extension. -/
theorem IsTail.hd_extends {D D' : Dbs X Z} (hDD : Extends D' D) {t : List X} {z : Z}
    (ht : IsTail π D t z) :
    hd π (tab D'.k) (tab D'.k') t = hd π (tab D.k) (tab D.k') t :=
  (congrArg Prod.fst ((isTail_iff π |>.1 ht).1.pathState_eq π hDD).1).symm

/-! ## The last hidden cell -/

section count

variable [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- **A hidden `κ` cell at a fresh block**: if the block `x` does not occur in `m0`, the last rate
of the path of `m0 ++ [x]` lies in `S` for at most `#S * G` values of `κ x`. -/
theorem card_hd_mem_le {G : ℕ} (hG : PermGood π G) (κ κ' : X → Z) {m0 : List X} {x : X}
    (hx : x ∉ m0) (S : Finset X) :
    #(univ.filter fun a : Z ↦ hd π (Function.update κ x a) κ' (m0 ++ [x]) ∈ S) ≤ #S * G := by
  have hz : ∀ a, zend π (Function.update κ x a) κ' m0 = zend π κ κ' m0 := fun a ↦
    zend_congr π (fun y hy ↦ Function.update_of_ne (ne_of_mem_of_not_mem hy hx) _ _)
      fun _ _ ↦ rfl
  calc #(univ.filter fun a : Z ↦ hd π (Function.update κ x a) κ' (m0 ++ [x]) ∈ S)
      ≤ #(S.biUnion fun xi ↦ univ.filter fun a ↦ (π (x, zend π κ κ' m0 + a)).1 = xi) := by
        refine card_le_card fun a ha ↦ ?_
        rw [mem_filter, hd_append_singleton, hz, Function.update_self] at ha
        exact mem_biUnion.2 ⟨_, ha.2, mem_filter.2 ⟨mem_univ _, rfl⟩⟩
    _ ≤ #S * G := card_biUnion_le_card_mul _ _ _ fun xi _ ↦
        (card_rate_shift π x xi _).trans_le (hG.rate x xi)

/-- **A hidden `κ'` cell at a fresh intermediate rate**: if the last rate `xi` of the path of
`m0 ++ [x]` is not an intermediate rate of `m0`, the path's end capacity lies in `T` for at most
`#T` values of `κ' xi`. -/
theorem card_zend_mem_le (κ κ' : X → Z) {m0 : List X} {x : X}
    (hxi : hd π κ κ' (m0 ++ [x]) ∉ pathRates π κ κ' m0) (T : Finset Z) :
    #(univ.filter fun b : Z ↦
      zend π κ (Function.update κ' (hd π κ κ' (m0 ++ [x])) b) (m0 ++ [x]) ∈ T) ≤ #T := by
  set xi := hd π κ κ' (m0 ++ [x])
  have hz : ∀ b, zend π κ (Function.update κ' xi b) m0 = zend π κ κ' m0 := fun b ↦
    (zend_congr π (fun _ _ ↦ rfl) fun y hy ↦
      (Function.update_of_ne (ne_of_mem_of_not_mem hy hxi) _ _).symm).symm
  have hxi' : (π (x, zend π κ κ' m0 + κ x)).1 = xi := (hd_append_singleton π κ κ' m0 x).symm
  calc #(univ.filter fun b : Z ↦ zend π κ (Function.update κ' xi b) (m0 ++ [x]) ∈ T)
      = #(univ.filter fun b : Z ↦ (π (x, zend π κ κ' m0 + κ x)).2 + b ∈ T) := by
        congr 1
        refine filter_congr fun b _ ↦ ?_
        rw [zend_append_singleton, hz, hxi', Function.update_self]
    _ = #(univ.filter fun b : Z ↦ b ∈ T) :=
        card_filter_add_left _ fun b ↦ b ∈ T
    _ ≤ #T := by rw [filter_mem_eq_inter, univ_inter]

end count

end paths

/-! ## The sponge on total tables -/

section sponge

variable {X Z : Type} [AddCommGroup X] [AddCommGroup Z] (π : Equiv.Perm (X × Z)) (h : Z → X)
  (k k' : X → Z)

/-- The sponge's capacity is the end of the Msponge path of its tail, and its rate after a
nonempty message is the Msponge output `msp` of the tail. -/
theorem absorb_eq_pathState (m : List X) :
    (absorb (spongePerm (h, k, k') π) m).2 =
        zend π k k' (absorbTail (spongePerm (h, k, k') π) m) ∧
      (m ≠ [] → (absorb (spongePerm (h, k, k') π) m).1 =
        msp π h k k' (absorbTail (spongePerm (h, k, k') π) m)) := by
  induction m using List.reverseRecOn with
  | nil => exact ⟨rfl, fun h ↦ absurd rfl h⟩
  | append_singleton m b ih =>
    rw [absorb_append_singleton, absorbTail_append_singleton, absorbStep, spongePerm_apply, msp,
      zend_append_singleton, hd_append_singleton, ← ih.1]
    exact ⟨rfl, fun _ ↦ rfl⟩

/-- **The sponge is the Msponge of its tail**: `spongeHash φ m = msp (absorbTail φ m)` for
`m ≠ []`. -/
theorem spongeHash_eq_msp {m : List X} (hm : m ≠ []) :
    spongeHash (spongePerm (h, k, k') π) m =
      msp π h k k' (absorbTail (spongePerm (h, k, k') π) m) :=
  (absorb_eq_pathState π h k k' m).2 hm

end sponge

end Quantum.Sponge

end
