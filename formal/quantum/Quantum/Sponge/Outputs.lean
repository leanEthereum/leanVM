module

public import Quantum.Sponge.Combinatorics
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section

/-!
# Reachable outputs, collisions and preimages of the Msponge

Section 6.1 of Alagic, Carolan, Majenz and Tokat (ePrint 2025/731). A nonempty tail `t0 ++ [xp]`
ends with a round whose intermediate rate `xi` is its head; the Msponge's output after absorbing
`t0 ++ [xp]` is the head plus `h` of the final capacity (Definition 6.1).

* `IsHeadTail π D t z xi`: `t` is a nonempty tail of `z` with head `xi`;
* `Reaches π D t y`: absorbing `t` outputs `y`;
* `Collision π D`: two distinct tails reach the same output (Definition 6.5);
* `ReachesOutput π D y`: some tail reaches `y` (the predicate `P_y` of Corollary 6.12).

For a good database without a collision (or without a path to `y`), we count the values of a fresh
cell of `h`, `k` or `k'` that create a collision (a path to `y`) or make the database bad: the
per-query cases of Lemma 6.6.
-/

namespace Quantum.Sponge

open Quantum

variable {X Z Y : Type} [AddCommGroup X] [AddCommGroup Z]

/-- `t` is a nonempty tail of `z` whose last round has intermediate rate `xi`, the head of `t`. -/
def IsHeadTail (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (t : List X) (z : Z) (xi : X) : Prop :=
  ∃ t0 zp xp a zi b, t = t0 ++ [xp] ∧ IsTail π D t0 zp ∧ D.k xp = some a ∧
    π (xp, zp + a) = (xi, zi) ∧ D.k' xi = some b ∧ z = zi + b

/-- The Msponge outputs `y` after absorbing `t`: `out` of the head of `t` plus `h` of its final
capacity. `out` truncates the rate to the output (`id` for the full rate). -/
def Reaches (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (out : X → Y) (t : List X) (y : Y) : Prop :=
  ∃ z xi w, IsHeadTail π D t z xi ∧ D.h z = some w ∧ y = out (xi + w)

/-- A collision (Definition 6.5): two distinct tails reach the same output. -/
def Collision (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (out : X → Y) : Prop :=
  ∃ t t' y, t ≠ t' ∧ Reaches π D out t y ∧ Reaches π D out t' y

/-- Some tail reaches the output `y`: the predicate `P_y` of Corollary 6.12. -/
def ReachesOutput (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (out : X → Y) (y : Y) : Prop :=
  ∃ t, Reaches π D out t y

/-- `D` extends `D'` on all three databases. -/
def ExtendsAll (D D' : Dbs X Z) : Prop :=
  Extends D D' ∧ ∀ z w, D'.h z = some w → D.h z = some w

variable {π : Equiv.Perm (X × Z)} {D D' : Dbs X Z} {out : X → Y}

/-! ## Tails and heads -/

section Tails

omit [AddCommGroup X]

theorem isTail_nil_iff {z : Z} : IsTail π D [] z ↔ z = 0 := by
  constructor
  · intro h
    generalize hs : ([] : List X) = s at h
    cases h with
    | nil => rfl
    | snoc => simp at hs
  · rintro rfl
    exact .nil

theorem isTail_snoc_iff {t : List X} {xp : X} {z : Z} :
    IsTail π D (t ++ [xp]) z ↔ ∃ zp a xi zi b, IsTail π D t zp ∧ D.k xp = some a ∧
      π (xp, zp + a) = (xi, zi) ∧ D.k' xi = some b ∧ z = zi + b := by
  constructor
  · intro h
    generalize hs : t ++ [xp] = s at h
    cases h with
    | nil => simp at hs
    | snoc ht hk hπ hk' =>
      obtain ⟨rfl, h1⟩ := List.append_inj' hs rfl
      obtain rfl := List.singleton_injective h1
      exact ⟨_, _, _, _, _, ht, hk, hπ, hk', rfl⟩
  · rintro ⟨zp, a, xi, zi, b, ht, hk, hπ, hk', rfl⟩
    exact .snoc ht hk hπ hk'

/-- A tail reaches only one capacity. -/
theorem IsTail.unique {t : List X} {z z' : Z} (h : IsTail π D t z) (h' : IsTail π D t z') :
    z = z' := by
  induction h generalizing z' with
  | nil => exact (isTail_nil_iff.1 h').symm
  | snoc _ hk hπ hk' ih =>
    obtain ⟨zp', a', xi', zi', b', ht', hk2, hπ2, hk'2, rfl⟩ := isTail_snoc_iff.1 h'
    obtain rfl := ih ht'
    obtain rfl := Option.some_injective _ (hk.symm.trans hk2)
    rw [hπ, Prod.mk.injEq] at hπ2
    obtain ⟨rfl, rfl⟩ := hπ2
    obtain rfl := Option.some_injective _ (hk'.symm.trans hk'2)
    rfl

theorem IsHeadTail.isTail {t : List X} {z : Z} {xi : X} (h : IsHeadTail π D t z xi) :
    IsTail π D t z := by
  obtain ⟨t0, zp, xp, a, zi, b, rfl, ht, hk, hπ, hk', rfl⟩ := h
  exact .snoc ht hk hπ hk'

theorem IsHeadTail.mono (hE : Extends D D') {t : List X} {z : Z} {xi : X}
    (h : IsHeadTail π D' t z xi) : IsHeadTail π D t z xi := by
  obtain ⟨t0, zp, xp, a, zi, b, rfl, ht, hk, hπ, hk', rfl⟩ := h
  exact ⟨t0, zp, xp, a, zi, b, rfl, ht.mono hE, hE.1 _ _ hk, hπ, hE.2 _ _ hk', rfl⟩

/-- A tail determines its capacity and its head. -/
theorem IsHeadTail.unique {t : List X} {z z' : Z} {xi xi' : X} (h : IsHeadTail π D t z xi)
    (h' : IsHeadTail π D t z' xi') : z = z' ∧ xi = xi' := by
  obtain ⟨t0, zp, xp, a, zi, b, rfl, ht, hk, hπ, hk', rfl⟩ := h
  obtain ⟨t0', zp', xp', a', zi', b', hs, ht', hk2, hπ2, hk'2, rfl⟩ := h'
  obtain ⟨rfl, h1⟩ := List.append_inj' hs rfl
  obtain rfl := List.singleton_injective h1
  obtain rfl := ht.unique ht'
  obtain rfl := Option.some_injective _ (hk.symm.trans hk2)
  rw [hπ, Prod.mk.injEq] at hπ2
  obtain ⟨rfl, rfl⟩ := hπ2
  obtain rfl := Option.some_injective _ (hk'.symm.trans hk'2)
  exact ⟨rfl, rfl⟩

/-- A head-tail of `D'` whose tail is a tail of the smaller `D` is a head-tail of `D`. -/
theorem IsHeadTail.of_isTail (hE : Extends D' D) {t : List X} {z : Z} {xi : X}
    (ht : IsTail π D t z) (h : IsHeadTail π D' t z xi) : IsHeadTail π D t z xi := by
  obtain ⟨t0, -, xp, -, -, -, rfl, -⟩ := id h
  obtain ⟨zp', a', xi', zi', b', ht', hk', hπ', hk'', hz⟩ := isTail_snoc_iff.1 ht
  have h0 : IsHeadTail π D (t0 ++ [xp]) z xi' := ⟨t0, zp', xp, a', zi', b', rfl, ht', hk', hπ', hk'', hz⟩
  obtain ⟨-, rfl⟩ := (h0.mono hE).unique h
  exact h0

/-- In a good database a capacity has at most one head-tail. -/
theorem Good.isHeadTail_unique (hG : Good π D) {t t' : List X} {z : Z} {xi xi' : X}
    (h : IsHeadTail π D t z xi) (h' : IsHeadTail π D t' z xi') : t = t' ∧ xi = xi' := by
  obtain rfl := hG.1 z t t' h.isTail h'.isTail
  exact ⟨rfl, (h.unique h').2⟩

omit [AddCommGroup Z] in
theorem extends_refl_of_eq (hk : D.k = D'.k) (hk' : D.k' = D'.k') : Extends D D' :=
  ⟨fun _ _ h ↦ hk ▸ h, fun _ _ h ↦ hk' ▸ h⟩

end Tails

/-! ## Upward closure -/

omit [AddCommGroup X] in
/-- A database contained in a good database is good. -/
theorem Good.of_extendsAll (hE : ExtendsAll D D') (hG : Good π D) : Good π D' :=
  hG.mono hE.1

theorem Reaches.mono (hE : ExtendsAll D D') {t : List X} {y : Y} (h : Reaches π D' out t y) :
    Reaches π D out t y := by
  obtain ⟨z, xi, w, hht, hw, rfl⟩ := h
  exact ⟨z, xi, w, hht.mono hE.1, hE.2 _ _ hw, rfl⟩

theorem Collision.mono (hE : ExtendsAll D D') (h : Collision π D' out) : Collision π D out := by
  obtain ⟨t, t', y, hne, h1, h2⟩ := h
  exact ⟨t, t', y, hne, h1.mono hE, h2.mono hE⟩

theorem ReachesOutput.mono (hE : ExtendsAll D D') {y : Y} (h : ReachesOutput π D' out y) :
    ReachesOutput π D out y := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, ht.mono hE⟩

/-! ## Updates of `h` -/

section UpdateH

variable [DecidableEq Z]

/-- A path in `D` with a fresh `h` cell at `z` set to `u`: an old path, or a path through `z`. -/
theorem reaches_updateH_iff {z : Z} {u : X} (hz : D.h z = none) {t : List X} {y : Y} :
    Reaches π { D with h := Function.update D.h z (some u) } out t y ↔
      Reaches π D out t y ∨ ∃ xi, IsHeadTail π D t z xi ∧ y = out (xi + u) := by
  have hE : Extends D { D with h := Function.update D.h z (some u) } := extends_refl_of_eq rfl rfl
  have hE' : Extends { D with h := Function.update D.h z (some u) } D := extends_refl_of_eq rfl rfl
  constructor
  · rintro ⟨z1, xi, w, hht, hw, rfl⟩
    by_cases h1 : z1 = z
    · subst h1
      simp only [Function.update_self, Option.some.injEq] at hw
      exact .inr ⟨xi, hht.mono hE, hw ▸ rfl⟩
    · dsimp only at hw
      rw [Function.update_of_ne h1] at hw
      exact .inl ⟨z1, xi, w, hht.mono hE, hw, rfl⟩
  · rintro (⟨z1, xi, w, hht, hw, rfl⟩ | ⟨xi, hht, rfl⟩)
    · have h1 : z1 ≠ z := by rintro rfl; simp [hz] at hw
      exact ⟨z1, xi, w, hht.mono hE', by simp [Function.update_of_ne h1, hw], rfl⟩
    · exact ⟨z, xi, u, hht.mono hE', by simp, rfl⟩

omit [AddCommGroup Z] [DecidableEq Z] in
/-- Values `u` whose translates by `x0` all have the same output lie in one translated fiber. -/
theorem card_le_of_out_translate [Fintype X] [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {s : Finset X} (x0 : X) (c : Y)
    (h : ∀ u ∈ s, out (x0 + u) = c) : s.card ≤ F :=
  (Finset.card_le_card_of_injOn (x0 + ·) (fun u hu ↦ by simp [h u hu])
    fun _ _ _ _ he ↦ add_left_cancel he).trans (hF c)

open scoped Classical in
/-- A fresh `h` cell creates a collision for at most `D.h.size * F` values, with `F` a bound on the
fibers of `out`: the new path runs through the fresh capacity, whose head-tail is unique, and its
output is one of the old outputs, one per cell. -/
theorem card_collision_updateH_le [Fintype X] [Fintype Z] [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (hG : Good π D)
    (hC : ¬ Collision π D out) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      Collision π { D with h := Function.update D.h z (some u) } out).card ≤ D.h.size * F := by
  let R : X → Z → Prop := fun u z1 ↦ ∃ t xi w, IsHeadTail π D t z1 xi ∧ D.h z1 = some w ∧
    ∃ s xs, IsHeadTail π D s z xs ∧ out (xs + u) = out (xi + w)
  have key : ∀ u t s y, Reaches π D out t y →
      (∃ xs, IsHeadTail π D s z xs ∧ y = out (xs + u)) →
      1 ≤ ((Finset.univ.filter fun z1 ↦ (D.h z1).isSome).bipartiteAbove R u).card := by
    rintro u t s y ⟨z1, xi, w, hht, hw, rfl⟩ ⟨xs, hs, hy⟩
    refine Finset.one_le_card.2 ⟨z1, (Finset.mem_bipartiteAbove R).2 ⟨by simp [hw], ?_⟩⟩
    exact ⟨t, xi, w, hht, hw, s, xs, hs, hy.symm⟩
  set S : Finset X := Finset.univ.filter fun u : X ↦
    Collision π { D with h := Function.update D.h z (some u) } out
  have h1 : ∀ u ∈ S,
      1 ≤ ((Finset.univ.filter fun z1 ↦ (D.h z1).isSome).bipartiteAbove R u).card := by
    intro u hu
    obtain ⟨t, t', y, hne, h1, h2⟩ := (Finset.mem_filter.1 hu).2
    rcases (reaches_updateH_iff hz).1 h1 with h1 | h1 <;>
      rcases (reaches_updateH_iff hz).1 h2 with h2 | h2
    · exact absurd ⟨t, t', y, hne, h1, h2⟩ hC
    · exact key u t t' y h1 h2
    · exact key u t' t y h2 h1
    · obtain ⟨xi, hi, -⟩ := h1
      obtain ⟨xi', hi', -⟩ := h2
      exact absurd (hG.isHeadTail_unique hi hi').1 hne
  have h2 : ∀ z1 ∈ Finset.univ.filter (fun z1 ↦ (D.h z1).isSome),
      (S.bipartiteBelow R z1).card ≤ F := by
    intro z1 _
    rcases Finset.eq_empty_or_nonempty (S.bipartiteBelow R z1) with he | ⟨u0, hu0⟩
    · simp [he]
    obtain ⟨-, t0, xi0, w0, hht0, hw0, s0, xs0, hs0, -⟩ := (Finset.mem_bipartiteBelow R).1 hu0
    refine card_le_of_out_translate hF xs0 (out (xi0 + w0)) fun u hu ↦ ?_
    obtain ⟨-, t, xi, w, hht, hw, s, xs, hs, he⟩ := (Finset.mem_bipartiteBelow R).1 hu
    obtain ⟨-, rfl⟩ := hG.isHeadTail_unique hht hht0
    obtain rfl := Option.some_injective _ (hw.symm.trans hw0)
    obtain ⟨-, rfl⟩ := hG.isHeadTail_unique hs hs0
    exact he
  simpa [Database.size] using Finset.card_mul_le_card_mul R h1 h2

open scoped Classical in
/-- A fresh `h` cell creates a path to `y` for at most `F` values, with `F` a bound on the fibers
of `out`: translates by the head of the fresh capacity's unique head-tail of `out`'s fiber of
`y`. -/
theorem card_reachesOutput_updateH_le [Fintype X] [DecidableEq Y] {F : ℕ}
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (hG : Good π D) {y : Y}
    (hy : ¬ ReachesOutput π D out y) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      ReachesOutput π { D with h := Function.update D.h z (some u) } out y).card ≤ F := by
  rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun u : X ↦
      ReachesOutput π { D with h := Function.update D.h z (some u) } out y) with he | ⟨u0, hu0⟩
  · simp [he]
  obtain ⟨t0, ht0⟩ := (Finset.mem_filter.1 hu0).2
  rcases (reaches_updateH_iff hz).1 ht0 with ht0 | ⟨xi0, hi0, -⟩
  · exact absurd ⟨t0, ht0⟩ hy
  refine card_le_of_out_translate hF xi0 y fun u hu ↦ ?_
  obtain ⟨t, ht⟩ := (Finset.mem_filter.1 hu).2
  rcases (reaches_updateH_iff hz).1 ht with ht | ⟨xi, hi, he⟩
  · exact absurd ⟨t, ht⟩ hy
  obtain ⟨-, rfl⟩ := hG.isHeadTail_unique hi hi0
  exact he.symm

omit [AddCommGroup X] [DecidableEq Z] in
theorem card_fiber_id_le [Fintype X] [DecidableEq X] (y : X) :
    (Finset.univ.filter fun x : X ↦ id x = y).card ≤ 1 :=
  Finset.card_le_one.2 fun _ ha _ hb ↦ by simp_all

open scoped Classical in
/-- Full-rate output: a fresh `h` cell creates a collision for at most `D.h.size` values. -/
theorem card_collision_updateH_id_le [Fintype X] [Fintype Z] [DecidableEq X] (hG : Good π D)
    (hC : ¬ Collision π D id) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      Collision π { D with h := Function.update D.h z (some u) } id).card ≤ D.h.size :=
  (card_collision_updateH_le card_fiber_id_le hG hC hz).trans_eq (mul_one _)

open scoped Classical in
/-- Full-rate output: a fresh `h` cell creates a path to `y` for at most one value. -/
theorem card_reachesOutput_updateH_id_le [Fintype X] [DecidableEq X] (hG : Good π D) {y : X}
    (hy : ¬ ReachesOutput π D id y) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      ReachesOutput π { D with h := Function.update D.h z (some u) } id y).card ≤ 1 :=
  card_reachesOutput_updateH_le card_fiber_id_le hG hy hz

end UpdateH

/-! ## Paths after an update of `k` or `k'` -/

/-- If `D'` extends `D` with the same `h`, and every tail of `D'` is a tail of `D` or reaches a
capacity outside the domain of `D.h`, then every path of `D'` is a path of `D`. -/
theorem Reaches.of_tails (hE : Extends D' D) (hh : D'.h = D.h)
    (hT : ∀ t z, IsTail π D' t z → IsTail π D t z ∨ D.h z = none) {t : List X} {y : Y}
    (h : Reaches π D' out t y) : Reaches π D out t y := by
  obtain ⟨z, xi, w, hht, hw, rfl⟩ := h
  rw [hh] at hw
  rcases hT t z hht.isTail with ht | hz
  · exact ⟨z, xi, w, hht.of_isTail hE ht, hw, rfl⟩
  · simp [hz] at hw

theorem Collision.of_tails (hE : Extends D' D) (hh : D'.h = D.h)
    (hT : ∀ t z, IsTail π D' t z → IsTail π D t z ∨ D.h z = none) (h : Collision π D' out) :
    Collision π D out := by
  obtain ⟨t, t', y, hne, h1, h2⟩ := h
  exact ⟨t, t', y, hne, h1.of_tails hE hh hT, h2.of_tails hE hh hT⟩

theorem ReachesOutput.of_tails (hE : Extends D' D) (hh : D'.h = D.h)
    (hT : ∀ t z, IsTail π D' t z → IsTail π D t z ∨ D.h z = none) {y : Y}
    (h : ReachesOutput π D' out y) : ReachesOutput π D out y := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, ht.of_tails hE hh hT⟩

omit [AddCommGroup X] in
open scoped Classical in
/-- In a good database at most one intermediate pair has rate `x'`, so at most `D.h.size` shifts
`y` move its capacity into the domain of `D.h`. -/
theorem card_IP_shift_le [Fintype Z] (hG : Good π D) (x' : X) :
    (Finset.univ.filter fun y : Z ↦
      ∃ s ∈ IP π D, s.1 = x' ∧ (D.h (s.2 + y)).isSome).card ≤ D.h.size := by
  refine Finset.card_le_card_of_forall_subsingleton
    (fun y z1 ↦ ∃ s ∈ IP π D, s.1 = x' ∧ z1 = s.2 + y) ?_ ?_
  · intro y hy
    obtain ⟨s, hs, h1, h2⟩ := (Finset.mem_filter.1 hy).2
    exact ⟨s.2 + y, by simpa using h2, s, hs, h1, rfl⟩
  · intro z1 _ y ⟨_, s, hs, h1, he⟩ y' ⟨_, s', hs', h1', he'⟩
    obtain rfl := hG.2 s hs s' hs' (h1.trans h1'.symm)
    exact add_left_cancel (he.symm.trans he')

omit [AddCommGroup X] in
open scoped Classical in
/-- If outside `B` every update `D' y` is good and its tails are old tails or reach capacities
outside the domain of `D.h`, then only `y ∈ B` make `D' y` bad or satisfy a predicate `P`
that, like collisions and paths to an output, transfers back along such updates. -/
theorem card_bad_le_of_tails [Fintype Z] {P : Dbs X Z → Prop}
    (hP : ∀ D', Extends D' D → D'.h = D.h →
      (∀ t z, IsTail π D' t z → IsTail π D t z ∨ D.h z = none) → P D' → P D)
    (hnP : ¬ P D) (D' : Z → Dbs X Z) (B : Finset Z) (hE : ∀ y, Extends (D' y) D)
    (hh : ∀ y, (D' y).h = D.h)
    (hB : ∀ y ∉ B, Good π (D' y) ∧
      ∀ t z, IsTail π (D' y) t z → IsTail π D t z ∨ D.h z = none) :
    (Finset.univ.filter fun y ↦ ¬ Good π (D' y) ∨ P (D' y)).card ≤ B.card := by
  refine Finset.card_le_card fun y hy ↦ ?_
  by_contra hyB
  obtain ⟨hG', hT⟩ := hB y hyB
  rcases (Finset.mem_filter.1 hy).2 with h | h
  · exact h hG'
  · exact hnP (hP _ (hE y) (hh y) hT h)

section UpdateK

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {t G : ℕ}

omit [AddCommGroup X] in
theorem updateK_tails (hG : Good π D) {x : X} (hx : D.k x = none) {y : Z}
    (hy : y ∉ badAttachK π D x) :
    Good π { D with k := Function.update D.k x (some y) } ∧
      ∀ t z, IsTail π { D with k := Function.update D.k x (some y) } t z →
        IsTail π D t z ∨ D.h z = none :=
  ⟨good_update_k hG hx hy, fun t z h ↦ .inl ((isTail_update_k_iff hG hx hy t z).1 h)⟩

open scoped Classical in
/-- A fresh `k` cell makes a good database without a collision bad or colliding for at most
`(t + 1) * ((t + 1) * t + 2 * t) * G` values: outside `badAttachK` the tails, hence the paths, are
the old ones. -/
theorem card_bad_collision_updateK_le (hG : Good π D) (hπ : PermGood π G) {x : X}
    (hx : D.k x = none) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) (hC : ¬ Collision π D out) :
    (Finset.univ.filter fun y : Z ↦ ¬ Good π { D with k := Function.update D.k x (some y) } ∨
      Collision π { D with k := Function.update D.k x (some y) } out).card ≤
        (t + 1) * ((t + 1) * t + 2 * t) * G :=
  (card_bad_le_of_tails (P := fun D ↦ Collision π D out)
    (fun _ hE hh hT h ↦ h.of_tails hE hh hT) hC _ _ (fun _ ↦ extends_update_k hx)
    (fun _ ↦ rfl) fun _ hy ↦ updateK_tails hG hx hy).trans (card_badAttachK_le hG hπ hk hk')

open scoped Classical in
/-- A fresh `k` cell makes a good database without a path to `y0` bad or reaching `y0` for at
most `(t + 1) * ((t + 1) * t + 2 * t) * G` values. -/
theorem card_bad_reachesOutput_updateK_le (hG : Good π D) (hπ : PermGood π G) {x : X}
    (hx : D.k x = none) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) {y0 : Y}
    (hy0 : ¬ ReachesOutput π D out y0) :
    (Finset.univ.filter fun y : Z ↦ ¬ Good π { D with k := Function.update D.k x (some y) } ∨
      ReachesOutput π { D with k := Function.update D.k x (some y) } out y0).card ≤
        (t + 1) * ((t + 1) * t + 2 * t) * G :=
  (card_bad_le_of_tails (P := fun D ↦ ReachesOutput π D out y0)
    (fun _ hE hh hT h ↦ h.of_tails hE hh hT) hy0 _ _ (fun _ ↦ extends_update_k hx)
    (fun _ ↦ rfl) fun _ hy ↦ updateK_tails hG hx hy).trans (card_badAttachK_le hG hπ hk hk')

end UpdateK

section UpdateK'

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {t G : ℕ}

open scoped Classical in
/-- The values of a fresh `k'` cell at `x'` to avoid: `badCompleteK'`, and the shifts moving the
capacity of the intermediate pair with rate `x'` into the domain of `D.h`. -/
noncomputable def badCompleteOutK' (π : Equiv.Perm (X × Z)) (D : Dbs X Z) (x' : X) : Finset Z :=
  badCompleteK' π D x' ∪
    Finset.univ.filter fun y : Z ↦ ∃ s ∈ IP π D, s.1 = x' ∧ (D.h (s.2 + y)).isSome

omit [AddCommGroup X] in
theorem card_badCompleteOutK'_le (hG : Good π D) (hπ : PermGood π G) (x' : X)
    (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) :
    (badCompleteOutK' π D x').card ≤
      (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + D.h.size :=
  (Finset.card_union_le _ _).trans
    (Nat.add_le_add (card_badCompleteK'_le hG hπ hk hk') (by convert card_IP_shift_le hG x'))

omit [AddCommGroup X] in
/-- Outside `badCompleteOutK'` a fresh `k'` cell keeps goodness, and its only new tail reaches a
capacity outside the domain of `D.h`. -/
theorem updateK'_tails (hG : Good π D) {x' : X} (hx' : D.k' x' = none) {y : Z}
    (hy : y ∉ badCompleteOutK' π D x') :
    Good π { D with k' := Function.update D.k' x' (some y) } ∧
      ∀ t z, IsTail π { D with k' := Function.update D.k' x' (some y) } t z →
        IsTail π D t z ∨ D.h z = none := by
  classical
  rw [badCompleteOutK', Finset.mem_union, not_or, Finset.mem_filter, not_and] at hy
  obtain ⟨hc, hG'⟩ := update_k'_of_not_mem hG hx' hy.1
  refine ⟨hG', fun t z h ↦ ?_⟩
  rcases hc with ⟨-, hT⟩ | ⟨t0, zp, xp, a, zi, ht0, hk, hπ, hT, -⟩
  · exact .inl ((hT t z).1 h)
  rcases (hT t z).1 h with h | ⟨-, rfl⟩
  · exact .inl h
  refine .inr (Option.not_isSome_iff_eq_none.1 fun hs ↦ ?_)
  exact hy.2 (Finset.mem_univ _) ⟨(x', zi), ⟨xp, zp, a, ⟨t0, ht0⟩, hk, hπ⟩, rfl, hs⟩

open scoped Classical in
/-- A fresh `k'` cell makes a good database without a collision bad or colliding for at most
`(t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + D.h.size` values: outside
`badCompleteOutK'` the only new tail ends at a capacity outside the domain of `D.h`, so no new
path reaches an output. -/
theorem card_bad_collision_updateK'_le (hG : Good π D) (hπ : PermGood π G) {x' : X}
    (hx' : D.k' x' = none) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t)
    (hC : ¬ Collision π D out) :
    (Finset.univ.filter fun y : Z ↦ ¬ Good π { D with k' := Function.update D.k' x' (some y) } ∨
      Collision π { D with k' := Function.update D.k' x' (some y) } out).card ≤
        (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + D.h.size :=
  (card_bad_le_of_tails (P := fun D ↦ Collision π D out)
    (fun _ hE hh hT h ↦ h.of_tails hE hh hT) hC _ _ (fun _ ↦ extends_update_k' hx')
    (fun _ ↦ rfl) fun _ hy ↦ updateK'_tails hG hx' hy).trans
      (card_badCompleteOutK'_le hG hπ x' hk hk')

open scoped Classical in
/-- A fresh `k'` cell makes a good database without a path to `y0` bad or reaching `y0` for at
most `(t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + D.h.size` values. -/
theorem card_bad_reachesOutput_updateK'_le (hG : Good π D) (hπ : PermGood π G) {x' : X}
    (hx' : D.k' x' = none) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) {y0 : Y}
    (hy0 : ¬ ReachesOutput π D out y0) :
    (Finset.univ.filter fun y : Z ↦ ¬ Good π { D with k' := Function.update D.k' x' (some y) } ∨
      ReachesOutput π { D with k' := Function.update D.k' x' (some y) } out y0).card ≤
        (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + D.h.size :=
  (card_bad_le_of_tails (P := fun D ↦ ReachesOutput π D out y0)
    (fun _ hE hh hT h ↦ h.of_tails hE hh hT) hy0 _ _ (fun _ ↦ extends_update_k' hx')
    (fun _ ↦ rfl) fun _ hy ↦ updateK'_tails hG hx' hy).trans
      (card_badCompleteOutK'_le hG hπ x' hk hk')

end UpdateK'

/-! ## Per-port flip counts -/

/-- The databases that are bad or contain a collision. -/
def CollisionBad (π : Equiv.Perm (X × Z)) (out : X → Y) : Set (Dbs X Z) :=
  {D | ¬ Good π D ∨ Collision π D out}

/-- The databases that are bad or contain a path to `y0`. -/
def PreimageBad (π : Equiv.Perm (X × Z)) (out : X → Y) (y0 : Y) : Set (Dbs X Z) :=
  {D | ¬ Good π D ∨ ReachesOutput π D out y0}

section Ports

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq Y] {t G F : ℕ}

omit [DecidableEq X] in
open scoped Classical in
/-- The `h` port of `CollisionBad`: at most `t * F` values of a fresh cell flip into the set. -/
theorem card_collisionBad_updateH_le
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F)
    (hD : D ∉ CollisionBad π out) (hh : D.h.size ≤ t) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ CollisionBad π out).card ≤ t * F := by
  have hD : Good π D ∧ ¬ Collision π D out :=
    have h : ¬ (¬ Good π D ∨ Collision π D out) := hD
    ⟨not_not.1 (not_or.1 h).1, (not_or.1 h).2⟩
  refine (Finset.card_le_card fun u hu ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩).trans
    ((card_collision_updateH_le hF hD.1 hD.2 hz).trans (Nat.mul_le_mul_right _ hh))
  rcases (Finset.mem_filter.1 hu).2 with h | h
  · exact absurd ((good_update_h_iff _).2 hD.1) h
  · exact h

omit [Fintype Z] [DecidableEq X] in
open scoped Classical in
/-- The `h` port of `PreimageBad`: at most `F` values of a fresh cell flip into the set. -/
theorem card_preimageBad_updateH_le
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) {y0 : Y}
    (hD : D ∉ PreimageBad π out y0) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ PreimageBad π out y0).card ≤ F := by
  have hD : Good π D ∧ ¬ ReachesOutput π D out y0 :=
    have h : ¬ (¬ Good π D ∨ ReachesOutput π D out y0) := hD
    ⟨not_not.1 (not_or.1 h).1, (not_or.1 h).2⟩
  refine (Finset.card_le_card fun u hu ↦ Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩).trans
    (card_reachesOutput_updateH_le hF hD.1 hD.2 hz)
  rcases (Finset.mem_filter.1 hu).2 with h | h
  · exact absurd ((good_update_h_iff _).2 hD.1) h
  · exact h

omit [DecidableEq Y] in
open scoped Classical in
/-- The `k` port of `CollisionBad`. -/
theorem card_collisionBad_updateK_le (hπ : PermGood π G) (hD : D ∉ CollisionBad π out)
    (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) {x : X} (hx : D.k x = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k := Function.update D.k x (some y) } ∈ CollisionBad π out).card ≤
        (t + 1) * ((t + 1) * t + 2 * t) * G := by
  have h : ¬ (¬ Good π D ∨ Collision π D out) := hD
  refine le_trans (Finset.card_le_card fun y hy ↦ ?_)
    (card_bad_collision_updateK_le (not_not.1 (not_or.1 h).1) hπ hx hk hk' (not_or.1 h).2)
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩

omit [DecidableEq Y] in
open scoped Classical in
/-- The `k` port of `PreimageBad`. -/
theorem card_preimageBad_updateK_le (hπ : PermGood π G) {y0 : Y}
    (hD : D ∉ PreimageBad π out y0) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) {x : X}
    (hx : D.k x = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k := Function.update D.k x (some y) } ∈ PreimageBad π out y0).card ≤
        (t + 1) * ((t + 1) * t + 2 * t) * G := by
  have h : ¬ (¬ Good π D ∨ ReachesOutput π D out y0) := hD
  refine le_trans (Finset.card_le_card fun y hy ↦ ?_)
    (card_bad_reachesOutput_updateK_le (not_not.1 (not_or.1 h).1) hπ hx hk hk' (not_or.1 h).2)
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩

omit [DecidableEq Y] in
open scoped Classical in
/-- The `k'` port of `CollisionBad`. -/
theorem card_collisionBad_updateK'_le (hπ : PermGood π G) (hD : D ∉ CollisionBad π out)
    (hh : D.h.size ≤ t) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) {x' : X}
    (hx' : D.k' x' = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k' := Function.update D.k' x' (some y) } ∈ CollisionBad π out).card ≤
        (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + t := by
  have h : ¬ (¬ Good π D ∨ Collision π D out) := hD
  refine le_trans (Finset.card_le_card fun y hy ↦ ?_) ((card_bad_collision_updateK'_le
    (not_not.1 (not_or.1 h).1) hπ hx' hk hk' (not_or.1 h).2).trans (Nat.add_le_add_left hh _))
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩

omit [DecidableEq Y] in
open scoped Classical in
/-- The `k'` port of `PreimageBad`. -/
theorem card_preimageBad_updateK'_le (hπ : PermGood π G) {y0 : Y}
    (hD : D ∉ PreimageBad π out y0) (hh : D.h.size ≤ t) (hk : D.k.size ≤ t)
    (hk' : D.k'.size ≤ t) {x' : X} (hx' : D.k' x' = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k' := Function.update D.k' x' (some y) } ∈ PreimageBad π out y0).card ≤
        (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + t := by
  have h : ¬ (¬ Good π D ∨ ReachesOutput π D out y0) := hD
  refine le_trans (Finset.card_le_card fun y hy ↦ ?_) ((card_bad_reachesOutput_updateK'_le
    (not_not.1 (not_or.1 h).1) hπ hx' hk hk' (not_or.1 h).2).trans (Nat.add_le_add_left hh _))
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩

end Ports

end Quantum.Sponge

end
