module

public import Quantum.Sponge.Outputs
public import Quantum.Sponge.Oracle

@[expose] public section

/-!
# The collision and preimage events through the compressed oracle

The sets `CollisionBad π out` and `PreimageBad π out y0` (Quantum.Sponge.Outputs) are upward closed
and miss the empty databases, and their per-port single-update counts give a `FreshBound`, so the
event bound of Quantum.Sponge.Oracle.Event applies: a program of `T` calls to the three random
functions ends with its compressed database bad, or holding a collision (a path to `y0`), with
weight at most `6 T² ε`, for `π` good with bound `G` and `ε` the largest per-port fraction.
-/

namespace Quantum.Sponge

open Quantum
open scoped ENNReal

variable {X Z Y : Type} {π : Equiv.Perm (X × Z)} {out : X → Y}

section Update

theorem extendsAll_update_h [DecidableEq Z] (D : Dbs X Z) {z : Z} (hz : D.h z = none) (u : X) :
    ExtendsAll { D with h := Function.update D.h z (some u) } D := by
  refine ⟨⟨fun _ _ h ↦ h, fun _ _ h ↦ h⟩, fun z' w h ↦ ?_⟩
  by_cases hz' : z' = z
  · subst hz'; simp [hz] at h
  · simp [Function.update_of_ne hz', h]

theorem extendsAll_update_k [DecidableEq X] (D : Dbs X Z) {x : X} (hx : D.k x = none) (u : Z) :
    ExtendsAll { D with k := Function.update D.k x (some u) } D := by
  refine ⟨⟨fun x' a h ↦ ?_, fun _ _ h ↦ h⟩, fun _ _ h ↦ h⟩
  by_cases hx' : x' = x
  · subst hx'; simp [hx] at h
  · simp [Function.update_of_ne hx', h]

theorem extendsAll_update_k' [DecidableEq X] (D : Dbs X Z) {x : X} (hx : D.k' x = none) (u : Z) :
    ExtendsAll { D with k' := Function.update D.k' x (some u) } D := by
  refine ⟨⟨fun _ _ h ↦ h, fun x' b h ↦ ?_⟩, fun _ _ h ↦ h⟩
  by_cases hx' : x' = x
  · subst hx'; simp [hx] at h
  · simp [Function.update_of_ne hx', h]

/-- A database outside `S` stays outside after removing cells; inside, it stays inside after
adding them. -/
private theorem mem_of_extendsAll [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
    {S : Set (Dbs X Z)} (hS : ∀ D D', ExtendsAll D D' → D' ∈ S → D ∈ S) : UpClosed S where
  h D hD _ u hz := hS _ D (extendsAll_update_h D hz u) hD
  k D hD _ u hx := hS _ D (extendsAll_update_k D hx u) hD
  k' D hD _ u hx := hS _ D (extendsAll_update_k' D hx u) hD

variable [AddCommGroup X] [AddCommGroup Z]

theorem upClosed_collisionBad [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] :
    UpClosed (CollisionBad π out) :=
  mem_of_extendsAll fun _ _ hE hD ↦ hD.imp (fun hb hg ↦ hb (hg.of_extendsAll hE))
    (Collision.mono hE)

theorem upClosed_preimageBad [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] (y0 : Y) :
    UpClosed (PreimageBad π out y0) :=
  mem_of_extendsAll fun _ _ hE hD ↦ hD.imp (fun hb hg ↦ hb (hg.of_extendsAll hE))
    (ReachesOutput.mono hE)

end Update

/-- The empty databases: only the empty tail, no intermediate pair, no `h` cell. -/
def emptyDbs : Dbs X Z := ⟨Database.empty, Database.empty, Database.empty⟩

theorem isTail_emptyDbs [AddCommGroup Z] {t : List X} {z : Z} (h : IsTail π emptyDbs t z) :
    t = [] ∧ z = 0 := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | snoc _ ha => exact absurd ha (by simp [emptyDbs, Database.empty])

theorem good_emptyDbs [AddCommGroup Z] : Good π (emptyDbs : Dbs X Z) := by
  refine ⟨fun z t t' h h' ↦ (isTail_emptyDbs h).1.trans (isTail_emptyDbs h').1.symm, ?_⟩
  rintro s ⟨xp, zp, a, -, ha, -⟩
  exact absurd ha (by simp [emptyDbs, Database.empty])

variable [AddCommGroup X] [AddCommGroup Z]

theorem not_mem_collisionBad_emptyDbs : (emptyDbs : Dbs X Z) ∉ CollisionBad π out := by
  rintro (h | ⟨t, t', y, -, ⟨z, xi, w, -, hw, -⟩, -⟩)
  · exact h good_emptyDbs
  · exact absurd hw (by simp [emptyDbs, Database.empty])

theorem not_mem_preimageBad_emptyDbs (y0 : Y) : (emptyDbs : Dbs X Z) ∉ PreimageBad π out y0 := by
  rintro (h | ⟨t, z, xi, w, -, hw, -⟩)
  · exact h good_emptyDbs
  · exact absurd hw (by simp [emptyDbs, Database.empty])

section Fresh

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [DecidableEq Y] {G F : ℕ}

/-- The largest per-port fraction of fresh answers entering `CollisionBad`, for databases below
`T` entries: `T F / |X|` for `h`, and the `k`, `k'` counts over `|Z|`. -/
noncomputable def collisionRateBound (T G F : ℕ) : ℝ≥0∞ :=
  max ((T * F : ℕ) / Fintype.card X : ℝ≥0∞)
    (max (((T + 1) * ((T + 1) * T + 2 * T) * G : ℕ) / Fintype.card Z : ℝ≥0∞)
      (((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T : ℕ) / Fintype.card Z : ℝ≥0∞))

open scoped Classical in
theorem freshBound_collisionBad (hπ : PermGood π G)
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (T : ℕ) :
    FreshBound (CollisionBad π out) T (collisionRateBound (X := X) (Z := Z) T G F) where
  h D hD hh _ _ z hz := by
    refine le_trans ?_ (le_max_left _ _)
    gcongr
    exact_mod_cast card_collisionBad_updateH_le hF hD hh.le hz
  k D hD _ hk hk' x hx := by
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_collisionBad_updateK_le hπ hD hk.le hk'.le hx
  k' D hD hh hk hk' x hx := by
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_collisionBad_updateK'_le hπ hD hh.le hk.le hk'.le hx

end Fresh

section FreshPreimage

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {G F : ℕ}

/-- The largest per-port fraction of fresh answers entering `PreimageBad`: `F / |X|` for `h`, and
the `k`, `k'` counts over `|Z|`. -/
noncomputable def preimageRateBound (T G F : ℕ) : ℝ≥0∞ :=
  max ((F : ℕ) / Fintype.card X : ℝ≥0∞)
    (max (((T + 1) * ((T + 1) * T + 2 * T) * G : ℕ) / Fintype.card Z : ℝ≥0∞)
      (((T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T : ℕ) / Fintype.card Z : ℝ≥0∞))

open scoped Classical in
theorem freshBound_preimageBad (hπ : PermGood π G)
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (y0 : Y) (T : ℕ) :
    FreshBound (PreimageBad π out y0) T (preimageRateBound (X := X) (Z := Z) T G F) where
  h D hD _ _ _ z hz := by
    refine le_trans ?_ (le_max_left _ _)
    gcongr
    exact_mod_cast card_preimageBad_updateH_le hF hD hz
  k D hD _ hk hk' x hx := by
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_preimageBad_updateK_le hπ hD hk.le hk'.le hx
  k' D hD hh hk hk' x hx := by
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_preimageBad_updateK'_le hπ hD hh.le hk.le hk'.le hx

end FreshPreimage

end Quantum.Sponge

end
