module

public import Quantum.Sponge.Bound

@[expose] public section

/-!
# Target events: a target output per tail

`TargetBad π out tgt` generalizes `PreimageBad π out y0` (Quantum.Sponge.Outputs) from one output
for all tails to a target `tgt t` per tail `t` (none for tails without a target): the databases
that are bad or in which some tail reaches its own target. It is upward closed and misses the empty
databases. A fresh `h` cell runs through at most one head-tail of a good database, which has at
most one target, so at most `F` answers (the fiber bound of `out`) flip a database into the set;
for `k` and `k'`, outside the answers of `card_bad_le_of_tails` the paths are the old ones, which
gives the counts of `preimageRateBound` (`freshBound_targetBad`).
-/

namespace Quantum.Sponge

open Quantum
open scoped ENNReal

variable {X Z Y : Type} [AddCommGroup X] [AddCommGroup Z] {π : Equiv.Perm (X × Z)} {out : X → Y}
  {tgt : List X → Option Y} {D D' : Dbs X Z}

/-- The databases that are bad or in which some tail `t` reaches its target `tgt t`. -/
def TargetBad (π : Equiv.Perm (X × Z)) (out : X → Y) (tgt : List X → Option Y) :
    Set (Dbs X Z) :=
  {D | ¬ Good π D ∨ ∃ t y, tgt t = some y ∧ Reaches π D out t y}

theorem not_mem_targetBad_iff :
    D ∉ TargetBad π out tgt ↔ Good π D ∧ ∀ t y, tgt t = some y → ¬ Reaches π D out t y := by
  simp [TargetBad]

/-- Fewer targets, fewer members. -/
theorem targetBad_mono {tgt' : List X → Option Y} (h : ∀ t y, tgt' t = some y → tgt t = some y) :
    TargetBad π out tgt' ⊆ TargetBad π out tgt :=
  fun _ hD ↦ hD.imp_right fun ⟨t, y, ht, hr⟩ ↦ ⟨t, y, h t y ht, hr⟩

theorem TargetBad.mono (hE : ExtendsAll D D') (hD' : D' ∈ TargetBad π out tgt) :
    D ∈ TargetBad π out tgt :=
  hD'.imp (fun hb hg ↦ hb (hg.of_extendsAll hE)) fun ⟨t, y, ht, hr⟩ ↦ ⟨t, y, ht, hr.mono hE⟩

theorem upClosed_targetBad [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] :
    UpClosed (TargetBad π out tgt) where
  h D hD _ u hz := TargetBad.mono (extendsAll_update_h D hz u) hD
  k D hD _ u hx := TargetBad.mono (extendsAll_update_k D hx u) hD
  k' D hD _ u hx := TargetBad.mono (extendsAll_update_k' D hx u) hD

theorem not_mem_targetBad_emptyDbs : (emptyDbs : Dbs X Z) ∉ TargetBad π out tgt := by
  rintro (h | ⟨t, y, -, z, xi, w, -, hw, -⟩)
  · exact h good_emptyDbs
  · exact absurd hw (by simp [emptyDbs, Database.empty])

/-! ## Per-port flip counts -/

section Ports

variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] {t G F : ℕ}

omit [Fintype Z] [DecidableEq X] in
open scoped Classical in
/-- The `h` port: at most `F` values of a fresh cell flip into `TargetBad`. The new paths run
through the fresh capacity, whose head-tail in the good database is unique and has one target, so
the values lie in one translate of a fiber of `out`. -/
theorem card_targetBad_updateH_le [DecidableEq Y]
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F)
    (hD : D ∉ TargetBad π out tgt) {z : Z} (hz : D.h z = none) :
    (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ TargetBad π out tgt).card ≤ F := by
  obtain ⟨hG, hT⟩ := not_mem_targetBad_iff.1 hD
  /- A flipping value reaches the target of a head-tail of `z`. -/
  have key : ∀ u, { D with h := Function.update D.h z (some u) } ∈ TargetBad π out tgt →
      ∃ s xi y, IsHeadTail π D s z xi ∧ tgt s = some y ∧ y = out (xi + u) := by
    rintro u (h | ⟨s, y, hs, hr⟩)
    · exact absurd ((good_update_h_iff _).2 hG) h
    rcases (reaches_updateH_iff hz).1 hr with hr | ⟨xi, hi, he⟩
    · exact absurd hr (hT s y hs)
    · exact ⟨s, xi, y, hi, hs, he⟩
  rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun u : X ↦
      { D with h := Function.update D.h z (some u) } ∈ TargetBad π out tgt) with he | ⟨u0, hu0⟩
  · simp [he]
  obtain ⟨s0, xi0, y0, hi0, hs0, -⟩ := key u0 (Finset.mem_filter.1 hu0).2
  refine card_le_of_out_translate hF xi0 y0 fun u hu ↦ ?_
  obtain ⟨s, xi, y, hi, hs, he⟩ := key u (Finset.mem_filter.1 hu).2
  obtain ⟨rfl, rfl⟩ := hG.isHeadTail_unique hi hi0
  obtain rfl := Option.some_injective _ (hs.symm.trans hs0)
  exact he.symm

open scoped Classical in
/-- The `k` port: outside `badAttachK` the tails, hence the paths, are the old ones. -/
theorem card_targetBad_updateK_le (hπ : PermGood π G) (hD : D ∉ TargetBad π out tgt)
    (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) {x : X} (hx : D.k x = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k := Function.update D.k x (some y) } ∈ TargetBad π out tgt).card ≤
        (t + 1) * ((t + 1) * t + 2 * t) * G := by
  obtain ⟨hG, hT⟩ := not_mem_targetBad_iff.1 hD
  refine le_trans (Finset.card_le_card fun y hy ↦ ?_)
    ((card_bad_le_of_tails (P := fun D ↦ ∃ s y, tgt s = some y ∧ Reaches π D out s y)
      (fun _ hE hh hT' ⟨s, y, hs, hr⟩ ↦ ⟨s, y, hs, hr.of_tails hE hh hT'⟩)
      (fun ⟨s, y, hs, hr⟩ ↦ hT s y hs hr) _ _ (fun _ ↦ extends_update_k hx) (fun _ ↦ rfl)
      fun _ hy ↦ updateK_tails hG hx hy).trans (card_badAttachK_le hG hπ hk hk'))
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩

open scoped Classical in
/-- The `k'` port: outside `badCompleteOutK'` the only new tail ends at a capacity outside the
domain of `D.h`, so no new path reaches an output. -/
theorem card_targetBad_updateK'_le (hπ : PermGood π G) (hD : D ∉ TargetBad π out tgt)
    (hh : D.h.size ≤ t) (hk : D.k.size ≤ t) (hk' : D.k'.size ≤ t) {x' : X}
    (hx' : D.k' x' = none) :
    (Finset.univ.filter fun y : Z ↦
      { D with k' := Function.update D.k' x' (some y) } ∈ TargetBad π out tgt).card ≤
        (t + 1) + t * ((t + 1) * t + t + 1) * G + t * t * G + t := by
  obtain ⟨hG, hT⟩ := not_mem_targetBad_iff.1 hD
  refine le_trans (Finset.card_le_card fun y hy ↦ ?_)
    (((card_bad_le_of_tails (P := fun D ↦ ∃ s y, tgt s = some y ∧ Reaches π D out s y)
      (fun _ hE hh hT' ⟨s, y, hs, hr⟩ ↦ ⟨s, y, hs, hr.of_tails hE hh hT'⟩)
      (fun ⟨s, y, hs, hr⟩ ↦ hT s y hs hr) _ _ (fun _ ↦ extends_update_k' hx') (fun _ ↦ rfl)
      fun _ hy ↦ updateK'_tails hG hx' hy).trans
        (card_badCompleteOutK'_le hG hπ x' hk hk')).trans (Nat.add_le_add_left hh _))
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hy).2⟩

open scoped Classical in
/-- The fresh-cell bound of `TargetBad`: the rates of `preimageRateBound`. -/
theorem freshBound_targetBad (hπ : PermGood π G)
    (hF : ∀ y, (Finset.univ.filter fun x ↦ out x = y).card ≤ F) (T : ℕ) :
    FreshBound (TargetBad π out tgt) T (preimageRateBound (X := X) (Z := Z) T G F) where
  h D hD _ _ _ z hz := by
    refine le_trans ?_ (le_max_left _ _)
    gcongr
    exact_mod_cast card_targetBad_updateH_le hF hD hz
  k D hD _ hk hk' x hx := by
    refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_targetBad_updateK_le hπ hD hk.le hk'.le hx
  k' D hD hh hk hk' x hx := by
    refine le_trans ?_ ((le_max_right _ _).trans (le_max_right _ _))
    gcongr
    exact_mod_cast card_targetBad_updateK'_le hπ hD hh.le hk.le hk'.le hx

end Ports

end Quantum.Sponge

end
