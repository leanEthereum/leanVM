module

public import Quantum.Sphincs.Assembly.SrcBad
public import Quantum.Xmss.Assembly.CoversFull
public import Quantum.Xmss.Assembly.EndReads
public import Quantum.Xmss.Hybrid.GradedMasked

@[expose] public section

/-!
# leanSPHINCS's honest paths of distinct slots share no cell

The good-table predicate `PathsDisjoint` of the event side, stated on the public data and hidden
values (contract C4): no `k`-, `k'`- or `h`-cell of a round of one structural slot's path is the
same kind of cell of a round of another's (FORS leaves, nodes and roots compressions, and the chain
steps, one-time leaves and tree nodes of the three layers, each slot once).

The count is SrcBad's: `InjAll` (the cells of all in-table rounds injective) fails only with one of
PathBad's events, so `frac_srcColl_le` with no virtual paths bounds it by PathBad's
`N² / |X| + N² (G + 1) / |Z|`, `N = 8 |xI|`.

* `PathMeet w h v`: two distinct in-table slots' paths share a cell; it breaks `InjAll` on the
  in-table rounds (`not_injAll_of_pathMeet`); `PathsDisjoint` is its negation.
* `pathMeet_frac_le_keccak`: `PathMeet` for at most `2^-400` of the coordinates `((h, w), ρ)` and
  values `v` (any padding `ρ : W`; the bad permutations `2^-777`, the collisions `2^-407`);
  `uavg_not_pathsDisjoint_le`: the same as an average.
* The honest tables: `HonestPathsDisjoint L` (no read of one structural slot's honest input is at
  the cell of a read of another's); `pathMeet_of_not_disjoint`: a table violating it has
  `PathMeet` at its own datum (`tabW L`, `L.keys.1`, `valuePos L`), the reads of a slot's honest
  input being its rounds' cells (`point_of_mem_inputReads`); `honestPathsDisjoint_of`: disjoint
  paths at the table's own datum give `HonestPathsDisjoint L`.
-/

open scoped ENNReal

open Quantum Quantum.Sponge Quantum.SufCma Sphincs
open HashSig (Digest PublicParameter)
open Quantum.Xmss (X Z blocks)
open Quantum.Xmss.Hybrid (uavg uavg_ite_zero_one)
open Quantum.Xmss.Assembly (rnSt rnK rnR rnZ famK famR famZ rnds mem_rnds XW InjAll SColl
  frac_srcColl_le card_filter_le_add_of_imp inv_card_mul_card_filter_comp_fst rnCard_X rnCard_Z
  permTerm_le_keccak exists_round_of_mem_spongeReads)

namespace Quantum.Sphincs.Assembly

/-! ## Meeting paths -/

/-- **Two in-table paths meet** at `w = (PK.seed, π, k, k')`, `h` and the values `v`: a `k`-,
`k'`- or `h`-cell of a round of one structural slot's path is the same kind of cell of a round of
another's. -/
def PathMeet (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  ∃ s s', InTable s ∧ InTable s' ∧ s ≠ s' ∧ ∃ j < nBlk w.1 s, ∃ j' < nBlk w.1 s',
    sCellK w h s v j = sCellK w h s' v j' ∨ sCellR w h s v j = sCellR w h s' v j' ∨
      sCellZ w h s v j = sCellZ w h s' v j'

/-- **The honest paths of distinct structural slots share no cell.** -/
def PathsDisjoint (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  ¬PathMeet w h v

/-- **Meeting paths break the injectivity of the in-table rounds' cells.** -/
theorem not_injAll_of_pathMeet {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hm : PathMeet w h v) :
    ¬InjAll w.2.1 (xBlk w.1 v) (rnds xI (xLen w.1)) h w.2.2.1 w.2.2.2 := by
  obtain ⟨s, s', hs, hs', hne, j, hj, j', hj', he⟩ := hm
  obtain ⟨p, hp, rfl⟩ : ∃ p, InPos p ∧ outSlot p = s :=
    ⟨slotOutPos s, inPos_slotOutPos hs, outSlot_slotOutPos hs⟩
  obtain ⟨p', hp', rfl⟩ : ∃ p, InPos p ∧ outSlot p = s' :=
    ⟨slotOutPos s', inPos_slotOutPos hs', outSlot_slotOutPos hs'⟩
  have hmem : ((p, j) : ValPos × ℕ) ∈ (↑(rnds xI (xLen w.1)) : Set (ValPos × ℕ)) :=
    Finset.mem_coe.mpr (mem_rnds.mpr ⟨mem_xI.mpr hp, hj⟩)
  have hmem' : ((p', j') : ValPos × ℕ) ∈ (↑(rnds xI (xLen w.1)) : Set (ValPos × ℕ)) :=
    Finset.mem_coe.mpr (mem_rnds.mpr ⟨mem_xI.mpr hp', hj'⟩)
  have hpp : ((p, j) : ValPos × ℕ) = (p', j') → False := fun e ↦
    hne (congrArg outSlot (congrArg Prod.fst e))
  rintro ⟨hK, hR, hZ⟩
  rcases he with e | e | e
  · exact hpp (hK hmem hmem' e)
  · exact hpp (hR hmem hmem' e)
  · exact hpp (hZ hmem hmem' e)

/-! ## The fraction -/

section fraction

variable (W : Type) [Fintype W] [Nonempty W]

omit [Fintype W] [Nonempty W] in
/-- Meeting paths at the coordinates `sEquiv W (q, t)` are SrcBad's source-collision event with no
virtual paths. -/
theorem sColl_of_pathMeet (q : SQ W) (t : (Z → X) × (X → Z) × (X → Z))
    (hm : PathMeet (sEquiv W (q, t)).1.1.2 (sEquiv W (q, t)).1.1.1 (sEquiv W (q, t)).2) :
    SColl q.2.1 (xBlk q.1 q.2.2.2) (xLen q.1) xI ∅ t.1 t.2.1 t.2.2 :=
  Or.inl (not_injAll_of_pathMeet (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1) (v := q.2.2.2) hm)

/-- The in-table first blocks are distinct (with no virtual paths). -/
theorem xBlk_injOn_union (P : PublicParameter) (v : ValPos → Digest) :
    Set.InjOn (fun p ↦ xBlk P v p 0) ↑(xI ∪ (∅ : Finset ValPos)) := by
  rw [Finset.union_empty]
  exact xBlk_injOn P v

/-- The source-collision constant with no virtual paths is PathBad's. -/
theorem sCollConst_zero (N : ℕ) : N * N + 0 * (2 * (0 * (N + 0))) = N * N := by
  rw [Nat.zero_mul, Nat.add_zero]

open scoped Classical in
/-- `pathMeet_good_frac_le` with SrcBad's constant. -/
theorem pathMeet_good_frac_le₀ (G : ℕ) :
    (Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet y.1.1.2 y.1.1.1 y.2).card ≤
      ((8 * xI.card * (8 * xI.card) + 0 * (2 * (0 * (8 * xI.card + 0))) : ℕ) : ℝ≥0∞) /
          Fintype.card X +
        (((8 * xI.card * (8 * xI.card) + 0 * (2 * (0 * (8 * xI.card + 0)))) * (G + 1) : ℕ) :
          ℝ≥0∞) / Fintype.card Z :=
  frac_srcColl_le (sEquiv W) (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2.2) (fun q ↦ xLen q.1)
    (fun _ ↦ xI) (fun _ ↦ ∅) (fun q ↦ xBlk_injOn_union q.1 q.2.2.2) G _ 0 0
    (fun q ↦ card_rnds_xI_le q.1) (fun _ _ hw ↦ absurd hw (Finset.notMem_empty _))
    (fun _ ↦ Finset.card_empty.le) _ fun q t hb ↦ ⟨hb.1, sColl_of_pathMeet W q t hb.2⟩

open scoped Classical in
/-- **The path-meeting event on good permutations**: `PermGood π G ∧ PathMeet` for at most a
fraction `N² / |X| + N² (G + 1) / |Z|` of the coordinates, `N = 8 |xI|`. -/
theorem pathMeet_good_frac_le (G : ℕ) :
    (Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet y.1.1.2 y.1.1.1 y.2).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z := by
  have h := pathMeet_good_frac_le₀ W G
  rwa [sCollConst_zero] at h

open scoped Classical in
/-- **The path-meeting fraction of leanSPHINCS**: `PathMeet` for at most the bad permutations plus
`N² / |X| + N² (G + 1) / |Z|`, `N = 8 |xI|`. -/
theorem pathMeet_frac_le (G : ℕ) :
    (Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PathMeet y.1.1.2 y.1.1.1 y.2).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z) := by
  set N := Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦ PathMeet y.1.1.2 y.1.1.1 y.2)
    (fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦ ¬PermGood (pxPermEquiv W y).1 G)
    (fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
      PermGood y.1.1.2.2.1 G ∧ PathMeet y.1.1.2 y.1.1.1 y.2)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
        PathMeet y.1.1.2 y.1.1.1 y.2).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv W y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet y.1.1.2 y.1.1.1 y.2).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv W y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet y.1.1.2 y.1.1.1 y.2).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst (pxPermEquiv W) fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (pathMeet_good_frac_le W G)

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The path-meeting fraction at Keccak's sizes**: at most `2^-400` (with `G = 18`: the bad
permutations `2^-777`, the collisions `2^-407` from `|xI| ≤ 2^47`). -/
theorem pathMeet_frac_le_keccak :
    (Fintype.card ((((Z → X) × XW) × W) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
          PathMeet y.1.1.2 y.1.1.1 y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) := by
  refine ((pathMeet_frac_le W 18).trans (add_le_add permTerm_le_keccak
    (collTerms_le card_xI_le rnCard_X rnCard_Z))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777)
    (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 407)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

open scoped Classical in
/-- **The debt `pathsDisjoint` on the coordinates**: the coordinates whose in-table paths meet
weigh at most `2^-400`. -/
theorem uavg_not_pathsDisjoint_le :
    uavg (fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
        if PathsDisjoint y.1.1.2 y.1.1.1 y.2 then (0 : ℝ≥0∞) else 1) ≤
      (2 ^ 400 : ℝ≥0∞)⁻¹ := by
  rw [uavg_ite_zero_one]
  have hf : (Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
      ¬PathsDisjoint y.1.1.2 y.1.1.1 y.2) =
      Finset.univ.filter fun y : (((Z → X) × XW) × W) × (ValPos → Digest) ↦
        PathMeet y.1.1.2 y.1.1.1 y.2 :=
    Finset.filter_congr fun _ _ ↦ not_not
  rw [hf]
  refine (pathMeet_frac_le_keccak W).trans_eq ?_
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

end fraction

/-! ## The honest tables -/

/-- **The honest paths of distinct table slots share no cell**: no read of one structural slot's
honest input is at the cell of a read of another's. -/
def HonestPathsDisjoint (L : HonestTable) : Prop :=
  ∀ s s' i i', InTable s → InTable s' → s ≠ s' → L.honestInput s = some i →
    L.honestInput s' = some i' → ∀ e ∈ inputReads L.keys L.perm i,
      ∀ e' ∈ inputReads L.keys L.perm i', e.point ≠ e'.point

/-- The public data of a table: `PK.seed`, `π`, `k`, `k'`. -/
def tabW (L : HonestTable) : XW :=
  (L.publicSeed, L.perm, L.keys.2.1, L.keys.2.2)

/-- **The sponge states of a message are its path's.** -/
theorem absorb_take_eq_rnSt (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (msg : List X) :
    ∀ j, j ≤ msg.length →
      absorb (spongePerm (h, k, k') π) (msg.take j) = rnSt π h k k' (fun i ↦ msg.getD i 0) j
  | 0, _ => rfl
  | j + 1, hj => by
    have hg : msg.getD j 0 = msg[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      absorb_append_singleton, absorb_take_eq_rnSt π h k k' msg j (by omega), ← hg]
    rfl

/-- The reads of a round of a path are its `k`-, `k'`- and `h`-cells with their key values. -/
theorem roundReads_rnSt (π : Equiv.Perm (X × Z)) (h : Z → X) (k k' : X → Z) (b : ℕ → X)
    (j : ℕ) :
    roundReads π h k k' (rnSt π h k k' b j) (b j) =
      [.k (rnK π h k k' b j) (k (rnK π h k k' b j)),
        .k' (rnR π h k k' b j) (k' (rnR π h k k' b j)),
        .h (rnZ π h k k' b j) (h (rnZ π h k k' b j))] :=
  rfl

/-- **A read of a slot's input is at a cell of one of its rounds.** -/
theorem point_of_mem_inputReads (L : HonestTable) (s : Slot) {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm (slotInput L.publicSeed s (valuePos L))) :
    ∃ j < nBlk L.publicSeed s, e.point = .k (sCellK (tabW L) L.keys.1 s (valuePos L) j) ∨
      e.point = .k' (sCellR (tabW L) L.keys.1 s (valuePos L) j) ∨
      e.point = .h (sCellZ (tabW L) L.keys.1 s (valuePos L) j) := by
  obtain ⟨j, hj, hje⟩ :=
    exists_round_of_mem_spongeReads L.perm L.keys.1 L.keys.2.1 L.keys.2.2 _ he
  rw [absorb_take_eq_rnSt _ _ _ _ _ j hj.le] at hje
  rw [length_blocks_slotInput] at hj
  refine ⟨j, hj, ?_⟩
  have h3 := (congrArg (e ∈ ·) (roundReads_rnSt L.perm L.keys.1 L.keys.2.1 L.keys.2.2
    (slotBlk L.publicSeed s (valuePos L)) j)).mp hje
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
  rcases h3 with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **A table whose honest paths share a cell has meeting paths** at its own datum. -/
theorem pathMeet_of_not_disjoint (L : HonestTable) (hd : ¬HonestPathsDisjoint L) :
    PathMeet (tabW L) L.keys.1 (valuePos L) := by
  by_contra hm
  refine hd fun s s' i i' hs hs' hne hi hi' e he e' he' hpt ↦ hm ?_
  obtain rfl := Option.some.inj ((L.honestInput_eq_slotInput hs).symm.trans hi)
  obtain rfl := Option.some.inj ((L.honestInput_eq_slotInput hs').symm.trans hi')
  obtain ⟨j, hj, h1⟩ := point_of_mem_inputReads L s he
  obtain ⟨j', hj', h2⟩ := point_of_mem_inputReads L s' he'
  refine ⟨s, s', hs, hs', hne, j, hj, j', hj', ?_⟩
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    have hq := h1.symm.trans (hpt.trans h2) <;>
    first
    | exact Or.inl (SpongeQuery.k.inj hq)
    | exact Or.inr (Or.inl (SpongeQuery.k'.inj hq))
    | exact Or.inr (Or.inr (SpongeQuery.h.inj hq))
    | exact absurd hq (by simp)

/-- **Disjoint paths at a table's own datum make its honest paths disjoint.** -/
theorem honestPathsDisjoint_of (L : HonestTable)
    (hp : PathsDisjoint (tabW L) L.keys.1 (valuePos L)) : HonestPathsDisjoint L :=
  by_contra fun hd ↦ hp (pathMeet_of_not_disjoint L hd)

end Quantum.Sphincs.Assembly

end
