module

public import Quantum.Xmss.Assembly.TrialsOff
public import Quantum.Xmss.Assembly.CoversFull
public import Quantum.Xmss.Assembly.ProgSafe
public import Quantum.Xmss.Assembly.EndReads
public import Quantum.Xmss.Hybrid.GradedMasked

@[expose] public section

/-!
# The honest paths of distinct slots share no cell

Security's debt `pathsDisjoint`: the tables violating EndReads' `HonestPathsDisjoint` (a read of one
in-table slot's honest input is at the cell of a read of another's) weigh at most `2^-170`.

The count is SrcBad's: `InjAll` (the `k`-, `k'`- and `h`-cells of all rounds injective) fails only
with one of PathBad's events (`exists_ev_of_not_injAll`), so `frac_srcColl_le` with no virtual
paths bounds it by PathBad's `N² / |X| + N² (G + 1) / |Z|`.

**leanXMSS.**

* `PathMeet pub v`: two distinct in-table slots' paths share a `k`-, `k'`- or `h`-cell at the
  public datum `pub` and the values `v`; it breaks `InjAll` on the in-table rounds
  (`not_injAll_of_pathMeet`). `pathMeet_frac_le_keccak`: at most `2^-400` of the public data and
  hidden values (the bad permutations `2^-777`, the collisions `2^-401`).
* `pathMeet_of_not_disjoint`: a table violating `HonestPathsDisjoint` has `PathMeet` at its own
  datum (`pubOf L`, `valuePos L`), the reads of a slot's honest input being its rounds' cells
  (`point_of_mem_inputReads`). `pathMeet_fwd`, `pathMeet_of_r0G`: on ReparamR0's good set
  `r0G treeQ 18`, `PathMeet` holds at the coordinates (`cells_transfer_keys`).
* `disjoint_r0G_frac_le_keccak`: `r0G treeQ 18 ∧ ¬HonestPathsDisjoint` for at most `2^-400` of the
  padded tables; `disjoint_frac_le_keccak`: `¬HonestPathsDisjoint` for at most `2^-173` of the
  honest tables (with `r0G_frac_le_keccak`'s `2^-174`); `uavg_not_pathsDisjoint_le`: the debt, at
  `2^-170`.
-/

open scoped ENNReal

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Quantum.Xmss.Hybrid

/-! ## leanXMSS -/

section xmss

open HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel

/-! ### Meeting paths at the coordinates -/

/-- **Two in-table paths meet** at the public datum `pub` and the values `v`: a `k`-, `k'`- or
`h`-cell of a round of one in-table slot's honest path is the same kind of cell of a round of
another's. -/
def PathMeet (pub : Pub) (v : ValPos → Digest) : Prop :=
  ∃ s s', InTable s ∧ InTable s' ∧ s ≠ s' ∧ ∃ j < nBlocks pub s, ∃ j' < nBlocks pub s',
    srcCellK pub s v j = srcCellK pub s' v j' ∨ srcCellK' pub s v j = srcCellK' pub s' v j' ∨
      srcCellH pub s v j = srcCellH pub s' v j'

/-- **Meeting paths break the injectivity of the in-table rounds' cells.** -/
theorem not_injAll_of_pathMeet {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hm : PathMeet (xPub w h) v) :
    ¬InjAll w.2.1 (xBlk w.1 v) (rnds xI (xLen w.1)) h w.2.2.1 w.2.2.2 := by
  obtain ⟨s, s', hs, hs', hne, j, hj, j', hj', he⟩ := hm
  obtain ⟨p, hp, rfl⟩ : ∃ p, InPos p ∧ outSlot p = s :=
    ⟨slotOutPos s, inPos_slotOutPos hs, outSlot_slotOutPos hs⟩
  obtain ⟨p', hp', rfl⟩ : ∃ p, InPos p ∧ outSlot p = s' :=
    ⟨slotOutPos s', inPos_slotOutPos hs', outSlot_slotOutPos hs'⟩
  have hmem : ((p, j) : ValPos × ℕ) ∈ (↑(rnds xI (xLen w.1)) : Set (ValPos × ℕ)) := by
    refine Finset.mem_coe.mpr (mem_rnds.mpr ⟨mem_xI.mpr hp, ?_⟩)
    show j < xLen w.1 p
    rw [← nBlocks_xPub_eq w h p]
    exact hj
  have hmem' : ((p', j') : ValPos × ℕ) ∈ (↑(rnds xI (xLen w.1)) : Set (ValPos × ℕ)) := by
    refine Finset.mem_coe.mpr (mem_rnds.mpr ⟨mem_xI.mpr hp', ?_⟩)
    show j' < xLen w.1 p'
    rw [← nBlocks_xPub_eq w h p']
    exact hj'
  have hpp : ((p, j) : ValPos × ℕ) = (p', j') → False := fun e ↦
    hne (congrArg outSlot (congrArg Prod.fst e))
  rintro ⟨hK, hR, hZ⟩
  rcases he with e | e | e
  · have e' : famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, j) =
        famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p', j') :=
      (srcCellK_eq_rnK w h (outSlot p) v hj).symm.trans
        (e.trans (srcCellK_eq_rnK w h (outSlot p') v hj'))
    exact hpp (hK hmem hmem' e')
  · have e' : famR w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, j) =
        famR w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p', j') :=
      (srcCellK'_eq_rnR w h (outSlot p) v hj).symm.trans
        (e.trans (srcCellK'_eq_rnR w h (outSlot p') v hj'))
    exact hpp (hR hmem hmem' e')
  · have e' : famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p, j) =
        famZ w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (p', j') :=
      (roundH_fst_eq_rnZ w h (outSlot p) v hj).symm.trans
        (e.trans (roundH_fst_eq_rnZ w h (outSlot p') v hj'))
    exact hpp (hZ hmem hmem' e')

/-- Meeting paths at the coordinates `sEquiv (q, t)` are SrcBad's source-collision event with no
virtual paths. -/
theorem sColl_of_pathMeet (q : SQ) (t : (Z → X) × (X → Z) × (X → Z))
    (hm : PathMeet (pubX (sEquiv (q, t)).1) (sEquiv (q, t)).2) :
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
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet (pubX y.1) y.2).card ≤
      ((8 * xI.card * (8 * xI.card) + 0 * (2 * (0 * (8 * xI.card + 0))) : ℕ) : ℝ≥0∞) /
          Fintype.card X +
        (((8 * xI.card * (8 * xI.card) + 0 * (2 * (0 * (8 * xI.card + 0)))) * (G + 1) : ℕ) :
          ℝ≥0∞) / Fintype.card Z :=
  frac_srcColl_le sEquiv (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2.2) (fun q ↦ xLen q.1)
    (fun _ ↦ xI) (fun _ ↦ ∅) (fun q ↦ xBlk_injOn_union q.1 q.2.2.2) G _ 0 0
    (fun q ↦ card_rnds_xI_le q.1) (fun _ _ hw ↦ absurd hw (Finset.notMem_empty _))
    (fun _ ↦ Finset.card_empty.le) _ fun q t hb ↦ ⟨hb.1, sColl_of_pathMeet q t hb.2⟩

open scoped Classical in
/-- **The path-meeting event on good permutations**: `PermGood π G ∧ PathMeet` for at most a
fraction `N² / |X| + N² (G + 1) / |Z|` of the public data and hidden values, `N = 8 |xI|`
(SrcBad's `frac_srcColl_le` with no virtual paths). -/
theorem pathMeet_good_frac_le (G : ℕ) :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet (pubX y.1) y.2).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z := by
  have h := pathMeet_good_frac_le₀ G
  rwa [sCollConst_zero] at h

open scoped Classical in
/-- **The path-meeting fraction of leanXMSS**: `PathMeet` for at most the bad permutations plus
`N² / |X| + N² (G + 1) / |Z|`, `N = 8 |xI|`. -/
theorem pathMeet_frac_le (G : ℕ) :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ PathMeet (pubX y.1) y.2).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z) := by
  set N := Fintype.card (PX × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : PX × (ValPos → Digest) ↦ PathMeet (pubX y.1) y.2)
    (fun y : PX × (ValPos → Digest) ↦ ¬PermGood (pxPermEquiv y).1 G)
    (fun y : PX × (ValPos → Digest) ↦ PermGood y.1.1.2.2.1 G ∧ PathMeet (pubX y.1) y.2)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ PathMeet (pubX y.1) y.2).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet (pubX y.1) y.2).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          ¬PermGood (pxPermEquiv y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
          PermGood y.1.1.2.2.1 G ∧ PathMeet (pubX y.1) y.2).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst pxPermEquiv fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (pathMeet_good_frac_le G)

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The path-meeting fraction at Keccak's sizes**: at most `2^-400` (with `G = 18`: the bad
permutations `2^-777`, the collisions `2^-401` from `|xI| ≤ 498 · 2^32`). -/
theorem pathMeet_frac_le_keccak :
    (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ PathMeet (pubX y.1) y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) := by
  refine ((pathMeet_frac_le 18).trans (add_le_add permTerm_le_keccak
    (collTerms_le card_xI_le rnCard_X rnCard_Z))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777)
    (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 401)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

/-! ### The honest tables -/

/-- The honest input of an in-table slot is the template's at the table's own datum. -/
theorem honestInput_eq_slotInput (L : HonestTable) {s : Slot} (hs : InTable s) :
    L.honestInput s = some (slotInput (pubOf L) s (valuePos L)) := by
  obtain ⟨l, e, w, -, hsl⟩ := exists_layerSlots hs
  rw [HonestTable.honestInput, ite_eq_left hs, slotInput, slotPayload_eq L hsl fun _ _ ↦ rfl]
  rfl

/-- **A read of a slot's input is at a cell of one of its rounds.** -/
theorem point_of_mem_inputReads (L : HonestTable) (s : Slot) {e : SpongeRead X Z}
    (he : e ∈ inputReads L.keys L.perm (slotInput (pubOf L) s (valuePos L))) :
    ∃ j < nBlocks (pubOf L) s, e.point = .k (srcCellK (pubOf L) s (valuePos L) j) ∨
      e.point = .k' (srcCellK' (pubOf L) s (valuePos L) j) ∨
      e.point = .h (srcCellH (pubOf L) s (valuePos L) j) := by
  obtain ⟨j, hj, hje⟩ :=
    exists_round_of_mem_spongeReads L.perm L.keys.1 L.keys.2.1 L.keys.2.2 _ he
  rw [length_blocks_slotInput] at hj
  refine ⟨j, hj, ?_⟩
  have h3 := (congrArg (e ∈ ·) (roundReads_slot L s (valuePos L) j)).mp hje
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
  rcases h3 with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **A table whose honest paths share a cell has meeting paths** at its own datum. -/
theorem pathMeet_of_not_disjoint (L : HonestTable) (hd : ¬HonestPathsDisjoint L) :
    PathMeet (pubOf L) (valuePos L) := by
  by_contra hm
  refine hd fun s s' i i' hs hs' hne hi hi' e he e' he' hpt ↦ hm ?_
  obtain rfl := Option.some.inj ((honestInput_eq_slotInput L hs).symm.trans hi)
  obtain rfl := Option.some.inj ((honestInput_eq_slotInput L hs').symm.trans hi')
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

/-- **Meeting paths transfer to the coordinates** of Reparam's table `θ` of the table `L`, at
public keys agreeing with the table's on its paths (`cells_transfer_keys`). -/
theorem pathMeet_fwd (L : HonestTable) (θ : RTab) (hθ : XGood θ) (hP : θ.2.1 = L.param)
    (hπ : θ.2.2.1 = L.perm)
    (hu : ∀ l e i, θ.1.2 (.chain l e i ⟨0, by decide⟩) = L.chainStart l e i)
    (hav : ∀ s, InTable s → ∀ j < nBlocks (pubOf L) s,
      KeysAt (pubOf L) (xPub θ.2 θ.1.1) s (valuePos L) j)
    (hm : PathMeet (pubOf L) (valuePos L)) :
    PathMeet (xPub (fwd xmssFix xO θ).1.2 (fwd xmssFix xO θ).1.1) (fwd xmssFix xO θ).2 := by
  obtain ⟨⟨h, u⟩, w⟩ := θ
  have hnb : nBlocks (xPub w (fwd xmssFix xO ((h, u), w)).1.1) = nBlocks (pubOf L) :=
    nBlocks_eq_of_param hP
  obtain ⟨s, s', hs, hs', hne, j, hj, j', hj', he⟩ := hm
  obtain ⟨k1, k1', h1⟩ := cells_transfer_keys L hθ hP hπ hu hav hs hj
  obtain ⟨k2, k2', h2⟩ := cells_transfer_keys L hθ hP hπ hu hav hs' hj'
  show PathMeet (xPub w (fwd xmssFix xO ((h, u), w)).1.1) (xVal w h u)
  refine ⟨s, s', hs, hs', hne, j, by rw [hnb]; exact hj, j', by rw [hnb]; exact hj', ?_⟩
  rcases he with e | e | e
  · exact Or.inl (k1.trans (e.trans k2.symm))
  · exact Or.inr (Or.inl (k1'.trans (e.trans k2'.symm)))
  · exact Or.inr (Or.inr (h1.trans (e.trans h2.symm)))

/-- **On ReparamR0's good set, honest paths sharing a cell meet at the coordinates.** -/
theorem pathMeet_of_r0G {t : HonestTable × RE} (ht : r0G treeQ 18 t)
    (hd : ¬HonestPathsDisjoint t.1) :
    PathMeet (pubX ((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2))
      (fwd xmssFix xO (r0Phi t).1.1).2 :=
  pathMeet_fwd t.1 (r0Phi t).1.1 ht.2.2.1 (r0G_param ht) (r0Phi_perm t) (r0G_start ht)
    (r0G_keys hashesSlots_treeQ ht) (pathMeet_of_not_disjoint t.1 hd)

open scoped Classical in
/-- **The good tables whose honest paths share a cell** are at most `PathMeet`'s fraction of the
public data and hidden values (the coordinates of Reparam-good tables are distinct). -/
theorem disjoint_r0G_frac_le :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬HonestPathsDisjoint t.1).card ≤
      (Fintype.card (PX × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : PX × (ValPos → Digest) ↦ PathMeet (pubX y.1) y.2).card := by
  have hC := card_filter_le_of_injOn
    (fun t ↦ ((((fwd xmssFix xO (r0Phi t).1.1).1, (r0Phi t).1.2), (fwd xmssFix xO (r0Phi t).1.1).2),
      (r0Phi t).2) :
        HonestTable × RE → (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS))
    (fun t ↦ r0G treeQ 18 t ∧ ¬HonestPathsDisjoint t.1)
    (fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
      PathMeet (pubX z.1.1) z.1.2)
    (fun _ h ↦ pathMeet_of_r0G h.1 h.2) fun t₁ t₂ h₁ h₂ e ↦ by
      have hf : fwd xmssFix xO (r0Phi t₁).1.1 = fwd xmssFix xO (r0Phi t₂).1.1 :=
        Prod.ext (congrArg (fun z ↦ z.1.1.1) e :) (congrArg (fun z ↦ z.1.2) e :)
      have hθ := injOn_fwd xO_consistent (good_of_xGood h₁.1.2.2.1) (good_of_xGood h₂.1.2.2.1) hf
      exact r0Phi.injective (Prod.ext (Prod.ext hθ (congrArg (fun z ↦ z.1.1.2) e :))
        (congrArg (fun z ↦ z.2) e :))
  have hP := card_filter_pad (W := CoinSlots R0.RLabel × SeedKS)
    (fun y : PX × (ValPos → Digest) ↦ PathMeet (pubX y.1) y.2)
  have hN : Fintype.card (HonestTable × RE) =
      Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr (r0Phi.trans (pxEquiv.symm.prodCongr (Equiv.refl _)))
  calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬HonestPathsDisjoint t.1).card
      ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun z : (PX × (ValPos → Digest)) × (CoinSlots R0.RLabel × SeedKS) ↦
            PathMeet (pubX z.1.1) z.1.2).card := by
        gcongr
    _ = (((Fintype.card (PX × (ValPos → Digest)) * Fintype.card (CoinSlots R0.RLabel × SeedKS) :
          ℕ) : ℝ≥0∞))⁻¹ * (((Finset.univ.filter fun y : PX × (ValPos → Digest) ↦
            PathMeet (pubX y.1) y.2).card * Fintype.card (CoinSlots R0.RLabel × SeedKS) : ℕ) :
              ℝ≥0∞) := by
        rw [hP, hN, Nat.cast_mul, Nat.cast_mul]
    _ = _ := natCast_mul_inv_mul_cancel _ _ _ Fintype.card_ne_zero

open scoped Classical in
/-- **The good tables whose honest paths share a cell at Keccak's sizes**: at most `2^-400` of the
padded tables are in ReparamR0's good set `r0G treeQ 18` and violate `HonestPathsDisjoint`. -/
theorem disjoint_r0G_frac_le_keccak :
    (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬HonestPathsDisjoint t.1).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) :=
  disjoint_r0G_frac_le.trans pathMeet_frac_le_keccak

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The honest tables whose honest paths share a cell** at Keccak's sizes: at most `2^-173` (the
tables outside `r0G treeQ 18`, `2^-174`, and the good ones violating it, `2^-400`). -/
theorem disjoint_frac_le_keccak :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun L : HonestTable ↦ ¬HonestPathsDisjoint L).card ≤
      ENNReal.ofReal (1 / 2 ^ 173) := by
  have hE := inv_card_mul_card_filter_comp_fst (Equiv.refl (HonestTable × RE))
    fun L ↦ ¬HonestPathsDisjoint L
  have hsub := card_filter_le_add_of_imp (fun t : HonestTable × RE ↦ ¬HonestPathsDisjoint t.1)
    (fun t ↦ ¬r0G treeQ 18 t) (fun t ↦ r0G treeQ 18 t ∧ ¬HonestPathsDisjoint t.1) fun t ht ↦ by
      by_cases hg : r0G treeQ 18 t
      · exact Or.inr ⟨hg, ht⟩
      · exact Or.inl hg
  rw [mul_comm, ← div_eq_mul_inv, ← hE]
  calc (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun t : HonestTable × RE ↦ ¬HonestPathsDisjoint t.1).card
      ≤ (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (((Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card : ℝ≥0∞) +
            (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬HonestPathsDisjoint t.1).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ ¬r0G treeQ 18 t).card +
        (Fintype.card (HonestTable × RE) : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun t ↦ r0G treeQ 18 t ∧ ¬HonestPathsDisjoint t.1).card :=
        mul_add _ _ _
    _ ≤ ENNReal.ofReal (1 / 2 ^ 174) + ENNReal.ofReal (1 / 2 ^ 400) :=
        add_le_add r0G_frac_le_keccak disjoint_r0G_frac_le_keccak
    _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)

open scoped Classical in
/-- **Security's debt `pathsDisjoint`**: the tables whose honest paths share a cell weigh at most
`2^-170` (`disjoint_frac_le_keccak`, `2^-173`). -/
theorem uavg_not_pathsDisjoint_le :
    uavg (fun L : HonestTable ↦ if HonestPathsDisjoint L then (0 : ℝ≥0∞) else 1) ≤
      (2 ^ 170 : ℝ≥0∞)⁻¹ := by
  rw [uavg_ite_zero_one]
  refine disjoint_frac_le_keccak.trans ((ENNReal.ofReal_le_ofReal
    (by norm_num : (1 : ℝ) / 2 ^ 173 ≤ 1 / 2 ^ 170)).trans_eq ?_)
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

end xmss

end Quantum.Xmss.Assembly

end
