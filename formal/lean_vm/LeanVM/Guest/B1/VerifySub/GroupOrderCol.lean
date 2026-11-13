/-
  LeanVM.Guest.B1.VerifySub.GroupOrderCol

  `Hints.colGroupOrder` is `certify_placement`'s honest group order: the committed columns sorted by their placements' offsets, by group, are the groups in `stackOffsets`' order (`cpGOrd`).
-/

module

public import LeanVM.Guest.B1.VerifySub.GroupOrder
public import LeanVM.Guest.B1.VerifySub.GroupOrderData
public import LeanVM.Guest.B1.Placement.CertifyComplete
public import LeanVM.Guest.B1.Terminal.Layout

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Guest.B1.Tables

@[expose] public section

theorem count_eq_gen {n : ℕ} (h : n < 2 ^ 64) : Hints.count n = gen ^ n := by
  rw [Hints.count, gpowE, gpowK_eq (by unfold u128Bound; omega), gen_pow_eq_ofK]

theorem map_count_eq_gen {l : List ℕ} (h : ∀ n ∈ l, n < 2 ^ 64) : l.map Hints.count = l.map (gen ^ ·) :=
  List.map_congr_left fun n hn => count_eq_gen (h n hn)

theorem placementsOf_length (kappas : List ℕ) : (placementsOf kappas).1.length = kappas.length := by
  unfold placementsOf
  simp

/-- **`colGroupOrder` is `certify_placement`'s honest group order**, as indices. -/
theorem colGroupOrder_eq_count {layout : Layout} {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6)
    (hP : layout.placements = (placementsOf (columnKappas lm guestLogBytecode hs)).1) :
    Hints.colGroupOrder layout = (cpGOrd lm hs).map Hints.count := by
  have hk := columnKappas_length lm guestLogBytecode hs
  have hcols : Hints.committedColumns layout = committedCols 158 := by
    unfold Hints.committedColumns
    rw [hP, placementsOf_length, hk]
    rfl
  have hKs : (cpKs lm hs).length = 94 := by rw [cpKs_eq hl]; simp
  have h94 : (committedCols 158).length = 94 := committedCols_158_length
  have hκ : ∀ j < 9, ∀ x, cpC0 j ≤ x → x < cpC0 (j + 1) → (cpKs lm hs).getD x 0 = cpKg lm hs j := by
    intro j hj x h1 h2
    have hx : x < 94 := lt_of_lt_of_le h2 (cpC0_le j hj)
    obtain ⟨e1, e2⟩ := cp_group_const j hj x hx h1 h2
    rw [cpKs_eq hl, List.getD_eq_getElem _ _ (by simpa using hx), List.getElem_map, List.getElem_range]
    simp only [cpKc, cpKg, e1, e2, cpSrc, cpAdj]
  have h := runHeads_sortOff (cpKs lm hs) (m := 9) cpC0 (cpKg lm hs) 0 (colGroupsH.getD · 0)
    (fun i => (layout.placement ((committedCols 158).getD i 0)).index) cpC0_zero (by rw [hKs]; rfl) cpC0_lt hκ
    (fun j hj x h1 h2 => (colGroupsH_eq j hj x (lt_of_lt_of_le h2 (cpC0_le j hj)) h1 h2).trans (Nat.zero_add j).symm)
    (fun i hi => by
      rw [placement_committed hk hP (by rw [hKs] at hi; exact hi)]
      rfl)
  rw [hKs] at h
  simp only [Nat.zero_add, List.map_id'] at h
  dsimp only [Hints.colGroupOrder]
  rw [hcols, h94]
  exact congrArg (List.map Hints.count) h

theorem cpGOrd_lt {lm : ℕ} {hs : List ℕ} : ∀ n ∈ cpGOrd lm hs, n < 9 := fun _ hn =>
  List.mem_range.mp ((List.mergeSort_perm _ _).subset hn)

/-- **`colGroupOrder` is `certify_placement`'s honest group order.** -/
theorem colGroupOrder_eq {layout : Layout} {lm : ℕ} {hs : List ℕ} (hl : hs.length = 6)
    (hP : layout.placements = (placementsOf (columnKappas lm guestLogBytecode hs)).1) :
    Hints.colGroupOrder layout = (cpGOrd lm hs).map (gen ^ ·) := by
  rw [colGroupOrder_eq_count hl hP, map_count_eq_gen fun n hn => by have := cpGOrd_lt n hn; omega]

end
end LeanVM.Guest.B1.VerifySub
