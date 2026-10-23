/-
  LeanVM.Guest.B1.Tables.VtZcC

  `verify_tables`' table sumcheck window completes (`VtZcComplete`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesC3

/-!
# The table sumcheck's window, complete (G:1690-1742)

The window's items run forward from the oracle `vtHvZc` (`g^n` and the three pointers): each
log-height's check reads `g^τ` and range-checks `g^(n - τ)`, the product of the `g^n + g^τ` is
zero at the largest one, `g^(μ - n)` is range-checked, `ξ` is the squeeze's challenge, the bus
target is the first round's claim, and the two loops run on the honest buffers
(`loop79_complete` on `ZcRound`, `loop80_complete` on `PeqBody`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig

@[expose] public section

theorem flatMapK_length {α : Type} (c : ℕ) (g : ℕ → List α) :
    ∀ m, (∀ r < m, (g r).length = c) → ((List.range m).flatMap g).length = c * m
  | 0, _ => by simp
  | m + 1, hg => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      flatMapK_length c g m (fun r hr => hg r (by omega))]
    simp [hg m (by omega)]; ring

/-- Entry `c·r + k` of a list of `c`-word blocks. -/
theorem flatMapK_get {α : Type} (c : ℕ) (g : ℕ → List α) :
    ∀ m, (∀ r < m, (g r).length = c) → ∀ r k, r < m → k < c →
      ((List.range m).flatMap g)[c * r + k]? = (g r)[k]?
  | 0, _, _, _, hr, _ => absurd hr (by omega)
  | m + 1, hg, r, k, hr, hk => by
    have hl := flatMapK_length c g m (fun r hr => hg r (by omega))
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge r m with h | h
    · rw [List.getElem?_append_left (by rw [hl]; nlinarith)]
      exact flatMapK_get c g m (fun r hr => hg r (by omega)) r k h hk
    · obtain rfl : r = m := by omega
      rw [List.getElem?_append_right (by rw [hl]; omega), hl]
      simp

theorem readsAt_get? {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {j : ℕ} {w : E}
    (hj : l[j]? = some w) : LoadHolds rd p j w := by
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  exact h j hl

theorem readsAt_getD0 {rd : Reader} {p : E} {l : List E} (h : ReadsAt rd p l) {k : ℕ}
    (hk : k < l.length) : LoadHolds rd p k (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

theorem zcRoundsW_get {rd : Reader} {pR cur : E} {cvr : ℕ → Digest} {cl : ℕ → E} {n : ℕ}
    (h : ReadsAt rd pR (zcRoundsW cvr cur cl n)) {r : ℕ} (hr : r ≤ n) :
    LoadHolds rd pR (4 * r) (digestScalars (cvr r)).1 ∧
      LoadHolds rd pR (4 * r + 1) (digestScalars (cvr r)).2 ∧
      LoadHolds rd pR (4 * r + 2) (cur * gen ^ (5 + 3 * r)) ∧ LoadHolds rd pR (4 * r + 3) (cl r) := by
  unfold zcRoundsW at h
  have g := fun k (hk : k < 4) => flatMapK_get 4 (fun r =>
    [(digestScalars (cvr r)).1, (digestScalars (cvr r)).2, cur * gen ^ (5 + 3 * r), cl r]) (n + 1)
    (fun _ _ => rfl) r k (by omega) hk
  exact ⟨readsAt_get? h (by simpa using g 0 (by omega)), readsAt_get? h (g 1 (by omega)),
    readsAt_get? h (g 2 (by omega)), readsAt_get? h (g 3 (by omega))⟩

theorem readsAt_map_get {rd : Reader} {p : E} {f : ℕ → E} {m j : ℕ} (h : ReadsAt rd p ((List.range m).map f))
    (hj : j < m) : LoadHolds rd p j (f j) := readsAt_get? h (by simp [hj])

theorem ld_mul {rd : Reader} {p w : E} {j : ℕ} (h : LoadHolds rd p j w) :
    LoadHolds rd (p * gen ^ j) 0 w := by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact h

theorem word_g5 : word 32 0 0 = gen ^ 5 := by
  rw [show (32 : ℕ) = 2 ^ 5 by norm_num]; exact word_two_pow (by norm_num)

theorem one_add_gen_pow {n : ℕ} (h : 1 + gen ^ n ≠ 0) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · exfalso; apply h; rw [h0, pow_zero]; exact e_add_self 1
  · exact h0

theorem isInK_one_add_gen_pow (n : ℕ) : IsInK (1 + gen ^ n) :=
  isInK_add (by simpa using gen_pow_isInK 0) (gen_pow_isInK n)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The table sumcheck's window completes** (`VtZcComplete`). -/
theorem vt_zc_complete : VtZcComplete := by
  intro κ hκ rd hlow σ dims chiP zeta cur pR pC pP T0 T1 T2 point chis τs n cvB cl cvr wsr ch h7 h6 h2
    h15 h5 hcv h3326 h3705 h4553 hdims hτn hτmax hnμ hμ33 hzeta hchiP hchis hcl0 hcvr0 hruns hws hR hC
    hP
  rw [← vtItZc_eq]
  have Cm := completes_items (C := coreProgram.Rel rd) (rd := rd) (vtHvZc n pR pC pP) vtItZc
    vtItZc_ok σ
  generalize hσf : fRunI rd 4554 (vtHvZc n pR pC pP) [] σ vtItZc = σf at Cm
  have hf : ∀ v, fRunI rd 4554 (vtHvZc n pR pC pP) [] σ vtItZc v = σf v := fun v => by rw [hσf]
  have E := fRunI_eqs rd (vtHvZc n pR pC pP) σf vtItZc [] σ vtItZc_ok hf
  have FR : ∀ k < 4554, σf (.n k) = σ (.n k) := fun k hk =>
    fRunI_eq_of_def rd (vtHvZc n pR pC pP) vtItZc_ok hf (by simp [fDef, vNum, hk])
  have hB := vtItZc_eqsB
  have Ed := fun e (he : e ∈ vtItZcEq) => E e (mem_of_any feqEqb_sound (List.all_eq_true.mp hB e he))
  simp only [vtItZcEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at Ed
  obtain ⟨i4554, l4555, d4556, s4557, r4557, d4561, l4562, d4563, s4564, r4564, d4568, d4569, l4570,
    d4571, s4572, r4572, d4576, d4577, l4578, d4579, s4580, r4580, d4584, d4585, l4586, d4587, s4588,
    r4588, d4592, d4593, l4594, d4595, s4596, r4596, d4600, d4601, d4602, d4603, s4604, r4604, isq,
    d4622, d4623, d4624, d4625, d4626, d4627, d4628, d4629, d4630, d4631, d4632, d4633, d4634, d4635,
    i4636, d4637, d4638, i4639, d4640, d4641, d4642, d4643, d4644, d4645, -, d4646, d4647, d4648,
    l4649, l4650, l4651, l4652, d4653, d4654, i4655, d4656, d4657, d4658, d4659, -⟩ := Ed
  have ptr := fun (it : FItem) (hit : FEq.Holds rd (vtHvZc n pR pC pP) σf (.item it)) (v : ℕ)
      (hs : it.sets = [.n v]) => hit 0 (by rw [hs]; simp) (by rw [FItem.vals_length, hs]; simp)
  have v4554 : σf (.n 4554) = gen ^ n := by
    have := ptr _ i4554 4554 rfl
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have v4636 : σf (.n 4636) = pR := by
    have := ptr _ i4636 4636 rfl
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have v4639 : σf (.n 4639) = pC := by
    have := ptr _ i4639 4639 rfl
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have v4655 : σf (.n 4655) = pP := by
    have := ptr _ i4655 4655 rfl
    simp only [FItem.sets, FItem.vals, hintCells, List.getElem_cons_zero, List.map_cons,
      List.map_nil] at this
    rw [this]; simp [vtHvZc]
  have f7 : σf (.n 7) = dims := by rw [FR 7 (by omega), h7]
  have hn32 : n ≤ 32 := by omega
  -- the six log-heights
  have blk : ∀ {L S C A : ℕ} (t : ℕ), t < 6 → σf (.n L) = memAt rd (σf (.n 7)) (t + 1) →
      σf (.n S) = σf (.n 4554) * (σf (.n L))⁻¹ →
      σf (.n (S + 1)) = σf (.n C) * (σf (.n S))⁻¹ → σf (.n C) = word 4294967296 0 0 →
      σf (.n A) = σf (.n 4554) + σf (.n L) →
      σf (.n L) = gen ^ τs t ∧ σf (.n S) = gen ^ (n - τs t) ∧
        σf (.n (S + 1)) = gen ^ (32 - (n - τs t)) ∧ σf (.n A) = gen ^ n + gen ^ τs t := by
    intro L S C A t ht hl hs hr hc ha
    have eL : σf (.n L) = gen ^ τs t := by rw [hl, f7, memAt_of_loadHolds (hdims t ht)]
    have eS : σf (.n S) = gen ^ (n - τs t) := by rw [hs, v4554, eL, gen_pow_div (hτn t ht)]
    refine ⟨eL, eS, ?_, by rw [ha, v4554, eL]⟩
    rw [hr, hc, word_g32, eS, gen_pow_div (by omega)]
  have B0 := blk 0 (by omega) l4555 s4557 r4557.1 d4556 d4561
  have B1 := blk 1 (by omega) l4562 s4564 r4564.1 d4563 d4568
  have B2 := blk 2 (by omega) l4570 s4572 r4572.1 d4571 d4576
  have B3 := blk 3 (by omega) l4578 s4580 r4580.1 d4579 d4584
  have B4 := blk 4 (by omega) l4586 s4588 r4588.1 d4587 d4592
  have B5 := blk 5 (by omega) l4594 s4596 r4596.1 d4595 d4600
  have v4601 : σf (.n 4601) = 0 := by
    have e : σf (.n 4601) = (gen ^ n + gen ^ τs 0) * (gen ^ n + gen ^ τs 1) * (gen ^ n + gen ^ τs 2) *
        (gen ^ n + gen ^ τs 3) * (gen ^ n + gen ^ τs 4) * (gen ^ n + gen ^ τs 5) := by
      have m69 : σf (.n 4569) = σf (.n 4561) * σf (.n 4568) := d4569
      have m77 : σf (.n 4577) = σf (.n 4569) * σf (.n 4576) := d4577
      have m85 : σf (.n 4585) = σf (.n 4577) * σf (.n 4584) := d4585
      have m93 : σf (.n 4593) = σf (.n 4585) * σf (.n 4592) := d4593
      have m01 : σf (.n 4601) = σf (.n 4593) * σf (.n 4600) := d4601
      rw [m01, m93, m85, m77, m69, B0.2.2.2, B1.2.2.2, B2.2.2.2, B3.2.2.2, B4.2.2.2, B5.2.2.2]
    obtain ⟨t, ht, htn⟩ := hτmax
    rw [e]
    interval_cases t <;> simp [htn, e_add_self]
  have v4602 : σf (.n 4602) = 0 := by rw [show σf (.n 4602) = word 0 0 0 from d4602, word_zero]
  have v4604 : σf (.n 4604) = gen ^ (point.length - n) := by
    rw [show σf (.n 4604) = σf (.n 6) * (σf (.n 4554))⁻¹ from s4604, FR 6 (by omega), h6, v4554,
      gen_pow_div hnμ]
  have v4605 : σf (.n 4605) = gen ^ (32 - (point.length - n)) := by
    rw [r4604.1, show σf (.n 4603) = word 4294967296 0 0 from d4603, word_g32, v4604,
      gen_pow_div (by omega)]
  -- the squeeze
  have hcvf : (σf (.n 3422), σf (.n 3423)) = digestScalars cvB := by
    rw [FR 3422 (by omega), FR 3423 (by omega)]; exact hcv
  have hdec : decodeCv (σf (.n 3422)) (σf (.n 3423)) = cvB :=
    digestScalars_injective ((decodeCv_spec ⟨cvB, hcvf⟩).symm.trans hcvf)
  have sq : ∀ k < 14, σf (.n (4608 + k)) = sqVals cvB k := fun k hk => by
    have := isq k (by simp [FItem.sets]; exact hk) (by rw [FItem.vals_length]; simp [FItem.sets]; exact hk)
    simp only [FItem.sets, FItem.vals, List.getElem_map, List.getElem_range, hdec] at this
    exact this
  set ξ := challengeOf (sqCv cvB) with hξ
  have v4613 : σf (.n 4613) = (digestScalars (sqCv cvB)).1 := sq 5 (by omega)
  have v4614 : σf (.n 4614) = (digestScalars (sqCv cvB)).2 := sq 6 (by omega)
  have v4621 : σf (.n 4621) = ξ := sq 13 (by omega)
  have hpw : ∀ k < 5, σf (.n (4622 + k)) = ξ ^ k := by
    have p0 : σf (.n 4622) = 1 := by rw [show σf (.n 4622) = word 1 0 0 from d4622, word_one]
    have p1 : σf (.n 4623) = ξ := by
      rw [show σf (.n 4623) = σf (.n 4622) * σf (.n 4621) from d4623, p0, v4621, one_mul]
    have p2 : σf (.n 4624) = ξ ^ 2 := by
      rw [show σf (.n 4624) = σf (.n 4623) * σf (.n 4621) from d4624, p1, v4621]; ring
    have p3 : σf (.n 4625) = ξ ^ 3 := by
      rw [show σf (.n 4625) = σf (.n 4624) * σf (.n 4621) from d4625, p2, v4621]; ring
    have p4 : σf (.n 4626) = ξ ^ 4 := by
      rw [show σf (.n 4626) = σf (.n 4625) * σf (.n 4621) from d4626, p3, v4621]; ring
    intro k hk
    interval_cases k
    · simpa using p0
    · simpa using p1
    · exact p2
    · exact p3
    · exact p4
  have v4631 : σf (.n 4631) = cl 0 := by
    rw [show σf (.n 4631) = σf (.n 4629) + σf (.n 4630) from d4631,
      show σf (.n 4629) = σf (.n 4627) + σf (.n 4628) from d4629,
      show σf (.n 4627) = σf (.n 4624) * σf (.n 3326) from d4627,
      show σf (.n 4628) = σf (.n 4625) * σf (.n 3705) from d4628,
      show σf (.n 4630) = σf (.n 4626) * σf (.n 4553) from d4630, hpw 2 (by omega), hpw 3 (by omega),
      hpw 4 (by omega), FR 3326 (by omega), FR 3705 (by omega), FR 4553 (by omega), h3326, h3705,
      h4553, hcl0]
  have v4641 : σf (.n 4641) = cur * gen ^ 5 := by
    rw [show σf (.n 4641) = σf (.n 2) * σf (.n 4640) from d4641,
      show σf (.n 4640) = word 32 0 0 from d4640, word_g5, FR 2 (by omega), h2]
  have v4642 : σf (.n 4642) = 1 := by rw [show σf (.n 4642) = word 1 0 0 from d4642, word_one]
  have v4644 : σf (.n 4644) = 1 + gen ^ n := by
    rw [show σf (.n 4644) = σf (.n 4643) + σf (.n 4554) from d4644,
      show σf (.n 4643) = word 1 0 0 from d4643, word_one, v4554]
  have v4645 : σf (.n 4645) = 1 := by rw [show σf (.n 4645) = word 1 0 0 from d4645, word_one]
  have v4648 : σf (.n 4648) = pR * gen ^ (4 * n) := by
    rw [show σf (.n 4648) = σf (.n 4636) * σf (.n 4647) from d4648,
      show σf (.n 4647) = σf (.n 4646) * σf (.n 4646) from d4647,
      show σf (.n 4646) = σf (.n 4554) * σf (.n 4554) from d4646, v4636, v4554, ← pow_add, ← pow_add, show n + n + (n + n) = 4 * n by ring]
  have v4656 : σf (.n 4656) = 1 := by rw [show σf (.n 4656) = word 1 0 0 from d4656, word_one]
  have v4658 : σf (.n 4658) = 1 + gen ^ n := by
    rw [show σf (.n 4658) = σf (.n 4657) + σf (.n 4554) from d4658,
      show σf (.n 4657) = word 1 0 0 from d4657, word_one, v4554]
  have v4659 : σf (.n 4659) = 1 := by rw [show σf (.n 4659) = word 1 0 0 from d4659, word_one]
  have f15 : σf (.n 15) = chiP := by rw [FR 15 (by omega), h15]
  have f5 : σf (.n 5) = zeta := by rw [FR 5 (by omega), h5]
  -- the rounds' slots
  have hchl : chis.length = n := by rw [hchis]; simp
  have hwl : ∀ r < n, (wsr r).length = 3 := fun r hr => RunsTo.roundPoly4_inv (hruns r hr)
  have slotN := zcRoundsW_get hR (r := n) le_rfl
  have hround : ∀ j < n, ZcRound rd pR chiP (gen ^ n) pC (gen ^ j) := by
    intro j hj
    obtain ⟨o0, o1, o2, o3⟩ := zcRoundsW_get hR (r := j) (by omega)
    obtain ⟨o4, o5, o6, o7⟩ := zcRoundsW_get hR (r := j + 1) (by omega)
    obtain ⟨c0, c2, c3, hw⟩ : ∃ c0 c2 c3, wsr j = [c0, c2, c3] := by
      match h : wsr j, hwl j hj with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    have hx4 : ∀ k w, LoadHolds rd pR (4 * j + k) w → LoadHolds rd (pR * (gen ^ j) ^ 4) k w := by
      intro k w h; rw [← pow_mul, loadHolds_mul_gen_pow, show j * 4 = 4 * j by ring]; exact h
    have hcur : ReadsAt rd (cur * gen ^ (5 + 3 * j)) [c0, c2, c3] := by
      intro k hk
      simp only [List.length_cons, List.length_nil] at hk
      have g := flatMapK_get 3 wsr n hwl j k hj (by omega)
      rw [hw, List.getElem?_eq_getElem (l := [c0, c2, c3]) (by simp; omega)] at g
      have := readsAt_get? hws g
      rw [pow_add, ← mul_assoc, loadHolds_mul_gen_pow]
      exact this
    have hq : gen ^ n * wInvG = gen ^ (n - 1 - j) * gen ^ j := by
      rw [← pow_add, show n - 1 - j + j = n - 1 by omega, show n = n - 1 + 1 by omega, pow_succ,
        mul_assoc, show gen * wInvG = 1 by rw [mul_comm]; exact wInvG_mul_gen, mul_one,
        Nat.add_sub_cancel]
    have hrk : LoadHolds rd (chiP * gen ^ (n - 1 - j)) 0 (ch j) := by
      apply ld_mul
      refine readsAt_get? hchiP ?_
      rw [hchis, List.getElem?_reverse (by simp; omega)]
      simp only [List.length_map, List.length_range, show n - 1 - (n - 1 - j) = j by omega,
        List.getElem?_map, List.getElem?_range hj, Option.map_some]
    have hc0 : LoadHolds rd (pC * gen ^ j) 0 (∏ i ∈ Finset.range j, ch i) :=
      ld_mul (readsAt_map_get hC (by omega))
    have hc1 : LoadHolds rd (pC * gen ^ j) 1 ((∏ i ∈ Finset.range j, ch i) * ch j) := by
      rw [loadHolds_mul_gen_pow, ← Finset.prod_range_succ]
      exact readsAt_map_get hC (by omega)
    refine ⟨cvr j, cur * gen ^ (5 + 3 * j), cl j, c0, c2, c3, cl (j + 1), ch j, cvr (j + 1),
      gen ^ (n - 1 - j), ∏ i ∈ Finset.range j, ch i, hx4 0 _ (by simpa using o0), hx4 1 _ o1,
      hx4 2 _ o2, hx4 3 _ o3, hcur, by rw [← hw]; exact hruns j hj, hq, hrk, hx4 4 _ ?_, hx4 5 _ ?_,
      hx4 6 _ ?_, hx4 7 _ ?_, hc0, hc1⟩
    · rw [show 4 * j + 4 = 4 * (j + 1) by ring]; exact o4
    · rw [show 4 * j + 5 = 4 * (j + 1) + 1 by ring]; exact o5
    · rw [show 4 * j + 6 = 4 * (j + 1) + 2 by ring, mul_assoc, ← pow_add,
        show 5 + 3 * j + 3 = 5 + 3 * (j + 1) by ring]; exact o6
    · rw [show 4 * j + 7 = 4 * (j + 1) + 3 by ring]; exact o7
  have hpeq : ∀ j < n, PeqBody rd pP zeta chiP (gen ^ j) := by
    intro j hj
    refine ⟨∏ i ∈ Finset.range j, (1 + point.getD i 0 + chis.getD i 0), point.getD j 0,
      chis.getD j 0, ld_mul (readsAt_map_get hP (by omega)),
      ld_mul (readsAt_getD0 hzeta (by omega)), ld_mul (readsAt_getD0 hchiP (by omega)), ?_⟩
    rw [loadHolds_mul_gen_pow, ← Finset.prod_range_succ]
    exact readsAt_map_get hP (by omega)
  refine (Cm (IObls_of_obs _ _ ?_)).mono le_rfl le_rfl ?_
  · rw [vtItZc_obs]
    have hdl : ∀ t < 6, Ob.Holds rd σf (.ld (.n 7) (t + 1)) := fun t ht => ob_ld_of f7 (hdims t ht)
    have hτ32 : ∀ t < 6, n - τs t < 2 ^ κ ∧ 32 - (n - τs t) < 2 ^ κ := fun t _ => by
      have : 64 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
      omega
    have h64 : 64 ≤ 2 ^ κ := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hκ)
    intro o ho
    simp only [vtItZcOb, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdl 0 (by omega)
    · show σf _ ≠ 0; rw [B0.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B0.2.1 B0.2.2.1 (hτ32 0 (by omega)).1 (hτ32 0 (by omega)).2
    · exact hdl 1 (by omega)
    · show σf _ ≠ 0; rw [B1.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B1.2.1 B1.2.2.1 (hτ32 1 (by omega)).1 (hτ32 1 (by omega)).2
    · exact hdl 2 (by omega)
    · show σf _ ≠ 0; rw [B2.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B2.2.1 B2.2.2.1 (hτ32 2 (by omega)).1 (hτ32 2 (by omega)).2
    · exact hdl 3 (by omega)
    · show σf _ ≠ 0; rw [B3.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B3.2.1 B3.2.2.1 (hτ32 3 (by omega)).1 (hτ32 3 (by omega)).2
    · exact hdl 4 (by omega)
    · show σf _ ≠ 0; rw [B4.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B4.2.1 B4.2.2.1 (hτ32 4 (by omega)).1 (hτ32 4 (by omega)).2
    · exact hdl 5 (by omega)
    · show σf _ ≠ 0; rw [B5.1]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow B5.2.1 B5.2.2.1 (hτ32 5 (by omega)).1 (hτ32 5 (by omega)).2
    · show σf (.n 4601) + σf (.n 4602) = 0; rw [v4601, v4602, add_zero]
    · show σf _ ≠ 0; rw [v4554]; exact gen_pow_ne_zero _
    · exact ob_rc_gen hlow v4604 v4605 (by omega) (by omega)
    · exact ⟨cvB, hcvf⟩
    · show LoadHolds rd (σf (.n 4636)) 0 (σf (.n 4613))
      rw [v4636, v4613, ← hcvr0]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).1
    · show LoadHolds rd (σf (.n 4636)) 1 (σf (.n 4614))
      rw [v4636, v4614, ← hcvr0]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).2.1
    · show LoadHolds rd (σf (.n 4636)) 2 (σf (.n 4641))
      rw [v4636, v4641]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).2.2.1
    · show LoadHolds rd (σf (.n 4636)) 3 (σf (.n 4631))
      rw [v4636, v4631]; simpa using (zcRoundsW_get hR (r := 0) (by omega)).2.2.2
    · show LoadHolds rd (σf (.n 4639)) 0 (σf (.n 4642))
      rw [v4639, v4642]
      simpa using readsAt_map_get hC (j := 0) (by omega)
    · refine ⟨by rw [v4644]; exact isInK_one_add_gen_pow n, fun hz => ?_⟩
      rw [v4644] at hz
      simp only [List.map_cons, List.map_nil]
      rw [v4645, v4554, v4636, f15, v4639]
      exact loop79_complete (one_add_gen_pow hz) hround
    · exact ob_ld_of v4648 (ld_mul slotN.1)
    · exact ob_ld_of v4648 ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.1)
    · exact ob_ld_of v4648 ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.1)
    · exact ob_ld_of v4648 ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.2)
    · show LoadHolds rd (σf (.n 4655)) 0 (σf (.n 4656))
      rw [v4655, v4656]
      simpa using readsAt_map_get hP (j := 0) (by omega)
    · refine ⟨by rw [v4658]; exact isInK_one_add_gen_pow n, fun hz => ?_⟩
      rw [v4658] at hz
      simp only [List.map_cons, List.map_nil]
      rw [v4659, v4554, v4655, f5, f15]
      exact loop80_complete (one_add_gen_pow hz) hpeq
  · intro σ' h
    rw [h]
    have m49 : σf (.n 4649) = (digestScalars (cvr n)).1 := by
      rw [show σf (.n 4649) = memAt rd (σf (.n 4648)) 0 from l4649, v4648, memAt_of_loadHolds (ld_mul slotN.1)]
    have m50 : σf (.n 4650) = (digestScalars (cvr n)).2 := by
      rw [show σf (.n 4650) = memAt rd (σf (.n 4648)) 1 from l4650, v4648,
        memAt_of_loadHolds ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.1)]
    have m51 : σf (.n 4651) = cur * gen ^ (5 + 3 * n) := by
      rw [show σf (.n 4651) = memAt rd (σf (.n 4648)) 2 from l4651, v4648,
        memAt_of_loadHolds ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.1)]
    have m52 : σf (.n 4652) = cl n := by
      rw [show σf (.n 4652) = memAt rd (σf (.n 4648)) 3 from l4652, v4648,
        memAt_of_loadHolds ((loadHolds_mul_gen_pow _ _ _ _ _).mpr slotN.2.2.2)]
    exact ⟨v4554, v4621, hpw, v4636, v4639, v4655, by rw [m49, m50], m51, m52⟩

end
end LeanVM.Guest.B1.VerifySub
