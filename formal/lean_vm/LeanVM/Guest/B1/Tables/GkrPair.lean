/-
  LeanVM.Guest.B1.Tables.GkrPair

  One pair step of the GKR walk, from its run to the facts `__loop10`'s iteration needs.
-/

module

public import LeanVM.Guest.B1.Tables.GkrComplete10
public import LeanVM.Guest.B1.Tables.GkrInv

/-!
# A pair step, backward

`pair_iter`: a run of `gkrStep 2` from a layer `L` gives the rounds' states `cvr`, claims `cl`
and challenges `ch`, the twelve children `es`, the next layer's state; and on any memory holding
the layer `L`, the round states, the next row and the next layer, `__loop10`'s iteration facts
(`L10Iter`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem RunsTo.roundPoly_inv {count : ℕ} {claim e : E} {cv cv' : Digest} {ws : List E}
    {r : E × E} (h : RunsTo (roundPoly count claim (some e)) cv ws r cv') : ws.length = count - 1 := by
  unfold roundPoly at h
  obtain ⟨x1, x2, msg, cv1, hx, h1, h⟩ := RunsTo.bind_inv' h
  unfold sumcheckRoundPoly at h1
  obtain ⟨y1, y2, tail, cv2, hy, h2, h1⟩ := RunsTo.bind_inv' h1
  obtain ⟨hl, -, -⟩ := RunsTo.readN_inv h2
  obtain ⟨hy2, -, -⟩ := RunsTo.ret_inv h1
  obtain ⟨x3, x4, c, cv3, hz, h3, h⟩ := RunsTo.bind_inv' h
  obtain ⟨hx3, -, -⟩ := RunsTo.sampleE_inv h3
  obtain ⟨hx4, -, -⟩ := RunsTo.ret_inv h
  rw [hx, hy, hz, hy2, hx3, hx4]
  simpa using hl

theorem list_four (l : List E) (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem map_range_getD_self (l : List E) : (List.range l.length).map (l.getD · 0) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ h2]

/-- The next layer's value of a side from its four children, as `__loop10` computes it. -/
def l10Next (es : ℕ → E) (b : ℕ) (c0 c1 : E) : E :=
  es b + c0 * (es b + es (b + 1)) + c1 * (es b + c0 * (es b + es (b + 1)) +
    (es (b + 2) + c0 * (es (b + 2) + es (b + 3))))

theorem l10cv_twelve (cvT : Digest) (c0 c1 c2 : List E) (h0 : c0.length = 4) (h1 : c1.length = 4)
    (h2 : c2.length = 4) :
    l10cv cvT (fun i => (c0 ++ (c1 ++ c2)).getD i 0) 12 = obsAll (obsAll (obsAll cvT c0) c1) c2 := by
  match c0, c1, c2, h0, h1, h2 with
  | [a0, a1, a2, a3], [b0, b1, b2, b3], [d0, d1, d2, d3], _, _, _ => rfl

/-- **A pair step's run, read back.** -/
theorem pair_data {s s' : GkrState} {cv cv' : Digest} {ys : List E} {L : ℕ}
    (h : RunsTo (gkrStep 2 s) cv ys s' cv') (hL : s.point.length = L) :
    ∃ (cl : ℕ → E) (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch : ℕ → E) (es : ℕ → E),
      cl 0 = polyEval s.values (challengeOf (sqCv cv)) ∧ cvr 0 = sqCv cv ∧
      (∀ r < L, (wsr r).length = 4 ∧ RunsTo (roundPoly 5 (cl r) (some (s.point.getD r 0))) (cvr r)
        (wsr r) (cl (r + 1), ch r) (cvr (r + 1))) ∧
      ys = (List.range L).flatMap wsr ++ (List.range 12).map es ∧
      cl L = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCv cv) * (es 4 * es 5 * es 6 * es 7 +
        challengeOf (sqCv cv) * (es 8 * es 9 * es 10 * es 11)) ∧
      s'.point = [challengeOf (sqCv (l10cv (cvr L) es 12)),
        challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))] ++ (List.range L).map ch ∧
      s'.values = [l10Next es 0 (challengeOf (sqCv (l10cv (cvr L) es 12)))
          (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))),
        l10Next es 4 (challengeOf (sqCv (l10cv (cvr L) es 12)))
          (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))),
        l10Next es 8 (challengeOf (sqCv (l10cv (cvr L) es 12)))
          (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12))))] ∧
      cv' = sqCv (sqCv (l10cv (cvr L) es 12)) := by
  obtain ⟨ws, chs, cl, cvS, c0, c1, c2, hsc, h0, h1, h2, hreq, rfl, rfl, rfl⟩ := RunsTo.gkrStep_inv h
  obtain ⟨a0, a1, a2, a3, rfl⟩ := list_four c0 h0
  obtain ⟨b0, b1, b2, b3, rfl⟩ := list_four c1 h1
  obtain ⟨d0, d1, d2, d3, rfl⟩ := list_four c2 h2
  obtain ⟨cl', cvr, wsr, ch, hc0, hcv0, hr, hws, hpt, hfin, hcvS⟩ := RunsTo.sumcheck_inv _ _ _ _ _ _ _ hsc
  simp only [List.length_map, hL] at hr hws hpt hfin hcvS
  have hes := l10cv_twelve cvS [a0, a1, a2, a3] [b0, b1, b2, b3] [d0, d1, d2, d3] rfl rfl rfl
  refine ⟨cl', cvr, wsr, ch, fun i => ([a0, a1, a2, a3] ++ ([b0, b1, b2, b3] ++ [d0, d1, d2, d3])).getD i 0, hc0, hcv0, fun r hr' => ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · have := hr r (by simpa using hr')
    simp only [List.getElem_map] at this
    have hpe : s.point[r]'(by omega) = s.point.getD r 0 := by rw [List.getD_eq_getElem _ _ (by omega)]
    rw [hpe] at this
    exact ⟨by have := RunsTo.roundPoly_inv this; simpa using this, this⟩
  · rw [hws]
    congr 1
  · rw [← hfin, hreq, polyEval_three]
    · simp only [prodE_four, List.cons_append, List.nil_append, List.getD_cons_zero,
        List.getD_cons_succ]
  · rw [← hcvS, hes, hpt]
    simp [sqAll]
  · rw [← hcvS, hes]
    simp only [List.map_cons, List.map_nil, sqAll, multilinearEval_four, l10Next, List.cons.injEq,
      and_true, List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ]
    refine ⟨by ring, by ring, by ring⟩
  · rw [← hcvS, hes]
    simp [sqAll]

theorem readsAt_split {rd : Reader} {p : E} {A B : List E} (h : ReadsAt rd p (A ++ B)) :
    ReadsAt rd p A ∧ ReadsAt rd (p * gen ^ A.length) B := by
  refine ⟨fun k hk => ?_, readsAt_gen_pow_mul.mpr fun k hk => ?_⟩
  · have := h k (by simp; omega); rwa [List.getElem_append_left hk] at this
  · have := h (A.length + k) (by simp; omega)
    rw [List.getElem_append_right (by omega)] at this
    simpa using this

theorem readsAt_flatMap_range {rd : Reader} {p : E} {w : ℕ → List E} {rest : List E} {L : ℕ}
    (hw : ∀ r < L, (w r).length = 4) (h : ReadsAt rd p ((List.range L).flatMap w ++ rest)) :
    (∀ r < L, ReadsAt rd (p * gen ^ (4 * r)) (w r)) ∧ ReadsAt rd (p * gen ^ (4 * L)) rest := by
  have hlen : ∀ r ≤ L, ((List.range r).flatMap w).length = 4 * r := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih (by omega)]
      simp [hw r (by omega)]; ring
  refine ⟨fun r hr => ?_, ?_⟩
  · have e : (List.range L).flatMap w ++ rest =
        (List.range r).flatMap w ++ (w r ++ (((List.range (L - (r + 1))).map (r + 1 + ·)).flatMap w ++ rest)) := by
      rw [show L = r + 1 + (L - (r + 1)) by omega, List.range_add, List.range_succ, List.flatMap_append,
        List.flatMap_append]
      simp [List.append_assoc]
    rw [e] at h
    have h2 := (readsAt_split h).2
    rw [hlen r (by omega)] at h2
    exact (readsAt_split h2).1
  · have h2 := (readsAt_split h).2
    rwa [hlen L le_rfl] at h2

/-- **A pair step's iteration facts**: on a memory holding the layer `L = 2j + sh`, its row, the
round states, the next row and the next layer, `__loop10`'s iteration at `g^j` holds its facts. -/
theorem pair_iter {rd : Reader} {cv : Digest} {s : GkrState} {cur : E} {L : ℕ} (cl : ℕ → E)
    (cvr : ℕ → Digest) (wsr : ℕ → List E) (ch es : ℕ → E) {v0 v1 v2 : E}
    (hvals : s.values = [v0, v1, v2])
    (hc0 : cl 0 = polyEval s.values (challengeOf (sqCv cv))) (hcv0 : cvr 0 = sqCv cv)
    (hr : ∀ r < L, (wsr r).length = 4 ∧ RunsTo (roundPoly 5 (cl r) (some (s.point.getD r 0))) (cvr r)
      (wsr r) (cl (r + 1), ch r) (cvr (r + 1)))
    (hfin : cl L = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCv cv) * (es 4 * es 5 * es 6 * es 7 +
      challengeOf (sqCv cv) * (es 8 * es 9 * es 10 * es 11)))
    {N dsb gmu layers rounds row : E} {j sh posE : ℕ} (hLj : L = 2 * j + sh)
    (hds : LoadHolds rd (dsb * gmu) 0 (gen ^ sh))
    (hlay : ∀ k < 8, LoadHolds rd layers (8 * L + k)
      ([(digestScalars cv).1, (digestScalars cv).2, cur, v0, v1, v2, row, gen ^ posE].getD k 0))
    (hrow : ∀ r < L, LoadHolds rd row r (s.point.getD r 0))
    (hrnd : ∀ r ≤ L, ∀ k < 4, LoadHolds rd rounds (4 * (posE + r) + k)
      ([(digestScalars (cvr r)).1, (digestScalars (cvr r)).2, cur * gen ^ (4 * r), cl r].getD k 0))
    (hnr : ∀ r < L, LoadHolds rd row (42 + r) (ch r))
    (hnr0 : LoadHolds rd row 40 (challengeOf (sqCv (l10cv (cvr L) es 12))))
    (hnr1 : LoadHolds rd row 41 (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))))
    (hnext : ∀ k < 8, LoadHolds rd layers (8 * L + 16 + k)
      ([(digestScalars (sqCv (sqCv (l10cv (cvr L) es 12)))).1,
        (digestScalars (sqCv (sqCv (l10cv (cvr L) es 12)))).2, cur * gen ^ (4 * L) * gen ^ 12,
        l10Next es 0 (challengeOf (sqCv (l10cv (cvr L) es 12)))
          (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))),
        l10Next es 4 (challengeOf (sqCv (l10cv (cvr L) es 12)))
          (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))),
        l10Next es 8 (challengeOf (sqCv (l10cv (cvr L) es 12)))
          (challengeOf (sqCv (sqCv (l10cv (cvr L) es 12)))),
        row * gen ^ 40, gen ^ (posE + L + 1)].getD k 0))
    (hys : ReadsAt rd cur ((List.range L).flatMap wsr ++ (List.range 12).map es)) :
    L10Iter rd N dsb gmu layers rounds (gen ^ j) (gen ^ sh) cv (cvr L) cur v0 v1 v2 row (gen ^ posE)
      (cur * gen ^ (4 * L)) (cl L) es := by
  have hXL : gen ^ j * gen ^ j * gen ^ sh = gen ^ L := by rw [hLj, ← pow_add, ← pow_add]; ring_nf
  have pL : layers * (gen ^ j * gen ^ j * gen ^ sh) ^ 8 = layers * gen ^ (8 * L) := by
    rw [hXL, ← pow_mul]; ring_nf
  have pH : rounds * (gen ^ posE) ^ 4 = rounds * gen ^ (4 * (posE + 0)) := by rw [← pow_mul]; ring_nf
  have pT : rounds * (gen ^ posE * (gen ^ j * gen ^ j * gen ^ sh)) ^ 4 = rounds * gen ^ (4 * (posE + L)) := by
    rw [hXL, ← pow_add, ← pow_mul]; ring_nf
  have hwl : ∀ r < L, (wsr r).length = 4 := fun r h => (hr r h).1
  obtain ⟨hws, hes⟩ := readsAt_flatMap_range hwl hys
  have lay := fun k (hk : k < 8) => (loadHolds_gen_pow_mul (p := layers) (j := 8 * L) (k := k)).mpr (hlay k hk)
  have nxt := fun k (hk : k < 8) => (loadHolds_gen_pow_mul (p := layers) (j := 8 * L) (k := 16 + k)).mpr
    (by rw [← Nat.add_assoc]; exact hnext k hk)
  have rnd := fun r (hr' : r ≤ L) k (hk : k < 4) =>
    (loadHolds_gen_pow_mul (p := rounds) (j := 4 * (posE + r)) (k := k)).mpr (hrnd r hr' k hk)
  have rH := fun k (hk : k < 4) => by
    have := rnd 0 (Nat.zero_le _) k hk; rw [← pH] at this; exact this
  have rT := fun k (hk : k < 4) => by
    have := rnd L le_rfl k hk; rw [← pT] at this; exact this
  have lay' := fun k (hk : k < 8) => by have := lay k hk; rw [← pL] at this; exact this
  have nxt' := fun k (hk : k < 8) => by have := nxt k hk; rw [← pL] at this; exact this
  have e23 : gen ^ posE * (gen ^ j * gen ^ j * gen ^ sh) * gen = gen ^ (posE + L + 1) := by
    rw [hXL, ← pow_add, ← pow_succ]
  have hpe : cl 0 = v0 + challengeOf (sqCv cv) * (v1 + challengeOf (sqCv cv) * v2) := by
    rw [hc0, hvals, polyEval_three]
  refine
    { hds := hds, hl0 := lay' 0 (by norm_num), hl1 := lay' 1 (by norm_num), hl2 := lay' 2 (by norm_num),
      hl3 := lay' 3 (by norm_num), hl4 := lay' 4 (by norm_num), hl5 := lay' 5 (by norm_num),
      hl6 := lay' 6 (by norm_num), hl7 := lay' 7 (by norm_num),
      hh0 := by have := rH 0 (by norm_num); rw [hcv0] at this; exact this,
      hh1 := by have := rH 1 (by norm_num); rw [hcv0] at this; exact this,
      hh2 := by have := rH 2 (by norm_num); simpa using this,
      hh3 := by have := rH 3 (by norm_num); rw [hpe] at this; exact this,
      ht0 := rT 0 (by norm_num), ht1 := rT 1 (by norm_num), ht2 := rT 2 (by norm_num),
      ht3 := rT 3 (by norm_num), hr0 := hnr0, hr1 := hnr1,
      hn16 := nxt' 0 (by norm_num), hn17 := nxt' 1 (by norm_num), hn18 := nxt' 2 (by norm_num),
      hn19 := nxt' 3 (by norm_num), hn20 := nxt' 4 (by norm_num), hn21 := nxt' 5 (by norm_num),
      hn22 := nxt' 6 (by norm_num), hn23 := by rw [e23]; exact nxt' 7 (by norm_num),
      hK1 := isInK_add (by simpa using gen_pow_isInK 0) (by rw [hXL]; exact gen_pow_isInK L),
      h101 := fun hne => ?_, hc := fun i hi => ?_, hcheck := hfin }
  · rw [hXL] at hne ⊢
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · exact absurd (by rw [h0, pow_zero]; exact e_add_self 1) hne
    refine loop101_complete hpos fun r hr' => ?_
    have pR : rounds * (gen ^ posE * gen ^ r) ^ 4 = rounds * gen ^ (4 * (posE + r)) := by
      rw [← pow_add, ← pow_mul]; ring_nf
    have r0 := fun k (hk : k < 4) => by
      have := rnd r (by omega) k hk; rw [← pR] at this; exact this
    have r1 := fun k (hk : k < 4) => by
      have := hrnd (r + 1) (by omega) k hk
      rw [show 4 * (posE + (r + 1)) + k = 4 * (posE + r) + (4 + k) by ring] at this
      exact (loadHolds_gen_pow_mul (p := rounds) (j := 4 * (posE + r)) (k := 4 + k)).mpr this
    have r1' := fun k (hk : k < 4) => by have := r1 k hk; rw [← pR] at this; exact this
    refine ⟨cvr r, cur * gen ^ (4 * r), cl r, s.point.getD r 0, wsr r, cl (r + 1), ch r, cvr (r + 1),
      r0 0 (by norm_num), r0 1 (by norm_num), r0 2 (by norm_num), r0 3 (by norm_num), ?_, (hr r hr').1,
      hws r hr', (hr r hr').2, ?_, r1' 0 (by norm_num), r1' 1 (by norm_num), ?_, r1' 3 (by norm_num)⟩
    · exact (loadHolds_gen_pow_mul (p := row) (j := r) (k := 0)).mpr (by simpa using hrow r hr')
    · refine (loadHolds_gen_pow_mul (p := row * gen ^ 40) (j := r) (k := 2)).mpr ?_
      refine (loadHolds_gen_pow_mul (p := row) (j := 40) (k := r + 2)).mpr ?_
      rw [show 40 + (r + 2) = 42 + r by omega]; exact hnr r hr'
    · have := r1' 2 (by norm_num)
      rw [show cur * gen ^ (4 * (r + 1)) = cur * gen ^ (4 * r) * gen ^ 4 by ring] at this
      exact this
  · have := hes i (by simp; omega)
    simpa using this

end
end LeanVM.Guest.B1.VerifySub
