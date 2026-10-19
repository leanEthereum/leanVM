/-
  LeanVM.Guest.B1.Tables.GkrHolds

  `verify_bus_gkr`'s body and its two loops hold on a memory holding an honest trace's buffers and
  the caller's words.
-/

module

public import LeanVM.Guest.B1.Tables.GkrOwn

/-!
# The body, honest

From `GkrMem` and the caller's words (the stream at `cur`, the point at `zeta`): `gkr_loop10`,
`gkr_loop11` and `gkr_holds`, the body at `vbgσ` returning the run's state, cursor and values.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem vbgDs_get {μ : ℕ} (hμ : μ < 33) : vbgDs.getD μ 0 = gen ^ (μ % 2) := by
  rw [← word_two_pow (by omega)]
  interval_cases μ <;> rfl

theorem vbgPb_get {μ : ℕ} (hμ : μ < 33) : vbgPb.getD μ 0 = gen ^ (μ / 2) := by
  rw [← word_two_pow (by omega)]
  interval_cases μ <;> rfl

theorem gk_getD_three (l : List E) (h : l.length = 3) : l = [l.getD 0 0, l.getD 1 0, l.getD 2 0] := by
  match l, h with
  | [a, b, c], _ => rfl

theorem length_flatMap_range_lt {F : ℕ → List E} {w : ℕ} :
    ∀ n, (∀ j < n, (F j).length = w) → ((List.range n).flatMap F).length = w * n
  | 0, _ => by simp
  | n + 1, h => by
    rw [length_flatMap_range_succ, length_flatMap_range_lt n (fun j hj => h j (by omega)), h n (by omega)]
    ring

theorem gen_pow_mul_mul (p : E) (a b : ℕ) : p * gen ^ a * gen ^ b = p * gen ^ (a + b) := by
  rw [mul_assoc, ← pow_add]

section
variable {T : GkrTrace} {μ : ℕ} {cv cv' : Digest} {xs : List E} {r : E × List E × List E}

theorem GkrTrace.Ok.vals (hT : T.Ok μ cv xs r cv') {i : ℕ} (hi : i ≤ μ / 2) :
    (T.P i).values = [(T.P i).values.getD 0 0, (T.P i).values.getD 1 0, (T.P i).values.getD 2 0] := by
  refine gk_getD_three _ ?_
  match i with
  | 0 =>
    rcases Nat.mod_two_eq_zero_or_one μ with h | h
    · rw [(hT.even h).1]; rfl
    · rw [(hT.odd h).2.2.1]; rfl
  | i + 1 => rw [(hT.pair i (by omega)).2.2.2.2.2.2.1]; rfl

theorem GkrTrace.Ok.ylen (hT : T.Ok μ cv xs r cv') {i : ℕ} (hi : i < μ / 2) :
    (T.Y i).length = 4 * gL (μ % 2) i + 12 := by
  obtain ⟨-, -, hr, hys, -⟩ := hT.pair i hi
  rw [hys, List.length_append, length_flatMap_range_lt (w := 4) _ (fun r hr' => (hr r hr').1)]
  simp

theorem GkrTrace.Ok.ys_len (hT : T.Ok μ cv xs r cv') :
    ∀ j ≤ μ / 2, ((List.range j).flatMap T.Y).length + gCur (μ % 2) 0 = gCur (μ % 2) j
  | 0, _ => by simp
  | j + 1, hj => by
    rw [length_flatMap_range_succ, hT.ylen (by omega),
      show gCur (μ % 2) (j + 1) = gCur (μ % 2) j + 4 * gL (μ % 2) j + 12 from rfl, ← hT.ys_len j (by omega)]
    omega

theorem GkrTrace.Ok.xs_len (hT : T.Ok μ cv xs r cv') : xs.length = gCur (μ % 2) (μ / 2) := by
  rw [← hT.ys_len _ le_rfl, hT.hxs]
  rcases Nat.mod_two_eq_zero_or_one μ with h | h
  · simp [h, gCur]
  · simp [h, gCur]; omega

/-- The odd step's words and each pair's, read at the cursor. -/
theorem GkrTrace.Ok.reads (hT : T.Ok μ cv xs r cv') {rd : Reader} {cur : E} (h : ReadsAt rd cur xs) :
    LoadHolds rd cur 0 T.x0 ∧ LoadHolds rd cur 1 T.cnt ∧
      (μ % 2 = 1 → ∀ i < 6, LoadHolds rd (cur * gen ^ 2) i (T.oes i)) ∧
      ∀ i < μ / 2, ReadsAt rd (cur * gen ^ gCur (μ % 2) i) (T.Y i) := by
  rw [hT.hxs] at h
  have h' : ReadsAt rd cur ([T.x0, T.cnt] ++ ((if μ % 2 = 1 then (List.range 6).map T.oes else []) ++
      (List.range (μ / 2)).flatMap T.Y)) := h
  have h2 := (readsAt_split h').2
  refine ⟨h' 0 (by simp), h' 1 (by simp), fun hs i hi => ?_, fun i hi => ?_⟩
  · have := (readsAt_split h2).1
    rw [ite_pos' hs] at this
    have := readsAt_getD this (k := i) (by simpa using hi)
    rwa [gk_getD_map_range _ hi] at this
  · have := readsAt_flatMap_block (readsAt_split h2).2 hi
    rw [gen_pow_mul_mul, gen_pow_mul_mul] at this
    convert this using 3
    rw [← hT.ys_len i (by omega)]
    rcases Nat.mod_two_eq_zero_or_one μ with h | h
    · simp [h, gCur]; omega
    · simp [h, gCur]; omega

theorem loadHolds_unshift {rd : Reader} {p v : E} {a k n : ℕ} (h : LoadHolds rd p n v) (hn : n = a + k) :
    LoadHolds rd (p * gen ^ a) k v := by
  rw [hn] at h; exact loadHolds_gen_pow_mul.mpr h

theorem GkrTrace.Ok.next_lay (hT : T.Ok μ cv xs r cv') {j : ℕ} (hj : j < μ / 2) (cur pts : E) :
    gLay T (μ % 2) cur pts (j + 1) =
      [(digestScalars (sqCv (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))).1,
        (digestScalars (sqCv (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))).2,
        cur * gen ^ gCur (μ % 2) j * gen ^ (4 * gL (μ % 2) j) * gen ^ 12,
        l10Next (T.ES j) 0 (challengeOf (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))
          (challengeOf (sqCv (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))),
        l10Next (T.ES j) 4 (challengeOf (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))
          (challengeOf (sqCv (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))),
        l10Next (T.ES j) 8 (challengeOf (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))
          (challengeOf (sqCv (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))),
        pts * gen ^ (40 * (μ % 2 + j)) * gen ^ 40, gen ^ (gPos (μ % 2) j + gL (μ % 2) j + 1)] := by
  obtain ⟨-, -, -, -, -, -, hvl, hcvn⟩ := hT.pair j hj
  simp only [gLay, hcvn, hvl, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true]
  refine ⟨trivial, trivial, ?_, trivial, trivial, trivial, ?_, rfl⟩
  · show cur * gen ^ (gCur (μ % 2) j + 4 * gL (μ % 2) j + 12) = _
    rw [pow_add, pow_add]; ring
  · rw [mul_assoc, ← pow_add, show 40 * (μ % 2 + j) + 40 = 40 * (μ % 2 + (j + 1)) by ring]

/-- **`__loop10`** on an honest memory. -/
theorem gkr_loop10 (hT : T.Ok μ cv xs r cv') (hμ : μ < 33) {rd : Reader}
    {cur layers rounds pts pb dsb : E} (hM : GkrMem rd T μ cv cur layers rounds pts pb dsb)
    (hx : ReadsAt rd cur xs) (hm : 0 < μ / 2) :
    coreProgram.Rel rd "__loop10" [1, gen ^ (μ / 2), dsb, gen ^ μ, layers, rounds] [] := by
  obtain ⟨-, -, -, hY⟩ := hT.reads hx
  refine loop10_complete hm fun j hj => ?_
  obtain ⟨hc0, hcv0, hr, hys, hfin, hpt, -, -⟩ := hT.pair j hj
  have hv := hT.vals (i := j) (by omega)
  have hL : gL (μ % 2) j + 2 ≤ μ := by unfold gL; omega
  have hpt' : ∀ t < gL (μ % 2) j + 2, (T.P (j + 1)).point.getD t 0 =
      ([challengeOf (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)),
        challengeOf (sqCv (sqCv (l10cv (T.CVR j (gL (μ % 2) j)) (T.ES j) 12)))] ++
        (List.range (gL (μ % 2) j)).map (T.CH j)).getD t 0 := fun t _ => by rw [hpt]
  have hds : LoadHolds rd (dsb * gen ^ μ) 0 (gen ^ (μ % 2)) :=
    loadHolds_unshift (by rw [← vbgDs_get hμ]; exact hM.ds μ (by omega)) rfl
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, pair_iter (T.CL j) (T.CVR j) (T.WSR j) (T.CH j) (T.ES j)
    hv hc0 hcv0 hr hfin (N := gen ^ (μ / 2)) (j := j) (sh := μ % 2) (posE := gPos (μ % 2) j)
    (row := pts * gen ^ (40 * (μ % 2 + j))) (cur := cur * gen ^ gCur (μ % 2) j) rfl hds
    (fun k hk => hM.lay j (by omega) k hk) (fun t ht => loadHolds_unshift (hM.row j (by omega) t (by omega)) rfl)
    (fun t ht k hk => hM.rnd j hj t ht k hk) (fun t ht => ?_) ?_ ?_ (fun k hk => ?_) (by rw [← hys]; exact hY j hj)⟩
  · have := hM.row (j + 1) (by omega) (2 + t) (by omega)
    rw [hpt' _ (by omega)] at this
    simp only [List.cons_append, List.nil_append] at this
    rw [show 2 + t = t + 1 + 1 by omega, List.getD_cons_succ, List.getD_cons_succ,
      gk_getD_map_range _ ht] at this
    exact loadHolds_unshift this (by ring)
  · have := hM.row (j + 1) (by omega) 0 (by omega)
    rw [hpt' _ (by omega)] at this
    exact loadHolds_unshift this (by ring)
  · have := hM.row (j + 1) (by omega) 1 (by omega)
    rw [hpt' _ (by omega)] at this
    exact loadHolds_unshift this (by ring)
  · have := hM.lay (j + 1) (by omega) k hk
    rw [hT.next_lay hj] at this
    rwa [show 8 * gL (μ % 2) (j + 1) + k = 8 * gL (μ % 2) j + 16 + k by unfold gL; ring] at this

/-- **`__loop11`** on an honest memory. -/
theorem gkr_loop11 (hT : T.Ok μ cv xs r cv') {rd : Reader} {cur layers rounds pts pb dsb zeta : E}
    (hM : GkrMem rd T μ cv cur layers rounds pts pb dsb) (hz : ReadsAt rd zeta r.2.1) (hμ : μ < 33)
    (hm : 0 < μ) :
    coreProgram.Rel rd "__loop11" [1, gen ^ μ, zeta, pts * gen ^ (40 * (μ % 2 + μ / 2))] [] := by
  have hl := hT.hlen _ le_rfl
  have hμL : gL (μ % 2) (μ / 2) = μ := by unfold gL; omega
  refine loop11_complete hm fun j hj => ⟨(T.P (μ / 2)).point.getD j 0,
    loadHolds_unshift (loadHolds_unshift (hM.row _ le_rfl j (by omega)) rfl) (by ring),
    loadHolds_unshift ?_ (by ring)⟩
  rw [hT.hr] at hz
  have := readsAt_getD hz (k := j) (by simp only; rw [hl, hμL]; exact hj)
  exact this

theorem gk_word4 : word 4 0 0 = gen ^ 2 := word_two_pow (a := 2) (by decide)

theorem gk_isInK_one_add (a : ℕ) : IsInK (word 1 0 0 + gen ^ a) := by
  rw [word_one, ← pow_zero gen]; exact isInK_add (gen_pow_isInK 0) (gen_pow_isInK a)

theorem gk_one_add_ne {a : ℕ} (ha : a < 33) (h : word 1 0 0 + gen ^ a ≠ 0) : 0 < a := by
  rcases Nat.eq_zero_or_pos a with rfl | h'
  · exact absurd (by rw [word_one, pow_zero]; exact e_add_self 1) h
  · exact h'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_bus_gkr`'s body holds** on an honest memory, returning the run's state, cursor and
values. -/
theorem gkr_holds (hT : T.Ok μ cv xs r cv') (hμ : μ < 33) {rd : Reader}
    {cur zeta layers rounds pts pb dsb rcy rct1 rct2 : E}
    (hM : GkrMem rd T μ cv cur layers rounds pts pb dsb) (hx : ReadsAt rd cur xs)
    (hz : ReadsAt rd zeta r.2.1) (hrc1 : LoadHolds rd (gen ^ μ) 0 rct1) (hrc2 : LoadHolds rd rcy 0 rct2)
    (hrck : word 4294967296 0 0 = gen ^ μ * rcy) :
    Stmt.HoldsList (coreProgram.Rel rd) rd (vbgσ zeta (digestScalars cv).1 (digestScalars cv).2 cur
      (gen ^ μ) layers rounds pts pb dsb rcy rct1 rct2 T.cnt⁻¹ T.x0 T.cnt (gen ^ (μ % 2))
      (gen ^ (μ / 2)) (cur * gen ^ gCur (μ % 2) (μ / 2)) (pts * gen ^ (40 * (μ % 2 + μ / 2)))
      ((T.P (μ / 2)).values.getD 0 0) ((T.P (μ / 2)).values.getD 1 0) ((T.P (μ / 2)).values.getD 2 0)
      cv (T.C (μ / 2)) T.oes) (Fn.body Data.core10) False
      (fun rs => rs = [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2) := by
  obtain ⟨hx0, hcnt, hodd, -⟩ := hT.reads hx
  have hμL : gL (μ % 2) (μ / 2) = μ := by unfold gL; omega
  have hret : [(digestScalars cv').1, (digestScalars cv').2, cur * gen ^ xs.length] ++ r.2.2 =
      [(digestScalars (T.C (μ / 2))).1, (digestScalars (T.C (μ / 2))).2, cur * gen ^ gCur (μ % 2) (μ / 2),
        (T.P (μ / 2)).values.getD 0 0, (T.P (μ / 2)).values.getD 1 0, (T.P (μ / 2)).values.getD 2 0] := by
    rw [hT.hcv, hT.xs_len, hT.hr]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and]
    exact hT.vals le_rfl
  rw [hret]
  have e0 : [(digestScalars (vbgCv0 cv T.x0 T.cnt)).1, (digestScalars (vbgCv0 cv T.x0 T.cnt)).2,
      cur * word 4 0 0, T.x0, T.x0, T.cnt, pts, word 1 0 0] = gLay0 T cv cur pts := by
    rw [gk_word4, word_one, gLay0, pow_zero]
  have hl0 : ∀ k < 8, LoadHolds rd layers k ([(digestScalars (vbgCv0 cv T.x0 T.cnt)).1,
      (digestScalars (vbgCv0 cv T.x0 T.cnt)).2, cur * word 4 0 0, T.x0, T.x0, T.cnt, pts,
      word 1 0 0].getD k 0) := by
    rw [e0]
    rcases Nat.mod_two_eq_zero_or_one μ with h | h
    · intro k hk
      have := hM.lay 0 (Nat.zero_le _) k hk
      obtain ⟨hp, hc⟩ := hT.even h
      have e : gLay T (μ % 2) cur pts 0 = gLay0 T cv cur pts := by
        rw [gLay, gLay0, hp, hc, h]; simp [gCur, gPos]
      rwa [e, show 8 * gL (μ % 2) 0 + k = k by unfold gL; omega] at this
    · exact hM.lay0 h
  have hds : LoadHolds rd (dsb * gen ^ μ) 0 (gen ^ (μ % 2)) :=
    loadHolds_unshift (by rw [← vbgDs_get hμ]; exact hM.ds μ (by omega)) rfl
  have hnp : LoadHolds rd (pb * gen ^ μ) 0 (gen ^ (μ / 2)) :=
    loadHolds_unshift (by rw [← vbgPb_get hμ]; exact hM.pb μ (by omega)) rfl
  refine vbg_holds (oes := T.oes) rfl (by simpa using hrc1) hrc2 hrck hx0 hcnt
    (by rw [word_zero, add_zero]; exact mul_inv_cancel₀ hT.hcnt) hl0 hM.pb hM.ds hds
    (by rw [add_comm]; exact gk_isInK_one_add _) (fun hne => ?_) hnp (gk_isInK_one_add _)
    (fun hne => ?_) (fun k hk => ?_) (gk_isInK_one_add _) (fun hne => ?_)
  · have hs : μ % 2 = 1 := by
      have := gk_one_add_ne (a := μ % 2) (by omega) (by rwa [add_comm] at hne)
      omega
    obtain ⟨hchk, hpt, hvl, hcv0⟩ := hT.odd hs
    refine ⟨fun i hi => by rw [gk_word4]; exact hodd hs i hi, ?_, ?_, fun k hk => ?_⟩
    · rw [← hchk, polyEval_three]
    · have := hM.row 0 (Nat.zero_le _) 0 (by omega)
      rw [hpt, hs] at this
      rw [word_g40]; exact loadHolds_unshift this rfl
    · have := hM.lay 0 (Nat.zero_le _) k hk
      have e : gLay T (μ % 2) cur pts 0 = [(digestScalars (sqCv (l10cv (sqCv (vbgCv0 cv T.x0 T.cnt)) T.oes 6))).1,
          (digestScalars (sqCv (l10cv (sqCv (vbgCv0 cv T.x0 T.cnt)) T.oes 6))).2,
          cur * word 4 0 0 * word 64 0 0,
          T.oes 0 + (challengeOf (sqCv (l10cv (sqCv (vbgCv0 cv T.x0 T.cnt)) T.oes 6))) * (T.oes 0 + T.oes 1),
          T.oes 2 + (challengeOf (sqCv (l10cv (sqCv (vbgCv0 cv T.x0 T.cnt)) T.oes 6))) * (T.oes 2 + T.oes 3),
          T.oes 4 + (challengeOf (sqCv (l10cv (sqCv (vbgCv0 cv T.x0 T.cnt)) T.oes 6))) * (T.oes 4 + T.oes 5),
          pts * word 1099511627776 0 0, word 2 0 0] := by
        rw [gLay, hcv0, hvl, hs, gk_word4, word_g6, word_g40, word_gen]
        simp only [List.getD_cons_zero, List.getD_cons_succ, gCur, gPos, List.cons.injEq, and_true]
        refine ⟨trivial, trivial, by rw [mul_assoc, ← pow_add], trivial, trivial, trivial, trivial, pow_one gen⟩
      rwa [e, show 8 * gL (μ % 2) 0 + k = 8 + k by unfold gL; omega] at this
  · have := gk_one_add_ne (by omega) hne
    rw [word_one]; exact gkr_loop10 hT hμ hM hx this
  · have := hM.lay (μ / 2) le_rfl k (by omega)
    rw [hμL] at this
    have e : (gLay T (μ % 2) cur pts (μ / 2)).getD k 0 = [(digestScalars (T.C (μ / 2))).1,
        (digestScalars (T.C (μ / 2))).2, cur * gen ^ gCur (μ % 2) (μ / 2), (T.P (μ / 2)).values.getD 0 0,
        (T.P (μ / 2)).values.getD 1 0, (T.P (μ / 2)).values.getD 2 0,
        pts * gen ^ (40 * (μ % 2 + μ / 2))].getD k 0 := by
      interval_cases k <;> rfl
    rw [e] at this
    rw [← pow_mul, mul_comm μ 8]; exact loadHolds_unshift this rfl
  · have := gk_one_add_ne hμ hne
    rw [word_one]; exact gkr_loop11 hT hM hz hμ this

end

end
end LeanVM.Guest.B1.VerifySub
