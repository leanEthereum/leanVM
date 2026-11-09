/-
  LeanVM.Guest.B1.Opening.QueriesComplete1

  The completeness of a query's row: its packs and its dot product hold at the honest values.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesHonest

/-!
# A query's row, completeness

With the valuation `σ` the honest values `d.val` on the query's range (`hv`) and the weights in
memory at `wp`, every atom of the packs (`oqPacks_complete`), of the dot product
(`oqDot_complete`) and of the padding run (`oqPad_complete`) holds.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace QD

variable (d : QD) {rd : Reader} {σ : Val}

/-- The query's places in order. -/
theorem places : d.b + d.s.R ≤ d.k1 ∧ d.k1 + d.s.D ≤ d.kL ∧ d.kL + d.s.chainLen = d.ch ∧
    d.kL + 25 ≤ d.ch ∧ d.e = d.ch :=
  ⟨by rw [k1_eq]; omega, le_kL d, (ch_eq d).symm, by rw [ch_eq]; unfold Oq.chainLen; omega,
    e_eq d⟩

theorem partV_zero (h : ℕ) : d.partV h 0 = d.W (d.s.lo * h) * d.w 0 := by
  simp [partV]

theorem partV_succ (h l : ℕ) :
    d.partV h (l + 1) = d.partV h l + d.W (d.s.lo * h + (l + 1)) * d.w (l + 1) := by
  unfold partV; rw [foldl_range_succ]

theorem dotAfterV_zero : d.dotAfterV 0 = d.w (d.s.lo + 0) * d.partV 0 (d.s.lo - 1) := by
  simp [dotAfterV]

theorem dotAfterV_succ (h : ℕ) :
    d.dotAfterV (h + 1) = d.dotAfterV h + d.w (d.s.lo + (h + 1)) * d.partV (h + 1) (d.s.lo - 1) := by
  unfold dotAfterV; rw [foldl_range_succ]

theorem pk_eq (j : ℕ) :
    d.pk j = E.ofLimbs (d.row.getD (2 * j) 0) (d.row.getD (2 * j + 1) 0) 0 := by
  rw [pk, rw, rw, word_y, ofK_add_y_mul_ofK]

theorem rw_inK (j : ℕ) : IsInK (d.rw j) := ofK_isInK _

theorem W_base1 (hb : d.s.base = 1) (jw : ℕ) : d.W jw = d.rw jw := by
  simp [W, rowWord, hb, QD.rw]

theorem W_even (hb : d.s.base = 0) {jw : ℕ} (he : jw % 2 = 0) :
    d.W jw = d.pk (3 * jw / 2) + word 0 0 1 * d.rw (3 * jw + 2) := by
  rw [pk_eq, show 2 * (3 * jw / 2) = 3 * jw by omega, word_yy, QD.rw, add_y_mul_y_mul_ofK]
  simp [W, rowWord, hb]

theorem W_odd (hb : d.s.base = 0) {jw : ℕ} (ho : jw % 2 = 1) :
    d.W jw = d.rw (3 * jw) + word 0 1 0 * d.pk ((3 * jw + 1) / 2) := by
  rw [pk_eq, show 2 * ((3 * jw + 1) / 2) = 3 * jw + 1 by omega, word_y, QD.rw,
    ofK_add_y_mul_ofLimbs]
  simp [W, rowWord, hb]

/-! ## The packs -/

theorem oqPacks_complete (hv : ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i) :
    ∀ a, Stmt.atom a ∈ oqPacksT d.b d.s.R → a.Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  intro a ha
  simp only [oqPacksT, List.mem_flatten, List.mem_map, List.mem_range] at ha
  obtain ⟨_, ⟨j, hj, rfl⟩, ha⟩ := ha
  have hk := k1_eq d
  have r0 : σ (.n (d.b + 2 * j)) = d.rw (2 * j) := by
    rw [hv _ (by omega) (by omega), val_row d (by omega)]
  have r1 : σ (.n (d.b + 2 * j + 1)) = d.rw (2 * j + 1) := by
    rw [hv _ (by omega) (by omega), Nat.add_assoc, val_row d (by omega)]
  have v : ∀ t < 3, σ (.n (d.b + d.s.R + 3 * j + t)) =
      [word 0 1 0, word 0 1 0 * d.rw (2 * j + 1), d.pk j].getD t 0 := fun t ht => by
    rw [hv _ (by omega) (by omega), val_pack d hj ht]
  have v0 := v 0 (by omega); have v1 := v 1 (by omega); have v2 := v 2 (by omega)
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at v0 v1 v2
  simp only [oqPackT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact ⟨by rw [r0]; exact rw_inK d _, by rw [r1]; exact rw_inK d _⟩
  · exact v0
  · show σ _ = σ _ * σ _
    rw [v1, v0, r1]
  · show σ _ = σ _ + σ _
    rw [v2, r0, v1, pk]

/-! ## The dot product -/

theorem dot_idx (hs : d.s.RowShape) {h l o : ℕ} (hh : h < d.s.I / d.s.lo) (hl : l < d.s.lo)
    (ho : o < (if l = 0 then 2 + d.s.tsz else 3 + d.s.tsz)) :
    gsOff d.s.G h + tsOff d.s.tsz l + o < d.s.D := by
  unfold gsOff tsOff
  rcases shape_nums hs with ⟨-, hI, ht, hlo, hG, -, hD, -⟩ | ⟨-, hI, ht, hlo, hG, -, hD, -⟩ <;>
    simp only [hI, ht, hlo, hG, hD] at hh hl ho ⊢ <;> split <;> split <;> split at ho <;> omega

theorem tail_idx (hs : d.s.RowShape) {h o : ℕ} (hh : h < d.s.I / d.s.lo)
    (ho : o < (if h = 0 then 2 else 3)) : gsOff d.s.G h + (d.s.G - 2 + o) < d.s.D := by
  unfold gsOff
  rcases shape_nums hs with ⟨-, hI, -, hlo, hG, -, hD, -⟩ | ⟨-, hI, -, hlo, hG, -, hD, -⟩ <;>
    simp only [hI, hlo, hG, hD] at hh ho ⊢ <;> split <;> split at ho <;> omega

theorem oqDot_complete (hs : d.s.RowShape) {wp : V}
    (hv : ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i)
    (hw : ∀ l < d.s.lo + d.s.I / d.s.lo, LoadHolds rd (σ wp) l (d.w l)) :
    ∀ a, Stmt.atom a ∈ oqDotT d.s wp d.b → a.Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hk := k1_eq d
  have hlo : d.s.lo = 8 := by rcases shape_nums hs with h | h <;> exact h.2.2.2.1
  have hR : ∀ jw, jw < d.s.I → (d.s.base = 1 → jw < d.s.R) ∧ (d.s.base = 0 → 3 * jw + 2 < d.s.R) :=
    fun jw hjw => by
      rcases shape_nums hs with ⟨hb, hI, -, -, -, hR, -⟩ | ⟨hb, hI, -, -, -, hR, -⟩ <;>
        simp only [hb, hI, hR] at hjw ⊢ <;> omega
  have hIlo : ∀ h l, h < d.s.I / d.s.lo → l < d.s.lo → d.s.lo * h + l < d.s.I := fun h l hh hl => by
    rcases shape_nums hs with ⟨-, hI, -, hlo', -⟩ | ⟨-, hI, -, hlo', -⟩ <;>
      simp only [hI, hlo'] at hh hl ⊢ <;> omega
  -- σ on a term, on a group's tail
  have hterm : ∀ h < d.s.I / d.s.lo, ∀ l < d.s.lo, ∀ o < (if l = 0 then 2 + d.s.tsz else 3 + d.s.tsz),
      σ (.n (oqTs d.s d.b h l + o)) = d.termV h l o := fun h hh l hl o ho => by
    have := dot_idx d hs hh hl ho
    rw [oqTs_eq, show oqK1 d.b d.s.R + gsOff d.s.G h + tsOff d.s.tsz l + o =
        d.k1 + (gsOff d.s.G h + tsOff d.s.tsz l + o) by simp only [QD.k1]; omega,
      hv _ (by omega) (by omega), val_dot d this, dotV_term d hs hl ho]
  have htail : ∀ h < d.s.I / d.s.lo, ∀ o < (if h = 0 then 2 else 3),
      σ (.n (oqGs d.s d.b h + d.s.G - 2 + o)) =
        [d.w (d.s.lo + h), d.w (d.s.lo + h) * d.partV h (d.s.lo - 1), d.dotAfterV h].getD o 0 :=
    fun h hh o ho => by
      have := tail_idx d hs hh ho
      have hG : 2 ≤ d.s.G := by rcases shape_nums hs with h | h <;> omega
      rw [show oqGs d.s d.b h + d.s.G - 2 + o = d.k1 + (gsOff d.s.G h + (d.s.G - 2 + o)) by
          simp only [oqGs, gsOff, show oqK1 d.b d.s.R = d.k1 from rfl]; split <;> omega,
        hv _ (by omega) (by omega), val_dot d this, dotV_tail d hs ho]
  -- the running sums
  have hpart : ∀ h < d.s.I / d.s.lo, ∀ l < d.s.lo, σ (.n (oqPart d.s d.b h l)) = d.partV h l :=
    fun h hh l hl => by
      rcases Nat.eq_zero_or_pos l with rfl | hpos
      · rw [show oqPart d.s d.b h 0 = oqTs d.s d.b h 0 + (d.s.tsz + 1) by simp [oqPart]; omega,
          hterm h hh 0 hl _ (by simp only [↓reduceIte]; omega), termV]
        simp [partV_zero]
      · rw [show oqPart d.s d.b h l = oqTs d.s d.b h l + (d.s.tsz + 2) by
          simp [oqPart, show l ≠ 0 by omega]; omega,
          hterm h hh l hl _ (by simp only [show l ≠ 0 by omega, ↓reduceIte]; omega)]
        simp [termV]
  have hdot : ∀ h < d.s.I / d.s.lo, σ (.n (oqDotAfter d.s d.b h)) = d.dotAfterV h := fun h hh => by
    rcases Nat.eq_zero_or_pos h with rfl | hpos
    · rw [show oqDotAfter d.s d.b 0 = oqGs d.s d.b 0 + d.s.G - 2 + 1 by
        have : 2 ≤ d.s.G := by rcases shape_nums hs with h | h <;> omega
        simp [oqDotAfter]; omega, htail 0 hh 1 (by simp)]
      simp [dotAfterV_zero]
    · rw [show oqDotAfter d.s d.b h = oqGs d.s d.b h + d.s.G - 2 + 2 by
        have : 2 ≤ d.s.G := by rcases shape_nums hs with h | h <;> omega
        simp [oqDotAfter, show h ≠ 0 by omega]; omega, htail h hh 2 (by simp [show h ≠ 0 by omega])]
      rfl
  -- the word a term reads
  have hword : ∀ h < d.s.I / d.s.lo, ∀ l < d.s.lo,
      σ (.n (oqWordV d.s d.b h l)) = d.W (d.s.lo * h + l) := fun h hh l hl => by
    by_cases hb : d.s.base = 1
    · simp only [oqWordV, hb, ↓reduceIte]
      rw [hv _ (by omega) (by have := (hR _ (hIlo h l hh hl)).1 hb; omega),
        val_row d ((hR _ (hIlo h l hh hl)).1 hb), W_base1 d hb]
    · have ht : d.s.tsz = 3 := by simp [Oq.tsz, hb]
      simp only [oqWordV, hb, ↓reduceIte]
      rw [hterm h hh l hl 2 (by rw [ht]; split <;> omega), termV]
      simp only [show 2 < d.s.tsz by omega, ↓reduceIte, wordStmtV]
      split <;> rfl
  intro a ha
  simp only [oqDotT, List.mem_flatten, List.mem_map, List.mem_range] at ha
  obtain ⟨_, ⟨h, hh, rfl⟩, ha⟩ := ha
  simp only [oqGroupT, List.mem_append, List.mem_flatten, List.mem_map, List.mem_range] at ha
  rcases ha with (⟨_, ⟨l, hl, rfl⟩, ha⟩ | ha) | ha
  · -- a term
    simp only [oqTermT, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · -- the word statements (deeper levels)
      by_cases hb : d.s.base = 1
      · simp [hb] at ha
      · simp only [hb, ↓reduceIte] at ha
        have hb0 : d.s.base = 0 := by
          rcases shape_nums hs with h | h
          · exact absurd h.1 hb
          · exact h.1
        have ht : d.s.tsz = 3 := by simp [Oq.tsz, hb]
        have hT := fun o (ho : o < 3) => hterm h hh l hl o (by rw [ht]; split <;> omega)
        have t0 := hT 0 (by omega); have t1 := hT 1 (by omega); have t2 := hT 2 (by omega)
        simp only [termV, ht, show (0 : ℕ) < 3 by omega, show (1 : ℕ) < 3 by omega,
          show (2 : ℕ) < 3 by omega, ↓reduceIte, wordStmtV, Nat.add_zero] at t0 t1 t2
        have hjw := (hR _ (hIlo h l hh hl)).2 hb0
        unfold oqWordT at ha
        split at ha <;> rename_i he
        · simp only [he, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ] at t0 t1 t2
          simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
          rcases ha with rfl | rfl | rfl
          · exact t0
          · show σ _ = σ _ * σ _
            rw [t1, t0, hv _ (by omega) (by omega), val_row d (by omega)]
          · show σ _ = σ _ + σ _
            rw [t2, t1, show oqPk d.b d.s.R (3 * (d.s.lo * h + l) / 2) =
                d.b + d.s.R + 3 * (3 * (d.s.lo * h + l) / 2) + 2 by simp [oqPk],
              hv _ (by omega) (by omega), val_pack d (by omega) (by omega)]
            simp [W_even d hb0 he]
        · have ho : (d.s.lo * h + l) % 2 = 1 := by omega
          simp only [he, ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ] at t0 t1 t2
          simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
          rcases ha with rfl | rfl | rfl
          · exact t0
          · show σ _ = σ _ * σ _
            rw [t1, t0, show oqPk d.b d.s.R ((3 * (d.s.lo * h + l) + 1) / 2) =
                d.b + d.s.R + 3 * ((3 * (d.s.lo * h + l) + 1) / 2) + 2 by simp [oqPk],
              hv _ (by omega) (by omega), val_pack d (by omega) (by omega)]
            rfl
          · show σ _ = σ _ + σ _
            rw [t2, t1, hv _ (by omega) (by omega), val_row d (by omega), W_odd d hb0 ho]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      rcases ha with rfl | rfl
      · have := hterm h hh l hl d.s.tsz (by split <;> omega)
        simp only [termV, lt_irrefl, ↓reduceIte] at this
        show LoadHolds rd _ _ _
        rw [this]; exact hw l (by omega)
      · have t1 := hterm h hh l hl (d.s.tsz + 1) (by split <;> omega)
        have t0 := hterm h hh l hl d.s.tsz (by split <;> omega)
        simp only [termV, lt_irrefl, ↓reduceIte, show ¬ d.s.tsz + 1 < d.s.tsz by omega,
          show d.s.tsz + 1 ≠ d.s.tsz by omega] at t1 t0
        show σ _ = σ _ * σ _
        rw [show oqTs d.s d.b h l + d.s.tsz + 1 = oqTs d.s d.b h l + (d.s.tsz + 1) by omega, t1,
          hword h hh l hl, t0]
    · split at ha
      · simp at ha
      · rename_i hl0
        simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
        subst ha
        have t2 := hterm h hh l hl (d.s.tsz + 2) (by simp only [hl0, ↓reduceIte]; omega)
        have t1 := hterm h hh l hl (d.s.tsz + 1) (by split <;> omega)
        simp only [termV, show ¬ d.s.tsz + 2 < d.s.tsz by omega, show d.s.tsz + 2 ≠ d.s.tsz by omega,
          show d.s.tsz + 2 ≠ d.s.tsz + 1 by omega, show ¬ d.s.tsz + 1 < d.s.tsz by omega,
          show d.s.tsz + 1 ≠ d.s.tsz by omega, ↓reduceIte] at t2 t1
        show σ _ = σ _ + σ _
        obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        rw [show oqTs d.s d.b h (l' + 1) + d.s.tsz + 2 = oqTs d.s d.b h (l' + 1) + (d.s.tsz + 2) by omega,
          t2, show oqTs d.s d.b h (l' + 1) + d.s.tsz + 1 = oqTs d.s d.b h (l' + 1) + (d.s.tsz + 1) by omega,
          t1, Nat.add_sub_cancel, hpart h hh l' (by omega), partV_succ]
  · -- the group's tail
    simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
    rcases ha with rfl | rfl
    · have := htail h hh 0 (by split <;> omega)
      simp only [List.getD_cons_zero, Nat.add_zero] at this
      show LoadHolds rd _ _ _
      rw [this]; exact hw _ (by omega)
    · have t1 := htail h hh 1 (by split <;> omega)
      have t0 := htail h hh 0 (by split <;> omega)
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at t1 t0
      show σ _ = σ _ * σ _
      have hG : 2 ≤ d.s.G := by rcases shape_nums hs with h | h <;> omega
      rw [show oqGs d.s d.b h + d.s.G - 1 = oqGs d.s d.b h + d.s.G - 2 + 1 by omega, t1, t0,
        hpart h hh _ (by omega)]
  · split at ha
    · simp at ha
    · rename_i hh0
      simp only [List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
      subst ha
      have hG : 2 ≤ d.s.G := by rcases shape_nums hs with h | h <;> omega
      have t2 := htail h hh 2 (by simp [hh0])
      have t1 := htail h hh 1 (by simp [hh0])
      simp only [List.getD_cons_zero, List.getD_cons_succ] at t2 t1
      show σ _ = σ _ + σ _
      obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
      have e2 : σ (.n (oqGs d.s d.b (h' + 1) + d.s.G)) = d.dotAfterV (h' + 1) := by
        rw [show oqGs d.s d.b (h' + 1) + d.s.G = oqGs d.s d.b (h' + 1) + d.s.G - 2 + 2 by omega, t2]
      have e1 : σ (.n (oqGs d.s d.b (h' + 1) + d.s.G - 1)) =
          d.w (d.s.lo + (h' + 1)) * d.partV (h' + 1) (d.s.lo - 1) := by
        rw [show oqGs d.s d.b (h' + 1) + d.s.G - 1 = oqGs d.s d.b (h' + 1) + d.s.G - 2 + 1 by omega,
          t1]
      rw [e2, e1, Nat.add_sub_cancel, hdot h' (by omega), dotAfterV_succ]

/-! ## The padding run -/

theorem oqPad_complete (he : d.emit = true)
    (hv : ∀ i, d.b ≤ i → i < d.e → σ (.n i) = d.val i) :
    ∀ a, Stmt.atom a ∈ oqPadT (oqK1 d.b d.s.R + d.s.D) → a.Holds rd σ := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := d.places
  have hk := k1_eq d
  have hkL : d.kL = d.k1 + d.s.D + 5 := by rw [kL_eq, he]; rfl
  have v : ∀ i < 5, σ (.n (d.k1 + d.s.D + i)) =
      [word 1 0 0, word 0 0 0, word 0 0 0, word 0 0 0, word 0 0 0].getD i 0 := fun i hi => by
    rw [hv _ (by omega) (by omega), val_pad d he hi]
  intro a ha
  simp only [oqPadT, List.mem_cons, List.not_mem_nil, or_false, Stmt.atom.injEq] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · show σ (.n (d.k1 + d.s.D)) = _
    simpa using v 0 (by omega)
  · show σ (.n (d.k1 + d.s.D + 1)) = _
    simpa using v 1 (by omega)
  · show σ (.n (d.k1 + d.s.D + 2)) = _
    simpa using v 2 (by omega)
  · show σ (.n (d.k1 + d.s.D + 3)) = _
    simpa using v 3 (by omega)
  · show σ (.n (d.k1 + d.s.D + 4)) = _
    simpa using v 4 (by omega)

end QD

end
end LeanVM.Guest.B1
