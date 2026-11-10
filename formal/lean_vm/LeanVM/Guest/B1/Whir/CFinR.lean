/-
  LeanVM.Guest.B1.Whir.CFinR

  The residual queries and steps are pure blocks in order: their values evaluated, their loads
  the positions, the basis row and the high part.
-/

module

public import LeanVM.Guest.B1.Whir.CFinEval
public import LeanVM.Guest.B1.Whir.ResLoop

/-!
# The residual steps, in order

`osResSteps_ssa`: the steps of `residual_query` (`osResChain`, `novel_eval`) and the chains'
updates define their values in order from their first free value, reading only the position
pointer at the steps' offsets, the basis row's first `ncols` words and the high part's `nhs`
words (`osResSteps_loads`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The chain of `residual_query` -/

theorem osResChain_ssa (bd ro vo ncols : ℕ) : ∀ (f t ch pe : ℕ) (ws : List ℕ) (k : ℕ),
    ch < k → pe < k → bd < k → (∀ x ∈ ws, x < k) →
    SsaP k (osResChain bd ro vo ncols f t ch pe ws k).1 (osResChain bd ro vo ncols f t ch pe ws k).2.2.2.2 ∧
      (osResChain bd ro vo ncols f t ch pe ws k).2.1 < (osResChain bd ro vo ncols f t ch pe ws k).2.2.2.2 ∧
      (osResChain bd ro vo ncols f t ch pe ws k).2.2.1 < (osResChain bd ro vo ncols f t ch pe ws k).2.2.2.2 ∧
      (∀ x ∈ (osResChain bd ro vo ncols f t ch pe ws k).2.2.2.1,
        x < (osResChain bd ro vo ncols f t ch pe ws k).2.2.2.2) ∧
      (∀ p o, (p, o) ∈ loadsOf (osResChain bd ro vo ncols f t ch pe ws k).1 →
        p = bd ∧ ∃ s, t ≤ s ∧ s < t + f ∧ s ≠ ncols ∧ o = ro + s)
  | 0, t, ch, pe, ws, k, hch, hpe, _, hws => ⟨.nil, hch, hpe, hws, by simp [osResChain, loadsOf]⟩
  | f + 1, t, ch, pe, ws, k, hch, hpe, hbd, hws => by
    have hws' : ∀ x ∈ (if t < 3 then ws ++ [k + 2] else ws), x < k + 3 := by
      intro x hx
      split_ifs at hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact lt_trans (hws x hx) (by omega)
        · simp at hx; omega
      · exact lt_trans (hws x hx) (by omega)
    unfold osResChain
    by_cases hn : t = ncols
    · simp only [hn, ↓reduceIte]
      have ih := osResChain_ssa bd ro vo ncols f (ncols + 1) (k + 2) pe
        (if ncols < 3 then ws ++ [k + 2] else ws) (k + 3) (by omega) (by omega) (by omega)
        (by rw [← hn]; exact hws')
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      refine ⟨.const le_rfl (.add (by omega) (by omega) (by omega) (.mul (by omega) (by omega) (by omega) h1)),
        h2, h3, h4, fun p o hm ↦ ?_⟩
      simp only [List.cons_append, List.nil_append, loadsOf] at hm
      obtain ⟨hp, s, hs1, hs2, hs3, hs4⟩ := h5 p o hm
      exact ⟨hp, s, by omega, by omega, hs3, hs4⟩
    · simp only [hn, ↓reduceIte]
      have ih := osResChain_ssa bd ro vo ncols f (t + 1) (k + 2) (k + 5)
        (if t < 3 then ws ++ [k + 2] else ws) (k + 6) (by omega) (by omega) (by omega)
        (fun x hx ↦ lt_trans (hws' x hx) (by omega))
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      refine ⟨.const le_rfl (.add (by omega) (by omega) (by omega) (.mul (by omega) (by omega) (by omega)
        (.load (by omega) (by omega) (.add (by omega) (by omega) (by omega)
          (.mul (by omega) (by omega) (by omega) h1))))), h2, h3, h4, fun p o hm ↦ ?_⟩
      simp only [List.cons_append, List.nil_append, loadsOf, List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        exact ⟨hm.1, t, le_rfl, by omega, hn, hm.2⟩
      · obtain ⟨hp, s, hs1, hs2, hs3, hs4⟩ := h5 p o hm
        exact ⟨hp, s, by omega, by omega, hs3, hs4⟩

/-! ## `novel_eval` -/

theorem osNovelLevel_ssa (hp ho : ℕ) (ins : Option (List ℕ)) (nIn w : ℕ) :
    ∀ (f k : ℕ), hp < k → w < k → (∀ vs, ins = some vs → ∀ x ∈ vs, x < k) →
      f ≤ (nIn + 1) / 2 →
      SsaP k (osNovelLevel hp ho ins nIn w f k).1 (osNovelLevel hp ho ins nIn w f k).2.2 ∧
        (∀ x ∈ (osNovelLevel hp ho ins nIn w f k).2.1, x < (osNovelLevel hp ho ins nIn w f k).2.2) ∧
        (∀ p o, (p, o) ∈ loadsOf (osNovelLevel hp ho ins nIn w f k).1 →
          ins = none ∧ p = hp ∧ ∃ c, c < nIn ∧ o = ho + c)
  | 0, k, _, _, _, _ => ⟨.nil, by simp [osNovelLevel], by simp [osNovelLevel, loadsOf]⟩
  | f + 1, k, hhp, hw, hins, hf => by
    unfold osNovelLevel
    simp only
    set m := (nIn + 1) / 2 - (f + 1) with hm
    have hm2 : 2 * m < nIn := by omega
    rcases ins with _ | vs
    · simp only
      by_cases two : 2 * m + 1 < nIn
      · simp only [two, ↓reduceIte]
        have ih := osNovelLevel_ssa hp ho none nIn w f (k + 1 + 1 + 2) (by omega) (by omega)
          (by simp) (by omega)
        obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨.load le_rfl (by omega) (.load (by omega) (by omega) (.mul (by omega) (by omega)
          (by omega) (.add (by omega) (by omega) (by omega) h1))), ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · have := h1.le; omega
          · exact h2 x hx
        · intro p o hmem
          simp only [List.cons_append, List.nil_append, loadsOf, List.mem_cons, Prod.mk.injEq]
            at hmem
          rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hmem
          · exact ⟨trivial, rfl, 2 * m, hm2, rfl⟩
          · exact ⟨trivial, rfl, 2 * m + 1, two, by ring⟩
          · exact ⟨trivial, (h3 p o hmem).2⟩
      · simp only [two, ↓reduceIte]
        have ih := osNovelLevel_ssa hp ho none nIn w f (k + 1 + 1) (by omega) (by omega)
          (by simp) (by omega)
        obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨.load le_rfl (by omega) (.copy (by omega) (by omega) h1), ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · have := h1.le; omega
          · exact h2 x hx
        · intro p o hmem
          simp only [List.cons_append, List.nil_append, loadsOf, List.mem_cons, Prod.mk.injEq]
            at hmem
          rcases hmem with ⟨rfl, rfl⟩ | hmem
          · exact ⟨trivial, rfl, 2 * m, hm2, rfl⟩
          · exact ⟨trivial, (h3 p o hmem).2⟩
    · simp only
      have hv : ∀ i, vs.getD i 0 < k ∨ vs.getD i 0 = 0 := fun i ↦ by
        rw [List.getD_eq_getElem?_getD]
        rcases h : vs[i]? with _ | x
        · simp
        · exact Or.inl (hins vs rfl x (List.mem_of_getElem? h))
      have hv' : ∀ i, vs.getD i 0 < k := fun i ↦ by
        rcases hv i with h | h
        · exact h
        · rw [h]; omega
      by_cases two : 2 * m + 1 < nIn
      · simp only [two, ↓reduceIte]
        have ih := osNovelLevel_ssa hp ho (some vs) nIn w f (k + 2) (by omega) (by omega)
          (fun vs' h x hx ↦ by
            simp only [Option.some.injEq] at h; subst h
            exact lt_trans (hins _ rfl x hx) (by omega)) (by omega)
        obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨.mul le_rfl (by omega) (hv' _) (.add (by omega) (lt_trans (hv' _) (by omega))
          (by omega) h1), ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · have := h1.le; omega
          · exact h2 x hx
        · intro p o hmem
          simp only [List.cons_append, List.nil_append, loadsOf] at hmem
          exact h3 p o hmem
      · simp only [two, ↓reduceIte]
        have ih := osNovelLevel_ssa hp ho (some vs) nIn w f (k + 1) (by omega) (by omega)
          (fun vs' h x hx ↦ by
            simp only [Option.some.injEq] at h; subst h
            exact lt_trans (hins _ rfl x hx) (by omega)) (by omega)
        obtain ⟨h1, h2, h3⟩ := ih
        refine ⟨.copy le_rfl (hv' _) h1, ?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · have := h1.le; omega
          · exact h2 x hx
        · intro p o hmem
          simp only [List.nil_append] at hmem
          exact h3 p o hmem

theorem osNovelLevels_ssa (hp ho n nbits : ℕ) (ws : List ℕ) :
    ∀ (f i : ℕ) (ins : Option (List ℕ)) (k : ℕ), hp < k → (∀ x ∈ ws, x < k) →
      (∀ vs, ins = some vs → ∀ x ∈ vs, x < k) → (ins = none → i = 0) →
      SsaP k (osNovelLevels hp ho n nbits ws f i ins k).1 (osNovelLevels hp ho n nbits ws f i ins k).2.2 ∧
        (osNovelLevels hp ho n nbits ws f i ins k).2.1 < (osNovelLevels hp ho n nbits ws f i ins k).2.2 ∧
        (∀ p o, (p, o) ∈ loadsOf (osNovelLevels hp ho n nbits ws f i ins k).1 →
          p = hp ∧ ∃ c, c < n ∧ o = ho + c)
  | 0, i, ins, k, hhp, _, hins, _ => by
    refine ⟨.nil, ?_, by simp [osNovelLevels, loadsOf]⟩
    simp only [osNovelLevels]
    rcases ins with _ | vs
    · simp only [Option.getD_none, List.headD_nil]; omega
    · simp only [Option.getD_some]
      rcases vs with _ | ⟨x, vs⟩
      · simp only [List.headD_nil]; omega
      · exact hins _ rfl x (by simp)
  | f + 1, i, ins, k, hhp, hws, hins, hi => by
    have hw : ws.getD i 0 < k := by
      rw [List.getD_eq_getElem?_getD]
      rcases h : ws[i]? with _ | x
      · simp only [Option.getD_none]; omega
      · exact hws x (List.mem_of_getElem? h)
    have hl := osNovelLevel_ssa hp ho ins ((n + 2 ^ i - 1) / 2 ^ i) (ws.getD i 0)
      (((n + 2 ^ i - 1) / 2 ^ i + 1) / 2) k hhp hw hins le_rfl
    obtain ⟨l1, l2, l3⟩ := hl
    set l := osNovelLevel hp ho ins ((n + 2 ^ i - 1) / 2 ^ i) (ws.getD i 0)
        (((n + 2 ^ i - 1) / 2 ^ i + 1) / 2) k with hl
    have ih := osNovelLevels_ssa hp ho n nbits ws f (i + 1) (some l.2.1) l.2.2
      (by have := l1.le; omega)
      (fun x hx ↦ by have := l1.le; exact lt_of_lt_of_le (hws x hx) this)
      (fun vs h x hx ↦ by simp only [Option.some.injEq] at h; subst h; exact l2 x hx) (by simp)
    obtain ⟨r1, r2, r3⟩ := ih
    refine ⟨l1.append r1, r2, fun p o hm ↦ ?_⟩
    simp only [osNovelLevels, loadsOf_append, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨h0, hp', c, hc, ho'⟩ := l3 p o hm
      have := hi h0
      subst this
      exact ⟨hp', c, by simpa using hc, ho'⟩
    · exact r3 p o hm

theorem osNovelEval_ssa (hp ho n nbits : ℕ) (ws : List ℕ) (k : ℕ) (hn : 0 < n) (hhp : hp < k)
    (hws : ∀ x ∈ ws, x < k) :
    SsaP k (osNovelEval hp ho n nbits ws k).1 (osNovelEval hp ho n nbits ws k).2.2 ∧
      (osNovelEval hp ho n nbits ws k).2.1 < (osNovelEval hp ho n nbits ws k).2.2 ∧
      (∀ p o, (p, o) ∈ loadsOf (osNovelEval hp ho n nbits ws k).1 →
        p = hp ∧ ∃ c, c < n ∧ o = ho + c) := by
  unfold osNovelEval
  split_ifs
  · refine ⟨.load le_rfl hhp .nil, by simp, fun p o hm ↦ ?_⟩
    simp only [loadsOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    exact ⟨hm.1, 0, hn, by simp [hm.2]⟩
  · exact osNovelLevels_ssa hp ho n nbits ws nbits 0 none k hhp hws (by simp) fun _ ↦ rfl

/-! ## `residual_query` and the steps -/

theorem osResQuery_ssa (pos bd ro hp ho vo ncols nhs hbits k : ℕ) (hn : 0 < nhs) (hc0 : 0 < ncols)
    (hpos : pos < k)
    (hbd : bd < k) (hhp : hp < k) :
    SsaP k (osResQuery pos bd ro hp ho vo ncols nhs hbits k).1
        (osResQuery pos bd ro hp ho vo ncols nhs hbits k).2.2.2 ∧
      (osResQuery pos bd ro hp ho vo ncols nhs hbits k).2.1 <
        (osResQuery pos bd ro hp ho vo ncols nhs hbits k).2.2.2 ∧
      (osResQuery pos bd ro hp ho vo ncols nhs hbits k).2.2.1 <
        (osResQuery pos bd ro hp ho vo ncols nhs hbits k).2.2.2 ∧
      (∀ p o, (p, o) ∈ loadsOf (osResQuery pos bd ro hp ho vo ncols nhs hbits k).1 →
        (p = bd ∧ ∃ s, s < ncols + 1 ∧ s ≠ ncols ∧ o = ro + s) ∨ (p = hp ∧ ∃ c, c < nhs ∧ o = ho + c)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := osResChain_ssa bd ro vo ncols ncols 1 pos (k + 2) [k] (k + 3)
    (by omega) (by omega) (by omega) (by simp)
  set c := osResChain bd ro vo ncols ncols 1 pos (k + 2) [k] (k + 3) with hc
  obtain ⟨n1, n2, n3⟩ := osNovelEval_ssa hp ho nhs hbits c.2.2.2.1 c.2.2.2.2 hn
    (by have := c1.le; omega) c4
  have hc1 := c1.le
  have hn1 := n1.le
  set ne := osNovelEval hp ho nhs hbits c.2.2.2.1 c.2.2.2.2 with hne
  have e : osResQuery pos bd ro hp ho vo ncols nhs hbits k =
      (osCp k pos :: osLd (k + 1) bd ro :: osAdd (k + 2) (k + 1) pos :: (c.1 ++ (ne.1 ++
        [osMul ne.2.2 c.2.1 ne.2.1])), c.2.2.1, ne.2.2, ne.2.2 + 1) := by
    simp only [osResQuery, hc, hne, List.cons_append, List.nil_append, List.append_assoc]
  rw [e]
  dsimp only
  refine ⟨.copy le_rfl hpos (.load (by omega) (by omega) (.add (by omega) (by omega) (by omega)
    (c1.append (n1.append (.mul le_rfl (by omega) n2 .nil))))), by omega, by omega, fun p o hm ↦ ?_⟩
  simp only [loadsOf, loadsOf_append, List.mem_cons, List.mem_append, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | hm | hm | hm
  · exact Or.inl ⟨rfl, 0, by omega, by omega, rfl⟩
  · obtain ⟨hp', s, hs1, hs2, hs3, hs4⟩ := c5 p o hm
    exact Or.inl ⟨hp', s, by omega, hs3, hs4⟩
  · exact Or.inr (n3 p o hm)
  · simp at hm

theorem osResSteps_ssa (pp bd ro hp ho vo ncols nhs hbits mu : ℕ) (hn : 0 < nhs) (hc0 : 0 < ncols) :
    ∀ (js : List ℕ) (h hh k : ℕ), pp < k → bd < k → hp < k → mu < k → h < k → hh < k →
      SsaP k (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).1
          (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).2.2.2 ∧
        (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).2.1 <
          (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).2.2.2 ∧
        (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).2.2.1 <
          (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).2.2.2 ∧
        (∀ p o, (p, o) ∈ loadsOf (osResSteps pp bd ro hp ho vo ncols nhs hbits mu js h hh k).1 →
          (p = pp ∧ o ∈ js) ∨ (p = bd ∧ ∃ s, s < ncols ∧ o = ro + s) ∨
            (p = hp ∧ ∃ c, c < nhs ∧ o = ho + c))
  | [], h, hh, k, _, _, _, _, hh1, hh2 => ⟨.nil, hh1, hh2, by simp [osResSteps, loadsOf]⟩
  | j :: js, h, hh, k, hpp, hbd, hhp, hmu, hh1, hh2 => by
    obtain ⟨q1, q2, q3, q4⟩ := osResQuery_ssa k bd ro hp ho vo ncols nhs hbits (k + 1) hn hc0 (by omega)
      (by omega) (by omega)
    set q := osResQuery k bd ro hp ho vo ncols nhs hbits (k + 1) with hq
    have hq1 := q1.le
    obtain ⟨r1, r2, r3, r4⟩ := osResSteps_ssa pp bd ro hp ho vo ncols nhs hbits mu hn hc0 js
      (q.2.2.2 + 1) (q.2.2.2 + 3) (q.2.2.2 + 4) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨?_, r2, r3, fun p o hm ↦ ?_⟩
    · simp only [osResSteps, osResStep, List.append_assoc, List.cons_append,
        List.nil_append, ← hq]
      exact .load le_rfl (by omega) (q1.append (.add le_rfl (by omega) q2 (.mul (by omega) (by omega)
        (by omega) (.add (by omega) (by omega) (by omega) (.mul (by omega) (by omega) (by omega) r1)))))
    · simp only [osResSteps, osResStep, List.cons_append, List.append_assoc, loadsOf,
        loadsOf_append, List.mem_cons, List.mem_append, Prod.mk.injEq, ← hq] at hm
      rcases hm with ⟨rfl, rfl⟩ | hm | hm | hm
      · exact Or.inl ⟨rfl, by simp⟩
      · rcases q4 p o hm with ⟨hp', s, hs1, hs2, hs3⟩ | h'
        · exact Or.inr (Or.inl ⟨hp', s, by omega, hs3⟩)
        · exact Or.inr (Or.inr h')
      · simp at hm
      · rcases r4 p o hm with ⟨hp', ho'⟩ | h'
        · exact Or.inl ⟨hp', by simp [ho']⟩
        · exact Or.inr h'

end
end LeanVM.Guest.B1.Whir
