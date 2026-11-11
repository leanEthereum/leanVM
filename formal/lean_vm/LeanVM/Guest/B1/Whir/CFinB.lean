/-
  LeanVM.Guest.B1.Whir.CFinB

  The finish's basis rows, honestly.
-/

module

public import LeanVM.Guest.B1.Whir.CFinEval
public import LeanVM.Guest.B1.Whir.Bases

/-!
# The basis rows, honestly (G:1778-1801)

`osBasisBlk_complete`: one coordinate: its challenge loaded, its coefficient (times the vanishing
inverse), `d = (1 + c)/coefficient` stored in `basis_d`, the scale and the product advanced.
`osBases_complete`: every non-final level's row, its `β` loaded from `level_betas`, its scale and
product stored in `level_scale` and `level_after`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

variable {H : CallRel → Reader → Prop}

theorem osBasisBlk_next (bd slot : ℕ) (src : ℕ × ℕ) (inv sc : ℕ) (after : Option ℕ) (k : ℕ) :
    k + 5 ≤ (osBasisBlk bd slot src inv sc after k).2.2.2 ∧
      (osBasisBlk bd slot src inv sc after k).2.1 < (osBasisBlk bd slot src inv sc after k).2.2.2 ∧
      (osBasisBlk bd slot src inv sc after k).2.2.1 < (osBasisBlk bd slot src inv sc after k).2.2.2 := by
  unfold osBasisBlk
  dsimp only
  split_ifs <;> rcases after with _ | x <;> simp

/-- **One coordinate of a basis row, honestly.** -/
theorem osBasisBlk_complete {σ : Val} {bd slot : ℕ} {src : ℕ × ℕ} {inv sc : ℕ} {after : Option ℕ}
    {k : ℕ} {cv : E} (hsrc : src.1 < k) (hbd : bd < k) (hsc : sc < k)
    (haft : ∀ x, after = some x → x < k)
    (hcv : ∀ C rd, H C rd → LoadHolds rd (σ (.n src.1)) src.2 cv) (hne : cv * word inv 0 ≠ 0)
    (hst : ∀ C rd, H C rd → LoadHolds rd (σ (.n bd)) slot ((1 + cv) / (cv * word inv 0))) :
    BlkA H σ k (osBasisBlk bd slot src inv sc after k).2.2.2 (osBasisBlk bd slot src inv sc after k).1
      (fun σ' ↦ σ' (.n (osBasisBlk bd slot src inv sc after k).2.1) = σ (.n sc) * (cv * word inv 0) ∧
        σ' (.n (osBasisBlk bd slot src inv sc after k).2.2.1) = optVal σ after * cv) := by
  obtain ⟨s1, s2⟩ := src
  simp only at hsrc hcv
  by_cases hi : inv = 1
  · subst hi
    rw [word_one, mul_one] at hne hst ⊢
    rcases after with _ | x
    · have e : osBasisBlk bd slot (s1, s2) 1 sc none k =
          ([osLd k s1 s2, osCst (k + 1) (word 1 0), osAdd (k + 2) (k + 1) k, osMul (k + 2) (k + 3) k,
            osLd (k + 3) bd slot, osMul (k + 4) sc k], k + 4, k, k + 5) := by
        simp [osBasisBlk]
      rw [e]
      have hS : Ssa k [osLd k s1 s2, osCst (k + 1) (word 1 0), osAdd (k + 2) (k + 1) k,
          osMul (k + 2) (k + 3) k, osLd (k + 3) bd slot, osMul (k + 4) sc k] (k + 5) :=
        .cons (.load le_rfl hsrc) (.cons (.const (by omega)) (.cons (.add (by omega) (by omega) (by omega))
          (.cons (.div (by omega) (by omega) (by omega)) (.cons (.store (by omega) (by omega))
            (.cons (.mul (by omega) (by omega) (by omega)) .nil)))))
      refine ssa_blk (Pt := fun _ ↦ 0) hS ?_ ?_
      · intro C rd hH σ' ha hr _
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e4 := hr (k + 4) (by omega) (by omega)
        have e0 := hr k le_rfl (by omega)
        simp [evalV, stepV, stepW, show sc ≠ k by omega,
          show sc ≠ k + 1 by omega, show sc ≠ k + 2 by omega, show sc ≠ k + 3 by omega, em] at e4 e0
        simp only [optVal, one_mul]
        exact ⟨by rw [e4], e0⟩
      · intro C rd hH σ' ha hr
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e0 := hr k le_rfl (by omega)
        have e3 := hr (k + 3) (by omega) (by omega)
        simp [evalV, stepV, stepW, em, word_one] at e0 e3
        simp only [SidesOk, Side, stepW, V.n, le_refl, ↓reduceIte, and_true, true_and,
          show ¬ k + 3 ≤ k + 2 by omega, show ¬ k + 4 ≤ k + 3 by omega, show k + 2 < k + 3 by omega,
          forall_const]
        rw [ha _ hsrc, ha _ hbd, em, e0, e3]
        exact ⟨hcv C rd hH, hne, hst C rd hH, fun h ↦ absurd h (by omega)⟩
    · have hx := haft x rfl
      have e : osBasisBlk bd slot (s1, s2) 1 sc (some x) k =
          ([osLd k s1 s2, osCst (k + 1) (word 1 0), osAdd (k + 2) (k + 1) k, osMul (k + 2) (k + 3) k,
            osLd (k + 3) bd slot, osMul (k + 4) sc k, osMul (k + 5) x k], k + 4, k + 5, k + 6) := by
        simp [osBasisBlk]
      rw [e]
      have hS : Ssa k [osLd k s1 s2, osCst (k + 1) (word 1 0), osAdd (k + 2) (k + 1) k,
          osMul (k + 2) (k + 3) k, osLd (k + 3) bd slot, osMul (k + 4) sc k, osMul (k + 5) x k] (k + 6) :=
        .cons (.load le_rfl hsrc) (.cons (.const (by omega)) (.cons (.add (by omega) (by omega) (by omega))
          (.cons (.div (by omega) (by omega) (by omega)) (.cons (.store (by omega) (by omega))
            (.cons (.mul (by omega) (by omega) (by omega)) (.cons (.mul (by omega) (by omega) (by omega))
              .nil))))))
      refine ssa_blk (Pt := fun _ ↦ 0) hS ?_ ?_
      · intro C rd hH σ' ha hr _
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e4 := hr (k + 4) (by omega) (by omega)
        have e5 := hr (k + 5) (by omega) (by omega)
        simp [evalV, stepV, stepW, show sc ≠ k by omega, show sc ≠ k + 1 by omega,
          show sc ≠ k + 2 by omega, show sc ≠ k + 3 by omega, show x ≠ k by omega,
          show x ≠ k + 1 by omega, show x ≠ k + 2 by omega, show x ≠ k + 3 by omega,
          show x ≠ k + 4 by omega, em] at e4 e5
        simp only [optVal]
        exact ⟨by rw [e4], by rw [e5]⟩
      · intro C rd hH σ' ha hr
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e0 := hr k le_rfl (by omega)
        have e3 := hr (k + 3) (by omega) (by omega)
        simp [evalV, stepV, stepW, em, word_one] at e0 e3
        simp only [SidesOk, Side, stepW, V.n, le_refl, ↓reduceIte, and_true, true_and,
          show ¬ k + 3 ≤ k + 2 by omega, show ¬ k + 4 ≤ k + 3 by omega, show k + 2 < k + 3 by omega,
          forall_const]
        rw [ha _ hsrc, ha _ hbd, em, e0, e3]
        exact ⟨hcv C rd hH, hne, hst C rd hH, fun h ↦ absurd h (by omega), fun h ↦ absurd h (by omega)⟩
  · rcases after with _ | x
    · have e : osBasisBlk bd slot (s1, s2) inv sc none k =
          ([osLd k s1 s2, osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1), osCst (k + 3) (word 1 0),
            osAdd (k + 4) (k + 3) k, osMul (k + 4) (k + 5) (k + 2), osLd (k + 5) bd slot,
            osMul (k + 6) sc (k + 2)], k + 6, k, k + 7) := by
        simp [osBasisBlk, hi]
      rw [e]
      have hS : Ssa k [osLd k s1 s2, osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1),
          osCst (k + 3) (word 1 0), osAdd (k + 4) (k + 3) k, osMul (k + 4) (k + 5) (k + 2),
          osLd (k + 5) bd slot, osMul (k + 6) sc (k + 2)] (k + 7) :=
        .cons (.load le_rfl hsrc) (.cons (.const (by omega)) (.cons (.mul (by omega) (by omega) (by omega))
          (.cons (.const (by omega)) (.cons (.add (by omega) (by omega) (by omega))
            (.cons (.div (by omega) (by omega) (by omega)) (.cons (.store (by omega) (by omega))
              (.cons (.mul (by omega) (by omega) (by omega)) .nil)))))))
      refine ssa_blk (Pt := fun _ ↦ 0) hS ?_ ?_
      · intro C rd hH σ' ha hr _
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e6 := hr (k + 6) (by omega) (by omega)
        have e0 := hr k le_rfl (by omega)
        simp [evalV, stepV, stepW, show sc ≠ k by omega, show sc ≠ k + 1 by omega,
          show sc ≠ k + 2 by omega, show sc ≠ k + 3 by omega, show sc ≠ k + 4 by omega,
          show sc ≠ k + 5 by omega, em] at e6 e0
        simp only [optVal, one_mul]
        exact ⟨by rw [e6], e0⟩
      · intro C rd hH σ' ha hr
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e2 := hr (k + 2) (by omega) (by omega)
        have e5 := hr (k + 5) (by omega) (by omega)
        simp [evalV, stepV, stepW, em, word_one] at e2 e5
        simp only [SidesOk, Side, stepW, V.n, le_refl, ↓reduceIte, and_true, true_and,
          show ¬ k + 5 ≤ k + 4 by omega, show ¬ k + 6 ≤ k + 5 by omega, show k + 4 < k + 5 by omega,
          forall_const]
        rw [ha _ hsrc, ha _ hbd, em, e2, e5]
        exact ⟨hcv C rd hH, fun h ↦ absurd h (by omega), hne, hst C rd hH, fun h ↦ absurd h (by omega)⟩
    · have hx := haft x rfl
      have e : osBasisBlk bd slot (s1, s2) inv sc (some x) k =
          ([osLd k s1 s2, osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1), osCst (k + 3) (word 1 0),
            osAdd (k + 4) (k + 3) k, osMul (k + 4) (k + 5) (k + 2), osLd (k + 5) bd slot,
            osMul (k + 6) sc (k + 2), osMul (k + 7) x k], k + 6, k + 7, k + 8) := by
        simp [osBasisBlk, hi]
      rw [e]
      have hS : Ssa k [osLd k s1 s2, osCst (k + 1) (word inv 0), osMul (k + 2) k (k + 1),
          osCst (k + 3) (word 1 0), osAdd (k + 4) (k + 3) k, osMul (k + 4) (k + 5) (k + 2),
          osLd (k + 5) bd slot, osMul (k + 6) sc (k + 2), osMul (k + 7) x k] (k + 8) :=
        .cons (.load le_rfl hsrc) (.cons (.const (by omega)) (.cons (.mul (by omega) (by omega) (by omega))
          (.cons (.const (by omega)) (.cons (.add (by omega) (by omega) (by omega))
            (.cons (.div (by omega) (by omega) (by omega)) (.cons (.store (by omega) (by omega))
              (.cons (.mul (by omega) (by omega) (by omega)) (.cons (.mul (by omega) (by omega) (by omega))
                .nil))))))))
      refine ssa_blk (Pt := fun _ ↦ 0) hS ?_ ?_
      · intro C rd hH σ' ha hr _
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e6 := hr (k + 6) (by omega) (by omega)
        have e7 := hr (k + 7) (by omega) (by omega)
        simp [evalV, stepV, stepW, show sc ≠ k by omega, show sc ≠ k + 1 by omega,
          show sc ≠ k + 2 by omega, show sc ≠ k + 3 by omega, show sc ≠ k + 4 by omega,
          show sc ≠ k + 5 by omega, show x ≠ k by omega, show x ≠ k + 1 by omega,
          show x ≠ k + 2 by omega, show x ≠ k + 3 by omega, show x ≠ k + 4 by omega,
          show x ≠ k + 5 by omega, show x ≠ k + 6 by omega, em] at e6 e7
        simp only [optVal]
        exact ⟨by rw [e6], by rw [e7]⟩
      · intro C rd hH σ' ha hr
        have em : memOf H (σ (.n s1)) s2 = cv := memOf_eq hcv hH
        have e2 := hr (k + 2) (by omega) (by omega)
        have e5 := hr (k + 5) (by omega) (by omega)
        simp [evalV, stepV, stepW, em, word_one] at e2 e5
        simp only [SidesOk, Side, stepW, V.n, le_refl, ↓reduceIte, and_true, true_and,
          show ¬ k + 5 ≤ k + 4 by omega, show ¬ k + 6 ≤ k + 5 by omega, show k + 4 < k + 5 by omega,
          forall_const]
        rw [ha _ hsrc, ha _ hbd, em, e2, e5]
        exact ⟨hcv C rd hH, fun h ↦ absurd h (by omega), hne, hst C rd hH, fun h ↦ absurd h (by omega),
          fun h ↦ absurd h (by omega)⟩

theorem osBasisRow_next (bd : ℕ) : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc : ℕ) (after : Option ℕ) (k : ℕ),
    k ≤ (osBasisRow bd cs sc after k).2.2.2
  | [], _, _, _ => le_rfl
  | (slot, src, inv) :: rest, sc, after, k => by
    simp only [osBasisRow]
    have := (osBasisBlk_next bd slot src inv sc after k).1
    exact le_trans (by omega) (osBasisRow_next bd rest _ _ _)

theorem osBasisRow_lt (bd : ℕ) : ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)), cs ≠ [] → ∀ (sc : ℕ)
    (after : Option ℕ) (k : ℕ),
    (osBasisRow bd cs sc after k).2.1 < (osBasisRow bd cs sc after k).2.2.2 ∧
      (osBasisRow bd cs sc after k).2.2.1 < (osBasisRow bd cs sc after k).2.2.2
  | [], h, _, _, _ => absurd rfl h
  | [(slot, src, inv)], _, sc, after, k => by
    simp only [osBasisRow]
    exact ⟨(osBasisBlk_next bd slot src inv sc after k).2.1, (osBasisBlk_next bd slot src inv sc after k).2.2⟩
  | (slot, src, inv) :: c2 :: rest, _, sc, after, k => by
    simp only [osBasisRow]
    exact osBasisRow_lt bd (c2 :: rest) (by simp) _ _ _

/-- **A basis row, honestly**: from the scale `sc` and the running product `after`, every
coordinate `t` reading `cv t` at its source and storing its `d` (`BasisIn`'s and `BasisOut`'s
words). -/
theorem osBasisRow_complete {bd : ℕ} (cv : ℕ → E) :
    ∀ (cs : List (ℕ × (ℕ × ℕ) × ℕ)) (sc : ℕ) (after : Option ℕ) (k : ℕ) (σ : Val),
      bd < k → sc < k → (∀ x, after = some x → x < k) →
      (∀ t < cs.length, (cs.getD t coordD).2.1.1 < k ∧
        cv t * word (cs.getD t coordD).2.2 0 ≠ 0 ∧ ∀ C rd, H C rd →
          LoadHolds rd (σ (.n (cs.getD t coordD).2.1.1)) (cs.getD t coordD).2.1.2 (cv t) ∧
          LoadHolds rd (σ (.n bd)) (cs.getD t coordD).1
            ((1 + cv t) / (cv t * word (cs.getD t coordD).2.2 0))) →
      BlkA H σ k (osBasisRow bd cs sc after k).2.2.2 (osBasisRow bd cs sc after k).1
        (fun σ' ↦ σ' (.n (osBasisRow bd cs sc after k).2.1) =
            σ' (.n sc) * ∏ t ∈ Finset.range cs.length, (cv t * word (cs.getD t coordD).2.2 0) ∧
          (after.isSome ∨ cs ≠ [] → σ' (.n (osBasisRow bd cs sc after k).2.2.1) =
            optVal σ' after * ∏ t ∈ Finset.range cs.length, cv t))
  | [], sc, after, k, σ, _, _, haft, _ => by
    refine BlkA.nil fun σ' _ ↦ ⟨by simp [osBasisRow], fun h ↦ ?_⟩
    rcases after with _ | x
    · simp at h
    · simp [osBasisRow, optVal]
  | (slot, src, inv) :: rest, sc, after, k, σ, hbd, hsc, haft, hin => by
    obtain ⟨h0s, h0n, h0m⟩ := hin 0 (by simp)
    simp only [List.getD_cons_zero] at h0s h0n h0m
    have hA := osBasisBlk_complete (H := H) (bd := bd) (slot := slot) (inv := inv) (sc := sc)
      (after := after) (k := k) (src := src) (cv := cv 0) h0s hbd hsc haft
      (fun C rd hH ↦ (h0m C rd hH).1) h0n (fun C rd hH ↦ (h0m C rd hH).2)
    obtain ⟨n1, n2, n3⟩ := osBasisBlk_next bd slot src inv sc after k
    set r := osBasisBlk bd slot src inv sc after k with hr
    have hB := BlkA.seq (H := H) (by omega) (osBasisRow_next bd rest r.2.1 (some r.2.2.1) r.2.2.2)
      hA.agree fun σ1 ha1 _ ↦ osBasisRow_complete (fun t ↦ cv (t + 1)) rest r.2.1 (some r.2.2.1)
        r.2.2.2 σ1 (by omega) n2 (fun x hx ↦ by simp only [Option.some.injEq] at hx; omega) fun t ht ↦ by
          obtain ⟨a, b, m⟩ := hin (t + 1) (by simp; omega)
          simp only [List.getD_cons_succ] at a b m
          refine ⟨by omega, b, fun C rd hH ↦ ?_⟩
          obtain ⟨m1, m2⟩ := m C rd hH
          rw [← ha1 _ a] at m1
          rw [← ha1 _ hbd] at m2
          exact ⟨m1, m2⟩
    simp only [osBasisRow]
    refine hB.mono fun σ' ⟨⟨⟨o1, o2⟩, ha⟩, o3, o4⟩ ↦ ⟨?_, fun _ ↦ ?_⟩
    · rw [o3, o1, ha _ hsc, List.length_cons, Finset.prod_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring
    · rw [o4 (Or.inl rfl), List.length_cons, Finset.prod_range_succ']
      simp only [optVal, o2]
      rcases after with _ | x
      · simp; ring
      · simp only [ha _ (haft x rfl)]; ring

theorem osBases_next (c : OsCfg) (tch bd ls la : ℕ) :
    ∀ (lvs : List OsLv) (lvl k : ℕ), k ≤ (osBases c tch bd ls la lvl lvs k).2
  | [], _, _ => le_rfl
  | lv :: rest, lvl, k => by
    simp only [osBases]
    exact le_trans (le_trans (by omega) (osBasisRow_next bd _ k none (k + 1)))
      (osBases_next c tch bd ls la rest (lvl + 1) _)

theorem coordSrc_lt {tch : ℕ} {lv : OsLv} {t k : ℕ} (hf : osFch < k) (ht : tch < k) :
    (coordSrc tch lv t).1 < k := by
  unfold coordSrc; split_ifs <;> assumption

theorem basisIn_agree {rd : Reader} {σ σ' : Val} {c : OsCfg} {tch L k : ℕ} {lv : OsLv} {β : E}
    {X : ℕ → E} (hk : 36 ≤ k) (htch : tch < k) (ha : AgreeBelow k σ σ')
    (h : BasisIn rd σ c tch L lv β X) : BasisIn rd σ' c tch L lv β X := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rwa [ha _ (by show 23 < k; omega)], fun t ht ↦ ⟨(h2 t ht).1, ?_⟩⟩
  rw [ha _ (coordSrc_lt (by show 19 < k; omega) htch)]
  exact (h2 t ht).2

theorem basisOut_agree {rd : Reader} {σ σ' : Val} {c : OsCfg} {bd ls la L k : ℕ} {lv : OsLv} {β : E}
    {X : ℕ → E} (hbd : bd < k) (hls : ls < k) (hla : la < k) (ha : AgreeBelow k σ σ')
    (h : BasisOut rd σ c bd ls la L lv β X) : BasisOut rd σ' c bd ls la L lv β X := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨fun t ht ↦ ⟨(h1 t ht).1, by rw [ha _ hbd]; exact (h1 t ht).2⟩, by rwa [ha _ hls],
    by rwa [ha _ hla]⟩

/-- **Every non-final level's basis row, honestly**: on memory holding what each row reads
(`BasisIn`) and what it stores (`BasisOut`), the coefficients not zero. -/
theorem osBases_complete {c : OsCfg} {tch bd ls la : ℕ} (β : ℕ → E) (X : ℕ → ℕ → E)
    (hpos : ∀ lv : OsLv, 1 ≤ lv.prefixLen + c.yrLog) :
    ∀ (levels : List OsLv) (lvl k : ℕ) (σ : Val), bd < k → ls < k → la < k → tch < k → 36 ≤ k →
      (∀ i (hi : i < levels.length), ∀ t < levels[i].prefixLen + c.yrLog,
        X (lvl + i) t * invW levels[i] t ≠ 0) →
      (∀ i (hi : i < levels.length), ∀ C rd, H C rd →
        BasisIn rd σ c tch (lvl + i) levels[i] (β (lvl + i)) (X (lvl + i)) ∧
          BasisOut rd σ c bd ls la (lvl + i) levels[i] (β (lvl + i)) (X (lvl + i))) →
      BlkA H σ k (osBases c tch bd ls la lvl levels k).2 (osBases c tch bd ls la lvl levels k).1
        (fun _ ↦ True)
  | [], _, _, _, _, _, _, _, _, _, _ => BlkA.nil fun _ _ ↦ trivial
  | lv :: rest, lvl, k, σ, hbd, hls, hla, htch, hk, hne, hm => by
    have hm0 := fun C rd hH ↦ hm 0 (by simp) C rd hH
    simp only [Nat.add_zero, List.getElem_cons_zero] at hm0
    have hne0 := hne 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hne0
    have hlen : (osBasisCoords c tch lvl lv).length = lv.prefixLen + c.yrLog := by
      simp [osBasisCoords]
    -- β, then the row from the scale `k`
    have hL : BlkA H σ k (k + 1) [osLd k osBetas lvl] (fun σ' ↦ σ' (.n k) = β lvl) := by
      have hS : Ssa k [osLd k osBetas lvl] (k + 1) := .cons (.load le_rfl (by show 23 < k; omega)) .nil
      refine ssa_blk (Pt := fun _ ↦ 0) hS (fun C rd hH σ' ha hr _ ↦ ?_) fun C rd hH σ' ha hr ↦ ?_
      · have e0 := hr k le_rfl (by omega)
        simp [evalV, stepV] at e0
        rw [e0, memOf_eq (fun C rd hH ↦ (hm0 C rd hH).1.1) hH]
      · simp only [SidesOk, Side, V.n, le_refl, ↓reduceIte, and_true]
        rw [ha _ (by show 23 < k; omega), memOf_eq (fun C rd hH ↦ (hm0 C rd hH).1.1) hH]
        exact (hm0 C rd hH).1.1
    set r := osBasisRow bd (osBasisCoords c tch lvl lv) k none (k + 1) with hr
    have hrn : k + 1 ≤ r.2.2.2 := osBasisRow_next bd (osBasisCoords c tch lvl lv) k none (k + 1)
    have hR := BlkA.seq (H := H) (by omega) hrn hL.agree fun σ1 ha1 _ ↦
      osBasisRow_complete (H := H) (X lvl) (osBasisCoords c tch lvl lv) k none (k + 1) σ1 (by omega)
        (by omega) (by simp) fun t ht ↦ by
          rw [hlen] at ht
          rw [osBasisCoords_getD ht]
          refine ⟨coordSrc_lt (by show 19 < k + 1; omega) (by omega), hne0 t ht, fun C rd hH ↦ ?_⟩
          obtain ⟨⟨-, hx⟩, ⟨hd, -⟩⟩ := hm0 C rd hH
          have hs := (hx t ht).2
          rw [← ha1 _ (coordSrc_lt (by show 19 < k; omega) htch)] at hs
          have hd' := (hd t ht).2
          rw [← ha1 _ hbd] at hd'
          exact ⟨hs, hd'⟩
    -- the scale and the product stored
    have hne' : osBasisCoords c tch lvl lv ≠ [] := by
      intro h0; have := hpos lv; rw [← hlen, h0] at this; simp at this
    have hsl : r.2.1 < r.2.2.2 ∧ r.2.2.1 < r.2.2.2 := osBasisRow_lt bd _ hne' k none (k + 1)
    have hS2 := BlkA.seq (H := H) (by omega) (le_refl (r.2.2.2))
      (B := [osLd r.2.1 ls lvl, osLd r.2.2.1 la lvl]) (OutB := fun _ ↦ True) hR fun σ2 ha2 ho2 ↦ by
        have hS : Ssa r.2.2.2 [osLd r.2.1 ls lvl, osLd r.2.2.1 la lvl] r.2.2.2 :=
          .cons (.store hsl.1 (by omega)) (.cons (.store hsl.2 (by omega)) .nil)
        refine ssa_blk (Pt := fun _ ↦ 0) hS (fun _ _ _ _ _ _ _ ↦ trivial) fun C rd hH σ' ha hr' ↦ ?_
        obtain ⟨⟨e0, -⟩, o1, o2⟩ := ho2 C rd hH
        obtain ⟨-, ⟨-, s1, s2⟩⟩ := hm0 C rd hH
        simp only [SidesOk, Side, V.n, show ¬ r.2.2.2 ≤ r.2.1 by omega,
          show ¬ r.2.2.2 ≤ r.2.2.1 by omega, ↓reduceIte, and_true, stepW]
        rw [ha _ hsl.1, ha _ hsl.2, ha _ (by omega), ha _ (by omega), o1, o2 (Or.inr hne'),
          ha2 _ hls, ha2 _ hla, e0]
        simp only [optVal, one_mul, hlen]
        refine ⟨?_, ?_⟩
        · convert s1 using 2
          refine Finset.prod_congr rfl fun t ht ↦ ?_
          rw [osBasisCoords_getD (Finset.mem_range.mp ht)]
        · exact s2
    have hnx := osBases_next c tch bd ls la rest (lvl + 1) r.2.2.2
    have hall := BlkA.seq (H := H) (by omega) hnx hS2 fun σ3 ha3 _ ↦
      osBases_complete β X hpos rest (lvl + 1) r.2.2.2 σ3 (by omega) (by omega) (by omega) (by omega)
        (by omega) (fun i hi t ht ↦ by
          have := hne (i + 1) (by simp; omega) t (by simpa using ht)
          simpa [show lvl + (i + 1) = lvl + 1 + i by ring] using this) fun i hi C rd hH ↦ by
          have h := hm (i + 1) (by simp; omega) C rd hH
          simp only [List.getElem_cons_succ, show lvl + (i + 1) = lvl + 1 + i by ring] at h
          have hk : AgreeBelow k σ σ3 := ha3.mono (by omega)
          exact ⟨basisIn_agree (by omega) htch hk h.1, basisOut_agree hbd hls hla hk h.2⟩
    refine (hall.congr ?_).mono fun _ _ ↦ trivial
    simp only [osBases, List.cons_append, List.append_assoc, List.nil_append, ← hr]

end
end LeanVM.Guest.B1.Whir
