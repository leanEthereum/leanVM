module

public import LeanVMCircuits.Rec.RoundSound

@[expose] public section

/-!
The other late tests' soundness: GKR's radix-four top layer, a claim's split into point claims, and WHIR's sumcheck.

`top_test_sound`: at an even depth GKR's top layer runs no sumcheck. It combines the input values at `λ`, reads four
children per value, tests their products combined at `λ`, and takes each value's bilinear interpolation of its
children at the next two challenges. If some value is not its true children's product, the challenge triples at which
the test holds and every next claim is its value's true interpolation are at most an `(m + 1)/|S|` fraction.

`split_test_sound`: a split (`design::program_claims`) tests a claim's value against a sum of coefficients times its
hints' powers. In any assignment where the replayed calls hold and the test holds, if the claim's value is not that
sum at the true values of the hints, some hint is not its true value: the input claim is false only if an output
claim is.

`whir_test_sound`: WHIR's sumcheck (`WhirCert`, fold rounds and batch rounds) is a sumcheck whose rounds' polynomials
read only what is bound before their challenges (a batch round's with the words squeezed with `λ`, its query
positions, as seeds), so `Sumcheck.sumcheck_sound_fun` bounds its test as `sumcheck_test_sound` does.
-/

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Sumcheck Polynomial

/-! GKR's radix-four top layer. -/

open Classical Finset in
/-- A line `x + t · (x + y)` not identically zero vanishes at at most one point. -/
theorem card_line_zero (S : Finset E) {x y : E} (h : x ≠ 0 ∨ y ≠ 0) : #{t ∈ S | lineE x y t = 0} ≤ 1 := by
  refine Finset.card_le_one.mpr fun t1 h1 t2 h2 => ?_
  have e1 : lineE x y t1 = 0 := (Finset.mem_filter.mp h1).2
  have e2 : lineE x y t2 = 0 := (Finset.mem_filter.mp h2).2
  simp only [lineE] at e1 e2
  have hd : (t1 - t2) * (x + y) = 0 := by linear_combination e1 - e2
  rcases mul_eq_zero.mp hd with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have hx : x = 0 := by
      have := e1
      rw [h0, mul_zero, add_zero] at this
      exact this
    have hy : y = 0 := by linear_combination h0 - hx
    rcases h with h | h <;> contradiction

open Classical Finset in
/-- A bilinear interpolation of four values not all zero vanishes at at most `2 |S|` points of `S^2`. -/
theorem card_plane_zero (S : Finset E) {d0 d1 d2 d3 : E} (h : d0 ≠ 0 ∨ d1 ≠ 0 ∨ d2 ≠ 0 ∨ d3 ≠ 0) :
    #{p ∈ S ×ˢ S | lineE (lineE d0 d1 p.1) (lineE d2 d3 p.1) p.2 = 0} ≤ 2 * #S := by
  set P := ({p ∈ S ×ˢ S | lineE (lineE d0 d1 p.1) (lineE d2 d3 p.1) p.2 = 0} : Finset (E × E))
  have hfib := card_eq_sum_card_fiberwise (s := P) (t := S) (f := Prod.fst) fun p hp =>
    (mem_product.mp (mem_filter.mp hp).1).1
  have hbad : #{l ∈ S | lineE d0 d1 l = 0 ∧ lineE d2 d3 l = 0} ≤ 1 := by
    rcases h with h | h | h | h
    · exact (card_le_card fun l hl => by simp only [mem_filter] at hl ⊢; exact ⟨hl.1, hl.2.1⟩).trans
        (card_line_zero S (Or.inl h))
    · exact (card_le_card fun l hl => by simp only [mem_filter] at hl ⊢; exact ⟨hl.1, hl.2.1⟩).trans
        (card_line_zero S (Or.inr h))
    · exact (card_le_card fun l hl => by simp only [mem_filter] at hl ⊢; exact ⟨hl.1, hl.2.2⟩).trans
        (card_line_zero S (Or.inl h))
    · exact (card_le_card fun l hl => by simp only [mem_filter] at hl ⊢; exact ⟨hl.1, hl.2.2⟩).trans
        (card_line_zero S (Or.inr h))
  have hl : ∀ l ∈ S, #{p ∈ P | p.1 = l} ≤ if lineE d0 d1 l = 0 ∧ lineE d2 d3 l = 0 then #S else 1 := by
    intro l _
    have hinj : #{p ∈ P | p.1 = l} ≤ #{t ∈ S | lineE (lineE d0 d1 l) (lineE d2 d3 l) t = 0} := by
      refine card_le_card_of_injOn Prod.snd (fun p hp => ?_) (fun p hp p' hp' he => ?_)
      · simp only [Finset.mem_coe, P, mem_filter, mem_product] at hp ⊢
        obtain ⟨⟨⟨-, h2⟩, hz⟩, h1⟩ := hp
        rw [h1] at hz
        exact ⟨h2, hz⟩
      · simp only [Finset.mem_coe, P, mem_filter] at hp hp'
        exact Prod.ext (hp.2.trans hp'.2.symm) he
    split
    · exact hinj.trans (card_le_card (filter_subset _ _))
    · rename_i hn
      refine hinj.trans (card_line_zero S ?_)
      by_contra hc
      push Not at hc
      exact hn hc
  calc #P = ∑ l ∈ S, #{p ∈ P | p.1 = l} := hfib
    _ ≤ ∑ l ∈ S, if lineE d0 d1 l = 0 ∧ lineE d2 d3 l = 0 then #S else 1 := sum_le_sum hl
    _ = #{l ∈ S | lineE d0 d1 l = 0 ∧ lineE d2 d3 l = 0} * #S +
          #{l ∈ S | ¬ (lineE d0 d1 l = 0 ∧ lineE d2 d3 l = 0)} := by
        rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul, mul_one]
    _ ≤ 1 * #S + #S := add_le_add (Nat.mul_le_mul_right _ hbad) (card_le_card (filter_subset _ _))
    _ = 2 * #S := by ring

/-- What `top_test_sound` asks of the prover's answers to a top layer's challenge triples `r` (`λ`, `low`, `high`):
answers in the random-oracle view (`RomAnswers`) that agree on the seeds before `λ`'s time, and when their `λ` agree on
the seeds before `low`'s time, both `good` collision-free on the rows bound by those times
(`PairCR`); whose challenges are `r`; and in which some input value is not its true children's product (`T k i`, child
`i` of value `k`). `top_answers_exist` exhibits such answers. -/
structure TopAnswers (c : Cert) (s : State) (tc : TopCert) (T : ℕ → ℕ → E) (good : (Fin 3 → E) → Prop)
    (st : (Fin 3 → E) → ℕ → Fin 4 → K) (val : (Fin 3 → E) → Val) : Prop where
  rom : RomAnswers c s tc.transcript st val
  seed0 : ∀ r r', ∀ n ∈ seedsBefore s (c.transcripts.getD tc.transcript default) tc.lam.time,
    nu (val r) n = nu (val r') n
  seed1 : ∀ r r', r 0 = r' 0 →
    ∀ n ∈ seedsBefore s (c.transcripts.getD tc.transcript default) tc.low.time, nu (val r) n = nu (val r') n
  cr0 : ∀ r r', good r → good r' → PairCRAt c s tc.transcript tc.lam.time (val r) (val r')
  cr1 : ∀ r r', good r → good r' → r 0 = r' 0 → PairCRAt c s tc.transcript tc.low.time (val r) (val r')
  chal : ∀ r, Model.ev (val r) tc.lam.chal = r 0 ∧ Model.ev (val r) tc.low.chal = r 1 ∧
    Model.ev (val r) tc.high.chal = r 2
  false_value : ∀ r, good r → ∃ k < tc.m, Model.ev (val r) (tc.values.getD k 0) ≠ T k 0 * T k 1 * T k 2 * T k 3

open Classical Finset in
/-- GKR's radix-four top layer on the circuit. Take an accepted circuit, a top layer it names (`tc`, `m` values), the
layer's true children `T k i`, and the prover's answers to the challenge triples (`TopAnswers`). The triples of `S^3`
at which the answer is `good`, the test holds and every next claim is its value's true children's interpolation at
`low` and `high` are at most `(m + 1) · |S|^2`: an `(m + 1)/|S|` fraction. -/
theorem top_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {tc : TopCert} (htc : tc ∈ c.tops)
    (S : Finset E) (T : ℕ → ℕ → E) (good : (Fin 3 → E) → Prop) (st : (Fin 3 → E) → ℕ → Fin 4 → K)
    (val : (Fin 3 → E) → Val) (ha : TopAnswers c s tc T good st val) :
    #{r ∈ Fintype.piFinset (fun _ : Fin 3 => S) | good r ∧
        (∀ a b, s.unions[tc.test]? = some (a, b) → val r a = val r b) ∧
        ∀ k < tc.m, Model.ev (val r) (tc.out c.outs k) =
          lineE (lineE (T k 0) (T k 1) (r 1)) (lineE (T k 2) (T k 3) (r 1)) (r 2)} ≤ (tc.m + 1) * #S ^ 2 := by
  have hall := (Cert.accepts_rounds h).2.2.2.2
  simp only [Cert.lateOk, Cert.topsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hall
  obtain ⟨⟨htops, -⟩, -⟩ := hall
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htr, hok⟩, -⟩, hpair⟩, -⟩, -⟩, -⟩, hb0⟩, hb1⟩ := htops tc htc
  have hm : 0 < tc.m := by
    simp only [TopCert.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1
  have hF := ha.rom.facts
  have agree := fun r r' {time w : ℕ} hc hb hs => bound_agree h htr ha.rom r r' (time := time) (w := w) hc hb hs
  have hval : ∀ r r', good r → good r' → ∀ k < tc.m,
      Model.ev (val r) (tc.values.getD k 0) = Model.ev (val r') (tc.values.getD k 0) :=
    fun r r' hg hg' k hk => agree r r' (ha.cr0 r r' hg hg')
      (boundBy_wires hb0 _ (getD_mem_of_lt (by simpa [TopCert.m] using hk))) (ha.seed0 r r')
  have hch : ∀ r r', good r → good r' → r 0 = r' 0 → ∀ k < tc.m, ∀ i < 4,
      Model.ev (val r) (tc.kid k i) = Model.ev (val r') (tc.kid k i) := by
    intro r r' hg hg' h0 k hk i hi
    exact agree r r' (ha.cr1 r r' hg hg' h0) (boundBy_wires hb1 _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩)) (ha.seed1 r r' h0)
  -- The values' differences from the children's products, a nonzero polynomial in `λ`.
  by_cases hex : ∃ r₀ : Fin 3 → E, good r₀
  swap
  · simp only [not_exists] at hex
    exact le_trans (le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun r _ hr => hex r hr.1))) (Nat.zero_le _)
  obtain ⟨r₀, hg₀⟩ := hex
  set vs : ℕ → E := fun k => Model.ev (val r₀) (tc.values.getD k 0)
  set P : ℕ → E := fun k => T k 0 * T k 1 * T k 2 * T k 3
  set D : E[X] := polyOf ((List.range tc.m).map fun k => vs k - P k)
  have hD0 : D ≠ 0 := by
    obtain ⟨k, hk, hk'⟩ := ha.false_value r₀ hg₀
    intro hD
    have := congrArg (fun p => Polynomial.coeff p k) hD
    simp only [D, coeff_polyOf, coeff_zero, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hk, Option.map_some, Option.getD_some] at this
    exact hk' (sub_eq_zero.mp this)
  have hDdeg : D.natDegree ≤ tc.m - 1 := (natDegree_polyOf _).trans (by simp)
  set A := ({r ∈ Fintype.piFinset (fun _ : Fin 3 => S) | good r ∧ (∀ a b, s.unions[tc.test]? = some (a, b) →
    val r a = val r b) ∧ ∀ k < tc.m, Model.ev (val r) (tc.out c.outs k) =
      lineE (lineE (T k 0) (T k 1) (r 1)) (lineE (T k 2) (T k 3) (r 1)) (r 2)} : Finset (Fin 3 → E))
  have hext : ∀ r r' : Fin 3 → E, r 0 = r' 0 → r 1 = r' 1 → r 2 = r' 2 → r = r' := by
    intro r r' h0 h1 h2
    funext i
    fin_cases i
    exacts [h0, h1, h2]
  -- At a `λ` that is no root, some child is false, and the answers are at most the zeros of its interpolation's error.
  have hgood : ∀ a, D.eval a ≠ 0 → #{r ∈ A | r 0 = a} ≤ 2 * #S := by
    intro a ha'
    rcases Finset.eq_empty_or_nonempty ({r ∈ A | r 0 = a} : Finset (Fin 3 → E)) with he | ⟨r1, hr1⟩
    · rw [he]
      exact Nat.zero_le _
    simp only [A, mem_filter] at hr1
    obtain ⟨⟨-, hg1, htest, -⟩, h10⟩ := hr1
    obtain ⟨hc1, he1, -⟩ := top_sem (hF r1) hok
    have htv : Model.ev (val r1) (tc.claim c.outs) = Model.ev (val r1) (tc.expected c.outs) := by
      rcases hpair with hp | hp
      · simp only [Model.ev, htest _ _ hp]
      · simp only [Model.ev, ← htest _ _ hp]
    rw [hc1, he1, (ha.chal r1).1, h10, map_eq_range _ 0 tc.values] at htv
    have hvs : (List.range tc.values.length).map (fun k => Model.ev (val r1) (tc.values.getD k 0)) =
        (List.range tc.m).map vs := List.map_congr_left fun k hk => hval r1 r₀ hg1 hg₀ k (List.mem_range.mp hk)
    rw [hvs] at htv
    obtain ⟨k, hk, hkne⟩ : ∃ k < tc.m, Model.ev (val r1) (tc.kid k 0) * Model.ev (val r1) (tc.kid k 1) *
        Model.ev (val r1) (tc.kid k 2) * Model.ev (val r1) (tc.kid k 3) ≠ P k := by
      by_contra hn
      simp only [not_exists, not_and, not_not] at hn
      apply ha'
      have hl : (List.range tc.m).map (fun k => Model.ev (val r1) (tc.kid k 0) * Model.ev (val r1) (tc.kid k 1) *
          Model.ev (val r1) (tc.kid k 2) * Model.ev (val r1) (tc.kid k 3)) = (List.range tc.m).map P :=
        List.map_congr_left fun k hk => hn k (List.mem_range.mp hk)
      rw [hl] at htv
      have hD : D.eval a = (polyOf ((List.range tc.m).map vs)).eval a - (polyOf ((List.range tc.m).map P)).eval a := by
        rw [← Polynomial.eval_sub, ← polyOf_map_sub]
      rw [hD, htv, sub_self]
    have hδ : Model.ev (val r1) (tc.kid k 0) - T k 0 ≠ 0 ∨ Model.ev (val r1) (tc.kid k 1) - T k 1 ≠ 0 ∨
        Model.ev (val r1) (tc.kid k 2) - T k 2 ≠ 0 ∨ Model.ev (val r1) (tc.kid k 3) - T k 3 ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hkne
      simp only [P]
      rw [sub_eq_zero.mp hn.1, sub_eq_zero.mp hn.2.1, sub_eq_zero.mp hn.2.2.1, sub_eq_zero.mp hn.2.2.2]
    refine (card_le_card_of_injOn (fun r => (r 1, r 2)) (fun r hr => ?_) (fun r hr r' hr' he => ?_)).trans
      (card_plane_zero S hδ)
    · simp only [Finset.mem_coe, A, mem_filter, Fintype.mem_piFinset] at hr
      obtain ⟨⟨hS, hg, -, hout⟩, h0⟩ := hr
      simp only [Finset.mem_coe, mem_filter, mem_product]
      refine ⟨⟨hS 1, hS 2⟩, ?_⟩
      have e := (top_sem (hF r) hok).2.2 k hk
      have hk' := hch r r1 hg hg1 (h0.trans h10.symm) k hk
      rw [hout k hk, (ha.chal r).2.1, (ha.chal r).2.2, hk' 0 (by norm_num), hk' 1 (by norm_num),
        hk' 2 (by norm_num), hk' 3 (by norm_num)] at e
      simp only [lineE] at e ⊢
      linear_combination -e
    · simp only [Finset.mem_coe, A, mem_filter] at hr hr'
      simp only [Prod.mk.injEq] at he
      exact hext r r' (hr.2.trans hr'.2.symm) he.1 he.2
  -- At a root, the answers are at most one per pair of next challenges.
  have hbad : ∀ a, #{r ∈ A | r 0 = a} ≤ #S ^ 2 := by
    intro a
    refine (card_le_card_of_injOn (fun r => (r 1, r 2)) (fun r hr => ?_) (fun r hr r' hr' he => ?_)).trans
      (by rw [card_product, sq])
    · simp only [Finset.mem_coe, A, mem_filter, Fintype.mem_piFinset] at hr
      simp only [Finset.mem_coe, mem_product]
      exact ⟨hr.1.1 1, hr.1.1 2⟩
    · simp only [Finset.mem_coe, A, mem_filter] at hr hr'
      simp only [Prod.mk.injEq] at he
      exact hext r r' (hr.2.trans hr'.2.symm) he.1 he.2
  have hfib := card_eq_sum_card_fiberwise (s := A) (t := S) (f := fun r => r 0) fun r hr => by
    exact Fintype.mem_piFinset.mp (mem_filter.mp hr).1 0
  calc #A = ∑ a ∈ S, #{r ∈ A | r 0 = a} := hfib
    _ ≤ ∑ a ∈ S, if D.eval a = 0 then #S ^ 2 else 2 * #S := sum_le_sum fun a _ => by
        split
        · exact hbad a
        · exact hgood a (by assumption)
    _ = #{a ∈ S | D.eval a = 0} * #S ^ 2 + #{a ∈ S | ¬ D.eval a = 0} * (2 * #S) := by
        rw [sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
    _ ≤ (tc.m - 1) * #S ^ 2 + #S * (2 * #S) :=
        add_le_add (Nat.mul_le_mul_right _ (card_roots_le S hD0 hDdeg))
          (Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _)))
    _ = (tc.m + 1) * #S ^ 2 := by
        obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
        rw [hm', Nat.succ_sub_one, Nat.succ_eq_add_one]
        ring

/-! A claim's split into point claims. -/

/-- A claim split on the circuit. Take an accepted circuit, a split it names (`pc`), and true values `D k` of its
hints. In any assignment where every replayed call holds (as in every `RomAnswers`) and the split's test holds, if the
claim's value is not the sum of the coefficients times the true values' powers, some hint is not its true value. -/
theorem split_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {pc : SplitCert} (hpc : pc ∈ c.splits)
    {st : ℕ → Fin 4 → K} {val : Val} (hF : Facts c.calls c.relax c.outs st val) (D : ℕ → E)
    (htest : ∀ a b, s.unions[pc.test]? = some (a, b) → val a = val b)
    (hne : Model.ev val pc.value ≠ ((List.range pc.terms.length).map fun k =>
      Model.ev val (pc.terms.getD k default).1 * D k ^ 2 ^ (pc.terms.getD k default).2.2.1.length).sum) :
    ∃ k < pc.terms.length, Model.ev val (pc.terms.getD k default).2.1 ≠ D k := by
  have hall := (Cert.accepts_rounds h).2.2.2.2
  simp only [Cert.lateOk, Cert.splitsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hall
  obtain ⟨⟨-, hsp⟩, -⟩ := hall
  obtain ⟨⟨hok, -⟩, hpair⟩ := hsp pc hpc
  by_contra hn
  push Not at hn
  apply hne
  have htv : Model.ev val pc.value = Model.ev val (pc.total c.outs) := by
    rcases hpair with hp | hp
    · simp only [Model.ev, htest _ _ hp]
    · simp only [Model.ev, ← htest _ _ hp]
  rw [htv, split_sem hF hok, map_eq_range _ default pc.terms]
  exact congrArg List.sum (List.map_congr_left fun k hk => by rw [hn k (List.mem_range.mp hk)])

/-! WHIR's sumcheck. -/

/-- A WHIR round's atoms are in the closure of its seeds (`WhirRound.seeds`) under its transcript's random-oracle
rules, when `Cert.whirBound` passes. -/
theorem whirBound_closure {c : Cert} {s : State} {os : Array (List ℕ)} {T : Transcript} {wr : WhirRound}
    (h : c.whirBound s os (T, c.timesRO s T) wr = true) :
    ∀ w ∈ wr.atoms os, ∀ n ∈ limbs3 w, Closure T.rulesRO (wr.seeds s T) n := by
  intro w hw n hn
  cases wr with
  | fold q cc u v =>
    simp only [Cert.whirBound] at h
    obtain ⟨k, hk, hle⟩ := boundBy_wires h w hw n hn
    exact (Cert.timesRO_sound c s T hk).mono (seedsBefore_mono hle)
  | batch cc e own fs =>
    simp only [Cert.whirBound, Bool.and_eq_true] at h
    obtain ⟨k, hk, hle⟩ := boundBy_wires h.2 w hw n hn
    refine (Cert.timesX_sound c s T _ fs hk).mono fun m hm => ?_
    simp only [WhirRound.seeds, List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact Or.inl (seedsBefore_mono hle m hm)
    · simp only [seedsBy, List.mem_map, List.mem_filter, decide_eq_true_eq] at hm
      obtain ⟨p, ⟨⟨x, hx, rfl⟩, -⟩, rfl⟩ := hm
      exact Or.inr hx

/-- What `whir_test_sound` asks of the prover's answers to a WHIR sumcheck `wc`'s challenge vectors `r`: answers in
the random-oracle view (`RomAnswers`); two answers whose challenges before round `i` agree agree on round `i`'s seeds
(`WhirRound.seeds`: the seeds before its time, and for a batch round the words squeezed with `λ` but `λ`'s own, its
query positions) and, both `good`, are collision-free on the rows those seeds bind (`PairCR`); round `i`'s
challenge is `r i`; the rounds' eq weights (none for a fold round, zero for a batch round) are the honest instance's;
and the input claim is not the instance's sum. `whir_answers_exist` exhibits such answers. -/
structure WhirAnswers (c : Cert) (s : State) (wc : WhirCert) (I : Inst E wc.rounds.length)
    (good : (Fin wc.rounds.length → E) → Prop) (st : (Fin wc.rounds.length → E) → ℕ → Fin 4 → K)
    (val : (Fin wc.rounds.length → E) → Val) : Prop where
  rom : RomAnswers c s wc.transcript st val
  seed : ∀ r r' (i : Fin wc.rounds.length), (∀ j < i, r j = r' j) →
    ∀ m ∈ (wc.rounds.getD i default).seeds s (c.transcripts.getD wc.transcript default),
      nu (val r) m = nu (val r') m
  cr : ∀ r r' (i : Fin wc.rounds.length), good r → good r' → (∀ j < i, r j = r' j) →
    PairCR c s wc.transcript ((wc.rounds.getD i default).seeds s (c.transcripts.getD wc.transcript default)) (val r)
      (val r')
  chal : ∀ r (i : Fin wc.rounds.length), Model.ev (val r) (wc.rounds.getD i default).chal.chal = r i
  weight : ∀ r (i : Fin wc.rounds.length), (wc.rounds.getD i default).weight = I.weight r i
  false_claim : ∀ r, good r → Model.ev (val r) wc.claim0 ≠ I.sum

open Classical Finset in
/-- WHIR's sumcheck on a certified test. Take an accepted circuit and a WHIR sumcheck it names (`wc`, `n` rounds of
degree at most `d`), the honest instance `I` of degree `d`, and the prover's answers (`WhirAnswers`). The challenge
vectors of `S^n` at which the answer is `good`, the test holds and its other side, the terminal value, is the
instance's final value are at most `n · d · |S|^(n-1)`. -/
theorem whir_test_sound (c : Cert) (s : State) (h : c.accepts s = true) {wc : WhirCert} (hwc : wc ∈ c.whirs)
    (S : Finset E) (I : Inst E wc.rounds.length) (hI : I.ok wc.deg) (good : (Fin wc.rounds.length → E) → Prop)
    (st : (Fin wc.rounds.length → E) → ℕ → Fin 4 → K) (val : (Fin wc.rounds.length → E) → Val)
    (ha : WhirAnswers c s wc I good st val) :
    #{r ∈ Fintype.piFinset (fun _ : Fin wc.rounds.length => S) | good r ∧
        (∀ a b, s.unions[wc.test]? = some (a, b) → val r a = val r b) ∧ Model.ev (val r) wc.final = I.final r} ≤
      wc.rounds.length * wc.deg * #S ^ (wc.rounds.length - 1) := by
  have hall := (Cert.accepts_rounds h).2.2.2.2
  simp only [Cert.lateOk, Cert.whirsOk, Array.all_eq_true', Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hall
  obtain ⟨-, hw⟩ := hall
  obtain ⟨⟨⟨⟨⟨htr, hok⟩, -⟩, hpair⟩, hb0⟩, hrounds⟩ := hw wc hwc
  simp only [WhirCert.ok, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hok
  obtain ⟨hpos, hok⟩ := hok
  have hF := ha.rom.facts
  set g : (Fin wc.rounds.length → E) → Fin wc.rounds.length → E[X] :=
    fun r i => (wc.rounds.getD i default).poly c.outs (val r)
  set cl : (Fin wc.rounds.length → E) → Fin (wc.rounds.length + 1) → E :=
    fun r k => Model.ev (val r) (wc.claimAt c.outs k)
  have hsem : ∀ r (i : Fin wc.rounds.length), (g r i).natDegree ≤ wc.deg ∧
      lin (I.weight r i) (g r i) = cl r i.castSucc ∧ cl r i.succ = (g r i).eval (r i) := by
    intro r i
    obtain ⟨h1, h2, h3⟩ := whirRound_sem (hF r) (hok i i.isLt)
    refine ⟨h1.trans (wc.deg_le i.isLt), by rw [← ha.weight r i]; exact h2, ?_⟩
    simp only [cl, Fin.val_succ, WhirCert.claimAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [h3, ha.chal r i]
  have htm := Cert.marksRO_getD c s htr
  have hpre : PrefixDepOn {r | good r} g := fun r hr r' hr' i hrr => by
    have hb := (hrounds i i.isLt).2
    rw [htm] at hb
    exact WhirRound.poly_congr _ _ fun w hw =>
      ro_agree h htr ha.rom r r' (ha.cr r r' i hr hr' hrr) (fun n hn => hn.mono fun m hm => List.mem_append_left _ hm)
        (whirBound_closure hb w hw) (ha.seed r r' i hrr)
  by_cases hex : ∃ r₀ : Fin wc.rounds.length → E, good r₀
  swap
  · simp only [not_exists] at hex
    exact le_trans (le_of_eq (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun r _ hr => hex r hr.1))) (Nat.zero_le _)
  obtain ⟨r₀, hg₀⟩ := hex
  have hc0 : ∀ r, good r → cl r 0 = cl r₀ 0 := fun r hr =>
    bound_agree h htr ha.rom r r₀
      ((ha.cr r r₀ ⟨0, hpos⟩ hr hg₀ fun j hj => absurd hj (by simp [Fin.lt_def])).anti
        (Cert.liveOn_mono c _ (WhirRound.seedsBefore_sub _ _ _)))
      (boundBy_wires hb0 _ (List.mem_singleton_self _)) fun m hm =>
      ha.seed r r₀ ⟨0, hpos⟩ (fun j hj => absurd hj (by simp [Fin.lt_def])) m (WhirRound.seedsBefore_sub _ _ _ m hm)
  refine le_trans (card_le_card fun r hr => ?_)
    (sumcheck_sound_on S wc.deg I hI {r | good r} g hpre (fun r i => (hsem r i).1) cl (cl r₀ 0)
      (ha.false_claim r₀ hg₀))
  simp only [mem_filter] at hr ⊢
  obtain ⟨hS, hg, htest, hfin⟩ := hr
  refine ⟨hS, hg, hc0 r hg, fun i => (hsem r i).2.1, fun i => (hsem r i).2.2, ?_⟩
  have hlast : cl r (Fin.last wc.rounds.length) = Model.ev (val r) wc.final := by
    simp only [cl, Fin.val_last]
    rcases hpair with hp | hp
    · simp only [Model.ev, htest _ _ hp]
    · simp only [Model.ev, ← htest _ _ hp]
  rw [hlast, hfin]

end LeanVMCircuits.Rec.Bind
