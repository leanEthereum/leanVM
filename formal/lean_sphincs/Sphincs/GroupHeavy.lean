import Sphincs.GroupFuture

/-!
# The true law of the signature of a message

`sgn` is the group operator in which a fresh position that lands discloses a fresh uniform view for
every start: it is the law of the view disclosed by the signature of the message (a cached hit, or a
fresh view), applied to a base function. It needs no forecast: a digest query of the message keeps
its mean exactly (`sgn_probe`). It consumes one fresh slot: `sgn X ≤ grp (X after a fresh view)`.
It is used for the one message on which more than half of the budget was spent, whose group can
hold almost all the mass.
-/

open ENNReal

namespace Sphincs.LoopWalk

open SphincsFors.Security.Domination Sphincs.Security.Domination

variable {α V : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (p : ℝ≥0∞) (A : ℕ) (U : Finset V)

/-- The sum over the starts of the walk payoffs, with the same payoffs for every start. -/
noncomputable def ws (st : α → St) (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ r, walk σ p st item fr ex A r

/-- **The law of the signed view** applied to a base function. -/
noncomputable def sgn (st : α → St) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ :=
  (Fintype.card α : ℝ≥0∞)⁻¹ * ws σ p A st (fun x => F (d + ext x)) (freshAvg U fun v => F (d + {v})) (F d)

variable {σ p A U}

omit [DecidableEq α] in
theorem ws_add (st : α → St) (item item' : α → ℝ≥0∞) (fr fr' ex ex' : ℝ≥0∞) :
    ws σ p A st (fun x => item x + item' x) (fr + fr') (ex + ex') =
      ws σ p A st item fr ex + ws σ p A st item' fr' ex' := by
  unfold ws
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => walk_add st item item' fr fr' ex ex' A r

omit [DecidableEq α] in
theorem ws_const_mul (st : α → St) (item : α → ℝ≥0∞) (fr ex c : ℝ≥0∞) :
    ws σ p A st (fun x => c * item x) (c * fr) (c * ex) = c * ws σ p A st item fr ex := by
  unfold ws
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => walk_const_mul st item fr ex c A r

omit [DecidableEq α] in
theorem ws_mono (st : α → St) {item item' : α → ℝ≥0∞} {fr fr' ex ex' : ℝ≥0∞} (hi : ∀ x, item x ≤ item' x)
    (hf : fr ≤ fr') (he : ex ≤ ex') : ws σ p A st item fr ex ≤ ws σ p A st item' fr' ex' :=
  Finset.sum_le_sum fun r _ => walk_mono st hi hf he A r

omit [DecidableEq α] in
theorem ws_zero (st : α → St) : ws σ p A st (fun _ => 0) 0 0 = 0 := by
  have h := ws_const_mul (σ := σ) (p := p) (A := A) st (fun _ => 0) 0 0 0
  simpa using h

omit [DecidableEq α] in
theorem ws_sum {ι : Type} [DecidableEq ι] (T : Finset ι) (st : α → St) (f : ι → α → ℝ≥0∞) (b e : ι → ℝ≥0∞) :
    ws σ p A st (fun x => ∑ t ∈ T, f t x) (∑ t ∈ T, b t) (∑ t ∈ T, e t) = ∑ t ∈ T, ws σ p A st (f t) (b t) (e t) := by
  induction T using Finset.induction_on with
  | empty => simp [ws_zero]
  | insert a T ha ih =>
      simp only [Finset.sum_insert ha]
      rw [ws_add, ih]

omit [DecidableEq α] in
theorem ws_le_gv (st : α → St) (item : α → ℝ≥0∞) {base favg : ℝ≥0∞} (h : base ≤ favg) :
    gv σ p st item base favg A ≤ ws σ p A st item favg base := by
  unfold gv ws
  refine Finset.sum_le_sum fun r _ => walk_mono st (fun _ => le_rfl) ?_ le_rfl A r
  split_ifs
  · exact h
  · exact le_rfl

omit [DecidableEq α] in
theorem sgn_add (st : α → St) (ext : α → Multiset V) (F G : Multiset V → ℝ≥0∞) (d : Multiset V) :
    sgn σ p A U st ext (fun e => F e + G e) d = sgn σ p A U st ext F d + sgn σ p A U st ext G d := by
  unfold sgn
  rw [freshAvg_add, ws_add, mul_add]

omit [DecidableEq α] in
theorem sgn_const_mul (st : α → St) (ext : α → Multiset V) (c : ℝ≥0∞) (F : Multiset V → ℝ≥0∞) (d : Multiset V) :
    sgn σ p A U st ext (fun e => c * F e) d = c * sgn σ p A U st ext F d := by
  unfold sgn
  rw [freshAvg_mul, ws_const_mul]
  ring

omit [DecidableEq α] in
theorem sgn_le_of_le (st : α → St) (ext : α → Multiset V) {F G : Multiset V → ℝ≥0∞} (h : ∀ e, F e ≤ G e)
    (d : Multiset V) : sgn σ p A U st ext F d ≤ sgn σ p A U st ext G d := by
  unfold sgn
  exact mul_le_mul' le_rfl (ws_mono st (fun x => h _) (freshAvg_mono U fun v _ => h _) (h d))

omit [DecidableEq α] in
theorem sgn_congr (st : α → St) (ext : α → Multiset V) {F G : Multiset V → ℝ≥0∞} (h : ∀ e, F e = G e)
    (d : Multiset V) : sgn σ p A U st ext F d = sgn σ p A U st ext G d :=
  le_antisymm (sgn_le_of_le st ext (fun e => (h e).le) d) (sgn_le_of_le st ext (fun e => (h e).ge) d)

omit [DecidableEq α] in
theorem sgn_shift (st : α → St) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞) (m d : Multiset V) :
    sgn σ p A U st ext (fun e => F (e + m)) d = sgn σ p A U st ext F (d + m) := by
  unfold sgn
  simp only [add_right_comm _ _ m]

omit [DecidableEq α] in
theorem sgn_mono (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞} (hF : Monotone' F) :
    Monotone' (sgn σ p A U st ext F) := by
  intro small large hle
  unfold sgn
  exact mul_le_mul' le_rfl (ws_mono st (fun x => hF _ _ (add_le_add hle le_rfl))
    (freshAvg_mono U fun v _ => hF _ _ (add_le_add hle le_rfl)) (hF _ _ hle))

omit [DecidableEq α] in
/-- The group is below the law of the signed view. -/
theorem grp_le_sgn (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞}
    (hF : Monotone' F) (d : Multiset V) : grp σ p A U st ext F d ≤ sgn σ p A U st ext F d := by
  unfold grp sgn
  refine mul_le_mul' le_rfl (ws_le_gv st _ ?_)
  calc F d = freshAvg U (fun _ => F d) := (freshAvg_const U hU _).symm
    _ ≤ _ := freshAvg_mono U fun v _ => hF _ _ (Multiset.le_add_right _ _)

omit [DecidableEq α] in
/-- **The law of the signed view consumes one fresh slot.** -/
theorem sgn_le_grp (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {X : Multiset V → ℝ≥0∞}
    (hX : Monotone' X) (d : Multiset V) :
    sgn σ p A U st ext X d ≤ grp σ p A U st ext (fun e => freshAvg U fun v => X (e + {v})) d := by
  have hUX : ∀ e, X e ≤ freshAvg U (fun v => X (e + {v})) := by
    intro e
    calc X e = freshAvg U (fun _ => X e) := (freshAvg_const U hU _).symm
      _ ≤ _ := freshAvg_mono U fun v _ => hX _ _ (Multiset.le_add_right _ _)
  unfold sgn grp gv ws
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ => walk_mono st (fun x => hUX _) ?_ (hUX d) A r)
  split_ifs
  · exact le_rfl
  · calc freshAvg U (fun v => X (d + {v})) = freshAvg U (fun _ => freshAvg U fun v => X (d + {v})) :=
          (freshAvg_const U hU _).symm
      _ ≤ _ := freshAvg_mono U fun v' _ => freshAvg_mono U fun v _ =>
          hX _ _ (add_le_add (Multiset.le_add_right _ _) le_rfl)

/-- **A digest query keeps the law of the signed view in the mean.** -/
theorem sgn_probe (hp : p ≤ 1) (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V)
    {F : Multiset V → ℝ≥0∞} (hF : Monotone' F) (hfin : ∀ e, F e ≠ ⊤) (d : Multiset V) (y : α)
    (hy : st y = .fresh) (hA : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y)
    (newExt : V → Multiset V) (hnew : ∀ v, newExt v ≤ {v}) :
    p * freshAvg U (fun v => sgn σ p A U (Function.update st y .hit) (Function.update ext y (newExt v)) F d) +
        (1 - p) * sgn σ p A U (Function.update st y .miss) ext F d ≤ sgn σ p A U st ext F d := by
  classical
  set favg := freshAvg U (fun v => F (d + {v})) with hfavg
  set item : α → ℝ≥0∞ := fun x => F (d + ext x) with hitem
  set c := (Fintype.card α : ℝ≥0∞)⁻¹ with hc
  have hft : favg ≠ ⊤ := freshAvg_ne_top hU fun _ => hfin _
  have hhit : freshAvg U (fun v => sgn σ p A U (Function.update st y .hit) (Function.update ext y (newExt v)) F d) ≤
      c * ws σ p A (Function.update st y .hit) (Function.update item y favg) favg (F d) := by
    unfold sgn
    rw [freshAvg_mul]
    refine mul_le_mul' le_rfl ?_
    have hpay : ∀ v x, F (d + Function.update ext y (newExt v) x) ≤ Function.update item y (F (d + {v})) x := by
      intro v x
      by_cases hx : x = y
      · subst hx
        rw [Function.update_self, Function.update_self]
        exact hF _ _ (add_le_add le_rfl (hnew v))
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
    calc freshAvg U (fun v => ws σ p A (Function.update st y .hit)
            (fun x => F (d + Function.update ext y (newExt v) x)) (freshAvg U fun v' => F (d + {v'})) (F d))
        ≤ freshAvg U (fun v => ws σ p A (Function.update st y .hit)
            (Function.update item y (F (d + {v}))) favg (F d)) :=
          freshAvg_mono U fun v _ => ws_mono _ (hpay v) le_rfl le_rfl
      _ = ws σ p A (Function.update st y .hit) (fun x => freshAvg U fun v => Function.update item y (F (d + {v})) x)
            (freshAvg U fun _ => favg) (freshAvg U fun _ => F d) := by
          simp only [freshAvg]
          rw [ws_const_mul, ws_sum]
      _ = _ := by
          rw [freshAvg_const U hU, freshAvg_const U hU]
          congr 1
          funext x
          by_cases hx : x = y
          · subst hx
            simp only [Function.update_self]
            rfl
          · simp only [Function.update_of_ne hx]
            exact freshAvg_const U hU _
  have hstart : ∀ r, p * walk σ p (Function.update st y .hit) (Function.update item y favg) favg (F d) A r +
      (1 - p) * walk σ p (Function.update st y .miss) item favg (F d) A r = walk σ p st item favg (F d) A r := by
    intro r
    have h := probe_eq hp st item favg (F d) favg y hy A hA r
    have hρ : p * reach σ p st y A r * favg ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ne_top_of_le_ne_top one_ne_top hp) (reach_ne_top st y A r)) hft
    exact (ENNReal.add_left_inj hρ).1 h
  calc p * freshAvg U (fun v => sgn σ p A U (Function.update st y .hit) (Function.update ext y (newExt v)) F d) +
        (1 - p) * sgn σ p A U (Function.update st y .miss) ext F d
      ≤ p * (c * ws σ p A (Function.update st y .hit) (Function.update item y favg) favg (F d)) +
        (1 - p) * (c * ws σ p A (Function.update st y .miss) item favg (F d)) := by
        gcongr
        exact le_rfl
    _ = c * ∑ r, (p * walk σ p (Function.update st y .hit) (Function.update item y favg) favg (F d) A r +
          (1 - p) * walk σ p (Function.update st y .miss) item favg (F d) A r) := by
        unfold ws
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ = _ := by
        unfold sgn ws
        rw [Finset.sum_congr rfl fun r _ => hstart r]

/-! ### The law of the signed view as a mix of translations -/

theorem ws_decomp (st : α → St) (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) :
    ws σ p A st item fr ex =
      ∑ z, item z * ws σ p A st (fun x => if x = z then 1 else 0) 0 0 +
        fr * ws σ p A st (fun _ => 0) 1 0 + ex * ws σ p A st (fun _ => 0) 0 1 := by
  have hitem : ws σ p A st item 0 0 = ∑ z, item z * ws σ p A st (fun x => if x = z then 1 else 0) 0 0 := by
    have hz : ∀ z, ws σ p A st (fun x => item z * (if x = z then 1 else 0)) 0 0 =
        item z * ws σ p A st (fun x => if x = z then 1 else 0) 0 0 := by
      intro z
      have h := ws_const_mul (σ := σ) (p := p) (A := A) st (fun x => if x = z then 1 else 0) 0 0 (item z)
      simpa using h
    have h := ws_sum (σ := σ) (p := p) (A := A) Finset.univ st (fun z x => item z * (if x = z then 1 else 0))
      (fun _ => 0) (fun _ => 0)
    simp only [Finset.sum_const_zero, hz] at h
    rw [← h]
    congr 1
    funext x
    simp
  calc ws σ p A st item fr ex
      = ws σ p A st (fun x => (item x + fr * 0) + ex * 0) ((0 + fr * 1) + ex * 0) ((0 + fr * 0) + ex * 1) := by
        simp
    _ = _ := by
        rw [ws_add st (fun x => item x + fr * 0) (fun _ => ex * 0), ws_add st item (fun _ => fr * 0),
          ws_const_mul, ws_const_mul, hitem]

theorem sgn_eq_mixAp (st : α → St) (ext : α → Multiset V) :
    ∃ M : List (ℝ≥0∞ × Multiset V), ∀ (F : Multiset V → ℝ≥0∞) (d : Multiset V),
      sgn σ p A U st ext F d = mixAp M F d := by
  classical
  set c := (Fintype.card α : ℝ≥0∞)⁻¹
  refine ⟨(Finset.univ.toList.map fun z => (c * ws σ p A st (fun x => if x = z then 1 else 0) 0 0, ext z)) ++
    ((c * ws σ p A st (fun _ => 0) 0 1, 0) ::
      (U.toList.map fun v => (c * ws σ p A st (fun _ => 0) 1 0 * (U.card : ℝ≥0∞)⁻¹, ({v} : Multiset V)))), ?_⟩
  intro F d
  have h1 : ((Finset.univ : Finset α).toList.map fun z =>
      c * ws σ p A st (fun x => if x = z then 1 else 0) 0 0 * F (d + ext z)).sum =
      ∑ z, c * ws σ p A st (fun x => if x = z then 1 else 0) 0 0 * F (d + ext z) :=
    Finset.sum_map_toList _ _
  have h2 : (U.toList.map fun v => c * ws σ p A st (fun _ => 0) 1 0 * (U.card : ℝ≥0∞)⁻¹ * F (d + {v})).sum =
      ∑ v ∈ U, c * ws σ p A st (fun _ => 0) 1 0 * (U.card : ℝ≥0∞)⁻¹ * F (d + {v}) :=
    Finset.sum_map_toList _ _
  unfold sgn mixAp
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
  rw [h1, h2, ws_decomp, add_zero, ← Finset.mul_sum, mul_add, mul_add, Finset.mul_sum, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun z _ => by ring
  · rw [add_comm]
    congr 1
    · ring
    · unfold freshAvg
      ring

/-- A group commutes with the law of the signed view of another message. -/
theorem grp_sgn_comm {β : Type} [Fintype β] [DecidableEq β] (τ : Equiv.Perm β) (A' : ℕ) (st : α → St)
    (ext : α → Multiset V) (st' : β → St) (ext' : β → Multiset V) (F : Multiset V → ℝ≥0∞) (d : Multiset V) :
    grp τ p A' U st' ext' (sgn σ p A U st ext F) d = sgn σ p A U st ext (grp τ p A' U st' ext' F) d := by
  obtain ⟨M, hM⟩ := sgn_eq_mixAp (σ := σ) (p := p) (A := A) (U := U) st ext
  rw [hM, ← grp_mixAp]
  exact grp_congr st' ext' (fun e => hM F e) d

end Sphincs.LoopWalk
