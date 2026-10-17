import Sphincs.LoopWalk
import Sphincs.BridgeVirtualMono

/-!
# The group of one message in the virtual future

For the scan loop `R = R0 + i` the cached digests of one unsigned message act on the potential as
one operator `grp`: the mean, over the start `R0`, of the walk payoffs, where a cached hit `x`
discloses `ext x` (its view), a fresh position that lands discloses nothing for a fresh start (the
fresh view of that signature is the slot's) and a fresh uniform view for a cached start (pending
mass of a dangling query). It is an average of translations of the base function, so it commutes
with the other operators of the virtual future.

* `probe_step`: a digest query at a fresh position is paid by one future coin of probability `w`
  on a uniform view, landing with probability `p`, as soon as
  `(2 − p) / card ≤ p · w · (mass on the identity)`.
* `sign_le`: the true law of the signature (cached hit, or fresh view) is below the group applied
  to one fresh slot.
-/

open ENNReal

namespace Sphincs.LoopWalk

open SphincsFors.Security.Domination Sphincs.Security.Domination

variable {α V : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (p : ℝ≥0∞) (A : ℕ) (U : Finset V)

/-- **The group operator** of one message. -/
noncomputable def grp (st : α → St) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ :=
  (Fintype.card α : ℝ≥0∞)⁻¹ *
    gv σ p st (fun x => F (d + ext x)) (F d) (freshAvg U fun v => F (d + {v})) A

/-- The mass that the group leaves on the identity. -/
noncomputable def idMass (st : α → St) : ℝ≥0∞ :=
  (Fintype.card α : ℝ≥0∞)⁻¹ * gv σ p st (fun _ => 0) 1 0 A

variable {σ p A U}

omit [DecidableEq α] in
theorem grp_add (st : α → St) (ext : α → Multiset V) (F G : Multiset V → ℝ≥0∞) (d : Multiset V) :
    grp σ p A U st ext (fun e => F e + G e) d = grp σ p A U st ext F d + grp σ p A U st ext G d := by
  unfold grp
  rw [freshAvg_add, gv_add, mul_add]

omit [DecidableEq α] in
theorem grp_const_mul (st : α → St) (ext : α → Multiset V) (c : ℝ≥0∞) (F : Multiset V → ℝ≥0∞) (d : Multiset V) :
    grp σ p A U st ext (fun e => c * F e) d = c * grp σ p A U st ext F d := by
  unfold grp
  rw [freshAvg_mul, gv_const_mul]
  ring

omit [DecidableEq α] in
theorem grp_le_of_le (st : α → St) (ext : α → Multiset V) {F G : Multiset V → ℝ≥0∞} (h : ∀ e, F e ≤ G e)
    (d : Multiset V) : grp σ p A U st ext F d ≤ grp σ p A U st ext G d := by
  unfold grp
  refine mul_le_mul' le_rfl (gv_mono st (fun x => h _) (h d) (freshAvg_mono U fun v _ => h _) A)

omit [DecidableEq α] in
theorem grp_congr (st : α → St) (ext : α → Multiset V) {F G : Multiset V → ℝ≥0∞} (h : ∀ e, F e = G e)
    (d : Multiset V) : grp σ p A U st ext F d = grp σ p A U st ext G d :=
  le_antisymm (grp_le_of_le st ext (fun e => (h e).le) d) (grp_le_of_le st ext (fun e => (h e).ge) d)

omit [DecidableEq α] in
/-- Only the disclosures of cached hits matter. -/
theorem grp_congr_ext (st : α → St) {ext ext' : α → Multiset V} (h : ∀ x, st x = .hit → ext x = ext' x)
    (F : Multiset V → ℝ≥0∞) (d : Multiset V) : grp σ p A U st ext F d = grp σ p A U st ext' F d := by
  unfold grp
  rw [gv_congr_item st _ _ fun x hx => by rw [h x hx]]

omit [DecidableEq α] in
/-- The group commutes with translations. -/
theorem grp_shift (st : α → St) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞) (m d : Multiset V) :
    grp σ p A U st ext (fun e => F (e + m)) d = grp σ p A U st ext F (d + m) := by
  unfold grp
  simp only [add_right_comm _ _ m]

omit [DecidableEq α] in
theorem grp_mono (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞} (hF : Monotone' F) :
    Monotone' (grp σ p A U st ext F) := by
  intro small large hle
  unfold grp
  refine mul_le_mul' le_rfl (gv_mono st (fun x => hF _ _ (add_le_add hle le_rfl)) (hF _ _ hle)
    (freshAvg_mono U fun v _ => hF _ _ (add_le_add hle le_rfl)) A)

section Card

variable (hp : p ≤ 1)
include hp

omit [DecidableEq α] in
/-- A constant is kept. -/
theorem grp_const [Nonempty α] (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) (c : ℝ≥0∞) (d : Multiset V) :
    grp σ p A U st ext (fun _ => c) d = c := by
  unfold grp
  rw [freshAvg_const U hU, gv_const hp, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]

omit [DecidableEq α] in
theorem grp_le [Nonempty α] (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞}
    {B : ℝ≥0∞} (h : ∀ e, F e ≤ B) (d : Multiset V) : grp σ p A U st ext F d ≤ B :=
  (grp_le_of_le st ext h d).trans (le_of_eq (grp_const hp hU st ext B d))

omit [DecidableEq α] in
/-- The group only adds disclosures. -/
theorem le_grp [Nonempty α] (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞}
    (hF : Monotone' F) (d : Multiset V) : F d ≤ grp σ p A U st ext F d := by
  calc F d = (Fintype.card α : ℝ≥0∞)⁻¹ * gv σ p st (fun _ => F d) (F d) (F d) A := by
        rw [gv_const hp, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ _ := by
        unfold grp
        refine mul_le_mul' le_rfl (gv_mono st (fun x => hF _ _ (Multiset.le_add_right _ _)) le_rfl ?_ A)
        calc F d = freshAvg U (fun _ => F d) := (freshAvg_const U hU _).symm
          _ ≤ _ := freshAvg_mono U fun v _ => hF _ _ (Multiset.le_add_right _ _)

omit [DecidableEq α] in
/-- A message without cached digest: the identity. -/
theorem grp_fresh [Nonempty α] (st : α → St) (hst : ∀ r, st r = .fresh) (ext : α → Multiset V)
    (F : Multiset V → ℝ≥0∞) (d : Multiset V) : grp σ p A U st ext F d = F d := by
  unfold grp
  rw [gv_fresh hp st hst, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]

omit [DecidableEq α] in
theorem grp_ne_top [Nonempty α] (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞}
    (hF : ∀ e, F e ≠ ⊤) (d : Multiset V) : grp σ p A U st ext F d ≠ ⊤ := by
  set B := (∑ x, F (d + ext x)) + F d + freshAvg U (fun v => F (d + {v})) with hB
  have hBt : B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.sum_ne_top.2 fun x _ => hF _, hF d⟩,
    freshAvg_ne_top hU fun _ => hF _⟩
  refine ne_top_of_le_ne_top hBt ?_
  unfold grp
  calc (Fintype.card α : ℝ≥0∞)⁻¹ * gv σ p st (fun x => F (d + ext x)) (F d) (freshAvg U fun v => F (d + {v})) A
      ≤ (Fintype.card α : ℝ≥0∞)⁻¹ * gv σ p st (fun _ => B) B B A := by
        refine mul_le_mul' le_rfl (gv_mono st (fun x => ?_) ?_ ?_ A)
        · exact le_trans (Finset.single_le_sum (f := fun x => F (d + ext x)) (fun _ _ => bot_le)
            (Finset.mem_univ x)) (le_trans le_self_add le_self_add)
        · exact le_trans le_add_self le_self_add
        · exact le_add_self
    _ = B := by
        rw [gv_const hp, ← mul_assoc,
          ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]

end Card

omit [DecidableEq α] in
theorem freshAvg_comm {W : Type} (T : Finset W) (g : V → W → ℝ≥0∞) :
    freshAvg U (fun v => freshAvg T fun t => g v t) = freshAvg T (fun t => freshAvg U fun v => g v t) := by
  simp only [freshAvg, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

omit [DecidableEq α] in
/-- The group commutes with averages. -/
theorem grp_freshAvg {W : Type} [DecidableEq W] (T : Finset W) (st : α → St) (ext : α → Multiset V)
    (h : W → Multiset V → ℝ≥0∞) (d : Multiset V) :
    grp σ p A U st ext (fun e => freshAvg T fun t => h t e) d =
      freshAvg T (fun t => grp σ p A U st ext (h t) d) := by
  unfold grp
  rw [freshAvg_comm T (fun v t => h t (d + {v}))]
  simp only [freshAvg]
  rw [gv_const_mul, gv_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

omit [DecidableEq α] in
/-- The group commutes with one coin. -/
theorem grp_coin (st : α → St) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞) (w : ℝ≥0∞) (m d : Multiset V) :
    grp σ p A U st ext (fun e => w * F (e + m) + (1 - w) * F e) d =
      w * grp σ p A U st ext F (d + m) + (1 - w) * grp σ p A U st ext F d := by
  rw [grp_add st ext (fun e => w * F (e + m)) (fun e => (1 - w) * F e), grp_const_mul, grp_const_mul,
    grp_shift]

/-- **A stopped group is below the group.** A fresh position that becomes a hit disclosing nothing
can only lower the group of a monotone function. -/
theorem grp_stop_le (hp : p ≤ 1) (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {F : Multiset V → ℝ≥0∞}
    (hF : Monotone' F) (d : Multiset V) (y : α) (hy : st y = .fresh) :
    grp σ p A U (Function.update st y .hit) (Function.update ext y 0) F d ≤ grp σ p A U st ext F d := by
  unfold grp
  refine mul_le_mul' le_rfl ?_
  have hitem : (fun x => F (d + Function.update ext y 0 x)) = Function.update (fun x => F (d + ext x)) y (F d) := by
    funext x
    by_cases hx : x = y
    · subst hx; simp
    · simp [Function.update_of_ne hx]
  rw [hitem]
  refine gv_stop_le hp st (fun x => hF _ _ (Multiset.le_add_right _ _)) ?_ y hy A
  calc F d = freshAvg U (fun _ => F d) := (freshAvg_const U hU _).symm
    _ ≤ _ := freshAvg_mono U fun v _ => hF _ _ (Multiset.le_add_right _ _)

/-- Disclosing less at the hits can only lower the group of a monotone function. -/
theorem grp_ext_mono (st : α → St) {ext ext' : α → Multiset V} (h : ∀ x, ext x ≤ ext' x) {F : Multiset V → ℝ≥0∞}
    (hF : Monotone' F) (d : Multiset V) : grp σ p A U st ext F d ≤ grp σ p A U st ext' F d := by
  unfold grp
  exact mul_le_mul' le_rfl (gv_mono st (fun x => hF _ _ (add_le_add le_rfl (h x))) le_rfl le_rfl A)

/-- The mass on the identity from the counts of cached positions and cached hits. -/
theorem idMass_ge [Nonempty α] (hp : p ≤ 1) (st : α → St) (hA : ∀ x j, 0 < j → j < A → (σ ^ j) x ≠ x) :
    p ≤ p * idMass σ p A st + p * ((Finset.univ.filter fun r => st r ≠ .fresh).card * (Fintype.card α : ℝ≥0∞)⁻¹) +
      (Finset.univ.filter fun x => st x = .hit).card * (1 - p) * (Fintype.card α : ℝ≥0∞)⁻¹ := by
  have h := mass_le hp st A hA
  have hc : (Fintype.card α : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have h2 := mul_le_mul_right' h (Fintype.card α : ℝ≥0∞)⁻¹
  rw [mul_assoc, hc, mul_one] at h2
  refine le_trans h2 (le_of_eq ?_)
  unfold idMass
  ring

/-! ### The group as a mix of translations -/

/-- A weighted family of translations applied to a base function. -/
noncomputable def mixAp (M : List (ℝ≥0∞ × Multiset V)) (F : Multiset V → ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ :=
  (M.map fun c => c.1 * F (d + c.2)).sum

omit [DecidableEq α] in
/-- The group commutes with every mix of translations. -/
theorem grp_mixAp (st : α → St) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞) :
    ∀ (M : List (ℝ≥0∞ × Multiset V)) (d : Multiset V),
      grp σ p A U st ext (fun e => mixAp M F e) d = mixAp M (grp σ p A U st ext F) d
  | [], d => by
      have h := grp_const_mul (σ := σ) (p := p) (A := A) (U := U) st ext 0 (fun _ => 0) d
      simpa [mixAp] using h
  | c :: M, d => by
      have ih := grp_mixAp st ext F M d
      simp only [mixAp, List.map_cons, List.sum_cons] at ih ⊢
      rw [grp_add st ext (fun e => c.1 * F (e + c.2)), grp_const_mul, grp_shift, ih]

/-- The group is a mix of translations. -/
theorem grp_eq_mixAp (st : α → St) (ext : α → Multiset V) :
    ∃ M : List (ℝ≥0∞ × Multiset V), ∀ (F : Multiset V → ℝ≥0∞) (d : Multiset V),
      grp σ p A U st ext F d = mixAp M F d := by
  classical
  set c := (Fintype.card α : ℝ≥0∞)⁻¹
  refine ⟨(Finset.univ.toList.map fun z => (c * gv σ p st (fun x => if x = z then 1 else 0) 0 0 A, ext z)) ++
    ((c * gv σ p st (fun _ => 0) 1 0 A, 0) ::
      (U.toList.map fun v => (c * gv σ p st (fun _ => 0) 0 1 A * (U.card : ℝ≥0∞)⁻¹, ({v} : Multiset V)))), ?_⟩
  intro F d
  have h1 : ((Finset.univ : Finset α).toList.map fun z =>
      c * gv σ p st (fun x => if x = z then 1 else 0) 0 0 A * F (d + ext z)).sum =
      ∑ z, c * gv σ p st (fun x => if x = z then 1 else 0) 0 0 A * F (d + ext z) :=
    Finset.sum_map_toList _ _
  have h2 : (U.toList.map fun v => c * gv σ p st (fun _ => 0) 0 1 A * (U.card : ℝ≥0∞)⁻¹ * F (d + {v})).sum =
      ∑ v ∈ U, c * gv σ p st (fun _ => 0) 0 1 A * (U.card : ℝ≥0∞)⁻¹ * F (d + {v}) :=
    Finset.sum_map_toList _ _
  unfold grp mixAp
  simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
  rw [h1, h2, gv_decomp, add_zero, ← Finset.mul_sum, mul_add, mul_add, Finset.mul_sum, add_assoc]
  congr 1
  · exact Finset.sum_congr rfl fun z _ => by ring
  · congr 1
    · ring
    · unfold freshAvg
      ring

/-- Two groups commute. -/
theorem grp_comm {β : Type} [Fintype β] [DecidableEq β] (τ : Equiv.Perm β) (A' : ℕ) (st : α → St)
    (ext : α → Multiset V) (st' : β → St) (ext' : β → Multiset V) (F : Multiset V → ℝ≥0∞) (d : Multiset V) :
    grp σ p A U st ext (grp τ p A' U st' ext' F) d = grp τ p A' U st' ext' (grp σ p A U st ext F) d := by
  obtain ⟨M, hM⟩ := grp_eq_mixAp (σ := σ) (p := p) (A := A) (U := U) st ext
  rw [hM, ← grp_mixAp]
  exact (grp_congr st' ext' (fun e => hM F e) d).symm

omit [DecidableEq α] in
/-- **The true law is below the group and one fresh slot.** The signature of the message uses a
cached hit `x` (payoff at most `G` after `ext x` and a fresh view) or a fresh landing view. -/
theorem sign_le (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V) {G : Multiset V → ℝ≥0∞}
    (hG : Monotone' G) (d : Multiset V) (item : α → ℝ≥0∞) (fr : ℝ≥0∞)
    (hitem : ∀ x, item x ≤ freshAvg U fun v => G (d + ext x + {v}))
    (hfr : fr ≤ freshAvg U fun v => G (d + {v})) :
    (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ r, walk σ p st item fr 0 A r ≤
      grp σ p A U st ext (fun e => freshAvg U fun v => G (e + {v})) d := by
  unfold grp gv
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun r _ => walk_mono st hitem ?_ bot_le A r)
  split_ifs
  · exact hfr
  · refine le_trans hfr ?_
    calc freshAvg U (fun v => G (d + {v})) = freshAvg U (fun _ => freshAvg U fun v => G (d + {v})) :=
          (freshAvg_const U hU _).symm
      _ ≤ _ := freshAvg_mono U fun v' _ => freshAvg_mono U fun v _ =>
          hG _ _ (add_le_add (Multiset.le_add_right _ _) le_rfl)

/-- **One digest query.** The fresh position `y` of the message is queried: with probability `p` it
becomes a hit with a uniform view, otherwise a miss. In the mean the group is at most the group of
the old state applied to the base function with one more future coin `w` on a uniform view, landing
with probability `p`, provided `(2 − p)/card ≤ p · w · idMass`. -/
theorem probe_step [Nonempty α] (hp : p ≤ 1) (hU : U.Nonempty) (st : α → St) (ext : α → Multiset V)
    {F : Multiset V → ℝ≥0∞} (hF : Monotone' F) (hfin : ∀ e, F e ≠ ⊤) (d : Multiset V) (y : α)
    (hy : st y = .fresh) (hA : ∀ j, 0 < j → j < A → (σ ^ j) y ≠ y) (w : ℝ≥0∞) (hw : w ≤ 1)
    (newExt : V → Multiset V) (hnew : ∀ v, newExt v ≤ {v})
    (hrate : (Fintype.card α : ℝ≥0∞)⁻¹ * ((1 - p) + 1) ≤ p * w * idMass σ p A st) :
    p * freshAvg U (fun v => grp σ p A U (Function.update st y .hit) (Function.update ext y (newExt v)) F d) +
        (1 - p) * grp σ p A U (Function.update st y .miss) ext F d ≤
      grp σ p A U st ext (fun e => (1 - p) * F e + p * freshAvg U fun v => w * F (e + {v}) + (1 - w) * F e) d := by
  set base := F d with hbase
  set favg := freshAvg U (fun v => F (d + {v})) with hfavg
  have hbf : base ≤ favg := by
    calc base = freshAvg U (fun _ => F d) := (freshAvg_const U hU _).symm
      _ ≤ _ := freshAvg_mono U fun v _ => hF _ _ (Multiset.le_add_right _ _)
  set δ := favg - base with hδ
  have hfb : favg = base + δ := (add_tsub_cancel_of_le hbf).symm
  have hbt : base ≠ ⊤ := hfin d
  have hft : favg ≠ ⊤ := freshAvg_ne_top hU fun _ => hfin _
  have hδt : δ ≠ ⊤ := ne_top_of_le_ne_top hft tsub_le_self
  set c := (Fintype.card α : ℝ≥0∞)⁻¹ with hc
  set item : α → ℝ≥0∞ := fun x => F (d + ext x) with hitem
  -- the hit branch, averaged over the view
  have hhit : freshAvg U (fun v => grp σ p A U (Function.update st y .hit) (Function.update ext y (newExt v)) F d) ≤
      c * gv σ p (Function.update st y .hit) (Function.update item y (base + δ)) base (base + δ) A := by
    unfold grp
    rw [freshAvg_mul]
    refine mul_le_mul' le_rfl ?_
    have hpay : ∀ v x, F (d + Function.update ext y (newExt v) x) ≤
        Function.update item y (F (d + {v})) x := by
      intro v x
      by_cases hx : x = y
      · subst hx
        rw [Function.update_self, Function.update_self]
        exact hF _ _ (add_le_add le_rfl (hnew v))
      · rw [Function.update_of_ne hx, Function.update_of_ne hx]
    calc freshAvg U (fun v => gv σ p (Function.update st y .hit)
            (fun x => F (d + Function.update ext y (newExt v) x)) (F d) (freshAvg U fun v' => F (d + {v'})) A)
        ≤ freshAvg U (fun v => gv σ p (Function.update st y .hit)
            (Function.update item y (F (d + {v}))) base favg A) :=
          freshAvg_mono U fun v _ => gv_mono _ (hpay v) le_rfl le_rfl A
      _ = gv σ p (Function.update st y .hit) (fun x => freshAvg U fun v => Function.update item y (F (d + {v})) x)
            (freshAvg U fun _ => base) (freshAvg U fun _ => favg) A := by
          classical
          simp only [freshAvg]
          rw [gv_const_mul, gv_sum]
      _ = _ := by
          rw [freshAvg_const U hU, freshAvg_const U hU, ← hfb]
          congr 1
          funext x
          by_cases hx : x = y
          · subst hx
            simp only [Function.update_self]
            rfl
          · simp only [Function.update_of_ne hx]
            exact freshAvg_const U hU _
  have hmiss : grp σ p A U (Function.update st y .miss) ext F d =
      c * gv σ p (Function.update st y .miss) item base (base + δ) A := by
    unfold grp
    rw [← hfb]
  have hcre := creation_le hp st item base δ hbt hδt y hy A hA
  -- the forecast side
  have hK : ∀ e, freshAvg U (fun v => w * F (e + {v}) + (1 - w) * F e) =
      w * freshAvg U (fun v => F (e + {v})) + (1 - w) * F e := by
    intro e
    rw [freshAvg_add, freshAvg_mul, freshAvg_const U hU]
  have hrhs : grp σ p A U st ext F d + p * w * (idMass σ p A st * δ) ≤
      grp σ p A U st ext (fun e => (1 - p) * F e + p * freshAvg U fun v => w * F (e + {v}) + (1 - w) * F e) d := by
    have hstep : grp σ p A U st ext F d + idMass σ p A st * δ ≤
        grp σ p A U st ext (fun e => freshAvg U fun v => F (e + {v})) d := by
      unfold grp idMass
      rw [mul_assoc, ← mul_add]
      refine mul_le_mul' le_rfl ?_
      calc gv σ p st (fun x => F (d + ext x)) (F d) (freshAvg U fun v => F (d + {v})) A +
            gv σ p st (fun _ => 0) 1 0 A * δ
          = gv σ p st (fun x => F (d + ext x) + δ * 0) (F d + δ * 1) (freshAvg U (fun v => F (d + {v})) + δ * 0) A := by
            rw [gv_add, gv_const_mul, mul_comm]
        _ ≤ _ := by
            refine gv_mono st (fun x => ?_) ?_ ?_ A
            · rw [mul_zero, add_zero]
              calc F (d + ext x) = freshAvg U (fun _ => F (d + ext x)) := (freshAvg_const U hU _).symm
                _ ≤ _ := freshAvg_mono U fun v _ => hF _ _ (Multiset.le_add_right _ _)
            · rw [mul_one]
              exact le_of_eq hfb.symm
            · rw [mul_zero, add_zero]
              refine freshAvg_mono U fun v _ => ?_
              calc F (d + {v}) = freshAvg U (fun _ => F (d + {v})) := (freshAvg_const U hU _).symm
                _ ≤ _ := freshAvg_mono U fun v' _ => hF _ _ (Multiset.le_add_right _ _)
    have hp1 : p ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hp
    have hw1 : w ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hw
    have hlin : grp σ p A U st ext (fun e => (1 - p) * F e + p * freshAvg U fun v => w * F (e + {v}) + (1 - w) * F e) d =
        (1 - p) * grp σ p A U st ext F d + p * (w * grp σ p A U st ext (fun e => freshAvg U fun v => F (e + {v})) d +
          (1 - w) * grp σ p A U st ext F d) := by
      rw [grp_add st ext (fun e => (1 - p) * F e), grp_const_mul, grp_const_mul]
      congr 2
      rw [grp_congr st ext hK, grp_add st ext (fun e => w * freshAvg U fun v => F (e + {v})), grp_const_mul,
        grp_const_mul]
    rw [hlin]
    set X := grp σ p A U st ext F d
    set Y := grp σ p A U st ext (fun e => freshAvg U fun v => F (e + {v})) d
    calc X + p * w * (idMass σ p A st * δ)
        = (1 - p) * X + p * (w * (X + idMass σ p A st * δ) + (1 - w) * X) := by
          have h1 : X = (1 - p) * X + p * X := by rw [← add_mul, tsub_add_cancel_of_le hp, one_mul]
          have h2 : X = w * X + (1 - w) * X := by rw [← add_mul, add_tsub_cancel_of_le hw, one_mul]
          calc X + p * w * (idMass σ p A st * δ) = (1 - p) * X + p * X + p * w * (idMass σ p A st * δ) := by
                rw [← h1]
            _ = (1 - p) * X + p * (w * X + (1 - w) * X) + p * w * (idMass σ p A st * δ) := by rw [← h2]
            _ = _ := by ring
      _ ≤ _ := by gcongr
  calc p * freshAvg U (fun v => grp σ p A U (Function.update st y .hit) (Function.update ext y (newExt v)) F d) +
        (1 - p) * grp σ p A U (Function.update st y .miss) ext F d
      ≤ p * (c * gv σ p (Function.update st y .hit) (Function.update item y (base + δ)) base (base + δ) A) +
        (1 - p) * (c * gv σ p (Function.update st y .miss) item base (base + δ) A) := by
        rw [hmiss]; gcongr
    _ = c * (p * gv σ p (Function.update st y .hit) (Function.update item y (base + δ)) base (base + δ) A +
          (1 - p) * gv σ p (Function.update st y .miss) item base (base + δ) A) := by ring
    _ ≤ c * (gv σ p st item base (base + δ) A + (1 - p) * δ + δ) := mul_le_mul' le_rfl hcre
    _ = grp σ p A U st ext F d + c * ((1 - p) + 1) * δ := by
        unfold grp
        rw [← hfb]
        ring
    _ ≤ grp σ p A U st ext F d + p * w * idMass σ p A st * δ := by gcongr
    _ = grp σ p A U st ext F d + p * w * (idMass σ p A st * δ) := by rw [mul_assoc (p * w)]
    _ ≤ _ := hrhs

end Sphincs.LoopWalk
