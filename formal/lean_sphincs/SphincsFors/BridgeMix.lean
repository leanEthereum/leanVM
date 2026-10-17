import SphincsFors.BridgeWalk

/-! Operators on base functions that are finite nonnegative combinations of translates
(`h ↦ fun d => Σ a_i h (d + e_i)`). Coins, fresh slots, future pairs and the walk of a signer are
all of this form, so they are linear and monotone in the base function, they preserve monotone
supermodular finite functions, and any two of them commute. -/

open ENNReal

namespace SphincsFors.Security.Domination

variable {V : Type}

/-- A finite nonnegative combination of translates. -/
noncomputable def mix (K : List (ℝ≥0∞ × Multiset V)) (h : Multiset V → ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ :=
  (K.map fun c => c.1 * h (d + c.2)).sum

/-- An operator that is a finite combination of translates with finite weights. -/
def Rep (T : (Multiset V → ℝ≥0∞) → Multiset V → ℝ≥0∞) : Prop :=
  ∃ K : List (ℝ≥0∞ × Multiset V), (∀ c ∈ K, c.1 ≠ ⊤) ∧ ∀ h d, T h d = mix K h d

theorem mix_add (K : List (ℝ≥0∞ × Multiset V)) (f g : Multiset V → ℝ≥0∞) (d : Multiset V) :
    mix K (fun D => f D + g D) d = mix K f d + mix K g d := by
  unfold mix
  rw [← List.sum_map_add]
  simp only [mul_add]

theorem mix_const_mul (K : List (ℝ≥0∞ × Multiset V)) (k : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) (d : Multiset V) :
    mix K (fun D => k * f D) d = k * mix K f d := by
  unfold mix
  rw [← List.sum_map_mul_left]
  simp only [mul_left_comm]

theorem mix_zero (K : List (ℝ≥0∞ × Multiset V)) (d : Multiset V) : mix K (fun _ => 0) d = 0 := by
  unfold mix
  simp

theorem mix_mono_above (K : List (ℝ≥0∞ × Multiset V)) {f g : Multiset V → ℝ≥0∞} (d : Multiset V)
    (h : ∀ D, d ≤ D → f D ≤ g D) : mix K f d ≤ mix K g d := by
  unfold mix
  refine List.sum_le_sum fun c _ => ?_
  exact mul_le_mul_right (h _ (Multiset.le_add_right _ _)) _

theorem mix_translate (K : List (ℝ≥0∞ × Multiset V)) (f : Multiset V → ℝ≥0∞) (e d : Multiset V) :
    mix K (fun D => f (D + e)) d = mix K f (d + e) := by
  unfold mix
  simp only [add_right_comm d _ e]

theorem mix_tsum {β : Type} (K : List (ℝ≥0∞ × Multiset V)) (w : β → ℝ≥0∞) (F : β → Multiset V → ℝ≥0∞)
    (d : Multiset V) : mix K (fun D => ∑' x, w x * F x D) d = ∑' x, w x * mix K (F x) d := by
  unfold mix
  induction K with
  | nil => simp
  | cons c K ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add]
      rw [ih]
      congr 1
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun x => by ring

namespace Rep

variable {T T' : (Multiset V → ℝ≥0∞) → Multiset V → ℝ≥0∞}

protected theorem id : Rep (fun (h : Multiset V → ℝ≥0∞) d => h d) :=
  ⟨[(1, 0)], by simp, fun h d => by simp [mix]⟩

protected theorem zero : Rep (fun (_ : Multiset V → ℝ≥0∞) _ => 0) :=
  ⟨[], by simp, fun h d => by simp [mix]⟩

theorem shift (hT : Rep T) (e : Multiset V) : Rep (fun h d => T h (d + e)) := by
  obtain ⟨K, hfin, hK⟩ := hT
  refine ⟨K.map fun c => (c.1, e + c.2), ?_, fun h d => ?_⟩
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact hfin c' hc'
  · beta_reduce
    rw [hK]
    unfold mix
    rw [List.map_map]
    simp only [Function.comp_def, add_assoc]

theorem translate (e : Multiset V) : Rep (fun (h : Multiset V → ℝ≥0∞) d => h (d + e)) := Rep.id.shift e

protected theorem add (hT : Rep T) (hT' : Rep T') : Rep (fun h d => T h d + T' h d) := by
  obtain ⟨K, hfin, hK⟩ := hT
  obtain ⟨K', hfin', hK'⟩ := hT'
  refine ⟨K ++ K', ?_, fun h d => ?_⟩
  · intro c hc
    rcases List.mem_append.1 hc with h | h
    · exact hfin c h
    · exact hfin' c h
  · beta_reduce
    rw [hK, hK']
    unfold mix
    rw [List.map_append, List.sum_append]

theorem const_mul (hT : Rep T) {k : ℝ≥0∞} (hk : k ≠ ⊤) : Rep (fun h d => k * T h d) := by
  obtain ⟨K, hfin, hK⟩ := hT
  refine ⟨K.map fun c => (k * c.1, c.2), ?_, fun h d => ?_⟩
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    exact ENNReal.mul_ne_top hk (hfin c' hc')
  · beta_reduce
    rw [hK]
    unfold mix
    rw [List.map_map, ← List.sum_map_mul_left]
    simp only [Function.comp_def, mul_assoc]

theorem list_sum {ι : Type} (F : ι → (Multiset V → ℝ≥0∞) → Multiset V → ℝ≥0∞) :
    ∀ l : List ι, (∀ i ∈ l, Rep (F i)) → Rep (fun h d => (l.map fun i => F i h d).sum)
  | [], _ => by simpa using (Rep.zero : Rep (fun (_ : Multiset V → ℝ≥0∞) _ => 0))
  | i :: l, h => by
      have h1 := h i (List.mem_cons_self ..)
      have h2 := list_sum F l fun j hj => h j (List.mem_cons_of_mem _ hj)
      simpa using h1.add h2

theorem finset_sum {ι : Type} (S : Finset ι) (F : ι → (Multiset V → ℝ≥0∞) → Multiset V → ℝ≥0∞)
    (h : ∀ i, Rep (F i)) : Rep (fun g d => ∑ i ∈ S, F i g d) := by
  have := list_sum F S.toList fun i _ => h i
  simpa [Finset.sum_toList] using this

theorem freshAvg {W : Type} (U : Finset W) (F : W → (Multiset V → ℝ≥0∞) → Multiset V → ℝ≥0∞)
    (h : ∀ u, Rep (F u)) : Rep (fun g d => freshAvg U fun u => F u g d) := by
  by_cases hU : U.Nonempty
  · have hk : ((U.card : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simpa using hU.ne_empty)
    exact (finset_sum U F h).const_mul hk
  · rw [Finset.not_nonempty_iff_eq_empty] at hU
    subst hU
    simpa [Domination.freshAvg] using (Rep.zero : Rep (fun (_ : Multiset V → ℝ≥0∞) _ => 0))

theorem comp (hT : Rep T) (hT' : Rep T') : Rep (fun h d => T (fun D => T' h D) d) := by
  obtain ⟨K, hfin, hK⟩ := hT
  have h := list_sum (fun (c : ℝ≥0∞ × Multiset V) h d => c.1 * T' h (d + c.2)) K
    fun c hc => (hT'.shift c.2).const_mul (hfin c hc)
  obtain ⟨K2, hfin2, hK2⟩ := h
  exact ⟨K2, hfin2, fun h d => by beta_reduce; rw [hK, ← hK2]; rfl⟩

/-! Consequences. -/

theorem map_add (hT : Rep T) (f g : Multiset V → ℝ≥0∞) (d : Multiset V) :
    T (fun D => f D + g D) d = T f d + T g d := by
  obtain ⟨K, _, hK⟩ := hT
  simp only [hK, mix_add]

theorem map_const_mul (hT : Rep T) (k : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) (d : Multiset V) :
    T (fun D => k * f D) d = k * T f d := by
  obtain ⟨K, _, hK⟩ := hT
  simp only [hK, mix_const_mul]

theorem map_zero (hT : Rep T) (d : Multiset V) : T (fun _ => 0) d = 0 := by
  obtain ⟨K, _, hK⟩ := hT
  simp only [hK, mix_zero]

theorem map_mono_above (hT : Rep T) {f g : Multiset V → ℝ≥0∞} (d : Multiset V) (h : ∀ D, d ≤ D → f D ≤ g D) :
    T f d ≤ T g d := by
  obtain ⟨K, _, hK⟩ := hT
  simp only [hK]
  exact mix_mono_above K d h

theorem map_mono (hT : Rep T) {f g : Multiset V → ℝ≥0∞} (h : ∀ D, f D ≤ g D) (d : Multiset V) : T f d ≤ T g d :=
  hT.map_mono_above d fun D _ => h D

theorem map_congr (hT : Rep T) {f g : Multiset V → ℝ≥0∞} (h : ∀ D, f D = g D) (d : Multiset V) : T f d = T g d :=
  le_antisymm (hT.map_mono (fun D => (h D).le) d) (hT.map_mono (fun D => (h D).ge) d)

theorem map_translate (hT : Rep T) (f : Multiset V → ℝ≥0∞) (e d : Multiset V) :
    T (fun D => f (D + e)) d = T f (d + e) := by
  obtain ⟨K, _, hK⟩ := hT
  simp only [hK, mix_translate]

theorem map_list_sum (hT : Rep T) {ι : Type} (F : ι → Multiset V → ℝ≥0∞) (d : Multiset V) :
    ∀ l : List ι, T (fun D => (l.map fun i => F i D).sum) d = (l.map fun i => T (F i) d).sum
  | [] => by simpa using hT.map_zero d
  | i :: l => by
      have := hT.map_add (F i) (fun D => (l.map fun i => F i D).sum) d
      simp only [List.map_cons, List.sum_cons]
      rw [this, map_list_sum hT F d l]

theorem map_finset_sum (hT : Rep T) {ι : Type} (S : Finset ι) (F : ι → Multiset V → ℝ≥0∞) (d : Multiset V) :
    T (fun D => ∑ i ∈ S, F i D) d = ∑ i ∈ S, T (F i) d := by
  have := hT.map_list_sum F d S.toList
  simpa [Finset.sum_toList] using this

theorem map_freshAvg (hT : Rep T) {W : Type} (U : Finset W) (F : W → Multiset V → ℝ≥0∞) (d : Multiset V) :
    T (fun D => Domination.freshAvg U fun u => F u D) d = Domination.freshAvg U fun u => T (F u) d := by
  unfold Domination.freshAvg
  rw [hT.map_const_mul, hT.map_finset_sum]

/-- Expectations over an outcome commute with the operator. -/
theorem map_tsum (hT : Rep T) {β : Type} (w : β → ℝ≥0∞) (F : β → Multiset V → ℝ≥0∞) (d : Multiset V) :
    T (fun D => ∑' x, w x * F x D) d = ∑' x, w x * T (F x) d := by
  obtain ⟨K, _, hK⟩ := hT
  simp only [hK, mix_tsum]

/-- Any two such operators commute. -/
theorem comm (hT : Rep T) (hT' : Rep T') (f : Multiset V → ℝ≥0∞) (d : Multiset V) :
    T (fun D => T' f D) d = T' (fun D => T f D) d := by
  obtain ⟨K, _, hK⟩ := hT
  have h1 : T (fun D => T' f D) d = (K.map fun c => c.1 * T' f (d + c.2)).sum := by rw [hK]; rfl
  have h2 : T' (fun D => T f D) d = (K.map fun c => T' (fun D => c.1 * f (D + c.2)) d).sum := by
    have : (fun D => T f D) = fun D => (K.map fun c => c.1 * f (D + c.2)).sum := by
      funext D; rw [hK]; rfl
    rw [this]
    exact hT'.map_list_sum (fun c D => c.1 * f (D + c.2)) d K
  rw [h1, h2]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  rw [hT'.map_const_mul, hT'.map_translate]

theorem monotone' (hT : Rep T) {f : Multiset V → ℝ≥0∞} (hf : Monotone' f) : Monotone' (T f) := by
  obtain ⟨K, _, hK⟩ := hT
  intro small large hle
  rw [hK, hK]
  unfold mix
  exact List.sum_le_sum fun c _ => mul_le_mul_right (hf _ _ (add_le_add hle le_rfl)) _

theorem supermodular (hT : Rep T) {f : Multiset V → ℝ≥0∞} (hf : Supermodular f) : Supermodular (T f) := by
  obtain ⟨K, _, hK⟩ := hT
  intro small large extra hle
  rw [hK, hK, hK, hK]
  unfold mix
  rw [← List.sum_map_add, ← List.sum_map_add]
  refine List.sum_le_sum fun c _ => ?_
  have := hf (small + c.2) (large + c.2) extra (add_le_add hle le_rfl)
  rw [add_right_comm small c.2 extra, add_right_comm large c.2 extra] at this
  calc c.1 * f (small + extra + c.2) + c.1 * f (large + c.2)
      = c.1 * (f (small + extra + c.2) + f (large + c.2)) := by ring
    _ ≤ c.1 * (f (large + extra + c.2) + f (small + c.2)) := mul_le_mul_right this _
    _ = _ := by ring

theorem ne_top (hT : Rep T) {f : Multiset V → ℝ≥0∞} (hf : ∀ D, f D ≠ ⊤) (d : Multiset V) : T f d ≠ ⊤ := by
  obtain ⟨K, hfin, hK⟩ := hT
  rw [hK]
  unfold mix
  refine list_sum_ne_top _ fun v hv => ?_
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
  exact ENNReal.mul_ne_top (hfin c hc) (hf _)

theorem props (hT : Rep T) {f : Multiset V → ℝ≥0∞} (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) :
    Monotone' (T f) ∧ Supermodular (T f) ∧ ∀ D, T f D ≠ ⊤ :=
  ⟨hT.monotone' hf.1, hT.supermodular hf.2.1, hT.ne_top hf.2.2⟩

end Rep

/-! ### The operators of the virtual future -/

theorem rep_slotValue : ∀ (coins : List (ℝ≥0∞ × Multiset V)), (∀ c ∈ coins, c.1 ≤ 1) →
    Rep (fun (h : Multiset V → ℝ≥0∞) d => slotValue h d coins)
  | [], _ => Rep.id
  | (p, extra) :: rest, hc => by
      have hp : p ≤ 1 := hc (p, extra) (List.mem_cons_self ..)
      have ih := rep_slotValue rest fun c h => hc c (List.mem_cons_of_mem _ h)
      have h1 := (ih.shift extra).const_mul (ne_top_of_le_ne_top ENNReal.one_ne_top hp)
      have h2 := ih.const_mul (k := 1 - p) (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      simpa only [slotValue] using h1.add h2

theorem rep_fresh (U : Finset V) : ∀ m : ℕ, Rep (fun (h : Multiset V → ℝ≥0∞) d => fresh U h m d)
  | 0 => Rep.id
  | m + 1 => by
      have := Rep.freshAvg U (fun u (h : Multiset V → ℝ≥0∞) d => fresh U h m (d + {u}))
        fun u => (rep_fresh U m).shift {u}
      simpa only [fresh] using this

theorem rep_virtualOnce (U : Finset V) {w : ℝ≥0∞} (hw : w ≤ 1) (m : ℕ) (coins : List V) :
    Rep (fun (h : Multiset V → ℝ≥0∞) d => virtualOnce U w h m coins d) := by
  have h1 := rep_slotValue (itemCoins w coins) (itemCoins_le hw coins)
  have := h1.comp (rep_fresh U m)
  simpa only [virtualOnce] using this

theorem rep_creations (U : Finset V) {land : ℝ≥0∞} (hland : land ≤ 1)
    (T : List V → (Multiset V → ℝ≥0∞) → Multiset V → ℝ≥0∞) (hT : ∀ J, Rep (T J)) :
    ∀ (k : ℕ) (I : List V), Rep (fun h d => creations U land (fun J => T J h d) k I)
  | 0, I => hT I
  | k + 1, I => by
      have h1 := (rep_creations U hland T hT k I).const_mul (k := 1 - land)
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      have h2 := (Rep.freshAvg U (fun v h d => creations U land (fun J => T J h d) k (v :: I))
        fun v => rep_creations U hland T hT k (v :: I)).const_mul (ne_top_of_le_ne_top ENNReal.one_ne_top hland)
      simpa only [creations] using h1.add h2

theorem rep_val {R : Type} (e : R → R) (s t : R → ℝ≥0∞) (hs : ∀ x, s x ≠ ⊤) (ht : ∀ x, t x ≠ ⊤)
    (c : (Multiset V → ℝ≥0∞) → Multiset V → R → ℝ≥0∞) (ev : (Multiset V → ℝ≥0∞) → Multiset V → ℝ≥0∞)
    (hc : ∀ x, Rep (fun h d => c h d x)) (hev : Rep ev) :
    ∀ (a : ℕ) (x : R), Rep (fun h d => Walk.val e s t (c h d) (ev h d) a x)
  | 0, _ => hev
  | a + 1, x => by
      have h1 := (hc x).const_mul (hs x)
      have h2 := (rep_val e s t hs ht c ev hc hev a (e x)).const_mul (ht x)
      simpa only [Walk.val] using h1.add h2

/-! ### One more future pair pays a small uniform coin -/

section Step

variable [Fintype V] [Nonempty V]

/-- The average of a function over one more disclosed uniform view. -/
noncomputable def avgT (h : Multiset V → ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ :=
  freshAvg Finset.univ fun v => h (d + {v})

theorem le_avgT {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (d : Multiset V) : h d ≤ avgT h d := by
  unfold avgT
  calc h d = freshAvg Finset.univ fun _ : V => h d := (freshAvg_const _ Finset.univ_nonempty _).symm
    _ ≤ _ := freshAvg_mono _ fun v _ => hmono _ _ (Multiset.le_add_right _ _)

/-- Gains grow with the base, on average. -/
theorem add_avgGain_le {h : Multiset V → ℝ≥0∞} (hmono : Monotone' h) (hsuper : Supermodular h)
    (hfin : ∀ D, h D ≠ ⊤) (d D : Multiset V) (hle : d ≤ D) : h D + (avgT h d - h d) ≤ avgT h D := by
  have hg : avgT h d - h d = freshAvg Finset.univ (gain h d) := by
    have : avgT h d = h d + freshAvg Finset.univ (gain h d) := by
      unfold avgT
      rw [← freshAvg_const (Finset.univ : Finset V) Finset.univ_nonempty (h d), ← freshAvg_add]
      congr 1
      funext v
      exact add_gain h hmono d v
    rw [this, ENNReal.add_sub_cancel_left (hfin d)]
  rw [hg]
  unfold avgT
  calc h D + freshAvg Finset.univ (gain h d)
      = freshAvg Finset.univ fun v => h D + gain h d v := by
        rw [freshAvg_add, freshAvg_const _ Finset.univ_nonempty]
    _ ≤ _ := freshAvg_mono _ fun v _ => gain_le_of_le h hmono hsuper hfin d D hle v

/-- A convex mixture with more weight on the larger value is larger. -/
theorem convex_weight_le {a b r r' : ℝ≥0∞} (hab : a ≤ b) (hr : r ≤ r') (hr' : r' ≤ 1) :
    (1 - r) * a + r * b ≤ (1 - r') * a + r' * b := by
  obtain ⟨δ, rfl⟩ := exists_add_of_le hr
  have hrt : r ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_self_add hr')
  have h1 : 1 - r = (1 - (r + δ)) + δ := by
    rw [← tsub_tsub, tsub_add_cancel_of_le]
    exact ENNReal.le_sub_of_add_le_left hrt hr'
  rw [h1]
  calc ((1 - (r + δ)) + δ) * a + r * b = (1 - (r + δ)) * a + r * b + δ * a := by ring
    _ ≤ (1 - (r + δ)) * a + r * b + δ * b := by gcongr
    _ = _ := by ring

/-- **One more future pair.** A base function mixed with weight `r` towards one more uniform
disclosure is paid by one more future pair when `r ≤ land · w`. -/
theorem creations_avg_step [DecidableEq V] {land w r : ℝ≥0∞} (hland : land ≤ 1) (hw : w ≤ 1) (hr : r ≤ land * w)
    {h : Multiset V → ℝ≥0∞} (hf : Monotone' h ∧ Supermodular h ∧ ∀ D, h D ≠ ⊤) (n : ℕ) (d : Multiset V)
    (k : ℕ) (I : List V) :
    creations Finset.univ land
        (fun J => virtualOnce Finset.univ w (fun D => (1 - r) * h D + r * avgT h D) n J d) k I ≤
      creations Finset.univ land (fun J => virtualOnce Finset.univ w h n J d) (k + 1) I := by
  set G : List V → ℝ≥0∞ := fun J => virtualOnce Finset.univ w h n J d with hG
  have hperm : ∀ a b : List V, a.Perm b → G a = G b := fun _ _ hab => virtualOnce_perm n hab d
  have hlw : land * w ≤ 1 := le_trans (mul_le_mul' hland hw) (by rw [one_mul])
  have hpoint : ∀ J, virtualOnce Finset.univ w (fun D => (1 - r) * h D + r * avgT h D) n J d ≤
      (1 - land) * G J + land * freshAvg Finset.univ (fun v => G ([v] ++ J)) := by
    intro J
    have hR := rep_virtualOnce (Finset.univ : Finset V) hw n J
    have hprops := virtualOnce_props (U := (Finset.univ : Finset V)) Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n J
    set X := virtualOnce Finset.univ w h n J with hX
    have h1 : virtualOnce Finset.univ w (fun D => (1 - r) * h D + r * avgT h D) n J d =
        (1 - r) * X d + r * avgT X d := by
      have := hR.map_add (fun D => (1 - r) * h D) (fun D => r * avgT h D) d
      rw [this, hR.map_const_mul, hR.map_const_mul]
      congr 2
      unfold avgT
      rw [hR.map_freshAvg]
      congr 1
      funext v
      exact hR.map_translate h {v} d
    have h2 : ∀ v, G ([v] ++ J) = w * X (d + {v}) + (1 - w) * X d := by
      intro v
      simp only [hG, hX, virtualOnce, List.singleton_append, itemCoins_cons, slotValue]
    have h3 : (1 - land) * G J + land * freshAvg Finset.univ (fun v => G ([v] ++ J)) =
        (1 - land * w) * X d + land * w * avgT X d := by
      simp only [h2]
      rw [freshAvg_add, freshAvg_mul, freshAvg_mul, freshAvg_const _ Finset.univ_nonempty]
      have hXd : X d ≠ ⊤ := hprops.2.2 d
      have hw' : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw
      have hl' : land ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hland
      have hsplit : (1 - land * w) = (1 - land) + land * (1 - w) := by
        rw [ENNReal.mul_sub (fun _ _ => hl'), mul_one]
        have h5 : land * w ≤ land := by simpa using mul_le_mul_right hw land
        rw [← AddLECancellable.add_tsub_assoc_of_le (ENNReal.cancel_of_ne (ENNReal.mul_ne_top hl' hw')) h5,
          tsub_add_cancel_of_le hland]
      rw [hsplit]
      unfold avgT
      ring
    rw [h1, h3]
    exact convex_weight_le (le_avgT hprops.1 d) hr hlw
  calc _ ≤ creations Finset.univ land
        (fun J => (1 - land) * G J + land * freshAvg Finset.univ (fun v => G ([v] ++ J))) k I :=
        creations_mono hpoint k I
    _ = (1 - land) * creations Finset.univ land G k I +
          land * freshAvg Finset.univ (fun v => creations Finset.univ land G k (v :: I)) := by
        have hpre : ∀ v, creations Finset.univ land (fun J => G ([v] ++ J)) k I =
            creations Finset.univ land G k (v :: I) := fun v => (creations_prepend hperm [v] k I).symm
        rw [creations_add, creations_const_mul, creations_const_mul, creations_freshAvg]
        simp only [hpre]
    _ = _ := rfl

end Step

end SphincsFors.Security.Domination
