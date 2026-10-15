import Sphincs.BridgePotentialA2

/-! The invariant of the linear potential, the steps that do not store a fresh answer (reveals,
canonical continuations, guesses at cached inputs, cached reads), and the closing arithmetic of
each input class under the numeric conditions. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- The numeric conditions on the plain rate `ρ`, for `x = total / 2^128`. -/
structure Numeric (ρ x : ℝ) : Prop where
  low : 3 / 2 ≤ ρ
  high : ρ ≤ 2
  enc : 1 + 4032 * (2 - ρ) * x ≤ ρ
  contact : 1 + 66 * x ≤ ρ
  small : 64 * x ≤ 1

theorem ν_eq_ofReal : ν = ENNReal.ofReal ((2 : ℝ) ^ 128)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp [ν]

theorem budget_ofReal (y : ℕ) : (y : ℝ≥0∞) * ν = ENNReal.ofReal ((y : ℝ) / 2 ^ 128) := by
  rw [ν_eq_ofReal, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), div_eq_mul_inv]

theorem budget_le_x {y total : ℕ} (hy : y ≤ total) :
    (y : ℝ≥0∞) * ν ≤ ENNReal.ofReal ((total : ℝ) / 2 ^ 128) := by
  rw [budget_ofReal]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by exact_mod_cast hy) (by positivity))

theorem payment_eq (ρ : ℝ) : ENNReal.ofReal (ρ / 2 ^ 128) = ν * ENNReal.ofReal ρ := by
  rw [ν_eq_ofReal, div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by positivity)]

theorem mul_ofReal_le {Y : ℝ≥0∞} {x c : ℝ} (hY : Y ≤ ENNReal.ofReal x) (hx : 0 ≤ x) (_hc : 0 ≤ c) :
    Y * ENNReal.ofReal c ≤ ENNReal.ofReal (x * c) := by
  rw [ENNReal.ofReal_mul hx]
  exact mul_le_mul_of_nonneg_right hY bot_le

section Arith

variable {ρ x : ℝ} (hN : Numeric ρ x) (hx : 0 ≤ x) {Y : ℝ≥0∞} (hY : Y ≤ ENNReal.ofReal x)
include hN hx hY

theorem arith_contact : 1 + Y * (ENNReal.ofReal (2 - ρ) + 64) ≤ ENNReal.ofReal ρ := by
  have h64 : ENNReal.ofReal (2 - ρ) + 64 = ENNReal.ofReal (66 - ρ) := by
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 by simp, ← ENNReal.ofReal_add (by linarith [hN.high]) (by norm_num)]
    ring_nf
  rw [h64]
  calc 1 + Y * ENNReal.ofReal (66 - ρ) ≤ ENNReal.ofReal 1 + ENNReal.ofReal (x * (66 - ρ)) :=
        add_le_add (by simp) (mul_ofReal_le hY hx (by linarith [hN.high]))
    _ = ENNReal.ofReal (1 + x * (66 - ρ)) := (ENNReal.ofReal_add (by norm_num)
        (mul_nonneg hx (by linarith [hN.high]))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hN.contact, hN.low])

theorem arith_pair : 1 + Y ≤ ENNReal.ofReal ρ := by
  calc 1 + Y ≤ ENNReal.ofReal 1 + ENNReal.ofReal x := add_le_add (by simp) hY
    _ = ENNReal.ofReal (1 + x) := (ENNReal.ofReal_add (by norm_num) hx).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [hN.contact])

theorem arith_small : 64 * Y ≤ 1 := by
  calc 64 * Y ≤ ENNReal.ofReal 64 * ENNReal.ofReal x := mul_le_mul_of_nonneg_left hY bot_le |>.trans_eq'
        (by simp)
    _ = ENNReal.ofReal (64 * x) := (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hN.small
    _ = 1 := by simp

theorem arith_enc : 1 + Y * (4032 * ENNReal.ofReal (2 - ρ)) ≤ ENNReal.ofReal ρ := by
  have h : (4032 : ℝ≥0∞) * ENNReal.ofReal (2 - ρ) = ENNReal.ofReal (4032 * (2 - ρ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h]
  calc 1 + Y * ENNReal.ofReal (4032 * (2 - ρ)) ≤ ENNReal.ofReal 1 + ENNReal.ofReal (x * (4032 * (2 - ρ))) :=
        add_le_add (by simp) (mul_ofReal_le hY hx (by linarith [hN.high]))
    _ = ENNReal.ofReal (1 + x * (4032 * (2 - ρ))) := (ENNReal.ofReal_add (by norm_num)
        (mul_nonneg hx (by linarith [hN.high]))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hN.enc])

end Arith

theorem one_le_ofReal {ρ : ℝ} (h : 1 ≤ ρ) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ρ := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h

theorem ofReal_le_two {ρ : ℝ} (h : ρ ≤ 2) : ENNReal.ofReal ρ ≤ 2 := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact ENNReal.ofReal_le_ofReal h

variable [Params]

namespace Ctx

variable (K : Ctx)

/-! ### The invariant -/

/-- Coordinates known from the start with fixed values: the chain values at and above the
prepared word of a landed leaf, and the tops of the forest chains. -/
def Anchor (c : Coordinate) : Prop :=
  AboveWord K.p K.R c ∨ ∃ index cc sp j a i, c = .fchain index cc sp j a i ⟨chainTop, by omega⟩

/-- **Invariant.** The prepared cache is kept, the anchors hold their values, and every fresh
parsed input whose incoming coordinate is still unexposed carries its guess record. -/
structure Inv (s : St) : Prop where
  prepared : Prepared K.initial s
  anchored : ∀ c, K.Anchor c → s.known c = some (K.F c)
  guessed : ∀ x u q, K.Fr s x u → HiddenGraph.parse K.p (candidateActive K.p) x = some q →
    s.known q.1.inputCoordinate = none → (q.1.inputCoordinate, q.2) ∈ s.guesses

variable {K} in
theorem Inv.expose {s : St} (h : K.Inv s) (c : Coordinate) (v : Digest) (hc : s.known c = none) :
    K.Inv (s.expose c v) where
  prepared := h.prepared
  anchored c' hc' := by
    have hne : c' ≠ c := by
      rintro rfl
      rw [h.anchored c' hc'] at hc
      cases hc
    have hk : (s.expose c v).known c' = s.known c' := by simp [DebtState.expose, hne]
    rw [hk]
    exact h.anchored c' hc'
  guessed x u q hfr hp hk := by
    refine h.guessed x u q hfr hp ?_
    by_cases hne : q.1.inputCoordinate = c
    · rw [hne]
      exact hc
    · have hk' : (s.expose c v).known q.1.inputCoordinate = s.known q.1.inputCoordinate := by
        simp [DebtState.expose, hne]
      rw [← hk']
      exact hk

variable {K} in
theorem Inv.record {s : St} (h : K.Inv s) (g : Coordinate × Digest) : K.Inv (s.record g) where
  prepared := h.prepared
  anchored := h.anchored
  guessed x u q hfr hp hk := List.mem_cons_of_mem _ (h.guessed x u q hfr hp hk)

variable {K} in
theorem Inv.store {s : St} (h : K.Inv s) (x : HashInput) (u : HashOutput) (hx : s.cache x = none)
    (hguess : ∀ q, HiddenGraph.parse K.p (candidateActive K.p) x = some q →
      s.known q.1.inputCoordinate = none → (q.1.inputCoordinate, q.2) ∈ s.guesses) :
    K.Inv (s.store x u) where
  prepared := prepared_store K.initial s h.prepared x u hx
  anchored := h.anchored
  guessed y w q hfr hp hk := by
    have hi := initial_none_of_fresh K.initial s h.prepared x hx
    rcases (K.fr_store u hx hi).1 hfr with hfr | ⟨rfl, -⟩
    · exact h.guessed y w q hfr hp hk
    · exact hguess q hp hk

/-! ### Steps without a fresh answer -/

theorem pot_succ (y : ℕ) (s : St) : K.pot (y + 1) s = K.pot y s + ν * K.rate s := by
  unfold pot
  push_cast
  ring

theorem pot_mono {y y' : ℕ} (h : y ≤ y') (s : St) : K.pot y s ≤ K.pot y' s := by
  unfold pot
  gcongr

theorem vrate_ge (hρ : K.ρ ≤ 2) (s : St) : ENNReal.ofReal K.ρ ≤ K.vrate s := by
  unfold vrate
  split_ifs
  · exact ofReal_le_two hρ
  · exact le_rfl

theorem vrate_le_rate (s : St) : K.vrate s ≤ K.rate s := by
  unfold rate
  rw [add_assoc]
  exact le_self_add

/-- A cached read: the step pays the digest baseline from the rate. -/
theorem pot_same (hρ : K.ρ ≤ 2) (_hρ1 : 1 ≤ K.ρ) (y : ℕ) (s : St) (d : ℝ≥0∞) (hd : d ≤ 1) :
    K.pot y s + ν * (d * ENNReal.ofReal K.ρ) ≤ K.pot (y + 1) s := by
  rw [K.pot_succ]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ bot_le)
  calc d * ENNReal.ofReal K.ρ ≤ 1 * ENNReal.ofReal K.ρ := mul_le_mul_of_nonneg_right hd bot_le
    _ = ENNReal.ofReal K.ρ := one_mul _
    _ ≤ _ := (K.vrate_ge hρ s).trans (K.vrate_le_rate s)

theorem bad_expose (s : St) (c : Coordinate) (v : Digest) (hc : s.known c = none) :
    K.Bad (s.expose c v) → K.Bad s ∨ v ∈ debts K.tg K.initial s c := by
  rintro (hr | hw)
  · rcases (realized_expose K.tg K.initial s c v hc).1 hr with hr | hv
    · exact Or.inl (Or.inl hr)
    · exact Or.inr hv
  · exact Or.inl (Or.inr hw)

theorem sum_nu_digest : ∑ _v : Digest, ν = 1 := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_digest_ennreal, mul_comm, ν_mul_space]

theorem sum_nu_ite (t : Digest) : ∑ v : Digest, ν * (if t = v then (1 : ℝ≥0∞) else 0) = ν := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ t, if_pos (Finset.mem_univ _)]

theorem cw_congr1 {s s' : St} (f : FIn) (hfr : ∀ u, K.Fr s' (f.input K.p) u ↔ K.Fr s (f.input K.p) u)
    (hk : s'.known f.outC = s.known f.outC) : K.cw s' f = K.cw s f := by
  have hFC : K.FC s' f ↔ K.FC s f := by simp only [FC, hfr, hk]
  have hLat : K.Lat s' f ↔ K.Lat s f := by simp only [Lat, FE, hfr, hk]
  simp only [cw, hFC, hLat]

theorem cw_expose_ne (s : St) (c : Coordinate) (v : Digest) (f : FIn) (hf : f.outC ≠ c) :
    K.cw (s.expose c v) f = K.cw s f :=
  K.cw_congr1 f (fun _ => Iff.rfl) (by simp [DebtState.expose, hf])

/-- **Exposure keeps a contact weight in the mean.** -/
theorem mean_cw (s : St) (c : Coordinate) (hc : s.known c = none) (f : FIn) :
    ∑ v : Digest, ν * K.cw (s.expose c v) f = K.cw s f := by
  by_cases hf : f.outC = c
  · have hFC : ¬K.FC s f := fun ⟨_, w, _, hw, _⟩ => by rw [hf, hc] at hw; cases hw
    have hkv : ∀ v, (s.expose c v).known f.outC = some v := fun v => by
      rw [hf]
      simp [DebtState.expose]
    have hLat' : ∀ v, ¬K.Lat (s.expose c v) f := fun v hl => by
      have h3 := hl.2
      rw [hkv v] at h3
      cases h3
    by_cases hfe : K.FE s f
    · obtain ⟨u, hu⟩ := hfe
      have hLat : K.Lat s f := ⟨⟨u, hu⟩, by rw [hf, hc]⟩
      have hcw : K.cw s f = ν := by simp only [cw, hFC, hLat, if_false, if_true]
      have hcw' : ∀ v, K.cw (s.expose c v) f = if truncateHash u = v then 1 else 0 := fun v => by
        have hFC' : K.FC (s.expose c v) f ↔ truncateHash u = v := by
          constructor
          · rintro ⟨u', w, hu', hw, ht⟩
            have hfr : K.Fr s (f.input K.p) u' := hu'
            have heq : u' = u := by
              have h1 := hfr.1
              have h2 := hu.1
              rw [h1] at h2
              exact Option.some.inj h2
            rw [hkv v] at hw
            cases hw
            rw [← heq]
            exact ht
          · intro ht
            exact ⟨u, v, hu, hkv v, ht⟩
        by_cases ht : truncateHash u = v
        · simp only [cw, hFC'.2 ht, if_true, ht]
        · simp only [cw, (not_congr hFC').2 ht, hLat' v, if_false, ht]
      rw [hcw]
      simp only [hcw']
      exact sum_nu_ite _
    · have h0 : K.cw s f = 0 := by
        have h2 : ¬K.Lat s f := fun hl => hfe hl.1
        simp only [cw, hFC, h2, if_false]
      have h0' : ∀ v, K.cw (s.expose c v) f = 0 := fun v => by
        have h1 : ¬K.FC (s.expose c v) f := fun ⟨u, w, hu, _⟩ => hfe ⟨u, hu⟩
        simp only [cw, h1, hLat' v, if_false]
      simp only [h0, h0', mul_zero, Finset.sum_const_zero]
  · simp only [K.cw_expose_ne s c _ f hf]
    rw [← Finset.sum_mul, sum_nu_digest, one_mul]

/-- Exposure keeps the product of the weights of steps writing different coordinates in the mean. -/
theorem mean_cw2 (s : St) (c : Coordinate) (hc : s.known c = none) (f g : FIn) (hfg : f.outC ≠ g.outC) :
    ∑ v : Digest, ν * (K.cw (s.expose c v) f * K.cw (s.expose c v) g) = K.cw s f * K.cw s g := by
  by_cases hg : g.outC = c
  · have hf : f.outC ≠ c := fun h => hfg (h.trans hg.symm)
    simp only [K.cw_expose_ne s c _ f hf]
    calc ∑ v : Digest, ν * (K.cw s f * K.cw (s.expose c v) g) = K.cw s f * ∑ v : Digest, ν * K.cw (s.expose c v) g := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = _ := by rw [K.mean_cw s c hc g]
  · simp only [K.cw_expose_ne s c _ g hg]
    calc ∑ v : Digest, ν * (K.cw (s.expose c v) f * K.cw s g) = (∑ v : Digest, ν * K.cw (s.expose c v) f) * K.cw s g := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = _ := by rw [K.mean_cw s c hc f]

theorem mean_ng (s : St) (c : Coordinate) (hc : s.known c = none) :
    ∑ v : Digest, ν * K.ng (s.expose c v) = K.ng s := by
  unfold ng
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hr : Recd s f
  · have h' : ∀ v, Recd (s.expose c v) f := fun _ => hr
    simp only [h', hr, if_true, mul_zero, Finset.sum_const_zero]
  · have h' : ∀ v, ¬Recd (s.expose c v) f := fun _ => hr
    simp only [h', hr, if_false]
    exact K.mean_cw s c hc f

theorem mean_kf (s : St) (c : Coordinate) (hc : s.known c = none) :
    ∑ v : Digest, ν * K.kf (s.expose c v) = K.kf s := by
  unfold kf
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hr : Recd s f
  · have h' : ∀ v, Recd (s.expose c v) f := fun _ => hr
    simp only [h', hr, if_true]
    exact K.mean_cw s c hc f
  · have h' : ∀ v, ¬Recd (s.expose c v) f := fun _ => hr
    simp only [h', hr, if_false, mul_zero, Finset.sum_const_zero]

theorem mean_pp (s : St) (c : Coordinate) (hc : s.known c = none) :
    ∑ v : Digest, ν * K.pp (s.expose c v) = K.pp s := by
  unfold pp
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases hr : Recd s f ∧ Recd s g ∧ f.Rel g
  · have h' : ∀ v, Recd (s.expose c v) f ∧ Recd (s.expose c v) g ∧ f.Rel g := fun _ => hr
    rw [if_pos hr]
    rw [Finset.sum_congr rfl fun v _ => by rw [if_pos (h' v)]]
    exact K.mean_cw2 s c hc f g (FIn.outC_ne_of_rel hr.2.2)
  · have h' : ∀ v, ¬(Recd (s.expose c v) f ∧ Recd (s.expose c v) g ∧ f.Rel g) := fun _ => hr
    rw [if_neg hr]
    rw [Finset.sum_congr rfl fun v _ => by rw [if_neg (h' v), mul_zero]]
    exact Finset.sum_const_zero

/-- **Reveal.** Sampling an unexposed coordinate settles its debts with exactly their share, and
keeps every contact weight in the mean. -/
theorem pot_expose_mean (y : ℕ) (s : St) (c : Coordinate) (hc : s.known c = none) :
    ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * K.pot y (s.expose c v) ≤ K.pot y s := by
  set E := ((debts K.tg K.initial s c).encard : ℝ≥0∞) * ν with hE
  have hlhs : ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * K.pot y (s.expose c v) =
      ∑ v : Digest, ν * K.pot y (s.expose c v) := by
    rw [tsum_fintype]
    exact Finset.sum_congr rfl fun v _ => by rw [probOutput_digest]
  rw [hlhs]
  have hUA : ∀ v, K.UAset (s.expose c v) = K.UAset s := fun _ => rfl
  have hV : ∀ v, K.vrate (s.expose c v) = K.vrate s := fun _ => rfl
  have hCC : ∀ v, K.contactCount (s.expose c v) = K.contactCount s := fun _ => rfl
  have hpoint : ∀ v, K.pot y (s.expose c v) ≤
      (K.done s + if v ∈ debts K.tg K.initial s c then 1 else 0) + K.pend (s.expose c v) +
        K.latent (s.expose c v) + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
        (y : ℝ≥0∞) * ν * (K.vrate s + 64 * K.contactCount s) + (y : ℝ≥0∞) * ν * K.kf (s.expose c v) := by
    intro v
    have hD := K.done_le (s := s) (s' := s.expose c v) (v ∈ debts K.tg K.initial s c) (K.bad_expose s c v hc)
    have hD' : K.done (s.expose c v) ≤ K.done s + if v ∈ debts K.tg K.initial s c then 1 else 0 :=
      hD.trans (add_le_add le_rfl (by split_ifs <;> simp_all))
    unfold pot rate
    rw [hUA, hV, hCC]
    calc K.done (s.expose c v) + K.pend (s.expose c v) + K.latent (s.expose c v) +
          ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
          (y : ℝ≥0∞) * ν * (K.vrate s + 64 * K.contactCount s + K.kf (s.expose c v))
        ≤ (K.done s + if v ∈ debts K.tg K.initial s c then 1 else 0) + K.pend (s.expose c v) +
          K.latent (s.expose c v) + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
          (y : ℝ≥0∞) * ν * (K.vrate s + 64 * K.contactCount s + K.kf (s.expose c v)) :=
          add_le_add (add_le_add (add_le_add (add_le_add hD' le_rfl) le_rfl) le_rfl) le_rfl
      _ = _ := by ring
  have hP : ∀ v, K.pend (s.expose c v) + E = K.pend s := fun v => (K.pend_expose s c v hc).symm
  have hind : ∑ v : Digest, ν * (if v ∈ debts K.tg K.initial s c then (1 : ℝ≥0∞) else 0) = E := by
    rw [← Finset.mul_sum]
    have := meanD_ite (fun v => v ∈ debts K.tg K.initial s c) (1 : ℝ≥0∞)
    rw [meanD] at this
    rw [this, mul_one, hE, mul_comm]
    rfl
  have hconst : ∀ a : ℝ≥0∞, ∑ _v : Digest, ν * a = a := fun a => by
    rw [← Finset.sum_mul, sum_nu_digest, one_mul]
  have hpend : ∑ v : Digest, ν * K.pend (s.expose c v) + E = K.pend s := by
    calc ∑ v : Digest, ν * K.pend (s.expose c v) + E = ∑ v : Digest, ν * (K.pend (s.expose c v) + E) := by
          rw [Finset.sum_congr rfl fun v _ => mul_add ν _ E, Finset.sum_add_distrib, hconst]
      _ = ∑ v : Digest, ν * K.pend s := Finset.sum_congr rfl fun v _ => by rw [hP v]
      _ = _ := hconst _
  have hdone : ∑ v : Digest, ν * (K.done s + if v ∈ debts K.tg K.initial s c then 1 else 0) = K.done s + E := by
    rw [Finset.sum_congr rfl fun v _ => mul_add ν _ _, Finset.sum_add_distrib, hconst, hind]
  have hpp2 : ∑ v : Digest, ν * (K.pp (s.expose c v) / 2) = K.pp s / 2 := by
    calc ∑ v : Digest, ν * (K.pp (s.expose c v) / 2) = (∑ v : Digest, ν * K.pp (s.expose c v)) / 2 := by
          simp only [ENNReal.div_eq_inv_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = _ := by rw [K.mean_pp s c hc]
  have hlat : ∑ v : Digest, ν * K.latent (s.expose c v) = K.latent s := by
    unfold latent
    rw [Finset.sum_congr rfl fun v _ => mul_add ν _ _, Finset.sum_add_distrib, K.mean_ng s c hc, hpp2]
  have hkf : ∑ v : Digest, ν * ((y : ℝ≥0∞) * ν * K.kf (s.expose c v)) = (y : ℝ≥0∞) * ν * K.kf s := by
    rw [← K.mean_kf s c hc, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  calc ∑ v : Digest, ν * K.pot y (s.expose c v)
      ≤ ∑ v : Digest, ν * ((K.done s + if v ∈ debts K.tg K.initial s c then 1 else 0) + K.pend (s.expose c v) +
        K.latent (s.expose c v) + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
        (y : ℝ≥0∞) * ν * (K.vrate s + 64 * K.contactCount s) + (y : ℝ≥0∞) * ν * K.kf (s.expose c v)) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hpoint v) bot_le
    _ = ∑ v : Digest, ν * (K.done s + if v ∈ debts K.tg K.initial s c then 1 else 0) +
        ∑ v : Digest, ν * K.pend (s.expose c v) + ∑ v : Digest, ν * K.latent (s.expose c v) +
        ∑ _v : Digest, ν * (ν / 2 * ((K.UAset s).encard : ℝ≥0∞)) +
        ∑ _v : Digest, ν * ((y : ℝ≥0∞) * ν * (K.vrate s + 64 * K.contactCount s)) +
        ∑ v : Digest, ν * ((y : ℝ≥0∞) * ν * K.kf (s.expose c v)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ = K.pot y s := by
        rw [hdone, hlat, hkf, hconst, hconst]
        unfold pot rate
        rw [← hpend]
        ring

/-- A guess record that is no new record of a fresh forest step keeps the forest aggregates. -/
theorem forest_record (s : St) (g : Coordinate × Digest)
    (h : ∀ f : FIn, g = (f.inC, f.v) → K.FE s f → g ∈ s.guesses) :
    K.ng (s.record g) = K.ng s ∧ K.kf (s.record g) = K.kf s ∧ K.pp (s.record g) = K.pp s ∧
      K.latent (s.record g) = K.latent s := by
  have hcw : ∀ f, K.cw (s.record g) f = K.cw s f := fun f => K.cw_congr1 f (fun _ => Iff.rfl) rfl
  have hR : ∀ f, K.cw s f ≠ 0 → (Recd (s.record g) f ↔ Recd s f) := fun f hf => by
    have hfe : K.FE s f := by
      by_contra hne
      exact hf (K.cw_of_not_fe hne)
    simp only [Recd, DebtState.record, List.mem_cons]
    constructor
    · rintro (heq | hm)
      · rw [heq]
        exact h f heq.symm hfe
      · exact hm
    · exact Or.inr
  have hng : K.ng (s.record g) = K.ng s := by
    unfold ng
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hcw f]
    by_cases hf : K.cw s f = 0
    · simp [hf]
    · simp only [hR f hf]
  have hkf : K.kf (s.record g) = K.kf s := by
    unfold kf
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hcw f]
    by_cases hf : K.cw s f = 0
    · simp [hf]
    · simp only [hR f hf]
  have hpp : K.pp (s.record g) = K.pp s := by
    unfold pp
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun f' _ => ?_
    rw [hcw f, hcw f']
    by_cases hf : K.cw s f = 0
    · simp [hf]
    · by_cases hf' : K.cw s f' = 0
      · simp [hf']
      · simp only [hR f hf, hR f' hf']
  exact ⟨hng, hkf, hpp, by simp only [latent, hng, hpp]⟩

/-- **Guess record.** Recording a guess at an unexposed coordinate adds at most one debt. -/
theorem pot_record (y : ℕ) (s : St) (g : Coordinate × Digest) (hg : s.known g.1 = none)
    (hF : ∀ f : FIn, g = (f.inC, f.v) → K.FE s f → g ∈ s.guesses) :
    K.pot y (s.record g) ≤ K.pot y s + ν := by
  obtain ⟨-, hkf, -, hlat⟩ := K.forest_record s g hF
  have hD : K.done (s.record g) ≤ K.done s := by
    have := K.done_le (s := s) (s' := s.record g) False (by
      rintro (hr | hw)
      · exact Or.inl (Or.inl ((realized_record K.tg K.initial s g hg).1 hr))
      · exact Or.inl (Or.inr hw))
    simpa using this
  have hR : K.rate (s.record g) = K.rate s := by
    unfold rate
    rw [hkf]
    rfl
  have hUA : K.UAset (s.record g) = K.UAset s := rfl
  unfold pot
  rw [hR, hUA, hlat]
  calc K.done (s.record g) + K.pend (s.record g) + K.latent s + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
        (y : ℝ≥0∞) * ν * K.rate s
      ≤ K.done s + (K.pend s + ν) + K.latent s + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
          (y : ℝ≥0∞) * ν * K.rate s := by
        gcongr
        exact K.pend_record s g
    _ = _ := by ring

end Ctx

end Sphincs.Security.PotentialA
