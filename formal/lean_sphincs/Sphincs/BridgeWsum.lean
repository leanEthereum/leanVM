import Sphincs.BridgeGameF

/-! **Recorded contact weights with coefficients.** The sum `Σ_f [recorded] g(f) cw(f)` over forest
steps, for any coefficients `g`, keeps its mean through an exposure and through every ordinary query,
except that a fresh forest step query at an unexposed read coordinate adds at most `2^-128` times
its coefficient. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

namespace Ctx

variable (K : Ctx)

/-- **Recorded contact weights with coefficients.** -/
noncomputable def wsum (g : FIn → ℝ≥0∞) (s : St) : ℝ≥0∞ := ∑ f, if Recd s f then g f * K.cw s f else 0

theorem wsum_expose_mean (g : FIn → ℝ≥0∞) (s : St) (c : Coordinate) (hc : s.known c = none) :
    ∑ v : Digest, ν * K.wsum g (s.expose c v) = K.wsum g s := by
  unfold wsum
  have hR : ∀ v f, Recd (s.expose c v) f ↔ Recd s f := fun _ _ => Iff.rfl
  simp only [hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hr : Recd s f
  · simp only [ite_eq_left hr]
    calc ∑ v, ν * (g f * K.cw (s.expose c v) f) = g f * ∑ v, ν * K.cw (s.expose c v) f := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
      _ = g f * K.cw s f := by rw [K.mean_cw s c hc f]
  · simp only [ite_eq_right hr, mul_zero, Finset.sum_const_zero]

theorem wsum_sample_le (g : FIn → ℝ≥0∞) (s : St) (c : Coordinate) :
    ∑' r, Pr{let x ← sampleCoordinate c s}[x = r] * K.wsum g r.2 ≤ K.wsum g s := by
  cases hc : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hc, OracleComp.tsum_prEvent_pure_mul]
  | none =>
      rw [sampleCoordinate_unknown c s hc, OracleComp.tsum_prEvent_map_mul]
      simp only [probOutput_digest]
      rw [tsum_fintype, K.wsum_expose_mean g s c hc]

theorem cw_store_new {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none) (hi : K.initial x = none)
    {f : FIn} (hxf : x = f.input K.p) : K.cw (s.store x u) f = cwNew s f (truncateHash u) := by
  have hnfe : ¬K.FE s f := fun ⟨w, hw⟩ => by
    have h1 := hw.1
    rw [← hxf, hx] at h1
    cases h1
  have hnfc : ¬K.FC s f := fun ⟨w, _, hw, _⟩ => hnfe ⟨w, hw⟩
  have hnlat : ¬K.Lat s f := fun hl => hnfe hl.1
  have hFC : K.FC (s.store x u) f ↔ ∃ w, s.known f.outC = some w ∧ truncateHash u = w := by
    rw [K.fc_store u hx hi f]
    simp only [hnfc, false_or]
    exact ⟨fun h => h.2, fun h => ⟨hxf, h⟩⟩
  have hLat : K.Lat (s.store x u) f ↔ s.known f.outC = none := by
    rw [K.lat_store u hx hi f]
    simp only [hnlat, false_or]
    exact ⟨fun h => h.2, fun h => ⟨hxf, h⟩⟩
  unfold cw cwNew
  cases hk : s.known f.outC with
  | none =>
      have h1 : ¬K.FC (s.store x u) f := fun h => by
        obtain ⟨w, hw, _⟩ := hFC.1 h
        rw [hk] at hw
        cases hw
      rw [ite_eq_right h1, ite_eq_left (hLat.2 hk), ite_eq_left rfl]
  | some w =>
      have h2 : ¬K.Lat (s.store x u) f := fun h => by
        have := hLat.1 h
        rw [hk] at this
        cases this
      simp only [reduceCtorEq, ite_false, Option.some.injEq]
      by_cases ht : w = truncateHash u
      · rw [ite_eq_left (hFC.2 ⟨w, hk, ht.symm⟩), ite_eq_left ht]
      · rw [ite_eq_right (fun h => by
          obtain ⟨w', hw', ht'⟩ := hFC.1 h
          rw [hk] at hw'
          cases hw'
          exact ht ht'.symm), ite_eq_right h2, ite_eq_right ht]

theorem cw_store_other {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none) (hi : K.initial x = none)
    {f : FIn} (hxf : x ≠ f.input K.p) : K.cw (s.store x u) f = K.cw s f := by
  refine K.cw_congr1 f (fun w => ?_) rfl
  rw [K.fr_store u hx hi]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · exact absurd h.symm hxf
  · exact Or.inl

theorem wsum_store_other (g : FIn → ℝ≥0∞) {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none)
    (hi : K.initial x = none) (hF : ∀ f : FIn, x ≠ f.input K.p) : K.wsum g (s.store x u) = K.wsum g s := by
  unfold wsum
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [K.cw_store_other u hx hi (hF f)]
  rfl

theorem wsum_store_new (g : FIn → ℝ≥0∞) {s : St} {x : HashInput} (u : HashOutput) (hx : s.cache x = none)
    (hi : K.initial x = none) {f0 : FIn} (hxf : x = f0.input K.p) :
    K.wsum g (s.store x u) = K.wsum g s + (if Recd s f0 then g f0 * cwNew s f0 (truncateHash u) else 0) := by
  unfold wsum
  have h := sum_single (fun f => if Recd s f then g f * K.cw s f else 0)
    (fun f => if Recd (s.store x u) f then g f * K.cw (s.store x u) f else 0) f0 (fun f hf => by
      have hne : x ≠ f.input K.p := fun h => hf (fchain_inj (hxf.symm.trans h)).symm
      rw [K.cw_store_other u hx hi hne]
      rfl) (by
      have hnfe : ¬K.FE s f0 := fun ⟨w, hw⟩ => by
        have h1 := hw.1
        rw [← hxf, hx] at h1
        cases h1
      simp only [K.cw_of_not_fe hnfe, mul_zero, ite_self])
  rw [h, K.cw_store_new u hx hi hxf]
  rfl

theorem mean_new (g : FIn → ℝ≥0∞) (s : St) (f0 : FIn) :
    ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] *
        (if Recd s f0 then g f0 * cwNew s f0 (truncateHash u) else 0) = if Recd s f0 then ν * g f0 else 0 := by
  by_cases hr : Recd s f0
  · simp only [ite_eq_left hr]
    rw [mean_trunc (fun t => g f0 * cwNew s f0 t)]
    have := meanD_cwNew s f0 (g f0)
    simp only [mul_comm (g f0)] at this ⊢
    exact this
  · simp only [ite_eq_right hr, mul_zero, tsum_zero]

theorem wsum_record (g : FIn → ℝ≥0∞) (s : St) (g0 : Coordinate × Digest)
    (h : ∀ f : FIn, (f.inC, f.v) = g0 → K.cw s f ≠ 0 → g0 ∈ s.guesses) :
    K.wsum g (s.record g0) = K.wsum g s := by
  unfold wsum
  refine Finset.sum_congr rfl fun f _ => ?_
  have hcw : K.cw (s.record g0) f = K.cw s f := K.cw_congr1 f (fun _ => Iff.rfl) rfl
  rw [hcw]
  by_cases hf : (f.inC, f.v) = g0
  · by_cases hc : K.cw s f = 0
    · simp [hc]
    · have hmem := h f hf hc
      have h1 : Recd (s.record g0) f := List.mem_cons.2 (Or.inl hf)
      have h2 : Recd s f := by unfold Recd; rw [hf]; exact hmem
      rw [ite_eq_left h1, ite_eq_left h2]
  · have hiff : Recd (s.record g0) f ↔ Recd s f := by
      unfold Recd
      simp only [DebtState.record, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact absurd h hf
        · exact h
      · exact Or.inr
    simp only [hiff]

/-! ### One ordinary query -/

section Model

variable (M : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : M.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : M.incoming = Address.inputCoordinate)

include hMp hMi in
/-- A parsed query reading the coordinate of a forest step with its payload is that step's input. -/
theorem input_of_guess {x : HashInput} {a : Address} {v : Digest} (hp : M.parse x = some (a, v)) {f : FIn}
    (hf : (M.incoming a, v) = (f.inC, f.v)) : x = f.input K.p := by
  rw [hMp] at hp
  obtain ⟨hx, -⟩ := (parse_some_iff _ _ x (a, v)).1 hp
  rw [hMi] at hf
  cases a with
  | chain lay tree leaf chainIdx step =>
      simp only [Address.inputCoordinate, FIn.inC, Prod.mk.injEq] at hf
      cases hf.1
  | fchain index c sp j a' i t =>
      rw [fin_eq_of_inC hf, hx]
      rfl

include hMp hMi in
/-- A fresh forest step input carries no guess record. -/
theorem not_recd_of_fresh {s : St} (hgc : ForsPotential.GuessCached M s) {f : FIn}
    (hx : s.cache (f.input K.p) = none) : ¬Recd s f := by
  intro hr
  obtain ⟨x', a, v, hp, hg, hc⟩ := hgc _ hr
  have := K.input_of_guess M hMp hMi hp hg.symm
  rw [this, hx] at hc
  exact hc rfl

include hMp hMi in
/-- **One ordinary query.** The recorded contact weights keep their mean, except that a fresh forest
step query at an unexposed read coordinate adds `2^-128` times its coefficient. -/
theorem wsum_ordinary {s : St} (hinv : K.Inv s) (hgc : ForsPotential.GuessCached M s) (x : HashInput)
    (g : FIn → ℝ≥0∞) (C : ℝ≥0∞) (hC : ∀ f : FIn, x = f.input K.p → s.known f.inC = none → g f ≤ C) :
    ∑' r, Pr{let y ← ordinaryStep M x s.known s}[y = r] * K.wsum g r.2 ≤
      K.wsum g s + ν * C * (if IsFchainIn K.p x then 1 else 0) := by
  -- a fresh read without a new record keeps the mean
  have hread : ∀ s1 : St, s1.cache = s.cache → s1.known = s.known → s1.guesses = s.guesses →
      ∑' r, Pr{let y ← readOutside x s1}[y = r] * K.wsum g r.2 ≤ K.wsum g s := by
    intro s1 hcache hknown hguess
    have hs1 : s1 = s := by
      cases s1; cases s
      simp only at hcache hknown hguess
      rw [hcache, hknown, hguess]
    subst hs1
    cases hc : s1.cache x with
    | some u =>
        rw [readOutside_cached x s1 u hc, OracleComp.tsum_prEvent_pure_mul]
    | none =>
        rw [readOutside_fresh x s1 hc, OracleComp.tsum_prEvent_map_mul]
        have hi := initial_none_of_fresh K.initial s1 hinv.prepared x hc
        by_cases hF : ∃ f0 : FIn, x = f0.input K.p
        · obtain ⟨f0, hxf⟩ := hF
          have hnr : ¬Recd s1 f0 := K.not_recd_of_fresh M hMp hMi hgc (by rw [← hxf]; exact hc)
          simp only [K.wsum_store_new g _ hc hi hxf, ite_eq_right hnr, add_zero]
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
        · push Not at hF
          simp only [K.wsum_store_other g _ hc hi hF]
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)
  cases hp : M.parse x with
  | none =>
      simp only [ordinaryStep, hp]
      exact le_trans (hread s rfl rfl rfl) le_self_add
  | some q =>
      obtain ⟨a, v⟩ := q
      cases hk : s.known (M.incoming a) with
      | none =>
          simp only [ordinaryStep, hp, hk]
          set g0 : Coordinate × Digest := (M.incoming a, v) with hg0
          have hrec : ∀ f : FIn, (f.inC, f.v) = g0 → x = f.input K.p := fun f hf =>
            K.input_of_guess M hMp hMi hp hf.symm
          cases hc : s.cache x with
          | some u =>
              have hc' : (s.record g0).cache x = some u := hc
              rw [readOutside_cached x _ u hc', OracleComp.tsum_prEvent_pure_mul]
              refine le_trans (le_of_eq (K.wsum_record g s g0 fun f hf hcw => ?_)) le_self_add
              have hfe : K.FE s f := by
                by_contra hn
                exact hcw (K.cw_of_not_fe hn)
              obtain ⟨w, hw⟩ := hfe
              have hxf := hrec f hf
              rw [← hxf] at hw
              have hq : HiddenGraph.parse K.p (candidateActive K.p) x = some (a, v) := by rw [← hMp, hp]
              have hk' : s.known (a, v).1.inputCoordinate = none := by rw [← hMi]; exact hk
              have := hinv.guessed x w (a, v) hw hq hk'
              rw [hg0, hMi]
              exact this
          | none =>
              have hc' : (s.record g0).cache x = none := hc
              rw [readOutside_fresh x _ hc', OracleComp.tsum_prEvent_map_mul]
              have hi := initial_none_of_fresh K.initial s hinv.prepared x hc
              have hrec0 : K.wsum g (s.record g0) = K.wsum g s := K.wsum_record g s g0 fun f hf hcw => by
                exfalso
                have hnfe : ¬K.FE s f := fun ⟨w, hw⟩ => by
                  have h1 := hw.1
                  rw [← hrec f hf, hc] at h1
                  cases h1
                exact hcw (K.cw_of_not_fe hnfe)
              by_cases hF : ∃ f0 : FIn, x = f0.input K.p
              · obtain ⟨f0, hxf⟩ := hF
                simp only [K.wsum_store_new g _ hc' hi hxf, hrec0, mul_add]
                rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, Ctx.mean_new g (s.record g0) f0]
                have hIs : IsFchainIn K.p x := ⟨f0, hxf⟩
                rw [ite_eq_left hIs, mul_one]
                refine add_le_add (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) ?_
                split_ifs
                · refine mul_le_mul_right (hC f0 hxf ?_) _
                  -- the read coordinate of the new step is the guessed one
                  have hp' : M.parse (f0.input K.p) = some (a, v) := by rw [← hxf]; exact hp
                  rw [hMp] at hp'
                  obtain ⟨hxe, -⟩ := (parse_some_iff _ _ _ (a, v)).1 hp'
                  have hfe : f0.input K.p = HiddenGraph.input K.p
                      (Address.fchain f0.index f0.c f0.s f0.j f0.a f0.i f0.t, f0.v) := rfl
                  have hav := input_injective K.p (hxe.symm.trans hfe)
                  rw [hMi] at hk
                  rw [Prod.mk.injEq] at hav
                  rw [hav.1] at hk
                  exact hk
                · exact bot_le
              · push Not at hF
                simp only [K.wsum_store_other g _ hc' hi hF, hrec0]
                rw [ENNReal.tsum_mul_right]
                exact le_trans (mul_le_of_le_one_left' (OracleComp.tsum_prEvent_le_one _)) le_self_add
      | some canonical =>
          by_cases heq : v = canonical
          · simp only [ordinaryStep, hp, hk, ite_eq_left heq]
            rw [OracleComp.tsum_prEvent_map_mul]
            exact le_trans (K.wsum_sample_le g s _) le_self_add
          · simp only [ordinaryStep, hp, hk, ite_eq_right heq]
            exact le_trans (hread s rfl rfl rfl) le_self_add

end Model

end Ctx

end Sphincs.Security.PotentialA
