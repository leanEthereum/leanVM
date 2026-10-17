import Sphincs.BridgePotentialA8
import Sphincs.BridgeFleafLinear

/-! The linear potential of the small-budget route pays, besides the digest baseline, a fixed
amount at every forest step query. A fresh forest step costs the potential at most
`(1 + Y + K_F) 2^-128` (a guess, a recorded contact weight at the remaining budget `Y`, and its pairs
with the weighted recorded contacts `K_F`), while the rate decreases by at least `(ρ + K_F) 2^-128`;
every other answer of a forest step (canonical, cached, or at a known read coordinate) costs at most
`(1 + Y) 2^-128`. So each forest step query, fresh or cached, leaves `(ρ - 1 - x) 2^-128`,
`x = total / 2^128`, which the potential pays out. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

variable [Params]

/-- The forest step inputs of a public parameter. -/
def IsFchainIn (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ f : PotentialA.FIn, input = f.input parameter

end Sphincs.Security.HiddenBridge

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- The slack of one FORS leaf query: `1 + Y + (ρ - 1 - x) ≤ ρ` for `Y ≤ x`. -/
theorem arith_fleaf {ρ x : ℝ} (hN : Numeric ρ x) (hx : 0 ≤ x) {Y : ℝ≥0∞} (hY : Y ≤ ENNReal.ofReal x) :
    1 + Y + ENNReal.ofReal (ρ - 1 - x) ≤ ENNReal.ofReal ρ := by
  have hd : 0 ≤ ρ - 1 - x := by linarith [hN.contact]
  calc 1 + Y + ENNReal.ofReal (ρ - 1 - x)
      ≤ ENNReal.ofReal 1 + ENNReal.ofReal x + ENNReal.ofReal (ρ - 1 - x) :=
        add_le_add (add_le_add (by rw [ENNReal.ofReal_one]) hY) le_rfl
    _ = ENNReal.ofReal (1 + x + (ρ - 1 - x)) := by
        rw [ENNReal.ofReal_add (by linarith) hd, ENNReal.ofReal_add (by norm_num) hx]
    _ = ENNReal.ofReal ρ := by
        congr 1
        ring

variable [Params]

namespace Ctx

variable (K : Ctx)

section Arith

variable {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) {Y : ℝ≥0∞} (hY : Y ≤ ENNReal.ofReal xr)
include hN hxr

theorem one_add_slack_le_rate (s : St) : 1 + ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.rate s :=
  calc 1 + ENNReal.ofReal (K.ρ - 1 - xr) = 1 + 0 + ENNReal.ofReal (K.ρ - 1 - xr) := by rw [add_zero]
    _ ≤ ENNReal.ofReal K.ρ := arith_fleaf hN hxr (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal xr)
    _ ≤ _ := K.rate_ge_rho hN s

include hY in
/-- **A fresh forest step leaves the slack.** -/
theorem arithFF (s : St) {f : FIn} {g : ℝ≥0∞} (hg : g ≤ 1) (hrec : g = 0 ∨ Recd s f) :
    g + (if Recd s f then Y + K.kf s else 1) + ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.rate s := by
  have hbase : 1 + Y + ENNReal.ofReal (K.ρ - 1 - xr) ≤ ENNReal.ofReal K.ρ := arith_fleaf hN hxr hY
  set d := ENNReal.ofReal (K.ρ - 1 - xr) with hd
  by_cases hr : Recd s f
  · rw [if_pos hr]
    calc g + (Y + K.kf s) + d ≤ (1 + Y + d) + K.kf s := by
          calc g + (Y + K.kf s) + d ≤ 1 + (Y + K.kf s) + d := add_le_add (add_le_add hg le_rfl) le_rfl
            _ = (1 + Y + d) + K.kf s := by ring
      _ ≤ ENNReal.ofReal K.ρ + K.kf s := add_le_add hbase le_rfl
      _ ≤ K.vrate s + K.kf s := add_le_add (K.vrate_ge hN.high s) le_rfl
      _ ≤ _ := K.rate_ge_kf s
  · have hg0 : g = 0 := hrec.resolve_right hr
    rw [hg0, if_neg hr, zero_add]
    calc 1 + d ≤ 1 + Y + d := add_le_add le_self_add le_rfl
      _ ≤ ENNReal.ofReal K.ρ := hbase
      _ ≤ _ := K.rate_ge_rho hN s

end Arith

/-! ### Forest steps leave the slack -/

section Fresh

variable {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) {y' : ℕ} (hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal xr)
  (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)

include hN hxr hY in
/-- A fresh forest step pays its guess and the slack. -/
theorem fresh_fchainF {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) {f : FIn}
    (hxF : x = f.input K.p) (hk : K.tg.kind x = .none) {g : ℝ≥0∞} (hg : g ≤ 1) (hrec : g = 0 ∨ Recd s f) :
    ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g + ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤
      K.pot (y' + 1) s := by
  have hi := initial_none_of_fresh K.initial s hinv.prepared x hx
  have h := K.step_fchain y' hx hi hxF hk
  have ha := K.arithFF hN hxr hY s hg hrec
  rw [K.pot_succ]
  calc ∑' r, Pr[= r | readOutside x s] * K.pot y' r.2 + ν * g + ν * ENNReal.ofReal (K.ρ - 1 - xr)
      ≤ K.pot y' s + ν * (if Recd s f then (y' : ℝ≥0∞) * ν + K.kf s else 1) + ν * g +
          ν * ENNReal.ofReal (K.ρ - 1 - xr) :=
        add_le_add (add_le_add h le_rfl) le_rfl
    _ = K.pot y' s + ν * (g + (if Recd s f then (y' : ℝ≥0∞) * ν + K.kf s else 1) +
          ENNReal.ofReal (K.ρ - 1 - xr)) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left ha bot_le)

include hN hxr hY hsec in
/-- **A guess at a fresh forest step** pays the guess, the answer and the slack. -/
theorem guess_freshF {s : St} (hinv : K.Inv s) {x : HashInput} (hx : s.cache x = none) (q : Address × Digest)
    (hp : HiddenGraph.parse K.p (candidateActive K.p) x = some q) (hk : s.known q.1.inputCoordinate = none)
    (hF : IsFchainIn K.p x) :
    ∑' r, Pr[= r | readOutside x (s.record (q.1.inputCoordinate, q.2))] * K.pot y' r.2 +
      ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.pot (y' + 1) s := by
  obtain ⟨rfl, -⟩ := (parse_some_iff _ _ x q).1 hp
  obtain ⟨addr, v⟩ := q
  obtain ⟨f₀, hxF⟩ := hF
  have hinv₁ := hinv.record (addr.inputCoordinate, v)
  have hx₁ : (s.record (addr.inputCoordinate, v)).cache (HiddenGraph.input K.p (addr, v)) = none := hx
  cases addr with
  | chain lay tree leaf chain step =>
      exfalso
      have hd := (domain_eq_of_input hxF trivial trivial).1
      cases hd
  | fchain index c sp j a i t =>
      have hKF : ∀ f : FIn, ((Address.fchain index c sp j a i t).inputCoordinate, v) = (f.inC, f.v) →
          K.FE s f → ((Address.fchain index c sp j a i t).inputCoordinate, v) ∈ s.guesses := by
        intro f hg hfe
        exfalso
        obtain ⟨w, hfr⟩ := hfe
        rw [fin_eq_of_inC hg] at hfr
        have h1 := hfr.1
        change s.cache (HiddenGraph.input K.p (Address.fchain _ _ _ _ _ _ _, _)) = some w at h1
        rw [hx] at h1
        cases h1
      have hkind := hsec _ (Or.inr ⟨index, c, sp, j, a, i, t, v, rfl⟩)
      rw [input_fchain] at hx₁ ⊢
      have main := K.fresh_fchainF hN hxr hY hinv₁ hx₁ rfl hkind le_rfl (Or.inr List.mem_cons_self)
      have hrec := K.pot_record (y' + 1) s ((Address.fchain index c sp j a i t).inputCoordinate, v) hk hKF
      rw [mul_one] at main
      refine (ENNReal.add_le_add_iff_right ν_ne_top).1 ?_
      calc ∑' r, Pr[= r | readOutside ((FIn.mk index c sp j a i t v).input K.p)
              (s.record ((Address.fchain index c sp j a i t).inputCoordinate, v))] * K.pot y' r.2 +
            ν * ENNReal.ofReal (K.ρ - 1 - xr) + ν
          = ∑' r, Pr[= r | readOutside ((FIn.mk index c sp j a i t v).input K.p)
              (s.record ((Address.fchain index c sp j a i t).inputCoordinate, v))] * K.pot y' r.2 + ν +
            ν * ENNReal.ofReal (K.ρ - 1 - xr) := by ring
        _ ≤ K.pot (y' + 1) (s.record ((Address.fchain index c sp j a i t).inputCoordinate, v)) := main
        _ ≤ _ := hrec

end Fresh

/-- **A guess at a cached forest step** pays the guess and the slack. -/
theorem guess_cachedF {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) (y' : ℕ) {s : St} (hinv : K.Inv s)
    {x : HashInput} {u : HashOutput} (hc : s.cache x = some u) (q : Address × Digest)
    (hp : HiddenGraph.parse K.p (candidateActive K.p) x = some q) (hk : s.known q.1.inputCoordinate = none) :
    K.pot y' (s.record (q.1.inputCoordinate, q.2)) + ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.pot (y' + 1) s := by
  obtain ⟨rfl, -⟩ := (parse_some_iff _ _ x q).1 hp
  have hKF : ∀ f : FIn, (q.1.inputCoordinate, q.2) = (f.inC, f.v) → K.FE s f →
      (q.1.inputCoordinate, q.2) ∈ s.guesses := by
    intro f hg hfe
    obtain ⟨addr, v⟩ := q
    cases addr with
    | chain lay tree' leaf' chain step =>
        have := congrArg Prod.fst hg
        cases this
    | fchain index c sp j a i t =>
        obtain ⟨w, hfr⟩ := hfe
        rw [fin_eq_of_inC hg] at hfr
        exact hinv.guessed _ w _ hfr hp hk
  calc K.pot y' (s.record (q.1.inputCoordinate, q.2)) + ν * ENNReal.ofReal (K.ρ - 1 - xr)
      ≤ K.pot y' s + ν + ν * ENNReal.ofReal (K.ρ - 1 - xr) := add_le_add (K.pot_record y' s _ hk hKF) le_rfl
    _ = K.pot y' s + ν * (1 + ENNReal.ofReal (K.ρ - 1 - xr)) := by ring
    _ ≤ K.pot y' s + ν * K.rate s :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (K.one_add_slack_le_rate hN hxr s) bot_le)
    _ = _ := (K.pot_succ y' s).symm

/-- A step that keeps the state pays the slack from the rate. -/
theorem pot_same_slack {xr : ℝ} (hN : Numeric K.ρ xr) (hxr : 0 ≤ xr) (y' : ℕ) (s : St) :
    K.pot y' s + ν * ENNReal.ofReal (K.ρ - 1 - xr) ≤ K.pot (y' + 1) s := by
  rw [K.pot_succ]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ bot_le)
  exact le_trans le_add_self (K.one_add_slack_le_rate hN hxr s)

/-! ### One step -/

section Model

variable (M : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : M.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : M.incoming = Address.inputCoordinate) (hMo : M.outgoing = Address.outputCoordinate)

include hMp hMi in
/-- **A forest step query** pays the slack `(ρ - 1 - x) 2^-128`, fresh or cached, at a known or an
unknown secret. -/
theorem stepFchain {total : ℕ} (hN : Numeric K.ρ ((total : ℝ) / 2 ^ 128))
    (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)
    (bytes : HashInput) (hF : IsFchainIn K.p bytes) (budget : ℕ) (s : St) (hinv : K.Inv s) (hcost : 1 ≤ budget) :
    ∑' r, Pr[= r | costStep M (.inl (.inr (.inl bytes))) s] * K.potCap total (budget - 1) r.2 +
      ν * ENNReal.ofReal (K.ρ - 1 - (total : ℝ) / 2 ^ 128) ≤ K.potCap total budget s := by
  unfold potCap
  by_cases hb : budget ≤ total
  swap
  · rw [if_neg hb]
    exact le_top
  rw [if_pos hb]
  have hpot : ∀ r : HashOutput × St,
      (if budget - 1 ≤ total then K.pot (budget - 1) r.2 else ⊤) = K.pot (budget - 1) r.2 :=
    fun r => if_pos ((Nat.sub_le _ _).trans hb)
  simp only [hpot]
  have hxr : (0 : ℝ) ≤ (total : ℝ) / 2 ^ 128 := by positivity
  obtain ⟨y', rfl⟩ : ∃ y', budget = y' + 1 := ⟨budget - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal ((total : ℝ) / 2 ^ 128) := budget_le_x (by omega)
  have hsame := K.pot_same_slack hN hxr y' s
  obtain ⟨f, hxF⟩ := hF
  have hkF : K.tg.kind bytes = .none := hsec _ (Or.inr ⟨f.index, f.c, f.s, f.j, f.a, f.i, f.t, f.v, hxF⟩)
  rw [costStep_inl]
  cases hp : M.parse bytes with
  | none =>
      rw [lazyStep_unparsed M bytes s hp]
      cases hc : s.cache bytes with
      | some u =>
          rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
          exact hsame
      | none =>
          have h := K.fresh_fchainF hN hxr hY hinv hc hxF hkF (g := 0) bot_le (Or.inl rfl)
          rw [mul_zero, add_zero] at h
          exact h
  | some q =>
      have hq : HiddenGraph.parse K.p (candidateActive K.p) bytes = some q := by rw [← hMp, hp]
      cases hk : s.known (M.incoming q.1) with
      | none =>
          rw [lazyStep_guess M bytes s q hp hk, hMi]
          rw [hMi] at hk
          cases hc : s.cache bytes with
          | some u =>
              have hc' : (s.record (q.1.inputCoordinate, q.2)).cache bytes = some u := hc
              rw [readOutside_cached bytes _ u hc', tsum_probOutput_pure_mul]
              exact K.guess_cachedF hN hxr y' hinv hc q hq hk
          | none => exact K.guess_freshF hN hxr hY hsec hinv hc q hq hk ⟨f, hxF⟩
      | some canonical =>
          by_cases heq : q.2 = canonical
          · rw [lazyStep_canonical M bytes s q hp canonical hk heq, tsum_probOutput_map_mul]
            calc ∑' r, Pr[= r | sampleCoordinate (M.outgoing q.1) s] * K.pot y' r.2 +
                  ν * ENNReal.ofReal (K.ρ - 1 - (total : ℝ) / 2 ^ 128)
                ≤ K.pot y' s + ν * ENNReal.ofReal (K.ρ - 1 - (total : ℝ) / 2 ^ 128) :=
                  add_le_add (K.sample_mean y' s _) le_rfl
              _ ≤ _ := hsame
          · rw [lazyStep_other M bytes s q hp canonical hk heq]
            cases hc : s.cache bytes with
            | some u =>
                rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
                exact hsame
            | none =>
                have h := K.fresh_fchainF hN hxr hY hinv hc hxF hkF (g := 0) bot_le (Or.inl rfl)
                rw [mul_zero, add_zero] at h
                exact h

theorem digestCount_fleaf (tg' : Targeting HashInput HashOutput Coordinate)
    (hdig : tg'.digest = ForestSigner.IsMsgInput) (bytes : HashInput) (hF : IsFchainIn K.p bytes) :
    digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes)))) =
      0 := by
  have hnm : ¬ForestSigner.IsMsgInput bytes := by
    obtain ⟨f, rfl⟩ := hF
    exact fun hd => msg_ne_fchain hd rfl
  have h := digestCount_bytes tg' bytes
  rw [hdig, if_neg hnm] at h
  exact_mod_cast h

include hMp hMi hMo in
/-- **One step with both payments.** -/
theorem stepF (tg' : Targeting HashInput HashOutput Coordinate) (hdig : tg'.digest = ForestSigner.IsMsgInput)
    {total : ℕ} (hN : Numeric K.ρ ((total : ℝ) / 2 ^ 128))
    (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)
    (hmsg : ∀ x, ForestSigner.IsMsgInput x → K.tg.kind x = .none)
    (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (budget : ℕ) (s : St) (hinv : K.Inv s)
    (hcost : sourceCost input ≤ budget) :
    ∑' r, Pr[= r | costStep M input s] * K.potCap total (budget - sourceCost input) r.2 +
      ENNReal.ofReal (K.ρ / 2 ^ 128) * digestCount tg' (recorded input) +
      ENNReal.ofReal ((K.ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) * fleafCount (IsFchainIn K.p) (recorded input) ≤
        K.potCap total budget s := by
  by_cases hF : ∃ bytes, input = .inl (.inr (.inl bytes)) ∧ IsFchainIn K.p bytes
  · obtain ⟨bytes, rfl, hF⟩ := hF
    have hc1 : sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes))) = 1 :=
      rfl
    rw [hc1] at hcost ⊢
    rw [K.digestCount_fleaf tg' hdig bytes hF, Nat.cast_zero, mul_zero, add_zero, fleafCount_recorded_inl,
      if_pos hF, mul_one, payment_eq]
    exact K.stepFchain M hMp hMi hN hsec bytes hF budget s hinv hcost
  · have hfc : fleafCount (IsFchainIn K.p) (recorded input) = 0 :=
      fleafCount_recorded_eq_zero _ input fun bytes h hb => hF ⟨bytes, h, hb⟩
    rw [hfc, Nat.cast_zero, mul_zero, add_zero]
    exact K.step M hMp hMi hMo tg' hdig hN hsec hmsg input budget s hinv hcost

end Model

end Ctx

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

/-- **Linear potential on the small-budget route, paying every FORS leaf query.** Besides the
digest baseline `ρ / 2^128`, every FORS leaf query of the trace (fresh or cached) is paid
`(ρ - 1 - x) / 2^128`, `x = total / 2^128`. -/
theorem smallRoute_potentialF
    (hknown : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (tg : Targeting HashInput HashOutput Coordinate) (hdigest : tg.digest = ForestSigner.IsMsgInput)
    (total : ℕ) (hN : Numeric ρ ((total : ℝ) / 2 ^ 128))
    {α : Type} (comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate) α) :
    ∑' out, Pr[= out | interp tg prepared.2 (sampleModel parameterOutput highs) comp total
        (DebtState.start prepared.2 known)] *
      (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
        ENNReal.ofReal (ρ / 2 ^ 128) * digestCount tg out.1.2.2.1 +
        ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
          fleafCount (IsFchainIn (truncateHash parameterOutput)) out.1.2.2.1) ≤
      ENNReal.ofReal (ρ * total / 2 ^ 128) := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  have hMp : (sampleModel parameterOutput highs).parse = HiddenGraph.parse K.p (candidateActive K.p) :=
    sampleModel_parse parameterOutput highs
  have hMi := sampleModel_incoming parameterOutput highs
  have hMo := sampleModel_outgoing parameterOutput highs
  have h := interp_potential2 tg prepared.2 (sampleModel parameterOutput highs) (IsFchainIn K.p) K.Inv
    (K.potCap total) K.payoff (ENNReal.ofReal (K.ρ / 2 ^ 128))
    (ENNReal.ofReal ((K.ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128))
    (fun budget state _ => K.endValue_le_cap total budget state)
    (fun input budget state hinv hcost => K.stepF (sampleModel parameterOutput highs) hMp hMi hMo tg hdigest hN
      (ctxA_sec parameterOutput fixed highs remaining prepared known ρ)
      (ctxA_msg parameterOutput fixed highs remaining prepared known ρ) input budget state hinv hcost)
    (fun input state hinv => K.inv_step (sampleModel parameterOutput highs) hMp hMi input state hinv)
    comp total (DebtState.start prepared.2 known)
    (inv_start parameterOutput fixed highs remaining prepared known ρ hknown)
  refine h.trans (le_of_eq ?_)
  unfold Ctx.potCap
  rw [if_pos le_rfl]
  exact pot_start K known (show (0 : ℝ) ≤ ρ by linarith [hN.low]) total

end Sample

end Sphincs.Security.PotentialA
