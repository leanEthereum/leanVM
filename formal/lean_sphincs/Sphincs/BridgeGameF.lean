import Sphincs.BridgeRevealRate
import Sphincs.BridgePotentialA8
import Sphincs.BridgeForsGameOnce

/-! **Paid potentials of the lazy run.** A potential of the state, the cached landed pairs, the
signing log, the disclosed views, the reveals and the remaining budget pays a final value of the
run if a new pair, any other ordinary query (up to a payment per query of a class), a signing call
on a fresh message and the end of the game are paid. The invariants carried along: the invariant of
the linear potential, the pair and count invariants, guesses backed by cached queries, and reveals
that are exposed and upward closed on their chains. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenBridge
open PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Reveals are exposed -/

omit [Params] in
/-- Revealed coordinates are exposed at the end of a run. -/
theorem interp_reveals_known {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
    (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    {α : Type} (computation : OracleComp CostSpec α) :
    ∀ budget (s : State), ∀ out ∈ support (interp tg initial model computation budget s),
      ∀ c ∈ out.1.2.1, out.2.known c ≠ none := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget s out hout c hc
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      cases hc
  | query_bind input next ih =>
      intro budget s out hout c hc
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        show inner.2.known c ≠ none
        change c ∈ HiddenBridge.revealed input ++ inner.1.2.1 at hc
        rcases List.mem_append.1 hc with hc | hc
        · rcases input with (draw | (bytes | coordinate)) | amount
          · cases hc
          · cases hc
          · simp only [HiddenBridge.revealed, List.mem_singleton] at hc
            subst hc
            change result ∈ support (sampleCoordinate _ s) at hresult
            have hexp := sampleCoordinate_expose _ s result hresult
            have hext := interp_extends tg initial model (next result.1) _ result.2 inner hinner
            have hres : result.2.known c = some result.1 := by
              rw [hexp]
              simp [DebtState.expose, QueryCache.cacheQuery_self]
            rw [hext.2.1 _ _ hres]
            exact Option.some_ne_none _
          · cases hc
        · exact ih result.1 _ result.2 inner hinner c hc
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        cases hc

/-! ### The invariants -/

section Defs

variable (K : Ctx) (data : PublicData) (Qtot : ℕ) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- **The invariants of the lazy run.** -/
structure BInvF (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate)
    (budget : ℕ) : Prop where
  inv : K.Inv s
  pinv : PInv K.p data s P
  minv : MInv K.p data s Ms
  dinv : DInv R d
  count : CountInv K.p data Qtot s budget
  gc : GuessCached model s
  rinv : ∀ c ∈ R, s.known c ≠ none
  rclosed : UpClosed R

/-- A potential of the lazy run. -/
abbrev PotF := State → List Pair → List Message → QueryLog SigningSpec → Multiset View → List Coordinate → ℕ → ℝ≥0∞

/-- A final value: of the result, of all reveals and of the final state. -/
abbrev FinalF := Option HiddenBridge.Outcome → List Coordinate → State → ℝ≥0∞

/-- A query reading a new pair is paid, unless the potential is already at least one (final values
are at most one). -/
def NewPairPaysF (Φ : PotF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    1 ≤ budget → BInvF K data Qtot model s P Ms d R budget →
      ∀ p : Pair, s.cache (pblk K.p data p) = none →
        1 ≤ Φ s P Ms L d R budget ∨
        pairE (fun u => Φ (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R (budget - 1)) ≤
          Φ s P Ms L d R budget

/-- A signing call on a fresh message is paid. -/
def SignPaysF (Φ : PotF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    BInvF K data Qtot model s P Ms d R budget → ∀ m : Message, (∀ entry ∈ L, entry.1 ≠ m) →
      ∑' o1, Pr{let x ← interp K.tg K.initial model (signCostSource K.p data m) budget s}[x = o1] *
          o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
            (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
        Φ s P Ms L d R budget

/-- The end of the game is paid. -/
def FinalPaysF (Φ : PotF) (G : FinalF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    BInvF K data Qtot model s P Ms d R budget → ∀ (forgery : Forgery) (verified : Bool),
      G (some (forgery, L, verified)) R s ≤ Φ s P Ms L d R budget

/-- Any other ordinary query is paid, up to `pay` for a query of the class. -/
def OrdinaryPaysF (IsF : HashInput → Prop) (pay : ℝ≥0∞) (Φ : PotF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    1 ≤ budget → BInvF K data Qtot model s P Ms d R budget → ∀ x : HashInput,
      ¬(∃ p, x = pblk K.p data p ∧ s.cache (pblk K.p data p) = none) →
        ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * Φ r.2 P Ms L d R (budget - 1) ≤
          Φ s P Ms L d R budget + pay * (if IsF x then 1 else 0)

/-- The expected number of queries of the class in the trace of an interpreted run. -/
noncomputable def expCount (IsF : HashInput → Prop) {α : Type} (prog : OracleComp CostSpec α) (budget : ℕ)
    (s : State) : ℝ≥0∞ :=
  ∑' out, Pr{let x ← interp K.tg K.initial model prog budget s}[x = out] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)

/-- A program whose final value is paid by the potential and `pay` per query of the class. -/
def GoodXF (IsF : HashInput → Prop) (pay : ℝ≥0∞) (Φ : PotF) (G : FinalF) (L : QueryLog SigningSpec)
    (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    BInvF K data Qtot model s P Ms d R budget →
      ∑' out, Pr{let x ← interp K.tg K.initial model prog budget s}[x = out] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
        Φ s P Ms L d R budget + pay * expCount K model IsF prog budget s

end Defs

/-! ### The invariants along the run -/

section Inv

variable {K : Ctx} {data : PublicData} {Qtot : ℕ} {model : HiddenRows.Model HashInput HashOutput Address Coordinate}

/-- After a new pair. -/
theorem binvF_withPair (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hparse : ∀ p, model.parse (pblk K.p data p) = none)
    {budget : ℕ} (hb : 1 ≤ budget) {s : State} {P : List Pair} {Ms : List Message} {d : Multiset View}
    {R : List Coordinate}
    (hB : BInvF K data Qtot model s P Ms d R budget) {p : Pair}
    (hp0 : s.cache (pblk K.p data p) = none) (u : HashOutput) :
    BInvF K data Qtot model (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) d R (budget - 1) := by
  have hext := extends_store s (pblk K.p data p) u hp0
  refine ⟨?_, pinv_withPair hB.pinv hp0 u, minv_withPair hB.minv p u, hB.dinv, fun m => ?_, ?_, hB.rinv,
    hB.rclosed⟩
  · refine hB.inv.store (pblk K.p data p) u hp0 fun q hq _ => ?_
    rw [← hMp, hparse p] at hq
    cases hq
  · have h1 := count_withPair (parameter := K.p) (data := data) m s p u
    have h2 := hB.count m
    omega
  · intro g hg
    obtain ⟨x, a, v, hp, hgq, hc⟩ := hB.gc g hg
    exact ⟨x, a, v, hp, hgq, cache_ne_of_extends hext hc⟩

/-- After an ordinary query touching no new pair. -/
theorem binvF_ordinary (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    {budget : ℕ} (hb : 1 ≤ budget) {s : State} {P : List Pair} {Ms : List Message}
    {d : Multiset View} {R : List Coordinate} (hB : BInvF K data Qtot model s P Ms d R budget)
    (x : HashInput) (hnew : ¬∃ p, x = pblk K.p data p ∧ s.cache (pblk K.p data p) = none)
    (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) :
    BInvF K data Qtot model r.2 P Ms d R (budget - 1) := by
  have hext := ordinaryStep_extends model x s r hr
  obtain ⟨hP', _⟩ := same_items K.p data hext (ordinaryStep_cache_ne model x s r hr) hnew hB.pinv
  refine ⟨K.inv_step model hMp hMi (.inl (.inr (.inl x))) s hB.inv r (by rw [costStep_ordinary]; exact hr),
    hP', minv_blocks (same_blocks hext (ordinaryStep_cache_ne model x s r hr) hnew) hB.minv, hB.dinv, fun m => ?_, guessCached_ordinary model x s hB.gc r hr, fun c hc => ?_, hB.rclosed⟩
  · have h1 : cachedCount K.p data m r.2 ≤ cachedCount K.p data m s + 1 := by
      rw [cachedCount_eq, cachedCount_eq]
      exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
    have h2 := hB.count m
    omega
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hB.rinv c hc)
    rw [hext.2.1 c v hv]
    exact Option.some_ne_none _

/-- A completed signing call (uniform start, then the scan) reveals upward-closed chains. -/
theorem closedRuns_source {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
    (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (parameter : PublicParameter) (data : PublicData) (message : Message) :
    ClosedRuns tg initial model (signCostSource parameter data message) := by
  intro budget s out hout hsome
  unfold signCostSource at hout
  rw [interp_liftProb_bind, support_bind] at hout
  obtain ⟨ρ, _, hout⟩ := Set.mem_iUnion₂.1 hout
  exact closedRuns_loop tg initial model parameter data message _ ρ budget s out hout hsome

/-- After a signing call. -/
theorem binvF_sign (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p, model.parse (pblk K.p data p) = none) (m : Message)
    (budget : ℕ) {s : State} {P : List Pair} {Ms : List Message} {d : Multiset View} {R : List Coordinate}
    (hB : BInvF K data Qtot model s P Ms d R budget)
    (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp K.tg K.initial model (signCostSource K.p data m) budget s))
    (r : Option Signature) (hr : o1.1.1 = some r) :
    BInvF K data Qtot model o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m)
      (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1) := by
  obtain ⟨_, hP', hM', hD', hC', _⟩ := sign_paramsS K.tg K.initial model Finset.univ Qtot hparse
    (fun _ _ _ _ _ _ _ _ => Finset.mem_univ _) budget s P Ms d R hB.inv.prepared hB.pinv hB.minv hB.dinv hB.count
    o1 ho1 r hr
  have hext := interp_extends K.tg K.initial model _ budget s o1 ho1
  refine ⟨inv_interp K model hMp hMi K.tg K.initial _ budget s hB.inv o1 ho1, hP', hM', hD', hC',
    interp_guessCached K.tg K.initial model _ budget s hB.gc o1 ho1, fun c hc => ?_,
    upClosed_append hB.rclosed (closedRuns_source K.tg K.initial model K.p data m budget s o1 ho1
      (by rw [hr]; rfl))⟩
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hB.rinv c hc)
    rw [hext.2.1 c v hv]
    exact Option.some_ne_none _
  · exact interp_reveals_known K.tg K.initial model _ budget s o1 ho1 c hc

/-- At the start of the run. -/
theorem binvF_start (hclean : ∀ p, K.initial (pblk K.p data p) = none) (known : HiddenReveal.Knowledge Coordinate)
    (hinv : K.Inv (DebtState.start K.initial known)) (total : ℕ) :
    BInvF K data total model (DebtState.start K.initial known) [] [] 0 [] total :=
  ⟨hinv, start_pinv K.p data K.initial hclean known, ⟨List.nodup_nil, fun m ρ h => absurd (hclean (m, ρ)) h⟩,
    (fun i c s j a ch pos h => by cases h),
    start_count K.p data K.initial hclean known total, guessCached_start K.initial model known,
    (fun c h => by cases h), fun _ _ _ _ _ _ _ _ h => by cases h⟩

end Inv

/-! ### The steps -/

section Steps

variable (K : Ctx) (data : PublicData) (Qtot : ℕ) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (IsF : HashInput → Prop) (pay : ℝ≥0∞) {Φ : PotF} {G : FinalF}

omit [Params] in
theorem tsum_bound_payF {α : Type} (mx : ProbComp α) (X : ℝ≥0∞) (Y : α → ℝ≥0∞) :
    ∑' a, Pr{let x ← mx}[x = a] * (X + pay * Y a) ≤ X + pay * ∑' a, Pr{let x ← mx}[x = a] * Y a := by
  calc ∑' a, Pr{let x ← mx}[x = a] * (X + pay * Y a)
      = (∑' a, Pr{let x ← mx}[x = a]) * X + pay * ∑' a, Pr{let x ← mx}[x = a] * Y a := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        exact tsum_congr fun a => by ring
    _ ≤ 1 * X + pay * ∑' a, Pr{let x ← mx}[x = a] * Y a := add_le_add (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl) le_rfl
    _ = _ := by rw [one_mul]

theorem goodXF_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodXF K data Qtot model IsF pay Φ G L (next v)) :
    GoodXF K data Qtot model IsF pay Φ G L (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hB
  unfold expCount
  rw [interp_draw, OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' v, Pr{let x ← (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))}[x = v] *
        (Φ s P Ms L d R budget + pay * expCount K model IsF (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hB) _
    _ ≤ _ := tsum_bound_payF pay _ _ _

/-- **One ordinary query**, with the payment. -/
theorem goodXF_ordinary (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p, model.parse (pblk K.p data p) = none) (hFp : ∀ p, ¬IsF (pblk K.p data p))
    (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hnewp : NewPairPaysF K data Qtot model Φ) (hord : OrdinaryPaysF K data Qtot model IsF pay Φ)
    (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodXF K data Qtot model IsF pay Φ G L (next v)) :
    GoodXF K data Qtot model IsF pay Φ G L (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hB
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinary, ite_eq_right hb, OracleComp.tsum_prEvent_pure_mul]
    simp only [hG0, zero_le]
  have hexp : expCount K model IsF (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
        ((if IsF x then 1 else 0) + expCount K model IsF (next r.1) (budget - 1) r.2) := by
    unfold expCount
    rw [interp_ordinary, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
    refine tsum_congr fun r => ?_
    rw [OracleComp.tsum_prEvent_map_mul]
    congr 1
    simp only [fleafCount_cons_inl, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, HiddenDebt.interp_mass, one_mul]
  by_cases hnew : ∃ p, x = pblk K.p data p ∧ s.cache (pblk K.p data p) = none
  · obtain ⟨p, rfl, hp0⟩ := hnew
    rcases hnewp budget s P Ms L d R hb hB p hp0 with hone | hnewp'
    · -- the potential is at least one: final values are at most one
      calc _ ≤ ∑' out, Pr{let x ← (interp K.tg K.initial model
              (liftM (CostSpec.query (.inl (.inr (.inl (pblk K.p data p))))) >>= next) budget s)}[x = out] * 1 :=
            ENNReal.tsum_le_tsum fun out => mul_le_mul_right (hG1 _ _ _) _
        _ ≤ 1 := by simp only [mul_one]; exact (OracleComp.tsum_prEvent_le_one _)
        _ ≤ _ := le_trans hone le_self_add
    rw [hexp, interp_ordinary, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
    simp only [OracleComp.tsum_prEvent_map_mul]
    simp only [ite_eq_right (hFp p), zero_add]
    rw [ordinaryStep, hparse p]
    simp only
    rw [readOutside_fresh _ s hp0, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
    calc ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] *
          ∑' out, Pr{let x ← interp K.tg K.initial model (next u) (budget - 1) (s.store (pblk K.p data p) u)}[x = out] *
            G out.1.1 (R ++ out.1.2.1) out.2
        ≤ ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] *
          (Φ (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R (budget - 1) +
            pay * expCount K model IsF (next u) (budget - 1) (s.store (pblk K.p data p) u)) :=
          ENNReal.tsum_le_tsum fun u => mul_le_mul_right
            (h u (budget - 1) _ _ _ d R (binvF_withPair hMp hparse hb hB hp0 u)) _
      _ = pairE (fun u => Φ (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R (budget - 1)) +
          pay * ∑' u, Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[x = u] *
            expCount K model IsF (next u) (budget - 1) (s.store (pblk K.p data p) u) := by
          unfold pairE
          simp only [mul_add, ENNReal.tsum_add]
          rw [← ENNReal.tsum_mul_left]
          congr 1
          exact tsum_congr fun a => by ring
      _ ≤ _ := add_le_add hnewp' le_rfl
  · rw [hexp, interp_ordinary, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
    simp only [OracleComp.tsum_prEvent_map_mul]
    calc _ ≤ ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
          (Φ r.2 P Ms L d R (budget - 1) + pay * expCount K model IsF (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · exact mul_le_mul_right (h r.1 (budget - 1) r.2 P Ms d R
              (binvF_ordinary hMp hMi hb hB x hnew r hr)) _
          · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
      _ = ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * Φ r.2 P Ms L d R (budget - 1) +
          pay * ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
            expCount K model IsF (next r.1) (budget - 1) r.2 := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [← ENNReal.tsum_mul_left]
          congr 1
          exact tsum_congr fun a => by ring
      _ ≤ (Φ s P Ms L d R budget + pay * (if IsF x then 1 else 0)) +
          pay * ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
            expCount K model IsF (next r.1) (budget - 1) r.2 :=
          add_le_add (hord budget s P Ms L d R hb hB x hnew) le_rfl
      _ = Φ s P Ms L d R budget + pay * ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
            ((if IsF x then 1 else 0) + expCount K model IsF (next r.1) (budget - 1) r.2) := by
          have hmass : ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] = 1 := by simp
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
          ring

theorem goodXF_pure (hfin : FinalPaysF K data Qtot model Φ G) (L : QueryLog SigningSpec)
    (forgery : Forgery) (verified : Bool) :
    GoodXF K data Qtot model IsF pay Φ G L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hB
  rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
  simp only [List.append_nil]
  exact le_trans (hfin budget s P Ms L d R hB forgery verified) le_self_add

theorem goodXF_liftHash (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p, model.parse (pblk K.p data p) = none) (hFp : ∀ p, ¬IsF (pblk K.p data p))
    (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hnewp : NewPairPaysF K data Qtot model Φ) (hord : OrdinaryPaysF K data Qtot model IsF pay Φ)
    (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodXF K data Qtot model IsF pay Φ G L (next a)) :
    GoodXF K data Qtot model IsF pay Φ G L ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodXF_ordinary K data Qtot model IsF pay hMp hMi hparse hFp hG0 hG1 hnewp hord L query _ ih

/-- **One signing call** on a message that was never signed before, with the payments. -/
theorem goodXF_sign (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p, model.parse (pblk K.p data p) = none)
    (hG0 : ∀ R s, G none R s = 0) (hsign : SignPaysF K data Qtot model Φ)
    (L : QueryLog SigningSpec) (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodXF K data Qtot model IsF pay Φ G (L ++ [⟨m, r⟩]) (next r)) :
    GoodXF K data Qtot model IsF pay Φ G L (signCostSource K.p data m >>= next) := by
  intro budget s P Ms d R hB
  set loop := signCostSource K.p data m with hloop
  set E1 : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 (fun r => expCount K model IsF (next r) (budget - traceCost o1.1.2.2.1) o1.2) with hE1
  have hpt : ∀ o1 ∈ support (interp K.tg K.initial model loop budget s),
      ∑' out, Pr{let x ← interpThen K.tg K.initial model next budget o1}[x = out] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
        o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
          (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) + pay * E1 o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        rw [interpThen_none K.tg K.initial model next budget o1 hres, OracleComp.tsum_prEvent_pure_mul]
        simp only [hG0, zero_le]
    | some r =>
        rw [interpThen_some K.tg K.initial model next budget o1 r hres, OracleComp.tsum_prEvent_map_mul]
        simp only [Option.elim, hE1, hres]
        have hB' := binvF_sign hMp hMi hparse m budget hB o1 ho1 r hres
        refine le_trans (le_of_eq (tsum_congr fun o2 => ?_)) (h r _ o1.2 _ _ _ _ hB')
        simp only [List.append_assoc]
  have hE1le : ∀ o1, E1 o1 ≤ ∑' out, Pr{let x ← interpThen K.tg K.initial model next budget o1}[x = out] *
      (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) := by
    intro o1
    cases hres : o1.1.1 with
    | none => simp only [hE1, hres, Option.elim, zero_le]
    | some r =>
        simp only [hE1, hres, Option.elim]
        rw [interpThen_some K.tg K.initial model next budget o1 r hres, OracleComp.tsum_prEvent_map_mul]
        unfold expCount
        refine ENNReal.tsum_le_tsum fun o2 => mul_le_mul_right ?_ _
        simp only [fleafCount_append, Nat.cast_add]
        exact le_add_self
  rw [interp_bind, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' o1, Pr{let x ← interp K.tg K.initial model loop budget s}[x = o1] *
        (o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
          (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) + pay * E1 o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp K.tg K.initial model loop budget s)
        · exact mul_le_mul_right (hpt o1 ho1) _
        · rw [(prEvent_eq_zero_of_not_mem_support _) ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr{let x ← interp K.tg K.initial model loop budget s}[x = o1] *
          o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
            (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) +
        pay * ∑' o1, Pr{let x ← interp K.tg K.initial model loop budget s}[x = o1] * E1 o1 := by
        simp only [mul_add, ENNReal.tsum_add]
        rw [← ENNReal.tsum_mul_left]
        congr 1
        exact tsum_congr fun a => by ring
    _ ≤ Φ s P Ms L d R budget + pay * expCount K model IsF (loop >>= next) budget s := by
        refine add_le_add (hsign budget s P Ms L d R hB m hm) (mul_le_mul_right ?_ _)
        unfold expCount
        rw [interp_bind, OracleComp.tsum_prEvent_bind_mul]
        exact ENNReal.tsum_le_tsum fun o1 => mul_le_mul_right (hE1le o1) _

/-- **A paid potential through any adversary that never repeats a message**, with the payments. -/
theorem goodXF_advProg (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p, model.parse (pblk K.p data p) = none) (hFp : ∀ p, ¬IsF (pblk K.p data p))
    (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hnewp : NewPairPaysF K data Qtot model Φ) (hord : OrdinaryPaysF K data Qtot model IsF pay Φ)
    (hsign : SignPaysF K data Qtot model Φ) (hfin : FinalPaysF K data Qtot model Φ G) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodXF K data Qtot model IsF pay Φ G L (advProg K.p data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      unfold finishGame
      exact goodXF_liftHash K data Qtot model IsF pay hMp hMi hparse hFp hG0 hG1 hnewp hord L _ _ fun v =>
        goodXF_pure K data Qtot model IsF pay hfin L forgery v
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodXF_draw K data Qtot model IsF pay L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodXF_ordinary K data Qtot model IsF pay hMp hMi hparse hFp hG0 hG1 hnewp hord L bytes _ fun v =>
          ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : ∀ entry ∈ L, entry.1 ≠ message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodXF_sign K data Qtot model IsF pay hMp hMi hparse hG0 hsign L message hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

/-- **The final value of the whole run** is at most the start potential plus `pay` times the
expected number of queries of the class. -/
theorem final_le_startF (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p, model.parse (pblk K.p data p) = none) (hFp : ∀ p, ¬IsF (pblk K.p data p))
    (hclean : ∀ p, K.initial (pblk K.p data p) = none)
    (total : ℕ) (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hnewp : NewPairPaysF K data total model Φ) (hord : OrdinaryPaysF K data total model IsF pay Φ)
    (hsign : SignPaysF K data total model Φ) (hfin : FinalPaysF K data total model Φ G)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : HiddenReveal.Knowledge Coordinate)
    (hinv : K.Inv (DebtState.start K.initial known)) :
    ∑' out, Pr{let x ← interp K.tg K.initial model (advProg K.p data M []) total (DebtState.start K.initial known)}[x = out] *
        G out.1.1 out.1.2.1 out.2 ≤
      Φ (DebtState.start K.initial known) [] [] [] 0 [] total +
        pay * expCount K model IsF (advProg K.p data M []) total (DebtState.start K.initial known) := by
  have h := goodXF_advProg K data total model IsF pay hMp hMi hparse hFp hG0 hG1 hnewp hord hsign hfin M [] hnr total
    (DebtState.start K.initial known) [] [] 0 [] (binvF_start hclean known hinv total)
  simpa only [List.nil_append] using h

end Steps

end Sphincs.Security.ForsPotential
