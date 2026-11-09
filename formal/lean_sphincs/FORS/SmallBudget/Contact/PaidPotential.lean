module

public import FORS.SmallBudget.Contact.RevealRate
public import FORS.SmallBudget.Linear.Payoff
public import FORS.CoverPotential.Game
public import FORS.Reduction.NoRepeat
public import FORS.CoverPotential.OneCoin

@[expose] public section

/-! **Paid potentials of the lazy run.** A potential of the state, the cached landed pairs, the
signing log, the disclosed views, the reveals and the remaining budget pays a final value of the
run if a new pair, any other ordinary query (up to a payment per query of a class), a signing call
on a fresh message and the end of the game are paid. A query of one digest call of a new pair
presamples the other calls. The invariants carried along: the invariant of the linear potential,
the pair and count invariants, guesses backed by cached queries, and exposed reveals. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenBridge
open PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Reveals are exposed -/

/-- Revealed coordinates are exposed at the end of a run. -/
theorem interp_reveals_known {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
    (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    {H : Type} [HonestInputs H HashInput]
    {α : Type} (computation : OracleComp (SourceCostSpec HashInput HashOutput Coordinate H) α) :
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
        · rcases input with (draw | (bytes | coordinate)) | (amount | honest)
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

/-- A potential of the lazy run. -/
abbrev PotF := State → List Pair → List Message → QueryLog SigningSpec → Multiset View → List Coordinate → ℕ → ℝ≥0∞

/-- A final value: of the result, of all reveals and of the final state. -/
abbrev FinalF := Option HiddenBridge.Outcome → List Coordinate → State → ℝ≥0∞

/-- The expected number of queries of the class in the trace of an interpreted run. -/
noncomputable def expCount (IsF : HashInput → Prop) {H : Type} [HonestInputs H HashInput] {α : Type}
    (prog : OracleComp (SourceCostSpec HashInput HashOutput Coordinate H) α) (budget : ℕ)
    (s : State) : ℝ≥0∞ :=
  ∑' out, Pr{let x ← interp K.tg K.initial model prog budget s}[x = out] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)

end Defs

/-! ### The invariants along the run -/

section Inv

variable {K : Ctx} {data : PublicData} {Qtot : ℕ} {model : HiddenRows.Model HashInput HashOutput Address Coordinate}

/-- The invariant survives the fresh stores of a family of inputs the model does not parse. -/
theorem inv_storeAll (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p)) :
    ∀ {n : ℕ} (x : Fin n → HashInput) (u : Fin n → HashOutput) (s : State), K.Inv s →
      Function.Injective x → (∀ i, s.cache (x i) = none) → (∀ i, model.parse (x i) = none) →
        K.Inv (storeAll x u s)
  | 0, _, _, _, h, _, _, _ => h
  | _ + 1, x, u, s, h, hx, hc, hp => by
      have hstep : K.Inv (s.store (x 0) (u 0)) := h.store (x 0) (u 0) (hc 0) fun q hq _ => by
        rw [← hMp, hp 0] at hq
        cases hq
      rw [storeAll_succ]
      exact inv_storeAll hMp (Fin.tail x) (Fin.tail u) _ hstep
        (fun a b e => Fin.succ_injective _ (hx e))
        (fun i => by
          show (s.store (x 0) (u 0)).cache (x i.succ) = none
          rw [store_cache_ne s (x 0) _ fun e => Fin.succ_ne_zero i (hx e)]
          exact hc i.succ)
        (fun i => hp i.succ)

/-- After a signing call. -/
theorem binvF_sign (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none) (m : Message)
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
    interp_guessCached K.tg K.initial model _ budget s hB.gc o1 ho1, fun c hc => ?_⟩
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hB.rinv c hc)
    rw [hext.2.1 c v hv]
    exact Option.some_ne_none _
  · exact interp_reveals_known K.tg K.initial model _ budget s o1 ho1 c hc

end Inv

/-! ### The steps -/

section Steps

variable (K : Ctx) (data : PublicData) (Qtot : ℕ) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (IsF : HashInput → Prop) (pay : ℝ≥0∞) {Φ : PotF} {G : FinalF}

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

end Steps

end FORS.Security.ForsPotential
