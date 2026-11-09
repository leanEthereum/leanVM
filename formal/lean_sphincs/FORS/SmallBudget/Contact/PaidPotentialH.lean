module

public import FORS.SmallBudget.Contact.PaidPotential
public import FORS.SmallBudget.Contact.HonestBase
public import FORS.CoverPotential.GameH

@[expose] public section

/-! **Paid potentials of the lazy run with the honest signer** (`advProgH`): the definitions and
steps of `PaidPotential` for the cost interface with honest reads. The signer reads honestly, so a
signing call costs no budget and the signed message's cached digest entries may grow for free: the
count invariant is kept for the live (unsigned) messages only, which is all the potentials use. The
invariants through a signing call are a hypothesis here (`SignInvH`), discharged by the signer's
facts. -/

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

section ThenH

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem interpThen_some {α β : Type} (next : α → OracleComp CostSpecH β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (v : α) (hv : o1.1.1 = some v) :
    interpThen tg initial model next budget o1 =
      (fun o2 => ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2)) <$>
        interp tg initial model (next v) (budget - traceCost o1.1.2.2.1) o1.2 := by
  unfold interpThen
  rw [hv]

theorem interpThen_none {α β : Type} (next : α → OracleComp CostSpecH β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (hv : o1.1.1 = none) :
    interpThen tg initial model next budget o1 = pure ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) := by
  unfold interpThen
  rw [hv]

end ThenH

/-! ### The invariants, with honest reads -/

section Defs

variable (K : Ctx) (data : PublicData) (Qtot : ℕ) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- **The invariants of the lazy run.** -/
structure BInvFH (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate)
    (budget : ℕ) : Prop where
  inv : K.Inv s
  pinv : PInv K.p data s P
  minv : MInv K.p data s Ms
  dinv : DInv R d
  count : ∀ m, MsgLive L m → cachedCount K.p data m s + budget ≤ Qtot
  gc : GuessCached model s
  rinv : ∀ c ∈ R, s.known c ≠ none

/-- A query reading a new pair is paid, unless the potential is already at least one (final values
are at most one). -/
def NewPairPaysF (Φ : PotF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    1 ≤ budget → BInvFH K data Qtot model s P Ms L d R budget →
      ∀ p : Pair, s.cache (pblk K.p data p firstCall) = none →
        1 ≤ Φ s P Ms L d R budget ∨
        pairE (fun u => Φ (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R (budget - 1)) ≤
          Φ s P Ms L d R budget

/-- A signing call on a fresh message is paid. -/
def SignPaysF (Φ : PotF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    BInvFH K data Qtot model s P Ms L d R budget → ∀ m : Message, (∀ entry ∈ L, entry.1 ≠ m) →
      ∑' o1, Pr{let x ← interp K.tg K.initial model (signCostSourceH K.p data m) budget s}[x = o1] *
          o1.1.1.elim 0 (fun r => Φ o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
            (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
        Φ s P Ms L d R budget

/-- **The invariants through an honest signing call** on a fresh message: the signed message is no
longer live, so its cached digest entries may grow at no budget (the signer's reads are honest). -/
def SignInvH : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate), BInvFH K data Qtot model s P Ms L d R budget → ∀ m : Message, (∀ entry ∈ L, entry.1 ≠ m) →
      ∀ o1 ∈ support (interp K.tg K.initial model (signCostSourceH K.p data m) budget s), ∀ r, o1.1.1 = some r →
        BInvFH K data Qtot model o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m) (L ++ [⟨m, r⟩])
          (discAfter K.p data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)

/-- The end of the game is paid. -/
def FinalPaysF (Φ : PotF) (G : FinalF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    BInvFH K data Qtot model s P Ms L d R budget → ∀ (forgery : Forgery) (verified : Bool),
      G (some (forgery, L, verified)) R s ≤ Φ s P Ms L d R budget

/-- Any other ordinary query is paid, up to `pay` for a query of the class. -/
def OrdinaryPaysF (IsF : HashInput → Prop) (pay : ℝ≥0∞) (Φ : PotF) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate),
    1 ≤ budget → BInvFH K data Qtot model s P Ms L d R budget → ∀ x : HashInput,
      ¬(∃ p call, x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none) →
        ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] * Φ r.2 P Ms L d R (budget - 1) ≤
          Φ s P Ms L d R budget + pay * (if IsF x then 1 else 0)

/-- A program whose final value is paid by the potential and `pay` per query of the class. -/
def GoodXF (IsF : HashInput → Prop) (pay : ℝ≥0∞) (Φ : PotF) (G : FinalF) (L : QueryLog SigningSpec)
    (prog : OracleComp CostSpecH HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    BInvFH K data Qtot model s P Ms L d R budget →
      ∑' out, Pr{let x ← interp K.tg K.initial model prog budget s}[x = out] * G out.1.1 (R ++ out.1.2.1) out.2 ≤
        Φ s P Ms L d R budget + pay * expCount K model IsF prog budget s

end Defs

/-! ### The invariants along the run -/

section Inv

variable {K : Ctx} {data : PublicData} {Qtot : ℕ} {model : HiddenRows.Model HashInput HashOutput Address Coordinate}

/-- After a new pair: every digest call of the pair is stored at once. -/
theorem binvFH_withPair (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    {budget : ℕ} (hb : 1 ≤ budget) {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {R : List Coordinate}
    (hB : BInvFH K data Qtot model s P Ms L d R budget) {p : Pair}
    (hp0 : s.cache (pblk K.p data p firstCall) = none) (u : DigestCall → HashOutput) :
    BInvFH K data Qtot model (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R (budget - 1) := by
  have hext := extends_withPair hB.pinv hp0 u
  have hknown := withPair_known (parameter := K.p) (data := data) s p u
  refine ⟨?_, pinv_withPair hB.pinv hp0 u, minv_withPair hB.minv p u, hB.dinv, fun m hm => ?_, ?_,
    fun c hc => by rw [hknown.1]; exact hB.rinv c hc⟩
  · exact inv_storeAll hMp (pblk K.p data p) u s hB.inv (pblk_call_injective K.p data p)
      (hB.pinv.first p hp0) (hparse p)
  · have h1 := count_withPair (parameter := K.p) (data := data) m s p u
    have h2 := hB.count m hm
    omega
  · intro g hg
    rw [hknown.2] at hg
    obtain ⟨x, a, v, hp, hgq, hc⟩ := hB.gc g hg
    exact ⟨x, a, v, hp, hgq, cache_ne_of_extends hext hc⟩

/-- After an ordinary query touching no new pair. -/
theorem binvFH_ordinary (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    {budget : ℕ} (hb : 1 ≤ budget) {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {R : List Coordinate} (hB : BInvFH K data Qtot model s P Ms L d R budget)
    (x : HashInput) (hnew : ¬∃ p call, x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none)
    (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) :
    BInvFH K data Qtot model r.2 P Ms L d R (budget - 1) := by
  have hext := ordinaryStep_extends model x s r hr
  obtain ⟨hP', _⟩ := same_items K.p data hext (ordinaryStep_cache_ne model x s r hr) hnew hB.pinv
  refine ⟨K.inv_step model hMp hMi (.inl (.inr (.inl x))) s hB.inv r (by rw [costStep_ordinary]; exact hr),
    hP', minv_blocks (same_blocks hext (ordinaryStep_cache_ne model x s r hr) hnew) hB.minv, hB.dinv,
    fun m hm => ?_, guessCached_ordinary model x s hB.gc r hr, fun c hc => ?_⟩
  · have h1 : cachedCount K.p data m r.2 ≤ cachedCount K.p data m s + 1 := by
      rw [cachedCount_eq, cachedCount_eq]
      exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
    have h2 := hB.count m hm
    omega
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hB.rinv c hc)
    rw [hext.2.1 c v hv]
    exact Option.some_ne_none _

/-- At the start of the run. -/
theorem binvFH_start (hclean : ∀ p call, K.initial (pblk K.p data p call) = none) (known : HiddenReveal.Knowledge Coordinate)
    (hinv : K.Inv (DebtState.start K.initial known)) (total : ℕ) :
    BInvFH K data total model (DebtState.start K.initial known) [] [] [] 0 [] total :=
  ⟨hinv, start_pinv K.p data K.initial hclean known, ⟨List.nodup_nil, fun m ρ h => absurd (hclean (m, ρ) firstCall) h⟩,
    (fun i κ l q h => by cases h),
    fun m _ => start_count K.p data K.initial hclean known total m, guessCached_start K.initial model known,
    (fun c h => by cases h)⟩

end Inv

/-! ### The steps -/

section Steps

variable (K : Ctx) (data : PublicData) (Qtot : ℕ) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (IsF : HashInput → Prop) (pay : ℝ≥0∞) {Φ : PotF} {G : FinalF}

theorem goodXFH_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodXF K data Qtot model IsF pay Φ G L (next v)) :
    GoodXF K data Qtot model IsF pay Φ G L (liftM (CostSpecH.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hB
  unfold expCount
  rw [interp_drawHB, OracleComp.tsum_prEvent_bind_mul, OracleComp.tsum_prEvent_bind_mul]
  calc _ ≤ ∑' v, Pr{let x ← (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))}[x = v] *
        (Φ s P Ms L d R budget + pay * expCount K model IsF (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hB) _
    _ ≤ _ := tsum_bound_payF pay _ _ _

/-- **One ordinary query**, with the payment. -/
theorem goodXFH_ordinary (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none) (hFp : ∀ p call, ¬IsF (pblk K.p data p call))
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPaysF K data Qtot model Φ) (hord : OrdinaryPaysF K data Qtot model IsF pay Φ)
    (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ v, GoodXF K data Qtot model IsF pay Φ G L (next v)) :
    GoodXF K data Qtot model IsF pay Φ G L (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hB
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinaryHB, ite_eq_right hb, OracleComp.tsum_prEvent_pure_mul]
    simp only [hG0, zero_le]
  have hexp : expCount K model IsF (liftM (CostSpecH.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr{let y ← ordinaryStep model x s.known s}[y = r] *
        ((if IsF x then 1 else 0) + expCount K model IsF (next r.1) (budget - 1) r.2) := by
    unfold expCount
    rw [interp_ordinaryHB, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
    refine tsum_congr fun r => ?_
    rw [OracleComp.tsum_prEvent_map_mul]
    congr 1
    simp only [fleafCount_cons_inl, mul_add]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, HiddenDebt.interp_mass, one_mul]
  by_cases hnew : ∃ p call, x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none
  · obtain ⟨p, c, rfl, hp0⟩ := hnew
    rcases hnewp budget s P Ms L d R hb hB p hp0 with hone | hnewp'
    · -- the potential is at least one: final values are at most one
      calc _ ≤ ∑' out, Pr{let x ← (interp K.tg K.initial model
              (liftM (CostSpecH.query (.inl (.inr (.inl (pblk K.p data p c))))) >>= next) budget s)}[x = out] * 1 :=
            ENNReal.tsum_le_tsum fun out => mul_le_mul_right (hG1 _ _ _) _
        _ ≤ 1 := by simp only [mul_one]; exact (OracleComp.tsum_prEvent_le_one _)
        _ ≤ _ := le_trans hone le_self_add
    -- every call of the pair is fresh and untargeted
    have hfresh : ∀ call, s.cache (pblk K.p data p call) = none := hB.pinv.first p hp0
    have hkind : ∀ call, K.tg.kind (pblk K.p data p call) = .none := fun call =>
      hmsg _ (msgInput_digestInput K.p data.root p.1 p.2 call)
    have hcard : (Fintype.card (DigestCall → HashOutput) : ℝ≥0∞) =
        (Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hpairE : ∀ F : (DigestCall → HashOutput) → ℝ≥0∞,
        pairE F = ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u, F u := by
      intro F
      unfold pairE
      rw [tsum_uniform_eq, hcard]
    -- the expected number of queries of the class is unchanged by the presampling
    have hcount : pairE (fun u => expCount K model IsF (next (u c)) (budget - 1)
          (withPair K.p data s p u)) =
        ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
          expCount K model IsF (next v) (budget - 1) (s.store (pblk K.p data p c) v) := by
      rw [hpairE]
      unfold expCount
      exact (interp_presample_new_eq K.tg K.initial model (pblk K.p data p)
        (pblk_call_injective K.p data p) hkind c next (budget - 1) s hfresh
        fun run => (fleafCount IsF run.2.2.1 : ℝ≥0∞)).symm
    rw [hexp, interp_ordinaryHB, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
    simp only [OracleComp.tsum_prEvent_map_mul]
    simp only [ite_eq_right (hFp p c), zero_add]
    rw [ordinaryStep, hparse p c]
    simp only
    rw [readOutside_fresh _ s (hfresh c), OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
    calc ∑' v, Pr{let z ← ($ᵗ HashOutput : ProbComp HashOutput)}[z = v] *
          ∑' out, Pr{let z ← (interp K.tg K.initial model (next v) (budget - 1)
            (s.store (pblk K.p data p c) v))}[z = out] * G out.1.1 (R ++ out.1.2.1) out.2
        ≤ pairE (fun u => ∑' out, Pr{let z ← (interp K.tg K.initial model (next (u c)) (budget - 1)
            (withPair K.p data s p u))}[z = out] * G out.1.1 (R ++ out.1.2.1) out.2) := by
          rw [hpairE]
          exact interp_presample_newH K.tg K.initial model (pblk K.p data p)
            (pblk_call_injective K.p data p) hkind c next (budget - 1) s hfresh
            (fun out => G out.1.1 (R ++ out.1.2.1) out.2) fun out y v hy => hGstore _ _ _ _ _ hy
      _ ≤ pairE (fun u => Φ (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R (budget - 1) +
            pay * expCount K model IsF (next (u c)) (budget - 1) (withPair K.p data s p u)) :=
          pairE_mono fun u => h (u c) (budget - 1) _ _ _ d R (binvFH_withPair hMp hparse hb hB hp0 u)
      _ = pairE (fun u => Φ (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R (budget - 1)) +
            pay * pairE (fun u => expCount K model IsF (next (u c)) (budget - 1)
              (withPair K.p data s p u)) := by
          rw [pairE_add, pairE_const_mul]
      _ ≤ _ := by
          rw [hcount]
          exact add_le_add hnewp' le_rfl
  · rw [hexp, interp_ordinaryHB, ite_eq_left hb, OracleComp.tsum_prEvent_bind_mul]
    simp only [OracleComp.tsum_prEvent_map_mul]
    calc _ ≤ ∑' r, Pr{let z ← ordinaryStep model x s.known s}[z = r] *
          (Φ r.2 P Ms L d R (budget - 1) + pay * expCount K model IsF (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · exact mul_le_mul_right (h r.1 (budget - 1) r.2 P Ms d R
              (binvFH_ordinary hMp hMi hb hB x hnew r hr)) _
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

theorem goodXFH_pure (hfin : FinalPaysF K data Qtot model Φ G) (L : QueryLog SigningSpec)
    (forgery : Forgery) (verified : Bool) :
    GoodXF K data Qtot model IsF pay Φ G L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hB
  rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
  simp only [List.append_nil]
  exact le_trans (hfin budget s P Ms L d R hB forgery verified) le_self_add

theorem goodXFH_liftHash (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none) (hFp : ∀ p call, ¬IsF (pblk K.p data p call))
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPaysF K data Qtot model Φ) (hord : OrdinaryPaysF K data Qtot model IsF pay Φ)
    (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ a, GoodXF K data Qtot model IsF pay Φ G L (next a)) :
    GoodXF K data Qtot model IsF pay Φ G L (liftRawH computation >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftRawH_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftRawH_query_bind, bind_assoc]
      exact goodXFH_ordinary K data Qtot model IsF pay hMp hMi hparse hFp hmsg hG0 hG1 hGstore hnewp hord
        L query _ ih

/-- **One signing call** on a message that was never signed before, with the payments. -/
theorem goodXFH_sign (hG0 : ∀ R s, G none R s = 0) (hsign : SignPaysF K data Qtot model Φ) (hsinv : SignInvH K data Qtot model)
    (L : QueryLog SigningSpec) (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m)
    (next : Option Signature → OracleComp CostSpecH HiddenBridge.Outcome)
    (h : ∀ r, GoodXF K data Qtot model IsF pay Φ G (L ++ [⟨m, r⟩]) (next r)) :
    GoodXF K data Qtot model IsF pay Φ G L (signCostSourceH K.p data m >>= next) := by
  intro budget s P Ms d R hB
  set loop := signCostSourceH K.p data m with hloop
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
        have hB' := hsinv budget s P Ms L d R hB m hm o1 ho1 r hres
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
theorem goodXFH_advProg (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none) (hFp : ∀ p call, ¬IsF (pblk K.p data p call))
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPaysF K data Qtot model Φ) (hord : OrdinaryPaysF K data Qtot model IsF pay Φ)
    (hsign : SignPaysF K data Qtot model Φ) (hsinv : SignInvH K data Qtot model) (hfin : FinalPaysF K data Qtot model Φ G) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodXF K data Qtot model IsF pay Φ G L (advProgH K.p data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProgH_pure]
      unfold finishGameH
      exact goodXFH_liftHash K data Qtot model IsF pay hMp hMi hparse hFp hmsg hG0 hG1 hGstore hnewp hord
        L _ _ fun v => goodXFH_pure K data Qtot model IsF pay hfin L forgery v
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProgH_draw]
        exact goodXFH_draw K data Qtot model IsF pay L draw _ fun v => ih v L (hnr v)
      · rw [advProgH_hash]
        exact goodXFH_ordinary K data Qtot model IsF pay hMp hMi hparse hFp hmsg hG0 hG1 hGstore hnewp hord
          L bytes _ fun v => ih v L (hnr v)
      · rw [advProgH_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : ∀ entry ∈ L, entry.1 ≠ message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodXFH_sign K data Qtot model IsF pay hG0 hsign hsinv L message hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

/-- **The final value of the whole run** is at most the start potential plus `pay` times the
expected number of queries of the class. -/
theorem final_le_startF (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none) (hFp : ∀ p call, ¬IsF (pblk K.p data p call))
    (hmsg : ∀ x, IsMsgInput x → K.tg.kind x = .none)
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (total : ℕ) (hG0 : ∀ R s, G none R s = 0) (hG1 : ∀ o R s, G o R s ≤ 1)
    (hGstore : ∀ o R (s : State) x u, s.cache x = none → G o R s ≤ G o R (s.store x u))
    (hnewp : NewPairPaysF K data total model Φ) (hord : OrdinaryPaysF K data total model IsF pay Φ)
    (hsign : SignPaysF K data total model Φ) (hsinv : SignInvH K data total model) (hfin : FinalPaysF K data total model Φ G)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : HiddenReveal.Knowledge Coordinate)
    (hinv : K.Inv (DebtState.start K.initial known)) :
    ∑' out, Pr{let x ← interp K.tg K.initial model (advProgH K.p data M []) total (DebtState.start K.initial known)}[x = out] *
        G out.1.1 out.1.2.1 out.2 ≤
      Φ (DebtState.start K.initial known) [] [] [] 0 [] total +
        pay * expCount K model IsF (advProgH K.p data M []) total (DebtState.start K.initial known) := by
  have h := goodXFH_advProg K data total model IsF pay hMp hMi hparse hFp hmsg hG0 hG1 hGstore hnewp hord
    hsign hsinv hfin M [] hnr total
    (DebtState.start K.initial known) [] [] 0 [] (binvFH_start hclean known hinv total)
  simpa only [List.nil_append] using h

end Steps

end FORS.Security.ForsPotential
