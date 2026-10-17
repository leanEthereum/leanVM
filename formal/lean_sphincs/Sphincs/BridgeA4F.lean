import Sphincs.BridgeWsum

/-! **The contact potential of the forest (A4).** A recorded forest step is a contact with weight
`cw` (one if decided, `2^-128` while its written coordinate is unexposed). Its chain is *settled*
once a reveal opens it at or below the step: the contact then pays one. An unsettled contact pays
its coefficient: the reveal rate of the remaining signatures, the coin part (the mass off the identity
of the groups of the live messages and the creation rate of the remaining budget), and the capped
near potential. The potential

  `Ψ = Σ_{recorded} cw · (settled ? 1 : sig + coin + min(1, potN(y))) + y 2^-128 coin +
      κ 2^-128 Σ_{j < y} potN(j) + lam Lmax (live landed pairs) y`

pays, at the end, a recorded contact at a chain opened at or below its step, or a near cover with a
recorded contact; a forest step query costs `2^-128 (N rate + 1 - κ)`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenBridge
open PotentialA
open Sphincs.LoopWalk

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Capped expectations -/

omit [Params] in
theorem tsum_min_leF {α : Type} (mx : ProbComp α) (X : α → ℝ≥0∞) :
    ∑' a, Pr[= a | mx] * min 1 (X a) ≤ min 1 (∑' a, Pr[= a | mx] * X a) := by
  refine le_min ?_ (ENNReal.tsum_le_tsum fun a => mul_le_mul_right (min_le_right _ _) _)
  calc ∑' a, Pr[= a | mx] * min 1 (X a) ≤ ∑' a, Pr[= a | mx] * 1 :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_right (min_le_left _ _) _
    _ = ∑' a, Pr[= a | mx] := by simp only [mul_one]
    _ ≤ 1 := tsum_probOutput_le_one

omit [Params] in
theorem pairE_min_leF (F : HashOutput → ℝ≥0∞) : pairE (fun a => min 1 (F a)) ≤ min 1 (pairE F) :=
  tsum_min_leF _ F

omit [Params] in
/-- **The split of one contact.** A contact with capped value is paid by `pay` and `κ` times its
uncapped value. -/
theorem capped_splitF {pay κ : ℝ≥0∞} (hκ : ν ≤ pay + κ * ν) (Q : ℝ≥0∞) :
    ν * min 1 Q ≤ pay + κ * ν * Q :=
  calc ν * min 1 Q ≤ (pay + κ * ν) * min 1 Q := mul_le_mul_left hκ _
    _ = pay * min 1 Q + κ * ν * min 1 Q := add_mul _ _ _
    _ ≤ pay * 1 + κ * ν * Q :=
        add_le_add (mul_le_mul_right (min_le_left _ _) _) (mul_le_mul_right (min_le_right _ _) _)
    _ = pay + κ * ν * Q := by rw [mul_one]

omit [Params] in
theorem pairE_sum_range (n : ℕ) (F : HashOutput → ℕ → ℝ≥0∞) :
    pairE (fun a => ∑ j ∈ Finset.range n, F a j) = ∑ j ∈ Finset.range n, pairE fun a => F a j := by
  unfold pairE
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]

/-! ### The potential -/

section DefsA4

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The chain of a step is opened by a reveal at or below the step. -/
def Settled (R : List Coordinate) (f : FIn) : Prop :=
  ∃ q : FPos, q.val ≤ f.t.val ∧ Coordinate.fchain f.index f.c f.s f.j f.a f.i q ∈ R

/-- Coefficient of a contact: one once settled, `C` otherwise. -/
noncomputable def gA (R : List Coordinate) (C : ℝ≥0∞) (f : FIn) : ℝ≥0∞ := if Settled R f then 1 else C

/-- The reveal rate of the remaining signatures. -/
noncomputable def sigRiskF (L : QueryLog SigningSpec) : ℝ≥0∞ := ((signatureLimit - L.length : ℕ) : ℝ≥0∞) * revRate

/-- The creation rate of the scan signer: `(2 − landing)/2^128` per query. -/
noncomputable def rateS : ℝ≥0∞ := (Fintype.card Randomness : ℝ≥0∞)⁻¹ * ((1 - landing) + 1)

/-- **The mass off the identity of the group of a message**: the mean over the starts of the walk
value with payoff 1 at every cached landed pair, 0 for a fresh start that ends at a fresh position
and 1 for a cached start that ends at a fresh position (pending mass). -/
noncomputable def offMass (parameter : PublicParameter) (data : PublicData) (s : State) (m : Message) : ℝ≥0∞ :=
  (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
    gv nextRand landing (stOf parameter data m s) (fun _ => 1) 0 1 digestAttemptLimit

/-- The coin part of the reveal rate: the mass off the identity of the groups of the live messages
and the creation rate of the remaining budget. -/
noncomputable def coinRiskF (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (budget : ℕ) : ℝ≥0∞ :=
  ((live L Ms).map fun m => offMass K.p data s m).sum + budget * rateS

/-- **The coin potential**: every unit of the remaining budget is either a contact attempt, hurt by the
masses off the identity of the live messages and by the digest queries of the budget after it, or a
digest query: `ν (y offSum + C(y, 2) rateS)`. -/
noncomputable def coinPotF (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (budget : ℕ) : ℝ≥0∞ :=
  ν * ((budget : ℝ≥0∞) * ((live L Ms).map fun m => offMass K.p data s m).sum +
    ((Nat.choose budget 2 : ℕ) : ℝ≥0∞) * rateS)

/-- **The near potential**: one coin, subtree-free near witness, baseline zero, no gate. -/
noncomputable def potNF (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  potG K.p data witnessNear wbar 0 Fail (fun _ => False) s P Ms L d k

/-- The coefficient of an unsettled contact. -/
noncomputable def coefU (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (budget : ℕ) : ℝ≥0∞ :=
  sigRiskF L + coinRiskF K data s Ms L budget + min 1 (potNF K data wbar Fail s P Ms L d budget)

/-- The contact potential without the cap term. -/
noncomputable def psiCoreF : PotF := fun s P Ms L d R budget =>
  if signatureLimit < L.length then 0
  else K.wsum (gA R (coefU K data wbar Fail s P Ms L d budget)) s +
      coinPotF K data s Ms L budget +
    κ * ν * ∑ j ∈ Finset.range budget, potNF K data wbar Fail s P Ms L d j

/-- **The contact potential**, with the cap term of the landed pairs of unsigned messages. -/
noncomputable def psiF (Lmax : ℕ) : PotF := fun s P Ms L d R budget =>
  psiCoreF K data wbar κ Fail s P Ms L d R budget + lam Lmax (livePairs L P).length budget

/-- The near forecast of a new pair at the start of the run. -/
noncomputable def startNearF (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excessW witnessNear 0) signatureLimit I 0) k []

end DefsA4

/-! ### Basic facts -/

section Basic

variable (K : Ctx)

omit [Params] in
theorem gA_mono (R : List Coordinate) {C C' : ℝ≥0∞} (h : C ≤ C') (f : FIn) : gA R C f ≤ gA R C' f := by
  unfold gA
  split_ifs
  · exact le_rfl
  · exact h

theorem wsum_mono_g {g g' : FIn → ℝ≥0∞} (h : ∀ f, g f ≤ g' f) (s : State) : K.wsum g s ≤ K.wsum g' s := by
  unfold Ctx.wsum
  refine Finset.sum_le_sum fun f _ => ?_
  split_ifs
  · exact mul_le_mul_left (h f) _
  · exact le_rfl

/-- The weights split into the settled part and the unsettled part times the coefficient. -/
theorem wsum_gA (R : List Coordinate) (C : ℝ≥0∞) (s : State) :
    K.wsum (gA R C) s = K.wsum (gA R 0) s + K.wsum (fun f => if Settled R f then 0 else 1) s * C := by
  unfold Ctx.wsum gA
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hr : Ctx.Recd s f <;> by_cases hS : Settled R f <;> simp [hr, hS, mul_comm]

theorem coinRiskF_mono (data : PublicData) (s : State) (Ms : List Message) (L : QueryLog SigningSpec) {k k' : ℕ}
    (h : k ≤ k') : coinRiskF K data s Ms L k ≤ coinRiskF K data s Ms L k' := by
  unfold coinRiskF
  gcongr

/-- One unit of budget releases the coin risk of one contact. -/
theorem coinPotF_succ (data : PublicData) (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (y : ℕ) :
    coinPotF K data s Ms L (y + 1) = coinPotF K data s Ms L y + ν * coinRiskF K data s Ms L y := by
  unfold coinPotF coinRiskF
  rw [Nat.choose_succ_succ' y 1, Nat.choose_one_right]
  push_cast
  ring

theorem coinPotF_mono (data : PublicData) (s : State) (Ms : List Message) (L : QueryLog SigningSpec) {k k' : ℕ}
    (h : k ≤ k') : coinPotF K data s Ms L k ≤ coinPotF K data s Ms L k' := by
  unfold coinPotF
  have hc : ((Nat.choose k 2 : ℕ) : ℝ≥0∞) ≤ ((Nat.choose k' 2 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.choose_le_choose 2 h
  gcongr

theorem potNF_mono (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (hw : wbar ≤ 1)
    (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ}
    (h : k ≤ k') :
    potNF K data wbar Fail s P Ms L d k ≤ potNF K data wbar Fail s P Ms L d k' :=
  potG_grow wbar 0 Fail witnessNear_props (fun _ _ _ h => h) hw ENNReal.zero_ne_top (Extends.refl s)
    (fun _ => rfl) P Ms L d h

/-- An unexposed read coordinate is not settled. -/
theorem not_settled_of_unknown {s : State} {R : List Coordinate} (hrinv : ∀ c ∈ R, s.known c ≠ none)
    (hclosed : UpClosed R) {f : FIn} (hk : s.known f.inC = none) : ¬Settled R f := by
  rintro ⟨q, hq, hmem⟩
  have hmem' := hclosed _ _ _ _ _ _ q ⟨f.t.val, by omega⟩ hmem hq
  exact hrinv _ hmem' hk

end Basic

/-! ### The mass off the identity -/

section OffMass

variable {parameter : PublicParameter} {data : PublicData}

/-- The probability that the scan signs with a cached landed pair is at most the mass off the
identity. -/
theorem hitMass_le_offMass (s : State) (m : Message) :
    hitMass parameter data s m ≤ offMass parameter data s m := by
  unfold hitMass offMass gv
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun ρ _ => ?_)
  exact walk_mono _ (fun _ => le_rfl) bot_le le_rfl _ _

/-- A message without cached digest has no mass off the identity. -/
theorem offMass_untouched (s : State) (m : Message) (h : ∀ ρ, s.cache (blk parameter data m ρ) = none) :
    offMass parameter data s m = 0 := by
  unfold offMass
  rw [gv_fresh landing_le_one _ (fun ρ => by simp [stOf, h ρ])]
  simp

/-- The mass off the identity of a message sees the state only through its digest blocks. -/
theorem offMass_congr {s s' : State} {m : Message}
    (h : ∀ ρ, s'.cache (blk parameter data m ρ) = s.cache (blk parameter data m ρ)) :
    offMass parameter data s' m = offMass parameter data s m := by
  have hst : stOf parameter data m s' = stOf parameter data m s := by
    funext ρ
    simp only [stOf]
    rw [h ρ]
  unfold offMass
  rw [hst]

/-- The mass off the identity sees the state only through the digest blocks. -/
theorem offMass_blocks {s s' : State}
    (h : ∀ q, s'.cache (pblk parameter data q) = s.cache (pblk parameter data q)) (m : Message) :
    offMass parameter data s' m = offMass parameter data s m :=
  offMass_congr fun ρ => h (m, ρ)

/-- A new pair of another message keeps the mass off the identity. -/
theorem offMass_withPair_other (s : State) (p : Pair) (u0 : HashOutput) {m : Message} (hm : m ≠ p.1) :
    offMass parameter data (withPair parameter data s p u0) m = offMass parameter data s m := by
  unfold offMass
  rw [stOf_withPair_other s p u0 hm]

/-- **A new pair, the mass off the identity of its message.** In the mean it grows by at most the
creation rate `(2 − landing)/2^128`. -/
theorem offMass_newPair (s : State) (p : Pair) (hp0 : s.cache (pblk parameter data p) = none) :
    pairE (fun u0 => offMass parameter data (withPair parameter data s p u0) p.1) ≤
      offMass parameter data s p.1 + rateS := by
  set cinv := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hcinv
  set st := stOf parameter data p.1 s with hstdef
  have hst : st p.2 = .fresh := by
    have h : s.cache (blk parameter data p.1 p.2) = none := hp0
    simp [hstdef, stOf, h]
  set Gh := gv nextRand landing (Function.update st p.2 .hit) (fun _ => (1 : ℝ≥0∞)) 0 1 digestAttemptLimit with hGh
  set Gm := gv nextRand landing (Function.update st p.2 .miss) (fun _ => (1 : ℝ≥0∞)) 0 1 digestAttemptLimit with hGm
  have hpt : ∀ u0, offMass parameter data (withPair parameter data s p u0) p.1 =
      if Landed parameter (blockIndex u0) then (fun _ : View => cinv * Gh) (viewOf u0) else cinv * Gm := by
    intro u0
    unfold offMass
    rw [stOf_withPair_self]
    split_ifs <;> rfl
  simp only [hpt]
  rw [pairE_landed parameter (fun _ => cinv * Gh) (cinv * Gm), freshAvg_const _ Finset.univ_nonempty]
  have hc := creation_le (σ := nextRand) (p := landing) landing_le_one st (fun _ => (1 : ℝ≥0∞)) 0 1
    ENNReal.zero_ne_top ENNReal.one_ne_top p.2 hst digestAttemptLimit
    (fun j h0 hj => nextRand_pow_ne p.2 j h0 (lt_trans hj (by unfold digestAttemptLimit; norm_num)))
  have hupd : Function.update (fun _ : Randomness => (1 : ℝ≥0∞)) p.2 (0 + 1) = fun _ => 1 := by
    funext x
    by_cases hx : x = p.2
    · rw [hx, Function.update_self, zero_add]
    · rw [Function.update_of_ne hx]
  rw [hupd, zero_add, mul_one] at hc
  unfold offMass rateS
  calc landing * (cinv * Gh) + (1 - landing) * (cinv * Gm)
      = cinv * (landing * Gh + (1 - landing) * Gm) := by ring
    _ ≤ cinv * (gv nextRand landing st (fun _ => (1 : ℝ≥0∞)) 0 1 digestAttemptLimit + (1 - landing) + 1) :=
        mul_le_mul' le_rfl hc
    _ = _ := by ring

/-- A new pair, the masses off the identity of a list of messages without repetition. -/
theorem offSum_newPair (s : State) (p : Pair) (hp0 : s.cache (pblk parameter data p) = none)
    (l : List Message) (hl : l.Nodup) :
    pairE (fun u0 => (l.map fun m => offMass parameter data (withPair parameter data s p u0) m).sum) ≤
      (l.map fun m => offMass parameter data s m).sum + rateS := by
  have hsame : ∀ (l' : List Message), p.1 ∉ l' → ∀ u0,
      (l'.map fun m => offMass parameter data (withPair parameter data s p u0) m).sum =
        (l'.map fun m => offMass parameter data s m).sum := by
    intro l' hnot u0
    rw [List.map_congr_left fun m hm => offMass_withPair_other s p u0 fun h => hnot (h ▸ hm)]
  by_cases hp : p.1 ∈ l
  · have hperm : l.Perm (p.1 :: l.erase p.1) := List.perm_cons_erase hp
    have hnot : p.1 ∉ l.erase p.1 := fun h => ((List.Nodup.mem_erase_iff hl).1 h).1 rfl
    have hpt : ∀ u0, (l.map fun m => offMass parameter data (withPair parameter data s p u0) m).sum =
        offMass parameter data (withPair parameter data s p u0) p.1 +
          ((l.erase p.1).map fun m => offMass parameter data s m).sum := by
      intro u0
      rw [(hperm.map _).sum_eq, List.map_cons, List.sum_cons, hsame _ hnot u0]
    simp only [hpt]
    rw [pairE_add, pairE_const, (hperm.map _).sum_eq, List.map_cons, List.sum_cons, add_right_comm]
    exact add_le_add (offMass_newPair s p hp0) le_rfl
  · simp only [hsame l hp, pairE_const]
    exact le_self_add

/-- Listing one more message does not change the masses off the identity: it has no cached digest. -/
theorem offSum_addMsg {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) (L : QueryLog SigningSpec)
    (m : Message) :
    ((live L (addMsg Ms m)).map fun m' => offMass parameter data s m').sum =
      ((live L Ms).map fun m' => offMass parameter data s m').sum := by
  unfold addMsg
  split_ifs with hm
  · rfl
  · have hun : ∀ ρ, s.cache (blk parameter data m ρ) = none := by
      intro ρ
      by_contra h
      exact hm (hM.mem m ρ h)
    unfold live
    rw [List.filter_cons]
    split_ifs
    · rw [List.map_cons, List.sum_cons, offMass_untouched s m hun, zero_add]
    · rfl

end OffMass


/-! ### A new pair -/

section NewPair

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- A new pair moves the near potential down by one level. -/
theorem potNF_newPair (hw : wbar ≤ 1) {s : State} {P : List Pair} {Ms : List Message} (hP : PInv K.p data s P)
    (hM : MInv K.p data s Ms) {p : Pair}
    (hp0 : s.cache (pblk K.p data p) = none) (L : QueryLog SigningSpec)
    (hrate : MsgLive L p.1 → Rate K.p data wbar s p.1) (d : Multiset View) (j : ℕ) :
    pairE (fun u => potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d j) ≤
      potNF K data wbar Fail s P Ms L d (j + 1) := by
  unfold potNF potG
  by_cases hL : False ∨ signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  · simp only [if_neg hL]
    have h := coreG_newPair wbar 0 Fail witnessNear_props hw ENNReal.zero_ne_top hP hM hp0 L hrate d
      (signatureLimit - L.length) j
    rwa [add_zero] at h

/-- **A new pair, the coin risk**: the mass off the identity of the message grows by at most the
creation rate in the mean, whether or not the message is live. -/
theorem coinRiskF_newPair {s : State} {Ms : List Message} (hM : MInv K.p data s Ms) (L : QueryLog SigningSpec)
    (p : Pair) (hp0 : s.cache (pblk K.p data p) = none) (y : ℕ) :
    pairE (fun u => coinRiskF K data (withPair K.p data s p u) (addMsg Ms p.1) L y) ≤
      coinRiskF K data s Ms L (y + 1) := by
  unfold coinRiskF
  rw [pairE_add, pairE_const, ← offSum_addMsg hM L p.1]
  have h := offSum_newPair (parameter := K.p) (data := data) s p hp0 (live L (addMsg Ms p.1))
    (live_nodup L (addMsg_nodup hM.nodup _))
  calc _ ≤ ((live L (addMsg Ms p.1)).map fun m => offMass K.p data s m).sum + rateS + (y : ℝ≥0∞) * rateS :=
        add_le_add h le_rfl
    _ = _ := by push_cast; ring

/-- **A new pair, the coin potential**: `y (offSum + rateS) + C(y, 2) rateS = y offSum + C(y + 1, 2) rateS`. -/
theorem coinPotF_newPair {s : State} {Ms : List Message} (hM : MInv K.p data s Ms) (L : QueryLog SigningSpec)
    (p : Pair) (hp0 : s.cache (pblk K.p data p) = none) (y : ℕ) :
    pairE (fun u => coinPotF K data (withPair K.p data s p u) (addMsg Ms p.1) L y) ≤
      coinPotF K data s Ms L (y + 1) := by
  unfold coinPotF
  rw [pairE_const_mul, pairE_add, pairE_const_mul, pairE_const, ← offSum_addMsg hM L p.1]
  have h := offSum_newPair (parameter := K.p) (data := data) s p hp0 (live L (addMsg Ms p.1))
    (live_nodup L (addMsg_nodup hM.nodup _))
  have hy : ((y : ℝ≥0∞)) ≤ ((y + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_succ y
  calc _ ≤ ν * ((y : ℝ≥0∞) * (((live L (addMsg Ms p.1)).map fun m => offMass K.p data s m).sum + rateS) +
          ((Nat.choose y 2 : ℕ) : ℝ≥0∞) * rateS) := by gcongr
    _ = ν * ((y : ℝ≥0∞) * ((live L (addMsg Ms p.1)).map fun m => offMass K.p data s m).sum +
          ((Nat.choose (y + 1) 2 : ℕ) : ℝ≥0∞) * rateS) := by
        rw [Nat.choose_succ_succ' y 1, Nat.choose_one_right]
        push_cast
        ring
    _ ≤ _ := by gcongr

/-- **A new pair.** With as many landed pairs of unsigned messages as the cap the potential is at
least one; otherwise the coin pays the creation rate. -/
theorem psiF_newPair {Cmax Lmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) :
    NewPairPaysF K data Qtot model (psiF K data wbar κ Fail Lmax) := by
  intro budget s P Ms L d R hb hB p hp0
  have hw := hfair.le_one
  set ℓ := (livePairs L P).length with hℓ
  by_cases hcap : 1 ≤ lam Lmax ℓ budget
  · refine Or.inl (le_trans hcap ?_)
    unfold psiF psiCoreF
    exact le_add_self
  refine Or.inr ?_
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → Rate K.p data wbar s p.1 := fun hlive =>
    rate_of_fair hfair s p.1 (by have := hB.count p.1; omega) (le_trans (landedCount_le hB.pinv L hlive) hlen)
  have hM := hB.minv
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- the cap term keeps its mean
  have hlam : pairE (fun u => lam Lmax (livePairs L (addPair K.p P p u)).length y) ≤ lam Lmax ℓ (y + 1) := by
    by_cases hlive : MsgLive L p.1
    · have hl : ∀ u, lam Lmax (livePairs L (addPair K.p P p u)).length y =
          if Landed K.p (blockIndex u) then lam Lmax (ℓ + 1) y else lam Lmax ℓ y := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, if_pos (by simpa using hlive), List.length_cons]
          rfl
        · rfl
      simp only [hl]
      exact le_of_eq (lam_newPair K.p Lmax ℓ y)
    · have hl : ∀ u, lam Lmax (livePairs L (addPair K.p P p u)).length y = lam Lmax ℓ y := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, if_neg (by simpa using hlive)]
          rfl
        · rfl
      simp only [hl, pairE_const]
      exact lam_mono le_rfl (Nat.le_succ y)
  unfold psiF psiCoreF
  rw [pairE_add]
  refine add_le_add ?_ hlam
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  simp only [if_neg hL]
  have hi := initial_none_of_fresh K.initial s hB.inv.prepared _ hp0
  have hnf : ∀ f : FIn, pblk K.p data p ≠ f.input K.p := fun f =>
    msg_ne_fchain (msgInput_digestInput K.p data.root p.1 p.2)
  have hw' : ∀ (g : FIn → ℝ≥0∞) u, K.wsum g (withPair K.p data s p u) = K.wsum g s := fun g u =>
    K.wsum_store_other g u hp0 hi hnf
  set wS := K.wsum (gA R 0) s with hwS
  set wU := K.wsum (fun f => if Settled R f then 0 else 1) s with hwU
  have hpt : ∀ u, K.wsum (gA R (coefU K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u)
        (addMsg Ms p.1) L d y)) (withPair K.p data s p u) =
      wS + wU * (sigRiskF L + coinRiskF K data (withPair K.p data s p u) (addMsg Ms p.1) L y +
        min 1 (potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d y)) := by
    intro u
    rw [hw', wsum_gA]
    rfl
  simp only [hpt]
  rw [pairE_add, pairE_add, pairE_add, pairE_const, pairE_const_mul, pairE_add, pairE_add, pairE_const,
    pairE_const_mul, pairE_sum_range]
  have h0 := coinPotF_newPair K data hM L p hp0 y
  have h1 := coinRiskF_newPair K data hM L p hp0 y
  have h2 : pairE (fun u => min 1 (potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u)
      (addMsg Ms p.1) L d y)) ≤ min 1 (potNF K data wbar Fail s P Ms L d (y + 1)) :=
    le_trans (pairE_min_leF _)
      (min_le_min le_rfl (potNF_newPair K data wbar Fail hw hB.pinv hM hp0 L hrate d y))
  have h3 : ∑ j ∈ Finset.range y, pairE (fun u =>
      potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d j) ≤
      ∑ j ∈ Finset.range (y + 1), potNF K data wbar Fail s P Ms L d j := by
    rw [Finset.sum_range_succ']
    exact le_trans (Finset.sum_le_sum fun j _ =>
      potNF_newPair K data wbar Fail hw hB.pinv hM hp0 L hrate d j) le_self_add
  rw [wsum_gA K R (coefU K data wbar Fail s P Ms L d (y + 1)) s, ← hwS, ← hwU]
  unfold coefU
  gcongr

end NewPair

/-! ### Any other ordinary query -/

section Ordinary

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- **Any other ordinary query**, paying `2^-128 (N rate) + payB` at a forest step input, once
`2^-128 ≤ payB + κ 2^-128`. -/
theorem psiF_ordinary (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate) (hw : wbar ≤ 1) {payB : ℝ≥0∞}
    (hκ : ν ≤ payB + κ * ν) (Lmax : ℕ) :
    OrdinaryPaysF K data Qtot model (IsFchainIn K.p) (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB)
      (psiF K data wbar κ Fail Lmax) := by
  intro budget s P Ms L d R hb hB x hnew
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hmass : ∑' r, Pr[= r | ordinaryStep model x s.known s] = 1 := by simp
  unfold psiF psiCoreF
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
  rw [add_right_comm]
  refine add_le_add ?_ (lam_mono le_rfl (Nat.le_succ y))
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, mul_zero, tsum_zero, zero_le]
  simp only [if_neg hL]
  set C0 := coefU K data wbar Fail s P Ms L d y with hC0
  set Q := potNF K data wbar Fail s P Ms L d y with hQ
  set S := ∑ j ∈ Finset.range y, potNF K data wbar Fail s P Ms L d j with hS
  set f1 : ℝ≥0∞ := if IsFchainIn K.p x then 1 else 0 with hf1
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      K.wsum (gA R (coefU K data wbar Fail r.2 P Ms L d y)) r.2 + coinPotF K data r.2 Ms L y +
          κ * ν * ∑ j ∈ Finset.range y, potNF K data wbar Fail r.2 P Ms L d j ≤
        K.wsum (gA R C0) r.2 + coinPotF K data s Ms L y + κ * ν * S := by
    intro r hr
    have hext := ordinaryStep_extends model x s r hr
    have hblocks := same_blocks (parameter := K.p) (data := data) hext (ordinaryStep_cache_ne model x s r hr) hnew
    have hcoin : coinRiskF K data r.2 Ms L y = coinRiskF K data s Ms L y := by
      unfold coinRiskF
      simp only [offMass_blocks hblocks]
    have hgrow : ∀ j, potNF K data wbar Fail r.2 P Ms L d j ≤ potNF K data wbar Fail s P Ms L d j := fun j =>
      potG_grow wbar 0 Fail witnessNear_props (fun _ _ _ h => h) hw ENNReal.zero_ne_top hext hblocks P Ms L d
        le_rfl
    have hcoinP : coinPotF K data r.2 Ms L y = coinPotF K data s Ms L y := by
      unfold coinPotF
      simp only [offMass_blocks hblocks]
    refine add_le_add (add_le_add (wsum_mono_g K (fun f => gA_mono R ?_ f) r.2) (le_of_eq hcoinP))
      (mul_le_mul_right (Finset.sum_le_sum fun j _ => hgrow j) _)
    rw [hC0]; unfold coefU; rw [hcoin]
    gcongr
    exact hgrow y
  have hC : ∀ f : FIn, x = f.input K.p → s.known f.inC = none → gA R C0 f ≤ C0 := by
    intro f _ hk
    unfold gA
    rw [if_neg (not_settled_of_unknown hB.rinv hB.rclosed hk)]
  have hmean := K.wsum_ordinary model hMp hMi hB.inv hB.gc x (gA R C0) C0 hC
  have hf1le : f1 ≤ 1 := by rw [hf1]; split_ifs <;> simp
  have hC0le : ν * C0 * f1 ≤ (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 + ν * coinRiskF K data s Ms L y +
      κ * ν * Q := by
    have hsig : sigRiskF L ≤ (signatureLimit : ℝ≥0∞) * revRate := by
      unfold sigRiskF
      gcongr
      exact_mod_cast Nat.sub_le _ _
    calc ν * C0 * f1 = (ν * sigRiskF L + ν * min 1 Q) * f1 + ν * coinRiskF K data s Ms L y * f1 := by
          rw [hC0]; unfold coefU; ring
      _ ≤ (ν * ((signatureLimit : ℝ≥0∞) * revRate) + (payB + κ * ν * Q)) * f1 + ν * coinRiskF K data s Ms L y * 1 := by
          gcongr
          exact capped_splitF hκ Q
      _ = (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 + ν * coinRiskF K data s Ms L y +
            κ * ν * Q * f1 := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hf1le)
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (K.wsum (gA R C0) r.2 + coinPotF K data s Ms L y + κ * ν * S) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_right (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = ∑' r, Pr[= r | ordinaryStep model x s.known s] * K.wsum (gA R C0) r.2 +
          (coinPotF K data s Ms L y + κ * ν * S) := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
        ring
    _ ≤ (K.wsum (gA R C0) s + ν * C0 * f1) + (coinPotF K data s Ms L y + κ * ν * S) :=
        add_le_add hmean le_rfl
    _ ≤ K.wsum (gA R C0) s + ((ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 +
          ν * coinRiskF K data s Ms L y + κ * ν * Q) + (coinPotF K data s Ms L y + κ * ν * S) := by
        gcongr
    _ = K.wsum (gA R C0) s + (coinPotF K data s Ms L y + ν * coinRiskF K data s Ms L y) + κ * ν * (S + Q) +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 := by ring
    _ ≤ K.wsum (gA R (coefU K data wbar Fail s P Ms L d (y + 1))) s +
          coinPotF K data s Ms L (y + 1) +
          κ * ν * ∑ j ∈ Finset.range (y + 1), potNF K data wbar Fail s P Ms L d j +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 := by
        rw [Finset.sum_range_succ, ← coinPotF_succ]
        gcongr
        refine wsum_mono_g K (fun f => gA_mono R ?_ f) s
        rw [hC0]; unfold coefU
        gcongr
        · exact coinRiskF_mono K data s Ms L (Nat.le_succ y)
        · exact potNF_mono K data wbar Fail hw s P Ms L d (Nat.le_succ y)

end Ordinary

/-! ### The start -/

section Start

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem potNF_start (known : HiddenReveal.Knowledge Coordinate) (total : ℕ) :
    potNF K data wbar Fail (DebtState.start K.initial known) [] [] [] 0 total =
      total * (startNearF wbar total + failMass Fail) + signatureLimit * failMass Fail := by
  unfold potNF potG
  rw [if_neg (by simp)]
  unfold coreG
  simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.sub_zero]
  rfl

/-- The coin risk at the start: the creation rate of the whole budget. -/
theorem coinRiskF_start (s : State) (total : ℕ) : coinRiskF K data s [] [] total = total * rateS := by
  unfold coinRiskF live
  simp

/-- The coin potential at the start: the digest queries of the budget after each unit. -/
theorem coinPotF_start (s : State) (total : ℕ) :
    coinPotF K data s [] [] total = ν * (((Nat.choose total 2 : ℕ) : ℝ≥0∞) * rateS) := by
  unfold coinPotF live
  simp

/-- **The start of the contact potential.** -/
theorem psiF_start (Lmax : ℕ) (known : HiddenReveal.Knowledge Coordinate) (total : ℕ) :
    psiF K data wbar κ Fail Lmax (DebtState.start K.initial known) [] [] [] 0 [] total =
      ν * (((Nat.choose total 2 : ℕ) : ℝ≥0∞) * rateS) +
        κ * ν * ∑ j ∈ Finset.range total, ((j : ℝ≥0∞) * (startNearF wbar j + failMass Fail) +
          signatureLimit * failMass Fail) + lam Lmax 0 total := by
  unfold psiF psiCoreF
  rw [if_neg (by simp)]
  have hw0 : ∀ g, K.wsum g (DebtState.start K.initial known) = 0 := fun g => by
    unfold Ctx.wsum
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [if_neg]
    intro h
    cases h
  rw [hw0, zero_add]
  simp only [potNF_start, coinPotF_start]
  rfl

end Start

end Sphincs.Security.ForsPotential
