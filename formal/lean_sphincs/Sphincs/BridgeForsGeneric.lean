import Sphincs.BridgeForsPotentialOnce

/-! The one-coin forest potential of the scan signer with a generic monotone witness. A witness `W`
assigns to a target view and a multiset of disclosed views a monotone, finite value; the fresh-digest
price is `landing` times its average over a uniform target. The potential and its new-pair, order and
signing lemmas are those of `BridgeForsPotentialOnce` (terms through `termO`, lists of touched
messages with `MInv`) with the cover witness replaced by `W` and an arbitrary monotone gate in place
of the decided-hit test, and without the cap term `lam`; the forecast level of the signing lemmas is
free of the run's budget. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Witnesses and their prices -/

/-- Monotone finite witnesses. -/
def WitnessProps (W : View → Multiset View → ℝ≥0∞) : Prop := ∀ v, MonoFin (W v)

/-- The fresh-digest price of a witness. -/
noncomputable def priceW (W : View → Multiset View → ℝ≥0∞) (D : Multiset View) : ℝ≥0∞ :=
  landing * freshAvg Finset.univ fun v => W v D

/-- The excess of the price over a baseline. -/
noncomputable def excessW (W : View → Multiset View → ℝ≥0∞) (b0 : ℝ≥0∞) (D : Multiset View) : ℝ≥0∞ :=
  priceW W D - b0

theorem priceW_props {W : View → Multiset View → ℝ≥0∞} (hW : WitnessProps W) : MonoFin (priceW W) := by
  refine ⟨fun a b hab => ?_, fun D => ?_⟩
  · unfold priceW
    exact mul_le_mul_right (freshAvg_mono _ fun v _ => (hW v).1 a b hab) _
  · unfold priceW
    refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top landing_le_one) ?_
    exact freshAvg_ne_top Finset.univ_nonempty fun v => (hW v).2 D

theorem excessW_props {W : View → Multiset View → ℝ≥0∞} (hW : WitnessProps W) {b0 : ℝ≥0∞} (_hb0 : b0 ≠ ⊤) :
    MonoFin (excessW W b0) := by
  refine ⟨fun a b hab => tsub_le_tsub_right ((priceW_props hW).1 a b hab) b0, fun D => ?_⟩
  unfold excessW
  exact ne_top_of_le_ne_top ((priceW_props hW).2 D) tsub_le_self


/-! ### The potential -/

section DefsG

variable (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞)
  (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The forecast of a candidate: its own pair discloses nothing for it. -/
noncomputable def candValueG (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  termO parameter data wbar s Ms L (· = p) (W (pview parameter data s p)) d n k

/-- The excess forecast of a new pair. -/
noncomputable def hValueG (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  termO parameter data wbar s Ms L (fun _ => False) (excessW W b0) d n k

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def candG (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then
    (if (pview parameter data s p).1 ∈ Fail then 1 else candValueG parameter data W wbar s Ms L d n k p)
  else 0

/-- The potential without the gate. -/
noncomputable def coreG (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  (P.map (candG parameter data W wbar Fail s Ms L d n k)).sum +
    k * (hValueG parameter data W wbar b0 s Ms L d n k + failMass Fail) + n * failMass Fail

variable (gate : State → Prop)

/-- **The generic potential.** -/
noncomputable def potG (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  if gate s ∨ signatureLimit < L.length then 0
  else coreG parameter data W wbar b0 Fail s P Ms L d (signatureLimit - L.length) k

end DefsG

section Basic

variable {parameter : PublicParameter} {data : PublicData} {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)

/-- A new candidate's forecast is at most the baseline plus one excess. -/
theorem fresh_forecastG (hw : wbar ≤ 1) (s : State) (Ms : List Message) (L : QueryLog SigningSpec)
    (excl : Pair → Prop) (d : Multiset View) (n k : ℕ) :
    landing * freshAvg Finset.univ (fun v => termO parameter data wbar s Ms L excl (W v) d n k) ≤
      b0 + termO parameter data wbar s Ms L excl (excessW W b0) d n k := by
  have hU : (Finset.univ : Finset View).Nonempty := Finset.univ_nonempty
  unfold termO
  rw [← creations_freshAvg, ← creations_const_mul]
  have hpt : ∀ J, landing * freshAvg Finset.univ (fun v => termBase parameter data wbar s Ms L excl (W v) d n J) ≤
      b0 + termBase parameter data wbar s Ms L excl (excessW W b0) d n J := by
    intro J
    unfold termBase
    rw [← grpAll_freshAvg, ← grpAll_const_mul]
    calc grpAll parameter data s excl (live L Ms)
          (fun e => landing * freshAvg Finset.univ fun v => virtualOnce Finset.univ wbar (W v) n J e) d
        ≤ grpAll parameter data s excl (live L Ms)
          (fun e => b0 + virtualOnce Finset.univ wbar (excessW W b0) n J e) d := by
          refine grpAll_le_of_le s excl (fun e => ?_) _ d
          rw [← virtualOnce_freshAvg hU, ← virtualOnce_const_mul]
          calc virtualOnce Finset.univ wbar (fun D => landing * freshAvg Finset.univ fun v => W v D) n J e
              ≤ virtualOnce Finset.univ wbar (fun D => b0 + excessW W b0 D) n J e :=
                virtualOnce_mono_base (fun D => show priceW W D ≤ b0 + (priceW W D - b0) from le_add_tsub) n J e
            _ = b0 + virtualOnce Finset.univ wbar (excessW W b0) n J e := by
                rw [virtualOnce_add hU (fun _ => b0) (excessW W b0), virtualOnce_const hU hw]
      _ = _ := by
          rw [grpAll_add s excl (fun _ => b0), grpAll_const]
  calc creations Finset.univ landing (fun J => landing * freshAvg Finset.univ fun v =>
        termBase parameter data wbar s Ms L excl (W v) d n J) k []
      ≤ creations Finset.univ landing (fun J => b0 + termBase parameter data wbar s Ms L excl (excessW W b0) d n J) k [] :=
        creations_mono hpt k []
    _ = _ := by rw [creations_add (fun _ => b0), creations_const Finset.univ_nonempty landing_le_one]

/-- The witness of a candidate is below its forecast. -/
theorem base_le_candValueG (hW : WitnessProps W) (hw : wbar ≤ 1) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) (p : Pair) :
    W (pview parameter data s p) d ≤ candValueG parameter data W wbar s Ms L d n k p :=
  base_le_termO hw (hW _) s Ms L _ d n k

end Basic

/-! ### A new pair -/

section NewPairG

variable {parameter : PublicParameter} {data : PublicData} {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem candValueG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (p : Pair) :
    candValueG parameter data W wbar s Ms L d n k p ≤ candValueG parameter data W wbar s Ms L d n k' p :=
  termO_mono hw (hW _) s Ms L _ d n hk

theorem hValueG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    hValueG parameter data W wbar b0 s Ms L d n k ≤ hValueG parameter data W wbar b0 s Ms L d n k' :=
  termO_mono hw (excessW_props hW hb0) s Ms L _ d n hk

theorem candG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (s : State) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (q : Pair) :
    candG parameter data W wbar Fail s Ms L d n k q ≤ candG parameter data W wbar Fail s Ms L d n k' q := by
  unfold candG
  split_ifs
  · exact le_rfl
  · exact candValueG_mono wbar hW hw s Ms L d n hk q
  · exact le_rfl

theorem coreG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    coreG parameter data W wbar b0 Fail s P Ms L d n k ≤ coreG parameter data W wbar b0 Fail s P Ms L d n k' := by
  unfold coreG
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => candG_mono wbar Fail hW hw s Ms L d n hk q) ?_) le_rfl
  exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValueG_mono wbar b0 hW hw hb0 s Ms L d n hk) le_rfl)

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. -/
theorem coreG_newPair (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s : State} {P : List Pair}
    {Ms : List Message} (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) {p : Pair}
    (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec)
    (hrate : MsgLive L p.1 → Rate parameter data wbar s p.1) (d : Multiset View) (n k : ℕ) :
    pairE (fun u0 => coreG parameter data W wbar b0 Fail (withPair parameter data s p u0)
      (addPair parameter P p u0) (addMsg Ms p.1) L d n k) ≤
      coreG parameter data W wbar b0 Fail s P Ms L d n (k + 1) + b0 := by
  set Ms' := addMsg Ms p.1 with hMs'
  set φ := failMass Fail with hφ
  have hpP := not_mem_of_fresh hP hp0
  set Wp : View → ℝ≥0∞ := fun v => termO parameter data wbar s Ms L (· = p) (W v) d n k with hWp
  set H := hValueG parameter data W wbar b0 s Ms L d n (k + 1) with hH
  set S := (P.map (candG parameter data W wbar Fail s Ms L d n (k + 1))).sum with hS
  -- the candidates of the old pairs
  have h2 : ∀ q ∈ P, pairE (fun u0 => candG parameter data W wbar Fail (withPair parameter data s p u0) Ms' L d n k q) ≤
      candG parameter data W wbar Fail s Ms L d n (k + 1) q := by
    intro q hq
    have hqp : q ≠ p := fun h => hpP (h ▸ hq)
    have hv : ∀ u0, pview parameter data (withPair parameter data s p u0) q = pview parameter data s q :=
      fun u0 => pview_withPair_other s p q hqp u0
    unfold candG candValueG
    simp only [hv]
    split_ifs
    · simp only [pairE_const, le_refl]
    · exact termO_newPair hw (hW _) hM p hp0 L _ hrate d n k
    · simp only [pairE_const, le_refl]
  -- the candidate of the new pair
  have hnew : ∀ u0, Landed parameter (blockIndex u0) →
      candG parameter data W wbar Fail (withPair parameter data s p u0) Ms' L d n k p ≤
        (if (viewOf u0).1 ∈ Fail then 1 else 0) + Wp (viewOf u0) := by
    intro u0 hl
    unfold candG candValueG
    rw [pview_withPair_self]
    by_cases hu : Unsigned L p
    · rw [ite_eq_left hu]
      by_cases hF : (viewOf u0).1 ∈ Fail
      · rw [ite_eq_left hF, ite_eq_left hF]
        exact le_self_add
      · rw [ite_eq_right hF, ite_eq_right hF, zero_add]
        exact termO_stop (hW _) hM p hp0 L (· = p) rfl u0 hl d n k
    · rw [ite_eq_right hu]
      exact bot_le
  have hpoint : ∀ u0, coreG parameter data W wbar b0 Fail (withPair parameter data s p u0)
      (addPair parameter P p u0) Ms' L d n k ≤
      ((if Landed parameter (blockIndex u0) then (fun v : View => (if v.1 ∈ Fail then 1 else 0) + Wp v) (viewOf u0)
          else 0) +
        (P.map fun q => candG parameter data W wbar Fail (withPair parameter data s p u0) Ms' L d n k q).sum) +
      k * (hValueG parameter data W wbar b0 (withPair parameter data s p u0) Ms' L d n k + φ) + n * φ := by
    intro u0
    unfold coreG
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    unfold addPair
    by_cases hl : Landed parameter (blockIndex u0)
    · rw [ite_eq_left hl, ite_eq_left hl, List.map_cons, List.sum_cons]
      exact add_le_add (hnew u0 hl) le_rfl
    · rw [ite_eq_right hl, ite_eq_right hl, zero_add]
  refine le_trans (pairE_mono hpoint) ?_
  simp only [pairE_add, pairE_const_mul, pairE_const, pairE_list_sum]
  have h1 : pairE (fun u0 => if Landed parameter (blockIndex u0) then
      (fun v : View => (if v.1 ∈ Fail then 1 else 0) + Wp v) (viewOf u0) else 0) =
      landing * (φ + freshAvg Finset.univ Wp) := by
    rw [pairE_landed parameter (fun v => (if v.1 ∈ Fail then 1 else 0) + Wp v) 0, mul_zero, add_zero, freshAvg_add]
    rfl
  have h3 : pairE (fun u0 => hValueG parameter data W wbar b0 (withPair parameter data s p u0) Ms' L d n k) ≤ H :=
    termO_newPair hw (excessW_props hW hb0) hM p hp0 L _ hrate d n k
  have hfresh : landing * freshAvg Finset.univ Wp ≤ b0 + H := by
    refine le_trans (fresh_forecastG wbar b0 hw s Ms L (· = p) d n k) (add_le_add le_rfl ?_)
    refine le_trans (termO_excl_mono (excessW_props hW hb0) s Ms L (fun _ h => False.elim h) d n k) ?_
    exact hValueG_mono wbar b0 hW hw hb0 s Ms L d n (Nat.le_succ k)
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  have hSle : (P.map fun q => pairE fun u0 => candG parameter data W wbar Fail (withPair parameter data s p u0) Ms' L d n k q).sum ≤
      S := List.sum_le_sum fun q hq => h2 q hq
  rw [h1]
  unfold coreG
  calc landing * (φ + freshAvg Finset.univ Wp) +
        (P.map fun q => pairE fun u0 => candG parameter data W wbar Fail (withPair parameter data s p u0) Ms' L d n k q).sum +
        k * (pairE (fun u0 => hValueG parameter data W wbar b0 (withPair parameter data s p u0) Ms' L d n k) + φ) + n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairG

/-! ### Order and congruence -/

section OrderG

variable {parameter : PublicParameter} {data : PublicData} {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The potential sees the state only through the digest blocks. -/
theorem coreG_congr {s s' : State} (h : ∀ q, s'.cache (pblk parameter data q) = s.cache (pblk parameter data q))
    (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    coreG parameter data W wbar b0 Fail s' P Ms L d n k = coreG parameter data W wbar b0 Fail s P Ms L d n k := by
  have hv : ∀ q, pview parameter data s' q = pview parameter data s q := fun q => by unfold pview; rw [h q]
  unfold coreG hValueG candG candValueG
  simp only [hv, termO_blocks wbar h]

theorem potG_le_coreG (gate : State → Prop) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    potG parameter data W wbar b0 Fail gate s P Ms L d k ≤
      coreG parameter data W wbar b0 Fail s P Ms L d (signatureLimit - L.length) k := by
  unfold potG
  split_ifs
  · exact bot_le
  · exact le_rfl

/-- A grown state with the same digest blocks has no larger potential. -/
theorem potG_grow (hW : WitnessProps W) {gate : State → Prop}
    (hgate : ∀ s s' : State, Extends s s' → gate s → gate s') (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s s' : State}
    (hext : Extends s s')
    (h : ∀ q, s'.cache (pblk parameter data q) = s.cache (pblk parameter data q)) (P : List Pair)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potG parameter data W wbar b0 Fail gate s' P Ms L d k ≤ potG parameter data W wbar b0 Fail gate s P Ms L d k' := by
  unfold potG
  by_cases hr : gate s' ∨ signatureLimit < L.length
  · rw [ite_eq_left hr]; exact bot_le
  · have hr' : ¬(gate s ∨ signatureLimit < L.length) := fun h' =>
      hr (h'.imp (hgate s s' hext) id)
    rw [ite_eq_right hr, ite_eq_right hr', coreG_congr wbar b0 Fail h]
    exact coreG_mono wbar b0 Fail hW hw hb0 s P Ms L d _ hk

end OrderG

/-! ### The potential after signing a message for the first time -/

section SignPointG

variable (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞) (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight))) (m : Message) (s : State) (P : List Pair) (Ms : List Message)
  (L : QueryLog SigningSpec) (d : Multiset View)

/-- Bound for one outcome of a signing call. -/
noncomputable def canonG (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (W (pview parameter data s q))
        (restMsgs m L Ms) (· = q) out J) k []) else 0).sum +
  k * (creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (excessW W b0)
      (restMsgs m L Ms) (fun _ => False) out J) k [] + failMass Fail) +
  n * failMass Fail

/-- The bound for one signing outcome with the gate and the signature limit: zero once the gate is
on or no signature is left. -/
noncomputable def canonL (gate : State → Prop) (K : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) :
    ℝ≥0∞ :=
  if gate s ∨ signatureLimit ≤ L.length then 0
  else canonG parameter data W wbar b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) K out

end SignPointG

section SignPointMainG

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)

/-- **The potential after one signing outcome.** -/
theorem sign_pointG_level (hW : WitnessProps W) {gate : State → Prop}
    (hgate : ∀ s s' : State, Extends s s' → gate s → gate s')
    (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' K : ℕ} (hk : k' ≤ K) :
    potG parameter data W wbar b0 Fail gate out.2 (newPairs parameter data m s out.2 ++ P) (addMsg Ms m)
        (L ++ [⟨m, r⟩]) (discAfter parameter data m s d out) k' ≤
      canonL parameter data W wbar b0 Fail m s P Ms L d gate K out := by
  unfold canonL
  obtain ⟨_, hP', _, _, _, hview⟩ := sign_paramsS tg initial model Fail Qtot hparse hfail budget
    s P Ms d R hprep hP hM hD hC out hout r hr
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := source_post tg initial model parameter data m (fun ρ => hparse (m, ρ)) Fail hfail
    budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  unfold potG
  by_cases hcase : gate out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [ite_eq_left hcase]; exact bot_le
  rw [ite_eq_right hcase]
  have hreal : ¬gate s := fun h => hcase (Or.inl (hgate s out.2 hext h))
  have hlen : L.length < signatureLimit := by
    have := hcase
    simp only [List.length_append, List.length_singleton, not_or, not_lt] at this
    omega
  rw [ite_eq_right (by push Not; exact ⟨hreal, hlen⟩)]
  have hn : signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length = signatureLimit - (L.length + 1) := by simp
  rw [hn]
  set n := signatureLimit - (L.length + 1) with hndef
  unfold coreG canonG
  rw [List.map_append, List.sum_append]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · -- new pairs: only a failed fresh pair stays a candidate
    rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u0, hnew, _, h0, hl, hs0, _, hfl, hsig⟩ | ⟨_, _, _, hnew, _⟩
    · unfold newPairs; rw [hnew]; simp
    · have hv : pview parameter data out.2 (m, ρ) = viewOf u0 := pview_of_cached h0
      have hlist : newPairs parameter data m s out.2 = [(m, ρ)] := by
        unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
      rw [hlist]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      refine le_trans ?_ (freshNewWeight_ge hr hs0 h0 hl (fun v => if v.1 ∈ Fail then 1 else 0))
      unfold candG
      rw [hv]
      split_ifs with hu hF hF'
      · exact le_rfl
      · exfalso
        rcases r with _ | sig
        · exact hF (hfl rfl)
        · exact not_unsigned_signed (m := m) (L := L) (sig := sig) (by rw [hsig sig rfl]; exact hu)
      · exact bot_le
      · exact le_rfl
    · unfold newPairs; rw [hnew]; simp
  · -- old candidates
    refine List.sum_le_sum fun q hq => ?_
    unfold candG
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [ite_eq_left hU', ite_eq_left hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueG
        rw [hview q hq]
        refine post_term_leO tg initial model parameter data wbar Fail m hw (hW _) hparse hfail budget s Ms L d
          hprep out hout r hr (· = q) (fun sig hsig _ heq => ?_) n hk
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [ite_eq_right hU']
      exact bot_le
  · -- the excess forecast
    refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueG
    exact post_term_leO tg initial model parameter data wbar Fail m hw (excessW_props hW hb0) hparse hfail budget
      s Ms L d hprep out hout r hr (fun _ => False) (fun _ _ _ h => h) n hk

/-- **The signing step in expectation**, for a message signed for the first time. -/
theorem sign_expectG_level (hW : WitnessProps W) (gate : State → Prop)
    (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hb0 : b0 ≠ ⊤) (budget K : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View) (hM : MInv parameter data s Ms) :
    ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
        canonL parameter data W wbar b0 Fail m s P Ms L d gate K out ≤
      potG parameter data W wbar b0 Fail gate s P Ms L d K := by
  unfold canonL
  by_cases hcase : gate s ∨ signatureLimit ≤ L.length
  · simp only [ite_eq_left hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [ite_eq_right hcase]
  have hcase' : ¬gate s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  unfold potG
  rw [ite_eq_right (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ, model.parse (blk parameter data m ρ) = none := fun ρ => hparse (m, ρ)
  have hmass : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] ≤ 1 :=
    (OracleComp.tsum_prEvent_le_one _)
  have hFN : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
      freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out ≤ failMass Fail :=
    fresh_expectO tg initial model hparse' _ budget
  have hT : ∀ q ∈ P, ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
      (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (W (pview parameter data s q))
          (restMsgs m L Ms) (· = q) out J) K []) else 0) ≤
      candG parameter data W wbar Fail s Ms L d (n + 1) K q := by
    intro q _
    unfold candG
    split_ifs
    · rw [ENNReal.tsum_mul_right, mul_one]; exact hmass
    · unfold candValueG
      rw [termO_eq_cons hm hM]
      exact term_expectO tg initial model hparse' (hW _) _ _ budget K
    · simp
  have hH : ∑' out, Pr{let x ← interp tg initial model (signCostSource parameter data m) budget s}[x = out] *
      creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (excessW W b0)
        (restMsgs m L Ms) (fun _ => False) out J) K [] ≤ hValueG parameter data W wbar b0 s Ms L d (n + 1) K := by
    unfold hValueG
    rw [termO_eq_cons hm hM]
    exact term_expectO tg initial model hparse' (excessW_props hW hb0) _ _ budget K
  unfold canonG coreG
  simp only [mul_add, ENNReal.tsum_add]
  rw [tsum_list_sum]
  calc _ ≤ failMass Fail + (P.map (candG parameter data W wbar Fail s Ms L d (n + 1) K)).sum +
        (K * hValueG parameter data W wbar b0 s Ms L d (n + 1) K + K * failMass Fail) +
          n * failMass Fail := by
        refine add_le_add (add_le_add (add_le_add hFN (List.sum_le_sum hT)) (add_le_add ?_ ?_)) ?_
        · simp only [mul_left_comm _ (K : ℝ≥0∞), ENNReal.tsum_mul_left]
          exact mul_le_mul_right hH _
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
    _ = _ := by push_cast; ring

end SignPointMainG

end Sphincs.Security.ForsPotential
