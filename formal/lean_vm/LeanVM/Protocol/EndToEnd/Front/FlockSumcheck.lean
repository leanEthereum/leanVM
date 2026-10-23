/-
  LeanVM.Protocol.EndToEnd.Front.FlockSumcheck

  The sumcheck rounds of the verifier program specified from the knowledge soundness of
  ArkLib's sumcheck round components: the wire's missing coefficient decoded from the running
  claim, the round's check holding of the decoded message by construction, and each challenge
  escaping at the family's soundness count.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.FlockMech
public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.ToArkLib.SumcheckRound
public import LeanVM.Protocol.Spine.Errors

/-!
# Sumcheck rounds

The program's rounds (`Verifier.sumcheck`, `verifier.py:405-426` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) read `count - 1` coefficients and derive the other
from the running claim: in plain mode (`none`) `c₁ = claim + Σ_{k ≥ 2} c_k`, in equality mode
(`some r`) `c₀ = claim + r · Σ_{k ≥ 1} c_k`. ArkLib's round (`SumcheckRound.round`) reads all
`d + 1` coefficients and checks their weighted sum over the domain, `[(0, 1), (1, 1)]` (plain)
or `[(0, 1 - r), (1, r)]` (normalized), against the claim.

**The fidelity check.** The decoded message (the program's list `toVec 3 msg`) passes the ArkLib
check at the running claim (`weightedSum_of_msgOk`): characteristic two makes `1 - r = 1 + r` and
`2 = 0`, so the derived coefficient is the unique one passing the check. The next claim, Horner's
`poly_eval(message, challenge)`, is ArkLib's `evaluate` (`polyEval_eq_evaluate`). The program's
challenges, in order, are ArkLib's. No mismatch.

**The specification** (`sumcheckSpec`). A candidate is alive at stage `j` with challenges `chis`
and claim `v` when its carried condition `G` holds and its ArkLib statement is in the family's
relation `rel Φ j`. The reads keep doom (the relation does not read the message); a challenge
escapes for one candidate at `d = 2` values at most (`SumcheckRound.card_badChallenge_le`: a
message passing the check at a wrong claim is not the honest one, and two quadratics agree at two
points). Lead `0`; each round's challenge group has lead `L₀ · 2/|E|` plus the next round's
(`0`) or, after the last round, the follower's `T`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.SumcheckRound
open scoped ENNReal NNReal

@[expose] public section

/-! ## Errors as averages -/

/-- A count of bad challenges bounds the average of their indicator by `overE`. -/
theorem avgE_indE_le_overE {p : E → Prop} {N : ℕ} (h : Nat.card {c // p c} ≤ N) :
    avgE (fun c ↦ indE (p c)) ≤ ((overE N : ℝ≥0) : ℝ≥0∞) := by
  classical
  rw [← card_filter_eq_avgE, overE, ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    ENNReal.coe_natCast, ENNReal.coe_natCast, div_eq_mul_inv, mul_comm]
  gcongr
  rw [← natCard_subtype_eq_card_filter]
  exact_mod_cast h

/-- A predicate that implies another holds of fewer elements. -/
theorem natCard_mono {α : Type} [Finite α] {p q : α → Prop} (h : ∀ a, p a → q a) :
    Nat.card {a // p a} ≤ Nat.card {a // q a} :=
  Nat.card_le_card_of_injective (fun a ↦ ⟨a.1, h a.1 a.2⟩) fun _ _ hab ↦
    Subtype.ext (congrArg Subtype.val hab :)

/-! ## The wire -/

/-- A list as a vector of length `n`, padded with zeros. -/
def toVec (n : ℕ) (l : List E) : Vector E n := Vector.ofFn fun i ↦ l.getD i 0

/-- Appending an entry to a list of length `j` pushes it onto the vector read off it. -/
theorem toVec_append_singleton {j : ℕ} {l : List E} (hl : l.length = j) (c : E) :
    toVec (j + 1) (l ++ [c]) = (toVec j l).push c := by
  apply Vector.ext
  intro i hi
  simp only [toVec, Vector.getElem_ofFn, Vector.getElem_push]
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < l.length)]
  · have : i = l.length := by omega
    subst this
    simp

/-- The ArkLib domain of a round: plain or normalized. -/
def domOf : Option E → WeightedDomain E
  | none => [(0, 1), (1, 1)]
  | some r => [(0, 1 - r), (1, r)]

/-- The message the program's round returns, with its derived coefficient. -/
def MsgOk : Option E → E → List E → Prop
  | none, claim, msg => ∃ c₀ c₂, msg = [c₀, claim + sumE [c₂], c₂]
  | some r, claim, msg => ∃ c₁ c₂, msg = [claim + r * sumE [c₁, c₂], c₁, c₂]

/-- The message has three coefficients. -/
theorem MsgOk.length {eq : Option E} {claim : E} {msg : List E} (h : MsgOk eq claim msg) :
    msg.length = 3 := by
  cases eq with
  | none => obtain ⟨_, _, rfl⟩ := h; rfl
  | some r => obtain ⟨_, _, rfl⟩ := h; rfl

/-- **The decoded message passes ArkLib's check** at the running claim. -/
theorem weightedSum_of_msgOk {eq : Option E} {claim : E} {msg : List E} (h : MsgOk eq claim msg) :
    weightedSum 2 (domOf eq) (toVec 3 msg) = claim := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  cases eq with
  | none =>
    obtain ⟨c₀, c₂, rfl⟩ := h
    simp [weightedSum, domOf, evaluate, toVec, sumE, Fin.sum_univ_succ]
    linear_combination (c₀ + c₂) * h2
  | some r =>
    obtain ⟨c₁, c₂, rfl⟩ := h
    simp [weightedSum, domOf, evaluate, toVec, sumE, Fin.sum_univ_succ]
    linear_combination (r * c₁ + r * c₂) * h2

/-- Horner's rule is ArkLib's evaluation. -/
theorem polyEval_eq_evaluate {msg : List E} (h : msg.length = 3) (c : E) :
    polyEval msg c = evaluate 2 (toVec 3 msg) c := by
  match msg, h with
  | [a, b, d], _ =>
    simp [polyEval, evaluate, toVec, Fin.sum_univ_succ]
    ring

/-! ## One round's message -/

variable {β : Type} {C : List Ev → Set β} {εmax T : ℝ≥0∞}

/-- **The round's message**: the reads keep doom and return a message of the program's shape. -/
noncomputable def roundPolySpec (hst : Stable C) (A : β → Prop) (hT : T ≤ εmax) (claim : E) :
    (eq : Option E) → Spec (sumcheckRoundPoly 3 claim eq) (Doomed C A)
      (fun msg h ↦ MsgOk eq claim msg ∧ Doomed C A h) εmax 0 T
  | none => (doomRead hst A (zero_le.trans (zero_le.trans le_rfl))).mono (fun _ h ↦ h)
      (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun c₀ ↦
        (doomReadN hst A hT 0).bind' fun tail ↦
          (Spec.ret (c₀ :: (claim + sumE tail) :: tail)).mono (fun _ h ↦ ⟨by
            obtain ⟨hl, -⟩ := h
            match tail, hl with
            | [c₂], _ => exact ⟨c₀, c₂, rfl⟩, h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | some r => (doomReadN hst A hT 1).bind' fun tail ↦
      (Spec.ret ((claim + r * sumE tail) :: tail)).mono (fun _ h ↦ ⟨by
        obtain ⟨hl, -⟩ := h
        match tail, hl with
        | [c₁, c₂], _ => exact ⟨c₁, c₂, rfl⟩, h.2⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-! ## The rounds -/

variable {X ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)]

/-- A candidate is alive at stage `j` with challenges `chis` and claim `v`: its carried condition
holds and its ArkLib statement is in the family's relation. -/
def SumAlive (Φ : Family E X O Unit 2) (G : β → Prop) (xq : β → X) (oq : β → ∀ i, O i)
    (j : ℕ) (chis : List E) (v : E) (q : β) : Prop :=
  G q ∧ (((xq q, (toVec j chis, v)), oq q), ()) ∈ rel Φ j

omit [∀ i, OracleInterface (O i)] in
/-- **One challenge's escape**: from a candidate not alive at stage `j`, a message of the program's
shape and a challenge make it alive at stage `j + 1` for two challenges at most. -/
theorem sumAlive_escape (Φ : Family E X O Unit 2) {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m)
    (G : β → Prop) (xq : β → X) (oq : β → ∀ i, O i) {j : ℕ} (hj : j < m) {chis : List E}
    (hlen : chis.length = j) {eq : Option E} {claim : E} {msg : List E}
    (hmsg : MsgOk eq claim msg) (q : β) (hw : Φ.weight (xq q) j = domOf eq)
    (hq : ¬ SumAlive Φ G xq oq j chis claim q) :
    avgE (fun c ↦ indE (SumAlive Φ G xq oq (j + 1) (chis ++ [c]) (polyEval msg c) q)) ≤
      ((overE 2 : ℝ≥0) : ℝ≥0∞) := by
  by_cases hG : G q
  · have hrel : (((xq q, (toVec j chis, claim)), oq q), ()) ∉ rel Φ j := fun h ↦ hq ⟨hG, h⟩
    have hc : check j Φ.weight (xq q, (toVec j chis, claim)) (toVec 3 msg) = true := by
      rw [check, decide_eq_true_eq, hw]
      exact weightedSum_of_msgOk hmsg
    refine avgE_indE_le_overE ((natCard_mono fun c hc' ↦ ?_).trans
      (card_badChallenge_le j Φ H S hj ((xq q, (toVec j chis, claim)), toVec 3 msg) (oq q) hc))
    refine ⟨(), fun hmid ↦ hrel hmid.1, ?_⟩
    obtain ⟨-, hc'⟩ := hc'
    rw [toVec_append_singleton hlen, polyEval_eq_evaluate hmsg.length] at hc'
    exact hc'
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hG h.1).trans ?_
    refine (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans ?_
    exact zero_le

variable [Finite β] {L₀ : ℕ}

open Classical in
/-- **The rounds' specification.** From stage `j` with challenges `chis` (`j` of them) and claim
`claim`, the rounds `eq :: eqs` keep doom and end, with the challenges `pt` and the final claim,
at stage `j + |eq :: eqs|`. Each round's challenge escapes with average at most `L₀ · 2/|E|`;
`L₀ · 2/|E| + T ≤ εmax` bounds every round's group, the last one followed by the follower's
`T`. -/
noncomputable def sumcheckSpec (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (Φ : Family E X O Unit 2) {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m)
    (G : β → Prop) (xq : β → X) (oq : β → ∀ i, O i)
    (hε : (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + T ≤ εmax) :
    (eqs : List (Option E)) → (eq : Option E) → (j : ℕ) → (chis : List E) → (claim : E) →
      chis.length = j → j + eqs.length < m →
      (∀ q (k : ℕ) (hk : k < (eq :: eqs).length),
        Φ.weight (xq q) (j + k) = domOf (eq :: eqs)[k]) →
      Spec (sumcheck claim 3 (eq :: eqs)) (Doomed C (SumAlive Φ G xq oq j chis claim))
        (fun pf h ↦ pf.1.length = eqs.length + 1 ∧
          Doomed C (SumAlive Φ G xq oq (j + eqs.length + 1) (chis ++ pf.1) pf.2) h) εmax 0 T
  | [], eq, j, chis, claim, hlen, hm, hw =>
    (roundPolySpec (T := (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + T) hst _ hε claim
      eq).bind' fun msg ↦
      if hmsg : MsgOk eq claim msg then
        ((doomSample (εmax := εmax) (T := T) hst hcard (SumAlive Φ G xq oq j chis claim)
          (fun c ↦ SumAlive Φ G xq oq (j + 1) (chis ++ [c]) (polyEval msg c))
          ((overE 2 : ℝ≥0) : ℝ≥0∞)
          fun q hq ↦ sumAlive_escape Φ H S G xq oq (by omega) hlen hmsg q
            (by have h0 := hw q 0 (by simp); rw [Nat.add_zero] at h0; exact h0) hq).mono
            (fun _ (h : MsgOk eq claim msg ∧ _) ↦ h.2) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).bind' fun c ↦
          (Spec.ret (Post := fun pf h ↦ pf.1 = [] ∧ Doomed C
              (SumAlive Φ G xq oq (j + 1) (chis ++ [c]) pf.2) h) ([], polyEval msg c)).mono
            (fun _ h ↦ ⟨rfl, h⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl |>.bind' fun
              | ⟨pt, fin⟩ => (Spec.ret (c :: pt, fin)).mono (fun _ h ↦ by
                  obtain ⟨rfl, hd⟩ := h
                  exact ⟨rfl, by simpa using hd⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h ↦ hmsg h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
  | eq' :: eqs, eq, j, chis, claim, hlen, hm, hw =>
    (roundPolySpec (T := (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + 0) hst _
      (by rw [add_zero]; exact le_trans le_self_add hε) claim eq).bind' fun msg ↦
      if hmsg : MsgOk eq claim msg then
        ((doomSample (εmax := εmax) (T := 0) hst hcard (SumAlive Φ G xq oq j chis claim)
          (fun c ↦ SumAlive Φ G xq oq (j + 1) (chis ++ [c]) (polyEval msg c))
          ((overE 2 : ℝ≥0) : ℝ≥0∞)
          fun q hq ↦ sumAlive_escape Φ H S G xq oq (by simp at hm; omega) hlen hmsg q
            (by have h0 := hw q 0 (by simp); rw [Nat.add_zero] at h0; exact h0) hq).mono
            (fun _ (h : MsgOk eq claim msg ∧ _) ↦ h.2) (fun _ _ h ↦ h) le_rfl
          le_rfl le_rfl).bind' fun c ↦
          (sumcheckSpec hst hcard Φ H S G xq oq hε eqs eq' (j + 1) (chis ++ [c])
            (polyEval msg c) (by simp [hlen]) (by simp at hm ⊢; omega)
            (fun q k hk ↦ by
              have := hw q (k + 1) (by simp at hk ⊢; omega)
              rw [show j + 1 + k = j + (k + 1) by omega, this]
              rfl)).bind' fun
              | ⟨pt, fin⟩ => (Spec.ret (c :: pt, fin)).mono (fun _ h ↦ by
                  obtain ⟨hl, hd⟩ := h
                  refine ⟨by simp [hl], ?_⟩
                  have e1 : j + 1 + eqs.length + 1 = j + (eq' :: eqs).length + 1 := by
                    simp only [List.length_cons]
                    omega
                  rw [e1] at hd
                  simpa using hd) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h ↦ hmsg h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The rounds' specification on a list of rounds**: `sumcheckSpec` for a nonempty list,
the stage after the rounds `j + |eqs|`. -/
noncomputable def sumcheckSpecL (hst : Stable C) (hcard : ∀ h, (C h).ncard ≤ L₀)
    (Φ : Family E X O Unit 2) {m : ℕ} (H : Φ.Consistent m) (S : Φ.Sound m)
    (G : β → Prop) (xq : β → X) (oq : β → ∀ i, O i)
    (hε : (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + T ≤ εmax) (j : ℕ) (chis : List E) (claim : E)
    (hlen : chis.length = j) :
    (eqs : List (Option E)) → eqs ≠ [] → j + eqs.length ≤ m →
      (∀ q (k : ℕ) (hk : k < eqs.length), Φ.weight (xq q) (j + k) = domOf eqs[k]) →
      Spec (sumcheck claim 3 eqs) (Doomed C (SumAlive Φ G xq oq j chis claim))
        (fun pf h ↦ pf.1.length = eqs.length ∧
          Doomed C (SumAlive Φ G xq oq (j + eqs.length) (chis ++ pf.1) pf.2) h) εmax 0 T
  | eq :: eqs, _, hm, hw =>
    (sumcheckSpec hst hcard Φ H S G xq oq hε eqs eq j chis claim hlen
      (by simp at hm; omega) hw).mono (fun _ h ↦ h) (fun pf h hh ↦ by
        refine ⟨by simpa using hh.1, ?_⟩
        have e : j + eqs.length + 1 = j + (eq :: eqs).length := by simp; omega
        rw [← e]
        exact hh.2) le_rfl le_rfl le_rfl

end
end LeanVM.Protocol.EndToEnd.Front
