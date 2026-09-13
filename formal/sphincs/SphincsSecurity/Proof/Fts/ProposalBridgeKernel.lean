import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalWordDistribution
namespace SphincsSecurity.Concrete

open ENNReal
attribute [local instance] Classical.propDecidable

theorem proposalResidual_sum {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hcap : ∀ index : α, accept * target index ≤ base index) :
    (∑' index : α, (base index - accept * target index)) = 1 - accept := by
  apply ENNReal.eq_sub_of_add_eq' (by finiteness)
  calc
    _ = ∑' index : α, ((base index - accept * target index) + accept * target index) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, target.tsum_coe, mul_one]
    _ = ∑' index, base index := tsum_congr (fun index => tsub_add_cancel_of_le (hcap index))
    _ = 1 := base.tsum_coe

noncomputable def proposalResidualLaw {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hlt : accept < 1) (hcap : ∀ index, accept * target index ≤ base index) : PMF α :=
  PMF.normalize (fun index => base index - accept * target index)
    (by rw [proposalResidual_sum base target accept hcap]; exact ne_of_gt (tsub_pos_iff_lt.mpr hlt))
    (by rw [proposalResidual_sum base target accept hcap]; finiteness)

theorem proposalResidualLaw_apply {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hlt : accept < 1) (hcap : ∀ index, accept * target index ≤ base index) (index : α) :
    proposalResidualLaw base target accept hlt hcap index =
      (base index - accept * target index) * (1 - accept)⁻¹ := by
  simp only [proposalResidualLaw, PMF.normalize_apply, proposalResidual_sum base target accept hcap]

theorem proposalResidualLaw_scaled {α : Type*} (base target : PMF α) (accept : ENNReal)
    (hlt : accept < 1) (hcap : ∀ index, accept * target index ≤ base index) (index : α) :
    (1 - accept) * proposalResidualLaw base target accept hlt hcap index = base index - accept * target index := by
  rw [proposalResidualLaw_apply]
  calc
    _ = (base index - accept * target index) * ((1 - accept) * (1 - accept)⁻¹) := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (ne_of_gt (tsub_pos_iff_lt.mpr hlt)) (by finiteness), mul_one]

noncomputable def proposalAcceptanceCoin (accept : ENNReal) (hle : accept ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun accepted => if accepted then accept else 1 - accept) (by
    simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
    exact (add_comm _ _).trans (tsub_add_cancel_of_le hle))

theorem proposalAcceptanceCoin_bind_apply {Ω : Type*} (accept : ENNReal) (hle : accept ≤ 1)
    (continuation : Bool → PMF Ω) (outcome : Ω) :
    (proposalAcceptanceCoin accept hle).bind continuation outcome =
      (1 - accept) * continuation false outcome + accept * continuation true outcome := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [Fintype.sum_bool, proposalAcceptanceCoin, PMF.ofFintype_apply, Bool.false_eq_true, if_false, if_true]
  exact add_comm _ _

noncomputable def proposalRecordStep {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) : PMF (α ⊕ Ω) :=
  (proposalAcceptanceCoin accept hlt.le).bind fun accepted =>
    if accepted then record.map Sum.inr
    else (proposalResidualLaw base (record.map label) accept hlt hcap).map Sum.inl

theorem proposalRecordStep_reject {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) (index : α) :
    proposalRecordStep base record label accept hlt hcap (.inl index) = base index - accept * (record.map label) index := by
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq Ω := Classical.decEq Ω
  rw [proposalRecordStep, proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true, PMF.map_apply, Sum.inl.injEq, Sum.inl_ne_inr,
    tsum_ite_eq', if_false, tsum_zero, mul_zero, add_zero, proposalResidualLaw_scaled]

theorem proposalRecordStep_accept {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) (outcome : Ω) :
    proposalRecordStep base record label accept hlt hcap (.inr outcome) = accept * record outcome := by
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq Ω := Classical.decEq Ω
  rw [proposalRecordStep, proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true, PMF.map_apply, Sum.inr.injEq, Sum.inr_ne_inl,
    tsum_ite_eq', if_false, tsum_zero, mul_zero, zero_add]

theorem proposalRecordStep_label {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hlt : accept < 1) (hcap : ∀ index, accept * (record.map label) index ≤ base index) :
    (proposalRecordStep base record label accept hlt hcap).map (Sum.elim id label) = base := by
  unfold proposalRecordStep
  rw [PMF.map_bind]
  have hbranch (accepted : Bool) :
      (if accepted then record.map Sum.inr
        else (proposalResidualLaw base (record.map label) accept hlt hcap).map Sum.inl).map (Sum.elim id label) =
      if accepted then record.map label else proposalResidualLaw base (record.map label) accept hlt hcap := by
    cases accepted <;> simp only [Bool.false_eq_true, if_false, if_true, PMF.map_comp, Function.comp_def, Sum.elim_inl,
      Sum.elim_inr, id_eq]
    exact PMF.map_id _
  simp_rw [hbranch]
  ext index
  rw [proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true, proposalResidualLaw_scaled, tsub_add_cancel_of_le (hcap index)]

noncomputable def cappedRecordProposalBridge {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) : PMF (List α × Ω) :=
  recordProposalBridge record (proposalResidualLaw base (record.map label) accept hlt hcap) accept hpos hlt.le

theorem cappedRecordProposalBridge_nil {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (outcome : Ω) :
    cappedRecordProposalBridge base record label accept hpos hlt hcap ([], outcome) =
      proposalRecordStep base record label accept hlt hcap (.inr outcome) := by
  rw [cappedRecordProposalBridge, recordProposalBridge_nil, proposalRecordStep_accept]

theorem cappedRecordProposalBridge_cons {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (head : α) (rest : List α) (outcome : Ω) :
    cappedRecordProposalBridge base record label accept hpos hlt hcap (head :: rest, outcome) =
      proposalRecordStep base record label accept hlt hcap (.inl head) *
        cappedRecordProposalBridge base record label accept hpos hlt hcap (rest, outcome) := by
  rw [cappedRecordProposalBridge, recordProposalBridge_cons, proposalResidualLaw_scaled, proposalRecordStep_reject]

def prependProposalRecord {α Ω : Type*} (head : α) (result : List α × Ω) : List α × Ω :=
  (head :: result.1, result.2)

private theorem prependProposalRecord_apply {α Ω : Type*} [DecidableEq α]
    (law : PMF (List α × Ω)) (head : α) (word : List α) (outcome : Ω) :
    (law.map (prependProposalRecord head)) (word, outcome) =
      match word with
      | [] => 0
      | next :: rest => if next = head then law (rest, outcome) else 0 := by
  cases word with
  | nil =>
      apply pmf_map_apply_zero_of_not_image
      intro source heq
      have h := congrArg Prod.fst heq
      change [] = head :: source.1 at h
      cases h
  | cons next rest =>
      change (law.map (prependProposalRecord head)) (next :: rest, outcome) =
        if next = head then law (rest, outcome) else 0
      by_cases h : next = head
      · subst next
        rw [if_pos rfl]
        apply pmf_map_injective_apply law (prependProposalRecord head) _ (rest, outcome)
        intro left right h
        have hfirst := congrArg Prod.fst h
        have hsecond := congrArg Prod.snd h
        change head :: left.1 = head :: right.1 at hfirst
        change left.2 = right.2 at hsecond
        exact Prod.ext (List.cons.inj hfirst).2 hsecond
      · rw [if_neg h]
        exact pmf_map_apply_zero_of_not_image _ _ _
          (fun source heq => h (List.cons.inj (congrArg Prod.fst heq)).1)

noncomputable def proposalBridgeContinuation {α Ω : Type*} (law : PMF (List α × Ω)) : α ⊕ Ω → PMF (List α × Ω)
  | .inl head => law.map (prependProposalRecord head)
  | .inr outcome => PMF.pure ([], outcome)

theorem cappedRecordProposalBridge_step {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) :
    cappedRecordProposalBridge base record label accept hpos hlt hcap =
      (proposalRecordStep base record label accept hlt hcap).bind
        (proposalBridgeContinuation (cappedRecordProposalBridge base record label accept hpos hlt hcap)) := by
  letI : DecidableEq α := Classical.decEq α
  let law := cappedRecordProposalBridge base record label accept hpos hlt hcap
  let rejected := proposalResidualLaw base (record.map label) accept hlt hcap
  have hexpand : (proposalRecordStep base record label accept hlt hcap).bind (proposalBridgeContinuation law) =
      (proposalAcceptanceCoin accept hlt.le).bind (fun accepted =>
        if accepted then record.map (fun outcome => ([], outcome))
        else rejected.bind (fun head => law.map (prependProposalRecord head))) := by
    rw [proposalRecordStep, PMF.bind_bind]
    apply congrArg (PMF.bind (proposalAcceptanceCoin accept hlt.le))
    funext accepted
    cases accepted <;> simp only [Bool.false_eq_true, if_false, if_true, PMF.bind_map,
      Function.comp_def, proposalBridgeContinuation]
    all_goals rfl
  change law = _
  rw [hexpand]
  ext result
  rcases result with ⟨word, outcome⟩
  rw [proposalAcceptanceCoin_bind_apply]
  simp only [Bool.false_eq_true, if_false, if_true]
  have hrej : (rejected.bind (fun head => law.map (prependProposalRecord head))) (word, outcome) =
      match word with
      | [] => 0
      | next :: rest => rejected next * law (rest, outcome) := by
    rw [PMF.bind_apply]
    simp only [prependProposalRecord_apply]
    cases word <;> simp only [mul_zero, tsum_zero, mul_ite, tsum_ite_eq']
  rw [hrej]
  cases word with
  | nil =>
      rw [pmf_map_injective_apply record (fun outcome => ([], outcome))
        (fun _ _ h => congrArg Prod.snd h) outcome, mul_zero, zero_add]
      exact (cappedRecordProposalBridge_nil base record label accept hpos hlt hcap outcome).trans
        (proposalRecordStep_accept base record label accept hlt hcap outcome)
  | cons head rest =>
      have hacc : (record.map (fun outcome => ([], outcome))) (head :: rest, outcome) = 0 :=
        pmf_map_apply_zero_of_not_image _ _ _ (fun _ heq => by
          have h := congrArg Prod.fst heq
          change head :: rest = [] at h
          cases h)
      rw [hacc, mul_zero, add_zero]
      change cappedRecordProposalBridge base record label accept hpos hlt hcap (head :: rest, outcome) = _
      rw [cappedRecordProposalBridge_cons, proposalRecordStep_reject, ← proposalResidualLaw_scaled base (record.map label) accept hlt hcap head]
      exact mul_assoc _ _ _

end SphincsSecurity.Concrete
