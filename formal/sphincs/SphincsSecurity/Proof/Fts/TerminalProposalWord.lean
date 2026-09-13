import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalBridgeKernel
namespace SphincsSecurity.Concrete

open ENNReal

noncomputable def completeProposalWord {α : Type*} (base : PMF α) : Nat → List α → PMF (List α)
  | 0, _ => PMF.pure []
  | total + 1, [] => independentProposalWord base (total + 1)
  | total + 1, head :: rest => (completeProposalWord base total rest).map (head :: ·)

theorem completeProposalWord_nil {α : Type*} (base : PMF α) (total : Nat) :
    completeProposalWord base total [] = independentProposalWord base total := by
  cases total <;> rfl

theorem completeProposalWord_eq_padding {α : Type*} (base : PMF α) (total : Nat) (consumed : List α) :
    completeProposalWord base total consumed =
      (independentProposalWord base (total - consumed.length)).map (fun word => consumed.take total ++ word) := by
  induction consumed generalizing total with
  | nil =>
      simp only [completeProposalWord_nil, List.length_nil, Nat.sub_zero, List.take_nil, List.nil_append]
      exact (PMF.map_id _).symm
  | cons head rest ih =>
      cases total with
      | zero => simp only [completeProposalWord, Nat.zero_sub, independentProposalWord,
          PMF.monad_pure_eq_pure, PMF.pure_map, List.take_zero, List.nil_append]
      | succ total =>
          rw [completeProposalWord, ih, PMF.map_comp]
          simp only [List.length_cons, Nat.succ_sub_succ_eq_sub, List.take_succ_cons]
          rfl

theorem complete_cappedRecordProposalBridge {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (total : Nat) :
    (cappedRecordProposalBridge base record label accept hpos hlt hcap).bind
        (fun result => completeProposalWord base total (result.1 ++ [label result.2])) =
      independentProposalWord base total := by
  induction total with
  | zero => simp only [completeProposalWord, PMF.bind_const, independentProposalWord, PMF.monad_pure_eq_pure]
  | succ total ih =>
      rw [cappedRecordProposalBridge_step, PMF.bind_bind]
      have hbranch (branch : α ⊕ Ω) :
          (proposalBridgeContinuation (cappedRecordProposalBridge base record label accept hpos hlt hcap) branch).bind
              (fun result => completeProposalWord base (total + 1) (result.1 ++ [label result.2])) =
            (independentProposalWord base total).map (Sum.elim id label branch :: ·) := by
        cases branch with
        | inl head =>
            rw [proposalBridgeContinuation, PMF.bind_map]
            change (cappedRecordProposalBridge base record label accept hpos hlt hcap).bind
                (fun result => (completeProposalWord base total (result.1 ++ [label result.2])).map (head :: ·)) = _
            rw [← PMF.map_bind, ih]
            rfl
        | inr outcome =>
            simp only [proposalBridgeContinuation, PMF.pure_bind, List.nil_append,
              completeProposalWord, completeProposalWord_nil, Sum.elim_inr]
      simp_rw [hbranch]
      change (proposalRecordStep base record label accept hlt hcap).bind
          ((fun index => (independentProposalWord base total).map (index :: ·)) ∘ Sum.elim id label) = _
      rw [← PMF.bind_map, proposalRecordStep_label]
      rfl

theorem complete_cappedRecordProposalBridge_prefix {α Ω : Type*} (base : PMF α) (record : PMF Ω) (label : Ω → α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hlt : accept < 1)
    (hcap : ∀ index, accept * (record.map label) index ≤ base index) (total : Nat) (consumed : List α) :
    (cappedRecordProposalBridge base record label accept hpos hlt hcap).bind
        (fun result => completeProposalWord base total (consumed ++ (result.1 ++ [label result.2]))) =
      completeProposalWord base total consumed := by
  induction consumed generalizing total with
  | nil =>
      simpa only [List.nil_append, completeProposalWord_nil] using
        complete_cappedRecordProposalBridge base record label accept hpos hlt hcap total
  | cons head rest ih =>
      cases total with
      | zero => simp only [completeProposalWord, PMF.bind_const]
      | succ total =>
          simp only [List.cons_append, completeProposalWord]
          rw [← PMF.map_bind, ih]

end SphincsSecurity.Concrete
