import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalLengthProjection
import SphincsSecurity.Proof.Residual.RetainedObservation
import SphincsSecurity.Proof.Fts.TerminalProposalWord
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp ENNReal
set_option backward.isDefEq.respectTransparency false

theorem pmfLift_map {Result Other : Type} (law : PMF Result) (f : Result → Other) :
    (liftM (law.map f) : SPMF Other) = f <$> (liftM law : SPMF Result) := by
  rw [← PMF.monad_map_eq_map]
  exact liftM_map _ _

theorem pmfLift_bind {Result Other : Type} (law : PMF Result) (next : Result → PMF Other) :
    (liftM (law.bind next) : SPMF Other) = ((liftM law : SPMF Result) >>= fun result => liftM (next result)) := by
  rw [← PMF.monad_bind_eq_bind]
  exact liftM_bind _ _

noncomputable def attachRejectedWord {Result : Type} (law : SPMF Result) (rejected : PMF Index) :
    SPMF (List Index × Result) :=
  law >>= fun result => (fun word => (word, result)) <$>
    (liftM (rejectedProposalWord rejected targetProposalAcceptance targetProposalAcceptance_ne_zero
      targetProposalAcceptance_lt_one.le) : SPMF (List Index))

theorem attachRejectedWord_record {Result : Type} (law : SPMF Result) (rejected : PMF Index) :
    Prod.snd <$> attachRejectedWord law rejected = law := by
  rw [attachRejectedWord, map_bind]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    RetainedObservation.lift_bind_const, bind_pure]

theorem attachRejectedWord_lift {Result : Type} (law : PMF Result) (rejected : PMF Index) :
    attachRejectedWord (liftM law) rejected =
      (liftM (recordProposalBridge law rejected targetProposalAcceptance targetProposalAcceptance_ne_zero
        targetProposalAcceptance_lt_one.le) : SPMF (List Index × Result)) := by
  rw [attachRejectedWord, recordProposalBridge, pmfLift_bind]
  simp only [pmfLift_map]

theorem attachRejectedWord_length {Result : Type} (law : SPMF Result) (rejected : PMF Index) :
    (fun result => (result.1.length + 1, result.2)) <$> attachRejectedWord law rejected =
      ((liftM (proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero
          targetProposalAcceptance_lt_one.le) : SPMF Nat) >>= fun length =>
        (fun result => (length, result)) <$> law) := by
  rw [attachRejectedWord, map_bind]
  have hword (result : Result) :
      (fun item : List Index × Result => (item.1.length + 1, item.2)) <$>
          ((fun word => (word, result)) <$>
            (liftM (rejectedProposalWord rejected targetProposalAcceptance targetProposalAcceptance_ne_zero
              targetProposalAcceptance_lt_one.le) : SPMF (List Index))) =
        (fun length => (length, result)) <$>
          (liftM (proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero
            targetProposalAcceptance_lt_one.le) : SPMF Nat) := by
    rw [Functor.map_map]
    calc
      _ = (fun length => (length, result)) <$>
          ((fun word : List Index => word.length + 1) <$>
            (liftM (rejectedProposalWord rejected targetProposalAcceptance targetProposalAcceptance_ne_zero
              targetProposalAcceptance_lt_one.le) : SPMF (List Index))) := by rw [Functor.map_map]
      _ = _ := by
        rw [← pmfLift_map, rejectedProposalWord_blockLength]
  simp_rw [hword]
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  exact RetainedObservation.bind_comm _ _ _

theorem attachRejectedWord_complete {Result Original : Type}
    (law : SPMF Result) (label : Result → Index) (record : PMF Original) (originalLabel : Original → Index)
    (hindex : label <$> law = (liftM (record.map originalLabel) : SPMF Index))
    (hcap : ∀ index, targetProposalAcceptance * (record.map originalLabel) index ≤ PMF.uniformOfFintype Index index)
    (total : Nat) (consumed : List Index) :
    (attachRejectedWord law
      (proposalResidualLaw (PMF.uniformOfFintype Index) (record.map originalLabel) targetProposalAcceptance
        targetProposalAcceptance_lt_one hcap) >>= fun result =>
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total
        (consumed ++ (result.1 ++ [label result.2]))) : SPMF (List Index))) =
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total consumed) : SPMF (List Index)) := by
  let rejected := proposalResidualLaw (PMF.uniformOfFintype Index) (record.map originalLabel) targetProposalAcceptance
    targetProposalAcceptance_lt_one hcap
  have hproject :
      (attachRejectedWord law rejected >>= fun result =>
        (liftM (completeProposalWord (PMF.uniformOfFintype Index) total
          (consumed ++ (result.1 ++ [label result.2]))) : SPMF (List Index))) =
      (attachRejectedWord (liftM record) rejected >>= fun result =>
        (liftM (completeProposalWord (PMF.uniformOfFintype Index) total
          (consumed ++ (result.1 ++ [originalLabel result.2]))) : SPMF (List Index))) := by
    simp only [attachRejectedWord, bind_assoc, bind_map_left]
    calc
      _ = (label <$> law) >>= fun index =>
          (liftM (rejectedProposalWord rejected targetProposalAcceptance targetProposalAcceptance_ne_zero
            targetProposalAcceptance_lt_one.le) : SPMF (List Index)) >>= fun word =>
              (liftM (completeProposalWord (PMF.uniformOfFintype Index) total
                (consumed ++ (word ++ [index]))) : SPMF (List Index)) := by rw [bind_map_left]
      _ = _ := by rw [hindex, pmfLift_map, bind_map_left]
  change (attachRejectedWord law rejected >>= _) = _
  rw [hproject, attachRejectedWord_lift, ← pmfLift_bind]
  change (liftM ((cappedRecordProposalBridge (PMF.uniformOfFintype Index) record originalLabel
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one hcap).bind
      (fun result => completeProposalWord (PMF.uniformOfFintype Index) total
        (consumed ++ (result.1 ++ [originalLabel result.2])))) : SPMF (List Index)) = _
  rw [complete_cappedRecordProposalBridge_prefix]

end SphincsSecurity.Concrete.RetainedResidual
