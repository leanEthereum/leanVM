import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.SigningProposalRecord
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem independentProposalWord_length {α : Type*} (law : PMF α) (steps : Nat) :
    (independentProposalWord law steps).map List.length = PMF.pure steps := by
  induction steps with
  | zero => exact PMF.pure_map _ _
  | succ steps ih =>
      rw [independentProposalWord, PMF.map_bind]
      have hbranch (head : α) :
          ((independentProposalWord law steps).map (head :: ·)).map List.length =
            PMF.pure (steps + 1) := by
        calc
          _ = ((independentProposalWord law steps).map List.length).map Nat.succ := by
            rw [PMF.map_comp, PMF.map_comp]
            rfl
          _ = _ := by rw [ih, PMF.pure_map]
      simp_rw [hbranch]
      exact PMF.bind_const _ _

theorem rejectedProposalWord_length {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map List.length =
      proposalFailureCount accept hpos hle := by
  rw [rejectedProposalWord, PMF.map_bind]
  simp_rw [independentProposalWord_length]
  exact PMF.bind_pure _

noncomputable def proposalBlockLength (accept : ENNReal) (hpos : accept ≠ 0)
    (hle : accept ≤ 1) : PMF Nat :=
  (proposalFailureCount accept hpos hle).map Nat.succ

theorem proposalBlockLength_zero (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    proposalBlockLength accept hpos hle 0 = 0 :=
  pmf_map_apply_zero_of_not_image _ _ _ (fun _ => Nat.zero_ne_add_one _)

theorem proposalBlockLength_succ (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1)
    (failures : Nat) :
    proposalBlockLength accept hpos hle (failures + 1) = accept * (1 - accept) ^ failures :=
  (pmf_map_injective_apply _ _ Nat.succ_injective failures).trans rfl

theorem rejectedProposalWord_blockLength {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (rejectedProposalWord law accept hpos hle).map (fun word => word.length + 1) =
      proposalBlockLength accept hpos hle := by
  change _ = ((proposalFailureCount accept hpos hle).map Nat.succ)
  rw [← rejectedProposalWord_length law accept hpos hle, PMF.map_comp]
  rfl

noncomputable def recordLengthBridge {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (Nat × Ω) :=
  record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (fun length => (length, outcome))

theorem recordProposalBridge_length_record {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordProposalBridge record rejected accept hpos hle).map
      (fun result => (result.1.length + 1, result.2)) = recordLengthBridge record accept hpos hle := by
  rw [recordProposalBridge, PMF.map_bind]
  have hbranch (outcome : Ω) :
      ((rejectedProposalWord rejected accept hpos hle).map (fun word => (word, outcome))).map
        (fun result => (result.1.length + 1, result.2)) =
      (proposalBlockLength accept hpos hle).map (fun length => (length, outcome)) := by
    rw [← rejectedProposalWord_blockLength rejected accept hpos hle, PMF.map_comp, PMF.map_comp]
    rfl
  simp_rw [hbranch]
  rfl

theorem recordLengthBridge_record {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.snd = record := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun outcome =>
    (proposalBlockLength accept hpos hle).map (Function.const Nat outcome)) = record
  simp only [PMF.map_const, PMF.bind_pure]

theorem recordLengthBridge_length {Ω : Type*} (record : PMF Ω)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordLengthBridge record accept hpos hle).map Prod.fst = proposalBlockLength accept hpos hle := by
  rw [recordLengthBridge, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun _ => (proposalBlockLength accept hpos hle).map id) = _
  rw [PMF.map_id, PMF.bind_const]

end SphincsSecurity.Concrete
