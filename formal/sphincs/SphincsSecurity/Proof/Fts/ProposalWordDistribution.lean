import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity.Concrete

open ENNReal
attribute [local instance] Classical.propDecidable

theorem pmf_map_injective_apply {α β : Type*} (law : PMF α) (f : α → β)
    (hinjective : Function.Injective f) (value : α) : (law.map f) (f value) = law value := by
  rw [PMF.map_apply, tsum_eq_single value]
  · simp only [↓reduceIte]
  · intro other hne
    exact if_neg (fun h => hne (hinjective h).symm)

theorem pmf_map_apply_zero_of_not_image {α β : Type*} (law : PMF α) (f : α → β) (value : β)
    (h : ∀ source, value ≠ f source) : (law.map f) value = 0 := by
  letI : DecidableEq β := Classical.decEq β
  rw [PMF.map_apply]
  exact (tsum_congr (fun source => if_neg (h source))).trans tsum_zero

noncomputable def independentProposalWord {α : Type*} (law : PMF α) : Nat → PMF (List α)
  | 0 => pure []
  | steps + 1 => law.bind fun next => (independentProposalWord law steps).map (next :: ·)

theorem independentProposalWord_apply {α : Type*} (law : PMF α) (steps : Nat) (word : List α) :
    independentProposalWord law steps word = if word.length = steps then (word.map law).prod else 0 := by
  classical
  letI : DecidableEq α := Classical.decEq α
  induction steps generalizing word with
  | zero => cases word <;> simp [independentProposalWord, PMF.pure_apply]
  | succ steps ih =>
      cases word with
      | nil => simp [independentProposalWord, PMF.bind_apply, PMF.map_apply]
      | cons next rest =>
          rw [independentProposalWord, PMF.bind_apply]
          have hm (head : α) : ((independentProposalWord law steps).map (head :: ·)) (next :: rest) =
              if next = head then independentProposalWord law steps rest else 0 := by
            by_cases h : next = head
            · subst next
              rw [if_pos rfl]
              exact pmf_map_injective_apply _ _ (fun _ _ h => (List.cons.inj h).2) rest
            · rw [if_neg h]
              exact pmf_map_apply_zero_of_not_image _ _ _ (fun _ heq => h (List.cons.inj heq).1)
          simp only [hm, tsum_ite_eq', mul_ite, mul_zero, ih, List.length_cons,
            Nat.add_right_cancel_iff, List.map_cons, List.prod_cons]

noncomputable def proposalFailureCount (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF Nat :=
  ⟨fun count => accept * (1 - accept) ^ count, by
    apply ENNReal.summable.hasSum_iff.mpr
    have hdouble : 1 - (1 - accept) = accept :=
      ENNReal.sub_eq_of_eq_add_rev' (by finiteness) (tsub_add_cancel_of_le hle).symm
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, hdouble,
      ENNReal.mul_inv_cancel hpos (ne_top_of_le_ne_top (by finiteness) hle)]⟩

theorem proposalFailureCount_apply (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (count : Nat) :
    proposalFailureCount accept hpos hle count = accept * (1 - accept) ^ count := rfl

noncomputable def rejectedProposalWord {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (List α) :=
  (proposalFailureCount accept hpos hle).bind (independentProposalWord law)

theorem rejectedProposalWord_apply {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (word : List α) :
    rejectedProposalWord law accept hpos hle word =
      accept * (1 - accept) ^ word.length * (word.map law).prod := by
  classical
  simp only [rejectedProposalWord, PMF.bind_apply, independentProposalWord_apply, mul_ite, mul_zero,
    tsum_ite_eq', proposalFailureCount_apply]

theorem rejectedProposalWord_nil {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    rejectedProposalWord law accept hpos hle [] = accept := by
  simp only [rejectedProposalWord_apply, List.length_nil, pow_zero, List.map_nil, List.prod_nil, mul_one]

theorem rejectedProposalWord_cons {α : Type*} (law : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (next : α) (rest : List α) :
    rejectedProposalWord law accept hpos hle (next :: rest) =
      (1 - accept) * law next * rejectedProposalWord law accept hpos hle rest := by
  simp only [rejectedProposalWord_apply, List.length_cons, pow_succ, List.map_cons, List.prod_cons]
  ring

noncomputable def recordProposalBridge {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) : PMF (List α × Ω) :=
  record.bind fun outcome => (rejectedProposalWord rejected accept hpos hle).map (fun word => (word, outcome))

theorem recordProposalBridge_apply {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (word : List α) (outcome : Ω) :
    recordProposalBridge record rejected accept hpos hle (word, outcome) =
      record outcome * rejectedProposalWord rejected accept hpos hle word := by
  classical
  letI : DecidableEq Ω := Classical.decEq Ω
  rw [recordProposalBridge, PMF.bind_apply]
  have hm (value : Ω) :
      ((rejectedProposalWord rejected accept hpos hle).map (fun word => (word, value))) (word, outcome) =
        if outcome = value then rejectedProposalWord rejected accept hpos hle word else 0 := by
    by_cases h : outcome = value
    · subst outcome
      rw [if_pos rfl]
      exact pmf_map_injective_apply _ _ (fun _ _ h => (Prod.mk.inj h).1) word
    · rw [if_neg h]
      exact pmf_map_apply_zero_of_not_image _ _ _ (fun _ heq => h (Prod.mk.inj heq).2)
  simp only [hm, mul_ite, mul_zero, tsum_ite_eq']

theorem recordProposalBridge_record {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) :
    (recordProposalBridge record rejected accept hpos hle).map Prod.snd = record := by
  unfold recordProposalBridge
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (record.bind fun outcome =>
    (rejectedProposalWord rejected accept hpos hle).map (Function.const (List α) outcome)) = record
  simp only [PMF.map_const, PMF.bind_pure]

theorem recordProposalBridge_nil {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (outcome : Ω) :
    recordProposalBridge record rejected accept hpos hle ([], outcome) = accept * record outcome := by
  rw [recordProposalBridge_apply, rejectedProposalWord_nil, mul_comm]

theorem recordProposalBridge_cons {α Ω : Type*} (record : PMF Ω) (rejected : PMF α)
    (accept : ENNReal) (hpos : accept ≠ 0) (hle : accept ≤ 1) (next : α) (rest : List α) (outcome : Ω) :
    recordProposalBridge record rejected accept hpos hle (next :: rest, outcome) =
      (1 - accept) * rejected next * recordProposalBridge record rejected accept hpos hle (rest, outcome) := by
  rw [recordProposalBridge_apply, recordProposalBridge_apply, rejectedProposalWord_cons]
  ring

end SphincsSecurity.Concrete
