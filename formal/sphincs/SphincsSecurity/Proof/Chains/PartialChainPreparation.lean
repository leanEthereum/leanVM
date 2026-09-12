import SphincsSecurity.Proof.Chains.PartialChainLongCompletion
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State]

noncomputable def queriedInputs (row : State → Option State) : Finset State :=
  Finset.univ.filter fun input => row input ≠ none

noncomputable def rowImage (row : State → Option State) : Finset State :=
  Finset.univ.biUnion fun input => (row input).toFinset

omit [DecidableEq State] in
theorem mem_queriedInputs (row : State → Option State) (input : State) :
    input ∈ queriedInputs row ↔ row input ≠ none := by simp [queriedInputs]

omit [DecidableEq State] in
theorem queriedInputs_card (row : State → Option State) : (queriedInputs row).card = queriedCount row := by
  rw [queriedInputs, Finset.card_filter, queriedCount_eq_sum]
  apply Finset.sum_congr rfl
  intro input _
  cases row input <;> simp

theorem mem_rowImage (row : State → Option State) (output : State) :
    output ∈ rowImage row ↔ ∃ input, row input = some output := by
  simp only [rowImage, Finset.mem_biUnion, Finset.mem_univ, true_and, Option.mem_toFinset, Option.mem_def]

theorem rowImage_card_le (row : State → Option State) : (rowImage row).card ≤ queriedCount row := by
  apply Finset.card_biUnion_le.trans
  rw [queriedCount_eq_sum]
  apply Finset.sum_le_sum
  intro input _
  cases row input <;> simp

noncomputable def productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) : Finset State :=
  queriedInputs (observed (Fin.last (n + 1))) ∩ rowImage (observed (Fin.last n).castSucc)

noncomputable def preparationCount {n : Nat} (observed : Fin (n + 2) → State → Option State) : Nat :=
  (productiveInputs observed).card

theorem mem_productiveInputs {n : Nat} (observed : Fin (n + 2) → State → Option State) (input : State) :
    input ∈ productiveInputs observed ↔
      observed (Fin.last (n + 1)) input ≠ none ∧ ∃ start, observed (Fin.last n).castSucc start = some input := by
  simp only [productiveInputs, Finset.mem_inter, mem_queriedInputs, mem_rowImage]

theorem productiveInputs_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    productiveInputs before ⊆ productiveInputs after := by
  intro input hi
  rw [mem_productiveInputs] at hi ⊢
  constructor
  · cases hr : before (Fin.last (n + 1)) input with
    | none => exact False.elim (hi.1 hr)
    | some answer => rw [h _ _ _ hr]; exact Option.some_ne_none answer
  · obtain ⟨start, hs⟩ := hi.2
    exact ⟨start, h _ _ _ hs⟩

theorem preparationCount_mono {n : Nat} {before after : Fin (n + 2) → State → Option State} (h : Extends before after) :
    preparationCount before ≤ preparationCount after := Finset.card_le_card (productiveInputs_mono h)

theorem preparationCount_le_last {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last (n + 1))) := by
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (queriedInputs_card _)

theorem preparationCount_le_penultimate {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queriedCount (observed (Fin.last n).castSucc) := by
  exact (Finset.card_le_card Finset.inter_subset_right).trans (rowImage_card_le _)

theorem preparationCount_le_prefix {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    preparationCount observed ≤ queryCount (Fin.init observed) := by
  apply (preparationCount_le_penultimate observed).trans
  change queriedCount ((Fin.init observed) (Fin.last n)) ≤ ∑ step, queriedCount ((Fin.init observed) step)
  exact Finset.single_le_sum (f := fun step => queriedCount ((Fin.init observed) step))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.last n))

theorem preparationCount_empty {n : Nat} : preparationCount (n := n) (fun (_ : Fin (n + 2)) (_ : State) => none) = 0 := by
  simp [preparationCount, productiveInputs, queriedInputs]

theorem preparationCount_last_fresh {n : Nat} (observed : Fin (n + 2) → State → Option State) (input answer : State)
    (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    preparationCount observed + 1 ≤ preparationCount (record observed (Fin.last (n + 1), input) answer) := by
  have hnot : input ∉ productiveInputs observed := by simp only [mem_productiveInputs, hfresh, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  have hmem : input ∈ productiveInputs (record observed (Fin.last (n + 1), input) answer) := by
    rw [mem_productiveInputs]
    constructor
    · simp only [record, Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]
    · obtain ⟨start, hs⟩ := hprepared
      refine ⟨start, ?_⟩
      rw [record_at_other observed (Fin.last (n + 1), input) ((Fin.last n).castSucc, start) answer]
      · exact hs
      · intro heq
        have hv := congrArg (fun query => query.1.val) heq
        simp only [Fin.val_castSucc, Fin.val_last] at hv
        omega
  have hsub := productiveInputs_mono (record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh))
  have hcard := Finset.card_le_card (Finset.insert_subset hmem hsub)
  rw [Finset.card_insert_of_notMem hnot] at hcard
  exact hcard

theorem preparation_charge_le_three_halves {n : Nat} (observed : Fin (n + 2) → State → Option State) :
    2 * (longCompleted observed + 2 * preparationCount observed) ≤ 3 * queryCount observed := by
  have hd := longCompleted_le_prefix_queries observed
  have hp := preparationCount_le_prefix observed
  have hl := preparationCount_le_last observed
  rw [queryCount_split_last]
  omega

end SphincsSecurity.Concrete.PartialChainEndpoint
