import SphincsSecurity.Proof.Chains.PartialChainPreparation
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State]

theorem contactCount_mono {n : Nat} {before after : Fin n → State → Option State}
    (h : Extends before after) (endpoint : State) : contactCount before endpoint ≤ contactCount after endpoint := by
  unfold contactCount
  apply Finset.sum_le_sum
  intro query _
  by_cases hk : query.1.val + 1 = n ∧ before query.1 query.2 = some endpoint
  · have hk' : query.1.val + 1 = n ∧ after query.1 query.2 = some endpoint := ⟨hk.1, h _ _ _ hk.2⟩
    simp only [if_pos hk, if_pos hk', le_refl]
  · simp only [if_neg hk, Nat.zero_le]

noncomputable def twoEdgeCharge {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State) (endpoint : State) : Nat :=
  longCompleted observed + 2 * preparationCount observed +
    spent * (contactCount observed endpoint * (contactCount observed endpoint + 2)) +
    contactCount observed endpoint * longCompleted (Fin.init observed)

theorem twoEdgeCharge_empty {n : Nat} (endpoint : State) :
    twoEdgeCharge 0 (n := n) (fun _ _ => none) endpoint = 0 := by
  simp only [twoEdgeCharge, longCompleted_empty, preparationCount_empty, contactCount_empty,
    Nat.mul_zero, Nat.zero_mul, Nat.add_zero]

theorem twoEdgeCharge_mono {n : Nat} {before after : Fin (n + 2) → State → Option State}
    {spent next : Nat} (hs : spent ≤ next) (h : Extends before after) (endpoint : State) :
    twoEdgeCharge spent before endpoint ≤ twoEdgeCharge next after endpoint := by
  unfold twoEdgeCharge
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (longCompleted_mono h) (Nat.mul_le_mul_left 2 (preparationCount_mono h)))
      (Nat.mul_le_mul hs (Nat.mul_le_mul (contactCount_mono h endpoint) (Nat.add_le_add_right (contactCount_mono h endpoint) 2))))
    (Nat.mul_le_mul (contactCount_mono h endpoint) (longCompleted_mono h.init))

private theorem charge_increment (d p r k d' p' r' k' spent dd dp dr : Nat)
    (hd : d + dd ≤ d') (hp : p + dp ≤ p') (hr : r + dr ≤ r') (hk : k ≤ k') :
    (d + 2 * p + spent * (k * (k + 2)) + k * r) + dd + 2 * dp + k * (k + 2) + k * dr ≤
      d' + 2 * p' + (spent + 1) * (k' * (k' + 2)) + k' * r' := by
  have hpoly := Nat.mul_le_mul (Nat.le_refl (spent + 1)) (Nat.mul_le_mul hk (Nat.add_le_add_right hk 2))
  have hprod := Nat.mul_le_mul hk hr
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hd (Nat.mul_le_mul_left 2 hp)) hpoly) hprod
  convert hsum using 1
  ring

theorem twoEdgeCharge_record_last {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last (n + 1)) input = none)
    (hprepared : ∃ start, observed (Fin.last n).castSucc start = some input) :
    twoEdgeCharge spent observed endpoint + (2 + contactCount observed endpoint + targetCount (Fin.init observed) input) ≤
      twoEdgeCharge (spent + 1) (record observed (Fin.last (n + 1), input) answer) endpoint := by
  have hext := record_extends observed (Fin.last (n + 1), input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent (targetCount (Fin.init observed) input) 1 0
    (le_of_eq (longCompleted_record_last observed input answer hfresh).symm)
    (preparationCount_last_fresh observed input answer hfresh hprepared)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext.init) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  have hk : contactCount observed endpoint ≤ contactCount observed endpoint * (contactCount observed endpoint + 2) := by nlinarith
  omega

theorem twoEdgeCharge_record_penultimate {n : Nat} (spent : Nat) (observed : Fin (n + 2) → State → Option State)
    (input answer endpoint : State) (hfresh : observed (Fin.last n).castSucc input = none) :
    twoEdgeCharge spent observed endpoint +
      contactCount observed endpoint * (2 + contactCount observed endpoint + targetCount (Fin.init (Fin.init observed)) input) ≤
      twoEdgeCharge (spent + 1) (record observed ((Fin.last n).castSucc, input) answer) endpoint := by
  have hext := record_extends observed ((Fin.last n).castSucc, input) answer (Or.inl hfresh)
  have h := charge_increment _ _ _ _ _ _ _ _ spent 0 0 (targetCount (Fin.init (Fin.init observed)) input)
    (by simpa only [Nat.add_zero] using longCompleted_mono hext)
    (by simpa only [Nat.add_zero] using preparationCount_mono hext)
    (le_of_eq (longCompleted_prefix_record_penultimate observed input answer hfresh).symm) (contactCount_mono hext endpoint)
  change twoEdgeCharge spent observed endpoint + _ + _ + _ + _ ≤ twoEdgeCharge (spent + 1) _ endpoint at h
  convert h using 1
  ring

theorem contact_correction_identity (k : Nat) : k * (k + 2) + k = contactFactorial k + 4 * k := by
  cases k with
  | zero => rfl
  | succ k => simp only [contactFactorial, Nat.add_sub_cancel]; ring

theorem twoEdgeCharge_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    twoEdgeCharge spent observed endpoint ≤ longCompleted observed + 2 * preparationCount observed +
      budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have hr := longCompleted_le_queryCount (Fin.init observed)
  have hsplit := queryCount_split_last observed
  have hrq : longCompleted (Fin.init observed) ≤ budget := by omega
  have hprod := Nat.mul_le_mul_left (contactCount observed endpoint) hrq
  have hspent := Nat.mul_le_mul_right (contactCount observed endpoint * (contactCount observed endpoint + 2)) hs
  have hsum := Nat.add_le_add hspent hprod
  rw [Nat.mul_comm (contactCount observed endpoint) budget, ← Nat.mul_add, contact_correction_identity] at hsum
  unfold twoEdgeCharge
  omega

theorem twoEdgeCharge_twice_le {n : Nat} (spent budget : Nat) (observed : Fin (n + 2) → State → Option State)
    (endpoint : State) (hs : spent ≤ budget) (hq : queryCount observed ≤ budget) :
    2 * twoEdgeCharge spent observed endpoint ≤ 3 * queryCount observed +
      2 * budget * (contactFactorial (contactCount observed endpoint) + 4 * contactCount observed endpoint) := by
  have h := twoEdgeCharge_le spent budget observed endpoint hs hq
  have hbase := preparation_charge_le_three_halves observed
  nlinarith

end SphincsSecurity.Concrete.PartialChainEndpoint
