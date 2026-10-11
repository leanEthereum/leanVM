import Whir.AnchoredFiatShamirSecurityROM
import Whir.WHIRHeaderRoots

/-! Exact output-run raw fibers. Freshness is checked against chronological raw
answers, not postulated for arbitrary source challenge keys. All other raw
answers and all retained bytes remain in the joint public view. -/
namespace Whir.AnchoredByteStreamGroups
open Concrete FiatShamirGame DuplexFraming DuplexModeGame
open RawOracleCoupling.Concrete AnchoredFiatShamirSecurityCodec
open CommitmentAnchor ParameterBounds
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

structure Run (Q dimension : Nat) (iv : Digest32) where
  history : FramedHistory
  admissible : ∀ i : Fin (blockCount dimension),
    DuplexEncoding.Admissible (⟨history,.output i.val⟩ : Coordinate)
  bounded : ∀ i : Fin (blockCount dimension),
    pathCost (⟨history,.output i.val⟩ : Coordinate) ≤ Q

def coordinate {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv)
    (i : Fin (blockCount dimension)) : Coordinate := ⟨run.history,.output i.val⟩

def key {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv)
    (i : Fin (blockCount dimension)) : RawKey Q :=
  constructionKey Q iv (coordinate run i) (run.bounded i)

theorem key_decodes {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv)
    (i : Fin (blockCount dimension)) :
    WHIRHeaderRoots.decodeRaw iv (key run i) = some (coordinate run i) :=
  WHIRHeaderRoots.decodeRaw_construction iv _ (run.admissible i) (run.bounded i)

theorem key_injective {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv) :
    Function.Injective (key run) := by
  intro i j same
  have h := (key_decodes run i).symm.trans (same ▸ key_decodes run j)
  have hq := Option.some.inj h
  have ht := congrArg Coordinate.terminal hq
  exact Fin.ext (Terminal.output.inj ht)

abbrev Outside {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv) :=
  {raw : RawKey Q // ¬ ∃ i, key run i = raw}

noncomputable def rawParts {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv) :
    (RawKey Q → Digest32) ≃ (Blocks dimension × (Outside run → Digest32)) where
  toFun table := (fun i => table (key run i), fun raw => table raw.val)
  invFun parts := fun raw => if h : ∃ i, key run i = raw then parts.1 (Classical.choose h)
    else parts.2 ⟨raw,h⟩
  left_inv table := by
    funext raw
    dsimp
    split
    · rename_i h
      exact congrArg table (Classical.choose_spec h)
    · rfl
  right_inv parts := by
    classical
    apply Prod.ext
    · funext i
      dsimp
      have h : ∃ j, key run j = key run i := ⟨i,rfl⟩
      simp only [h, dite_true]
      exact congrArg parts.1 (key_injective run (Classical.choose_spec h))
    · funext raw
      dsimp
      simp only [raw.property, dite_false]

noncomputable def jointParts {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv) :
    (RawKey Q → Digest32) ≃ (Joint dimension × (Outside run → Digest32)) :=
  (rawParts run).trans (Equiv.prodCongr (vectorParts dimension) (Equiv.refl _))

/-- No oracle observer is excluded: the point, suffix and complete remaining
raw table are preserved together, including arbitrary known-answer observers. -/
theorem joint_public_average {Q dimension : Nat} {iv : Digest32}
    (run : Run Q dimension iv)
    (payoff : Joint dimension × (Outside run → Digest32) → ℚ) :
    average (fun table : RawKey Q → Digest32 => payoff (jointParts run table)) =
      average payoff := RawOracleCoupling.average_equiv (jointParts run) payoff

abbrev ByteHistory (Q : Nat) := List (RawKey Q × Digest32)

def Fresh {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv)
    (past : ByteHistory Q) : Prop := ∀ i entry, entry ∈ past → key run i ≠ entry.1

noncomputable def eligible {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv)
    (past : ByteHistory Q) : Bool := by
  classical
  exact decide (Fresh run past)

theorem eligible_fresh {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv)
    (past : ByteHistory Q) (checked : eligible run past = true) : Fresh run past := by
  classical
  simpa [eligible] using checked

def agrees {Q : Nat} (past : ByteHistory Q) (table : RawKey Q → Digest32) : Prop :=
  ∀ entry ∈ past, table entry.1 = entry.2

noncomputable def outsideAgrees {Q dimension : Nat} {iv : Digest32}
    (run : Run Q dimension iv) (past : ByteHistory Q) (fresh : Fresh run past)
    (rest : Outside run → Digest32) : Prop :=
  ∀ entry (member : entry ∈ past), rest ⟨entry.1,by
    rintro ⟨i,h⟩
    exact fresh i entry member h⟩ = entry.2

theorem agrees_joint {Q dimension : Nat} {iv : Digest32} (run : Run Q dimension iv)
    (past : ByteHistory Q) (fresh : Fresh run past) (table : RawKey Q → Digest32) :
    agrees past table ↔ outsideAgrees run past fresh (jointParts run table).2 := by
  rfl

/-- Exact causal fiber equality. Conditioning on every chronological raw reply
leaves the joint point and residual uniform, and leaves all other answers
available. The prepare step may use the whole completed history. -/
theorem fresh_history_average {Q dimension : Nat} {iv : Digest32}
    (run : Run Q dimension iv) (past : ByteHistory Q) (checked : eligible run past = true)
    (payoff : Joint dimension → (Outside run → Digest32) → ℚ) :
    average (fun table : RawKey Q → Digest32 =>
      if agrees past table then payoff (jointParts run table).1 (jointParts run table).2 else 0) =
    average (fun rest : Outside run → Digest32 =>
      if outsideAgrees run past (eligible_fresh run past checked) rest then
        average (fun answer : Joint dimension => payoff answer rest) else 0) := by
  classical
  have h := joint_public_average run (fun parts =>
    if outsideAgrees run past (eligible_fresh run past checked) parts.2 then
      payoff parts.1 parts.2 else 0)
  simp only [← agrees_joint] at h
  rw [h, WHIRObservableSecurity.average_product, RawOracleCoupling.average_comm]
  apply congrArg average
  funext rest
  split <;> simp only [average_const]

/-- The source root and lanes are frozen inputs on this fresh chronological
fiber. The same choose-list ambiguity bound applies to real byte-stream points. -/
theorem fresh_group_ambiguity {Q : Nat} {iv : Digest32} (p : Profile)
    (run : Run Q (config p).logN iv) (past : ByteHistory Q)
    (checked : eligible run past = true) (lanes : Nat) (root : CausalGame.BaseOracle)
    (occupied : lanes ≤ 2^(config p).folds[0]!) :
    average (fun table : RawKey Q → Digest32 =>
      if agrees past table ∧ Ambiguous p lanes root (jointParts run table).1.1
      then (1 : ℚ) else 0) ≤
      average (fun table : RawKey Q → Digest32 => if agrees past table then (1 : ℚ) else 0) /
        2^124 := by
  classical
  have badBound : average (fun answer : Joint (config p).logN =>
      if Ambiguous p lanes root answer.1 then (1 : ℚ) else 0) ≤ (1 : ℚ)/2^124 := by
    rw [WHIRObservableSecurity.average_product]
    change average (fun pt : Fin (config p).logN → E =>
      average (fun _ : Residual (config p).logN =>
        if Ambiguous p lanes root pt then (1 : ℚ) else 0)) ≤ _
    simp_rw [average_const]
    have bound := ambiguity_probability_numeric p lanes root occupied
    simpa only [average, Soundness.uniformProb, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using bound
  have lhs := fresh_history_average run past checked (fun answer _ =>
    if Ambiguous p lanes root answer.1 then (1 : ℚ) else 0)
  have rhs := fresh_history_average run past checked (fun _ _ => (1 : ℚ))
  simp only [average_const] at rhs
  simp only [ite_and] at *
  rw [lhs, rhs]
  calc
    _ ≤ average (fun rest : Outside run → Digest32 =>
        (if outsideAgrees run past (eligible_fresh run past checked) rest then (1 : ℚ) else 0) /
          2^124) := by
      apply average_mono
      intro rest
      by_cases h : outsideAgrees run past (eligible_fresh run past checked) rest
      · simpa [h] using badBound
      · simp [h]
    _ = _ := by simp only [average, Finset.sum_div, div_div, mul_comm]

end Whir.AnchoredByteStreamGroups

#print axioms Whir.AnchoredByteStreamGroups.joint_public_average
#print axioms Whir.AnchoredByteStreamGroups.fresh_history_average
#print axioms Whir.AnchoredByteStreamGroups.fresh_group_ambiguity
