module

public import LeanVM.Cost.AS.Bounds.StepUp
public import LeanVM.Cost.AS.Bounds.Descent
import all LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Whir.Params.Check
import all LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDeployedTable

/-!
# Bounds: the descent across levels

`traceCostB μ R W tr i`: the price of the descent across levels from level `i` of the trace `tr`,
level by level as the code goes: the level's shape (`lvC`), its initial tuple (the final
polynomial on its domain, or the step up from the next level, `upAtA`), and the descent within the
level (`descPrice`, from `descRevGo_cost`). **`descendTraceGo_cost`**: the compiled descent's
worker is within it.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Verifier

public section

variable (P : MachineProgram)

/-- Every level of the fold table has at most `6` folds and a threshold below `2^40`. -/
theorem foldTable_folds : (Protocol.Whir.AffineCombiner.foldTable.all fun row ↦ row.all fun lvs ↦
    lvs.all fun lv ↦ decide (lv.2.2.1 ≤ 6 ∧ lv.2.2.2.1 < 2 ^ 40)) = true := by
  decide +kernel

theorem lvC_folds (μ R i : ℕ) : (lvC μ R i).2.2.1 ≤ 6 ∧ (lvC μ R i).2.2.2 < 2 ^ 40 := by
  have hT := foldTable_folds
  simp only [List.all_eq_true, decide_eq_true_eq] at hT
  have key : ((Protocol.Whir.Params.levelsOf μ R).getD i Protocol.Whir.Params.junkLv).2.2.1 ≤ 6 ∧
      ((Protocol.Whir.Params.levelsOf μ R).getD i Protocol.Whir.Params.junkLv).2.2.2.1 < 2 ^ 40 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (Protocol.Whir.Params.levelsOf μ R)[i]? with
    | none => simp [Protocol.Whir.Params.junkLv]
    | some lv =>
      simp only [Option.getD_some]
      have hm := List.mem_of_getElem? h
      unfold Protocol.Whir.Params.levelsOf at hm
      rw [List.getD_eq_getElem?_getD] at hm
      cases h2 : (Protocol.Whir.AffineCombiner.foldTable.getD (R - 1) [])[μ - 16]? with
      | none => rw [h2] at hm; simp at hm
      | some lvs =>
        rw [h2, Option.getD_some] at hm
        have hm2 := List.mem_of_getElem? h2
        rw [List.getD_eq_getElem?_getD] at hm2
        cases h3 : Protocol.Whir.AffineCombiner.foldTable[R - 1]? with
        | none => rw [h3] at hm2; simp at hm2
        | some row =>
          rw [h3, Option.getD_some] at hm2
          exact hT row (List.mem_of_getElem? h3) lvs hm2 lv hm
  unfold lvC
  dsimp only
  split_ifs <;> simp only <;> omega

/-- The lanes the descent within a level returns: one more per round. -/
theorem descRevC_fst (n d A ℓ : ℕ) (OA : AV) : ∀ (rs : List FoldRound) (m : ℕ) (VA : AV)
    {T : ℕ × AV}, descRevC n d A ℓ OA rs m VA = some T → T.1 = m + rs.length
  | [], m, VA, T, h => by simp [descRevC] at h; subst h; rfl
  | r :: rs, m, VA, T, h => by
    unfold descRevC at h
    dsimp only at h
    split_ifs at h
    obtain ⟨TA, -, h⟩ := Option.bind_eq_some_iff.mp h
    rw [descRevC_fst n d A ℓ OA rs (m + 1) TA h]
    simp only [List.length_cons]
    omega

/-- A trace's number of levels after the first. -/
@[expose] def traceDepth : WhirTrace → ℕ
  | .final _ _ => 0
  | .mid _ _ rest => traceDepth rest + 1

/-- A trace's sizes within the machine's words. -/
@[expose] def TraceSmall : WhirTrace → Prop
  | .final rounds folded => rounds.length ≤ 50 ∧ folded.length < 2 ^ 32
  | .mid rounds high rest => rounds.length ≤ 50 ∧ high.length < 2 ^ 32 ∧ TraceSmall rest

theorem descendTraceC_fst (μ R : ℕ) (OAs : List AV) : ∀ (tr : WhirTrace) (i : ℕ) {T : ℕ × AV},
    TraceSmall tr → descendTraceC μ R OAs tr i = some T → T.1 ≤ 50
  | .final rounds folded, i, T, hs, h => by
    unfold descendTraceC at h
    rw [descRevC_fst _ _ _ _ _ _ _ _ h, List.length_reverse]
    have := hs.1
    omega
  | .mid rounds high rest, i, T, hs, h => by
    unfold descendTraceC at h
    obtain ⟨T', -, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split_ifs at h
    rw [descRevC_fst _ _ _ _ _ _ _ _ h, List.length_reverse]
    have := hs.1
    omega

/-- The descent within a level of `n` columns at degree `d`, `r` rounds from one lane. -/
@[expose] def descPrice (n d W r : ℕ) : ℕ := stepF n d * 2 ^ (0 + 1 + r) + stepG n W r * r + 9

/-- **The descent across levels' price**, level by level. -/
@[expose] def traceCostB (μ R W : ℕ) : WhirTrace → ℕ → ℕ
  | .final rounds folded, i =>
    (15 * (μ + R + i) + 20000) + 15 * i + 17 + 11 * rounds.length + 3 +
      (polyPrice folded.length + 13 + 16) * 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) + 5 +
      2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) +
      descPrice (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1)
        W rounds.length + 100
  | .mid rounds high rest, i =>
    traceCostB μ R W rest (i + 1) + (15 * (μ + R + i) + 20000) +
      (15 * (μ + R + (i + 1)) + 20000) + 15 * i + 17 + 11 * rounds.length + 3 +
      upPrice (lvC μ R i).1 (lvC μ R (i + 1)).1 (lvC μ R (i + 1)).2.2.1 (lvC μ R i).2.1 high.length +
      descPrice (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1)
        W rounds.length + 200

theorem lvC_limbs (μ R i : ℕ) :
    (lvC μ R i).1 + (lvC μ R i).2.1 < 2 ^ 64 ∧ (lvC μ R i).1 < 2 ^ 64 ∧ (lvC μ R i).2.1 < 2 ^ 64 ∧
      2 ^ (lvC μ R i).1 < 2 ^ 64 ∧ 2 ^ (lvC μ R i).1 - 1 < 2 ^ 64 ∧ (lvC μ R i).2.2.1 < 2 ^ 64 ∧
      2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) < 2 ^ 62 ∧
      2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1 + 3 < 2 ^ 40 ∧ (lvC μ R i).2.2.2 < 2 ^ 62 := by
  have h1 := lvC_small μ R i
  obtain ⟨h2, h3⟩ := lvC_folds μ R i
  have p1 : 2 ^ (lvC μ R i).1 ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have p2 : 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) h1
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The descent across levels, its worker, priced.** -/
theorem descendTraceGo_cost
    (hP : Includes P Auto.LeanVM.Protocol.Whir.Sound.descendTraceC.c407.costDeps)
    (μ R : ℕ) (OAs : List AV) (W : ℕ) (hμ : μ < 2 ^ 50) (hR : R < 2 ^ 50)
    (hW : ∀ i x, ((OAs.getD i #[]).getD x #[]).size ≤ W) (hW' : W < 2 ^ 62) :
    ∀ (tr : WhirTrace) (i : ℕ), i + traceDepth tr < 2 ^ 50 → TraceSmall tr →
      machineCost P Auto.LeanVM.Protocol.Whir.Sound.descendTraceC.c407.costIdx
        [encodeValue μ, encodeValue R, encodeValue OAs, encodeValue tr, encodeValue i] ≤
        traceCostB μ R W tr i
  | .final rounds folded, i, hi, hs => by
    rw [Auto.LeanVM.Protocol.Whir.Sound.descendTraceC.c407.costEq P hP]
    obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := lvC_limbs μ R i
    simp only [traceCostB]
    have s1 : 1 <<< (lvC μ R i).1 < 2 ^ 64 := by rw [Nat.shiftLeft_eq, one_mul]; exact l4
    have s2 : 1 <<< ((lvC μ R i).1 + (lvC μ R i).2.1) < 2 ^ 64 := by
      rw [Nat.shiftLeft_eq, one_mul]; omega
    have s3 : 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) < 2 ^ 64 := by omega
    have s4 : 2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1 < 2 ^ 64 := by omega
    have s5 : (lvC μ R i).2.2.2 < 2 ^ 64 := by omega
    simp (disch := omega) only [limbs_of_lt]
    rw [ofFnFrom_length]
    have c1 := lvC_cost P (by includes) μ R i (by omega) (by omega) (by omega)
    have c2 := getD_cost_idx P (by includes) OAs i #[] (by omega)
    have c3 := reverseAux_cost P (by includes) rounds []
    have c4 := ofFnFrom_cost P (by includes) (n := 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1))
      (by omega) _ (.closure descendTraceCC.lam0.costIdx [encodeValue folded, encodeValue μ,
        encodeValue R, encodeValue i])
      (fun x ↦ RunsApp.of_spec (descendTraceCC.lam0.costSpec P (by includes) folded μ R i x))
      (polyPrice folded.length + 13) (fun x ↦ by
        rw [appCost_fn]
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [descendTraceCC.lam0.costEq P (by includes)]
        have := polyOfAtH_cost P (by includes) folded x folded.length le_rfl hs.2 (by omega)
        omega) 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at c4
    have c5 := descRevGo_cost P (by includes) (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1))
      (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1) (lvC μ R i).2.2.2 (lvC μ R i).2.2.1
      (OAs.getD i #[]) W rounds.length l7 l8 (fun x _ ↦ hW i x) hW' l9
      (by have := (lvC_folds μ R i).1; omega)
      rounds.reverse 0
      (Array.ofFn fun x : Fin (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) ↦ #[polyOfAtH folded x])
      (by rw [List.length_reverse]) (by rw [List.length_reverse]; have := hs.1; omega)
    rw [List.length_reverse] at c5
    unfold descPrice
    simp only [max_self]
    omega
  | .mid rounds high rest, i, hi, hs => by
    rw [Auto.LeanVM.Protocol.Whir.Sound.descendTraceC.c407.costEq P hP]
    simp only [traceCostB]
    rw [limbs_of_lt (by omega : i + 1 < 2 ^ 64), limbs_of_lt (by omega : i < 2 ^ 64)]
    simp only [traceDepth] at hi
    have ih := descendTraceGo_cost hP μ R OAs W hμ hR hW hW' rest (i + 1) (by omega) hs.2.2
    rw [Auto.Option.bind.c47.costEq P (by includes) _
      (fun T' ↦ if T'.1 = (lvC μ R (i + 1)).2.2.1 ∧ (lvC μ R i).1 =
          (lvC μ R (i + 1)).2.2.1 + (lvC μ R (i + 1)).1 then
        descRevC (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1)
          (lvC μ R i).2.2.2 (lvC μ R i).2.2.1 (OAs.getD i #[]) rounds.reverse 0
          (upAtA (lvC μ R i).1 (lvC μ R (i + 1)).1 (lvC μ R (i + 1)).2.2.1 (lvC μ R i).2.1 T'.2 high)
        else none)
      _ (fun T' ↦ RunsApp.of_spec (descendTraceCC.lam1.costSpec P (by includes) rounds high μ R
        OAs i T'))]
    rcases hT : descendTraceC μ R OAs rest (i + 1) with _ | T'
    · simp only
      unfold descPrice
      omega
    · have hT1 := descendTraceC_fst μ R OAs rest (i + 1) hs.2.2 hT
      simp only
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [descendTraceCC.lam1.costEq P (by includes)]
      obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := lvC_limbs μ R i
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9⟩ := lvC_limbs μ R (i + 1)
      have c1 := lvC_cost P (by includes) μ R i (by omega) (by omega) (by omega)
      have c1' := lvC_cost P (by includes) μ R (i + 1) (by omega) (by omega) (by omega)
      have c2 := getD_cost_idx P (by includes) OAs i #[] (by omega)
      have c3 := reverseAux_cost P (by includes) rounds []
      have c4 := upAtA_cost P (by includes) (lvC μ R i).1 (lvC μ R (i + 1)).1
        (lvC μ R (i + 1)).2.2.1 (lvC μ R i).2.1 T'.2 high high.length
        (by have := lvC_small μ R i; omega) (by have := lvC_small μ R (i + 1); omega)
        (by have := (lvC_folds μ R (i + 1)).1; omega)
        le_rfl hs.2.1
      have c5 := descRevGo_cost P (by includes) (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1))
        (2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1) (lvC μ R i).2.2.2 (lvC μ R i).2.2.1
        (OAs.getD i #[]) W rounds.length l7 l8 (fun x _ ↦ hW i x) hW' l9
        (by have := (lvC_folds μ R i).1; omega)
        rounds.reverse 0 (upAtA (lvC μ R i).1 (lvC μ R (i + 1)).1 (lvC μ R (i + 1)).2.2.1
          (lvC μ R i).2.1 T'.2 high)
        (by rw [List.length_reverse]) (by rw [List.length_reverse]; have := hs.1; omega)
      rw [List.length_reverse] at c5
      have s1 : 1 <<< (lvC μ R i).1 < 2 ^ 64 := by rw [Nat.shiftLeft_eq, one_mul]; exact l4
      have s2 : 1 <<< ((lvC μ R i).1 + (lvC μ R i).2.1) < 2 ^ 64 := by
        rw [Nat.shiftLeft_eq, one_mul]; omega
      have s3 : 2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1) < 2 ^ 64 := by omega
      have s4 : 2 ^ (lvC μ R i).1 - 1 + (lvC μ R i).2.2.1 < 2 ^ 64 := by omega
      have s5 : (lvC μ R i).2.2.2 < 2 ^ 64 := by omega
      have s6 : (lvC μ R (i + 1)).2.2.1 + (lvC μ R (i + 1)).1 < 2 ^ 64 := by
        have := (lvC_folds μ R (i + 1)).1; have := lvC_small μ R (i + 1); omega
      simp (disch := omega) only [limbs_of_lt]
      unfold descPrice
      simp only [max_self]
      split_ifs <;> omega

end

end LeanVM.Cost.Bounds.AS
