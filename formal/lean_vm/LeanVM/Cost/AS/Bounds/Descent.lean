module

public import LeanVM.Cost.AS.Bounds.Newton
import all LeanVM.Protocol.Whir.Sound.DescentC
import all LeanVM.Protocol.Whir.Sound.DescentA

/-!
# Bounds: the descent's folds, agreement sets and one-error decoding over arrays

* `foldCA_cost`: one fold of a column of `s` lanes, `113·s + 320`; `foldsCA_cost`: the rounds' folds
  of a column of at most `W` lanes, `(113·W + 340)·r + 10`; `foldsAC_cost`: every column's;
* `agreeC_cost`: the agreement set's columns, a tuple of `2^m` lanes;
* `winPtsC_cost`, `decFs_cost`, `valsOf_cost`, `badCols_cost`, `checkStage_cost`,
  `decStage_cost`, **`newtonDecC_cost`**: one-error decoding of `2^(m+1)` lanes on `n` columns.
-/

namespace LeanVM.Cost.Bounds.AS

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.AS LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Protocol.Whir.Sound LeanVM.Protocol.Whir.Sound.Newton LeanVM.Protocol.Verifier

public section

variable (P : MachineProgram)

/-- `List.any` (`any.c293`): `11` per element and the predicate's price, `3`. -/
theorem anyC_cost (hP : Includes P Auto.List.any.c293.costDeps) {α : Type} [MachineEncoding α]
    (p : α → Bool) (pVal : MachineValue) (hp : ∀ a, RunsApp P pVal [encodeValue a] (encodeValue (p a))) (B : ℕ) :
    ∀ l : List α, (∀ a ∈ l, appCost P pVal [encodeValue a] ≤ B) →
      machineCost P Auto.List.any.c293.costIdx [encodeValue l, pVal] ≤ (B + 11) * l.length + 3 := by
  intro l
  induction l with
  | nil => intro _; rw [Auto.List.any.c293.costEq_nil P hP p pVal hp]; omega
  | cons a l ih =>
    intro hB
    rw [Auto.List.any.c293.costEq_cons P hP a l p pVal hp]
    have h1 := ih fun a' ha ↦ hB a' (by simp [ha])
    have h2 := hB a (by simp)
    simp only [List.length_cons]
    split_ifs <;> nlinarith

theorem size_foldCA (y : E) (r : FoldRound) (o : Array E) :
    (foldCA y r o).size = (o.size + 1) / 2 := by
  simp [foldCA]

theorem foldCA_cost (hP : Includes P foldCAC.costDeps) (y : E) (r : FoldRound) (o : Array E)
    (ho : o.size < 2 ^ 62) :
    machineCost P foldCAC.costIdx [encodeValue y, encodeValue r, encodeValue o] ≤
      113 * o.size + 320 := by
  rw [foldCAC.costEq P hP, limbs_of_lt (by omega : o.size + 1 < 2 ^ 64),
    limbs_of_lt (by omega : o.size < 2 ^ 64), ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := (o.size + 1) / 2) (by omega) _
    (.closure foldCAC.lam0.costIdx [encodeValue o, encodeValue (r.alpha + r.beta * y),
      encodeValue (r.beta * y)])
    (fun k ↦ RunsApp.of_spec (foldCAC.lam0.costSpec P (by includes) o _ _ k)) 208
    (fun k ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        foldCAC.lam0.costEq P (by includes)]
      have hk := k.isLt
      rw [limbs_of_lt (by omega : 2 * (k : ℕ) < 2 ^ 64), limbs_of_lt (by omega : (k : ℕ) < 2 ^ 64),
        limbs_of_lt (by omega : 2 * (k : ℕ) + 1 < 2 ^ 64)]
      simp) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at this
  omega

theorem foldsCA_size (y : E) : ∀ (rounds : List FoldRound) (o : Array E),
    (foldsCA y rounds o).size ≤ o.size
  | [], o => le_rfl
  | r :: rounds, o => by
    unfold foldsCA
    rw [List.foldl_cons]
    have := foldsCA_size y rounds (foldCA y r o)
    unfold foldsCA at this
    rw [size_foldCA] at this
    omega

theorem foldsCA_cost (hP : Includes P foldsCAC.costDeps) (y : E) (rounds : List FoldRound)
    (o : Array E) (W : ℕ) (hW : o.size ≤ W) (hW' : W < 2 ^ 62) :
    machineCost P foldsCAC.costIdx [encodeValue y, encodeValue rounds, encodeValue o] ≤
      (113 * W + 340) * rounds.length + 10 := by
  rw [foldsCAC.costEq P hP]
  have := listFoldl_le' P (by includes) (fun o r ↦ foldCA y r o)
    (.closure foldsCAC.lam0.costIdx [encodeValue y])
    (fun o r ↦ RunsApp.of_spec (foldsCAC.lam0.costSpec P (by includes) y o r)) (113 * W + 325)
    (fun o _ ↦ o.size ≤ W)
    (fun o r _ h ↦ by
      refine ⟨by rw [size_foldCA]; omega, ?_⟩
      rw [appCost_fn, List.cons_append, List.nil_append, foldsCAC.lam0.costEq P (by includes)]
      have := foldCA_cost P (by includes) y r o (by omega)
      simp only [List.length_cons, List.length_nil]
      nlinarith) rounds o hW
  have : (113 * W + 325 + 11) * rounds.length ≤ (113 * W + 340) * rounds.length :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem foldsAC_col (n : ℕ) (rounds : List FoldRound) (OA : AV) (x : ℕ) (W : ℕ)
    (hW : ∀ x < n, (OA.getD x #[]).size ≤ W) : ((foldsAC n rounds OA).getD x #[]).size ≤ W := by
  unfold foldsAC
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split_ifs with hx
  · exact (foldsCA_size _ _ _).trans (hW x hx)
  · simp

theorem foldsAC_cost (hP : Includes P foldsACC.costDeps) (n : ℕ) (rounds : List FoldRound)
    (OA : AV) (W : ℕ) (hn : n < 2 ^ 62) (hW : ∀ x < n, (OA.getD x #[]).size ≤ W)
    (hW' : W < 2 ^ 62) :
    machineCost P foldsACC.costIdx [encodeValue n, encodeValue rounds, encodeValue OA] ≤
      ((113 * W + 340) * rounds.length + 60) * n + 20 := by
  rw [foldsACC.costEq P hP, ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := n) (by omega) _
    (.closure foldsACC.lam0.costIdx [encodeValue n, encodeValue rounds, encodeValue OA])
    (fun x ↦ RunsApp.of_spec (foldsACC.lam0.costSpec P (by includes) n rounds OA x))
    ((113 * W + 340) * rounds.length + 30)
    (fun x ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        foldsACC.lam0.costEq P (by includes), limbs_of_lt (by omega : (x : ℕ) < 2 ^ 64)]
      have := foldsCA_cost P (by includes) (ptE x) rounds (OA.getD x #[]) W (hW x x.isLt) hW'
      simp only [List.length_cons, List.length_nil]
      omega) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at this
  nlinarith

theorem agreeC_cost (hP : Includes P agreeCC.costDeps) (n m : ℕ) (r : FoldRound) (VA QA : AV)
    (W : ℕ) (hn : n < 2 ^ 62) (hm : m < 60) (hW : ∀ x < n, (QA.getD x #[]).size ≤ W)
    (hW' : W < 2 ^ 62) :
    machineCost P agreeCC.costIdx [encodeValue n, encodeValue m, encodeValue r, encodeValue VA,
      encodeValue QA] ≤ (113 * W + 56 * 2 ^ m + 430) * n + 30 := by
  rw [agreeCC.costEq P hP]
  have hm2 : 2 ^ m < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) hm
  have hfr := finRangeFrom_cost P (by includes) n (by omega) 0 (Nat.zero_le _)
  have hf := filter_cost P (by includes) _
    (.closure agreeCC.lam0.costIdx [encodeValue n, encodeValue m, encodeValue r, encodeValue VA,
      encodeValue QA])
    (fun x ↦ RunsApp.of_spec (agreeCC.lam0.costSpec P (by includes) n m r VA QA x))
    (113 * W + 56 * 2 ^ m + 400) (List.finRange n)
    (fun x _ ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [agreeCC.lam0.costEq P (by includes), limbs_of_lt (by omega : (x : ℕ) < 2 ^ 64),
        limbs_of_lt (by omega : m < 2 ^ 64),
        limbs_of_lt (by rw [Nat.shiftLeft_eq, one_mul]; omega : 1 <<< m < 2 ^ 64)]
      have h1 := foldCA_cost P (by includes) (ptE x) r (QA.getD x #[]) (by
        have := hW x x.isLt; omega)
      have h2 := hW x x.isLt
      have h3 := finRangeFrom_cost P (by includes) (2 ^ m) (by omega) 0 (Nat.zero_le _)
      have h4 := all_cost P (by includes) _
        (.closure agreeCC.lam0.lam0.costIdx [encodeValue m,
          encodeValue (foldCA (ptE x) r (QA.getD x #[])), encodeValue (VA.getD x #[])])
        (fun k ↦ RunsApp.of_spec (agreeCC.lam0.lam0.costSpec P (by includes) m _ _ k)) 32
        (List.finRange (2 ^ m)) (fun k _ ↦ by
          rw [appCost_fn]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [agreeCC.lam0.lam0.costEq P (by includes)]
          split_ifs <;> omega)
      simp only [List.length_finRange, Nat.sub_zero] at h3 h4
      have h5 : 113 * (QA.getD x #[]).size ≤ 113 * W := Nat.mul_le_mul_left _ h2
      simp only [max_self]
      omega)
  simp only [List.length_finRange, Nat.sub_zero] at hf hfr
  have : (113 * W + 56 * 2 ^ m + 400 + 15) * n + 13 * n ≤ (113 * W + 56 * 2 ^ m + 430) * n := by
    rw [← Nat.add_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  omega

theorem length_winPtsC {n : ℕ} (d : ℕ) (QA : AV) (cols : List (Fin n)) (k : ℕ)
    (h : d + 3 ≤ cols.length) : (winPtsC d QA cols k).length = d + 3 := by
  simp [winPtsC]; omega

theorem winPtsC_cost (hP : Includes P winPtsCC.costDeps) {n : ℕ} (d : ℕ) (QA : AV)
    (cols : List (Fin n)) (k : ℕ) (hd : d + 3 < 2 ^ 62) (hn : n < 2 ^ 62) :
    machineCost P winPtsCC.costIdx [encodeValue n, encodeValue d, encodeValue QA, encodeValue cols,
      encodeValue k] ≤ 53 * (d + 3) + 22 := by
  rw [winPtsCC.costEq P hP, limbs_of_lt (by omega : d + 3 < 2 ^ 64), limbs_of_lt (by omega : d < 2 ^ 64)]
  have ht := take_cost P (by includes) (d + 3) cols (by omega)
  have hm := map_cost P (by includes) _ (.closure winPtsCC.lam0.costIdx [encodeValue n,
      encodeValue QA, encodeValue k])
    (fun x ↦ RunsApp.of_spec (winPtsCC.lam0.costSpec P (by includes) QA k x)) 21 (cols.take (d + 3))
    (fun x _ ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [winPtsCC.lam0.costEq P (by includes), limbs_of_lt (by omega : (x : ℕ) < 2 ^ 64)])
  have hl : (cols.take (d + 3)).length ≤ d + 3 := by simp
  simp only [max_self]
  nlinarith

theorem length_nFormK (q : List (K × E)) : (nFormK q).1.length = q.length := by
  have h := congrArg (fun f ↦ f.1.length) (nFormK_eq q)
  simp only [List.length_map] at h
  rw [← h, (nForm_fst (liftPts q)).1, List.length_map, length_liftPts]

theorem length_decode1K {d : ℕ} {pts : List (K × E)} {f : List K × List E}
    (h : decode1K d pts = some f) : f.1.length ≤ pts.length := by
  unfold decode1K at h
  simp only at h
  split_ifs at h <;> rw [Option.some.injEq] at h <;> subst h
  · rw [length_nFormK]
  · rw [length_nFormK]; exact length_dropLoc _ _ _

theorem decFs_cost (hP : Includes P decFsC.costDeps) {n : ℕ} (d m : ℕ) (QA : AV)
    (cols : List (Fin n)) (hd : d + 3 < 2 ^ 40) (hm : m < 59) (hn : n < 2 ^ 62)
    (hc : d + 3 ≤ cols.length) :
    machineCost P decFsC.costIdx [encodeValue n, encodeValue d, encodeValue m, encodeValue QA,
      encodeValue cols] ≤ (600 * (d + 3) ^ 2 + 8100 * (d + 3) + 10100) * 2 ^ (m + 1) + 30 := by
  have hm2 : 2 ^ (m + 1) < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [decFsC.costEq P hP, limbs_of_lt (by omega : m + 1 < 2 ^ 64), limbs_of_lt (by omega : m < 2 ^ 64),
    limbs_of_lt (by rw [Nat.shiftLeft_eq, one_mul]; omega : 1 <<< (m + 1) < 2 ^ 64), ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := 2 ^ (m + 1)) (by omega) _
    (.closure decFsC.lam0.costIdx [encodeValue n, encodeValue d, encodeValue m, encodeValue QA,
      encodeValue cols])
    (fun k ↦ RunsApp.of_spec (decFsC.lam0.costSpec P (by includes) d m QA cols k))
    (600 * (d + 3) ^ 2 + 8053 * (d + 3) + 10035)
    (fun k ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [decFsC.lam0.costEq P (by includes)]
      have h1 := winPtsC_cost P (by includes) d QA cols k (by omega) hn
      have h2 := decode1K_cost P (by includes) d (winPtsC d QA cols k)
        (length_winPtsC d QA cols k hc) (by omega)
      omega) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero, max_self] at this ⊢
  nlinarith

theorem valsOf_cost (hP : Includes P valsOfC.costDeps) (n m : ℕ)
    (fs : Array (Option (List K × List E))) (L : ℕ)
    (hL : ∀ k, ((fs.getD k none).getD ([], [])).1.length ≤ L) (hn : n < 2 ^ 62) (hm : m < 59) :
    machineCost P valsOfC.costIdx [encodeValue n, encodeValue m, encodeValue fs] ≤
      ((206 * L + 58) * 2 ^ (m + 1) + 50) * n + 20 := by
  have hm2 : 2 ^ (m + 1) < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [valsOfC.costEq P hP, ofFnFrom_length]
  have := ofFnFrom_cost P (by includes) (n := n) (by omega) _
    (.closure valsOfC.lam0.costIdx [encodeValue n, encodeValue m, encodeValue fs])
    (fun x ↦ RunsApp.of_spec (valsOfC.lam0.costSpec P (by includes) n m fs x))
    ((206 * L + 58) * 2 ^ (m + 1) + 25)
    (fun x ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [valsOfC.lam0.costEq P (by includes), limbs_of_lt (by omega : m + 1 < 2 ^ 64),
        limbs_of_lt (by omega : m < 2 ^ 64),
        limbs_of_lt (by rw [Nat.shiftLeft_eq, one_mul]; omega : 1 <<< (m + 1) < 2 ^ 64),
        ofFnFrom_length]
      have hi := ofFnFrom_cost P (by includes) (n := 2 ^ (m + 1)) (by omega) _
        (.closure valsOfC.lam0.lam0.costIdx [encodeValue n, encodeValue m, encodeValue fs,
          encodeValue x])
        (fun k ↦ RunsApp.of_spec (valsOfC.lam0.lam0.costSpec P (by includes) n m fs x k))
        (206 * L + 41)
        (fun k ↦ by
          rw [appCost_fn]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [valsOfC.lam0.lam0.costEq P (by includes), limbs_of_lt (by omega : (x : ℕ) < 2 ^ 64)]
          have h1 := nEvalK_go_cost P (by includes) ((fs.getD k none).getD ([], [])).1
            ((fs.getD k none).getD ([], [])).2 (K.ofBits x)
          have h2 := hL k
          have h3 : 206 * ((fs.getD k none).getD ([], [])).1.length ≤ 206 * L :=
            Nat.mul_le_mul_left _ h2
          generalize fs.getD k none = o at h1 h3 ⊢
          cases o <;> simp only at h1 h3 ⊢ <;> omega) 0 (Nat.zero_le _)
      simp only [Nat.sub_zero, max_self] at hi ⊢
      nlinarith) 0 (Nat.zero_le _)
  simp only [Nat.sub_zero] at this
  nlinarith

theorem badCols_cost (hP : Includes P badColsC.costDeps) {n : ℕ} (m : ℕ) (QA : AV)
    (cols : List (Fin n)) (V : AV) (_hn : n < 2 ^ 62) (hm : m < 59) :
    machineCost P badColsC.costIdx [encodeValue n, encodeValue m, encodeValue QA, encodeValue cols,
      encodeValue V] ≤ (58 * 2 ^ (m + 1) + 60) * cols.length + 20 := by
  have hm2 : 2 ^ (m + 1) < 2 ^ 60 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [badColsC.costEq P hP]
  have := filter_cost P (by includes) _
    (.closure badColsC.lam0.costIdx [encodeValue n, encodeValue m, encodeValue QA, encodeValue V])
    (fun x ↦ RunsApp.of_spec (badColsC.lam0.costSpec P (by includes) m QA V x))
    (58 * 2 ^ (m + 1) + 45) cols
    (fun x _ ↦ by
      rw [appCost_fn]
      simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [badColsC.lam0.costEq P (by includes), limbs_of_lt (by omega : m + 1 < 2 ^ 64),
        limbs_of_lt (by omega : m < 2 ^ 64),
        limbs_of_lt (by rw [Nat.shiftLeft_eq, one_mul]; omega : 1 <<< (m + 1) < 2 ^ 64)]
      have h1 := finRangeFrom_cost P (by includes) (2 ^ (m + 1)) (by omega) 0 (Nat.zero_le _)
      have h2 := anyC_cost P (by includes) _
        (.closure badColsC.lam0.lam0.costIdx [encodeValue m, encodeValue (V.getD x #[]),
          encodeValue (QA.getD x #[])])
        (fun k ↦ RunsApp.of_spec (badColsC.lam0.lam0.costSpec P (by includes) m _ _ k)) 34
        (List.finRange (2 ^ (m + 1))) (fun k _ ↦ by
          rw [appCost_fn]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [badColsC.lam0.lam0.costEq P (by includes)]
          split_ifs <;> omega)
      simp only [List.length_finRange, Nat.sub_zero] at h1 h2
      simp only [max_self]
      omega)
  nlinarith

theorem length_badCols {n : ℕ} (m : ℕ) (QA : AV) (cols : List (Fin n)) (V : AV) :
    (badCols m QA cols V).length ≤ cols.length := List.length_filter_le _ _

theorem checkStage_cost (hP : Includes P checkStageC.costDeps) {n : ℕ} (m : ℕ) (QA : AV)
    (cols : List (Fin n)) (V : AV) (hn : n < 2 ^ 62) (hm : m < 59) (hc : cols.length < 2 ^ 62) :
    machineCost P checkStageC.costIdx [encodeValue n, encodeValue m, encodeValue QA,
      encodeValue cols, encodeValue V] ≤ (58 * 2 ^ (m + 1) + 70) * cols.length + 40 := by
  rw [checkStageC.costEq P hP]
  have h1 := badCols_cost P (by includes) m QA cols V hn hm
  have hb := length_badCols m QA cols V
  have h2 := length_cost P (by includes) (badCols m QA cols V) (by omega)
  rw [limbs_of_lt (by omega : (badCols m QA cols V).length < 2 ^ 64)]
  split_ifs <;> nlinarith

theorem decStage_cost (hP : Includes P decStageC.costDeps) (n m : ℕ) (QA : AV) (cols : List (Fin n))
    (fs : Array (Option (List K × List E))) (L : ℕ)
    (hL : ∀ k, ((fs.getD k none).getD ([], [])).1.length ≤ L) (hs : fs.size = 2 ^ (m + 1))
    (hn : n < 2 ^ 62) (hm : m < 59) (hc : cols.length ≤ n) :
    machineCost P decStageC.costIdx [encodeValue n, encodeValue m, encodeValue QA,
      encodeValue cols, encodeValue fs] ≤
      ((206 * L + 116) * 2 ^ (m + 1) + 120) * n + 18 * 2 ^ (m + 1) + 80 := by
  rw [decStageC.costEq P hP]
  have h1 := all_cost P (by includes) _ (.closure decStageC.lam0.costIdx [])
    (fun x ↦ RunsApp.of_spec (decStageC.lam0.costSpec P (by includes) x)) 4 fs.toList
    (fun x _ ↦ by
      rw [appCost_fn, List.nil_append, decStageC.lam0.costEq P (by includes)]
      cases x <;> simp)
  have h2 := valsOf_cost P (by includes) n m fs L hL hn hm
  have h3 := checkStage_cost P (by includes) m QA cols (valsOf n m fs) hn hm (by omega)
  simp only [Array.length_toList, hs] at h1
  have h4 : (58 * 2 ^ (m + 1) + 70) * cols.length ≤ (58 * 2 ^ (m + 1) + 70) * n :=
    Nat.mul_le_mul_left _ hc
  rw [hs]
  split_ifs <;> nlinarith

theorem decFs_forms {n : ℕ} (d m : ℕ) (QA : AV) (cols : List (Fin n)) (hc : d + 3 ≤ cols.length)
    (k : ℕ) : (((decFs d m QA cols).getD k none).getD ([], [])).1.length ≤ d + 3 := by
  unfold decFs
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split_ifs with hk
  · simp only [Option.getD_some]
    rcases h : decode1K d (winPtsC d QA cols k) with _ | f
    · simp
    · have := length_decode1K h
      rw [length_winPtsC d QA cols k hc] at this
      simpa using this
  · simp

/-- **One-error decoding of `2^(m+1)` lanes on `n` columns, priced.** -/
theorem newtonDecC_cost (hP : Includes P newtonDecCC.costDeps) (n d m : ℕ) (QA : AV)
    (cols : List (Fin n)) (hd : d + 3 < 2 ^ 40) (hm : m < 59) (hn : n < 2 ^ 62)
    (hc : cols.length ≤ n) :
    machineCost P newtonDecCC.costIdx [encodeValue n, encodeValue d, encodeValue m, encodeValue QA,
      encodeValue cols] ≤
      (600 * (d + 3) ^ 2 + 8200 * (d + 3) + 10200 + (206 * (d + 3) + 116) * n) * 2 ^ (m + 1) +
        130 * n + 200 := by
  rw [newtonDecCC.costEq P hP, limbs_of_lt (by omega : d + 3 < 2 ^ 64),
    limbs_of_lt (by omega : d < 2 ^ 64), limbs_of_lt (by omega : cols.length < 2 ^ 64)]
  have hl := length_cost P (by includes) cols (by omega)
  split_ifs with h
  · have h1 := decFs_cost P (by includes) d m QA cols hd hm hn h
    have h2 := decStage_cost P (by includes) n m QA cols (decFs d m QA cols) (d + 3)
      (decFs_forms d m QA cols h) (by simp [decFs]) hn hm hc
    simp only [max_self]
    nlinarith
  · simp only [max_self]
    omega

theorem length_agreeC (n m : ℕ) (r : FoldRound) (VA QA : AV) :
    (agreeC n m r VA QA).length ≤ n :=
  (List.length_filter_le _ _).trans (by simp)

/-- The lane-dependent price of a round of the descent, per `2^(m+1)`. -/
@[expose] def stepF (n d : ℕ) : ℕ := 600 * (d + 3) ^ 2 + 8200 * (d + 3) + 10200 + (206 * (d + 3) + 144) * n

/-- The lane-independent price of a round of the descent. -/
@[expose] def stepG (n W R : ℕ) : ℕ := ((113 * W + 340) * R + 113 * W + 1100) * n + 30 * R + 1000

/-- One round's arithmetic: the round's parts and the rest's price within the bound. -/
theorem descStep_le (n d W R t m c₁ c₂ c₃ c₄ c₅ c₆ c₇ rec q : ℕ) (ht : t + 1 ≤ R) (hq : q ≤ n)
    (h₁ : c₁ ≤ 11 * t + 3) (h₂ : c₂ ≤ ((113 * W + 340) * t + 60) * n + 20)
    (h₃ : c₃ ≤ (113 * W + 56 * 2 ^ m + 430) * n + 30) (h₄ : c₄ ≤ 8 * t + 3) (h₅ : c₅ ≤ 8 * q + 3)
    (h₆ : c₆ ≤ (600 * (d + 3) ^ 2 + 8200 * (d + 3) + 10200 + (206 * (d + 3) + 116) * n) *
      2 ^ (m + 1) + 130 * n + 200)
    (h₇ : c₇ ≤ rec + 24 + 6)
    (hrec : rec + stepF n d * 2 ^ (m + 1 + 1) ≤ stepF n d * 2 ^ (m + 1 + 1 + t) + stepG n W R * t + 9) :
    c₁ + c₂ + c₃ + c₄ + 4 + c₅ + 1 + (c₆ + c₇ + 22) + 28 + stepF n d * 2 ^ (m + 1) ≤
      stepF n d * 2 ^ (m + 1 + (t + 1)) + stepG n W R * (t + 1) + 9 := by
  have e1 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
  have e2 : 2 ^ (m + 1 + (t + 1)) = 2 ^ (m + 1 + 1 + t) := by ring_nf
  have e3 : 56 * 2 ^ m * n = 28 * n * 2 ^ (m + 1) := by ring
  rw [e2]
  rw [e1] at hrec
  have hF : stepF n d * 2 ^ (m + 1) = (600 * (d + 3) ^ 2 + 8200 * (d + 3) + 10200 +
      (206 * (d + 3) + 116) * n) * 2 ^ (m + 1) + 28 * n * 2 ^ (m + 1) := by unfold stepF; ring
  have hG : stepG n W R * (t + 1) = stepG n W R * t + stepG n W R := by ring
  have hGt : ((113 * W + 340) * t + 60) * n ≤ ((113 * W + 340) * R) * n :=
    Nat.mul_le_mul_right _ (by nlinarith)
  have hG' : ((113 * W + 340) * R + 113 * W + 1100) * n + 30 * R + 1000 = stepG n W R := rfl
  have hA : (113 * W + 56 * 2 ^ m + 430) * n = 113 * W * n + 56 * 2 ^ m * n + 430 * n := by ring
  have hS : ((113 * W + 340) * R + 113 * W + 1100) * n =
      (113 * W + 340) * R * n + 113 * W * n + 1100 * n := by ring
  rw [hA] at h₃
  rw [e3] at h₃
  have h2t : 2 * (stepF n d * 2 ^ (m + 1)) = stepF n d * (2 * 2 ^ (m + 1)) := by ring
  rw [← h2t] at hrec
  omega

theorem pow_le_pow_add (F a t : ℕ) : F * 2 ^ a ≤ F * 2 ^ (a + t) :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The descent within a level, its recursive worker, priced**: with `F = stepF n d` the
lane-dependent and `G = stepG n W R` the lane-independent price of a round, the rounds `rs` from
`2^m` lanes cost at most `F·(2^(m+1+|rs|) − 2^(m+1)) + G·|rs| + 9`. -/
theorem descRevGo_cost (hP : Includes P Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.costDeps)
    (n d A ℓ : ℕ) (OA : AV) (W R : ℕ) (hn : n < 2 ^ 62) (hd : d + 3 < 2 ^ 40)
    (hW : ∀ x < n, (OA.getD x #[]).size ≤ W) (hW' : W < 2 ^ 62) (hA : A < 2 ^ 62)
    (hℓ : ℓ < 2 ^ 62) :
    ∀ (rs : List FoldRound) (m : ℕ) (VA : AV), rs.length ≤ R → m + rs.length < 59 →
      machineCost P Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.costIdx [encodeValue n,
        encodeValue d, encodeValue A, encodeValue ℓ, encodeValue OA, encodeValue rs, encodeValue m,
        encodeValue VA] + stepF n d * 2 ^ (m + 1) ≤
        stepF n d * 2 ^ (m + 1 + rs.length) + stepG n W R * rs.length + 9
  | [], m, VA, _, _ => by
    rw [Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.costEq_nil P hP]
    simp only [List.length_nil, Nat.add_zero, Nat.mul_zero]
    omega
  | r :: tail, m, VA, hR, hm => by
    simp only [List.length_cons] at hR hm ⊢
    rw [Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.costEq_cons P hP]
    have c₁ := reverseAux_cost P (by includes) tail []
    have c₂ := foldsAC_cost P (by includes) n tail.reverse OA W hn hW hW'
    rw [List.length_reverse] at c₂
    have c₃ := agreeC_cost P (by includes) n m r VA (foldsAC n tail.reverse OA) W hn (by omega)
      (fun x _ ↦ foldsAC_col n tail.reverse OA x W hW) hW'
    have c₄ := length_cost P (by includes) tail (by omega)
    have hag := length_agreeC n m r VA (foldsAC n tail.reverse OA)
    have c₅ := length_cost P (by includes) (agreeC n m r VA (foldsAC n tail.reverse OA)) (by omega)
    rw [limbs_of_lt (by omega : tail.length + 1 < 2 ^ 64), limbs_of_lt (by omega : tail.length < 2 ^ 64),
      limbs_of_lt (by omega : ℓ < 2 ^ 64), limbs_of_lt (by omega : A < 2 ^ 64),
      limbs_of_lt (by omega : ℓ - (tail.length + 1) < 2 ^ 64),
      limbs_of_lt (by omega : A - (ℓ - (tail.length + 1)) < 2 ^ 64),
      limbs_of_lt (by omega : (agreeC n m r VA (foldsAC n tail.reverse OA)).length < 2 ^ 64)]
    have ih := fun VA' ↦ descRevGo_cost hP n d A ℓ OA W R hn hd hW hW' hA hℓ tail (m + 1) VA'
      (by omega) (by omega)
    set rec := stepF n d * 2 ^ (m + 1 + 1 + tail.length) + stepG n W R * tail.length + 9 -
      stepF n d * 2 ^ (m + 1 + 1) with hrec
    have hmono := pow_le_pow_add (stepF n d) (m + 1 + 1) tail.length
    have hrec' : rec + stepF n d * 2 ^ (m + 1 + 1) ≤
        stepF n d * 2 ^ (m + 1 + 1 + tail.length) + stepG n W R * tail.length + 9 := by omega
    split_ifs with hthr
    · have c₆ := newtonDecC_cost P (by includes) n d m (foldsAC n tail.reverse OA)
        (agreeC n m r VA (foldsAC n tail.reverse OA)) hd (by omega) hn hag
      have c₇ := bind_cost P (by includes) (fun TA ↦ descRevC n d A ℓ OA tail (m + 1) TA)
        (.closure Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.lam0.costIdx [encodeValue tail,
          encodeValue n, encodeValue d, encodeValue A, encodeValue ℓ, encodeValue OA, encodeValue m])
        (fun TA ↦ RunsApp.of_spec (Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.lam0.costSpec P
          (by includes) tail n d A ℓ OA m TA))
        (rec + 24) (fun TA ↦ by
          rw [appCost_fn]
          simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.lam0.costEq P (by includes),
            limbs_of_lt (by omega : m + 1 < 2 ^ 64),
            limbs_of_lt (by omega : m < 2 ^ 64)]
          have := ih TA
          omega) (newtonDecC n d m (foldsAC n tail.reverse OA)
            (agreeC n m r VA (foldsAC n tail.reverse OA)))
      have := descStep_le n d W R tail.length m _ _ _ _ _ _ _ rec _ (by omega) hag c₁ c₂ c₃ c₄
        c₅ c₆ c₇ hrec'
      simp only [max_self]
      rw [show (302 : ℕ) = Auto.LeanVM.Protocol.Whir.Sound.descRevC.c301.lam0.costIdx from rfl]
      omega
    · have := descStep_le n d W R tail.length m _ _ _ _ _ 0 0 rec _ (by omega) hag c₁ c₂ c₃ c₄
        c₅ (Nat.zero_le _) (Nat.zero_le _) hrec'
      simp only [max_self]
      omega


end

end LeanVM.Cost.Bounds.AS
