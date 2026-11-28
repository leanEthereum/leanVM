/-
  LeanVM.Guest.B1.Stack.TermRing

  The merged ring claim's weight as a sum over its pieces.
-/

module

public import LeanVM.Guest.B1.Stack.TermMath

/-!
# The ring weight, piece by piece

`ringMerge` groups the pieces of its claims by point, and `ringWeight` shares each group's product
of `eq` factors among the group's pieces. The weight is linear in the pieces, so it is the sum over
every piece, in claim order, of the piece's own term (`ringMerge_weight`): claim `j`'s piece of
point `r`, placement `p` and scale `s` adds `Σ_k c_k eq(r^(2^k), x) above_p(x) (ρ^j s)^(2^k)`
(`pieceTerm_eq`).
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Sums -/

theorem sumE_eq_sum (l : List E) : sumE l = l.sum := Tables.sumE_eq l

theorem list_sum_comm {α β : Type} (K : List α) (L : List β) (f : α → β → E) :
    (K.map fun k ↦ (L.map fun l ↦ f k l).sum).sum = (L.map fun l ↦ (K.map fun k ↦ f k l).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.sum_map_add, ih]

theorem zip_map_self {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun a ↦ (a, f a)
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.zip_cons_cons, zip_map_self f l, List.map_cons]

/-- A sum over `zipIdx` from `n` as a sum over the indices. -/
theorem sumE_zipIdx (F : E → ℕ → E) : ∀ (cs : List E) (n : ℕ),
    sumE ((cs.zipIdx n).map fun ck ↦ F ck.1 ck.2) =
      ∑ k ∈ Finset.range cs.length, F (cs.getD k 0) (n + k)
  | [], _ => by simp [sumE]
  | c :: cs, n => by
    have ih := sumE_zipIdx F cs (n + 1)
    rw [sumE_eq_sum] at ih ⊢
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih, List.length_cons,
      Finset.sum_range_succ' _ cs.length]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [show n + 1 + k = n + (k + 1) by omega]

/-! ## The weight of the groups -/

/-- A piece's weight above its window: its placement's `eqAbove`, `1` for the whole stack. -/
def aboveOf (x : List E) : Option Placement → E
  | some p => p.eqAbove x
  | none => 1

/-- A piece's term at its group's point `P` (each coordinate's Frobenius powers), its above weight
and its scale's Frobenius powers `sc`. -/
def pieceTerm (cs x : List E) (P : List (List E)) (above : E) (sc : List E) : E :=
  sumE (cs.zipIdx.map fun ck ↦
    (P.zip (x.take P.length)).foldl (fun acc (pw : List E × E) ↦ acc * (1 + pw.1.getD ck.2 0 + pw.2))
      ck.1 * (above * sc.getD ck.2 0))

/-- A group's weight: its pieces' terms. -/
def groupW (cs x : List E) (g : RingPointGroup) : E :=
  sumE (g.pieces.map fun pc ↦ pieceTerm cs x g.point (aboveOf x pc.1) pc.2)

theorem aboveOf_eq (x : List E) (o : Option Placement) :
    (match o with
      | some placement => placement.eqAbove x
      | none => 1) = aboveOf x o := by
  cases o <;> rfl

/-- **`ringWeight` is the sum of its groups' weights.** -/
theorem ringWeight_eq (groups : List RingPointGroup) (x cs : List E) :
    ringWeight groups x cs = sumE (groups.map (groupW cs x)) := by
  unfold ringWeight
  congr 1
  refine List.map_congr_left fun g _ ↦ ?_
  simp only [groupW, pieceTerm, zip_map_self, List.map_map]
  rw [sumE_eq_sum, sumE_eq_sum]
  simp only [Function.comp_def, sumE_eq_sum, ← List.sum_map_mul_left]
  exact list_sum_comm _ _ _

/-! ## The merge -/

/-- `ringMerge`'s step on one piece (its inner fold). -/
def pieceStep (rhoJ : E) (gp : List RingPointGroup × List (List E)) (piece : RingPiece) :
    List RingPointGroup × List (List E) :=
  let (groups, points) := gp
  let scale := Verifier.frobenius (rhoJ * piece.scale)
  match points.findIdx? (fun p ↦ decide (p = piece.point)) with
  | some index => (groups.modify index fun group ↦
      { group with pieces := group.pieces ++ [(piece.placement, scale)] }, points)
  | none => (groups ++ [⟨piece.point.map Verifier.frobenius, [(piece.placement, scale)]⟩],
      points ++ [piece.point])

/-- `ringMerge`'s step on one claim (its outer fold). -/
def mergeStep (rho : E) (acc : List E × List RingPointGroup × List (List E) × E) (claim : RingClaim) :
    List E × List RingPointGroup × List (List E) × E :=
  let (slices, groups, points, rhoJ) := acc
  let slices := slices.zipIdx.map fun (sum, i) ↦
    match claim.slices[i]? with
    | some s => sum + rhoJ * s
    | none => sum
  let (groups, points) := claim.pieces.foldl (pieceStep rhoJ) (groups, points)
  (slices, groups, points, rhoJ * rho)

theorem ringMerge_fst (claims : List RingClaim) (f g : List E) (rho : E) (x : List E) :
    (ringMerge claims f g rho).1 x =
      ringWeight (claims.foldl (mergeStep rho) (List.replicate kBits 0, [], [], 1)).2.1 x
        (ringCoefficients f g) := rfl

/-- The groups' points are the seen points' Frobenius powers. -/
def GroupsInv (gs : List RingPointGroup) (ps : List (List E)) : Prop :=
  gs.length = ps.length ∧ ∀ i < gs.length, (gs.getD i default).point = (ps.getD i []).map Verifier.frobenius

theorem sumE_modify (h : RingPointGroup → E) (F : RingPointGroup → RingPointGroup) :
    ∀ (gs : List RingPointGroup) (i : ℕ), i < gs.length →
      sumE ((gs.modify i F).map h) + h (gs.getD i default) = sumE (gs.map h) + h (F (gs.getD i default))
  | [], _, hi => absurd hi (by simp)
  | g :: gs, 0, _ => by
    rw [List.modify_zero_cons, sumE_eq_sum, sumE_eq_sum]
    simp only [List.map_cons, List.sum_cons, List.getD_cons_zero]
    ring
  | g :: gs, i + 1, hi => by
    have ih := sumE_modify h F gs i (by simpa using hi)
    rw [List.modify_succ_cons, sumE_eq_sum, sumE_eq_sum] at *
    simp only [List.map_cons, List.sum_cons, List.getD_cons_succ]
    rw [add_assoc, ih, add_assoc]

/-- The term `pieceStep` adds for a piece at `rhoJ`. -/
def stepTerm (cs x : List E) (rhoJ : E) (piece : RingPiece) : E :=
  pieceTerm cs x (piece.point.map Verifier.frobenius) (aboveOf x piece.placement)
    (Verifier.frobenius (rhoJ * piece.scale))

theorem pieceStep_sound (cs x : List E) (rhoJ : E) {gs : List RingPointGroup} {ps : List (List E)}
    (hinv : GroupsInv gs ps) (piece : RingPiece) :
    GroupsInv (pieceStep rhoJ (gs, ps) piece).1 (pieceStep rhoJ (gs, ps) piece).2 ∧
      sumE ((pieceStep rhoJ (gs, ps) piece).1.map (groupW cs x)) =
        sumE (gs.map (groupW cs x)) + stepTerm cs x rhoJ piece := by
  obtain ⟨hlen, hpt⟩ := hinv
  unfold pieceStep
  simp only
  split
  · rename_i i hfind
    obtain ⟨hi, hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hfind
    simp only [decide_eq_true_eq] at hpi
    have hig : i < gs.length := by omega
    refine ⟨⟨by rw [List.length_modify]; exact hlen, fun j hj ↦ ?_⟩, ?_⟩
    · rw [List.length_modify] at hj
      rw [← hpt j hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_modify]
      split_ifs <;> cases gs[j]? <;> rfl
    · have hm := sumE_modify (groupW cs x) (fun group ↦
        { group with pieces := group.pieces ++ [(piece.placement, Verifier.frobenius (rhoJ * piece.scale))] })
        gs i hig
      have hgp : (gs.getD i default).point = piece.point.map Verifier.frobenius := by
        rw [hpt i hig, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hpi]
      have hF : groupW cs x { gs.getD i default with pieces := (gs.getD i default).pieces ++
            [(piece.placement, Verifier.frobenius (rhoJ * piece.scale))] } =
          groupW cs x (gs.getD i default) + stepTerm cs x rhoJ piece := by
        simp only [groupW, List.map_append, List.map_cons, List.map_nil, stepTerm, ← hgp]
        rw [sumE_eq_sum, sumE_eq_sum, List.sum_append]
        simp
      rw [hF] at hm
      linear_combination hm
  · refine ⟨⟨by simp [hlen], fun j hj ↦ ?_⟩, ?_⟩
    · simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (by omega), hpt j hj]
      · rw [List.getD_append_right _ _ _ _ le_rfl, hlen, List.getD_append_right _ _ _ _ le_rfl]
        simp
    · rw [sumE_eq_sum, sumE_eq_sum, List.map_append, List.sum_append]
      simp [groupW, stepTerm, sumE_eq_sum]

theorem pieces_fold_sound (cs x : List E) (rhoJ : E) : ∀ (pieces : List RingPiece)
    {gs : List RingPointGroup} {ps : List (List E)}, GroupsInv gs ps →
      GroupsInv (pieces.foldl (pieceStep rhoJ) (gs, ps)).1 (pieces.foldl (pieceStep rhoJ) (gs, ps)).2 ∧
        sumE ((pieces.foldl (pieceStep rhoJ) (gs, ps)).1.map (groupW cs x)) =
          sumE (gs.map (groupW cs x)) + sumE (pieces.map (stepTerm cs x rhoJ))
  | [], _, _, h => ⟨h, by simp [sumE]⟩
  | piece :: pieces, gs, ps, h => by
    obtain ⟨h1, e1⟩ := pieceStep_sound cs x rhoJ h piece
    rw [List.foldl_cons]
    obtain ⟨h2, e2⟩ := pieces_fold_sound cs x rhoJ pieces h1
    refine ⟨h2, ?_⟩
    rw [e2, e1, sumE_eq_sum, sumE_eq_sum, sumE_eq_sum, List.map_cons, List.sum_cons]
    ring

/-- The pieces' terms, claim `j` at `ρ^j`. -/
def mergeTotal (cs x : List E) (rho : E) : List RingClaim → E → E
  | [], _ => 0
  | claim :: claims, rhoJ => sumE (claim.pieces.map (stepTerm cs x rhoJ)) + mergeTotal cs x rho claims (rhoJ * rho)

theorem merge_fold_sound (cs x : List E) (rho : E) : ∀ (claims : List RingClaim)
    (sl : List E) {gs : List RingPointGroup} {ps : List (List E)} (rhoJ : E), GroupsInv gs ps →
      sumE ((claims.foldl (mergeStep rho) (sl, gs, ps, rhoJ)).2.1.map (groupW cs x)) =
        sumE (gs.map (groupW cs x)) + mergeTotal cs x rho claims rhoJ
  | [], _, _, _, _, _ => by simp [mergeTotal]
  | claim :: claims, sl, gs, ps, rhoJ, h => by
    obtain ⟨h1, e1⟩ := pieces_fold_sound cs x rhoJ claim.pieces h
    rw [List.foldl_cons]
    show sumE ((claims.foldl (mergeStep rho) (_, (claim.pieces.foldl (pieceStep rhoJ) (gs, ps)).1,
      (claim.pieces.foldl (pieceStep rhoJ) (gs, ps)).2, rhoJ * rho)).2.1.map (groupW cs x)) = _
    rw [merge_fold_sound cs x rho claims _ _ h1, e1, mergeTotal]
    ring

/-- **The merged ring claim's weight, piece by piece.** -/
theorem ringMerge_weight (claims : List RingClaim) (f g : List E) (rho : E) (x : List E) :
    (ringMerge claims f g rho).1 x = mergeTotal (ringCoefficients f g) x rho claims 1 := by
  rw [ringMerge_fst, ringWeight_eq, merge_fold_sound _ x rho claims _ 1 ⟨rfl, fun _ h ↦ absurd h (by simp)⟩]
  simp [sumE]

/-! ## A piece's term -/

theorem foldl_pw (k : ℕ) : ∀ (P : List (List E)) (y : List E) (c : E),
    (P.zip y).foldl (fun acc (pw : List E × E) ↦ acc * (1 + pw.1.getD k 0 + pw.2)) c =
      c * eqEval (P.map (·.getD k 0)) y
  | [], _, c => by simp [eqEval]
  | _ :: _, [], c => by simp [eqEval]
  | a :: P, b :: y, c => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_pw k P y, List.map_cons, Ring.eqEval_eq_prod,
      Ring.eqEval_eq_prod, List.zipWith_cons_cons, List.prod_cons]
    ring

/-- **A piece's term**: at a point `r` and `64` coefficients, `Σ_k c_k eq(r^(2^k), x) above s^(2^k)`. -/
theorem pieceTerm_eq (cs x : List E) (hcs : cs.length = kBits) (r : List E) (above s : E) :
    pieceTerm cs x (r.map Verifier.frobenius) above (Verifier.frobenius s) =
      ∑ k ∈ Finset.range kBits, cs.getD k 0 * eqEval (r.map (· ^ 2 ^ k)) (x.take r.length) *
        (above * s ^ 2 ^ k) := by
  unfold pieceTerm
  simp only [List.length_map, foldl_pw]
  have hz := sumE_zipIdx (fun c k ↦ c * eqEval ((r.map Verifier.frobenius).map (·.getD k 0)) (x.take r.length) *
      (above * (Verifier.frobenius s).getD k 0)) cs 0
  simp only [Nat.zero_add] at hz
  rw [hz, hcs]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk := Finset.mem_range.1 hk
  have hm : (r.map Verifier.frobenius).map (fun v ↦ v.getD k 0) = r.map (· ^ 2 ^ k) := by
    simp only [List.map_map, Function.comp_def]
    exact List.map_congr_left fun v _ ↦ frobenius_getD v hk
  rw [hm, frobenius_getD s hk]

end
end LeanVM.Guest.B1.Stack
