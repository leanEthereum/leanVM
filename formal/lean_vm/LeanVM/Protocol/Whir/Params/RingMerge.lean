/-
  LeanVM.Protocol.Whir.Params.RingMerge

  Ring switching's merge (`ringMerge`, `ring_switch.rs`) read piece by piece: the merged weight is
  the sum of its pieces' weights, each claim's scaled by its power of `ρ`, and the merged slices are
  the claims' slices combined by the same powers.
-/

module

public import LeanVM.Protocol.Whir.Params.Iface
public import LeanVM.Protocol.RingMap
import LeanVM.Protocol.Tables

/-!
# The merge, piece by piece

`ringMerge claims f g ρ` groups the claims' pieces by point (first seen first), each piece's scale
multiplied by `ρ^j` for claim `j`, and sums the claims' slices by the same powers. Its weight at
the stack point `x` (`ringWeight`) shares each group's product over the pieces of the group; read
piece by piece it is `Σ_j Σ_{pieces p of claim j} pieceWeight p (ρ^j)` (`ringMerge_weight`), and
its slices are `Σ_j ρ^j s_j` (`ringMerge_slices`).
-/

namespace LeanVM.Protocol.Whir.Params

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd
  Finset

@[expose] public section

/-! ## Sums of lists -/

theorem sumE_eq_sum' (l : List E) : sumE l = l.sum := Tables.sumE_eq l

theorem list_sum_map_comm {α β : Type} (L₁ : List α) (L₂ : List β) (F : α → β → E) :
    (L₁.map fun a ↦ (L₂.map fun b ↦ F a b).sum).sum =
      (L₂.map fun b ↦ (L₁.map fun a ↦ F a b).sum).sum := by
  induction L₁ with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih, ← List.sum_map_add]

theorem list_sum_map_mul_left {α : Type} (L : List α) (c : E) (F : α → E) :
    c * (L.map F).sum = (L.map fun a ↦ c * F a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem sumE_zip_map {α : Type} (L : List α) (h : α → E) (F : α × E → E) :
    sumE ((L.zip (L.map h)).map F) = (L.map fun a ↦ F (a, h a)).sum := by
  rw [sumE_eq_sum']
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.zip_cons_cons, List.sum_cons, ih]

/-! ## A group's weight, piece by piece -/

/-- The equality weight above a piece's placement (`1` for the whole stack). -/
def aboveOf (o : Option Placement) (x : List E) : E :=
  match o with
  | some placement => placement.eqAbove x
  | none => 1

/-- A group's product at the stack point `x` for the Frobenius power `k`, from the coefficient
`c`: `c Π_n (1 + r_n^(2^k) + x_n)`, the point's powers `P`. -/
def prodP (P : List (List E)) (x : List E) (k : ℕ) (c : E) : E :=
  (P.zip (x.take P.length)).foldl (fun acc (powers, xn) ↦ acc * (1 + powers.getD k 0 + xn)) c

/-- One piece's share of a group's weight: the group's point's powers `P`, the piece's placement
and its scale's powers. -/
def entryWeight (coefs : List E) (P : List (List E)) (x : List E)
    (e : Option Placement × List E) : E :=
  sumE (coefs.zipIdx.map fun (c, k) ↦ prodP P x k c * (aboveOf e.1 x * e.2.getD k 0))

/-- **A group's weight is the sum of its pieces' shares.** -/
theorem groupWeight_eq (coefs x : List E) (group : RingPointGroup) :
    sumE (coefs.zipIdx.map fun (c, k) ↦
      (group.point.zip (x.take group.point.length)).foldl
        (fun acc (powers, xn) ↦ acc * (1 + powers.getD k 0 + xn)) c *
      sumE ((group.pieces.zip (group.pieces.map fun piece ↦
        match piece.1 with
        | some placement => placement.eqAbove x
        | none => 1)).map fun (piece, above) ↦ above * piece.2.getD k 0)) =
      (group.pieces.map (entryWeight coefs group.point x)).sum := by
  have hab : (fun piece : Option Placement × List E ↦
      match piece.1 with
      | some placement => placement.eqAbove x
      | none => 1) = fun piece ↦ aboveOf piece.1 x := by
    funext piece
    rfl
  simp only [hab, sumE_zip_map]
  simp only [sumE_eq_sum', list_sum_map_mul_left]
  rw [list_sum_map_comm]
  congr 1
  refine List.map_congr_left fun e _ ↦ ?_
  simp only [entryWeight, sumE_eq_sum', prodP]

/-- `ringWeight` is the sum of its groups' pieces' shares. -/
theorem ringWeight_eq_entries (groups : List RingPointGroup) (x coefs : List E) :
    ringWeight groups x coefs =
      (groups.map fun group ↦ (group.pieces.map (entryWeight coefs group.point x)).sum).sum := by
  unfold ringWeight
  rw [sumE_eq_sum']
  congr 1
  refine List.map_congr_left fun group _ ↦ ?_
  exact groupWeight_eq coefs x group

/-! ## The merge's fold -/

theorem modify_sum {α : Type} (G : α → E) (f : α → α) :
    ∀ (l : List α) (i : ℕ) (hi : i < l.length),
      ((l.modify i f).map G).sum = (l.map G).sum + (G (f l[i]) - G l[i])
  | [], _, hi => absurd hi (by simp)
  | a :: l, 0, _ => by simp; ring
  | a :: l, i + 1, hi => by
    simp only [List.modify_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]
    rw [modify_sum G f l i (by simpa using hi)]
    ring

theorem modify_map_of {α β : Type} (P : α → β) (f : α → α) (hf : ∀ a, P (f a) = P a) :
    ∀ (l : List α) (i : ℕ), (l.modify i f).map P = l.map P
  | [], _ => by simp
  | a :: l, 0 => by simp [hf]
  | a :: l, i + 1 => by simp [modify_map_of P f hf l i]

/-- The pieces of the merge, claim `j`'s scales multiplied by `ρ^j`, from the power `rhoJ`. -/
def flatPieces (rho : E) : List RingClaim → E → List RingPiece
  | [], _ => []
  | claim :: claims, rhoJ =>
    claim.pieces.map (fun piece ↦ { piece with scale := rhoJ * piece.scale }) ++
      flatPieces rho claims (rhoJ * rho)

/-- A flat piece's weight. -/
def flatWeight (coefs x : List E) (piece : RingPiece) : E :=
  entryWeight coefs (piece.point.map frobenius) x (piece.placement, frobenius piece.scale)

/-- The groups' weight, piece by piece. -/
def groupsWeight (coefs x : List E) (groups : List RingPointGroup) : E :=
  (groups.map fun group ↦ (group.pieces.map (entryWeight coefs group.point x)).sum).sum

/-- The merge's invariant: the groups' points are the points' Frobenius powers. -/
def GroupsOK (groups : List RingPointGroup) (points : List (List E)) : Prop :=
  groups.map (·.point) = points.map (·.map frobenius)

/-- The inner step of `ringMerge`: a piece joins its point's group, or opens one. -/
def pieceStep (rhoJ : E) (gp : List RingPointGroup × List (List E)) (piece : RingPiece) :
    List RingPointGroup × List (List E) :=
  let (groups, points) := gp
  let scale := frobenius (rhoJ * piece.scale)
  match points.findIdx? (fun p ↦ decide (p = piece.point)) with
  | some index => (groups.modify index fun group ↦
      { group with pieces := group.pieces ++ [(piece.placement, scale)] }, points)
  | none => (groups ++ [⟨piece.point.map frobenius, [(piece.placement, scale)]⟩],
      points ++ [piece.point])

theorem pieceStep_spec (rhoJ : E) (gp : List RingPointGroup × List (List E)) (piece : RingPiece)
    (h : GroupsOK gp.1 gp.2) (coefs x : List E) :
    GroupsOK (pieceStep rhoJ gp piece).1 (pieceStep rhoJ gp piece).2 ∧
      groupsWeight coefs x (pieceStep rhoJ gp piece).1 =
        groupsWeight coefs x gp.1 + flatWeight coefs x { piece with scale := rhoJ * piece.scale } := by
  obtain ⟨groups, points⟩ := gp
  unfold pieceStep
  simp only
  rcases hf : points.findIdx? (fun p ↦ decide (p = piece.point)) with _ | i
  · refine ⟨?_, ?_⟩
    · unfold GroupsOK at h ⊢
      simp [h]
    · simp [groupsWeight, flatWeight]
  · obtain ⟨hi, hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    have hpi' : points[i] = piece.point := by simpa using hpi
    have hlen : groups.length = points.length := by
      have := congrArg List.length h
      simpa using this
    have hgi : i < groups.length := hlen ▸ hi
    have hpt : groups[i].point = piece.point.map frobenius := by
      have := congrArg (fun l ↦ l[i]?) h
      simp only [List.getElem?_map, List.getElem?_eq_getElem hgi,
        List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at this
      rw [this, hpi']
    dsimp only
    refine ⟨?_, ?_⟩
    · unfold GroupsOK at h ⊢
      exact (modify_map_of (fun g : RingPointGroup ↦ g.point) (fun group ↦
        { group with pieces := group.pieces ++ [(piece.placement, frobenius (rhoJ * piece.scale))] })
        (fun _ ↦ rfl) groups i).trans h
    · unfold groupsWeight
      rw [modify_sum _ _ groups i hgi]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, flatWeight, hpt]
      ring

theorem pieces_fold_spec (rhoJ : E) (coefs x : List E) :
    ∀ (pieces : List RingPiece) (gp : List RingPointGroup × List (List E)), GroupsOK gp.1 gp.2 →
      GroupsOK (pieces.foldl (pieceStep rhoJ) gp).1 (pieces.foldl (pieceStep rhoJ) gp).2 ∧
        groupsWeight coefs x (pieces.foldl (pieceStep rhoJ) gp).1 =
          groupsWeight coefs x gp.1 +
            (pieces.map fun piece ↦ flatWeight coefs x { piece with scale := rhoJ * piece.scale }).sum
  | [], gp, h => by simp [h]
  | piece :: pieces, gp, h => by
    obtain ⟨h1, h2⟩ := pieceStep_spec rhoJ gp piece h coefs x
    obtain ⟨h3, h4⟩ := pieces_fold_spec rhoJ coefs x pieces _ h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4, h2, List.map_cons, List.sum_cons]
    ring

/-- The outer step of `ringMerge`: a claim's slices join by its power of `ρ`, its pieces join
their groups. -/
def claimStep (rho : E) (acc : List E × List RingPointGroup × List (List E) × E)
    (claim : RingClaim) : List E × List RingPointGroup × List (List E) × E :=
  let (slices, groups, points, rhoJ) := acc
  let slices := slices.zipIdx.map fun (sum, i) ↦
    match claim.slices[i]? with
    | some s => sum + rhoJ * s
    | none => sum
  let (groups, points) := claim.pieces.foldl (pieceStep rhoJ) (groups, points)
  (slices, groups, points, rhoJ * rho)

theorem claimStep_eq (rho : E) (slices : List E) (groups : List RingPointGroup)
    (points : List (List E)) (rhoJ : E) (claim : RingClaim) :
    claimStep rho (slices, groups, points, rhoJ) claim =
      (slices.zipIdx.map fun (sum, i) ↦
          match claim.slices[i]? with
          | some s => sum + rhoJ * s
          | none => sum,
        (claim.pieces.foldl (pieceStep rhoJ) (groups, points)).1,
        (claim.pieces.foldl (pieceStep rhoJ) (groups, points)).2, rhoJ * rho) := rfl

/-- `ringMerge` is its fold's weight and target. -/
theorem ringMerge_eq (claims : List RingClaim) (f g : List E) (rho : E) :
    ringMerge claims f g rho =
      (fun x ↦ ringWeight (claims.foldl (claimStep rho) (List.replicate kBits 0, [], [], 1)).2.1 x
          (ringCoefficients f g),
        ringTarget (claims.foldl (claimStep rho) (List.replicate kBits 0, [], [], 1)).1 f g) := rfl

theorem mergeFold_groups (rho : E) (coefs x : List E) :
    ∀ (claims : List RingClaim) (acc : List E × List RingPointGroup × List (List E) × E),
      GroupsOK acc.2.1 acc.2.2.1 →
      GroupsOK (claims.foldl (claimStep rho) acc).2.1 (claims.foldl (claimStep rho) acc).2.2.1 ∧
        groupsWeight coefs x (claims.foldl (claimStep rho) acc).2.1 =
          groupsWeight coefs x acc.2.1 +
            ((flatPieces rho claims acc.2.2.2).map (flatWeight coefs x)).sum
  | [], acc, h => by simp [h, flatPieces]
  | claim :: claims, ⟨slices, groups, points, rhoJ⟩, h => by
    obtain ⟨h1, h2⟩ := pieces_fold_spec rhoJ coefs x claim.pieces (groups, points) h
    rw [List.foldl_cons, claimStep_eq]
    obtain ⟨h3, h4⟩ := mergeFold_groups rho coefs x claims (_,
      (claim.pieces.foldl (pieceStep rhoJ) (groups, points)).1,
      (claim.pieces.foldl (pieceStep rhoJ) (groups, points)).2, rhoJ * rho) h1
    refine ⟨h3, ?_⟩
    rw [h4, h2, flatPieces, List.map_append, List.sum_append, List.map_map]
    simp only [add_assoc]
    rfl

/-- **The merged weight, piece by piece.** -/
theorem ringMerge_weight (claims : List RingClaim) (f g : List E) (rho : E) (x : List E) :
    (ringMerge claims f g rho).1 x =
      ((flatPieces rho claims 1).map (flatWeight (ringCoefficients f g) x)).sum := by
  rw [ringMerge_eq]
  dsimp only
  rw [ringWeight_eq_entries]
  have := (mergeFold_groups rho (ringCoefficients f g) x claims (List.replicate kBits 0, [], [], 1)
    (by simp [GroupsOK])).2
  simp only [groupsWeight, List.map_nil, List.sum_nil, zero_add] at this
  exact this

/-! ## The merged weight is multiaffine -/

/-- **A piece lies on a placement within the stack**: its point fills the placement's variables. -/
def PieceOK (μ : ℕ) (piece : RingPiece) : Prop :=
  ∃ p : Placement, piece.placement = some p ∧ piece.point.length = p.variableCount ∧
    p.variableCount ≤ μ

theorem foldl_zip_mul {α β : Type} (F : α → β → E) :
    ∀ (L₁ : List α) (L₂ : List β) (c : E),
      (L₁.zip L₂).foldl (fun acc (a, b) ↦ acc * F a b) c = c * (List.zipWith F L₁ L₂).prod
  | [], _, c => by simp
  | _ :: _, [], c => by simp
  | a :: L₁, b :: L₂, c => by
    rw [List.zip_cons_cons, List.foldl_cons, foldl_zip_mul F L₁ L₂, List.zipWith_cons_cons,
      List.prod_cons]
    ring

/-- A group's product is an `eq_eval` at the powers its point holds. -/
theorem prodP_eq (pt x : List E) (k : ℕ) (c : E) :
    prodP (pt.map frobenius) x k c =
      c * eqEval (pt.map fun a ↦ (frobenius a).getD k 0) (x.take pt.length) := by
  unfold prodP
  rw [List.length_map, foldl_zip_mul (fun (powers : List E) (xn : E) ↦ 1 + powers.getD k 0 + xn),
    eqEval, ← List.prod_eq_foldl]
  simp only [List.zipWith_map_left]

/-- **A placed piece's weight** at a point of the stack's `μ` coordinates: for each Frobenius
power, its coefficient and scale power times `eq` of the point's powers and the placement's
selector. -/
theorem flatWeight_eq {μ : ℕ} (coefs : List E) (piece : RingPiece) {p : Placement}
    (hp : piece.placement = some p) (hlen : piece.point.length = p.variableCount)
    (hvc : p.variableCount ≤ μ) (x : List E) (hx : x.length = μ) :
    flatWeight coefs x piece =
      (coefs.zipIdx.map fun (c, k) ↦ c * (frobenius piece.scale).getD k 0 *
        eqEval (piece.point.map (fun a ↦ (frobenius a).getD k 0) ++
          selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount)) x).sum := by
  unfold flatWeight entryWeight
  rw [sumE_eq_sum']
  refine congrArg List.sum (List.map_congr_left fun ck _ ↦ ?_)
  obtain ⟨c, k⟩ := ck
  have key : eqEval (piece.point.map (fun a ↦ (frobenius a).getD k 0) ++
      selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount)) x =
      eqEval (piece.point.map (fun a ↦ (frobenius a).getD k 0)) (x.take p.variableCount) *
        eqEval (selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount))
          (x.drop p.variableCount) := by
    have := Tables.eqEval_append (piece.point.map (fun a ↦ (frobenius a).getD k 0))
      (selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount))
      (x.take p.variableCount) (x.drop p.variableCount)
      (by rw [List.length_map, List.length_take, hlen, hx, Nat.min_eq_left hvc])
    rwa [List.take_append_drop] at this
  dsimp only
  rw [key, prodP_eq, hlen]
  simp only [aboveOf, hp, Placement.eqAbove, hx]
  ring

theorem IsMultiaffine.congr' {n : ℕ} {Φ Ψ : List E → E} (h : ∀ l, l.length = n → Φ l = Ψ l)
    (hΨ : Sound.IsMultiaffine n Ψ) : Sound.IsMultiaffine n Φ := by
  intro l hl k hk X
  rw [h _ (by simp [hl]), h _ (by simp [hl]), h _ (by simp [hl])]
  exact hΨ l hl k hk X

theorem isMultiaffine_listSum {α : Type} {n : ℕ} (L : List α) (F : α → List E → E)
    (h : ∀ a ∈ L, Sound.IsMultiaffine n (F a)) :
    Sound.IsMultiaffine n fun x ↦ (L.map fun a ↦ F a x).sum := by
  induction L with
  | nil => simpa using (Sound.IsMultiaffine.zero (n := n))
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-- **A placed piece's weight is multiaffine on the stack.** -/
theorem isMultiaffine_flatWeight {μ : ℕ} (coefs : List E) (piece : RingPiece)
    (h : PieceOK μ piece) : Sound.IsMultiaffine μ fun x ↦ flatWeight coefs x piece := by
  obtain ⟨p, hp, hlen, hvc⟩ := h
  refine IsMultiaffine.congr' (fun x hx ↦ flatWeight_eq coefs piece hp hlen hvc x hx) ?_
  refine isMultiaffine_listSum _ _ fun ck _ ↦ ?_
  obtain ⟨c, k⟩ := ck
  have he := Sound.isMultiaffine_eqEval (piece.point.map (fun a ↦ (frobenius a).getD k 0) ++
    selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount))
  have hl : (piece.point.map (fun a ↦ (frobenius a).getD k 0) ++
      selectorPoint (p.index >>> p.variableCount) (μ - p.variableCount)).length = μ := by
    simp [selectorPoint, hlen]
    omega
  rw [hl] at he
  exact he.const_mul _

theorem flatPieces_ok {μ : ℕ} (rho : E) :
    ∀ (claims : List RingClaim) (r : E), (∀ c ∈ claims, ∀ piece ∈ c.pieces, PieceOK μ piece) →
      ∀ piece ∈ flatPieces rho claims r, PieceOK μ piece
  | [], _, _, piece, hp => by simp [flatPieces] at hp
  | claim :: claims, r, h, piece, hp => by
    simp only [flatPieces, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | hp
    · exact h claim List.mem_cons_self q hq
    · exact flatPieces_ok rho claims _ (fun c hc ↦ h c (List.mem_cons_of_mem _ hc)) piece hp

/-- **The merged weight is multiaffine on the stack** when every piece is placed. -/
theorem isMultiaffine_ringMerge {μ : ℕ} (claims : List RingClaim)
    (h : ∀ c ∈ claims, ∀ piece ∈ c.pieces, PieceOK μ piece) (f g : List E) (rho : E) :
    Sound.IsMultiaffine μ (ringMerge claims f g rho).1 := by
  have he : (ringMerge claims f g rho).1 =
      fun x ↦ ((flatPieces rho claims 1).map fun piece ↦
        flatWeight (ringCoefficients f g) x piece).sum := by
    funext x
    exact ringMerge_weight claims f g rho x
  rw [he]
  exact isMultiaffine_listSum _ _ fun piece hp ↦
    isMultiaffine_flatWeight _ piece (flatPieces_ok rho claims 1 h piece hp)

/-- **Ring switching's facts from the pieces' placement and the merge's soundness**: the merged
weight's multiaffinity holds for placed pieces (`isMultiaffine_ringMerge`); the soundness count is
the hypothesis `hsound`. -/
theorem ringFacts_of {μ : ℕ} {rings : List RingClaim}
    (h : ∀ c ∈ rings, ∀ piece ∈ c.pieces, PieceOK μ piece)
    (hsound : ∀ q : Column μ, (∃ rc ∈ rings, ¬ Relation.RingClaimHolds q rc) →
      avgPk (ringChallengeCount rings)
          (fun pre ↦ open Classical in
            if StackClaim.Holds μ (ringClaimAt rings pre) q then 1 else 0) ≤
        (3 : ENNReal) / Fintype.card E) :
    RingFacts μ rings :=
  ⟨fun _ ↦ isMultiaffine_ringMerge rings h _ _ _, hsound⟩

end
end LeanVM.Protocol.Whir.Params
