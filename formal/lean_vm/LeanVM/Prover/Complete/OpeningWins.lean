/-
  LeanVM.Prover.Complete.OpeningWins

  The honest script's last phases win: the stack's commitment, then ring switching and the
  stacked opening on claims that hold (`CommitOpenWins`), from ring switching's fact on the
  honest stack.
-/

module

public import LeanVM.Prover.Complete.ClaimTables
public import LeanVM.Prover.Complete.Opening
public import LeanVM.Prover.Complete.Assemble
import LeanVM.Protocol.Relation.Placement

/-!
# The opening phases win

`commitOpenWins_of`: `CommitOpenWins` from `RingSwitchHonest`, ring switching's merged claim on
the honest stack (its description adds its weight, which is multilinear, and the claim holds). The
other claims are placed equality kernels (`descMatches_cells`, `descMatches_ood`), whose truth on
the honest stack is the claims' truth on the columns (`holds_placed`), and the opening wins on
them (`follows_stackedOpening`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd LeanVM.Protocol.Tables
  LeanVM.Protocol.Whir.Complete Finset

/-- **Ring switching on a stack**: for two ring claims that hold of the stack `q`, their pieces
placed blocks inside it, the merged claim's description adds its weight, the weight is
multilinear, and the merged claim holds of `q`. -/
def RingSwitchHonest : Prop :=
  ∀ (μ : ℕ) (q : Column μ) (a b : RingClaim) (f g : List E) (rho : E),
    f.length = ringMapWidth → g.length = ringMapWidth →
    (∀ rc ∈ [a, b], rc.HoldsOn q.values.toArray ∧
      ∀ piece ∈ rc.pieces, ∃ p, piece.placement = some p ∧ PartOK μ (p, piece.point, piece.scale)) →
    DescMatches μ (.ring [a, b] f g rho) (ringMerge [a, b] f g rho).1 ∧
      IsMultilinearFn μ (ringMerge [a, b] f g rho).1 ∧
      StackClaim.Holds μ (ringMerge [a, b] f g rho) q

section Witness

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {W : Witness}

/-- A placement of the honest witness, with a point over its variables, is a part inside the
stack. -/
theorem partOK_witness (hW : witness? prog input t = some W) {c : ℕ} {p : Placement}
    (hp : W.layout.placements.getD c none = some p) {point : List E}
    (hpt : point.length = p.variableCount) (scale : E) :
    PartOK W.layout.stackLog (p, point, scale) := by
  obtain ⟨-, -, hdvd, hin, -, -⟩ := placement_witness hW hp
  refine ⟨hpt, ?_, hdvd, hin⟩
  have : 2 ^ p.variableCount ≤ 2 ^ W.layout.stackLog := le_trans (Nat.le_add_left _ _) hin
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

/-- **A placed claim's weight on the honest stack** is the column's extension at the point. -/
theorem holds_placed (hW : witness? prog input t = some W) (hS : W.stack.size = 2 ^ W.layout.stackLog)
    {c : ℕ} {p : Placement} (hp : W.layout.placements.getD c none = some p) {point : List E}
    (hpt : point.length = p.variableCount) :
    ∑ x : Fin (2 ^ W.layout.stackLog), eqEval (p.stackPoint point W.layout.stackLog)
        (boolPoint W.layout.stackLog x) * ofK ((stackColumn W hS).values.getD x 0) =
      mleK (W.cols.getD c #[]) point := by
  obtain ⟨-, hsize, -, -, -, hget⟩ := placement_witness hW hp
  obtain ⟨-, hv, hdvd, hin⟩ := partOK_witness hW hp hpt 1
  rw [Fin.sum_univ_eq_sum_range (fun y ↦ eqEval (p.stackPoint point W.layout.stackLog)
      (boolPoint W.layout.stackLog y) * ofK ((stackColumn W hS).values.getD y 0)),
    sum_stackPoint (fun y ↦ ofK ((stackColumn W hS).values.getD y 0)) hpt hv hdvd hin,
    mleK_eq, multilinearEval_eq_sum p.variableCount _ _
      (by rw [List.length_map, Array.length_toList, hsize]) hpt]
  refine sum_congr rfl fun u hu ↦ ?_
  have hu' := mem_range.mp hu
  have hg := hget u hu'
  have hst : (stackColumn W hS).values.getD (p.index + u) 0 = W.stack.getD (p.index + u) 0 := rfl
  rw [hst, hg, mul_comm, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  rcases (W.cols.getD c #[])[u]? with _ | a <;> simp

/-- Matched descriptions over a `filterMap`. -/
theorem forall₂_filterMap {α β γ : Type} {R : β → γ → Prop} {F : α → Option β} {G : α → Option γ} :
    ∀ (l : List α), (∀ a ∈ l, match F a, G a with
      | some b, some c => R b c
      | none, none => True
      | _, _ => False) → List.Forall₂ R (l.filterMap F) (l.filterMap G)
  | [], _ => List.Forall₂.nil
  | a :: l, h => by
    have ih := forall₂_filterMap l fun a' ha' ↦ h a' (List.mem_cons_of_mem _ ha')
    have ha := h a List.mem_cons_self
    simp only [List.filterMap_cons]
    rcases hF : F a with _ | b <;> rcases hG : G a with _ | c <;> simp only [hF, hG] at ha
    · exact ih
    · exact List.Forall₂.cons ha ih

private theorem length_powersFrom' (base : E) : ∀ (count : ℕ) (acc : E),
    (powersFrom acc base count).length = count
  | 0, _ => rfl
  | count + 1, acc => by simp [powersFrom, length_powersFrom' base count]

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {m₁ : List α} {m₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R m₁ m₂ → List.Forall₂ R (l₁ ++ m₁) (l₂ ++ m₂)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a b, h => .cons a (forall₂_append b h)

/-- The link's memory term as the verifier states it (`memoryTermClaim`). -/
def memoryClaimOf (W : Witness) (link : LinkEnd) (p0 p1 : Placement) : StackClaim :=
  (fun x ↦ sumE (List.map (fun x_1 ↦ x_1.2 * eqEval x_1.1 x)
      [(p0.stackPoint link.memoryPoint W.layout.stackLog, link.memoryScales.1),
        (p1.stackPoint link.memoryPoint W.layout.stackLog, link.memoryScales.2)]),
    link.memoryValue)

section Facts

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {W : Witness}

theorem descMatches_memory (hW : witness? prog input t = some W) {link : LinkEnd}
    {p0 p1 : Placement} (hp0 : W.layout.placements.getD memory0 none = some p0)
    (hp1 : W.layout.placements.getD memory1 none = some p1)
    (hmp0 : link.memoryPoint.length = p0.variableCount)
    (hmp1 : link.memoryPoint.length = p1.variableCount) :
    DescMatches W.layout.stackLog (ClaimDesc.cells [(p0, link.memoryPoint, link.memoryScales.1),
      (p1, link.memoryPoint, link.memoryScales.2)]) (memoryClaimOf W link p0 p1).1 :=
  (descMatches_cells _ (by
    intro part hpart
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
    rcases hpart with rfl | rfl
    · exact partOK_witness hW hp0 hmp0 _
    · exact partOK_witness hW hp1 hmp1 _)).congr fun y _ ↦ by
      simp [memoryClaimOf, sumE_eq]

theorem descMatches_columns (hW : witness? prog input t = some W) (claims : List ColumnClaim)
    (H1 : ∀ c ∈ claims, ∀ p, W.layout.placements.getD c.column none = some p →
      c.point.length = p.variableCount) :
    List.Forall₂ (fun d c ↦ DescMatches W.layout.stackLog d c.1)
      (List.filterMap (fun c ↦ Option.map (fun p ↦ ClaimDesc.cells [(p, c.point, 1)])
        (W.layout.placements.getD c.column none)) claims)
      (List.filterMap (fun x ↦ x.onStack W.layout) claims) := by
  refine forall₂_filterMap claims fun c hc ↦ ?_
  rcases hpc : W.layout.placements.getD c.column none with _ | p
  · simp only [ColumnClaim.onStack]
    rw [hpc]
    trivial
  · simp only [ColumnClaim.onStack]
    rw [hpc]
    simp only [Option.map_some]
    exact (descMatches_cells _ (by
      intro part hpart
      simp only [List.mem_singleton] at hpart
      subst hpart
      exact partOK_witness hW hpc (H1 c hc p hpc) _)).congr fun y _ ↦ by simp

theorem memoryClaim_facts (hW : witness? prog input t = some W)
    (hS : W.stack.size = 2 ^ W.layout.stackLog) {link : LinkEnd} {p0 p1 : Placement}
    (hp0 : W.layout.placements.getD memory0 none = some p0)
    (hp1 : W.layout.placements.getD memory1 none = some p1)
    (hmp0 : link.memoryPoint.length = p0.variableCount)
    (hmp1 : link.memoryPoint.length = p1.variableCount)
    (hmem : link.memoryValue =
      link.memoryScales.1 * mleK (W.cols.getD memory0 #[]) link.memoryPoint +
        link.memoryScales.2 * mleK (W.cols.getD memory1 #[]) link.memoryPoint) :
    StackClaim.Holds W.layout.stackLog (memoryClaimOf W link p0 p1) (stackColumn W hS) ∧
      IsMultilinearFn W.layout.stackLog (memoryClaimOf W link p0 p1).1 := by
  have hv0' : p0.variableCount ≤ W.layout.stackLog := (partOK_witness hW hp0 hmp0 1).2.1
  have hv1' : p1.variableCount ≤ W.layout.stackLog := (partOK_witness hW hp1 hmp1 1).2.1
  refine ⟨?_, ?_⟩
  · simp only [StackClaim.Holds, memoryClaimOf, sumE_eq, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, add_mul, Finset.sum_add_distrib, mul_assoc,
      ← Finset.mul_sum]
    rw [holds_placed hW hS hp0 hmp0, holds_placed hW hS hp1 hmp1, hmem]
  · refine isMultilinearFn_congr (isMultilinearFn_add
      (isMultilinearFn_const_mul (isMultilinearFn_stackPoint hmp0 hv0') link.memoryScales.1)
      (isMultilinearFn_const_mul (isMultilinearFn_stackPoint hmp1 hv1') link.memoryScales.2))
      fun x _ ↦ ?_
    simp [memoryClaimOf, sumE_eq]

theorem column_facts (hW : witness? prog input t = some W)
    (hS : W.stack.size = 2 ^ W.layout.stackLog) {claims : List ColumnClaim}
    (hcl : ∀ c ∈ claims, c.HoldsIn W.cols)
    (H1 : ∀ c ∈ claims, ∀ p, W.layout.placements.getD c.column none = some p →
      c.point.length = p.variableCount) :
    ∀ c ∈ List.filterMap (fun x ↦ x.onStack W.layout) claims,
      StackClaim.Holds W.layout.stackLog c (stackColumn W hS) ∧
        IsMultilinearFn W.layout.stackLog c.1 := by
  intro c hc
  obtain ⟨c', hc', hon⟩ := List.mem_filterMap.mp hc
  simp only [ColumnClaim.onStack] at hon
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hon
  refine ⟨?_, isMultilinearFn_stackPoint (H1 c' hc' p hp)
    (partOK_witness hW hp (H1 c' hc' p hp) 1).2.1⟩
  simp only [StackClaim.Holds]
  rw [holds_placed hW hS hp (H1 c' hc' p hp)]
  exact (hcl c' hc').symm

theorem ood_facts (hS : W.stack.size = 2 ^ W.layout.stackLog) {oodPoint : List E}
    (hood : oodPoint.length = W.layout.stackLog) :
    StackClaim.Holds W.layout.stackLog ((fun x ↦ eqEval oodPoint x), mleK W.stack oodPoint)
        (stackColumn W hS) ∧
      IsMultilinearFn W.layout.stackLog (fun x ↦ eqEval oodPoint x) := by
  refine ⟨?_, by have := isMultilinearFn_eqEval oodPoint; rw [hood] at this; exact this⟩
  simp only [StackClaim.Holds]
  rw [Fin.sum_univ_eq_sum_range (fun y ↦ eqEval oodPoint (boolPoint W.layout.stackLog y) *
      ofK ((stackColumn W hS).values.getD y 0)), mleK_eq,
    multilinearEval_eq_sum W.layout.stackLog _ _ (by simp [hS]) hood]
  refine Finset.sum_congr rfl fun y hy ↦ ?_
  have hst : (stackColumn W hS).values.getD y 0 = W.stack.getD y 0 := rfl
  rw [hst, eqEval_comm, mul_comm, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  rcases W.stack[y]? with _ | a <;> simp

end Facts

/-- **The opening phases win**, from ring switching on the honest stack. -/
theorem commitOpenWins_of (hring : RingSwitchHonest) : CommitOpenWins := by
  intro prog input t ρ W hA
  have hW := hA.witness
  have hρ := hA.rate
  refine ⟨stackCommitted W ρ, wins_commitStack hW hρ, ?_⟩
  intro oodPoint link claims kp ks hood hcl hmem hlr hkr H1 H2 H3 H4 H5
  obtain ⟨-, steps, -, -, hl, -⟩ := witness?_spec hW
  have hS := stack_size_witness hW
  have hadm := admissible_witness hW hρ
  have hnotOut : ∀ c < 3, ¬ (globalColumnBases.getD opKeccak 0 + keccakOut ≤ c ∧
      c < globalColumnBases.getD opKeccak 0 + keccakOut + keccakStateLanes) := fun c hc ↦ by
    rw [keccakBase_eq]; omega
  obtain ⟨pq, hpq⟩ : ∃ p, W.layout.placements.getD qkeccak none = some p :=
    Option.isSome_iff_exists.mp (placement_isSome hl (by decide) (hnotOut _ (by decide)))
  obtain ⟨p0, hp0⟩ : ∃ p, W.layout.placements.getD memory0 none = some p :=
    Option.isSome_iff_exists.mp (placement_isSome hl (by decide) (hnotOut _ (by decide)))
  obtain ⟨p1, hp1⟩ : ∃ p, W.layout.placements.getD memory1 none = some p :=
    Option.isSome_iff_exists.mp (placement_isSome hl (by decide) (hnotOut _ (by decide)))
  have hvq : pq.variableCount = W.layout.tableLogHeights.getD opKeccak 0 + qkeccakSlotBits :=
    (placement_variableCount hl hpq).trans (columnKappas_memory _ _).2.2
  have hv0 : p0.variableCount = W.layout.logMemory :=
    (placement_variableCount hl hp0).trans (columnKappas_memory _ _).1
  have hv1 : p1.variableCount = W.layout.logMemory :=
    (placement_variableCount hl hp1).trans (columnKappas_memory _ _).2.1
  simp only [hpq, hp0, hp1, Option.getD_some, LeanVM.Protocol.Verifier.liftOption, memoryTermClaim, ringSwitch, ringFast,
    VerifierProgram.grindProofOfWork, Script.grindBits,
    show Whir.batchGrindingBits ≠ 0 by decide, ↓reduceIte, VerifierProgram.bind_eq,
    Script.bind_eq, VerifierProgram.ret_bind, VerifierProgram.pure_eq, Script.pure_eq,
    VerifierProgram.bind_assoc, Script.bind_assoc]
  have hm : decide (1 < [keccakRingClaim pq kp ks, link.ring].length) = true := rfl
  simp only [hm, ↓reduceIte]
  refine Wins.grind (by decide) ?_
  intro ys hys
  simp only [Bool.true_and, Script.bind]
  have hqa : (stackColumn W hS).values.toArray = W.stack := rfl
  set f := List.take ringMapWidth ys
  set g := List.take ringMapWidth (List.drop ringMapWidth ys)
  set rho := (List.drop (2 * ringMapWidth) ys).getD 0 0
  set batching := (List.drop (2 * ringMapWidth) ys).getD 1 0
  have hf : f.length = ringMapWidth := by simp [f, hys, ringMapWidth]
  have hg : g.length = ringMapWidth := by simp [g, hys, ringMapWidth]
  have hpq' : kp.length = pq.variableCount := H3.trans hvq.symm
  have hmp0 : link.memoryPoint.length = p0.variableCount := H2.trans hv0.symm
  have hmp1 : link.memoryPoint.length = p1.variableCount := H2.trans hv1.symm
  obtain ⟨hrm, hrml, hrh⟩ := hring W.layout.stackLog (stackColumn W hS)
      (keccakRingClaim pq kp ks) link.ring f g rho hf hg (by
    intro rc hrc
    rw [hqa]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrc
    rcases hrc with rfl | rfl
    · refine ⟨keccakRingClaim_holdsOn hW hpq hkr, fun piece hpiece ↦ ?_⟩
      simp only [keccakRingClaim, List.mem_singleton] at hpiece
      subst hpiece
      exact ⟨pq, rfl, partOK_witness hW hpq hpq' 1⟩
    · refine ⟨hlr, fun piece hpiece ↦ ?_⟩
      obtain ⟨c, p, hp, hpl, hpt⟩ := H4 piece hpiece
      exact ⟨p, hpl, partOK_witness hW hp hpt piece.scale⟩)
  have hv0' : p0.variableCount ≤ W.layout.stackLog := (partOK_witness hW hp0 hmp0 1).2.1
  have hv1' : p1.variableCount ≤ W.layout.stackLog := (partOK_witness hW hp1 hmp1 1).2.1
  have hM : List.Forall₂ (fun d c ↦ DescMatches W.layout.stackLog d c.1)
      (ClaimDesc.ring [keccakRingClaim pq kp ks, link.ring] f g rho ::
        ClaimDesc.cells [(p0, link.memoryPoint, link.memoryScales.1),
          (p1, link.memoryPoint, link.memoryScales.2)] ::
        List.filterMap (fun c ↦ Option.map (fun p ↦ ClaimDesc.cells [(p, c.point, 1)])
          (W.layout.placements.getD c.column none)) claims ++ [ClaimDesc.ood oodPoint])
      (ringMerge [keccakRingClaim pq kp ks, link.ring] f g rho ::
        memoryClaimOf W link p0 p1 :: List.filterMap (fun x ↦ x.onStack W.layout) claims ++
        [((fun x ↦ eqEval oodPoint x), mleK W.stack oodPoint)]) :=
    List.Forall₂.cons hrm (List.Forall₂.cons (descMatches_memory hW hp0 hp1 hmp0 hmp1)
      (forall₂_append (descMatches_columns hW claims H1)
        (List.Forall₂.cons (descMatches_ood hood) List.Forall₂.nil)))
  have hlenV : (ringMerge [keccakRingClaim pq kp ks, link.ring] f g rho ::
        memoryClaimOf W link p0 p1 :: List.filterMap (fun x ↦ x.onStack W.layout) claims ++
        [((fun x ↦ eqEval oodPoint x), mleK W.stack oodPoint)]).length ≤ maxStackedClaims := by
    have := List.length_filterMap_le (fun x ↦ x.onStack W.layout) claims
    have h512 : maxStackedClaims = 512 := rfl
    simp only [List.length_cons, List.length_append, List.length_nil, h512]
    omega
  have hholds : ∀ c ∈ (ringMerge [keccakRingClaim pq kp ks, link.ring] f g rho ::
        memoryClaimOf W link p0 p1 :: List.filterMap (fun x ↦ x.onStack W.layout) claims ++
        [((fun x ↦ eqEval oodPoint x), mleK W.stack oodPoint)]),
      StackClaim.Holds W.layout.stackLog c (stackColumn W hS) ∧
        IsMultilinearFn W.layout.stackLog c.1 := by
    intro c hc
    rcases List.mem_cons.mp hc with h | hc
    · subst h; exact ⟨hrh, hrml⟩
    rcases List.mem_cons.mp hc with h | hc
    · subst h; exact memoryClaim_facts hW hS hp0 hp1 hmp0 hmp1 hmem
    rcases List.mem_append.mp hc with hc | hc
    · exact column_facts hW hS hcl H1 c hc
    · rw [List.mem_singleton] at hc
      subst hc
      exact ood_facts hS hood
  have hμ6 : 6 ≤ W.layout.stackLog := le_trans (by decide) hadm.1
  have hc : stackCommitted W ρ =
      Whir.Complete.stackCommitted W.layout.stackLog ρ (stackColumn W hS) := by
    obtain ⟨q₀, rest, hcl', -⟩ := exists_ladder hadm
    simp only [stackCommitted, hcl', levelShape, Whir.Complete.stackCommitted, laneBits]
    rfl
  rw [hc]
  refine Wins.mono (fun _ _ _ _ _ ↦ trivial) _ _ _ _ (follows_stackedOpening hadm
    (stackColumn W hS) _ batching hlenV (fun c hc ↦ (hholds c hc).1) (fun c hc ↦ (hholds c hc).2)
    _ ?_)
  rw [toList_basisTableA hμ6 _ _ _ hM (by simp only [powers, length_powersFrom']),
    hM.length_eq]

end Witness

end LeanVM.Prover

end
