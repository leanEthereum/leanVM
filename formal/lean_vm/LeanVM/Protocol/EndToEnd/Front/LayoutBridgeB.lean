/-
  LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB

  The layout facts the public-input bridge assumes, proved at the verifier's layout and the
  leanISA instance: the reading of a candidate as the instance's stack, the memory claims at the
  public point, and the `KECCAK` height.
-/

module

public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.EndToEnd.Front.PubPhase

/-!
# Layout facts for the public input

The public-input bridge (`PubPhase`) takes facts about the verifier's layout as hypotheses. At
`layout = verifierLayout prog s` and the leanISA instance at `s`:

* `toI`: a stack on the layout's `stackLog` variables read on the instance's `μ`, the cast along
  `stackLog_verifierLayout`;
* `pubLayoutHyp_verifierLayout`: the program's claim on memory column `j < 3` at `(r, 0, …, 0)` is
  the instance's claim on `MEM_j` at `linePoint r`;
* `tableLogHeights_keccak`: the layout's `KECCAK` height is `τ_KECCAK`.

The memory columns are committed columns.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Stacks on equal numbers of variables -/

/-- A stack on `a` variables read on `b = a`. -/
def castColumn {a b : ℕ} (h : a = b) (q : Column a) : Column b :=
  ⟨Vector.cast (congrArg (2 ^ ·) h) q.values⟩

/-- A stack claim holds of a stack exactly when it holds of the stack read on equal variables. -/
theorem holds_castColumn {a b : ℕ} (h : a = b) (c : StackClaim) (q : Column a) :
    StackClaim.Holds a c q ↔ StackClaim.Holds b c (castColumn h q) := by
  subst h
  simp [castColumn]

/-- Pairing the equality weight of `z` with a stack is the stack's extension at `z`. -/
theorem sum_eqEval_mul {μ : ℕ} (z : Vector E μ) (q : Column μ) :
    ∑ x : Fin (2 ^ μ), eqEval z.toList (boolPoint μ x) * ofK (q.values.getD x 0) =
      eval₂Mle q.values (algebraMap K E) z := by
  rw [eval₂Mle, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [eqEval_boolPoint, mul_comm]
  simp [CMlPolynomialEval.map, Vector.getD, x.isLt]

variable (prog : LeanIsaProgram) (s : Sizes)

/-- **A candidate read on the instance's stack**: the cast along `stackLog_verifierLayout`. -/
def toI (q : Column (verifierLayout prog s).stackLog) : Column (leanIsaμ prog s) :=
  castColumn (stackLog_verifierLayout prog s) q

/-! ## Reading a claim of the program -/

/-- **A claim of the program, read on a candidate** (the wire's reading): a claim on a `KECCAK`
output lane, which the layout does not place, is read as the claim on the derived column it names
(lane `column − 113`, at the point, on `τ_KECCAK` variables); every other claim on the stack, at
its placement (`ColumnClaim.onStack`). -/
def WireHolds (c : Verifier.ColumnClaim) (q : Column (verifierLayout prog s).stackLog) : Prop :=
  if c.column ∈ keccakOutputColumns then
    ∃ hl : c.point.length = s.τ 5,
      eval₂Mle ((leanIsaInstance prog s).column (toI prog s q)
          (outCol ⟨(c.column - 113) % 25, Nat.mod_lt _ (by norm_num)⟩)).values (algebraMap K E)
        (⟨c.point.toArray, by simpa using hl⟩ : Vector E (s.τ 5)) = c.value
  else StackClaim.Holds (verifierLayout prog s).stackLog (c.stackClaim (verifierLayout prog s)) q

/-- A claim off the output lanes is read on the stack. -/
theorem wireHolds_of_not_mem {c : Verifier.ColumnClaim} (hc : c.column ∉ keccakOutputColumns)
    (q : Column (verifierLayout prog s).stackLog) :
    WireHolds prog s c q ↔
      StackClaim.Holds (verifierLayout prog s).stackLog (c.stackClaim (verifierLayout prog s)) q := by
  unfold WireHolds
  rw [ite_eq_right hc]

/-- An output lane is `outCol` of its lane. -/
theorem eq_outCol_of_isOut {c : Col} (h : IsOut c) :
    c = outCol ⟨(refCol c - 113) % 25, Nat.mod_lt _ (by norm_num)⟩ := by
  obtain ⟨-, -, -, hv⟩ := refCol_lanes c
  have hp := hv h.isVirtual
  obtain ⟨j, i⟩ := c
  obtain ⟨hj, h1, h2⟩ := h
  simp only at hj h1 h2 hp
  subst hj
  simp only [outCol, Sigma.mk.injEq, heq_eq_eq, true_and]
  ext
  simp only [hp]
  omega

/-- **The wire's reading of a claim on an instance column is the instance's claim**: the program's
claim on global column `refCol col` at `z` holds of a candidate exactly when the instance's claim on
`col` holds of its reading, output lanes included. -/
theorem wireHolds_iff (col : Col) (z : Vector E (kappa prog s col)) (v : E)
    (q : Column (verifierLayout prog s).stackLog) :
    WireHolds prog s ⟨refCol col, z.toList, v⟩ q ↔
      (⟨col, z, v⟩ : LeanVM.Protocol.ColumnClaim (leanIsaInstance prog s)).Holds (toI prog s q) := by
  by_cases ho : IsOut col
  · have hm : refCol col ∈ keccakOutputColumns := (mem_keccakOutputColumns_pyCol col).mpr ho
    have he := eq_outCol_of_isOut ho
    unfold WireHolds
    rw [ite_eq_left hm]
    simp only
    generalize hl : (⟨(refCol col - 113) % 25, Nat.mod_lt _ (by norm_num)⟩ : Fin 25) = l at he ⊢
    subst he
    unfold LeanVM.Protocol.ColumnClaim.Holds
    constructor
    · rintro ⟨hl, h⟩
      exact h
    · intro h
      exact ⟨by simp; rfl, h⟩
  · have hm : refCol col ∉ keccakOutputColumns := (mem_keccakOutputColumns_pyCol col).not.mpr ho
    rw [wireHolds_of_not_mem prog s hm, holds_castColumn (stackLog_verifierLayout prog s)]
    exact onStack_holds_iff prog s col ho z v (toI prog s q)

/-! ## The facts -/

/-- **The `KECCAK` height** of the verifier's layout is `τ_KECCAK`. -/
theorem tableLogHeights_keccak :
    (verifierLayout prog s).tableLogHeights.getD opKeccak 0 = s.τ 5 := by
  simp [verifierLayout, tableLogs, opKeccak]

/-- The memory columns are committed. -/
theorem not_isVirtual_memCol (i : Fin 4) : ¬ IsVirtual (memCol i) := by
  revert i; decide

/-- The public point of the program is the instance's line point. -/
theorem pubPoint_eq (r : E) :
    pubPoint (verifierLayout prog s) r = (PublicInput.linePoint s.logMem_pos r).toList := by
  have hv : ((verifierLayout prog s).placement memory0).variableCount = s.logMem := by
    have h := placement_committed prog s (memCol 0) (not_isVirtual_memCol 0)
    rw [refCol_memCol] at h
    simp only [Fin.val_zero] at h
    rw [show memory0 = 0 from rfl, h]
    rfl
  rw [pubPoint, hv]
  apply List.ext_getElem (by simp; have := s.logMem_pos; omega)
  intro i h1 h2
  simp only [PublicInput.linePoint, Vector.toList_cast, Vector.toList_append]
  rcases i with _ | i
  · simp
  · simp

/-- **The memory claims at the public point** (`pubLayoutHyp`): the program's claim on memory
column `j < 3` at `(r, 0, …, 0)` holding of a candidate is the instance's claim on `MEM_j` at
`linePoint r` holding of its reading. -/
theorem pubLayoutHyp_verifierLayout :
    pubLayoutHyp prog s (verifierLayout prog s) (toI prog s) (WireHolds prog s) := by
  intro j r v q h
  have hcol : (j.val : ℕ) = refCol (memCol j.castSucc) := by
    rw [refCol_memCol]; rfl
  rw [hcol, pubPoint_eq] at h
  exact (wireHolds_iff prog s (memCol j.castSucc) (PublicInput.linePoint s.logMem_pos r) v q).mp h

end
end LeanVM.Protocol.EndToEnd.Front
