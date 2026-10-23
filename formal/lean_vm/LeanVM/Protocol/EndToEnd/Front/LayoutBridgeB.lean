/-
  LeanVM.Protocol.EndToEnd.Front.LayoutBridgeB

  The layout facts the public-input, Flock and ring-switching bridge assumes, proved at the
  verifier's layout and the leanISA instance: the reading of a candidate as the instance's stack,
  the memory claims at the public point, the `QFLOCK` weight, and the `BLAKE2S` height.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutInstance
public import LeanVM.Protocol.EndToEnd.Front.PubPhase
public import LeanVM.Protocol.EndToEnd.Front.RingFidelity

/-!
# Layout facts for the public input and ring switching

The public-input, Flock and ring-switching bridge (`PubPhase`, `FlockBridge`, `RingFidelity`)
takes four facts about the verifier's layout as hypotheses. At `layout = verifierLayout prog s`
and the leanISA instance at `s`:

* `toI`: a stack on the layout's `stackLog` variables read on the instance's `μ`, the cast along
  `stackLog_verifierLayout`;
* `pubLayoutHyp_verifierLayout`: the program's claim on memory column `j < 3` at `(r, 0, …, 0)` is
  the instance's claim on `MEM_j` at `linePoint r`;
* `ringLayoutHyp_verifierLayout`: the program's weight of the `QFLOCK` placement at a point of the
  region, paired with a stack, is the stack's extension at the point lifted by the instance;
* `tableLogHeights_blake2s`: the layout's `BLAKE2S` height is `τ_BLAKE2S`.

Memory columns and `QFLOCK` are committed columns, so these hold for every Flock specification:
the deployed slots only place the `BLAKE2S` limbs.
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

/-- `eq_eval` splits over concatenations of equal-length prefixes. -/
theorem eqEval_append (a b c d : List E) (h : a.length = c.length) :
    eqEval (a ++ b) (c ++ d) = eqEval a c * eqEval b d := by
  rw [eqEval_eq_list_prod, eqEval_eq_list_prod, eqEval_eq_list_prod, List.zipWith_append h,
    List.prod_append]

variable (prog : Program) (s : Sizes)

/-- **A candidate read on the instance's stack**: the cast along `stackLog_verifierLayout`. -/
def toI (q : Column (verifierLayout prog s).stackLog) : Column (leanIsaμ prog s) :=
  castColumn (stackLog_verifierLayout prog s) q

/-! ## Committed columns, for any Flock specification -/

/-- A placed point of a committed column is the instance's lifted point, for any slots. -/
theorem stackPoint_eq_extend_committed (F : FlockSpec) (c : Col) (hc : ¬ IsLimb c)
    (z : Vector E (kappa prog s c)) :
    ((verifierLayout prog s).placements.getD (pyCol c) default).stackPoint z.toList
        (verifierLayout prog s).stackLog =
      ((leanIsaInstance F prog s).layout.extend c z).toList := by
  rw [stackLog_verifierLayout]
  show _ = ((LeanIsa.layout prog s F.slot).extend c z).toList
  rw [placement_committed prog s c hc, extend_committed prog s _ c hc, stackPoint_aligned]

/-- **A verifier claim on a committed column means the instance's claim**, for any slots. -/
theorem onStack_holds_iff_committed (F : FlockSpec) (c : Col) (hc : ¬ IsLimb c)
    (z : Vector E (kappa prog s c)) (v : E) (q : Column (leanIsaμ prog s)) :
    StackClaim.Holds (leanIsaμ prog s)
        ((⟨pyCol c, z.toList, v⟩ : Verifier.ColumnClaim).onStack (verifierLayout prog s)) q ↔
      (⟨c, z, v⟩ : LeanVM.Protocol.ColumnClaim (leanIsaInstance F prog s)).Holds q := by
  unfold Verifier.ColumnClaim.onStack
  simp only
  rw [stackPoint_eq_extend_committed prog s F c hc z, stackClaim_holds_eqEval_iff]
  unfold LeanVM.Protocol.ColumnClaim.Holds M3Instance.column
  rw [(leanIsaInstance F prog s).layout.read_eval]

/-! ## The four facts -/

/-- **The `BLAKE2S` height** of the verifier's layout is `τ_BLAKE2S`. -/
theorem tableLogHeights_blake2s :
    (verifierLayout prog s).tableLogHeights.getD opBlake2s 0 = s.τ 5 := by
  simp [verifierLayout, tableLogs, opBlake2s]

/-- The memory columns are committed. -/
theorem not_isLimb_memCol (i : Fin 4) : ¬ IsLimb (memCol i) := by
  revert i; decide

/-- The public point of the program is the instance's line point. -/
theorem pubPoint_eq (r : E) :
    pubPoint (verifierLayout prog s) r = (PublicInput.linePoint s.logMem_pos r).toList := by
  have hv : ((verifierLayout prog s).placements.getD memory0 default).vars = s.logMem := by
    have h := placement_committed prog s (memCol 0) (not_isLimb_memCol 0)
    rw [pyCol_memCol] at h
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
theorem pubLayoutHyp_verifierLayout (F : FlockSpec) :
    pubLayoutHyp F prog s (verifierLayout prog s) (toI prog s) := by
  intro j r v q h
  have hcol : (j.val : ℕ) = pyCol (memCol j.castSucc) := by
    rw [pyCol_memCol]; rfl
  rw [hcol, pubPoint_eq, holds_castColumn (stackLog_verifierLayout prog s)] at h
  exact (onStack_holds_iff_committed prog s F (memCol j.castSucc) (not_isLimb_memCol _)
    (PublicInput.linePoint s.logMem_pos r) v (toI prog s q)).mp h

/-- A stack's extension read on equal variables. -/
theorem eval₂Mle_castColumn {a b : ℕ} (h : a = b) (q : Column a) (v : Vector E b) :
    eval₂Mle (castColumn h q).values (algebraMap K E) v =
      eval₂Mle q.values (algebraMap K E) (Vector.cast h.symm v) := by
  subst h
  simp [castColumn]

/-- An aligned placement's weight at a cube point: the equality with the placed point. -/
theorem eqAbove_mul_eqEval (v off μ : ℕ) (hv : v ≤ μ) (p : List E) (hp : p.length = v)
    (x : ℕ) :
    ({ vars := v, index := off } : Placement).eqAbove (boolPoint μ x) *
        eqEval p ((boolPoint μ x).take v) =
      eqEval (({ vars := v, index := off } : Placement).stackPoint p μ) (boolPoint μ x) := by
  rw [stackPoint_aligned, ← List.take_append_drop v (boolPoint μ x),
    eqEval_append _ _ _ _ (by simp [hp]; omega), List.take_append_drop, mul_comm]
  congr 1
  simp only [Placement.eqAbove, zero_add, length_boolPoint, Nat.sub_zero,
    selectorPoint_eq_boolPoint, Nat.shiftRight_eq_div_pow]

/-- **The `QFLOCK` weight** (`ringLayoutHyp`): the program's weight of the `QFLOCK` placement at a
point of the region, paired with a candidate, is its reading's extension at the point lifted by
the instance's layout. -/
theorem ringLayoutHyp_verifierLayout (F : FlockSpec) :
    ringLayoutHyp F prog s (verifierLayout prog s) (toI prog s) := by
  intro p hp q
  have hP := placement_committed prog s flockCol not_isLimb_flockCol
  rw [pyCol_flockCol] at hP
  rw [hP]
  let z' : Vector E (kappa prog s flockCol) := toVec _ p
  have hz' : z'.toList = p := by
    apply List.ext_getElem (by simp [z', hp]; rfl)
    intro i h1 h2
    simp [z', toVec, List.getElem?_eq_getElem h2]
  have hsp := stackPoint_eq_extend_committed prog s F flockCol not_isLimb_flockCol z'
  rw [pyCol_flockCol, hP, hz'] at hsp
  have hle : kappa prog s flockCol ≤ (verifierLayout prog s).stackLog := by
    rw [stackLog_verifierLayout]
    have h := Blocks.size_le _ (blocks_fits prog s) (flockBlock prog s)
    rw [size_flockBlock] at h
    exact h
  have hpt : ∀ x : Fin (2 ^ (verifierLayout prog s).stackLog),
      ({ vars := kappa prog s flockCol,
          index := (blocks prog s).offset (LeanIsa.blockOf flockCol not_isLimb_flockCol) } :
          Placement).eqAbove (boolPoint (verifierLayout prog s).stackLog x) *
        eqEval p ((boolPoint (verifierLayout prog s).stackLog x).take (kappa prog s flockCol)) =
      eqEval (Vector.cast (stackLog_verifierLayout prog s).symm
        ((leanIsaInstance F prog s).layout.extend flockCol z')).toList
        (boolPoint (verifierLayout prog s).stackLog x) := fun x ↦ by
    rw [eqAbove_mul_eqEval _ _ _ hle p (by rw [hp]; rfl), hsp, Vector.toList_cast]
  simp only [hpt]
  rw [sum_eqEval_mul, toI, eval₂Mle_castColumn]
  rfl

end
end LeanVM.Protocol.EndToEnd.Front
