/-
  LeanVM.Protocol.ToArkLib.Flock.Tables

  The tables of a Flock argument for a batch of Boolean R1CS blocks, and the identities its
  zerocheck and lincheck rest on: the constraint residuals, the univariate skip's polynomial and
  its interpolation, the lincheck's tables and the block-diagonal identity, and the native
  lincheck terminal. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.BlockR1CS
public import LeanVM.Protocol.ToCompPoly.Interpolation

/-!
# The tables of a Flock argument

A batch of `2 ^ κ` blocks of `2 ^ (s + m)` positions is stored as `2 ^ s` tables `z i` on the
other `m + κ` coordinates (`BlockR1CS.batchBlock`); the univariate skip replaces the low `s`
coordinates by one variable `Y` interpolated over `2 ^ s` nodes (Annex C, §C.2). Over a field
`F`:

* **Residuals.** `leftTable`, `rightTable` lay the rows `A z_t`, `B z_t` of every block out like
  the witness; `errTable i = a_i · b_i - z_i` and `constTable t = 1 - z_t(cpos)` vanish exactly
  when every block satisfies the constraints and the constant position (`batchHolds_iff`).
* **The skip.** `skipTable T Y` is the quirky extension of a family of tables at `Y`, the
  Lagrange combination `Σ_i L_i(Y) · T_i` over the skip nodes; `zcFun Y` is
  `â(Y, ·) · b̂(Y, ·) - ẑ(Y, ·)`, and `pValue r Y = Σ_u eq(r, u) · zcFun Y u` is the
  polynomial `P(Y)` of degree below `2 · 2 ^ s` (`pPoly`, `natDegree_pPoly_le`) the zerocheck's
  first message describes. At a skip node it is the residual's extension (`pValue_skipNode`), so
  zeros there are what the R1CS gives; and the verifier's value `skipClaim`, interpolating zeros
  on the skip nodes and the received values on their coset, is `P` itself when the received
  values are `P`'s (`skipClaim_skipMessage`).

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval Polynomial BlockR1CS

@[expose] public section

variable {F : Type*} [Field F] {s m κ : ℕ}

/-! ## Residuals -/

/-- The left products laid out like the witness: entry `cubeIndex jin t` of table `i` is row
`cubeIndex i jin` of `A` applied to block `t`. -/
def leftTable (C : BlockR1CS F (s + m)) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (i : Fin (2 ^ s)) : CMlPolynomialEval F (m + κ) :=
  Vector.ofFn fun u ↦
    (C.rows (batchBlock z ((cubeSplit m κ).symm u).2)).1[cubeIndex i ((cubeSplit m κ).symm u).1]

/-- The right products laid out like the witness. -/
def rightTable (C : BlockR1CS F (s + m)) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (i : Fin (2 ^ s)) : CMlPolynomialEval F (m + κ) :=
  Vector.ofFn fun u ↦
    (C.rows (batchBlock z ((cubeSplit m κ).symm u).2)).2[cubeIndex i ((cubeSplit m κ).symm u).1]

/-- The constraint residual `a · b - z`, laid out like the witness. -/
def errTable (C : BlockR1CS F (s + m)) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (i : Fin (2 ^ s)) : CMlPolynomialEval F (m + κ) :=
  Vector.ofFn fun u ↦ (leftTable C z i)[u] * (rightTable C z i)[u] - (z i)[u]

/-- The constant position's residual `1 - z_t(cpos)`, one entry per block. -/
def constTable (cpos : Fin (2 ^ (s + m))) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) :
    CMlPolynomialEval F κ :=
  Vector.ofFn fun t ↦ 1 - (batchBlock z t)[cpos]

private theorem cubeSplit_symm_cubeIndex {a b : ℕ} (i : Fin (2 ^ a)) (j : Fin (2 ^ b)) :
    (cubeSplit a b).symm (cubeIndex i j) = (i, j) := by
  rw [← cubeSplit_apply, Equiv.symm_apply_apply]

theorem leftTable_cubeIndex (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (i : Fin (2 ^ s)) (jin : Fin (2 ^ m))
    (t : Fin (2 ^ κ)) :
    (leftTable C z i)[cubeIndex jin t] = (C.rows (batchBlock z t)).1[cubeIndex i jin] := by
  simp only [leftTable, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    cubeSplit_symm_cubeIndex]

theorem rightTable_cubeIndex (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (i : Fin (2 ^ s)) (jin : Fin (2 ^ m))
    (t : Fin (2 ^ κ)) :
    (rightTable C z i)[cubeIndex jin t] = (C.rows (batchBlock z t)).2[cubeIndex i jin] := by
  simp only [rightTable, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    cubeSplit_symm_cubeIndex]

theorem errTable_getElem (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (i : Fin (2 ^ s)) (u : Fin (2 ^ (m + κ))) :
    (errTable C z i)[u] = (leftTable C z i)[u] * (rightTable C z i)[u] - (z i)[u] := by
  simp [errTable]

/-- Every block satisfies the constraints and the constant position exactly when every residual
vanishes. -/
theorem batchHolds_iff (C : BlockR1CS F (s + m)) (cpos : Fin (2 ^ (s + m)))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) :
    BatchHolds C cpos z ↔
      (∀ (i : Fin (2 ^ s)) (u : Fin (2 ^ (m + κ))), (errTable C z i)[u] = 0) ∧
        ∀ t : Fin (2 ^ κ), (constTable cpos z)[t] = 0 := by
  constructor
  · intro h
    refine ⟨fun i u ↦ ?_, fun t ↦ ?_⟩
    · obtain ⟨⟨jin, t⟩, rfl⟩ := (cubeSplit m κ).surjective u
      have hb := (h t).1 (cubeIndex i jin)
      rw [batchBlock_cubeIndex] at hb
      rw [cubeSplit_apply, errTable_getElem, leftTable_cubeIndex, rightTable_cubeIndex, hb,
        sub_self]
    · simp only [constTable, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
      rw [show (batchBlock z t)[cpos.val] = (batchBlock z t)[cpos] from rfl, (h t).2, sub_self]
  · rintro ⟨herr, hconst⟩ t
    refine ⟨fun k ↦ ?_, ?_⟩
    · obtain ⟨⟨i, jin⟩, rfl⟩ := (cubeSplit s m).surjective k
      rw [cubeSplit_apply, batchBlock_cubeIndex, ← leftTable_cubeIndex, ← rightTable_cubeIndex]
      have := herr i (cubeIndex jin t)
      rw [errTable_getElem] at this
      exact sub_eq_zero.mp this
    · have := hconst t
      simp only [constTable, Fin.getElem_fin, Vector.getElem_ofFn] at this
      exact (sub_eq_zero.mp this).symm

/-! ## The univariate skip -/

/-- The skip nodes: the first `2 ^ s` of the `2 ^ s + 2 ^ s` nodes; the others are their
coset. -/
def skipNodes (pts : Vector F (2 ^ s + 2 ^ s)) : Vector F (2 ^ s) :=
  Vector.ofFn fun i ↦ pts[i.val]

/-- The nodes of a univariate skip, the `2 ^ s` skip nodes then their coset, with the inverses
of their Lagrange denominators over the skip nodes and over all of them: what a verifier computes
once. -/
structure SkipDomain (F : Type*) [Field F] (s : ℕ) where
  /-- The skip nodes, then their coset. -/
  pts : Vector F (2 ^ s + 2 ^ s)
  /-- The inverse denominators over the skip nodes. -/
  skipInv : Vector F (2 ^ s)
  /-- The inverse denominators over all the nodes. -/
  allInv : Vector F (2 ^ s + 2 ^ s)
  /-- They are the skip nodes' inverse denominators. -/
  skipInv_eq : skipInv = lagrangeInv (skipNodes pts)
  /-- They are all the nodes' inverse denominators. -/
  allInv_eq : allInv = lagrangeInv pts

/-- A skip domain from its nodes, the inverse denominators computed. -/
def SkipDomain.ofPts (pts : Vector F (2 ^ s + 2 ^ s)) : SkipDomain F s :=
  ⟨pts, lagrangeInv (skipNodes pts), lagrangeInv pts, rfl, rfl⟩

/-- The Lagrange weights of the skip nodes at `Y`, from the precomputed denominators. -/
def skipWeights (nodes : SkipDomain F s) (Y : F) : Vector F (2 ^ s) :=
  Vector.ofFn fun i ↦ lagrangeWeightWith (skipNodes nodes.pts) nodes.skipInv Y i

theorem skipWeights_getElem (nodes : SkipDomain F s) (Y : F) (i : Fin (2 ^ s)) :
    (skipWeights nodes Y)[i] = lagrangeWeight (skipNodes nodes.pts) Y i := by
  simp [skipWeights, nodes.skipInv_eq, lagrangeWeightWith_lagrangeInv]

/-- The quirky extension of a family of tables at `Y`: `Σ_i L_i(Y) · T_i`, the Lagrange
combination over the skip nodes. -/
def skipTable {n : ℕ} (nodes : SkipDomain F s) (T : Fin (2 ^ s) → CMlPolynomialEval F n)
    (Y : F) : CMlPolynomialEval F n :=
  let L := skipWeights nodes Y
  Vector.ofFn fun u ↦ ∑ i, L[i] * (T i)[u]

theorem skipTable_getElem {n : ℕ} (nodes : SkipDomain F s)
    (T : Fin (2 ^ s) → CMlPolynomialEval F n) (Y : F) (u : Fin (2 ^ n)) :
    (skipTable nodes T Y)[u] = ∑ i, lagrangeWeight (skipNodes nodes.pts) Y i * (T i)[u] := by
  simp [skipTable, ← skipWeights_getElem]

/-- The zerocheck's summand at the skip value `Y`: `â(Y, v) · b̂(Y, v) - ẑ(Y, v)`. -/
def zcFun (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (Y : F) (v : Vector F (m + κ)) : F :=
  evalMle (skipTable nodes (leftTable C z) Y) v * evalMle (skipTable nodes (rightTable C z) Y) v -
    evalMle (skipTable nodes z Y) v

/-- `P(Y) = Σ_u eq(r, u) · (â(Y, u) · b̂(Y, u) - ẑ(Y, u))`. -/
def pValue (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) (Y : F) : F :=
  let A := skipTable nodes (leftTable C z) Y
  let B := skipTable nodes (rightTable C z) Y
  let Z := skipTable nodes z Y
  evalMle (Vector.ofFn fun u ↦ A[u] * B[u] - Z[u]) r

/-- `P(Y)` is the extension at `r` of the zerocheck's summand on the cube. -/
theorem pValue_eq (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) (Y : F) :
    pValue nodes C z r Y = evalMle (Vector.ofFn fun u ↦ zcFun nodes C z Y (boolVec u)) r := by
  simp only [pValue, zcFun, evalMle_boolVec]

/-- `P` as a polynomial in `Y`. -/
noncomputable def pPoly (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) : F[X] :=
  ∑ u : Fin (2 ^ (m + κ)), Polynomial.C (lagrangeBasis r)[u] *
    ((∑ i, Polynomial.C (leftTable C z i)[u] *
        Lagrange.basis Finset.univ (fun i : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[i]) i) *
      (∑ i, Polynomial.C (rightTable C z i)[u] *
        Lagrange.basis Finset.univ (fun i : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[i]) i) -
      ∑ i, Polynomial.C (z i)[u] *
        Lagrange.basis Finset.univ (fun i : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[i]) i)

private theorem eval_lagrangeSum {n : ℕ} (nodes : SkipDomain F s)
    (T : Fin (2 ^ s) → CMlPolynomialEval F n) (u : Fin (2 ^ n)) (Y : F) :
    (∑ i, Polynomial.C (T i)[u] *
      Lagrange.basis Finset.univ (fun i : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[i]) i).eval Y =
        (skipTable nodes T Y)[u] := by
  rw [skipTable_getElem]
  simp only [eval_finsetSum, eval_mul, eval_C, lagrangeWeight_eq]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The polynomial evaluates to `P(Y)`. -/
theorem eval_pPoly (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) (Y : F) :
    (pPoly nodes C z r).eval Y = pValue nodes C z r Y := by
  rw [pValue_eq, evalMle_eq_sum, pPoly, eval_finsetSum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [eval_mul, eval_C, eval_sub, eval_mul, eval_lagrangeSum, eval_lagrangeSum, eval_lagrangeSum]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, zcFun, evalMle_boolVec]
  ring

private theorem natDegree_lagrangeSum_le {n : ℕ} (nodes : SkipDomain F s)
    (T : Fin (2 ^ s) → CMlPolynomialEval F n) (u : Fin (2 ^ n)) :
    (∑ i, Polynomial.C (T i)[u] *
      Lagrange.basis Finset.univ (fun i : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[i]) i).natDegree ≤
        2 ^ s - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ 1 fun j _ ↦ ?_).trans ?_
  · unfold Lagrange.basisDivisor
    refine (natDegree_C_mul_le _ _).trans ?_
    exact natDegree_X_sub_C_le _
  · rw [smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]

/-- `P` has degree at most `2 · (2 ^ s - 1)`, below the `2 · 2 ^ s` nodes. -/
theorem natDegree_pPoly_le (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) :
    (pPoly nodes C z r).natDegree ≤ 2 * (2 ^ s - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun u _ ↦ (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_mul_le).trans ?_
    have h₁ := natDegree_lagrangeSum_le nodes (leftTable C z) u
    have h₂ := natDegree_lagrangeSum_le nodes (rightTable C z) u
    omega
  · have := natDegree_lagrangeSum_le nodes z u
    omega

theorem degree_pPoly_lt (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) :
    (pPoly nodes C z r).degree < ((2 ^ s + 2 ^ s : ℕ) : WithBot ℕ) := by
  refine (degree_le_natDegree).trans_lt ?_
  have := natDegree_pPoly_le nodes C z r
  have hpos := Nat.two_pow_pos s
  have h : (pPoly nodes C z r).natDegree < 2 ^ s + 2 ^ s := by omega
  exact_mod_cast h

/-- At a skip node the Lagrange weights select that node. -/
theorem lagrangeWeight_skipNode (nodes : SkipDomain F s)
    (hnodes : Function.Injective fun j : Fin (2 ^ s + 2 ^ s) ↦ nodes.pts[j]) (i i' : Fin (2 ^ s)) :
    lagrangeWeight (skipNodes nodes.pts) nodes.pts[i.val] i' = if i' = i then 1 else 0 := by
  have hinj : Set.InjOn (fun j : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[j])
      ↑(Finset.univ : Finset (Fin (2 ^ s))) := by
    intro a _ b _ hab
    simp only [skipNodes, Fin.getElem_fin, Vector.getElem_ofFn] at hab
    have := @hnodes ⟨a.val, by have := a.isLt; omega⟩ ⟨b.val, by have := b.isLt; omega⟩ hab
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hnode : nodes.pts[i.val] = (skipNodes nodes.pts)[i] := by simp [skipNodes]
  rw [hnode, lagrangeWeight_eq]
  split
  · subst_vars
    exact Lagrange.eval_basis_self (v := fun j : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[j]) hinj
      (Finset.mem_univ _)
  · exact Lagrange.eval_basis_of_ne (v := fun j : Fin (2 ^ s) ↦ (skipNodes nodes.pts)[j])
      (by assumption) (Finset.mem_univ _)

/-- At a skip node, the quirky extension is the table at that node. -/
theorem skipTable_skipNode {n : ℕ} (nodes : SkipDomain F s)
    (hnodes : Function.Injective fun j : Fin (2 ^ s + 2 ^ s) ↦ nodes.pts[j])
    (T : Fin (2 ^ s) → CMlPolynomialEval F n) (i : Fin (2 ^ s)) :
    skipTable nodes T nodes.pts[i.val] = T i := by
  apply Vector.ext
  intro u hu
  have := skipTable_getElem nodes T nodes.pts[i.val] ⟨u, hu⟩
  simp only [lagrangeWeight_skipNode nodes hnodes, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at this
  simpa using this

/-- At a skip node, `P` is the residual's extension at `r`. -/
theorem pValue_skipNode (nodes : SkipDomain F s)
    (hnodes : Function.Injective fun j : Fin (2 ^ s + 2 ^ s) ↦ nodes.pts[j])
    (C : BlockR1CS F (s + m)) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (r : Vector F (m + κ)) (i : Fin (2 ^ s)) :
    pValue nodes C z r nodes.pts[i.val] = evalMle (errTable C z i) r := by
  simp only [pValue, skipTable_skipNode nodes hnodes]
  rfl

/-- The prover's first message: `P` on the coset of the skip nodes. -/
def skipMessage (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (r : Vector F (m + κ)) : Vector F (2 ^ s) :=
  Vector.ofFn fun k ↦ pValue nodes C z r nodes.pts[2 ^ s + k.val]

/-- The verifier's value at `Y` of the polynomial with zeros on the skip nodes and the received
values on their coset. -/
def skipClaim (nodes : SkipDomain F s) (msg : Vector F (2 ^ s)) (Y : F) : F :=
  interpolateWith nodes.pts nodes.allInv (Vector.replicate (2 ^ s) (0 : F) ++ msg) Y

/-- **The skip round is complete.** When the residuals' extensions vanish at `r`, the verifier's
interpolated value of the honest message is `P` itself. -/
theorem skipClaim_skipMessage (nodes : SkipDomain F s)
    (hnodes : Function.Injective fun j : Fin (2 ^ s + 2 ^ s) ↦ nodes.pts[j])
    (C : BlockR1CS F (s + m)) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (r : Vector F (m + κ)) (hzero : ∀ i, evalMle (errTable C z i) r = 0) (Y : F) :
    skipClaim nodes (skipMessage nodes C z r) Y = pValue nodes C z r Y := by
  rw [skipClaim, nodes.allInv_eq, interpolateWith_lagrangeInv, ← eval_pPoly nodes C z r Y]
  rw [← interpolateAt_eval nodes.pts hnodes _ (degree_pPoly_lt nodes C z r) Y]
  congr 1
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, eval_pPoly, Vector.getElem_append]
  split
  · rw [Vector.getElem_replicate]
    have := pValue_skipNode nodes hnodes C z r ⟨j, by assumption⟩
    rw [hzero] at this
    exact this.symm
  · simp only [skipMessage, Vector.getElem_ofFn]
    congr 2
    show 2 ^ s + (j - 2 ^ s) = j
    omega

/-! ## The lincheck -/

/-- The row weights at the quirky point `(Y, χin)`: `e(k) = L_{ksk}(Y) · eq(χin, kin)`, `ksk` the
low `s` bits of `k` and `kin` the high `m`. -/
def eRow (nodes : SkipDomain F s) (Y : F) (χin : Vector F m) :
    CMlPolynomialEval F (s + m) :=
  let L := skipWeights nodes Y
  let Lin := lagrangeBasis χin
  Vector.ofFn fun k ↦ L[((cubeSplit s m).symm k).1] * Lin[((cubeSplit s m).symm k).2]

theorem eRow_cubeIndex (nodes : SkipDomain F s) (Y : F) (χin : Vector F m)
    (i : Fin (2 ^ s)) (jin : Fin (2 ^ m)) :
    (eRow nodes Y χin)[cubeIndex i jin] =
      lagrangeWeight (skipNodes nodes.pts) Y i * (lagrangeBasis χin)[jin] := by
  simp only [eRow, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, cubeSplit_symm_cubeIndex]
  rw [← Fin.getElem_fin, skipWeights_getElem]

/-- The witness folded over the batch at `χout`: entry `j` is `ẑ_{jsk}(jin, χout)`. -/
def zTable (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (χout : Vector F κ) :
    CMlPolynomialEval F (s + m) :=
  Vector.ofFn fun j ↦ evalMle (z ((cubeSplit s m).symm j).1)
    ((boolVec ((cubeSplit s m).symm j).2 : Vector F m) ++ χout)

theorem zTable_cubeIndex (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (χout : Vector F κ)
    (i : Fin (2 ^ s)) (jin : Fin (2 ^ m)) :
    (zTable z χout)[cubeIndex i jin] = evalMle (z i) ((boolVec jin : Vector F m) ++ χout) := by
  simp only [zTable, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, cubeSplit_symm_cubeIndex]

/-- The folded witness is the combination of the blocks by `eq(χout, ·)`. -/
theorem zTable_eq_sum (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (χout : Vector F κ) :
    zTable z χout = Vector.ofFn fun j ↦
      ∑ t ∈ Finset.univ, (lagrangeBasis χout)[t] * (batchBlock z t)[j] := by
  have key : ∀ k : Fin (2 ^ (s + m)), (zTable z χout)[k] =
      ∑ t ∈ Finset.univ, (lagrangeBasis χout)[t] * (batchBlock z t)[k] := by
    intro k
    obtain ⟨⟨i, jin⟩, rfl⟩ := (cubeSplit s m).surjective k
    rw [cubeSplit_apply, zTable_cubeIndex, evalMle_boolVec_append, evalMle_eq_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [sliceLow_getElem, batchBlock_cubeIndex, mul_comm]
  apply Vector.ext
  intro j hj
  simpa [Fin.getElem_fin] using key ⟨j, hj⟩

/-- **The quirky evaluation by rows.** For tables `T` laid out from a family `V` of row vectors,
one per block, the quirky extension at `(Y, χin, χout)` is `Σ_k e(k) Σ_t eq(χout, t) V_t(k)`. -/
theorem evalMle_skipTable_eq (nodes : SkipDomain F s) (Y : F) (χin : Vector F m)
    (χout : Vector F κ) (T : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (V : Fin (2 ^ κ) → CMlPolynomialEval F (s + m))
    (hT : ∀ (i : Fin (2 ^ s)) (jin : Fin (2 ^ m)) (t : Fin (2 ^ κ)),
      (T i)[cubeIndex jin t] = (V t)[cubeIndex i jin]) :
    evalMle (skipTable nodes T Y) (χin ++ χout) =
      ∑ k : Fin (2 ^ (s + m)),
        (eRow nodes Y χin)[k] * ∑ t : Fin (2 ^ κ), (lagrangeBasis χout)[t] * (V t)[k] := by
  rw [evalMle_eq_sum, sum_cube_split, sum_cube_split]
  simp only [lagrangeBasis_cubeIndex, lowVec_append, highVec_append, eRow_cubeIndex,
    skipTable_getElem, hT, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun jin _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
  ring

/-- The `A` part of the lincheck sum is the zerocheck's `â`. -/
theorem sum_colsFst_zTable (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (Y : F) (χin : Vector F m)
    (χout : Vector F κ) :
    ∑ j : Fin (2 ^ (s + m)), (C.cols (eRow nodes Y χin)).1[j] * (zTable z χout)[j] =
      evalMle (skipTable nodes (leftTable C z) Y) (χin ++ χout) := by
  rw [← C.sum_mul_rows_fst, evalMle_skipTable_eq nodes Y χin χout _
    (fun t ↦ (C.rows (batchBlock z t)).1) (fun i jin t ↦ leftTable_cubeIndex C z i jin t),
    zTable_eq_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [C.rows_fst_sum]

/-- The `B` part of the lincheck sum is the zerocheck's `b̂`. -/
theorem sum_colsSnd_zTable (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (Y : F) (χin : Vector F m)
    (χout : Vector F κ) :
    ∑ j : Fin (2 ^ (s + m)), (C.cols (eRow nodes Y χin)).2[j] * (zTable z χout)[j] =
      evalMle (skipTable nodes (rightTable C z) Y) (χin ++ χout) := by
  rw [← C.sum_mul_rows_snd, evalMle_skipTable_eq nodes Y χin χout _
    (fun t ↦ (C.rows (batchBlock z t)).2) (fun i jin t ↦ rightTable_cubeIndex C z i jin t),
    zTable_eq_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [C.rows_snd_sum]

/-- The identity part of the lincheck sum is the zerocheck's `ẑ`. -/
theorem sum_eRow_zTable (nodes : SkipDomain F s) (Y : F) (χin : Vector F m)
    (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (χout : Vector F κ) :
    ∑ j : Fin (2 ^ (s + m)), (eRow nodes Y χin)[j] * (zTable z χout)[j] =
      evalMle (skipTable nodes z Y) (χin ++ χout) := by
  rw [evalMle_skipTable_eq nodes Y χin χout z (batchBlock z)
    (fun i jin t ↦ (batchBlock_cubeIndex z t i jin).symm), zTable_eq_sum]
  simp

/-- The constant position of the folded witness is `1` minus the constant residual's
extension. -/
theorem zTable_cpos (cpos : Fin (2 ^ (s + m))) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (χout : Vector F κ) :
    (zTable z χout)[cpos] = 1 - evalMle (constTable cpos z) χout := by
  have hone := sumCube_lagrangeBasis χout
  simp only [sumCube, Fin.getElem_fin] at hone
  rw [zTable_eq_sum, evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, constTable, Fin.eta, sub_mul, one_mul,
    Finset.sum_sub_distrib, hone, sub_sub_cancel]
  exact Finset.sum_congr rfl fun t _ ↦ mul_comm _ _

/-- The lincheck's column weights at `α`: `(Aᵀ e) + α (Bᵀ e) + α² e + α³ [· = cpos]`. -/
def mTable (C : BlockR1CS F (s + m)) (cpos : Fin (2 ^ (s + m))) (e : CMlPolynomialEval F (s + m))
    (α : F) : CMlPolynomialEval F (s + m) :=
  Vector.ofFn fun j ↦ (C.cols e).1[j] + α * (C.cols e).2[j] + α ^ 2 * e[j] +
    α ^ 3 * if j = cpos then 1 else 0

theorem mTable_getElem (C : BlockR1CS F (s + m)) (cpos : Fin (2 ^ (s + m)))
    (e : CMlPolynomialEval F (s + m)) (α : F) (j : Fin (2 ^ (s + m))) :
    (mTable C cpos e α)[j] = (C.cols e).1[j] + α * (C.cols e).2[j] + α ^ 2 * e[j] +
      α ^ 3 * if j = cpos then 1 else 0 := by
  simp [mTable]

/-- **The block-diagonal identity** (Annex C, Lemma C.1): the lincheck sum is the batch of the
three zerocheck values and the constant position, by the powers of `α`. -/
theorem sum_mTable_zTable (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (cpos : Fin (2 ^ (s + m))) (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ)) (Y : F)
    (χin : Vector F m) (χout : Vector F κ) (α : F) :
    ∑ j : Fin (2 ^ (s + m)), (mTable C cpos (eRow nodes Y χin) α)[j] * (zTable z χout)[j] =
      evalMle (skipTable nodes (leftTable C z) Y) (χin ++ χout) +
        α * evalMle (skipTable nodes (rightTable C z) Y) (χin ++ χout) +
        α ^ 2 * evalMle (skipTable nodes z Y) (χin ++ χout) +
        α ^ 3 * (1 - evalMle (constTable cpos z) χout) := by
  rw [← sum_colsFst_zTable, ← sum_colsSnd_zTable, ← sum_eRow_zTable, ← zTable_cpos,
    Finset.mul_sum, Finset.mul_sum]
  simp only [mTable_getElem, add_mul, Finset.sum_add_distrib, mul_assoc, ite_mul, one_mul,
    zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The lincheck's summand on `m` coordinates: `Σ_i M̃_i(v) · Z̃_i(v)`, the slices at each low
index. -/
def linFun (M Z : CMlPolynomialEval F (s + m)) (v : Vector F m) : F :=
  ∑ i, evalMle (sliceLow M i) v * evalMle (sliceLow Z i) v

/-- Summed over the cube, the lincheck's summand is the inner product of the two tables. -/
theorem sum_linFun_boolVec (M Z : CMlPolynomialEval F (s + m)) :
    ∑ jin : Fin (2 ^ m), linFun M Z (boolVec jin) = ∑ j : Fin (2 ^ (s + m)), M[j] * Z[j] := by
  rw [sum_cube_split]
  refine Finset.sum_congr rfl fun jin _ ↦ ?_
  simp only [linFun, evalMle_boolVec, sliceLow_getElem]

/-- The slices of the folded witness extend to the witness at `(p, χout)`. -/
theorem evalMle_sliceLow_zTable (z : Fin (2 ^ s) → CMlPolynomialEval F (m + κ))
    (χout : Vector F κ) (i : Fin (2 ^ s)) (p : Vector F m) :
    evalMle (sliceLow (zTable z χout) i) p = evalMle (z i) (p ++ χout) := by
  rw [evalMle_split_low, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun jin _ ↦ ?_
  rw [sliceLow_getElem, zTable_cubeIndex, mul_comm]

/-- The column weights `w(j) = s_{jsk} · eq(p, jin)` of the claimed slices `s` at `p`. -/
def wCol (sv : Vector F (2 ^ s)) (p : Vector F m) : CMlPolynomialEval F (s + m) :=
  Vector.ofFn fun j ↦
    sv[((cubeSplit s m).symm j).1] * (lagrangeBasis p)[((cubeSplit s m).symm j).2]

theorem wCol_cubeIndex (sv : Vector F (2 ^ s)) (p : Vector F m) (i : Fin (2 ^ s))
    (jin : Fin (2 ^ m)) : (wCol sv p)[cubeIndex i jin] = sv[i] * (lagrangeBasis p)[jin] := by
  simp only [wCol, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, cubeSplit_symm_cubeIndex]

/-- The native lincheck terminal (Annex C, §C.3.1): one forward walk of the circuit at the column
weights `w`, `⟨e, A w⟩ + α ⟨e, B w⟩`, the identity's term by tensors,
`α² · eq(χin, p) · Σ_i L_i(Y) s_i`, and the constant position's, `α³ · w(cpos)`. -/
def linTerminal (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (cpos : Fin (2 ^ (s + m))) (Y : F) (χin : Vector F m) (α : F) (p : Vector F m)
    (sv : Vector F (2 ^ s)) : F :=
  let e := eRow nodes Y χin
  let w := wCol sv p
  let rw := C.rows w
  let L := skipWeights nodes Y
  (∑ k : Fin (2 ^ (s + m)), e[k] * rw.1[k]) + α * (∑ k : Fin (2 ^ (s + m)), e[k] * rw.2[k]) +
    α ^ 2 * (eqTilde χin p * ∑ i : Fin (2 ^ s), L[i] * sv[i]) + α ^ 3 * w[cpos]

/-- The native terminal is the lincheck summand's terminal value at the claimed slices. -/
theorem linTerminal_eq (nodes : SkipDomain F s) (C : BlockR1CS F (s + m))
    (cpos : Fin (2 ^ (s + m))) (Y : F) (χin : Vector F m) (α : F) (p : Vector F m)
    (sv : Vector F (2 ^ s)) :
    linTerminal nodes C cpos Y χin α p sv =
      ∑ i : Fin (2 ^ s), evalMle (sliceLow (mTable C cpos (eRow nodes Y χin) α) i) p * sv[i] := by
  have hsum : ∑ i : Fin (2 ^ s),
      evalMle (sliceLow (mTable C cpos (eRow nodes Y χin) α) i) p * sv[i] =
      ∑ j : Fin (2 ^ (s + m)), (mTable C cpos (eRow nodes Y χin) α)[j] * (wCol sv p)[j] := by
    rw [sum_cube_split, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [evalMle_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun jin _ ↦ ?_
    rw [sliceLow_getElem, wCol_cubeIndex]
    ring
  have heq : ∑ j : Fin (2 ^ (s + m)), (eRow nodes Y χin)[j] * (wCol sv p)[j] =
      eqTilde χin p * ∑ i : Fin (2 ^ s), lagrangeWeight (skipNodes nodes.pts) Y i * sv[i] := by
    rw [eqTilde, ← eval_mle_eq_eval, evalMle_eq_sum, sum_cube_split, Finset.sum_mul]
    refine Finset.sum_congr rfl fun jin _ ↦ ?_
    simp only [eRow_cubeIndex, wCol_cubeIndex, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hsum, linTerminal]
  simp only [mTable_getElem, add_mul, Finset.sum_add_distrib, mul_assoc, ite_mul, one_mul,
    zero_mul, skipWeights_getElem]
  rw [← C.sum_mul_rows_fst]
  simp only [← Finset.mul_sum]
  rw [← C.sum_mul_rows_snd, heq, Finset.sum_ite_eq']
  simp

end

end Flock

end LeanVM.Protocol
