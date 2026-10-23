/-
  LeanVM.Protocol.EndToEnd.Complete.Flock

  The honest prover of the verifier program's Flock phase: the zerocheck's skip message, round
  polynomials and terminal values, the lincheck's round polynomials and the true slices of the
  `QFLOCK` region, against which `verifyFlock` returns the region's point and true slices for
  every challenge.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.FlockRounds
public import LeanVM.Protocol.EndToEnd.Complete.Facts

/-!
# Completeness of the Flock phase

The verifier program's step 6 (`verifyFlock (14 + τ_BLAKE2S)`, `verifyFlockZerocheck`,
`verifyFlockLincheck`; `python-verifier/verifier.py:1125-1301` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) against the honest prover of a stack `q` that
satisfies the leanISA instance's relation. The honest messages are the Flock argument's
(`LeanVM.Protocol.ToArkLib.Flock`), at the parameters and tables the soundness side reads the
program at (`Front.fP`, `Front.fC`, `Front.fz`: `flockParams τ_BLAKE2S`, the BLAKE2s circuit's
R1CS, the 64 bit tables of the `QFLOCK` column):

1. the point's `τ + 1` drawn coordinates are received (`Script.sampleN`);
2. the skip message is `P` on the coset (`Flock.skipMessage`). The program interpolates
   `P(z_skip)` from 64 assumed zeros and the 64 values (`lagrangeInterpolate`), which is ArkLib's
   `skipClaim` (`Front.lagrangeInterpolate_eq_skipClaim`); with the R1CS residuals' extensions
   zero at the point (`M3Holds`' Flock clause, through `Front.aux_iff` and `batchHolds_iff`), it
   is `P(z_skip)` itself (`Flock.skipClaim_skipMessage`), the full partial sum of the zerocheck;
3. the zerocheck's rounds (`follows_normSumcheck`, equality mode at the point, whose coordinates
   are the program's: `Front.point_getElem`), then `v_a = â(χ)` and `v_b = b̂(χ)`; the program's
   `v_c = R + v_a·v_b` is `ẑ(χ)` in characteristic two (`ZcGood`);
4. `α`; the batched claim `v_a + α v_b + α² v_c + α³` is the lincheck's full sum by the
   block-diagonal identity (`Flock.sum_mTable_zTable`) and the constant position's residual being
   zero; the lincheck's rounds (`follows_highSumcheck`);
5. the 64 slices: the extensions of the region's bit tables at the point `χ'_in ‖ χ_out`, which
   is `flockSlice` at the program's returned point. The program's terminal check passes when its
   terminal is ArkLib's `linTerminal` (`Front.TerminalFaithful`, the forward walk of the BLAKE2s
   circuit computing the R1CS's products): ArkLib's terminal at the honest slices is the
   lincheck's final claim (`Flock.linTerminal_eq`, `Flock.evalMle_sliceLow_zTable`).

## Main result

`follows_verifyFlock`: under `Front.TerminalFaithful` (the one hypothesis, a statement about
the deployed circuit and the program's forward walk alone, which the soundness side reduces to
the walk's fidelity in `Front.FlockTerminal`), the honest prover `hFlock` follows `verifyFlock`
to `FlockGood`: the program's point, of the region's `8 + τ` coordinates, and the true slices
there.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open LeanVM.Protocol LeanVM.Protocol.LeanIsa LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.Verifier (ZerocheckResult fixedChallenges flockKSkip kBits
  flockNumLincheckRounds)
open CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The argument at the instance -/

/-- The program's `logN` for the Flock phase: `14 + τ_BLAKE2S`. -/
abbrev flockLogN (prog : Program) (s : Sizes) : ℕ :=
  Verifier.blake2sR1csLogSize +
    (Front.verifierLayout prog s).tableLogHeights.getD Verifier.opBlake2s 0

/-- The Flock argument's parameters at the instance. -/
abbrev flockArgP (prog : Program) (s : Sizes) : Flock.Params E :=
  Front.fP Blake2sFlock.blake2sFlockSpec prog s

/-- The region's R1CS. -/
abbrev flockArgC (prog : Program) (s : Sizes) :
    BlockR1CS E ((flockArgP prog s).s + (flockArgP prog s).m) :=
  Front.fC Blake2sFlock.blake2sFlockSpec prog s

/-- The number of coordinates of the zerocheck's point, `8 + τ`. -/
abbrev flockN (prog : Program) (s : Sizes) : ℕ := (flockArgP prog s).m + (flockArgP prog s).κ

/-- The 64 bit tables of the stack's `QFLOCK` column. -/
def flockBits (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Fin (2 ^ (flockArgP prog s).s) → CMlPolynomialEval E (flockN prog s) :=
  Front.fz Blake2sFlock.blake2sFlockSpec prog s (Front.stackOracle Blake2sFlock.blake2sFlockSpec
    prog s q)

/-- The zerocheck's point: the fixed coordinates, then the drawn ones. -/
def zcPoint (prog : Program) (s : Sizes) (sampled : List E) : Vector E (flockN prog s) :=
  (flockArgP prog s).point (Front.toVec _ sampled)

/-- `â(Y, ·)`: the quirky extension of the left products. -/
def zcTabA (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (Y : E) :
    CMlPolynomialEval E (flockN prog s) :=
  Flock.skipTable (flockArgP prog s).nodes (Flock.leftTable (flockArgC prog s) (flockBits prog s q))
    Y

/-- `b̂(Y, ·)`: the quirky extension of the right products. -/
def zcTabB (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (Y : E) :
    CMlPolynomialEval E (flockN prog s) :=
  Flock.skipTable (flockArgP prog s).nodes
    (Flock.rightTable (flockArgC prog s) (flockBits prog s q)) Y

/-- `ẑ(Y, ·)`: the quirky extension of the witness. -/
def zcTabZ (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (Y : E) :
    CMlPolynomialEval E (flockN prog s) :=
  Flock.skipTable (flockArgP prog s).nodes (flockBits prog s q) Y

/-- The zerocheck's summand at the skip value: `â · b̂ - ẑ`. -/
def zcSummand (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (Y : E) :
    Vector E (flockN prog s) → E :=
  Flock.prodSub (zcTabA prog s q Y) (zcTabB prog s q Y) (zcTabZ prog s q Y)

/-- The lincheck's column weights at the zerocheck's result and `α`. -/
def linTabM (prog : Program) (s : Sizes) (zc : ZerocheckResult) (α : E) :
    CMlPolynomialEval E ((flockArgP prog s).s + (flockArgP prog s).m) :=
  Flock.mTable (flockArgC prog s) (flockArgP prog s).cpos
    (Flock.eRow (flockArgP prog s).nodes zc.zSkip (lowVec (Front.toVec (flockN prog s) zc.chi))) α

/-- The lincheck's folded witness at the zerocheck's batch coordinates. -/
def linTabZ (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (zc : ZerocheckResult) :
    CMlPolynomialEval E ((flockArgP prog s).s + (flockArgP prog s).m) :=
  Flock.zTable (flockBits prog s q) (highVec (Front.toVec (flockN prog s) zc.chi))

/-! ## The honest prover -/

/-- The honest prover of the zerocheck. -/
noncomputable def hZerocheck (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script ZerocheckResult :=
  (Script.sampleN (flockLogN prog s - flockKSkip - fixedChallenges.length)).bind fun sampled ↦
  (Script.sendList (Flock.skipMessage (flockArgP prog s).nodes (flockArgC prog s)
    (flockBits prog s q) (zcPoint prog s sampled)).toList).bind fun _ ↦
  Script.sampleE.bind fun zSkip ↦
  (hSumcheck 3 (claimL (partialSum (zcSummand prog s q zSkip) (zcPoint prog s sampled)))
    ((fixedChallenges ++ sampled).map some) []).bind fun x ↦
  (Script.sendE (evalMle (zcTabA prog s q zSkip) (Front.toVec _ x.1))).bind fun _ ↦
  (Script.sendE (evalMle (zcTabB prog s q zSkip) (Front.toVec _ x.1))).bind fun _ ↦
  .ret ⟨zSkip, x.1, evalMle (zcTabA prog s q zSkip) (Front.toVec _ x.1),
    evalMle (zcTabB prog s q zSkip) (Front.toVec _ x.1),
    x.2 + evalMle (zcTabA prog s q zSkip) (Front.toVec _ x.1) *
      evalMle (zcTabB prog s q zSkip) (Front.toVec _ x.1)⟩

/-- The honest prover of the lincheck, after the zerocheck's result `zc`: the rounds, then the
true slices at the program's point. -/
noncomputable def hLincheck (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s))
    (zc : ZerocheckResult) : Script (List E × List E) :=
  Script.sampleE.bind fun α ↦
  (hSumcheck 3 (claimL (highSum (Flock.linFun (linTabM prog s zc α) (linTabZ prog s q zc))))
    (List.replicate (flockArgP prog s).m none) []).bind fun x ↦
  (Script.sendList ((List.range 64).map fun i ↦
    flockSlice prog s q i (x.1.reverse ++ zc.chi.drop flockNumLincheckRounds))).bind fun _ ↦
  .ret (x.1.reverse ++ zc.chi.drop flockNumLincheckRounds, (List.range 64).map fun i ↦
    flockSlice prog s q i (x.1.reverse ++ zc.chi.drop flockNumLincheckRounds))

/-- **The honest prover of the Flock phase**: the zerocheck, then the lincheck. -/
noncomputable def hFlock (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script (List E × List E) :=
  (hZerocheck prog s q).bind (hLincheck prog s q)

/-! ## Facts of the instance -/

section Facts

variable {prog : Program} {s : Sizes} {q : Column (leanIsaμ prog s)}

/-- The bit tables of the region, as lists, are the bits of the `QFLOCK` cells. -/
theorem toList_flockBits (i : Fin (2 ^ Flock.kSkip)) :
    (flockBits prog s q i).toList =
      ((inst prog s).column q flockCol).values.toList.map fun a ↦ cellBit a i := by
  show (Vector.ofFn (n := 2 ^ (8 + s.τ 5)) fun u ↦
    cellBit (((inst prog s).column q flockCol).values.get u) i).toList = _
  rw [Vector.toList_ofFn]
  apply List.ext_getElem (by simp; rfl)
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, Vector.getElem_toList]
  rfl

/-- A slice is the extension of its bit table. -/
theorem flockSlice_eq (i : Fin (2 ^ (flockArgP prog s).s)) {point : List E}
    (hp : point.length = flockN prog s) :
    flockSlice prog s q i point = evalMle (flockBits prog s q i) (Front.toVec _ point) := by
  unfold flockSlice
  refine (congrArg (fun l ↦ Verifier.multilinearEval l point) (toList_flockBits i)).symm.trans ?_
  calc Verifier.multilinearEval (flockBits prog s q i).toList point
      = Verifier.multilinearEval (flockBits prog s q i).toList
          (Front.toVec (flockN prog s) point).toList := by rw [toList_toVec hp]
    _ = evalMle (flockBits prog s q i) (Front.toVec _ point) := Front.multilinearEval_eq_evalMle _ _

/-- A table whose entries all vanish has a vanishing extension. -/
theorem evalMle_eq_zero_of_entries {n : ℕ} {t : CMlPolynomialEval E n}
    (h : ∀ u : Fin (2 ^ n), t[u] = 0) (x : Vector E n) : evalMle t x = 0 := by
  rw [evalMle_eq_sum]
  exact Finset.sum_eq_zero fun u _ ↦ by rw [h u, zero_mul]

/-- The relation gives the batch of R1CS blocks on the region's bit tables. -/
theorem batchHolds_of {input : PublicInput} (hq : M3Holds (inst prog s) input q) :
    BlockR1CS.BatchHolds (flockArgC prog s) (flockArgP prog s).cpos (flockBits prog s q) :=
  (Front.aux_iff _ prog s q).mp hq.2.2.2.2

/-- The residuals' extensions vanish everywhere. -/
theorem evalMle_errTable {input : PublicInput} (hq : M3Holds (inst prog s) input q)
    (i : Fin (2 ^ (flockArgP prog s).s)) (x : Vector E (flockN prog s)) :
    evalMle (Flock.errTable (flockArgC prog s) (flockBits prog s q) i) x = 0 :=
  evalMle_eq_zero_of_entries (((Flock.batchHolds_iff _ _ _).mp (batchHolds_of hq)).1 i) x

/-- The constant position's residual's extension vanishes everywhere. -/
theorem evalMle_constTable {input : PublicInput} (hq : M3Holds (inst prog s) input q)
    (x : Vector E (flockArgP prog s).κ) :
    evalMle (Flock.constTable (flockArgP prog s).cpos (flockBits prog s q)) x = 0 :=
  evalMle_eq_zero_of_entries (((Flock.batchHolds_iff _ _ _).mp (batchHolds_of hq)).2) x

end Facts

/-! ## The zerocheck -/

/-- **The zerocheck's result is true**: `χ` has a coordinate per variable, and `v_a, v_b, v_c`
are the quirky extensions `â, b̂, ẑ` at `(z_skip, χ)`. -/
def ZcGood (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (zc : ZerocheckResult) :
    Prop :=
  zc.chi.length = flockN prog s ∧
    zc.vA = evalMle (zcTabA prog s q zc.zSkip) (Front.toVec _ zc.chi) ∧
    zc.vB = evalMle (zcTabB prog s q zc.zSkip) (Front.toVec _ zc.chi) ∧
    zc.vC = evalMle (zcTabZ prog s q zc.zSkip) (Front.toVec _ zc.chi)

/-- The number of drawn coordinates is `τ + 1`. -/
theorem flockLogN_sub (prog : Program) (s : Sizes) :
    flockLogN prog s - flockKSkip - fixedChallenges.length = (flockArgP prog s).nRand := by
  have h5 : (Front.verifierLayout prog s).tableLogHeights.getD Verifier.opBlake2s 0 = s.τ 5 := by
    simp [Front.verifierLayout, Front.tableLogs, Verifier.opBlake2s]
  have hk : flockKSkip = 6 := by decide
  have hf : fixedChallenges.length = 7 := rfl
  rw [flockLogN, h5, hk, hf]
  show 14 + s.τ 5 - 6 - 7 = s.τ 5 + 1
  omega

/-- **The honest zerocheck follows the program's** to a true result. -/
theorem follows_hZerocheck {prog : Program} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hq : M3Holds (inst prog s) input q) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ ZcGood prog s q b) (hZerocheck prog s q)
      (Verifier.verifyFlockZerocheck (flockLogN prog s)) cs := by
  unfold hZerocheck
  rw [Front.verifyFlockZerocheck_eq, Prog.bind_eq, flockLogN_sub]
  refine Follows.bind (fun cs₁ sampled sampled' h₁ ↦ ?_) _ _ _ (Follows.sampleN_sampleN cs _)
  have e₁ := h₁.1
  have e₂ := h₁.2.1
  have hlen := h₁.2.2
  subst e₁ e₂
  set msg := Flock.skipMessage (flockArgP prog s).nodes (flockArgC prog s) (flockBits prog s q)
    (zcPoint prog s sampled) with hmsg
  have hml : msg.toList.length = kBits := by simp; rfl
  simp only [Front.zcRest, Prog.bind_eq]
  rw [← hml]
  refine Follows.bind (fun cs₂ _ pc h₂ ↦ ?_) _ _ _ (Follows.sendList_readN cs₁ msg.toList)
  have e₁ := h₂.1
  have e₂ := h₂.2
  subst e₁ e₂
  refine Follows.bind (fun cs₃ zSkip zSkip' h₃ ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs₂)
  have e₁ := h₃.1
  have e₂ := h₃.2
  subst e₁ e₂
  have hv : Front.vPOf msg.toList zSkip =
      partialSum (zcSummand prog s q zSkip) (zcPoint prog s sampled) 0 #v[] := by
    rw [Front.vPOf, Front.lagrangeInterpolate_eq_skipClaim _ (by rw [hml]; rfl)]
    have h2 := Flock.skipClaim_skipMessage (flockArgP prog s).nodes (by exact flockNodes_injective)
      (flockArgC prog s) (flockBits prog s q) (zcPoint prog s sampled)
      (fun i ↦ evalMle_errTable hq i _) zSkip
    rw [← hmsg] at h2
    refine (congrArg (fun v ↦ Flock.skipClaim flockSkipDomain v zSkip)
      (toVec_toList msg)).trans (h2.trans ?_)
    rw [partialSum_zero, Flock.pValue_eq]
    rfl
  rw [hv]
  have hrounds := follows_normSumcheck (zcTabA prog s q zSkip) (zcTabB prog s q zSkip)
    (zcTabZ prog s q zSkip) (zcPoint prog s sampled) ((fixedChallenges ++ sampled).map some)
    (by
      have hf : fixedChallenges.length = 7 := rfl
      simp only [List.length_map, List.length_append, hf, hlen]
      exact (flockArgP prog s).hpoint)
    (fun k hk ↦ by
      simp only [List.getElem_map]
      congr 1
      exact (Front.point_getElem _ prog s hlen k _).symm) cs₃
  refine Follows.bind (fun cs₄ x x' h₄ ↦ ?_) _ _ _ hrounds
  have e₁ := h₄.1
  have e₂ := h₄.2.1
  have hxl := h₄.2.2.1
  have hx := h₄.2.2.2
  subst e₁ e₂
  rw [← Prod.mk.eta (p := x)]
  set chi := x.1
  set running := x.2
  simp only [Front.zcRest.zcTail, Prog.bind_eq]
  refine Follows.bind (fun cs₅ _ vA h₅ ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₄)
  have e₁ := h₅.1
  have e₂ := h₅.2
  subst e₁ e₂
  refine Follows.bind (fun cs₆ _ vB h₆ ↦ ?_) _ _ _ (Follows.sendE_readE _ cs₅)
  have e₁ := h₆.1
  have e₂ := h₆.2
  subst e₁ e₂
  refine ⟨rfl, rfl, hxl, rfl, rfl, ?_⟩
  simp only
  rw [hx, Flock.prodSub, CharTwo.sub_eq_add]
  linear_combination (CharTwo.two_eq_zero (R := E)) *
    (evalMle (zcTabA prog s q zSkip) (Front.toVec _ chi) *
      evalMle (zcTabB prog s q zSkip) (Front.toVec _ chi))

/-! ## The lincheck -/

/-- **The honest lincheck follows the program's** from a true zerocheck result, to the program's
point and the true slices there, given that the program's terminal is ArkLib's. -/
theorem follows_hLincheck {prog : Program} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hq : M3Holds (inst prog s) input q)
    (hterm : Front.TerminalFaithful Blake2sFlock.blake2sFlockSpec prog s)
    (zc : ZerocheckResult) (hzc : ZcGood prog s q zc) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ FlockGood prog s q b) (hLincheck prog s q zc)
      (Verifier.verifyFlockLincheck .computed zc) cs := by
  have hchi := hzc.1
  have hA := hzc.2.1
  have hB := hzc.2.2.1
  have hC := hzc.2.2.2
  unfold hLincheck
  rw [Front.verifyFlockLincheck_eq, Prog.bind_eq]
  refine Follows.bind (fun cs₁ α α' h₁ ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs)
  have e₁ := h₁.1
  have e₂ := h₁.2
  subst e₁ e₂
  have hclaim : zc.vA + α * zc.vB + α ^ 2 * zc.vC + α ^ 3 =
      highSum (Flock.linFun (linTabM prog s zc α) (linTabZ prog s q zc)) 0 #v[] := by
    rw [highSum_zero, Flock.sum_linFun_boolVec, linTabM, linTabZ, Flock.sum_mTable_zTable,
      lowVec_append_highVec, evalMle_constTable hq, hA, hB, hC]
    simp only [zcTabA, zcTabB, zcTabZ]
    ring
  have hm : flockNumLincheckRounds = (flockArgP prog s).m := by
    have hk : flockKSkip = 6 := by decide
    show Verifier.blake2sR1csLogSize - flockKSkip = 8
    rw [hk]
    rfl
  rw [hclaim, hm, Prog.bind_eq]
  refine Follows.bind (fun cs₂ x x' h₂ ↦ ?_) _ _ _ (follows_highSumcheck _ _ cs₁)
  have e₁ := h₂.1
  have e₂ := h₂.2.1
  have hxl := h₂.2.2.1
  have hx := h₂.2.2.2
  subst e₁ e₂
  rw [← Prod.mk.eta (p := x)]
  generalize x.1 = rc at hxl hx ⊢
  generalize x.2 = rLc at hx ⊢
  generalize hpoint : rc.reverse ++ zc.chi.drop (flockArgP prog s).m = point
  have hpl : point.length = flockN prog s := by
    rw [← hpoint, List.length_append, List.length_reverse, List.length_drop, hxl, hchi]
    show (flockArgP prog s).m + ((flockArgP prog s).m + (flockArgP prog s).κ -
      (flockArgP prog s).m) = (flockArgP prog s).m + (flockArgP prog s).κ
    omega
  generalize hsl : (List.range 64).map (fun i ↦ flockSlice prog s q i point) = sl
  have hsll : sl.length = kBits := by rw [← hsl]; simp; rfl
  simp only [Front.linTail, Prog.bind_eq, hm, hpoint]
  rw [← hsll]
  refine Follows.bind (fun cs₃ _ sv h₃ ↦ ?_) _ _ _ (Follows.sendList_readN cs₂ sl)
  have e₁ := h₃.1
  have e₂ := h₃.2
  subst e₁ e₂
  have hterm' := hterm zc α rc sv hchi hxl (by rw [hsll]; rfl)
  have hcheck : Front.progTerminal zc α rc sv = rLc := by
    rw [hterm', Flock.linTerminal_eq, hx, Flock.linFun]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    rw [linTabZ, Flock.evalMle_sliceLow_zTable]
    have hi : i.val < 64 := i.isLt
    simp only [Front.toVec, Vector.getElem_ofFn, Fin.getElem_fin]
    rw [← hsl, List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_range]
    rw [flockSlice_eq i hpl, ← hpoint, Front.toVec_linPoint hxl hchi]
    rfl
  simp only [Prog.require, hcheck, ↓reduceIte, Prog.ret_bind, Prog.pure_eq]
  exact ⟨rfl, rfl, hpl, hsl.symm⟩

/-! ## The phase -/

/-- **Completeness of the Flock phase.** For a stack satisfying the leanISA instance's relation,
and given that the program's lincheck terminal is ArkLib's (`Front.TerminalFaithful`), the honest
prover follows `verifyFlock (14 + τ_BLAKE2S)` to the program's point and the true slices of the
`QFLOCK` region there, for every challenge. -/
theorem follows_verifyFlock {prog : Program} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hq : M3Holds (inst prog s) input q)
    (hterm : Front.TerminalFaithful Blake2sFlock.blake2sFlockSpec prog s) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ FlockGood prog s q b) (hFlock prog s q)
      (Verifier.verifyFlock .computed (Verifier.blake2sR1csLogSize +
        (Front.verifierLayout prog s).tableLogHeights.getD Verifier.opBlake2s 0)) cs := by
  unfold hFlock Verifier.verifyFlock
  refine Follows.bind (fun cs₁ zc zc' h₁ ↦ ?_) _ _ _ (follows_hZerocheck hq cs)
  have e₁ := h₁.1
  have e₂ := h₁.2.1
  have hzc := h₁.2.2
  subst e₁ e₂
  exact follows_hLincheck hq hterm zc hzc cs₁

end
end LeanVM.Protocol.EndToEnd.Complete
