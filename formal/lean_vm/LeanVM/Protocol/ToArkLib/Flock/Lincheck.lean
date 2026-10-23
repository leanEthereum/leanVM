/-
  LeanVM.Protocol.ToArkLib.Flock.Lincheck

  The lincheck of a Flock argument as components: the batching challenge `α`, the plain rounds on
  the within-block coordinates, highest first, and the claimed slices checked against the native
  terminal, each with its completeness. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.Zerocheck

/-!
# The lincheck

After the zerocheck the claims are `â, b̂, ĉ` at the quirky point `(z_skip, χ)`, `χ = (χin, χout)`.
By the block-diagonal identity (`sum_mTable_zTable`) the three and the constant position are one
sum over a single block's positions, `Σ_j M_α(j) · Z(j)`, with `M_α` the column weights at a
batching challenge `α` and `Z(j) = ẑ_{jsk}(jin, χout)` (Annex C, §C.3). Three components:

1. `alphaDraw`: the verifier draws `α` and starts the sumcheck at
   `v_a + α v_b + α² v_c + α³`.
2. `linRounds`: the plain rounds on the `m` within-block coordinates, highest first
   (`linFamily`); the challenges, reversed, are the point `χ'in`.
3. `linEnd`: the prover sends the slices `s_i = ẑ_i(χ'in, χout)` and the verifier checks the
   running claim against the native terminal (`linTerminal`): one forward walk of the circuit.
   The output is the point `(χ'in, χout)` and the slices; the state (`outRel`): the slices are
   the witness tables' extensions there.

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval OracleComp OracleSpec SumcheckRound BlockR1CS

@[expose] public section

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F] (P : Params F)
  {ι : Type} {O : ι → Type} [∀ i, OracleInterface (O i)] {W : Type}
  (C : BlockR1CS F (P.s + P.m))
  (z : (∀ i, O i) → Fin (2 ^ P.s) → CMlPolynomialEval F (P.m + P.κ))
  {S : Type} (side : S → (∀ i, O i) → Prop)

/-! ## The batching challenge -/

/-- The lincheck's public data: the zerocheck's terminal statement and `α`. -/
abbrev LinX (S F : Type) (n : ℕ) : Type := TermStmt S F n × F

/-- After `α`: the sumcheck starts at `v_a + α v_b + α² v_c + α³`. -/
def alphaNext {n : ℕ} (t : TermStmt S F n) (α : F) : Stmt (LinX S F n) F 0 :=
  ((t, α), (#v[], t.2.2.1 + α * t.2.2.2.1 + α ^ 2 * t.2.2.2.2 + α ^ 3))

/-- `α`, as a typed component. -/
def alphaDraw :
    Typed.Def O (TermStmt S F (P.m + P.κ)) W (Stmt (LinX S F (P.m + P.κ)) F 0) W
      (Typed.drawSlot F) :=
  Typed.sampleChallenge O F (fun _ ↦ true) alphaNext

/-- The lincheck's column weights `M_α`, from the oracles and its public data. -/
def linM (x : LinX S F (P.m + P.κ)) : CMlPolynomialEval F (P.s + P.m) :=
  mTable C P.cpos (eRow P.nodes x.1.1.2.2 (lowVec x.1.2.1)) x.2

/-- The folded witness `Z`, from the oracles and the lincheck's public data. -/
def linZ (o : ∀ i, O i) (x : LinX S F (P.m + P.κ)) : CMlPolynomialEval F (P.s + P.m) :=
  zTable (z o) (highVec x.1.2.1)

/-- The lincheck's sumcheck: `Σ_jin Σ_i M̃_α,i(jin) · Z̃_i(jin)`, plain, highest coordinate
first; the invariant carries the side condition. -/
def linFamily : Family F (LinX S F (P.m + P.κ)) O W 2 where
  claim ctx j c := highSum (linFun (linM P C ctx.1.1) (linZ P z ctx.1.2 ctx.1.1)) j c
  poly ctx j c := highRound (linM P C ctx.1.1) (linZ P z ctx.1.2 ctx.1.1) j c
  weight := fun _ _ ↦ [(0, 1), (1, 1)]
  inv ctx _ _ := side ctx.1.1.1.1.1 ctx.1.2

instance [∀ s o, Decidable (side s o)] (ctx : Ctx (LinX S F (P.m + P.κ)) O W) (j : ℕ)
    (c : Vector F j) : Decidable ((linFamily P C z side).inv ctx j c) :=
  inferInstanceAs (Decidable (side _ _))

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The lincheck's family is honest. -/
theorem linFamily_honest : (linFamily P C z side (W := W)).Honest P.m where
  check := fun ctx _ c hj ↦
    weightedSum_highRound (linM P C ctx.1.1) (linZ P z ctx.1.2 ctx.1.1) hj c
  next := fun ctx _ c x hj ↦ evaluate_highRound (linM P C ctx.1.1) (linZ P z ctx.1.2 ctx.1.1) hj c x
  inv_push := fun _ _ _ _ _ h ↦ h

omit [DecidableEq F] [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- The constant position's residual vanishes at the batch coordinates of the final point. -/
theorem evalMle_constTable_eq_zero {χ : Vector F (P.m + P.κ)} {o : ∀ i, O i}
    (h : RestrictedZero (constTable P.cpos (z o)) (Partial.ofSuffix P.m χ)) :
    evalMle (constTable P.cpos (z o)) (highVec χ) = 0 :=
  (restrictedZero_of_all _ _ _ fun k hk ↦ by
    rw [Partial.ofSuffix_all _ χ k hk]
    simp [highVec]).mp h

/-! ## The rounds -/

/-! ## The claimed slices -/

/-- What the lincheck hands on: the input statement, the point `(χ'in, χout)` and the claimed
slices `s_i`. -/
abbrev OutStmt (S F : Type) (n s : ℕ) : Type := S × Vector F n × Vector F (2 ^ s)

/-- The point the lincheck ends at: the reversed challenges, then the zerocheck's batch
coordinates. -/
def linPoint (st : Stmt (LinX S F (P.m + P.κ)) F P.m) : Vector F (P.m + P.κ) :=
  st.2.1.reverse ++ highVec st.1.1.2.1

/-- The prover sends the slices `ẑ_i` at the lincheck's point. -/
def linHonest (p : (Stmt (LinX S F (P.m + P.κ)) F P.m × ∀ i, O i) × W) : Vector F (2 ^ P.s) :=
  Vector.ofFn fun i ↦ evalMle (z p.1.2 i) (linPoint P p.1.1)

/-- The verifier's check: the running claim is the native terminal at the received slices. -/
def linCheck (st : Stmt (LinX S F (P.m + P.κ)) F P.m) (sv : Vector F (2 ^ P.s)) : Bool :=
  decide (st.2.2 = linTerminal P.nodes C P.cpos st.1.1.1.2.2 (lowVec st.1.1.2.1) st.1.2
    st.2.1.reverse sv)

/-- After the slices: the input statement, the point and the slices. -/
def linNext (st : Stmt (LinX S F (P.m + P.κ)) F P.m) (sv : Vector F (2 ^ P.s)) :
    OutStmt S F (P.m + P.κ) P.s :=
  (st.1.1.1.1, linPoint P st, sv)

/-- The slices, as a typed component. -/
def linEnd :
    Typed.Def O (Stmt (LinX S F (P.m + P.κ)) F P.m) W (OutStmt S F (P.m + P.κ) P.s) W
      (Typed.saySlot (Vector F (2 ^ P.s))) :=
  Typed.sendChecked O _ (linHonest P z) (linCheck P C) (linNext P)

/-- After the lincheck: the side condition, and the slices are the witness tables' extensions at
the point. -/
def outRel : Set ((OutStmt S F (P.m + P.κ) P.s × ∀ i, O i) × W) :=
  {p | side p.1.1.1 p.1.2 ∧ ∀ i : Fin (2 ^ P.s), p.1.1.2.2[i] = evalMle (z p.1.2 i) p.1.1.2.1}

instance [∀ s o, Decidable (side s o)] (p : (OutStmt S F (P.m + P.κ) P.s × ∀ i, O i) × W) :
    Decidable (p ∈ outRel P z side) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ## The components -/

omit [DecidableEq F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of `α`. -/
theorem alphaDrawComplete :
    Typed.Complete (alphaDraw P (S := S) (O := O) (W := W)) (termRel P C z side)
      (rel (linFamily P C z side) 0) :=
  Typed.sampleChallengeComplete fun t o w h ↦ ⟨rfl, fun α ↦ by
    obtain ⟨hside, hconst, ha, hb, hc⟩ := h
    refine ⟨hside, ?_⟩
    show t.2.2.1 + α * t.2.2.2.1 + α ^ 2 * t.2.2.2.2 + α ^ 3 =
      highSum (linFun (linM P C (t, α)) (linZ P z o (t, α))) 0 #v[]
    rw [highSum_zero, sum_linFun_boolVec, linM, linZ, sum_mTable_zTable, lowVec_append_highVec,
      evalMle_constTable_eq_zero P z hconst]
    simp only [zcA, zcB, zcC] at ha hb hc
    rw [ha, hb, hc]
    ring⟩

/-- The lincheck's rounds, as a typed component. -/
def linRounds : Typed.Def O (Stmt (LinX S F (P.m + P.κ)) F 0) W
    (Stmt (LinX S F (P.m + P.κ)) F P.m) W (Typed.roundsSlot F 2 P.m) :=
  rounds (linFamily P C z side (W := W)).poly (linFamily P C z side (W := W)).weight P.m P.m 0
    (Nat.zero_add _)

omit [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the lincheck's rounds. -/
theorem linRoundsComplete :
    Typed.Complete (linRounds P C z side (O := O) (W := W)) (rel (linFamily P C z side) 0)
      (rel (linFamily P C z side) P.m) :=
  roundsComplete (linFamily P C z side) P.m (linFamily_honest P C z side) P.m 0 (Nat.zero_add _)

omit [SampleableType F] [∀ i, OracleInterface (O i)] in
/-- Typed completeness of the slices. -/
theorem linEndComplete :
    Typed.Complete (linEnd P C z (S := S) (O := O) (W := W)) (rel (linFamily P C z side) P.m)
      (outRel P z side) :=
  Typed.sendCheckedComplete fun st o w h ↦ ⟨by
    obtain ⟨_, hclaim⟩ := h
    rw [linCheck, decide_eq_true_eq, hclaim, linTerminal_eq]
    show highSum (linFun (linM P C st.1) (linZ P z o st.1)) P.m st.2.1 = _
    rw [highSum_self, linFun]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [linHonest, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, linPoint]
    rw [← evalMle_sliceLow_zTable]
    rfl, h.1, fun i ↦ by simp [linHonest, linNext]⟩

end

end Flock

end LeanVM.Protocol
