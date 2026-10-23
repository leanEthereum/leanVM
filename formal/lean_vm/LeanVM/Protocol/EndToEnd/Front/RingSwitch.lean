/-
  LeanVM.Protocol.EndToEnd.Front.RingSwitch

  The verifier program's ring switching specified from the knowledge soundness of the Flock
  argument's ring-switching components over the leanISA instance, ending on the switched claim on
  the stack.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.FlockLin

/-!
# Ring switching as a specification

`ringSwitch point s` (`verifier.py:1331-1340` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) draws the six coefficients of the staged map `Φ` and
returns the target `Σ_i g^i Φ(s_i)` and the weight `W(u) = Σ_k c_k eq(point^(2^k), u)`; the
program claims `⟨eqAbove · W, q⟩ = target` on the stack (`ringSwitchClaim`). Against the Flock
argument's components (`ToArkLib/Flock/RingSwitch.lean`):

| program | component | doom after it | escape per challenge |
| --- | --- | --- | --- |
| `sampleN 6` (coefficients `0 … 4`) | `ringDraw p` | `ringRel (p + 1)` | `1/|E|` |
| (coefficient `5`) | `ringFinal` | `Seam.flock` at the switched claim | `1/|E|` |

The proved errors are `1/|E|` per coefficient (`ringDrawSecurity`, `ringFinalSecurity`); the
slot's `ringError` charges more.

The start: a candidate outside `outRel` is outside `ringRel 0`, by the injectivity of ring
switching (`ringSwitch_injective`), as in `ringStartSecurity`. The end: a candidate satisfying the
program's ring claim satisfies ArkLib's switched weighted claim, provided the program's target
and weight pair with the stack as ArkLib's do (`RingFaithful`, discharged in `RingFidelity`).
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

section Ring

variable (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
  (layout : LeanVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
  (toI : Column layout.stackLog → Column (fI F prog s).μ)
  (claims : List LeanVM.Protocol.Verifier.ColumnClaim) (input : LeanVM.Semantics.PublicInput)

/-- The region is the instance's Flock region. -/
theorem fR_eq : (fI F prog s).flock = some (fR F prog s) := rfl

/-- The lincheck's output statement of a candidate at the program's point and slices. -/
def outStmt (pt sv : List E) (q : Column layout.stackLog) :
    Flock.OutStmt ((fI F prog s).Stmt × PubOut (fI F prog s)) E
      ((fP F prog s).m + (fP F prog s).κ) (fP F prog s).s :=
  (fS F prog s layout toI input q, toVec ((fP F prog s).m + (fP F prog s).κ) pt,
    toVec (2 ^ (fP F prog s).s) sv)

/-- ArkLib's switched weight at the program's point and coefficients. -/
def arkWeight (pt ch : List E) : Weight E (fI F prog s).μ :=
  Flock.ringWeight (fP F prog s) 5 (FlockPhase.lift (fR F prog s))
    (toVec ((fP F prog s).m + (fP F prog s).κ) pt) (toVec 6 ch)

/-- ArkLib's switched target at the program's slices and coefficients. -/
def arkTarget (sv ch : List E) : E :=
  Flock.ringTarget (fP F prog s) 5 (algebraMap K E) g (toVec (2 ^ (fP F prog s).s) sv) (toVec 6 ch)

/-- Alive while the coefficients are drawn: `ringRel j` for the first `j ≤ 5`, then the Flock
seam at the switched claim. -/
def RingAlive (pt sv : List E) (j : ℕ) (acc : List E) (q : Column layout.stackLog) : Prop :=
  if j ≤ 5 then
    fG layout claims q ∧ (((outStmt F prog s layout toI input pt sv q, toVec j acc),
      fO F prog s layout toI q), ()) ∈
        Flock.ringRel (fP F prog s) (fz F prog s) (fside F prog s) 5 (algebraMap K E) g j
  else if j = 6 then
    fG layout claims q ∧ ((FlockPhase.finish (fR F prog s) (fR_eq F prog s)
      (fS F prog s layout toI input q) (arkWeight F prog s pt acc) (arkTarget F prog s sv acc),
        fO F prog s layout toI q), ()) ∈ Seam.flock (fI F prog s)
  else False

/-- The Flock seam at a switched claim gives the side condition and the claim. -/
theorem ring_hOut_gen {I : M3Instance} (r : FlockRegion I.toShape) (h : I.flock = some r)
    (sIn : I.Stmt × PubOut I) (o : ∀ i, TheOracle I i) (W : Weight E I.μ) (T : E)
    (hout : ((FlockPhase.finish r h sIn W T, o), ()) ∈ Seam.flock I) :
    FlockPhase.side sIn o ∧ W.pair (algebraMap K E) (theStack o).values = T := by
  have h1 : FlockPhase.side sIn o := hout.1
  have h2 : WeightedClaim.Holds (theStack o) ⟨W, T⟩ :=
    hout.2 _ (FlockPhase.mem_weighted_finish r h sIn W T)
  exact ⟨h1, h2⟩

/-- The last coefficient's security, at the instance's region (`ringFinalSecurity`). -/
noncomputable def ringFinalSec :=
  Flock.ringFinalSecurity (fP F prog s) (fz F prog s) (fside F prog s) 5 (algebraMap K E) g
    (FlockPhase.lift (fR F prog s))
    (fun o ↦ ((fI F prog s).flockColumn (fR F prog s) (theStack o)).values)
    (fun o ↦ (theStack o).values) (FlockPhase.finish (fR F prog s) (fR_eq F prog s))
    (Seam.flock (fI F prog s)) (ring_hOut_gen (fR F prog s) (fR_eq F prog s))
    (fun o u ↦ ofK_eq_sum_bitTable ((fI F prog s).flockColumn (fR F prog s) (theStack o)) u)
    (fun o i u ↦ bitTable_isBool ((fI F prog s).flockColumn (fR F prog s) (theStack o)) i u)
    (fun o p ↦ FlockPhase.eval₂Mle_flockColumn (fR F prog s) (theStack o) p)

/-- **A coefficient's escape** (`ringDrawSecurity`, `ringFinalSecurity`): a family whose `π`s do
not all vanish keeps a nonzero `π` for every coefficient but one. -/
theorem ring_escape (pt sv acc : List E) (q : Column layout.stackLog)
    (hq : ¬ RingAlive F prog s layout toI claims input pt sv acc.length acc q) :
    avgE (fun c ↦ indE (RingAlive F prog s layout toI claims input pt sv (acc ++ [c]).length
      (acc ++ [c]) q)) ≤ ((overE 1 : ℝ≥0) : ℝ≥0∞) := by
  have hzero : avgE (fun _ : E ↦ indE False) ≤ ((overE 1 : ℝ≥0) : ℝ≥0∞) :=
    (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans zero_le
  simp only [List.length_append, List.length_singleton]
  by_cases hG : fG layout claims q
  · rcases Nat.lt_or_ge acc.length 5 with hp | hp
    · have hin : (((outStmt F prog s layout toI input pt sv q, toVec acc.length acc),
          fO F prog s layout toI q), ()) ∉
          Flock.ringRel (fP F prog s) (fz F prog s) (fside F prog s) 5 (algebraMap K E) g
            acc.length := fun h ↦ hq (by
        simp only [RingAlive, show acc.length ≤ 5 from hp.le, ↓reduceIte]
        exact ⟨hG, h⟩)
      have h := sample_escape (Flock.ringDrawSecurity (fP F prog s) (fz F prog s)
        (fside F prog s) 5 (algebraMap K E) g acc.length (by omega)) _ _ hin rfl
      rw [← overF_eq_overE]
      refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans h
      simp only [RingAlive, show acc.length + 1 ≤ 5 by omega, ↓reduceIte] at hc
      have hc' := hc.2
      rw [toVec_append_singleton rfl] at hc'
      exact hc'
    · rcases Nat.lt_or_ge acc.length 6 with hp' | hp'
      · have h5 : acc.length = 5 := by omega
        have hin : (((outStmt F prog s layout toI input pt sv q, toVec acc.length acc),
            fO F prog s layout toI q), ()) ∉
            Flock.ringRel (fP F prog s) (fz F prog s) (fside F prog s) 5 (algebraMap K E) g
              acc.length :=
          fun h ↦ hq (by
            simp only [RingAlive, show acc.length ≤ 5 by omega, ↓reduceIte]
            exact ⟨hG, h⟩)
        rw [h5] at hin
        have h := sample_escape (ringFinalSec F prog s) _ _ hin rfl
        rw [← overF_eq_overE]
        refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans h
        simp only [RingAlive, h5, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceIte] at hc
        have hc' := hc.2
        rw [arkWeight, arkTarget, toVec_append_singleton h5] at hc'
        exact hc'
      · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ ?_).trans hzero
        simp only [RingAlive, show ¬ acc.length + 1 ≤ 5 by omega,
          show ¬ acc.length + 1 = 6 by omega, ↓reduceIte] at hc
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun hc ↦ ?_).trans hzero
    unfold RingAlive at hc
    split_ifs at hc
    · exact hG hc.1
    · exact hG hc.1

/-- **The start of ring switching** (`ringStartSecurity`): a candidate outside `outRel` is
outside `ringRel 0`, ring switching being injective (`ringSwitch_injective`). -/
theorem ring_start (pt sv : List E) (q : Column layout.stackLog)
    (hq : ¬ OutAlive F prog s layout toI claims input pt sv q) :
    ¬ RingAlive F prog s layout toI claims input pt sv ([] : List E).length [] q := by
  simp only [RingAlive, List.length_nil, Nat.zero_le, ↓reduceIte]
  rintro ⟨hG, hside, hπ⟩
  refine hq ⟨hG, hside, fun i ↦ ?_⟩
  have herr := ringSwitch_injective _ (fun k hk ↦ hπ k (by simpa using hk)) i
  simp only [Flock.ringStages, List.ofFn_zero, frobMap, Flock.sliceError, sub_eq_zero]
    at herr
  exact herr

/-- **The ring claim's fidelity**: when the program's ring claim holds of a candidate, ArkLib's
switched claim at the program's point, slices and coefficients holds of its reading. -/
def RingFaithful : Prop :=
  ∀ (pt sv ch : List E) (q : Column layout.stackLog),
    pt.length = (fP F prog s).m + (fP F prog s).κ → sv.length = 64 → ch.length = 6 →
    StackClaim.Holds layout.stackLog
      (LeanVM.Protocol.Verifier.ringSwitchClaim layout
        (LeanVM.Protocol.Verifier.polyEval
          (sv.map (LeanVM.Protocol.Verifier.phiMap · ch)) LeanVM.Protocol.Verifier.gen)
        fun rPrime ↦ LeanVM.Protocol.Verifier.ringWeight pt rPrime
          (LeanVM.Protocol.Verifier.ringCoefficients ch)) q →
      (arkWeight F prog s pt ch).pair (algebraMap K E) (toI q).values = arkTarget F prog s sv ch

/-- **The ring-switching phase's postcondition**: no candidate satisfies the program's claims and
the ring claim. -/
def RingPost (r : E × (List E → E)) (h : List Ev) : Prop :=
  Doomed C (fun q ↦ ColumnClaimsHold layout claims q ∧
    StackClaim.Holds layout.stackLog (LeanVM.Protocol.Verifier.ringSwitchClaim layout r.1 r.2) q)
    h

/-- Ring switching draws the six coefficients and returns the target and the weight. -/
theorem ringSwitch_eq (point sv : List E) :
    LeanVM.Protocol.Verifier.ringSwitch point sv = Prog.sampleN 6 >>= fun ch ↦
      Prog.ret (LeanVM.Protocol.Verifier.polyEval
          (sv.map (LeanVM.Protocol.Verifier.phiMap · ch)) LeanVM.Protocol.Verifier.gen,
        fun rPrime ↦ LeanVM.Protocol.Verifier.ringWeight point rPrime
          (LeanVM.Protocol.Verifier.ringCoefficients ch)) := rfl

open Classical in
/-- **Ring switching's specification**, from the lincheck's postcondition at the program's point
and slices to `RingPost`: lead `6 · L₀/|E|` plus the follower's `T` (the six coefficients and the
opening's challenges are one group). -/
noncomputable def ringSpec (hst : Stable C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    (hring : RingFaithful F prog s layout toI) {εmax T : ℝ≥0∞} (pt sv : List E) :
    Spec (LeanVM.Protocol.Verifier.ringSwitch pt sv)
      (LinPost F prog s layout C toI claims input (pt, sv))
      (RingPost layout C claims) εmax
      ((∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + T) T :=
  if hl : pt.length = (fP F prog s).m + (fP F prog s).κ ∧ sv.length = 64 then
    Spec.congr (ringSwitch_eq pt sv).symm <|
      ((doomSampleN hst hcard
        (fun acc q ↦ RingAlive F prog s layout toI claims input pt sv acc.length acc q)
        (fun _ ↦ ((overE 1 : ℝ≥0) : ℝ≥0∞))
        (fun acc q hq ↦ ring_escape F prog s layout toI claims input pt sv acc q hq) 6 []).mono
          (fun _ h q hq hr ↦ ring_start F prog s layout toI claims input pt sv q (h.2.2 q hq) hr)
          (fun _ _ h ↦ h) le_rfl (by simp) le_rfl).bind' fun ch ↦
        (Spec.ret _).mono (fun h hd ↦ by
          intro q hq ⟨hG, hclaim⟩
          refine hd.2 q hq ?_
          have h6 : ([] ++ ch).length = 6 := by simpa using hd.1
          simp only [RingAlive, h6, Nat.reduceLeDiff, ↓reduceIte]
          refine ⟨hG, fun c hc ↦ ?_, fun c hc ↦ ?_⟩
          · simp only [FlockPhase.finish, fS, flockStmt, Vector.toList_replicate,
              List.mem_replicate] at hc
            rw [hc.2]
            rfl
          · simp only [FlockPhase.finish, Vector.toList_cast, Vector.toList_mk,
              List.mem_singleton] at hc
            subst hc
            exact hring pt sv ch q hl.1 hl.2 (by simpa using hd.1) hclaim) (fun _ _ h ↦ h)
          le_rfl le_rfl le_rfl
  else Spec.dead.mono (fun _ h ↦ hl ⟨h.1, h.2.1⟩) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- **The Flock phase's specification** (`verifyFlock`, `verifier.py:1297-1301`): the zerocheck
then the lincheck, from the Flock phase's precondition (the reading of `Seam.pub`) to `LinPost`,
with lead `(k + 1)·L₀/|E|` and the follower's allowance `T` after the slices. Each group of the
phase is bounded by `εmax`: the skip challenge's `L₀·127/|E|`, each round's `L₀·2/|E|`, `α`'s
`L₀·3/|E|`. -/
noncomputable def verifyFlockSpec (hst : Stable C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    (hterm : TerminalFaithful F prog s) {εmax T : ℝ≥0∞} (hT : T ≤ εmax)
    (h127 : (L₀ : ℝ≥0∞) * ((overE 127 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (h2 : (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (h3 : (L₀ : ℝ≥0∞) * ((overE 3 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax) (logN : ℕ)
    (hlog : logN - LeanVM.Protocol.Verifier.flockKSkip -
      LeanVM.Protocol.Verifier.fixedChallenges.length = (fP F prog s).nRand) :
    Spec (LeanVM.Protocol.Verifier.verifyFlock .computed logN)
      (FlockPre F prog s layout C toI claims) (LinPost F prog s layout C toI claims input) εmax
      ((∑ _i ∈ Finset.range (logN - LeanVM.Protocol.Verifier.flockKSkip -
          LeanVM.Protocol.Verifier.fixedChallenges.length),
        (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + 0) T :=
  (zcSpec F prog s layout C toI claims input hst hcard h3 h127 h2 logN hlog).bind' fun zc ↦
    linSpec F prog s layout C toI claims input hst hcard hterm hT h2 zc

/-- The program's Flock size: `14 + τ_BLAKE2S` gives the point's `k + 1` drawn coordinates. -/
theorem flock_logN (hk : layout.tableLogHeights.getD LeanVM.Protocol.Verifier.opBlake2s 0 =
      s.τ 5) :
    LeanVM.Protocol.Verifier.blake2sR1csLogSize +
        layout.tableLogHeights.getD LeanVM.Protocol.Verifier.opBlake2s 0 -
      LeanVM.Protocol.Verifier.flockKSkip - LeanVM.Protocol.Verifier.fixedChallenges.length =
      (fP F prog s).nRand := by
  rw [hk]
  have h6 : LeanVM.Protocol.Verifier.flockKSkip = 6 := by decide
  have h7 : LeanVM.Protocol.Verifier.fixedChallenges.length = 7 := rfl
  rw [h6, h7]
  show 14 + s.τ 5 - 6 - 7 = s.τ 5 + 1
  omega

end Ring

end
end LeanVM.Protocol.EndToEnd.Front
