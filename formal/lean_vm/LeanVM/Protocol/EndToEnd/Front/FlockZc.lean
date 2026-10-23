/-
  LeanVM.Protocol.EndToEnd.Front.FlockZc

  The verifier program's Flock zerocheck specified from the knowledge soundness of the Flock
  argument's components over the leanISA instance: the drawn coordinates of the point, the skip
  message and challenge, the normalized rounds and the terminal values.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.FlockSetup

/-!
# The Flock zerocheck as a specification

`verifyFlockZerocheck (14 + k)` (`verifier.py:1134-1149` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) is, against the Flock argument's components
(`ToArkLib/Flock/Zerocheck.lean`), at `flockParams k`:

| program | component | doom after it (no candidate alive) | escape per challenge |
| --- | --- | --- | --- |
| `sampleN (k + 1)` | `pointDraws` | `pointRel j` at the drawn coordinates | `1/|E|` |
| `readN 64` | `skipMsg` | unchanged (the message is checked by `skipRel`'s first conjunct) | |
| `sampleE` (`z_skip`) | `skipDraw` | `rel zcFamily 0` at the interpolated claim | `127/|E|` |
| `sumcheck v_P 3 r` | `zcRoundsLow`, `zcRoundsHigh` | `rel zcFamily j` | `2/|E|` |
| `readE`, `readE` | `zcEnd` | `termRel` at `v_a, v_b, v_c` | |

**The fidelity checks.** The program's coordinates are ArkLib's point (`point_getElem`), its skip
interpolation ArkLib's claim (`lagrangeInterpolate_eq_skipClaim`), its rounds ArkLib's normalized
rounds (`FlockSumcheck`), and its `v_c = R + v_a·v_b` ArkLib's `termNext`, `v_a·v_b - R`, in
characteristic two. The terminal relation does not read the zerocheck point (`termRel` reads the
skip challenge and `χ`), so the program's result, which drops the point, carries its doom
(`TermAlive`, at the point `0`). No mismatch.

A candidate `q` is alive when the program's carried claims hold of it (`fG`) and its true
statement (`flockStmt`) is in the component's relation. The lead is `(k + 1)·L₀/|E|`, the group
after the skip message `L₀·127/|E|`, each round's `L₀·2/|E|`, the last one followed by the
follower's `T`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Compile CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

section Zc

variable (F : FlockSpec) (prog : LeanVM.Semantics.Program) (s : LeanIsa.Sizes)
  (layout : LeanVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
  (toI : Column layout.stackLog → Column (fI F prog s).μ)
  (claims : List LeanVM.Protocol.Verifier.ColumnClaim) (input : LeanVM.Semantics.PublicInput)

/-- The carried condition: the program's column claims hold of the candidate. -/
def fG (q : Column layout.stackLog) : Prop := ColumnClaimsHold layout claims q

/-- A candidate's true statement. -/
def fS (q : Column layout.stackLog) : (fI F prog s).Stmt × PubOut (fI F prog s) :=
  flockStmt F prog s input (toI q)

/-- A candidate as the oracle. -/
def fO (q : Column layout.stackLog) : ∀ i, TheOracle (fI F prog s) i :=
  stackOracle F prog s (toI q)

/-- **The Flock phase's precondition** (the reading of `Seam.pub`): no candidate satisfies the
program's claims and the Flock predicate. -/
def FlockPre (h : List Ev) : Prop :=
  Doomed C (fun q ↦ ColumnClaimsHold layout claims q ∧ (fI F prog s).aux (toI q)) h

/-- Alive while the point is drawn: `pointRel j` at the first `j` drawn coordinates. -/
def PointAlive (j : ℕ) (acc : List E) (q : Column layout.stackLog) : Prop :=
  fG layout claims q ∧ (((fS F prog s layout toI input q, toVec j acc),
    fO F prog s layout toI q), ()) ∈
      Flock.pointRel (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s) j

/-- The zerocheck point's coordinates are the program's: the fixed ones, then the drawn ones. -/
theorem point_getElem {sampled : List E} (hlen : sampled.length = (fP F prog s).nRand)
    (j : ℕ) (hj : j < (fP F prog s).m + (fP F prog s).κ) :
    ((fP F prog s).point (toVec _ sampled))[j] =
      (LeanVM.Protocol.Verifier.fixedChallenges ++ sampled)[j]'(by
        have h7 : LeanVM.Protocol.Verifier.fixedChallenges.length = 7 := rfl
        have hn : (fP F prog s).nRand = s.τ 5 + 1 := rfl
        rw [List.length_append, h7, hlen, hn]
        change j < 8 + s.τ 5 at hj
        omega) := by
  have hn : (fP F prog s).nRand = s.τ 5 + 1 := rfl
  have h7 : LeanVM.Protocol.Verifier.fixedChallenges.length = 7 := rfl
  change j < 8 + s.τ 5 at hj
  simp only [Flock.Params.point, Vector.getElem_cast, Vector.getElem_append]
  split_ifs with hj7
  · change j < 7 at hj7
    rw [List.getElem_append_left (by rw [h7]; exact hj7)]
    simp [LeanVM.Protocol.Verifier.fixedChallenges, fP, flockParams]
  · change ¬ j < 7 at hj7
    rw [List.getElem_append_right (by rw [h7]; omega)]
    simp only [toVec, Vector.getElem_ofFn, h7]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    rfl

/-- A Vector of length `0` read off any list is the empty one. -/
theorem toVec_zero (l : List E) : toVec 0 l = #v[] := Vector.ext fun i hi ↦ absurd hi (by omega)

/-- **The point's escape**: a drawn coordinate makes a candidate alive at one value at most
(`drawPointSecurity`, `1/|E|`). -/
theorem point_escape (acc : List E) (q : Column layout.stackLog)
    (hq : ¬ PointAlive F prog s layout toI claims input acc.length acc q) :
    avgE (fun c ↦ indE (PointAlive F prog s layout toI claims input (acc ++ [c]).length
      (acc ++ [c]) q)) ≤ ((overE 1 : ℝ≥0) : ℝ≥0∞) := by
  simp only [List.length_append, List.length_singleton]
  by_cases hG : fG layout claims q
  · have hin := fun h ↦ hq ⟨hG, h⟩
    have h := sample_escape (Flock.drawPointSecurity (fP F prog s) (fC F prog s) (fz F prog s)
      (fside F prog s) acc.length) _ _ hin rfl
    rw [← overF_eq_overE]
    refine (avgE_mono fun c ↦ indE_mono fun hc ↦ ?_).trans h
    have hc' := hc.2
    rw [toVec_append_singleton rfl] at hc'
    exact hc'
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hG h.1).trans ?_
    refine (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans ?_
    exact zero_le

/-- The program's skip claim, `P(z_skip)` interpolated from the assumed zeros and the received
values. -/
def vPOf (pCoset : List E) (zSkip : E) : E :=
  LeanVM.Protocol.Verifier.lagrangeInterpolate (2 * LeanVM.Protocol.Verifier.kBits)
    (List.replicate LeanVM.Protocol.Verifier.kBits 0 ++ pCoset) zSkip

/-- Alive during the zerocheck's rounds: `rel zcFamily j` at the point, the skip challenge, the
round challenges and the running claim. -/
def ZcAlive (sampled : List E) (zSkip : E) (j : ℕ) (chi : List E) (v : E)
    (q : Column layout.stackLog) : Prop :=
  SumAlive (Flock.zcFamily (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s))
    (fG layout claims)
    (fun q ↦ (fS F prog s layout toI input q, (fP F prog s).point (toVec _ sampled), zSkip))
    (fO F prog s layout toI) j chi v q

/-- **The skip challenge's escape**: from a candidate outside `pointRel` at the drawn point, the
skip challenge makes it alive at the interpolated claim for `127` values at most
(`skipDrawSecurity`): two distinct polynomials of degree below `128` agree at `127` points. -/
theorem skip_escape (sampled pCoset : List E) (hp : pCoset.length = 64) (q : Column layout.stackLog)
    (hq : ¬ PointAlive F prog s layout toI claims input (fP F prog s).nRand sampled q) :
    avgE (fun Y ↦ indE (ZcAlive F prog s layout toI claims input sampled Y 0 []
      (vPOf pCoset Y) q)) ≤ ((overE 127 : ℝ≥0) : ℝ≥0∞) := by
  by_cases hG : fG layout claims q
  · have hin : ((((fS F prog s layout toI input q, toVec (fP F prog s).nRand sampled),
        (toVec 64 pCoset : Vector E (2 ^ (fP F prog s).s))), fO F prog s layout toI q), ()) ∉
        Flock.skipRel (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s) :=
      fun h ↦ hq ⟨hG, h.1⟩
    have h := sample_escape (Flock.skipDrawSecurity (fP F prog s) (fC F prog s) (fz F prog s)
      (fside F prog s) flockNodes_injective) _ _ hin rfl
    rw [← overF_eq_overE]
    refine (avgE_mono fun Y ↦ indE_mono fun hY ↦ ?_).trans h
    have hY' := hY.2
    rw [toVec_zero, vPOf, lagrangeInterpolate_eq_skipClaim pCoset hp] at hY'
    exact hY'
  · refine (avgE_mono fun c ↦ indE_mono (q := False) fun h ↦ hG h.1).trans ?_
    refine (avgE_le_of_le fun c ↦ (indE_of_not not_false).le).trans ?_
    exact zero_le

/-- The point the zerocheck's result is judged at: the terminal relation does not read it. -/
def zcDummy : Vector E ((fP F prog s).m + (fP F prog s).κ) := Vector.replicate _ 0

/-- Alive after the zerocheck: the terminal relation at the program's result (`χ`, `v_a, v_b,
v_c` and the skip challenge). -/
def TermAlive (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (q : Column layout.stackLog) :
    Prop :=
  fG layout claims q ∧ ((((fS F prog s layout toI input q, zcDummy F prog s, zc.zSkip),
    toVec ((fP F prog s).m + (fP F prog s).κ) zc.chi, zc.vA, zc.vB, zc.vC),
      fO F prog s layout toI q), ()) ∈
    Flock.termRel (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s)

/-- **The terminal values keep doom** (`zcEndSecurity`): a candidate alive at the program's result
was alive at the end of the rounds, since `v_c = R + v_a·v_b` is ArkLib's `v_a·v_b - R`. -/
theorem term_reflect (sampled : List E) (zSkip : E) (chi : List E) (running vA vB : E)
    (q : Column layout.stackLog)
    (hq : ¬ ZcAlive F prog s layout toI claims input sampled zSkip
      ((fP F prog s).m + (fP F prog s).κ) chi running q) :
    ¬ TermAlive F prog s layout toI claims input ⟨zSkip, chi, vA, vB, running + vA * vB⟩ q := by
  rintro ⟨hG, ht⟩
  refine hq ⟨hG, sendChecked_reflect (Flock.zcEndSecurity (fP F prog s) (fC F prog s)
    (fz F prog s) (fside F prog s)) _ _ #v[vA, vB] rfl ?_⟩
  have heq : vA * vB - running = running + vA * vB := by rw [CharTwo.sub_eq_add, add_comm]
  simp only [Flock.termNext, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, heq]
  exact ht

/-! ## The specification -/

/-- The rest of the zerocheck after the point: the skip message, `z_skip`, the rounds, the
terminal values. -/
def zcRest (sampled : List E) : Prog LeanVM.Protocol.Verifier.ZerocheckResult := do
  let pCoset ← Prog.readN LeanVM.Protocol.Verifier.kBits
  let zSkip ← Prog.sampleE
  let x ← LeanVM.Protocol.Verifier.sumcheck (vPOf pCoset zSkip) 3
    ((LeanVM.Protocol.Verifier.fixedChallenges ++ sampled).map some)
  zcTail zSkip x
where
  /-- The terminal values. -/
  zcTail (zSkip : E) : List E × E → Prog LeanVM.Protocol.Verifier.ZerocheckResult
    | (chi, running) => do
      let vA ← Prog.readE
      let vB ← Prog.readE
      return ⟨zSkip, chi, vA, vB, running + vA * vB⟩

/-- The zerocheck is the point's draws, then the rest. -/
theorem verifyFlockZerocheck_eq (logN : ℕ) :
    LeanVM.Protocol.Verifier.verifyFlockZerocheck logN =
      Prog.sampleN (logN - LeanVM.Protocol.Verifier.flockKSkip -
        LeanVM.Protocol.Verifier.fixedChallenges.length) >>= zcRest := rfl

/-- **The zerocheck's postcondition**: the result's `χ` has a coordinate per variable, and no
candidate is alive at the result. -/
def ZcPost (zc : LeanVM.Protocol.Verifier.ZerocheckResult) (h : List Ev) : Prop :=
  zc.chi.length = (fP F prog s).m + (fP F prog s).κ ∧
    Doomed C (TermAlive F prog s layout toI claims input zc) h

/-- The rounds' domains are the program's: the normalized domain at the program's coordinate. -/
theorem zc_weight (sampled : List E) (hlen : sampled.length = (fP F prog s).nRand) (zSkip : E)
    (q : Column layout.stackLog) (k : ℕ)
    (hk : k < ((LeanVM.Protocol.Verifier.fixedChallenges ++ sampled).map some).length) :
    (Flock.zcFamily (W := Unit) (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s)).weight
        (fS F prog s layout toI input q, (fP F prog s).point (toVec _ sampled), zSkip) (0 + k) =
      domOf ((LeanVM.Protocol.Verifier.fixedChallenges ++ sampled).map some)[k] := by
  have h7 : LeanVM.Protocol.Verifier.fixedChallenges.length = 7 := rfl
  have hn : (fP F prog s).nRand = s.τ 5 + 1 := rfl
  have hk' : k < (fP F prog s).m + (fP F prog s).κ := by
    simp only [List.length_map, List.length_append, h7, hlen, hn] at hk
    change k < 8 + s.τ 5
    omega
  simp only [Flock.zcFamily, SumcheckRound.normalizedWeights, zero_add, dite_eq_left hk',
    List.getElem_map, domOf]
  rw [point_getElem F prog s hlen k hk']

open Classical in
/-- **The rest of the zerocheck's specification**, from the drawn point. -/
noncomputable def zcRestSpec (hst : Stable C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} (hT : T ≤ εmax)
    (h127 : (L₀ : ℝ≥0∞) * ((overE 127 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (h2 : (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (sampled : List E) (hlen : sampled.length = (fP F prog s).nRand) :
    Spec (zcRest sampled)
      (Doomed C (PointAlive F prog s layout toI claims input (fP F prog s).nRand sampled))
      (ZcPost F prog s layout C toI claims input) εmax 0 T :=
  (doomReadN hst _ h127 63).bind' fun pCoset ↦
    if hp : pCoset.length = 64 then
      ((doomSample (εmax := εmax) (T := 0) hst hcard
        (PointAlive F prog s layout toI claims input (fP F prog s).nRand sampled)
        (fun Y q ↦ ZcAlive F prog s layout toI claims input sampled Y 0 [] (vPOf pCoset Y) q)
        ((overE 127 : ℝ≥0) : ℝ≥0∞)
        fun q hq ↦ skip_escape F prog s layout toI claims input sampled pCoset hp q hq).mono
          (fun _ (h : pCoset.length = 63 + 1 ∧ _) ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl
          le_rfl).bind' fun zSkip ↦
        (sumcheckSpecL (T := 0) hst hcard _
          (Flock.zcFamily_honest (fP F prog s) (fC F prog s) (fz F prog s)
            (fside F prog s)).toConsistent
          (Flock.zcFamily_sound (fP F prog s) (fC F prog s) (fz F prog s) (fside F prog s))
          (fG layout claims)
          (fun q ↦ (fS F prog s layout toI input q, (fP F prog s).point (toVec _ sampled), zSkip))
          (fO F prog s layout toI) h2 0 [] (vPOf pCoset zSkip) rfl _ (by
            simp only [ne_eq, List.map_eq_nil_iff, List.append_eq_nil_iff, not_and]
            intro h
            exact absurd h (by decide))
          (by
            have h7 : LeanVM.Protocol.Verifier.fixedChallenges.length = 7 := rfl
            simp only [List.length_map, List.length_append, h7, hlen, zero_add]
            change 7 + (s.τ 5 + 1) ≤ 8 + s.τ 5
            omega)
          (zc_weight F prog s layout toI input sampled hlen zSkip)).bind' fun (x : List E × E) ↦
            match x with
            | (chi, running) =>
              if hc : chi.length = (fP F prog s).m + (fP F prog s).κ then
              (doomRead (εmax := εmax) (T := 0) hst _ (zero_le.trans (zero_le.trans le_rfl))).mono
                (fun _ (h : chi.length = _ ∧ _) ↦ h.2) (fun _ _ h ↦ h) le_rfl le_rfl
                le_rfl |>.bind' fun vA ↦
              (doomRead hst _ hT).bind' fun vB ↦
                (Spec.ret (LeanVM.Protocol.Verifier.ZerocheckResult.mk zSkip chi vA vB
                  (running + vA * vB))).mono (fun h hd ↦ by
                  refine ⟨hc, fun q hq ht ↦ hd q hq ?_⟩
                  have e : 0 + ((LeanVM.Protocol.Verifier.fixedChallenges ++ sampled).map
                      some).length = (fP F prog s).m + (fP F prog s).κ := by
                    have h7 : LeanVM.Protocol.Verifier.fixedChallenges.length = 7 := rfl
                    simp only [List.length_map, List.length_append, h7, hlen, zero_add]
                    exact (fP F prog s).hpoint
                  rw [e, List.nil_append]
                  by_contra hz
                  exact term_reflect F prog s layout toI claims input sampled zSkip chi running
                    vA vB q hz ht) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
              else Spec.dead.mono (fun _ h ↦ hc (by
                have h7 : LeanVM.Protocol.Verifier.fixedChallenges.length = 7 := rfl
                have := h.1
                simp only [List.length_map, List.length_append, h7, hlen] at this
                rw [this]
                exact (fP F prog s).hpoint)) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
    else Spec.dead.mono (fun _ h ↦ hp h.1) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

/-- The Flock phase's precondition puts every candidate outside the argument's first relation. -/
theorem flockPre_point {h : List Ev} (hpre : FlockPre F prog s layout C toI claims h) :
    Doomed C (fun q ↦ PointAlive F prog s layout toI claims input ([] : List E).length [] q) h := by
  intro q hq ⟨hG, hrel⟩
  refine hpre q hq ⟨hG, ?_⟩
  by_contra haux
  refine not_pointRel_zero F prog s input (toI q) haux ?_
  have := hrel
  rw [List.length_nil, toVec_zero] at this
  exact this

/-- **The zerocheck's specification**: `verifyFlockZerocheck logN` at `logN = 14 + τ_BLAKE2S`
(`hlog`), from the Flock phase's precondition to `ZcPost`. The lead is `(k + 1) · L₀/|E|`, the
point's draws; the skip challenge's group is `L₀·127/|E|`, each round's `L₀·2/|E|`; the follower's
allowance `T` follows the terminal values. -/
noncomputable def zcSpec (hst : Stable C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} (hT : T ≤ εmax)
    (h127 : (L₀ : ℝ≥0∞) * ((overE 127 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax)
    (h2 : (L₀ : ℝ≥0∞) * ((overE 2 : ℝ≥0) : ℝ≥0∞) + 0 ≤ εmax) (logN : ℕ)
    (hlog : logN - LeanVM.Protocol.Verifier.flockKSkip -
      LeanVM.Protocol.Verifier.fixedChallenges.length = (fP F prog s).nRand) :
    Spec (LeanVM.Protocol.Verifier.verifyFlockZerocheck logN)
      (FlockPre F prog s layout C toI claims) (ZcPost F prog s layout C toI claims input) εmax
      ((∑ _i ∈ Finset.range (logN - LeanVM.Protocol.Verifier.flockKSkip -
          LeanVM.Protocol.Verifier.fixedChallenges.length),
        (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + 0) T :=
  Spec.congr (verifyFlockZerocheck_eq logN).symm <|
    ((doomSampleN hst hcard
      (fun acc q ↦ PointAlive F prog s layout toI claims input acc.length acc q)
      (fun _ ↦ ((overE 1 : ℝ≥0) : ℝ≥0∞))
      (fun acc q hq ↦ point_escape F prog s layout toI claims input acc q hq) _ []).mono
        (fun _ hpre ↦ flockPre_point F prog s layout C toI claims input hpre) (fun _ _ h ↦ h)
        le_rfl (by simp) le_rfl).bind' fun sampled ↦
      open Classical in
      if hl : sampled.length = (fP F prog s).nRand then
        (zcRestSpec F prog s layout C toI claims input hst hcard hT h127 h2 sampled hl).mono
          (fun _ h ↦ by simpa [hl] using h.2) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl
      else Spec.dead.mono (fun _ h ↦ hl (h.1.trans hlog)) (fun _ _ h ↦ h) le_rfl le_rfl le_rfl

end Zc

end
end LeanVM.Protocol.EndToEnd.Front
