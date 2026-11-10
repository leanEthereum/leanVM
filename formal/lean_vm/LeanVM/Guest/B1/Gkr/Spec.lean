/-
  LeanVM.Guest.B1.Gkr.Spec

  The specification's GKR walk as runs on the carried sponge: the equality-mode sumcheck round by
  round, one step of the walk, and the walk by layers.
-/

module

public import LeanVM.Guest.B1.Gkr.Interface
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Guest.B1.Sumcheck.Meaning

/-!
# The GKR walk on the carried sponge

* `gkrRun` (B1-a's, `B1/Sumcheck/Meaning`): equality-mode rounds of four coefficients each, the
  derived `c0 = claim + e·Σ c`, a squeeze per round; `gkr_sumcheck_run`: it is `sumcheck _ 5`
  over the eq factors, as a run.
* `gkrStep_run`: one step of `step ≤ 2` levels (`gkrStep`), from its combiner, rounds, children
  and new coordinates, when its check holds. Its grinds are of `0` bits (`grindingBits_le_eight`):
  the combiner's of `grindingBits 2`, the rounds' of `grindingBits 5` at most, `y`'s of
  `grindingBits 4` at most, so a step is the same program whether it is the last or not
  (`gkrStep_last`).
* `gkrLayers_even`, `gkrLayers_odd`: the walk is its root-most step, of two levels at an even
  depth and one at an odd depth, then `gkrPairs`, steps of two levels appended one at a time.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## The grinds of `0` bits -/

/-- **A message of at most eight values grinds no bits** (`2^-125` at `|E| = 2^128`). -/
theorem grindingBits_le_eight {n : ℕ} (h : n ≤ 8) : grindingBits n = 0 := by
  unfold grindingBits securityBits
  interval_cases n <;> decide

theorem grindProofOfWork_le_eight {n : ℕ} (h : n ≤ 8) :
    VerifierProgram.grindProofOfWork (grindingBits n) = pure () := by
  rw [grindingBits_le_eight h]; rfl

/-- An equality-mode round of five coefficients grinds nothing. -/
theorem sumcheckRoundPoly_five (claim e : E) :
    sumcheckRoundPoly 5 claim (some e) = VerifierProgram.readScalars 4 >>= fun tail =>
      pure ((claim + e * sumE tail) :: tail) := by
  simp (disch := omega) only [sumcheckRoundPoly, grindingBits_le_eight,
    VerifierProgram.grindProofOfWork, ↓reduceIte]
  rfl

/-! ## Equality-mode sumcheck rounds -/

theorem sumcheck_cons_eq' (claim : E) (count : ℕ) (e : Option E) (es : List (Option E)) :
    sumcheck claim count (e :: es) =
      sumcheckRoundPoly count claim e >>= fun message
          => VerifierProgram.sampleChallenge >>= fun challenge =>
        sumcheck (polyEval message challenge) count es >>= fun r =>
          pure (challenge :: r.1, r.2) := by
  simp only [sumcheck]

/-- **The equality-mode sumcheck of `count = 5` coefficients is `gkrRun`.** -/
theorem gkr_sumcheck_run : ∀ (cs : List (List E)) (es : List E) (claim : E) (s : Fs),
    cs.length = es.length → (∀ c ∈ cs, c.length = 4) →
    RunsTo (sumcheck claim 5 (es.map some)) s cs.flatten
      ((gkrRun cs es claim s).1, (gkrRun cs es claim s).2.1) (gkrRun cs es claim s).2.2
  | [], [], claim, s, _, _ => by
    simp only [List.map_nil, sumcheck, List.flatten_nil, gkrRun]
    exact runsTo_ret _ _
  | c :: cs, e :: es, claim, s, hl, hc => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hc4 : c.length = 4 := hc c (by simp)
    have ih := gkr_sumcheck_run cs es
      (polyEval ((claim + e * sumE c) :: c) ((s.absorbAll c dsObserve).squeeze.1))
      (s.absorbAll c dsObserve).squeeze.2 hl (fun c' hc' => hc c' (by simp [hc']))
    rw [List.map_cons, sumcheck_cons_eq']
    have hround : RunsTo (sumcheckRoundPoly 5 claim (some e)) s c
        ((claim + e * sumE c) :: c) (s.absorbAll c dsObserve) := by
      have h := (runsTo_readN s c).bind
        (f := fun tail => (pure ((claim + e * sumE tail) :: tail) : VerifierProgram (List E)))
        (runsTo_ret ((claim + e * sumE c) :: c) _)
      rw [List.append_nil, hc4] at h
      rw [sumcheckRoundPoly_five]
      exact h
    have := hround.bind (f := fun message => VerifierProgram.sampleChallenge >>= fun challenge =>
        sumcheck (polyEval message challenge) 5 (es.map some) >>= fun r =>
          pure (challenge :: r.1, r.2))
      ((runsTo_sampleE _).bind (ih.bind (f := fun r =>
        (pure ((s.absorbAll c dsObserve).squeeze.1 :: r.1, r.2) : VerifierProgram (List E × E)))
        (runsTo_ret _ _)))
    refine this.of_eq rfl ?_ ?_ ?_
    · simp
    · simp [gkrRun]
    · simp [gkrRun]

/-! ## One step of the walk -/

/-- **A step of at most two levels grinds nothing**, so it is the same program whether it is the
last or not. -/
theorem gkrStep_eq {step : ℕ} (hs : step ≤ 2) (last : Bool) (st : GkrState) :
    gkrStep step last st = VerifierProgram.sampleChallenge >>= fun combiner =>
      sumcheck (polyEval st.values combiner) (2 ^ step + 1) (st.point.map some) >>= fun r =>
        VerifierProgram.readScalars (2 ^ step) >>= fun child0
            => VerifierProgram.readScalars (2 ^ step) >>= fun child1 =>
          VerifierProgram.readScalars (2 ^ step) >>= fun child2 =>
            VerifierProgram.require (r.2 = polyEval [prodE child0, prodE child1, prodE child2]
                combiner) >>=
              fun _ => VerifierProgram.sampleChallenges step >>= fun y =>
                pure ⟨[child0, child1, child2].map (multilinearEval · y), y ++ r.1⟩ := by
  have hy : grindingBits (if last = true then 2 * step else step) = 0 :=
    grindingBits_le_eight (by split <;> omega)
  simp (disch := omega) only [gkrStep, nTrees, hy, grindingBits_le_eight,
    VerifierProgram.grindProofOfWork, ↓reduceIte, List.map_cons, List.map_nil]
  rfl

theorem gkrStep_last {step : ℕ} (hs : step ≤ 2) (last : Bool) (st : GkrState) :
    gkrStep step last st = gkrStep step false st := by
  rw [gkrStep_eq hs, gkrStep_eq hs]

theorem tb_runsTo_require {c : Prop} [Decidable c] (hc : c) (s : Fs) :
    RunsTo (VerifierProgram.require c) s [] () s := by
  simp only [VerifierProgram.require, hc, ↓reduceIte]
  exact runsTo_ret () s

/-- **One step of the walk as a run**: from the sponge `s`, the step samples its combiner, runs
its sumcheck (`hsc`, reading `xs` to the challenges `x` and the claim `claim'`), reads the three
trees' children, checks them, samples `y`, and returns their values at `y` with the point
`y ++ x`. -/
theorem gkrStep_run {step : ℕ} (hs : step ≤ 2) (last : Bool) {st : GkrState} {s s1 : Fs} {xs : List E} {x : List E}
    {claim' : E}
    (hsc : RunsTo (sumcheck (polyEval st.values s.squeeze.1) (2 ^ step + 1) (st.point.map some))
      s.squeeze.2 xs (x, claim') s1)
    {ch0 ch1 ch2 : List E} (h0 : ch0.length = 2 ^ step) (h1 : ch1.length = 2 ^ step)
    (h2 : ch2.length = 2 ^ step)
    (hcheck : claim' = polyEval [prodE ch0, prodE ch1, prodE ch2] s.squeeze.1) :
    RunsTo (gkrStep step last st) s (xs ++ (ch0 ++ (ch1 ++ ch2)))
      ⟨[ch0, ch1, ch2].map (fun c ↦ multilinearEval c
          ((((s1.absorbAll ch0 dsObserve).absorbAll ch1 dsObserve).absorbAll ch2
            dsObserve).squeezeN step).1),
        ((((s1.absorbAll ch0 dsObserve).absorbAll ch1 dsObserve).absorbAll ch2
            dsObserve).squeezeN step).1 ++ x⟩
      ((((s1.absorbAll ch0 dsObserve).absorbAll ch1 dsObserve).absorbAll ch2
        dsObserve).squeezeN step).2 := by
  rw [gkrStep_eq hs]
  have r0 := runsTo_readN s1 ch0
  have r1 := runsTo_readN (s1.absorbAll ch0 dsObserve) ch1
  have r2 := runsTo_readN ((s1.absorbAll ch0 dsObserve).absorbAll ch1 dsObserve) ch2
  rw [h0] at r0
  rw [h1] at r1
  rw [h2] at r2
  have hq := tb_runsTo_require hcheck
    (((s1.absorbAll ch0 dsObserve).absorbAll ch1 dsObserve).absorbAll ch2 dsObserve)
  have hy := runsTo_sampleN step
    (((s1.absorbAll ch0 dsObserve).absorbAll ch1 dsObserve).absorbAll ch2 dsObserve)
  have hc2 := r2.bind (f := fun child2 =>
    VerifierProgram.require (claim' = polyEval [prodE ch0, prodE ch1, prodE child2] s.squeeze.1) >>=
      fun _ => VerifierProgram.sampleChallenges step >>= fun y =>
        (pure ⟨[ch0, ch1, child2].map (multilinearEval · y), y ++ x⟩ : VerifierProgram GkrState))
    (hq.bind (f := fun _ => VerifierProgram.sampleChallenges step >>= fun y =>
        (pure ⟨[ch0, ch1, ch2].map (multilinearEval · y), y ++ x⟩ : VerifierProgram GkrState))
      (hy.bind (f := fun y =>
        (pure ⟨[ch0, ch1, ch2].map (multilinearEval · y), y ++ x⟩ : VerifierProgram GkrState))
        (runsTo_ret _ _)))
  have hc1 := r1.bind (f := fun child1 => VerifierProgram.readScalars (2 ^ step) >>= fun child2 =>
    VerifierProgram.require (claim' = polyEval [prodE ch0, prodE child1, prodE child2]
        s.squeeze.1) >>=
      fun _ => VerifierProgram.sampleChallenges step >>= fun y =>
        (pure ⟨[ch0, child1, child2].map
            (multilinearEval · y), y ++ x⟩ : VerifierProgram GkrState)) hc2
  have hc0 := r0.bind (f := fun child0 => VerifierProgram.readScalars (2 ^ step) >>= fun child1 =>
    VerifierProgram.readScalars (2 ^ step) >>= fun child2 =>
    VerifierProgram.require (claim' = polyEval [prodE child0, prodE child1, prodE child2]
        s.squeeze.1) >>=
      fun _ => VerifierProgram.sampleChallenges step >>= fun y =>
        (pure ⟨[child0, child1, child2].map
            (multilinearEval · y), y ++ x⟩ : VerifierProgram GkrState)) hc1
  have hs := hsc.bind (f := fun r => VerifierProgram.readScalars (2 ^ step) >>= fun child0 =>
    VerifierProgram.readScalars (2 ^ step) >>= fun child1
        => VerifierProgram.readScalars (2 ^ step) >>= fun child2 =>
    VerifierProgram.require (r.2 = polyEval [prodE child0, prodE child1, prodE child2]
        s.squeeze.1) >>=
      fun _ => VerifierProgram.sampleChallenges step >>= fun y =>
        (pure ⟨[child0, child1, child2].map
            (multilinearEval · y), y ++ r.1⟩ : VerifierProgram GkrState)) hc0
  have := (runsTo_sampleE s).bind (f := fun combiner =>
    sumcheck (polyEval st.values combiner) (2 ^ step + 1) (st.point.map some) >>= fun r =>
      VerifierProgram.readScalars (2 ^ step) >>= fun child0
          => VerifierProgram.readScalars (2 ^ step) >>= fun child1 =>
        VerifierProgram.readScalars (2 ^ step) >>= fun child2 =>
          VerifierProgram.require (r.2 = polyEval [prodE child0, prodE child1, prodE child2]
              combiner) >>=
            fun _ => VerifierProgram.sampleChallenges step >>= fun y =>
              (pure ⟨[child0, child1, child2].map (multilinearEval · y), y ++ r.1⟩ : VerifierProgram GkrState)) hs
  exact this.of_eq rfl (by simp) rfl rfl

/-! ## The walk by layers -/

/-- `n` steps of two levels, from `s`. -/
def gkrPairs : ℕ → GkrState → VerifierProgram GkrState
  | 0, s => pure s
  | k + 1, s => gkrPairs k s >>= gkrStep 2 false

theorem gkrPairs_succ' (k : ℕ) (s : GkrState) :
    gkrPairs (k + 1) s = gkrStep 2 false s >>= gkrPairs k := by
  induction k generalizing s with
  | zero => simp only [gkrPairs, pure_bind, bind_pure]
  | succ k ih => rw [gkrPairs, ih, bind_assoc]; rfl

/-- At an even depth past the root-most step, the walk is `gkrPairs`. -/
theorem gkrLayers_pairs (k : ℕ) (s : GkrState) : gkrLayers (2 * k) s = gkrPairs k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, gkrLayers, gkrPairs_succ']
    simp only [show ¬ (2 * k % 2 = 1) by omega, ↓reduceIte]
    rw [gkrStep_last (step := 2) le_rfl (decide (2 * k = 0))]
    congr 1
    funext t
    exact ih t

/-- **At an even depth, the walk is one step of two levels, then `gkrPairs`.** -/
theorem gkrLayers_even (k : ℕ) (s : GkrState) :
    gkrLayers (2 * k + 2) s = gkrStep 2 false s >>= gkrPairs k := by
  rw [show 2 * k + 2 = 2 * (k + 1) by omega, gkrLayers_pairs, gkrPairs_succ']

/-- **At an odd depth, the walk is one step of one level, then `gkrPairs`.** -/
theorem gkrLayers_odd (k : ℕ) (s : GkrState) :
    gkrLayers (2 * k + 1) s = gkrStep 1 false s >>= gkrPairs k := by
  cases k with
  | zero =>
    show gkrLayers 1 s = _
    rw [gkrLayers, gkrStep_last (step := 1) (by norm_num) true]
    rfl
  | succ k =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, gkrLayers]
    simp only [show (2 * k + 1) % 2 = 1 by omega, ↓reduceIte]
    congr 1
    funext t
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, gkrLayers_pairs]

end
end LeanVM.Guest.B1.Tables
