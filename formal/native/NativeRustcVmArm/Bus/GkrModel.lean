module

public import NativeVm.Model.Gkr
public import NativeRustcVm.Sumcheck.Model
public import NativeRustcVm.Sumcheck.RoundPoly

/-!
# The GKR walk's model, as `gkr.rs` runs it

- `sampleChallenges_size`, `sumcheckFn_size`: `n` challenges, `n` rounds' challenges.
- `grindingBits_small`: the walk's grinds are of `0` bits (numerators at most `4`).
- `gkrStep_run`: `gkrStep` step by step, as `gkr_step` runs it (its grinds of `0` bits dropped);
  `gkrStep_size`: the point grows by `step`, three values.
- `gkrLayers_zero`, `gkrLayers_one`, `gkrLayers_odd`, `gkrLayers_even`: `gkrLayers`'s equations
  on states.
-/

namespace NativeRustcVmArm.Bus.Gkr

open NativeVm.Model NativeRustcVm.Sumcheck

public section

/-- `sampleChallenges n` returns `n` challenges. -/
theorem sampleChallenges_size {n : Nat} {s s' : TState} {xs : Array EW}
    (h : (sampleChallenges n).run s = some (xs, s')) : xs.size = n := by
  have key : ∀ (l : List Nat) (acc : Array EW) (s s' : TState) (xs : Array EW),
      (l.foldlM (fun acc _ ↦ do pure (acc.push (← sampleChallenge))) acc : VM (Array EW)).run s =
        some (xs, s') → xs.size = acc.size + l.length := by
    intro l
    induction l with
    | nil =>
      intro acc s s' xs h
      simp only [List.foldlM_nil, StateT.run_pure, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; simp
    | cons x l ih =>
      intro acc s s' xs h
      simp only [List.foldlM_cons, StateT.run_bind] at h
      cases hr : (sampleChallenge.run s) with
      | none =>
        simp only [bind, StateT.run] at h hr
        simp [hr] at h
      | some p =>
        obtain ⟨x, s1⟩ := p
        simp only [bind, StateT.run] at h hr
        simp only [hr, pure, StateT.pure, Option.bind_some] at h
        have := ih _ _ _ _ h
        simp at this
        simp; omega
  have := key (List.range n) #[] s s' xs h
  simpa using this

/-- `n` rounds of the sumcheck return `n` challenges. -/
theorem sumcheckFn_size (claim : EW) (count : Nat) (E : Nat → Option EW) :
    ∀ (n : Nat) {s s' : TState} {xs : Array EW} {c : EW},
      sumcheckFn claim count E n s = some ((xs, c), s') → xs.size = n
  | 0, s, s', xs, c, h => by
    rw [sumcheckFn_zero] at h
    cases h
    rfl
  | n + 1, s, s', xs, c, h => by
    rw [sumcheckFn_succ_apply] at h
    cases h0 : sumcheckFn claim count E n s with
    | none => rw [h0] at h; cases h
    | some p =>
      obtain ⟨⟨xs0, c0⟩, s0⟩ := p
      rw [h0, Option.bind_some] at h
      have ih := sumcheckFn_size claim count E n h0
      simp only [sumcheckRound, bind, StateT.bind, pure, StateT.pure] at h
      cases h1 : sumcheckRoundPoly count c0 (E n) s0 with
      | none => rw [h1] at h; cases h
      | some q =>
        rw [h1] at h
        simp only [Option.bind_some] at h
        cases h2 : sampleChallenge q.2 with
        | none => rw [h2] at h; cases h
        | some r =>
          rw [h2] at h
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1.1, Array.size_push, ih]

/-- The walk's grinds: numerators at most `4`, `0` bits. -/
theorem grindingBits_small {n : Nat} (h : n ≤ 4) : grindingBits n = 0 := by
  show LeanVM.Protocol.Compile.grindingBits n = 0
  unfold LeanVM.Protocol.Compile.grindingBits LeanVM.Protocol.Compile.securityBits
  split
  · rfl
  · have : Nat.log2 (n - 1) ≤ 1 := by
      have h3 : n - 1 < 2 ^ 2 := by omega
      have := (Nat.log2_lt (by omega)).mpr h3
      omega
    omega

/-- A grind of `0` bits changes nothing. -/
theorem grind_zero_run (s : TState) : (grind 0).run s = some ((), s) := by
  simp [grind, StateT.run, pure, StateT.pure]

/-- **`gkrStep` as `gkr_step` runs it**: the challenge, the sumcheck, the three children, the
check, the coordinates (the grinds, of `0` bits, dropped). -/
theorem gkrStep_run (step : Nat) (last : Bool) (g : GkrStateW) (s : TState) (hs : step ≤ 2) :
    (gkrStep step last g).run s =
      (sampleChallenge.run s).bind fun c ↦
        ((sumcheck (polyEval g.values c.1) (2 ^ step + 1) (g.point.map some)).run c.2).bind
          fun x ↦ ((readScalars (2 ^ step)).run x.2).bind fun h0 ↦
            ((readScalars (2 ^ step)).run h0.2).bind fun h1 ↦
              ((readScalars (2 ^ step)).run h1.2).bind fun h2 ↦
                if x.1.2 == polyEval #[prodE h0.1, prodE h1.1, prodE h2.1] c.1 then
                  ((sampleChallenges step).run h2.2).bind fun y ↦
                    some (⟨#[multilinearEval h0.1 y.1, multilinearEval h1.1 y.1,
                      multilinearEval h2.1 y.1], y.1 ++ x.1.1⟩, y.2)
                else none := by
  have g1 : grindingBits (LeanVM.Protocol.Verifier.nTrees - 1) = 0 :=
    grindingBits_small (by decide)
  have g2 : grindingBits (if last then 2 * step else step) = 0 :=
    grindingBits_small (by split <;> omega)
  simp only [gkrStep, g1, g2, StateT.run, bind, StateT.bind, pure, StateT.pure, grind,
    ↓reduceIte, require, Option.bind_some]
  cases sampleChallenge s with
  | none => rfl
  | some c =>
    simp only [Option.bind_some]
    cases sumcheck (polyEval g.values c.1) (2 ^ step + 1) (g.point.map some) c.2 with
    | none => rfl
    | some x =>
      simp only [Option.bind_some]
      cases readScalars (2 ^ step) x.2 with
      | none => rfl
      | some h0 =>
        simp only [Option.bind_some]
        cases readScalars (2 ^ step) h0.2 with
        | none => rfl
        | some h1 =>
          simp only [Option.bind_some]
          cases readScalars (2 ^ step) h1.2 with
          | none => rfl
          | some h2 =>
            simp only [Option.bind_some, List.map_toArray, List.map_cons, List.map_nil]
            by_cases hc : (x.1.2 == polyEval #[prodE h0.1, prodE h1.1, prodE h2.1] c.1) = true <;>
              simp only [hc, ↓reduceIte, Bool.false_eq_true] <;> rfl

/-- **The point grows by `step`**; three values. -/
theorem gkrStep_size {step : Nat} {last : Bool} {g g' : GkrStateW} {s s' : TState}
    (hs : step ≤ 2) (h : (gkrStep step last g).run s = some (g', s')) :
    g'.point.size = g.point.size + step ∧ g'.values.size = 3 := by
  rw [gkrStep_run step last g s hs] at h
  cases hc : sampleChallenge.run s with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc, Option.bind_some] at h
    cases hx : (sumcheck (polyEval g.values c.1) (2 ^ step + 1) (g.point.map some)).run c.2 with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx, Option.bind_some] at h
      cases h0 : (readScalars (2 ^ step)).run x.2 with
      | none => rw [h0] at h; cases h
      | some p0 =>
        rw [h0, Option.bind_some] at h
        cases h1 : (readScalars (2 ^ step)).run p0.2 with
        | none => rw [h1] at h; cases h
        | some p1 =>
          rw [h1, Option.bind_some] at h
          cases h2 : (readScalars (2 ^ step)).run p1.2 with
          | none => rw [h2] at h; cases h
          | some p2 =>
            rw [h2, Option.bind_some] at h
            split at h
            · cases hy : (sampleChallenges step).run p2.2 with
              | none => rw [hy] at h; cases h
              | some y =>
                rw [hy, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                obtain ⟨⟨xs, cl⟩, sx⟩ := x
                have hxs : xs.size = g.point.size := by
                  have := sumcheckFn_size (polyEval g.values c.1) (2 ^ step + 1)
                    (fun i ↦ g.point[i]?) g.point.size (s := c.2) (s' := sx) (xs := xs) (c := cl)
                    (by rw [sumcheckFn_getElem?]; exact hx)
                  exact this
                refine ⟨?_, rfl⟩
                simp only [Array.size_append, hxs, sampleChallenges_size hy]
                omega
            · cases h

/-! ## `gkrLayers` -/

theorem gkrLayers_zero (g : GkrStateW) (s : TState) : (gkrLayers 0 g).run s = some (g, s) := rfl

theorem gkrLayers_one (g : GkrStateW) (s : TState) :
    (gkrLayers 1 g).run s = (gkrStep 1 true g).run s := by
  simp only [gkrLayers, StateT.run, bind, StateT.bind, pure, StateT.pure]
  cases gkrStep 1 true g s <;> rfl

theorem gkrLayers_odd {n : Nat} (hn : n % 2 = 1) (g : GkrStateW) (s : TState) :
    (gkrLayers (n + 2) g).run s =
      ((gkrStep 1 false g).run s).bind fun p ↦ (gkrLayers (n + 1) p.1).run p.2 := by
  simp only [gkrLayers, hn, ite_true, StateT.run, bind, StateT.bind]

theorem gkrLayers_even {n : Nat} (hn : n % 2 = 0) (g : GkrStateW) (s : TState) :
    (gkrLayers (n + 2) g).run s =
      ((gkrStep 2 (decide (n = 0)) g).run s).bind fun p ↦ (gkrLayers n p.1).run p.2 := by
  have : ¬ n % 2 = 1 := by omega
  simp only [gkrLayers, this, ite_false, StateT.run, bind, StateT.bind]

/-! ## `gkrStep` after its sumcheck -/

/-- After the children: the check, the coordinates, the new state. -/
@[expose] def gkrFinish (step : Nat) (c cl : EW) (xs h0 h1 h2 : Array EW) (s : TState) :
    Option (GkrStateW × TState) :=
  if cl == polyEval #[prodE h0, prodE h1, prodE h2] c then
    ((sampleChallenges step).run s).bind fun y ↦
      some (⟨#[multilinearEval h0 y.1, multilinearEval h1 y.1, multilinearEval h2 y.1],
        y.1 ++ xs⟩, y.2)
  else none

/-- After the sumcheck: the three children, then `gkrFinish`. -/
@[expose] def gkrChildren (step : Nat) (c cl : EW) (xs : Array EW) (s : TState) :
    Option (GkrStateW × TState) :=
  ((readScalars (2 ^ step)).run s).bind fun h0 ↦
    ((readScalars (2 ^ step)).run h0.2).bind fun h1 ↦
      ((readScalars (2 ^ step)).run h1.2).bind fun h2 ↦
        gkrFinish step c cl xs h0.1 h1.1 h2.1 h2.2

/-- **`gkrStep` as `gkr_step` runs it**, the sumcheck as `sumcheckFn`. -/
theorem gkrStep_run' (step : Nat) (last : Bool) (g : GkrStateW) (s : TState) (hs : step ≤ 2) :
    (gkrStep step last g).run s =
      (sampleChallenge.run s).bind fun c ↦
        ((sumcheckFn (polyEval g.values c.1) (2 ^ step + 1) (fun i ↦ g.point[i]?)
          g.point.size).run c.2).bind fun x ↦ gkrChildren step c.1 x.1.2 x.1.1 x.2 := by
  rw [gkrStep_run step last g s hs]
  simp only [StateT.run, sumcheckFn_getElem?]
  rfl

/-! ## `verifyGkrGrandProducts` -/

/-- **`verifyGkrGrandProducts` step by step**: the two roots, the walk. -/
theorem verifyGkr_run (d : Nat) (s : TState) :
    (verifyGkrGrandProducts d).run s =
      (readScalar.run s).bind fun x ↦ (readScalar.run x.2).bind fun y ↦
        ((gkrLayers d ⟨#[x.1, x.1, y.1], #[]⟩).run y.2).bind fun z ↦
          some ((y.1, z.1.point, z.1.values), z.2) := by
  simp only [verifyGkrGrandProducts, StateT.run, bind, StateT.bind, pure, StateT.pure]

end

end NativeRustcVmArm.Bus.Gkr
