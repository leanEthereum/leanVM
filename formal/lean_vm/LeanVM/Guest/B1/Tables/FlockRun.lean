/-
  LeanVM.Guest.B1.Tables.FlockRun

  `verifyFlock`'s run read backward: an accepting run on any words determines them, the
  challenges and the matrices' arguments.
-/

module

public import LeanVM.Guest.B1.Tables.Flock

/-!
# `verifyFlock`, backward

`runId_verifyFlock`: on words of the zerocheck's and lincheck's shape, the run reaches the
matrices' value and the terminal check. `flockEv`: the evaluations taking `mv` at exactly one
argument and rejecting elsewhere, so that an accepting run with them names its arguments.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

theorem runs_of_nil {α : Type} {p : Prog α} {cv cv' : Digest} {a : α} (h : RunsTo p cv [] a cv')
    (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    Runs p ⟨cv, rest, os, roots⟩ a ⟨cv', rest, os, roots⟩ := h rest os roots

theorem runs_readE' (cv : Digest) (x : E) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs Prog.readE ⟨cv, x :: rest, os, roots⟩ x ⟨obsCv cv x, rest, os, roots⟩ := rfl

theorem runId_bind_of {α β : Type} {p : Prog α} {f : α → Prog β} {s s1 : St} {a : α}
    (h : Runs p s a s1) : runId (p.bind f) s = runId (f a) s1 := by
  rw [run_bind, h]; rfl

/-- **`verifyFlock` up to its matrices**: on the words of the zerocheck and the lincheck, the run
reaches the matrices' value at its arguments and the terminal check. -/
theorem runId_verifyFlock (ev : Evaluations) (τ : ℕ) (cv0 : Digest) (p : List E)
    (hp : p.length = 64) (ys chi : List E) (running : E) (cv4 : Digest)
    (hsc : ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      Runs (sumcheck (lagrangeInterpolate 128 (List.replicate 64 0 ++ p)
          (challengeOf (sqCv (obsAll (sqAll (τ + 1) cv0).2 p)))) 3
          ((fixedChallenges ++ (sqAll (τ + 1) cv0).1).map some))
        ⟨sqCv (obsAll (sqAll (τ + 1) cv0).2 p), ys ++ rest, os, roots⟩ (chi, running)
        ⟨cv4, rest, os, roots⟩)
    (a b : E) (zs rc : List E) (rLc : E) (cv7 : Digest)
    (hlc : ∀ (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      Runs (sumcheck (a + challengeOf (sqCv (obsCv (obsCv cv4 a) b)) * b +
          challengeOf (sqCv (obsCv (obsCv cv4 a) b)) ^ 2 * (running + a * b) +
          challengeOf (sqCv (obsCv (obsCv cv4 a) b)) ^ 3) 3 (List.replicate 8 none))
        ⟨sqCv (obsCv (obsCv cv4 a) b), zs ++ rest, os, roots⟩ (rc, rLc) ⟨cv7, rest, os, roots⟩)
    (s : List E) (hs : s.length = 64) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    runId (verifyFlock ev (14 + τ)) ⟨cv0, p ++ ys ++ [a, b] ++ zs ++ s ++ rest, os, roots⟩ =
      runId ((ev.matrices (challengeOf (sqCv (obsCv (obsCv cv4 a) b)))
          (challengeOf (sqCv (obsAll (sqAll (τ + 1) cv0).2 p))) (chi.take 8) rc.reverse s).bind
        fun mv => (Prog.require (mv + challengeOf (sqCv (obsCv (obsCv cv4 a) b)) ^ 2 *
            eqEval (chi.take 8) rc.reverse *
            dot (lagrangeWeights 64 (challengeOf (sqCv (obsAll (sqAll (τ + 1) cv0).2 p)))) s +
          challengeOf (sqCv (obsCv (obsCv cv4 a) b)) ^ 3 *
            (lincheckColumnWeights rc.reverse s).getD 512 0 = rLc)).bind
          fun _ => Prog.ret (rc.reverse ++ chi.drop 8, s))
        ⟨obsAll cv7 s, rest, os, roots⟩ := by
  have hsamp : 14 + τ - flockKSkip - fixedChallenges.length = τ + 1 := by
    rw [flockKSkip_eq, fixedChallenges_length]; omega
  simp only [verifyFlock, verifyFlockZerocheck, verifyFlockLincheck, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc, Prog.ret_bind, hsamp, flockNumLincheckRounds_eq, List.append_assoc,
    List.cons_append, List.nil_append, show kBits = 64 from rfl, show blake2sConstantColumn = 512 from rfl]
  rw [runId_bind_of (runs_of_nil (runsTo_sampleN (τ + 1) cv0) _ os roots),
    runId_bind_of (runs_readN _ p _ os roots (by rw [hp])),
    runId_bind_of (runs_of_nil (runsTo_sampleE _) _ os roots),
    show 2 * 64 = 128 from rfl,
    runId_bind_of (hsc _ os roots),
    runId_bind_of (runs_readE' _ a _ os roots),
    runId_bind_of (runs_readE' _ b _ os roots),
    runId_bind_of (runs_of_nil (runsTo_sampleE _) _ os roots),
    runId_bind_of (hlc _ os roots),
    runId_bind_of (runs_readN _ s _ os roots (by rw [hs]))]

/-! ## The evaluations naming their arguments -/

open Classical in
/-- The evaluations whose matrices take `mv` at `(alpha, zSkip, chiIn, chiInPrime, s)` and reject
at any other argument. -/
noncomputable def flockEv (alpha zSkip : E) (chiIn chiInPrime s : List E) (mv : E) : Evaluations :=
  ⟨fun _ _ => Prog.ret 0, fun a z ci cp sl =>
    (Prog.require (a = alpha ∧ z = zSkip ∧ ci = chiIn ∧ cp = chiInPrime ∧ sl = s)).bind
      fun _ => Prog.ret mv⟩

theorem flockEv_at (alpha zSkip : E) (chiIn chiInPrime s : List E) (mv : E) :
    MatricesAt (flockEv alpha zSkip chiIn chiInPrime s mv) alpha zSkip chiIn chiInPrime s mv := by
  intro st
  simp [flockEv, Prog.require]
  rfl

/-! ## The honest run on words `W` -/

section
variable (τ : ℕ) (cv0 : Digest) (W : List E)

/-- The words `verifyFlock` reads. -/
def flLen : ℕ := 146 + 2 * (τ + 8)

/-- Round 1's words. -/
def flP : List E := W.take 64

/-- The state after the sampled coordinates. -/
def flCvS : Digest := (sqAll (τ + 1) cv0).2

/-- The skip challenge. -/
def flZ : E := challengeOf (sqCv (obsAll (flCvS τ cv0) (flP W)))

/-- The zerocheck's equality factors: the fixed then the sampled coordinates. -/
def flE : ℕ → E := fun j => (fixedChallenges ++ (sqAll (τ + 1) cv0).1).getD j 0

/-- The zerocheck's rounds. -/
def flG : ℕ → E × E := fun j => (W.getD (64 + 2 * j) 0, W.getD (65 + 2 * j) 0)

/-- The zerocheck's start. -/
def flSt0 : E × Digest :=
  (lagrangeInterpolate 128 (List.replicate 64 0 ++ flP W) (flZ τ cv0 W),
    sqCv (obsAll (flCvS τ cv0) (flP W)))

/-- The zerocheck's end. -/
def flSc : E × Digest := scSt (flE τ cv0) (flG W) (flSt0 τ cv0 W) (τ + 8)

/-- The final evaluations. -/
def flA : E := W.getD (64 + 2 * (τ + 8)) 0

def flB : E := W.getD (65 + 2 * (τ + 8)) 0

/-- The state after them. -/
def flCv5 : Digest := obsCv (obsCv (flSc τ cv0 W).2 (flA τ W)) (flB τ W)

/-- The lincheck's `alpha`. -/
def flAlpha : E := challengeOf (sqCv (flCv5 τ cv0 W))

/-- The lincheck's start. -/
def flSt0' : E × Digest :=
  (flA τ W + flAlpha τ cv0 W * flB τ W +
    flAlpha τ cv0 W ^ 2 * ((flSc τ cv0 W).1 + flA τ W * flB τ W) + flAlpha τ cv0 W ^ 3,
    sqCv (flCv5 τ cv0 W))

/-- The lincheck's rounds. -/
def flG' : ℕ → E × E := fun j =>
  (W.getD (66 + 2 * (τ + 8) + 2 * j) 0, W.getD (67 + 2 * (τ + 8) + 2 * j) 0)

/-- The lincheck's end. -/
def flLc : E × Digest := lcSt (flG' τ W) (flSt0' τ cv0 W) 8

/-- The slices. -/
def flS : List E := (W.drop (82 + 2 * (τ + 8))).take 64

/-- The zerocheck's point. -/
def flChi : List E := (List.range (τ + 8)).map (scCh (flE τ cv0) (flG W) (flSt0 τ cv0 W))

/-- The lincheck's challenges. -/
def flRc : List E := (List.range 8).map (lcCh (flG' τ W) (flSt0' τ cv0 W))

/-- The terminal check at the matrices' value `mv`. -/
@[reducible] def flTerm (mv : E) : Prop :=
  mv + flAlpha τ cv0 W ^ 2 * eqEval ((flChi τ cv0 W).take 8) (flRc τ cv0 W).reverse *
      dot (lagrangeWeights 64 (flZ τ cv0 W)) (flS τ W) +
    flAlpha τ cv0 W ^ 3 * (lincheckColumnWeights (flRc τ cv0 W).reverse (flS τ W)).getD 512 0 =
      (flLc τ cv0 W).1

end

/-- A list's first `2n` words from offset `2k` are its rounds. -/
theorem roundWords_of_list (l : List E) (b : ℕ) (n : ℕ) (hl : b + 2 * n ≤ l.length) :
    roundWords (fun j => (l.getD (b + 2 * j) 0, l.getD (b + 1 + 2 * j) 0)) n 0 =
      (l.drop b).take (2 * n) := by
  apply List.ext_getElem (by rw [roundWords_length]; simp; omega)
  intro k h1 h2
  rw [roundWords_length] at h1
  rw [← List.getD_eq_getElem _ 0 (by rw [roundWords_length]; exact h1), roundWords_getD _ _ _ _ h1,
    List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0 (by omega)]
  split_ifs with h
  · simp only [Nat.zero_add]; congr 1; omega
  · simp only [Nat.zero_add]; congr 1; omega

/-- The words split into the run's phases. -/
theorem flock_split (τ : ℕ) (Y : List E) (hY : flLen τ ≤ Y.length) :
    Y = flP Y ++ roundWords (flG Y) (τ + 8) 0 ++ [flA τ Y, flB τ Y] ++
      roundWords (flG' τ Y) 8 0 ++ flS τ Y ++ Y.drop (flLen τ) := by
  have e1 := roundWords_of_list Y 64 (τ + 8) (by unfold flLen at hY; omega)
  have e2 := roundWords_of_list Y (66 + 2 * (τ + 8)) 8 (by unfold flLen at hY; omega)
  simp only [show ∀ j, 64 + 1 + 2 * j = 65 + 2 * j from fun j => by omega,
    show ∀ j, 66 + 2 * (τ + 8) + 1 + 2 * j = 67 + 2 * (τ + 8) + 2 * j from fun j => by omega] at e1 e2
  rw [show roundWords (flG Y) (τ + 8) 0 = _ from e1, show roundWords (flG' τ Y) 8 0 = _ from e2]
  unfold flLen at hY ⊢
  have dc : ∀ n, n < Y.length → Y.drop n = Y.getD n 0 :: Y.drop (n + 1) := fun n hn => by
    rw [List.drop_eq_getElem_cons hn, List.getD_eq_getElem _ _ hn]
  have d4 : Y.drop (82 + 2 * (τ + 8)) = flS τ Y ++ Y.drop (146 + 2 * (τ + 8)) := by
    have h := List.take_append_drop 64 (Y.drop (82 + 2 * (τ + 8)))
    rw [List.drop_drop] at h
    rw [flS, show 146 + 2 * (τ + 8) = 82 + 2 * (τ + 8) + 64 by omega]
    exact h.symm
  have d3 : Y.drop (66 + 2 * (τ + 8)) = (Y.drop (66 + 2 * (τ + 8))).take (2 * 8) ++
      Y.drop (82 + 2 * (τ + 8)) := by
    have h := List.take_append_drop (2 * 8) (Y.drop (66 + 2 * (τ + 8)))
    rw [List.drop_drop] at h
    rw [show 82 + 2 * (τ + 8) = 66 + 2 * (τ + 8) + 2 * 8 by omega]
    exact h.symm
  have d2 : Y.drop (64 + 2 * (τ + 8)) = flA τ Y :: flB τ Y :: Y.drop (66 + 2 * (τ + 8)) := by
    rw [dc _ (by omega), dc (64 + 2 * (τ + 8) + 1) (by omega), flA, flB,
      show 64 + 2 * (τ + 8) + 1 + 1 = 66 + 2 * (τ + 8) by omega,
      show 64 + 2 * (τ + 8) + 1 = 65 + 2 * (τ + 8) by omega]
  have d1 : Y.drop 64 = (Y.drop 64).take (2 * (τ + 8)) ++ Y.drop (64 + 2 * (τ + 8)) := by
    have h := List.take_append_drop (2 * (τ + 8)) (Y.drop 64)
    rw [List.drop_drop] at h
    exact h.symm
  conv_lhs => rw [← List.take_append_drop 64 Y, d1, d2, d3, d4]
  simp only [flP, List.append_assoc, List.cons_append, List.nil_append]

/-- **The run on any words long enough**: up to the matrices' value and the terminal check. -/
theorem flock_tail (ev : Evaluations) (τ : ℕ) (cv0 : Digest) (Y : List E) (hY : flLen τ ≤ Y.length)
    (os : List Opening) (roots : List (Digest × ℕ × ℕ)) :
    runId (verifyFlock ev (14 + τ)) ⟨cv0, Y, os, roots⟩ =
      runId ((ev.matrices (flAlpha τ cv0 Y) (flZ τ cv0 Y) ((flChi τ cv0 Y).take 8)
          (flRc τ cv0 Y).reverse (flS τ Y)).bind
        fun mv => (Prog.require (flTerm τ cv0 Y mv)).bind
          fun _ => Prog.ret ((flRc τ cv0 Y).reverse ++ (flChi τ cv0 Y).drop 8, flS τ Y))
        ⟨obsAll (flLc τ cv0 Y).2 (flS τ Y), Y.drop (flLen τ), os, roots⟩ := by
  have hL : flLen τ = 146 + 2 * (τ + 8) := rfl
  have hp : (flP Y).length = 64 := by simp [flP]; omega
  have hs : (flS τ Y).length = 64 := by simp [flS]; omega
  have hlen : (fixedChallenges ++ (sqAll (τ + 1) cv0).1).length = τ + 8 := by
    rw [List.length_append, fixedChallenges_length, sqAll_eq]; simp; omega
  conv_lhs => rw [flock_split τ Y hY]
  refine runId_verifyFlock ev τ cv0 (flP Y) hp _ (flChi τ cv0 Y) (flSc τ cv0 Y).1 (flSc τ cv0 Y).2
    (fun rest os roots => ?_) (flA τ Y) (flB τ Y) _ (flRc τ cv0 Y) (flLc τ cv0 Y).1 (flLc τ cv0 Y).2
    (fun rest os roots => ?_) (flS τ Y) hs _ os roots
  · have := runs_sumcheck_eq (flE τ cv0) (flG Y) (flSt0 τ cv0 Y) (τ + 8) 0 rest os roots
    simp only [Nat.zero_add] at this
    rw [map_some_range, hlen]
    exact this
  · have := runs_sumcheck_plain (flG' τ Y) (flSt0' τ cv0 Y) 8 0 rest os roots
    simp only [Nat.zero_add] at this
    rw [show List.replicate 8 (none : Option E) = (List.range 8).map (fun _ => none) from rfl]
    exact this

open Classical in
theorem flockEv_tail {alpha zSkip : E} {chiIn chiInPrime sl : List E} {mv : E} (A Z : E)
    (CI CP S : List E) (T : E → Prop) [DecidablePred T] {β : Type} (out : β) (st : St) :
    runId (((flockEv alpha zSkip chiIn chiInPrime sl mv).matrices A Z CI CP S).bind
        fun v => (Prog.require (T v)).bind fun _ => Prog.ret out) st =
      if (A = alpha ∧ Z = zSkip ∧ CI = chiIn ∧ CP = chiInPrime ∧ S = sl) ∧ T mv then some (out, st)
      else none := by
  simp only [flockEv, Prog.require]
  by_cases h1 : A = alpha ∧ Z = zSkip ∧ CI = chiIn ∧ CP = chiInPrime ∧ S = sl
  · rw [ite_pos' h1]
    simp only [Prog.ret_bind]
    by_cases h2 : T mv
    · rw [ite_pos' h2, ite_pos' ⟨h1, h2⟩]; rfl
    · rw [ite_neg' h2, ite_neg' (fun h => h2 h.2)]; rfl
  · rw [ite_neg' h1, ite_neg' (fun h => h1 h.1)]; rfl

/-- **An accepting run with `flockEv` names its words and arguments**: the words have the run's
length, the challenges, the slices and the final state are the honest ones of the words, and the
terminal check holds at `mv`. -/
theorem flock_inv {τ : ℕ} {cv0 cv' : Digest} {xs : List E} {alpha zSkip mv : E}
    {chi rcs s : List E}
    (h : RunsTo (verifyFlock (flockEv alpha zSkip (chi.take 8) rcs.reverse s mv) (14 + τ)) cv0 xs
      (rcs.reverse ++ chi.drop 8, s) cv') :
    xs.length = flLen τ ∧ zSkip = flZ τ cv0 xs ∧ alpha = flAlpha τ cv0 xs ∧ chi = flChi τ cv0 xs ∧
      rcs = flRc τ cv0 xs ∧ s = flS τ xs ∧ flTerm τ cv0 xs mv ∧
      cv' = obsAll (flLc τ cv0 xs).2 (flS τ xs) := by
  classical
  have hlen : xs.length = flLen τ := by
    have h1 := h (List.replicate (flLen τ) 0) [] []
    rw [flock_tail _ τ cv0 _ (by simp), flockEv_tail] at h1
    split_ifs at h1 with hc
    simp only [Option.some.injEq, Prod.mk.injEq, St.mk.injEq] at h1
    have := congrArg List.length h1.2.2.1
    simp at this
    omega
  have h0 := h [] [] []
  rw [List.append_nil, flock_tail _ τ cv0 _ (by omega), flockEv_tail] at h0
  split_ifs at h0 with hc
  obtain ⟨⟨ha, hz, hci, hcp, hs⟩, ht⟩ := hc
  simp only [Option.some.injEq, Prod.mk.injEq, St.mk.injEq] at h0
  obtain ⟨⟨ho1, ho2⟩, hcv, -⟩ := h0
  have hrc : rcs = flRc τ cv0 xs := by
    have := List.reverse_injective hcp
    exact this.symm
  have hchi : chi = flChi τ cv0 xs := by
    rw [← List.take_append_drop 8 chi, ← List.take_append_drop 8 (flChi τ cv0 xs), ← hci]
    rw [hrc] at ho1
    exact congrArg _ (List.append_cancel_left ho1).symm
  exact ⟨hlen, hz.symm, ha.symm, hchi, hrc, hs.symm, ht, hcv.symm⟩

end
end LeanVM.Guest.B1
