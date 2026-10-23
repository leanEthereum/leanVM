/-
  LeanVM.Guest.B1.Tables.FlockSpec

  `verifyFlock` (V:1997) as the guest walks it: the two sumchecks round by round, the skip
  interpolation from the numerators, and the whole run assembled from its phases.
-/

module

public import LeanVM.Guest.B1.Tables.FlockLoops
public import LeanVM.Guest.B1.VerifySub.Run
public import LeanVM.Guest.B1.Main.FreshWeight

/-!
# `verifyFlock`, phase by phase

`scSt e g s0` is the state (claim, chain) of the equality-mode sumcheck after its first `j`
rounds, the round `j` with equality factor `e j` reading `g j`; `scCh` its challenges
(`runs_sumcheck_eq`). `lcSt`, `lcCh`: the same for the plain-mode sumcheck of the lincheck
(`runs_sumcheck_plain`). `runs_verifyFlock` assembles `verifyFlock ev (14 + τ)` from its phases.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-! ## The sumchecks round by round -/

/-- The equality-mode sumcheck's claim and chain after `j` rounds. -/
def scSt (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) : ℕ → E × Digest
  | 0 => s0
  | j + 1 => (scStep (e j) (g j) (scSt e g s0 j)).2

/-- Its challenge at round `j`. -/
def scCh (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) : E :=
  (scStep (e j) (g j) (scSt e g s0 j)).1

/-- The plain-mode sumcheck's claim and chain after `j` rounds. -/
def lcSt (g : ℕ → E × E) (s0 : E × Digest) : ℕ → E × Digest
  | 0 => s0
  | j + 1 => (lcStep (g j) (lcSt g s0 j)).2

/-- Its challenge at round `j`. -/
def lcCh (g : ℕ → E × E) (s0 : E × Digest) (j : ℕ) : E := (lcStep (g j) (lcSt g s0 j)).1

/-- The words of rounds `k .. k + n`. -/
def roundWords (g : ℕ → E × E) (n k : ℕ) : List E :=
  ((List.range n).map fun j => [(g (k + j)).1, (g (k + j)).2]).flatten

theorem roundWords_succ (g : ℕ → E × E) (n k : ℕ) :
    roundWords g (n + 1) k = (g k).1 :: (g k).2 :: roundWords g n (k + 1) := by
  simp only [roundWords, List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons,
    Nat.add_zero, List.cons_append, List.nil_append]
  congr 3
  exact List.map_congr_left fun j _ => by
    simp only [Function.comp_apply, show k + (j + 1) = k + 1 + j by omega]

theorem roundWords_length (g : ℕ → E × E) (n k : ℕ) : (roundWords g n k).length = 2 * n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => rw [roundWords_succ, List.length_cons, List.length_cons, ih]; ring

theorem map_range_succ_shift {α : Type} (f : ℕ → α) (n k : ℕ) :
    (List.range (n + 1)).map (fun j => f (k + j)) =
      f k :: (List.range n).map fun j => f (k + 1 + j) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  exact List.map_congr_left fun j _ => by simp only [Function.comp_apply]; congr 1; omega

theorem runs_roundEq (c e g1 g2 : E) (cv : Digest) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs (sumcheckRoundPoly 3 c (some e)) ⟨cv, g1 :: g2 :: rest, os, roots⟩
      [c + e * sumE [g1, g2], g1, g2] ⟨obsCv (obsCv cv g1) g2, rest, os, roots⟩ := by
  simp only [sumcheckRoundPoly, Prog.bind_eq, Prog.pure_eq]
  exact Runs.bind (RunsTo.runs (runsTo_readN cv [g1, g2]) rest os roots) (Runs.ret _ _)

theorem runs_roundPlain (c c0 c2 : E) (cv : Digest) (rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) :
    Runs (sumcheckRoundPoly 3 c none) ⟨cv, c0 :: c2 :: rest, os, roots⟩
      [c0, c + sumE [c2], c2] ⟨obsCv (obsCv cv c0) c2, rest, os, roots⟩ := by
  simp only [sumcheckRoundPoly, Prog.bind_eq, Prog.pure_eq]
  exact Runs.bind (RunsTo.runs (runsTo_readE cv c0) _ os roots)
    (Runs.bind (RunsTo.runs (runsTo_readN (obsCv cv c0) [c2]) rest os roots) (Runs.ret _ _))

/-- **The equality-mode sumcheck** (V:1325, every round `some (e j)`) runs round by round. -/
theorem runs_sumcheck_eq (e : ℕ → E) (g : ℕ → E × E) (s0 : E × Digest) :
    ∀ n k (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      Runs (sumcheck (scSt e g s0 k).1 3 ((List.range n).map fun j => some (e (k + j))))
        ⟨(scSt e g s0 k).2, roundWords g n k ++ rest, os, roots⟩
        ((List.range n).map fun j => scCh e g s0 (k + j), (scSt e g s0 (k + n)).1)
        ⟨(scSt e g s0 (k + n)).2, rest, os, roots⟩
  | 0, k, rest, os, roots => by
    simp only [List.range_zero, List.map_nil, Nat.add_zero, roundWords, List.flatten_nil,
      List.nil_append, sumcheck]
    exact Runs.ret _ _
  | n + 1, k, rest, os, roots => by
    have ih := runs_sumcheck_eq e g s0 n (k + 1) rest os roots
    have hp : polyEval [(scSt e g s0 k).1 + e k * sumE [(g k).1, (g k).2], (g k).1, (g k).2]
        (scCh e g s0 k) = (scSt e g s0 (k + 1)).1 := by
      simp only [polyEval, sumE, scCh, scSt, scStep, List.foldr, List.foldl]
      ring
    rw [show (List.range (n + 1)).map (fun j => some (e (k + j))) = some (e k) ::
        (List.range n).map (fun j => some (e (k + 1 + j))) from
        map_range_succ_shift (fun j => some (e j)) n k,
      show (List.range (n + 1)).map (fun j => scCh e g s0 (k + j)) = scCh e g s0 k ::
        (List.range n).map (fun j => scCh e g s0 (k + 1 + j)) from
        map_range_succ_shift (scCh e g s0) n k, roundWords_succ,
      show k + (n + 1) = k + 1 + n by omega, sumcheck,
      Prog.bind_eq]
    refine Runs.bind (runs_roundEq _ _ _ _ _ _ os roots) ?_
    simp only [Prog.bind_eq]
    refine Runs.bind (RunsTo.runs (runsTo_sampleE _) _ os roots) ?_
    rw [show challengeOf (sqCv (obsCv (obsCv (scSt e g s0 k).2 (g k).1) (g k).2)) =
      scCh e g s0 k from rfl, hp]
    refine Runs.bind ih ?_
    exact Runs.ret _ _

/-- **The plain-mode sumcheck** (every round `none`) runs round by round. -/
theorem runs_sumcheck_plain (g : ℕ → E × E) (s0 : E × Digest) :
    ∀ n k (rest : List E) (os : List Opening) (roots : List (Digest × ℕ × ℕ)),
      Runs (sumcheck (lcSt g s0 k).1 3 ((List.range n).map fun _ => none))
        ⟨(lcSt g s0 k).2, roundWords g n k ++ rest, os, roots⟩
        ((List.range n).map fun j => lcCh g s0 (k + j), (lcSt g s0 (k + n)).1)
        ⟨(lcSt g s0 (k + n)).2, rest, os, roots⟩
  | 0, k, rest, os, roots => by
    simp only [List.range_zero, List.map_nil, Nat.add_zero, roundWords, List.flatten_nil,
      List.nil_append, sumcheck]
    exact Runs.ret _ _
  | n + 1, k, rest, os, roots => by
    have ih := runs_sumcheck_plain g s0 n (k + 1) rest os roots
    have hp : polyEval [(g k).1, (lcSt g s0 k).1 + sumE [(g k).2], (g k).2] (lcCh g s0 k) =
        (lcSt g s0 (k + 1)).1 := by
      simp only [polyEval, sumE, lcCh, lcSt, lcStep, List.foldr, List.foldl]
      ring
    rw [show (List.range (n + 1)).map (fun _ => (none : Option E)) = none ::
        (List.range n).map (fun _ => none) from map_range_succ_shift (fun _ => none) n k,
      show (List.range (n + 1)).map (fun j => lcCh g s0 (k + j)) = lcCh g s0 k ::
        (List.range n).map (fun j => lcCh g s0 (k + 1 + j)) from
        map_range_succ_shift (lcCh g s0) n k, roundWords_succ,
      show k + (n + 1) = k + 1 + n by omega, sumcheck, Prog.bind_eq]
    refine Runs.bind (runs_roundPlain _ _ _ _ _ os roots) ?_
    simp only [Prog.bind_eq]
    refine Runs.bind (RunsTo.runs (runsTo_sampleE _) _ os roots) ?_
    rw [show challengeOf (sqCv (obsCv (obsCv (lcSt g s0 k).2 (g k).1) (g k).2)) =
      lcCh g s0 k from rfl, hp]
    refine Runs.bind ih ?_
    exact Runs.ret _ _

/-! ## The whole run -/

theorem flockKSkip_eq : flockKSkip = 6 := by decide

theorem fixedChallenges_length : fixedChallenges.length = 7 := rfl

theorem flockNumLincheckRounds_eq : flockNumLincheckRounds = 8 := by decide

theorem runs_readN (cv : Digest) (xs rest : List E) (os : List Opening)
    (roots : List (Digest × ℕ × ℕ)) {n : ℕ} (hn : xs.length = n) :
    Runs (Prog.readN n) ⟨cv, xs ++ rest, os, roots⟩ xs ⟨obsAll cv xs, rest, os, roots⟩ := by
  subst hn; exact RunsTo.runs (runsTo_readN cv xs) rest os roots

/-- **`verifyFlock ev (14 + τ)` from its phases** (V:1829-1999): the `τ + 1` sampled
coordinates, round 1's 64 words `p`, the skip challenge `z`, the equality-mode sumcheck over the
fixed then sampled coordinates, the final evaluations `a`, `b`, the lincheck's `alpha`, its
plain-mode sumcheck, the 64 slices `s`, and the terminal identity with the matrices' value `mv`
that `ev` takes. -/
theorem runs_verifyFlock (ev : Evaluations) (τ : ℕ) (cv0 : Digest) (p : List E)
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
    (s : List E) (hs : s.length = 64) (mv : E)
    (hmv : MatricesAt ev (challengeOf (sqCv (obsCv (obsCv cv4 a) b)))
      (challengeOf (sqCv (obsAll (sqAll (τ + 1) cv0).2 p))) (chi.take 8) rc.reverse s mv)
    (hterm : mv + challengeOf (sqCv (obsCv (obsCv cv4 a) b)) ^ 2 * eqEval (chi.take 8) rc.reverse *
        dot (lagrangeWeights 64 (challengeOf (sqCv (obsAll (sqAll (τ + 1) cv0).2 p)))) s +
        challengeOf (sqCv (obsCv (obsCv cv4 a) b)) ^ 3 *
          (lincheckColumnWeights rc.reverse s).getD 512 0 = rLc) :
    RunsTo (verifyFlock ev (14 + τ)) cv0 (p ++ ys ++ [a, b] ++ zs ++ s)
      (rc.reverse ++ chi.drop 8, s)
      (obsAll cv7 s) := by
  intro rest os roots
  have hsamp : 14 + τ - flockKSkip - fixedChallenges.length = τ + 1 := by
    rw [flockKSkip_eq, fixedChallenges_length]; omega
  show Runs _ _ _ _
  simp only [verifyFlock, verifyFlockZerocheck, verifyFlockLincheck, Prog.bind_eq, Prog.pure_eq,
    Prog.bind_assoc, Prog.ret_bind, hsamp, flockNumLincheckRounds_eq, List.append_assoc,
    List.cons_append, List.nil_append]
  refine Runs.bind (RunsTo.runs (runsTo_sampleN (τ + 1) cv0) _ os roots) ?_
  refine Runs.bind (runs_readN _ p _ os roots (by rw [hp]; rfl)) ?_
  refine Runs.bind (RunsTo.runs (runsTo_sampleE _) _ os roots) ?_
  refine Runs.bind (hsc _ os roots) ?_
  refine Runs.bind (RunsTo.runs (runsTo_readE _ a) _ os roots) ?_
  refine Runs.bind (RunsTo.runs (runsTo_readE _ b) _ os roots) ?_
  refine Runs.bind (RunsTo.runs (runsTo_sampleE _) _ os roots) ?_
  refine Runs.bind (hlc _ os roots) ?_
  refine Runs.bind (runs_readN _ s _ os roots (by rw [hs]; rfl)) ?_
  refine Runs.bind (hmv _) ?_
  rw [require_pos (by simpa [blake2sConstantColumn, kBits] using hterm)]
  exact Runs.ret _ _

end
end LeanVM.Guest.B1
