/-
  LeanVM.Guest.B1.Whir.SpecQS

  The query steps of an accepting run, step by step: the primitive steps, the rounds.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.SpecFold
public import LeanVM.Protocol.WithHash

/-!
# Query steps, step by step

`queryStepsOf` follows `runF`: a step that queries nothing passes the query steps on to its
continuation (`qs_readE_bind` …), a query adds its positions zipped with the openings
(`qs_queryP_bind`); `readN`, `sampleN`, `sampleQueries`, the fold rounds and the tail rounds query
nothing (`qs_readN_bind`, …, `qs_folds`, `qs_tail`), on the runs `SpecPrim` and `SpecFold` read.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {β : Type}

theorem qs_readE_bind (k : E → VerifierProgram β) (F : Fs) (x : E) (xs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) :
    queryStepsOf (VerifierProgram.readScalar.bind k) ⟨F, x :: xs, os, R⟩ =
      queryStepsOf (k x) ⟨F.absorb x dsObserve, xs, os, R⟩ := rfl

theorem qs_sampleE_bind (k : E → VerifierProgram β) (F : Fs) (xs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) :
    queryStepsOf (VerifierProgram.sampleChallenge.bind k) ⟨F, xs, os, R⟩ =
      queryStepsOf (k F.squeeze.1) ⟨F.squeeze.2, xs, os, R⟩ := rfl

theorem qs_grindP_bind {bits : ℕ} (k : Unit → VerifierProgram β) (F : Fs) (n : E) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ))
    (hp : powOk bits n (F.absorb n dsPowNonce).squeeze.1 = true) :
    queryStepsOf ((VerifierProgram.grindProofOfWork bits).bind k) ⟨F, n :: xs, os, R⟩ =
      queryStepsOf (k ()) ⟨(F.absorb n dsPowNonce).squeeze.2, xs, os, R⟩ := by
  simp only [VerifierProgram.grindProofOfWork, VerifierProgram.bind, queryStepsOf, hp, ↓reduceIte]

theorem qs_commitP_bind {hh ww : ℕ} (k : Unit → VerifierProgram β) (F : Fs) (x0 x1 : E) (xs :
    List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) {d : Digest}
    (hd : digestFromHalves (x0, x1) = some d) :
    queryStepsOf ((VerifierProgram.readCommitment hh ww).bind k) ⟨F, x0 :: x1 :: xs, os, R⟩ =
      queryStepsOf (k ()) ⟨(F.absorb x0 dsObserve).absorb x1 dsObserve, xs, os,
        R ++ [(d, hh, ww)]⟩ := by
  simp only [VerifierProgram.readCommitment, VerifierProgram.bind, queryStepsOf, hd]

theorem qs_require_bind {c : Prop} [Decidable c] (k : Unit → VerifierProgram β) (st : FSt)
    (hc : c) :
    queryStepsOf ((VerifierProgram.require c).bind k) st = queryStepsOf (k ()) st := by
  simp only [VerifierProgram.require, hc, ↓reduceIte, VerifierProgram.ret_bind]

theorem qs_queryP_bind {i : ℕ} {ps : List ℕ} (k : List (List K) → VerifierProgram β) (F : Fs)
    (xs : List E) (phase : List Opening) (rest : List (List Opening)) (R : List (Digest × ℕ × ℕ))
    {root : Digest} {height width : ℕ} {rows : List (List K)}
    (hR : R[i]? = some (root, height, width))
    (ho : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) =
      some rows) :
    queryStepsOf ((VerifierProgram.queryOpenings i ps).bind k) ⟨F, xs, phase :: rest, R⟩ =
      (height, ps.zip phase) :: queryStepsOf (k rows) ⟨F, xs, rest, R⟩ := by
  simp only [Id.run] at ho
  simp only [VerifierProgram.queryOpenings, VerifierProgram.bind, queryStepsOf, hR, ho, Id.run]

theorem qs_readN_bind : ∀ (n : ℕ) (k : List E → VerifierProgram β) (F : Fs) (xs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)), n ≤ xs.length →
    queryStepsOf ((VerifierProgram.readScalars n).bind k) ⟨F, xs, os, R⟩ =
      queryStepsOf (k (xs.take n)) ⟨F.absorbAll (xs.take n) dsObserve, xs.drop n, os, R⟩
  | 0, k, F, xs, os, R, _ => by simp [VerifierProgram.readScalars, Fs.absorbAll]
  | n + 1, k, F, x :: xs, os, R, hl => by
    have e : (VerifierProgram.readScalars (n + 1)).bind k =
        VerifierProgram.readScalar.bind fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦ k (x
            :: xs) := by
      simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
          VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [e, qs_readE_bind, qs_readN_bind n _ _ _ _ _ (by simp at hl; omega)]
    simp [Fs.absorbAll, List.take_succ_cons, List.drop_succ_cons]
  | n + 1, k, F, [], os, R, hl => by simp at hl

theorem qs_sampleN_bind : ∀ (n : ℕ) (k : List E → VerifierProgram β) (F : Fs) (xs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)),
    queryStepsOf ((VerifierProgram.sampleChallenges n).bind k) ⟨F, xs, os, R⟩ =
      queryStepsOf (k (F.squeezeN n).1) ⟨(F.squeezeN n).2, xs, os, R⟩
  | 0, k, F, xs, os, R => by simp [VerifierProgram.sampleChallenges, Fs.squeezeN]
  | n + 1, k, F, xs, os, R => by
    have e : (VerifierProgram.sampleChallenges (n + 1)).bind k =
        VerifierProgram.sampleChallenge.bind fun x ↦ (VerifierProgram.sampleChallenges n).bind
            fun xs ↦ k (x :: xs) := by
      simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
          VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [e, qs_sampleE_bind, qs_sampleN_bind n]
    rfl

theorem qs_sampleQueriesAux_bind (d : ℕ) (hd : 1 ≤ 192 / d) :
    ∀ (fuel rem : ℕ) (k : List ℕ → VerifierProgram β) (F : Fs) (xs : List E) (os : List (List Opening))
      (R : List (Digest × ℕ × ℕ)), ceilDiv rem (192 / d) ≤ fuel →
      queryStepsOf ((sampleQueriesAux d fuel rem).bind k) ⟨F, xs, os, R⟩ =
        queryStepsOf (k (queriesOf (192 / d) d (F.squeezeN (ceilDiv rem (192 / d))).1 rem))
          ⟨(F.squeezeN (ceilDiv rem (192 / d))).2, xs, os, R⟩
  | fuel, 0, k, F, xs, os, R, _ => by
    rw [ceilDiv_zero]
    rcases fuel with _ | fuel <;> simp [sampleQueriesAux, queriesOf, Fs.squeezeN]
  | 0, rem + 1, k, F, xs, os, R, h => by
    have := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem); omega
  | fuel + 1, rem + 1, k, F, xs, os, R, h => by
    have hs := ceilDiv_step (a := rem + 1) hd (Nat.succ_pos rem)
    have hp : (sampleQueriesAux d (fuel + 1) (rem + 1)).bind k =
        VerifierProgram.sampleChallenge.bind fun w ↦
        (sampleQueriesAux d fuel (rem + 1 - min (192 / d) (rem + 1))).bind fun rest ↦
          k (((List.range (min (192 / d) (rem + 1))).map fun c ↦
            (eToNat w >>> (c * d)) % 2 ^ d) ++ rest) := by
      simp only [sampleQueriesAux, Nat.add_one_ne_zero, ↓reduceIte, VerifierProgram.bind_eq,
          VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc, VerifierProgram.ret_bind]
    rw [hp, qs_sampleE_bind, qs_sampleQueriesAux_bind d hd fuel _ _ _ _ _ _ (by omega), hs,
      queriesOf_cons _ _ hd]
    rfl

theorem qs_sampleQueries_bind {d q : ℕ} (hd : 1 ≤ 192 / d) (k : List ℕ → VerifierProgram β) (F : Fs)
    (xs : List E) (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    queryStepsOf ((sampleQueries d q).bind k) ⟨F, xs, os, R⟩ =
      queryStepsOf (k (queriesOf (192 / d) d (F.squeezeN (ceilDiv q (192 / d))).1 q))
        ⟨(F.squeezeN (ceilDiv q (192 / d))).2, xs, os, R⟩ :=
  qs_sampleQueriesAux_bind d hd q q k F xs os R (ceilDiv_le_self hd)

/-- **The fold rounds query nothing.** -/
theorem qs_folds {b : ℕ} {K : WhirStateT × List E → VerifierProgram β} :
    ∀ (n : ℕ) (ws : WhirStateT) (lf : List E) (F : Fs) (xs : List E) (os : List (List Opening))
      (R : List (Digest × ℕ × ℕ)), roundLen b * n ≤ xs.length →
      (∀ c ∈ (foldsTr b n F ws.quad ws.target xs).2.1, c ≠ 0) →
      FoldsPow b n F ws.quad ws.target xs →
      queryStepsOf ((foldRoundsNZ b n ws lf).bind K) ⟨F, xs, os, R⟩ =
        queryStepsOf (K ({ ws with
            target := (foldsTr b n F ws.quad ws.target xs).2.2.2
            quad := (foldsTr b n F ws.quad ws.target xs).2.2.1
            folds := ws.folds ++ (foldsTr b n F ws.quad ws.target xs).2.1 },
          lf ++ (foldsTr b n F ws.quad ws.target xs).2.1))
          ⟨(foldsTr b n F ws.quad ws.target xs).1, xs.drop (roundLen b * n), os, R⟩
  | 0, ws, lf, F, xs, os, R, _, _, _ => by
    simp only [foldsTr, List.append_nil, Nat.mul_zero, List.drop_zero]
    simp [foldRoundsNZ]
  | n + 1, ws, lf, F, xs, os, R, hl, hnz, hpw => by
    obtain ⟨hp0, hpw'⟩ := hpw
    have e : (foldRoundsNZ b (n + 1) ws lf).bind K =
        (VerifierProgram.foldProofOfWork b).bind fun _ ↦ VerifierProgram.sampleChallenge.bind fun c ↦
        (VerifierProgram.require (c ≠ 0)).bind fun _ ↦ VerifierProgram.readScalar.bind fun d0 ↦
          VerifierProgram.readScalar.bind fun d2 ↦
          (foldRoundsNZ b n { ws with
            target := polyEval ws.quad c
            quad := [d0, polyEval ws.quad c + d2, d2]
            folds := ws.folds ++ [c] } (lf ++ [c])).bind K := by
      simp only [foldRoundsNZ, VerifierProgram.bind_eq, VerifierProgram.bind_assoc]
      congr 1; funext u; congr 1; funext c; congr 1; funext u
      rw [sumcheck3_bind]
    set G := powSponge b F (nonceOf b xs) with hG
    obtain ⟨ys, hys, hstep⟩ : ∃ ys, xs = powWords b (nonceOf b xs) ++ ys ∧
        queryStepsOf ((foldRoundsNZ b (n + 1) ws lf).bind K) ⟨F, xs, os, R⟩ =
        queryStepsOf ((VerifierProgram.sampleChallenge.bind fun c ↦
          (VerifierProgram.require (c ≠ 0)).bind fun _ ↦ VerifierProgram.readScalar.bind fun d0 ↦
            VerifierProgram.readScalar.bind fun d2 ↦
            (foldRoundsNZ b n { ws with
              target := polyEval ws.quad c
              quad := [d0, polyEval ws.quad c + d2, d2]
              folds := ws.folds ++ [c] } (lf ++ [c])).bind K)) ⟨G, ys, os, R⟩ := by
      rw [e]
      by_cases hb : b = 0
      · subst hb
        exact ⟨xs, by simp [powWords], by simp [VerifierProgram.foldProofOfWork, hG, powSponge]⟩
      · have hl1 : 1 ≤ xs.length := by
          have : roundLen b = 3 := by simp [roundLen, hb]
          rw [this] at hl; nlinarith
        obtain ⟨n0, xs', rfl⟩ : ∃ n0 xs', xs = n0 :: xs' := by
          match xs, hl1 with
          | n0 :: xs', _ => exact ⟨n0, xs', rfl⟩
        refine ⟨xs', by simp [powWords, nonceOf, hb], ?_⟩
        simp only [VerifierProgram.foldProofOfWork, hb, ↓reduceIte]
        rw [qs_grindP_bind _ _ _ _ _ _ (by simpa [nonceOf, hb] using hp0 hb)]
        simp [hG, powSponge, nonceOf, hb]
    have hlen : (powWords b (nonceOf b xs)).length = powOff b := by
      unfold powWords powOff; split_ifs <;> rfl
    have hl' : 2 ≤ ys.length := by
      have : xs.length = powOff b + ys.length := by rw [hys]; simp [hlen]
      have := roundLen_eq b; rw [Nat.mul_succ] at hl; omega
    rcases ys with _ | ⟨d0, _ | ⟨d2, xs2⟩⟩
    · simp at hl'
    · simp at hl'
    have gen : ∀ (P : List E) (m : ℕ), P.length = m →
        (P ++ d0 :: d2 :: xs2).getD m 0 = d0 ∧ (P ++ d0 :: d2 :: xs2).getD (m + 1) 0 = d2 ∧
          (P ++ d0 :: d2 :: xs2).drop (m + 2) = xs2 ∧
          (P ++ d0 :: d2 :: xs2).length = m + 2 + xs2.length := by
      intro P m hm; subst hm
      refine ⟨by simp, by simp, by simp, by simp; omega⟩
    obtain ⟨hd0, hd2, hdr, hxl⟩ := gen _ _ hlen
    rw [← hys] at hd0 hd2 hdr hxl
    rw [← roundLen_eq] at hdr
    have hc : G.squeeze.1 ≠ 0 := hnz _ (by simp [foldsTr, hG])
    rw [hstep, qs_sampleE_bind, qs_require_bind _ _ hc, qs_readE_bind, qs_readE_bind,
      squeeze_absorb_two]
    have hR : foldsTr b (n + 1) F ws.quad ws.target xs =
        ((foldsTr b n (foldStep G d0 d2) [d0, polyEval ws.quad G.squeeze.1 + d2, d2]
          (polyEval ws.quad G.squeeze.1) xs2).1,
         G.squeeze.1 :: (foldsTr b n (foldStep G d0 d2) [d0, polyEval ws.quad G.squeeze.1 + d2, d2]
          (polyEval ws.quad G.squeeze.1) xs2).2.1,
         (foldsTr b n (foldStep G d0 d2) [d0, polyEval ws.quad G.squeeze.1 + d2, d2]
          (polyEval ws.quad G.squeeze.1) xs2).2.2.1,
         (foldsTr b n (foldStep G d0 d2) [d0, polyEval ws.quad G.squeeze.1 + d2, d2]
          (polyEval ws.quad G.squeeze.1) xs2).2.2.2) := by
      simp only [foldsTr, hd0, hd2, hdr, hG]
    have hpw2 : FoldsPow b n (foldStep G d0 d2) [d0, polyEval ws.quad G.squeeze.1 + d2, d2]
        (polyEval ws.quad G.squeeze.1) xs2 := by
      simp only [hd0, hd2, hdr] at hpw'; exact hpw'
    rw [qs_folds n _ _ _ xs2 os R (by have := roundLen_eq b; rw [hxl, Nat.mul_succ] at hl; omega)
      (fun c' hc' ↦ hnz c' (by rw [hR]; exact List.mem_cons_of_mem _ hc')) hpw2, hR]
    have hdrop : xs.drop (roundLen b * (n + 1)) = xs2.drop (roundLen b * n) := by
      rw [Nat.mul_succ, Nat.add_comm, ← List.drop_drop, hdr]
    simp only [List.append_assoc, List.singleton_append, hdrop]

/-- **The tail rounds query nothing.** -/
theorem qs_tail {K : List E × E → VerifierProgram β} :
    ∀ (n : ℕ) (t : E) (q : List E) (F : Fs) (xs : List E) (os : List (List Opening))
      (R : List (Digest × ℕ × ℕ)), 2 * (n - 1) ≤ xs.length →
      (∀ c ∈ (tailTr n F q t xs).2.1, c ≠ 0) →
      queryStepsOf ((tailRoundsNZ n t q).bind K) ⟨F, xs, os, R⟩ =
        queryStepsOf (K ((tailTr n F q t xs).2.1, (tailTr n F q t xs).2.2))
          ⟨(tailTr n F q t xs).1, xs.drop (2 * (n - 1)), os, R⟩
  | 0, t, q, F, xs, os, R, _, _ => by simp [tailRoundsNZ, tailTr]
  | 1, t, q, F, xs, os, R, _, hnz => by
    have hc : F.squeeze.1 ≠ 0 := hnz _ (by simp [tailTr])
    simp only [tailRoundsNZ, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
    rw [qs_sampleE_bind, qs_require_bind _ _ hc]
    simp [tailTr]
  | n + 2, t, q, F, d0 :: d2 :: xs, os, R, hl, hnz => by
    have hc : F.squeeze.1 ≠ 0 := hnz _ (by simp [tailTr])
    rw [tailRoundsNZ]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
    rw [qs_sampleE_bind, qs_require_bind _ _ hc, sumcheck3_bind, qs_readE_bind, qs_readE_bind,
      squeeze_absorb_two, qs_tail (n + 1) _ _ _ xs os R (by simp at hl ⊢; omega) (fun c' hc' ↦
        hnz c' (by simp only [tailTr, List.mem_cons]; exact Or.inr hc'))]
    simp only [tailTr, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
      List.drop_zero]
    rw [show n + 2 - 1 = (n + 1 - 1) + 1 by omega, show 2 * (n + 1 - 1 + 1) = 2 * (n + 1 - 1) + 2 by
      ring]
    rfl
  | n + 2, _, _, _, [], _, _, hl, _ => by simp at hl
  | n + 2, _, _, _, [_], _, _, hl, _ => by simp at hl; omega

end
end LeanVM.Guest.B1.Whir
