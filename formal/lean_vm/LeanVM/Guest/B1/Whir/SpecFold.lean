/-
  LeanVM.Guest.B1.Whir.SpecFold

  The fold rounds, the tail rounds and the openings of an accepting run, read backwards.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.SpecNZ
public import LeanVM.Guest.B1.Whir.CFold
public import LeanVM.Protocol.WithHash

/-!
# Rounds and openings, backwards

* `openAll_inv`: openings that pass `openAll` are the first `|ps|` of the list, each passing
  `openOne`, their leaves the rows (the converse of `openAll_eq`).
* `foldsNZ_inv`: `foldRoundsNZ n` followed by `K`, accepting on the words `xs`: the first `2n`
  words are the rounds' (`foldsTr`), every challenge is nonzero, and `K` accepts on the state
  `foldsTr` leaves.
* `tailTr`, `tailNZ_inv`: the tail rounds, as a function of the sponge and the words, the same
  way: `2(n - 1)` words, every challenge nonzero.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Openings -/

/-- **Openings that pass `openAll`**: one per position, each passing `openOne`, the rows their
leaves, the rest left. -/
theorem openAll_inv (root : Digest) (height width : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening) (rows : List (List K)) (rest : List Opening),
      Id.run (Compile.openAllWithHash (m := Id) keccak256 root height width ps os) = some (rows, rest) →
      ∃ osL : List Opening, os = osL ++ rest ∧ osL.length = ps.length ∧
        (∀ k (hk : k < ps.length) (ho : k < osL.length),
          Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] osL[k]) = true) ∧
        rows = osL.map (·.leaf)
  | [], os, rows, rest, h => by
    simp only [Compile.openAllWithHash, Id.run, pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl, fun k hk ↦ absurd hk (by simp), rfl⟩
  | _ :: _, [], rows, rest, h => by simp [Compile.openAllWithHash, Id.run, pure] at h
  | q :: qs, o :: os, rows, rest, h => by
    simp only [Compile.openAllWithHash, Id.run, bind] at h
    split at h
    · rename_i hq
      cases ho : Id.run (Compile.openAllWithHash (m := Id) keccak256 root height width qs os) with
      | none =>
        simp only [Id.run] at ho
        simp [ho, pure] at h
      | some v =>
        obtain ⟨rows', rest'⟩ := v
        simp only [Id.run] at ho
        simp only [ho, Option.map_some, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨osL, e, hl, hok, hr⟩ := openAll_inv root height width qs os rows' rest' ho
        refine ⟨o :: osL, by rw [e]; rfl, by simp [hl], fun k hk ho' ↦ ?_, by rw [hr]; rfl⟩
        rcases k with _ | k
        · exact hq
        · exact hok k (by simpa using hk) (by simpa using ho')
    · simp [pure] at h

/-- **A phase that passes `openPhase`**: one opening per position, each passing `openOne`, the
rows their leaves. -/
theorem openPhase_inv {root : Digest} {height width : ℕ} {ps : List ℕ} {phase : List Opening}
    {rows : List (List K)}
    (h : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) =
      some rows) :
    phase.length = ps.length ∧
      (∀ k (hk : k < ps.length) (ho : k < phase.length),
        Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width ps[k] phase[k]) =
          true) ∧
      rows = phase.map (·.leaf) := by
  obtain ⟨-, -, ho⟩ := openPhase_some keccak256 h
  obtain ⟨osL, e, hl, hok, hr⟩ := openAll_inv root height width ps phase rows [] ho
  rw [List.append_nil] at e
  subst e
  exact ⟨hl, hok, hr⟩

/-! ## The fold rounds -/

theorem sumcheck3_bind {β : Type} (claim : E) (k : List E → VerifierProgram β) :
    (sumcheckRoundPoly 3 claim none).bind k =
      VerifierProgram.readScalar.bind fun d0 ↦ VerifierProgram.readScalar.bind fun d2 ↦ k [d0, claim
          + d2, d2] := by
  simp only [sumcheckRoundPoly, VerifierProgram.readScalars, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind, sumE_single]

/-- Two words read after a squeeze leave `foldStep`. -/
theorem squeeze_absorb_two (F : Fs) (d0 d2 : E) :
    (F.squeeze.2.absorb d0 dsObserve).absorb d2 dsObserve = foldStep F d0 d2 := by
  simp [Fs.absorb, Fs.squeeze, foldStep, rateScalars]

/-- **The fold rounds, backwards.** -/
theorem foldsNZ_inv {β : Type} {K : WhirStateT × List E → VerifierProgram β} :
    ∀ (n : ℕ) (ws : WhirStateT) (lf : List E) (F : Fs) (xs : List E) (os : List (List Opening))
      (R : List (Digest × ℕ × ℕ)) (r : β × FSt),
      runF ((foldRoundsNZ n ws lf).bind K) ⟨F, xs, os, R⟩ = some r →
        2 * n ≤ xs.length ∧ (∀ c ∈ (foldsTr n F ws.quad ws.target xs).2.1, c ≠ 0) ∧
        runF (K ({ ws with
            target := (foldsTr n F ws.quad ws.target xs).2.2.2
            quad := (foldsTr n F ws.quad ws.target xs).2.2.1
            folds := ws.folds ++ (foldsTr n F ws.quad ws.target xs).2.1 },
          lf ++ (foldsTr n F ws.quad ws.target xs).2.1))
          ⟨(foldsTr n F ws.quad ws.target xs).1, xs.drop (2 * n), os, R⟩ = some r
  | 0, ws, lf, F, xs, os, R, r, h => by
    refine ⟨Nat.zero_le _, fun c hc ↦ by simp [foldsTr] at hc, ?_⟩
    simp only [foldsTr, List.append_nil, Nat.mul_zero, List.drop_zero]
    simpa [foldRoundsNZ] using h
  | n + 1, ws, lf, F, xs, os, R, r, h => by
    have e : (foldRoundsNZ (n + 1) ws lf).bind K = VerifierProgram.sampleChallenge.bind fun c ↦
        (VerifierProgram.require (c ≠ 0)).bind fun _ ↦ VerifierProgram.readScalar.bind fun d0 ↦ VerifierProgram.readScalar.bind fun d2 ↦
          (foldRoundsNZ n { ws with
            target := polyEval ws.quad c
            quad := [d0, polyEval ws.quad c + d2, d2]
            folds := ws.folds ++ [c] } (lf ++ [c])).bind K := by
      simp only [foldRoundsNZ, VerifierProgram.bind_eq, VerifierProgram.bind_assoc, sumcheck3_bind]
    rw [e, runF_sampleE_bind] at h
    obtain ⟨hc, h⟩ := runF_require_bind h
    obtain ⟨d0, xs1, hx1, h1⟩ := runF_readE_bind h
    obtain ⟨d2, xs2, hx2, h2⟩ := runF_readE_bind h1
    subst hx1 hx2
    rw [squeeze_absorb_two] at h2
    obtain ⟨hl, hnz, h⟩ := foldsNZ_inv n _ _ _ xs2 os R r h2
    have hR : foldsTr (n + 1) F ws.quad ws.target (d0 :: d2 :: xs2) =
        ((foldsTr n (foldStep F d0 d2) [d0, polyEval ws.quad F.squeeze.1 + d2, d2]
          (polyEval ws.quad F.squeeze.1) xs2).1,
         F.squeeze.1 :: (foldsTr n (foldStep F d0 d2) [d0, polyEval ws.quad F.squeeze.1 + d2, d2]
          (polyEval ws.quad F.squeeze.1) xs2).2.1,
         (foldsTr n (foldStep F d0 d2) [d0, polyEval ws.quad F.squeeze.1 + d2, d2]
          (polyEval ws.quad F.squeeze.1) xs2).2.2.1,
         (foldsTr n (foldStep F d0 d2) [d0, polyEval ws.quad F.squeeze.1 + d2, d2]
          (polyEval ws.quad F.squeeze.1) xs2).2.2.2) := rfl
    rw [hR]
    refine ⟨by simp at hl ⊢; omega, ?_, ?_⟩
    · intro c' hc'
      simp only [List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact hc
      · exact hnz c' hc'
    · simp only [List.append_assoc, List.singleton_append, List.drop_succ_cons,
        show 2 * (n + 1) = 2 * n + 2 by ring] at h ⊢
      exact h

/-! ## The tail rounds -/

/-- **The tail rounds** from the sponge `F`, the quadratic `q` and the words `xs`: the last
round's sponge, the challenges and the final claim. -/
def tailTr : ℕ → Fs → List E → E → List E → Fs × List E × E
  | 0, F, _, t, _ => (F, [], t)
  | 1, F, q, _, _ => (F.squeeze.2, [F.squeeze.1], polyEval q F.squeeze.1)
  | n + 2, F, q, _, xs =>
    let c := F.squeeze.1
    let cl := polyEval q c
    let r := tailTr (n + 1) (foldStep F (xs.getD 0 0) (xs.getD 1 0))
      [xs.getD 0 0, cl + xs.getD 1 0, xs.getD 1 0] cl (xs.drop 2)
    (r.1, c :: r.2.1, r.2.2)

theorem tailTr_length : ∀ (n : ℕ) (F : Fs) (q : List E) (t : E) (xs : List E),
    (tailTr n F q t xs).2.1.length = n
  | 0, _, _, _, _ => rfl
  | 1, _, _, _, _ => rfl
  | n + 2, F, q, t, xs => by simp [tailTr, tailTr_length (n + 1)]

/-- **The tail rounds, backwards.** -/
theorem tailNZ_inv {β : Type} {K : List E × E → VerifierProgram β} :
    ∀ (n : ℕ) (t : E) (q : List E) (F : Fs) (xs : List E) (os : List (List Opening))
      (R : List (Digest × ℕ × ℕ)) (r : β × FSt),
      runF ((tailRoundsNZ n t q).bind K) ⟨F, xs, os, R⟩ = some r →
        2 * (n - 1) ≤ xs.length ∧ (∀ c ∈ (tailTr n F q t xs).2.1, c ≠ 0) ∧
        runF (K ((tailTr n F q t xs).2.1, (tailTr n F q t xs).2.2))
          ⟨(tailTr n F q t xs).1, xs.drop (2 * (n - 1)), os, R⟩ = some r
  | 0, t, q, F, xs, os, R, r, h => by
    refine ⟨by simp, fun c hc ↦ by simp [tailTr] at hc, ?_⟩
    simpa [tailRoundsNZ, tailTr] using h
  | 1, t, q, F, xs, os, R, r, h => by
    simp only [tailRoundsNZ, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind] at h
    rw [runF_sampleE_bind] at h
    obtain ⟨hc, h⟩ := runF_require_bind h
    refine ⟨by simp, fun c hc' ↦ ?_, by simpa [tailTr] using h⟩
    simp only [tailTr, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rw [hc']; exact hc
  | n + 2, t, q, F, xs, os, R, r, h => by
    rw [tailRoundsNZ] at h
    simp only [Nat.add_one_ne_zero, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind] at h
    rw [runF_sampleE_bind] at h
    obtain ⟨hc, h⟩ := runF_require_bind h
    rw [sumcheck3_bind] at h
    obtain ⟨d0, xs1, hx1, h1⟩ := runF_readE_bind h
    obtain ⟨d2, xs2, hx2, h2⟩ := runF_readE_bind h1
    subst hx1 hx2
    rw [squeeze_absorb_two] at h2
    obtain ⟨hl, hnz, h3⟩ := tailNZ_inv (n + 1) _ _ _ xs2 os R r h2
    refine ⟨by simp at hl ⊢; omega, ?_, ?_⟩
    · intro c' hc'
      simp only [tailTr, List.mem_cons] at hc'
      rcases hc' with rfl | hc'
      · exact hc
      · exact hnz c' hc'
    · simp only at h3
      simp only [tailTr, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons,
        List.drop_zero]
      rw [show n + 2 - 1 = (n + 1 - 1) + 1 by omega, show 2 * (n + 1 - 1 + 1) = 2 * (n + 1 - 1) + 2 by
        ring]
      exact h3

end
end LeanVM.Guest.B1.Whir
