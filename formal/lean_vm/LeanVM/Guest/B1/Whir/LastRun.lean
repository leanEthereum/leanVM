/-
  LeanVM.Guest.B1.Whir.LastRun

  The Spec's run of the final level after its folds (`levelLast`), from the words, the grind's
  passing nonce, the openings and the closing rounds' words.
-/

module

public import LeanVM.Guest.B1.Whir.LevelRun
public import LeanVM.Guest.B1.Whir.TailRun

/-!
# The final level's run (V: `whirLevels`, the `[]` arm)

`levelLast_run`: from a sponge with nothing waiting, the final lane `fold` read, the query nonce
read and its grind passing, the positions sampled from its challenge, one phase of openings at
the positions passing `openOne` and the final check, the closing rounds' words `pairs`:
`levelLast` returns the rotated point, the glued weight, the lane's low part at the tail
challenges and the closing claim (`tailRun`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem runsWith_require {c : Prop} [Decidable c] (hc : c) (s : Fs)
    (roots : List (Digest × ℕ × ℕ)) :
    RunsWith (VerifierProgram.require c) s [] [] roots () s roots := by
  have h := runsWith_ret () s roots
  simpa [VerifierProgram.require, hc, VerifierProgram.pure_eq] using h

/-- The sponge after the squeezes of the positions, nothing waiting. -/
theorem squeezeN_mk (cap : List E) (n : ℕ) :
    (((⟨cap, []⟩ : Fs).squeezeN n).2 : Fs) = ⟨((⟨cap, []⟩ : Fs).squeezeN n).2.cap, []⟩ := by
  have h := squeezeN_pend (s := (⟨cap, []⟩ : Fs)) rfl n
  generalize ((⟨cap, []⟩ : Fs).squeezeN n).2 = t at h ⊢
  obtain ⟨c, p⟩ := t
  subst h
  rfl

/-- **The final level after its folds runs** (`levelLast`). -/
theorem levelLast_run (logN laneFolds index : ℕ) (level : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) (F : Fs) (R : List (Digest × ℕ × ℕ)) {root : Digest}
    {height width : ℕ} (hi : R[index]? = some (root, height, width))
    (fold : List E) (hfl : fold.length = 2 ^ (logN - s.alphas.length) + level.fold) (nn : E)
    (hb1 : Whir.queryGrindingBits ≠ 0)
    (hP : 1 ≤ 128 / (logN - s.alphas.length + level.logInvRate)) (hQ : 0 < level.queries)
    (hok1 : powOk Whir.queryGrindingBits
      (Keccak.lane ((F.absorbAll fold dsObserve).nonceState nn) 2) = true)
    (qs : List ℕ) (hqs : qs = sqPositions (logN - s.alphas.length + level.logInvRate)
      (sqSample (challengeOf ((F.absorbAll fold dsObserve).nonceState nn))
        (capOf ((F.absorbAll fold dsObserve).nonceState nn))) level.queries)
    (F3 : Fs) (hF3 : F3 = ((⟨capOf ((F.absorbAll fold dsObserve).nonceState nn), []⟩ : Fs).squeezeN
        (sqCount (128 / (logN - s.alphas.length + level.logInvRate)) level.queries - 1)).2)
    (os : List Opening) (hl : os.length = qs.length)
    (hopen : ∀ k (hk : k < qs.length) (ho : k < os.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width qs[k] os[k]) = true)
    (hidx : os.map Opening.leafIndex = qs)
    (hreq : ∀ k (hk : k < qs.length) (ho : k < os.length),
      foldRow (specLanes index os[k].leaf) (K.ofBits qs[k]) rounds =
        novelEval fold (subspaceAt (logN - s.alphas.length) (K.ofBits qs[k])))
    (pairs : List (E × E)) (hpl : pairs.length = logN - s.alphas.length) :
    RunsWith (levelLast logN laneFolds index level s rounds) F (fold ++ [nn] ++ tailWords pairs) [os] R
      ⟨(s.alphas ++ (tailRun pairs F3.cap s.claim).1).drop laneFolds ++
          (s.alphas ++ (tailRun pairs F3.cap s.claim).1).take laneFolds,
        s.glued.foldl (fun weight glued ↦ weight + glued.scalar *
          glued.weightAt ((s.alphas ++ (tailRun pairs F3.cap s.claim).1).drop glued.foldStart)) 0,
        multilinearEval (fold.take (2 ^ (logN - s.alphas.length))) (tailRun pairs F3.cap s.claim).1,
        (tailRun pairs F3.cap s.claim).2.1⟩
      ⟨(tailRun pairs F3.cap s.claim).2.2, []⟩ R := by
  set mu := logN - s.alphas.length with hmu
  have h1 := RunsTo.toW (runsTo_readN F fold) R
  rw [hfl] at h1
  have h2 := RunsToG.toW (runsToG_grind hb1 _ nn hok1) R
  set S := (F.absorbAll fold dsObserve).nonceState nn with hS
  have h3 : RunsW (Fs.CarriesGround (capOf S) (challengeOf S))
      (sampleQueries (mu + level.logInvRate) level.queries) [] [] R qs F3.Carries R := by
    rw [hqs, hF3]
    exact RunsFromG.toW (sampleQueries_runG (mu + level.logInvRate) level.queries hP hQ
      (capOf S) (challengeOf S)) R
  have h4 := RunsWith.toW (runsWith_queryP F3 R hi qs os hl hopen hidx)
  have hreq' : ((List.zip qs (os.map (·.leaf))).all fun (p : ℕ × List K) ↦
      decide (foldRow ((fun row ↦ if index = 0 then row.reverse.map ofK else extRow row) p.2)
        (K.ofBits p.1) rounds = novelEval fold (subspaceAt mu (K.ofBits p.1)))) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
    simp only [List.length_zip, List.length_map, hl, min_self] at hk
    simp only [List.getElem_zip, List.getElem_map, decide_eq_true_eq]
    exact hreq k hk (by omega)
  have h5 := RunsWith.toW (runsWith_require hreq' F3 R)
  have hF3' : F3 = ⟨F3.cap, []⟩ := by rw [hF3]; exact squeezeN_mk _ _
  have h6 := RunsTo.toW (sumcheck_tail_run pairs F3.cap s.claim) R
  rw [← hF3', hpl] at h6
  have h7 := RunsWith.toW (runsWith_ret (⟨(s.alphas ++ (tailRun pairs F3.cap s.claim).1).drop laneFolds ++
          (s.alphas ++ (tailRun pairs F3.cap s.claim).1).take laneFolds,
        s.glued.foldl (fun weight glued ↦ weight + glued.scalar *
          glued.weightAt ((s.alphas ++ (tailRun pairs F3.cap s.claim).1).drop glued.foldStart)) 0,
        multilinearEval (fold.take (2 ^ mu)) (tailRun pairs F3.cap s.claim).1,
        (tailRun pairs F3.cap s.claim).2.1⟩ : WhirEnd) (⟨(tailRun pairs F3.cap s.claim).2.2, []⟩ : Fs) R)
  unfold levelLast
  refine RunsW.toWith (RunsW.of_eq (h1.bind (h2.bind (h3.bind (h4.bind (h5.bind (h6.bind h7))))))
    ?_ ?_ rfl rfl rfl)
  · simp
  · simp

end
end LeanVM.Guest.B1.Whir
