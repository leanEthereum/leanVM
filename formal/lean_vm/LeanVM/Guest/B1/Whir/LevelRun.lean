/-
  LeanVM.Guest.B1.Whir.LevelRun

  The Spec's run of a non-final level after its folds (`levelNext`), from the words, the grinds'
  passing nonces and the openings the guest's blocks name.
-/

module

public import LeanVM.Guest.B1.Whir.LevelSpec
public import LeanVM.Guest.B1.Whir.Run
public import LeanVM.Guest.B1.Whir.Squeezes

/-!
# A non-final level's run (V: `whirLevels`, the `next :: _` arm)

`levelNext_run`: from a sponge with nothing waiting, the next root's two cells `x0, x1` and the
high part read and absorbed (the commitment appended), the two out-of-domain points squeezed, their
values and the query nonce read, the query grind passing, the positions sampled from its challenge
(`sampleQueries_runG`), the batching nonce read, its grind passing and `λ` drawn, and one phase of
openings at the positions passing `openOne`: `levelNext` returns the glued state.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The out-of-domain points of a non-final level, `mu` coordinates each, from the sponge `F`. -/
theorem sampleOodPoints_two (mu : ℕ) (F : Fs) :
    RunsTo (sampleOodPoints mu 2) F [] [(F.squeezeN mu).1, ((F.squeezeN mu).2.squeezeN mu).1]
      ((F.squeezeN mu).2.squeezeN mu).2 := by
  have h := (runsTo_sampleN mu F).bind (f := fun p ↦ do
      let points ← sampleOodPoints mu 1
      return p :: points)
    (((runsTo_sampleN mu (F.squeezeN mu).2).bind (f := fun p ↦ do
        let points ← sampleOodPoints mu 0
        return p :: points)
      ((runsTo_ret [] _).bind (f := fun points ↦
        (pure (((F.squeezeN mu).2.squeezeN mu).1 :: points) : VerifierProgram (List (List E))))
        (runsTo_ret _ _))).bind (f := fun points ↦
          (pure ((F.squeezeN mu).1 :: points) : VerifierProgram (List (List E)))) (runsTo_ret _ _))
  exact h

/-! ## Runs between any sponges -/

/-- From any Spec sponge with `P`, the program `p` reads exactly the words `xs` and the phases
`os`, the commitments growing from `roots` to `roots'`, and returns `a`, leaving a sponge with
`Q`: `RunsWith`, `RunsTo`, `RunsToG`, `RunsFromG` with their sponges' predicates. -/
def RunsW {α : Type} (P : Sponge → Prop) (p : VerifierProgram α) (xs : List E)
    (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)) (a : α) (Q : Sponge → Prop)
    (roots' : List (Digest × ℕ × ℕ)) : Prop :=
  ∀ sp, P sp → ∀ (rest : List E) (orest : List (List Opening)),
    ∃ sp', Q sp' ∧ runId p ⟨sp, xs ++ rest, os ++ orest, roots⟩ = some (a, ⟨sp', rest, orest, roots'⟩)

theorem RunsW.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    {P Q T : Sponge → Prop} {xs ys : List E} {os1 os2 : List (List Opening)}
    {r0 r1 r2 : List (Digest × ℕ × ℕ)} {a : α} {b : β}
    (h1 : RunsW P p xs os1 r0 a Q r1) (h2 : RunsW Q (f a) ys os2 r1 b T r2) :
    RunsW P (p >>= f) (xs ++ ys) (os1 ++ os2) r0 b T r2 := by
  intro sp hs rest orest
  obtain ⟨sp1, hs1, e1⟩ := h1 sp hs (ys ++ rest) (os2 ++ orest)
  obtain ⟨sp2, hs2, e2⟩ := h2 sp1 hs1 rest orest
  refine ⟨sp2, hs2, ?_⟩
  rw [prog_bind_eq, run_bind, List.append_assoc, List.append_assoc, e1]
  exact e2

theorem RunsW.of_eq {α : Type} {P Q : Sponge → Prop} {p : VerifierProgram α} {xs xs' : List E}
    {os os' : List (List Opening)} {r r' q q' : List (Digest × ℕ × ℕ)} {a a' : α}
    (h : RunsW P p xs os r a Q q) (hx : xs = xs') (ho : os = os') (hr : r = r') (ha : a = a')
    (hq : q = q') : RunsW P p xs' os' r' a' Q q' := by
  subst hx ho hr ha hq; exact h

theorem RunsTo.toW {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') (roots : List (Digest × ℕ × ℕ)) :
    RunsW s.Carries p xs [] roots a s'.Carries roots :=
  fun sp hs rest orest ↦ h sp hs rest ([] ++ orest) roots

theorem RunsToG.toW {α : Type} {p : VerifierProgram α} {s : Fs} {xs : List E} {a : α}
    {cap : List E} {c : E} (h : RunsToG p s xs a cap c) (roots : List (Digest × ℕ × ℕ)) :
    RunsW s.Carries p xs [] roots a (Fs.CarriesGround cap c) roots :=
  fun sp hs rest orest ↦ h sp hs rest ([] ++ orest) roots

theorem RunsFromG.toW {α : Type} {p : VerifierProgram α} {cap : List E} {c : E} {xs : List E}
    {a : α} {s' : Fs} (h : RunsFromG p cap c xs a s') (roots : List (Digest × ℕ × ℕ)) :
    RunsW (Fs.CarriesGround cap c) p xs [] roots a s'.Carries roots :=
  fun sp hs rest orest ↦ h sp hs rest ([] ++ orest) roots

theorem RunsWith.toW {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E}
    {os : List (List Opening)} {r r' : List (Digest × ℕ × ℕ)} {a : α}
    (h : RunsWith p s xs os r a s' r') : RunsW s.Carries p xs os r a s'.Carries r' := h

theorem RunsW.toWith {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E}
    {os : List (List Opening)} {r r' : List (Digest × ℕ × ℕ)} {a : α}
    (h : RunsW s.Carries p xs os r a s'.Carries r') : RunsWith p s xs os r a s' r' := h

/-! ## The level -/

/-- **A non-final level after its folds runs** (`levelNext`): the words `x0, x1` (the next root's
cells), the high part, `y0, y1` (the out-of-domain values), the query nonce `nn` and the batching
nonce `n2`; the two grinds passing; one phase of openings at the positions, each passing `openOne`
against commitment `index`'s root. It returns the glued state. -/
theorem levelNext_run (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) (F : Fs) (R : List (Digest × ℕ × ℕ)) {root : Digest}
    {height width : ℕ} (hi : R[index]? = some (root, height, width))
    (x0 x1 : E) (high : List E) (hhl : high.length = level.fold) (y0 y1 nn n2 : E)
    (hb1 : Whir.queryGrindingBits ≠ 0) (hb2 : Whir.batchGrindingBits ≠ 0)
    (hP : 1 ≤ 128 / (logN - s.gammas.length + level.logInvRate)) (hQ : 0 < level.queries)
    (hok1 : powOk Whir.queryGrindingBits (Keccak.lane
      (((((F.absorbAll (x0 :: x1 :: high) dsObserve).squeezeN (logN - s.gammas.length)).2.squeezeN
        (logN - s.gammas.length)).2.absorbAll [y0, y1] dsObserve).nonceState nn) 2) = true)
    (qs : List ℕ) (hqs : qs = sqPositions (logN - s.gammas.length + level.logInvRate)
      (sqSample (challengeOf (((((F.absorbAll (x0 :: x1 :: high) dsObserve).squeezeN
        (logN - s.gammas.length)).2.squeezeN (logN - s.gammas.length)).2.absorbAll [y0, y1]
          dsObserve).nonceState nn))
        (capOf (((((F.absorbAll (x0 :: x1 :: high) dsObserve).squeezeN
        (logN - s.gammas.length)).2.squeezeN (logN - s.gammas.length)).2.absorbAll [y0, y1]
          dsObserve).nonceState nn))) level.queries)
    (F3 : Fs) (hF3 : F3 = ((⟨capOf (((((F.absorbAll (x0 :: x1 :: high) dsObserve).squeezeN
        (logN - s.gammas.length)).2.squeezeN (logN - s.gammas.length)).2.absorbAll [y0, y1]
          dsObserve).nonceState nn), []⟩ : Fs).squeezeN
        (sqCount (128 / (logN - s.gammas.length + level.logInvRate)) level.queries - 1)).2)
    (hok2 : powOk Whir.batchGrindingBits (Keccak.lane (F3.nonceState n2) 2) = true)
    (os : List Opening) (hl : os.length = qs.length)
    (hopen : ∀ k (hk : k < qs.length) (ho : k < os.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width qs[k] os[k]) = true)
    (hidx : os.map Opening.leafIndex = qs) :
    RunsWith (levelNext logN index level next s rounds) F
      (x0 :: x1 :: high ++ [y0, y1, nn, n2]) [os] R
      (glueLevel s (challengeOf (F3.nonceState n2)) (logN - s.gammas.length)
        [((F.absorbAll (x0 :: x1 :: high) dsObserve).squeezeN (logN - s.gammas.length)).1,
          (((F.absorbAll (x0 :: x1 :: high) dsObserve).squeezeN (logN - s.gammas.length)).2.squeezeN
            (logN - s.gammas.length)).1] [y0, y1] qs
        (powers (challengeOf (F3.nonceState n2)) qs.length)
        (levelBatched (logN - s.gammas.length) index rounds high qs (os.map (·.leaf))
          (challengeOf (F3.nonceState n2))))
      ⟨capOf (F3.nonceState n2), []⟩
      (R ++ [(digestFromHalves (x0, x1), levelShape (logN - s.gammas.length) next
        (2 * 2 ^ next.fold))]) := by
  set mu := logN - s.gammas.length with hmu
  set R' := R ++ [(digestFromHalves (x0, x1), levelShape mu next (2 * 2 ^ next.fold))] with hR'
  have hi' : R'[index]? = some (root, height, width) := by
    rw [hR', List.getElem?_append_left (List.getElem?_eq_some_iff.mp hi).1]; exact hi
  have h1 := RunsWith.toW (runsWith_commitP F x0 x1 (levelShape mu next (2 * 2 ^ next.fold)).1
    (levelShape mu next (2 * 2 ^ next.fold)).2 R)
  have h2 := RunsTo.toW (runsTo_readN ((F.absorb x0 dsObserve).absorb x1 dsObserve) high) R'
  rw [hhl] at h2
  set F1 := F.absorbAll (x0 :: x1 :: high) dsObserve with hF1
  have hF1' : ((F.absorb x0 dsObserve).absorb x1 dsObserve).absorbAll high dsObserve = F1 := rfl
  rw [hF1'] at h2
  have h3 := RunsTo.toW (sampleOodPoints_two mu F1) R'
  have h4 := RunsTo.toW (runsTo_readN ((F1.squeezeN mu).2.squeezeN mu).2 [y0, y1]) R'
  have h5 := RunsToG.toW (runsToG_grind hb1 _ nn hok1) R'
  set S := ((((F1.squeezeN mu).2.squeezeN mu).2.absorbAll [y0, y1] dsObserve).nonceState nn) with hS
  have h6 : RunsW (Fs.CarriesGround (capOf S) (challengeOf S))
      (sampleQueries (mu + level.logInvRate) level.queries) [] [] R' qs F3.Carries R' := by
    rw [hqs, hF3]
    exact RunsFromG.toW (sampleQueries_runG (mu + level.logInvRate) level.queries hP hQ
      (capOf S) (challengeOf S)) R'
  have h7 := RunsToG.toW (runsToG_grind hb2 F3 n2 hok2) R'
  have h8 := RunsFromG.toW (runsFromG_sample (capOf (F3.nonceState n2))
    (challengeOf (F3.nonceState n2))) R'
  have h9 := RunsWith.toW (runsWith_queryP ⟨capOf (F3.nonceState n2), []⟩ R' hi' qs os hl hopen hidx)
  have h10 := RunsWith.toW (runsWith_ret (glueLevel s (challengeOf (F3.nonceState n2)) mu
    [(F1.squeezeN mu).1, ((F1.squeezeN mu).2.squeezeN mu).1] [y0, y1] qs
    (powers (challengeOf (F3.nonceState n2)) qs.length)
    (levelBatched mu index rounds high qs (os.map (·.leaf)) (challengeOf (F3.nonceState n2))))
    (⟨capOf (F3.nonceState n2), []⟩ : Fs) R')
  refine RunsW.toWith (RunsW.of_eq (h1.bind (h2.bind (h3.bind (h4.bind (h5.bind (h6.bind
    (h7.bind (h8.bind (h9.bind h10))))))))) ?_ ?_ rfl rfl rfl)
  · simp
  · simp

end
end LeanVM.Guest.B1.Whir
