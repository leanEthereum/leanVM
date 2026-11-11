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
high part read and absorbed (the commitment appended), the OOD nonce read and its grind passing,
the OOD point drawn from its challenge (`oodPt`), its value and the query nonce read, the query
grind passing, the positions sampled from its challenge (`sampleQueries_runG`), `λ` the next
squeeze, and one phase of openings at the positions passing `openOne`: `levelNext` returns the
glued state.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

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

theorem levelOodGrind_eq : levelOodGrind = Whir.levelOodGrindingBits := rfl

/-- The OOD point, from the OOD grind's ground challenge. -/
theorem oodPt_eq (F : Fs) (xs : List E) (n1 : E) (mu : ℕ) :
    oodPt F xs n1 mu =
      (challengeOf ((F.absorbAll xs dsObserve).nonceState n1) ::
          ((⟨capOf ((F.absorbAll xs dsObserve).nonceState n1), []⟩ : Fs).squeezeN (mu - 1)).1,
        ((⟨capOf ((F.absorbAll xs dsObserve).nonceState n1), []⟩ : Fs).squeezeN (mu - 1)).2) := by
  simp only [oodPt, oodG, Fs.grindSqueeze_pos _ (show levelOodGrind ≠ 0 by decide)]

/-- `n + 1` challenges from a ground challenge `c`: `c`, then `n` squeezes. -/
theorem runsFromG_sampleN (n : ℕ) (cap : List E) (c : E) :
    RunsFromG (VerifierProgram.sampleChallenges (n + 1)) cap c [] (c :: ((⟨cap, []⟩ : Fs).squeezeN n).1)
      ((⟨cap, []⟩ : Fs).squeezeN n).2 :=
  (runsFromG_sample cap c).bind (f := fun x ↦ do
      let xs ← VerifierProgram.sampleChallenges n
      return x :: xs)
    ((runsTo_sampleN n _).bind (f := fun xs ↦ (pure (c :: xs) : VerifierProgram (List E)))
      (runsTo_ret _ _))

/-- **A non-final level after its folds runs** (`levelNext`): the words `x0, x1` (the next root's
cells), the high part, the OOD nonce `n1`, the OOD value `y0` and the query nonce `nn`; the two
grinds passing; the positions sampled from the query grind's challenge and `λ` the next squeeze;
one phase of openings at the positions, each passing `openOne` against commitment `index`'s root.
It returns the glued state. -/
theorem levelNext_run (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) (F : Fs) (R : List (Digest × ℕ × ℕ)) {root : Digest}
    {height width : ℕ} (hi : R[index]? = some (root, height, width))
    (x0 x1 : E) (high : List E) (hhl : high.length = level.fold) (n1 y0 nn : E)
    (hmu : 1 ≤ logN - s.alphas.length)
    (hP : 1 ≤ 128 / (logN - s.alphas.length + level.logInvRate)) (hQ : 0 < level.queries)
    (hok0 : (F.absorbAll (x0 :: x1 :: high) dsObserve).GrindOk levelOodGrind n1)
    (hok1 : powOk Whir.queryGrindingBits
      (Keccak.lane (oodQ F (x0 :: x1 :: high) n1 (logN - s.alphas.length) y0 nn) 2) = true)
    (qs : List ℕ) (hqs : qs = sqPositions (logN - s.alphas.length + level.logInvRate)
      (sqSample (challengeOf (oodQ F (x0 :: x1 :: high) n1 (logN - s.alphas.length) y0 nn))
        (capOf (oodQ F (x0 :: x1 :: high) n1 (logN - s.alphas.length) y0 nn))) level.queries)
    (F3 : Fs) (hF3 : F3 = ((⟨capOf (oodQ F (x0 :: x1 :: high) n1 (logN - s.alphas.length) y0 nn),
        []⟩ : Fs).squeezeN (sqCount (128 / (logN - s.alphas.length + level.logInvRate))
          level.queries - 1)).2)
    (os : List Opening) (hl : os.length = qs.length)
    (hopen : ∀ k (hk : k < qs.length) (ho : k < os.length),
      Id.run (Compile.openOneWithHash (m := Id) keccak256 root height width qs[k] os[k]) = true)
    (hidx : os.map Opening.leafIndex = qs) :
    RunsWith (levelNext logN index level next s rounds) F
      (x0 :: x1 :: high ++ [n1, y0, nn]) [os] R
      (glueLevel s F3.squeeze.1 (logN - s.alphas.length)
        (oodPt F (x0 :: x1 :: high) n1 (logN - s.alphas.length)).1 y0 qs
        (powers F3.squeeze.1 qs.length)
        (levelBatched (logN - s.alphas.length) index rounds high qs (os.map (·.leaf)) F3.squeeze.1))
      F3.squeeze.2
      (R ++ [(digestFromHalves (x0, x1), levelShape (logN - s.alphas.length) next
        (2 * 2 ^ next.fold))]) := by
  set mu := logN - s.alphas.length with hmud
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
  have hb0 : Whir.levelOodGrindingBits ≠ 0 := by decide
  have hb1 : Whir.queryGrindingBits ≠ 0 := by decide
  have h3 := RunsToG.toW (runsToG_grind hb0 F1 n1 (hok0.resolve_left hb0)) R'
  set S1 := F1.nonceState n1 with hS1
  obtain ⟨m, hm⟩ : ∃ m, mu = m + 1 := ⟨mu - 1, by omega⟩
  have h4 : RunsW (Fs.CarriesGround (capOf S1) (challengeOf S1))
      (VerifierProgram.sampleChallenges mu) [] [] R'
      (oodPt F (x0 :: x1 :: high) n1 mu).1 (oodPt F (x0 :: x1 :: high) n1 mu).2.Carries R' := by
    rw [oodPt_eq, hm, Nat.add_sub_cancel]
    exact RunsFromG.toW (runsFromG_sampleN m (capOf S1) (challengeOf S1)) R'
  set G := (oodPt F (x0 :: x1 :: high) n1 mu).2 with hG
  have h5 := RunsTo.toW (runsTo_readE G y0) R'
  have h6 := RunsToG.toW (runsToG_grind hb1 (G.absorb y0 dsObserve) nn hok1) R'
  set S := oodQ F (x0 :: x1 :: high) n1 mu y0 nn with hS
  have hSe : (G.absorb y0 dsObserve).nonceState nn = S := rfl
  rw [hSe] at h6
  have h7 : RunsW (Fs.CarriesGround (capOf S) (challengeOf S))
      (sampleQueries (mu + level.logInvRate) level.queries) [] [] R' qs F3.Carries R' := by
    rw [hqs, hF3]
    exact RunsFromG.toW (sampleQueries_runG (mu + level.logInvRate) level.queries hP hQ
      (capOf S) (challengeOf S)) R'
  have h8 := RunsTo.toW (runsTo_sampleE F3) R'
  have h9 := RunsWith.toW (runsWith_queryP F3.squeeze.2 R' hi' qs os hl hopen hidx)
  have h10 := RunsWith.toW (runsWith_ret (glueLevel s F3.squeeze.1 mu
    (oodPt F (x0 :: x1 :: high) n1 mu).1 y0 qs (powers F3.squeeze.1 qs.length)
    (levelBatched mu index rounds high qs (os.map (·.leaf)) F3.squeeze.1)) F3.squeeze.2 R')
  refine RunsW.toWith (RunsW.of_eq (h1.bind (h2.bind (h3.bind (h4.bind (h5.bind (h6.bind
    (h7.bind (h8.bind (h9.bind h10))))))))) ?_ ?_ rfl rfl rfl)
  · simp
  · simp

end
end LeanVM.Guest.B1.Whir
