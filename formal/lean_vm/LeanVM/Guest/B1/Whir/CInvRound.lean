/-
  LeanVM.Guest.B1.Whir.CInvRound

  A fold round and a level's fold rounds, read backwards from an accepting run.
-/

module

public import LeanVM.Guest.B1.Whir.CInv
public import LeanVM.Guest.B1.Whir.CRounds

/-!
# Fold rounds, backwards

* `runTz_readE`, `runTz_sampleE_none`, `runTz_sampleE_some`, `runTz_grindPoW`: the Spec's reads,
  samples and grinds in a sequence, backwards.
* `runT_of_runsTo`: a forward run reading no opening is the carried run on any rest.
* `foldRound_inv`: an accepting run of `foldRound` from a carried capacity read its seven words
  `n1, u0, v0, c0, v1, c1, n2`, both grinds passing (`RoundGrinds`), `θ, γ, α, β` nonzero; it
  returns `opening_round_run`'s.
* `foldRounds_inv`: `n` of them (`roundsSpec`, `RoundsOk`), the carried capacity `roundsCap`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none)

@[expose] public section

variable {α β : Type}

/-! ## The primitives in a sequence -/

theorem runTz_readE {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTz (VerifierProgram.readScalar.bind f) st = some r) :
    ∃ x xs, st.stream = x :: xs ∧ st.ground = none ∧
      runTz (f x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ = some r :=
  runTz_read (k := f) h

theorem runTz_sampleE_none {f : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTz (VerifierProgram.sampleChallenge.bind f) st = some r) (hg : st.ground = none) :
    st.sponge.squeeze.1 ≠ 0 ∧
      runTz (f st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ =
        some r :=
  runTz_sample_none (k := f) h hg

theorem runTz_sampleE_some {f : E → VerifierProgram α} {st : TSt} {r : α × TSt} {c : E}
    (h : runTz (VerifierProgram.sampleChallenge.bind f) st = some r) (hg : st.ground = some c) :
    c ≠ 0 ∧ runTz (f c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ = some r :=
  runTz_sample_some (k := f) h hg

theorem runTz_grindPoW {b : ℕ} (hb : b ≠ 0) {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runTz ((VerifierProgram.grindProofOfWork b).bind f) st = some r) :
    ∃ n xs, st.stream = n :: xs ∧ st.ground = none ∧
      powOk b (Keccak.lane (st.sponge.nonceState n) 2) = true ∧
      runTz (f ()) ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)),
        xs, st.openings, st.roots⟩ = some r := by
  unfold VerifierProgram.grindProofOfWork at h
  simp only [hb, ↓reduceIte] at h
  exact runTz_grind (k := f ()) h

/-- **A forward run reading no opening is the carried run** on any rest. -/
theorem runT_of_runsTo {p : VerifierProgram α} {F F' : Fs} {xs : List E} {a : α}
    (h : RunsTo p F xs a F') (hc : ∃ sp, F.Carries sp) (rest : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runT p ⟨F, none, xs ++ rest, os, R⟩ = some (a, ⟨F', none, rest, os, R⟩) := by
  have := runT_of_runsWith (RunsTo.withRoots h R) hc rest os
  simpa using this

/-- An accepting `runTz` from a carried capacity returns what a forward run reading no opening
does. -/
theorem runTz_detTo {p : VerifierProgram α} {F F' : Fs} {xs rest : List E} {a b : α}
    {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)} {st1 : TSt}
    (h : runTz p ⟨F, none, xs ++ rest, os, R⟩ = some (b, st1)) (hf : RunsTo p F xs a F')
    (hc : ∃ sp, F.Carries sp) : b = a ∧ st1 = ⟨F', none, rest, os, R⟩ := by
  have e1 := runTz_runT p _ _ h
  rw [runT_of_runsTo hf hc rest os R] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.symm⟩

/-! ## One fold round -/

/-- The sponge `opening_round_run` leaves. -/
def roundSponge (fs : List E) (w : List E) : Fs :=
  (rdG2 fs (w.getD 0 0) [w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0, w.getD 5 0]
    (w.getD 6 0)).2.squeeze.2.squeeze.2

/-- What `opening_round_run` returns. -/
def roundSpec (s : WhirState) (fs : List E) (w : List E) : WhirState × FoldRound :=
  let n1 := w.getD 0 0
  let m := [w.getD 1 0, w.getD 2 0, w.getD 3 0, w.getD 4 0, w.getD 5 0]
  let n2 := w.getD 6 0
  ({ s with
      claim := roundClaim s.claim (rdG1 fs n1).1 (rdG2 fs n1 m n2).1
        (rdG2 fs n1 m n2).2.squeeze.1 (rdG2 fs n1 m n2).2.squeeze.2.squeeze.1
        (w.getD 1 0) (w.getD 2 0) (w.getD 3 0) (w.getD 4 0) (w.getD 5 0),
      gammas := s.gammas ++ [(rdG2 fs n1 m n2).1] },
    ⟨(rdG1 fs n1).1, (rdG2 fs n1 m n2).2.squeeze.1, (rdG2 fs n1 m n2).2.squeeze.2.squeeze.1⟩)

/-- A round's challenges `θ, γ, α, β` are nonzero. -/
def RoundNZ (fs w : List E) : Prop :=
  (roundChs fs w).1 ≠ 0 ∧ (roundChs fs w).2.1 ≠ 0 ∧ (roundChs fs w).2.2.1 ≠ 0 ∧
    (roundChs fs w).2.2.2 ≠ 0

theorem foldGrind_ne : _root_.LeanVM.Parameters.Whir.foldGrindingBits ≠ 0 := by decide

/-- **A fold round, backwards.** -/
theorem foldRound_inv {s : WhirState} {fs xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : WhirState × FoldRound} {st1 : TSt}
    (hc : ∃ sp, (⟨fs, []⟩ : Fs).Carries sp)
    (h : runTz (foldRound s) ⟨⟨fs, []⟩, none, xs, os, R⟩ = some (a, st1)) :
    ∃ w xs', w.length = 7 ∧ xs = w ++ xs' ∧ RoundGrinds fs w ∧ RoundNZ fs w ∧
      a = roundSpec s fs w ∧ st1 = ⟨roundSponge fs w, none, xs', os, R⟩ := by
  have hb := foldGrind_ne
  have h0 := h
  unfold foldRound at h
  obtain ⟨n1, xs1, hs1, -, hp1, h⟩ := runTz_grindPoW hb h
  obtain ⟨hθ, h⟩ := runTz_sampleE_some h rfl
  obtain ⟨u0, xs2, hs2, -, h⟩ := runTz_readE h
  obtain ⟨v0, xs3, hs3, -, h⟩ := runTz_readE h
  obtain ⟨c0, xs4, hs4, -, h⟩ := runTz_readE h
  obtain ⟨v1, xs5, hs5, -, h⟩ := runTz_readE h
  obtain ⟨c1, xs6, hs6, -, h⟩ := runTz_readE h
  obtain ⟨n2, xs7, hs7, -, hp2, h⟩ := runTz_grindPoW hb h
  obtain ⟨hγ, h⟩ := runTz_sampleE_some h rfl
  obtain ⟨hα, h⟩ := runTz_sampleE_none h rfl
  obtain ⟨hβ, -⟩ := runTz_sampleE_none h rfl
  simp only at hs1 hs2 hs3 hs4 hs5 hs6 hs7 hθ hγ hα hβ hp1 hp2
  subst hs7 hs6 hs5 hs4 hs3 hs2
  have hxs : xs = [n1, u0, v0, c0, v1, c1, n2] ++ xs7 := by rw [hs1]; rfl
  have e1 : rdG1 fs n1 = (challengeOf ((⟨fs, []⟩ : Fs).nonceState n1),
      ⟨capOf ((⟨fs, []⟩ : Fs).nonceState n1), []⟩) := Fs.grindSqueeze_pos _ hb _
  have es : rdS2 fs n1 [u0, v0, c0, v1, c1] =
      (((((⟨capOf ((⟨fs, []⟩ : Fs).nonceState n1), []⟩ : Fs).absorb u0 dsObserve).absorb v0
        dsObserve).absorb c0 dsObserve).absorb v1 dsObserve).absorb c1 dsObserve := by
    rw [rdS2, e1]; rfl
  have e2 : rdG2 fs n1 [u0, v0, c0, v1, c1] n2 =
      (challengeOf ((rdS2 fs n1 [u0, v0, c0, v1, c1]).nonceState n2),
        ⟨capOf ((rdS2 fs n1 [u0, v0, c0, v1, c1]).nonceState n2), []⟩) := Fs.grindSqueeze_pos _ hb _
  have g1 : (⟨fs, []⟩ : Fs).GrindOk _root_.LeanVM.Parameters.Whir.foldGrindingBits n1 := Or.inr hp1
  have g2 : (rdS2 fs n1 [u0, v0, c0, v1, c1]).GrindOk
      _root_.LeanVM.Parameters.Whir.foldGrindingBits n2 := Or.inr (by rw [es]; exact hp2)
  have hf := opening_round_run s fs n1 u0 v0 c0 v1 c1 n2 g1 g2
  rw [hxs] at h0
  obtain ⟨ea, est⟩ := runTz_detTo h0 hf hc
  refine ⟨[n1, u0, v0, c0, v1, c1, n2], xs7, rfl, hxs, ⟨g1, g2⟩, ?_, ea, est⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [roundChs, List.getD_cons_zero, List.getD_cons_succ]
  · rw [e2, es]; exact hγ
  · rw [e2, es]; exact hα
  · rw [e2, es]; exact hβ
  · rw [e1]; exact hθ


/-! ## A level's fold rounds -/

/-- What `foldRounds n` returns on the words `xs`, from the capacity `fs`. -/
def roundsSpec : ℕ → WhirState → List E → List E → WhirState × List FoldRound
  | 0, s, _, _ => (s, [])
  | n + 1, s, fs, xs =>
    let t := roundsSpec n (roundSpec s fs (xs.take 7)).1 (roundSponge fs (xs.take 7)).cap (xs.drop 7)
    (t.1, (roundSpec s fs (xs.take 7)).2 :: t.2)

/-- The capacity after `n` rounds. -/
def roundsCap : ℕ → List E → List E → List E
  | 0, fs, _ => fs
  | n + 1, fs, xs => roundsCap n (roundSponge fs (xs.take 7)).cap (xs.drop 7)

/-- Every round's grinds pass and its challenges are nonzero. -/
def RoundsOk : ℕ → List E → List E → Prop
  | 0, _, _ => True
  | n + 1, fs, xs => RoundGrinds fs (xs.take 7) ∧ RoundNZ fs (xs.take 7) ∧
      RoundsOk n (roundSponge fs (xs.take 7)).cap (xs.drop 7)

theorem roundSponge_pend (fs w : List E) : (roundSponge fs w).pend = [] := rfl

theorem roundSponge_eq (fs w : List E) : roundSponge fs w = ⟨(roundSponge fs w).cap, []⟩ := rfl

/-- The guest's rounds' capacity is the Spec's. -/
theorem roundRets_take5 (fs : List E) (cur cl : E) (w : List E) :
    (roundRets fs cur cl w).take 5 = (roundSponge fs w).cap := by
  simp [roundRets, roundSponge, Fs.squeeze, capOf]

theorem roundsTr_cap : ∀ (n : ℕ) (fs : List E) (cl : E) (xs : List E),
    (roundsTr n fs cl xs).1 = roundsCap n fs xs
  | 0, _, _, _ => rfl
  | n + 1, fs, cl, xs => by
    simp only [roundsTr, roundsCap, roundRets_take5]
    exact roundsTr_cap n _ _ _

/-- **A level's fold rounds, backwards.** -/
theorem foldRounds_inv : ∀ (n : ℕ) {s : WhirState} {fs xs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {a : WhirState × List FoldRound} {st1 : TSt},
    (∃ sp, (⟨fs, []⟩ : Fs).Carries sp) →
    runTz (foldRounds n s) ⟨⟨fs, []⟩, none, xs, os, R⟩ = some (a, st1) →
    ∃ ws xs', ws.length = 7 * n ∧ xs = ws ++ xs' ∧ RoundsOk n fs ws ∧ a = roundsSpec n s fs ws ∧
      st1 = ⟨⟨roundsCap n fs ws, []⟩, none, xs', os, R⟩
  | 0, s, fs, xs, os, R, a, st1, _, h => by
    have e := runTz_ret_inv (α := WhirState × List FoldRound) h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨[], xs, rfl, rfl, trivial, rfl, rfl⟩
  | n + 1, s, fs, xs, os, R, a, st1, hc, h => by
    obtain ⟨a1, st2, h1, h2⟩ := runTz_bind_some (p := foldRound s) h
    obtain ⟨w, xs1, hwl, hxs, hg, hnz, ea, est⟩ := foldRound_inv hc h1
    subst ea est
    obtain ⟨a2, st3, h3, h4⟩ := runTz_bind_some (p := foldRounds n (roundSpec s fs w).1) h2
    have hc1 : ∃ sp, (⟨(roundSponge fs w).cap, []⟩ : Fs).Carries sp := by
      obtain ⟨sp, hsp⟩ := runTz_carries h1 (by obtain ⟨sp, h⟩ := hc; exact ⟨sp, h⟩)
      exact ⟨sp, hsp⟩
    have h3' : runTz (foldRounds n (roundSpec s fs w).1)
        ⟨⟨(roundSponge fs w).cap, []⟩, none, xs1, os, R⟩ = some (a2, st3) := h3
    obtain ⟨ws, xs', hl, hx, hok, ea2, est3⟩ := foldRounds_inv n hc1 h3'
    subst ea2 est3
    have e := runTz_ret_inv h4
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have htw : (w ++ ws).take 7 = w := by simp [hwl]
    have hdw : (w ++ ws).drop 7 = ws := by simp [hwl]
    refine ⟨w ++ ws, xs', by simp [hwl, hl]; ring, by rw [hxs, hx, List.append_assoc], ?_, ?_, ?_⟩
    · simp only [RoundsOk, htw, hdw]
      exact ⟨hg, hnz, hok⟩
    · simp only [roundsSpec, htw, hdw]; rfl
    · simp only [roundsCap, htw, hdw]

end
end LeanVM.Guest.B1.Whir
