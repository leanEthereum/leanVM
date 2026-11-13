/-
  LeanVM.Guest.B1.Gkr.SpecInv

  The specification's GKR walk read back from an accepting run: each step's rounds and children,
  the states and sponges between steps, as functions of the words the run reads.
-/

module

public import LeanVM.Guest.B1.Gkr.Spec
public import LeanVM.Guest.B1.Tables.RunF

/-!
# The GKR walk, read back

An accepting run from a carried sponge is the carried run (`RunsTo.toT`), which is deterministic:
the reads, samples, `require`s, the equality-mode sumcheck (`gkrRun`) and a step of the walk read
back from it (`runT_readN_some`, `runT_sumcheck5_some`, `gkrStep_inv`).

`GkStepD`: a step's words, the rounds' coefficients and the three trees' children; from the
sponge and the state before it, its rounds (`run`), the sponge after its children (`sb`), the new
coordinates, the sponge and the state after it (`s'`, `st'`); `GkStepD.Ok`: the lengths and the
check. `gkStepAt zs o L c`: the words of a step of `L` rounds and `c` children a tree at offset
`o` of the stream `zs`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Runs as carried runs -/

/-- **An accepting run is the carried run**, on any rest of the stream. -/
theorem RunsTo.toT {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') {sp : Sponge} (hc : s.Carries sp) (rest : List E) :
    runT p ⟨s, none, xs ++ rest, [], []⟩ = some (a, ⟨s', none, rest, [], []⟩) := by
  obtain ⟨sp', hc', he⟩ := h sp hc rest [] []
  obtain ⟨e1, e2⟩ := eq_fsOfT (g := none) hc'
  rw [runT_of_runId p ⟨s, none, xs ++ rest, [], []⟩ sp hc a _ he, ← e1, ← e2]

/-- **Two accepting runs of one program** from one carried sponge, the second's words extending
the first's, are one. -/
theorem RunsTo.det {α : Type} {p : VerifierProgram α} {s s1 s2 : Fs} {xs ys : List E} {a b : α}
    (h1 : RunsTo p s xs a s1) (h2 : RunsTo p s (xs ++ ys) b s2) (hc : ∃ sp, s.Carries sp) :
    ys = [] ∧ a = b ∧ s1 = s2 := by
  obtain ⟨sp, hsp⟩ := hc
  have e1 := RunsTo.toT h1 hsp ys
  have e2 := RunsTo.toT h2 hsp []
  rw [List.append_nil, e1] at e2
  simp only [Option.some.injEq, Prod.mk.injEq, TSt.mk.injEq, and_true, true_and] at e2
  exact ⟨e2.2.2, e2.1, e2.2.1⟩

/-! ## The carried run, read back -/

theorem runT_bind_some {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {st st'' :
    TSt} {b : β}
    (h : runT (p >>= f) st = some (b, st'')) :
    ∃ a st', runT p st = some (a, st') ∧ runT (f a) st' = some (b, st'') := by
  rw [prog_bind_eq, runT_bind] at h
  obtain ⟨⟨a, st'⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, st', h1, h2⟩

theorem runT_pure_some {α : Type} {a b : α} {st st' : TSt}
    (h : runT (pure a : VerifierProgram α) st = some (b, st')) : b = a ∧ st' = st := by
  change runT (VerifierProgram.ret a) st = some (b, st') at h
  simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem runT_readE_some {s : Fs} {zs : List E} {os : List (List Opening)} {R : List (Digest × ℕ × ℕ)}
    {x : E} {st' : TSt} (h : runT VerifierProgram.readScalar ⟨s, none, zs, os, R⟩ = some (x, st')) :
    ∃ zs', zs = x :: zs' ∧ st' = ⟨s.absorb x dsObserve, none, zs', os, R⟩ := by
  cases zs with
  | nil => simp [VerifierProgram.readScalar, runT] at h
  | cons z zs' =>
    simp only [VerifierProgram.readScalar, runT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨zs', rfl, rfl⟩

theorem runT_sampleE (s : Fs) (zs : List E) (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) :
    runT VerifierProgram.sampleChallenge ⟨s, none, zs, os, R⟩ =
      some (s.squeeze.1, ⟨s.squeeze.2, none, zs, os, R⟩) :=
  rfl

/-- `n` reads take the next `n` words, absorbed. -/
theorem runT_readN_some : ∀ (n : ℕ) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) (xs : List E) (st' : TSt),
    runT (VerifierProgram.readScalars n) ⟨s, none, zs, os, R⟩ = some (xs, st') →
      ∃ rest, xs.length = n ∧ zs = xs ++ rest ∧ st' = ⟨s.absorbAll xs dsObserve, none, rest, os, R⟩
  | 0, s, zs, os, R, xs, st', h => by
    obtain ⟨rfl, rfl⟩ := runT_pure_some (a := ([] : List E)) h
    exact ⟨zs, rfl, rfl, rfl⟩
  | n + 1, s, zs, os, R, xs, st', h => by
    simp only [VerifierProgram.readScalars] at h
    obtain ⟨x, st1, h1, h2⟩ := runT_bind_some h
    obtain ⟨zs1, rfl, rfl⟩ := runT_readE_some h1
    obtain ⟨ys, st2, h3, h4⟩ := runT_bind_some h2
    obtain ⟨rest, hl, hz, hst⟩ := runT_readN_some n _ _ _ _ _ _ h3
    obtain ⟨rfl, rfl⟩ := runT_pure_some h4
    exact ⟨rest, by simp [hl], by rw [hz]; rfl, hst⟩

/-- `n` samples squeeze `n` challenges. -/
theorem runT_sampleN : ∀ (n : ℕ) (s : Fs) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)),
    runT (VerifierProgram.sampleChallenges n) ⟨s, none, zs, os, R⟩ = some ((s.squeezeN n).1,
      ⟨(s.squeezeN n).2, none, zs, os, R⟩)
  | 0, s, zs, os, R => rfl
  | n + 1, s, zs, os, R => by
    simp only [VerifierProgram.sampleChallenges, prog_bind_eq, runT_bind, runT_sampleE,
        Option.bind_some]
    rw [runT_sampleN n]
    rfl

theorem runT_require_some {c : Prop} [Decidable c] {st st' : TSt} {u : Unit}
    (h : runT (VerifierProgram.require c) st = some (u, st')) : c ∧ st' = st := by
  unfold VerifierProgram.require at h
  split at h
  · rename_i hc
    simp only [runT, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc, h.2.symm⟩
  · simp [runT] at h

/-- **The equality-mode sumcheck of five coefficients, read back**: its rounds' four words each,
and `gkrRun` of them. -/
theorem runT_sumcheck5_some : ∀ (es : List E) (claim : E) (s : Fs) (zs : List E)
    (os : List (List Opening)) (R : List (Digest × ℕ × ℕ)) (r : List E × E) (st' : TSt),
    runT (sumcheck claim 5 (es.map some)) ⟨s, none, zs, os, R⟩ = some (r, st') →
      ∃ (cs : List (List E)) (rest : List E), cs.length = es.length ∧ (∀ c ∈ cs, c.length = 4) ∧
        zs = cs.flatten ++ rest ∧
        r = ((gkrRun cs es claim s).1, (gkrRun cs es claim s).2.1) ∧
        st' = ⟨(gkrRun cs es claim s).2.2, none, rest, os, R⟩
  | [], claim, s, zs, os, R, r, st', h => by
    simp only [List.map_nil, sumcheck] at h
    obtain ⟨rfl, rfl⟩ := runT_pure_some h
    exact ⟨[], zs, rfl, by simp, rfl, rfl, rfl⟩
  | e :: es, claim, s, zs, os, R, r, st', h => by
    rw [List.map_cons, sumcheck_cons_eq'] at h
    obtain ⟨msg, st1, h1, h2⟩ := runT_bind_some h
    simp only [sumcheckRoundPoly] at h1
    obtain ⟨c, st0, h3, h4⟩ := runT_bind_some h1
    obtain ⟨rest0, hl, hz, rfl⟩ := runT_readN_some _ _ _ _ _ _ _ h3
    obtain ⟨rfl, rfl⟩ := runT_pure_some h4
    obtain ⟨ch, st2, h5, h6⟩ := runT_bind_some h2
    rw [runT_sampleE] at h5
    simp only [Option.some.injEq, Prod.mk.injEq] at h5
    obtain ⟨rfl, rfl⟩ := h5
    obtain ⟨r', st3, h7, h8⟩ := runT_bind_some h6
    obtain ⟨cs, rest, hcl, hc4, hz', hr, hst⟩ := runT_sumcheck5_some es _ _ _ _ _ _ _ h7
    obtain ⟨rfl, rfl⟩ := runT_pure_some h8
    refine ⟨c :: cs, rest, by simp [hcl], fun c' hc' => ?_, ?_, ?_, ?_⟩
    · rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hl
      · exact hc4 c' hc'
    · simp only [List.flatten_cons, List.append_assoc]
      rw [hz, hz']
    · rw [hr]; rfl
    · exact hst

/-! ## A step's words -/

/-- A step's words: its rounds' coefficients (four a round) and the three trees' children. -/
structure GkStepD where
  /-- The rounds' coefficients. -/
  cs : List (List E)
  /-- The first tree's children. -/
  ch0 : List E
  /-- The second tree's children. -/
  ch1 : List E
  /-- The third tree's children. -/
  ch2 : List E

namespace GkStepD

variable (D : GkStepD) (s : Fs) (st : GkrState)

/-- The words the step reads. -/
def xs : List E := D.cs.flatten ++ (D.ch0 ++ (D.ch1 ++ D.ch2))

/-- The rounds, from the sponge after the combiner: challenges, last claim, sponge. -/
def run : List E × E × Fs := gkrRun D.cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2

/-- The sponge after the children. -/
def sb : Fs :=
  (((D.run s st).2.2.absorbAll D.ch0 dsObserve).absorbAll D.ch1 dsObserve).absorbAll D.ch2
    dsObserve

/-- The `n` new coordinates. -/
def ys (n : ℕ) : List E := ((D.sb s st).squeezeN n).1

/-- The sponge after the step of `n` levels. -/
def s' (n : ℕ) : Fs := ((D.sb s st).squeezeN n).2

/-- The state after the step of `n` levels. -/
def st' (n : ℕ) : GkrState :=
  ⟨[D.ch0, D.ch1, D.ch2].map (multilinearEval · (D.ys s st n)), D.ys s st n ++ (D.run s st).1⟩

/-- **A step's facts**: a round per coordinate, `2^n` children a tree, and the check. -/
def Ok (n : ℕ) : Prop :=
  D.cs.length = st.point.length ∧ (∀ c ∈ D.cs, c.length = 4) ∧ D.ch0.length = 2 ^ n ∧
    D.ch1.length = 2 ^ n ∧ D.ch2.length = 2 ^ n ∧
    (D.run s st).2.1 = polyEval [prodE D.ch0, prodE D.ch1, prodE D.ch2] s.squeeze.1

end GkStepD

/-- **One step of the walk, read back** from the carried run (two levels, or one from a state
without a point). -/
theorem gkrStep_invT {n : ℕ} (hs : n ≤ 2) (last : Bool) {st st' : GkrState} {s : Fs}
    {zs : List E} {X : TSt}
    (e : runT (gkrStep n last st) ⟨s, none, zs, [], []⟩ = some (st', X))
    (hn : n = 2 ∨ st.point = []) :
    ∃ (D : GkStepD) (rest : List E), D.Ok s st n ∧ zs = D.xs ++ rest ∧ st' = D.st' s st n ∧
      X = ⟨D.s' s st n, none, rest, [], []⟩ := by
  rw [gkrStep_eq hs] at e
  obtain ⟨c, st1, h1, h2⟩ := runT_bind_some e
  rw [runT_sampleE] at h1
  simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  obtain ⟨r, st2, h3, h4⟩ := runT_bind_some h2
  obtain ⟨cs, rest0, hcl, hc4, hz, hr, hst⟩ : ∃ (cs : List (List E)) (rest0 : List E),
      cs.length = st.point.length ∧ (∀ c ∈ cs, c.length = 4) ∧ zs = cs.flatten ++ rest0 ∧
      r = ((gkrRun cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2).1,
        (gkrRun cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2).2.1) ∧
      st2 = ⟨(gkrRun cs st.point (polyEval st.values s.squeeze.1) s.squeeze.2).2.2, none, rest0,
        [], []⟩ := by
    rcases hn with rfl | hp
    · exact runT_sumcheck5_some _ _ _ _ _ _ _ _ h3
    · rw [hp] at h3 ⊢
      simp only [List.map_nil, sumcheck] at h3
      obtain ⟨rfl, rfl⟩ := runT_pure_some h3
      exact ⟨[], zs, rfl, by simp, rfl, rfl, rfl⟩
  subst hr hst
  obtain ⟨ch0, st3, h5, h6⟩ := runT_bind_some h4
  obtain ⟨r0, l0, z0, rfl⟩ := runT_readN_some _ _ _ _ _ _ _ h5
  obtain ⟨ch1, st4, h7, h8⟩ := runT_bind_some h6
  obtain ⟨r1, l1, z1, rfl⟩ := runT_readN_some _ _ _ _ _ _ _ h7
  obtain ⟨ch2, st5, h9, h10⟩ := runT_bind_some h8
  obtain ⟨r2, l2, z2, rfl⟩ := runT_readN_some _ _ _ _ _ _ _ h9
  obtain ⟨u, st6, h11, h12⟩ := runT_bind_some h10
  obtain ⟨hchk, rfl⟩ := runT_require_some h11
  obtain ⟨y, st7, h13, h14⟩ := runT_bind_some h12
  rw [runT_sampleN] at h13
  simp only [Option.some.injEq, Prod.mk.injEq] at h13
  obtain ⟨rfl, rfl⟩ := h13
  obtain ⟨e1, e2⟩ := runT_pure_some h14
  refine ⟨⟨cs, ch0, ch1, ch2⟩, r2, ⟨hcl, hc4, l0, l1, l2, hchk⟩, ?_, ?_, ?_⟩
  · rw [hz, z0, z1, z2]
    simp [GkStepD.xs]
  · rw [e1]; rfl
  · rw [e2]; rfl

end
end LeanVM.Guest.B1.Tables
