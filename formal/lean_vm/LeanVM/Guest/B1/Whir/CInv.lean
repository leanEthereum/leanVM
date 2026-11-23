/-
  LeanVM.Guest.B1.Whir.CInv

  Accepting runs read backwards: the carried run, split at its binds and at each primitive, for the
  completeness direction.
-/

module

public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.B1.Whir.Run
public import Statement.LeanVmGuestCompleteness

/-!
# Runs, backwards

`runTc p st`: `Tables.runT` (the Spec's run on the carried sponge, with openings and roots), its
equation lemmas read backwards here; it is `runT` (`runTc_runT`), and it splits at a `bind`
(`runTc_bind`).

The primitives read backwards (`runTc_read`, `runTc_sample_none`, `runTc_sample_some`,
`runTc_grind`, `runTc_commit`, `runTc_query`, `runTc_require`), and the loops of reads and samples
(`runTc_readScalars`, `runTc_sampleChallenges`). `runT_of_runsWith`: a forward run (`RunsWith`) is
the carried run on any rest, so a forward lemma fixes what an accepting run returns.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none)

@[expose] public section

/-- **The carried run**, `runT` clause by clause. -/
def runTc {α : Type} : VerifierProgram α → TSt → Option (α × TSt)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.stream, s.ground with
    | x :: xs, none => runTc (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
    | _, _ => none
  | .sample k, s => match s.ground with
    | some c => runTc (k c) { s with ground := none }
    | none => runTc (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .grind bits k, s => match s.stream, s.ground with
    | n :: xs, none =>
      if powOk bits (Keccak.lane (s.sponge.nonceState n) 2) then
        runTc k { s with
          sponge := Fs.mk (capOf (s.sponge.nonceState n)) []
          ground := some (challengeOf (s.sponge.nonceState n))
          stream := xs }
      else none
    | _, _ => none
  | .commit height width k, s => match s.stream, s.ground with
    | x0 :: x1 :: xs, none =>
      runTc k { s with
        sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
        stream := xs
        roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)] }
    | _, _ => none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => runTc (k rows) { s with openings := rest }
      | none => none
    | _, _ => none

variable {α β : Type}

/-- **`runTc` is `runT`.** -/
theorem runTc_eq_runT (p : VerifierProgram α) : ∀ st, runTc p st = runT p st := by
  induction p with
  | ret a => intro st; rfl
  | fail => intro st; rfl
  | read k ih =>
    intro st
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | x :: xs, none => exact ih x _
  | sample k ih =>
    intro st
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | none => exact ih _ _
    | some c => exact ih _ _
  | grind b k ih =>
    intro st
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | n :: xs, none =>
      simp only [runTc, runT]
      by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
      · simp only [hp, ↓reduceIte]; exact ih _
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
  | commit hh ww k ih =>
    intro st
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, some _ => rfl
    | x0 :: x1 :: xs, none => exact ih _
  | query i ps k ih =>
    intro st
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runTc, runT, hR]
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runTc, runT, hR]
      | cons phase rest =>
        simp only [runTc, runT, hR]
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp only
        | some rows => simp only; exact ih rows _

/-- **An accepting `runTc` is an accepting run.** -/
theorem runTc_runT (p : VerifierProgram α) : ∀ st r, runTc p st = some r → runT p st = some r := by
  induction p with
  | ret a => intro st r h; exact h
  | fail => intro st r h; simp [runTc] at h
  | read k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTc] at h
    | _ :: _, some _, h => simp [runTc] at h
    | x :: xs, none, h => exact ih x _ r h
  | sample k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | none => exact ih _ _ r h
    | some c => exact ih _ _ r h
  | grind b k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTc] at h
    | _ :: _, some _, h => simp [runTc] at h
    | n :: xs, none, h =>
      simp only [runTc] at h
      simp only [runT]
      by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
      · simp only [hp, ↓reduceIte] at h ⊢
        exact ih _ r h
      · simp [hp] at h
  | commit hh ww k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTc] at h
    | [_], _, h => simp [runTc] at h
    | _ :: _ :: _, some _, h => simp [runTc] at h
    | x0 :: x1 :: xs, none, h => exact ih _ r h
  | query i ps k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runTc, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runTc, hR] at h
      | cons phase rest =>
        simp only [runTc, hR] at h
        simp only [runT, hR]
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h ⊢
          exact ih rows _ r h

/-- **`runTc` splits at a `bind`.** -/
theorem runTc_bind (p : VerifierProgram α) (f : α → VerifierProgram β) (st : TSt) :
    runTc (p.bind f) st = (runTc p st).bind (fun r ↦ runTc (f r.1) r.2) := by
  induction p generalizing st with
  | ret a => rfl
  | fail => rfl
  | read k ih =>
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | x :: xs, none => exact ih _ _
  | sample k ih =>
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | none => exact ih _ _
    | some c => exact ih _ _
  | grind b k ih =>
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | n :: xs, none =>
      show (if _ then _ else none) = (if _ then _ else none).bind _
      by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
      · simp only [hp, ↓reduceIte]; exact ih _
      · simp only [hp]; rfl
  | commit hh ww k ih =>
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, some _ => rfl
    | x0 :: x1 :: xs, none => exact ih _
  | query i ps k ih =>
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [VerifierProgram.bind, runTc, hR]
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [VerifierProgram.bind, runTc, hR]
      | cons phase rest =>
        simp only [VerifierProgram.bind, runTc, hR]
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp only; rfl
        | some rows => simp only; exact ih rows _

/-- An accepting run of a sequence: its first part's, then the rest's. -/
theorem runTc_bind_some {p : VerifierProgram α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runTc (p.bind f) st = some r) :
    ∃ a st1, runTc p st = some (a, st1) ∧ runTc (f a) st1 = some r := by
  rw [runTc_bind] at h
  obtain ⟨⟨a, st1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, st1, h1, h2⟩

/-! ## The primitives, backwards -/

theorem runTc_read {k : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTc (.read k) st = some r) :
    ∃ x xs, st.stream = x :: xs ∧ st.ground = none ∧
      runTc (k x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  rcases stream with _ | ⟨x, xs⟩ <;> rcases g with _ | c <;> simp only [runTc, reduceCtorEq] at h
  exact ⟨x, xs, rfl, rfl, h⟩

theorem runTc_sample_none {k : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTc (.sample k) st = some r) (hg : st.ground = none) :
    runTc (k st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ =
      some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact h

theorem runTc_sample_some {k : E → VerifierProgram α} {st : TSt} {r : α × TSt} {c : E}
    (h : runTc (.sample k) st = some r) (hg : st.ground = some c) :
    runTc (k c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  exact h

theorem runTc_grind {b : ℕ} {k : VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTc (.grind b k) st = some r) :
    ∃ n xs, st.stream = n :: xs ∧ st.ground = none ∧
      powOk b (Keccak.lane (st.sponge.nonceState n) 2) = true ∧
      runTc k ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)), xs,
        st.openings, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  rcases stream with _ | ⟨n, xs⟩ <;> rcases g with _ | c <;> simp only [runTc, reduceCtorEq] at h
  split_ifs at h with hp
  exact ⟨n, xs, rfl, rfl, hp, h⟩

theorem runTc_commit {hh ww : ℕ} {k : VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTc (.commit hh ww k) st = some r) :
    ∃ x0 x1 xs, st.stream = x0 :: x1 :: xs ∧ st.ground = none ∧
      runTc k ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> rcases g with _ | c <;>
    simp only [runTc, reduceCtorEq] at h
  exact ⟨x0, x1, xs, rfl, rfl, h⟩

theorem runTc_query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runTc (.query i ps k) st = some r) :
    ∃ root height width phase rest rows, st.roots[i]? = some (root, height, width) ∧
      st.openings = phase :: rest ∧
      Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows ∧
      runTc (k rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  cases hR : R[i]? with
  | none => simp [runTc, hR] at h
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil => simp [runTc, hR] at h
    | cons phase rest =>
      simp only [runTc, hR] at h
      cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
          phase) with
      | none => simp [hop] at h
      | some rows =>
        simp only [hop] at h
        exact ⟨root, height, width, phase, rest, rows, rfl, rfl, hop, h⟩

theorem runTc_require {c : Prop} [Decidable c] {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runTc ((VerifierProgram.require c).bind f) st = some r) :
    c ∧ runTc (f ()) st = some r := by
  unfold VerifierProgram.require at h
  split_ifs at h with hc
  · exact ⟨hc, h⟩
  · simp [VerifierProgram.bind, runTc] at h

theorem runTc_ret_inv {a : α} {st : TSt} {r : α × TSt} (h : runTc (.ret a) st = some r) :
    r = (a, st) := (Option.some.inj h).symm

/-! ## Loops of reads and samples -/

/-- `n` reads, backwards: the words, absorbed. -/
theorem runTc_readScalars {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runTc ((VerifierProgram.readScalars n).bind f) st = some r →
      ∃ ys xs, ys.length = n ∧ st.stream = ys ++ xs ∧
        runTc (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩ = some r
  | 0, st, r, hg, h => by
    refine ⟨[], st.stream, rfl, rfl, ?_⟩
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at hg
    subst hg
    exact h
  | n + 1, st, r, hg, h => by
    have e : (VerifierProgram.readScalars (n + 1)).bind f =
        .read fun x ↦ (VerifierProgram.readScalars n).bind fun xs ↦ f (x :: xs) := by
      show ((VerifierProgram.read VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.readScalars n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e] at h
    obtain ⟨x, xs, hs, -, h1⟩ := runTc_read h
    obtain ⟨ys, zs, hl, hz, h2⟩ := runTc_readScalars n _ r rfl h1
    simp only at hz
    refine ⟨x :: ys, zs, by simp [hl], by rw [hs, hz]; rfl, ?_⟩
    exact h2

/-- `n` samples from no ground, backwards: the squeezes. -/
theorem runTc_sampleChallenges {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runTc ((VerifierProgram.sampleChallenges n).bind f) st = some r →
        runTc (f (st.sponge.squeezeN n).1)
          ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩ = some r
  | 0, st, r, hg, h => by
    obtain ⟨s, g, stream, os, R⟩ := st
    simp only at hg
    subst hg
    exact h
  | n + 1, st, r, hg, h => by
    have e : (VerifierProgram.sampleChallenges (n + 1)).bind f =
        .sample fun x ↦ (VerifierProgram.sampleChallenges n).bind fun xs ↦ f (x :: xs) := by
      show ((VerifierProgram.sample VerifierProgram.ret).bind fun x ↦
        ((VerifierProgram.sampleChallenges n).bind fun xs ↦ VerifierProgram.ret (x :: xs))).bind f = _
      simp only [VerifierProgram.bind_assoc]
      rfl
    rw [e] at h
    exact runTc_sampleChallenges n _ r rfl (runTc_sample_none h hg)

/-! ## Forward runs fix accepting ones -/

/-- **A forward run is the carried run** on any rest, from a sponge some state carries. -/
theorem runT_of_runsWith {p : VerifierProgram α} {F F' : Fs} {xs : List E}
    {os : List (List Opening)} {R R' : List (Digest × ℕ × ℕ)} {a : α}
    (h : RunsWith p F xs os R a F' R') (hc : ∃ sp, F.Carries sp) (rest : List E)
    (orest : List (List Opening)) :
    runT p ⟨F, none, xs ++ rest, os ++ orest, R⟩ = some (a, ⟨F', none, rest, orest, R'⟩) := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', hc', e⟩ := h sp hsp rest orest
  have := runT_of_runId p ⟨F, none, xs ++ rest, os ++ orest, R⟩ sp hsp a _ e
  obtain ⟨e1, e2⟩ := eq_fsOfT (tcar_none.mpr hc')
  rw [this, ← e1, ← e2]

/-- **An accepting `runTc` returns what a forward run of the same program does.** -/
theorem runTc_det {p : VerifierProgram α} {F F' : Fs} {xs : List E}
    {os : List (List Opening)} {R R' : List (Digest × ℕ × ℕ)} {a b : α} {rest : List E}
    {orest : List (List Opening)} {st1 : TSt}
    (h : runTc p ⟨F, none, xs ++ rest, os ++ orest, R⟩ = some (b, st1))
    (hf : RunsWith p F xs os R a F' R') (hc : ∃ sp, F.Carries sp) :
    b = a ∧ st1 = ⟨F', none, rest, orest, R'⟩ := by
  have e1 := runTc_runT p _ _ h
  rw [runT_of_runsWith hf hc rest orest] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.symm⟩

/-- A run from a carried sponge leaves a carried one. -/
theorem runTc_carries {p : VerifierProgram α} {st st' : TSt} {a : α}
    (h : runTc p st = some (a, st')) (hc : ∃ sp, TCar st.sponge st.ground sp) :
    ∃ sp, TCar st'.sponge st'.ground sp := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', hc', -⟩ := runId_of_runT p st sp hsp a st' (runTc_runT p st _ h)
  exact ⟨sp', hc'⟩

end
end LeanVM.Guest.B1.Whir
