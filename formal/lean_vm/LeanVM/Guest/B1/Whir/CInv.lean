/-
  LeanVM.Guest.B1.Whir.CInv

  Accepting runs read backwards: the carried run refusing a zero challenge, split at its binds and
  at each primitive, for the completeness direction.
-/

module

public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.B1.Whir.Run

/-!
# Runs, backwards

`runTz p st`: `Tables.runT` (the Spec's run on the carried sponge, with openings and roots) where a
sampled challenge `0` fails. It is `runT` of `p.refusingZeroChallenge` (`runTz_rz`), so the
completeness hypothesis `NoZeroChallenge` is an accepting `runTz`; it accepts less than `runT` and
agrees with it where it accepts (`runTz_runT`), and it splits at a `bind` (`runTz_bind`).

The primitives read backwards (`runTz_read`, `runTz_sample_none`, `runTz_sample_some`,
`runTz_grind`, `runTz_commit`, `runTz_query`, `runTz_require`), and the loops of reads and samples
(`runTz_readScalars`, `runTz_sampleChallenges`). `runT_of_runsWith`: a forward run (`RunsWith`) is
the carried run on any rest, so a forward lemma fixes what an accepting run returns.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT TCar fsOfT eq_fsOfT runT_of_runId runId_of_runT tcar_none)

@[expose] public section

/-- **The carried run refusing a zero challenge.** -/
def runTz {α : Type} : VerifierProgram α → TSt → Option (α × TSt)
  | .ret a, s => some (a, s)
  | .fail, _ => none
  | .read k, s => match s.stream, s.ground with
    | x :: xs, none => runTz (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
    | _, _ => none
  | .sample k, s => match s.ground with
    | some c => if c = 0 then none else runTz (k c) { s with ground := none }
    | none => if s.sponge.squeeze.1 = 0 then none
      else runTz (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .grind bits k, s => match s.stream, s.ground with
    | n :: xs, none =>
      if powOk bits (Keccak.lane (s.sponge.nonceState n) 2) then
        runTz k { s with
          sponge := Fs.mk (capOf (s.sponge.nonceState n)) []
          ground := some (challengeOf (s.sponge.nonceState n))
          stream := xs }
      else none
    | _, _ => none
  | .commit height width k, s => match s.stream, s.ground with
    | x0 :: x1 :: xs, none =>
      runTz k { s with
        sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
        stream := xs
        roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)] }
    | _, _ => none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => runTz (k rows) { s with openings := rest }
      | none => none
    | _, _ => none

variable {α β : Type}


/-- **`runTz` is the carried run of the program refusing zero challenges.** -/
theorem runTz_rz (p : VerifierProgram α) : ∀ st, runTz p st = runT p.refusingZeroChallenge st := by
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
    | none =>
      simp only [runTz, runT, VerifierProgram.refusingZeroChallenge]
      by_cases h0 : s.squeeze.1 = 0
      · simp only [h0, ↓reduceIte, runT]
      · simp only [h0, ↓reduceIte]; exact ih _ _
    | some c =>
      simp only [runTz, runT, VerifierProgram.refusingZeroChallenge]
      by_cases h0 : c = 0
      · simp only [h0, ↓reduceIte, runT]
      · simp only [h0, ↓reduceIte]; exact ih _ _
  | grind b k ih =>
    intro st
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g with
    | [], _ => rfl
    | _ :: _, some _ => rfl
    | n :: xs, none =>
      simp only [runTz, runT, VerifierProgram.refusingZeroChallenge]
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
    | none => simp [runTz, runT, VerifierProgram.refusingZeroChallenge, hR]
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runTz, runT, VerifierProgram.refusingZeroChallenge, hR]
      | cons phase rest =>
        simp only [runTz, runT, VerifierProgram.refusingZeroChallenge, hR]
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp only
        | some rows => simp only; exact ih rows _

/-- **An accepting `runTz` is an accepting run.** -/
theorem runTz_runT (p : VerifierProgram α) : ∀ st r, runTz p st = some r → runT p st = some r := by
  induction p with
  | ret a => intro st r h; exact h
  | fail => intro st r h; simp [runTz] at h
  | read k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTz] at h
    | _ :: _, some _, h => simp [runTz] at h
    | x :: xs, none, h => exact ih x _ r h
  | sample k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases g with
    | none =>
      have h' : (if s.squeeze.1 = 0 then none else runTz (k s.squeeze.1) ⟨s.squeeze.2, none, stream, os, R⟩) =
          some r := h
      by_cases h0 : s.squeeze.1 = 0
      · simp [h0] at h'
      · simp only [h0, ↓reduceIte] at h'
        exact ih _ _ r h'
    | some c =>
      have h' : (if c = 0 then none else runTz (k c) ⟨s, none, stream, os, R⟩) = some r := h
      by_cases h0 : c = 0
      · simp [h0] at h'
      · simp only [h0, ↓reduceIte] at h'
        exact ih _ _ r h'
  | grind b k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTz] at h
    | _ :: _, some _, h => simp [runTz] at h
    | n :: xs, none, h =>
      simp only [runTz] at h
      simp only [runT]
      by_cases hp : powOk b (Keccak.lane (s.nonceState n) 2) = true
      · simp only [hp, ↓reduceIte] at h ⊢
        exact ih _ r h
      · simp [hp] at h
  | commit hh ww k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    match stream, g, h with
    | [], _, h => simp [runTz] at h
    | [_], _, h => simp [runTz] at h
    | _ :: _ :: _, some _, h => simp [runTz] at h
    | x0 :: x1 :: xs, none, h => exact ih _ r h
  | query i ps k ih =>
    intro st r h
    obtain ⟨s, g, stream, os, R⟩ := st
    cases hR : R[i]? with
    | none => simp [runTz, hR] at h
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [runTz, hR] at h
      | cons phase rest =>
        simp only [runTz, hR] at h
        simp only [runT, hR]
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp [hop] at h
        | some rows =>
          simp only [hop] at h ⊢
          exact ih rows _ r h

/-- **`runTz` splits at a `bind`.** -/
theorem runTz_bind (p : VerifierProgram α) (f : α → VerifierProgram β) (st : TSt) :
    runTz (p.bind f) st = (runTz p st).bind (fun r ↦ runTz (f r.1) r.2) := by
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
    | none =>
      show (if _ then none else _) = (if _ then none else _).bind _
      by_cases h0 : s.squeeze.1 = 0
      · simp only [h0, ↓reduceIte]; rfl
      · simp only [h0, ↓reduceIte]; exact ih _ _
    | some c =>
      show (if _ then none else _) = (if _ then none else _).bind _
      by_cases h0 : c = 0
      · simp only [h0, ↓reduceIte]; rfl
      · simp only [h0, ↓reduceIte]; exact ih _ _
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
    | none => simp [VerifierProgram.bind, runTz, hR]
    | some v =>
      obtain ⟨root, height, width⟩ := v
      cases os with
      | nil => simp [VerifierProgram.bind, runTz, hR]
      | cons phase rest =>
        simp only [VerifierProgram.bind, runTz, hR]
        cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
            phase) with
        | none => simp only; rfl
        | some rows => simp only; exact ih rows _

/-- An accepting run of a sequence: its first part's, then the rest's. -/
theorem runTz_bind_some {p : VerifierProgram α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runTz (p.bind f) st = some r) :
    ∃ a st1, runTz p st = some (a, st1) ∧ runTz (f a) st1 = some r := by
  rw [runTz_bind] at h
  obtain ⟨⟨a, st1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, st1, h1, h2⟩

/-! ## The primitives, backwards -/

theorem runTz_read {k : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTz (.read k) st = some r) :
    ∃ x xs, st.stream = x :: xs ∧ st.ground = none ∧
      runTz (k x) ⟨st.sponge.absorb x dsObserve, none, xs, st.openings, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  rcases stream with _ | ⟨x, xs⟩ <;> rcases g with _ | c <;> simp only [runTz, reduceCtorEq] at h
  exact ⟨x, xs, rfl, rfl, h⟩

theorem runTz_sample_none {k : E → VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTz (.sample k) st = some r) (hg : st.ground = none) :
    st.sponge.squeeze.1 ≠ 0 ∧
      runTz (k st.sponge.squeeze.1) ⟨st.sponge.squeeze.2, none, st.stream, st.openings, st.roots⟩ =
        some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  simp only [runTz] at h
  split_ifs at h with h0
  exact ⟨h0, h⟩

theorem runTz_sample_some {k : E → VerifierProgram α} {st : TSt} {r : α × TSt} {c : E}
    (h : runTz (.sample k) st = some r) (hg : st.ground = some c) :
    c ≠ 0 ∧ runTz (k c) ⟨st.sponge, none, st.stream, st.openings, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  simp only at hg
  subst hg
  simp only [runTz] at h
  split_ifs at h with h0
  exact ⟨h0, h⟩

theorem runTz_grind {b : ℕ} {k : VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTz (.grind b k) st = some r) :
    ∃ n xs, st.stream = n :: xs ∧ st.ground = none ∧
      powOk b (Keccak.lane (st.sponge.nonceState n) 2) = true ∧
      runTz k ⟨⟨capOf (st.sponge.nonceState n), []⟩, some (challengeOf (st.sponge.nonceState n)), xs,
        st.openings, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  rcases stream with _ | ⟨n, xs⟩ <;> rcases g with _ | c <;> simp only [runTz, reduceCtorEq] at h
  split_ifs at h with hp
  exact ⟨n, xs, rfl, rfl, hp, h⟩

theorem runTz_commit {hh ww : ℕ} {k : VerifierProgram α} {st : TSt} {r : α × TSt}
    (h : runTz (.commit hh ww k) st = some r) :
    ∃ x0 x1 xs, st.stream = x0 :: x1 :: xs ∧ st.ground = none ∧
      runTz k ⟨(st.sponge.absorb x0 dsObserve).absorb x1 dsObserve, none, xs, st.openings,
        st.roots ++ [(digestFromHalves (x0, x1), hh, ww)]⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  rcases stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩ <;> rcases g with _ | c <;>
    simp only [runTz, reduceCtorEq] at h
  exact ⟨x0, x1, xs, rfl, rfl, h⟩

theorem runTz_query {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runTz (.query i ps k) st = some r) :
    ∃ root height width phase rest rows, st.roots[i]? = some (root, height, width) ∧
      st.openings = phase :: rest ∧
      Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) = some rows ∧
      runTz (k rows) ⟨st.sponge, st.ground, st.stream, rest, st.roots⟩ = some r := by
  obtain ⟨s, g, stream, os, R⟩ := st
  cases hR : R[i]? with
  | none => simp [runTz, hR] at h
  | some v =>
    obtain ⟨root, height, width⟩ := v
    cases os with
    | nil => simp [runTz, hR] at h
    | cons phase rest =>
      simp only [runTz, hR] at h
      cases hop : Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps
          phase) with
      | none => simp [hop] at h
      | some rows =>
        simp only [hop] at h
        exact ⟨root, height, width, phase, rest, rows, rfl, rfl, hop, h⟩

theorem runTz_require {c : Prop} [Decidable c] {f : Unit → VerifierProgram α} {st : TSt}
    {r : α × TSt} (h : runTz ((VerifierProgram.require c).bind f) st = some r) :
    c ∧ runTz (f ()) st = some r := by
  unfold VerifierProgram.require at h
  split_ifs at h with hc
  · exact ⟨hc, h⟩
  · simp [VerifierProgram.bind, runTz] at h

theorem runTz_ret_inv {a : α} {st : TSt} {r : α × TSt} (h : runTz (.ret a) st = some r) :
    r = (a, st) := (Option.some.inj h).symm

/-! ## Loops of reads and samples -/

/-- `n` reads, backwards: the words, absorbed. -/
theorem runTz_readScalars {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runTz ((VerifierProgram.readScalars n).bind f) st = some r →
      ∃ ys xs, ys.length = n ∧ st.stream = ys ++ xs ∧
        runTz (f ys) ⟨st.sponge.absorbAll ys dsObserve, none, xs, st.openings, st.roots⟩ = some r
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
    obtain ⟨x, xs, hs, -, h1⟩ := runTz_read h
    obtain ⟨ys, zs, hl, hz, h2⟩ := runTz_readScalars n _ r rfl h1
    simp only at hz
    refine ⟨x :: ys, zs, by simp [hl], by rw [hs, hz]; rfl, ?_⟩
    exact h2

/-- `n` samples from no ground, backwards: the squeezes, none zero. -/
theorem runTz_sampleChallenges {f : List E → VerifierProgram α} :
    ∀ (n : ℕ) (st : TSt) (r : α × TSt), st.ground = none →
      runTz ((VerifierProgram.sampleChallenges n).bind f) st = some r →
      (∀ c ∈ (st.sponge.squeezeN n).1, c ≠ 0) ∧
        runTz (f (st.sponge.squeezeN n).1)
          ⟨(st.sponge.squeezeN n).2, none, st.stream, st.openings, st.roots⟩ = some r
  | 0, st, r, hg, h => by
    refine ⟨by simp [Fs.squeezeN], ?_⟩
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
    obtain ⟨h0, h1⟩ := runTz_sample_none h hg
    obtain ⟨hnz, h2⟩ := runTz_sampleChallenges n _ r rfl h1
    refine ⟨?_, h2⟩
    intro c hc
    simp only [Fs.squeezeN, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact h0
    · exact hnz c hc

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

/-- **An accepting `runTz` returns what a forward run of the same program does.** -/
theorem runTz_det {p : VerifierProgram α} {F F' : Fs} {xs : List E}
    {os : List (List Opening)} {R R' : List (Digest × ℕ × ℕ)} {a b : α} {rest : List E}
    {orest : List (List Opening)} {st1 : TSt}
    (h : runTz p ⟨F, none, xs ++ rest, os ++ orest, R⟩ = some (b, st1))
    (hf : RunsWith p F xs os R a F' R') (hc : ∃ sp, F.Carries sp) :
    b = a ∧ st1 = ⟨F', none, rest, orest, R'⟩ := by
  have e1 := runTz_runT p _ _ h
  rw [runT_of_runsWith hf hc rest orest] at e1
  simp only [Option.some.injEq, Prod.mk.injEq] at e1
  exact ⟨e1.1.symm, e1.2.symm⟩

/-- A run from a carried sponge leaves a carried one. -/
theorem runTz_carries {p : VerifierProgram α} {st st' : TSt} {a : α}
    (h : runTz p st = some (a, st')) (hc : ∃ sp, TCar st.sponge st.ground sp) :
    ∃ sp, TCar st'.sponge st'.ground sp := by
  obtain ⟨sp, hsp⟩ := hc
  obtain ⟨sp', hc', -⟩ := runId_of_runT p st sp hsp a st' (runTz_runT p st _ h)
  exact ⟨sp', hc'⟩

end
end LeanVM.Guest.B1.Whir
