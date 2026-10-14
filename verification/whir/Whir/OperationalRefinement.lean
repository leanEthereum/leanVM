import Whir.ReplayRefinement

/-! Operational refinement of the untrusted verifier. These are the kernels called
by `Protocol.verify`, not a second verifier or an honest transcript relation.
No field laws for `Concrete.E` are assumed. Ring interpretation of these very
fold/batch operations is provided separately by `ReplayRefinement`; transporting
it to the concrete field remains the field bridge's responsibility. -/
namespace Whir.OperationalRefinement
open Concrete Protocol

private theorem except_pure {S : Type*} (s : S) :
    (pure s : Except String S) = .ok s := rfl

private theorem except_bind_ok {S T : Type u} (s : S) (f : S → Except String T) :
    (Except.ok s >>= f) = f s := rfl

private theorem except_bind_error {S T : Type u} (e : String) (f : S → Except String T) :
    (Except.error e >>= f) = .error e := rfl

private theorem except_throw {S : Type*} (e : String) :
    (throw e : Except String S) = .error e := rfl

attribute [local simp] except_pure except_bind_ok except_bind_error except_throw

/-- Indexed recursion has precisely the left-to-right list-fold meaning. -/
theorem runSteps_eq_foldl {S : Type*} (step : Nat → S → S)
    (count start : Nat) (s : S) :
    runSteps step count start s =
      (List.range' start count).foldl (fun s i => step i s) s := by
  induction count generalizing start s with
  | zero => simp [runSteps]
  | succ count ih => simp [runSteps, List.range'_succ, ih]

/-- Checked recursion has the same short-circuit/error order as monadic fold. -/
theorem runChecked_eq_foldlM {S : Type*} (step : Nat → S → Except String S)
    (count start : Nat) (s : S) :
    runChecked step count start s =
      (List.range' start count).foldlM (fun s i => step i s) s := by
  induction count generalizing start s with
  | zero => simp [runChecked]
  | succ count ih => simp [runChecked, List.range'_succ, ih]

/-- An invariant may depend on the exact next challenge index. Messages are
unrestricted; callers can use a lost-invariant or bad-event-conditioned predicate. -/
theorem runSteps_invariant {S : Type*} (step : Nat → S → S)
    (P : Nat → S → Prop) (count start : Nat) (s : S)
    (initial : P start s)
    (preserve : ∀ i t, start ≤ i → i < start + count → P i t → P (i+1) (step i t)) :
    P (start + count) (runSteps step count start s) := by
  induction count generalizing start s with
  | zero => simpa [runSteps] using initial
  | succ count ih =>
    simp only [runSteps]
    have first := preserve start s (by omega) (by omega) initial
    have rest := ih (start+1) (step start s) first (by
      intro i t lo hi h
      exact preserve i t (by omega) (by omega) h)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest

/-- Successful checked execution preserves any index-dependent invariant for
which each successful actual transition has the required implication. -/
theorem runChecked_invariant {S : Type*} (step : Nat → S → Except String S)
    (P : Nat → S → Prop) (count start : Nat) (s finish : S)
    (initial : P start s)
    (preserve : ∀ i t u, start ≤ i → i < start + count →
      P i t → step i t = .ok u → P (i+1) u)
    (success : runChecked step count start s = .ok finish) :
    P (start + count) finish := by
  induction count generalizing start s with
  | zero =>
    simp only [runChecked, Except.ok.injEq] at success
    subst finish
    simpa using initial
  | succ count ih =>
    cases h : step start s with
    | error e => simp [runChecked, h] at success
    | ok next =>
      have first := preserve start s next (by omega) (by omega) initial h
      have rest := ih (start+1) next first (by
        intro i t u lo hi ht hu
        exact preserve i t u (by omega) (by omega) ht hu)
        (by simpa [runChecked, h] using success)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using rest

/-- Successful checked executions expose every actual intermediate transition. -/
inductive CheckedTrace {S : Type*} (step : Nat → S → Except String S) :
    Nat → Nat → S → S → Prop
  | done (start : Nat) (s : S) : CheckedTrace step 0 start s s
  | next {count start : Nat} {s t finish : S}
      (transition : step start s = .ok t)
      (rest : CheckedTrace step count (start+1) t finish) :
      CheckedTrace step (count+1) start s finish

theorem runChecked_ok_iff_trace {S : Type*} (step : Nat → S → Except String S)
    (count start : Nat) (s finish : S) :
    runChecked step count start s = .ok finish ↔
      CheckedTrace step count start s finish := by
  induction count generalizing start s with
  | zero =>
    constructor
    · intro h
      simp only [runChecked, Except.ok.injEq] at h
      subst finish
      exact .done _ _
    · intro h
      cases h
      rfl
  | succ count ih =>
    constructor
    · intro h
      cases hs : step start s with
      | error e => simp [runChecked, hs] at h
      | ok t => exact .next hs ((ih _ _).mp (by simpa [runChecked, hs] using h))
    · intro h
      cases h with
      | next transition rest => simpa [runChecked, transition] using (ih _ _).mpr rest

/-- Exact concrete Boolean check, with no use of `CommRing E` or a field axiom. -/
theorem checkClosing_ok_iff (ch : Challenges) (proof : Opening) (s : VerifierState E) :
    checkClosing ch proof s = .ok () ↔
      s.checkTerminal (Concrete.mle proof.residual ch.tail) = true := by
  cases h : s.checkTerminal (Concrete.mle proof.residual ch.tail) <;> simp [checkClosing, h]

/-- Acceptance of arbitrary untrusted messages entails a successful trace of the
actual checked levels and the actual residual-MLE terminal comparison. -/
theorem verify_ok_iff (c : Config) (ch : Challenges) (lanes : Nat) (root : Oracle)
    (b : Array E) (target : E) (proof : Opening) :
    verify c ch lanes root b target proof = .ok () ↔
      ∃ initial finish,
        initializeVerifier c ch lanes root b target proof = .ok initial ∧
        CheckedTrace (verifyLevel c ch proof) c.folds.size 0 initial finish ∧
        (closeTail ch proof finish.state).checkTerminal (Concrete.mle proof.residual ch.tail) = true := by
  simp only [verify, replayLevels, ← runChecked_ok_iff_trace]
  cases hi : initializeVerifier c ch lanes root b target proof with
  | error e => simp
  | ok initial =>
    cases hf : runChecked (verifyLevel c ch proof) c.folds.size 0 initial with
    | error e => simp [hf]
    | ok finish => simp [hf, checkClosing_ok_iff]

/-- A false terminal comparison rejects through `verify` itself, not through a
standalone mathematical checker. Earlier failures remain their own errors. -/
theorem verify_terminal_rejection (c : Config) (ch : Challenges) (lanes : Nat)
    (root : Oracle) (b : Array E) (target : E) (proof : Opening)
    (initial finish : CheckedState)
    (hi : initializeVerifier c ch lanes root b target proof = .ok initial)
    (hf : replayLevels c ch proof initial = .ok finish)
    (bad : (closeTail ch proof finish.state).checkTerminal
      (Concrete.mle proof.residual ch.tail) = false) :
    verify c ch lanes root b target proof = .error "terminal mismatch" := by
  simp [verify, hi, hf, checkClosing, bad]

/-- The outer invariant rule applies directly to actual accepted openings. -/
theorem accepted_levels_invariant (c : Config) (ch : Challenges) (lanes : Nat)
    (root : Oracle) (b : Array E) (target : E) (proof : Opening)
    (P : Nat → CheckedState → Prop)
    (initial : ∀ s, initializeVerifier c ch lanes root b target proof = .ok s → P 0 s)
    (preserve : ∀ i s t, i < c.folds.size → P i s →
      verifyLevel c ch proof i s = .ok t → P (i+1) t)
    (accepted : verify c ch lanes root b target proof = .ok ()) :
    ∃ finish, P c.folds.size finish ∧
      (closeTail ch proof finish.state).checkTerminal (Concrete.mle proof.residual ch.tail) = true := by
  obtain ⟨s, t, hi, trace, terminal⟩ := (verify_ok_iff c ch lanes root b target proof).mp accepted
  refine ⟨t, ?_, terminal⟩
  simpa only [Nat.zero_add] using runChecked_invariant (verifyLevel c ch proof) P c.folds.size 0 s t (initial s hi)
    (by intro i s t _ hi hs ht; exact preserve i s t (by omega) hs ht)
    ((runChecked_ok_iff_trace _ _ _ _ _).mpr trace)

/-- Fold-block induction uses the supplied next messages, never reconstructed
honest intros. The predicate can track both the remaining dimension and state. -/
theorem foldBlock_invariant (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (P : Nat → CheckedState → Prop) (s : CheckedState) (initial : P 0 s)
    (preserve : ∀ j t, j < cs.folds.size → P j t → P (j+1) (foldStep block cs p j t)) :
    P cs.folds.size (foldBlock block cs p s) := by
  simpa only [foldBlock, Nat.zero_add] using
    runSteps_invariant (foldStep block cs p) P cs.folds.size 0 s initial
      (by intro j t _ hi h; exact preserve j t (by omega) h)

/-- OOD induction retains the precise running power of lambda in the state. -/
theorem oodBatch_invariant (cs : LevelChallenges) (p : LevelProof)
    (P : Nat → VerifierState E × E → Prop) (s : VerifierState E)
    (initial : P 0 (s, E.one))
    (preserve : ∀ j t, j < p.oods.size → P j t → P (j+1) (oodStep cs p j t)) :
    P p.oods.size (oodBatch cs p s) := by
  simpa only [oodBatch, Nat.zero_add] using
    runSteps_invariant (oodStep cs p) P p.oods.size 0 (s, E.one) initial
      (by intro j t _ hi h; exact preserve j t (by omega) h)

/-- Closing induction includes the final fold that deliberately retains the
unused pending message instead of reading an absent tail message. -/
theorem closeTail_invariant (ch : Challenges) (proof : Opening)
    (P : Nat → VerifierState E → Prop) (s : VerifierState E) (initial : P 0 s)
    (preserve : ∀ j t, j < ch.tail.size → P j t → P (j+1) (tailStep ch proof j t)) :
    P ch.tail.size (closeTail ch proof s) := by
  simpa only [closeTail, Nat.zero_add] using
    runSteps_invariant (tailStep ch proof) P ch.tail.size 0 s initial
      (by intro j t _ hi h; exact preserve j t (by omega) h)

/-- Checked unit loops accept exactly when every indexed check accepts. -/
theorem runChecked_unit_ok_iff (step : Nat → Unit → Except String Unit)
    (count start : Nat) :
    runChecked step count start () = .ok () ↔
      ∀ j, start ≤ j → j < start + count → step j () = .ok () := by
  induction count generalizing start with
  | zero =>
    simp only [runChecked, Nat.add_zero, true_iff]
    intro j lo hi
    omega
  | succ count ih =>
    cases h : step start () with
    | error e =>
      simp only [runChecked, h, except_bind_error, reduceCtorEq, false_iff]
      intro all
      have := all start (by omega) (by omega)
      simp [h] at this
    | ok u =>
      cases u
      simp only [runChecked, h, except_bind_ok, ih]
      constructor
      · intro all j lo hi
        by_cases hj : j = start
        · simpa [hj] using h
        · exact all j (by omega) (by omega)
      · intro all j lo hi
        exact all j (by omega) (by omega)

/-- Successful authentication entails the exact comparison used by the actual
verifier for every sampled row, including duplicate samples. -/
theorem authentication_ok_iff (oracle : Oracle) (qs : Array Nat) (p : LevelProof) :
    runChecked (authenticateRow oracle qs p) qs.size 0 () = .ok () ↔
      ∀ j, j < qs.size → (p.rows[j]! != oracle[qs[j]!]!) = false := by
  rw [runChecked_unit_ok_iff]
  simp only [Nat.zero_add, Nat.zero_le, forall_const]
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro _
  cases h : (p.rows[j]! != oracle[qs[j]!]!) <;> simp [authenticateRow, h]

private theorem bind_ok_iff {S T : Type u} (x : Except String S)
    (f : S → Except String T) (t : T) :
    (x >>= f) = .ok t ↔ ∃ s, x = .ok s ∧ f s = .ok t := by
  cases x <;> simp

/-- A successful actual level exposes authenticated queries and its exact
post-batching state. The fold messages and OOD/query intros remain unrestricted. -/
theorem verifyLevel_success (c : Config) (ch : Challenges) (proof : Opening)
    (i : Nat) (s finish : CheckedState)
    (success : verifyLevel c ch proof i s = .ok finish) :
    let cs := ch.levels[i]!
    let p := proof.levels[i]!
    let folded := foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1) cs p s
    p.afterFold.size = cs.folds.size ∧ p.oods.size = cs.oodPoints.size ∧
      ∃ qs, deriveQueries (folded.n+c.rates[i]!) c.queries[i]! cs.querySqueezes = some qs ∧
        p.rows.size = qs.size ∧
        (∀ j, j < qs.size → (p.rows[j]! != folded.oracle[qs[j]!]!) = false) ∧
        finish = ⟨folded.n, queryBatch folded.n i cs p qs (oodBatch cs p folded.state),
          p.nextOracle.getD #[]⟩ := by
  dsimp
  unfold verifyLevel at success
  simp only [except_throw, except_bind_error, except_pure] at success
  generalize hf : foldBlock (if i == 0 then 2^(c.logN-c.folds[0]!) else 1)
    ch.levels[i]! proof.levels[i]! s = folded at success ⊢
  cases hn : proof.levels[i]!.nextOracle <;>
    cases hq : deriveQueries (folded.n+c.rates[i]!) c.queries[i]!
      ch.levels[i]!.querySqueezes
  all_goals
    simp only [hn, hq, Option.elim, except_pure, except_bind_ok,
      except_bind_error] at success
    split_ifs at success <;> simp_all [bind_ok_iff]
  all_goals
    obtain ⟨⟨u, authenticated⟩, _⟩ := success
    cases u
    have auth := (authentication_ok_iff _ _ _).mp authenticated
    intro j hj
    simpa [*] using auth j hj

end Whir.OperationalRefinement
