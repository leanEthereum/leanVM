/-
  LeanVM.Guest.Child.Range

  The verifier program opens every commitment at positions below its leaf count, and a refining
  program's query steps are the refined one's.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.B1.VerifySub.NZBridge
public import LeanVM.Guest.Child.Fresh
public import LeanVM.Guest.Child.Reads
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# Query positions in range

`InRange p hs Q`: along every run of `p`, from commitments of heights `hs`, every query of
commitment `i` asks positions below `2^hs[i]`, and every value returned satisfies `Q` at the
heights then committed. The leanVM verifier program satisfies it from no commitment
(`inRange_leanVmProgram`): its only commitments are the stack's and the WHIR levels', and WHIR's
level `ℓ` samples its positions modulo `2^depth` (`sampleQueries`), `depth` the height of
commitment `ℓ` (`inRange_whirLevels`).

`queriesOf_le`: a refining program (`VerifierProgram.Le`) makes a subset of the query steps of the
program it refines, so the deferring program's are among the verifier's.
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {α β : Type}

/-! ## Refinement keeps the query steps -/

/-- **A refining program's query steps are the refined one's.** -/
theorem queriesOf_le {p q : VerifierProgram α} (hpq : VerifierProgram.Le p q) :
    ∀ {st : VerifierProgramState} {b}, b ∈ Limits.queryStepsOf p st → b ∈ Limits.queryStepsOf q
        st := by
  induction hpq with
  | fail q => intro st b h; simp [Limits.queryStepsOf] at h
  | ret a => intro st b h; exact h
  | read _ ih =>
    intro st b h
    obtain ⟨⟨S, pend, g⟩, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [Limits.queryStepsOf] at h
    | cons x xs =>
      cases g with
      | none => exact ih x h
      | some c => simp [Limits.queryStepsOf] at h
  | sample _ ih => intro st b h; simp only [Limits.queryStepsOf] at h ⊢; exact ih _ h
  | grind bits _ ih =>
    intro st b h
    obtain ⟨⟨S, pend, g⟩, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [Limits.queryStepsOf] at h
    | cons n xs =>
      cases g with
      | some c => simp [Limits.queryStepsOf] at h
      | none =>
        revert h
        simp only [Limits.queryStepsOf]
        generalize Id.run (absorbNonce keccakF1600 ⟨S, pend, none⟩ n) = r
        obtain ⟨pow, sp'⟩ := r
        dsimp only
        by_cases hc : powOk bits pow = true
        · simp only [hc, ↓reduceIte]
          exact fun h ↦ ih h
        · simp [hc]
  | commit height width _ ih =>
    intro st b h
    obtain ⟨⟨S, pend, g⟩, stream, os, roots⟩ := st
    match stream, g, h with
    | [], _, h => simp [Limits.queryStepsOf] at h
    | [_], _, h => simp [Limits.queryStepsOf] at h
    | _ :: _ :: _, some _, h => simp [Limits.queryStepsOf] at h
    | x0 :: x1 :: xs, none, h => exact ih h
  | query i ps _ ih =>
    intro st b h
    obtain ⟨sp, stream, os, roots⟩ := st
    cases hr : roots[i]? with
    | none => simp [Limits.queryStepsOf, hr] at h
    | some x =>
      obtain ⟨root, height, width⟩ := x
      cases os with
      | nil => simp [Limits.queryStepsOf, hr] at h
      | cons phase rest =>
        simp only [Limits.queryStepsOf, hr] at h ⊢
        cases ho : Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) with
        | none => simp [ho] at h
        | some rows =>
          simp only [ho] at h ⊢
          rcases List.mem_cons.mp h with h | h
          · exact List.mem_cons.mpr (Or.inl h)
          · exact List.mem_cons_of_mem _ (ih rows h)

/-! ## The calculus -/

/-- **Queries in range**: along every run of `p` from commitments of heights `hs`, every query
asks positions below `2^` its commitment's height, and every value returned satisfies `Q` at the
heights then committed. -/
def InRange : VerifierProgram α → List ℕ → (α → List ℕ → Prop) → Prop
  | .ret a, hs, Q => Q a hs
  | .fail, _, _ => True
  | .read k, hs, Q => ∀ x, InRange (k x) hs Q
  | .sample k, hs, Q => ∀ c, InRange (k c) hs Q
  | .grind _ k, hs, Q => InRange k hs Q
  | .commit ht _ k, hs, Q => InRange k (hs ++ [ht]) Q
  | .query i ps k, hs, Q => (∀ q ∈ ps, q < 2 ^ hs.getD i 0) ∧ ∀ rows, InRange (k rows) hs Q

namespace InRange

theorem mono {p : VerifierProgram α} {hs : List ℕ} {Q R : α → List ℕ → Prop} (h : InRange p hs Q)
    (hQR : ∀ a hs', Q a hs' → R a hs') : InRange p hs R := by
  induction p generalizing hs with
  | ret a => exact hQR a hs h
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (h x)
  | sample k ih => exact fun x ↦ ih x (h x)
  | grind b k ih => exact ih h
  | commit ht w k ih => exact ih h
  | query i ps k ih => exact ⟨h.1, fun r ↦ ih r (h.2 r)⟩

theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {hs : List ℕ} {Q : α → List ℕ
    → Prop}
    {R : β → List ℕ → Prop} (hp : InRange p hs Q) (hf : ∀ a hs', Q a hs' → InRange (f a) hs' R) :
    InRange (p.bind f) hs R := by
  induction p generalizing hs with
  | ret a => exact hf a hs hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact ⟨hp.1, fun r ↦ ih r (hp.2 r)⟩

/-- A program without commitments or queries keeps the heights. -/
theorem of_noCommitA : ∀ {p : VerifierProgram α} {hs : List ℕ}, NoCommitA p →
    InRange p hs fun a hs' ↦ hs' = hs ∧ VerifierProgram.Returns p a := by
  intro p
  induction p with
  | ret a => intro hs _; exact ⟨rfl, .ret a⟩
  | fail => intro hs _; trivial
  | read k ih =>
    intro hs h x
    exact (ih x (h x)).mono fun a hs' hr ↦ ⟨hr.1, .read x hr.2⟩
  | sample k ih =>
    intro hs h x
    exact (ih x (h x)).mono fun a hs' hr ↦ ⟨hr.1, .sample x hr.2⟩
  | grind b k ih =>
    intro hs h
    exact (ih h).mono fun a hs' hr ↦ ⟨hr.1, .grind b hr.2⟩
  | commit _ _ _ _ => intro hs h; exact h.elim
  | query _ _ _ _ => intro hs h; exact h.elim

theorem of_noCommit {p : VerifierProgram α} {hs : List ℕ} (h : NoCommit p) :
    InRange p hs fun a hs' ↦ hs' = hs ∧ VerifierProgram.Returns p a :=
  of_noCommitA ((noCommit_iff _).1 h)

/-- A program without commitments or queries, followed by one in range. -/
theorem nc_bind {p : VerifierProgram α} {f : α → VerifierProgram β} {hs : List ℕ} {R : β → List ℕ
    → Prop}
    (hp : NoCommit p) (hf : ∀ a, VerifierProgram.Returns p a → InRange (f a) hs R) :
    InRange (p.bind f) hs R :=
  bind (of_noCommit hp) fun a _ h ↦ h.1 ▸ hf a h.2

end InRange

/-! ## WHIR -/

/-- A fold round adds one `α`. -/
theorem foldRound_returns {s : WhirState} {p : WhirState × FoldRound}
    (h : VerifierProgram.Returns (foldRound s) p) : p.1.alphas.length = s.alphas.length + 1 := by
  unfold foldRound at h
  repeat (obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h)
  rw [VerifierProgram.returns_ret h]
  simp

/-- A level's fold rounds add one `α` each. -/
theorem foldRounds_returns : ∀ {n : ℕ} {s : WhirState} {p : WhirState × List FoldRound},
    VerifierProgram.Returns (foldRounds n s) p → p.1.alphas.length = s.alphas.length + n
  | 0, s, p, h => by
    rw [foldRounds] at h
    rw [VerifierProgram.returns_ret h]
    rfl
  | n + 1, s, p, h => by
    rw [foldRounds] at h
    obtain ⟨⟨s', r⟩, h1, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨⟨s'', rs⟩, h2, h⟩ := VerifierProgram.returns_bind h
    rw [VerifierProgram.returns_ret h]
    rw [foldRounds_returns h2, foldRound_returns h1]
    omega

theorem noCommit_foldRound (s : WhirState) : NoCommit (foldRound s) := by
  unfold foldRound
  nc

theorem noCommit_foldRounds : ∀ (n : ℕ) (s : WhirState), NoCommit (foldRounds n s)
  | 0, _ => noCommit_ret _
  | n + 1, s => by
    unfold foldRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind (noCommit_foldRound s) fun p ↦ ?_
    obtain ⟨s', r⟩ := p
    refine NoCommit.bind (noCommit_foldRounds n s') fun q ↦ ?_
    obtain ⟨s'', rs⟩ := q
    exact noCommit_ret _

theorem noCommit_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    NoCommit (sampleQueriesAux depth fuel remaining)
  | 0, _ => noCommit_ret _
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    split
    · exact noCommit_ret _
    · exact NoCommit.bind noCommit_sampleE fun _ ↦ NoCommit.bind
        (noCommit_sampleQueriesAux depth fuel _) fun _ ↦ noCommit_ret _

theorem sampleQueriesAux_returns (depth : ℕ) : ∀ (fuel remaining : ℕ) {qs : List ℕ},
    VerifierProgram.Returns (sampleQueriesAux depth fuel remaining) qs → ∀ q ∈ qs, q < 2 ^ depth
  | 0, _, qs, h => by
    have := VerifierProgram.returns_ret h
    subst this
    simp
  | fuel + 1, remaining, qs, h => by
    unfold sampleQueriesAux at h
    split at h
    · have := VerifierProgram.returns_ret h
      subst this
      simp
    · obtain ⟨c, -, h⟩ := VerifierProgram.returns_bind h
      obtain ⟨rest, hrest, h⟩ := VerifierProgram.returns_bind h
      have := VerifierProgram.returns_ret h
      subst this
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hq
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · exact sampleQueriesAux_returns depth fuel _ hrest q hq

/-- **The WHIR levels open in range**: at level `index`, the heights so far end with the
current level's, `logN − αs − fold + rate`. -/
theorem inRange_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (hs : List ℕ),
      hs.length = index + 1 →
      (∀ level ∈ levels.head?,
        hs.getD index 0 = logN - s.alphas.length - level.fold + level.logInvRate) →
      InRange (whirLevels logN laneFolds evaluateBasis index levels s) hs fun _ _ ↦ True
  | [], _, _, _, _, _ => trivial
  | level :: rest, index, s, hs, hl, hh => by
    have hh' := hh level rfl
    unfold whirLevels
    simp only [VerifierProgram.bind_eq]
    refine InRange.nc_bind (noCommit_foldRounds _ _) fun r hr ↦ ?_
    obtain ⟨s', rounds⟩ := r
    have hf := foldRounds_returns hr
    dsimp only at hf ⊢
    have hdepth : logN - s'.alphas.length + level.logInvRate = hs.getD index 0 := by
      rw [hh', hf]; omega
    cases rest with
    | nil =>
      dsimp only
      refine InRange.nc_bind (noCommit_readN _) fun _ _ ↦ ?_
      refine InRange.nc_bind (noCommit_grind _) fun _ _ ↦ ?_
      refine InRange.nc_bind (p := sampleQueries _ level.queries)
        (noCommit_sampleQueriesAux _ _ _) fun queries hq ↦ ?_
      refine ⟨fun q hqq ↦ ?_, fun words ↦ ?_⟩
      · rw [← hdepth]
        exact sampleQueriesAux_returns _ _ _ hq q hqq
      · refine InRange.nc_bind (noCommit_ret _) fun _ _ ↦ ?_
        refine InRange.nc_bind (noCommit_require _) fun _ _ ↦ ?_
        refine InRange.nc_bind (noCommit_sumcheck _ _ _) fun _ _ ↦ ?_
        exact (InRange.of_noCommit (noCommit_require _)).mono fun _ _ _ ↦ trivial
    | cons next rest' =>
      dsimp only
      simp only [levelShape]
      have hc : InRange (VerifierProgram.readCommitment (logN - s'.alphas.length - next.fold +
          next.logInvRate) (2 * 2 ^ next.fold)) hs
          (fun _ hs' ↦ hs' = hs ++ [logN - s'.alphas.length - next.fold + next.logInvRate]) :=
        rfl
      refine InRange.bind (Q := fun (_ : Unit) hs' ↦
        hs' = hs ++ [logN - s'.alphas.length - next.fold + next.logInvRate]) hc fun _ _ e ↦ ?_
      subst e
      have hgi : (hs ++ [logN - s'.alphas.length - next.fold + next.logInvRate]).getD index 0 =
          hs.getD index 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      refine InRange.nc_bind (noCommit_readN _) fun _ _ ↦ ?_
      refine InRange.nc_bind (noCommit_grind _) fun _ _ ↦ ?_
      refine InRange.nc_bind (noCommit_sampleN _) fun _ _ ↦ ?_
      refine InRange.nc_bind noCommit_readE fun _ _ ↦ ?_
      refine InRange.nc_bind (noCommit_grind _) fun _ _ ↦ ?_
      refine InRange.nc_bind (p := sampleQueries _ level.queries)
        (noCommit_sampleQueriesAux _ _ _) fun queries hq ↦ ?_
      refine InRange.nc_bind (p := VerifierProgram.sampleChallenge) noCommit_sampleE fun lam _ ↦ ?_
      refine ⟨fun q hqq ↦ ?_, fun words ↦ ?_⟩
      · rw [hgi, ← hdepth]
        exact sampleQueriesAux_returns _ _ _ hq q hqq
      · refine inRange_whirLevels logN laneFolds evaluateBasis (next :: rest') (index + 1) _ _
          (by simp [hl]) fun lv hlv ↦ ?_
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
        subst hlv
        rw [glueLevel_alphas]
        simp [List.getD_eq_getElem?_getD, hl]

/-! ## The verifier program -/

theorem noCommit_busRest_computed (L : Layout) (weights : List E) (beta : E) (point tv : List E) :
    NoCommit (LeanVM.Guest.B1.Tables.busRest computedBytecodeValue L weights beta point tv) := by
  unfold LeanVM.Guest.B1.Tables.busRest
  simp only [computedBytecodeValue, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_readN _) fun _ ↦ ?_
  refine NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind noCommit_readE fun _ ↦ ?_
  refine NoCommit.bind (noCommit_bytecodeShare _ _) fun _ ↦ ?_
  nc

theorem noCommit_verifyBusBalance_computed (layout : Layout) :
    NoCommit (verifyBusBalance computedBytecodeValue layout) := by
  rw [verifyBusBalance_split]
  exact NoCommit.bind (noCommit_require _) fun _ ↦ NoCommit.bind (noCommit_grind _) fun _ ↦
    NoCommit.bind (noCommit_sampleN _) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦
    NoCommit.bind (noCommit_gkrPhase _) fun _ ↦ noCommit_busRest_computed _ _ _ _ _

/-- The stack's commitment: the height of the ladder's first level. -/
theorem inRange_commitStack (μ r : ℕ) (hs : List ℕ) :
    InRange (commitStack μ r) hs fun _ hs' ↦ ∃ level rest,
      Whir.ladder μ r = some (level :: rest) ∧ hs' = hs ++ [μ - level.fold + level.logInvRate] := by
  unfold commitStack
  refine InRange.nc_bind (noCommit_liftOption _) fun config hc ↦ ?_
  have hc' : Whir.ladder μ r = some config := by
    unfold Verifier.liftOption at hc
    split at hc
    · cases hc
    · next a ha => rw [VerifierProgram.returns_ret hc]; exact ha
  cases config with
  | nil => trivial
  | cons level rest => exact ⟨level, rest, hc', rfl⟩

/-- The stacked opening opens in range, the stack committed at the ladder's first level. -/
theorem inRange_verifyStackedOpening {μ r : ℕ} {level : Whir.Level} {rest : List Whir.Level}
    (hcfg : Whir.ladder μ r = some (level :: rest)) (cl : List StackClaim) :
    InRange (verifyStackedOpening μ r cl) [μ - level.fold + level.logInvRate] fun _ _ ↦ True := by
  unfold verifyStackedOpening verifyWhir
  simp only [VerifierProgram.bind_eq]
  refine InRange.nc_bind (noCommit_require _) fun _ _ ↦ ?_
  refine InRange.nc_bind noCommit_sampleE fun _ _ ↦ ?_
  refine InRange.nc_bind (noCommit_liftOption _) fun config hc ↦ ?_
  have hc' : Whir.ladder μ r = some config := by
    unfold Verifier.liftOption at hc
    split at hc
    · cases hc
    · next a ha => rw [VerifierProgram.returns_ret hc]; exact ha
  rw [hcfg] at hc'
  cases hc'
  refine inRange_whirLevels _ _ _ _ 0 _ _ rfl fun lv hlv ↦ ?_
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
  subst hlv
  simp

/-- **The verifier program opens in range**, from no commitment. -/
theorem inRange_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    InRange (leanVmVerifierProgram bytecode publicInput) [] fun _ _ ↦ True := by
  rw [leanVmProgram_eq]
  refine InRange.bind (Q := fun _ _ ↦ True) ?_ fun _ _ _ ↦ trivial
  unfold verifyExecutionClaims
  simp only [VerifierProgram.bind_eq]
  refine InRange.nc_bind (noCommit_readSizes _) fun ls _ ↦ ?_
  obtain ⟨layout, rate⟩ := ls
  dsimp only
  refine InRange.bind (inRange_commitStack _ _ []) fun _ hs' hc ↦ ?_
  obtain ⟨level, rest, hcfg, rfl⟩ := hc
  rw [List.nil_append]
  refine InRange.nc_bind (noCommit_readOod _) fun ood _ ↦ ?_
  refine InRange.nc_bind (noCommit_verifyBusBalance_computed _) fun _ _ ↦ ?_
  refine InRange.nc_bind (noCommit_tablePhase _ _) fun _ _ ↦ ?_
  refine InRange.nc_bind (noCommit_publicInputPhase _ _) fun _ _ ↦ ?_
  refine InRange.nc_bind (noCommit_keccakPhaseClaims _ _) fun kc _ ↦ ?_
  obtain ⟨cl, kp, ks⟩ := kc
  dsimp only
  -- Elaborating `InRange` at `ringSwitch kp ks` itself is slow: name it first.
  have hrs := noCommit_ringSwitch kp ks
  generalize ringSwitch kp ks = rsw at hrs ⊢
  exact InRange.nc_bind hrs fun _ _ ↦ inRange_verifyStackedOpening hcfg _

end
end LeanVM.Guest.Child
