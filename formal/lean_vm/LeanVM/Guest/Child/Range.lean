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
    obtain ⟨sp, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [Limits.queryStepsOf] at h
    | cons x xs => simp only [Limits.queryStepsOf] at h ⊢; exact ih x h
  | sample _ ih => intro st b h; simp only [Limits.queryStepsOf] at h ⊢; exact ih _ h
  | grind bits _ ih =>
    intro st b h
    obtain ⟨sp, stream, os, roots⟩ := st
    cases stream with
    | nil => simp [Limits.queryStepsOf] at h
    | cons n xs =>
      simp only [Limits.queryStepsOf] at h ⊢
      split at h
      · next hpow => simp only [hpow, ↓reduceIte]; exact ih h
      · simp at h
  | commit height width _ ih =>
    intro st b h
    obtain ⟨sp, stream, os, roots⟩ := st
    match stream, h with
    | [], h => simp [Limits.queryStepsOf] at h
    | [_], h => simp [Limits.queryStepsOf] at h
    | x0 :: x1 :: xs, h =>
      simp only [Limits.queryStepsOf] at h ⊢
      split at h
      · next root hroot => exact ih h
      · simp at h
  | query i ps _ ih =>
    intro st b h
    obtain ⟨sp, stream, os, roots⟩ := st
    simp only [Limits.queryStepsOf] at h ⊢
    cases hr : roots[i]? with
    | none => simp [hr] at h
    | some x =>
      obtain ⟨root, height, width⟩ := x
      cases os with
      | nil => simp [hr] at h
      | cons phase rest =>
        simp only [hr, openPhase_eq_withHash, keccak256With_keccakF1600] at h ⊢
        cases ho : Id.run (openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
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

theorem foldRounds_returns (b : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (lf : List E) {r : WhirStateT × List E},
    VerifierProgram.Returns (foldRoundsT b n s lf) r → r.1.folds.length = s.folds.length + n
  | 0, s, lf, r, h => by
    have := VerifierProgram.returns_ret h
    subst this
    rfl
  | n + 1, s, lf, r, h => by
    unfold foldRoundsT at h
    obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨c, -, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
    have := foldRounds_returns b n _ _ h
    simp only [List.length_append, List.length_singleton] at this
    omega

theorem noCommit_foldProofOfWork (b : ℕ) : NoCommit (VerifierProgram.foldProofOfWork b) := by
  unfold VerifierProgram.foldProofOfWork
  split
  · exact noCommit_ret _
  · exact (noCommit_iff _).2 trivial

theorem noCommit_foldRounds (b : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (lf : List E),
    NoCommit (foldRoundsT b n s lf)
  | 0, _, _ => noCommit_ret _
  | n + 1, s, lf => by
    unfold foldRoundsT
    simp only [VerifierProgram.bind_eq]
    exact NoCommit.bind (noCommit_foldProofOfWork b) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦
      NoCommit.bind (noCommit_sumcheckRoundPoly _ _ _) fun _ ↦ noCommit_foldRounds b n _ _

theorem noCommit_tailRounds : ∀ (n : ℕ) (t : E) (quad : List E), NoCommit (tailRoundsT n t quad)
  | 0, _, _ => noCommit_ret _
  | n + 1, t, quad => by
    unfold tailRoundsT
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoCommit.bind noCommit_sampleE fun _ ↦ ?_
    split
    · exact noCommit_ret _
    · exact NoCommit.bind (noCommit_sumcheckRoundPoly _ _ _) fun _ ↦
        NoCommit.bind (noCommit_tailRounds n _ _) fun _ ↦ noCommit_ret _

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
current level's, `logN − folds − fold + rate`. -/
theorem inRange_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirStateT) (hs : List ℕ),
      hs.length = index + 1 →
      (∀ level ∈ levels.head?,
        hs.getD index 0 = logN - s.folds.length - level.fold + level.logInvRate) →
      InRange (whirLevelsT logN laneFolds evaluateBasis index levels s) hs fun _ _ ↦ True
  | [], _, _, _, _, _ => trivial
  | level :: rest, index, s, hs, hl, hh => by
    have hh' := hh level rfl
    unfold whirLevelsT
    refine InRange.nc_bind (noCommit_foldRounds _ _ _ _) fun r hr ↦ ?_
    obtain ⟨s', levelFolds⟩ := r
    have hf := foldRounds_returns _ _ _ _ hr
    simp only at hf
    have hdepth : logN - s'.folds.length + level.logInvRate = hs.getD index 0 := by
      rw [hh', hf]; omega
    cases rest with
    | nil =>
      refine InRange.nc_bind (noCommit_readN _) fun _ _ ↦ ?_
      refine InRange.nc_bind (p := VerifierProgram.grindProofOfWork Whir.queryGrindingBits)
        ((noCommit_iff _).2 trivial) fun _ _ ↦ ?_
      refine InRange.nc_bind (p := sampleQueries _ level.queries)
        (noCommit_sampleQueriesAux _ _ _) fun queries hq ↦ ?_
      refine InRange.nc_bind (p := VerifierProgram.sampleChallenge) noCommit_sampleE fun lam _ ↦ ?_
      refine ⟨fun q hqq ↦ ?_, fun words ↦ ?_⟩
      · rw [← hdepth]
        exact sampleQueriesAux_returns _ _ _ hq q hqq
      · refine InRange.nc_bind (p := sumcheckRoundPoly 3 _ none)
          (noCommit_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
        refine InRange.nc_bind (p := tailRoundsT _ _ _) (noCommit_tailRounds _ _ _) fun r _ ↦ ?_
        obtain ⟨tf, tg⟩ := r
        exact (InRange.of_noCommit (noCommit_require _)).mono fun _ _ _ ↦ trivial
    | cons next rest' =>
      simp only [VerifierProgram.pure_eq, levelShape]
      have hc : InRange (VerifierProgram.readCommitment (logN - s'.folds.length - next.fold +
          next.logInvRate)
          (3 * 2 ^ next.fold)) hs
          (fun _ hs' ↦ hs' = hs ++ [logN - s'.folds.length - next.fold + next.logInvRate]) :=
        rfl
      refine InRange.bind (Q := fun (_ : Unit) hs' ↦
        hs' = hs ++ [logN - s'.folds.length - next.fold + next.logInvRate]) hc fun _ _ e ↦ ?_
      subst e
      have hgi : (hs ++ [logN - s'.folds.length - next.fold + next.logInvRate]).getD index 0 =
          hs.getD index 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      refine InRange.nc_bind (noCommit_sampleN _) fun _ _ ↦ ?_
      refine InRange.nc_bind noCommit_readE fun _ _ ↦ ?_
      refine InRange.nc_bind (noCommit_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
      refine InRange.nc_bind (p := VerifierProgram.grindProofOfWork Whir.queryGrindingBits)
        ((noCommit_iff _).2 trivial) fun _ _ ↦ ?_
      refine InRange.nc_bind (p := sampleQueries _ level.queries)
        (noCommit_sampleQueriesAux _ _ _) fun queries hq ↦ ?_
      refine InRange.nc_bind (p := VerifierProgram.sampleChallenge) noCommit_sampleE fun lam _ ↦ ?_
      refine ⟨fun q hqq ↦ ?_, fun words ↦ ?_⟩
      · rw [hgi, ← hdepth]
        exact sampleQueriesAux_returns _ _ _ hq q hqq
      · refine InRange.nc_bind (p := sumcheckRoundPoly 3 _ none)
          (noCommit_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
        refine inRange_whirLevels logN laneFolds evaluateBasis (next :: rest') (index + 1) _ _
          (by simp [hl]) fun lv hlv ↦ ?_
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
        subst hlv
        rw [glue_folds]
        simp [List.getD_eq_getElem?_getD, hl]

/-! ## The verifier program -/

theorem noCommit_busRest_computed (L : Layout) (alphas : List E) (beta : E) (point tv : List E) :
    NoCommit (LeanVM.Guest.B1.Tables.busRest computedBytecodeValue L alphas beta point tv) := by
  unfold LeanVM.Guest.B1.Tables.busRest
  simp only [computedBytecodeValue]
  nc

theorem noCommit_verifyBusBalance_computed (layout : Layout) :
    NoCommit (verifyBusBalance computedBytecodeValue layout) := by
  rw [verifyBusBalance_split]
  exact NoCommit.bind (noCommit_sampleN _) fun _ ↦ NoCommit.bind noCommit_sampleE fun _ ↦
    NoCommit.bind (noCommit_gkrPhase _) fun _ ↦ noCommit_busRest_computed _ _ _ _ _

theorem noCommit_restClaims_computed (layout : Layout) (pi : Digest) :
    NoCommit (restClaims computedBytecodeValue layout pi) := by
  unfold restClaims keccakPhaseClaims ringSwitch
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]
  refine NoCommit.bind (noCommit_verifyBusBalance_computed _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_tablePhase _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_publicInputPhase _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_require _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_verifyKeccak _ _ _) fun x ↦ ?_
  rcases x with ⟨cl, kp, ks⟩
  exact NoCommit.bind (noCommit_sampleN _) fun _ ↦ noCommit_ret _

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

/-- **The verifier program opens in range**, from no commitment. -/
theorem inRange_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    InRange (leanVmVerifierProgram bytecode publicInput) [] fun _ _ ↦ True := by
  rw [leanVmProgram_eq]
  rw [verifyExecution_pre]
  unfold specPre
  simp only [VerifierProgram.bind_assoc]
  refine InRange.nc_bind (noCommit_readSizes _) fun ls _ ↦ ?_
  refine InRange.bind (inRange_commitStack _ _ []) fun _ hs' hc ↦ ?_
  obtain ⟨level, rest, hcfg, rfl⟩ := hc
  refine InRange.nc_bind (noCommit_restClaims_computed _ _) fun cl _ ↦ ?_
  simp only [VerifierProgram.ret_bind]
  unfold verifyStackedOpening
  simp only [verifyWhir_eq_target]
  unfold verifyWhirT
  simp only [VerifierProgram.bind_eq, VerifierProgram.bind_assoc]
  refine InRange.nc_bind noCommit_sampleE fun _ _ ↦ ?_
  refine InRange.nc_bind (noCommit_liftOption _) fun config hc ↦ ?_
  have hc' : Whir.ladder ls.1.stackLog ls.2 = some config := by
    unfold Verifier.liftOption at hc
    split at hc
    · cases hc
    · next a ha => rw [VerifierProgram.returns_ret hc]; exact ha
  rw [hcfg] at hc'
  cases hc'
  refine InRange.nc_bind (noCommit_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
  refine InRange.bind (inRange_whirLevels _ _ _ _ 0 _ _ rfl fun lv hlv ↦ ?_) fun _ _ _ ↦ trivial
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
  subst hlv
  simp

end
end LeanVM.Guest.Child
