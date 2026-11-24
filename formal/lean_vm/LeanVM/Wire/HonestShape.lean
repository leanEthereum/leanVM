/-
  LeanVM.Wire.HonestShape

  Every opening phase of the leanVM verifier program is within the wire decoding's bounds: at most
  `wireMaxPhases` phases, each of `1` to `wireMaxQueries` positions below `2^height`, of a
  commitment of height at most `wireMaxHeight` and width at most `wireMaxLeafWords`.
-/

module

public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Verifier.Deferred
public import LeanVM.Protocol.Verifier.NoCommit
public import LeanVM.Wire.Spec

/-!
# The verifier program's openings are within the wire bounds

`Wired p shapes n Q`: along every run of `p`, from commitments of the shapes `shapes` (height,
width) and with at most `n` openings left, every opening asks `1` to `wireMaxQueries` positions
below `2^height` of a commitment of height at most `wireMaxHeight` and width at most
`wireMaxLeafWords` (`QueryShape`), there are at most `n` of them, and every value returned
satisfies `Q` at the shapes and the openings left then.

The leanVM verifier program is `Wired` from no commitment with `wireMaxPhases` openings left
(`wired_leanVmProgram`). Its only commitments are the stack's and the WHIR levels', its only
openings the WHIR levels', one per level; every phase before the stacked opening commits and
opens nothing (`NoCommit`). The bounds are decided over the `56` admissible ladders
(`ladder_wire`): at most `6` levels, `13` to `234` queries per level, query depths (the
commitments' heights) `9` to `26`, the stack's width `64` and the deeper levels' at most `32`.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

variable {α β : Type}

/-! ## The phases before the stacked opening -/

/-- The phases between the stack's commitment and the stacked opening. -/
def claimsPhase (layout : Layout) (publicInput : Digest) : VerifierProgram (List StackClaim) := do
  let bus ← verifyBusBalance computedBytecodeValue layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let (claims, keccakPoint, keccakSlices) ← keccakPhaseClaims layout (claims ++ publicClaims)
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  return ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout)

theorem noCommit_claimsPhase (layout : Layout) (pi : Digest) :
    NoCommit (claimsPhase layout pi) := by
  unfold claimsPhase
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoCommit.bind (noCommit_verifyBusBalance noCommit_computedBytecodeValue _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_tablePhase _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_publicInputPhase _ _) fun _ ↦ ?_
  refine NoCommit.bind (noCommit_keccakPhaseClaims _ _) fun x ↦ ?_
  obtain ⟨cl, kp, ks⟩ := x
  exact NoCommit.bind (noCommit_ringSwitch _ _) fun _ ↦ noCommit_ret _

/-- The verifier program, regrouped: the sizes, the stack's commitment, its out-of-domain sample,
the claims, the stacked opening. -/
theorem leanVmProgram_regroup (bytecode : List K) (publicInput : Digest) :
    leanVmVerifierProgram bytecode publicInput =
      (readAnnouncedSizes bytecode).bind fun ls ↦
      (commitStack ls.1.stackLog ls.2).bind fun _ ↦
      (readOod ls.1.stackLog).bind fun ood ↦
      (claimsPhase ls.1 publicInput).bind fun cl ↦
      (verifyStackedOpening ls.1.stackLog ls.2 (cl ++ [ood])).bind fun _ ↦
        VerifierProgram.ret true := by
  rw [leanVmProgram_eq]
  simp only [verifyExecutionClaims, claimsPhase, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind, List.cons_append]

/-! ## The calculus -/

/-- **An opening within the wire bounds**: `1` to `wireMaxQueries` positions, below `2^height`, of
a commitment `(height, width)` of height at most `wireMaxHeight` and width at most
`wireMaxLeafWords`. -/
def QueryShape (shape : ℕ × ℕ) (positions : List ℕ) : Prop :=
  positions ≠ [] ∧ positions.length ≤ wireMaxQueries ∧ shape.1 ≤ wireMaxHeight ∧
    shape.2 ≤ wireMaxLeafWords ∧ ∀ q ∈ positions, q < 2 ^ shape.1

/-- **Openings within the wire bounds**: along every run of `p` from commitments of the shapes
`shapes`, with at most `n` openings left, every opening is within the bounds (`QueryShape`), there
are at most `n`, and every value returned satisfies `Q` at the shapes and openings left then. -/
def Wired : VerifierProgram α → List (ℕ × ℕ) → ℕ → (α → List (ℕ × ℕ) → ℕ → Prop) → Prop
  | .ret a, shapes, n, Q => Q a shapes n
  | .fail, _, _, _ => True
  | .read k, shapes, n, Q => ∀ x, Wired (k x) shapes n Q
  | .sample k, shapes, n, Q => ∀ c, Wired (k c) shapes n Q
  | .grind _ k, shapes, n, Q => Wired k shapes n Q
  | .commit height width k, shapes, n, Q => Wired k (shapes ++ [(height, width)]) n Q
  | .query i ps k, shapes, n, Q =>
    0 < n ∧ QueryShape (shapes.getD i (0, 0)) ps ∧ ∀ rows, Wired (k rows) shapes (n - 1) Q

namespace Wired

theorem mono {p : VerifierProgram α} {shapes : List (ℕ × ℕ)} {n : ℕ}
    {Q R : α → List (ℕ × ℕ) → ℕ → Prop} (h : Wired p shapes n Q)
    (hQR : ∀ a shapes' n', Q a shapes' n' → R a shapes' n') : Wired p shapes n R := by
  induction p generalizing shapes n with
  | ret a => exact hQR a shapes n h
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (h x)
  | sample k ih => exact fun x ↦ ih x (h x)
  | grind b k ih => exact ih h
  | commit ht w k ih => exact ih h
  | query i ps k ih => exact ⟨h.1, h.2.1, fun r ↦ ih r (h.2.2 r)⟩

theorem bind {p : VerifierProgram α} {f : α → VerifierProgram β} {shapes : List (ℕ × ℕ)} {n : ℕ}
    {Q : α → List (ℕ × ℕ) → ℕ → Prop} {R : β → List (ℕ × ℕ) → ℕ → Prop}
    (hp : Wired p shapes n Q) (hf : ∀ a shapes' n', Q a shapes' n' → Wired (f a) shapes' n' R) :
    Wired (p.bind f) shapes n R := by
  induction p generalizing shapes n with
  | ret a => exact hf a shapes n hp
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact ih hp
  | query i ps k ih => exact ⟨hp.1, hp.2.1, fun r ↦ ih r (hp.2.2 r)⟩

/-- A program that commits and opens nothing keeps the shapes and the openings left. -/
theorem of_noCommitA : ∀ {p : VerifierProgram α} {shapes : List (ℕ × ℕ)} {n : ℕ}, NoCommitA p →
    Wired p shapes n fun a shapes' n' ↦ shapes' = shapes ∧ n' = n ∧ VerifierProgram.Returns p a := by
  intro p
  induction p with
  | ret a => intro shapes n _; exact ⟨rfl, rfl, .ret a⟩
  | fail => intro shapes n _; trivial
  | read k ih =>
    intro shapes n h x
    exact (ih x (h x)).mono fun a _ _ hr ↦ ⟨hr.1, hr.2.1, .read x hr.2.2⟩
  | sample k ih =>
    intro shapes n h x
    exact (ih x (h x)).mono fun a _ _ hr ↦ ⟨hr.1, hr.2.1, .sample x hr.2.2⟩
  | grind b k ih =>
    intro shapes n h
    exact (ih h).mono fun a _ _ hr ↦ ⟨hr.1, hr.2.1, .grind b hr.2.2⟩
  | commit _ _ _ _ => intro shapes n h; exact h.elim
  | query _ _ _ _ => intro shapes n h; exact h.elim

/-- A program that commits and opens nothing, followed by a wired one. -/
theorem no_bind {p : VerifierProgram α} {f : α → VerifierProgram β} {shapes : List (ℕ × ℕ)}
    {n : ℕ} {R : β → List (ℕ × ℕ) → ℕ → Prop} (hp : NoCommit p)
    (hf : ∀ a, VerifierProgram.Returns p a → Wired (f a) shapes n R) :
    Wired (p.bind f) shapes n R :=
  bind (of_noCommitA ((noCommit_iff _).1 hp)) fun a _ _ h ↦ h.1 ▸ h.2.1 ▸ hf a h.2.2

end Wired

/-! ## The WHIR ladders -/

/-- The levels from a message of `μ` variables are within the wire bounds: each queries `1` to
`wireMaxQueries` positions at a depth (its commitment's height) of `1` to `wireMaxHeight` bits,
and each deeper level's commitment is at most `wireMaxLeafWords` wide. -/
def levelsWired : ℕ → List Whir.Level → Bool
  | _, [] => true
  | μ, level :: rest =>
    decide (1 ≤ level.queries ∧ level.queries ≤ wireMaxQueries ∧
        1 ≤ μ - level.fold + level.logInvRate ∧ μ - level.fold + level.logInvRate ≤ wireMaxHeight) &&
      (match rest with
        | [] => true
        | next :: _ => decide (2 * 2 ^ next.fold ≤ wireMaxLeafWords)) &&
      levelsWired (μ - level.fold) rest

/-- The stack's commitment is at most `wireMaxLeafWords` wide. -/
def stackWired : List Whir.Level → Bool
  | [] => true
  | level :: _ => decide (2 ^ level.fold ≤ wireMaxLeafWords)

/-- **Every admissible ladder is within the wire bounds**: at most `wireMaxPhases` levels, each
within the bounds; decided over the `60` admissible pairs. -/
theorem ladder_wire (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) :
    levels.length ≤ wireMaxPhases ∧ levelsWired μ levels = true ∧ stackWired levels = true := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels →
          (decide (levels.length ≤ wireMaxPhases) && levelsWired μ levels &&
            stackWired levels) = true := by
      decide +kernel
    have hk := key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
    exact ⟨hk.1.1, hk.1.2, hk.2⟩
  · simp [Whir.ladder, hadm] at h

/-! ## The WHIR levels -/

theorem foldRound_returns (s : WhirState) {r : WhirState × FoldRound}
    (h : VerifierProgram.Returns (foldRound s) r) : r.1.alphas.length = s.alphas.length + 1 := by
  unfold foldRound at h
  repeat obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  simp

theorem foldRounds_returns : ∀ (n : ℕ) (s : WhirState) {r : WhirState × List FoldRound},
    VerifierProgram.Returns (foldRounds n s) r → r.1.alphas.length = s.alphas.length + n
  | 0, s, r, h => by
    have := VerifierProgram.returns_ret h
    subst this
    rfl
  | n + 1, s, r, h => by
    unfold foldRounds at h
    obtain ⟨c, hc, h⟩ := VerifierProgram.returns_bind h
    obtain ⟨d, hd, h⟩ := VerifierProgram.returns_bind h
    have h1 := foldRound_returns s hc
    have h2 := foldRounds_returns n _ hd
    rw [VerifierProgram.returns_ret h]
    simp only at h2 ⊢
    omega

/-- The positions `sampleQueriesAux` returns: at most `remaining`, below `2^depth`, and at least
one when `1 ≤ remaining`, `1 ≤ depth ≤ 128` and there is fuel. -/
theorem sampleQueriesAux_returns (depth : ℕ) : ∀ (fuel remaining : ℕ) {qs : List ℕ},
    VerifierProgram.Returns (sampleQueriesAux depth fuel remaining) qs →
      qs.length ≤ remaining ∧ (∀ q ∈ qs, q < 2 ^ depth) ∧
        (1 ≤ fuel → 1 ≤ remaining → 1 ≤ depth → depth ≤ 128 → qs ≠ [])
  | 0, _, qs, h => by
    have := VerifierProgram.returns_ret h
    subst this
    simp
  | fuel + 1, remaining, qs, h => by
    unfold sampleQueriesAux at h
    split at h
    · have := VerifierProgram.returns_ret h
      subst this
      simp only [List.length_nil, Nat.zero_le, List.not_mem_nil, false_implies,
        implies_true, true_and]
      intro _ hr
      omega
    · obtain ⟨c, -, h⟩ := VerifierProgram.returns_bind h
      obtain ⟨rest, hrest, h⟩ := VerifierProgram.returns_bind h
      have := VerifierProgram.returns_ret h
      subst this
      obtain ⟨hl, hlt, -⟩ := sampleQueriesAux_returns depth fuel _ hrest
      refine ⟨?_, fun q hq ↦ ?_, fun _ _ hd1 hd2 ↦ ?_⟩
      · simp only [List.length_append, List.length_map, List.length_range]
        omega
      · rcases List.mem_append.mp hq with hq | hq
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp hq
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · exact hlt q hq
      · have h128 : 1 ≤ 128 / depth := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
        have hn : 1 ≤ min (128 / depth) remaining := by omega
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_map, List.length_range, List.length_nil] at this
        omega

/-- **The WHIR levels are wired**: at level `index`, the shapes so far end with the current
level's commitment, of height `logN − |α| − fold + rate` and width at most `wireMaxLeafWords`, and
as many openings are left as levels. -/
theorem wired_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState) (shapes : List (ℕ × ℕ)) (n : ℕ),
      shapes.length = index + 1 → levels.length ≤ n →
      levelsWired (logN - s.alphas.length) levels = true →
      (∀ level ∈ levels.head?,
        (shapes.getD index (0, 0)).1 = logN - s.alphas.length - level.fold + level.logInvRate ∧
          (shapes.getD index (0, 0)).2 ≤ wireMaxLeafWords) →
      Wired (whirLevels logN laneFolds evaluateBasis index levels s) shapes n
        fun _ _ _ ↦ True
  | [], _, _, _, _, _, _, _, _ => trivial
  | level :: rest, index, s, shapes, n, hl, hn, hw, hh => by
    obtain ⟨hh1, hh2⟩ := hh level rfl
    simp only [levelsWired, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨hq1, hq2, hd1, hd2⟩, hnext⟩, hrest⟩ := hw
    unfold whirLevels
    refine Wired.no_bind (noCommit_foldRounds _ _) fun r hr ↦ ?_
    obtain ⟨s', rounds⟩ := r
    have hf := foldRounds_returns _ _ hr
    simp only at hf
    have hdepth : logN - s'.alphas.length + level.logInvRate = (shapes.getD index (0, 0)).1 := by
      rw [hh1, hf]; omega
    have hn1 : 0 < n := by simp only [List.length_cons] at hn; omega
    have hq : ∀ queries, VerifierProgram.Returns
        (sampleQueries (logN - s'.alphas.length + level.logInvRate) level.queries) queries →
        QueryShape (shapes.getD index (0, 0)) queries := by
      intro queries hqs
      obtain ⟨hlen, hlt, hne⟩ := sampleQueriesAux_returns _ _ _ hqs
      rw [hdepth] at hlt hne
      exact ⟨hne hq1 hq1 (by rw [hh1]; omega) (by rw [hh1]; unfold wireMaxHeight at hd2; omega),
        hlen.trans hq2, by rw [hh1]; exact hd2, hh2, hlt⟩
    cases rest with
    | nil =>
      refine Wired.no_bind (noCommit_readN _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.grindProofOfWork Whir.queryGrindingBits)
        (noCommit_grind _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := sampleQueries _ level.queries)
        (noCommit_sampleQueriesAux _ _ _) fun queries hqs ↦ ?_
      refine ⟨hn1, hq queries hqs, fun words ↦ ?_⟩
      refine Wired.no_bind (noCommit_ret words) fun _ _ ↦ ?_
      refine Wired.no_bind (noCommit_require _) fun _ _ ↦ ?_
      refine Wired.no_bind (noCommit_sumcheck _ _ _) fun r _ ↦ ?_
      obtain ⟨tail, claim⟩ := r
      exact (Wired.of_noCommitA ((noCommit_iff _).1 (noCommit_require _))).mono
        fun _ _ _ _ ↦ trivial
    | cons next rest' =>
      simp only [levelShape]
      simp only [decide_eq_true_eq] at hnext
      have hc : Wired (VerifierProgram.readCommitment (logN - s'.alphas.length - next.fold +
          next.logInvRate) (2 * 2 ^ next.fold)) shapes n
          (fun _ shapes' n' ↦ shapes' = shapes ++ [(logN - s'.alphas.length - next.fold +
            next.logInvRate, 2 * 2 ^ next.fold)] ∧ n' = n) :=
        ⟨rfl, rfl⟩
      refine Wired.bind hc fun _ _ _ e ↦ ?_
      obtain ⟨rfl, rfl⟩ := e
      have hgi : (shapes ++ [(logN - s'.alphas.length - next.fold + next.logInvRate,
          2 * 2 ^ next.fold)]).getD index (0, 0) = shapes.getD index (0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      refine Wired.no_bind (noCommit_readN _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.grindProofOfWork Whir.oodGrindingBits)
        (noCommit_grind _) fun _ _ ↦ ?_
      refine Wired.no_bind (noCommit_sampleN _) fun _ _ ↦ ?_
      refine Wired.no_bind noCommit_readE fun _ _ ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.grindProofOfWork Whir.queryGrindingBits)
        (noCommit_grind _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := sampleQueries _ level.queries)
        (noCommit_sampleQueriesAux _ _ _) fun queries hqs ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.sampleChallenge) noCommit_sampleE fun lam _ ↦ ?_
      refine ⟨hn1, by rw [hgi]; exact hq queries hqs, fun words ↦ ?_⟩
      refine wired_whirLevels logN laneFolds evaluateBasis (next :: rest') (index + 1) _ _ _
        (by simp [hl]) (by simp only [List.length_cons] at hn ⊢; omega) ?_ fun lv hlv ↦ ?_
      · rw [glueLevel_alphas, hf]
        rw [show logN - (s.alphas.length + level.fold) = logN - s.alphas.length - level.fold by
          omega]
        exact hrest
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
        subst hlv
        rw [glueLevel_alphas]
        simp [List.getD_eq_getElem?_getD, hl, hnext]

/-- The stack's commitment: the shape of the ladder's first level. -/
theorem wired_commitStack (μ r : ℕ) (shapes : List (ℕ × ℕ)) (n : ℕ) :
    Wired (commitStack μ r) shapes n fun _ shapes' n' ↦ n' = n ∧ ∃ level rest,
      Whir.ladder μ r = some (level :: rest) ∧
        shapes' = shapes ++ [(μ - level.fold + level.logInvRate, 2 ^ level.fold)] := by
  rw [commitStack_eq]
  refine Wired.no_bind (noCommit_liftOption _) fun shape hc ↦ ?_
  have hs : commitShapeOf μ r = some shape := by
    unfold Verifier.liftOption at hc
    split at hc
    · cases hc
    · next a ha => rw [VerifierProgram.returns_ret hc]; exact ha
  obtain ⟨level, rest, hl, rfl⟩ := commitShapeOf_spec hs
  exact ⟨rfl, level, rest, hl, rfl⟩

/-- **The verifier program's openings are within the wire bounds**, from no commitment, with
`wireMaxPhases` openings left. -/
theorem wired_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    Wired (leanVmVerifierProgram bytecode publicInput) [] wireMaxPhases fun _ _ _ ↦ True := by
  rw [leanVmProgram_regroup]
  refine Wired.no_bind (noCommit_readSizes _) fun ls _ ↦ ?_
  refine Wired.bind (wired_commitStack _ _ [] _) fun _ shapes' n' hc ↦ ?_
  obtain ⟨rfl, level, rest, hcfg, rfl⟩ := hc
  obtain ⟨hlen, hlw, hsw⟩ := ladder_wire _ _ _ hcfg
  refine Wired.no_bind (noCommit_readOod _) fun _ _ ↦ ?_
  refine Wired.no_bind (noCommit_claimsPhase _ _) fun cl _ ↦ ?_
  refine Wired.bind (Q := fun _ _ _ ↦ True) ?_ fun _ _ _ _ ↦ trivial
  rw [verifyStackedOpening_nf]
  refine Wired.no_bind (noCommit_require _) fun _ _ ↦ ?_
  refine Wired.no_bind noCommit_sampleE fun _ _ ↦ ?_
  unfold verifyWhir
  refine Wired.no_bind (noCommit_liftOption _) fun config hc ↦ ?_
  have hc' : Whir.ladder ls.1.stackLog ls.2 = some config := by
    unfold Verifier.liftOption at hc
    split at hc
    · cases hc
    · next a ha => rw [VerifierProgram.returns_ret hc]; exact ha
  rw [hcfg] at hc'
  cases hc'
  refine wired_whirLevels _ _ _ _ 0 _ _ _ rfl hlen (by simpa using hlw) fun lv hlv ↦ ?_
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
  subst hlv
  simp only [stackWired, decide_eq_true_eq] at hsw
  simp [hsw]

end LeanVM.Wire

end
