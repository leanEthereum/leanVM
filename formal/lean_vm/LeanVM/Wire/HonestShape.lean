/-
  LeanVM.Wire.HonestShape

  Every opening phase of the leanVM verifier program is within the wire decoding's bounds: at most
  `wireMaxPhases` phases, each of `1` to `wireMaxQueries` positions below `2^height`, of a
  commitment of height at most `wireMaxHeight` and width at most `wireMaxLeafWords`.
-/

module

public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Verifier.Deferred
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
opens nothing (`NoOpen`). The bounds are decided over the `56` admissible ladders
(`ladder_wire`): at most `6` levels, `12` to `225` queries per level, query depths (the
commitments' heights) `9` to `26`, the stack's width `64` and the deeper levels' at most `48`.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

variable {α β : Type}

/-! ## Programs that commit and open nothing -/

/-- No `commit` and no `query` on any path (the recursion). -/
def NoOpenA : VerifierProgram α → Prop
  | .ret _ => True
  | .fail => True
  | .read k => ∀ x, NoOpenA (k x)
  | .sample k => ∀ c, NoOpenA (k c)
  | .grind _ k => NoOpenA k
  | .commit _ _ _ => False
  | .query _ _ _ => False

/-- **No `commit` and no `query` on any path.** Irreducible: unfolding it on a large program would
evaluate the program. -/
@[irreducible] def NoOpen (p : VerifierProgram α) : Prop := NoOpenA p

theorem noOpen_iff (p : VerifierProgram α) : NoOpen p ↔ NoOpenA p := by
  unfold NoOpen; rfl

theorem NoOpenA.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoOpenA p)
    (hf : ∀ a, NoOpenA (f a)) : NoOpenA (p.bind f) := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun c ↦ ih c (hp c)
  | grind b k ih => exact ih hp
  | commit _ _ _ _ => exact hp.elim
  | query _ _ _ _ => exact hp.elim

theorem NoOpen.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoOpen p)
    (hf : ∀ a, NoOpen (f a)) : NoOpen (p.bind f) :=
  (noOpen_iff _).2 (NoOpenA.bind ((noOpen_iff _).1 hp) fun a ↦ (noOpen_iff _).1 (hf a))

theorem noOpen_ret (a : α) : NoOpen (VerifierProgram.ret a) := (noOpen_iff _).2 trivial

theorem noOpen_fail : NoOpen (VerifierProgram.fail : VerifierProgram α) := (noOpen_iff _).2 trivial

theorem noOpen_readE : NoOpen VerifierProgram.readScalar := (noOpen_iff _).2 fun _ ↦ trivial

theorem noOpen_sampleE : NoOpen VerifierProgram.sampleChallenge :=
  (noOpen_iff _).2 fun _ ↦ trivial

theorem noOpen_grind (bits : ℕ) : NoOpen (VerifierProgram.grindProofOfWork bits) :=
  (noOpen_iff _).2 trivial

theorem noOpen_readN : ∀ n, NoOpen (VerifierProgram.readScalars n)
  | 0 => noOpen_ret _
  | n + 1 => by
    simp only [VerifierProgram.readScalars, VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoOpen.bind noOpen_readE fun _ ↦ NoOpen.bind (noOpen_readN n) fun _ ↦ noOpen_ret _

theorem noOpen_sampleN : ∀ n, NoOpen (VerifierProgram.sampleChallenges n)
  | 0 => noOpen_ret _
  | n + 1 => by
    simp only [VerifierProgram.sampleChallenges, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq]
    exact NoOpen.bind noOpen_sampleE fun _ ↦ NoOpen.bind (noOpen_sampleN n) fun _ ↦ noOpen_ret _

theorem noOpen_require (c : Prop) [Decidable c] : NoOpen (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split
  · exact noOpen_ret _
  · exact noOpen_fail

theorem noOpen_liftOption (o : Option α) : NoOpen (liftOption o) := by
  cases o
  · exact noOpen_fail
  · exact noOpen_ret _

theorem noOpen_sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) :
    NoOpen (sumcheckRoundPoly count claim e) := by
  cases e <;> (unfold sumcheckRoundPoly; simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq])
  · exact NoOpen.bind noOpen_readE fun _ ↦ NoOpen.bind (noOpen_readN _) fun _ ↦ noOpen_ret _
  · exact NoOpen.bind (noOpen_readN _) fun _ ↦ noOpen_ret _

theorem noOpen_sumcheck (claim : E) (count : ℕ) : ∀ eqs : List (Option E),
    NoOpen (sumcheck claim count eqs) := by
  intro eqs
  induction eqs generalizing claim with
  | nil => exact noOpen_ret _
  | cons e eqs ih =>
    unfold sumcheck
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoOpen.bind (noOpen_sumcheckRoundPoly _ _ _) fun _ ↦ NoOpen.bind noOpen_sampleE
      fun _ ↦ NoOpen.bind (ih _) fun _ ↦ noOpen_ret _

/-- A search for `NoOpen` through binds, the primitives, matches and `if`s. -/
macro "no_open" : tactic => `(tactic| repeat (first
  | exact noOpen_ret _
  | exact noOpen_readE
  | exact noOpen_sampleE
  | exact noOpen_readN _
  | exact noOpen_sampleN _
  | exact noOpen_require _
  | exact noOpen_liftOption _
  | exact noOpen_fail
  | exact noOpen_sumcheckRoundPoly _ _ _
  | exact noOpen_sumcheck _ _ _
  | (refine NoOpen.bind ?_ fun _ ↦ ?_)
  | (simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq])
  | split
  | (intro _)))

/-! ## The phases before the stacked opening -/

theorem noOpen_readSizes (bytecode : List K) : NoOpen (readAnnouncedSizes bytecode) := by
  unfold readAnnouncedSizes
  no_open

theorem noOpen_gkrStep (step : ℕ) (s : GkrState) : NoOpen (gkrStep step s) := by
  unfold gkrStep
  no_open

theorem noOpen_gkrLayers : ∀ (n : ℕ) (s : GkrState), NoOpen (gkrLayers n s)
  | 0, _ => noOpen_ret _
  | 1, s => by
    unfold gkrLayers
    simp only [VerifierProgram.bind_eq]
    exact NoOpen.bind (noOpen_gkrStep _ _) fun _ ↦ noOpen_gkrLayers 0 _
  | n + 2, s => by
    unfold gkrLayers
    split
    · simp only [VerifierProgram.bind_eq]
      exact NoOpen.bind (noOpen_gkrStep _ _) fun _ ↦ noOpen_gkrLayers (n + 1) _
    · simp only [VerifierProgram.bind_eq]
      exact NoOpen.bind (noOpen_gkrStep _ _) fun _ ↦ noOpen_gkrLayers n _

theorem noOpen_verifyGkr (depth : ℕ) : NoOpen (verifyGkrGrandProducts depth) := by
  unfold verifyGkrGrandProducts
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoOpen.bind noOpen_readE fun _ ↦ NoOpen.bind noOpen_readE fun _ ↦
    NoOpen.bind (noOpen_gkrLayers _ _) fun _ ↦ noOpen_ret _

theorem noOpen_verifyBusBalance (layout : Layout) :
    NoOpen (verifyBusBalance computedBytecodeValue layout) := by
  unfold verifyBusBalance computedBytecodeValue
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoOpen.bind (noOpen_sampleN _) fun _ ↦ NoOpen.bind noOpen_sampleE fun _ ↦ ?_
  refine NoOpen.bind (noOpen_verifyGkr _) fun _ ↦ ?_
  no_open

theorem noOpen_tableTerms (cP fP point : List E) :
    ∀ (rows : List (Table × ℕ × List Form × E)) (cursor : ℕ) (final : E)
      (claims : List ColumnClaim), NoOpen (tableTermsClaims cP fP point rows cursor final claims)
  | [], _, _, _ => noOpen_ret _
  | (table, height, forms, weight) :: rest, cursor, final, claims => by
    unfold tableTermsClaims
    simp only [VerifierProgram.bind_eq]
    exact NoOpen.bind (noOpen_readN _) fun _ ↦ noOpen_tableTerms cP fP point rest _ _ _

theorem noOpen_tablePhase (layout : Layout) (bus : BusResult) :
    NoOpen (tablePhaseClaims layout bus) := by
  unfold tablePhaseClaims tableSumcheckClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc]
  refine NoOpen.bind noOpen_sampleE fun _ ↦ NoOpen.bind (noOpen_sumcheck _ _ _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_tableTerms _ _ _ _ _ _ _) fun _ ↦ ?_
  no_open

theorem noOpen_publicInputPhase (layout : Layout) (pi : Digest) :
    NoOpen (publicInputPhase layout pi) := by
  unfold publicInputPhase
  no_open

theorem noOpen_keccakPackRounds : ∀ (rs : List E) (value scale : E),
    NoOpen (keccakPackRounds rs value scale)
  | [], _, _ => noOpen_ret _
  | r :: rs, value, scale => by
    unfold keccakPackRounds
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    exact NoOpen.bind (noOpen_sumcheckRoundPoly _ _ _) fun _ ↦ NoOpen.bind noOpen_sampleE
      fun _ ↦ NoOpen.bind (noOpen_keccakPackRounds rs _ _) fun _ ↦ noOpen_ret _

theorem noOpen_verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) :
    NoOpen (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoOpen.bind (noOpen_readN _) fun _ ↦ NoOpen.bind (noOpen_require _) fun _ ↦ ?_
  refine NoOpen.bind noOpen_sampleE fun _ ↦ NoOpen.bind (noOpen_keccakPackRounds _ _ _) fun _ ↦ ?_
  no_open

theorem noOpen_keccakLayers (logSteps : ℕ) (steps : List ℕ) :
    ∀ claim : KeccakClaim, NoOpen (keccakLayers logSteps steps claim) := by
  induction steps with
  | nil => intro _; exact noOpen_ret _
  | cons step steps ih =>
    intro claim
    unfold keccakLayers
    simp only [VerifierProgram.bind_eq]
    exact NoOpen.bind (noOpen_verifyKeccakLayer logSteps step claim) fun _ ↦ ih _

theorem noOpen_keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    NoOpen (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoOpen.bind (noOpen_sumcheck _ _ _) fun _ ↦ noOpen_ret _

theorem noOpen_verifyKeccak (logSteps : ℕ) (inst output : List E) :
    NoOpen (verifyKeccak logSteps inst output) := by
  have h1 : 1 < keccakSegments := by decide
  unfold verifyKeccak
  simp only [h1, ↓reduceIte, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
    VerifierProgram.ret_bind]
  refine NoOpen.bind (noOpen_sampleN _) fun _ ↦ NoOpen.bind (noOpen_sampleN _) fun _ ↦ ?_
  refine NoOpen.bind noOpen_readE fun _ ↦ NoOpen.bind (noOpen_keccakLayers _ _ _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_keccakOpen _ _ _ _ _) fun _ ↦ ?_
  refine NoOpen.bind noOpen_readE fun _ ↦ NoOpen.bind (noOpen_require _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_sumcheck _ _ _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_keccakOpen _ _ _ _ _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_readN _) fun _ ↦ NoOpen.bind (noOpen_require _) fun _ ↦ ?_
  exact noOpen_ret _

theorem noOpen_keccakPhase (layout : Layout) (claims : List ColumnClaim) :
    NoOpen (keccakPhaseClaims layout claims) := by
  unfold keccakPhaseClaims
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoOpen.bind (noOpen_require _) fun _ ↦ NoOpen.bind (noOpen_verifyKeccak _ _ _) fun _ ↦
    noOpen_ret _

theorem noOpen_ringSwitch (point s : List E) : NoOpen (ringSwitch point s) := by
  unfold ringSwitch
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  exact NoOpen.bind (noOpen_sampleN _) fun _ ↦ noOpen_ret _

/-- The phases between the stack's commitment and the stacked opening. -/
def claimsPhase (layout : Layout) (publicInput : Digest) : VerifierProgram (List StackClaim) := do
  let bus ← verifyBusBalance computedBytecodeValue layout
  let claims ← tablePhaseClaims layout bus
  let publicClaims ← publicInputPhase layout publicInput
  let (claims, keccakPoint, keccakSlices) ← keccakPhaseClaims layout (claims ++ publicClaims)
  let (ringTarget, ringWeight) ← ringSwitch keccakPoint keccakSlices
  return ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.stackClaim layout)

theorem noOpen_claimsPhase (layout : Layout) (pi : Digest) : NoOpen (claimsPhase layout pi) := by
  unfold claimsPhase
  simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
  refine NoOpen.bind (noOpen_verifyBusBalance _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_tablePhase _ _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_publicInputPhase _ _) fun _ ↦ ?_
  refine NoOpen.bind (noOpen_keccakPhase _ _) fun x ↦ ?_
  obtain ⟨cl, kp, ks⟩ := x
  exact NoOpen.bind (noOpen_ringSwitch _ _) fun _ ↦ noOpen_ret _

/-- The verifier program, regrouped: the sizes, the stack's commitment, the claims, the stacked
opening. -/
theorem leanVmProgram_regroup (bytecode : List K) (publicInput : Digest) :
    leanVmVerifierProgram bytecode publicInput =
      (readAnnouncedSizes bytecode).bind fun ls ↦
      (commitStack ls.1.stackLog ls.2).bind fun _ ↦
      (claimsPhase ls.1 publicInput).bind fun cl ↦
      (verifyStackedOpening ls.1.stackLog ls.2 cl).bind fun _ ↦ VerifierProgram.ret true := by
  rw [leanVmProgram_eq]
  simp only [verifyExecutionClaims, claimsPhase, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

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
theorem of_noOpenA : ∀ {p : VerifierProgram α} {shapes : List (ℕ × ℕ)} {n : ℕ}, NoOpenA p →
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
    {n : ℕ} {R : β → List (ℕ × ℕ) → ℕ → Prop} (hp : NoOpen p)
    (hf : ∀ a, VerifierProgram.Returns p a → Wired (f a) shapes n R) :
    Wired (p.bind f) shapes n R :=
  bind (of_noOpenA ((noOpen_iff _).1 hp)) fun a _ _ h ↦ h.1 ▸ h.2.1 ▸ hf a h.2.2

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
        | next :: _ => decide (3 * 2 ^ next.fold ≤ wireMaxLeafWords)) &&
      levelsWired (μ - level.fold) rest

/-- The stack's commitment is at most `wireMaxLeafWords` wide. -/
def stackWired : List Whir.Level → Bool
  | [] => true
  | level :: _ => decide (2 ^ level.fold ≤ wireMaxLeafWords)

/-- **Every admissible ladder is within the wire bounds**: at most `wireMaxPhases` levels, each
within the bounds; decided over the `104` admissible pairs. -/
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

theorem foldRoundsT_returns (b : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (lf : List E)
    {r : WhirStateT × List E},
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
    have := foldRoundsT_returns b n _ _ h
    simp only [List.length_append, List.length_singleton] at this
    omega

theorem noOpen_foldProofOfWork (b : ℕ) : NoOpen (VerifierProgram.foldProofOfWork b) := by
  unfold VerifierProgram.foldProofOfWork
  split
  · exact noOpen_ret _
  · exact noOpen_grind b

theorem noOpen_foldRoundsT (b : ℕ) : ∀ (n : ℕ) (s : WhirStateT) (lf : List E),
    NoOpen (foldRoundsT b n s lf)
  | 0, _, _ => noOpen_ret _
  | n + 1, s, lf => by
    unfold foldRoundsT
    simp only [VerifierProgram.bind_eq]
    exact NoOpen.bind (noOpen_foldProofOfWork b) fun _ ↦ NoOpen.bind noOpen_sampleE fun _ ↦
      NoOpen.bind (noOpen_sumcheckRoundPoly _ _ _) fun _ ↦ noOpen_foldRoundsT b n _ _

theorem noOpen_tailRoundsT : ∀ (n : ℕ) (t : E) (quad : List E), NoOpen (tailRoundsT n t quad)
  | 0, _, _ => noOpen_ret _
  | n + 1, t, quad => by
    unfold tailRoundsT
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    refine NoOpen.bind noOpen_sampleE fun _ ↦ ?_
    split
    · exact noOpen_ret _
    · exact NoOpen.bind (noOpen_sumcheckRoundPoly _ _ _) fun _ ↦
        NoOpen.bind (noOpen_tailRoundsT n _ _) fun _ ↦ noOpen_ret _

theorem noOpen_sampleQueriesAux (depth : ℕ) : ∀ (fuel remaining : ℕ),
    NoOpen (sampleQueriesAux depth fuel remaining)
  | 0, _ => noOpen_ret _
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq]
    split
    · exact noOpen_ret _
    · exact NoOpen.bind noOpen_sampleE fun _ ↦ NoOpen.bind
        (noOpen_sampleQueriesAux depth fuel _) fun _ ↦ noOpen_ret _

/-- The positions `sampleQueriesAux` returns: at most `remaining`, below `2^depth`, and at least
one when `1 ≤ remaining`, `1 ≤ depth ≤ 192` and there is fuel. -/
theorem sampleQueriesAux_returns (depth : ℕ) : ∀ (fuel remaining : ℕ) {qs : List ℕ},
    VerifierProgram.Returns (sampleQueriesAux depth fuel remaining) qs →
      qs.length ≤ remaining ∧ (∀ q ∈ qs, q < 2 ^ depth) ∧
        (1 ≤ fuel → 1 ≤ remaining → 1 ≤ depth → depth ≤ 192 → qs ≠ [])
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
      · have h192 : 1 ≤ 192 / depth := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
        have hn : 1 ≤ min (192 / depth) remaining := by omega
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_map, List.length_range, List.length_nil] at this
        omega

/-- **The WHIR levels are wired**: at level `index`, the shapes so far end with the current
level's commitment, of height `logN − folds − fold + rate` and width at most
`wireMaxLeafWords`, and as many openings are left as levels. -/
theorem wired_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirStateT) (shapes : List (ℕ × ℕ)) (n : ℕ),
      shapes.length = index + 1 → levels.length ≤ n →
      levelsWired (logN - s.folds.length) levels = true →
      (∀ level ∈ levels.head?,
        (shapes.getD index (0, 0)).1 = logN - s.folds.length - level.fold + level.logInvRate ∧
          (shapes.getD index (0, 0)).2 ≤ wireMaxLeafWords) →
      Wired (whirLevelsT logN laneFolds evaluateBasis index levels s) shapes n
        fun _ _ _ ↦ True
  | [], _, _, _, _, _, _, _, _ => trivial
  | level :: rest, index, s, shapes, n, hl, hn, hw, hh => by
    obtain ⟨hh1, hh2⟩ := hh level rfl
    simp only [levelsWired, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨hq1, hq2, hd1, hd2⟩, hnext⟩, hrest⟩ := hw
    unfold whirLevelsT
    refine Wired.no_bind (noOpen_foldRoundsT _ _ _ _) fun r hr ↦ ?_
    obtain ⟨s', levelFolds⟩ := r
    have hf := foldRoundsT_returns _ _ _ _ hr
    simp only at hf
    have hdepth : logN - s'.folds.length + level.logInvRate = (shapes.getD index (0, 0)).1 := by
      rw [hh1, hf]; omega
    have hn1 : 0 < n := by simp only [List.length_cons] at hn; omega
    have hq : ∀ queries, VerifierProgram.Returns
        (sampleQueries (logN - s'.folds.length + level.logInvRate) level.queries) queries →
        QueryShape (shapes.getD index (0, 0)) queries := by
      intro queries hqs
      obtain ⟨hlen, hlt, hne⟩ := sampleQueriesAux_returns _ _ _ hqs
      rw [hdepth] at hlt hne
      exact ⟨hne hq1 hq1 (by rw [hh1]; omega) (by rw [hh1]; unfold wireMaxHeight at hd2; omega),
        hlen.trans hq2, by rw [hh1]; exact hd2, hh2, hlt⟩
    cases rest with
    | nil =>
      refine Wired.no_bind (noOpen_readN _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.grindProofOfWork Whir.queryGrindingBits)
        (noOpen_grind _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := sampleQueries _ level.queries)
        (noOpen_sampleQueriesAux _ _ _) fun queries hqs ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.sampleChallenge) noOpen_sampleE fun lam _ ↦ ?_
      refine ⟨hn1, hq queries hqs, fun words ↦ ?_⟩
      refine Wired.no_bind (p := sumcheckRoundPoly 3 _ none)
        (noOpen_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := tailRoundsT _ _ _) (noOpen_tailRoundsT _ _ _) fun r _ ↦ ?_
      obtain ⟨tf, tg⟩ := r
      exact (Wired.of_noOpenA ((noOpen_iff _).1 (noOpen_require _))).mono fun _ _ _ _ ↦ trivial
    | cons next rest' =>
      simp only [VerifierProgram.pure_eq, levelShape]
      simp only [decide_eq_true_eq] at hnext
      have hc : Wired (VerifierProgram.readCommitment (logN - s'.folds.length - next.fold +
          next.logInvRate) (3 * 2 ^ next.fold)) shapes n
          (fun _ shapes' n' ↦ shapes' = shapes ++ [(logN - s'.folds.length - next.fold +
            next.logInvRate, 3 * 2 ^ next.fold)] ∧ n' = n) :=
        ⟨rfl, rfl⟩
      refine Wired.bind hc fun _ _ _ e ↦ ?_
      obtain ⟨rfl, rfl⟩ := e
      have hgi : (shapes ++ [(logN - s'.folds.length - next.fold + next.logInvRate,
          3 * 2 ^ next.fold)]).getD index (0, 0) = shapes.getD index (0, 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      refine Wired.no_bind (noOpen_sampleN _) fun _ _ ↦ ?_
      refine Wired.no_bind noOpen_readE fun _ _ ↦ ?_
      refine Wired.no_bind (noOpen_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.grindProofOfWork Whir.queryGrindingBits)
        (noOpen_grind _) fun _ _ ↦ ?_
      refine Wired.no_bind (p := sampleQueries _ level.queries)
        (noOpen_sampleQueriesAux _ _ _) fun queries hqs ↦ ?_
      refine Wired.no_bind (p := VerifierProgram.sampleChallenge) noOpen_sampleE fun lam _ ↦ ?_
      refine ⟨hn1, by rw [hgi]; exact hq queries hqs, fun words ↦ ?_⟩
      refine Wired.no_bind (p := sumcheckRoundPoly 3 _ none)
        (noOpen_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
      refine wired_whirLevels logN laneFolds evaluateBasis (next :: rest') (index + 1) _ _ _
        (by simp [hl]) (by simp only [List.length_cons] at hn ⊢; omega) ?_ fun lv hlv ↦ ?_
      · rw [glue_folds, hf]
        rw [show logN - (s.folds.length + level.fold) = logN - s.folds.length - level.fold by
          omega]
        exact hrest
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
        subst hlv
        rw [glue_folds]
        simp [List.getD_eq_getElem?_getD, hl, hnext]

/-- The stack's commitment: the shape of the ladder's first level. -/
theorem wired_commitStack (μ r : ℕ) (shapes : List (ℕ × ℕ)) (n : ℕ) :
    Wired (commitStack μ r) shapes n fun _ shapes' n' ↦ n' = n ∧ ∃ level rest,
      Whir.ladder μ r = some (level :: rest) ∧
        shapes' = shapes ++ [(μ - level.fold + level.logInvRate, 2 ^ level.fold)] := by
  unfold commitStack
  refine Wired.no_bind (noOpen_liftOption _) fun config hc ↦ ?_
  have hc' : Whir.ladder μ r = some config := by
    unfold Verifier.liftOption at hc
    split at hc
    · cases hc
    · next a ha => rw [VerifierProgram.returns_ret hc]; exact ha
  cases config with
  | nil => trivial
  | cons level rest => exact ⟨rfl, level, rest, hc', rfl⟩

/-- **The verifier program's openings are within the wire bounds**, from no commitment, with
`wireMaxPhases` openings left. -/
theorem wired_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    Wired (leanVmVerifierProgram bytecode publicInput) [] wireMaxPhases fun _ _ _ ↦ True := by
  rw [leanVmProgram_regroup]
  refine Wired.no_bind (noOpen_readSizes _) fun ls _ ↦ ?_
  refine Wired.bind (wired_commitStack _ _ [] _) fun _ shapes' n' hc ↦ ?_
  obtain ⟨rfl, level, rest, hcfg, rfl⟩ := hc
  obtain ⟨hlen, hlw, hsw⟩ := ladder_wire _ _ _ hcfg
  refine Wired.no_bind (noOpen_claimsPhase _ _) fun cl _ ↦ ?_
  refine Wired.bind (Q := fun _ _ _ ↦ True) ?_ fun _ _ _ _ ↦ trivial
  unfold verifyStackedOpening
  simp only [verifyWhir_eq_target]
  unfold verifyWhirT
  simp only [VerifierProgram.bind_eq]
  refine Wired.no_bind noOpen_sampleE fun _ _ ↦ ?_
  refine Wired.no_bind (noOpen_liftOption _) fun config hc ↦ ?_
  have hc' : Whir.ladder ls.1.stackLog ls.2 = some config := by
    unfold Verifier.liftOption at hc
    split at hc
    · cases hc
    · next a ha => rw [VerifierProgram.returns_ret hc]; exact ha
  rw [hcfg] at hc'
  cases hc'
  refine Wired.no_bind (noOpen_sumcheckRoundPoly _ _ _) fun _ _ ↦ ?_
  refine wired_whirLevels _ _ _ _ 0 _ _ _ rfl hlen (by simpa using hlw) fun lv hlv ↦ ?_
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hlv
  subst hlv
  simp only [stackWired, decide_eq_true_eq] at hsw
  simp [hsw]

end LeanVM.Wire

end
