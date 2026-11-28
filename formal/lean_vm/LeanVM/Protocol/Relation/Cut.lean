/-
  LeanVM.Protocol.Relation.Cut

  The cut verifier's extracted run: wherever the ghost verifier's run returns, the cut's run from
  the same state returns the same value, and the final query's proof of work hits after it.
-/

module

public import LeanVM.Protocol.Relation.ExtractorDef
public import LeanVM.Protocol.Relation.XRun
public import LeanVM.Protocol.Relation.Whole
public import LeanVM.Protocol.Relation.Runs
public import LeanVM.Protocol.Relation.NoCommit
public import LeanVM.Protocol.Whir.Params.Iface
import LeanVM.Protocol.Verifier.Cost

/-!
# The cut verifier's run

From tag `formal-bus-archive`, `EndToEnd/Sound/{CutRun, CutXrun}.lean`, on Hotwire's body.

`XCut H F Q p q`: wherever the extracted run of `p` returns a value, the extracted run of `q`
from the same state and history returns it too, with a history the first one extends by no
commitment, at a state where `Q` holds. It passes through a common prefix program (`XCut.bind`)
and a final return (`XCut.mapRet`), so the cut levels (`xcut_whirLevelsGF`; the final level's rest
opens rows but commits nothing, `NoCommit`) give the cut verifier (`xcut_leanVmProgramG`), the
final query's proof of work hitting after it (`CutEnd`: `FinalShapeOK`).

`replayU_cut`: so the replay of the cut (`Rom.replayU`) on permutation answers agreeing with the
run's on its inputs returns the ghost verifier's value, at the extracted run's state, whose roots
hold the commitments of the ghost's whole history.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Compile.Rom
open LeanVM.Protocol.Verifier LeanVM.Protocol.Whir LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Params

@[expose] public section

/-! ## Returned values -/

/-- A return after a return is the same, after no event. -/
theorem after_ret_eq {α : Type} {a b : α} {l : List Ev}
    (h : (VerifierProgram.ret a).after l = some (.ret b)) : l = [] ∧ a = b := by
  cases l with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq, VerifierProgram.ret.injEq] at h
    exact ⟨rfl, h⟩
  | cons e es => cases e <;> simp [VerifierProgram.after] at h

/-- A cost's postcondition holds of every value the program may return. -/
theorem post_of_returns {α : Type} {height n : ℕ} {Q : α → Prop} {p : VerifierProgram α} {a : α}
    (hc : VerifierProgram.Costs height p n Q) (hr : VerifierProgram.Returns p a) : Q a := by
  induction hr generalizing n with
  | ret a => exact hc
  | read x _ ih => exact ih (hc.2 x)
  | sample x _ ih => exact ih (hc.2 x)
  | readPacked _ xs _ _ ih => exact ih (hc.2 xs)
  | samplePacked _ xs _ _ ih => exact ih (hc.2 xs)
  | grind _ _ ih => exact ih hc.2
  | commit _ _ _ ih => exact ih hc.2.2
  | query _ _ rows _ ih => exact ih (hc.2 rows)

theorem returns_foldRounds {n : ℕ} {s : WhirState} {r : WhirState × List FoldRound}
    (h : VerifierProgram.Returns (foldRounds n s) r) : r.1.alphas.length = s.alphas.length + n :=
  post_of_returns (Q := fun r : WhirState × List FoldRound ↦ r.1.alphas.length = s.alphas.length + n)
    (costs_foldRounds (height := 0) n s) h

/-- A level's rest hands its continuation a state with the same `α`s. -/
theorem returns_midTailPre {logN index : ℕ} {level next : Whir.Level} {s : WhirState}
    {rounds : List FoldRound} {p : List E × WhirState}
    (h : VerifierProgram.Returns (midTailPre logN index level next s rounds) p) :
    p.2.alphas = s.alphas := by
  unfold midTailPre midTailC at h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  obtain ⟨_, -, h⟩ := VerifierProgram.returns_bind h
  rw [VerifierProgram.returns_ret h]
  rfl

theorem noCommit_sampleQueriesAux (depth : ℕ) :
    ∀ fuel remaining, NoCommit (sampleQueriesAux depth fuel remaining)
  | 0, _ => noCommit_pure _
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · exact noCommit_pure _
    · exact NoCommit.bind' noCommit_sampleChallenge fun _ ↦
        NoCommit.bind' (noCommit_sampleQueriesAux depth fuel _) fun _ ↦ noCommit_pure _

theorem noCommit_sampleQueries (depth count : ℕ) : NoCommit (sampleQueries depth count) :=
  noCommit_sampleQueriesAux depth count count

/-- **The rest of the final level commits nothing.** -/
theorem noCommit_finRest (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) (tr : WhirTrace) :
    NoCommit ((finRest logN laneFolds eb index level s rounds tr).bind fun _ ↦
      VerifierProgram.ret tr) := by
  refine NoCommit.bind ?_ fun _ ↦ .ret _
  cases tr with
  | mid => exact .fail
  | final _ folded =>
    simp only [finRest, finalTailRest, VerifierProgram.bind_eq]
    refine (noCommit_grindProofOfWork _).bind fun _ ↦ NoCommit.bind ?_ fun _ ↦
      (noCommit_sumcheck _ _ _).bind fun _ ↦ noCommit_require _
    refine (noCommit_sampleQueries _ _).bind fun _ ↦ (NoCommit.query fun _ ↦ .ret _).bind
      fun _ ↦ noCommit_require _

/-! ## The final proof of work -/

/-- The positions a challenge names first: `n` of `depth` bits (`sample_queries`'s first chunk). -/
def firstPositions (depth n : ℕ) (c : E) : List ℕ :=
  (List.range n).map fun i ↦ (eToNat c >>> (i * depth)) % 2 ^ depth

/-- **A hit of a proof of work of `bits` bits**: the answer `u` passes it, and its challenge names
the phase's first `n` positions at `depth` bits. -/
def GrindHit (bits depth n : ℕ) (phase : List Opening) (u : KeccakState) : Prop :=
  powOk bits (Keccak.lane u 2) = true ∧
    firstPositions depth n (challengeOf u) = (phase.map Opening.leafIndex).take n

/-- **The final query's proof of work hits from the state `s`** on the answers `F`: the next
scalar is its nonce, and the permutation that absorbs it answers a hit for the next phase, at the
final level's query depth and count. -/
def FinalOK (F : KeccakState → Option KeccakState) (depth count : ℕ) (s : VerifierProgramState) :
    Prop :=
  ∃ n xs sp1 sp2 phase rest, s.stream = n :: xs ∧ s.sponge.ground = none ∧
    absorb (m := Option) F s.sponge n dsPowNonce = some sp1 ∧
    duplex (m := Option) F sp1 = some sp2 ∧ s.openings = phase :: rest ∧
    GrindHit Whir.queryGrindingBits depth (min (128 / depth) count) phase sp2.state

/-- The final level's query depth of a ladder whose levels start after `a` folds. -/
def finalDepth (logN a : ℕ) (levels : List Whir.Level) : ℕ :=
  logN - (a + (levels.map (·.fold)).sum) + (levels.getLast?.map (·.logInvRate)).getD 0

/-- The final level's query count of a ladder. -/
def finalCount (levels : List Whir.Level) : ℕ := (levels.getLast?.map (·.queries)).getD 0

/-- **The final shape's hit**: the stack's size and rate have a ladder, at whose final level the
final query's proof of work hits. -/
def FinalShapeOK (F : KeccakState → Option KeccakState) (logN ρ : ℕ) (s : VerifierProgramState) :
    Prop :=
  ∃ config, Whir.ladder logN ρ = some config ∧
    FinalOK F (finalDepth logN 0 config) (finalCount config) s

/-! ## The cut on runs -/

section XCut

variable (H : Bytes → Option Digest) (F : KeccakState → Option KeccakState)

/-- **`q` cuts `p` on runs, ending in `Q`**: wherever `p`'s extracted run returns a value, `q`'s
does, with a history that `p`'s extends by no commitment, at a state where `Q` holds. -/
def XCut {α : Type} (Q : α → VerifierProgramState → Prop) (p q : VerifierProgram α) : Prop :=
  ∀ s h a s' hist, xrun H F p s h = some (a, s', hist) → ∃ s₁ h₁,
    xrun H F q s h = some (a, s₁, h₁) ∧ (∃ l, hist = h₁ ++ l ∧ commits l = []) ∧ Q a s₁

variable {H F}

theorem XCut.mono {α : Type} {Q Q' : α → VerifierProgramState → Prop} {p q : VerifierProgram α}
    (hpq : XCut H F Q p q) (hQ : ∀ a s, Q a s → Q' a s) : XCut H F Q' p q := by
  intro s h a s' hist hx
  obtain ⟨s₁, h₁, hq, hl, hQa⟩ := hpq s h a s' hist hx
  exact ⟨s₁, h₁, hq, hl, hQ _ _ hQa⟩

/-- Binding the same program before cut continuations cuts, the continuations at the values it
may return. -/
theorem XCut.bind {α β : Type} (p : VerifierProgram α) {f g : α → VerifierProgram β}
    {Q : β → VerifierProgramState → Prop}
    (hfg : ∀ a, VerifierProgram.Returns p a → XCut H F Q (f a) (g a)) :
    XCut H F Q (p.bind f) (p.bind g) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨l, -, ha, -⟩ := xrun_after H F _ _ _ hr
  obtain ⟨s₁, h₁, hg, hl⟩ := hfg r.1 (returns_of_after ha) _ _ _ _ _ hf
  exact ⟨s₁, h₁, by rw [hr, Option.bind_some, hg], hl⟩

theorem XCut.mapRet {α β : Type} {p q : VerifierProgram α} {Q : α → VerifierProgramState → Prop}
    {Q' : β → VerifierProgramState → Prop} (hpq : XCut H F Q p q) (w : α → β)
    (hQ : ∀ a s, Q a s → Q' (w a) s) :
    XCut H F Q' (p.bind fun a ↦ VerifierProgram.ret (w a))
      (q.bind fun a ↦ VerifierProgram.ret (w a)) := by
  intro s h b s' hist hx
  rw [xrun_bind] at hx ⊢
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, -, rfl⟩ := hf
  obtain ⟨s₁, h₁, hq, hl, hQa⟩ := hpq _ _ _ _ _ hr
  exact ⟨s₁, h₁, by rw [hq, Option.bind_some]; rfl, hl, hQ _ _ hQa⟩

/-- The query positions' run: the openings and roots kept, and from a challenge a grind drew,
the first positions it names. -/
theorem xrun_sampleQueriesAux {depth : ℕ} : ∀ (fuel remaining : ℕ) {st : VerifierProgramState}
    {h : List Ev} {qs : List ℕ} {st' : VerifierProgramState} {h' : List Ev},
    xrun H F (sampleQueriesAux depth fuel remaining) st h = some (qs, st', h') →
    st'.openings = st.openings ∧ st'.roots = st.roots ∧
      ∀ c, st.sponge.ground = some c → remaining ≤ fuel →
        ∃ rest, qs = firstPositions depth (min (128 / depth) remaining) c ++ rest
  | 0, remaining, st, h, qs, st', h', hx => by
    simp only [sampleQueriesAux, VerifierProgram.pure_eq, xrun, Option.some.injEq,
      Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl, -⟩ := hx
    refine ⟨rfl, rfl, fun c _ hr ↦ ⟨[], ?_⟩⟩
    rw [show remaining = 0 by omega]
    simp [firstPositions]
  | fuel + 1, remaining, st, h, qs, st', h', hx => by
    unfold sampleQueriesAux at hx
    simp only [VerifierProgram.bind_eq, VerifierProgram.pure_eq] at hx
    split at hx
    · rename_i hr0
      simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl, -⟩ := hx
      refine ⟨rfl, rfl, fun c _ _ ↦ ⟨[], ?_⟩⟩
      simp [firstPositions, hr0]
    · rw [xrun_bind] at hx
      obtain ⟨r, hr, hx⟩ := Option.bind_eq_some_iff.mp hx
      rw [xrun_bind] at hx
      obtain ⟨r', hr', hx⟩ := Option.bind_eq_some_iff.mp hx
      simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl, -⟩ := hx
      simp only [VerifierProgram.sampleChallenge, xrun] at hr
      obtain ⟨c', hc', hr⟩ := Option.bind_eq_some_iff.mp hr
      simp only [Option.some.injEq] at hr
      subst hr
      obtain ⟨ho, hroots, -⟩ := xrun_sampleQueriesAux fuel _ hr'
      refine ⟨ho, hroots, fun c hg _ ↦ ⟨r'.1, ?_⟩⟩
      simp only [squeeze, hg, pure, Option.some.injEq] at hc'
      subst hc'
      rfl

/-- **The final level's rest hits**: where it returns from a state, the final query's proof of
work hits there, at the level's depth and count. -/
theorem finalOK_of_xrun {logN laneFolds : ℕ} {eb : List E → E} {index : ℕ} {level : Whir.Level}
    {s : WhirState} {rounds : List FoldRound} {folded : List E} {st : VerifierProgramState}
    {h : List Ev} {a : Unit} {st' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (finalTailRest logN laneFolds eb index level s rounds folded) st h =
      some (a, st', hist)) :
    FinalOK F (logN - s.alphas.length + level.logInvRate) level.queries st := by
  unfold finalTailRest at hx
  simp only [VerifierProgram.bind_eq] at hx
  rw [xrun_bind] at hx
  obtain ⟨r1, h1, hx⟩ := Option.bind_eq_some_iff.mp hx
  rw [xrun_bind] at hx
  obtain ⟨r2, h2, hx⟩ := Option.bind_eq_some_iff.mp hx
  rw [xrun_bind] at h2
  obtain ⟨r3, h3, h2⟩ := Option.bind_eq_some_iff.mp h2
  rw [xrun_bind] at h2
  obtain ⟨r4, h4, -⟩ := Option.bind_eq_some_iff.mp h2
  have hbits : Whir.queryGrindingBits ≠ 0 := by decide
  simp only [VerifierProgram.grindProofOfWork, hbits, ↓reduceIte, xrun] at h1
  split at h1
  · rename_i n xs hst hg
    obtain ⟨r, hr, h1⟩ := Option.bind_eq_some_iff.mp h1
    split_ifs at h1 with hp
    simp only [Option.some.injEq] at h1
    subst h1
    have hr' := hr
    simp only [absorbNonce, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hr'
    obtain ⟨sp1, hsp1, sp2, hsp2, rfl⟩ := hr'
    obtain ⟨ho, -, hpos⟩ := xrun_sampleQueriesAux _ _ h3
    obtain ⟨rest, hqs⟩ := hpos _ rfl le_rfl
    simp only [VerifierProgram.queryOpenings, xrun] at h4
    split at h4
    · rename_i root height width phase rest' hroot hop
      split at h4
      · rename_i rows hrows
        simp only [openPhaseWithHash] at hrows
        split_ifs at hrows with hcond
        · refine ⟨n, xs, sp1, sp2, phase, rest', hst, hg, hsp1, hsp2, by rw [← hop, ho], hp, ?_⟩
          rw [hcond.2, hqs, List.take_left' (by simp [firstPositions])]
        · simp [pure] at hrows
      · simp at h4
    · simp at h4
  · simp at h1

/-- The full final step's run returns where the cut's does, with the same trace, and the final
query's proof of work hits after it. -/
theorem xcut_fin (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) :
    XCut H F (fun _ st ↦ FinalOK F (logN - s.alphas.length + level.logInvRate) level.queries st)
      (finFull logN laneFolds eb index level s rounds) (finCut logN index level s rounds) := by
  intro st h a s' hist hx
  rw [finFull_eq, xrun_bind] at hx
  obtain ⟨r, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨l, hl, hafter, -⟩ := xrun_after H F _ _ _ hf
  have hr1 : r.1 = a := by
    obtain ⟨u, m₁, m₂, -, -, hret⟩ := after_bind_ret hafter
    exact (after_ret_eq hret).2
  subst hr1
  refine ⟨r.2.1, r.2.2, hr, ⟨l, hl, (noCommit_finRest logN laneFolds eb index level s rounds
    r.1).commits_after hafter⟩, ?_⟩
  obtain ⟨tr, st1, h1⟩ := r
  rw [xrun_bind] at hf
  obtain ⟨r', hr', -⟩ := Option.bind_eq_some_iff.mp hf
  cases tr with
  | mid => simp [finRest, xrun] at hr'
  | final _ folded => exact finalOK_of_xrun hr'

theorem finalDepth_single (logN a : ℕ) (level : Whir.Level) :
    finalDepth logN a [level] = logN - (a + level.fold) + level.logInvRate := by
  simp [finalDepth]

theorem finalDepth_cons (logN a : ℕ) (level next : Whir.Level) (rest : List Whir.Level) :
    finalDepth logN a (level :: next :: rest) = finalDepth logN (a + level.fold) (next :: rest) := by
  simp only [finalDepth, List.map_cons, List.sum_cons, List.getLast?_cons_cons]
  rw [Nat.add_assoc]

theorem finalCount_cons (level next : Whir.Level) (rest : List Whir.Level) :
    finalCount (level :: next :: rest) = finalCount (next :: rest) := by
  simp only [finalCount, List.getLast?_cons_cons]

/-- **The cut levels' run** returns where the full levels' does, the final query's proof of work
hitting after it. -/
theorem xcut_whirLevelsGF (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      XCut H F (fun _ st ↦ FinalOK F (finalDepth logN s.alphas.length levels) (finalCount levels) st)
        (whirLevelsGF logN (finFull logN laneFolds eb) index levels s)
        (whirLevelsGF logN (finCut logN) index levels s)
  | _, [], _ => fun _ _ _ _ _ hx ↦ by simp [whirLevelsGF, xrun] at hx
  | index, [level], s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    refine XCut.bind _ fun r hr ↦ (xcut_fin logN laneFolds eb index level r.1 r.2).mono ?_
    intro _ st hst
    rwa [finalDepth_single, finalCount, ← returns_foldRounds hr]
  | index, level :: next :: rest, s => by
    simp only [whirLevelsGF, VerifierProgram.bind_eq]
    refine XCut.bind _ fun r hr ↦ ?_
    rw [midTailC_eq_pre, midTailC_eq_pre]
    refine XCut.bind _ fun p hp ↦
      ((xcut_whirLevelsGF logN laneFolds eb (index + 1) (next :: rest) p.2).mapRet
        (fun tr ↦ WhirTrace.mid r.2 p.1 tr)
        (Q' := fun _ st ↦ FinalOK F (finalDepth logN p.2.alphas.length (next :: rest))
          (finalCount (next :: rest)) st) fun _ _ h ↦ h).mono ?_
    intro _ st hst
    rw [returns_midTailPre hp, returns_foldRounds hr] at hst
    rwa [finalDepth_cons, finalCount_cons]

theorem xcut_verifyStackedOpeningG (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (batching : E) :
    XCut H F (fun _ st ↦ FinalShapeOK F stackLog logInvRate st)
      (verifyStackedOpeningG stackLog logInvRate claims batching)
      (verifyStackedOpeningCut stackLog logInvRate claims batching) := by
  refine XCut.bind _ fun _ _ ↦ ?_
  unfold verifyWhirG verifyWhirCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun config hc ↦ ?_
  rw [whirLevelsG_eq]
  exact (xcut_whirLevelsGF _ _ _ _ _ _).mono fun _ st hst ↦ ⟨config, returns_liftOption hc, hst⟩

theorem xcut_veBodyG (layout : Layout) (ρ : ℕ) (input : PublicInput) :
    XCut H F (fun _ st ↦ FinalShapeOK F layout.stackLog ρ st) (veBodyG layout ρ input)
      (veBodyCut layout ρ input) := by
  unfold veBodyG veBodyCut
  simp only [VerifierProgram.bind_eq]
  refine XCut.bind _ fun _ _ ↦ XCut.bind _ fun ood _ ↦ XCut.bind _ fun r _ ↦ ?_
  obtain ⟨link, pub, outs, kp, ks⟩ := r
  refine XCut.bind _ fun qk _ ↦ XCut.bind _ fun y _ ↦ ?_
  obtain ⟨ring, batching⟩ := y
  exact XCut.bind _ fun _ _ ↦ xcut_verifyStackedOpeningG _ _ _ _

/-- What the cut verifier's run ends with: the final query's proof of work hits at the announced
shape. -/
def CutEnd (F : KeccakState → Option KeccakState) (r : Bool × ((Layout × ℕ) × WhirTrace))
    (s : VerifierProgramState) : Prop :=
  FinalShapeOK F r.2.1.1.stackLog r.2.1.2 s

/-- **The cut verifier's run** returns where the ghost verifier's does, the final query's proof
of work hitting after it. -/
theorem xcut_leanVmProgramG (bytecode : List K) (input : PublicInput) :
    XCut H F (CutEnd F) (leanVmProgramG bytecode input) (leanVmProgramCut bytecode input) :=
  XCut.bind _ fun (a : Layout × ℕ) _ ↦ (xcut_veBodyG a.1 a.2 input).mapRet
    (fun tr ↦ (true, (a, tr))) fun _ _ h ↦ h

end XCut

/-! ## The replay of the cut -/

/-- An accepting extracted run of the verifier is one of the ghost verifier, with its data. -/
theorem xrun_leanVmProgramG {H : Bytes → Option Digest} {F : KeccakState → Option KeccakState}
    {bytecode : List K} {input : PublicInput} {s : VerifierProgramState}
    {h : List Ev} {s' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (leanVmVerifierProgram bytecode (publicInputDigest input)) s h =
      some (true, s', hist)) :
    ∃ d, xrun H F (leanVmProgramG bytecode input) s h = some ((true, d), s', hist) := by
  rw [← leanVmProgramG_eq, xrun_bind] at hx
  obtain ⟨⟨⟨b, d⟩, s₁, h₁⟩, hr, hf⟩ := Option.bind_eq_some_iff.mp hx
  simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, rfl, rfl⟩ := hf
  exact ⟨d, hr⟩

/-- **The replay of the cut returns the ghost verifier's value**: where the ghost verifier's
extracted run returns, the cut's returns the same value, and so does the replay of the cut on
permutation answers agreeing with `F` on its inputs, at the cut run's state; that state's roots
hold the commitments of the ghost's whole history. -/
theorem replayU_cut {H : Bytes → Option Digest} {F F' : KeccakState → Option KeccakState}
    {bytecode : List K} {input : PublicInput}
    {s : VerifierProgramState} {h : List Ev} {a : Bool × ((Layout × ℕ) × WhirTrace)}
    {s' : VerifierProgramState} {hist : List Ev}
    (hx : xrun H F (leanVmProgramG bytecode input) s h = some (a, s', hist))
    (hR : RootsInv H s h)
    (hF : ∀ x ∈ replayIn F (leanVmProgramCut bytecode input) s, F' x = F x) :
    ∃ s₁ h₁, xrun H F (leanVmProgramCut bytecode input) s h = some (a, s₁, h₁) ∧
      replayU F' (leanVmProgramCut bytecode input) s = some (a, s₁) ∧
      commits hist = s₁.roots.map (fun r ↦ (r.2.1, r.2.2, extract H r.1 r.2.1 r.2.2)) ∧
      CutEnd F a s₁ := by
  obtain ⟨s₁, h₁, hc, ⟨l, rfl, hl⟩, hend⟩ := xcut_leanVmProgramG bytecode input s h a s' hist hx
  refine ⟨s₁, h₁, hc, ?_, ?_, hend⟩
  · rw [replayU_congr _ _ hF]
    exact replayU_of_xrun H F _ _ _ hc
  · rw [commits_append, hl, List.append_nil]
    exact xrun_rootsInv H F _ _ _ hR hc

end
end LeanVM.Protocol.Relation
