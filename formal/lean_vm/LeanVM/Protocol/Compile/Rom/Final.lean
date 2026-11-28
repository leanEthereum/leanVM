/-
  LeanVM.Protocol.Compile.Rom.Final

  The final inequality of the random-oracle theorem: if the compiled verifier accepts under the
  answers of a log without failure, and its extracted history passes through a doomed boundary,
  the potential of the log is one.
-/

module

public import LeanVM.Protocol.Compile.Rom.Known
public import LeanVM.Protocol.Compile.Rom.History
public import LeanVM.Protocol.Compile.Rom.Potential

/-!
# The final inequality

`final_ineq`: let `C : Cert P` be a doom certificate whose escape bound is below one at every
history without proof of work, `ℓ` a log without failure, and `π` a proof the seeded verifier
accepts with every query answered by `ℓ`. If some boundary prefix of the extracted history
(`extractedFrom`) is doomed, then `1 ≤ pot C.D σ P ℓ`.

The run is followed group by group. A *boundary* of the run is the seed or the point right after
a prover move (a scalar, a commitment, a proof of work). At each boundary `h`, with node `p`, the
sponge's state is decoded (`Known`) at a history and position from which its waiting scalars,
consumed, lead to `h` and `p` (`SpInv`), and the group starting at `h` is carried (`Carried`):

* after the seed no scalar waits, and the state's record has term at least `[D h] · gv ℓ u h p`
  (`seed_known`);
* after a proof of work no scalar waits and its permutation's challenge does (`ground`): the
  state's record has term at least `[D h] · gv1 ℓ u h p`, and the run's openings lead to the
  squeeze that returns that challenge, permuting nothing (`followGround`, `move`);
* after a scalar or a commitment, scalars wait, and the group's first squeeze, a permutation of
  them, is decoded as the record `sq h p` (`duplex_read`, `walk`), unless the group has no
  squeeze at all: then it is a run of openings, whose escape probability is `0` or `1`; the
  certificate bounds it by `C.ε h < 1`, so it is `0`.

The run's squeezes and openings until the next prover move or the verdict are the ones `gv`
follows (`follow`): the squeezes are lookups in `ℓ`, and the openings return the extracted rows
because the answers are injective (`answer_of_openPhase`). So the record's term is at least
`[D h] · esc D` at the group's end, which is `1` if `D h` holds there and not at the end
(`group`).

A packed draw's chunks are squeezes the decoder reads in the draw's middle (`squeeze_chunks`), as
`gv` follows them (`chunks`); right after a grind its first chunk is the grind's cells. A packed
message (a prover move, its scalars at least one: `PackedPos`) permutes what waits, then absorbs
its chunks, read in the message's middle (`absorb_chunks`); the last one's output is the state at
the boundary after it, recorded as `st h p none` (`move`).

The run's final history is not doomed (`Cert.final`) and prover moves keep doom (`Cert.read`,
`Cert.grind`, `Cert.commit`), so from the first doomed boundary some group leaves doom; its record
has term `1` (`from_boundary`). A prover move absorbs its scalars, a permutation being forced
when four wait (`absorb_step`): the decoder reads the forced permutation at its entry, and its
output is decoded at the move's position. Commitments read the word extracted from the entries
before their root is absorbed, which is the word extracted from the whole log (`duplex_read`).
A nonce's permutation is the proof of work's, decoded as the record `st h p (some (b, n))` whose
factor is the proof of work's result on its third lane, `1`.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom
open scoped ENNReal

@[expose] public section

/- The enumerations of `Digest` and `KState` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest instFintypeKState

variable {X : Type} {σ : Seeds X} {P : VerifierProgram Bool}

/-! ## The sponge in `Option` -/

theorem absorb_option (F : KeccakState → Option KeccakState) (sp : Sponge) (x : E) (tag : ℕ)
    (sp' : Sponge) :
    Compile.absorb (m := Option) F sp x tag = some sp' ↔
      if sp.pending.length = 4 then ∃ u, F (duplexInput sp) = some u ∧ sp' = ⟨u, [(x, tag)], sp.ground⟩
      else sp' = { sp with pending := sp.pending ++ [(x, tag)] } := by
  unfold Compile.absorb duplex
  split
  · rename_i h4
    simp only [rateScalars] at h4
    simp only [h4, ↓reduceIte, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
    constructor
    · rintro ⟨sp1, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, [], sp.ground⟩, ⟨u, hu, rfl⟩, rfl⟩
  · rename_i h4
    simp only [rateScalars] at h4
    simp [h4, pure, eq_comm]

theorem squeeze_option (F : KeccakState → Option KeccakState) {sp : Sponge}
    (hg : sp.ground = none) (r : E × Sponge) :
    squeeze (m := Option) F sp = some r ↔
      ∃ u, F (duplexInput sp) = some u ∧ r = (challengeOf u, ⟨u, [], none⟩) := by
  unfold squeeze duplex
  rw [hg]
  simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨sp1, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, [], none⟩, ⟨u, hu, rfl⟩, rfl⟩

/-- A squeeze returns the challenge a grind drew, permuting nothing. -/
theorem squeeze_ground (F : KeccakState → Option KeccakState) {sp : Sponge} {c : E}
    (hg : sp.ground = some c) :
    squeeze (m := Option) F sp = some (c, { sp with ground := none }) := by
  unfold squeeze
  rw [hg]
  rfl

/-- A grind's nonce: absorbed, then a permutation, whose third lane is the proof of work and whose
first two lanes the challenge kept for the next squeeze. -/
theorem absorbNonce_option (F : KeccakState → Option KeccakState) (sp : Sponge) (n : E)
    (r : UInt64 × Sponge) :
    absorbNonce (m := Option) F sp n = some r ↔
      ∃ sp1, Compile.absorb (m := Option) F sp n dsPowNonce = some sp1 ∧
        ∃ u, F (duplexInput sp1) = some u ∧
          r = (Keccak.lane u 2, ⟨u, [], some (challengeOf u)⟩) := by
  unfold absorbNonce duplex
  simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨sp1, h1, sp2, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨sp1, h1, u, hu, rfl⟩
  · rintro ⟨sp1, h1, u, hu, rfl⟩; exact ⟨sp1, h1, _, ⟨u, hu, rfl⟩, rfl⟩

/-- The loop of a packed draw: one squeeze, its first cells, then the rest. -/
theorem squeezePackedChunks_succ (F : KeccakState → Option KeccakState) (fuel missing : ℕ)
    (sp : Sponge) (r : List E × Sponge) :
    squeezePackedChunks (m := Option) F (fuel + 1) sp (missing + 1) = some r ↔
      ∃ u rest sp', F (duplexInput sp) = some u ∧
        squeezePackedChunks (m := Option) F fuel ⟨u, [], sp.ground⟩
          (missing + 1 - min (missing + 1) 8) = some (rest, sp') ∧
        r = ((cells8 u).take (missing + 1) ++ rest, sp') := by
  have ht : ∀ u, (List.range (min (missing + 1) 8)).map (packedChallengeOf u) =
      (cells8 u).take (missing + 1) := fun u ↦ by rw [take_cells8]
  simp only [squeezePackedChunks, duplex, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
    min_comm 8 (missing + 1)]
  constructor
  · rintro ⟨sp1, ⟨u, hu, rfl⟩, ⟨rest, sp'⟩, hrest, rfl⟩
    exact ⟨u, rest, sp', hu, hrest, by rw [← ht]⟩
  · rintro ⟨u, rest, sp', hu, hrest, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, (rest, sp'), hrest, by rw [← ht]⟩

theorem squeezePackedChunks_zero (F : KeccakState → Option KeccakState) (fuel : ℕ) (sp : Sponge) :
    squeezePackedChunks (m := Option) F fuel sp 0 = some ([], sp) := by
  cases fuel <;> rfl

/-- A packed draw with no challenge waiting is its loop. -/
theorem samplesPacked_none (F : KeccakState → Option KeccakState) {sp : Sponge}
    (hg : sp.ground = none) (n : ℕ) (r : List E × Sponge) :
    samplesPacked (m := Option) F sp n = some r ↔
      squeezePackedChunks (m := Option) F n sp n = some r := by
  unfold samplesPacked
  rcases n with _ | n
  · simp [squeezePackedChunks, bind, pure]
  · simp only [hg, List.length_nil, Nat.sub_zero, List.nil_append, bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq]
    constructor
    · rintro ⟨⟨a, b⟩, h, rfl⟩; exact h
    · intro h; exact ⟨r, h, rfl⟩

theorem groundCells_take_succ (u : KeccakState) (c : ℕ) :
    (groundCells u).take (c + 1) =
      challengeOf u :: ((List.range 6).take c).map (packedChallengeOf u ∘ (· + 2)) := by
  simp only [groundCells, List.take_succ_cons, List.map_take]
  rfl

/-- A packed draw right after a grind: the grind's cells, then the loop. -/
theorem samplesPacked_ground (F : KeccakState → Option KeccakState) {sp : Sponge}
    (hg : sp.ground = some (challengeOf sp.state)) {n : ℕ} (hn : 0 < n) (r : List E × Sponge) :
    samplesPacked (m := Option) F sp n = some r ↔
      ∃ rest sp', squeezePackedChunks (m := Option) F
          (n - ((groundCells sp.state).take n).length) { sp with ground := none }
          (n - ((groundCells sp.state).take n).length) = some (rest, sp') ∧
        r = ((groundCells sp.state).take n ++ rest, sp') := by
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  unfold samplesPacked
  simp only [hg, groundCells_take_succ, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨⟨a, b⟩, h, rfl⟩; exact ⟨a, b, h, rfl⟩
  · rintro ⟨a, b, h, rfl⟩; exact ⟨(a, b), h, rfl⟩

theorem absorbPackedChunks_nil (F : KeccakState → Option KeccakState) (fuel : ℕ)
    (state : KeccakState) : absorbPackedChunks (m := Option) F fuel state [] = some state := by
  cases fuel <;> rfl

theorem absorbPackedChunks_succ (F : KeccakState → Option KeccakState) (fuel : ℕ)
    (state : KeccakState) {vals : List E} (hv : vals ≠ []) (st : KeccakState) :
    absorbPackedChunks (m := Option) F (fuel + 1) state vals = some st ↔
      ∃ s1, F (packedInput state (vals.take 8)) = some s1 ∧
        absorbPackedChunks (m := Option) F fuel s1 (vals.drop 8) = some st := by
  rcases vals with _ | ⟨v, vs⟩
  · exact absurd rfl hv
  · simp only [absorbPackedChunks, bind, Option.bind_eq_some_iff]

/-- A packed message's absorption: a permutation of what waits, if anything, then its chunks. -/
theorem observePacked_option (F : KeccakState → Option KeccakState) (sp : Sponge) (vals : List E)
    (sp' : Sponge) :
    observePacked (m := Option) F sp vals = some sp' ↔
      ∃ sp1, (if sp.pending.isEmpty then some sp else duplex (m := Option) F sp) = some sp1 ∧
        ∃ st, absorbPackedChunks (m := Option) F vals.length sp1.state vals = some st ∧
          { sp1 with state := st } = sp' := by
  unfold observePacked
  simp only [bind, pure]
  split <;> simp only [Option.bind_eq_some_iff, Option.some.injEq]

/-! ## Histories without boundaries -/

/-- No prefix of `h'` strictly longer than `h` is a boundary. -/
def NoBnd (h h' : List Ev) : Prop :=
  ∀ n, h.length < n → n ≤ h'.length → ¬ Boundary (h'.take n)

theorem noBnd_refl (h : List Ev) : NoBnd h h := fun _ h1 h2 ↦ absurd h1 (by omega)

theorem noBnd_append_single {h : List Ev} {e : Ev} (he : ¬ Boundary (h ++ [e])) :
    NoBnd h (h ++ [e]) := by
  intro n h1 h2
  have : n = h.length + 1 := by simp at h2; omega
  subst this
  rw [List.take_of_length_le (by simp)]
  exact he

theorem noBnd_trans {h h₁ h₂ : List Ev} (h01 : NoBnd h h₁) (h12 : NoBnd h₁ h₂)
    (hp : h₁ <+: h₂) : NoBnd h h₂ := by
  intro n hn hn2
  by_cases hn1 : n ≤ h₁.length
  · obtain ⟨r, rfl⟩ := hp
    rw [List.take_append_of_le_length hn1]
    exact h01 n hn hn1
  · exact h12 n (by omega) hn2

/-- A prover move or the accepting verdict: where a group of challenges ends. -/
def Move : VerifierProgram Bool → Prop
  | .ret true => True
  | .read _ => True
  | .readPacked _ _ => True
  | .grind _ _ => True
  | .commit _ _ _ => True
  | _ => False

theorem esc_move {D : List Ev → Prop} {h : List Ev} {p : VerifierProgram Bool} (hm : Move p)
    (hD : ¬ D h) : esc D h p = 1 := by
  cases p with
  | ret a => cases a <;> simp_all [Move, esc]
  | read _ => simp [esc, hD]
  | readPacked _ _ => simp [esc, hD]
  | grind _ _ => simp [esc, hD]
  | commit _ _ _ => simp [esc, hD]
  | sample _ => exact absurd hm id
  | query _ _ _ => exact absurd hm id
  | fail => exact absurd hm id
  | samplePacked _ _ => exact absurd hm id

theorem not_query_of_move {p : VerifierProgram Bool} (hm : Move p) : ∀ i ps k, p ≠ .query i ps
    k := by
  rintro i ps k rfl; exact hm

/-! ## Openings between absorptions -/

/-- The run goes from `(h, p)` to `(h', p')` through openings only, each answered from the
history's words. -/
inductive QSteps : List Ev → VerifierProgram Bool → List Ev → VerifierProgram Bool → Prop where
  | refl (h : List Ev) (p : VerifierProgram Bool) : QSteps h p h p
  | step {h : List Ev} {i : ℕ} {ps : List ℕ} {k : List (List K) → VerifierProgram Bool}
      {rows : List (List K)} {h' : List Ev} {p' : VerifierProgram Bool} :
      answer h i ps = some rows → QSteps (h ++ [Ev.query rows]) (k rows) h' p' →
      QSteps h (.query i ps k) h' p'

theorem QSteps.snoc {h₁ h : List Ev} {p₁ : VerifierProgram Bool} {i : ℕ} {ps : List ℕ}
    {k : List (List K) → VerifierProgram Bool} {rows : List (List K)}
    (hq : QSteps h₁ p₁ h (.query i ps k)) (ha : answer h i ps = some rows) :
    QSteps h₁ p₁ (h ++ [Ev.query rows]) (k rows) := by
  generalize hp : (VerifierProgram.query i ps k : VerifierProgram Bool) = q at hq
  induction hq with
  | refl => subst hp; exact .step ha (.refl _ _)
  | step ha' _ ih => exact .step ha' (ih ha hp)

theorem settle_eq_of_qsteps {h₁ h : List Ev} {p₁ p : VerifierProgram Bool} (hq : QSteps h₁ p₁ h p) :
    settle h₁ p₁ = settle h p := by
  induction hq with
  | refl => rfl
  | step ha _ ih => simp only [settle, ha]; exact ih

theorem settle_self {h : List Ev} {q : VerifierProgram Bool} (hq : ∀ i ps k, q ≠ .query i ps k) :
    settle h q = some (h, q) := by
  cases q with
  | query i ps k => exact absurd rfl (hq i ps k)
  | _ => rfl

theorem esc_eq_of_qsteps (D : List Ev → Prop) {h h' : List Ev} {p p' : VerifierProgram Bool}
    (hq : QSteps h p h' p') : esc D h p = esc D h' p' := by
  induction hq with
  | refl => rfl
  | step ha _ ih => rw [esc_query, ha]; exact ih

theorem gvF_eq_of_qsteps (D : List Ev → Prop) (ℓ : Log) (L : List E) (u : KeccakState)
    {h h' : List Ev} {p p' : VerifierProgram Bool} (hq : QSteps h p h' p') :
    gvF D ℓ L u h p = gvF D ℓ L u h' p' := by
  induction hq with
  | refl => rfl
  | step ha _ ih => simp only [gvF, ha]; exact ih

/-- Nonempty packed messages along a history. -/
theorem packedPos_step {h h' : List Ev} {p p' : VerifierProgram Bool} (ha : P.after h = some p)
    (hpp : p.PackedPos) (hpre : h <+: h') (ha' : P.after h' = some p') : p'.PackedPos := by
  obtain ⟨l, rfl⟩ := hpre
  rw [VerifierProgram.after_append, ha, Option.bind_some] at ha'
  exact hpp.after l ha'

/-! ## Consumption, continued -/

/-- Consuming more scalars continues from where the first ones left. -/
theorem consume_append_done {W : Digest → ℕ → ℕ → Word} :
    ∀ (ps : List (E × ℕ)) (h : List Ev) (pos : Pos) {h' : List Ev} {pos' : Pos}
      (qs : List (E × ℕ)), consume W h pos ps = .done h' pos' →
        consume W h pos (ps ++ qs) = consume W h' pos' qs
  | [], h, pos, h', pos', qs, hc => by
    simp only [consume, Cons.done.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rfl
  | (x, tag) :: rest, h, .node p, h', pos', qs, hc => by
    simp only [List.cons_append, consume] at hc ⊢
    split at hc
    · split at hc
      · rename_i hs _
        simp only [↓reduceIte, *]
        exact consume_append_done rest _ _ qs hc
      · cases hc
    · split at hc
      · rename_i hs _
        simp only [↓reduceIte, *]
        exact consume_append_done rest _ _ qs hc
      · cases hc
    · split at hc <;> cases hc
    · cases hc
  | (x, tag) :: rest, h, .half ht w k x₀, h', pos', qs, hc => by
    simp only [List.cons_append, consume] at hc ⊢
    by_cases htag : tag = 1
    · simp only [htag, ↓reduceIte] at hc ⊢
      exact consume_append_done rest _ _ qs hc
    · simp only [htag, ↓reduceIte] at hc
      cases hc
  | (_, _) :: _, _, .rpk _ _ _, _, _, _, hc => by simp [consume] at hc
  | (_, _) :: _, _, .spk _ _ _, _, _, _, hc => by simp [consume] at hc

/-- A nonempty consumption ends at a node or in the middle of a commitment. -/
theorem consume_done_plain {W : Digest → ℕ → ℕ → Word} :
    ∀ (ps : List (E × ℕ)) (h : List Ev) (pos : Pos) {h' : List Ev} {n : ℕ}
      {k : List E → VerifierProgram Bool} {xs : List E}, ps ≠ [] →
      consume W h pos ps ≠ .done h' (.rpk n k xs) ∧ consume W h pos ps ≠ .done h' (.spk n k xs)
  | [], _, _, _, _, _, _, hne => absurd rfl hne
  | (x, tag) :: rest, h, pos, h', n, k, xs, _ => by
    rcases pos with p | ⟨ht, w, k', x₀⟩ | _ | _
    · simp only [consume]
      split
      · split
        · rcases rest with _ | ⟨y, rest'⟩
          · simp [consume]
          · exact consume_done_plain _ _ _ (by simp)
        · simp
      · split
        · rcases rest with _ | ⟨y, rest'⟩
          · simp [consume]
          · exact consume_done_plain _ _ _ (by simp)
        · simp
      · split <;> simp
      · simp
    · simp only [consume]
      split
      · rcases rest with _ | ⟨y, rest'⟩
        · simp [consume]
        · exact consume_done_plain _ _ _ (by simp)
      · simp
    · simp [consume]
    · simp [consume]

/-- A position from which a nonempty consumption runs is plain. -/
theorem plainPos_of_consume {W : Digest → ℕ → ℕ → Word} {ps : List (E × ℕ)} {h : List Ev}
    {pos : Pos} (hne : ps ≠ []) (hc : consume W h pos ps ≠ .bad) : PlainPos h pos := by
  rcases ps with _ | ⟨⟨x, tag⟩, rest⟩
  · exact absurd rfl hne
  rcases pos with p | ⟨ht, w, k, x₀⟩ | _ | _
  · intro h1 n k hs
    simp [consume, hs] at hc
  · trivial
  · simp [consume] at hc
  · simp [consume] at hc

/-- A node whose next operation is not a packed message is plain. -/
theorem plainPos_node {h h' : List Ev} {p q : VerifierProgram Bool} (hs : settle h p = some (h', q))
    (hq : ∀ n k, q ≠ .readPacked n k) : PlainPos h (.node p) := by
  intro h1 n k hs'
  rw [hs] at hs'
  cases hs'
  exact hq n k rfl

/-- A node at which the program absorbs a scalar. -/
def Absorbs : VerifierProgram Bool → Prop
  | .read _ => True
  | .grind _ _ => True
  | .commit _ _ _ => True
  | _ => False

/-! ## The sponge's invariant -/

/-- **The sponge at a point of the run.** Its waiting scalars are as the verifier keeps them; its
state's capacity is known at `(h₀, pos₀)`; consuming the waiting scalars from there, with the
whole log's words, reaches `(h₁, p₁)`, from which openings reach the run's `(h, p)`. -/
def SpInv (σ : Seeds X) (P : VerifierProgram Bool) (ℓ : Log) (sp : Sponge) (h : List Ev) (p :
    VerifierProgram Bool) :
    Prop :=
  ValidPending sp.pending ∧ sp.ground = none ∧ ∃ h₀ pos₀ h₁ p₁, Known σ P ℓ (capOf sp.state) (h₀, pos₀) ∧
    consume (extract (lookH ℓ)) h₀ pos₀ sp.pending = .done h₁ (.node p₁) ∧ QSteps h₁ p₁ h p

theorem SpInv.snoc {ℓ : Log} {sp : Sponge} {h : List Ev} {i : ℕ} {ps : List ℕ}
    {k : List (List K) → VerifierProgram Bool} {rows : List (List K)}
    (hs : SpInv σ P ℓ sp h (.query i ps k)) (ha : answer h i ps = some rows) :
    SpInv σ P ℓ sp (h ++ [Ev.query rows]) (k rows) := by
  obtain ⟨hv, hg, h₀, pos₀, h₁, p₁, hk, hc, hq⟩ := hs
  exact ⟨hv, hg, h₀, pos₀, h₁, p₁, hk, hc, hq.snoc ha⟩

/-- **An absorption under the invariant.** Absorbing one scalar, when the program absorbs next,
keeps the state known, a forced permutation being read by the decoder, and the waiting scalars
consume as before, then the new one. -/
theorem absorb_step {ℓ : Log} (hf : ¬ Fail σ ℓ) {sp : Sponge} {h₀ h₁ : List Ev} {pos₀ pos₁ : Pos}
    (hk : Known σ P ℓ (capOf sp.state) (h₀, pos₀)) (hv : ValidPending sp.pending)
    (hc : consume (extract (lookH ℓ)) h₀ pos₀ sp.pending = .done h₁ pos₁)
    (habs : ∀ p₁, pos₁ = .node p₁ → ∃ h' q, settle h₁ p₁ = some (h', q) ∧ Absorbs q)
    {x : E} {tag : ℕ} (htag : tag = 1 ∨ tag = 4) {sp' : Sponge}
    (ha : Compile.absorb (m := Option) (lookF ℓ) sp x tag = some sp') :
    ValidPending sp'.pending ∧ sp'.pending ≠ [] ∧ sp'.ground = sp.ground ∧
      ∃ h₀' pos₀', Known σ P ℓ (capOf sp'.state) (h₀', pos₀') ∧
        consume (extract (lookH ℓ)) h₀' pos₀' sp'.pending =
          consume (extract (lookH ℓ)) h₁ pos₁ [(x, tag)] := by
  rw [absorb_option] at ha
  split at ha
  · rename_i h4
    obtain ⟨v, hl, rfl⟩ := ha
    refine ⟨⟨by simp, by simpa using htag⟩, by simp, rfl, ?_⟩
    rw [duplexInput_eq] at hl
    have hne4 : sp.pending ≠ [] := by intro h0; rw [h0] at h4; simp at h4
    obtain ⟨-, hkn⟩ := duplex_read hf hk
      (plainPos_of_consume (ps := sp.pending) hne4 (by rw [hc]; simp)) hv hl
    rw [hc] at hkn
    rcases pos₁ with p₁ | ⟨ht, w, k, x₀⟩ | ⟨n, k, xs⟩ | ⟨n, k, cs⟩
    · obtain ⟨h', q, hs, habq⟩ := habs p₁ rfl
      have hq : ∀ i ps k, q ≠ .query i ps k := by rintro i ps k rfl; exact habq
      have hcons : consume (extract (lookH ℓ)) h' (.node q) [(x, tag)] =
          consume (extract (lookH ℓ)) h₁ (.node p₁) [(x, tag)] := by
        simp only [consume, settle_self hq, hs]
      cases q with
      | read k =>
        refine ⟨h', .node (.read k), hkn _ ?_, hcons⟩
        simp [decodeAt, hs, forced, h4]
      | commit ht w k =>
        refine ⟨h', .node (.commit ht w k), hkn _ ?_, hcons⟩
        simp [decodeAt, hs, forced, h4]
      | grind b k =>
        refine ⟨h', .node (.grind b k), hkn _ ?_, hcons⟩
        simp [decodeAt, hs, forced, h4]
      | _ => exact absurd habq id
    · exact ⟨h₁, .half ht w k x₀, hkn _ (by simp [decodeAt, h4]), rfl⟩
    · exact absurd hc (consume_done_plain _ _ _ hne4).1
    · exact absurd hc (consume_done_plain _ _ _ hne4).2
  · rename_i h4
    subst ha
    refine ⟨⟨by have := hv.1; simp; omega, ?_⟩, by simp, rfl, h₀, pos₀, hk, ?_⟩
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact hv.2 e he
      · rw [List.mem_singleton] at he; subst he; exact htag
    · exact consume_append_done _ _ _ _ hc

/-! ## Packed draws and packed messages along the run -/

/-- The decoder knows a state from which a packed draw of `n` challenges, `cs` drawn, squeezes its
next chunk: in the middle of the draw, or, with nothing drawn, at a node whose openings lead to
the draw. -/
def DrawKnown (σ : Seeds X) (P : VerifierProgram Bool) (ℓ : Log) (c : Fin 9 → UInt64)
    (h : List Ev) (n : ℕ) (k : List E → VerifierProgram Bool) (cs : List E) : Prop :=
  Known σ P ℓ c (h, .spk n k cs) ∨
    (cs = [] ∧ ∃ h₀ p₀, Known σ P ℓ c (h₀, .node p₀) ∧ settle h₀ p₀ = some (h, .samplePacked n k))

/-- A chunk of a packed draw from a known state is decoded. -/
theorem draw_read {ℓ : Log} (hf : ¬ Fail σ ℓ) {c : Fin 9 → UInt64} {h : List Ev} {n : ℕ}
    {k : List E → VerifierProgram Bool} {cs : List E} (hd : DrawKnown σ P ℓ c h n k cs)
    {v : KeccakState} (hl : lookF ℓ (duplexOf c []) = some v) :
    Known σ P ℓ (capOf v) (drawInfo h n k cs ((cells8 v).take (n - cs.length))) := by
  rcases hd with hk | ⟨rfl, h₀, p₀, hk, hs⟩
  · exact spk_read hf hk hl
  · obtain ⟨-, hkn⟩ := duplex_read hf hk (plainPos_node hs (by intros; simp)) (ps := [])
      ⟨by simp, by simp⟩ hl
    exact hkn _ (by simp [consume, decodeAt, hs])

/-- **The rest of a packed draw**, run from a known state with nothing waiting: its chunks are the
ones `chunks` follows, and the state after it is known at the node after the draw. -/
theorem squeeze_chunks {ℓ : Log} (hf : ¬ Fail σ ℓ) {h : List Ev} {n : ℕ}
    {k : List E → VerifierProgram Bool} (fin : List E → KeccakState → ℝ≥0∞)
    (rest : List E → ℝ≥0∞) :
    ∀ (fuel : ℕ) (sp : Sponge) (cs : List E) {ds : List E} {sp' : Sponge},
      sp.pending = [] → sp.ground = none → DrawKnown σ P ℓ (capOf sp.state) h n k cs →
      cs.length < n → n - cs.length ≤ fuel →
      squeezePackedChunks (m := Option) (lookF ℓ) fuel sp (n - cs.length) = some (ds, sp') →
      sp'.pending = [] ∧ sp'.ground = none ∧ (cs ++ ds).length = n ∧
        Known σ P ℓ (capOf sp'.state) (h ++ [Ev.samplePacked (cs ++ ds)], .node (k (cs ++ ds))) ∧
        chunks ℓ fin rest n sp.state cs = fin (cs ++ ds) sp'.state
  | 0, _, cs, _, _, _, _, _, hlt, hle, _ => by omega
  | fuel + 1, sp, cs, ds, sp', hpe, hg, hd, hlt, hle, hrun => by
    obtain ⟨m, hm⟩ : ∃ m, n - cs.length = m + 1 := ⟨n - cs.length - 1, by omega⟩
    rw [hm, squeezePackedChunks_succ] at hrun
    obtain ⟨u, rest1, sp1, hu, hrest, hr⟩ := hrun
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hdup : duplexInput sp = duplexOf (capOf sp.state) [] := by rw [duplexInput_eq, hpe]
    rw [hdup] at hu
    have hkn := draw_read hf hd hu
    rw [hm] at hkn
    rw [chunks_some (fin := fin) (rest := rest) (n := n) cs
      (show lookF ℓ (sqIn sp.state) = some u from hu), hm]
    have hlen : (cs ++ (cells8 u).take (m + 1)).length = cs.length + min (m + 1) 8 := by simp
    have hmc := min_choice (m + 1) 8
    have hm1 := Nat.min_le_left (m + 1) 8
    have hm2 := Nat.min_le_right (m + 1) 8
    by_cases hc : n ≤ (cs ++ (cells8 u).take (m + 1)).length
    · have hz : m + 1 - min (m + 1) 8 = 0 := by rw [hlen] at hc; omega
      rw [hz, squeezePackedChunks_zero] at hrest
      simp only [Option.some.injEq, Prod.mk.injEq] at hrest
      obtain ⟨rfl, rfl⟩ := hrest
      simp only [drawInfo, hc, ↓reduceIte] at hkn
      have hfin : drawVal (fun cs' ↦ fin cs' u) (chunks ℓ fin rest n u) n
          (cs ++ (cells8 u).take (m + 1)) = fin (cs ++ (cells8 u).take (m + 1)) u := by
        simp only [drawVal, hc, ↓reduceIte]
      rw [hfin, List.append_nil]
      exact ⟨rfl, hg, by omega, hkn, rfl⟩
    · simp only [drawInfo, hc, ↓reduceIte] at hkn
      have hm' : n - (cs ++ (cells8 u).take (m + 1)).length = m + 1 - min (m + 1) 8 := by
        rw [hlen]; omega
      rw [← hm'] at hrest
      obtain ⟨hpe', hg', hl', hk', hch'⟩ := squeeze_chunks hf fin rest fuel ⟨u, [], sp.ground⟩
        (cs ++ (cells8 u).take (m + 1)) rfl hg (Or.inl hkn) (by omega)
        (by rw [hm']; rw [hlen] at hc; omega) hrest
      simp only [List.append_assoc] at hl' hk' hch'
      refine ⟨hpe', hg', hl', hk', ?_⟩
      simp only [drawVal, hc, ↓reduceIte]
      exact hch'

/-- The decoder knows a state from which a packed message of `n` scalars, `xs` absorbed, absorbs
its next chunk: in the middle of the message, or, with nothing absorbed, at a node whose openings
lead to the message. -/
def PkKnown (σ : Seeds X) (P : VerifierProgram Bool) (ℓ : Log) (c : Fin 9 → UInt64)
    (h : List Ev) (n : ℕ) (k : List E → VerifierProgram Bool) (xs : List E) : Prop :=
  Known σ P ℓ c (h, .rpk n k xs) ∨
    (xs = [] ∧ ∃ h₀ p₀, Known σ P ℓ c (h₀, .node p₀) ∧ settle h₀ p₀ = some (h, .readPacked n k))

/-- A chunk of a packed message from a known state is decoded. -/
theorem pk_read {ℓ : Log} (hf : ¬ Fail σ ℓ) {c : Fin 9 → UInt64} {h : List Ev} {n : ℕ}
    {k : List E → VerifierProgram Bool} {xs : List E} (hd : PkKnown σ P ℓ c h n k xs)
    {ys : List E} (hys : (cells8 (packedOf c ys)).take (n - xs.length) = ys) {v : KeccakState}
    (hl : lookF ℓ (packedOf c ys) = some v) :
    ((readChunk h n k xs ys).1, v) ∈ (decode σ P ℓ).kinds ∧
      ∀ inf, (readChunk h n k xs ys).2 v = some inf → Known σ P ℓ (capOf v) inf := by
  rcases hd with hk | ⟨rfl, h₀, p₀, hk, hs⟩
  · exact chunk_read hf hk hys hl
  · exact chunk_read_node hf hk hs (by simpa using hys) hl

theorem take_cells8_chunk (c : Fin 9 → UInt64) (vals : List E) :
    (cells8 (packedOf c (vals.take 8))).take vals.length = vals.take 8 := by
  have h8 : (vals.take 8).length ≤ 8 := by simp
  have := take_cells8_packedOf c h8
  rw [take_cells8] at this ⊢
  rw [show min vals.length 8 = min (vals.take 8).length 8 by simp; omega]
  exact this

/-- **A packed message's chunks**, absorbed from a known state: the last one's output is the
state at the boundary after the message, recorded and known. -/
theorem absorb_chunks {ℓ : Log} (hf : ¬ Fail σ ℓ) {h : List Ev} {n : ℕ}
    {k : List E → VerifierProgram Bool} :
    ∀ (fuel : ℕ) (state : KeccakState) (xs vals : List E) {st : KeccakState},
      PkKnown σ P ℓ (capOf state) h n k xs → xs.length + vals.length = n → vals ≠ [] →
      vals.length ≤ fuel →
      absorbPackedChunks (m := Option) (lookF ℓ) fuel state vals = some st →
      (Shape.st (h ++ [Ev.readPacked (xs ++ vals)]) (k (xs ++ vals)) none, st) ∈
          (decode σ P ℓ).kinds ∧
        Known σ P ℓ (capOf st) (h ++ [Ev.readPacked (xs ++ vals)], .node (k (xs ++ vals)))
  | 0, _, _, vals, _, _, _, hne, hle, _ =>
    absurd (List.length_eq_zero_iff.mp (by omega)) hne
  | fuel + 1, state, xs, vals, st, hd, hlen, hne, hle, hrun => by
    rw [absorbPackedChunks_succ _ _ _ hne] at hrun
    obtain ⟨s1, hs1, hrest⟩ := hrun
    rw [packedInput_eq] at hs1
    have hys : (cells8 (packedOf (capOf state) (vals.take 8))).take (n - xs.length) =
        vals.take 8 := by
      rw [show n - xs.length = vals.length by omega]; exact take_cells8_chunk _ _
    obtain ⟨hkind, hkn⟩ := pk_read hf hd hys hs1
    by_cases hc : vals.length ≤ 8
    · have ht : vals.take 8 = vals := List.take_of_length_le hc
      rw [List.drop_eq_nil_of_le hc, absorbPackedChunks_nil] at hrest
      cases hrest
      have hcomp : n ≤ (xs ++ vals).length := by simp; omega
      simp only [readChunk, ht, hcomp, ↓reduceIte] at hkind hkn
      exact ⟨hkind, hkn _ rfl⟩
    · have hl8' : (vals.take 8).length = 8 := List.length_take_of_le (by omega)
      have hcomp : ¬ n ≤ (xs ++ vals.take 8).length := by
        simp only [List.length_append, hl8']; omega
      simp only [readChunk, hcomp, ↓reduceIte] at hkn
      have hk1 := hkn _ rfl
      have hne' : vals.drop 8 ≠ [] := by
        intro h0
        have := congrArg List.length h0
        simp at this
        omega
      have hmc := Nat.min_le_left 8 vals.length
      have hl8 : (vals.take 8).length = 8 := by simp; omega
      have := absorb_chunks hf fuel s1 (xs ++ vals.take 8) (vals.drop 8) (Or.inl hk1)
        (by simp only [List.length_append, List.length_drop, hl8]; omega) hne'
        (by simp only [List.length_drop]; omega) hrest
      simpa only [List.append_assoc, List.take_append_drop] using this

/-- What the decoder knows of the state a grind's permutation left at `(h, p)`, its challenge
waiting: after the openings, at the squeeze that returns that challenge, or at a packed draw whose
first chunk the grind's cells are. -/
def GroundKnown (σ : Seeds X) (P : VerifierProgram Bool) (ℓ : Log) (u : KeccakState)
    (h : List Ev) (p : VerifierProgram Bool) : Prop :=
  (∀ h₁ k, settle h p = some (h₁, .sample k) →
    Known σ P ℓ (capOf u) (h₁ ++ [Ev.sample (challengeOf u)], .node (k (challengeOf u)))) ∧
  (∀ h₁ n k, settle h p = some (h₁, .samplePacked n k) →
    Known σ P ℓ (capOf u) (drawInfo h₁ n k [] ((groundCells u).take n)))

/-! ## Following a group -/

section Follow

variable {G : List Ev → Prop} (C : CertG P G) {ℓ : Log}

/-- **Following a group with no scalar waiting.** From a state the decoder knows, the run's
squeezes and openings up to the next prover move or the verdict are those `gv` follows. -/
theorem follow (hf : ¬ Fail σ ℓ) :
    ∀ (p : VerifierProgram Bool) (s : VerifierProgramState) (h : List Ev) {s_f :
        VerifierProgramState} {hist : List Ev},
      RootsInv (lookH ℓ) s h → P.Reachable h → P.after h = some p → p.PackedPos →
      s.sponge.pending = [] → SpInv σ P ℓ s.sponge h p →
      xrun (lookH ℓ) (lookF ℓ) p s h = some (true, s_f, hist) →
      ∃ (p_e : VerifierProgram Bool) (s_e : VerifierProgramState) (h_e : List Ev),
        gv C.D ℓ s.sponge.state h p = esc C.D h_e p_e ∧
        xrun (lookH ℓ) (lookF ℓ) p_e s_e h_e = some (true, s_f, hist) ∧
        RootsInv (lookH ℓ) s_e h_e ∧ P.Reachable h_e ∧ P.after h_e = some p_e ∧
        SpInv σ P ℓ s_e.sponge h_e p_e ∧ Move p_e ∧ h <+: h_e ∧ NoBnd h h_e ∧
        s_e.stream = s.stream
  | .ret true, s, h, _, _, hR, hr, ha, _, _, hsp, hx =>
    ⟨.ret true, s, h, rfl, hx, hR, hr, ha, hsp, trivial, List.prefix_refl _, noBnd_refl h, rfl⟩
  | .ret false, s, h, _, _, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .fail, s, h, _, _, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .read k, s, h, _, _, hR, hr, ha, _, _, hsp, hx =>
    ⟨.read k, s, h, rfl, hx, hR, hr, ha, hsp, trivial, List.prefix_refl _, noBnd_refl h, rfl⟩
  | .readPacked n k, s, h, _, _, hR, hr, ha, _, _, hsp, hx =>
    ⟨.readPacked n k, s, h, rfl, hx, hR, hr, ha, hsp, trivial, List.prefix_refl _, noBnd_refl h,
      rfl⟩
  | .grind b k, s, h, _, _, hR, hr, ha, _, _, hsp, hx =>
    ⟨.grind b k, s, h, rfl, hx, hR, hr, ha, hsp, trivial, List.prefix_refl _, noBnd_refl h,
      rfl⟩
  | .commit ht w k, s, h, _, _, hR, hr, ha, _, _, hsp, hx =>
    ⟨.commit ht w k, s, h, rfl, hx, hR, hr, ha, hsp, trivial, List.prefix_refl _, noBnd_refl h,
      rfl⟩
  | .sample k, s, h, s_f, hist, hR, hr, ha, hpp, hpe, hsp, hx => by
    simp only [xrun, Option.bind_eq_some_iff] at hx
    obtain ⟨r, hr0, hx⟩ := hx
    obtain ⟨hv, hg0, h₀, pos₀, h₁, p₁, hk, hc, hq⟩ := hsp
    obtain ⟨u, hu, rfl⟩ := (squeeze_option _ hg0 _).mp hr0
    rw [duplexInput_eq, hpe] at hu
    rw [hpe] at hc
    simp only [consume, Cons.done.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hsq : settle h₀ p₁ = some (h, .sample k) := by
      rw [settle_eq_of_qsteps hq]; rfl
    obtain ⟨-, hkn⟩ := duplex_read hf hk (plainPos_node hsq (by intros; simp)) (ps := [])
      ⟨by simp, by simp⟩ hu
    have hk' : Known σ P ℓ (capOf u)
        (h ++ [Ev.sample (challengeOf u)], .node (k (challengeOf u))) :=
      hkn _ (by simp [consume, decodeAt, hsq])
    have hr' := VerifierProgram.Reachable.sample (challengeOf u) hr ha
    have ha' := after_sample_step ha (challengeOf u)
    obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
      follow hf (k (challengeOf u)) { s with sponge := ⟨u, [], none⟩ } _
        (rootsInv_append_sample hR _ _) hr' ha'
        (packedPos_step ha hpp (List.prefix_append _ _) ha') rfl
        ⟨⟨by simp, by simp⟩, rfl, _, _, _, _, hk', rfl, .refl _ _⟩ hx
    refine ⟨p_e, s_e, h_e, ?_, hx', hR', hre, hae, hse, hm,
      (List.prefix_append _ _).trans hp, ?_, hst⟩
    · have hsqIn : sqIn s.sponge.state = duplexOf (capOf s.sponge.state) [] := rfl
      simp only [gv, hsqIn, hu]
      exact hg
    · exact noBnd_trans (noBnd_append_single (not_boundary_append_sample h _)) hnb hp
  | .samplePacked n k, s, h, s_f, hist, hR, hr, ha, hpp, hpe, hsp, hx => by
    simp only [xrun, Option.bind_eq_some_iff] at hx
    obtain ⟨⟨ds, sp'⟩, hr0, hx⟩ := hx
    obtain ⟨hv, hg0, h₀, pos₀, h₁, p₁, hk, hc, hq⟩ := hsp
    rw [samplesPacked_none _ hg0] at hr0
    rw [hpe] at hc
    simp only [consume, Cons.done.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hsq : settle h₀ p₁ = some (h, .samplePacked n k) := by
      rw [settle_eq_of_qsteps hq]; rfl
    have hn : 0 < n := hpp.1
    obtain ⟨hpe', hg', hl', hk', hch'⟩ := squeeze_chunks hf (h := h) (n := n) (k := k)
      (fun cs u ↦ gv C.D ℓ u (h ++ [Ev.samplePacked cs]) (k cs))
      (restAvg (fun cs ↦ esc C.D (h ++ [Ev.samplePacked cs]) (k cs)) n) n s.sponge []
      hpe hg0 (Or.inr ⟨rfl, h₀, p₁, hk, hsq⟩) (by simpa using hn) (by simp)
      (by simpa using hr0)
    simp only [List.nil_append] at hl' hk' hch'
    have hr' := VerifierProgram.Reachable.samplePacked ds hr ha hl'
    have ha' := after_samplePacked_step ha hl'
    obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
      follow hf (k ds) { s with sponge := sp' } _
        (rootsInv_append_samplePacked hR _ _) hr' ha'
        (packedPos_step ha hpp (List.prefix_append _ _) ha') hpe'
        ⟨by rw [hpe']; exact ⟨by simp, by simp⟩, hg', _, _, _, _, hk', by simp [hpe', consume],
          .refl _ _⟩ hx
    refine ⟨p_e, s_e, h_e, ?_, hx', hR', hre, hae, hse, hm,
      (List.prefix_append _ _).trans hp, ?_, hst⟩
    · simp only [gv]
      rw [hch']
      exact hg
    · exact noBnd_trans (noBnd_append_single (not_boundary_append_samplePacked h _)) hnb hp
  | .query i ps k, s, h, s_f, hist, hR, hr, ha, hpp, hpe, hsp, hx => by
    simp only [xrun] at hx
    split at hx
    · next root ht w phase rest hroot hphase =>
      split at hx
      · next rows ho =>
        have hans := answer_of_openPhase (answersInj_lookH hf) hR hroot ho
        have hr' := VerifierProgram.Reachable.query hr ha hans
        have ha' := after_query_step ha rows
        obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
          follow hf (k rows) { s with openings := rest } _ (rootsInv_append_query hR rows rest)
            hr' ha' (packedPos_step ha hpp (List.prefix_append _ _) ha') hpe (hsp.snoc hans) hx
        refine ⟨p_e, s_e, h_e, ?_, hx', hR', hre, hae, hse, hm,
          (List.prefix_append _ _).trans hp, ?_, hst⟩
        · simp only [gv, hans]
          exact hg
        · exact noBnd_trans (noBnd_append_single (not_boundary_append_query h _)) hnb hp
      · simp at hx
    · simp at hx

/-- **Walking a group's openings with scalars waiting.** From a boundary `(h, p)` at which the
waiting scalars, consumed, end, the run's openings lead either to the group's first squeeze, a
permutation of the waiting scalars decoded as the record `sq h p`, and the rest of the group, or
to a prover move or the verdict with no squeeze at all. -/
theorem walk (hf : ¬ Fail σ ℓ) {h : List Ev} {p : VerifierProgram Bool} {h₀ : List Ev} {pos₀
    : Pos} :
    ∀ (p' : VerifierProgram Bool) (s : VerifierProgramState) (h' : List Ev) {s_f :
        VerifierProgramState} {hist : List Ev},
      Known σ P ℓ (capOf s.sponge.state) (h₀, pos₀) → ValidPending s.sponge.pending →
      s.sponge.ground = none → s.sponge.pending ≠ [] →
      consume (extract (lookH ℓ)) h₀ pos₀ s.sponge.pending = .done h (.node p) →
      QSteps h p h' p' →
      RootsInv (lookH ℓ) s h' → P.Reachable h' → P.after h' = some p' → p'.PackedPos →
      xrun (lookH ℓ) (lookF ℓ) p' s h' = some (true, s_f, hist) →
      ∃ (p_e : VerifierProgram Bool) (s_e : VerifierProgramState) (h_e : List Ev),
        xrun (lookH ℓ) (lookF ℓ) p_e s_e h_e = some (true, s_f, hist) ∧
        RootsInv (lookH ℓ) s_e h_e ∧ P.Reachable h_e ∧ P.after h_e = some p_e ∧
        (p_e ≠ .ret true → SpInv σ P ℓ s_e.sponge h_e p_e) ∧ Move p_e ∧ h' <+: h_e ∧
        NoBnd h' h_e ∧ s_e.stream = s.stream ∧
        ((∃ κ ∈ (decode σ P ℓ).kinds, ind (C.D h) * esc C.D h_e p_e ≤ term C.D ℓ κ) ∨
          esc C.D h p = esc C.D h_e p_e)
  | .sample k, s, h', s_f, hist, hk, hv, hg0, hne, hc, hq, hR, hr, ha, hpp, hx => by
    simp only [xrun, Option.bind_eq_some_iff] at hx
    obtain ⟨r, hr0, hx⟩ := hx
    obtain ⟨u, hu, rfl⟩ := (squeeze_option _ hg0 _).mp hr0
    rw [duplexInput_eq] at hu
    obtain ⟨hkind, hkn⟩ := duplex_read hf hk
      (plainPos_of_consume hne (by rw [hc]; simp)) hv hu
    rw [hc] at hkind hkn
    have hsq : settle h p = some (h', .sample k) := by
      rw [settle_eq_of_qsteps hq]; rfl
    have hdec : decodeAt (.done h (.node p)) s.sponge.pending =
        (.sq h p, fun u ↦ some (h' ++ [Ev.sample (challengeOf u)], .node (k (challengeOf u)))) := by
      simp [decodeAt, hsq, hne]
    rw [hdec] at hkind hkn
    have hk' := hkn _ rfl
    have hr' := VerifierProgram.Reachable.sample (challengeOf u) hr ha
    have ha' := after_sample_step ha (challengeOf u)
    obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
      follow C hf (k (challengeOf u)) { s with sponge := ⟨u, [], none⟩ } _
        (rootsInv_append_sample hR _ _) hr' ha'
        (packedPos_step ha hpp (List.prefix_append _ _) ha') rfl
        ⟨⟨by simp, by simp⟩, rfl, _, _, _, _, hk', rfl, .refl _ _⟩ hx
    refine ⟨p_e, s_e, h_e, hx', hR', hre, hae, fun _ ↦ hse, hm, (List.prefix_append _ _).trans hp,
      noBnd_trans (noBnd_append_single (not_boundary_append_sample h' _)) hnb hp, hst,
      Or.inl ⟨_, hkind, ?_⟩⟩
    simp only [term, gv1, gvF_eq_of_qsteps C.D ℓ _ u hq, gvF, headD_cells8]
    rw [← hg]
  | .samplePacked n k, s, h', s_f, hist, hk, hv, hg0, hne, hc, hq, hR, hr, ha, hpp, hx => by
    simp only [xrun, Option.bind_eq_some_iff] at hx
    obtain ⟨⟨ds, sp'⟩, hr0, hx⟩ := hx
    rw [samplesPacked_none _ hg0] at hr0
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hpp.1; omega⟩
    rw [squeezePackedChunks_succ] at hr0
    obtain ⟨u, rest1, sp1, hu, hrest, hr⟩ := hr0
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [duplexInput_eq] at hu
    obtain ⟨hkind, hkn⟩ := duplex_read hf hk
      (plainPos_of_consume hne (by rw [hc]; simp)) hv hu
    rw [hc] at hkind hkn
    have hsq : settle h p = some (h', .samplePacked (m + 1) k) := by
      rw [settle_eq_of_qsteps hq]; rfl
    have hdec : decodeAt (.done h (.node p)) s.sponge.pending =
        (.sq h p, fun u ↦ some (drawInfo h' (m + 1) k [] ((cells8 u).take (m + 1)))) := by
      simp [decodeAt, hsq, hne]
    rw [hdec] at hkind hkn
    have hk1 := hkn _ rfl
    -- the rest of the draw, and the term's group value, from the first chunk
    have hgv : gv1 C.D ℓ u h p = drawVal
        (fun cs ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
        (chunks ℓ (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
          (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) (m + 1)) (m + 1) u)
        (m + 1) ((cells8 u).take (m + 1)) := by
      simp only [gv1, gvF_eq_of_qsteps C.D ℓ _ u hq, gvF]
    have hlen : ((cells8 u).take (m + 1)).length = min (m + 1) 8 := by simp
    have hmc := min_choice (m + 1) 8
    have hm1 := Nat.min_le_left (m + 1) 8
    have hm2 := Nat.min_le_right (m + 1) 8
    obtain ⟨hpe', hg', hl', hk', hch'⟩ : sp'.pending = [] ∧ sp'.ground = none ∧
        ((cells8 u).take (m + 1) ++ rest1).length = m + 1 ∧
        Known σ P ℓ (capOf sp'.state) (h' ++ [Ev.samplePacked ((cells8 u).take (m + 1) ++ rest1)],
          .node (k ((cells8 u).take (m + 1) ++ rest1))) ∧
        drawVal (fun cs ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
          (chunks ℓ (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
            (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) (m + 1)) (m + 1) u)
          (m + 1) ((cells8 u).take (m + 1)) =
          gv C.D ℓ sp'.state (h' ++ [Ev.samplePacked ((cells8 u).take (m + 1) ++ rest1)])
            (k ((cells8 u).take (m + 1) ++ rest1)) := by
      by_cases hcomp : m + 1 ≤ ((cells8 u).take (m + 1)).length
      · have hz : m + 1 - min (m + 1) 8 = 0 := by omega
        rw [hz, squeezePackedChunks_zero] at hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        simp only [drawInfo, List.nil_append, hcomp, ↓reduceIte] at hk1
        have hfin : drawVal (fun cs ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
            (chunks ℓ (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
              (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) (m + 1)) (m + 1) u)
            (m + 1) ((cells8 u).take (m + 1)) =
            gv C.D ℓ u (h' ++ [Ev.samplePacked ((cells8 u).take (m + 1))])
              (k ((cells8 u).take (m + 1))) := by
          simp only [drawVal, hcomp, ↓reduceIte]
        rw [hfin, List.append_nil]
        exact ⟨rfl, hg0, by omega, hk1, rfl⟩
      · simp only [drawInfo, List.nil_append, hcomp, ↓reduceIte] at hk1
        have hm' : m + 1 - ((cells8 u).take (m + 1)).length = m + 1 - min (m + 1) 8 := by
          omega
        rw [← hm'] at hrest
        simp only [hg0] at hrest
        obtain ⟨hpe', hg', hl', hk', hch'⟩ := squeeze_chunks hf (h := h') (n := m + 1) (k := k)
          (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
          (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) (m + 1)) m
          ⟨u, [], none⟩ ((cells8 u).take (m + 1)) rfl rfl (Or.inl hk1) (by omega) (by omega)
          hrest
        refine ⟨hpe', hg', hl', hk', ?_⟩
        simp only [drawVal, hcomp, ↓reduceIte]
        exact hch'
    set ds := (cells8 u).take (m + 1) ++ rest1 with hds
    have hr' := VerifierProgram.Reachable.samplePacked ds hr ha hl'
    have ha' := after_samplePacked_step ha hl'
    obtain ⟨p_e, s_e, h_e, hg, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
      follow C hf (k ds) { s with sponge := sp' } _
        (rootsInv_append_samplePacked hR _ _) hr' ha'
        (packedPos_step ha hpp (List.prefix_append _ _) ha') hpe'
        ⟨by rw [hpe']; exact ⟨by simp, by simp⟩, hg', _, _, _, _, hk', by simp [hpe', consume],
          .refl _ _⟩ hx
    refine ⟨p_e, s_e, h_e, hx', hR', hre, hae, fun _ ↦ hse, hm, (List.prefix_append _ _).trans hp,
      noBnd_trans (noBnd_append_single (not_boundary_append_samplePacked h' _)) hnb hp, hst,
      Or.inl ⟨_, hkind, ?_⟩⟩
    simp only [term]
    rw [hgv, hch', ← hg]
  | .query i ps k, s, h', s_f, hist, hk, hv, hg0, hne, hc, hq, hR, hr, ha, hpp, hx => by
    simp only [xrun] at hx
    split at hx
    · next root ht w phase rest hroot hphase =>
      split at hx
      · next rows ho =>
        have hans := answer_of_openPhase (answersInj_lookH hf) hR hroot ho
        have hr' := VerifierProgram.Reachable.query hr ha hans
        have ha' := after_query_step ha rows
        obtain ⟨p_e, s_e, h_e, hx', hR', hre, hae, hse, hm, hp, hnb, hst, hres⟩ :=
          walk hf (k rows) { s with openings := rest } _ hk hv hg0 hne hc (hq.snoc hans)
            (rootsInv_append_query hR rows rest) hr' ha'
            (packedPos_step ha hpp (List.prefix_append _ _) ha') hx
        exact ⟨p_e, s_e, h_e, hx', hR', hre, hae, hse, hm, (List.prefix_append _ _).trans hp,
          noBnd_trans (noBnd_append_single (not_boundary_append_query h' _)) hnb hp, hst, hres⟩
      · simp at hx
    · simp at hx
  | .ret true, s, h', _, _, hk, hv, hg0, _, hc, hq, hR, hr, ha, _, hx =>
    ⟨.ret true, s, h', hx, hR, hr, ha, fun _ ↦ ⟨hv, hg0, _, _, _, _, hk, hc, hq⟩, trivial,
      List.prefix_refl _, noBnd_refl _, rfl, Or.inr (esc_eq_of_qsteps C.D hq)⟩
  | .ret false, s, h', _, _, _, _, _, _, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .fail, s, h', _, _, _, _, _, _, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .read k', s, h', _, _, hk, hv, hg0, _, hc, hq, hR, hr, ha, _, hx =>
    ⟨.read k', s, h', hx, hR, hr, ha, fun _ ↦ ⟨hv, hg0, _, _, _, _, hk, hc, hq⟩, trivial,
      List.prefix_refl _, noBnd_refl _, rfl, Or.inr (esc_eq_of_qsteps C.D hq)⟩
  | .readPacked n k', s, h', _, _, hk, hv, hg0, _, hc, hq, hR, hr, ha, _, hx =>
    ⟨.readPacked n k', s, h', hx, hR, hr, ha, fun _ ↦ ⟨hv, hg0, _, _, _, _, hk, hc, hq⟩, trivial,
      List.prefix_refl _, noBnd_refl _, rfl, Or.inr (esc_eq_of_qsteps C.D hq)⟩
  | .grind b k', s, h', _, _, hk, hv, hg0, _, hc, hq, hR, hr, ha, _, hx =>
    ⟨.grind b k', s, h', hx, hR, hr, ha, fun _ ↦ ⟨hv, hg0, _, _, _, _, hk, hc, hq⟩, trivial,
      List.prefix_refl _, noBnd_refl _, rfl, Or.inr (esc_eq_of_qsteps C.D hq)⟩
  | .commit ht w k', s, h', _, _, hk, hv, hg0, _, hc, hq, hR, hr, ha, _, hx =>
    ⟨.commit ht w k', s, h', hx, hR, hr, ha, fun _ ↦ ⟨hv, hg0, _, _, _, _, hk, hc, hq⟩, trivial,
      List.prefix_refl _, noBnd_refl _, rfl, Or.inr (esc_eq_of_qsteps C.D hq)⟩

/-- **Following a group whose first challenge a grind drew.** From the state a grind's
permutation left, its challenge waiting, the run's openings lead to the squeeze that returns that
challenge, or to a packed draw that takes the grind's cells first, and from there the group is
followed as `gv` follows it; or to the verdict with no squeeze. -/
theorem followGround (hf : ¬ Fail σ ℓ) {h : List Ev} {p : VerifierProgram Bool} :
    ∀ (p' : VerifierProgram Bool) (s : VerifierProgramState) (h' : List Ev) {s_f :
        VerifierProgramState} {hist : List Ev},
      s.sponge.pending = [] → s.sponge.ground = some (challengeOf s.sponge.state) →
      GroundKnown σ P ℓ s.sponge.state h p → QSteps h p h' p' →
      RootsInv (lookH ℓ) s h' → P.Reachable h' → P.after h' = some p' → p'.PackedPos →
      xrun (lookH ℓ) (lookF ℓ) p' s h' = some (true, s_f, hist) →
      ∃ (p_e : VerifierProgram Bool) (s_e : VerifierProgramState) (h_e : List Ev),
        gvG C.D ℓ s.sponge.state h p = esc C.D h_e p_e ∧
        xrun (lookH ℓ) (lookF ℓ) p_e s_e h_e = some (true, s_f, hist) ∧
        RootsInv (lookH ℓ) s_e h_e ∧ P.Reachable h_e ∧ P.after h_e = some p_e ∧
        (p_e ≠ .ret true → SpInv σ P ℓ s_e.sponge h_e p_e) ∧ Move p_e ∧ h' <+: h_e ∧
        NoBnd h' h_e ∧ s_e.stream = s.stream
  | .sample k, s, h', s_f, hist, hpe, hg, hgk, hq, hR, hr, ha, hpp, hx => by
    simp only [xrun, squeeze_ground _ hg, Option.bind_some] at hx
    have hsq : settle h p = some (h', .sample k) := by
      rw [settle_eq_of_qsteps hq]; rfl
    have hk' := hgk.1 _ _ hsq
    have hr' := VerifierProgram.Reachable.sample (challengeOf s.sponge.state) hr ha
    have ha' := after_sample_step ha (challengeOf s.sponge.state)
    obtain ⟨p_e, s_e, h_e, hgv, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
      follow C hf (k (challengeOf s.sponge.state))
        { s with sponge := { s.sponge with ground := none } } _
        (rootsInv_append_sample hR _ _) hr' ha'
        (packedPos_step ha hpp (List.prefix_append _ _) ha') hpe
        ⟨⟨by simp [hpe], by simp [hpe]⟩, rfl, _, _, _, _, hk', by simp [hpe, consume],
          .refl _ _⟩ hx
    refine ⟨p_e, s_e, h_e, ?_, hx', hR', hre, hae, fun _ ↦ hse, hm,
      (List.prefix_append _ _).trans hp,
      noBnd_trans (noBnd_append_single (not_boundary_append_sample h' _)) hnb hp, hst⟩
    simp only [gvG, gvF_eq_of_qsteps C.D ℓ _ _ hq, gvF, headD_groundCells]
    exact hgv
  | .samplePacked n k, s, h', s_f, hist, hpe, hg, hgk, hq, hR, hr, ha, hpp, hx => by
    simp only [xrun, Option.bind_eq_some_iff] at hx
    obtain ⟨⟨ds, sp'⟩, hr0, hx⟩ := hx
    rw [samplesPacked_ground _ hg hpp.1] at hr0
    obtain ⟨rest1, sp1, hrest, hr⟩ := hr0
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hsq : settle h p = some (h', .samplePacked n k) := by
      rw [settle_eq_of_qsteps hq]; rfl
    have hk1 := hgk.2 _ _ _ hsq
    set u := s.sponge.state with hu
    have hgv : gvG C.D ℓ u h p = drawVal
        (fun cs ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
        (chunks ℓ (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
          (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) n) n u)
        n ((groundCells u).take n) := by
      simp only [gvG, gvF_eq_of_qsteps C.D ℓ _ u hq, gvF]
    obtain ⟨hpe', hg', hl', hk', hch'⟩ : sp'.pending = [] ∧ sp'.ground = none ∧
        ((groundCells u).take n ++ rest1).length = n ∧
        Known σ P ℓ (capOf sp'.state) (h' ++ [Ev.samplePacked ((groundCells u).take n ++ rest1)],
          .node (k ((groundCells u).take n ++ rest1))) ∧
        drawVal (fun cs ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
          (chunks ℓ (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
            (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) n) n u)
          n ((groundCells u).take n) =
          gv C.D ℓ sp'.state (h' ++ [Ev.samplePacked ((groundCells u).take n ++ rest1)])
            (k ((groundCells u).take n ++ rest1)) := by
      by_cases hcomp : n ≤ ((groundCells u).take n).length
      · have hz : n - ((groundCells u).take n).length = 0 := by omega
        rw [hz, squeezePackedChunks_zero] at hrest
        simp only [Option.some.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        simp only [drawInfo, List.nil_append, hcomp, ↓reduceIte] at hk1
        have hfin : drawVal (fun cs ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
            (chunks ℓ (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
              (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) n) n u)
            n ((groundCells u).take n) =
            gv C.D ℓ u (h' ++ [Ev.samplePacked ((groundCells u).take n)])
              (k ((groundCells u).take n)) := by
          simp only [drawVal, hcomp, ↓reduceIte]
        rw [hfin, List.append_nil]
        exact ⟨hpe, rfl, by simp only [List.length_take] at hcomp ⊢; omega, hk1, rfl⟩
      · simp only [drawInfo, List.nil_append, hcomp, ↓reduceIte] at hk1
        obtain ⟨hpe', hg', hl', hk', hch'⟩ := squeeze_chunks hf (h := h') (n := n) (k := k)
          (fun cs u ↦ gv C.D ℓ u (h' ++ [Ev.samplePacked cs]) (k cs))
          (restAvg (fun cs ↦ esc C.D (h' ++ [Ev.samplePacked cs]) (k cs)) n) _
          { s.sponge with ground := none } ((groundCells u).take n) hpe rfl (Or.inl hk1)
          (by omega) le_rfl hrest
        refine ⟨hpe', hg', hl', hk', ?_⟩
        simp only [drawVal, hcomp, ↓reduceIte]
        exact hch'
    set ds := (groundCells u).take n ++ rest1 with hds
    have hr' := VerifierProgram.Reachable.samplePacked ds hr ha hl'
    have ha' := after_samplePacked_step ha hl'
    obtain ⟨p_e, s_e, h_e, hgv', hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
      follow C hf (k ds) { s with sponge := sp' } _
        (rootsInv_append_samplePacked hR _ _) hr' ha'
        (packedPos_step ha hpp (List.prefix_append _ _) ha') hpe'
        ⟨by rw [hpe']; exact ⟨by simp, by simp⟩, hg', _, _, _, _, hk', by simp [hpe', consume],
          .refl _ _⟩ hx
    refine ⟨p_e, s_e, h_e, ?_, hx', hR', hre, hae, fun _ ↦ hse, hm,
      (List.prefix_append _ _).trans hp,
      noBnd_trans (noBnd_append_single (not_boundary_append_samplePacked h' _)) hnb hp, hst⟩
    rw [hgv, hch']
    exact hgv'
  | .query i ps k, s, h', s_f, hist, hpe, hg, hgk, hq, hR, hr, ha, hpp, hx => by
    simp only [xrun] at hx
    split at hx
    · next root ht w phase rest hroot hphase =>
      split at hx
      · next rows ho =>
        have hans := answer_of_openPhase (answersInj_lookH hf) hR hroot ho
        have hr' := VerifierProgram.Reachable.query hr ha hans
        have ha' := after_query_step ha rows
        obtain ⟨p_e, s_e, h_e, hgv, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
          followGround hf (k rows) { s with openings := rest } _ hpe hg hgk (hq.snoc hans)
            (rootsInv_append_query hR rows rest) hr' ha'
            (packedPos_step ha hpp (List.prefix_append _ _) ha') hx
        exact ⟨p_e, s_e, h_e, hgv, hx', hR', hre, hae, hse, hm,
          (List.prefix_append _ _).trans hp,
          noBnd_trans (noBnd_append_single (not_boundary_append_query h' _)) hnb hp, hst⟩
      · simp at hx
    · simp at hx
  | .ret true, s, h', _, _, _, _, _, hq, hR, hr, ha, _, hx =>
    ⟨.ret true, s, h', by rw [gvG, gvF_eq_of_qsteps C.D ℓ _ _ hq]; rfl, hx, hR, hr, ha,
      fun hne ↦ absurd rfl hne, trivial, List.prefix_refl _, noBnd_refl _, rfl⟩
  | .ret false, s, h', _, _, _, _, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .fail, s, h', _, _, _, _, _, _, _, _, _, _, hx => by simp [xrun] at hx
  | .read k', s, h', _, _, _, hg, _, _, _, _, _, _, hx => by
    simp only [xrun, hg] at hx
    split at hx <;> simp_all
  | .readPacked n k', s, h', _, _, _, hg, _, _, _, _, _, _, hx => by
    simp [xrun, hg] at hx
  | .grind b k', s, h', _, _, _, hg, _, _, _, _, _, _, hx => by
    simp only [xrun, hg] at hx
    split at hx <;> simp_all
  | .commit ht w k', s, h', _, _, _, hg, _, _, _, _, _, _, hx => by
    simp only [xrun, hg] at hx
    split at hx <;> simp_all

/-- The group at a boundary is carried: after the seed or a packed message, with no scalar
waiting, by the state's record; after a scalar or a commitment, with scalars waiting, at a history
without proof of work, by the record of the group's first squeeze. -/
def Carried {G : List Ev → Prop} (C : CertG P G) (ℓ : Log) (s : VerifierProgramState) (h : List Ev) (p : VerifierProgram
    Bool) : Prop :=
  (s.sponge.pending = [] ∧ ∃ κ ∈ (decode σ P ℓ).kinds,
    ind (C.D h) * gv C.D ℓ s.sponge.state h p ≤ term C.D ℓ κ) ∨
  (s.sponge.pending ≠ [] ∧ grindBits h = 0)

/-- **The run at a boundary.** Either no challenge waits, the sponge's state is known at a
history and position from which its waiting scalars lead to `(h, p)`, and the group is carried;
or a grind's permutation left the state, its challenge waiting, and the group is carried by the
grind's record. -/
def BInv {G : List Ev → Prop} (C : CertG P G) (ℓ : Log) (s : VerifierProgramState) (h : List Ev)
    (p : VerifierProgram Bool) : Prop :=
  (s.sponge.ground = none ∧ ValidPending s.sponge.pending ∧
    (∃ h₀ pos₀, Known σ P ℓ (capOf s.sponge.state) (h₀, pos₀) ∧
      consume (extract (lookH ℓ)) h₀ pos₀ s.sponge.pending = .done h (.node p)) ∧
    Carried (σ := σ) C ℓ s h p) ∨
  (s.sponge.pending = [] ∧ s.sponge.ground = some (challengeOf s.sponge.state) ∧
    GroundKnown σ P ℓ s.sponge.state h p ∧
    ∃ κ ∈ (decode σ P ℓ).kinds, ind (C.D h) * gvG C.D ℓ s.sponge.state h p ≤ term C.D ℓ κ)

/-- **A group.** From a boundary whose group is carried, the run reaches the next prover move or
the verdict; either a record bounds `[D h]` times the escape probability there, or the group has
no squeeze and its escape probability is the one at its start. -/
theorem group (hf : ¬ Fail σ ℓ) {p : VerifierProgram Bool} {s : VerifierProgramState} {h : List Ev}
    {s_f : VerifierProgramState}
    {hist : List Ev} (hR : RootsInv (lookH ℓ) s h) (hr : P.Reachable h)
    (ha : P.after h = some p) (hpp : p.PackedPos) (hB : BInv (σ := σ) C ℓ s h p)
    (hx : xrun (lookH ℓ) (lookF ℓ) p s h = some (true, s_f, hist)) :
    ∃ (p_e : VerifierProgram Bool) (s_e : VerifierProgramState) (h_e : List Ev),
      xrun (lookH ℓ) (lookF ℓ) p_e s_e h_e = some (true, s_f, hist) ∧
      RootsInv (lookH ℓ) s_e h_e ∧ P.Reachable h_e ∧ P.after h_e = some p_e ∧
      (p_e ≠ .ret true → SpInv σ P ℓ s_e.sponge h_e p_e) ∧ Move p_e ∧ h <+: h_e ∧
      NoBnd h h_e ∧ s_e.stream = s.stream ∧
      ((∃ κ ∈ (decode σ P ℓ).kinds, ind (C.D h) * esc C.D h_e p_e ≤ term C.D ℓ κ) ∨
        (esc C.D h p = esc C.D h_e p_e ∧ grindBits h = 0)) := by
  rcases hB with ⟨hg0, hv, ⟨h₀, pos₀, hk, hc⟩, hcar⟩ | ⟨hpe, hg, hgk, κ, hκ, hterm⟩
  · rcases hcar with ⟨hpe, κ, hκ, hterm⟩ | ⟨hne, hg⟩
    · obtain ⟨p_e, s_e, h_e, hgv, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
        follow C hf p s h hR hr ha hpp hpe ⟨hv, hg0, h₀, pos₀, h, p, hk, hc, .refl _ _⟩ hx
      exact ⟨p_e, s_e, h_e, hx', hR', hre, hae, fun _ ↦ hse, hm, hp, hnb, hst,
        Or.inl ⟨κ, hκ, by rw [← hgv]; exact hterm⟩⟩
    · obtain ⟨p_e, s_e, h_e, hx', hR', hre, hae, hse, hm, hp, hnb, hst, hres⟩ :=
        walk C hf p s h hk hv hg0 hne hc (.refl _ _) hR hr ha hpp hx
      exact ⟨p_e, s_e, h_e, hx', hR', hre, hae, hse, hm, hp, hnb, hst,
        hres.imp id fun he ↦ ⟨he, hg⟩⟩
  · obtain ⟨p_e, s_e, h_e, hgv, hx', hR', hre, hae, hse, hm, hp, hnb, hst⟩ :=
      followGround C hf p s h hpe hg hgk (.refl _ _) hR hr ha hpp hx
    exact ⟨p_e, s_e, h_e, hx', hR', hre, hae, hse, hm, hp, hnb, hst,
      Or.inl ⟨κ, hκ, by rw [← hgv]; exact hterm⟩⟩

end Follow

/-! ## Prover moves -/

section Move

variable {G : List Ev → Prop} (C : CertG P G) {ℓ : Log}

/-- **A prover move.** From the run at a prover move, with the sponge's invariant, the run
reaches the next boundary, where the run's invariant holds and the group is carried; doom is
kept. -/
theorem move (hf : ¬ Fail σ ℓ) {p : VerifierProgram Bool} (hm : Move p) (hp : ∀ a, p ≠ .ret a) {s :
    VerifierProgramState}
    {h : List Ev} {s_f : VerifierProgramState} {hist : List Ev} (hR : RootsInv (lookH ℓ) s h)
    (hr : P.Reachable h) (ha : P.after h = some p) (hpp : p.PackedPos)
    (hsp : SpInv σ P ℓ s.sponge h p)
    (hx : xrun (lookH ℓ) (lookF ℓ) p s h = some (true, s_f, hist)) :
    ∃ (s' : VerifierProgramState) (h' : List Ev) (p' : VerifierProgram Bool),
      s'.stream.length < s.stream.length ∧ RootsInv (lookH ℓ) s' h' ∧ P.Reachable h' ∧
      Boundary h' ∧ P.after h' = some p' ∧ BInv (σ := σ) C ℓ s' h' p' ∧
      xrun (lookH ℓ) (lookF ℓ) p' s' h' = some (true, s_f, hist) ∧
      (C.D h → C.D h') ∧ h <+: h' ∧ h'.length = h.length + 1 := by
  obtain ⟨hv, hg0, h₀, pos₀, h₁, p₁, hk, hc, hq⟩ := hsp
  have hset : settle h₁ p₁ = some (h, p) := by
    rw [settle_eq_of_qsteps hq, settle_self (not_query_of_move hm)]
  cases p with
  | ret a => exact absurd rfl (hp a)
  | sample _ => exact absurd hm id
  | query _ _ _ => exact absurd hm id
  | fail => exact absurd hm id
  | samplePacked _ _ => exact absurd hm id
  | readPacked n k =>
    have hn : 0 < n := hpp.1
    simp only [xrun] at hx
    split at hx
    · rename_i hcond
      simp only [Option.bind_eq_some_iff] at hx
      obtain ⟨sp', hob, hx⟩ := hx
      have hxl : (s.stream.take n).length = n := by simp; omega
      rw [observePacked_option] at hob
      obtain ⟨sp1, hsp1, st, hst, rfl⟩ := hob
      have hpk : PkKnown σ P ℓ (capOf sp1.state) h n k [] ∧ sp1.pending = [] ∧
          sp1.ground = s.sponge.ground := by
        by_cases hpe : s.sponge.pending = []
        · simp only [hpe, List.isEmpty_nil, ↓reduceIte, Option.some.injEq] at hsp1
          subst hsp1
          rw [hpe] at hc
          simp only [consume, Cons.done.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          exact ⟨Or.inr ⟨rfl, h₀, p₁, hk, hset⟩, hpe, rfl⟩
        · have hpe' : s.sponge.pending.isEmpty = false := by
            cases hps : s.sponge.pending with
            | nil => exact absurd hps hpe
            | cons _ _ => rfl
          simp only [hpe', Bool.false_eq_true, ↓reduceIte, duplex, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] at hsp1
          obtain ⟨u0, hu0, rfl⟩ := hsp1
          rw [duplexInput_eq] at hu0
          obtain ⟨-, hkn⟩ := duplex_read hf hk (plainPos_of_consume hpe (by rw [hc]; simp)) hv hu0
          rw [hc] at hkn
          exact ⟨Or.inl (hkn (h, .rpk n k []) (by simp [decodeAt, hset, hpe])), rfl, rfl⟩
      obtain ⟨hpk, hpe1, hg1⟩ := hpk
      have hne : s.stream.take n ≠ [] := by
        intro h0; rw [h0] at hxl; simp at hxl; omega
      obtain ⟨hkind, hk1⟩ := absorb_chunks hf _ sp1.state [] (s.stream.take n) hpk
        (by simpa using hxl) hne le_rfl hst
      simp only [List.nil_append] at hkind hk1
      have hr' := VerifierProgram.Reachable.readPacked _ hr ha hxl
      have ha' := after_readPacked_step ha hxl
      refine ⟨{ s with sponge := { sp1 with state := st }, stream := s.stream.drop n },
        h ++ [Ev.readPacked (s.stream.take n)], k (s.stream.take n),
        by simp only [List.length_drop]; omega,
        rootsInv_append_readPacked hR _ _ _, hr', boundary_append_readPacked h _, ha',
        Or.inl ⟨hg1.trans hg0, ⟨by simp [hpe1], by simp [hpe1]⟩,
          ⟨_, _, hk1, by simp [hpe1, consume]⟩, Or.inl ⟨hpe1, _, hkind, ?_⟩⟩, hx,
        fun hD ↦ C.readPacked _ hr ha hxl hD, List.prefix_append _ _, by simp⟩
      simp only [term, powF, stGv, one_mul, le_refl]
    · simp at hx
  | read k =>
    rcases hs : s.stream with _ | ⟨x, xs⟩
    · simp [xrun, hs] at hx
    · simp only [xrun, hs, hg0, Option.bind_eq_some_iff] at hx
      obtain ⟨sp', hab, hx⟩ := hx
      obtain ⟨hv', hne', hg', h₀', pos₀', hk', hc'⟩ := absorb_step hf hk hv hc
        (fun p₁' he ↦ by cases he; exact ⟨h, _, hset, trivial⟩) (Or.inl rfl) hab
      have hr' := VerifierProgram.Reachable.read x hr ha
      have ha' := after_read_step ha x
      refine ⟨_, h ++ [Ev.read x], k x, by simp, rootsInv_append_read hR x sp' xs, hr',
        boundary_append_read h x, ha', Or.inl ⟨hg'.trans hg0, hv', ⟨h₀', pos₀', hk', ?_⟩,
        Or.inr ⟨hne', grindBits_append_read h x⟩⟩, hx, fun hD ↦ C.read x hr ha hD,
        List.prefix_append _ _, by simp⟩
      rw [hc']
      simp [consume, hset]
  | grind b k =>
    rcases hs : s.stream with _ | ⟨n, xs⟩
    · simp [xrun, hs] at hx
    · simp only [xrun, hs, hg0, Option.bind_eq_some_iff] at hx
      obtain ⟨r, hr0, hx⟩ := hx
      obtain ⟨sp1, hab, u, hu, rfl⟩ := (absorbNonce_option _ _ _ _).mp hr0
      obtain ⟨hv', hne1, -, h₀', pos₀', hk', hc'⟩ := absorb_step hf hk hv hc
        (fun p₁' he ↦ by cases he; exact ⟨h, _, hset, trivial⟩) (Or.inr rfl) hab
      have hgrd : consume (extract (lookH ℓ)) h₀' pos₀' sp1.pending = .grd h b k n := by
        rw [hc']
        simp [consume, hset]
      split at hx
      · rename_i hpow
        rw [duplexInput_eq] at hu
        obtain ⟨hkind, hkn⟩ := duplex_read hf hk'
          (plainPos_of_consume hne1 (by rw [hgrd]; simp)) hv' hu
        rw [hgrd] at hkind hkn
        simp only [decodeAt] at hkind hkn
        have hgk : GroundKnown σ P ℓ u (h ++ [Ev.grind b]) k :=
          ⟨fun h₁' k' hs' ↦ hkn _ (by rw [hs']), fun h₁' n' k' hs' ↦ hkn _ (by rw [hs'])⟩
        have hr' := VerifierProgram.Reachable.grind hr ha
        have ha' := after_grind_step ha
        refine ⟨_, h ++ [Ev.grind b], k, by simp, rootsInv_append_grind hR b _ xs, hr',
          boundary_append_grind h b, ha', Or.inr ⟨rfl, rfl, hgk, _, hkind, ?_⟩, hx,
          fun hD ↦ C.grind hr ha hD, List.prefix_append _ _, by simp⟩
        simp only [term, powF, stGv, ind_of hpow, one_mul, le_refl]
      · simp at hx
  | commit ht w k =>
    rcases hs : s.stream with _ | ⟨x0, _ | ⟨x1, xs⟩⟩
    · simp [xrun, hs] at hx
    · simp [xrun, hs] at hx
    · simp only [xrun, hs, hg0, Option.bind_eq_some_iff] at hx
      obtain ⟨sp0, h0, sp1, h1, hx⟩ := hx
      obtain ⟨hv0, -, hg0', h₀', pos₀', hk0, hc0⟩ := absorb_step hf hk hv hc
        (fun p₁' he ↦ by cases he; exact ⟨h, _, hset, trivial⟩) (Or.inl rfl) h0
      have hc0' : consume (extract (lookH ℓ)) h₀' pos₀' sp0.pending =
          .done h (.half ht w k x0) := by
        rw [hc0]
        simp [consume, hset]
      obtain ⟨hv1, hne1, hg1, h₀'', pos₀'', hk1, hc1⟩ := absorb_step hf hk0 hv0 hc0'
        (fun p₁' he ↦ by cases he) (Or.inl rfl) h1
      set root := digestFromHalves (x0, x1)
      have hr' := VerifierProgram.Reachable.commit (extract (lookH ℓ) root ht w) hr ha
        (wellShaped_extract _ _ _ _)
      have ha' := after_commit_step ha (extract (lookH ℓ) root ht w)
      refine ⟨_, _, k, by simp, rootsInv_append_commit hR root ht w sp1 xs, hr',
        boundary_append_commit _ _ _ _, ha',
        Or.inl ⟨hg1.trans (hg0'.trans hg0), hv1, ⟨h₀'', pos₀'', hk1, ?_⟩,
          Or.inr ⟨hne1, grindBits_append_commit _ _ _ _⟩⟩, hx,
        fun hD ↦ C.commit _ hr ha (wellShaped_extract _ _ _ _) hD,
        List.prefix_append _ _, by simp⟩
      rw [hc1]
      simp [consume, root]

end Move

/-! ## The final inequality -/

section Final

variable {G : List Ev → Prop} (C : CertG P G) {ℓ : Log}

theorem eq_take_of_prefix {h₀ h₁ hist : List Ev} (h0 : h₀ <+: hist) (h1 : h₁ <+: hist)
    (hl : h₀.length ≤ h₁.length) : h₀ = h₁.take h₀.length :=
  List.prefix_iff_eq_take.mp (List.prefix_of_prefix_length_le h0 h1 hl)

theorem term_le_termSum {κ : Shape × KeccakState} (hκ : κ ∈ (decode σ P ℓ).kinds) :
    term C.D ℓ κ ≤ termSum C.D σ P ℓ :=
  List.single_le_sum (fun _ _ ↦ bot_le) _ (List.mem_map_of_mem hκ)

/-- **The run from a boundary.** From a boundary of an accepting run whose group is carried, if a
boundary at least as long on the extracted history is doomed, the records' terms sum to at least
one. -/
theorem from_boundary (hf : ¬ Fail σ ℓ) (hε1 : ∀ h, grindBits h = 0 → C.ε h < 1) {s_f :
    VerifierProgramState}
    {hist : List Ev} (hG : ¬ G hist) :
    ∀ (n : ℕ) (s : VerifierProgramState) (h : List Ev) (p : VerifierProgram Bool),
        s.stream.length < n →
      RootsInv (lookH ℓ) s h → P.Reachable h → P.after h = some p → p.PackedPos → Boundary h →
      BInv (σ := σ) C ℓ s h p → xrun (lookH ℓ) (lookF ℓ) p s h = some (true, s_f, hist) →
      (∃ h₀, h₀ <+: hist ∧ h.length ≤ h₀.length ∧ Boundary h₀ ∧ C.D h₀) →
      1 ≤ termSum C.D σ P ℓ
  | 0, _, _, _, hn, _, _, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, s, h, p, hn, hR, hr, ha, hpp, hb, hB, hx, hbad => by
    obtain ⟨p_e, s_e, h_e, hx', hR', hre, hae, hse, hm, hpre, hnb, hst, hres⟩ :=
      group C hf hR hr ha hpp hB hx
    have hppe := packedPos_step ha hpp hpre hae
    have hhist : h <+: hist := xrun_prefix _ _ _ _ _ hx
    have hehist : h_e <+: hist := xrun_prefix _ _ _ _ _ hx'
    by_cases hesc : C.D h ∧ ¬ C.D h_e
    · -- the group leaves doom
      rcases hres with ⟨κ, hκ, hterm⟩ | ⟨heq, hg⟩
      · calc (1 : ℝ≥0∞) = ind (C.D h) * esc C.D h_e p_e := by
              rw [ind_of hesc.1, one_mul, esc_move hm hesc.2]
          _ ≤ term C.D ℓ κ := hterm
          _ ≤ termSum C.D σ P ℓ := term_le_termSum C hκ
      · -- a group of openings only escapes with probability `0` or `1`; the certificate makes
        -- it `0`
        exfalso
        have h1 : esc C.D h p = 1 := by rw [heq, esc_move hm hesc.2]
        have h2 := esc_le_eps C hr hb ha hesc.1
        rw [h1] at h2
        exact absurd (hε1 h hg) (not_lt.mpr h2)
    have hcase : C.D h_e ∨ ¬ C.D h := by tauto
    -- a doomed boundary past `h` is past the group
    have hpast : ¬ C.D h → ∀ h₀, h₀ <+: hist → h.length ≤ h₀.length → Boundary h₀ → C.D h₀ →
        h_e.length < h₀.length := by
      intro hD h₀ hh₀ hl hb₀ hD₀
      by_contra hle
      rw [not_lt] at hle
      rcases Nat.lt_or_eq_of_le hl with hlt | heq
      · rw [eq_take_of_prefix hh₀ hehist hle] at hb₀
        exact hnb _ hlt hle hb₀
      · have : h₀ = h := by
          rw [eq_take_of_prefix hh₀ hhist (by omega), ← heq, List.take_length]
        exact hD (this ▸ hD₀)
    by_cases hret : p_e = .ret true
    · subst hret
      simp only [xrun, Option.some.injEq, Prod.mk.injEq] at hx'
      obtain ⟨-, -, rfl⟩ := hx'
      rcases hcase with hD | hD
      · exact absurd (C.final hre hae hD) hG
      · obtain ⟨h₀, hh₀, hl, hb₀, hD₀⟩ := hbad
        have := hpast hD h₀ hh₀ hl hb₀ hD₀
        have := hh₀.length_le
        omega
    have hpm : ∀ a, p_e ≠ .ret a := by
      intro a hpa
      subst hpa
      cases a
      · exact hm
      · exact hret rfl
    obtain ⟨s', h', p', hlt, hR'', hr'', hb'', ha'', hB'', hx'', hDD, hpre', hlen'⟩ :=
      move C hf hm hpm hR' hre hae hppe (hse hret) hx'
    refine from_boundary hf hε1 hG n s' h' p' (by rw [hst] at hlt; omega) hR'' hr'' ha''
      (packedPos_step hae hppe hpre' ha'') hb'' hB'' hx'' ?_
    rcases hcase with hD | hD
    · exact ⟨h', xrun_prefix _ _ _ _ _ hx'', le_rfl, hb'', hDD hD⟩
    · obtain ⟨h₀, hh₀, hl, hb₀, hD₀⟩ := hbad
      exact ⟨h₀, hh₀, by have := hpast hD h₀ hh₀ hl hb₀ hD₀; omega, hb₀, hD₀⟩

/-- **The final inequality.** If the seeded verifier of the statement `x`, whose root is a root
of the program, accepts `π` with every query answered by a log without failure, and some
boundary prefix of the extracted history past the root is doomed, while the extracted history
fails `G`, the potential of the log is at least one. The certificate's escape bounds are below one
at histories without proof of work. -/
theorem final_ineq (hf : ¬ Fail σ ℓ) (hε1 : ∀ h, grindBits h = 0 → C.ε h < 1) {x : X}
    {π : Proof} (hroot : RootOk P (σ.root x))
    (hv : verify (lookH ℓ) (lookF ℓ) (σ.seed x) (nodeAt P (σ.root x)) π = some true)
    (hG : ¬ G (extractedFrom (lookH ℓ) (lookF ℓ) (σ.seed x) (nodeAt P (σ.root x)) (σ.root x) π))
    (hbad : ∃ h₀, h₀ <+: extractedFrom (lookH ℓ) (lookF ℓ) (σ.seed x) (nodeAt P (σ.root x))
      (σ.root x) π ∧ (σ.root x).length ≤ h₀.length ∧ Boundary h₀ ∧ C.D h₀) :
    1 ≤ pot C.D σ P ℓ := by
  obtain ⟨seed, s, hseed, hx⟩ := xrun_of_verify_from (σ.root x) hv
  obtain ⟨hkind, hknown⟩ := seed_known (P := P) hf hseed hroot
  have hS : 1 ≤ termSum C.D σ P ℓ := by
    refine from_boundary C hf hε1 hG (π.stream.length + 1)
      ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ (σ.root x) (nodeAt P (σ.root x))
      (Nat.lt_succ_self _) ?_ hroot.1 (after_nodeAt hroot) hroot.2.2.2.2.2 hroot.2.1
      (Or.inl ⟨rfl, ⟨by simp, by simp⟩, ⟨_, _, hknown, rfl⟩, Or.inl ⟨rfl, _, hkind, ?_⟩⟩) hx hbad
    · show commits (σ.root x) = []
      exact hroot.2.2.2.1
    · simp only [term, powF, stGv, one_mul, le_refl]
  simp only [pot, hf, ↓reduceIte]
  exact le_min le_rfl hS

end Final

end
end LeanVM.Protocol.Compile.Rom
