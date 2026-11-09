/-
  LeanVM.Protocol.Compile.Rom.Decode

  Reading the random oracles' log back into the verifier program: which states are states of
  the Fiat-Shamir sponge, at which interactive history and position, and which log entries start
  a group of challenges.
-/

module

public import LeanVM.Protocol.Compile.Rom.Extract
public import LeanVM.Protocol.Compile.Prover

/-!
# Decoding a log

The random-oracle theorem (`LeanVM.Protocol.Compile.Rom.Sound`) reads the log of the random
oracles, entry by entry and in order, as moves of the verifier program `P` from the seed
(`decode`). The reading is a fold: each entry is read with the entries before it (`decStep`).
Only permutation entries are read; a hash entry leaves the decoder as it is.

## What a permutation entry is

The decoder keeps, for each capacity, the decoding of the sponge state with that capacity
(`Dec.info`): an interactive history and a position, a node of the program (`Pos.node`) or the
middle of a commitment whose root's first half has been absorbed (`Pos.half`). It also keeps one
record per permutation entry (`Dec.kinds`). An entry `(t, u)` is read as follows.

* **Seeding.** If, for some statement `x` of the family of seedings, the hash entries before it
  answer `x`'s seeding and `t` is its permutation input (`rootAt`), `u` is the seed: the state at
  `x`'s root history (`rootStep`, when that history is a root of the program, `RootOk`).
* **A permutation of the sponge.** Otherwise, if the capacity of `t` is decoded at a history `h`
  and position `pos`, the waiting scalars of `t` (`parsePending`) are consumed from there
  (`consume`): a scalar of tag `1` at a `read` node is the prover's scalar; at a `commit` node the
  root's first half, and at a `half` position its second half, which completes the commitment,
  recorded with the word extracted for the root from the hash entries *before* this one
  (`extract`); a scalar of tag `4` at a `grind` node, the last one, is the nonce. Openings take
  no query of the sponge: before each scalar the openings are followed, each answered from the
  extracted words (`settle`). Then (`decodeAt`):
  - after a nonce, the permutation is the proof of work's: its third lane's low bits are the check,
    and its first two lanes the challenge the next `sample` returns (`ground`), after the openings
    in between: `u` is the state after that challenge;
  - at a `sample` node (after the openings), the permutation is a squeeze: `u` is the state after
    the challenge `challengeOf u`;
  - with four scalars consumed and the program at an absorption (`read`, `commit`, `grind`, or in
    the middle of a commitment), the permutation is forced by a fifth absorption: `u` is the
    state at the same history and position, the queue emptied.

  Anything else is not decoded.

## The records

Each permutation entry gets a `Shape`, paired with its output in `Dec.kinds`: `st h p pw` if its
output is a state at the boundary history `h` with node `p`, after the seed (`pw = none`) or a
proof of work of `b` bits with nonce `n` (`pw = some (b, n)`); `sq h p` if it is the first
squeeze of the group starting at the boundary `h`, the scalars of the permutation being the
prover's last moves. The potential (`LeanVM.Protocol.Compile.Rom.Potential`) gives each record a
term. A squeeze after the seed, with no scalar waiting, gets no record: the state's record carries
its group. A proof of work's permutation draws the first challenge of its group itself, and its
record carries the group.

Every record and every decoded state carries a reachable history at which the program is at the
recorded node (`decode_ok`): the certificate's lemmas apply to them.

Nothing here assumes the log is free of failure; the reading is a function of the log. Its
agreement with the compiled verifier's run is proved, under no failure, in
`LeanVM.Protocol.Compile.Rom.Known` and `LeanVM.Protocol.Compile.Rom.Final`.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Rom

@[expose] public section

/-! ## Histories -/

theorem getLast?_append_single (h : List Ev) (e : Ev) : (h ++ [e]).getLast? = some e := by
  simp

theorem boundary_append_read (h : List Ev) (x : E) : Boundary (h ++ [Ev.read x]) := by
  unfold Boundary; split
  · simp_all
  · rw [getLast?_append_single]; trivial

theorem boundary_append_grind (h : List Ev) (b : ℕ) : Boundary (h ++ [Ev.grind b]) := by
  unfold Boundary; split
  · simp_all
  · rw [getLast?_append_single]; trivial

theorem boundary_append_commit (h : List Ev) (ht w : ℕ) (W : Word) :
    Boundary (h ++ [Ev.commit ht w W]) := by
  unfold Boundary; split
  · simp_all
  · rw [getLast?_append_single]; trivial

theorem not_boundary_append_sample (h : List Ev) (c : E) : ¬ Boundary (h ++ [Ev.sample c]) := by
  unfold Boundary; split
  · simp_all
  · rw [getLast?_append_single]; simp

theorem not_boundary_append_query (h : List Ev) (rows : List (List K)) :
    ¬ Boundary (h ++ [Ev.query rows]) := by
  unfold Boundary; split
  · simp_all
  · rw [getLast?_append_single]; simp

theorem grindBits_nil : grindBits [] = 0 := rfl

theorem grindBits_append_read (h : List Ev) (x : E) : grindBits (h ++ [Ev.read x]) = 0 := by
  simp [grindBits]

theorem grindBits_append_commit (h : List Ev) (ht w : ℕ) (W : Word) :
    grindBits (h ++ [Ev.commit ht w W]) = 0 := by
  simp [grindBits]

theorem grindBits_append_grind (h : List Ev) (b : ℕ) : grindBits (h ++ [Ev.grind b]) = b := by
  simp [grindBits]

/-! ## Settling openings -/

/-- Follow the openings at a node, each answered from the words of the history: the history and
node at the next operation that is not an opening, `none` at an opening of a missing
commitment. -/
def settle : List Ev → VerifierProgram Bool → Option (List Ev × VerifierProgram Bool)
  | h, .query i ps k => match answer h i ps with
    | some rows => settle (h ++ [Ev.query rows]) (k rows)
    | none => none
  | h, p => some (h, p)

/-- Settling keeps reachability. -/
theorem settle_ok {P : VerifierProgram Bool} :
    ∀ (p : VerifierProgram Bool) (h : List Ev) {h' : List Ev} {p' : VerifierProgram Bool},
        P.Reachable h →
      P.after h = some p → settle h p = some (h', p') → P.Reachable h' ∧ P.after h' = some p'
  | .query i ps k, h, h', p', hr, ha, hs => by
    simp only [settle] at hs
    split at hs
    · rename_i rows hrows
      refine settle_ok (k rows) _ (VerifierProgram.Reachable.query hr ha hrows) ?_ hs
      rw [VerifierProgram.after_append_single _ ha]
      simp [VerifierProgram.after]
    · simp at hs
  | .ret _, h, _, _, hr, ha, hs => by
    simp only [settle, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hr, ha⟩
  | .fail, h, _, _, hr, ha, hs => by
    simp only [settle, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hr, ha⟩
  | .read _, h, _, _, hr, ha, hs => by
    simp only [settle, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hr, ha⟩
  | .sample _, h, _, _, hr, ha, hs => by
    simp only [settle, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hr, ha⟩
  | .grind _ _, h, _, _, hr, ha, hs => by
    simp only [settle, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hr, ha⟩
  | .commit _ _ _, h, _, _, hr, ha, hs => by
    simp only [settle, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hr, ha⟩

/-! ## Positions and the consumption of waiting scalars -/

/-- Where the program is, between two absorptions: at a node, or in the middle of a commitment
of a matrix of `2^ht` rows of `w` words, continuing with `k`, whose root's first half `x₀` has
been absorbed. -/
inductive Pos where
  /-- At a node of the program. -/
  | node (p : VerifierProgram Bool)
  /-- In the middle of a commitment. -/
  | half (ht w : ℕ) (k : VerifierProgram Bool) (x₀ : E)

/-- The result of consuming waiting scalars. -/
inductive Cons where
  /-- All consumed, at a history and position. -/
  | done (h : List Ev) (pos : Pos)
  /-- The last one was the nonce `n` of a proof of work of `b` bits, at the history `h` before
  it, continuing with `k`. -/
  | grd (h : List Ev) (b : ℕ) (k : VerifierProgram Bool) (n : E)
  /-- Not the verifier's. -/
  | bad

/-- Consume waiting scalars from a history and position, the commitments holding the words
`W r ht w` for their roots: each scalar after the openings before it. -/
def consume (W : Digest → ℕ → ℕ → Word) : List Ev → Pos → List (E × ℕ) → Cons
  | h, pos, [] => .done h pos
  | h, .node p, (x, tag) :: rest => match settle h p with
    | some (h1, .read k) =>
      if tag = 1 then consume W (h1 ++ [Ev.read x]) (.node (k x)) rest else .bad
    | some (h1, .commit ht w k) => if tag = 1 then consume W h1 (.half ht w k x) rest else .bad
    | some (h1, .grind b k) => if tag = 4 ∧ rest = [] then .grd h1 b k x else .bad
    | _ => .bad
  | h, .half ht w k x₀, (x, tag) :: rest =>
    if tag = 1 then
      consume W (h ++ [Ev.commit ht w (W (digestFromHalves (x₀, x)) ht w)]) (.node k) rest
    else .bad

/-! ## The decoder -/

/-- What a decoded state is: the history and position at which it is the sponge's state, with no
scalar waiting. -/
abbrev Info : Type := List Ev × Pos

/-- What a permutation entry starts. -/
inductive Shape where
  /-- Nothing. -/
  | none
  /-- A state at a boundary, after the seed (`pw = none`) or after a proof of work of `b` bits
  with the nonce `n` (`pw = some (b, n)`). -/
  | st (h : List Ev) (p : VerifierProgram Bool) (pw : Option (ℕ × E))
  /-- The first squeeze of the group starting at the boundary `h`, at node `p`. -/
  | sq (h : List Ev) (p : VerifierProgram Bool)

/-- The decoder's state. -/
structure Dec where
  /-- The decoded states, by capacity. -/
  info : (Fin 9 → UInt64) → Option Info
  /-- One record per permutation entry read, with the entry's output. -/
  kinds : List (Shape × KeccakState)

/-- The decoder before any entry. -/
def Dec.init : Dec := ⟨fun _ ↦ none, []⟩

/-- A permutation forced by an absorption: four scalars consumed and the program about to absorb
one more. -/
def forced (h : List Ev) (p : VerifierProgram Bool) (ps : List (E × ℕ)) : Shape × (KeccakState → Option Info) :=
  if ps.length = 4 then (.none, fun _ ↦ some (h, .node p)) else (.none, fun _ ↦ none)

/-- The record and the decoding of the output, once the waiting scalars are consumed. -/
def decodeAt : Cons → List (E × ℕ) → Shape × (KeccakState → Option Info)
  | .done h (.half ht w k x₀), ps =>
    if ps.length = 4 then (.none, fun _ ↦ some (h, .half ht w k x₀)) else (.none, fun _ ↦ none)
  | .done h (.node p), ps => match settle h p with
    | some (h1, .sample k) =>
      (if ps = [] then .none else .sq h p,
        fun u ↦ some (h1 ++ [Ev.sample (challengeOf u)], .node (k (challengeOf u))))
    | some (h1, .read k) => forced h1 (.read k) ps
    | some (h1, .commit ht w k) => forced h1 (.commit ht w k) ps
    | some (h1, .grind b k) => forced h1 (.grind b k) ps
    | _ => (.none, fun _ ↦ none)
  | .grd h b k n, _ =>
    (.st (h ++ [Ev.grind b]) k (some (b, n)), match settle (h ++ [Ev.grind b]) k with
      | some (h1, .sample k') =>
        fun u ↦ some (h1 ++ [Ev.sample (challengeOf u)], .node (k' (challengeOf u)))
      | _ => fun _ ↦ none)
  | .bad, _ => (.none, fun _ ↦ none)

/-- A history at which a seed can put the program: reachable, a boundary without proof of work
and without commitment, at a node of the program. -/
def RootOk (P : VerifierProgram Bool) (h : List Ev) : Prop :=
  P.Reachable h ∧ Boundary h ∧ grindBits h = 0 ∧ commits h = [] ∧ (P.after h).isSome

/-- The node of the program at a history (`fail` off the program). -/
def nodeAt (P : VerifierProgram Bool) (h : List Ev) : VerifierProgram Bool := (P.after h).getD .fail

theorem after_nodeAt {P : VerifierProgram Bool} {h : List Ev} (hr : RootOk P h) :
    P.after h = some (nodeAt P h) := by
  obtain ⟨-, -, -, -, hs⟩ := hr
  rcases ha : P.after h with _ | p
  · rw [ha] at hs; cases hs
  · simp [nodeAt, ha]

section Step

variable {X : Type} (σ : Seeds X) (P : VerifierProgram Bool)

open Classical in
/-- The statement whose seeding the permutation input `t` completes after the entries `ℓ`, if
any. -/
noncomputable def rootAt (ℓ : Log) (t : KeccakState) : Option X :=
  if h : ∃ x ds, Answered (lookH ℓ) (σ.seed x) ds ∧ (σ.seed x).fin ds = t then some h.choose
  else none

open Classical in
/-- The seed of a statement: a state at its root history, if that history is a root. -/
noncomputable def rootStep (h : List Ev) : Shape × (KeccakState → Option Info) :=
  if RootOk P h then (.st h (nodeAt P h) none, fun _ ↦ some (h, .node (nodeAt P h)))
  else (.none, fun _ ↦ none)

/-- Reading a permutation entry with input `t` after the entries `ℓ`, decoded as `δ`: the
record, and the decoding of the output as a function of the output. -/
noncomputable def stepF (ℓ : Log) (δ : Dec) (t : KeccakState) : Shape × (KeccakState → Option Info) :=
  match rootAt σ ℓ t with
  | some x => rootStep P (σ.root x)
  | none => match δ.info (capOf t) with
    | some (h, pos) =>
      decodeAt (consume (extract (lookH ℓ)) h pos (parsePending t)) (parsePending t)
    | none => (.none, fun _ ↦ none)

/-- Record a decoding at the capacity `c`, if there is one. -/
def setInfo (f : (Fin 9 → UInt64) → Option Info) (c : Fin 9 → UInt64) :
    Option Info → (Fin 9 → UInt64) → Option Info
  | some i => Function.update f c (some i)
  | none => f

/-- The decoder after an entry, read after the entries `ℓ`. -/
noncomputable def decStep (ℓ : Log) (δ : Dec) : Entry → Dec
  | .inl _ => δ
  | .inr (t, u) =>
    { info := setInfo δ.info (capOf u) ((stepF σ P ℓ δ t).2 u)
      kinds := δ.kinds ++ [((stepF σ P ℓ δ t).1, u)] }

/-- The decoder with the log read so far. -/
noncomputable def decodeAux (ℓ : Log) : Log × Dec :=
  ℓ.foldl (fun acc e ↦ (acc.1 ++ [e], decStep σ P acc.1 acc.2 e)) ([], Dec.init)

/-- **The decoding of a log**: the fold of `decStep` over its entries. -/
noncomputable def decode (ℓ : Log) : Dec := (decodeAux σ P ℓ).2

theorem decodeAux_append (ℓ : Log) (e : Entry) :
    decodeAux σ P (ℓ ++ [e]) =
      ((decodeAux σ P ℓ).1 ++ [e], decStep σ P (decodeAux σ P ℓ).1 (decodeAux σ P ℓ).2 e) := by
  simp [decodeAux, List.foldl_append]

theorem decodeAux_fst (ℓ : Log) : (decodeAux σ P ℓ).1 = ℓ := by
  induction ℓ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ℓ e ih => rw [decodeAux_append, ih]

@[simp] theorem decode_nil : decode σ P [] = Dec.init := rfl

/-- Decoding one more entry. -/
theorem decode_append (ℓ : Log) (e : Entry) :
    decode σ P (ℓ ++ [e]) = decStep σ P ℓ (decode σ P ℓ) e := by
  rw [decode, decodeAux_append, decodeAux_fst]
  rfl

theorem decode_append_inl (ℓ : Log) (p : Bytes × Digest) :
    decode σ P (ℓ ++ [.inl p]) = decode σ P ℓ := by
  rw [decode_append]; rfl

theorem kinds_decode_append_inr (ℓ : Log) (t u : KeccakState) :
    (decode σ P (ℓ ++ [.inr (t, u)])).kinds =
      (decode σ P ℓ).kinds ++ [((stepF σ P ℓ (decode σ P ℓ) t).1, u)] := by
  rw [decode_append]; rfl

theorem info_decode_append_inr (ℓ : Log) (t u : KeccakState) :
    (decode σ P (ℓ ++ [.inr (t, u)])).info =
      setInfo (decode σ P ℓ).info (capOf u) ((stepF σ P ℓ (decode σ P ℓ) t).2 u) := by
  rw [decode_append]; rfl

end Step

/-! ## Invariants -/

section Invariants

variable {X : Type} {σ : Seeds X} {P : VerifierProgram Bool}

/-- A decoded state is at a reachable history where the program is at the recorded position. -/
def InfoOk (P : VerifierProgram Bool) : Info → Prop
  | (h, .node p) => P.Reachable h ∧ P.after h = some p
  | (h, .half ht w k _) => P.Reachable h ∧ P.after h = some (.commit ht w k)

/-- A record is at a reachable boundary history where the program is at the recorded node, with
the proof-of-work bits that precede it. -/
def ShapeOk (P : VerifierProgram Bool) : Shape → Prop
  | .none => True
  | .st h p pw => P.Reachable h ∧ Boundary h ∧ P.after h = some p ∧
      grindBits h = (pw.map Prod.fst).getD 0
  | .sq h p => P.Reachable h ∧ Boundary h ∧ P.after h = some p ∧ grindBits h = 0

/-- What a consumption guarantees: every position it ends at is reachable, a node reached after
at least one scalar is a boundary without proof of work, and a nonce is read at a `grind`
node. -/
def ConsOk (P : VerifierProgram Bool) (ps : List (E × ℕ)) : Cons → Prop
  | .done h pos => InfoOk P (h, pos) ∧
      (ps ≠ [] → ∀ p, pos = .node p → Boundary h ∧ grindBits h = 0)
  | .grd h b k _ => P.Reachable h ∧ P.after h = some (.grind b k)
  | .bad => True

theorem after_read_step {h : List Ev} {k : E → VerifierProgram Bool} (ha : P.after h = some
    (.read k))
    (x : E) : P.after (h ++ [Ev.read x]) = some (k x) := by
  rw [VerifierProgram.after_append_single _ ha]; simp [VerifierProgram.after]

theorem after_sample_step {h : List Ev} {k : E → VerifierProgram Bool} (ha : P.after h = some
    (.sample k))
    (c : E) : P.after (h ++ [Ev.sample c]) = some (k c) := by
  rw [VerifierProgram.after_append_single _ ha]; simp [VerifierProgram.after]

theorem after_grind_step {h : List Ev} {b : ℕ} {k : VerifierProgram Bool}
    (ha : P.after h = some (.grind b k)) : P.after (h ++ [Ev.grind b]) = some k := by
  rw [VerifierProgram.after_append_single _ ha]; simp [VerifierProgram.after]

theorem after_commit_step {h : List Ev} {ht w : ℕ} {k : VerifierProgram Bool}
    (ha : P.after h = some (.commit ht w k)) (W : Word) :
    P.after (h ++ [Ev.commit ht w W]) = some k := by
  rw [VerifierProgram.after_append_single _ ha]; simp [VerifierProgram.after]

theorem after_query_step {h : List Ev} {i : ℕ} {ps : List ℕ} {k : List (List K) →
    VerifierProgram Bool}
    (ha : P.after h = some (.query i ps k)) (rows : List (List K)) :
    P.after (h ++ [Ev.query rows]) = some (k rows) := by
  rw [VerifierProgram.after_append_single _ ha]; simp [VerifierProgram.after]

/-- **Consumption keeps the invariants**, for well-shaped words. -/
theorem consume_ok {W : Digest → ℕ → ℕ → Word} (hW : ∀ r ht w, WellShaped w (W r ht w)) :
    ∀ (ps : List (E × ℕ)) (h : List Ev) (pos : Pos), InfoOk P (h, pos) →
      ConsOk P ps (consume W h pos ps)
  | [], h, pos, hi => ⟨hi, fun hne ↦ absurd rfl hne⟩
  | (x, tag) :: rest, h, .node p, hi => by
    obtain ⟨hr, ha⟩ := hi
    simp only [consume]
    split
    · rename_i h1 k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      split
      · have hc := consume_ok hW rest (h1 ++ [Ev.read x]) (.node (k x))
          ⟨VerifierProgram.Reachable.read x hr1 ha1, after_read_step ha1 x⟩
        rcases hrest : rest with _ | ⟨y, rest'⟩
        · subst hrest
          refine ⟨⟨VerifierProgram.Reachable.read x hr1 ha1, after_read_step ha1 x⟩, fun _ p'
              hp' ↦ ?_⟩
          exact ⟨boundary_append_read _ _, grindBits_append_read _ _⟩
        · rw [← hrest]
          revert hc
          generalize consume W (h1 ++ [Ev.read x]) (.node (k x)) rest = c
          intro hc
          rcases c with ⟨h', pos'⟩ | _ | _
          · exact ⟨hc.1, fun _ p' hp' ↦ hc.2 (by rw [hrest]; simp) p' hp'⟩
          · exact hc
          · trivial
      · trivial
    · rename_i h1 ht w k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      split
      · have hc := consume_ok hW rest h1 (.half ht w k x) ⟨hr1, ha1⟩
        rcases hrest : rest with _ | ⟨y, rest'⟩
        · subst hrest
          exact ⟨⟨hr1, ha1⟩, fun _ p' hp' ↦ by cases hp'⟩
        · rw [← hrest]
          revert hc
          generalize consume W h1 (.half ht w k x) rest = c
          intro hc
          rcases c with ⟨h', pos'⟩ | _ | _
          · exact ⟨hc.1, fun _ p' hp' ↦ hc.2 (by rw [hrest]; simp) p' hp'⟩
          · exact hc
          · trivial
      · trivial
    · rename_i h1 b k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      split
      · exact ⟨hr1, ha1⟩
      · trivial
    · trivial
  | (x, tag) :: rest, h, .half ht w k x₀, hi => by
    obtain ⟨hr, ha⟩ := hi
    simp only [consume]
    split
    · set r := digestFromHalves (x₀, x)
      have hr' := VerifierProgram.Reachable.commit (W r ht w) hr ha (hW r ht w)
      have ha' := after_commit_step ha (W r ht w)
      have hc := consume_ok hW rest (h ++ [Ev.commit ht w (W r ht w)]) (.node k) ⟨hr', ha'⟩
      rcases hrest : rest with _ | ⟨y, rest'⟩
      · subst hrest
        exact ⟨⟨hr', ha'⟩, fun _ p' _ ↦
          ⟨boundary_append_commit _ _ _ _, grindBits_append_commit _ _ _ _⟩⟩
      · rw [← hrest]
        revert hc
        generalize consume W (h ++ [Ev.commit ht w (W r ht w)]) (.node k) rest = c
        intro hc
        rcases c with ⟨h', pos'⟩ | _ | _
        · exact ⟨hc.1, fun _ p' hp' ↦ hc.2 (by rw [hrest]; simp) p' hp'⟩
        · exact hc
        · trivial
    · trivial

theorem forced_ok {h : List Ev} {p : VerifierProgram Bool} (hr : P.Reachable h) (ha : P.after h =
    some p)
    (ps : List (E × ℕ)) :
    ShapeOk P (forced h p ps).1 ∧ ∀ u i, (forced h p ps).2 u = some i → InfoOk P i := by
  unfold forced
  split
  · exact ⟨trivial, fun _ i hi ↦ by cases hi; exact ⟨hr, ha⟩⟩
  · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩

/-- Reading the consumed scalars keeps the invariants. -/
theorem decodeAt_ok {ps : List (E × ℕ)} {c : Cons} (hc : ConsOk P ps c) :
    ShapeOk P (decodeAt c ps).1 ∧ ∀ u i, (decodeAt c ps).2 u = some i → InfoOk P i := by
  rcases c with ⟨h, ⟨p⟩ | ⟨ht, w, k, x₀⟩⟩ | ⟨h, b, k, n⟩ | _
  · obtain ⟨⟨hr, ha⟩, hb⟩ := hc
    simp only [decodeAt]
    split
    · rename_i h1 k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      refine ⟨?_, fun u i hi ↦ ?_⟩
      · split
        · trivial
        · rename_i hne
          obtain ⟨hb1, hg⟩ := hb hne p rfl
          exact ⟨hr, hb1, ha, hg⟩
      · cases hi
        exact ⟨VerifierProgram.Reachable.sample _ hr1 ha1, after_sample_step ha1 _⟩
    · rename_i h1 k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      exact forced_ok hr1 ha1 ps
    · rename_i h1 ht w k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      exact forced_ok hr1 ha1 ps
    · rename_i h1 b k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      exact forced_ok hr1 ha1 ps
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
  · obtain ⟨⟨hr, ha⟩, -⟩ := hc
    simp only [decodeAt]
    split
    · exact ⟨trivial, fun _ i hi ↦ by cases hi; exact ⟨hr, ha⟩⟩
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
  · obtain ⟨hr, ha⟩ := hc
    simp only [decodeAt]
    have hr' := VerifierProgram.Reachable.grind hr ha
    have ha' := after_grind_step ha
    refine ⟨⟨hr', boundary_append_grind h b, ha', by simp [grindBits_append_grind]⟩, ?_⟩
    split
    · rename_i h1 k' hs
      obtain ⟨hr1, ha1⟩ := settle_ok k _ hr' ha' hs
      intro u i hi
      cases hi
      exact ⟨VerifierProgram.Reachable.sample _ hr1 ha1, after_sample_step ha1 _⟩
    · exact fun _ _ hi ↦ by simp at hi
  · exact ⟨trivial, fun _ _ hi ↦ by simp [decodeAt] at hi⟩

theorem setInfo_ok {f : (Fin 9 → UInt64) → Option Info} {c : Fin 9 → UInt64} {o : Option Info}
    (hf : ∀ c i, f c = some i → InfoOk P i) (ho : ∀ i, o = some i → InfoOk P i) :
    ∀ c' i, setInfo f c o c' = some i → InfoOk P i := by
  intro c' i hi
  rcases o with _ | j
  · exact hf c' i hi
  · simp only [setInfo, Function.update_apply] at hi
    split at hi
    · cases hi; exact ho _ rfl
    · exact hf c' i hi

/-- A permutation step from a decoder whose decoded states satisfy the invariant keeps it. -/
theorem stepF_ok_of (ℓ : Log) (δ : Dec) (t : KeccakState)
    (hδ : ∀ c i, δ.info c = some i → InfoOk P i) :
    ShapeOk P (stepF σ P ℓ δ t).1 ∧ ∀ u i, (stepF σ P ℓ δ t).2 u = some i → InfoOk P i := by
  unfold stepF
  split
  · rename_i x _
    unfold rootStep
    split
    · rename_i hr
      exact ⟨⟨hr.1, hr.2.1, after_nodeAt hr, by simpa using hr.2.2.1⟩,
        fun _ i hi ↦ by cases hi; exact ⟨hr.1, after_nodeAt hr⟩⟩
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
  · split
    · rename_i h pos hinfo
      exact decodeAt_ok (consume_ok (fun r ht w ↦ wellShaped_extract _ r ht w) _ h pos
        (hδ _ _ hinfo))
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩

/-- **The decoder's invariants**: every decoded state and every record is at a reachable history
at which the program is at the recorded position. -/
theorem decode_ok (ℓ : Log) :
    (∀ c i, (decode σ P ℓ).info c = some i → InfoOk P i) ∧
      ∀ k ∈ (decode σ P ℓ).kinds, ShapeOk P k.1 := by
  induction ℓ using List.reverseRecOn with
  | nil => exact ⟨fun _ _ h ↦ by simp [Dec.init] at h, fun _ h ↦ by simp [Dec.init] at h⟩
  | append_singleton ℓ e ih =>
    rcases e with p | ⟨t, u⟩
    · rw [decode_append_inl]; exact ih
    have hstep := stepF_ok_of (σ := σ) (P := P) ℓ (decode σ P ℓ) t ih.1
    refine ⟨?_, ?_⟩
    · rw [info_decode_append_inr]
      exact setInfo_ok ih.1 (hstep.2 u)
    · rw [kinds_decode_append_inr]
      intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · exact ih.2 k hk
      · rw [List.mem_singleton] at hk
        subst hk
        exact hstep.1

/-- The record of the next permutation entry satisfies the invariant. -/
theorem stepF_shapeOk (ℓ : Log) (t : KeccakState) : ShapeOk P (stepF σ P ℓ (decode σ P ℓ) t).1 :=
  (stepF_ok_of ℓ (decode σ P ℓ) t (decode_ok ℓ).1).1

end Invariants

end
end LeanVM.Protocol.Compile.Rom
