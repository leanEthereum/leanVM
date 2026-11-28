/-
  LeanVM.Protocol.Compile.Rom.Decode

  Reading the random oracles' log back into the verifier program: which states are states of
  the Fiat-Shamir sponge, at which interactive history and position, and which log entries start
  a group of challenges.
-/

module

public import LeanVM.Protocol.Compile.Rom.Extract

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
    state at the same history and position, the queue emptied;
  - at a `samplePacked n` node (after the openings), the permutation is a packed draw's first
    chunk: its first `min(n, 8)` cells (`cells8`) are the draw's challenges, and `u` is the state
    after the draw (`drawInfo`), or in its middle (`Pos.spk`);
  - at a `readPacked n` node, the permutation is the one that absorbs what waits before a packed
    message: `u` is at the start of the message (`Pos.rpk`, nothing absorbed).
* **A packed message's chunk.** If the capacity is decoded in the middle of a packed message of
  `n` scalars (`Pos.rpk`), or at a node whose next operation is one (nothing waits there), the
  input carries the next chunk, its first `min(8, missing)` cells, untagged (`readChunk`): `u` is
  the state at the boundary after the message once it has its `n` scalars, recorded as
  `st h p none`, or in its middle.
* **A packed draw's chunk.** If the capacity is decoded in the middle of a packed draw
  (`Pos.spk`), the permutation squeezes the next chunk: `u`'s first cells (`drawInfo`).

  The position, not the input, tells a packed chunk from tagged scalars. Anything else is not
  decoded.

## The records

Each permutation entry gets a `Shape`, paired with its output in `Dec.kinds`: `st h p pw` if its
output is a state at the boundary history `h` with node `p`, after the seed (`pw = none`) or a
proof of work of `b` bits with nonce `n` (`pw = some (b, n)`); `sq h p` if it is the first
squeeze of the group starting at the boundary `h`, the scalars of the permutation being the
prover's last moves; the boundary state after a packed message's last chunk gets `st h p none`, as
the seed's does. The potential (`LeanVM.Protocol.Compile.Rom.Potential`) gives each record a
term. A squeeze after the seed, with no scalar waiting, gets no record: the state's record carries
its group. A proof of work's permutation draws the first challenge of its group itself (or the first cells of a
packed draw, `groundCells`), and its record carries the group.

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

theorem boundary_append_readPacked (h : List Ev) (xs : List E) :
    Boundary (h ++ [Ev.readPacked xs]) := by
  unfold Boundary; split
  · simp_all
  · rw [getLast?_append_single]; trivial

theorem not_boundary_append_samplePacked (h : List Ev) (cs : List E) :
    ¬ Boundary (h ++ [Ev.samplePacked cs]) := by
  unfold Boundary; split
  · simp_all
  · rw [getLast?_append_single]; simp

theorem grindBits_append_readPacked (h : List Ev) (xs : List E) :
    grindBits (h ++ [Ev.readPacked xs]) = 0 := by
  simp [grindBits]

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
  | .readPacked _ _, h, _, _, hr, ha, hs => by
    simp only [settle, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨hr, ha⟩
  | .samplePacked _ _, h, _, _, hr, ha, hs => by
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
  /-- In the middle of a packed message of `n` scalars, continuing with `k`, the scalars `xs`
  absorbed, none waiting. -/
  | rpk (n : ℕ) (k : List E → VerifierProgram Bool) (xs : List E)
  /-- In the middle of a packed draw of `n` challenges, continuing with `k`, the challenges `cs`
  drawn. -/
  | spk (n : ℕ) (k : List E → VerifierProgram Bool) (cs : List E)

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
  | _, .rpk _ _ _, _ :: _ => .bad
  | _, .spk _ _ _, _ :: _ => .bad

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

/-- The decoding after a packed draw of `n` challenges took `ys` after `cs`: the node after the
draw once it has its `n` challenges, the middle of the draw otherwise. -/
def drawInfo (h : List Ev) (n : ℕ) (k : List E → VerifierProgram Bool) (cs ys : List E) : Info :=
  if n ≤ (cs ++ ys).length then (h ++ [Ev.samplePacked (cs ++ ys)], .node (k (cs ++ ys)))
  else (h, .spk n k (cs ++ ys))

/-- The record and the decoding after a packed message of `n` scalars absorbed `ys` after `xs`:
the state at the boundary after the message once it has its `n` scalars, the middle of the
message otherwise. -/
def readChunk (h : List Ev) (n : ℕ) (k : List E → VerifierProgram Bool) (xs ys : List E) :
    Shape × (KeccakState → Option Info) :=
  if n ≤ (xs ++ ys).length then
    (.st (h ++ [Ev.readPacked (xs ++ ys)]) (k (xs ++ ys)) none,
      fun _ ↦ some (h ++ [Ev.readPacked (xs ++ ys)], .node (k (xs ++ ys))))
  else (.none, fun _ ↦ some (h, .rpk n k (xs ++ ys)))

/-- The record and the decoding of the output, once the waiting scalars are consumed. -/
def decodeAt : Cons → List (E × ℕ) → Shape × (KeccakState → Option Info)
  | .done h (.half ht w k x₀), ps =>
    if ps.length = 4 then (.none, fun _ ↦ some (h, .half ht w k x₀)) else (.none, fun _ ↦ none)
  | .done h (.node p), ps => match settle h p with
    | some (h1, .sample k) =>
      (if ps = [] then .none else .sq h p,
        fun u ↦ some (h1 ++ [Ev.sample (challengeOf u)], .node (k (challengeOf u))))
    | some (h1, .samplePacked n k) =>
      (if ps = [] then .none else .sq h p, fun u ↦ some (drawInfo h1 n k [] ((cells8 u).take n)))
    | some (h1, .readPacked n k) =>
      if ps = [] then (.none, fun _ ↦ none) else (.none, fun _ ↦ some (h1, .rpk n k []))
    | some (h1, .read k) => forced h1 (.read k) ps
    | some (h1, .commit ht w k) => forced h1 (.commit ht w k) ps
    | some (h1, .grind b k) => forced h1 (.grind b k) ps
    | _ => (.none, fun _ ↦ none)
  | .grd h b k n, _ =>
    (.st (h ++ [Ev.grind b]) k (some (b, n)), fun u ↦ match settle (h ++ [Ev.grind b]) k with
      | some (h1, .sample k') => some (h1 ++ [Ev.sample (challengeOf u)], .node (k' (challengeOf u)))
      | some (h1, .samplePacked n k') => some (drawInfo h1 n k' [] ((groundCells u).take n))
      | _ => none)
  | .done _ (.rpk _ _ _), _ => (.none, fun _ ↦ none)
  | .done _ (.spk _ _ _), _ => (.none, fun _ ↦ none)
  | .bad, _ => (.none, fun _ ↦ none)

/-- The node of the program at a history (`fail` off the program). -/
def nodeAt (P : VerifierProgram Bool) (h : List Ev) : VerifierProgram Bool := (P.after h).getD .fail

/-- A history at which a seed can put the program: reachable, a boundary without proof of work
and without commitment, at a node of the program whose packed messages are nonempty
(`VerifierProgram.PackedPos`). -/
def RootOk (P : VerifierProgram Bool) (h : List Ev) : Prop :=
  P.Reachable h ∧ Boundary h ∧ grindBits h = 0 ∧ commits h = [] ∧ (P.after h).isSome ∧
    (nodeAt P h).PackedPos

theorem after_nodeAt {P : VerifierProgram Bool} {h : List Ev} (hr : RootOk P h) :
    P.after h = some (nodeAt P h) := by
  obtain ⟨-, -, -, -, hs, -⟩ := hr
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
    | some (h, .rpk n k xs) => readChunk h n k xs ((cells8 t).take (n - xs.length))
    | some (h, .spk n k cs) => (.none, fun u ↦ some (drawInfo h n k cs ((cells8 u).take (n - cs.length))))
    | some (h, .node p) => match settle h p with
      | some (h1, .readPacked n k) => readChunk h1 n k [] ((cells8 t).take n)
      | _ => decodeAt (consume (extract (lookH ℓ)) h (.node p) (parsePending t)) (parsePending t)
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
  | (h, .rpk n k xs) => P.Reachable h ∧ P.after h = some (.readPacked n k) ∧ xs.length ≤ n
  | (h, .spk n k cs) => P.Reachable h ∧ P.after h = some (.samplePacked n k) ∧ cs.length ≤ n

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
  | (_, _) :: _, _, .rpk _ _ _, _ => trivial
  | (_, _) :: _, _, .spk _ _ _, _ => trivial

theorem after_readPacked_step {h : List Ev} {n : ℕ} {k : List E → VerifierProgram Bool}
    (ha : P.after h = some (.readPacked n k)) {xs : List E} (hn : xs.length = n) :
    P.after (h ++ [Ev.readPacked xs]) = some (k xs) := by
  rw [VerifierProgram.after_append_single _ ha]; simp [VerifierProgram.after, hn]

theorem after_samplePacked_step {h : List Ev} {n : ℕ} {k : List E → VerifierProgram Bool}
    (ha : P.after h = some (.samplePacked n k)) {cs : List E} (hn : cs.length = n) :
    P.after (h ++ [Ev.samplePacked cs]) = some (k cs) := by
  rw [VerifierProgram.after_append_single _ ha]; simp [VerifierProgram.after, hn]

/-- A packed draw's decoding is at a reachable history. -/
theorem drawInfo_ok {h : List Ev} {n : ℕ} {k : List E → VerifierProgram Bool} {cs ys : List E}
    (hr : P.Reachable h) (ha : P.after h = some (.samplePacked n k)) (hcs : cs.length ≤ n)
    (hys : ys.length ≤ n - cs.length) : InfoOk P (drawInfo h n k cs ys) := by
  unfold drawInfo
  split
  · rename_i hle
    have hl : (cs ++ ys).length = n := by simp at hle ⊢; omega
    exact ⟨.samplePacked _ hr ha hl, after_samplePacked_step ha hl⟩
  · exact ⟨hr, ha, by simp; omega⟩

/-- A packed message's record and decoding are at a reachable history. -/
theorem readChunk_ok {h : List Ev} {n : ℕ} {k : List E → VerifierProgram Bool} {xs ys : List E}
    (hr : P.Reachable h) (ha : P.after h = some (.readPacked n k)) (hxs : xs.length ≤ n)
    (hys : ys.length ≤ n - xs.length) :
    ShapeOk P (readChunk h n k xs ys).1 ∧
      ∀ u i, (readChunk h n k xs ys).2 u = some i → InfoOk P i := by
  unfold readChunk
  split
  · rename_i hle
    have hl : (xs ++ ys).length = n := by simp at hle ⊢; omega
    have hr' := VerifierProgram.Reachable.readPacked _ hr ha hl
    have ha' := after_readPacked_step ha hl
    exact ⟨⟨hr', boundary_append_readPacked _ _, ha', by simp [grindBits_append_readPacked]⟩,
      fun _ i hi ↦ by cases hi; exact ⟨hr', ha'⟩⟩
  · exact ⟨trivial, fun _ i hi ↦ by cases hi; exact ⟨hr, ha, by simp; omega⟩⟩

theorem length_take_cells8_le (u : KeccakState) (m : ℕ) : ((cells8 u).take m).length ≤ m := by
  simp

theorem length_take_groundCells_le (u : KeccakState) (m : ℕ) :
    ((groundCells u).take m).length ≤ m := by
  simp

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
  rcases c with ⟨h, ⟨p⟩ | ⟨ht, w, k, x₀⟩ | ⟨n, k, xs⟩ | ⟨n, k, cs⟩⟩ | ⟨h, b, k, n⟩ | _
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
    · rename_i h1 n k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      refine ⟨?_, fun u i hi ↦ ?_⟩
      · split
        · trivial
        · rename_i hne
          obtain ⟨hb1, hg⟩ := hb hne p rfl
          exact ⟨hr, hb1, ha, hg⟩
      · cases hi
        exact drawInfo_ok hr1 ha1 (by simp) (by simp)
    · rename_i h1 n k hs
      obtain ⟨hr1, ha1⟩ := settle_ok p h hr ha hs
      split
      · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
      · exact ⟨trivial, fun _ i hi ↦ by cases hi; exact ⟨hr1, ha1, by simp⟩⟩
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
  · exact ⟨trivial, fun _ _ hi ↦ by simp [decodeAt] at hi⟩
  · exact ⟨trivial, fun _ _ hi ↦ by simp [decodeAt] at hi⟩
  · obtain ⟨hr, ha⟩ := hc
    simp only [decodeAt]
    have hr' := VerifierProgram.Reachable.grind hr ha
    have ha' := after_grind_step ha
    refine ⟨⟨hr', boundary_append_grind h b, ha', by simp [grindBits_append_grind]⟩, ?_⟩
    intro u i hi
    split at hi
    · rename_i h1 k' hs
      obtain ⟨hr1, ha1⟩ := settle_ok k _ hr' ha' hs
      cases hi
      exact ⟨VerifierProgram.Reachable.sample _ hr1 ha1, after_sample_step ha1 _⟩
    · rename_i h1 n' k' hs
      obtain ⟨hr1, ha1⟩ := settle_ok k _ hr' ha' hs
      cases hi
      exact drawInfo_ok hr1 ha1 (by simp) (by simp)
    · simp at hi
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
  · have hW := fun r ht w ↦ wellShaped_extract (lookH ℓ) r ht w
    split
    · rename_i h n k xs hinfo
      obtain ⟨hr, ha, hxs⟩ := hδ _ _ hinfo
      exact readChunk_ok hr ha hxs (by simp)
    · rename_i h n k cs hinfo
      obtain ⟨hr, ha, hcs⟩ := hδ _ _ hinfo
      refine ⟨trivial, fun u i hi ↦ ?_⟩
      cases hi
      exact drawInfo_ok hr ha hcs (length_take_cells8_le u _)
    · rename_i h p hinfo
      have hi := hδ _ _ hinfo
      split
      · rename_i h1 n k hs
        obtain ⟨hr1, ha1⟩ := settle_ok p h hi.1 hi.2 hs
        exact readChunk_ok hr1 ha1 (by simp) (by simp)
      · exact decodeAt_ok (consume_ok hW _ h _ hi)
    · rename_i h pos _ _ _ hinfo
      exact decodeAt_ok (consume_ok hW _ h pos (hδ _ _ hinfo))
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
