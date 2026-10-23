/-
  LeanVM.Protocol.Compile.Rom.Decode

  Reading the random oracle's log back into the verifier program: which digests are states of
  the Fiat-Shamir chain, at which interactive history, and which log entries start a group of
  challenges.
-/

module

public import LeanVM.Protocol.Compile.Rom.Extract
public import LeanVM.Protocol.Compile.Prover

/-!
# Decoding a log

The random-oracle theorem (`LeanVM.Protocol.Compile.Rom.Sound`) reads the log of the random
oracle, entry by entry and in order, as moves of the verifier program `P` from the seed
(`decode`). The reading is a fold: each entry is read with the entries before it (`decStep`).

## What an entry is

The decoder keeps the decoded digests (`Dec.info`) and one record per entry (`Dec.kinds`). An
entry `(t, u)` is read as follows.

* **Seeding.** If, for some statement `x` of the family of seedings, the entries before it answer
  every input of `x`'s seeding but the last, and `t` is the last (`pend`, `rootAt`), `u` is the
  seed: the chain state at `x`'s root history (`rootStep`, when that history is a root of the
  program, `RootOk`).
* **A chain step.** Otherwise, if `t = cv ‖ (x, tag)` (`parse`) with `cv` a decoded digest, the
  entry is read at `cv`'s decoding:
  - at a chain state at node `read`, tag `1`: `u` is the state after the prover's scalar `x`;
  - at `sample`, the block `(0, 2)`: `u` is the state after the challenge `challengeOf u`;
  - at `grind b`, the block `(0, 3)`: `u` is the proof-of-work base of `cv`; tag `4`: `u` is the
    state after the nonce `x`;
  - at `commit`, tag `1`: `u` is the state after the first half `x₀` of the root (`Info.half`),
    and at such a state tag `1` again: `u` is the state after the commitment of the root
    `digestOfScalars (x₀, x)`, with the word extracted for it from the entries *before* this one
    (`extract`);
  - at a proof-of-work base, tag `4`: the entry is the proof of work of the nonce `x`.

  Openings take no query of the chain: a state is recorded after the openings that follow it,
  each answered from the extracted words (`settle`). Anything else is not decoded.

## The records

Each entry gets a `Shape`, paired with its output in `Dec.kinds`: `bnd h p` if its output is a
chain state after a scalar, a commitment, or the seeding, at the boundary history `h` with node `p`;
`grd h p b cv n` if it is the state after the nonce `n` at the grind state `cv`, `h` ending in
`Ev.grind b`; `pow h p b cv n` if it is the proof of work of that pair. The potential
(`LeanVM.Protocol.Compile.Rom.Potential`) gives each record a term. A nonce's pair gets only one
non-trivial record: the first of its two entries (`powIn`, and the test on `cv ‖ (n, 4)`).

Every record and every decoded state carries a reachable history at which the program is at the
recorded node (`decode_ok`): the certificate's lemmas apply to them.

Nothing here assumes the log is free of failure; the reading is a function of the log. Its
agreement with the compiled verifier's run is proved, under no failure, in
`LeanVM.Protocol.Compile.Rom.Known` and `LeanVM.Protocol.Compile.Rom.Final`.
-/

namespace LeanVM.Protocol.Compile.Rom

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Rom

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
def settle : List Ev → Prog Bool → Option (List Ev × Prog Bool)
  | h, .query i ps k => match answer h i ps with
    | some rows => settle (h ++ [Ev.query rows]) (k rows)
    | none => none
  | h, p => some (h, p)

/-- Settling keeps reachability. -/
theorem settle_ok {P : Prog Bool} :
    ∀ (p : Prog Bool) (h : List Ev) {h' : List Ev} {p' : Prog Bool}, P.Reachable h →
      P.after h = some p → settle h p = some (h', p') → P.Reachable h' ∧ P.after h' = some p'
  | .query i ps k, h, h', p', hr, ha, hs => by
    simp only [settle] at hs
    split at hs
    · rename_i rows hrows
      refine settle_ok (k rows) _ (Prog.Reachable.query hr ha hrows) ?_ hs
      rw [Prog.after_append_single _ ha]
      simp [Prog.after]
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

/-! ## Parsing chain inputs -/

open Classical in
/-- A chain input `cv ‖ (x, tag)`, read back. -/
noncomputable def parse (t : Bytes) : Option (Digest × E × ℕ) :=
  if h : ∃ q : Digest × E × ℕ, q.2.2 < 256 ∧ t = digestBytes q.1 ++ blockOf q.2.1 q.2.2 then
    some (Classical.choose h)
  else none

theorem parse_eq_some {t : Bytes} {q : Digest × E × ℕ} (h : parse t = some q) :
    q.2.2 < 256 ∧ t = digestBytes q.1 ++ blockOf q.2.1 q.2.2 := by
  unfold parse at h
  split at h
  · rename_i hex
    cases h
    exact Classical.choose_spec hex
  · simp at h

/-- A chain input parses to its state, scalar and tag. -/
theorem parse_chain (c : Digest) (x : E) {tag : ℕ} (htag : tag < 256) :
    parse (digestBytes c ++ blockOf x tag) = some (c, x, tag) := by
  have hex : ∃ q : Digest × E × ℕ, q.2.2 < 256 ∧
      digestBytes c ++ blockOf x tag = digestBytes q.1 ++ blockOf q.2.1 q.2.2 :=
    ⟨(c, x, tag), htag, rfl⟩
  have hspec := Classical.choose_spec hex
  unfold parse
  simp only [hex, ↓reduceDIte, Option.some.injEq]
  generalize Classical.choose hex = q at hspec ⊢
  obtain ⟨c', x', tag'⟩ := q
  obtain ⟨htag', heq⟩ := hspec
  obtain ⟨rfl, rfl, ht⟩ := chainInput_inj heq
  have h1 := congrArg UInt8.toNat ht
  simp only [Nat.toUInt8, UInt8.toNat_ofNat'] at h1
  have : tag = tag' := by simp only at htag'; omega
  rw [this]

/-! ## The decoder -/

/-- What a decoded digest is. -/
inductive Info where
  /-- A chain state, at a history and node (after its openings). -/
  | st (h : List Ev) (p : Prog Bool)
  /-- A chain state inside a commitment, after the root's first half. -/
  | half (h : List Ev) (ht w : ℕ) (k : Prog Bool) (x₀ : E)
  /-- The proof-of-work base of the grind state `cv`. -/
  | base (h : List Ev) (b : ℕ) (k : Prog Bool) (cv : Digest)

/-- What an entry starts. -/
inductive Shape where
  /-- Nothing. -/
  | none
  /-- A chain state at a boundary that is not a proof of work. -/
  | bnd (h : List Ev) (p : Prog Bool)
  /-- A chain state after the nonce `n` at the grind state `cv`, before the proof of work. -/
  | grd (h : List Ev) (p : Prog Bool) (b : ℕ) (cv : Digest) (n : E)
  /-- The proof of work of the nonce `n` at the grind state `cv`, before the chain state. -/
  | pow (h : List Ev) (p : Prog Bool) (b : ℕ) (cv : Digest) (n : E)

/-- The decoder's state. -/
structure Dec where
  /-- The decoded digests. -/
  info : Digest → Option Info
  /-- One record per entry read, with the entry's output. -/
  kinds : List (Shape × Digest)

/-- The decoder before any entry. -/
def Dec.init : Dec := ⟨fun _ ↦ none, []⟩

/-- The chain state recorded at a history and node, after its openings. -/
def stInfo (h : List Ev) (p : Prog Bool) : Option Info :=
  (settle h p).map fun q ↦ Info.st q.1 q.2

/-- The proof-of-work answer of the nonce `n` at the grind state `cv`, if the log has it. -/
def powIn (ℓ : Log) (cv : Digest) (n : E) : Option Digest :=
  (look ℓ (digestBytes cv ++ blockOf 0 3)).bind fun base ↦ look ℓ (digestBytes base ++ blockOf n 4)

/-- A history at which a seed can put the program: reachable, a boundary without proof of work
and without commitment, at a node of the program. -/
def RootOk (P : Prog Bool) (h : List Ev) : Prop :=
  P.Reachable h ∧ Boundary h ∧ grindBits h = 0 ∧ commits h = [] ∧ (P.after h).isSome

/-- The node of the program at a history (`fail` off the program). -/
def nodeAt (P : Prog Bool) (h : List Ev) : Prog Bool := (P.after h).getD .fail

theorem after_nodeAt {P : Prog Bool} {h : List Ev} (hr : RootOk P h) :
    P.after h = some (nodeAt P h) := by
  obtain ⟨-, -, -, -, hs⟩ := hr
  rcases ha : P.after h with _ | p
  · rw [ha] at hs; cases hs
  · simp [nodeAt, ha]

section Step

variable {X : Type} (σ : Seeds X) (P : Prog Bool)

open Classical in
/-- The statement whose seeding the input `t` completes after the entries `ℓ`, if any. -/
noncomputable def rootAt (ℓ : Log) (t : Bytes) : Option X :=
  if h : ∃ x, pend (look ℓ) (σ.seed x) = some (t, true) then some h.choose else none

open Classical in
/-- The seed of a statement: a chain state at its root history, if that history is a root. -/
noncomputable def rootStep (h : List Ev) : Shape × (Digest → Option Info) :=
  if RootOk P h then (.bnd h (nodeAt P h), fun _ ↦ stInfo h (nodeAt P h))
  else (.none, fun _ ↦ none)

/-- A chain step at a chain state `cv` at history `h` and node `p`, with block `(x, tag)`: the
record, and the decoding of the output as a function of the output. -/
noncomputable def stepSt (ℓ : Log) (h : List Ev) (p : Prog Bool) (cv : Digest) (x : E)
    (tag : ℕ) : Shape × (Digest → Option Info) :=
  match p with
  | .read k =>
    if tag = 1 then (.bnd (h ++ [Ev.read x]) (k x), fun _ ↦ stInfo (h ++ [Ev.read x]) (k x))
    else (.none, fun _ ↦ none)
  | .sample k => if tag = 2 ∧ x = 0 then
      (.none, fun u ↦ stInfo (h ++ [Ev.sample (challengeOf u)]) (k (challengeOf u)))
    else (.none, fun _ ↦ none)
  | .grind b k => if tag = 3 ∧ x = 0 then (.none, fun _ ↦ some (.base h b k cv))
    else if tag = 4 then
      (if powIn ℓ cv x = none then .grd (h ++ [Ev.grind b]) k b cv x else .none,
        fun _ ↦ stInfo (h ++ [Ev.grind b]) k)
    else (.none, fun _ ↦ none)
  | .commit ht w k => if tag = 1 then (.none, fun _ ↦ some (.half h ht w k x))
    else (.none, fun _ ↦ none)
  | _ => (.none, fun _ ↦ none)

/-- A step at a decoded digest. -/
noncomputable def stepAt (ℓ : Log) (cv : Digest) (x : E) (tag : ℕ) :
    Option Info → Shape × (Digest → Option Info)
  | some (.st h p) => stepSt ℓ h p cv x tag
  | some (.half h ht w k x₀) =>
    if tag = 1 then
      match digestOfScalars (x₀, x) with
      | some r =>
        (.bnd (h ++ [Ev.commit ht w (extract (look ℓ) r ht w)]) k,
          fun _ ↦ stInfo (h ++ [Ev.commit ht w (extract (look ℓ) r ht w)]) k)
      | none => (.none, fun _ ↦ none)
    else (.none, fun _ ↦ none)
  | some (.base h b k cv₀) =>
    if tag = 4 then
      (if look ℓ (digestBytes cv₀ ++ blockOf x 4) = none then .pow (h ++ [Ev.grind b]) k b cv₀ x
        else .none, fun _ ↦ none)
    else (.none, fun _ ↦ none)
  | none => (.none, fun _ ↦ none)

/-- Reading an entry with input `t` after the entries `ℓ`, decoded as `δ`: the record, and the
decoding of the output as a function of the output. -/
noncomputable def step (ℓ : Log) (δ : Dec) (t : Bytes) : Shape × (Digest → Option Info) :=
  match rootAt σ ℓ t with
  | some x => rootStep P (σ.root x)
  | none => match parse t with
    | some (cv, x, tag) => stepAt ℓ cv x tag (δ.info cv)
    | none => (.none, fun _ ↦ none)

/-- Record a decoding of `u`, if there is one. -/
def setInfo (f : Digest → Option Info) (u : Digest) : Option Info → Digest → Option Info
  | some i => Function.update f u (some i)
  | none => f

/-- The decoder after the entry `(t, u)`, read after the entries `ℓ`. -/
noncomputable def decStep (ℓ : Log) (δ : Dec) (t : Bytes) (u : Digest) : Dec where
  info := setInfo δ.info u ((step σ P ℓ δ t).2 u)
  kinds := δ.kinds ++ [((step σ P ℓ δ t).1, u)]

/-- The decoder with the log read so far. -/
noncomputable def decodeAux (ℓ : Log) : Log × Dec :=
  ℓ.foldl (fun acc e ↦ (acc.1 ++ [e], decStep σ P acc.1 acc.2 e.1 e.2)) ([], Dec.init)

/-- **The decoding of a log**: the fold of `decStep` over its entries. -/
noncomputable def decode (ℓ : Log) : Dec := (decodeAux σ P ℓ).2

theorem decodeAux_append (ℓ : Log) (e : Bytes × Digest) :
    decodeAux σ P (ℓ ++ [e]) =
      ((decodeAux σ P ℓ).1 ++ [e],
        decStep σ P (decodeAux σ P ℓ).1 (decodeAux σ P ℓ).2 e.1 e.2) := by
  simp [decodeAux, List.foldl_append]

theorem decodeAux_fst (ℓ : Log) : (decodeAux σ P ℓ).1 = ℓ := by
  induction ℓ using List.reverseRecOn with
  | nil => rfl
  | append_singleton ℓ e ih => rw [decodeAux_append, ih]

@[simp] theorem decode_nil : decode σ P [] = Dec.init := rfl

/-- Decoding one more entry. -/
theorem decode_append (ℓ : Log) (t : Bytes) (u : Digest) :
    decode σ P (ℓ ++ [(t, u)]) = decStep σ P ℓ (decode σ P ℓ) t u := by
  rw [decode, decodeAux_append, decodeAux_fst]
  rfl

theorem kinds_decode_append (ℓ : Log) (t : Bytes) (u : Digest) :
    (decode σ P (ℓ ++ [(t, u)])).kinds =
      (decode σ P ℓ).kinds ++ [((step σ P ℓ (decode σ P ℓ) t).1, u)] := by
  rw [decode_append]; rfl

theorem info_decode_append (ℓ : Log) (t : Bytes) (u : Digest) :
    (decode σ P (ℓ ++ [(t, u)])).info =
      setInfo (decode σ P ℓ).info u ((step σ P ℓ (decode σ P ℓ) t).2 u) := by
  rw [decode_append]; rfl


end Step

/-! ## Invariants -/

section Invariants

variable {X : Type} {σ : Seeds X} {P : Prog Bool}

/-- A decoded digest is at a reachable history where the program is at the recorded node. -/
def InfoOk (P : Prog Bool) : Info → Prop
  | .st h p => P.Reachable h ∧ P.after h = some p
  | .half h ht w k _ => P.Reachable h ∧ P.after h = some (.commit ht w k)
  | .base h b k _ => P.Reachable h ∧ P.after h = some (.grind b k)

/-- A record is at a reachable boundary history where the program is at the recorded node, with
the proof-of-work bits that precede it. -/
def ShapeOk (P : Prog Bool) : Shape → Prop
  | .none => True
  | .bnd h p => P.Reachable h ∧ Boundary h ∧ P.after h = some p ∧ grindBits h = 0
  | .grd h p b _ _ => P.Reachable h ∧ Boundary h ∧ P.after h = some p ∧ grindBits h = b
  | .pow h p b _ _ => P.Reachable h ∧ Boundary h ∧ P.after h = some p ∧ grindBits h = b

theorem stInfo_ok {h : List Ev} {p : Prog Bool} (hr : P.Reachable h) (ha : P.after h = some p) :
    ∀ i, stInfo h p = some i → InfoOk P i := by
  intro i hi
  simp only [stInfo, Option.map_eq_some_iff] at hi
  obtain ⟨⟨h', p'⟩, hs, rfl⟩ := hi
  exact settle_ok p h hr ha hs

/-- A step at a decoded state keeps the invariants. -/
theorem stepAt_ok (ℓ : Log) (cv : Digest) (x : E) (tag : ℕ) (o : Option Info)
    (ho : ∀ i, o = some i → InfoOk P i) :
    ShapeOk P (stepAt ℓ cv x tag o).1 ∧ ∀ u i, (stepAt ℓ cv x tag o).2 u = some i → InfoOk P i := by
  rcases o with _ | (⟨h, p⟩ | ⟨h, ht, w, k, x₀⟩ | ⟨h, b, k, cv₀⟩)
  · exact ⟨trivial, fun _ _ hi ↦ by simp [stepAt] at hi⟩
  · obtain ⟨hr, ha⟩ := ho _ rfl
    simp only [stepAt]
    cases p with
    | read k =>
      simp only [stepSt]
      split
      · have hr' := Prog.Reachable.read x hr ha
        have ha' : P.after (h ++ [Ev.read x]) = some (k x) := by
          rw [Prog.after_append_single _ ha]; simp [Prog.after]
        exact ⟨⟨hr', boundary_append_read h x, ha', grindBits_append_read h x⟩,
          fun _ ↦ stInfo_ok hr' ha'⟩
      · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
    | sample k =>
      simp only [stepSt]
      split
      · refine ⟨trivial, fun u ↦ ?_⟩
        refine stInfo_ok (Prog.Reachable.sample (challengeOf u) hr ha) ?_
        rw [Prog.after_append_single _ ha]; simp [Prog.after]
      · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
    | grind b k =>
      simp only [stepSt]
      split
      · exact ⟨trivial, fun _ i hi ↦ by cases hi; exact ⟨hr, ha⟩⟩
      · split
        · have hr' := Prog.Reachable.grind hr ha
          have ha' : P.after (h ++ [Ev.grind b]) = some k := by
            rw [Prog.after_append_single _ ha]; simp [Prog.after]
          refine ⟨?_, fun _ ↦ stInfo_ok hr' ha'⟩
          split
          · exact ⟨hr', boundary_append_grind h b, ha', grindBits_append_grind h b⟩
          · trivial
        · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
    | commit ht w k =>
      simp only [stepSt]
      split
      · exact ⟨trivial, fun _ i hi ↦ by cases hi; exact ⟨hr, ha⟩⟩
      · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
    | ret a => exact ⟨trivial, fun _ _ hi ↦ by simp [stepSt] at hi⟩
    | fail => exact ⟨trivial, fun _ _ hi ↦ by simp [stepSt] at hi⟩
    | query i ps k => exact ⟨trivial, fun _ _ hi ↦ by simp [stepSt] at hi⟩
  · obtain ⟨hr, ha⟩ := ho _ rfl
    simp only [stepAt]
    split
    · split
      · rename_i r _
        have hr' := Prog.Reachable.commit (extract (look ℓ) r ht w) hr ha
          (wellShaped_extract _ _ _ _)
        have ha' : P.after (h ++ [Ev.commit ht w (extract (look ℓ) r ht w)]) = some k := by
          rw [Prog.after_append_single _ ha]; simp [Prog.after]
        exact ⟨⟨hr', boundary_append_commit _ _ _ _, ha', grindBits_append_commit _ _ _ _⟩,
          fun _ ↦ stInfo_ok hr' ha'⟩
      · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
  · obtain ⟨hr, ha⟩ := ho _ rfl
    simp only [stepAt]
    split
    · refine ⟨?_, fun _ _ hi ↦ by simp at hi⟩
      split
      · have hr' := Prog.Reachable.grind hr ha
        have ha' : P.after (h ++ [Ev.grind b]) = some k := by
          rw [Prog.after_append_single _ ha]; simp [Prog.after]
        exact ⟨hr', boundary_append_grind h b, ha', grindBits_append_grind h b⟩
      · trivial
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩

theorem setInfo_ok {f : Digest → Option Info} {u : Digest} {o : Option Info}
    (hf : ∀ c i, f c = some i → InfoOk P i) (ho : ∀ i, o = some i → InfoOk P i) :
    ∀ c i, setInfo f u o c = some i → InfoOk P i := by
  intro c i hi
  rcases o with _ | j
  · exact hf c i hi
  · simp only [setInfo, Function.update_apply] at hi
    split at hi
    · cases hi; exact ho _ rfl
    · exact hf c i hi

/-- A step from a decoder whose decoded digests satisfy the invariant keeps it. -/
theorem step_ok_of (ℓ : Log) (δ : Dec) (t : Bytes) (hδ : ∀ c i, δ.info c = some i → InfoOk P i) :
    ShapeOk P (step σ P ℓ δ t).1 ∧ ∀ u i, (step σ P ℓ δ t).2 u = some i → InfoOk P i := by
  unfold step
  split
  · rename_i x _
    unfold rootStep
    split
    · rename_i hr
      exact ⟨⟨hr.1, hr.2.1, after_nodeAt hr, hr.2.2.1⟩, fun _ ↦ stInfo_ok hr.1 (after_nodeAt hr)⟩
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩
  · split
    · exact stepAt_ok ℓ _ _ _ _ fun i hi ↦ hδ _ i hi
    · exact ⟨trivial, fun _ _ hi ↦ by simp at hi⟩

/-- **The decoder's invariants**: every decoded digest and every record is at a reachable
history at which the program is at the recorded node. -/
theorem decode_ok (ℓ : Log) :
    (∀ c i, (decode σ P ℓ).info c = some i → InfoOk P i) ∧
      ∀ k ∈ (decode σ P ℓ).kinds, ShapeOk P k.1 := by
  induction ℓ using List.reverseRecOn with
  | nil => exact ⟨fun _ _ h ↦ by simp [Dec.init] at h, fun _ h ↦ by simp [Dec.init] at h⟩
  | append_singleton ℓ e ih =>
    obtain ⟨t, u⟩ := e
    have hstep := step_ok_of (σ := σ) ℓ (decode σ P ℓ) t ih.1
    refine ⟨?_, ?_⟩
    · rw [info_decode_append]
      exact setInfo_ok ih.1 (hstep.2 u)
    · rw [kinds_decode_append]
      intro k hk
      rcases List.mem_append.mp hk with hk | hk
      · exact ih.2 k hk
      · rw [List.mem_singleton] at hk
        subst hk
        exact hstep.1

/-- The record of the next entry satisfies the invariant. -/
theorem step_shapeOk (ℓ : Log) (t : Bytes) : ShapeOk P (step σ P ℓ (decode σ P ℓ) t).1 :=
  (step_ok_of ℓ (decode σ P ℓ) t (decode_ok ℓ).1).1

end Invariants

/-! ## The records of a step -/

section Records

variable {X : Type} {σ : Seeds X} {P : Prog Bool}

/-- A record after a nonce is read at the input `cv ‖ (n, 4)`, when the proof of work is not in
the log. -/
theorem step_grd {ℓ : Log} {δ : Dec} {t : Bytes} {h : List Ev} {p : Prog Bool} {b : ℕ}
    {cv : Digest} {n : E} (hs : (step σ P ℓ δ t).1 = .grd h p b cv n) :
    t = digestBytes cv ++ blockOf n 4 ∧ powIn ℓ cv n = none := by
  unfold step at hs
  split at hs
  · unfold rootStep at hs
    split at hs <;> cases hs
  · split at hs
    · rename_i cv' x tag hp
      obtain ⟨-, rfl⟩ := parse_eq_some hp
      unfold stepAt at hs
      split at hs
      · unfold stepSt at hs
        split at hs <;> try (split at hs <;> cases hs)
        all_goals try cases hs
        · split at hs
          · cases hs
          · split at hs
            · split at hs
              · rename_i htag hpow
                cases hs
                subst htag
                exact ⟨rfl, hpow⟩
              · cases hs
            · cases hs
      · split at hs
        · split at hs <;> cases hs
        · cases hs
      · split at hs
        · split at hs <;> cases hs
        · cases hs
      · cases hs
    · cases hs

/-- A record of a proof of work is read when the chain state after the nonce is not in the
log. -/
theorem step_pow {ℓ : Log} {δ : Dec} {t : Bytes} {h : List Ev} {p : Prog Bool} {b : ℕ}
    {cv : Digest} {n : E} (hs : (step σ P ℓ δ t).1 = .pow h p b cv n) :
    look ℓ (digestBytes cv ++ blockOf n 4) = none := by
  unfold step at hs
  split at hs
  · unfold rootStep at hs
    split at hs <;> cases hs
  · split at hs
    · unfold stepAt at hs
      split at hs
      · unfold stepSt at hs
        split at hs <;> try (split at hs <;> cases hs)
        all_goals try cases hs
        · split at hs
          · cases hs
          · split at hs
            · split at hs <;> cases hs
            · cases hs
      · split at hs
        · split at hs <;> cases hs
        · cases hs
      · split at hs
        · split at hs
          · rename_i hlook
            cases hs
            exact hlook
          · cases hs
        · cases hs
      · cases hs
    · cases hs

end Records

end
end LeanVM.Protocol.Compile.Rom
