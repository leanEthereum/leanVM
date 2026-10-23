/-
  LeanVM.Protocol.Compile.Prover

  The honest prover of a compiled verifier program and the completeness of the compilation: an
  interactive strategy that wins with probability one, run through the Fiat-Shamir chain with
  Merkle-committed words and a proof-of-work search, gives a proof the compiled verifier accepts,
  for every hash function.
-/

module

public import LeanVM.Spec.Verifier
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Parameters.Field
public import LeanVM.Protocol.ToArkLib.Merkle

/-!
# The honest prover and the completeness of the compilation

The prover is transcribed from the pinned leanVM
(`127510d14c98ade4e8a97646c44fa7f1ff5e752d`):

* the Fiat-Shamir chain is the one `run` checks (`crates/fiat_shamir/src/lib.rs:85-99`,
  `observe`, `sample`): a scalar sent is absorbed with tag `1`, a challenge squeezed with tag `2`;
* the proof of work is `grind_pow` (`lib.rs:47-51, 108-174`): at `bits = 0` the canonical nonce `0`,
  otherwise the smallest `u64` nonce `n`, as the scalar with limbs `(n, 0, 0)`, whose digest
  `H(H(cv ‖ (0, 3)) ‖ (n, 4))` has its low `bits` bits zero; the nonce is then absorbed with
  tag `4`. Here the search is bounded by a `fuel`: nonces `0, …, fuel - 1` (`findNonce`);
* a commitment is the Merkle tree of `merkle_tree` (`crates/pcs/src/merkle.rs:50-61`): the
  `2^height` rows of the word hashed as the little-endian bytes of their `K` words (`:401-404`),
  each parent the hash of the 64 bytes of its children, left first
  (`crates/fiat_shamir/src/merkle.rs:21-34`);
  its root goes on the stream as two scalars (`digestScalars`, `hash_to_scalars`);
* an opening is the row at the position's low `height` bits and its authentication path,
  leaf level first, one per queried position, in the order the verifier reads them (the
  unpruned form of `Proof.openings`).

An interactive prover is a `Strategy`: the scalar it sends and the word it commits, each a
function of the history so far. `runI` is the interactive run against challenges given as a
function of the history, every opening answered from the committed words (`answer`). The
compiled honest prover `prove` follows the program with the same strategy: the history it builds
is the interactive history in which each challenge is the one squeezed from the chain.

## Main results

* `runProof_prove`: for every hash function `H`, if the strategy is interactively perfectly
  complete (`∀ chal, runI P S chal = some true`) and commits well-shaped words (`shapedI`), every
  proof the honest prover produces is accepted by the compiled verifier `runProof` at `H`.
* `prove_ne_none`: the prover produces a proof as soon as every proof-of-work search along the
  run finds a nonce below `fuel`, which `findNonce_eq_none_iff` makes explicit.

Together: the compiled verifier accepts the honest proof for every hash function, so with
probability one over a random oracle, conditioned on the proof-of-work searches succeeding
(`exists_prove_runProof`). Only the `Id` instance of `run` is covered: the prover is a plain
function of `H`.

The proof is a simulation: from a history `h` and chain state `cv`, if the prover's output from
there is the stream `xs` and the openings `os`, then `run` from the state with chain `cv`, stream
`xs ++ restS`, openings `os ++ restO` and the roots of the trees committed in `h` returns `true`
with exactly `restS` and `restO` left (`run_proveFrom`). The Merkle step is the generic
`MerkleTree.rootOfPath_path`, after `climb_mod` reduces the position to its low `height` bits.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol

@[expose] public section

/-! ## The interactive honest prover -/

/-- An interactive prover: the scalar it sends at a `read` node and the word it commits at a
`commit` node, each from the history so far. -/
structure Strategy where
  /-- The scalar sent at a `read` node. -/
  msg : List Ev → E
  /-- The word committed at a `commit` node. -/
  word : List Ev → Word

namespace Strategy

/-- The interactive run of a program from a history, against the challenges `chal`: the
strategy's moves, the challenge at each `sample`, a passed proof of work at each `grind`, and the
rows the committed words give at each `query`; `none` on rejection or on an opening of a missing
commitment. -/
def runFrom (S : Strategy) (chal : List Ev → E) {α : Type} : Prog α → List Ev → Option α
  | .ret a, _ => some a
  | .fail, _ => none
  | .read k, h => S.runFrom chal (k (S.msg h)) (h ++ [Ev.read (S.msg h)])
  | .sample k, h => S.runFrom chal (k (chal h)) (h ++ [Ev.sample (chal h)])
  | .grind b k, h => S.runFrom chal k (h ++ [Ev.grind b])
  | .commit ht w k, h => S.runFrom chal k (h ++ [Ev.commit ht w (S.word h)])
  | .query i ps k, h => match answer h i ps with
    | some rows => S.runFrom chal (k rows) (h ++ [Ev.query rows])
    | none => none

/-- The words the strategy commits along the interactive run from a history, against the
challenges `chal`, are well shaped: each has the width its `commit` node announces. -/
def ShapedFrom (S : Strategy) (chal : List Ev → E) {α : Type} : Prog α → List Ev → Prop
  | .ret _, _ => True
  | .fail, _ => True
  | .read k, h => S.ShapedFrom chal (k (S.msg h)) (h ++ [Ev.read (S.msg h)])
  | .sample k, h => S.ShapedFrom chal (k (chal h)) (h ++ [Ev.sample (chal h)])
  | .grind b k, h => S.ShapedFrom chal k (h ++ [Ev.grind b])
  | .commit ht w k, h =>
    WellShaped w (S.word h) ∧ S.ShapedFrom chal k (h ++ [Ev.commit ht w (S.word h)])
  | .query i ps k, h => match answer h i ps with
    | some rows => S.ShapedFrom chal (k rows) (h ++ [Ev.query rows])
    | none => True

/-- The strategy wins from a history for every choice of the remaining challenges: the
program accepts, every committed word is well shaped, and every opening is answered. -/
def AcceptsFrom (S : Strategy) : Prog Bool → List Ev → Prop
  | .ret b, _ => b = true
  | .fail, _ => False
  | .read k, h => S.AcceptsFrom (k (S.msg h)) (h ++ [Ev.read (S.msg h)])
  | .sample k, h => ∀ c, S.AcceptsFrom (k c) (h ++ [Ev.sample c])
  | .grind b k, h => S.AcceptsFrom k (h ++ [Ev.grind b])
  | .commit ht w k, h =>
    WellShaped w (S.word h) ∧ S.AcceptsFrom k (h ++ [Ev.commit ht w (S.word h)])
  | .query i ps k, h =>
    ∃ rows, answer h i ps = some rows ∧ S.AcceptsFrom (k rows) (h ++ [Ev.query rows])

end Strategy

/-- The interactive run of a program from the empty history. -/
def runI {α : Type} (P : Prog α) (S : Strategy) (chal : List Ev → E) : Option α :=
  S.runFrom chal P []

/-- The words the strategy commits along the interactive run of a program are well shaped. -/
def shapedI {α : Type} (P : Prog α) (S : Strategy) (chal : List Ev → E) : Prop :=
  S.ShapedFrom chal P []

/-! ## The compiled honest prover -/

section Prover

variable (H : Bytes → Digest)

/-- The nonce `n` as a scalar: limb `0` holds the 64-bit word `n` (`F192::new(n, 0, 0)`). -/
def nonceOf (n : ℕ) : E := E.ofLimbs (K.ofBits n) 0 0

/-- The proof-of-work digest of a nonce at chain state `cv`: `H(H(cv ‖ (0, 3)) ‖ (n, 4))`, the
digest `run` checks at a `grind` node (`pow_base`, `pow_bits_ok`). -/
def powDigest (cv : Digest) (n : E) : Digest :=
  H (digestBytes (H (digestBytes cv ++ blockOf 0 3)) ++ blockOf n 4)

/-- The proof-of-work search (`grind_pow`): at `bits = 0` the nonce `0`; otherwise the smallest
`n < fuel` whose digest passes `powOk`, if any. -/
def findNonce (bits : ℕ) (cv : Digest) (fuel : ℕ) : Option E :=
  if bits = 0 then some (nonceOf 0)
  else ((List.range fuel).find? fun n ↦ powOk bits (nonceOf n) (powDigest H cv (nonceOf n))).map
    nonceOf

/-- The leaf hash: the hash of the leaf's words as little-endian bytes (`hash_words`). -/
def leafHash (leaf : List K) : Digest := H (leaf.flatMap kBytes)

/-- The node hash: the hash of the 64 bytes of the two children, left first (`hash_pair`). -/
def nodeHash (left right : Digest) : Digest := H (digestBytes left ++ digestBytes right)

/-- The `2^height` rows of a word. -/
def leavesOf (height : ℕ) (word : Word) : Vector (List K) (2 ^ height) :=
  Vector.ofFn fun i ↦ word i

/-- The Merkle root of the `2^height` rows of a word (`merkle_tree`). -/
def treeRoot (height : ℕ) (word : Word) : Digest :=
  MerkleTree.root (leafHash H) (nodeHash H) (leavesOf height word)

/-- The opening of a word's tree at position `q`: the row at `q`'s low `height` bits and its
authentication path, leaf level first. -/
def openingAt (height : ℕ) (word : Word) (q : ℕ) : Opening where
  leaf := word (q % 2 ^ height)
  path := MerkleTree.path (leafHash H) (nodeHash H) (leavesOf height word)
    ⟨q % 2 ^ height, Nat.mod_lt _ (Nat.two_pow_pos height)⟩

/-- The honest prover from a history `h` at chain state `cv`: the scalars and the openings it
puts in the proof from there on, or `none` if a proof-of-work search fails. A rejection, and an
opening of a missing commitment, end the proof. -/
def proveFrom (S : Strategy) (fuel : ℕ) {α : Type} :
    Prog α → Digest → List Ev → Option (List E × List Opening)
  | .ret _, _, _ => some ([], [])
  | .fail, _, _ => some ([], [])
  | .read k, cv, h =>
    (proveFrom S fuel (k (S.msg h)) (H (digestBytes cv ++ blockOf (S.msg h) 1))
      (h ++ [Ev.read (S.msg h)])).map fun t ↦ (S.msg h :: t.1, t.2)
  | .sample k, cv, h =>
    proveFrom S fuel (k (challengeOf (H (digestBytes cv ++ blockOf 0 2))))
      (H (digestBytes cv ++ blockOf 0 2))
      (h ++ [Ev.sample (challengeOf (H (digestBytes cv ++ blockOf 0 2)))])
  | .grind bits k, cv, h => match findNonce H bits cv fuel with
    | none => none
    | some n =>
      (proveFrom S fuel k (H (digestBytes cv ++ blockOf n 4)) (h ++ [Ev.grind bits])).map
        fun t ↦ (n :: t.1, t.2)
  | .commit ht w k, cv, h =>
    (proveFrom S fuel k
      (H (digestBytes (H (digestBytes cv ++ blockOf (digestScalars (treeRoot H ht (S.word h))).1 1))
        ++ blockOf (digestScalars (treeRoot H ht (S.word h))).2 1))
      (h ++ [Ev.commit ht w (S.word h)])).map
      fun t ↦ ((digestScalars (treeRoot H ht (S.word h))).1 ::
        (digestScalars (treeRoot H ht (S.word h))).2 :: t.1, t.2)
  | .query i ps k, cv, h => match (commits h)[i]? with
    | none => some ([], [])
    | some (ht, _, word) =>
      (proveFrom S fuel (k (ps.map fun q ↦ word (q % 2 ^ ht))) cv
        (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])).map
        fun t ↦ (t.1, ps.map (openingAt H ht word) ++ t.2)

/-- The honest prover: the proof of the program from the seed state and the empty history, or
`none` if a proof-of-work search finds no nonce below `fuel`. -/
def prove (P : Prog Bool) (S : Strategy) (seed : Digest) (fuel : ℕ) : Option Proof :=
  (proveFrom H S fuel P seed []).map fun t ↦ ⟨t.1, t.2⟩

end Prover

/-! ## Histories -/

/-- The commitments of a concatenation are those of each piece, in order. -/
theorem commits_append (h h' : List Ev) : commits (h ++ h') = commits h ++ commits h' := by
  induction h with
  | nil => rfl
  | cons e es ih => cases e <;> simp [commits, ih]

/-- Following a history in two pieces. -/
theorem Prog.after_append {α : Type} :
    ∀ (P : Prog α) (h h' : List Ev), P.after (h ++ h') = (P.after h).bind fun p ↦ p.after h'
  | _, [], _ => by simp [Prog.after]
  | P, e :: es, h' => by
    cases P <;> cases e <;> simp only [List.cons_append, Prog.after, Option.bind_none] <;>
      first
      | exact Prog.after_append _ es h'
      | (split <;> simp [Prog.after_append _ es h'])

/-- One more event, after a history that leads to `p`, is read by `p`. -/
theorem Prog.after_append_single {α : Type} {P p : Prog α} {h : List Ev} (e : Ev)
    (ha : P.after h = some p) : P.after (h ++ [e]) = p.after [e] := by
  rw [Prog.after_append, ha, Option.bind_some]

/-! ## From the interactive run to `AcceptsFrom` -/

namespace Strategy

/-- The run from `h` reads the challenges only at histories at least as long as `h`. -/
theorem runFrom_congr (S : Strategy) {α : Type} :
    ∀ (p : Prog α) (h : List Ev) (chal chal' : List Ev → E),
      (∀ h', h.length ≤ h'.length → chal h' = chal' h') →
        S.runFrom chal p h = S.runFrom chal' p h := by
  intro p
  induction p with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro h chal chal' hc
    exact ih _ _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
  | sample k ih =>
    intro h chal chal' hc
    simp only [runFrom]
    rw [hc h le_rfl]
    exact ih _ _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
  | grind b k ih =>
    intro h chal chal' hc
    exact ih _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
  | commit ht w k ih =>
    intro h chal chal' hc
    exact ih _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
  | query i ps k ih =>
    intro h chal chal' hc
    simp only [runFrom]
    split
    · exact ih _ _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
    · rfl

/-- The shape condition from `h` reads the challenges only at histories at least as long as
`h`. -/
theorem shapedFrom_congr (S : Strategy) {α : Type} :
    ∀ (p : Prog α) (h : List Ev) (chal chal' : List Ev → E),
      (∀ h', h.length ≤ h'.length → chal h' = chal' h') →
        S.ShapedFrom chal p h = S.ShapedFrom chal' p h := by
  intro p
  induction p with
  | ret a => intros; rfl
  | fail => intros; rfl
  | read k ih =>
    intro h chal chal' hc
    exact ih _ _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
  | sample k ih =>
    intro h chal chal' hc
    simp only [ShapedFrom]
    rw [hc h le_rfl]
    exact ih _ _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
  | grind b k ih =>
    intro h chal chal' hc
    exact ih _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
  | commit ht w k ih =>
    intro h chal chal' hc
    simp only [ShapedFrom]
    rw [ih _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)]
  | query i ps k ih =>
    intro h chal chal' hc
    simp only [ShapedFrom]
    split
    · exact ih _ _ _ _ fun h' hl ↦ hc h' (by simp at hl; omega)
    · rfl

/-- The challenges `chal` with the one at the histories of length `h.length` replaced by `c`. -/
private def setChal (chal : List Ev → E) (h : List Ev) (c : E) : List Ev → E :=
  fun h' ↦ if h'.length = h.length then c else chal h'

private theorem setChal_agree (chal : List Ev → E) (h : List Ev) (c : E) (e : Ev) :
    ∀ h', (h ++ [e]).length ≤ h'.length → setChal chal h c h' = chal h' := by
  intro h' hl
  simp only [List.length_append, List.length_singleton] at hl
  simp only [setChal, show h'.length ≠ h.length by omega, ↓reduceIte]

/-- A strategy that wins every interactive run from a history and commits well-shaped words
along it wins from that history for every choice of the remaining challenges. -/
theorem acceptsFrom_of_runFrom {S : Strategy} :
    ∀ (p : Prog Bool) (h : List Ev), (∀ chal, S.runFrom chal p h = some true) →
      (∀ chal, S.ShapedFrom chal p h) → S.AcceptsFrom p h := by
  intro p
  induction p with
  | ret b =>
    intro h hrun _
    simpa [runFrom, AcceptsFrom] using hrun fun _ ↦ 0
  | fail =>
    intro h hrun _
    simpa [runFrom] using hrun fun _ ↦ 0
  | read k ih =>
    intro h hrun hsh
    exact ih _ _ hrun hsh
  | sample k ih =>
    intro h hrun hsh c
    refine ih c _ (fun chal ↦ ?_) (fun chal ↦ ?_)
    · have hrun' := hrun (setChal chal h c)
      simp only [runFrom, setChal, ↓reduceIte] at hrun'
      rw [← hrun']
      exact runFrom_congr S _ _ _ _ fun h' hl ↦ (setChal_agree chal h c _ h' hl).symm
    · have hsh' := hsh (setChal chal h c)
      simp only [ShapedFrom, setChal, ↓reduceIte] at hsh'
      rwa [shapedFrom_congr S _ _ _ chal fun h' hl ↦ setChal_agree chal h c _ h' hl] at hsh'
  | grind b k ih =>
    intro h hrun hsh
    exact ih _ hrun hsh
  | commit ht w k ih =>
    intro h hrun hsh
    exact ⟨(hsh fun _ ↦ 0).1, ih _ hrun fun chal ↦ (hsh chal).2⟩
  | query i ps k ih =>
    intro h hrun hsh
    have h0 := hrun fun _ ↦ 0
    simp only [runFrom] at h0
    split at h0
    · rename_i rows hans
      refine ⟨rows, hans, ih rows _ (fun chal ↦ ?_) (fun chal ↦ ?_)⟩
      · simpa only [runFrom, hans] using hrun chal
      · simpa only [ShapedFrom, hans] using hsh chal
    · exact absurd h0 (by simp)

end Strategy

/-! ## The Merkle openings -/

section Merkle

variable (H : Bytes → Digest)

/-- The compiled verifier's climb is the generic one at the node hash. -/
theorem climb_eq_merkleClimb :
    ∀ (node : Digest) (q : ℕ) (path : List Digest),
      climb (m := Id) H node q path = MerkleTree.climb (nodeHash H) node q path
  | _, _, [] => rfl
  | node, q, s :: ss => by
    simp only [climb, MerkleTree.climb]
    by_cases hq : q % 2 = 0 <;> simp only [hq, ↓reduceIte] <;> exact climb_eq_merkleClimb _ _ _

/-- A climb reads the position only modulo two to the length of the path. -/
theorem climb_mod {D : Type} (hp : D → D → D) :
    ∀ (node : D) (q : ℕ) (path : List D),
      MerkleTree.climb hp node q path = MerkleTree.climb hp node (q % 2 ^ path.length) path
  | _, _, [] => rfl
  | node, q, s :: ss => by
    simp only [MerkleTree.climb, List.length_cons]
    have h2 : q % 2 ^ (ss.length + 1) % 2 = q % 2 :=
      Nat.mod_mod_of_dvd q (dvd_pow_self 2 (Nat.succ_ne_zero _))
    have hd : q % 2 ^ (ss.length + 1) / 2 % 2 ^ ss.length = q / 2 % 2 ^ ss.length := by
      rw [pow_succ', Nat.mod_mul_right_div_self, Nat.mod_mod]
    simp only [h2]
    rw [climb_mod hp _ (q / 2) ss, climb_mod hp _ (q % 2 ^ (ss.length + 1) / 2) ss, hd]

/-- The honest opening at any position is accepted under the root of a well-shaped word. -/
theorem openOne_openingAt {height width : ℕ} {word : Word} (hw : WellShaped width word)
    (q : ℕ) :
    openOne (m := Id) H (treeRoot H height word) height width q (openingAt H height word q) =
      true := by
  have hlen : (openingAt H height word q).path.length = height :=
    MerkleTree.length_path _ _ _ _
  have hleaf : (openingAt H height word q).leaf.length = width := hw _
  simp only [openOne, hleaf, hlen, and_self, ↓reduceIte]
  show decide ((climb (m := Id) H (leafHash H (word (q % 2 ^ height))) q
    (openingAt H height word q).path).toList = (treeRoot H height word).toList) = true
  rw [climb_eq_merkleClimb, climb_mod, hlen]
  have hroot := MerkleTree.rootOfPath_path (leafHash H) (nodeHash H) (leavesOf height word)
    ⟨q % 2 ^ height, Nat.mod_lt _ (Nat.two_pow_pos height)⟩
  simp only [leavesOf, Fin.getElem_fin, Vector.getElem_ofFn] at hroot
  simp only [MerkleTree.rootOfPath] at hroot
  simp only [openingAt, leavesOf, treeRoot, hroot, decide_true]

/-- The honest openings of a list of positions are accepted, give the rows, and leave the rest
of the openings. -/
theorem openAll_openingAt {height width : ℕ} {word : Word} (hw : WellShaped width word) :
    ∀ (ps : List ℕ) (rest : List Opening),
      openAll (m := Id) H (treeRoot H height word) height width ps
          (ps.map (openingAt H height word) ++ rest) =
        some (ps.map fun q ↦ word (q % 2 ^ height), rest)
  | [], _ => rfl
  | q :: qs, rest => by
    have ih := openAll_openingAt (height := height) hw qs rest
    have ho := openOne_openingAt H hw (height := height) q
    simp only [List.map_cons, List.cons_append, openAll]
    simp only [bind, pure] at ih ho ⊢
    simp only [ho, ↓reduceIte, ih]
    rfl

end Merkle

/-! ## The simulation -/

section Simulation

variable (H : Bytes → Digest)

/-- The roots the compiled verifier holds after the commitments of a history. -/
def rootsOf (cs : List (ℕ × ℕ × Word)) : List (Digest × ℕ × ℕ) :=
  cs.map fun c ↦ (treeRoot H c.1 c.2.2, c.1, c.2.1)

/-- The proof-of-work search returns a nonce that passes the check `run` makes. -/
theorem powOk_of_findNonce {bits : ℕ} {cv : Digest} {fuel : ℕ} {n : E}
    (hn : findNonce H bits cv fuel = some n) : powOk bits n (powDigest H cv n) = true := by
  unfold findNonce at hn
  split at hn
  · rename_i hb
    cases hn
    simp only [powOk, hb, ↓reduceIte, decide_eq_true_eq]
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hn
    have := List.find?_some hm
    exact this

/-- **The simulation.** If the strategy wins from `h`, the words committed in `h` are well
shaped, and the honest prover's output from `h` at chain state `cv` is `(xs, os)`, then the
compiled verifier, from chain state `cv` with the roots of `h`'s trees, accepts on any stream
and openings that start with `xs` and `os`, leaving exactly what follows them. -/
theorem run_proveFrom (S : Strategy) (fuel : ℕ) :
    ∀ (p : Prog Bool) (h : List Ev) (cv : Digest) (xs : List E) (os : List Opening)
      (restS : List E) (restO : List Opening),
      S.AcceptsFrom p h → (∀ c ∈ commits h, WellShaped c.2.1 c.2.2) →
      proveFrom H S fuel p cv h = some (xs, os) →
      ∃ s', run (m := Id) H p ⟨cv, xs ++ restS, os ++ restO, rootsOf H (commits h)⟩ =
          some (true, s') ∧ s'.stream = restS ∧ s'.openings = restO := by
  intro p
  induction p with
  | ret b =>
    intro h cv xs os restS restO hacc _ hp
    simp only [Strategy.AcceptsFrom] at hacc
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨_, by rw [hacc]; rfl, rfl, rfl⟩
  | fail =>
    intro h cv xs os restS restO hacc
    exact absurd hacc id
  | read k ih =>
    intro h cv xs os restS restO hacc hws hp
    simp only [proveFrom] at hp
    obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.read (S.msg h)]), WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ t.1 t.2 restS restO hacc hws' ht
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    simp [run, absorbBlock, commits_append, commits]
    rfl
  | sample k ih =>
    intro h cv xs os restS restO hacc hws hp
    simp only [proveFrom] at hp
    have hws' : ∀ c ∈ commits (h ++ [Ev.sample (challengeOf (H (digestBytes cv ++ blockOf 0 2)))]),
        WellShaped c.2.1 c.2.2 := by
      simpa [commits_append, commits] using hws
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ xs os restS restO (hacc _) hws' hp
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    simp [run, absorbBlock, commits_append, commits]
    rfl
  | grind b k ih =>
    intro h cv xs os restS restO hacc hws hp
    simp only [proveFrom] at hp
    split at hp
    · exact absurd hp (by simp)
    · rename_i n hn
      obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hws' : ∀ c ∈ commits (h ++ [Ev.grind b]), WellShaped c.2.1 c.2.2 := by
        simpa [commits_append, commits] using hws
      obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ t.1 t.2 restS restO hacc hws' ht
      refine ⟨s', ?_, hs1, hs2⟩
      have hpow := powOk_of_findNonce H hn
      rw [← hrun]
      simp only [commits_append, commits, List.append_nil] at *
      simp only [run, absorbBlock, List.cons_append]
      show (if powOk b n (powDigest H cv n) = true then _ else pure none) = _
      simp only [hpow, ↓reduceIte]
  | commit ht w k ih =>
    intro h cv xs os restS restO hacc hws hp
    obtain ⟨hw, hacc⟩ := hacc
    simp only [proveFrom] at hp
    obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hws' : ∀ c ∈ commits (h ++ [Ev.commit ht w (S.word h)]), WellShaped c.2.1 c.2.2 := by
      simp only [commits_append, commits, List.mem_append, List.mem_singleton]
      rintro c (hc | rfl)
      · exact hws c hc
      · exact hw
    obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ t.1 t.2 restS restO hacc hws' htt
    refine ⟨s', ?_, hs1, hs2⟩
    rw [← hrun]
    have hdec : digestOfScalars ((digestScalars (treeRoot H ht (S.word h))).1,
        (digestScalars (treeRoot H ht (S.word h))).2) = some (treeRoot H ht (S.word h)) :=
      digestOfScalars_digestScalars _
    have hroots : rootsOf H (commits (h ++ [Ev.commit ht w (S.word h)])) =
        rootsOf H (commits h) ++ [(treeRoot H ht (S.word h), ht, w)] := by
      simp [rootsOf, commits_append, commits]
    simp only [run, absorbBlock, List.cons_append, hdec]
    rw [hroots]
    rfl
  | query i ps k ih =>
    intro h cv xs os restS restO hacc hws hp
    obtain ⟨rows, hans, hacc⟩ := hacc
    simp only [proveFrom] at hp
    split at hp
    · rename_i hc
      simp [answer, hc] at hans
    · rename_i ht w word hc
      obtain ⟨t, htt, he⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hrows : rows = ps.map fun q ↦ word (q % 2 ^ ht) := by
        simp only [answer, hc, Option.map_some, Option.some.injEq] at hans
        exact hans.symm
      subst hrows
      have hws' : ∀ c ∈ commits (h ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))]),
          WellShaped c.2.1 c.2.2 := by
        simpa [commits_append, commits] using hws
      have hw : WellShaped w word := hws _ (List.mem_of_getElem? hc)
      obtain ⟨s', hrun, hs1, hs2⟩ := ih _ _ _ t.1 t.2 restS restO hacc hws' htt
      refine ⟨s', ?_, hs1, hs2⟩
      rw [← hrun]
      have hroot : (rootsOf H (commits h))[i]? = some (treeRoot H ht word, ht, w) := by
        simp [rootsOf, hc]
      have hopen := openAll_openingAt H hw (height := ht) ps (t.2 ++ restO)
      simp only [run, hroot, List.append_assoc]
      simp only [bind] at hopen ⊢
      rw [hopen]
      simp [commits_append, commits]

end Simulation

/-! ## Completeness -/

/-- **Completeness of the compilation.** For every hash function `H`, every program `P`,
strategy `S`, seed and fuel: if `S` wins every interactive run of `P` (whatever the
challenges) and commits well-shaped words, then every proof the honest prover produces is
accepted by the compiled verifier at `H`. -/
theorem runProof_prove (H : Bytes → Digest) (P : Prog Bool) (S : Strategy) (seed : Digest)
    (fuel : ℕ) {π : Proof} (hc : ∀ chal, runI P S chal = some true)
    (hs : ∀ chal, shapedI P S chal)
    (hπ : prove H P S seed fuel = some π) :
    runProof (m := Id) H P seed π = true := by
  have hacc : S.AcceptsFrom P [] :=
    Strategy.acceptsFrom_of_runFrom P [] hc hs
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hπ
  obtain ⟨s', hrun, hs1, hs2⟩ :=
    run_proveFrom H S fuel P [] seed t.1 t.2 [] [] hacc (by simp [commits]) ht
  simp only [List.append_nil] at hrun
  simp only [runProof, bind]
  show (match run (m := Id) H P ⟨seed, t.1, t.2, rootsOf H (commits [])⟩ with
    | some (true, s) => _ | _ => _) = true
  rw [hrun]
  simp [hs1, hs2]
  rfl

/-! ## When the prover produces a proof -/

/-- The proof-of-work search fails exactly when `bits > 0` and no nonce below `fuel` passes. -/
theorem findNonce_eq_none_iff (H : Bytes → Digest) (bits : ℕ) (cv : Digest) (fuel : ℕ) :
    findNonce H bits cv fuel = none ↔
      bits ≠ 0 ∧ ∀ n < fuel, powOk bits (nonceOf n) (powDigest H cv (nonceOf n)) = false := by
  unfold findNonce
  split
  · simp_all
  · rename_i hb
    simp [hb, List.find?_eq_none]

/-- The honest prover fails only at a failed proof-of-work search: from a history at which the
program is at `p`, if the search succeeds at every `grind` node the program can reach and every
chain state, the prover produces a proof. -/
theorem proveFrom_ne_none (H : Bytes → Digest) (S : Strategy) (fuel : ℕ) {P : Prog Bool}
    (hg : ∀ h bits k cv, P.after h = some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    ∀ (p : Prog Bool) (h : List Ev) (cv : Digest), P.after h = some p →
      proveFrom H S fuel p cv h ≠ none := by
  intro p
  induction p with
  | ret b => intros; simp [proveFrom]
  | fail => intros; simp [proveFrom]
  | read k ih =>
    intro h cv ha
    simp only [proveFrom, ne_eq, Option.map_eq_none_iff]
    exact ih _ _ _ (by rw [Prog.after_append_single _ ha]; simp [Prog.after])
  | sample k ih =>
    intro h cv ha
    simp only [proveFrom]
    exact ih _ _ _ (by rw [Prog.after_append_single _ ha]; simp [Prog.after])
  | grind b k ih =>
    intro h cv ha
    simp only [proveFrom]
    split
    · rename_i hn
      exact absurd hn (hg h b k cv ha)
    · simp only [ne_eq, Option.map_eq_none_iff]
      exact ih _ _ (by rw [Prog.after_append_single _ ha]; simp [Prog.after])
  | commit ht w k ih =>
    intro h cv ha
    simp only [proveFrom, ne_eq, Option.map_eq_none_iff]
    exact ih _ _ (by rw [Prog.after_append_single _ ha]; simp [Prog.after])
  | query i ps k ih =>
    intro h cv ha
    simp only [proveFrom]
    split
    · simp
    · simp only [ne_eq, Option.map_eq_none_iff]
      exact ih _ _ _ (by rw [Prog.after_append_single _ ha]; simp [Prog.after])

/-- The honest prover produces a proof as soon as the proof-of-work search succeeds at every
`grind` node of the program, at every chain state. -/
theorem prove_ne_none (H : Bytes → Digest) (P : Prog Bool) (S : Strategy) (seed : Digest)
    (fuel : ℕ)
    (hg : ∀ h bits k cv, P.after h = some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    prove H P S seed fuel ≠ none := by
  simp only [prove, ne_eq, Option.map_eq_none_iff]
  exact proveFrom_ne_none H S fuel hg P [] seed (Prog.after.eq_1 P)

/-- **Completeness, conditioned on the proof of work.** A strategy that wins every interactive
run with well-shaped words gives, for every hash function, an accepted proof whenever every
proof-of-work search finds its nonce below `fuel`. -/
theorem exists_prove_runProof (H : Bytes → Digest) (P : Prog Bool) (S : Strategy)
    (seed : Digest) (fuel : ℕ) (hc : ∀ chal, runI P S chal = some true)
    (hs : ∀ chal, shapedI P S chal)
    (hg : ∀ h bits k cv, P.after h = some (.grind bits k) → findNonce H bits cv fuel ≠ none) :
    ∃ π, prove H P S seed fuel = some π ∧ runProof (m := Id) H P seed π = true := by
  obtain ⟨π, hπ⟩ := Option.ne_none_iff_exists'.mp (prove_ne_none H P S seed fuel hg)
  exact ⟨π, hπ, runProof_prove H P S seed fuel hc hs hπ⟩

end
end LeanVM.Protocol.Compile
