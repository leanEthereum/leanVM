/-
  LeanVM.Protocol.Compile.Prog

  The interactive-oracle reading of the verifier language of `Statement.LeanVmVerifier`: histories
  of prover messages, challenges and committed words, and the round-by-round certificate whose
  escape probabilities the random-oracle theorem sums.
-/

module

public import Statement.LeanVmVerifier
public import Statement.Prover.Script
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Protocol.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.ENNReal.Operations

/-!
# The interactive reading of the verifier language

The language (`VerifierProgram`, its five operations, and the compiled reading `runProof` on a proof
with a hash function) is defined with the verifier, in `Statement.LeanVmVerifier` (Part 2). This
module gives the second reading of the same programs: a public-coin protocol in which the prover
sends field elements and whole matrices (`Word`s), and the verifier draws uniform challenges and
reads rows of the matrices directly. A run is a history (`List Ev`).

Soundness is stated on the interactive reading by a *doom certificate* (`Cert`): a predicate
`D` on histories ("the prover has lost") that prover moves keep, that the verdict refutes, and
that each *group* of challenges (the maximal run of samples and openings between two prover
moves) leaves with probability at most `ε` (`esc`). This is round-by-round soundness
([CCHLRR19]) with the challenges between two prover messages taken together, the form in which
a run of squeezes with no absorb in between (the query positions of a WHIR level) has its
escape probability. The random-oracle theorem turns a certificate into a bound on the compiled
verifier.

## Conventions

* A committed matrix is a `Word`: position `p` holds the row `word (p % 2^height)`, the reading
  the Merkle path gives a position (its low `height` bits pick the leaf,
  `crates/verifier/src/merkle.rs`).
* A history records a commitment with its shape and word, an opening with the rows the words
  give (`answer`); `Reachable P h` says `h` is a run of `P` with every opening answered from the
  words committed before it, and every committed word well shaped.
* The nonce of a proof of work is not recorded: no interactive reading depends on it. A proof of
  work `Ev.grind b` has `b ≥ 1` bits (`grindProofOfWork` grinds nothing at `0`), and on the
  verifier's program the challenge after it is drawn by its own permutation (`GrindThenSample`).
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

@[expose] public section

namespace VerifierProgram

variable {α β γ : Type}

@[simp] theorem pure_eq (a : α) : (pure a : VerifierProgram α) = ret a := rfl

@[simp] theorem bind_eq (p : VerifierProgram α) (f : α → VerifierProgram β) : p >>= f = p.bind
    f := rfl

@[simp] theorem ret_bind (a : α) (f : α → VerifierProgram β) : (ret a).bind f = f a := rfl

theorem bind_ret (p : VerifierProgram α) : p.bind ret = p := by
  induction p with
  | ret a => rfl
  | fail => rfl
  | read k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | grind b k ih => simp only [bind, ih]
  | commit h w k ih => simp only [bind, ih]
  | query i ps k ih => simp only [bind, ih]

theorem bind_assoc (p : VerifierProgram α) (f : α → VerifierProgram β) (g : β → VerifierProgram γ) :
    (p.bind f).bind g = p.bind fun a ↦ (f a).bind g := by
  induction p with
  | ret a => rfl
  | fail => rfl
  | read k ih => simp only [bind, ih]
  | sample k ih => simp only [bind, ih]
  | grind b k ih => simp only [bind, ih]
  | commit h w k ih => simp only [bind, ih]
  | query i ps k ih => simp only [bind, ih]

instance : LawfulMonad VerifierProgram := LawfulMonad.mk'
  (id_map := fun p ↦ bind_ret p)
  (pure_bind := fun _ _ ↦ rfl)
  (bind_assoc := fun p f g ↦ bind_assoc p f g)

end VerifierProgram

/-- Digests are finite: the uniform distribution of the random oracle ranges over them. A proof
object only: its element list has `2^256` entries, and compiled code would build it when the
program starts (a closed constant is evaluated at initialization), so it is `noncomputable`. -/
noncomputable instance instFintypeDigest : Fintype Digest :=
  Fintype.ofEquiv (Fin 4 → UInt64)
    { toFun := Vector.ofFn, invFun := fun v i ↦ v[i]
      left_inv := fun _ ↦ funext fun _ ↦ Vector.getElem_ofFn _
      right_inv := fun _ ↦ Vector.ext fun _ _ ↦ Vector.getElem_ofFn _ }

/-- Keccak states are finite, as digests are (`2^1600` of them). -/
noncomputable instance instFintypeKState : Fintype LeanVM.Semantics.KeccakState :=
  Fintype.ofEquiv (Fin 25 → UInt64)
    { toFun := Vector.ofFn, invFun := fun v i ↦ v[i]
      left_inv := fun _ ↦ funext fun _ ↦ Vector.getElem_ofFn _
      right_inv := fun _ ↦ Vector.ext fun _ _ ↦ Vector.getElem_ofFn _ }

/-! ## The interactive reading -/

-- `Word`, a committed matrix (the row at each position), is the statement's
-- (`Statement/Prover/Script.lean`).

/-- Every row of a word has `width` entries. -/
def WellShaped (width : ℕ) (word : Word) : Prop := ∀ p, (word p).length = width

/-- An event of an interactive run. -/
inductive Ev where
  /-- The prover sent the scalar `x`. -/
  | read (x : E)
  /-- The verifier drew the challenge `c`. -/
  | sample (c : E)
  /-- The prover passed (or skipped) a proof of work of `bits` bits. -/
  | grind (bits : ℕ)
  /-- The prover committed `word`, a matrix of `2^height` rows of `width` words. -/
  | commit (height width : ℕ) (word : Word)
  /-- The verifier opened rows and read `rows`. -/
  | query (rows : List (List K))

/-- The commitments of a history, in order, with their shapes. -/
def commits : List Ev → List (ℕ × ℕ × Word)
  | [] => []
  | Ev.commit h w word :: es => (h, w, word) :: commits es
  | _ :: es => commits es

/-- The rows the `i`-th commitment of `h` holds at `positions`, if there is such a commitment. -/
def answer (h : List Ev) (i : ℕ) (positions : List ℕ) : Option (List (List K)) :=
  (commits h)[i]?.map fun c ↦ positions.map fun p ↦ c.2.2 (p % 2 ^ c.1)

namespace VerifierProgram

variable {α : Type}

/-- The program after a history: follow the events, each of the kind the program expects. -/
def after : VerifierProgram α → List Ev → Option (VerifierProgram α)
  | p, [] => some p
  | read k, Ev.read x :: es => (k x).after es
  | sample k, Ev.sample c :: es => (k c).after es
  | grind b k, Ev.grind b' :: es => if b = b' then k.after es else none
  | commit h w k, Ev.commit h' w' _ :: es => if h = h' ∧ w = w' then k.after es else none
  | query _ _ k, Ev.query rows :: es => (k rows).after es
  | _, _ :: _ => none

/-- The interactive runs of a program: every prover move the program expects, every challenge,
every well-shaped commitment, and every opening answered from the words committed so far. -/
inductive Reachable (P : VerifierProgram α) : List Ev → Prop where
  | nil : Reachable P []
  | read {h k} (x : E) : Reachable P h → P.after h = some (read k) →
      Reachable P (h ++ [Ev.read x])
  | sample {h k} (c : E) : Reachable P h → P.after h = some (sample k) →
      Reachable P (h ++ [Ev.sample c])
  | grind {h b k} : Reachable P h → P.after h = some (grind b k) →
      Reachable P (h ++ [Ev.grind b])
  | commit {h ht w k} (word : Word) : Reachable P h → P.after h = some (commit ht w k) →
      WellShaped w word → Reachable P (h ++ [Ev.commit ht w word])
  | query {h i ps k rows} : Reachable P h → P.after h = some (query i ps k) →
      answer h i ps = some rows → Reachable P (h ++ [Ev.query rows])

end VerifierProgram

/-! ## Histories -/

/-- The commitments of a concatenation are those of each piece, in order. -/
theorem commits_append (h h' : List Ev) : commits (h ++ h') = commits h ++ commits h' := by
  induction h with
  | nil => rfl
  | cons e es ih => cases e <;> simp [commits, ih]

/-- Following a history in two pieces. -/
theorem VerifierProgram.after_append {α : Type} :
    ∀ (P : VerifierProgram α) (h h' : List Ev), P.after (h ++ h') = (P.after h).bind fun p ↦
        p.after h'
  | _, [], _ => by simp [VerifierProgram.after]
  | P, e :: es, h' => by
    cases P <;> cases e <;> simp only [List.cons_append, VerifierProgram.after,
        Option.bind_none] <;>
      first
      | exact VerifierProgram.after_append _ es h'
      | (split <;> simp [VerifierProgram.after_append _ es h'])

/-- One more event, after a history that leads to `p`, is read by `p`. -/
theorem VerifierProgram.after_append_single {α : Type} {P p : VerifierProgram α} {h : List Ev}
    (e : Ev)
    (ha : P.after h = some p) : P.after (h ++ [e]) = p.after [e] := by
  rw [VerifierProgram.after_append, ha, Option.bind_some]

/-- Every proof of work of the program is followed at once by a challenge. The compiled
verifier's proof of work permutes and keeps the permutation's first two lanes as the next
challenge (`absorbNonce`, `ground`), and rejects an absorption while it waits; on such a program
that challenge is the next event, drawn by the grind's own permutation. -/
def GrindThenSample {α : Type} (P : VerifierProgram α) : Prop :=
  ∀ h b k, P.after h = some (.grind b k) → ∃ k', k = .sample k'

/-- A history ends with a prover move (or is empty): the points at which a group of challenges
can start. -/
def Boundary : List Ev → Prop
  | [] => True
  | h => match h.getLast? with
    | some (Ev.read _) => True
    | some (Ev.grind _) => True
    | some (Ev.commit _ _ _) => True
    | _ => False

/-- The proof-of-work bits of the move that ends a history, `0` if it ends otherwise. -/
def grindBits (h : List Ev) : ℕ :=
  match h.getLast? with
  | some (Ev.grind b) => b
  | _ => 0

/-- The escape probability of a group: from history `h` at program `p`, the probability over
the group's uniform challenges that the run reaches the next prover move, or the verdict,
outside the doom predicate `D`. Openings answer from the words of `h`; an opening of a missing
commitment, and a rejection, escape nothing. -/
noncomputable def esc (D : List Ev → Prop) : List Ev → VerifierProgram Bool → ENNReal
  | h, VerifierProgram.sample k
      => (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, esc D (h ++ [Ev.sample c]) (k c)
  | h, VerifierProgram.query i ps k => match answer h i ps with
    | some rows => esc D (h ++ [Ev.query rows]) (k rows)
    | none => 0
  | _, VerifierProgram.fail => 0
  | _, VerifierProgram.ret false => 0
  | h, _ => by classical exact if D h then 0 else 1

/-- A **doom certificate** for the program `P`: a predicate `D` on histories ("the prover has
lost") with

* `read`, `grind`, `commit`: prover moves keep it (`commit` for well-shaped words);
* `group`: from a boundary history in `D` at which the program draws a challenge or opens rows,
  the group of challenges escapes `D` with probability at most `ε h`;
* `final`: the program does not accept from a history in `D`.

The random-oracle theorem bounds the probability that the compiled verifier accepts a proof whose
extracted history passes through `D` by the number of queries times the largest `ε`, each
discounted by the proof of work that precedes its group, plus the hash's collision terms. -/
structure Cert (P : VerifierProgram Bool) where
  /-- The doom predicate. -/
  D : List Ev → Prop
  /-- The escape bound of the group starting at a history. -/
  ε : List Ev → ENNReal
  /-- A scalar from the prover keeps doom. -/
  read : ∀ {h k} (x : E), P.Reachable h → P.after h = some (.read k) → D h →
    D (h ++ [Ev.read x])
  /-- A proof of work keeps doom. -/
  grind : ∀ {h b k}, P.Reachable h → P.after h = some (.grind b k) → D h →
    D (h ++ [Ev.grind b])
  /-- A well-shaped commitment keeps doom. -/
  commit : ∀ {h ht w k} (word : Word), P.Reachable h → P.after h = some (.commit ht w k) →
    WellShaped w word → D h → D (h ++ [Ev.commit ht w word])
  /-- A group of challenges escapes doom with probability at most `ε`. -/
  group : ∀ {h p}, P.Reachable h → Boundary h → P.after h = some p →
    (∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k) → D h → esc D h p ≤ ε h
  /-- The verifier rejects from doom. -/
  final : ∀ {h}, P.Reachable h → P.after h = some (.ret true) → ¬ D h

end
end LeanVM.Protocol.Compile
