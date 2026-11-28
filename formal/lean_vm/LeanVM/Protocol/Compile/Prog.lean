/-
  LeanVM.Protocol.Compile.Prog

  The interactive-oracle reading of the verifier language of `Statement.Verifier.Transcript`: histories
  of prover messages, challenges and committed words, and the round-by-round certificate whose
  escape probabilities the random-oracle theorem sums.
-/

module

public import Statement.Verifier.Lib
public import Statement.Prover.Script
import Statement.Fast.Keccak
import FastFields.QuadExt
import FastFields.FieldWords
import LeanVM.Protocol.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.ENNReal.Operations
public import LeanVM.Parameters.Field
public import ArkLib.OracleReduction.OracleInterface
public import CompPoly.Multilinear.Basic
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# The interactive reading of the verifier language

The language (`VerifierProgram`, its seven operations, and the compiled reading `runProof` on a proof
with a hash function) is defined with the verifier, in `Statement.Verifier.Transcript`. This
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

* A packed message is one event: `Ev.readPacked xs`, the `n` scalars of a `readPacked n` (a prover
  move), and `Ev.samplePacked cs`, the `n` challenges of a `samplePacked n`, uniform and
  independent in `E^n` (`avgPk`). A packed draw belongs to the group of challenges it is in: its
  escape probability is the average over `E^n`. The random-oracle theorem asks that every packed
  message of the program has at least one scalar (`VerifierProgram.PackedPos`).

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
  | readPacked n k ih => simp only [bind, ih]
  | samplePacked n k ih => simp only [bind, ih]
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
  | readPacked n k ih => simp only [bind, ih]
  | samplePacked n k ih => simp only [bind, ih]
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
  /-- The prover sent the packed message `xs` (`next_scalars_packed`). -/
  | readPacked (xs : List E)
  /-- The verifier drew the packed challenges `cs` (`samples_packed`). -/
  | samplePacked (cs : List E)

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
  | readPacked n k, Ev.readPacked xs :: es => if xs.length = n then (k xs).after es else none
  | samplePacked n k, Ev.samplePacked cs :: es => if cs.length = n then (k cs).after es else none
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
  | readPacked {h n k} (xs : List E) : Reachable P h → P.after h = some (readPacked n k) →
      xs.length = n → Reachable P (h ++ [Ev.readPacked xs])
  | samplePacked {h n k} (cs : List E) : Reachable P h → P.after h = some (samplePacked n k) →
      cs.length = n → Reachable P (h ++ [Ev.samplePacked cs])

end VerifierProgram

namespace VerifierProgram

variable {α β : Type}

/-- **No packed message**: the program reads and draws no packed message (`readPacked`,
`samplePacked`) on any path. -/
def NoPacked : VerifierProgram α → Prop
  | ret _ => True
  | fail => True
  | read k => ∀ x, (k x).NoPacked
  | sample k => ∀ x, (k x).NoPacked
  | readPacked _ _ => False
  | samplePacked _ _ => False
  | grind _ k => k.NoPacked
  | commit _ _ k => k.NoPacked
  | query _ _ k => ∀ rows, (k rows).NoPacked

/-- A sequence of programs without packed messages has none. -/
theorem NoPacked.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.NoPacked)
    (hf : ∀ a, (f a).NoPacked) : (p.bind f).NoPacked := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked n k ih => exact hp.elim
  | samplePacked n k ih => exact hp.elim
  | grind b k ih => exact ih hp
  | commit h w k ih => exact ih hp
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

/-- A program without packed messages has none after any history. -/
theorem NoPacked.after {p : VerifierProgram α} (hp : p.NoPacked) (h : List Ev)
    {q : VerifierProgram α} (ha : p.after h = some q) : q.NoPacked := by
  induction h generalizing p with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq] at ha
    exact ha ▸ hp
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    all_goals first
      | exact ih (hp _) ha
      | exact hp.elim
      | (split at ha
         · exact ih (p := _) (by exact hp) ha
         · cases ha)

/-- **Every packed message has a scalar**: every `readPacked n` and `samplePacked n` of the
program, on every path, has `n ≥ 1`. The random-oracle theorem asks it of the program: a packed
message of none takes no permutation (`observePacked`, `samplesPacked`), and its event would
have none to decode it from. leanVM's packed messages all have at least one scalar. -/
def PackedPos : VerifierProgram α → Prop
  | ret _ => True
  | fail => True
  | read k => ∀ x, (k x).PackedPos
  | sample k => ∀ x, (k x).PackedPos
  | readPacked n k => 0 < n ∧ ∀ xs, (k xs).PackedPos
  | samplePacked n k => 0 < n ∧ ∀ xs, (k xs).PackedPos
  | grind _ k => k.PackedPos
  | commit _ _ k => k.PackedPos
  | query _ _ k => ∀ rows, (k rows).PackedPos

/-- A program without packed messages has every packed message nonempty. -/
theorem NoPacked.packedPos {p : VerifierProgram α} (hp : p.NoPacked) : p.PackedPos := by
  induction p with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked n k ih => exact hp.elim
  | samplePacked n k ih => exact hp.elim
  | grind b k ih => exact ih hp
  | commit h w k ih => exact ih hp
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

/-- A sequence of programs whose packed messages are nonempty has them nonempty. -/
theorem PackedPos.bind {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : p.PackedPos)
    (hf : ∀ a, (f a).PackedPos) : (p.bind f).PackedPos := by
  induction p with
  | ret a => exact hf a
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | readPacked n k ih => exact ⟨hp.1, fun xs ↦ ih xs (hp.2 xs)⟩
  | samplePacked n k ih => exact ⟨hp.1, fun xs ↦ ih xs (hp.2 xs)⟩
  | grind b k ih => exact ih hp
  | commit h w k ih => exact ih hp
  | query i ps k ih => exact fun rows ↦ ih rows (hp rows)

namespace PackedPos

theorem ret' (a : α) : (ret a).PackedPos := trivial

theorem readScalar' : readScalar.PackedPos := fun _ ↦ trivial

theorem sampleChallenge' : sampleChallenge.PackedPos := fun _ ↦ trivial

/-- A packed message of at least one scalar. -/
theorem readScalarsPacked' {n : ℕ} (hn : 0 < n) : (readScalarsPacked n).PackedPos :=
  ⟨hn, fun _ ↦ trivial⟩

/-- A packed draw of at least one challenge. -/
theorem sampleChallengesPacked' {n : ℕ} (hn : 0 < n) : (sampleChallengesPacked n).PackedPos :=
  ⟨hn, fun _ ↦ trivial⟩

theorem grindProofOfWork' (b : ℕ) : (grindProofOfWork b).PackedPos := by
  unfold grindProofOfWork; split <;> trivial

theorem readCommitment' (ht w : ℕ) : (readCommitment ht w).PackedPos := trivial

theorem queryOpenings' (i : ℕ) (ps : List ℕ) : (queryOpenings i ps).PackedPos := fun _ ↦ trivial

theorem require' (c : Prop) [Decidable c] : (require c).PackedPos := by
  unfold require; split <;> trivial

theorem ite' {c : Prop} [Decidable c] {p q : VerifierProgram α} (hp : c → p.PackedPos)
    (hq : ¬ c → q.PackedPos) : (if c then p else q).PackedPos := by
  split
  · exact hp ‹_›
  · exact hq ‹_›

end PackedPos

/-- Nonempty packed messages after any history. -/
theorem PackedPos.after {p : VerifierProgram α} (hp : p.PackedPos) (h : List Ev)
    {q : VerifierProgram α} (ha : p.after h = some q) : q.PackedPos := by
  induction h generalizing p with
  | nil =>
    simp only [VerifierProgram.after, Option.some.injEq] at ha
    exact ha ▸ hp
  | cons e es ih =>
    cases p <;> cases e <;> simp only [VerifierProgram.after, reduceCtorEq] at ha
    all_goals first
      | exact ih (hp _) ha
      | (split at ha
         · first | exact ih (hp.2 _) ha | exact ih (p := _) (by exact hp) ha
         · cases ha)

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

/-- Every proof of work of the program is followed at once by a challenge, or a packed draw of at
least one. The compiled verifier's proof of work permutes and keeps the permutation's first two
lanes as the next challenge (`absorbNonce`, `ground`), and rejects an absorption while it waits;
on such a program that challenge is the next event's (the first of a packed draw), drawn by the
grind's own permutation. -/
def GrindThenSample {α : Type} (P : VerifierProgram α) : Prop :=
  ∀ h b k, P.after h = some (.grind b k) →
    (∃ k', k = .sample k') ∨ ∃ n k', k = .samplePacked (n + 1) k'

/-- A history ends with a prover move (or is empty): the points at which a group of challenges
can start. -/
def Boundary : List Ev → Prop
  | [] => True
  | h => match h.getLast? with
    | some (Ev.read _) => True
    | some (Ev.grind _) => True
    | some (Ev.commit _ _ _) => True
    | some (Ev.readPacked _) => True
    | _ => False

/-- The proof-of-work bits of the move that ends a history, `0` if it ends otherwise. -/
def grindBits (h : List Ev) : ℕ :=
  match h.getLast? with
  | some (Ev.grind b) => b
  | _ => 0

/-- The average over `n` uniform and independent challenges: `avgPk n f` is `f` averaged over
the lists of `n` elements of `E`. -/
noncomputable def avgPk : ℕ → (List E → ENNReal) → ENNReal
  | 0, f => f []
  | n + 1, f => (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, avgPk n fun cs ↦ f (c :: cs)

section AvgPk

open Finset

theorem avgPk_zero (f : List E → ENNReal) : avgPk 0 f = f [] := rfl

theorem avgPk_succ (n : ℕ) (f : List E → ENNReal) :
    avgPk (n + 1) f = (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, avgPk n fun cs ↦ f (c :: cs) := rfl

theorem inv_card_mul_sum_const (b : ENNReal) :
    (Fintype.card E : ENNReal)⁻¹ * ∑ _c : E, b = b := by
  rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

/-- Only the lists of `n` challenges count. -/
theorem avgPk_mono {n : ℕ} {f g : List E → ENNReal} (h : ∀ l, l.length = n → f l ≤ g l) :
    avgPk n f ≤ avgPk n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
    rw [avgPk_succ, avgPk_succ]
    gcongr with c
    exact ih fun l hl ↦ h (c :: l) (by simp [hl])

theorem avgPk_congr {n : ℕ} {f g : List E → ENNReal} (h : ∀ l, l.length = n → f l = g l) :
    avgPk n f = avgPk n g :=
  le_antisymm (avgPk_mono fun l hl ↦ (h l hl).le) (avgPk_mono fun l hl ↦ (h l hl).ge)

theorem avgPk_const (n : ℕ) (b : ENNReal) : avgPk n (fun _ ↦ b) = b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [avgPk_succ]; simp only [ih]; exact inv_card_mul_sum_const b

theorem avgPk_le_of_le {n : ℕ} {f : List E → ENNReal} {b : ENNReal}
    (h : ∀ l, l.length = n → f l ≤ b) : avgPk n f ≤ b :=
  (avgPk_mono h).trans_eq (avgPk_const n b)

theorem avgPk_add (n : ℕ) (f g : List E → ENNReal) :
    avgPk n (fun l ↦ f l + g l) = avgPk n f + avgPk n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [avgPk_succ, ih, sum_add_distrib, mul_add]

theorem avgPk_mul_left (n : ℕ) (a : ENNReal) (f : List E → ENNReal) :
    avgPk n (fun l ↦ a * f l) = a * avgPk n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [avgPk_succ, ih, ← mul_sum]
    ring

/-- **Splitting the challenges in two runs.** -/
theorem avgPk_append (n m : ℕ) (f : List E → ENNReal) :
    avgPk (n + m) f = avgPk n fun a ↦ avgPk m fun b ↦ f (a ++ b) := by
  induction n generalizing f with
  | zero => simp [avgPk_zero]
  | succ n ih =>
    rw [Nat.succ_add, avgPk_succ, avgPk_succ]
    simp only [ih, List.cons_append]

/-- The average is the sum over the challenge vectors over their number. -/
theorem avgPk_eq_sum (n : ℕ) (f : List E → ENNReal) :
    avgPk n f = (∑ v : Fin n → E, f (List.ofFn v)) / (Fintype.card E : ENNReal) ^ n := by
  induction n generalizing f with
  | zero => simp [avgPk_zero]
  | succ n ih =>
    rw [avgPk_succ]
    simp only [ih]
    have hsplit : ∑ v : Fin (n + 1) → E, f (List.ofFn v) =
        ∑ c : E, ∑ v : Fin n → E, f (c :: List.ofFn v) := by
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) ↦ E).sum_comp, Fintype.sum_prod_type]
      refine sum_congr rfl fun c _ ↦ sum_congr rfl fun v _ ↦ ?_
      simp [Fin.consEquiv, List.ofFn_succ]
    have h0 : (Fintype.card E : ENNReal) ≠ 0 := by simp
    have ht : (Fintype.card E : ENNReal) ≠ ⊤ := by simp
    rw [hsplit, pow_succ, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inr ht) (Or.inr h0)]
    simp only [ENNReal.div_eq_inv_mul, Finset.mul_sum]
    refine sum_congr rfl fun c _ ↦ sum_congr rfl fun v _ ↦ ?_
    ring

open Classical in
/-- An indicator's average is its set's size over `|E|^n`. -/
theorem avgPk_indicator (n : ℕ) (B : List E → Prop) :
    avgPk n (fun l ↦ if B l then 1 else 0) =
      ((univ.filter fun v : Fin n → E ↦ B (List.ofFn v)).card : ENNReal) /
        (Fintype.card E : ENNReal) ^ n := by
  rw [avgPk_eq_sum, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_one]

open Classical in
/-- **The counting bound.** A set of at most `N·|E|^(n-1)` of the `|E|^n` challenge vectors has
average at most `N/|E|`. -/
theorem avgPk_le_card {n N : ℕ} (hn : 1 ≤ n) (B : List E → Prop)
    (hc : (univ.filter fun v : Fin n → E ↦ B (List.ofFn v)).card ≤ N * Fintype.card E ^ (n - 1)) :
    avgPk n (fun l ↦ if B l then 1 else 0) ≤ (N : ENNReal) / Fintype.card E := by
  rw [avgPk_indicator]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hc
  have h0 : (Fintype.card E : ENNReal) ≠ 0 := by simp
  have ht : (Fintype.card E : ENNReal) ≠ ⊤ := by simp
  rw [ENNReal.div_le_iff (pow_ne_zero _ h0) (ENNReal.pow_ne_top ht),
    pow_succ, ← mul_assoc, mul_right_comm, ENNReal.div_mul_cancel h0 ht]
  exact_mod_cast hc

end AvgPk

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
  | h, VerifierProgram.samplePacked n k =>
      avgPk n fun cs ↦ esc D (h ++ [Ev.samplePacked cs]) (k cs)
  | _, VerifierProgram.fail => 0
  | _, VerifierProgram.ret false => 0
  | h, _ => by classical exact if D h then 0 else 1

/-- A **doom certificate** for the program `P`: a predicate `D` on histories ("the prover has
lost") with

* `read`, `readPacked`, `grind`, `commit`: prover moves keep it (`commit` for well-shaped
  words);
* `group`: from a boundary history in `D` at which the program draws a challenge (or a packed
  draw) or opens rows,
  the group of challenges escapes `D` with probability at most `ε h`;
* `final`: where the program accepts from a history in `D`, that history satisfies `G`.

With `G` false (`Cert`), the program does not accept from doom. The random-oracle theorem bounds
the probability that the compiled verifier accepts a proof whose extracted history passes through
`D` and fails `G` by the number of queries times the largest `ε`, each discounted by the proof of
work that precedes its group, plus the hash's collision terms. -/
structure CertG (P : VerifierProgram Bool) (G : List Ev → Prop) where
  /-- The doom predicate. -/
  D : List Ev → Prop
  /-- The escape bound of the group starting at a history. -/
  ε : List Ev → ENNReal
  /-- A scalar from the prover keeps doom. -/
  read : ∀ {h k} (x : E), P.Reachable h → P.after h = some (.read k) → D h →
    D (h ++ [Ev.read x])
  /-- A packed message from the prover keeps doom. -/
  readPacked : ∀ {h n k} (xs : List E), P.Reachable h → P.after h = some (.readPacked n k) →
    xs.length = n → D h → D (h ++ [Ev.readPacked xs])
  /-- A proof of work keeps doom. -/
  grind : ∀ {h b k}, P.Reachable h → P.after h = some (.grind b k) → D h →
    D (h ++ [Ev.grind b])
  /-- A well-shaped commitment keeps doom. -/
  commit : ∀ {h ht w k} (word : Word), P.Reachable h → P.after h = some (.commit ht w k) →
    WellShaped w word → D h → D (h ++ [Ev.commit ht w word])
  /-- A group of challenges escapes doom with probability at most `ε`. -/
  group : ∀ {h p}, P.Reachable h → Boundary h → P.after h = some p →
    (∃ k, p = .sample k) ∨ (∃ i ps k, p = .query i ps k) ∨ (∃ n k, p = .samplePacked n k) →
      D h → esc D h p ≤ ε h
  /-- Where the verifier accepts from doom, the history satisfies `G`. -/
  final : ∀ {h}, P.Reachable h → P.after h = some (.ret true) → D h → G h

/-- A **doom certificate** with nothing accepted from doom: the verifier rejects from `D`. -/
abbrev Cert (P : VerifierProgram Bool) := CertG P fun _ ↦ False

end
end LeanVM.Protocol.Compile
