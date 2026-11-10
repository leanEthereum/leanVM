module

public import Statement.Prover.Script

/-!
# Running a prover's script against the verifier's program

`runFrom F fuel P S sp cs` runs the script `S` against the verifier's program `P` through the
Fiat-Shamir sponge `sp`, over the permutation `F` (Keccak-256 the sponge over `F`), and returns the
proof's scalars and Merkle openings: a script's scalar is absorbed at each `read` of `P`, a
challenge squeezed at each `sample`; a `grind` takes the smallest nonce below `fuel` that passes
(`grind`, `crates/fiat_shamir/src/lib.rs`), the proof failing if none does, absorbs it and permutes
(`absorbNonce`), the permutation's challenge kept for the next `sample`; a `commit`
builds the matrix's Merkle tree once (`MerkleBuilder`, `crates/pcs/src/merkle.rs:39-176`) and sends
its root;
a `query` gives the script the rows at the positions and puts their openings, read off the tree,
in the proof as one phase. Where the script's move is not the program's, the run sends `0`,
commits the empty matrix and gives the script nothing more; a script that follows the program
never meets it.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-! ## Merkle trees -/

/-- A committed matrix with its Merkle tree: the height, the rows, and the tree's levels, the
`2^height` leaf digests first and the root, alone, last. -/
structure Tree where
  height : ℕ
  word : Word
  levels : Array (Array Digest)

/-- The sibling of node `i` of a level. -/
def sibling (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- The root of a tree. -/
def Tree.root (t : Tree) : Digest := (t.levels.getD t.height #[]).getD 0 default

/-- The opening of a tree at position `q` (`open`, `crates/fiat_shamir/src/merkle.rs:51-68`): the
position, the row at `q`'s low `height` bits and its authentication path, leaf level first. -/
def Tree.opening (t : Tree) (q : ℕ) : Opening :=
  let i := q % 2 ^ t.height
  ⟨q, t.word i, (List.range t.height).map fun l ↦
    (t.levels.getD l #[]).getD (sibling (i / 2 ^ l)) default⟩

section Monadic

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- The leaf digests of the `2^height` rows of a matrix (`hash_words`). -/
def leafDigestsM (height : ℕ) (word : Word) : m (Array Digest) :=
  (Array.range (2 ^ height)).mapM fun i ↦ keccak256With F ((word i).flatMap K.toBytes)

/-- The first `n` parents of a level: parent `j` hashes nodes `2j` and `2j + 1`
(`hash_pair`). -/
def parentsM (level : Array Digest) (n : ℕ) : m (Array Digest) :=
  (Array.range n).mapM fun j ↦
    keccak256With F
      (digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))

/-- The levels of a tree from a level of `2^k` nodes up to the root. -/
def levelsM : ℕ → Array Digest → m (List (Array Digest))
  | 0, level => pure [level]
  | k + 1, level => do
    let up ← parentsM F level (2 ^ k)
    let rest ← levelsM k up
    pure (level :: rest)

/-- The Merkle tree of the `2^height` rows of a matrix. -/
def buildTreeM (height : ℕ) (word : Word) : m Tree := do
  let leaves ← leafDigestsM F height word
  let levels ← levelsM F height leaves
  pure ⟨height, word, levels.toArray⟩

/-! ## Proofs of work -/

/-- The nonce `n` as a scalar: limb `0` holds the 64-bit word `n` (`F128::new(n, 0)`). -/
def nonceOf (n : ℕ) : E := E.ofLimbs (K.ofBits n) 0

/-- The nonce search from `n`, trying `count` nonces: the first that passes, each absorbed with
tag `4` into the sponge `sp` and permuted, the permutation's third lane checked (`pow_bits_ok`). -/
def searchM (bits : ℕ) (sp : Sponge) : ℕ → ℕ → m (Option E)
  | _, 0 => pure none
  | n, count + 1 => do
    let r ← absorbNonce F sp (nonceOf n)
    if powOk bits r.1 then pure (some (nonceOf n)) else searchM bits sp (n + 1) count

/-- The proof-of-work search (`FiatShamirState::grind`, `crates/fiat_shamir/src/lib.rs:170-215`):
the smallest nonce below `fuel` that passes, if one does. The Rust's parallel search returns the
smallest passing nonce too: the first matching batch of the first matching block, and its first
match. -/
def findNonceM (bits : ℕ) (sp : Sponge) (fuel : ℕ) : m (Option E) := searchM F bits sp 0 fuel

end Monadic

/-! ## The script's moves -/

namespace Script

variable {β : Type}

/-- The scalar a script sends, `0` if it does not send one. -/
def msgOf : Option (Script β) → E
  | some (.send x _) => x
  | _ => 0

/-- The script after sending. -/
def afterSend : Option (Script β) → Option (Script β)
  | some (.send _ k) => some k
  | _ => none

/-- The script after receiving the challenge `c`. -/
def afterSample (c : E) : Option (Script β) → Option (Script β)
  | some (.sample k) => some (k c)
  | _ => none

/-- The script after a proof of work. -/
def afterGrind : Option (Script β) → Option (Script β)
  | some (.grind k) => some k
  | _ => none

/-- The matrix a script commits, the empty rows if it does not commit one. -/
def wordOf : Option (Script β) → Word
  | some (.commit w _) => w
  | _ => fun _ ↦ []

/-- The script after committing. -/
def afterCommit : Option (Script β) → Option (Script β)
  | some (.commit _ k) => some k
  | _ => none

/-- The script after receiving the rows `rows`. -/
def afterQuery (rows : List (List K)) : Option (Script β) → Option (Script β)
  | some (.query k) => some (k rows)
  | _ => none

end Script

/-! ## The run -/

section Run

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- **The script `S` against the program `P`**, from the sponge `sp` and the trees `cs` committed
so far: the scalars and the openings the proof holds from there on, or `none` if a proof-of-work
search finds no nonce below `fuel`. A rejection, and an opening of a missing commitment, end the
proof. -/
def runFrom (fuel : ℕ) {α β : Type} :
    VerifierProgram α → Option (Script β) → Sponge → List Tree →
      m (Option (List E × List (List Opening)))
  | .ret _, _, _, _ => pure (some ([], []))
  | .fail, _, _, _ => pure (some ([], []))
  | .read k, S, sp, cs => do
    let sp' ← absorb F sp (Script.msgOf S) dsObserve
    let r ← runFrom fuel (k (Script.msgOf S)) (Script.afterSend S) sp' cs
    pure (r.map fun t ↦ (Script.msgOf S :: t.1, t.2))
  | .sample k, S, sp, cs => do
    let r ← squeeze F sp
    runFrom fuel (k r.1) (Script.afterSample r.1 S) r.2 cs
  | .grind bits k, S, sp, cs => do
    match ← findNonceM F bits sp fuel with
    | none => pure none
    | some n => do
      let r ← absorbNonce F sp n
      let t ← runFrom fuel k (Script.afterGrind S) r.2 cs
      pure (t.map fun t ↦ (n :: t.1, t.2))
  | .commit ht _ k, S, sp, cs => do
    let tree ← buildTreeM F ht (Script.wordOf S)
    let sp0 ← absorb F sp (digestHalves tree.root).1 dsObserve
    let sp1 ← absorb F sp0 (digestHalves tree.root).2 dsObserve
    let r ← runFrom fuel k (Script.afterCommit S) sp1 (cs ++ [tree])
    pure (r.map fun t ↦ ((digestHalves tree.root).1 :: (digestHalves tree.root).2 :: t.1, t.2))
  | .query i ps k, S, sp, cs => match cs[i]? with
    | none => pure (some ([], []))
    | some tree => do
      let rows := ps.map fun q ↦ tree.word (q % 2 ^ tree.height)
      let r ← runFrom fuel (k rows) (Script.afterQuery rows S) sp cs
      pure (r.map fun t ↦ (t.1, ps.map tree.opening :: t.2))

/-- **A proof from a script**: the script run against the program from the seed, or `none` if a
proof-of-work search finds no nonce below `fuel`. -/
def runScript (P : VerifierProgram Bool) {β : Type} (S : Script β) (seed : KeccakState) (fuel : ℕ) :
    m (Option Proof) := do
  let r ← runFrom F fuel P (some S) ⟨seed, [], none⟩ []
  pure (r.map fun t ↦ (⟨t.1, t.2⟩ : Proof))

end Run

end LeanVM.Prover

end
