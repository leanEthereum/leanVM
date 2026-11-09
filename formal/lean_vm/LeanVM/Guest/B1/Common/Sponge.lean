/-
  LeanVM.Guest.B1.Common.Sponge

  The guest's Fiat-Shamir sponge as it carries it, five capacity cells and the scalars waiting,
  its operations on the cells, and the Spec's sponge it stands for.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Protocol.WithHash

/-!
# The sponge the guest carries

The verifier's transcript (`Statement/LeanVmVerifier.lean`, `Sponge`, `absorb`, `squeeze`, `duplex`) is a
duplex over Keccak-f[1600]: a state of 25 lanes and up to four waiting scalars, each with a tag.
The guest (`crates/rec_aggregation/guests/lean_ethereum.py` at leanVM main `40f877dc`, G below,
G:600-710) carries between permutations only the capacity, the cells `8..12` of the last
permutation's output in the even layout (lanes `16..24`, `fs0 .. fs4`), and the waiting scalars
as rate cells (`fs_pack`) or as values its callers re-pack. A duplex reads nothing else of the
state (`duplexInput`), so the guest's sponge is the pair `Fs` of the five capacity cells and the
waiting scalars:

* `capOf S`: the five capacity cells of a state;
* `rateOf pend`: the eight rate cells of the waiting scalars (`Keccak.rateCell`, `fs_pack`'s
  cells, zero past them);
* `permOf cells`: the state one `KECCAK` in the even layouts writes from thirteen cells read;
* `Fs.perm`, `Fs.absorb`, `Fs.squeeze`, `Fs.absorbAll`: the Spec's sponge operations on the
  carried cells (`absorb` permutes a full queue first, `squeeze` permutes and reads
  `challengeOf`);
* `Fs.Carries s sp`: the Spec's sponge `sp` is the one the guest carries as `s` (its state's
  capacity cells are `s.cap`, its waiting scalars `s.pend`);
* `runId`: the deployed reading of a Spec program (`Compile.run` at `keccak256`, `keccakF`);
* `RunsTo p s xs a s'`: from any sponge the guest carries as `s`, the Spec program `p` reads
  exactly the stream words `xs`, returns `a` and leaves a sponge the guest carries as `s'`, on any
  rest of the stream, openings and roots.

A B1 meaning states what a function computes on the carried cells with these operations; the
`…_run` theorems of each family turn it into a `RunsTo` of the Spec program the function
mirrors.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Cells of the sponge -/

/-- The five capacity cells of a state: cells `8..12` of its even layout, lanes `16..24`
(`fs0 .. fs4`, `sp[8] .. sp[12]`). -/
def capOf (S : KeccakState) : List E :=
  [cellsOfState S false 8, cellsOfState S false 9, cellsOfState S false 10,
    cellsOfState S false 11, cellsOfState S false 12]

/-- The eight rate cells of the waiting scalars: scalar `k`'s two cells at `2k`, `2k + 1`
(`fs_pack`), zero past them. -/
def rateOf (pend : List (E × ℕ)) : List E := (List.range 8).map (Keccak.rateCell pend)

/-- The state one `KECCAK` in the even layouts writes from the thirteen cells it reads. -/
def permOf (cells : List E) : KeccakState := keccakF1600 (stateOfCells (cells13 cells) false)

/-- Every cell canonical (`IsCanonical128`), as a `KECCAK` requires of the cells it reads. -/
def AllCanonical (cs : List E) : Prop := ∀ c ∈ cs, IsCanonical128 c

/-! ## The carried sponge -/

/-- The guest's sponge: the five capacity cells it carries, and the scalars waiting with their
tags. -/
structure Fs where
  /-- The capacity cells. -/
  cap : List E
  /-- The waiting scalars and their tags. -/
  pend : List (E × ℕ)

namespace Fs

/-- The state the next permutation writes: the waiting scalars over the rate, the capacity
kept. -/
def perm (s : Fs) : KeccakState := permOf (rateOf s.pend ++ s.cap)

/-- Absorb a scalar with a tag: a full queue is permuted first (`absorb`). -/
def absorb (s : Fs) (x : E) (t : ℕ) : Fs :=
  if s.pend.length = rateScalars then ⟨capOf s.perm, [(x, t)]⟩ else ⟨s.cap, s.pend ++ [(x, t)]⟩

/-- Absorb scalars in order, each with the tag `t`. -/
def absorbAll (s : Fs) (xs : List E) (t : ℕ) : Fs := xs.foldl (fun s x ↦ s.absorb x t) s

/-- Squeeze a challenge: a permutation, its state's challenge (`squeeze`, `challengeOf`). -/
def squeeze (s : Fs) : E × Fs := (challengeOf s.perm, ⟨capOf s.perm, []⟩)

/-- `n` challenges in order, and the sponge after them. -/
def squeezeN : ℕ → Fs → List E × Fs
  | 0, s => ([], s)
  | n + 1, s => ((s.squeeze.1 :: (squeezeN n s.squeeze.2).1), (squeezeN n s.squeeze.2).2)

/-- The cells a `KECCAK` can read: five canonical capacity cells, at most four waiting. -/
def Ok (s : Fs) : Prop := s.cap.length = 5 ∧ AllCanonical s.cap ∧ s.pend.length ≤ rateScalars

/-- The Spec's sponge `sp` is the one the guest carries as `s`. -/
def Carries (s : Fs) (sp : Sponge) : Prop := capOf sp.state = s.cap ∧ sp.pending = s.pend

end Fs

/-! ## Runs of the Spec's programs -/

/-- The deployed reading of a Spec program: `Compile.run` at Keccak-256 and Keccak-f. -/
abbrev runId {α : Type} (p : VerifierProgram α) (st : VerifierProgramState) : Option (α ×
    VerifierProgramState) :=
  Compile.runWithHash (m := Id) keccak256 keccakF1600 p st

/-- From any Spec sponge the guest carries as `s`, the program `p` reads exactly the stream words
`xs` and returns `a`, leaving a sponge the guest carries as `s'`, on any rest of the stream, any
openings and any roots. -/
def RunsTo {α : Type} (p : VerifierProgram α) (s : Fs) (xs : List E) (a : α) (s' : Fs) : Prop :=
  ∀ sp : Sponge, s.Carries sp → ∀ (rest : List E) (os : List (List Opening))
    (roots : List (Digest × ℕ × ℕ)), ∃ sp' : Sponge, s'.Carries sp' ∧
      runId p ⟨sp, xs ++ rest, os, roots⟩ = some (a, ⟨sp', rest, os, roots⟩)

end
end LeanVM.Guest.B1
