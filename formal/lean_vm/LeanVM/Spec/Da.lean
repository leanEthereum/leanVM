/-
  LeanVM.Spec.Da

  What an aggregate's DA claim on a root says, in terms of LeanDA as `formal/lean_da` defines it.
-/

module

public import LeanDa.Scheme
public import LeanVM.Spec.Fast.Da
public import LeanVM.Spec.Fast.Hash

/-!
# The DA claim

LeanDA, the commitment to a blob matrix and the Reed-Solomon membership vector its root
determines, is `formal/lean_da`'s, imported from its `Scheme` module: the security of the scheme
is proved there, and its deployed algorithms (`LeanDa.commitCodewords`,
`LeanDa.membershipVector`, `LeanDa.vectorDigest`) are transcribed there, generic in the hash. Here
the hash is this project's BLAKE2s-256 (`blake2s`), its digest read as LeanDA's 32 bytes
(`toBytes`), and `Fast.Da` compiles the membership vector with this project's field arithmetic.

An aggregate's DA claim is a pair of a root and a vector digest; it is held by a matrix committed
to the root whose rows are orthogonal to a vector of that digest (`Witness.Opens`,
`lean_ethereum.py:3159-3353` at `a0ca7858`). The guest takes the vector digest from the
statement; the outer verifier derives it from the root (`vectorDigestOf`), so that the rows are
codewords given that BLAKE2s, here and in the statement's digests, has no collision. The prover's
copy of the membership vector (`lean_da/src/{encode,membership}.rs`) is not transcribed; that it
agrees with `verifier/src/da.rs` is an implementation fact, which honest aggregates rely on.
-/

namespace LeanVM.Da

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

/-- A digest as LeanDA's 32 bytes: its words, little-endian (`state_bytes`). -/
def toBytes (d : Digest) : LeanDa.Digest :=
  ⟨(digestBytes d).toArray, by simp [digestBytes, wordBytes]⟩

/-- BLAKE2s-256 as LeanDA's hash. -/
def blake2s (input : List UInt8) : LeanDa.Digest := toBytes (blake2sBytes input)

/-- **The vector digest of a root**, as the outer verifier derives it
(`vector_digest(membership_vector(root))`, `verifier/src/da.rs:91-101`). -/
def vectorDigestOf (root : Digest) : LeanDa.Digest :=
  LeanDa.vectorDigest blake2s (LeanDa.membershipVector blake2s (toBytes root))

/-- What holds a DA claim: a matrix of codewords and the vector its rows are orthogonal to. -/
structure Witness where
  /-- The codewords. -/
  rows : List (List K)
  /-- The vector. -/
  vector : List E

/-- **The witness holds the DA claim `(root, vd)`** (`da_verify`): `1` to `1024` codewords of
`2^15` symbols commit to `root`, and every one is orthogonal to the vector, whose digest is
`vd`. -/
def Witness.Opens (root vd : Digest) (w : Witness) : Prop :=
  1 ≤ w.rows.length ∧ w.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ w.rows, row.length = 2 ^ LeanDa.logM) ∧
    LeanDa.commitCodewords blake2s w.rows = toBytes root ∧ w.vector.length = 2 ^ LeanDa.logM ∧
    LeanDa.vectorDigest blake2s w.vector = toBytes vd ∧
    ∀ row ∈ w.rows, LeanDa.dot (fun b ↦ w.vector.getD b 0) (fun b ↦ row.getD b 0) = 0

end
end LeanVM.Da
