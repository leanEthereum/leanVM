module

public import LeanDa.Field
public import Mathlib.LinearAlgebra.Lagrange
public import Statement.LeanDa
public import LeanDa.WithHash

/-!
# LeanDA

The erasure code commitment of `crates/lean_da`,
specified in `doc/leanvm/body/10-ethereum.tex`
§sec:leanda, for a matrix of `r` rows.

* **The code** (`encode.rs`). A row's payload is `2^13` symbols of `E`, the evaluations on the
  domain points `0 … 2^13 - 1` (in `K`) of the polynomial of `E[X]` of degree below `2^13` they
  determine. Its codeword is that polynomial's evaluations on all `2^14` points (`encodeRow`): the
  inverse additive NTT interpolates, the forward one evaluates, each on both limbs, so the payload
  is the codeword's first half. The transforms compute these maps (Annex D, Proposition
  prop:ntt); they are not transcribed here.
* **Cells** (`lib.rs`). A codeword is `128` cells of `128` symbols, cell `j` its symbols
  `128 j … 128 j + 127`. A matrix of `r` codewords has `128 r` cells, cell `j` of row `i` at
  position `128 i + j`: the positions of the erasure code commitment are the cells sampling
  opens.
* **The commitment** (`commit.rs`). The rows are padded to `2^⌈log₂ r⌉` with zero
  codewords. A cell's digest is the hash of its symbols' little-endian bytes. Each padded row, a
  blob, has the Merkle root of its `128` cell digests (`blob_merkle_nodes`), and the commitment is the
  Merkle root of the padded rows' blob roots (`DaWitness::build`); a padding row's blob root is
  the zero codeword's (`root_of_padding_blob`). A tree hashes neighbours in pairs, level by level
  (`fill_levels`).
* **Openings.** A cell is opened by its path in its blob's tree, then its blob root's in the tree
  over the blob roots: the path of leaf `128 i + j` in the one tree of depth `7 + ⌈log₂ r⌉` the
  two make. The crate keeps the codewords and the root (`DaWitness`, `commit.rs`) but
  builds and verifies no path.
* **Membership** (`verifier/src/da.rs`, the guest program's `da_vector`). One challenge `z ∈ E` gives
  the dual codeword `L(x) = ∏_j (1 + z^(2^j) Ŵ_j(x))` on the domain (Annex D, eq. dual-product,
  at the challenges `z^(2^j)`), with `Ŵ_j` the normalized subspace polynomial of the span of
  `e_0 … e_(j-1)`. A matrix passes when every row is orthogonal to `L` (the guest program's
  `da_verify`). The challenge is drawn
  from the root by leanVM's transcript (`membership_challenge`, `verifier/src/da.rs`), its
  sponge over Keccak-f[1600] seeded with the label's hash and the root, squeezed once; the
  security game models it as one random oracle on the root.
* **The deployed algorithms** (`commit.rs`, `subspace_above` in `rec_aggregation`'s `placeholders.rs`,
  `verifier/src/da.rs`, `verifier/src/transcript.rs`). The crate's computations,
  transcribed computably on lists, for `lean_vm` to state the aggregation node's DA claim with:
  `commitCodewords`, the tree of blob trees level by level, which is `commitCells` of the matrix
  (`commitCodewords_eq_commitCells`, `LeanDa.Commitment`); the challenge's sponge (`Sponge`,
  `membershipChallenge`); the table of the normalized subspace polynomials at the basis
  (`subspaceEvaluations`, the NTT's `generate_evals_from_subspace`) and its subset sums
  (`subspaceAbove`, `subspace_above`), from which the guest builds `L` (`dualCodeword`, the
  crate's test `dual_codeword`), which `LeanDa.Subspace` proves are `Ŵ_j` and `dualCodewordAt`.

The row count `r` is a parameter. The crate takes `1 ≤ r ≤ maxRows` (`DaWitness::build` rejects any other
count with a `BlobCountError`, `commit.rs`, `lib.rs`);
the statements hold for every `r ≥ 1`. So are the hash `H` and the sponge's permutation `P`: the
crate's are Keccak-256 (Ethereum's: rate `136` bytes, padding `0x01 ‖ 0^* ‖ 0x80`,
`verifier/src/hash.rs`) and the Keccak-f[1600] it is built on, which `lean_vm` supplies,
and the statements hold for every `H` and `P`.

Part of `lean_da`, which instantiates Benedikt Wagner's framework for erasure code commitments
(`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

open Polynomial

namespace LeanDa

@[expose] public section

/-! ## Membership (`verifier/src/da.rs`, the guest program's `da_vector`) -/

/-- The tensor `⊗_j (1, z_j)`: coefficient `u` is the product of the `z_j` over the bits of `u`;
at `z_j = z^(2^j)` it is `z^u`. -/
def tensor (z : Fin 13 → E) (u : Fin (2 ^ 13)) : E :=
  ∏ j : Fin 13, if (u : ℕ).testBit j then z j else 1

/-! ## The challenge (`verifier/src/da.rs`)

Drawn from the root by the duplex sponge the security game models as a random oracle, over a
hash `H` and a permutation `P` of `25` lanes. The crate's are Keccak-256 and Keccak-f[1600]
(`keccak_f`, `verifier/src/hash.rs`), which `lean_vm` supplies; the definitions hold for
every `H` and `P`. A lane is a `u64`, read as the element of `K` with its bits, so a scalar's limbs
are lanes as they are. The rate is lanes `0 … 15`, the capacity lanes `16 … 24`. -/

variable (H : List UInt8 → Common.DigestBytes)
  (P : LeanVM.Semantics.KeccakState → LeanVM.Semantics.KeccakState)

/-- **The challenge of a root** with a pure hash and permutation (`membership_challenge`). -/
def membershipChallenge (root : Common.DigestBytes) : Option E :=
  Id.run (membershipChallengeMWithHash (fun a ↦ pure (H a)) (fun L ↦ pure (P L)) root)

/-! ## The dual codeword as the guest builds it (`subspace_above` in `rec_aggregation`'s `placeholders.rs`) -/

/-- Row `i` of the subspace evaluations before scaling: `s_i` at the basis elements `x^j`,
`j ≥ i` (`generate_evals_from_subspace`, `pcs/src/ntt/twiddles.rs`). -/
def subspaceRow : ℕ → List K
  | 0 => (List.range logM).map fun j ↦ K.ofBits (2 ^ j)
  | i + 1 =>
    let previous := subspaceRow i
    (previous.drop 1).map fun value ↦ value * (value + previous.headD 0)

/-- Row `i` of the subspace evaluations, scaled so that its first entry is one: `Ŵ_i` at
`e_i … e_13` (`generate_evals_from_subspace`; `LeanDa.Subspace`'s `subspaceEvaluations_eq`). -/
def subspaceEvaluations (i : ℕ) : List K :=
  (subspaceRow i).map (· * ((subspaceRow i).headD 0)⁻¹)

/-- **`Ŵ_j` at the point whose bits above `j` are `y`'s**, `Σ_l bit_l(y) · Ŵ_j(e_(j+1+l))`
(`subspace_above` in `rec_aggregation`'s `placeholders.rs`: the NTT's twiddle of block `y` at layer `13 - j`, a
subset sum of row `j`, `twiddle`, `pcs/src/ntt/twiddles.rs`). For `y < 2^(13 - j)` it is
`Ŵ_j(point (y · 2^(j+1)))` (`LeanDa.Subspace`'s `subspaceAbove_eq`). -/
def subspaceAbove (j y : ℕ) : K :=
  ((List.range (logK - j)).filter y.testBit).foldl
    (fun t l ↦ t + ((subspaceEvaluations j).drop 1).getD l 0) 0

/-- `Ŵ_j` at point `i` from the table: bit `j` of `i`, plus `subspaceAbove` at its bits above `j`
(the guest program's `da_vector`). -/
def subspaceAt (j i : ℕ) : K :=
  (if i.testBit j then 1 else 0) + subspaceAbove j (i >>> (j + 1))

/-- **The dual codeword of `z` as the guest builds it** (the guest program's
`da_vector`): at each of the `2^14` points `i`, `∏_j (1 + z^(2^j) Ŵ_j(i))`.
It is `dualCodewordAt z` (`LeanDa.Subspace`'s
`dualCodeword_eq_dualCodewordAt`). -/
def dualCodeword (z : E) : List E :=
  let powers := (List.range logK).map fun j ↦ z ^ 2 ^ j
  (List.range (2 ^ logM)).map fun i ↦
    (List.range logK).foldl
      (fun product j ↦ product * (1 + powers.getD j 0 * CompPoly.Extension.Ext.ofBase (subspaceAt j i)))
      1

end

end LeanDa
