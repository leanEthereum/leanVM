module
public import WhirAeneas.Generated.Replay.Types
public import WhirAeneas.Std.Bulk
public import WhirAeneas.Std.Guards
public import WhirAeneas.Std.Merkle
public import WhirAeneas.Std.Native
public import WhirAeneas.Std.Replay
public import Mathlib.Data.Finset.Sort
@[expose] public section
open Aeneas Aeneas.Std Result

namespace ReplaySource

/-- `pcs::merkle::sorted_unique`: the queries with duplicates removed, ascending. Its body
    (`to_vec`, `sort_unstable`, `dedup`) is outside the backend's library; on `usize` an unstable
    sort followed by removing adjacent duplicates is the ascending list of the distinct values. -/
def merkle.sorted_unique (queries : Slice Std.Usize) : Result (alloc.vec.Vec Std.Usize) :=
  let l : List Std.Usize := ((queries.val.map (·.val)).toFinset.sort (· ≤ ·)).map
    fun n => ⟨BitVec.ofNat UScalarTy.Usize.numBits n⟩
  .ok (.from l (by
    have h1 : l.length ≤ queries.val.length := by
      simp only [l, List.length_map, Finset.length_sort]
      exact (List.toFinset_card_le _).trans (by simp)
    have := queries.property
    omega))

/-- `pcs::merkle::hash_pairs`, the batched pair hash: the hash boundary, with no body here. Its
    content contract is `WhirAeneas.Merkle.PairHash`. -/
opaque merkle.hash_pairs :
    Slice (Array (Array Std.U8 32#usize) 2#usize) → alloc.vec.Vec (Array Std.U8 32#usize) →
      Result (alloc.vec.Vec (Array Std.U8 32#usize))

/-- `pcs::merkle::hash_rows`, the batched leaf hash: the hash boundary, with no body here. Its
    content contract is `WhirAeneas.Merkle.RowHash`. -/
opaque merkle.hash_rows :
    Slice primitives.field.gf2_64.F64 → Std.Usize → Std.Usize → Std.Usize →
      Result (alloc.vec.Vec (Array Std.U8 32#usize))

/-- `primitives::hash::hash`, one BLAKE2s-256 hash: the hash boundary (x86 assembly), with no
    body here. The proof-of-work trial hashes one 64-byte block with it; its content contract is
    `WhirAeneas.NativeReads.PowHash`. -/
opaque primitives.hash.hash : Slice Std.U8 → Result (Array Std.U8 32#usize)

/-- The BLAKE2s duplex sponge's methods: the transcript sponge, with no body here. Its content
    contract is `WhirAeneas.NativeReads.Duplex`: an absorb extends the logical transcript by its
    bytes, a squeeze returns the duplex's output for the transcript so far. `context` copies the
    logical state for recursion records and no verifier read uses it. -/
opaque fiat_shamir.duplex.Blake2sDuplex.absorb :
    fiat_shamir.duplex.Blake2sDuplex → Slice Std.U8 → Result fiat_shamir.duplex.Blake2sDuplex

opaque fiat_shamir.duplex.Blake2sDuplex.squeeze :
    fiat_shamir.duplex.Blake2sDuplex → Slice Std.U8 →
      Result (fiat_shamir.duplex.Blake2sDuplex × Slice Std.U8)

opaque fiat_shamir.duplex.Blake2sDuplex.context :
    fiat_shamir.duplex.Blake2sDuplex →
      Result (fiat_shamir.TranscriptContext primitives.field.gf2_64.F64 (Array Std.U8 32#usize))

/-- `Encoding::encode` for the transmitted types: the prover's direction, with no body here. The
    verifier reads absorb the proof's own bytes and never encode, so no statement uses them;
    `FromNarg` only carries `Encoding` as its supertrait. -/
opaque U64.Insts.Fiat_shamirCodecEncodingArrayU88.encode : Std.U64 → Result (Array Std.U8 8#usize)

opaque primitives.field.gf2_64x3.F192.Insts.Fiat_shamirCodecEncodingArrayU824.encode :
    primitives.field.gf2_64x3.F192 → Result (Array Std.U8 24#usize)

opaque ArrayU8N.Insts.Fiat_shamirCodecEncodingArrayU8N.encode {N : Std.Usize} :
    Array Std.U8 N → Result (Array Std.U8 N)

end ReplaySource
