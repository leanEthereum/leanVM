/-
  LeanVM.Guest.Value.Keccak

  The Keccak library of the guest's proof: what chains of `KECCAK` atoms compute.
-/

module

public import LeanVM.Guest.Value.KeccakConst
public import LeanVM.Guest.Value.KeccakDuplex
public import LeanVM.Guest.Value.KeccakSponge
public import LeanVM.Guest.Batch.Def

/-!
# The Keccak library

The core IR keeps one `Atom.keccak ins outs inOdd outOdd` per `KECCAK` instruction, its meaning,
with thirteen written cells, `KeccakCellsRelation (cells13 (ins.map σ)) inOdd (cells13 (outs.map σ))
outOdd .all` (`keccak_holds_13`; a one- or two-cell write is its first cells, `keccak_holds_full`); the padding `XOR`s and
the zero/padding run are ordinary atoms. What a call of `keccak` or `keccak_cells` computes is
recovered here, on the words `I = cells13 (ins.map σ)`, `O = cells13 (outs.map σ)` of the atoms,
generic in their cells. Namespace `LeanVM.Guest.Value.Keccak` (`KeccakEval` for the evaluator).

## API

**Bytes and layouts** (`KeccakLayout`)
* `cellBytes c`, `cellsBytes cs`: a cell's sixteen bytes, limb `0` then limb `1`, little-endian.
* `leLane_cellsBytes : littleEndianLane (cellsBytes cs) l = ((cs.getD (l / 2) 0).limb ⟨l % 2, _⟩).lane`.
* `laneCell odd l`, `laneLimb odd l`, `lane_stateOfCells`, `limb_cellsOfState`: where lane `l`
  sits; `stateOfCells_cellsOfState : stateOfCells (cellsOfState S odd) odd = S`;
  `cellsOfState_zero : cellsOfState zeroState odd c = 0`.
* `keccak_block` (one block XORed into a state):
  `(∀ c, I c = cellsOfState S inOdd c + if c.val < 9 then blk.getD c 0 else 0) →
   KeccakCells I inOdd O outOdd → O = cellsOfState (absorbBlock S (blockBytes inOdd blk)) outOdd`.

**The sponge** (`KeccakSponge`; `B = len / 136 + 1` blocks, `rate = 136`)
* `absorbChunks n S bytes`, `padBytes data`, `padCells cells len` (`xor_byte` of `0x01` at
  `len` and `0x80` at `136 B - 1`, cells zero-extended to `padRead len = 17 (B - 1) / 2 + 9`),
  `inLayout k = (k % 2 == 1)`, `outLayout B k = (k + 1 != B && k % 2 == 0)`.
* `keccak_chain`: `O 0 = cellsOfState S0 false →
   (∀ k < B, ∀ c : Fin 13, c.val < 9 → I k c = O k c + P.getD (17 * k / 2 + c) 0) →
   (∀ k < B, ∀ c : Fin 13, 9 ≤ c.val → I k c = O k c) →
   (∀ k < B, KeccakCells (I k) (inLayout k) (O (k + 1)) (outLayout B k)) →
   O B = cellsOfState (absorbChunks B S0 (cellsBytes P)) false`.
* `keccak_final_digest` (default `final`, after a prefix `pre` of `n` whole blocks absorbed into
  `O 0`; `pre = []`, `n = 0` from the zero state): with `pre.length = rate * n`,
  `len ≤ 16 * cells.length`, `∀ j, len ≤ j → (cellsBytes cells).getD j 0 = 0`,
  `O 0 = cellsOfState (absorbChunks n zeroState pre) false` and the three hypotheses of
  `keccak_chain` for `P = padCells cells len`:
  `(O B 0, O B 1) = digestHalves (keccak256 (pre ++ (cellsBytes cells).take len))`;
  `keccak_final` gives the whole output, `cellsOfState (absorbChunks (n + B) zeroState
  (pre ++ padBytes ((cellsBytes cells).take len))) false`.
* `keccak_one` (one `KECCAK` from the zero state, `len < 136`):
  `I c = (padCells cells len).getD c 0` for `c < 9`, `I c = 0` for `c ≥ 9`,
  `KeccakCellsRelation I false O false .all` give
  `O = cellsOfState (absorbChunks 1 zeroState (padBytes msg)) false ∧
   (O 0, O 1) = digestScalars (keccak256 msg)`, `msg = (cellsBytes cells).take len`.
* `keccak_whole` (`final=0` over whole blocks, `16 * cells.length = rate * B`): the state after
  `pre ++ cellsBytes cells`, `absorbChunks (n + B) zeroState (pre ++ cellsBytes cells)`, ready for
  a `state=` continuation (`keccak_final` with that prefix).
* `absorbChunks_seed : absorbChunks 1 zeroState (cellsBytes [(digestScalars iv).1,
   (digestScalars iv).2, (digestScalars pi).1, (digestScalars pi).2]) = keccakF (seedInput iv pi)`
  (`verify_sub`'s `keccak_cells(…, final=0)`, with `keccak_chain`).
* `keccak256_eq_absorbChunks`, `keccak256_append`, `absorbChunks_append`, `padCells_bytes`,
  `digestScalars_digestOf : digestScalars (digestOf S) = (cellsOfState S false 0,
  cellsOfState S false 1)`.

**The duplex** (`KeccakDuplex`)
* `rateCell pending c`, `scalarCells x t = (E.ofLimbs (x.limb 0) (x.limb 1) 0,
  E.ofLimbs (x.limb 2) (K.ofLane t.toUInt64) 0)`, `rateCell_scalar`, `rateCell_past`.
* `keccak_duplex`: `(∀ c : Fin 13, c.val < 8 → I c = rateCell pending c) →
   (∀ c : Fin 13, 8 ≤ c.val → I c = cellsOfState S false c) → KeccakCells I false O false →
   O = cellsOfState (keccakF (duplexInput ⟨S, pending⟩)) false`.
* `duplex_id`, `squeeze_id`, `absorb_id_lt`, `absorb_id_full`: the Spec's sponge at `Id`, `keccakF`.
* `challengeOf_cells : challengeOf S =
   cellsOfState S false 0 + y * y * ofK ((cellsOfState S false 1).limb 0)`, `challengeOf_limb0`;
  `fsPack_cells` (`fs_pack`'s two cells, canonical exactly at the top limb).

**Constants by kernel evaluation** (`KeccakConst`, `KeccakEval`)
* `keccakF_zero : keccakF zeroState = keccakFZero` (the `KECCAK` table's padding row).
* `batchSeed_eq : Node.batchSeed = batchSeedValue`;
  `aggSeed_cells : litField (aggSeed.getD c 0) = cellsOfState Node.batchSeed false ⟨8 + c, _⟩`.
* `paddingCell_eq : LeanDa.paddingCellWithHash Da.keccak256Bytes = LeanVM.Protocol.Digest.toBytes daPadCellDigest`,
  `paddingBlobRoot_eq` (the zero codeword's blob root, seven levels of `daPadLevel`),
  `daPadBlob_cells` (`DA_PAD_BLOB_0/1 = digestHalves daPadBlobDigest`).
* For new constants: `keccakF_eq_iff : keccakF a = b ↔ keccakFN (toNats a) = toNats b` and
  `keccak256_eq_iff : keccak256 data = d ↔ keccak256N (data.map UInt8.toNat) =
  d.toList.map UInt64.toNat`, then `decide +kernel` (milliseconds a permutation; avoid
  `Vector.ofFn` and `String.toUTF8` in the closed term: their bodies are not exposed to a
  `module`'s kernel, rewrite them first as `seedInput_eq` and `batchLabel_eq` do).
-/
