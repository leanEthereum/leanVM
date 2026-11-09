/-
  LeanVM.Guest.Value.KeccakConst

  The guest's baked constants that are Keccak-f[1600] or Keccak-256 of fixed inputs, checked by
  kernel evaluation.
-/

module

public import LeanVM.Guest.Value.KeccakSponge
public import Statement.LeanVmGuest
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Guest.Batch.Def
public import LeanDa.WithHash
public import LeanDa.Commitment
public import LeanVM.Guest.WithHash

/-!
# Baked Keccak constants

The host bakes into the guest (`placeholder_map`,
`crates/rec_aggregation/src/aggregation/placeholders.rs` at leanVM main `40f877dc`)
constants that are permutations or hashes of fixed inputs. Each is an equation between closed
terms, checked here by `decide +kernel` through the evaluator of `KeccakEval` (`keccakF_eq_iff`,
`keccak256_eq_iff`): no compiled code is trusted.

* `keccakF_zero`: Keccak-f[1600] of the zero state, the `KECCAK` table's padding row
  (`Table.padding`, the guest's `COORD_PADDING`);
* `batchSeed_eq`, `aggSeed_cells`: the batching transcript's initial state, whose five capacity
  cells are `AGG_SEED_0 .. AGG_SEED_4` (`FiatShamirState::from_label(RECURSION_AGG_LABEL)
  .capacity_cells()`, `aggregation/placeholders.rs:823-826`);
* `paddingCell_eq`, `paddingBlobRoot_eq`, `daPadBlob_cells`: LeanDA's padding blob root, the root
  of the tree over `128` copies of the zero cell's digest (`padding_root`, `padding_tree`,
  `crates/lean_da/src/commit.rs:70-78`), whose two cells are `DA_PAD_BLOB_0/1` (`hash_to_scalars`,
  `aggregation/placeholders.rs:841-847`).

Kernel cost (measured on the build machine): each permutation of the evaluator is milliseconds;
Keccak-256 of the 2048-byte zero cell (16 permutations) about 6 s and 2 GB over the imports.
-/

namespace LeanVM.Guest.Value.Keccak

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.Value.KeccakEval

@[expose] public section

/-! ## Keccak-f of the zero state -/

/-- Keccak-f[1600] of the zero state. -/
def keccakFZero : KeccakState :=
  #v[17376452488221285863, 9571781953733019530, 15391093639620504046, 13624874521033984333,
    10027350355371872343, 18417369716475457492, 10448040663659726788, 10113917136857017974,
    12479658147685402012, 3500241080921619556, 16959053435453822517, 12224711289652453635,
    9342009439668884831, 4879704952849025062, 140226327413610143, 424854978622500449,
    7259519967065370866, 7004910057750291985, 13293599522548616907, 10105770293752443592,
    10668034807192757780, 1747952066141424100, 1654286879329379778, 8500057116360352059,
    16929593379567477321]

/-- **Keccak-f[1600] of the zero state**, the `KECCAK` table's padding row's output. -/
theorem keccakF_zero : keccakF1600 zeroState = keccakFZero := by
  rw [keccakF_eq_iff]; decide +kernel

/-! ## The batching seed (`AGG_SEED_*`) -/

/-- Keccak-256 of the batching label. -/
def batchLabelDigest : Digest :=
  #v[3225554803577962359, 10440387594429029835, 3141269080130101615, 2858618447650156248]

/-- The batching label's bytes. -/
theorem batchLabel_eq : Node.batchingLabel = [108, 101, 97, 110, 118, 109, 47, 114, 101, 99, 117, 114,
    115, 105, 111, 110, 45, 97, 103, 103, 114, 101, 103, 97, 116, 105, 111, 110, 47, 118, 49] := by
  rw [Node.batchingLabel, show "leanvm/recursion-aggregation/v1" = String.ofList ['l', 'e', 'a', 'n',
      'v', 'm', '/', 'r', 'e', 'c', 'u', 'r', 's', 'i', 'o', 'n', '-', 'a', 'g', 'g', 'r', 'e', 'g',
      'a', 't', 'i', 'o', 'n', '/', 'v', '1'] from rfl,
    String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  decide +kernel

theorem keccak256_batchLabel : keccak256 Node.batchingLabel = batchLabelDigest := by
  rw [batchLabel_eq, keccak256_eq_iff]; decide +kernel

/-- The seed input of two digests, lane by lane. -/
theorem seedInput_eq (iv pi : Digest) :
    Compile.seedInput iv pi = #v[iv[0], iv[1], iv[2], iv[3], pi[0], pi[1], pi[2], pi[3],
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> simp [Compile.seedInput]

/-- The batching transcript's initial state. -/
def batchSeedValue : KeccakState :=
  #v[9731470080330201434, 13021276346064953969, 17641262088094796327, 15385747579934674281,
    16767942838229146784, 1929300249522848364, 2670637271811230429, 15973221218815429819,
    3410770349630169017, 12695776346224436678, 784848704834098333, 12002339076772184942,
    14464553134880188447, 12612206758652206804, 18205192014848753121, 1589440240854800282,
    1562680967124014521, 7666384441264927334, 11925545048015809408, 14528471851986820829,
    15194020773630548750, 6704907289165917069, 10885225211858021658, 10587785389206534793,
    159208925504336485]

/-- **The batching seed's value.** -/
theorem batchSeed_eq : Node.batchSeed = batchSeedValue := by
  rw [Node.batchSeed, keccak256_batchLabel, seedInput_eq, keccakF_eq_iff]; decide +kernel

/-- `AGG_SEED_0 .. AGG_SEED_4` as the host bakes them (`dsl_u128` of the capacity cells). -/
def aggSeed : List ℕ :=
  [1562680967124014521, 219987477440241922375488438384259330662,
    280280212661789141853795656654516100829, 200796963667835759483519841953162816397,
    2936886303028784551432414362146044553]

/-- **`AGG_SEED_c` is cell `8 + c` of the batching seed** (even layout): the guest's
`seed = [AGG_SEED_0, …, AGG_SEED_4]` (`aggregate_claims`, `lean_ethereum.py:4686`) is the
capacity a `cap=seed` duplex step reads. -/
theorem aggSeed_cells (c : Fin 5) :
    LeanVM.Guest.litField (aggSeed.getD c 0) =
      cellsOfState Node.batchSeed false ⟨8 + c, by omega⟩ := by
  rw [batchSeed_eq]
  apply E.ext
  intro i
  fin_cases c <;> fin_cases i <;> rfl

/-! ## LeanDA's padding blob root (`DA_PAD_BLOB_*`) -/

/-- The digest of the zero cell. -/
def daPadCellDigest : Digest :=
  #v[15569472805043175342, 18354418831448413762, 11782766640862828499, 15718207409690975807]

/-- **LeanDA's padding cell digest.** -/
theorem paddingCell_eq : LeanDa.paddingCellWithHash Da.keccak256Bytes = LeanVM.Protocol.Digest.toBytes daPadCellDigest := by
  rw [LeanDa.paddingCellWithHash, Da.keccak256Bytes]
  refine congrArg LeanVM.Protocol.Digest.toBytes ?_
  rw [keccak256_eq_iff]; decide +kernel

/-- The zero codeword's blob root, level `7` of its tree. -/
def daPadBlobDigest : Digest :=
  #v[8002054802297438051, 4108169256045952147, 12830724869163462953, 1721925254677230945]

/-- Level `k` of the zero codeword's blob tree, `k < 7`: every node is the digest of two copies
of the level below; level `0` is the zero cell's digest. -/
def daPadLevel : ℕ → Digest
  | 0 => #v[15569472805043175342, 18354418831448413762, 11782766640862828499, 15718207409690975807]
  | 1 => #v[14369258901718716213, 1148698013832551171, 11114768001093208614, 4024475884843678426]
  | 2 => #v[16384331582733952155, 4872841518684838795, 4963418389712070825, 5657312520029772919]
  | 3 => #v[4325506311329920960, 3990153883492882141, 15991342632079755805, 15556484451381276208]
  | 4 => #v[14516598363330464605, 6536086711024295040, 16323196108830172471, 1631986071079656599]
  | 5 => #v[16566772253878538657, 13661756115384085219, 18376426559722138097, 7791538171676559580]
  | 6 => #v[2520529203033256297, 13966105018950953778, 17342732538992512079, 14513495305663590460]
  | _ => daPadBlobDigest

/-- One level up the zero codeword's blob tree. -/
theorem daPadLevel_succ : ∀ k < 7, keccak256 (digestBytes (daPadLevel k) ++ digestBytes (daPadLevel k)) =
    daPadLevel (k + 1) := by
  intro k hk
  interval_cases k <;> (rw [keccak256_eq_iff]; decide +kernel)

/-- The root of a tree over `2^k` copies of one leaf. -/
theorem merkleRoot_const (H : List UInt8 → Common.DigestBytes) (d : Common.DigestBytes) :
    ∀ k, LeanDa.merkleRootWithHash H (k + 1) (fun _ ↦ d) =
      LeanDa.merkleRootWithHash H k (fun _ ↦ H (LeanDa.pairBytes d d)) := fun _ ↦ rfl

theorem daPadLevel_toBytes_succ {k : ℕ} (hk : k < 7) :
    Da.keccak256Bytes (LeanDa.pairBytes (daPadLevel k).toBytes (daPadLevel k).toBytes) =
      (daPadLevel (k + 1)).toBytes := by
  rw [Da.keccak256Bytes, ← daPadLevel_succ k hk]
  rfl

/-- **LeanDA's padding blob root** (`padding_root`, `commit.rs:70-78`): the zero codeword's blob
root is `daPadBlobDigest`. -/
theorem paddingBlobRoot_eq :
    LeanDa.paddingBlobRootWithHash Da.keccak256Bytes = LeanVM.Protocol.Digest.toBytes daPadBlobDigest := by
  have hrep : List.replicate LeanDa.cellsPerRow (LeanDa.paddingCellWithHash Da.keccak256Bytes) =
      (List.range (2 ^ 7)).map fun _ ↦ (daPadLevel 0).toBytes := by
    rw [paddingCell_eq, List.map_const', List.length_range]; rfl
  rw [LeanDa.paddingBlobRootWithHash, hrep, LeanDa.treeRoot_map_range]
  rw [merkleRoot_const, daPadLevel_toBytes_succ (by norm_num), merkleRoot_const,
    daPadLevel_toBytes_succ (by norm_num), merkleRoot_const, daPadLevel_toBytes_succ (by norm_num),
    merkleRoot_const, daPadLevel_toBytes_succ (by norm_num), merkleRoot_const,
    daPadLevel_toBytes_succ (by norm_num), merkleRoot_const, daPadLevel_toBytes_succ (by norm_num),
    merkleRoot_const, daPadLevel_toBytes_succ (by norm_num)]
  rfl

/-- **`DA_PAD_BLOB_0`, `DA_PAD_BLOB_1`** (`aggregation/placeholders.rs:845-847`, `lean_ethereum.py:4360-4361`)
are the padding blob root's two cells. -/
theorem daPadBlob_cells :
    (LeanVM.Guest.word 8002054802297438051 4108169256045952147 0,
      LeanVM.Guest.word 12830724869163462953 1721925254677230945 0) =
      digestHalves daPadBlobDigest := by
  simp only [digestHalves, daPadBlobDigest, LeanVM.Guest.word]; rfl

end
end LeanVM.Guest.Value.Keccak
