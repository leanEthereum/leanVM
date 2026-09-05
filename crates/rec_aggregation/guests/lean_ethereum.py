# The recursive aggregation guest: zkDSL, not runnable Python (see
# crates/lean_compiler/zkDSL.md). One node of an aggregation tree verifies raw XMSS
# and SPHINCS+ signatures and sub-proofs OF THIS SAME BYTECODE, and publishes the
# statement digest binding the signer set it covers. Reading order: `main` is the
# node, `verify_sub` the in-circuit copy of `lean_vm::cpu::verify`, and
# `open_stacked` the WHIR opening it dispatches into.
#
# Every `*_PLACEHOLDER` below is filled by the host at compile time
# (rec_aggregation::aggregation::placeholder_map), so one source serves every inner
# shape. Names follow doc/leanvm/preamble/macros.tex.
from snark_lib import *

# ---------------------------------------------------------------- proof stream
# The proof stream rides ONE padded witness hint (the guest walks only the prefix
# the shape dictates); binding always comes from the per-word absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
MIN_LOG_MEM = MIN_LOG_MEM_PLACEHOLDER
INV_GEN = INV_GEN_PLACEHOLDER

# ------------------------------------------------------------- the field, GF(2^192)
# Tower F192 = F64[Y]/(Y^3+Y+1). Y_TOWER embeds Y for reassembling
# e192(lo,hi,top) = lo + hi*Y + top*Y², and Y_INV also deduces a top limb at the
# opening boundary once the low and high limbs are transmitted. COORD_BASIS is the
# coordinate basis e_i of F192 (which spans the WHOLE field, unlike the g-power
# basis GEN**i, which spans only F64): hint_decompose_bits emits a word's
# coordinate bits, so a value reconstructs as Σ b_i·COORD_BASIS[i].
FIELD_BITS = 192
BASE_FIELD_BITS = 64
Y_TOWER = Y_TOWER_PLACEHOLDER
Y_INV = Y_INV_PLACEHOLDER
COORD_BASIS = COORD_BASIS_PLACEHOLDER
# Six challenges compose the F2-linear map that batches the 192 transposed
# ring-switch coordinates.
RING_MAP_SHIFTS = [32, 16, 8, 4, 2, 1]
# Exponent bit-widths: an announced 32-bit count decomposes into COUNT_BITS bits,
# its top bit constrained to zero so the native strict 32-bit bound holds; any
# structural size (sums of 2^kappa, packing offsets) fits SIZE_BITS bits; and a
# structural LOG (log_mem, tau_t, log_inv_rate), announced as an integer word and
# raised to a g-power by g_power_of_word, is below SIZE_BITS, so LOG_WORD_BITS bits
# are enough and the reconstruction IS the bound (a larger announced log cannot
# reproduce itself from this many bits).
COUNT_BITS = 33
SIZE_BITS = 34
LOG_WORD_BITS = 6

# ------------------------------------------------------------------- Fiat-Shamir
# Every absorbed block carries its domain tag in lane 3, which is exactly
# `fs_compress`'s `tail` argument, so a role is never smuggled through the data
# lanes. The seeding block has none, being fixed at the head of the chain.
DS_OBSERVE = 1
DS_SQ = 2
DS_POW_BASE = 3
DS_POW_NONCE = 4

# ----------------------------------------------------------- loop-carried chains
# A loop whose state is several fields keeps ONE heap run of N cells per iteration,
# so a step is one pointer multiply rather than one per field.
PAIR_SLOTS = 2  # the Fiat-Shamir state pair alone
# A Fiat-Shamir chain carrying one accumulator (the claim batching loops).
ACC_FS0 = 0
ACC_FS1 = 1
ACC_VALUE = 2
ACC_SLOTS = 3
# One sumcheck round of the bus GKR, the table batch, or flock's multilinear rounds.
ROUND_FS0 = 0
ROUND_FS1 = 1
ROUND_CURSOR = 2
ROUND_CLAIM = 3
ROUND_SLOTS = 4
# One product layer of the bus GKR.
LAYER_FS0 = 0
LAYER_FS1 = 1
LAYER_CURSOR = 2
LAYER_PUSH = 3
LAYER_PULL = 4
LAYER_COUNT = 5
LAYER_LAMBDA = 6
LAYER_ROW = 7
LAYER_POS = 8
LAYER_SLOTS = 9
# One OOD sample of a WHIR level.
OOD_BETA = 0
OOD_Y = 1
OOD_C0 = 2
OOD_C2 = 3
OOD_SLOTS = 4

# ---------------------------------------------------- the bus: sides and blocks
# GKR sides. The layer counts mu_s are hinted and certified from the block kappas;
# GKR_ROUNDS_CAP caps the per-tree round positions (triangle rounds plus one slot
# per layer) and GKR_POINTS_CAP the point triangle (rows x MU_CAP).
PUSH_SIDE = 0
PULL_SIDE = 1
COUNT_SIDE = 2
N_GKR_SIDES = 3
GKR_ROUNDS_CAP = GKR_ROUNDS_CAP_PLACEHOLDER
MU_CAP = MU_CAP_PLACEHOLDER
GKR_POINTS_CAP = GKR_POINTS_CAP_PLACEHOLDER
# Bus blocks, flattened across the 3 sides (side s covers blocks
# [SIDE_BLOCK_START[s], SIDE_BLOCK_START[s+1])). The block STRUCTURE is
# protocol-fixed and baked: each block's coord range [BLOCK_COORD_OFF,
# +BLOCK_COORD_COUNT), per coord its COORD_TYPE kind (mirroring leaf.rs::Coord),
# COORD_CONST (the const value, a product's or gcol's g^k, else 0), and the kappa
# SOURCE map (BLOCK_KAPPA_SRC/ADJ: 0 = const adj, 1 = log_mem, 2+t = tau_t). The
# block SHAPES are all reconstructed at runtime from the certified logs: kappa
# directly, the selector bits by pinned advice-decompositions. BLOCK_TABLE names
# the table a block's flush belongs to, or NO_TABLE for the framework blocks
# (boundary, memory seed/finalize, bytecode seed/finalize); it is also what marks a
# block as owned, an owned block's fingerprint being settled by the table sumcheck
# off its table's column evaluations.
COORD_KIND_CONST = 0
COORD_KIND_COL = 1
COORD_KIND_GCOL = 2
COORD_KIND_INDEX = 3
COORD_KIND_PUBLIC = 4
COORD_KIND_PROD = 5
NO_TABLE = NO_TABLE_PLACEHOLDER
SIDE_BLOCK_START = SIDE_BLOCK_START_PLACEHOLDER
N_BLOCKS = N_BLOCKS_PLACEHOLDER
BLOCK_KAPPA_SRC = BLOCK_KAPPA_SRC_PLACEHOLDER
BLOCK_KAPPA_ADJ = BLOCK_KAPPA_ADJ_PLACEHOLDER
BLOCK_TABLE = BLOCK_TABLE_PLACEHOLDER
BLOCK_SIDE = BLOCK_SIDE_PLACEHOLDER
BLOCK_COORD_OFF = BLOCK_COORD_OFF_PLACEHOLDER
BLOCK_COORD_COUNT = BLOCK_COORD_COUNT_PLACEHOLDER
COORD_TYPE = COORD_TYPE_PLACEHOLDER
COORD_CONST = COORD_CONST_PLACEHOLDER
# Claim dedup: push/pull share their GKR point, so a column read by two blocks with
# the same kappa (across OR within the sides) is streamed and opened ONCE.
# COORD_FRESH = 1 on the first occurrence (read the stream, fill pool slot
# COORD_CLAIM_SLOT), 0 on a duplicate (reuse that slot). The count side has its own
# point, so its claims never dedup against the pair's.
COORD_FRESH = COORD_FRESH_PLACEHOLDER
COORD_CLAIM_SLOT = COORD_CLAIM_SLOT_PLACEHOLDER
# A TABLE block's coordinates, flattened into TERMS: coord c is
# Σ_{j < COORD_TERM_COUNT[c]} term(COORD_TERM_OFF[c] + j), each term a TERM_TYPE
# kind over that table's LOCAL column indices TERM_COL_A/TERM_COL_B, scaled by
# TERM_CONST. Those coords raise no claim (the table sumcheck settles them), which
# is what lets one carry a value the row DERIVES from its columns: an XOR/MUL
# result, a DEREF store, a JUMP successor. A framework coord has no terms.
COORD_TERM_OFF = COORD_TERM_OFF_PLACEHOLDER
COORD_TERM_COUNT = COORD_TERM_COUNT_PLACEHOLDER
TERM_TYPE = TERM_TYPE_PLACEHOLDER
TERM_CONST = TERM_CONST_PLACEHOLDER
TERM_COL_A = TERM_COL_A_PLACEHOLDER
TERM_COL_B = TERM_COL_B_PLACEHOLDER
N_BUS_CLAIMS = N_BUS_CLAIMS_PLACEHOLDER
INDEX_MLE_FACTORS = INDEX_MLE_FACTORS_PLACEHOLDER  # 1 + g^(2^i)
# Committed-coordinate claims (Col/GCol coords across all sides) and the deferred
# bytecode values (Public coords).
N_CLAIMS = N_CLAIMS_PLACEHOLDER
# A bus tuple's coordinates index the 2^N_TUPLE_BITS fingerprint slots (doc
# sec:gp). The stacked bytecode has BYTECODE_COLS encoding columns, stacked along
# LOG2_BYTECODE_COLS selector bits into ONE multilinear; push and pull share their
# GKR point, so the columns are opened ONCE.
N_TUPLE_BITS = 4
N_TUPLE_SLOTS = 16
BYTECODE_COLS = BYTECODE_COLS_PLACEHOLDER
LOG2_BYTECODE_COLS = LOG2_BYTECODE_COLS_PLACEHOLDER

# --------------------------------------------------------------- the six tables
# The table sumcheck's batch carries EVERY committed column of a table, because its
# bus forms read the flushed ones and its constraint the rest; TABLE_COLS_CAP caps
# the evaluation frame. ETA_OFFSET[t] starts table t's disjoint range of zc_xi
# powers; the three bus forms take ETA_FORM_BASE + side, the SAME three powers for
# every table, and that sharing is what makes the batch's target derivable from the
# three leaf claims. FLOORS[t] is the table's tau floor (BLAKE2s is sized to
# flock's instance count, >= 2^3).
TABLE_XOR = 0
TABLE_MUL = 1
TABLE_SET = 2
TABLE_DEREF = 3
TABLE_JUMP = 4
TABLE_BLAKE2s = 5
N_TABLES = N_TABLES_PLACEHOLDER
FLOORS = [0, 0, 0, 0, 0, 3]
N_TABLE_COLS = N_TABLE_COLS_PLACEHOLDER
TABLE_COLS_CAP = TABLE_COLS_CAP_PLACEHOLDER
ETA_OFFSET = ETA_OFFSET_PLACEHOLDER
ETA_FORM_BASE = ETA_FORM_BASE_PLACEHOLDER
N_ETA_POWS = N_ETA_POWS_PLACEHOLDER

# ------------------------------------------------------------ flock (the R1CS)
# Univariate skip: K_SKIP variables fold in one skip round (half-domain 2^K_SKIP
# phi8 nodes), then N_FIXED_CHALLENGE_ROUNDS fixed inner rounds (FIXED_CHALLENGES),
# then sampled outer rounds. LAGRANGE_INV_* are the one baked inverse barycentric
# denominator per domain (combined, S). The zerocheck point/round buffers are sized
# at runtime in the exponent (m = K_LOG + tau_5 and m - 6, both certified);
# LINCHECK_ROUNDS = K_LOG - K_SKIP is protocol-fixed and PIN_COLUMN is the
# const-pin column.
K_SKIP = K_SKIP_PLACEHOLDER
N_FIXED_CHALLENGE_ROUNDS = N_FIXED_CHALLENGE_ROUNDS_PLACEHOLDER
FIXED_CHALLENGES = FIXED_CHALLENGES_PLACEHOLDER
PHI8_NODES = PHI8_NODES_PLACEHOLDER
LAGRANGE_INV_COMBINED = LAGRANGE_INV_COMBINED_PLACEHOLDER
LAGRANGE_INV_S = LAGRANGE_INV_S_PLACEHOLDER
LINCHECK_ROUNDS = LINCHECK_ROUNDS_PLACEHOLDER
PIN_COLUMN = PIN_COLUMN_PLACEHOLDER
K_LOG = K_LOG_PLACEHOLDER
SLOT_STRIDE_LOG = SLOT_STRIDE_LOG_PLACEHOLDER  # = K_LOG - LOG_PACKING (=8); the q_flock slot stride

# ------------------------------------------------- the stacked WHIR opening
# The opening is dispatched by the certified committed log-size m through `match`.
# The LIG_* tables carry one row per (rate, m), emitted from the same
# derive_profile/level_shapes the prover uses: scalars index as TBL[m_idx],
# per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl] where m_idx is the
# flattened rate-major configuration index, and the subspace vanishing constants
# with the LIG_MAX_VANISH_LEN stride.
LIG_MIN_LOG_SIZE = LIG_MIN_LOG_SIZE_PLACEHOLDER
LIG_N_LOG_SIZES = LIG_N_LOG_SIZES_PLACEHOLDER
LIG_N_RATES = LIG_N_RATES_PLACEHOLDER
# Committed-column kappa sources (0 = const COL_KAPPA_ADJ, 1 = log_mem, 2+t = tau_t)
# and the PCS floor for the stacked size.
N_COMMITTED_COLS = N_COMMITTED_COLS_PLACEHOLDER
COL_KAPPA_SRC = COL_KAPPA_SRC_PLACEHOLDER
COL_KAPPA_ADJ = COL_KAPPA_ADJ_PLACEHOLDER
PCS_MIN_MU = PCS_MIN_MU_PLACEHOLDER
# Global maxima; StackBuf frame sizes are parse-time, so they must be baked.
LIG_MAX_LEVELS = LIG_MAX_LEVELS_PLACEHOLDER
LIG_MAX_VANISH_LEN = LIG_MAX_VANISH_LEN_PLACEHOLDER
LIG_MAX_OOD_SAMPLES = LIG_MAX_OOD_SAMPLES_PLACEHOLDER
LIG_LOG_MSG_COLS_CAP = LIG_LOG_MSG_COLS_CAP_PLACEHOLDER
YR_LOG_CAP = YR_LOG_CAP_PLACEHOLDER
MAX_STACK_LOG = LIG_MIN_LOG_SIZE + LIG_N_LOG_SIZES - 1
COL_BITS_STRIDE = MAX_STACK_LOG + YR_LOG_CAP
LIG_N_LEVELS = LIG_N_LEVELS_PLACEHOLDER
LIG_YR_LEVEL = LIG_YR_LEVEL_PLACEHOLDER
LIG_YR_LOG_LEN = LIG_YR_LOG_LEN_PLACEHOLDER
LIG_YR_LEN = LIG_YR_LEN_PLACEHOLDER
LIG_TOTAL_FOLDS = LIG_TOTAL_FOLDS_PLACEHOLDER
LIG_MAX_QUERIES = LIG_MAX_QUERIES_PLACEHOLDER
LIG_MAX_SQUEEZES = LIG_MAX_SQUEEZES_PLACEHOLDER
LIG_MAX_INTERLEAVE = LIG_MAX_INTERLEAVE_PLACEHOLDER
LIG_POSITIONS_LEN = LIG_POSITIONS_LEN_PLACEHOLDER
LIG_ROWS_LEN = LIG_ROWS_LEN_PLACEHOLDER
LIG_PATHS_LEN = LIG_PATHS_LEN_PLACEHOLDER
LIG_QUERY_GRIND_BITS = LIG_QUERY_GRIND_BITS_PLACEHOLDER
LIG_OOD_SAMPLES = LIG_OOD_SAMPLES_PLACEHOLDER
LIG_QUERIES = LIG_QUERIES_PLACEHOLDER
LIG_FOLDS = LIG_FOLDS_PLACEHOLDER
LIG_INTERLEAVE = LIG_INTERLEAVE_PLACEHOLDER
LIG_LEAF_PAIRS = LIG_LEAF_PAIRS_PLACEHOLDER
LIG_LEAF_BLOCKS = LIG_LEAF_BLOCKS_PLACEHOLDER
LIG_PACKED_ROW_CAP = LIG_PACKED_ROW_CAP_PLACEHOLDER
LIG_TREE_DEPTH = LIG_TREE_DEPTH_PLACEHOLDER
LIG_SQUEEZES = LIG_SQUEEZES_PLACEHOLDER
LIG_POSITIONS_OFF = LIG_POSITIONS_OFF_PLACEHOLDER
LIG_LOG_MSG_COLS = LIG_LOG_MSG_COLS_PLACEHOLDER
LIG_RESIDUAL_FOLD_OFF = LIG_RESIDUAL_FOLD_OFF_PLACEHOLDER
LIG_RESIDUAL_PREFIX_LEN = LIG_RESIDUAL_PREFIX_LEN_PLACEHOLDER
LIG_FOLDS_OFF = LIG_FOLDS_OFF_PLACEHOLDER
LIG_ROWS_OFF = LIG_ROWS_OFF_PLACEHOLDER
LIG_PATHS_OFF = LIG_PATHS_OFF_PLACEHOLDER
LIG_VANISH_OFF = LIG_VANISH_OFF_PLACEHOLDER
LIG_VANISH_VALS = LIG_VANISH_VALS_PLACEHOLDER
LIG_VANISH_INVS = LIG_VANISH_INVS_PLACEHOLDER
LIG_N_CANDIDATES = LIG_N_CANDIDATES_PLACEHOLDER
LIG_MIN_SHIFT_INV = LIG_MIN_SHIFT_INV_PLACEHOLDER
# eval_b claim descriptors. CLAIM_POINT_BUF says which point buffer a pooled
# claim's x-part lives in, CLAIM_COMMITTED_COL maps it to the compact index of the
# committed column it must open (a virtual BLAKE2s value claim maps to QFLOCK),
# CLAIM_QFLOCK_SLOT_BITS holds the fixed packed-slot bits of every logical claim
# (zero for a non-virtual one), and QFLOCK_COMMITTED_COL is the ring-switch target.
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QFLOCK_RHO = 3
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_COMMITTED_COL = CLAIM_COMMITTED_COL_PLACEHOLDER
CLAIM_QFLOCK_SLOT_BITS = CLAIM_QFLOCK_SLOT_BITS_PLACEHOLDER
QFLOCK_COMMITTED_COL = QFLOCK_COMMITTED_COL_PLACEHOLDER
QFLOCK_VARS_CAP = QFLOCK_VARS_CAP_PLACEHOLDER

# ------------------------------------------------------ statements and deferral
# A node defers three claims on fixed polynomials. DEFER_SIZE is the region one
# sub-proof's verification exports (a bytecode point plus the flock lincheck data,
# see verify_sub's defer_out layout); DEFER_STMT_* index the batched claims a
# node's OWN statement carries. The Fiat-Shamir seed rides the public input rather
# than being baked, so one compiled guest verifies proofs of any inner program.
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER  # log rows of the bytecode blocks
DEFER_SIZE = DEFER_SIZE_PLACEHOLDER
BYTECODE_VARS = BYTECODE_VARS_PLACEHOLDER  # = BYTECODE_LOG + LOG2_BYTECODE_COLS
# The exported record's layout: the shared bytecode point, then the flock data.
FRESH_BC_VALUE = BYTECODE_VARS
FRESH_ALPHA = BYTECODE_VARS + 1
FRESH_Z_SKIP = BYTECODE_VARS + 2
FRESH_ZCHI = BYTECODE_VARS + 3
FRESH_LINCHECK_RS = FRESH_ZCHI + LINCHECK_ROUNDS
FRESH_Z_PARTIAL = FRESH_LINCHECK_RS + LINCHECK_ROUNDS
FRESH_MATPART = FRESH_Z_PARTIAL + 2 ** K_SKIP
DEFER_STMT_CELLS = BYTECODE_VARS + 1 + 2 * K_LOG + 2
DEFER_STMT_BC_VALUE = BYTECODE_VARS
DEFER_STMT_MAT_POINT = BYTECODE_VARS + 1
DEFER_STMT_A_VALUE = BYTECODE_VARS + 1 + 2 * K_LOG
DEFER_STMT_B_VALUE = BYTECODE_VARS + 2 + 2 * K_LOG
AGG_SEED_0 = AGG_SEED_0_PLACEHOLDER
AGG_SEED_1 = AGG_SEED_1_PLACEHOLDER
# The statement digest's preimage: the STMT_HEADER header values as the 16-byte
# cells they already are (the seed and the signer-set digest, which itself binds
# the epoch groups and every count), then the deferred cells' tower limbs, two to
# a cell and four cells to a 64-byte block. No domain tag: the seed leads, and it
# binds this bytecode and flock's R1CS.
STMT_HEADER = STMT_HEADER_PLACEHOLDER
STMT_DEFER_OFF = STMT_HEADER
STMT_ODD = STMT_ODD_PLACEHOLDER
STMT_PAIRS = STMT_PAIRS_PLACEHOLDER
STMT_PAD_CELLS = STMT_PAD_CELLS_PLACEHOLDER
STMT_BLOCKS = STMT_BLOCKS_PLACEHOLDER
# The declared lists are hashed with plain BLAKE2s over a flat run of cells, 64
# bytes a compression. A block's byte counter is a runtime value and the ISA has no
# integer addition, so it splits as in doc §sec:prog-byte-counter: a window of
# SIGNERS_WINDOW blocks shares one base 64·SIGNERS_WINDOW·q, whose set bits all sit
# above the window's own offsets 64(j+1), so a block's metadata cell is one XOR. The
# base comes from the window loop's own counter, and the one block whose offset
# overlaps it takes the next window's base instead.
SIGNERS_WINDOW = SIGNERS_WINDOW_PLACEHOLDER
SIGNERS_WINDOW_LOG = SIGNERS_WINDOW_LOG_PLACEHOLDER
SIGNERS_MAX_WINDOWS = SIGNERS_MAX_WINDOWS_PLACEHOLDER
SIGNERS_COUNT_BITS = SIGNERS_COUNT_BITS_PLACEHOLDER
# BLAKE2s's parameterized initial chaining value, which every hash here starts from,
# and the metadata of a final block with a zero counter, to add a length into.
BLAKE2S_IV_0 = BLAKE2S_IV_0_PLACEHOLDER
BLAKE2S_IV_1 = BLAKE2S_IV_1_PLACEHOLDER
MD_FINAL = MD_FINAL_PLACEHOLDER
# The two cells that tag the set's own string, so its hash cannot be confused with
# either list's or with a Fiat-Shamir state.
SIGNERS_TAG_0 = SIGNERS_TAG_0_PLACEHOLDER
SIGNERS_TAG_1 = SIGNERS_TAG_1_PLACEHOLDER

# ---------------------------------------------------------- XMSS (host-supplied)
# Every 16-byte native value (tweak, digest, chain tip, sibling, public parameter)
# is one canonical 128-bit cell. XM_* are the tweaks minus their index field, as
# the host read them out of the native `make_tweak`, so the guest holds no byte
# layout of its own; XM_INDEX_WEIGHT[b] is what bit b of an index weighs, an index
# being its set bits summed.
V = V_PLACEHOLDER
W = W_PLACEHOLDER
TARGET_SUM = TARGET_SUM_PLACEHOLDER
LOG_LIFETIME = LOG_LIFETIME_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
CHAIN_STEPS = CHAIN_LENGTH - 1
WORDS_PER_VALUE = 1
WORDS_PER_BLOCK = 2
# Tweak table (one 1-cell tweak per index): encoding | V·CHAIN_STEPS chain |
# wots-pk | merkle. Derived in-circuit, once per epoch group the statement carries.
N_TWEAKS = 1 + V * CHAIN_STEPS + 1 + LOG_LIFETIME
N_TWEAK_CELLS = WORDS_PER_VALUE * N_TWEAKS
WOTS_PK_TWEAK_IDX = 1 + V * CHAIN_STEPS
MERKLE_TWEAK_IDX = WOTS_PK_TWEAK_IDX + 1
MERKLE_BIT_CELLS = WORDS_PER_VALUE * LOG_LIFETIME  # one 1-cell bit word per level
XM_ENC_TWEAK = XM_ENC_TWEAK_PLACEHOLDER
XM_PK_TWEAK = XM_PK_TWEAK_PLACEHOLDER
XM_CHAIN_TWEAKS = XM_CHAIN_TWEAKS_PLACEHOLDER   # indexed CHAIN_STEPS·i + s
XM_MERKLE_TWEAKS = XM_MERKLE_TWEAKS_PLACEHOLDER  # indexed by level
XM_INDEX_WEIGHT = XM_INDEX_WEIGHT_PLACEHOLDER
# Digits packed per digest lane: W bits each in GF(2^64)'s monomial budget (the
# lane's leftover top bits are ground to zero by the signer).
DIGITS_PER_WORD = V / 2
TIP_CELLS = WORDS_PER_VALUE * V
WOTS_PK_BLOCKS = (2 + V) / 4  # prefix (tweak, pp) + V tips, four cells a block

# ------------------------------------------------------ SPHINCS+ (host-supplied)
# The scheme's own letters, prefixed SP_ where XMSS has the same one.
SP_V = SP_V_PLACEHOLDER
SP_W = SP_W_PLACEHOLDER
SP_TARGET_SUM = SP_TARGET_SUM_PLACEHOLDER
SP_D = SP_D_PLACEHOLDER
SP_HEIGHTS = SP_HEIGHTS_PLACEHOLDER   # h_lay, one per hypertree layer, top first
SP_SUFFIX = SP_SUFFIX_PLACEHOLDER     # SP_SUFFIX[lay] = sum of h_j for j >= lay
SP_A = SP_A_PLACEHOLDER
SP_K = SP_K_PLACEHOLDER
SP_H = SP_H_PLACEHOLDER               # the total hypertree height, SP_SUFFIX[0]
SP_CHAIN_LENGTH = 2 ** SP_W
SP_CHAIN_STEPS = SP_CHAIN_LENGTH - 1
SP_DIGITS_PER_WORD = SP_V / 2
SP_TIP_CELLS = SP_V
SP_LEAF_BLOCKS = (2 + SP_V) / 4       # prefix (tweak, pp) + V tips, four cells a block
SP_N_FTS = SP_K - 1                   # the forest drops the last index's tree
SP_ROOT_BLOCKS = (2 + SP_N_FTS) / 4
# The message digest is h + k*a bits of a BLAKE2s output: the whole low cell and
# the low 48 bits of the high one. Decomposing the high cell's low lane covers
# them, so the buffer holds three lanes and the top 16 are never read.
SP_BIT_LANES = 3
SP_BIT_CELLS = SP_BIT_LANES * BASE_FIELD_BITS
# Tweak types (the tweak's first byte). Types 0 and 5 are the seed derivation's,
# which is a signer's own business: nothing in-circuit ever verifies one.
SP_TW_PRF = 0
SP_TW_CHAIN = 1
SP_TW_LEAF = 2
SP_TW_NODE = 3
SP_TW_ENC = 4
SP_TW_FTS_PRF = 5
SP_TW_FTS_LEAF = 6
SP_TW_FTS_NODE = 7
SP_TW_FTS_ROOTS = 8
SP_TW_MSG = 9
# enc(t, lay, tau, p, j) packs t at bit 0, lay at 8, tau at 16, p at 48 and j at
# 80, fourteen bytes of fields and two of padding. Every field this instance uses
# is small enough that none straddles the 64-bit lane boundary (tau < 2^26 at bit
# 16, p <= 334 at bit 48, j < 2^12 at bit 80), so a tweak cell is
# `t + lay*2^8 + tau*2^16 + p*2^48` in lane 0 plus `j*2^16` in lane 1, and every
# term is one field addition. SP_TAU_POS and SP_J_POS are where a bit of tau or of
# j weighs in the coordinate basis, the j position already carrying the lane, so
# nothing has to be multiplied by Y afterwards.
SP_LAY_MUL = 2 ** 8
SP_P_MUL = 2 ** 48
SP_TAU_POS = 16
SP_J_POS = BASE_FIELD_BITS + 16
SP_CHAIN_MUL = SP_CHAIN_LENGTH * SP_P_MUL   # chain i's tweaks start at p = 2^w * i
# The encoding counter, LE_32 in the low four bytes of its cell: bounded by
# decomposing exactly that many bits, so the guest accepts no preimage the native
# verifier cannot parse.
SP_COUNTER_BITS = 32

# --------------------------------------------------------------- node capacities
# MAX_KEYS caps the coverage table's slots, both schemes' declared keys and their
# duplicates, which is what the coverage range check needs below 2^MIN_LOG_MEM;
# MAX_RECURSIONS is the arity of an aggregation tree; MAX_EPOCHS caps the runtime
# number of XMSS epoch groups.
MAX_KEYS = MAX_KEYS_PLACEHOLDER
MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER
MAX_EPOCHS = MAX_EPOCHS_PLACEHOLDER


# =================================== field packing ==================================
# Serializing a word means exposing its three K limbs, and the tower representation
# is unique, so proving that the exposed lanes are in K and weight back to the word
# is the whole check: no equality to make, one less hint to distrust.


@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + Y_TOWER * b


def assert_canonical(word):
    # Hint the low limb and derive the quotient by Y. Requiring both in K proves
    # `word = lo + Y*hi`, hence that its top limb is zero.
    lo = StackBuf(1)
    hint_f192_limbs(lo, word)
    hi = (word + lo[0]) * Y_INV
    assert_in_k(lo[0], hi)
    return 0


@inline
def challenge_from_state(state):
    # `hash_state_to_words` with the second word dropped, written out because a
    # tuple-unpacking call is not inlinable and `squeeze` is @inline. Both words are
    # BLAKE2s outputs, so their top limbs are already zero; only d2 is needed
    # separately, so hint it, derive d3 = (state[1] + d2)/Y, and prove both in K.
    d2 = StackBuf(1)
    hint_f192_limbs(d2, state[1])
    d3 = (state[1] + d2[0]) * Y_INV
    assert_in_k(d2[0], d3)
    return state[0] + Y_TOWER * Y_TOWER * d2[0]


# ==================================== Fiat-Shamir ===================================


@inline
def fs_compress(state, scalar, tail, out):
    # Absorb [scalar.c0, scalar.c1, scalar.c2, tail] as two canonical cells. Only
    # the two LOW limbs are advice: pack64x2 proves them in K and makes block[0]
    # their packing lo + Y·hi, which leaves the top limb determined as
    # (scalar + block[0])·Y⁻², the second pack proving that is in K too.
    lo = StackBuf(2)
    hint_f192_limbs(lo, scalar)
    block = StackBuf(2)
    block[0] = pack64x2(lo[0], lo[1])
    top = (scalar + block[0]) * (Y_INV * Y_INV)
    block[1] = pack64x2(top, tail)
    blake2s(state, block, out)
    return


@inline
def obs(state, x):
    # Bind one scalar into the chain: state <- compress(state, (x, DS_OBSERVE)).
    # Returns the successor StackBuf; the call site aliases it (zero copies).
    nb = StackBuf(2)
    fs_compress(state, x, DS_OBSERVE, nb)
    return nb


@inline
def fs_next(state, cursor):
    # Fetch, observe and advance in one act: read the word under `cursor`, fold it
    # into the state, and hand back the successor state, the word, AND the cursor
    # stepped one word on. Reading and absorbing are inseparable here, so no
    # proof-stream word can enter the computation unbound: the soundness invariant
    # the whole guest rests on. All three returns alias into the caller for free.
    x = cursor[GEN ** 0]
    nb = obs(state, x)
    return nb, x, cursor * GEN


@inline
def squeeze(state):
    # Ratchet: the canonical 128+128 digest is the new state; its first three K
    # lanes are reassembled as the F192 challenge.
    nb = StackBuf(2)
    fs_compress(state, 0, DS_SQ, nb)
    challenge = challenge_from_state(nb)
    return nb, challenge


@inline
def absorb_nonce(state, x):
    # Full-field grinding nonce absorb: [x.c0, x.c1, x.c2, DS_POW_NONCE].
    nb = StackBuf(2)
    fs_compress(state, x, DS_POW_NONCE, nb)
    return nb


def squeeze_step(state_0, state_1):
    # `squeeze` exposing BOTH output words, so a query-squeeze loop can chain the
    # state through a heap buffer. Returns (challenge, next_state_0, next_state_1).
    state = [state_0, state_1]
    next_state, challenge = squeeze(state)
    return challenge, next_state[0], next_state[1]


# ============================ bits, logs, and the exponent ==========================


@inline
def bind_bits(bits_ptr, value, n: Const):
    # Tie an advice bit run back to the value it decomposes. Booleanity is a
    # write-once pin: the cell already holds the bit, so storing its square IS the
    # assert, one instruction shorter than a separate equality.
    acc = 0
    for i in unroll(0, n):
        b = bits_ptr[GEN ** i]
        bits_ptr[GEN ** i] = b * b
        acc += b * COORD_BASIS[i]
    assert acc == value
    return


def exponent_tables():
    # Read-only lookup tables over the exponent domain, indexed at runtime g-powers
    # (so they must be heap, not stack): g_logs_pow2[g^j] = 2^j raises a g-power's
    # log, and g_squares[g^j] = g^(2^j) turns integer sums of powers of two into
    # field products. Both span SIZE_BITS because verify_log2_ceil bounds its result
    # there, so g_log reaches g^(SIZE_BITS-1) and indexes g_logs_pow2 at it; sizing
    # to COUNT_BITS would leave that lookup reading a prover-chosen cell.
    g_logs_pow2 = HeapBuf(SIZE_BITS)
    for j in unroll(0, SIZE_BITS):
        g_logs_pow2[GEN ** j] = 2 ** j
    g_squares = HeapBuf(SIZE_BITS)
    sq_run = GEN
    for j in unroll(0, SIZE_BITS):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    return g_logs_pow2, g_squares


def g_power_of_word(value, g_squares, nbits: Const):
    # g^value for a concrete integer `value` < 2^nbits: advice-decompose its bits,
    # tie them back to the word, and assemble Π g^(bit_j·2^j).
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits(bits, value, nbits)
    word = 0
    g_value = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits[GEN ** j]
        assert bit * bit == bit
        word += bit * (2 ** j)
        g_value *= (1 + bit * (g_squares[GEN ** j] + 1))
    assert word == value
    return g_value


def verify_log2_ceil(bits_buf, g_logs_pow2, g_squares, floor: Const, nbits: Const):
    # Given `nbits` bits already in bits_buf, return (g_log, exp_prod) for
    # word = Σ bit_j 2^j: exp_prod = g^word and g_log = g^max(log2_ceil(word),
    # floor). g_log is prover advice, pinned to log2_ceil(word) by psum[g_log] ==
    # word (word < 2^log, the == 2^log case via g_logs_pow2) and word > 2^(log-1)
    # (waived at floor). Callers fill the bits and tie word or exp_prod to their
    # value. NB: log2 here is the base-2 log of the integer word, not the discrete
    # log base g that `log(...)` means.
    psum_buf = HeapBuf(GEN ** (nbits + 1))  # psum_buf[g^j] = value of bits [0, j)
    psum_buf[GEN ** 0] = 0
    word = 0
    exp_prod = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits_buf[GEN ** j]
        assert bit * bit == bit
        exp_prod *= (1 + bit * (g_squares[GEN ** j] + 1))
        word += bit * (2 ** j)
        psum_buf[GEN ** (j + 1)] = word
    g_log = hint_log2_ceil(bits_buf, nbits, floor)  # prover advice; verified below
    assert log(g_log) < SIZE_BITS
    low_bits = psum_buf[g_log]                  # value of bits [0, log)
    high_bits = low_bits + word                 # value of bits [log, nbits)
    assert high_bits * low_bits == 0            # word < 2^log (high bits clear) OR ...
    assert high_bits * (word + g_logs_pow2[g_log]) == 0  # ... word == 2^log
    if g_log != GEN ** floor:
        # minimality (word > 2^(log-1)); skip at g_log == g^0, where word is in
        # {0,1}, its ceil-log 0 already minimal and psum_buf[g^-1] out of range.
        if g_log != GEN ** 0:
            low_bits_prev = psum_buf[g_log * INV_GEN]  # bits [0, log-1)
            word_vs_2logprev = word + g_logs_pow2[g_log * INV_GEN]  # 0 iff word == 2^(log-1)
            assert (low_bits_prev + word) * word_vs_2logprev != 0
    return g_log, exp_prod


def log2_ceil_in_the_exponent(g_N, g_logs_pow2, g_squares, floor: Const, nbits: Const):
    # g^log2_ceil(N) given g_N = g^N (N < 2^nbits). There is no in-circuit log, so
    # the prover hints N's bits; they are verified and tied back, the value they
    # decode to having to equal g_N.
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits_exponent(bits, g_N, nbits)
    g_log, g_bits_value = verify_log2_ceil(bits, g_logs_pow2, g_squares, floor, nbits)
    assert g_bits_value == g_N
    return g_log


def decode_query_bits(squeezed_word, positions_out, bit_ptrs_out, depth: Const):
    # The squeezed word's bits are advice-decomposed HERE, boolean-constrained and
    # tied back by reconstruction; each depth-bit group also becomes a query
    # position (little-endian), with a pointer to its bit run (the Merkle direction
    # bits). Each field word packs FIELD_BITS // depth positions. The bits live in
    # FRAME cells, every index into them being compile-time, and `addr` names the
    # run so the direction-bit pointers still reach it.
    per_word = FIELD_BITS // depth
    bits = StackBuf(FIELD_BITS)
    hint_decompose_bits(bits, squeezed_word, FIELD_BITS)
    bits_ptr = addr(bits)
    reconstructed = 0
    for j in unroll(0, per_word):
        base_bit = j * depth
        # A group inside one 64-bit limb shifts as a WHOLE, the coordinate basis
        # being the polynomial basis there: COORD_BASIS[base_bit + b] ==
        # COORD_BASIS[base_bit] * COORD_BASIS[b] below 64, so the group contributes
        # one multiply rather than one per bit. A group straddling the boundary
        # splits into the two runs that do stay inside a limb; `b // cut == 0` IS
        # `b < cut`, the DSL's `if` comparing for equality only.
        cut = 64 - base_bit % 64  # bits of this group below the next limb
        p_lo = 0
        p_hi = 0
        for b in unroll(0, depth):
            t = bits[base_bit + b]
            bits[base_bit + b] = t * t  # booleanity, as a write-once pin
            if b // cut == 0:
                p_lo += t * COORD_BASIS[b]
            else:
                p_hi += t * COORD_BASIS[b - cut]
        # position = p_lo + 2^cut * p_hi: multiplying by X^cut concatenates the two
        # runs, since both degrees stay below 64.
        if cut // depth == 0:  # `cut < depth`: this group straddles the boundary
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base_bit] * p_lo + COORD_BASIS[base_bit + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base_bit] * p_lo
        bit_ptrs_out[GEN ** j] = bits_ptr * GEN ** base_bit
    for i in unroll(per_word * depth, FIELD_BITS):
        t = bits[i]
        bits[i] = t * t
        reconstructed += t * COORD_BASIS[i]
    assert reconstructed == squeezed_word
    return


def grind_check(state_0, state_1, nonce, nbits_g):
    # WHIR fold/query grinding: digest = H(H(state, POW_BASE), (nonce, POW_NONCE)),
    # whose low nbits (nbits_g = g^nbits) must be zero. The PoW window of
    # transcript::pow_bits_ok is `digest.0 & ((1 << bits) - 1)` with nbits < 64, so
    # it lives entirely in the digest's FIRST 64-bit lane: only that lane is
    # advice-decomposed and verified, not all FIELD_BITS of the cell. The caller
    # absorbs the full field nonce afterwards. The honest prover searches the
    # deterministic u64 subset while verification permits the full field: each
    # candidate still costs one hash and succeeds with probability 2^-bits.
    if nbits_g == GEN ** 0:
        assert nonce == 0  # native canonical zero-work nonce
    st = [state_0, state_1]
    base = StackBuf(2)
    fs_compress(st, 0, DS_POW_BASE, base)
    out = StackBuf(2)
    fs_compress(base, nonce, DS_POW_NONCE, out)
    lanes = StackBuf(1)
    hint_f192_limbs(lanes, out[0])
    high = (out[0] + lanes[0]) * Y_INV
    assert_in_k(lanes[0], high)
    # Frame cells for the unrolled pass (no DEREF per bit), named by `addr` for the
    # zero-check walk, whose bound is runtime and so must index a pointer.
    lane_bits = StackBuf(BASE_FIELD_BITS)
    hint_decompose_bits(lane_bits, lanes[0], BASE_FIELD_BITS)
    acc = 0
    for i in unroll(0, BASE_FIELD_BITS):
        b = lane_bits[i]
        lane_bits[i] = b * b  # booleanity, as a write-once pin
        acc += b * COORD_BASIS[i]
    assert acc == lanes[0]  # the bits ARE the lane's coordinates, so the pins below bind it
    lane_ptr = addr(lane_bits)
    for xb in mul_range(1, nbits_g):
        assert lane_ptr[xb] == 0
    return


# =============================== multilinear primitives =============================


@inline
def eq_weight(ch, count: Const, idx: Const, msb_span: Const):
    # The eq-tensor weight of compile-time index `idx` against the challenge run
    # ch[0..count): prod_c eq(bit(idx), ch[c]), where the bit is bit c of idx
    # (msb_span == 0) or bit (msb_span - 1 - c) (an MSB-first walk over an
    # msb_span-bit index).
    w = GEN ** 0
    for c in unroll(0, count):
        cv = ch[GEN ** c]
        if msb_span == 0:
            if (idx // (2 ** c)) % 2 == 1:
                w *= cv
            else:
                w *= (1 + cv)
        else:
            if (idx // (2 ** (msb_span - 1 - c))) % 2 == 1:
                w *= cv
            else:
                w *= (1 + cv)
    return w


@inline
def eqtree(point_ptr, out, n_coords: Const):
    # The eq tensor of the n_coords challenges at point_ptr[0..n_coords), built by
    # doubling into out (size 2^(n_coords+1) - 2); the final 2^n_coords values start
    # at offset 2^n_coords - 2.
    r0 = point_ptr[GEN ** 0]
    out[GEN ** 0] = 1 + r0
    out[GEN ** 1] = r0
    for t in unroll(1, n_coords):
        rt = point_ptr[GEN ** t]
        one_plus_rt = 1 + rt
        for i in unroll(0, 2 ** t):
            pw = out[GEN ** (2 ** t - 2 + i)]
            out[GEN ** (2 ** (t + 1) - 2 + i)] = pw * one_plus_rt
            out[GEN ** (2 ** (t + 1) - 2 + 2 ** t + i)] = pw * rt
    return


@inline
def lag64(z, out, node_base: Const):
    # The 64 phi8-domain Lagrange NUMERATORS at z over nodes
    # PHI8_NODES[node_base .. node_base + 64]: out[i] = prod_{j != i} (z +
    # PHI8_NODES[node_base + j]). Every barycentric denominator over an aligned phi8
    # window is the same element, so callers scale the finished sum once by
    # LAGRANGE_INV_S / LAGRANGE_INV_COMBINED instead of the numerators one by one.
    pre = StackBuf(65)
    pre[0] = 1
    for i in unroll(0, 64):
        pre[i + 1] = pre[i] * (z + PHI8_NODES[node_base + i])
    suf = StackBuf(65)
    suf[64] = 1
    for i in unroll(0, 64):
        suf[63 - i] = suf[64 - i] * (z + PHI8_NODES[node_base + 63 - i])
    for i in unroll(0, 64):
        out[i] = pre[i] * suf[i + 1]
    return


def eq_prefix_chain(chain, seed, a, b, count_g):
    # Prefix products of eq(a_k, b_k) = 1 + a_k + b_k from `seed`, so a reader picks
    # the partial product up at its own certified length. Entry t is written from
    # inputs with index < t only, so a garbage tail past a buffer's written extent
    # cannot corrupt any shorter prefix.
    chain[GEN ** 0] = seed
    for xk in mul_range(1, count_g):
        chain[xk * GEN] = chain[xk] * (1 + a[xk] + b[xk])
    return


def rs_eq_run(chain, z_vals, point, count_g):
    # One run of the telescoped ring-switch product E = sum_k c_k * prod_j
    # (z_j^(2^k) + 1 + ris_j): coordinate x multiplies row k by (z^(2^k) + 1 +
    # point_x), z evolving by squaring per row. The runtime coordinates walk
    # OUTSIDE and the fixed Frobenius powers inside, so nothing stores a z-power
    # table.
    for xk in mul_range(1, count_g):
        zv = z_vals[xk]
        one_plus = 1 + point[xk]
        row = chain * xk ** BASE_FIELD_BITS
        nxt = row * GEN ** BASE_FIELD_BITS
        for k in unroll(0, BASE_FIELD_BITS):
            nxt[GEN ** k] = row[GEN ** k] * (zv + one_plus)
            if k != BASE_FIELD_BITS - 1:
                zv *= zv
    return


@inline
def fold_final_msg(msg, weights, log_len: Const):
    # Weighted fold of the final_msg multilinear over 2^log_len values (log_len is
    # the candidate's yr_log_n; the frame buffers use the global max size).
    l0 = StackBuf(2 ** YR_LOG_CAP)
    for t in unroll(0, 2 ** log_len // 2):
        l0[t] = weights[0] * msg[GEN ** (2 * t)] + weights[1] * msg[GEN ** (2 * t + 1)]
    cursor = l0
    n = 2 ** log_len // 2
    for j in unroll(1, log_len):
        nxt = StackBuf(2 ** YR_LOG_CAP)
        for t in unroll(0, n // 2):
            nxt[t] = weights[2 * j] * cursor[2 * t] + weights[2 * j + 1] * cursor[2 * t + 1]
        cursor = nxt
        n = n // 2
    return cursor[0]


def sumcheck_round4(state_0, state_1, msg_cursor, claim):
    # One PLAIN sumcheck round. The prover sends the round polynomial's coefficients
    # bar the one the split h(0) + h(1) == claim fixes, so the verifier derives that
    # one and reads h at the challenge by Horner. Nothing is reapplied: no eq
    # factor, no separate term for the tables still waiting, and the eq point is not
    # read here at all.
    fs = [state_0, state_1]
    fs, c0, msg_cursor = fs_next(fs, msg_cursor)
    fs, c2, msg_cursor = fs_next(fs, msg_cursor)
    fs, c3, msg_cursor = fs_next(fs, msg_cursor)
    c1 = claim + c2 + c3  # the split identity fixes it, so it is neither sent nor bound
    fs, y = squeeze(fs)
    return fs[0], fs[1], msg_cursor, c0 + y * (c1 + y * (c2 + y * c3)), y


def sumcheck_round5(state_0, state_1, msg_cursor, claim, prev_challenge):
    # One GKR round. The prover sends every coefficient but c0, which the round's
    # pulled-out eq factor leaves fixed: `c0 + prev_challenge * (c1 + ... + c4) ==
    # claim`.
    fs = [state_0, state_1]
    fs, c1, msg_cursor = fs_next(fs, msg_cursor)
    fs, c2, msg_cursor = fs_next(fs, msg_cursor)
    fs, c3, msg_cursor = fs_next(fs, msg_cursor)
    fs, c4, msg_cursor = fs_next(fs, msg_cursor)
    fs, y = squeeze(fs)
    c0 = claim + prev_challenge * (c1 + c2 + c3 + c4)
    return fs[0], fs[1], msg_cursor, c0 + y * (c1 + y * (c2 + y * (c3 + y * c4))), y


def batch_sumcheck(fs0, fs1, msgs, running, point, n_rounds: Const):
    # The rounds of a claim-batching sumcheck: two hinted coefficients a round
    # (g(1) and g(inf)), the split fixing the third against the running claim, and
    # the challenges collected into `point`.
    fs = [fs0, fs1]
    for rd in unroll(0, n_rounds):
        fs, msg_g1, c = fs_next(fs, msgs * GEN ** (2 * rd))
        fs, msg_ginf, c = fs_next(fs, c)
        fs, rv = squeeze(fs)
        point[GEN ** rd] = rv
        g_zero = running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        running = (msg_ginf * rv + c_one) * rv + g_zero  # fold the degree-2 round at rv
    return fs[0], fs[1], running


# ==================================== Merkle paths ==================================


@inline
def order_children(node, sibling, bit):
    # Branchless child ordering: `bit` is boolean-pinned wherever it comes from, so
    # `m = bit*(node + sibling)` selects rather than branches, leaving (node,
    # sibling) at bit 0 and (sibling, node) at bit 1.
    m = bit * (node + sibling)
    kids = [node + m, sibling + m]
    return kids


@inline
def verify_merkle_path(leaf_0, leaf_1, path_ptr, direction_bits, depth: Const):
    # A two-cell PCS leaf up to its level root; the query index's bit at each level
    # orders the two children.
    node_0 = leaf_0
    node_1 = leaf_1
    for level in unroll(0, depth):
        dir_bit = direction_bits[GEN ** level]
        diff_0 = node_0 + path_ptr[GEN ** (2 * level)]
        diff_1 = node_1 + path_ptr[GEN ** (2 * level + 1)]
        left = [node_0 + dir_bit * diff_0, node_1 + dir_bit * diff_1]
        right = [diff_0 + left[0], diff_1 + left[1]]
        parent = StackBuf(2)
        blake2s(left, right, parent)
        node_0 = parent[0]
        node_1 = parent[1]
    return node_0, node_1


# ============================== the stacked WHIR opening ============================


def open_stacked(m_idx: Const, fs0, fs1, target, commit_root_0, commit_root_1, cursor):
    # The stacked WHIR opening, one specialization per (rate, committed log-size)
    # candidate: every LIG_* table reads row m_idx, per level row `ml`, and all
    # opening proof data is hinted here, so only the executed arm pops its streams.
    #
    # Returns sumcheck_target, point_fold, inner_total, g^yr_log_n,
    # g^(YR_LOG_CAP - yr_log_n), g^lenris, point_tail, yr_at_tail. The two g-powers
    # let the terminal zero-pin residual coordinates past final_msg's 2^yr_log_n
    # cells; g^lenris is the certified fold count it pins its claim lengths against.
    #
    # point_fold/point_tail index that point by WITNESS coordinate (see the rotation
    # below), which is what every transparent weight downstream is written in. The
    # ROUND-order buffers fold_challenges/tail_challenges stay local on purpose:
    # everything reading the point in round order (per-level induced weights, OOD
    # claim points, the residual yr_at_tail) is computed here, and a new round-order
    # consumer that reached for the returned pair would silently evaluate its weight
    # at the wrong point.
    n_levels = LIG_N_LEVELS[m_idx]
    yr_level = LIG_YR_LEVEL[m_idx]
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]
    max_q = LIG_MAX_QUERIES[m_idx]
    ood_stride = LIG_MAX_OOD_SAMPLES * OOD_SLOTS

    # The opening's scalars (sumcheck messages, level roots, nonces, final message)
    # ride the SHARED stream, walked on in protocol order. The K opener binds a
    # Merkle root as its two F192 scalars, not as a byte string, and every digest
    # uses ONE 128/128 encoding, so those scalars are exactly the root's two cells.
    fs = [fs0, fs1]
    msg_cursor = cursor
    fs, round_quad_c, msg_cursor = fs_next(fs, msg_cursor)  # the round polynomial in coefficients
    fs, round_quad_a, msg_cursor = fs_next(fs, msg_cursor)  # bar the linear one, which the split fixes
    round_quad_b = target + round_quad_a
    sumcheck_target = target

    # Opening data for every level, all consumed by the level loop below (each
    # buffer is one flat run indexed by the baked LIG_*_OFF[ml] offsets). It lives
    # here, before the loop, because the loop is unrolled per level, so a per-level
    # declaration inside would be replicated. Hinted proof data:
    merkle_leaf_rows = HeapBuf(GEN ** (LIG_ROWS_LEN[m_idx]))
    hint_witness(merkle_leaf_rows[0:LIG_ROWS_LEN[m_idx]], "merkle_leaf_rows")
    merkle_paths = HeapBuf(GEN ** (LIG_PATHS_LEN[m_idx]))
    hint_witness(merkle_paths[0:LIG_PATHS_LEN[m_idx]], "merkle_paths")
    final_msg = HeapBuf(GEN ** yr_len)  # filled from the stream at the last level
    # Level roots, two cells a level: slot 0 is the commitment root (bound above),
    # the rest are filled as each root is read off the stream. Every query then
    # checks its walk with ONE heap store per digest cell, the write-once equality,
    # with no level-0 special case.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # ...and guest-filled accumulators (one slot per fold / per level / per query):
    fold_challenges = HeapBuf(GEN ** n_folds)
    level_betas = HeapBuf(GEN ** n_levels)
    query_weights = HeapBuf(GEN ** (n_levels * max_q))
    query_positions = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    query_bit_ptrs = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    # Explicit OOD claims bind every recursive Johnson-list commitment. L0 needs
    # none: the opening claim itself is its post-commit binding value. An OOD claim
    # is read before its level's query positions but batched after them (one
    # challenge per level), so its value and intro message wait here.
    ood_z = HeapBuf(GEN ** (n_levels * LIG_MAX_OOD_SAMPLES * LIG_LOG_MSG_COLS_CAP))
    ood = HeapBuf(GEN ** (n_levels * ood_stride))

    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        n_queries = LIG_QUERIES[ml]
        depth = LIG_TREE_DEPTH[ml]
        interleave = LIG_INTERLEAVE[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        pos_off = LIG_POSITIONS_OFF[ml]
        for j in unroll(0, LIG_FOLDS[ml]):
            fs, fold_challenge = squeeze(fs)
            fold_challenges[GEN ** (folds_off + j)] = fold_challenge
            # evaluate this level's folded quadratic at the fold challenge
            sumcheck_target = (round_quad_a * fold_challenge + round_quad_b) * fold_challenge + round_quad_c
            fs, round_quad_c, msg_cursor = fs_next(fs, msg_cursor)  # the round polynomial in coefficients
            fs, round_quad_a, msg_cursor = fs_next(fs, msg_cursor)  # bar the linear one
            round_quad_b = sumcheck_target + round_quad_a  # the split fixes it against the running claim

        if lvl == yr_level:
            for iy in unroll(0, yr_len):
                fs, yv, msg_cursor = fs_next(fs, msg_cursor)
                final_msg[GEN ** iy] = yv
        else:
            fs, next_root_a, msg_cursor = fs_next(fs, msg_cursor)
            fs, next_root_b, msg_cursor = fs_next(fs, msg_cursor)
            # A non-canonical half is rejected (merkle.rs `scalars_to_hash`), as
            # the commitment root was at its own read.
            canon = StackBuf(2)
            canon[0] = assert_canonical(next_root_a)
            canon[1] = assert_canonical(next_root_b)
            level_roots[GEN ** (2 * lvl + 2)] = next_root_a
            level_roots[GEN ** (2 * lvl + 3)] = next_root_b
            # OOD binding for the newly observed level-(lvl+1) commitment. The
            # random point has the just-folded witness dimension, namely this
            # level's message-column dimension.
            for os in unroll(0, LIG_OOD_SAMPLES[ml + 1]):
                oz = ood_z * GEN ** (((lvl + 1) * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
                for t in unroll(0, LIG_LOG_MSG_COLS[ml]):
                    fs, oz_challenge = squeeze(fs)
                    oz[GEN ** t] = oz_challenge
                sample = ood * GEN ** ((lvl + 1) * ood_stride + os * OOD_SLOTS)
                fs, ood_y, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_c0, msg_cursor = fs_next(fs, msg_cursor)
                fs, ood_c2, msg_cursor = fs_next(fs, msg_cursor)
                sample[GEN ** OOD_Y] = ood_y
                sample[GEN ** OOD_C0] = ood_c0
                sample[GEN ** OOD_C2] = ood_c2  # the split fixes c1 = y + c2
        q_nonce = msg_cursor[GEN ** 0]  # raw transport word: bound by the DS_POW_NONCE absorb below
        msg_cursor = msg_cursor * GEN
        if LIG_QUERY_GRIND_BITS[ml] != 0:
            grind_check(fs[0], fs[1], q_nonce, GEN ** LIG_QUERY_GRIND_BITS[ml])
        else:
            assert q_nonce == 0
        fs = absorb_nonce(fs, q_nonce)

        sqz = HeapBuf((GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1)) ** PAIR_SLOTS)
        sqz[GEN ** 0] = fs[0]
        sqz[GEN ** 1] = fs[1]
        for xs in mul_range(1, GEN ** LIG_SQUEEZES[ml]):
            # a loop body captures free names BY VALUE, so the compile-time aliases
            # are rebound here (m_idx and lvl are substituted literals)
            depth = LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl]
            pos_off = LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl]
            row = sqz * xs ** PAIR_SLOTS
            packed_word, next_c0, next_c1 = squeeze_step(row[GEN ** 0], row[GEN ** 1])
            row[GEN ** PAIR_SLOTS] = next_c0
            row[GEN ** (PAIR_SLOTS + 1)] = next_c1
            query_ptr = xs ** (FIELD_BITS // depth)
            decode_query_bits(packed_word, query_positions * GEN ** pos_off * query_ptr, query_bit_ptrs * GEN ** pos_off * query_ptr, depth)
        sqz_end = sqz * (GEN ** LIG_SQUEEZES[ml]) ** PAIR_SLOTS
        fs = [sqz_end[GEN ** 0], sqz_end[GEN ** 1]]

        # One batching challenge for the level, drawn once every claim it batches is
        # fixed: its OOD claims above and these query positions. Claim tau of the
        # level is weighted lam^tau, the running claim keeping lam^0 (Annex B,
        # Protocol 1 step 1): query i is claim n_ood + 1 + i, so its weight splits
        # into lam^i here and the level scalar lam^(n_ood+1) below.
        fs, lam = squeeze(fs)
        lam_pow = 1
        for i in unroll(0, n_queries):
            query_weights[GEN ** (lvl * max_q + i)] = lam_pow
            lam_pow = lam_pow * lam
        # At level 0, slot i of a leaf image is interleaving index n-1-i: the image
        # reads its lanes from the top down, so the lanes a padding-free commitment
        # leaves out are its LEADING words, whose whole blocks the committer hashes
        # once for all leaves. The flip is a compile-time index and the guest still
        # hashes the full image. Deeper levels commit every lane, ascending.
        row_eq_weights = HeapBuf(GEN ** (LIG_MAX_INTERLEAVE[m_idx]))
        for i in unroll(0, interleave):
            if lvl == 0:
                slot = interleave - 1 - i
            else:
                slot = i
            row_eq_weights[GEN ** i] = eq_weight(fold_challenges * GEN ** folds_off, LIG_FOLDS[ml], slot, 0)

        query_sum_chain = HeapBuf(GEN ** (max_q + 1))
        query_sum_chain[GEN ** 0] = 0
        for xe in mul_range(1, GEN ** n_queries):
            ml = m_idx * LIG_MAX_LEVELS + lvl  # rebound: the body captures by value
            interleave = LIG_INTERLEAVE[ml]
            depth = LIG_TREE_DEPTH[ml]
            pos_off = LIG_POSITIONS_OFF[ml]
            max_q = LIG_MAX_QUERIES[m_idx]
            if lvl == 0:
                row_base = xe ** interleave
            else:
                row_base = xe ** (3 * interleave)
            row_ptr = merkle_leaf_rows * GEN ** LIG_ROWS_OFF[ml] * row_base
            row_dot = 0
            packed_row = StackBuf(LIG_PACKED_ROW_CAP)
            if lvl == 0:
                # Level-0 rows are base-field F64, embedded one per word. Pack the
                # lanes into a contiguous run of canonical 128-bit cells for the
                # standard leaf hash; the dot consumes the individual lanes. The
                # untaken JUMP reads both source cells through the memory bus as
                # `(lo, 0, 0)`, so the packing helpers also prove every hinted lane
                # is genuinely F64 before it enters the hash or row_dot.
                for jb in unroll(0, interleave // 4):
                    e0 = row_ptr[GEN ** (4 * jb)]
                    e1 = row_ptr[GEN ** (4 * jb + 1)]
                    e2 = row_ptr[GEN ** (4 * jb + 2)]
                    e3 = row_ptr[GEN ** (4 * jb + 3)]
                    packed_row[2 * jb] = pack64x2(e0, e1)
                    packed_row[2 * jb + 1] = pack64x2(e2, e3)
                    row_dot += e0 * row_eq_weights[GEN ** (4 * jb)] + e1 * row_eq_weights[GEN ** (4 * jb + 1)] + e2 * row_eq_weights[GEN ** (4 * jb + 2)] + e3 * row_eq_weights[GEN ** (4 * jb + 3)]
            else:
                # Higher-level F192 rows arrive as flat F64 tower limbs (three per
                # word); every serialized limb is constrained before reassembly and
                # packed into the contiguous 24-byte-per-word image the leaf hashes.
                # A pack holds `lane(2k) + Y*lane(2k+1)` exactly, so word w (limbs
                # 3w..3w+2) is one multiply-add off the pack covering its even
                # limb pair.
                lanes = StackBuf(LIG_PACKED_ROW_CAP)  # >= 3 limbs per word for every candidate
                for jl in unroll(0, 3 * interleave):
                    lanes[jl] = row_ptr[GEN ** jl]
                for jb in unroll(0, LIG_LEAF_PAIRS[ml]):
                    packed_row[2 * jb] = pack64x2(lanes[4 * jb], lanes[4 * jb + 1])
                    packed_row[2 * jb + 1] = pack64x2(lanes[4 * jb + 2], lanes[4 * jb + 3])
                for jw in unroll(0, interleave):
                    if 3 * jw % 2 == 0:
                        # limbs (3w, 3w+1) are a pack; add Y^2 * limb(3w+2).
                        row_word = packed_row[3 * jw // 2] + Y_TOWER * Y_TOWER * lanes[3 * jw + 2]
                    else:
                        # limbs (3w+1, 3w+2) are a pack; shift it by Y and add limb(3w).
                        row_word = lanes[3 * jw] + Y_TOWER * packed_row[(3 * jw + 1) // 2]
                    row_dot += row_word * row_eq_weights[GEN ** jw]
            # Standard BLAKE2s of the packed row (a power of two of full 64-byte
            # blocks, within one 1024-byte chunk).
            leaf_hash_state = StackBuf(2)
            blake2s(packed_row[0:2], packed_row[2:4], leaf_hash_state, counter=64, final=1 // LIG_LEAF_BLOCKS[ml])
            for jb in unroll(1, LIG_LEAF_BLOCKS[ml]):
                leaf_digest = StackBuf(2)
                blake2s(packed_row[4 * jb:4 * jb + 2], packed_row[4 * jb + 2:4 * jb + 4], leaf_digest, cv=leaf_hash_state, counter=64 * (jb + 1), final=(jb + 1) // LIG_LEAF_BLOCKS[ml])
                leaf_hash_state = leaf_digest
            query_sum_chain[xe * GEN] = query_sum_chain[xe] + query_weights[GEN ** (lvl * max_q) * xe] * row_dot
            direction_bits = query_bit_ptrs[GEN ** pos_off * xe]
            path_ptr = merkle_paths * GEN ** LIG_PATHS_OFF[ml] * xe ** (2 * depth)
            # walk the query's Merkle path to the level root. A heap store IS the
            # equality assert here (`DerefMode::Cell` unifies the two cells, and the
            # slot holds this level's bound root already), at one instruction
            # instead of three.
            root_0, root_1 = verify_merkle_path(leaf_hash_state[0], leaf_hash_state[1], path_ptr, direction_bits, depth)
            level_roots[GEN ** (2 * lvl)] = root_0
            level_roots[GEN ** (2 * lvl + 1)] = root_1
        level_query_sum = query_sum_chain[GEN ** n_queries]

        # Every level, including the last, ties its commitment in through an intro
        # message. The level's claims then enter the running one with powers of
        # `lam`: the OOD claims held above first, then this query batch.
        fs, intro_c0, msg_cursor = fs_next(fs, msg_cursor)
        fs, intro_c2, msg_cursor = fs_next(fs, msg_cursor)
        intro_c1 = level_query_sum + intro_c2  # the split fixes the linear coefficient
        if lvl == yr_level:
            beta_lvl = lam  # no OOD claim at the last level: no new oracle
        else:
            ood_scalar = lam
            for os in unroll(0, LIG_OOD_SAMPLES[ml + 1]):
                sample = ood * GEN ** ((lvl + 1) * ood_stride + os * OOD_SLOTS)
                ood_y = sample[GEN ** OOD_Y]
                ood_c2 = sample[GEN ** OOD_C2]
                sample[GEN ** OOD_BETA] = ood_scalar
                round_quad_c += ood_scalar * sample[GEN ** OOD_C0]
                round_quad_b += ood_scalar * (ood_y + ood_c2)
                round_quad_a += ood_scalar * ood_c2
                sumcheck_target += ood_scalar * ood_y
                ood_scalar = ood_scalar * lam
            beta_lvl = ood_scalar
        level_betas[GEN ** lvl] = beta_lvl
        round_quad_c += beta_lvl * intro_c0
        round_quad_b += beta_lvl * intro_c1
        round_quad_a += beta_lvl * intro_c2
        sumcheck_target += beta_lvl * level_query_sum

    # ---- finish the sumcheck over the tail coordinates ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log - 1):
        fs, tail_c = squeeze(fs)
        tail_challenges[GEN ** j] = tail_c
        sumcheck_target = round_quad_c + tail_c * round_quad_b + tail_c * tail_c * round_quad_a
        fs, round_quad_c, msg_cursor = fs_next(fs, msg_cursor)
        fs, round_quad_a, msg_cursor = fs_next(fs, msg_cursor)
        round_quad_b = sumcheck_target + round_quad_a
    # The closing round sends no following message.
    fs, tail_last = squeeze(fs)
    tail_challenges[GEN ** (yr_log - 1)] = tail_last
    sumcheck_target = round_quad_c + tail_last * round_quad_b + tail_last * tail_last * round_quad_a
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    tail_w = StackBuf(2 * YR_LOG_CAP)
    for j in unroll(0, yr_log):
        tail_w[2 * j] = 1 + tail_challenges[GEN ** j]
        tail_w[2 * j + 1] = tail_challenges[GEN ** j]
    yr_at_tail = fold_final_msg(final_msg, tail_w, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The folds bind coordinates in ROUND order, and level 0's folds are the lane
    # fold, binding the witness's TOP k coordinates: lane l of the commitment is the
    # stack block q[l * 2^(mu-k) ...], which is what makes the witness's zero
    # padding whole lanes for the committer to leave out of the encode. Every
    # transparent weight downstream is written in witness coordinates, so rotate the
    # point left by those k rounds here, while the level shape is still
    # compile-time. One buffer holds the rotated run: point_fold names it and
    # point_tail the window past lenris.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    point_fold = HeapBuf(GEN ** (n_folds + YR_LOG_CAP))
    point_tail = point_fold * GEN ** n_folds
    for j in unroll(0, fold_head):
        point_fold[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point_fold[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point_fold[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
    for j in unroll(yr_log, YR_LOG_CAP):
        point_tail[GEN ** j] = 0

    # ---- per-level induced bases at the single terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates; only the novel-basis chain (the query position's
    # subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # fold coords then tail coords) and each query is one multiply-add a
    # coordinate.
    basis_a = HeapBuf(GEN ** (n_levels * LIG_LOG_MSG_COLS_CAP))
    basis_b = HeapBuf(GEN ** (n_levels * LIG_LOG_MSG_COLS_CAP))
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            basis_a[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] = 1 + fold_c
            basis_b[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] = fold_c * LIG_VANISH_INVS[vanish + t]
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            basis_a[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + prefix_len + j)] = 1 + tail_c
            basis_b[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + prefix_len + j)] = tail_c * LIG_VANISH_INVS[vanish + prefix_len + j]
    inner_chain = HeapBuf(GEN ** (n_levels + 1))
    inner_chain[GEN ** 0] = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        basis_row = lvl * LIG_LOG_MSG_COLS_CAP
        residual_chain = HeapBuf(GEN ** (max_q + 1))
        residual_chain[GEN ** 0] = 0
        for xr in mul_range(1, GEN ** LIG_QUERIES[ml]):
            ml = m_idx * LIG_MAX_LEVELS + lvl  # rebound: the body captures by value
            vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
            basis_row = lvl * LIG_LOG_MSG_COLS_CAP
            max_q = LIG_MAX_QUERIES[m_idx]
            basis_chain = query_positions[GEN ** LIG_POSITIONS_OFF[ml] * xr]
            prefix_eq = basis_a[GEN ** basis_row] + basis_b[GEN ** basis_row] * basis_chain
            for t in unroll(1, LIG_LOG_MSG_COLS[ml]):
                # subspace-vanishing recurrence for the novel-basis point
                basis_chain *= (basis_chain + LIG_VANISH_VALS[vanish + t - 1])
                prefix_eq *= basis_a[GEN ** (basis_row + t)] + basis_b[GEN ** (basis_row + t)] * basis_chain
            residual_chain[xr * GEN] = residual_chain[xr] + query_weights[GEN ** (lvl * max_q)* xr] * prefix_eq
        # accumulate beta_lvl * (per-level residual sum) into the grand residual
        inner_chain[GEN ** (lvl + 1)] = inner_chain[GEN ** lvl] + level_betas[GEN ** lvl] * residual_chain[GEN ** LIG_QUERIES[ml]]

    # Explicit OOD eq bases at the same terminal point.
    ood_inner = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        for os in unroll(0, LIG_OOD_SAMPLES[ml]):
            oz = ood_z * GEN ** ((ood_lvl * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
            scalar = ood[GEN ** (ood_lvl * ood_stride + os * OOD_SLOTS + OOD_BETA)]
            for t in unroll(0, z_folded):
                scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
            for t in unroll(0, yr_log):
                scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
            ood_inner += scalar
    return sumcheck_target, point_fold, inner_chain[GEN ** n_levels] + ood_inner, GEN ** yr_log, GEN ** (YR_LOG_CAP - yr_log), GEN ** n_folds, point_tail, yr_at_tail


# ============================== inner-proof verification ============================
# The phases of `verify_sub`, in the order it runs them. Each takes and returns the
# Fiat-Shamir state pair and the stream cursor, so the sequence is what binds them.


def verify_bus_gkr(fs0, fs1, cursor, g_bus_mu, zeta):
    # ONE GKR grand product over push, pull and count, RLC-batched. Push and pull
    # have equal depth (matched blocks) and the count tree is padded with identity
    # leaves up to it (product unchanged), so a single sumcheck serves all three.
    # Radix four contracts two binary levels per layer; after checking the combined
    # product identity, a fresh λ pins the individual values. All three trees reduce
    # to the one shared point `zeta`, which this fills, returning their three leaf
    # values with the walked Fiat-Shamir state and stream cursor.
    layers = HeapBuf((g_bus_mu * GEN ** 2) ** LAYER_SLOTS)  # mu + 2 layers
    rounds = HeapBuf(GKR_ROUNDS_CAP * ROUND_SLOTS)
    gkr_pts = HeapBuf(GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    fs = [fs0, fs1]
    fs, root_push, cursor = fs_next(fs, cursor)
    root_pull = root_push
    fs, root_count, cursor = fs_next(fs, cursor)
    assert root_count != 0  # count-tree root nonzero: no read count self-cancels
    fs, root_lambda = squeeze(fs)
    layers[GEN ** LAYER_FS0] = fs[0]
    layers[GEN ** LAYER_FS1] = fs[1]
    layers[GEN ** LAYER_CURSOR] = cursor
    layers[GEN ** LAYER_PUSH] = root_push
    layers[GEN ** LAYER_PULL] = root_pull
    layers[GEN ** LAYER_COUNT] = root_count
    layers[GEN ** LAYER_LAMBDA] = root_lambda  # λ over the three roots
    layers[GEN ** LAYER_ROW] = gkr_pts
    layers[GEN ** LAYER_POS] = GEN ** 0

    # Contract two binary product levels at a time. pair_bounds[g^d] = g^(d//2) is
    # the radix-four layer count, and shift is g exactly when the depth is odd, in
    # which case the root-most BINARY layer runs first.
    pair_bounds = HeapBuf(COUNT_BITS)
    depth_shift = HeapBuf(COUNT_BITS)
    for depth in unroll(0, COUNT_BITS):
        pair_bounds[GEN ** depth] = GEN ** (depth // 2)
        depth_shift[GEN ** depth] = GEN ** (depth % 2)

    if depth_shift[g_bus_mu] != 1:
        # The odd layer is layer 0, so its round state would be written and read
        # back at the same position: read it straight off the layer instead.
        lam = layers[GEN ** LAYER_LAMBDA]
        tail_fs = [layers[GEN ** LAYER_FS0], layers[GEN ** LAYER_FS1]]
        tcur = layers[GEN ** LAYER_CURSOR]
        tclaim = layers[GEN ** LAYER_PUSH] + lam * (layers[GEN ** LAYER_PULL] + lam * layers[GEN ** LAYER_COUNT])
        nextrow = layers[GEN ** LAYER_ROW] * GEN ** MU_CAP
        evals = StackBuf(2 * N_GKR_SIDES)  # the two children of each side, in side order
        for i in unroll(0, 2 * N_GKR_SIDES):
            tail_fs, ev, tcur = fs_next(tail_fs, tcur)
            evals[i] = ev
        combined = 0
        for i in unroll(0, N_GKR_SIDES):
            side = N_GKR_SIDES - 1 - i  # Horner in lam, so the top side lands last
            combined = evals[2 * side] * evals[2 * side + 1] + lam * combined
        assert tclaim == combined
        tail_fs, c0 = squeeze(tail_fs)
        nextrow[GEN ** 0] = c0
        tail_fs, tail_lambda = squeeze(tail_fs)  # fresh λ pins the tail individuals
        nxt = layers * GEN ** LAYER_SLOTS
        nxt[GEN ** LAYER_FS0] = tail_fs[0]
        nxt[GEN ** LAYER_FS1] = tail_fs[1]
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            nxt[GEN ** (LAYER_PUSH + side)] = evals[2 * side] + c0 * (evals[2 * side] + evals[2 * side + 1])
        nxt[GEN ** LAYER_LAMBDA] = tail_lambda
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN

    for x_pair in mul_range(1, pair_bounds[g_bus_mu]):
        x_layer = x_pair * x_pair * depth_shift[g_bus_mu]
        layer = layers * x_layer ** LAYER_SLOTS
        lam = layer[GEN ** LAYER_LAMBDA]
        point_row = layer[GEN ** LAYER_ROW]
        round_pos = layer[GEN ** LAYER_POS]
        nextrow = point_row * GEN ** MU_CAP
        head = rounds * round_pos ** ROUND_SLOTS
        head[GEN ** ROUND_FS0] = layer[GEN ** LAYER_FS0]
        head[GEN ** ROUND_FS1] = layer[GEN ** LAYER_FS1]
        head[GEN ** ROUND_CURSOR] = layer[GEN ** LAYER_CURSOR]
        head[GEN ** ROUND_CLAIM] = layer[GEN ** LAYER_PUSH] + lam * (layer[GEN ** LAYER_PULL] + lam * layer[GEN ** LAYER_COUNT])
        for x_round in mul_range(1, x_layer):
            rd = rounds * (round_pos * x_round) ** ROUND_SLOTS
            nfs0, nfs1, ncur, nclaim, rk = sumcheck_round5(rd[GEN ** ROUND_FS0], rd[GEN ** ROUND_FS1], rd[GEN ** ROUND_CURSOR], rd[GEN ** ROUND_CLAIM], point_row[x_round])
            nextrow[x_round * GEN ** 2] = rk
            rd_next = rd * GEN ** ROUND_SLOTS
            rd_next[GEN ** ROUND_FS0] = nfs0
            rd_next[GEN ** ROUND_FS1] = nfs1
            rd_next[GEN ** ROUND_CURSOR] = ncur
            rd_next[GEN ** ROUND_CLAIM] = nclaim
        tail = rounds * (round_pos * x_layer) ** ROUND_SLOTS
        tail_fs = [tail[GEN ** ROUND_FS0], tail[GEN ** ROUND_FS1]]
        tcur = tail[GEN ** ROUND_CURSOR]
        tclaim = tail[GEN ** ROUND_CLAIM]
        evals = StackBuf(4 * N_GKR_SIDES)  # the four children of each side, in side order
        for i in unroll(0, 4 * N_GKR_SIDES):
            tail_fs, ev, tcur = fs_next(tail_fs, tcur)
            evals[i] = ev
        combined = 0
        for i in unroll(0, N_GKR_SIDES):
            side = N_GKR_SIDES - 1 - i  # Horner in lam, so the top side lands last
            combined = evals[4 * side] * evals[4 * side + 1] * evals[4 * side + 2] * evals[4 * side + 3] + lam * combined
        assert tclaim == combined
        tail_fs, c0 = squeeze(tail_fs)
        tail_fs, c1 = squeeze(tail_fs)
        nextrow[GEN ** 0] = c0
        nextrow[GEN ** 1] = c1
        tail_fs, tail_lambda = squeeze(tail_fs)
        nxt = layer * GEN ** (2 * LAYER_SLOTS)
        nxt[GEN ** LAYER_FS0] = tail_fs[0]
        nxt[GEN ** LAYER_FS1] = tail_fs[1]
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            lo = evals[4 * side] + c0 * (evals[4 * side] + evals[4 * side + 1])
            hi = evals[4 * side + 2] + c0 * (evals[4 * side + 2] + evals[4 * side + 3])
            nxt[GEN ** (LAYER_PUSH + side)] = lo + c1 * (lo + hi)
        nxt[GEN ** LAYER_LAMBDA] = tail_lambda
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = round_pos * x_layer * GEN
    last = layers * g_bus_mu ** LAYER_SLOTS
    fs = [last[GEN ** LAYER_FS0], last[GEN ** LAYER_FS1]]
    cursor = last[GEN ** LAYER_CURSOR]
    final_point_row = last[GEN ** LAYER_ROW]
    for xt in mul_range(1, g_bus_mu):
        zeta[xt] = final_point_row[xt]  # the ONE shared point
    return fs[0], fs[1], cursor, last[GEN ** LAYER_PUSH], last[GEN ** LAYER_PULL], last[GEN ** LAYER_COUNT]


def verify_tables(fs0, fs1, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, block_kappa, g_squares, fp_w, beta, claim_pool, claim_cplen_g, chi, claim_push, claim_pull, claim_count):
    # Settle the bus against the six tables, in four steps: certify each side's
    # leaf-cube tiling, decompose the three GKR leaf values over it, run the ONE
    # table sumcheck they all reduce to, and bind the public input. Pooled claims
    # land in claim_pool/claim_cplen_g and the reduced point in `chi`; the batch's
    # round count g^n, the deferred bytecode share and the PI point come back.
    #
    # Bus-leaf packing offsets, for the selector certification. Each side's blocks
    # tile its leaf cube, block b at offset_b; the hinted order is only
    # PERMUTATION-checked and offsets accumulate as g^offset = Π_{earlier} g^(2^κ).
    # The decompose below pins each block's selector bits against this offset,
    # forcing κ-alignment, and no sort or tie-break check is needed: alignment plus
    # consecutive offsets force a valid tiling, and the grand product is
    # position-independent, so any tiling is sound. Pull's blocks mirror push's and
    # share zeta, so only push and count need offsets (pull's slots go unread).
    fs = [fs0, fs1]
    gkr_claims = StackBuf(N_GKR_SIDES)
    gkr_claims[PUSH_SIDE] = claim_push
    gkr_claims[PULL_SIDE] = claim_pull
    gkr_claims[COUNT_SIDE] = claim_count
    sort_order = HeapBuf(N_BLOCKS)
    hint_witness(sort_order[0:N_BLOCKS], "sort_order")
    block_side_tab = HeapBuf(N_BLOCKS)  # global block -> its side
    for b in unroll(0, N_BLOCKS):
        block_side_tab[GEN ** b] = BLOCK_SIDE[b]
    block_off_g = HeapBuf(N_BLOCKS)  # g^offset per block, keyed by global index
    for cert in unroll(0, 2):
        s = COUNT_SIDE * cert  # PUSH_SIDE (0), then COUNT_SIDE (2)
        g_off = GEN ** 0
        for r in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            global_g = sort_order[GEN ** r]       # g^{global block index at this rank}
            assert log(global_g) < N_BLOCKS       # a valid block index
            assert block_side_tab[global_g] == s  # ...belonging to THIS side
            # write-once: a repeat collides, and an omission fails the decompose's
            # offset read below
            block_off_g[global_g] = g_off
            g_off *= g_squares[block_kappa[global_g]]

    # ---- 3x leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); Index
    # coordinates use the factored index MLE; and the program's whole share of a
    # bytecode leaf is ONE evaluation of the stacked polynomial, since its slots are
    # aligned with the tuple and the weights are eq(α⃗, ·), so the share IS that
    # polynomial at (ζ_lo, α⃗) (doc sec:e2e-bc): one hinted value, exported as a
    # deferred claim, with no per-coordinate values and no selector challenge.
    #
    # Pull's blocks mirror push's (same kappas, same offsets, generator-asserted
    # pairing) and share zeta, so each pull block REUSES its push twin's eq_hi and
    # Index-MLE value instead of recomputing them; its column values are mostly
    # deduped pool reads (COORD_FRESH). The identity check against pull's own GKR
    # claim still binds everything.
    bc_share = hint_witness("bytecode_val")
    idxc_tab = HeapBuf(SIZE_BITS)  # INDEX_MLE_FACTORS[t] = 1 + g^(2^t)
    for t in unroll(0, SIZE_BITS):
        idxc_tab[GEN ** t] = INDEX_MLE_FACTORS[t]
    bus_table_total = StackBuf(N_GKR_SIDES)  # per side, what its tables' blocks owe
    block_eq_hi = StackBuf(N_BLOCKS)         # every block's eq_hi, reused below
    block_index_mle = HeapBuf(N_BLOCKS)      # per push block with an Index coord
    for s in unroll(0, N_GKR_SIDES):
        acc = 0
        selector_sum = 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_has_public = 0
            kappa_g = block_kappa[GEN ** b]
            assert log(kappa_g) < SIZE_BITS
            if s == PULL_SIDE:
                eq_hi = block_eq_hi[b - SIDE_BLOCK_START[PULL_SIDE]]
            else:
                # eq_hi over the ζ coords above κ against the selector bits, whose
                # run is mu_s − κ = g^mu_s / g^κ long. Selector bits = offset >> κ:
                # advice-decompose the offset and read it shifted by κ. Rebuilding
                # g^offset from those high bits alone (weights g^(2^(κ+k))) and
                # asserting it equals block_off_g pins the bits AND the κ-alignment
                # in one shot; the low κ bit cells are written but never read.
                sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                assert log(sel_len_g) < SIZE_BITS
                zeta_hi = zeta * kappa_g
                offset_bits = HeapBuf(GEN ** SIZE_BITS)
                hint_decompose_bits_exponent(offset_bits, block_off_g[GEN ** b], SIZE_BITS)
                sel_bits = offset_bits * kappa_g
                eq_chain = HeapBuf(MU_CAP + 2)
                goff_chain = HeapBuf(MU_CAP + 2)  # rebuild g^offset from the high bits
                eq_chain[GEN ** 0] = 1
                goff_chain[GEN ** 0] = 1
                for xk in mul_range(1, sel_len_g):
                    sbit = sel_bits[xk]
                    sel_bits[xk] = sbit * sbit  # booleanity as a write-once pin
                    eq_chain[xk * GEN] = eq_chain[xk] * (1 + sbit + zeta_hi[xk])  # eq over GF(2) is 1 + b + z
                    goff_chain[xk * GEN] = goff_chain[xk] * (1 + sbit * (g_squares[kappa_g * xk] + 1))
                eq_hi = eq_chain[sel_len_g]
                assert goff_chain[sel_len_g] == block_off_g[GEN ** b]  # bits == offset >> κ, κ-aligned
            selector_sum += eq_hi
            block_eq_hi[b] = eq_hi
            # A TABLE's block streams no value here: the table sumcheck settles its
            # fingerprint from that table's column evaluations. Only the framework
            # blocks (boundary, memory, bytecode) still decompose.
            if BLOCK_TABLE[b] == NO_TABLE:
                # inner fingerprint Σ_i w_i · coord_i(ζ_lo); the count side weighs
                # slot 0 alone (α⃗ = 0), γ = 0.
                inner_sum = 0
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                    if COORD_TYPE[ci] == COORD_KIND_CONST:
                        coord_val = COORD_CONST[ci]
                    if COORD_TYPE[ci] == COORD_KIND_COL:
                        if COORD_FRESH[ci] == 1:
                            fs, coord_val, cursor = fs_next(fs, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = coord_val
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g  # cplen = block kappa
                        else:
                            coord_val = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                    if COORD_TYPE[ci] == COORD_KIND_GCOL:
                        if COORD_FRESH[ci] == 1:
                            fs, rawv, cursor = fs_next(fs, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = rawv
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g
                        else:
                            rawv = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                        coord_val = COORD_CONST[ci] * rawv
                    if COORD_TYPE[ci] == COORD_KIND_INDEX:
                        if s == PULL_SIDE:
                            coord_val = block_index_mle[GEN ** (b - SIDE_BLOCK_START[PULL_SIDE])]
                        else:
                            # Index-coord MLE: prod_t (1 + zeta_t * (1 + g^(2^t)))
                            idx_chain = HeapBuf(MU_CAP + 2)
                            idx_chain[GEN ** 0] = 1
                            for xt in mul_range(1, kappa_g):
                                idx_chain[xt * GEN] = idx_chain[xt] * (1 + zeta[xt] * idxc_tab[xt])
                            coord_val = idx_chain[kappa_g]
                            if s == PUSH_SIDE:
                                block_index_mle[GEN ** b] = coord_val
                    if COORD_TYPE[ci] == COORD_KIND_PUBLIC:
                        # The public slots carry no value of their own here: their
                        # alpha-weighted sum IS bc_share, added once per block below
                        # (push and pull share zeta, so both get the same one).
                        coord_val = 0
                        block_has_public = 1
                    if s == COUNT_SIDE:
                        inner_sum += coord_val
                    else:
                        inner_sum += fp_w[GEN ** i] * coord_val
                inner_sum += block_has_public * bc_share  # the bytecode blocks' public slots
                if s == COUNT_SIDE:
                    acc += eq_hi * inner_sum
                else:
                    acc += eq_hi * (beta + inner_sum)
        acc += 1 + selector_sum
        # What the tables' blocks owe this side: its GKR leaf value less the
        # framework decomposition. DERIVED, not read: a transmitted total would be a
        # free value in its own check. The table sumcheck's target pins it below.
        bus_table_total[s] = acc + gkr_claims[s]
    claim_idx = N_BUS_CLAIMS  # AIR/PI/pin claims pool after the deduped bus claims

    # ---- ONE table sumcheck for all six tables ----
    # Mirrors lean_vm::constraints::verify. zc_xi ONCE, each table folding its own
    # identities with a DISJOINT range of its powers (ETA_OFFSET[t]); one shared
    # point zeta (the bus GKR's); n = max_t tau_t rounds. Rounds bind the HIGHEST
    # variable first, so a 2^tau table sits out the first n - tau and joins carrying
    # the challenges it sat out, weighing cprod[n - tau] * peq[tau] where peq[tau] =
    # eq(zeta[..tau], chi[..tau]); the zc_xi-powers are inside constraint_eval.
    #
    # g^n is hinted, then pinned exactly: the range-checked division slacks force it
    # to dominate every certified tau and the product identity forces it to BE one.
    g_zc_n = hint_witness("zc_tau_max")
    zc_is_a_tau = 1
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        assert log(g_zc_n / tau_g) < COUNT_BITS
        zc_is_a_tau *= g_zc_n + tau_g
    assert zc_is_a_tau == 0
    # n <= mu, the `Error::Truncated` of constraints.rs. Every table pushes at
    # kappa = tau, so it holds structurally, but zc_peq below reads zeta[..n] and
    # zeta only holds mu coords: unwritten heap there is prover-chosen.
    assert log(g_bus_mu / g_zc_n) < COUNT_BITS
    fs, zc_xi = squeeze(fs)
    zc_xi_pows = StackBuf(N_ETA_POWS)
    zc_xi_pows[0] = 1
    for k in unroll(1, N_ETA_POWS):
        zc_xi_pows[k] = zc_xi_pows[k - 1] * zc_xi
    # The eq point is the bus GKR's zeta, NOT a fresh one, which is what lets the
    # batch settle the bus forms alongside the constraints. It is also why no target
    # is read: what the three sides' tables owe, each in its own shared power of
    # zc_xi, IS the sum the batch must reach, and zc_xi is squeezed after those
    # totals are fixed, so hitting one number forces all three side equations.
    bus_target = 0
    for sd in unroll(0, N_GKR_SIDES):
        bus_target += zc_xi_pows[ETA_FORM_BASE + sd] * bus_table_total[sd]
    # n vanilla sumcheck rounds: the round polynomial arrives whole, so a round is
    # `h(0) + h(1) == claim` and a fold, with no eq to reapply. The tables still
    # waiting ride inside h, so nothing here is indexed by height; the heights enter
    # only the per-table weights below.
    zc_rounds = HeapBuf((g_zc_n * GEN) ** ROUND_SLOTS)
    zc_cprod = HeapBuf(g_zc_n * GEN)  # the challenges bound so far, multiplied
    zc_rounds[GEN ** ROUND_FS0] = fs[0]
    zc_rounds[GEN ** ROUND_FS1] = fs[1]
    zc_rounds[GEN ** ROUND_CURSOR] = cursor
    zc_rounds[GEN ** ROUND_CLAIM] = bus_target
    zc_cprod[GEN ** 0] = 1
    for xk in mul_range(1, g_zc_n):
        rd = zc_rounds * xk ** ROUND_SLOTS
        nfs0, nfs1, ncur, nclaim, rk = sumcheck_round4(rd[GEN ** ROUND_FS0], rd[GEN ** ROUND_FS1], rd[GEN ** ROUND_CURSOR], rd[GEN ** ROUND_CLAIM])
        chi[g_zc_n * INV_GEN / xk] = rk  # g^(n-1-j): the variable round j binds
        nxt = rd * GEN ** ROUND_SLOTS
        nxt[GEN ** ROUND_FS0] = nfs0
        nxt[GEN ** ROUND_FS1] = nfs1
        nxt[GEN ** ROUND_CURSOR] = ncur
        nxt[GEN ** ROUND_CLAIM] = nclaim
        # cprod is the weight of a table that joins here; peq below is the rest
        zc_cprod[xk * GEN] = zc_cprod[xk] * rk
    zc_last = zc_rounds * g_zc_n ** ROUND_SLOTS
    fs = [zc_last[GEN ** ROUND_FS0], zc_last[GEN ** ROUND_FS1]]
    cursor = zc_last[GEN ** ROUND_CURSOR]
    claim = zc_last[GEN ** ROUND_CLAIM]
    # peq[g^tau] = eq(zeta[..tau], chi[..tau]), as a prefix chain.
    zc_peq = HeapBuf(g_zc_n * GEN)
    zc_peq[GEN ** 0] = 1
    for xi in mul_range(1, g_zc_n):
        zc_peq[xi * GEN] = zc_peq[xi] * (1 + zeta[xi] + chi[xi])
    # Per table: every committed column's evaluation (pooled), its AIR constraint
    # at its own reduced point chi[..tau_t], weighted into the batch's final claim.
    air_acc = 0
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        col_evals = StackBuf(TABLE_COLS_CAP)
        for k in unroll(0, N_TABLE_COLS[t]):
            fs, e, cursor = fs_next(fs, cursor)
            col_evals[k] = e
            claim_pool[GEN ** claim_idx] = e
            claim_cplen_g[GEN ** claim_idx] = tau_g  # cplen = tau_t
            claim_idx += 1
        # The table's AIR constraint at the final point (col_evals is indexed by
        # local column index; the formulas mirror tables.rs eval_constraint). Every
        # value relation now rides the bus as a degree-2 coordinate, so only JUMP's
        # is-nonzero indicator is left with an identity of its own.
        constraint_eval = 0
        if t == TABLE_JUMP:
            # `b = c*w` and `c*(b+1) = 0`. The condition is K-valued, its memory read
            # carrying literal zeros above the low limb, so both identities are
            # single-lane (tables.rs jump_identity). Local columns: v_cond at 5, w at
            # 12, the indicator b at 13.
            c = col_evals[5]
            b = col_evals[13]
            constraint_eval = zc_xi_pows[ETA_OFFSET[t] + 0] * (b + c * col_evals[12])
            constraint_eval += zc_xi_pows[ETA_OFFSET[t] + 1] * (c * (b + 1))
        # The table's three bus forms, evaluated at the SAME column evaluations:
        # Σ_b eq_hi(b) · (γ + Σ_i α^i · coord_i), the coords read off col_evals at
        # their local index. This is what replaces opening those columns at ζ.
        for sd in unroll(0, N_GKR_SIDES):
            form = 0
            for b in unroll(0, N_BLOCKS):
                if BLOCK_SIDE[b] == sd:
                    if BLOCK_TABLE[b] == t:
                        inner = 0
                        for i in unroll(0, BLOCK_COORD_COUNT[b]):
                            # Each coord is the sum of its terms, over this table's
                            # column evaluations. A product term (an address, an
                            # arithmetic result) is degree 2, which the batch's
                            # round polynomial already allows.
                            ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                            cv = 0
                            for j in unroll(0, COORD_TERM_COUNT[ci]):
                                tj = COORD_TERM_OFF[ci] + j
                                if TERM_TYPE[tj] == COORD_KIND_CONST:
                                    cv += TERM_CONST[tj]
                                if TERM_TYPE[tj] == COORD_KIND_COL:
                                    cv += col_evals[TERM_COL_A[tj]]
                                if TERM_TYPE[tj] == COORD_KIND_GCOL:
                                    cv += TERM_CONST[tj] * col_evals[TERM_COL_A[tj]]
                                if TERM_TYPE[tj] == COORD_KIND_PROD:
                                    cv += TERM_CONST[tj] * (col_evals[TERM_COL_A[tj]] * col_evals[TERM_COL_B[tj]])
                            if sd == COUNT_SIDE:
                                inner += cv
                            else:
                                inner += fp_w[GEN ** i] * cv
                        if sd == COUNT_SIDE:
                            form += block_eq_hi[b] * inner
                        else:
                            form += block_eq_hi[b] * (beta + inner)
            constraint_eval += zc_xi_pows[ETA_FORM_BASE + sd] * form
        air_acc += zc_cprod[g_zc_n / tau_g] * zc_peq[tau_g] * constraint_eval  # cprod[n - tau] * peq[tau]
    assert air_acc == claim

    # ---- public-input binding claim: MEM as ONE logical E-column ----
    # The VM's bind_pi_claim makes a SINGLE E-claim at [rm, 0..]:
    #   MEM(rm) = interp(pi_0, pi_1, rm) = pi_0 + rm*(pi_0 + pi_1)
    # over the E-valued public input (no lane splitting, no Frobenius). Both
    # public words have a zero top limb, so that limb's evaluation is zero at
    # every rm; only the two low ones ride the stream and must reassemble it:
    # MEM = v_lo + Y*v_hi (doc sec:e2e-pi).
    fs, rm = squeeze(fs)
    mem = pi_0 + rm * (pi_0 + pi_1)
    fs, mem_lo, cursor = fs_next(fs, cursor)
    fs, mem_hi, cursor = fs_next(fs, cursor)
    assert mem == mem_lo + mem_hi * Y_TOWER
    claim_pool[GEN ** claim_idx] = mem_lo
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = mem_hi
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = 0
    claim_idx += 1
    return fs[0], fs[1], cursor, g_zc_n, bc_share, rm


def verify_flock(fs0, fs1, cursor, tau_blake2s_g, zerocheck_chis, lincheck_rs, z_partial):
    # Flock's zerocheck (univariate skip, k_skip = 6) then its lincheck, whose
    # matrix evaluation is DEFERRED to the caller's statement. The three run buffers
    # come in pre-sized; the point z, lincheck's alpha and the deferred matrix part
    # come back with the walked Fiat-Shamir state and stream cursor.
    #
    # tau's reach is bounded: the count gadget gives tau < 34 (every flock buffer is
    # sized for that), and q_flock's committed kappa = K_LOG + tau feeds the
    # certified size m, whose dispatch bound caps tau below any baked structure. The
    # first K_SKIP Boolean rounds are replaced by the univariate skip and consume no
    # equality challenges; the remaining r coordinates are N_FIXED_CHALLENGE_ROUNDS
    # fixed inner values then sampled outer ones. The prover builds round 1 from
    # this equality tail, so its sampled part is squeezed before round 1 is fetched,
    # and round 1 before z, which evaluates it.
    fs = [fs0, fs1]
    mr1cs_g = tau_blake2s_g * GEN ** K_LOG  # runtime m = K_LOG + tau_5, in the exponent
    zerocheck_r = HeapBuf(mr1cs_g)
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        zerocheck_r[GEN ** (K_SKIP + i)] = FIXED_CHALLENGES[i]
    flock_pts = HeapBuf((mr1cs_g * GEN ** 2) ** PAIR_SLOTS)
    seed = flock_pts * (GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS)) ** PAIR_SLOTS
    seed[GEN ** 0] = fs[0]
    seed[GEN ** 1] = fs[1]
    for xi in mul_range(GEN ** (K_SKIP + N_FIXED_CHALLENGE_ROUNDS), mr1cs_g):
        row = flock_pts * xi ** PAIR_SLOTS
        point_fs = [row[GEN ** 0], row[GEN ** 1]]
        point_fs, zerocheck_challenge = squeeze(point_fs)
        zerocheck_r[xi] = zerocheck_challenge
        row[GEN ** PAIR_SLOTS] = point_fs[0]
        row[GEN ** (PAIR_SLOTS + 1)] = point_fs[1]
    pts_last = flock_pts * mr1cs_g ** PAIR_SLOTS
    fs = [pts_last[GEN ** 0], pts_last[GEN ** 1]]
    # round-1 message (P = P^AB + P^C on Lambda, 2^K_SKIP words): fetch +
    # observe each word as it comes off the stream, then sample z.
    zc_round1 = HeapBuf(2 ** K_SKIP)
    for i in unroll(0, 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        zc_round1[GEN ** i] = w
    fs, zerocheck_z = squeeze(fs)  # cursor now sits at the multilinear round messages, walked below
    # P(z), interpolated at z over ALL 128 phi8 nodes: the transmitted Lambda values
    # (nodes 64..128) plus the S half, zero by the zerocheck identity. The finished
    # sum is scaled once by the domain's inverse denominator; the full-domain
    # product only adds the S-half factor to the Lambda numerators.
    lagrange_nums = StackBuf(2 ** K_SKIP)
    lag64(zerocheck_z, lagrange_nums, 2 ** K_SKIP)
    s_half_product = GEN ** 0
    zc_running = 0  # the zerocheck running claim entering the multilinear rounds
    for i in unroll(0, 2 ** K_SKIP):
        s_half_product *= (zerocheck_z + PHI8_NODES[i])
        zc_running += lagrange_nums[i] * zc_round1[GEN ** i]
    zc_running *= s_half_product * LAGRANGE_INV_COMBINED
    mr1cs_rounds_g = mr1cs_g * INV_GEN ** 6  # the multilinear rounds: m - 6
    for i in unroll(0, N_FIXED_CHALLENGE_ROUNDS):
        r_eq = zerocheck_r[GEN ** (K_SKIP + i)]
        fs, g_1, cursor = fs_next(fs, cursor)  # G's coefficients, bar the constant one
        fs, g_2, cursor = fs_next(fs, cursor)
        g_0 = zc_running + r_eq * (g_1 + g_2)  # the eq-weighted split fixes it
        fs, chi_v = squeeze(fs)
        zerocheck_chis[GEN ** i] = chi_v
        zc_running = g_0 + chi_v * (g_1 + chi_v * g_2)
    # the sampled rounds: K_LOG + tau_5 - K_SKIP in all, certified
    nmlv_g = tau_blake2s_g * GEN ** (K_LOG - K_SKIP)
    flock_rounds = HeapBuf((mr1cs_rounds_g * GEN ** 2) ** ROUND_SLOTS)
    seed = flock_rounds * (GEN ** N_FIXED_CHALLENGE_ROUNDS) ** ROUND_SLOTS
    seed[GEN ** ROUND_FS0] = fs[0]
    seed[GEN ** ROUND_FS1] = fs[1]
    seed[GEN ** ROUND_CURSOR] = cursor
    seed[GEN ** ROUND_CLAIM] = zc_running
    for xi in mul_range(GEN ** N_FIXED_CHALLENGE_ROUNDS, nmlv_g):
        rd = flock_rounds * xi ** ROUND_SLOTS
        round_fs = [rd[GEN ** ROUND_FS0], rd[GEN ** ROUND_FS1]]
        r_eq = zerocheck_r[GEN ** K_SKIP * xi]
        cur_i = rd[GEN ** ROUND_CURSOR]
        round_fs, g_1, cur_i = fs_next(round_fs, cur_i)  # coefficients, bar the constant one
        round_fs, g_2, cur_i = fs_next(round_fs, cur_i)
        g_0 = rd[GEN ** ROUND_CLAIM] + r_eq * (g_1 + g_2)  # the eq-weighted split fixes it
        round_fs, chi_v = squeeze(round_fs)
        zerocheck_chis[xi] = chi_v
        nxt = rd * GEN ** ROUND_SLOTS
        nxt[GEN ** ROUND_FS0] = round_fs[0]
        nxt[GEN ** ROUND_FS1] = round_fs[1]
        nxt[GEN ** ROUND_CURSOR] = cur_i
        nxt[GEN ** ROUND_CLAIM] = g_0 + chi_v * (g_1 + chi_v * g_2)
    fr_last = flock_rounds * nmlv_g ** ROUND_SLOTS
    fs = [fr_last[GEN ** ROUND_FS0], fr_last[GEN ** ROUND_FS1]]
    zc_running = fr_last[GEN ** ROUND_CLAIM]
    cursor = fr_last[GEN ** ROUND_CURSOR]  # walked past all 2*n_mlv round words, now at a_eval
    # final: observe a_eval, b_eval; the terminal identity is what defines
    # c_eval, so nothing is checked here. C rode the rounds above, so all three
    # claims sit at the same point and lincheck pins all three at once.
    fs, a_eval, cursor = fs_next(fs, cursor)
    fs, b_eval, cursor = fs_next(fs, cursor)
    c_eval = zc_running + a_eval * b_eval
    # The phi8 Lagrange weights at z over the S nodes: the quirky extension's
    # own combination, which the lincheck terminal applies to the 64 slices.
    claim_nums = StackBuf(2 ** K_SKIP)
    lag64(zerocheck_z, claim_nums, 0)

    # ---- flock lincheck (matrix evaluation DEFERRED) ----
    matrix_eval = hint_witness("matpart")
    fs, lincheck_alpha = squeeze(fs)
    lincheck_beta = lincheck_alpha * lincheck_alpha
    lincheck_cube = lincheck_beta * lincheck_alpha
    lc_running = a_eval + lincheck_alpha * b_eval + lincheck_beta * c_eval + lincheck_cube  # seed: a + alpha*b + alpha^2*c + alpha^3 (the two matrix claims, C, and the pin)
    for i in unroll(0, LINCHECK_ROUNDS):
        fs, c0, cursor = fs_next(fs, cursor)  # q's coefficients, bar the linear one
        fs, c2, cursor = fs_next(fs, cursor)
        c1 = lc_running + c2  # the split fixes it against the running claim
        fs, rv = squeeze(fs)
        lincheck_rs[GEN ** i] = rv
        lc_running = c0 + rv * (c1 + rv * c2)  # fold the degree-2 round poly at the challenge rv
    # post-sumcheck collapse: fetch + observe each word
    for i in unroll(0, 2 ** K_SKIP):
        fs, w, cursor = fs_next(fs, cursor)
        z_partial[GEN ** i] = w
    # final consistency: running == matpart (DEFERRED) + beta * pin term. The
    # const-pin column folds through the top-variable bindings: weight =
    # prod_j (bit_{klog-1-j}(PIN_COLUMN) ? r_j : 1+r_j), surviving z_partial index
    # = PIN_COLUMN low 6 bits.
    pin_term = lincheck_cube * eq_weight(lincheck_rs, LINCHECK_ROUNDS, PIN_COLUMN, K_LOG)
    pin_term *= z_partial[GEN ** (PIN_COLUMN % 2 ** K_SKIP)]
    # The C term. Its column weight is the row weight itself (C = I), and both
    # sides are tensors, so it collapses to eq(chi_in, chi_in_prime) times the
    # phi8 Lagrange combination of the 64 slices: no second matrix walk, no
    # second family.
    c_point_eq = GEN ** 0
    for t in unroll(0, LINCHECK_ROUNDS):
        c_point_eq *= (1 + zerocheck_chis[GEN ** t] + lincheck_rs[GEN ** (LINCHECK_ROUNDS - 1 - t)])
    c_slice_value = 0
    for i in unroll(0, 2 ** K_SKIP):
        c_slice_value += claim_nums[i] * z_partial[GEN ** i]
    c_slice_value *= LAGRANGE_INV_S
    # deferred matrix eval + pin + C
    assert lc_running == matrix_eval + pin_term + lincheck_beta * c_point_eq * c_slice_value
    # z_partial IS the claim: the terminal identity above pins its 64 slices, and
    # ring switching binds every one of them.
    return fs[0], fs[1], cursor, zerocheck_z, lincheck_alpha, matrix_eval


def certify_placement(kappa_base, g_squares, col_offset_bits):
    # Reconstruct the native committed-column placement. placements_of sorts
    # committed columns by descending kappa and then by ascending column index; the
    # hinted order is only transport, and the range checks, write-once dynamic
    # stores, descending-kappa slack and tie-break check certify that it is exactly
    # that canonical permutation. Offsets accumulate as g^offset *= g^(2^kappa), and
    # `col_offset_bits` receives each one's exact bit decomposition. Returns
    # g^(sum 2^kappa), which the caller turns into the stacked size m.
    col_kappa_g = HeapBuf(N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        col_kappa_g[GEN ** c] = kappa_base[GEN ** COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]
    col_sort_order = HeapBuf(N_COMMITTED_COLS)
    hint_witness(col_sort_order[0:N_COMMITTED_COLS], "col_sort_order")
    col_off_g = HeapBuf(N_COMMITTED_COLS)
    g_total = GEN ** 0
    prev_col = GEN ** 0
    prev_kappa = GEN ** 0
    for rank in unroll(0, N_COMMITTED_COLS):
        col = col_sort_order[GEN ** rank]
        assert log(col) < N_COMMITTED_COLS
        kappa_g = col_kappa_g[col]
        if rank != 0:
            # A negative exponent wraps around the order of GEN and cannot pass this
            # small range check, hence prev_kappa >= kappa.
            assert log(prev_kappa / kappa_g) < SIZE_BITS
            if prev_kappa == kappa_g:
                # Equal-sized columns use their compact (native column-order) index
                # as the deterministic ascending tie-break.
                assert log(col / prev_col) < N_COMMITTED_COLS
        col_off_g[col] = g_total  # write-once: a duplicate permutation entry collides
        # g_squares spans SIZE_BITS, and every kappa is under it: a certified log
        # <= 32 (log_mem or a tau), the baked bytecode log, or q_flock's tau_5 + 8.
        # That last one is bounded only by the rs checks far below, and through m,
        # which is itself computed from this product; pin it here instead, so an
        # index into g_squares never rests on an argument that runs through the
        # value the index produces.
        assert log(kappa_g) < SIZE_BITS
        g_total *= g_squares[kappa_g]
        prev_col = col
        prev_kappa = kappa_g

    # Exact bit decompositions of every certified offset, over the MAX_STACK_LOG
    # bits one can have. The window is tight both ways: an offset is < 2^m <=
    # 2^MAX_STACK_LOG so the rebuild pins it exactly, and the rebuild IS a range
    # check, only one exponent below the generator's order reproducing g^offset.
    # Every coordinate a reader touches is therefore rebuilt here or, being at or
    # above m, zero-pinned at its use site; the extra zero cells cover residual
    # coordinates past the bound, which arise when candidates differ in residual
    # cap. `1 + g^(2^k)` is wanted once per bit per column, so it lives in FRAME
    # cells, where a HeapBuf read would be a DEREF.
    gsq_plus = StackBuf(SIZE_BITS)
    for k in unroll(0, SIZE_BITS):
        gsq_plus[k] = 1 + g_squares[GEN ** k]
    for c in unroll(0, N_COMMITTED_COLS):
        offset_row = col_offset_bits * GEN ** (COL_BITS_STRIDE * c)
        col_off = col_off_g[GEN ** c]
        hint_decompose_bits_exponent(offset_row, col_off, MAX_STACK_LOG)
        rebuilt_offset = GEN ** 0
        for k in unroll(0, MAX_STACK_LOG):
            offset_bit = offset_row[GEN ** k]
            offset_row[GEN ** k] = offset_bit * offset_bit  # booleanity, as a write-once pin
            rebuilt_offset *= (1 + offset_bit * gsq_plus[k])
        assert rebuilt_offset == col_off
        for k in unroll(MAX_STACK_LOG, COL_BITS_STRIDE):
            offset_row[GEN ** k] = 0
    return g_total


def check_opening_terminal(zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_blake2s_g, claim_cplen_g, lam_pool, col_offset_bits, z_vals, c_table, point_fold, point_tail, fold_cap_g, yr_log_n_g, yr_pad_g, inner_total, yr_at_tail, sumcheck_target):
    # The generalized eval_b terminal: every transparent weight evaluated at the one
    # point the opening reduced to, summed against the opening's own residual, and
    # checked against the sumcheck target. Per-claim lengths stay certified here,
    # every stack selector comes from the certified offset of CLAIM_COMMITTED_COL[j]
    # rather than from advice, QFLOCK value-slot IDs are baked per logical claim,
    # and all selector products use eq(b, r) = 1 + b + r.
    claim_low_len = HeapBuf(N_CLAIMS)  # the y-slot overlap pointers below re-read it
    claim_nover = HeapBuf(N_CLAIMS)
    hint_witness(claim_nover[0:N_CLAIMS], "claim_nover")
    pi_cplen = hint_witness("pi_cplen")
    # baked prefix-mask table replacing the hinted overlap mask: row t holds
    # [k < t] for k in [0, YR_LOG_CAP); the y-slot loop below selects row nover
    # by pointer arithmetic, so the mask is a prefix of exactly nover ones BY
    # CONSTRUCTION (no hint, no booleanity/monotone/popcount pins).
    prefix_mask_table = HeapBuf((YR_LOG_CAP + 1) * YR_LOG_CAP)
    for t in unroll(0, YR_LOG_CAP + 1):
        for k in unroll(0, t):
            prefix_mask_table[GEN ** (t * YR_LOG_CAP + k)] = 1
        for k in unroll(t, YR_LOG_CAP):
            prefix_mask_table[GEN ** (t * YR_LOG_CAP + k)] = 0
    # ---- shared low-coordinate eq chains ----
    # A claim's low_eq is the prefix product prod_{k < low_len} (1 + p_k + ris_k)
    # over its point buffer p: the FACTORS depend only on which buffer the claim
    # reads (and, for the qflock slots, on the ris shift), never on the claim, so
    # one chain per buffer serves every claim on it, each stopping at its own
    # certified length. The length pins below keep every read inside the written
    # span (low_len <= cplen <= the point buffer's extent, and nlow <= lenris).
    # The qflock variant reads chi against ris shifted past the slot coordinates,
    # so it needs its own chain. There is no zeta counterpart: a virtual value
    # column is referenced only by its own table's bus blocks, which the zerocheck
    # settles, so no framework block can raise one (asserted while the placeholder
    # map is built).
    zeta_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(zeta_eq_chain, 1, zeta, point_fold, g_bus_mu)
    chi_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(chi_eq_chain, 1, chi, point_fold, g_zc_n)
    chi_slot_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(chi_slot_eq_chain, 1, chi, point_fold * GEN ** SLOT_STRIDE_LOG, g_zc_n)
    claim_weights = HeapBuf(N_CLAIMS)
    for j in unroll(0, N_CLAIMS):
        claim_offset_bits = col_offset_bits * GEN ** (COL_BITS_STRIDE * CLAIM_COMMITTED_COL[j])
        # EXACT lengths: cplen is certified, nover (the residual-overlap count)
        # is the ONE hinted branch choice; low_len = cplen - nover and
        # seln = lenris + nover - nlow are divisions off it, and the range
        # checks + the product pins below reject any wrong nover.
        if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
            # pi: cplen = min(log_mem, lenris), certified as a min (<= both via
            # the range-checked division slacks, == one via the product).
            cplen_g = pi_cplen
            assert log(g_log_mem / cplen_g) < SIZE_BITS
            assert log(fold_cap_g / cplen_g) < SIZE_BITS
            assert (cplen_g + g_log_mem) * (cplen_g + fold_cap_g) == 0  # == one of them
            nlow = cplen_g                             # delta = 0 for pi
        else:
            cplen_g = claim_cplen_g[GEN ** j]
            nlow = cplen_g
            if CLAIM_POINT_BUF[j] == POINT_BUF_QFLOCK_RHO:
                nlow = cplen_g * GEN ** SLOT_STRIDE_LOG  # nlow = cplen + the qflock slot coords
        nover_g = claim_nover[GEN ** j]
        # nover <= YR_LOG_CAP: honest nover <= yr_log_n <= cap, and the y-slot
        # loop below selects prefix_mask_table row nover, so its log must be
        # pinned to the table (subsumes the SIZE_BITS check the division
        # pins need).
        assert log(nover_g) < YR_LOG_CAP + 1
        low_len_g = cplen_g / nover_g              # low_len = cplen - nover
        assert log(low_len_g) < SIZE_BITS
        claim_low_len[GEN ** j] = low_len_g
        seln = fold_cap_g * nover_g / nlow         # seln = lenris + nover - nlow
        assert log(seln) < SIZE_BITS
        assert (nover_g + 1) * (seln + 1) == 0      # nover == 0 OR seln == 0
        # selector loop reads point_fold[nlow .. nlow+seln); pin the reach
        # so it stays in [0, lenris): either seln == 0 (empty loop) or
        # nlow + seln == lenris (the honest overlap-free case).
        assert (nlow * seln + fold_cap_g) * (seln + 1) == 0
        # low_eq: the shared chain's partial product at this claim's certified
        # length, times the qflock slot factors (the only per-claim part).
        if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
            low_eq = zeta_eq_chain[low_len_g]
        if CLAIM_POINT_BUF[j] == POINT_BUF_RHO:
            low_eq = chi_eq_chain[low_len_g]
        if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
            low_chain = HeapBuf(SIZE_BITS + 1)
            low_chain[GEN ** 0] = 1
            low_chain[GEN ** 1] = 1 + rm + point_fold[GEN ** 0]
            for xk in mul_range(GEN, low_len_g):
                low_chain[xk * GEN] = low_chain[xk] * (1 + point_fold[xk])
            low_eq = low_chain[low_len_g]
        if CLAIM_POINT_BUF[j] == POINT_BUF_QFLOCK_RHO:
            qflock_slot_eq = GEN ** 0
            for k in unroll(0, SLOT_STRIDE_LOG):
                sb3 = CLAIM_QFLOCK_SLOT_BITS[SLOT_STRIDE_LOG * j + k]
                qflock_slot_eq *= (1 + sb3 + point_fold[GEN ** k])
            low_eq = qflock_slot_eq * chi_slot_eq_chain[low_len_g]
        ris_hi = point_fold * nlow
        # Selector coordinates [nlow, lenris) are exactly the corresponding
        # certified placement-offset bits.
        selrow = claim_offset_bits * nlow
        sel_chain = HeapBuf(SIZE_BITS + 1)
        sel_chain[GEN ** 0] = low_eq
        for xk in mul_range(1, seln):
            sel_bit = selrow[xk]
            sel_chain[xk * GEN] = sel_chain[xk] * (1 + sel_bit + ris_hi[xk])
        claim_weights[GEN ** j] = sel_chain[seln] * lam_pool[GEN ** j]
    # The ring-switch claim spans the opening point's first qflockv coordinates,
    # where the point in witness coordinates is point_fold[0, lenris) ++
    # point_tail[0, yr_log_n) and QFLOCK_VARS_CAP = tau_5 + SLOT_STRIDE_LOG is
    # exponent-additive from the certified announced log. A BLAKE2s-dominated inner
    # proof (every real XMSS aggregation) pushes qflockv past lenris, so the top
    # rs_nover coordinates continue into the residual challenges. rs_nover is hinted
    # and pinned exactly as the point claims pin theirs: rs_low = qflockv - rs_nover
    # and rs_len = lenris + rs_nover - qflockv are divisions off it, so the two
    # range checks plus the either/or leave rs_nover = max(0, qflockv - lenris).
    qflockv_g = tau_blake2s_g * GEN ** SLOT_STRIDE_LOG
    rs_nover_g = hint_witness("rs_nover")
    assert log(rs_nover_g) < YR_LOG_CAP + 1
    rs_low_g = qflockv_g / rs_nover_g
    assert log(rs_low_g) < SIZE_BITS
    prod_chains = HeapBuf((qflockv_g * GEN) ** BASE_FIELD_BITS)
    for k in unroll(0, BASE_FIELD_BITS):
        prod_chains[GEN ** k] = 1
    rs_eq_run(prod_chains, z_vals, point_fold, rs_low_g)
    # coordinates [rs_low, qflockv) = [lenris, lenris + rs_nover), against the
    # residual challenges; the chain rows stay indexed by absolute coordinate.
    rs_eq_run(prod_chains * rs_low_g ** BASE_FIELD_BITS, z_vals * rs_low_g, point_tail, rs_nover_g)
    prod_final = prod_chains * qflockv_g ** BASE_FIELD_BITS
    rs_weight = 0
    for k in unroll(0, BASE_FIELD_BITS):
        rs_weight += c_table[GEN ** k] * prod_final[GEN ** k]
    # ring-switch weight: extend by the selector bits over the point_fold coords
    # [qflockv, lenris), empty when the claim already reached past lenris.
    rs_len_g = fold_cap_g * rs_nover_g / qflockv_g
    assert log(rs_len_g) < SIZE_BITS
    assert (rs_nover_g + 1) * (rs_len_g + 1) == 0  # rs_nover == 0 OR rs_len == 0
    qflock_offset_bits = col_offset_bits * GEN ** (COL_BITS_STRIDE * QFLOCK_COMMITTED_COL)
    rsw_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(rsw_chain, rs_weight, qflock_offset_bits * qflockv_g, point_fold * qflockv_g, rs_len_g)
    rs_weight = rsw_chain[rs_len_g]
    # Evaluate every transparent weight at the one terminal fold point. Claim
    # j contributes cw_j * eq(slot_point_j, point_tail); the transmitted
    # final message is evaluated once and multiplied into their combined weight.
    inner_sum = inner_total
    for j in unroll(0, N_CLAIMS):
        overlap_ptr = chi * claim_low_len[GEN ** j]
        if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
            overlap_ptr = zeta * claim_low_len[GEN ** j]
        # overlap_ptr[g^k] reads the claim point at low_len + k, which is written
        # only for k < nover (the [low_len, cplen) span); at k >= nover it points
        # into the unwritten point-buffer gap (prover-chosen free cells). The
        # mask row IS the baked prefix of exactly nover ones (selected by the
        # pinned nover), so no overlap coord can read past cplen by construction;
        # a mask with a stray 1 at k >= nover would read a free cell and hand
        # the sumcheck a linear knob, i.e. a full opening forgery.
        mask_row = prefix_mask_table * claim_nover[GEN ** j] ** YR_LOG_CAP  # row nover: g^(nover * cap)
        claim_offset_bits = col_offset_bits * GEN ** (COL_BITS_STRIDE * CLAIM_COMMITTED_COL[j])
        residual_offset_bits = claim_offset_bits * fold_cap_g
        tail_eq = GEN ** 0
        for k in unroll(0, YR_LOG_CAP):
            mask_bit = mask_row[GEN ** k]
            slot_bit = residual_offset_bits[GEN ** k]
            slot_coord = mask_bit * overlap_ptr[GEN ** k] + (1 + mask_bit) * slot_bit
            tail_eq *= (1 + slot_coord + point_tail[GEN ** k])
        # zero-pin coords beyond final_msg's log-length (no over-cap weight): the
        # pointers start at yr_log_n. The zero asserts double as the
        # nover <= yr_log_n pin: a larger nover selects a row whose prefix
        # reaches into [yr_log_n, cap), failing here. So the mask is 0 in this
        # span, slot_point is 0, and no eq weight lands on the unwritten
        # final_msg cells past 2^yr_log_n.
        hi_mask = mask_row * yr_log_n_g
        hi_slot = residual_offset_bits * yr_log_n_g
        for xk in mul_range(1, yr_pad_g):
            assert hi_mask[xk] == 0
            assert hi_slot[xk] == 0
        inner_sum += claim_weights[GEN ** j] * tail_eq
    # Residual coords [rs_nover, yr_log_n) carry this column's slot bits; the
    # first rs_nover already entered the product above, so the mask row turns
    # their factor into 1 rather than double-counting them.
    rs_yslot_bits = qflock_offset_bits * fold_cap_g
    rs_mask_row = prefix_mask_table * rs_nover_g ** YR_LOG_CAP
    rs_tail_eq = GEN ** 0
    for k in unroll(0, YR_LOG_CAP):
        mb = rs_mask_row[GEN ** k]
        yb = rs_yslot_bits[GEN ** k]
        rs_tail_eq *= (1 + mb) * (1 + yb + point_tail[GEN ** k]) + mb
    rs_hi = rs_yslot_bits * yr_log_n_g
    rs_hi_mask = rs_mask_row * yr_log_n_g
    for xk in mul_range(1, yr_pad_g):
        assert rs_hi[xk] == 0  # zero-pin coords beyond final_msg's log-length
        assert rs_hi_mask[xk] == 0  # and pin rs_nover <= yr_log_n
    inner_sum += rs_weight * rs_tail_eq
    assert inner_sum * yr_at_tail == sumcheck_target


def verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement (pi_0, pi_1),
    # mirroring cpu::verify step for step; the `# ---- ... ----` headers below run
    # in that order. All proof data is hinted HERE, so each call pops the next
    # sub-proof's entry of every witness stream and the body lowers once. The
    # exponent tables are shared read-only; the deferred claims go to `defer_out`.
    #
    # The pool holds every committed-coordinate claim's value in decompose order
    # (the points are the GKR zetas, resolvable from the baked block structure) and
    # its certified low dimension, which the terminal pins its lengths against.
    claim_pool = HeapBuf(N_CLAIMS)
    claim_cplen_g = HeapBuf(N_CLAIMS)

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    fs = StackBuf(2)
    blake2s([seed_0, seed_1], [pi_0, pi_1], fs)
    stream = HeapBuf(STREAM_CAP)
    hint_witness(stream[0:STREAM_CAP], "stream")
    cursor = stream  # the proof stream, replayed word by word (advance = * g)

    # ---- announced layout and PCS rate (observed, then certified) ----
    # The stream announces the sizes as integer WORDS, one log each; the
    # shape-generic phases need them as G-POWERS (loop bounds, match scrutinees), so
    # each is reassembled from its advice-decomposed bits, with no hint and no
    # g^j -> j lookup. Every table's rows are real rows (the prover's fill blocks
    # bring each count up to a power of two), so a height is all there is to
    # announce.
    sizes = StackBuf(N_TABLES + 1)
    for i in unroll(0, N_TABLES + 1):
        fs, x, cursor = fs_next(fs, cursor)
        sizes[i] = x
    fs, log_inv_rate, cursor = fs_next(fs, cursor)
    rate_sel = g_power_of_word(log_inv_rate, g_squares, LOG_WORD_BITS) / GEN
    assert log(rate_sel) < LIG_N_RATES
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_{N_TABLES-1}]
    g_log_mem = g_power_of_word(sizes[0], g_squares, LOG_WORD_BITS)
    assert log(g_log_mem) < COUNT_BITS
    assert log(g_log_mem / GEN ** MIN_LOG_MEM) < COUNT_BITS  # native MIN_LOG_MEM <= log_mem
    dims_g[GEN ** 0] = g_log_mem
    for t in unroll(0, N_TABLES):
        g_tau = g_power_of_word(sizes[t + 1], g_squares, LOG_WORD_BITS)
        assert log(g_tau) < COUNT_BITS
        # A table's floor: flock sizes its BLAKE2s argument to at least 2^3 instances.
        assert log(g_tau / GEN ** FLOORS[t]) < COUNT_BITS
        dims_g[GEN ** (t + 1)] = g_tau
    # kappa_base maps a kappa source index to its certified announced log (source 0
    # = const via the baked adj). Each block's kappa then DERIVES from its
    # structural source as a compile-time offset off a certified log: no hint, and
    # nothing left free.
    kappa_base = HeapBuf(N_TABLES + 2)
    kappa_base[GEN ** 0] = 1
    kappa_base[GEN ** 1] = g_log_mem
    for t in unroll(0, N_TABLES):
        kappa_base[GEN ** (2 + t)] = dims_g[GEN ** (t + 1)]
    block_kappa = HeapBuf(N_BLOCKS)
    for b in unroll(0, N_BLOCKS):
        block_kappa[GEN ** b] = kappa_base[GEN ** BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]
    # The ONE bus depth, COMPUTED (not hinted): mu = log2_ceil(Σ_b 2^κ_b) over
    # PUSH's blocks; pull matches by pairing, the count tree is padded to it.
    push_total = GEN ** 0
    for b in unroll(SIDE_BLOCK_START[PUSH_SIDE], SIDE_BLOCK_START[PUSH_SIDE + 1]):
        push_total *= g_squares[block_kappa[GEN ** b]]  # g^(sum of 2^kappa)
    g_bus_mu = log2_ceil_in_the_exponent(push_total, g_logs_pow2, g_squares, 0, SIZE_BITS)
    zeta = HeapBuf(g_bus_mu)  # the ONE shared GKR point: exactly mu coords

    # ---- commitment root (2 words), kept for the opening phase ----
    fs, commit_root_0, cursor = fs_next(fs, cursor)
    fs, commit_root_1, cursor = fs_next(fs, cursor)
    # A non-canonical half is rejected here (merkle.rs `scalars_to_hash`); the level
    # roots get the same treatment at their own read.
    root_cells = StackBuf(2)
    root_cells[0] = assert_canonical(commit_root_0)
    root_cells[1] = assert_canonical(commit_root_1)

    # ---- bus challenges (F192 provides the soundness margin without grinding) ----
    # A tuple is fingerprinted multilinearly: slot x weighs eq(alphas, x), so a leaf
    # factor has total degree N_TUPLE_BITS in the challenges and the aligned bytecode
    # polynomial is read off at the challenge vector itself (doc sec:gp, sec:e2e-bc).
    bus_alpha = HeapBuf(N_TUPLE_BITS)
    for t in unroll(0, N_TUPLE_BITS):
        fs, av = squeeze(fs)
        bus_alpha[GEN ** t] = av
    fp_w = HeapBuf(N_TUPLE_SLOTS)
    for x in unroll(0, N_TUPLE_SLOTS):
        fp_w[GEN ** x] = eq_weight(bus_alpha, N_TUPLE_BITS, x, 0)
    fs, beta = squeeze(fs)

    # ---- ONE GKR grand product: push, pull, and count RLC-batched ----
    fs0, fs1, cursor, claim_push, claim_pull, claim_count = verify_bus_gkr(fs[0], fs[1], cursor, g_bus_mu, zeta)
    fs = [fs0, fs1]

    # ---- the bus leaves, the table sumcheck, and the public-input claim ----
    chi = HeapBuf(SIZE_BITS)  # chi[i] = the challenge that bound variable i
    fs0, fs1, cursor, g_zc_n, bc_share, rm = verify_tables(fs[0], fs[1], cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, block_kappa, g_squares, fp_w, beta, claim_pool, claim_cplen_g, chi, claim_push, claim_pull, claim_count)
    fs = [fs0, fs1]

    # ---- flock zerocheck and lincheck (the matrix evaluation is DEFERRED) ----
    tau_blake2s_g = dims_g[GEN ** (TABLE_BLAKE2s + 1)]  # the BLAKE2s table's certified tau
    zerocheck_chis = HeapBuf(tau_blake2s_g * GEN ** (K_LOG - K_SKIP))  # m - 6 rounds
    lincheck_rs = HeapBuf(LINCHECK_ROUNDS)
    z_partial = HeapBuf(2 ** K_SKIP)
    fs0, fs1, cursor, zerocheck_z, lincheck_alpha, matrix_eval = verify_flock(fs[0], fs[1], cursor, tau_blake2s_g, zerocheck_chis, lincheck_rs, z_partial)
    fs = [fs0, fs1]

    # ---- stacked mixed opening: ring-switch front + claim combination ----
    # The ring-switch slices are z_partial, read and bound above; this block only
    # binds them to the commitment. Compose six two-term F2-linear maps with shifts
    # 32,16,8,4,2,1: their expansion has all 64 Frobenius terms soundness needs,
    # while direct application costs 63 squarings and only six general
    # multiplications.
    map_challenges = HeapBuf(6)  # len(RING_MAP_SHIFTS)
    c_table = HeapBuf(BASE_FIELD_BITS)
    z_vals = HeapBuf(QFLOCK_VARS_CAP)
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        fs, map_challenge = squeeze(fs)
        map_challenges[GEN ** stage] = map_challenge
    # Expand the same composition once for the later transparent-weight evaluation.
    # Before shift d, the populated coefficients are exactly at multiples of 2d; the
    # new branch fills the adjacent d-offset entries.
    c_table[GEN ** 0] = 1
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        shift = RING_MAP_SHIFTS[stage]
        map_challenge = map_challenges[GEN ** stage]
        for slot in unroll(0, BASE_FIELD_BITS // (2 * shift)):
            coefficient = c_table[GEN ** (slot * 2 * shift)]
            for k in unroll(0, shift):
                coefficient *= coefficient
            c_table[GEN ** (slot * 2 * shift + shift)] = map_challenge * coefficient
    # Evaluate the claim and combine its 64 packing rows: the running x-power and
    # the running sum ride one two-slot chain.
    rs_chain = HeapBuf(((2 ** K_SKIP) + 1) * PAIR_SLOTS)
    rs_chain[GEN ** 0] = GEN ** 0  # x^i
    rs_chain[GEN ** 1] = 0         # the running sum
    for x_round in mul_range(1, GEN ** (2 ** K_SKIP)):
        lin_eval = z_partial[x_round]
        for stage in unroll(0, len(RING_MAP_SHIFTS)):
            frobenius = lin_eval
            for k in unroll(0, RING_MAP_SHIFTS[stage]):
                frobenius *= frobenius
            lin_eval += map_challenges[GEN ** stage] * frobenius
        row = rs_chain * x_round ** PAIR_SLOTS
        x_pow = row[GEN ** 0]
        row[GEN ** PAIR_SLOTS] = x_pow * 2
        row[GEN ** (PAIR_SLOTS + 1)] = row[GEN ** 1] + x_pow * lin_eval
    rs_end = rs_chain * (GEN ** (2 ** K_SKIP)) ** PAIR_SLOTS
    transposed_claim = rs_end[GEN ** 1]
    # Suffix point for the transparent weight.
    for t in unroll(0, LINCHECK_ROUNDS):
        z_vals[GEN ** t] = lincheck_rs[GEN ** (LINCHECK_ROUNDS - 1 - t)]
    zv_lo = z_vals * GEN ** LINCHECK_ROUNDS
    zr_hi = zerocheck_chis * GEN ** LINCHECK_ROUNDS
    for xt in mul_range(1, tau_blake2s_g):
        zv_lo[xt] = zr_hi[xt]
    # ONE batching challenge for the whole pool: N_CLAIMS - 1 fewer Fiat-Shamir
    # compressions than a challenge per claim, and none for the values themselves,
    # `fs_next` having bound every one of them as it read it, so `lam_cl` already
    # depends on all of them. Disjoint power ranges, as for the zc_xi-powers above:
    # the ring-switch claim takes lam_cl^0, the pool lam_cl^1 onward.
    fs, lam_cl = squeeze(fs)
    target = transposed_claim
    lam_pool = HeapBuf(N_CLAIMS)
    lam_pow = lam_cl
    for j in unroll(0, N_CLAIMS):
        lam_pool[GEN ** j] = lam_pow
        target += lam_pow * claim_pool[GEN ** j]
        lam_pow *= lam_cl

    col_offset_bits = HeapBuf(N_COMMITTED_COLS * COL_BITS_STRIDE)
    g_total = certify_placement(kappa_base, g_squares, col_offset_bits)

    # ---- certify g^m: m = max(log2_ceil(sum_cols 2^kappa), PCS_MIN_MU) ----
    # g_total is g^(sum 2^kappa) from the certified placement walk above.
    gmv = log2_ceil_in_the_exponent(g_total, g_logs_pow2, g_squares, PCS_MIN_MU, SIZE_BITS)  # g^m
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES
    # Flatten (rate-1, m-MIN) in rate-major order. Both coordinates are
    # transcript-bound and range-checked above, so a single compiled guest can
    # dispatch independently for every inner proof in a mixed-rate batch.
    config_sel = size_sel * rate_sel ** LIG_N_LOG_SIZES
    assert log(config_sel) < LIG_N_CANDIDATES
    sumcheck_target, point_fold, inner_total, yr_log_n_g, yr_pad_g, fold_cap_g, point_tail, yr_at_tail = match(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], target, commit_root_0, commit_root_1, cursor))
    # `stream` is a fixed-capacity witness transport. The shape fixes the exact
    # consumed prefix, whose every word is transcript-bound; the unused suffix
    # is outside the recursively verified proof and intentionally unconstrained.

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    check_opening_terminal(zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_blake2s_g, claim_cplen_g, lam_pool, col_offset_bits, z_vals, c_table, point_fold, point_tail, fold_cap_g, yr_log_n_g, yr_pad_g, inner_total, yr_at_tail, sumcheck_target)

    # ---- export this sub-proof's deferred-claim data to the caller (FRESH_*) ----
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = zeta[GEN ** k]
    for k in unroll(0, LOG2_BYTECODE_COLS):
        defer_out[GEN ** (BYTECODE_LOG + k)] = bus_alpha[GEN ** k]
    defer_out[GEN ** FRESH_BC_VALUE] = bc_share
    defer_out[GEN ** FRESH_ALPHA] = lincheck_alpha
    defer_out[GEN ** FRESH_Z_SKIP] = zerocheck_z
    for k in unroll(0, LINCHECK_ROUNDS):
        defer_out[GEN ** (FRESH_ZCHI + k)] = zerocheck_chis[GEN ** k]
        defer_out[GEN ** (FRESH_LINCHECK_RS + k)] = lincheck_rs[GEN ** k]
    for k in unroll(0, 2 ** K_SKIP):
        defer_out[GEN ** (FRESH_Z_PARTIAL + k)] = z_partial[GEN ** k]
    defer_out[GEN ** FRESH_MATPART] = matrix_eval
    return


# ============================ XMSS signature verification ===========================
# One signature of its epoch group's (epoch, message), against the signer's public
# key at `pk_ptr[g^0..g^1]` = (merkle_root, public_param). Every 16-byte native
# value (tweak, digest, chain tip, sibling, pp) is one canonical 128-bit cell.
# Tweak table layout (tweak index t at cell g^t):
#     0                        : encoding tweak
#     1 + CHAIN_STEPS·i + s    : chain tweak, chain i < V, step s < CHAIN_STEPS
#     WOTS_PK_TWEAK_IDX        : wots-pk tweak
#     MERKLE_TWEAK_IDX + l     : merkle tweak, level l < LOG_LIFETIME


def fill_xmss_epoch_tables(epoch, merkle_bits, tweak_table):
    # The tweak table and the Merkle direction bits at `epoch`, shared by every XMSS
    # signature this node verifies at it. One bit decomposition gives all three uses:
    # a tweak's index field is the epoch (encoding, chain, wots-pk) or the parent
    # index `epoch >> lvl` at Merkle level lvl - 1, and the direction bit at that
    # level IS bit lvl - 1. Booleanity is a write-once pin and the reconstruction
    # ties the bits back to the epoch, which also bounds it to LOG_LIFETIME bits.
    # SPHINCS shares none of this, deriving every tweak from the index its own
    # digest picks, which is neither public nor shared between signers.
    hint_decompose_bits(merkle_bits, epoch, LOG_LIFETIME)
    bits = StackBuf(LOG_LIFETIME)
    reconstructed = 0
    index = 0
    for b in unroll(0, LOG_LIFETIME):
        bit = merkle_bits[GEN ** b]
        merkle_bits[GEN ** b] = bit * bit
        bits[b] = bit
        reconstructed += bit * COORD_BASIS[b]
        index += bit * XM_INDEX_WEIGHT[b]
    assert reconstructed == epoch
    tweak_table[1] = index + XM_ENC_TWEAK
    for i in unroll(0, V):
        for s in unroll(0, CHAIN_STEPS):
            tweak_table[GEN ** (1 + CHAIN_STEPS * i + s)] = index + XM_CHAIN_TWEAKS[CHAIN_STEPS * i + s]
    tweak_table[GEN ** WOTS_PK_TWEAK_IDX] = index + XM_PK_TWEAK
    # Merkle level lvl - 1 hashes the parent at `epoch >> lvl`: the epoch's bits from
    # lvl up, each weighed lvl places down. The top level gets the empty sum.
    for lvl in unroll(1, LOG_LIFETIME + 1):
        parent = 0
        for b in unroll(lvl, LOG_LIFETIME):
            parent += bits[b] * XM_INDEX_WEIGHT[b - lvl]
        tweak_table[GEN ** (MERKLE_TWEAK_IDX + lvl - 1)] = parent + XM_MERKLE_TWEAKS[lvl - 1]
    return


def verify_sig(message, tweak_table, merkle_bits, pk_ptr):
    pp = pk_ptr[GEN]

    # Encoding digest D = BLAKE2s(tweak | pp | msg | randomness | zero-pad), 96
    # bytes: one full 64-byte block then a 32-byte final block (24 bytes of
    # randomness and the specified 8-byte zero pad). A packing helper source is read
    # as (lo, 0, 0) where BLAKE2s reads (lo, hi, 0), which is what pins that pad.
    after_msg = StackBuf(WORDS_PER_BLOCK)
    blake2s([tweak_table[1], pp], [message[1], message[GEN]], after_msg, counter=64, final=0)
    rand_block = StackBuf(WORDS_PER_BLOCK)
    hint_witness(rand_block, "rand")
    assert_in_k(rand_block[1], 0)
    digest = StackBuf(WORDS_PER_BLOCK)
    blake2s(rand_block, [0, 0], digest, cv=after_msg, counter=96, final=1)

    # V WOTS chains. Per chain the digit is hinted in the exponent (g^{e_i}), range
    # checked and dispatched once; arm k walks the remaining CHAIN_STEPS-k steps and
    # returns the tip cell plus the digit literal. The product of the digits is the
    # target sum (g^{Σe_i}); the digits, weighted by CHAIN_LENGTH^i inside their own
    # 64-bit lane (DIGITS_PER_WORD digits a lane, GF(2^64)'s monomial budget, each
    # lane's leftover top bits ground to zero by the signer), reconstruct D's first
    # cell as `acc_lo + acc_hi·Y`.
    tips = StackBuf(TIP_CELLS)
    chain_tweaks = tweak_table * GEN ** WORDS_PER_VALUE  # chain i at cell 1 + CHAIN_STEPS·i
    digit_product = 1
    acc_lo = 0
    acc_hi = 0
    for i in unroll(0, V):
        digit = hint_witness("digits")
        assert log(digit) < CHAIN_LENGTH
        chain_start = hint_witness("chain_starts")
        tips[i], e = match(log(digit), range(0, CHAIN_LENGTH), lambda k: walk(chain_start, chain_tweaks, pp, k))
        digit_product = digit_product * digit
        term = e * CHAIN_LENGTH ** (i % DIGITS_PER_WORD)  # e_i in its monomial subspace
        if i // DIGITS_PER_WORD == 0:
            acc_lo = acc_lo + term
        else:
            acc_hi = acc_hi + term
        chain_tweaks = chain_tweaks * GEN ** (WORDS_PER_VALUE * CHAIN_STEPS)
    assert digit_product == GEN ** TARGET_SUM
    assert acc_lo + acc_hi * Y_TOWER == digest[0]

    # WOTS public-key leaf = standard BLAKE2s over prefix + V tips: WOTS_PK_BLOCKS
    # full blocks, carrying the chaining value between instructions.
    leaf = StackBuf(WORDS_PER_BLOCK)
    blake2s([tweak_table[GEN ** (WORDS_PER_VALUE * WOTS_PK_TWEAK_IDX)], pp], tips[0:2], leaf, counter=64, final=0)
    for q in unroll(1, WOTS_PK_BLOCKS):
        next_leaf = StackBuf(WORDS_PER_BLOCK)
        blake2s(tips[4 * q - 2:4 * q], tips[4 * q:4 * q + 2], next_leaf, cv=leaf, counter=64 * (q + 1), final=(q + 1) // WOTS_PK_BLOCKS)
        leaf = next_leaf

    # Merkle path from the leaf to the root: the epoch bit orders the two children at
    # each level, and the tweak carries that level's parent index.
    node = leaf[0]
    for lvl in unroll(0, LOG_LIFETIME):
        sibling = hint_witness("siblings")
        children = order_children(node, sibling, merkle_bits[GEN ** (WORDS_PER_VALUE * lvl)])
        parent = StackBuf(WORDS_PER_BLOCK)
        blake2s([tweak_table[GEN ** (WORDS_PER_VALUE * (MERKLE_TWEAK_IDX + lvl))], pp], children, parent)
        node = parent[0]
    assert node == pk_ptr[1]
    return


def walk(value, chain_tweaks, pp, k: Const):
    # Walk WOTS chain steps k..CHAIN_STEPS-1: value' = H(tweak|pp, value|0). Step s
    # reads its tweak at cell s off the chain's subtable, a compile-time offset.
    word = value
    for s in unroll(k, CHAIN_STEPS):
        out = StackBuf(WORDS_PER_BLOCK)
        blake2s([chain_tweaks[GEN ** (WORDS_PER_VALUE * s)], pp], [word, 0], out, counter=48, final=1)
        word = out[0]
    return word, k


# ========================== SPHINCS+ signature verification =========================


@inline
def sp_bit_field(bits_ptr, off: Const, n: Const, pos: Const):
    # The integer held by bits [off, off+n) of the digest, weighed into the
    # coordinate basis at `pos`: a tweak field placed where the tweak wants it, one
    # fused multiply-add a bit, whatever lane the bits came from.
    acc = 0
    for i in unroll(0, n):
        acc += bits_ptr[GEN ** (off + i)] * COORD_BASIS[pos + i]
    return acc


def sp_walk(value, tw_base, pp, k: Const):
    # Walk chain steps k..SP_CHAIN_STEPS-1: value' = Th(P, tw_chain, value).
    # `tw_base` already carries the type byte, the layer, 2^w*i and the position
    # (tau, e), so step s's tweak is one addition of a compile-time literal.
    word = value
    for s in unroll(k, SP_CHAIN_STEPS):
        out = StackBuf(WORDS_PER_BLOCK)
        blake2s([tw_base + s * SP_P_MUL, pp], [word, 0], out, counter=48, final=1)
        word = out[0]
    return word, k


def sp_ots_leaf(tw_pos, pp, msg):
    # One layer's one-time verification: the encoding of `msg` under the hinted
    # counter, the V chains walked from the revealed values, and the leaf they hash
    # to. `tw_pos` is the position's tweak base (layer, tau, e); this function is
    # called once per layer, so the V dispatch tables are compiled once for the
    # whole scheme.
    ctr = hint_witness("sp_counter")
    ctr_bits = HeapBuf(GEN ** SP_COUNTER_BITS)
    hint_decompose_bits(ctr_bits, ctr, SP_COUNTER_BITS)
    bind_bits(ctr_bits, ctr, SP_COUNTER_BITS)  # LE_32: four counter bytes, twelve of padding

    # D = Th(P, tw_enc, msg | LE_32(c)), a 52-byte one-block hash.
    digest = StackBuf(WORDS_PER_BLOCK)
    blake2s([tw_pos + SP_TW_ENC, pp], [msg, ctr], digest, counter=52, final=1)

    # The codeword, as in XMSS: each digit hinted in the exponent, range checked and
    # dispatched once, arm k walking the remaining steps; the product of the digits
    # is the target sum, and the digits weighted by 2^w within each 64-bit lane
    # reconstruct D, which pins each lane's leftover top bits to zero.
    tips = StackBuf(SP_TIP_CELLS)
    digit_product = 1
    acc_lo = 0
    acc_hi = 0
    for i in unroll(0, SP_V):
        digit = hint_witness("sp_digits")
        assert log(digit) < SP_CHAIN_LENGTH
        chain_start = hint_witness("sp_chain_starts")
        tw_chain = tw_pos + SP_TW_CHAIN + i * SP_CHAIN_MUL
        tips[i], e = match(log(digit), range(0, SP_CHAIN_LENGTH), lambda k: sp_walk(chain_start, tw_chain, pp, k))
        digit_product = digit_product * digit
        term = e * SP_CHAIN_LENGTH ** (i % SP_DIGITS_PER_WORD)
        if i // SP_DIGITS_PER_WORD == 0:
            acc_lo = acc_lo + term
        else:
            acc_hi = acc_hi + term
    assert digit_product == GEN ** SP_TARGET_SUM
    assert acc_lo + acc_hi * Y_TOWER == digest[0]

    leaf = StackBuf(WORDS_PER_BLOCK)
    blake2s([tw_pos + SP_TW_LEAF, pp], tips[0:2], leaf, counter=64, final=0)
    for q in unroll(1, SP_LEAF_BLOCKS):
        next_leaf = StackBuf(WORDS_PER_BLOCK)
        blake2s(tips[4 * q - 2:4 * q], tips[4 * q:4 * q + 2], next_leaf, cv=leaf, counter=64 * (q + 1), final=(q + 1) // SP_LEAF_BLOCKS)
        leaf = next_leaf
    return leaf[0]


def verify_sig_sphincs(signer):
    # `signer` is one 4-cell entry of the SPHINCS coverage table: the key's root and
    # public parameter, then the message THAT signer signed. Where XMSS's message is
    # one statement field for the whole node, a SPHINCS message rides its own slot,
    # and the signer-set digest binds the two together.
    pp = signer[GEN]

    # ---- the message digest, which chooses the few-time key ----
    # D = Truncate(H(tw_msg | P | rho | root | m)), 96 bytes in two blocks.
    rho_root = StackBuf(WORDS_PER_BLOCK)
    hint_witness(rho_root[0:1], "sp_rand")
    rho_root[1] = signer[1]
    prefix = StackBuf(WORDS_PER_BLOCK)
    blake2s([SP_TW_MSG, pp], rho_root, prefix, counter=64, final=0)
    digest = StackBuf(WORDS_PER_BLOCK)
    blake2s([signer[GEN ** 2], signer[GEN ** 3]], [0, 0], digest, cv=prefix, counter=96, final=1)

    # The index and the k leaf indices are bit fields of that digest, so its bits are
    # advice-decomposed here and bound lane by lane. Nothing else derives them: every
    # tweak below is built from these bits.
    bits = HeapBuf(GEN ** SP_BIT_CELLS)
    lo = StackBuf(1)
    hint_f192_limbs(lo, digest[0])
    hi = (digest[0] + lo[0]) * Y_INV
    assert_in_k(lo[0], hi)
    tail = StackBuf(1)
    hint_f192_limbs(tail, digest[1])
    tail_hi = (digest[1] + tail[0]) * Y_INV
    assert_in_k(tail[0], tail_hi)
    lanes = [lo[0], hi, tail[0]]
    for lane in unroll(0, SP_BIT_LANES):
        run = bits * GEN ** (lane * BASE_FIELD_BITS)
        hint_decompose_bits(run, lanes[lane], BASE_FIELD_BITS)
        bind_bits(run, lanes[lane], BASE_FIELD_BITS)

    # The digest is admissible only if its last leaf index is zero, which is what
    # lets the forest drop that tree.
    for b in unroll(0, SP_A):
        assert bits[GEN ** (SP_H + (SP_K - 1) * SP_A + b)] == 0

    # ---- the few-time signature: one opened leaf per tree of the forest ----
    idx_tau = sp_bit_field(bits, 0, SP_H, SP_TAU_POS)
    roots = StackBuf(SP_N_FTS)
    for kappa in unroll(0, SP_N_FTS):
        leaf_off = SP_H + kappa * SP_A
        secret = StackBuf(WORDS_PER_BLOCK)
        hint_witness(secret[0:1], "sp_fts_secrets")
        fts_leaf = StackBuf(WORDS_PER_BLOCK)
        blake2s([SP_TW_FTS_LEAF + kappa * SP_LAY_MUL + idx_tau + sp_bit_field(bits, leaf_off, SP_A, SP_J_POS), pp], [secret[0], 0], fts_leaf, counter=48, final=1)
        node = fts_leaf[0]
        for level in unroll(0, SP_A):
            sibling = hint_witness("sp_fts_paths")
            children = order_children(node, sibling, bits[GEN ** (leaf_off + level)])
            parent = StackBuf(WORDS_PER_BLOCK)
            blake2s([SP_TW_FTS_NODE + kappa * SP_LAY_MUL + const((level + 1) * SP_P_MUL) + idx_tau + sp_bit_field(bits, leaf_off + level + 1, SP_A - level - 1, SP_J_POS), pp], children, parent)
            node = parent[0]
        roots[kappa] = node
    fts_key = StackBuf(WORDS_PER_BLOCK)
    blake2s([SP_TW_FTS_ROOTS + idx_tau, pp], roots[0:2], fts_key, counter=64, final=0)
    for q in unroll(1, SP_ROOT_BLOCKS):
        next_key = StackBuf(WORDS_PER_BLOCK)
        blake2s(roots[4 * q - 2:4 * q], roots[4 * q:4 * q + 2], next_key, cv=fts_key, counter=64 * (q + 1), final=(q + 1) // SP_ROOT_BLOCKS)
        fts_key = next_key
    signed = fts_key[0]

    # ---- the hypertree, bottom layer first ----
    # Layer lay signs what the layer below produced: the few-time key at the bottom,
    # that layer's root above it, and the public key's root at the top.
    for step in unroll(0, SP_D):
        lay = SP_D - 1 - step
        leaf_index_off = SP_SUFFIX[lay + 1]
        tau_field = sp_bit_field(bits, SP_SUFFIX[lay], SP_H - SP_SUFFIX[lay], SP_TAU_POS)
        tw_pos = tau_field + sp_bit_field(bits, leaf_index_off, SP_HEIGHTS[lay], SP_J_POS) + lay * SP_LAY_MUL
        node = sp_ots_leaf(tw_pos, pp, signed)
        for level in unroll(0, SP_HEIGHTS[lay]):
            sibling = hint_witness("sp_siblings")
            children = order_children(node, sibling, bits[GEN ** (leaf_index_off + level)])
            parent = StackBuf(WORDS_PER_BLOCK)
            blake2s([SP_TW_NODE + lay * SP_LAY_MUL + const((level + 1) * SP_P_MUL) + tau_field + sp_bit_field(bits, leaf_index_off + level + 1, SP_HEIGHTS[lay] - level - 1, SP_J_POS), pp], children, parent)
            node = parent[0]
        signed = node
    assert signed == signer[1]
    return


# =========================== statements and the signer set ==========================


def statement_digest(seed_0, seed_1, signers_hash, defer):
    # A node's statement, hashed to the two words the VM publishes, over the
    # proving environment's Fiat-Shamir seed (flock's R1CS and this bytecode), the
    # two-cell signer-set digest, and the DEFER_STMT_CELLS deferred-claim cells. A
    # parent rebuilds a child's statement with this same call, over a signer-set
    # digest it re-absorbed itself, which forces the child to be a proof of THIS
    # bytecode over groups checked against the parent's own.
    #
    # The preimage is fixed-length, so a plain BLAKE2s beats the Fiat-Shamir chain.
    # A header value is a canonical cell and needs no check, the BLAKE2s table
    # reading only cells whose top limb is zero. A deferred cell is a full field
    # element, so two fill three cells as (s0,s1) (s2,t0) (t1,t2), each top limb
    # derived from the two hinted below it and each pack proving its lanes in K.
    cells = StackBuf(4 * STMT_BLOCKS)
    cells[0] = seed_0  # the STMT_HEADER header cells
    cells[1] = seed_1
    cells[2] = signers_hash[1]
    cells[3] = signers_hash[GEN]
    for p in unroll(0, STMT_PAIRS):
        s = defer[GEN ** (2 * p)]
        if const(2 * p + 1 == DEFER_STMT_CELLS):
            t = 0  # an odd cell count pairs the last one with a zero partner
        else:
            t = defer[GEN ** (2 * p + 1)]
        s_lo = StackBuf(2)
        t_lo = StackBuf(2)
        hint_f192_limbs(s_lo, s)
        hint_f192_limbs(t_lo, t)
        cells[STMT_DEFER_OFF + 3 * p] = pack64x2(s_lo[0], s_lo[1])
        cells[STMT_DEFER_OFF + 3 * p + 1] = pack64x2(((s + s_lo[0]) * Y_INV + s_lo[1]) * Y_INV, t_lo[0])
        cells[STMT_DEFER_OFF + 3 * p + 2] = pack64x2(t_lo[1], ((t + t_lo[0]) * Y_INV + t_lo[1]) * Y_INV)
    for k in unroll(0, STMT_PAD_CELLS):
        cells[STMT_DEFER_OFF + 3 * STMT_PAIRS + k] = 0
    st = StackBuf(2)
    blake2s(cells[0:2], cells[2:4], st, counter=64, final=1 // STMT_BLOCKS)
    for b in unroll(1, STMT_BLOCKS):
        nxt = StackBuf(2)
        blake2s(cells[4 * b:4 * b + 2], cells[4 * b + 2:4 * b + 4], nxt, cv=st, counter=64 * (b + 1), final=(b + 1) // STMT_BLOCKS)
        st = nxt
    return st[0], st[1]


def keys_window(state_0, state_1, base, keys_ptr, x_q, g_squares):
    # One window of an epoch group's key hash: SIGNERS_WINDOW blocks, two declared
    # keys each (a key is two cells, a block four). Counters as in `sphincs_window`.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        pair = keys_ptr * (GEN ** (4 * j))
        hint_witness(pair[0:4], "pubkeys")
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(pair[0:2], pair[2:4], out, cv=st, md=nxt)
        else:
            blake2s(pair[0:2], pair[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def keys_tail(state_0, state_1, base, keys_ptr, k: Const):
    # The key pairs past the last whole window, all non-final, so every offset stays
    # below the base's lowest set bit.
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        pair = keys_ptr * (GEN ** (4 * j))
        hint_witness(pair[0:4], "pubkeys")
        out = StackBuf(2)
        blake2s(pair[0:2], pair[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], keys_ptr * (GEN ** (4 * k))


def key_list_digest(keys_ptr, half_g, odd_g, n_keys_g, g_squares):
    # BLAKE2s of one epoch group's declared key list: 32 bytes a key, so the hashed
    # string is 32·n bytes and its last block is the only partial one. The n // 2
    # pairs and the odd key out make half + odd blocks; all but the last run in
    # windows plus a tail (doc §sec:prog-byte-counter), and the last carries the
    # total length as its counter and the final-block flag.
    split = StackBuf(2)
    hint_witness(split, "signers_split")  # g^windows, g^tail_blocks
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == half_g * odd_g * INV_GEN
    chain = HeapBuf((windows * GEN) ** 4)  # state pair, base, first key of the window
    chain[1] = BLAKE2S_IV_0
    chain[GEN] = BLAKE2S_IV_1
    chain[GEN ** 2] = 0
    chain[GEN ** 3] = keys_ptr
    for xq in mul_range(1, windows):
        slot = chain * (xq ** 4)
        s0, s1, nb = keys_window(slot[1], slot[GEN], slot[GEN ** 2], slot[GEN ** 3], xq, g_squares)
        step = chain * ((xq * GEN) ** 4)
        step[1] = s0
        step[GEN] = s1
        step[GEN ** 2] = nb
        step[GEN ** 3] = slot[GEN ** 3] * (GEN ** (4 * SIGNERS_WINDOW))
    end = chain * (windows ** 4)
    t0, t1, last = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: keys_tail(end[1], end[GEN], end[GEN ** 2], end[GEN ** 3], k))
    final = scaled_log(n_keys_g, g_squares, 5) + MD_FINAL
    digest = StackBuf(2)
    if odd_g == 1:
        hint_witness(last[0:4], "pubkeys")
        blake2s(last[0:2], last[2:4], digest, cv=[t0, t1], md=final)
    else:
        # The odd key out fills half its block, the rest being the zero bytes the
        # counter already accounts for.
        hint_witness(last[0:2], "pubkeys")
        blake2s(last[0:2], [0, 0], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def child_keys_window(state_0, state_1, base, keys_ptr, cover, marks, origin_g, limit_g, x_q, g_squares):
    # One window of a child's key hash, absorbed exactly as the child absorbed it,
    # but with both keys of a block read at hinted indices into THIS node's table and
    # marked in the coverage table. Each index is an offset into the parent group the
    # caller mapped this child group to, bounded by that group's size, so a child's
    # key can only ever land on an XMSS slot of the right epoch.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)  # precondition as in the raw loops
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks * (GEN ** (2 * j))
        cover[origin_g * two[1]] = marks * (GEN ** (2 * j + 1))
        key_a = keys_ptr * (two[0] * two[0])
        key_b = keys_ptr * (two[1] * two[1])
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(key_a[0:2], key_b[0:2], out, cv=st, md=nxt)
        else:
            blake2s(key_a[0:2], key_b[0:2], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def child_keys_tail(state_0, state_1, base, keys_ptr, cover, marks, origin_g, limit_g, k: Const):
    # The child's key pairs past its last whole window, all non-final.
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks * (GEN ** (2 * j))
        cover[origin_g * two[1]] = marks * (GEN ** (2 * j + 1))
        key_a = keys_ptr * (two[0] * two[0])
        key_b = keys_ptr * (two[1] * two[1])
        out = StackBuf(2)
        blake2s(key_a[0:2], key_b[0:2], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], marks * (GEN ** (2 * k))


def child_key_list_digest(keys_ptr, cover, base, origin_g, limit_g, half_g, odd_g, n_keys_g, g_squares):
    # BLAKE2s of one epoch group of a child's keys, over the same 32·n bytes the
    # child hashed (`key_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. `base` prefixes the coverage write values, which
    # count the keys off as they are marked.
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == half_g * odd_g * INV_GEN
    chain = HeapBuf((windows * GEN) ** 4)
    chain[1] = BLAKE2S_IV_0
    chain[GEN] = BLAKE2S_IV_1
    chain[GEN ** 2] = 0
    chain[GEN ** 3] = base
    for xq in mul_range(1, windows):
        slot = chain * (xq ** 4)
        s0, s1, nb = child_keys_window(slot[1], slot[GEN], slot[GEN ** 2], keys_ptr, cover, slot[GEN ** 3], origin_g, limit_g, xq, g_squares)
        step = chain * ((xq * GEN) ** 4)
        step[1] = s0
        step[GEN] = s1
        step[GEN ** 2] = nb
        step[GEN ** 3] = slot[GEN ** 3] * (GEN ** (2 * SIGNERS_WINDOW))
    end = chain * (windows ** 4)
    t0, t1, marks = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: child_keys_tail(end[1], end[GEN], end[GEN ** 2], keys_ptr, cover, end[GEN ** 3], origin_g, limit_g, k))
    final = scaled_log(n_keys_g, g_squares, 5) + MD_FINAL
    digest = StackBuf(2)
    if odd_g == 1:
        two = StackBuf(2)
        hint_witness(two, "child_index")
        assert log(two[0]) < log(limit_g)
        assert log(two[1]) < log(limit_g)
        cover[origin_g * two[0]] = marks
        cover[origin_g * two[1]] = marks * GEN
        key_a = keys_ptr * (two[0] * two[0])
        key_b = keys_ptr * (two[1] * two[1])
        blake2s(key_a[0:2], key_b[0:2], digest, cv=[t0, t1], md=final)
    else:
        tail_idx = hint_witness("child_index")
        assert log(tail_idx) < log(limit_g)
        cover[origin_g * tail_idx] = marks
        key_last = keys_ptr * (tail_idx * tail_idx)
        blake2s(key_last[0:2], [0, 0], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def scaled_log(x, g_squares, shift: Const):
    # 2^shift times the exponent of `x`, as a bit pattern (doc §sec:prog-byte-counter).
    # The exponent's bits are advice, tied back by the g-power product; weighing them
    # at COORD_BASIS[j] assembles the exponent itself and the final multiply is the
    # shift, exact because nothing reduces below degree 64. Both sides of the product
    # stay under the order of g, so the bits ARE that exponent, hence below
    # 2^SIGNERS_COUNT_BITS, which every count and window index here is.
    bits = StackBuf(SIGNERS_COUNT_BITS)
    hint_decompose_bits_exponent(bits, x, SIGNERS_COUNT_BITS)
    value = 0
    rebuilt = GEN ** 0
    for j in unroll(0, SIGNERS_COUNT_BITS):
        b = bits[j]
        bits[j] = b * b  # booleanity, as a write-once pin
        value += b * COORD_BASIS[j]
        rebuilt *= (1 + b * (g_squares[GEN ** j] + 1))
    assert rebuilt == x
    return value * COORD_BASIS[shift]


def sphincs_window(state_0, state_1, base, entries_ptr, x_q, g_squares):
    # One window of the SPHINCS list's hash: SIGNERS_WINDOW claims, one 64-byte block
    # each (the claimed key, then the message it signed). Block j's counter is
    # base + 64(j+1), one XOR, except the last, whose offset is the base's own lowest
    # bit and which therefore takes the NEXT window's base as its whole counter. That
    # base is derived here and carried out for the following window.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        entry = entries_ptr * (GEN ** (4 * j))
        hint_witness(entry[0:4], "sphincs_signers")
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(entry[0:2], entry[2:4], out, cv=st, md=nxt)
        else:
            blake2s(entry[0:2], entry[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def sphincs_tail(state_0, state_1, base, entries_ptr, k: Const):
    # The blocks the window loop leaves over, fewer than a window, so every offset
    # 64(j+1) stays below the base's lowest set bit and needs no next base.
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        entry = entries_ptr * (GEN ** (4 * j))
        hint_witness(entry[0:4], "sphincs_signers")
        out = StackBuf(2)
        blake2s(entry[0:2], entry[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], entries_ptr * (GEN ** (4 * k))


def sphincs_list_digest(entries_ptr, n_g, g_squares):
    # BLAKE2s of the declared SPHINCS claims: n blocks of 64 bytes, so the hash is
    # over exactly 64n bytes and no block is partial. The last block is absorbed
    # apart, carrying the total length as its counter and the final-block flag; the
    # n - 1 before it run in windows plus a tail (doc §sec:prog-byte-counter).
    digest = StackBuf(2)
    if n_g == 1:
        # No claims: the hash of the empty string, one compression of a zero block.
        blake2s([0, 0], [0, 0], digest, md=MD_FINAL)
    else:
        split = StackBuf(2)
        hint_witness(split, "signers_split")  # g^windows, g^tail_blocks
        windows = split[0]
        tail = split[1]
        assert log(tail) < SIGNERS_WINDOW
        assert log(windows) < SIGNERS_MAX_WINDOWS
        assert windows ** SIGNERS_WINDOW * tail == n_g * INV_GEN
        # Four cells a window: the state pair, the window's base, its first entry.
        chain = HeapBuf((windows * GEN) ** 4)
        chain[1] = BLAKE2S_IV_0
        chain[GEN] = BLAKE2S_IV_1
        chain[GEN ** 2] = 0
        chain[GEN ** 3] = entries_ptr
        for xq in mul_range(1, windows):
            slot = chain * (xq ** 4)
            s0, s1, nb = sphincs_window(slot[1], slot[GEN], slot[GEN ** 2], slot[GEN ** 3], xq, g_squares)
            step = chain * ((xq * GEN) ** 4)
            step[1] = s0
            step[GEN] = s1
            step[GEN ** 2] = nb
            step[GEN ** 3] = slot[GEN ** 3] * (GEN ** (4 * SIGNERS_WINDOW))
        end = chain * (windows ** 4)
        t0, t1, last = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: sphincs_tail(end[1], end[GEN], end[GEN ** 2], end[GEN ** 3], k))
        hint_witness(last[0:4], "sphincs_signers")
        final = scaled_log(n_g, g_squares, 6) + MD_FINAL
        blake2s(last[0:2], last[2:4], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def child_sphincs_window(state_0, state_1, base, entries_ptr, cover, marks, origin_g, limit_g, x_q, g_squares):
    # One window of a child's SPHINCS list, absorbed exactly as the child absorbed
    # it, but with each block's claim read at a hinted index into THIS node's table
    # and marked in the coverage table. The index is an offset into the SPHINCS
    # region and bounded by that region's size, so a child's claim can only ever
    # land on a SPHINCS slot. Counters as in `sphincs_window`.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        off_hint = hint_witness("child_sphincs_index")
        assert log(off_hint) < log(limit_g)  # precondition as in the raw loops
        cover[origin_g * off_hint] = marks * (GEN ** j)
        entry = entries_ptr * (off_hint ** 4)
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(entry[0:2], entry[2:4], out, cv=st, md=nxt)
        else:
            blake2s(entry[0:2], entry[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def child_sphincs_tail(state_0, state_1, base, entries_ptr, cover, marks, origin_g, limit_g, k: Const):
    # The blocks past the child's last whole window, all of them non-final, so every
    # offset stays below this base's lowest set bit.
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        off_hint = hint_witness("child_sphincs_index")
        assert log(off_hint) < log(limit_g)
        cover[origin_g * off_hint] = marks * (GEN ** j)
        entry = entries_ptr * (off_hint ** 4)
        out = StackBuf(2)
        blake2s(entry[0:2], entry[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1]


def child_sphincs_list_digest(entries_ptr, cover, base, origin_g, limit_g, n_g, g_squares):
    # BLAKE2s of a child's declared SPHINCS claims, over the same 64n bytes the
    # child hashed (`sphincs_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. `base` prefixes the coverage write values, which
    # count the claims off as they are marked.
    digest = StackBuf(2)
    if n_g == 1:
        blake2s([0, 0], [0, 0], digest, md=MD_FINAL)
    else:
        split = StackBuf(2)
        hint_witness(split, "signers_split")
        windows = split[0]
        tail = split[1]
        assert log(tail) < SIGNERS_WINDOW
        assert log(windows) < SIGNERS_MAX_WINDOWS
        assert windows ** SIGNERS_WINDOW * tail == n_g * INV_GEN
        chain = HeapBuf((windows * GEN) ** 4)
        chain[1] = BLAKE2S_IV_0
        chain[GEN] = BLAKE2S_IV_1
        chain[GEN ** 2] = 0
        for xq in mul_range(1, windows):
            slot = chain * (xq ** 4)
            marks = base * (xq ** SIGNERS_WINDOW)
            s0, s1, nb = child_sphincs_window(slot[1], slot[GEN], slot[GEN ** 2], entries_ptr, cover, marks, origin_g, limit_g, xq, g_squares)
            step = chain * ((xq * GEN) ** 4)
            step[1] = s0
            step[GEN] = s1
            step[GEN ** 2] = nb
        end = chain * (windows ** 4)
        marks = base * (windows ** SIGNERS_WINDOW)
        t0, t1 = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: child_sphincs_tail(end[1], end[GEN], end[GEN ** 2], entries_ptr, cover, marks, origin_g, limit_g, k))
        off_hint = hint_witness("child_sphincs_index")
        assert log(off_hint) < log(limit_g)
        cover[origin_g * off_hint] = base * (n_g * INV_GEN)
        entry = entries_ptr * (off_hint ** 4)
        final = scaled_log(n_g, g_squares, 6) + MD_FINAL
        blake2s(entry[0:2], entry[2:4], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def plain_window(state_0, state_1, base, run_ptr, x_q, g_squares):
    # One window over a run of cells already in memory, four to a block, hinting
    # nothing. Counters as in `sphincs_window`.
    nxt = scaled_log(x_q * GEN, g_squares, const(6 + SIGNERS_WINDOW_LOG))
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, SIGNERS_WINDOW):
        block = run_ptr * (GEN ** (4 * j))
        out = StackBuf(2)
        if const(j + 1 == SIGNERS_WINDOW):
            blake2s(block[0:2], block[2:4], out, cv=st, md=nxt)
        else:
            blake2s(block[0:2], block[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], nxt


def plain_tail(state_0, state_1, base, run_ptr, k: Const):
    # The blocks of the run past its last whole window, all non-final.
    st = StackBuf(2)
    st[0] = state_0
    st[1] = state_1
    for j in unroll(0, k):
        block = run_ptr * (GEN ** (4 * j))
        out = StackBuf(2)
        blake2s(block[0:2], block[2:4], out, cv=st, md=base + const(64 * (j + 1)))
        st = out
    return st[0], st[1], run_ptr * (GEN ** (4 * k))


def signer_set_digest(run_ptr, n_epochs_g, g_squares):
    # BLAKE2s of the signer set: the tag block carrying both list lengths, the
    # SPHINCS list's digest, then two blocks a group, its (epoch, count, message)
    # and its key list's digest. Every block is full, so the hash is over exactly
    # 64·(2 + 2·epochs) bytes, and leading with both lengths makes the encoding
    # prefix-free: no set's string is a prefix of another's.
    blocks = n_epochs_g * n_epochs_g * (GEN ** 2)  # g^(2 + 2·epochs)
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    windows = split[0]
    tail = split[1]
    assert log(tail) < SIGNERS_WINDOW
    assert log(windows) < SIGNERS_MAX_WINDOWS
    assert windows ** SIGNERS_WINDOW * tail == blocks * INV_GEN
    chain = HeapBuf((windows * GEN) ** 4)
    chain[1] = BLAKE2S_IV_0
    chain[GEN] = BLAKE2S_IV_1
    chain[GEN ** 2] = 0
    chain[GEN ** 3] = run_ptr
    for xq in mul_range(1, windows):
        slot = chain * (xq ** 4)
        s0, s1, nb = plain_window(slot[1], slot[GEN], slot[GEN ** 2], slot[GEN ** 3], xq, g_squares)
        step = chain * ((xq * GEN) ** 4)
        step[1] = s0
        step[GEN] = s1
        step[GEN ** 2] = nb
        step[GEN ** 3] = slot[GEN ** 3] * (GEN ** (4 * SIGNERS_WINDOW))
    end = chain * (windows ** 4)
    t0, t1, last = match(log(tail), range(0, SIGNERS_WINDOW), lambda k: plain_tail(end[1], end[GEN], end[GEN ** 2], end[GEN ** 3], k))
    final = scaled_log(blocks, g_squares, 6) + MD_FINAL
    digest = StackBuf(2)
    blake2s(last[0:2], last[2:4], digest, cv=[t0, t1], md=final)
    return digest[0], digest[1]


def rebuild_child_groups(nsub_e_g, run_ptr, base, epochs, msgs, group_base, group_slots, n_epochs_g, xmss_table, cover, g_squares):
    # The child's epoch groups, written into the run its own signer-set hash covers,
    # two blocks a group exactly as the child laid them out: its (epoch, count,
    # message), then the digest of its keys, read from THIS node's table through
    # hinted indices. A hinted map ties each group to the parent group holding the
    # same epoch AND message, whose region its keys land in. Everything hinted here
    # is pinned by the digest, which the child's statement carries. The running
    # product of the group counts prefixes each group's coverage writes and ends as
    # the child's XMSS claim count.
    counts = HeapBuf(nsub_e_g * GEN)
    counts[GEN ** 0] = 1
    for xj in mul_range(1, nsub_e_g):
        grp = StackBuf(4)
        hint_witness(grp, "child_group")  # epoch, msg_lo, msg_hi, count
        n_keys = grp[3]
        assert log(n_keys) < MAX_KEYS
        parent = hint_witness("child_group_map")
        assert log(parent) < log(n_epochs_g)
        assert epochs[parent] == grp[0]
        parent_msg = msgs * (parent * parent)
        assert parent_msg[1] == grp[1]
        assert parent_msg[GEN] == grp[2]
        halves = StackBuf(2)
        hint_witness(halves, "child_halves")
        assert log(halves[1]) < 2
        assert log(halves[0]) < MAX_KEYS
        assert halves[0] * halves[0] * halves[1] == n_keys
        gb = group_base[parent]
        prefix = counts[xj]
        kd_0, kd_1 = child_key_list_digest(xmss_table * (gb * gb), cover, base * prefix, gb, group_slots[parent], halves[0], halves[1], n_keys, g_squares)
        slot = run_ptr * (xj ** 8) * (GEN ** 8)
        slot[1] = grp[0]
        slot[GEN] = n_keys
        slot[GEN ** 2] = grp[1]
        slot[GEN ** 3] = grp[2]
        slot[GEN ** 4] = kd_0
        slot[GEN ** 5] = kd_1
        slot[GEN ** 6] = 0
        slot[GEN ** 7] = 0
        counts[xj * GEN] = prefix * n_keys
    return counts[nsub_e_g]


# ================================ the aggregation node ==============================


def main():
    # One node of an aggregation tree: raw XMSS signatures grouped by the epoch they
    # were made at (a RUNTIME number of groups), n_raw_sphincs SPHINCS signatures
    # and n_children sub-proofs OF THIS SAME BYTECODE. Each XMSS group carries its
    # own (epoch, message) pair, and each SPHINCS signature is against the message
    # in its own coverage slot.
    #
    # The declared lists are the signer set; the duplicate slots absorb keys a child
    # covers that the set does not declare. The coverage table is one region per
    # epoch group, each its declared keys then its own duplicates, then the SPHINCS
    # region shaped the same way:
    #
    #   [group 0: declared | dup]...[group n_epochs-1: declared | dup][SPHINCS: declared | dup]
    #
    # The first n_decl groups are the signer set's; the n_drop after them declare
    # nothing, holding a child group's (epoch, message) without publishing it.
    #
    # so one range check per write keeps each writer inside its own region: that is
    # what makes the statement's split mean which scheme verified which key against
    # which (epoch, message). An XMSS slot is two cells, a SPHINCS slot four: a key
    # and the message that key signed.
    meta = StackBuf(6)
    hint_witness(meta, "meta")  # every count in the exponent
    n_decl_g = meta[0]
    n_drop_g = meta[1]
    n_sphincs_g = meta[2]
    n_sdup_g = meta[3]
    n_raw_s_g = meta[4]
    n_children_g = meta[5]
    # Declared plus dropped, so bounding each side pins n_decl <= n_epochs.
    assert log(n_decl_g) < MAX_EPOCHS + 1
    assert log(n_drop_g) < MAX_EPOCHS + 1
    n_epochs_g = n_decl_g * n_drop_g
    assert log(n_epochs_g) < MAX_EPOCHS + 1
    assert log(n_sphincs_g) < MAX_KEYS
    assert log(n_sdup_g) < MAX_KEYS
    assert log(n_raw_s_g) < MAX_KEYS
    assert log(n_children_g) < MAX_RECURSIONS + 1

    # ---- the epoch groups: geometry pass ----
    # Per group: its epoch, its two message cells, and its declared, duplicate and
    # raw-signature counts, each count bounded before it enters a product (up to
    # 2^16 factors of exponent < 2^17 stay far from the order 2^64 - 1, so nothing
    # wraps). Region bases and the three totals ride a stride-4 chain; the per-group
    # values land in heap buffers the later passes and the children's hinted group
    # maps read back at runtime.
    epochs = HeapBuf(n_epochs_g)
    msgs = HeapBuf(n_epochs_g * n_epochs_g)
    group_n_keys = HeapBuf(n_epochs_g)
    group_n_dups = HeapBuf(n_epochs_g)
    group_n_raw = HeapBuf(n_epochs_g)
    group_base = HeapBuf(n_epochs_g)
    group_slots = HeapBuf(n_epochs_g)
    geo = HeapBuf((n_epochs_g * GEN) ** 4)  # [base, n_xmss product, n_raw product]
    geo[1] = 1
    geo[GEN] = 1
    geo[GEN ** 2] = 1
    for xe in mul_range(1, n_epochs_g):
        grp = StackBuf(6)
        hint_witness(grp, "group")  # epoch, msg_lo, msg_hi, n, n_dup, n_raw
        assert log(grp[3]) < MAX_KEYS
        assert log(grp[4]) < MAX_KEYS
        assert log(grp[5]) < MAX_KEYS
        epochs[xe] = grp[0]
        msg = msgs * (xe * xe)
        msg[1] = grp[1]
        msg[GEN] = grp[2]
        group_n_keys[xe] = grp[3]
        group_n_dups[xe] = grp[4]
        group_n_raw[xe] = grp[5]
        state = geo * (xe ** 4)
        base = state[1]
        group_base[xe] = base
        slots = grp[3] * grp[4]
        group_slots[xe] = slots
        nxt = geo * ((xe * GEN) ** 4)
        nxt[1] = base * slots
        nxt[GEN] = state[GEN] * grp[3]
        nxt[GEN ** 2] = state[GEN ** 2] * grp[5]
    geo_end = geo * (n_epochs_g ** 4)
    xmss_slots_g = geo_end[1]
    n_raw_x_g = geo_end[GEN ** 2]
    sphincs_slots_g = n_sphincs_g * n_sdup_g
    # The sum of every region bounds the coverage indices, so it is what has to sit
    # below the minimum memory size.
    n_total_g = xmss_slots_g * sphincs_slots_g
    assert log(n_total_g) < MAX_KEYS

    # The proving environment (flock's R1CS and this bytecode) as one digest. It
    # rides the statement rather than the bytecode, so nothing here has to know its
    # own hash; the outer verifier pins it, and every child statement rebuilt below
    # copies it, which is what keeps a whole tree on one bytecode.
    fs_seed = StackBuf(2)
    hint_witness(fs_seed, "fs_seed")
    seed_0 = fs_seed[0]
    seed_1 = fs_seed[1]

    # ---- the signer set ----
    g_logs_pow2, g_squares = exponent_tables()
    # One table per scheme, the XMSS one an epoch group at a time: each group its
    # declared list (strictly sorted, checked by the outer verifier, which holds it)
    # followed by its own duplicate slots. The coverage indices below run over one
    # space: the group regions in order, then the SPHINCS one.
    #
    # The digest is a plain BLAKE2s of one string, in whole blocks: a tag block with
    # both lengths, the SPHINCS list's digest, then per group its (epoch, count,
    # message) and its key list's digest, each list hashed plainly in turn. Leading
    # with both lengths makes the encoding prefix-free, so no set's string is a
    # prefix of another's and the digest binds its own lengths. `half` and `odd` are
    # hinted per group and pinned by half*half*odd == n with odd in {0, 1}, which
    # leaves half = n // 2 and odd = n % 2 as the only solution.
    xmss_table = HeapBuf(xmss_slots_g * xmss_slots_g)
    sphincs_table = HeapBuf(sphincs_slots_g ** 4)
    # The run the set's hash covers: the tag block with both lengths, a block for the
    # SPHINCS list's digest, then two a group. Eight cells a group, so a group's
    # header and its key digest are one block each.
    signers_run = HeapBuf(n_decl_g ** 8 * GEN ** 8)
    signers_run[1] = SIGNERS_TAG_0
    signers_run[GEN] = SIGNERS_TAG_1
    signers_run[GEN ** 2] = n_decl_g
    signers_run[GEN ** 3] = n_sphincs_g
    decl_keys = HeapBuf(n_decl_g * GEN)
    decl_keys[GEN ** 0] = 1
    for xe in mul_range(1, n_decl_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        decl_keys[xe * GEN] = decl_keys[xe] * n_keys
        halves = StackBuf(2)
        hint_witness(halves, "pk_halves")
        assert log(halves[1]) < 2
        assert log(halves[0]) < MAX_KEYS
        assert halves[0] * halves[0] * halves[1] == n_keys
        kd_0, kd_1 = key_list_digest(xmss_table * (base * base), halves[0], halves[1], n_keys, g_squares)
        group_msg = msgs * (xe * xe)
        slot = signers_run * (xe ** 8) * (GEN ** 8)
        slot[1] = epochs[xe]
        slot[GEN] = n_keys
        slot[GEN ** 2] = group_msg[1]
        slot[GEN ** 3] = group_msg[GEN]
        slot[GEN ** 4] = kd_0
        slot[GEN ** 5] = kd_1
        slot[GEN ** 6] = 0
        slot[GEN ** 7] = 0
    # The duplicate slots ride the same table but outside the hashed prefix, past
    # each group's declared keys. Over the whole table: a dropped group has only these.
    for xe in mul_range(1, n_epochs_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        dup_ptr = xmss_table * (base * base * n_keys * n_keys)
        for xd in mul_range(1, group_n_dups[xe]):
            dup = dup_ptr * (xd * xd)
            hint_witness(dup[0:2], "dup_pubkeys")
    sp_0, sp_1 = sphincs_list_digest(sphincs_table, n_sphincs_g, g_squares)
    signers_run[GEN ** 4] = sp_0
    signers_run[GEN ** 5] = sp_1
    signers_run[GEN ** 6] = 0
    signers_run[GEN ** 7] = 0
    # Over the declared prefix, since a dropped group's count is advice. Ahead of
    # `cover` below, so it also rules out a zero-slot table.
    assert decl_keys[n_decl_g] * n_sphincs_g != 1  # a signer set is never empty
    set_0, set_1 = signer_set_digest(signers_run, n_decl_g, g_squares)
    signers_hash = HeapBuf(WORDS_PER_BLOCK)
    signers_hash[1] = set_0
    signers_hash[GEN] = set_1
    for xd in mul_range(1, n_sdup_g):
        dup = sphincs_table * ((n_sphincs_g * xd) ** 4)
        hint_witness(dup[0:4], "dup_sphincs")

    # ---- coverage ----
    # Every one of the n_total slots is written exactly once: write-once memory
    # rejects a second write (the value written is the running count, so two writes
    # to one slot disagree), and the count below rejects a missed one. So every
    # declared signer is covered by a signature of ITS OWN scheme, at ITS OWN epoch,
    # or by a verified child, which is the whole security claim of the aggregate.
    # The raw XMSS walk runs one loop per epoch group, each signature verified
    # against that group's tables (built here, only for a group that holds raw
    # signatures); a stride-1 chain threads the running count across the groups.
    cover = HeapBuf(n_total_g)
    merkle_bits = HeapBuf(n_epochs_g ** MERKLE_BIT_CELLS)
    tweak_tables = HeapBuf(n_epochs_g ** N_TWEAK_CELLS)
    raw_count = HeapBuf(n_epochs_g * GEN)
    raw_count[GEN ** 0] = 1
    for xe in mul_range(1, n_epochs_g):
        n_raw = group_n_raw[xe]
        prefix = raw_count[xe]
        if n_raw != 1:
            tweak_table = tweak_tables * (xe ** N_TWEAK_CELLS)
            group_bits = merkle_bits * (xe ** MERKLE_BIT_CELLS)
            fill_xmss_epoch_tables(epochs[xe], group_bits, tweak_table)
            slots = group_slots[xe]
            base = group_base[xe]
            keys = xmss_table * (base * base)
            group_msg = msgs * (xe * xe)
            for xi in mul_range(1, n_raw):
                idx = hint_witness("raw_index")
                # A runtime bound, whose `n_total < 2^MIN_LOG_MEM` precondition is
                # discharged by `assert log(n_total_g) < MAX_KEYS` above. Without it
                # this degenerates to what DEREF alone gives and an index could
                # reach past `cover`, which is the whole bijection. The bound is
                # this GROUP's region, so a signature verified at this (epoch,
                # message) covers no other group's declared key.
                assert log(idx) < log(slots)
                cover[base * idx] = prefix * xi
                verify_sig(group_msg, tweak_table, group_bits, keys * (idx * idx))
            raw_count[xe * GEN] = prefix * n_raw
        else:
            raw_count[xe * GEN] = prefix
    for xj in mul_range(1, n_raw_s_g):
        off_hint = hint_witness("sp_raw_index")
        assert log(off_hint) < log(sphincs_slots_g)
        cover[xmss_slots_g * off_hint] = n_raw_x_g * xj
        verify_sig_sphincs(sphincs_table * (off_hint ** 4))

    # ---- children ----
    child_pi = HeapBuf(n_children_g * n_children_g)
    child_fresh = HeapBuf(n_children_g ** DEFER_SIZE)
    child_carried = HeapBuf(n_children_g ** DEFER_STMT_CELLS)
    written = HeapBuf(n_children_g * GEN)  # loop-carried write count, one per child
    written[GEN ** 0] = n_raw_x_g * n_raw_s_g
    for xc in mul_range(1, n_children_g):
        base = written[xc]
        # The child's two list lengths, then its groups, rebuilt into its signer-set
        # chain by rebuild_child_groups: everything hinted there is pinned by the
        # chain, which the child's statement digest carries, so a lie about any of
        # it changes the public input its proof has to satisfy. Nothing demands a
        # mid-tree statement be canonical (sorted, distinct groups); it still binds
        # every claim to its (epoch, message), which is all the group map relies on.
        child_meta = StackBuf(2)
        hint_witness(child_meta, "child_meta")  # n_epochs, n_sphincs
        nsub_e_g = child_meta[0]
        nsub_s_g = child_meta[1]
        assert log(nsub_e_g) < MAX_EPOCHS + 1
        assert log(nsub_s_g) < MAX_KEYS
        sub_run = HeapBuf(nsub_e_g ** 8 * GEN ** 8)
        sub_run[1] = SIGNERS_TAG_0
        sub_run[GEN] = SIGNERS_TAG_1
        sub_run[GEN ** 2] = nsub_e_g
        sub_run[GEN ** 3] = nsub_s_g
        nsub_x_g = rebuild_child_groups(nsub_e_g, sub_run, base, epochs, msgs, group_base, group_slots, n_epochs_g, xmss_table, cover, g_squares)
        # Implied by the per-group bounds and the child's own n_total assert; stands
        # as documentation.
        assert log(nsub_x_g) < MAX_KEYS
        nsub_g = nsub_x_g * nsub_s_g
        assert nsub_g != 1
        csp_0, csp_1 = child_sphincs_list_digest(sphincs_table, cover, base * nsub_x_g, xmss_slots_g, sphincs_slots_g, nsub_s_g, g_squares)
        sub_run[GEN ** 4] = csp_0
        sub_run[GEN ** 5] = csp_1
        sub_run[GEN ** 6] = 0
        sub_run[GEN ** 7] = 0
        sub_set_0, sub_set_1 = signer_set_digest(sub_run, nsub_e_g, g_squares)
        sub_hash = HeapBuf(WORDS_PER_BLOCK)
        sub_hash[1] = sub_set_0
        sub_hash[GEN] = sub_set_1
        carried = child_carried * xc ** DEFER_STMT_CELLS
        hint_witness(carried[0:DEFER_STMT_CELLS], "child_defer")
        pi_0, pi_1 = statement_digest(seed_0, seed_1, sub_hash, carried)
        pi = xc * xc
        child_pi[pi] = pi_0
        child_pi[pi * GEN] = pi_1
        verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, child_fresh * xc ** DEFER_SIZE)
        written[xc * GEN] = base * nsub_g
    assert written[n_children_g] == n_total_g

    # ---- this node's own deferred claims ----
    defer_stmt = HeapBuf(DEFER_STMT_CELLS)
    if n_children_g == 1:
        # A leaf has nothing to batch, so it defers the three fixed polynomials at
        # the all-zeros point. Their values ride a hint and are checked nowhere
        # here: the outer verifier recomputes them and rebuilds the statement, so a
        # lie changes the public input rather than the claim.
        leaf_values = StackBuf(3)
        hint_witness(leaf_values, "leaf_defer")
        for k in unroll(0, BYTECODE_VARS):
            defer_stmt[GEN ** k] = 0
        defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = leaf_values[0]
        for k in unroll(0, 2 * K_LOG):
            defer_stmt[GEN ** (DEFER_STMT_MAT_POINT + k)] = 0
        defer_stmt[GEN ** DEFER_STMT_A_VALUE] = leaf_values[1]
        defer_stmt[GEN ** DEFER_STMT_B_VALUE] = leaf_values[2]
    else:
        aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt)

    own_0, own_1 = statement_digest(seed_0, seed_1, signers_hash, defer_stmt)
    pub_ptr = GEN ** 0
    assert pub_ptr[1] == own_0
    assert pub_ptr[GEN] == own_1
    return


def aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt):
    # Every child contributes two claims per fixed polynomial: the one IT deferred
    # (carried in its statement) and the fresh one raised by verifying its proof. A
    # fresh transcript binds all of them, samples the batching coefficients, and two
    # sumchecks (one for the bytecode, one shared by the two matrices) reduce the
    # lot to one claim each, which is what the node then defers in its own
    # statement.
    #
    # A carried claim is a plain point, so its weight is an eq product; a fresh one
    # carries flock's zerocheck/lincheck structure and keeps the succinct weight the
    # sub-verifier exported. That is the only asymmetry.
    bc_msgs = HeapBuf(2 * BYTECODE_VARS)
    hint_witness(bc_msgs[0:2 * BYTECODE_VARS], "bc_sumcheck_msgs")
    mat_msgs = HeapBuf(4 * K_LOG)
    hint_witness(mat_msgs[0:4 * K_LOG], "mat_sumcheck_msgs")
    bytecode_star = hint_witness("bc_star_hint")
    mat_stars = StackBuf(2)
    hint_witness(mat_stars[0:2], "mat_stars_hint")

    # ---- one transcript over every child's statement and both its claim sets ----
    fresh_row = HeapBuf(n_children_g)
    carried_row = HeapBuf(n_children_g)
    agg_fs = [AGG_SEED_0, AGG_SEED_1]
    agg_fs = obs(agg_fs, n_children_g)
    absorb = HeapBuf((n_children_g * GEN) ** PAIR_SLOTS)
    absorb[GEN ** 0] = agg_fs[0]
    absorb[GEN ** 1] = agg_fs[1]
    for xc in mul_range(1, n_children_g):
        row = absorb * xc ** PAIR_SLOTS
        st = [row[GEN ** 0], row[GEN ** 1]]
        pi = xc * xc
        st = obs(st, child_pi[pi])
        st = obs(st, child_pi[pi * GEN])
        fresh = child_fresh * xc ** DEFER_SIZE
        fresh_row[xc] = fresh
        for k in unroll(0, DEFER_SIZE):
            st = obs(st, fresh[GEN ** k])
        carried = child_carried * xc ** DEFER_STMT_CELLS
        carried_row[xc] = carried
        for k in unroll(0, DEFER_STMT_CELLS):
            st = obs(st, carried[GEN ** k])
        row[GEN ** PAIR_SLOTS] = st[0]
        row[GEN ** (PAIR_SLOTS + 1)] = st[1]
    absorbed = absorb * n_children_g ** PAIR_SLOTS

    # ---- bytecode batching sumcheck (BYTECODE_VARS variables, 2 per child) ----
    # Fresh and carried share the bytecode layout (point, then value), so the two
    # differ only in which buffer they come from.
    lam_bc = HeapBuf(n_children_g * n_children_g)
    bc_chain = HeapBuf((n_children_g * GEN) ** ACC_SLOTS)
    bc_chain[GEN ** ACC_FS0] = absorbed[GEN ** 0]
    bc_chain[GEN ** ACC_FS1] = absorbed[GEN ** 1]
    bc_chain[GEN ** ACC_VALUE] = 0
    for xc in mul_range(1, n_children_g):
        row = bc_chain * xc ** ACC_SLOTS
        st = [row[GEN ** ACC_FS0], row[GEN ** ACC_FS1]]
        st, lam_fresh = squeeze(st)
        st, lam_carried = squeeze(st)
        pair = xc * xc
        lam_bc[pair] = lam_fresh
        lam_bc[pair * GEN] = lam_carried
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        nxt = row * GEN ** ACC_SLOTS
        nxt[GEN ** ACC_FS0] = st[0]
        nxt[GEN ** ACC_FS1] = st[1]
        nxt[GEN ** ACC_VALUE] = row[GEN ** ACC_VALUE] + lam_fresh * fresh[GEN ** FRESH_BC_VALUE] + lam_carried * carried[GEN ** DEFER_STMT_BC_VALUE]
    bc_end = bc_chain * n_children_g ** ACC_SLOTS
    agg_fs = [bc_end[GEN ** ACC_FS0], bc_end[GEN ** ACC_FS1]]
    bc_running = bc_end[GEN ** ACC_VALUE]
    bc_point = HeapBuf(BYTECODE_VARS)
    fs0, fs1, bc_running = batch_sumcheck(agg_fs[0], agg_fs[1], bc_msgs, bc_running, bc_point, BYTECODE_VARS)
    agg_fs = [fs0, fs1]
    bc_wsum = HeapBuf(n_children_g * GEN)
    bc_wsum[GEN ** 0] = 0
    for xc in mul_range(1, n_children_g):
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        eq_fresh = GEN ** 0
        eq_carried = GEN ** 0
        for k in unroll(0, BYTECODE_VARS):
            rk = bc_point[GEN ** k]
            eq_fresh *= (1 + fresh[GEN ** k] + rk)
            eq_carried *= (1 + carried[GEN ** k] + rk)
        pair = xc * xc
        bc_wsum[xc * GEN] = bc_wsum[xc] + lam_bc[pair] * eq_fresh + lam_bc[pair * GEN] * eq_carried
    assert bc_running == bytecode_star * bc_wsum[n_children_g]

    # ---- matrix batching sumcheck (2*K_LOG variables, 3 claims per child) ----
    # The fresh claim is one value against A0 weighted by lincheck's alpha plus B0;
    # a carried claim is one value per matrix at a shared point.
    lam_mat = HeapBuf(n_children_g ** 3)
    mat_chain = HeapBuf((n_children_g * GEN) ** ACC_SLOTS)
    mat_chain[GEN ** ACC_FS0] = agg_fs[0]
    mat_chain[GEN ** ACC_FS1] = agg_fs[1]
    mat_chain[GEN ** ACC_VALUE] = 0
    for xc in mul_range(1, n_children_g):
        row = mat_chain * xc ** ACC_SLOTS
        st = [row[GEN ** ACC_FS0], row[GEN ** ACC_FS1]]
        st, lam_fresh = squeeze(st)
        st, lam_a = squeeze(st)
        st, lam_b = squeeze(st)
        triple = xc ** 3
        lam_mat[triple] = lam_fresh
        lam_mat[triple * GEN] = lam_a
        lam_mat[triple * GEN ** 2] = lam_b
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        nxt = row * GEN ** ACC_SLOTS
        nxt[GEN ** ACC_FS0] = st[0]
        nxt[GEN ** ACC_FS1] = st[1]
        nxt[GEN ** ACC_VALUE] = row[GEN ** ACC_VALUE] + lam_fresh * fresh[GEN ** FRESH_MATPART] + lam_a * carried[GEN ** DEFER_STMT_A_VALUE] + lam_b * carried[GEN ** DEFER_STMT_B_VALUE]
    mat_end = mat_chain * n_children_g ** ACC_SLOTS
    agg_fs = [mat_end[GEN ** ACC_FS0], mat_end[GEN ** ACC_FS1]]
    mat_running = mat_end[GEN ** ACC_VALUE]
    mat_point = HeapBuf(2 * K_LOG)
    fs0, fs1, mat_running = batch_sumcheck(agg_fs[0], agg_fs[1], mat_msgs, mat_running, mat_point, 2 * K_LOG)
    agg_fs = [fs0, fs1]
    # Terminal weights. A fresh claim's is U_t(r*) = urow_t(r*_row) * wcol_t(r*_col),
    # with row_weight = (sum_i L_i(zz_t) eq(r*[0..6], i)) * eq(zchi_t, r*[6..K_LOG])
    # and col_weight = (sum_i z_partial_t[i] eq(r*[K_LOG..K_LOG+6], i)) * prod_j (1 +
    # lrr_j + r*[2*K_LOG-1-j]) (the lincheck binds column variables top-down). A
    # carried claim's is a plain eq over all 2*K_LOG coordinates.
    eq_rows = HeapBuf(2 ** (K_SKIP + 1) - 2)
    eqtree(mat_point, eq_rows, K_SKIP)
    eq_cols = HeapBuf(2 ** (K_SKIP + 1) - 2)
    eqtree(mat_point * GEN ** K_LOG, eq_cols, K_SKIP)
    w_sums = HeapBuf((n_children_g * GEN) ** PAIR_SLOTS)  # the A and B weight sums
    w_sums[GEN ** 0] = 0
    w_sums[GEN ** 1] = 0
    for xc in mul_range(1, n_children_g):
        fresh = fresh_row[xc]
        row_nums = StackBuf(2 ** K_SKIP)
        lag64(fresh[GEN ** FRESH_Z_SKIP], row_nums, 0)
        row_weight = 0
        for i in unroll(0, 2 ** K_SKIP):
            row_weight += row_nums[i] * eq_rows[GEN ** (2 ** K_SKIP - 2 + i)]
        row_weight *= LAGRANGE_INV_S
        for k in unroll(0, LINCHECK_ROUNDS):
            row_weight *= (1 + fresh[GEN ** (FRESH_ZCHI + k)] + mat_point[GEN ** (K_SKIP + k)])
        col_weight = 0
        for i in unroll(0, 2 ** K_SKIP):
            col_weight += fresh[GEN ** (FRESH_Z_PARTIAL + i)] * eq_cols[GEN ** (2 ** K_SKIP - 2 + i)]
        for j in unroll(0, LINCHECK_ROUNDS):
            col_weight *= (1 + fresh[GEN ** (FRESH_LINCHECK_RS + j)] + mat_point[GEN ** (2 * K_LOG - 1 - j)])
        weight_u = row_weight * col_weight
        carried = carried_row[xc]
        eq_carried = GEN ** 0
        for k in unroll(0, 2 * K_LOG):
            eq_carried *= (1 + carried[GEN ** (DEFER_STMT_MAT_POINT + k)] + mat_point[GEN ** k])
        triple = xc ** 3
        lam_fresh = lam_mat[triple]
        row = w_sums * xc ** PAIR_SLOTS
        row[GEN ** PAIR_SLOTS] = row[GEN ** 0] + lam_fresh * weight_u + lam_mat[triple * GEN] * eq_carried
        row[GEN ** (PAIR_SLOTS + 1)] = row[GEN ** 1] + lam_fresh * fresh[GEN ** FRESH_ALPHA] * weight_u + lam_mat[triple * GEN ** 2] * eq_carried
    w_end = w_sums * n_children_g ** PAIR_SLOTS
    a_star = mat_stars[0]
    b_star = mat_stars[1]
    assert mat_running == a_star * w_end[GEN ** 0] + b_star * w_end[GEN ** 1]

    for k in unroll(0, BYTECODE_VARS):
        defer_stmt[GEN ** k] = bc_point[GEN ** k]
    defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = bytecode_star
    for k in unroll(0, 2 * K_LOG):
        defer_stmt[GEN ** (DEFER_STMT_MAT_POINT + k)] = mat_point[GEN ** k]
    defer_stmt[GEN ** DEFER_STMT_A_VALUE] = a_star
    defer_stmt[GEN ** DEFER_STMT_B_VALUE] = b_star
    return
