# The recursive aggregation guest: zkDSL, not runnable Python (see
# crates/lean_compiler/zkDSL.md). One node of an aggregation tree verifies raw leanXMSS
# and SPHINCS+ signatures and sub-proofs OF THIS SAME BYTECODE, and publishes the
# statement digest binding its signature claims and a possibly empty list of LeanDA roots.
# It may check a blob matrix directly and retain any roots proved by its children.
# Reading order: `main` is the
# node, `verify_sub` the in-circuit copy of `verifier::verify_execution`, and
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
RS_CHUNK = 8  # ring-switch rows per loop iteration
RS_COUNT_BITS = 6  # a ring-switch coordinate count is below 2^RS_COUNT_BITS
# Exponent bit-widths: an announced 32-bit count decomposes into COUNT_BITS bits,
# its top bit constrained to zero so the native strict 32-bit bound holds; any
# structural size (sums of 2^kappa, packing offsets) fits SIZE_BITS bits; and a
# structural LOG (log_mem, log_inv_rate), announced as an integer word and
# raised to a g-power by g_power_of_word, is below SIZE_BITS, so LOG_WORD_BITS bits
# are enough and the reconstruction IS the bound (a larger announced log cannot
# reproduce itself from this many bits).
COUNT_BITS = 33
SIZE_BITS = 34
LOG_WORD_BITS = 6

# ------------------------------------------------------------------- Fiat-Shamir
# An absorbed scalar's fourth lane is its domain tag (fs_pack), so a role is never
# smuggled through the data lanes. The capacity a sponge carries is FS_CELLS cells.
DS_OBSERVE = 1
DS_POW_NONCE = 4
FS_CELLS = 5

# ----------------------------------------------------------- loop-carried chains
# A loop whose state is several fields keeps ONE heap run of N cells per iteration,
# so a step is one pointer multiply rather than one per field.
PAIR_SLOTS = 2  # a two-field chain
# A record's Fiat-Shamir sponge is its FS_CELLS capacity cells, from field *_FS on.
# A Fiat-Shamir chain carrying one accumulator (the claim batching loops).
ACC_FS = 0
ACC_PEND = 5  # the eight rate cells the record's first permutation takes
ACC_VALUE = 13
ACC_SLOTS = 14
# A sponge with a full rate waiting: its capacity, then those eight rate cells.
PEND_SLOTS = 13
# One sumcheck round of the bus GKR or the table batch.
ROUND_FS = 0
ROUND_CURSOR = 5
ROUND_CLAIM = 6
ROUND_SLOTS = 7
# One product layer of the bus GKR.
LAYER_FS = 0
LAYER_CURSOR = 5
LAYER_PUSH = 6
LAYER_PULL = 7
LAYER_COUNT = 8
LAYER_ROW = 9
LAYER_POS = 10
LAYER_HALF = 11  # g^(k // 2) at radix-four layer k
LAYER_PARITY = 12  # k % 2, as a field element
LAYER_PEND = 13  # the four rate cells the layer's first permutation takes: the roots', then zero
LAYER_SLOTS = 17
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
# A table coord's value on its table's padding row (doc sec:e2e-pad), zero for a
# framework coord: a block's rows past its table's announced count flush nothing,
# their leaves being 1, so the decompose adds back what its form sums there.
COORD_PADDING = COORD_PADDING_PLACEHOLDER
# Claim dedup: push/pull share their GKR point, so a column read by two blocks with
# the same kappa (across OR within the sides) is streamed and opened ONCE.
# COORD_FRESH = 1 on the first occurrence (read the stream, fill pool slot
# COORD_CLAIM_SLOT), 0 on a duplicate (reuse that slot).
COORD_FRESH = COORD_FRESH_PLACEHOLDER
COORD_FRESH_POS = COORD_FRESH_POS_PLACEHOLDER  # a fresh coordinate's place among the words the decomposition absorbs
N_FRESH = N_FRESH_PLACEHOLDER
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
# three leaf claims. FLOORS[t] is the table's least log height (the Keccak reduction
# is sized for at least one block of 2^9 steps).
TABLE_XOR = 0
TABLE_MUL = 1
TABLE_SET = 2
TABLE_DEREF = 3
TABLE_JUMP = 4
TABLE_SHA3 = 5
N_TABLES = N_TABLES_PLACEHOLDER
FLOORS = FLOORS_PLACEHOLDER
N_TABLE_COLS = N_TABLE_COLS_PLACEHOLDER
TABLE_COL_BASE = TABLE_COL_BASE_PLACEHOLDER  # a table's first column among all the evaluations
N_COL_EVALS = N_COL_EVALS_PLACEHOLDER
TABLE_COLS_CAP = TABLE_COLS_CAP_PLACEHOLDER
ETA_OFFSET = ETA_OFFSET_PLACEHOLDER
ETA_FORM_BASE = ETA_FORM_BASE_PLACEHOLDER
N_ETA_POWS = N_ETA_POWS_PLACEHOLDER

# ------------------------------------------------- Keccak, by GKR over its rounds
# q_keccak holds a step's state every KECCAK_DEPTH rounds but its output, a lane per
# slot and a word per step; a pack is KECCAK_PACK consecutive steps, embedded in a polynomial of
# degree under KECCAK_EMBED_BITS whose products have KECCAK_PROD_BITS coefficients.
# The *_START / *_IDX pairs are index lists: row i is IDX[START[i] .. START[i + 1]].
KECCAK_DEPTH = KECCAK_DEPTH_PLACEHOLDER
KECCAK_SEGMENTS = KECCAK_SEGMENTS_PLACEHOLDER
KECCAK_SEG_LOG = KECCAK_SEG_LOG_PLACEHOLDER
KECCAK_PACK = KECCAK_PACK_PLACEHOLDER
KECCAK_PACK_LOG = 4
KECCAK_EMBED_BITS = KECCAK_EMBED_BITS_PLACEHOLDER
KECCAK_PROD_BITS = KECCAK_PROD_BITS_PLACEHOLDER
KECCAK_PROJ_START = KECCAK_PROJ_START_PLACEHOLDER
KECCAK_PROJ_IDX = KECCAK_PROJ_IDX_PLACEHOLDER
KECCAK_EMB_START = KECCAK_EMB_START_PLACEHOLDER
KECCAK_EMB_IDX = KECCAK_EMB_IDX_PLACEHOLDER
KECCAK_IOTA_START = KECCAK_IOTA_START_PLACEHOLDER
KECCAK_IOTA_IDX = KECCAK_IOTA_IDX_PLACEHOLDER
KECCAK_PI = KECCAK_PI_PLACEHOLDER
KECCAK_RHO = KECCAK_RHO_PLACEHOLDER
KECCAK_SHIFT_USED = KECCAK_SHIFT_USED_PLACEHOLDER
KECCAK_END_BIT = KECCAK_END_BIT_PLACEHOLDER
KECCAK_LANES = 25
KECCAK_Z_BITS = 6      # a bit position is z + 64 * lane
KECCAK_LANE_BITS = 5
KECCAK_LOCAL_BITS = KECCAK_Z_BITS + KECCAK_LANE_BITS
LANE_OFF = 2 ** KECCAK_LANE_BITS - 2  # where a frame eqtree's last level starts
SLICE_OFF = 2 ** KECCAK_Z_BITS - 2
KECCAK_IOTA_BITS = 7   # iota flips slices 2^i - 1 of lane 0 only
QKECCAK_SLOT_LOG = QKECCAK_SLOT_LOG_PLACEHOLDER
# A claim's record: its value, the sum of its instance weights, pointers to its
# point, its lane table, its slice table and the local point that table is the eq
# of, then the instance weights and its position weights where iota flips.
KC_VALUE = 0
KC_KAPPA = 1
KC_POINT = 2
KC_LANES = 3
KC_LOCAL = 4
KC_SLICES = 5
KC_MU = 6
KC_SIZE = KC_MU + KECCAK_PACK
# One round of a layer's sumcheck over packs and segments.
KR_FS = 0
KR_CURSOR = 5
KR_CLAIM = 6
KR_SCALE = 7
KR_SLOTS = 8
# A layer's round records lie field by field, KR_CAP apart, one per two rounds:
# a layer has tau - 3 < 30 rounds, so at most 16 records.
KR_CAP = 16

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
N_COLUMN_LOGS = N_COLUMN_LOGS_PLACEHOLDER
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
SEL_NIBBLES = (MAX_STACK_LOG + 3) // 4  # four selector bits share one table lookup
SEL_EQ_STRIDE = 30                      # a nibble's eq tables over its top 1..4 coords
EQ_CHAIN_ARMS = SIZE_BITS + QKECCAK_SLOT_LOG + 1  # eq prefix chain lengths
SEL_TAB_NIBBLES = (SIZE_BITS + 3) // 4  # nibbles of a bus selector run
SEL_TAB_EQ_STRIDE = 32                  # a nibble's eq tables over its low 1..4 coords, padded
LIG_N_LEVELS = LIG_N_LEVELS_PLACEHOLDER
LIG_YR_LEVEL = LIG_YR_LEVEL_PLACEHOLDER
LIG_YR_LOG_LEN = LIG_YR_LOG_LEN_PLACEHOLDER
LIG_YR_LEN = LIG_YR_LEN_PLACEHOLDER
LIG_TOTAL_FOLDS = LIG_TOTAL_FOLDS_PLACEHOLDER
LIG_MAX_QUERIES = LIG_MAX_QUERIES_PLACEHOLDER
LIG_MAX_SQUEEZES = LIG_MAX_SQUEEZES_PLACEHOLDER
LIG_MAX_INTERLEAVE = LIG_MAX_INTERLEAVE_PLACEHOLDER
LIG_POSITIONS_LEN = LIG_POSITIONS_LEN_PLACEHOLDER
LIG_CAP_DEPTH = LIG_CAP_DEPTH_PLACEHOLDER
LIG_CAP_OFF = LIG_CAP_OFF_PLACEHOLDER
LIG_CAP_LEN = LIG_CAP_LEN_PLACEHOLDER
LIG_QUERY_GRIND_BITS = LIG_QUERY_GRIND_BITS_PLACEHOLDER
LIG_OOD_SAMPLES = LIG_OOD_SAMPLES_PLACEHOLDER
LIG_QUERIES = LIG_QUERIES_PLACEHOLDER
LIG_FOLDS = LIG_FOLDS_PLACEHOLDER
LIG_INTERLEAVE = LIG_INTERLEAVE_PLACEHOLDER
LIG_LEAF_CELLS = LIG_LEAF_CELLS_PLACEHOLDER
LIG_PACKED_ROW_CAP = LIG_PACKED_ROW_CAP_PLACEHOLDER
LIG_ROW_CAP = LIG_ROW_CAP_PLACEHOLDER
LIG_PATH_CAP = LIG_PATH_CAP_PLACEHOLDER
LIG_TREE_DEPTH = LIG_TREE_DEPTH_PLACEHOLDER
LIG_SQUEEZES = LIG_SQUEEZES_PLACEHOLDER
LIG_POSITIONS_OFF = LIG_POSITIONS_OFF_PLACEHOLDER
LIG_LOG_MSG_COLS = LIG_LOG_MSG_COLS_PLACEHOLDER
LIG_RESIDUAL_FOLD_OFF = LIG_RESIDUAL_FOLD_OFF_PLACEHOLDER
LIG_RESIDUAL_PREFIX_LEN = LIG_RESIDUAL_PREFIX_LEN_PLACEHOLDER
LIG_FOLDS_OFF = LIG_FOLDS_OFF_PLACEHOLDER
LIG_VANISH_OFF = LIG_VANISH_OFF_PLACEHOLDER
LIG_VANISH_VALS = LIG_VANISH_VALS_PLACEHOLDER
LIG_VANISH_INVS = LIG_VANISH_INVS_PLACEHOLDER
LIG_N_CANDIDATES = LIG_N_CANDIDATES_PLACEHOLDER
LIG_MIN_SHIFT_INV = LIG_MIN_SHIFT_INV_PLACEHOLDER
# eval_b claim descriptors. CLAIM_POINT_BUF says which point buffer a pooled
# claim's x-part lives in, CLAIM_COMMITTED_COL maps it to the compact index of the
# committed column it must open (a virtual SHA3 value claim maps to QKECCAK),
# CLAIM_QKECCAK_SLOT_BITS holds the bits of the q_keccak slot a virtual claim reads
# (zero for a non-virtual one), CLAIM_END_LANE marks the one lane committed with
# the padding bit XORed in, and QKECCAK_COMMITTED_COL is the ring-switch target.
# A SHA3 output lane's claim is POINT_BUF_KECCAK_OUT: never opened, the 25 of them,
# from KECCAK_OUT_POOL on, are the Keccak reduction's claim on the output.
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QKECCAK_RHO = 3
POINT_BUF_KECCAK_OUT = 4
KECCAK_OUT_POOL = KECCAK_OUT_POOL_PLACEHOLDER
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_COMMITTED_COL = CLAIM_COMMITTED_COL_PLACEHOLDER
CLAIM_QKECCAK_SLOT_BITS = CLAIM_QKECCAK_SLOT_BITS_PLACEHOLDER
CLAIM_END_LANE = CLAIM_END_LANE_PLACEHOLDER
QKECCAK_COMMITTED_COL = QKECCAK_COMMITTED_COL_PLACEHOLDER
QKECCAK_VARS_CAP = QKECCAK_VARS_CAP_PLACEHOLDER

# ------------------------------------------------------ statements and deferral
# A node defers one claim on the stacked bytecode. DEFER_SIZE is the region one
# sub-proof's verification exports (the claim's point, then its value);
# DEFER_STMT_* index the batched claim a node's OWN statement carries, laid out the
# same way. The Fiat-Shamir seed rides the public input rather than being baked,
# so one compiled guest verifies proofs of any inner program.
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER  # log rows of the bytecode blocks
DEFER_SIZE = DEFER_SIZE_PLACEHOLDER
BYTECODE_VARS = BYTECODE_VARS_PLACEHOLDER  # = BYTECODE_LOG + LOG2_BYTECODE_COLS
FRESH_BC_VALUE = BYTECODE_VARS
DEFER_STMT_CELLS = BYTECODE_VARS + 1
DEFER_STMT_BC_VALUE = BYTECODE_VARS
# The aggregation transcript's seeded capacity, and the zeros padding a child's words
# to whole rates (so every child starts with a full rate waiting).
AGG_SEED_0 = AGG_SEED_0_PLACEHOLDER
AGG_SEED_1 = AGG_SEED_1_PLACEHOLDER
AGG_SEED_2 = AGG_SEED_2_PLACEHOLDER
AGG_SEED_3 = AGG_SEED_3_PLACEHOLDER
AGG_SEED_4 = AGG_SEED_4_PLACEHOLDER
AGG_CHILD_PAD = AGG_CHILD_PAD_PLACEHOLDER
AGG_CHILD_WORDS = 2 + DEFER_SIZE + DEFER_STMT_CELLS
# The statement digest's preimage: the STMT_HEADER header values as the 16-byte
# cells they already are (the seed and the signer-set digest, which itself binds
# both claim lists), then the deferred cells' tower limbs, two to a cell. No domain
# tag: the seed leads, and it binds this bytecode and the Keccak relation.
STMT_HEADER = STMT_HEADER_PLACEHOLDER
STMT_DEFER_OFF = STMT_HEADER
STMT_ODD = STMT_ODD_PLACEHOLDER
STMT_PAIRS = STMT_PAIRS_PLACEHOLDER
STMT_CELLS = STMT_DEFER_OFF + 3 * STMT_PAIRS

# ------------------------------------------------------------------ the hash
# Every hash is Keccak-256 in the cell encoding (primitives::hash::hash): a `sha3`
# block absorbs eight cells, and its output is the SHA3_STATE-cell sponge state,
# whose first two cells are the digest. A hash of runtime length carries that
# state through a heap run between loop frames, SHA3_STATE cells a step.
SHA3_STATE = SHA3_STATE_PLACEHOLDER
# One step of such a chain: the state, then whatever count the loop threads with it.
STATE_SLOTS = SHA3_STATE + 1

# --------------------------------------------------------- WOTS+C (host-supplied)
# Both schemes' one-time keys: chains of CHAIN_LENGTH positions, whose digits are
# dispatched DIGIT_GROUP at a time, the last chain alone, and the leanSPHINCS
# address, a cell whose low lane is lo:32 | hi:24 | type:5 | step:3, its high lane
# zero. TW_* hold the type. Every 16-byte native value is one canonical cell.
W = W_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
CHAIN_STEPS = CHAIN_LENGTH - 1
DIGIT_GROUP = DIGIT_GROUP_PLACEHOLDER
DIGIT_GROUPS = CHAIN_LENGTH ** DIGIT_GROUP
# The digit sum of group k, at k.
DIGIT_SUMS = DIGIT_SUMS_PLACEHOLDER
TW_CHAIN = TW_CHAIN_PLACEHOLDER
TW_LEAF = TW_LEAF_PLACEHOLDER
TW_NODE = TW_NODE_PLACEHOLDER
TW_MSG = TW_MSG_PLACEHOLDER
HI_MUL = 2 ** 32
STEP_MUL = 2 ** 61
DIGEST_CELLS = 2

# ----------------------------------------------------- leanXMSS (host-supplied)
# Two layers of trees of height LX_HEIGHT over keys of LX_V chains. A layer's digest
# is a codeword when its first LX_V digits sum to LX_TARGET_SUM and the rest are
# zero. LX_TOP is the top layer's flag where an address holds it.
LX_V = LX_V_PLACEHOLDER
LX_TARGET_SUM = LX_TARGET_SUM_PLACEHOLDER
LX_HEIGHT = LX_HEIGHT_PLACEHOLDER
LX_TOP = LX_TOP_PLACEHOLDER

# ------------------------------------------------------ SPHINCS+ (host-supplied)
# The scheme's own letters, prefixed SP_: one tree of height SP_H over WOTS+C keys,
# each signing a forest of small WOTS keys.
SP_V = SP_V_PLACEHOLDER
SP_TARGET_SUM = SP_TARGET_SUM_PLACEHOLDER
SP_H = SP_H_PLACEHOLDER
# The forest: SP_TREES trees of height SP_TREE_HEIGHT, each leaf over two subtrees
# of height SP_SUBTREE_HEIGHT, whose leaves are WOTS keys of SP_FCHAINS chains with
# top position SP_FTOP. A codeword is an SP_WORD_BITS-bit index into a table.
SP_TREES = SP_TREES_PLACEHOLDER
SP_TREE_HEIGHT = SP_TREE_HEIGHT_PLACEHOLDER
SP_SUBTREE_HEIGHT = SP_SUBTREE_HEIGHT_PLACEHOLDER
SP_FCHAINS = SP_FCHAINS_PLACEHOLDER
SP_FTOP = SP_FTOP_PLACEHOLDER
SP_WORD_BITS = SP_WORD_BITS_PLACEHOLDER
SP_WORDS = 2 ** SP_WORD_BITS
SP_LEAVES = 2 ** SP_TREE_HEIGHT
SP_KEYS = 2 ** SP_SUBTREE_HEIGHT
# Digit i of codeword t, at SP_FCHAINS * t + i.
SP_CODEWORDS = SP_CODEWORDS_PLACEHOLDER
# The message digest: its first cell is the codewords, a byte per subtree, and its
# second holds bit fields, the index, each tree's leaf, each subtree's WOTS key, and
# bits nothing uses.
SP_CELL_BITS = 2 * BASE_FIELD_BITS
SP_LEAF_OFF = SP_H
SP_KEY_OFF = SP_LEAF_OFF + SP_TREES * SP_TREE_HEIGHT
SP_USED_BITS = SP_KEY_OFF + 2 * SP_TREES * SP_SUBTREE_HEIGHT
SP_UNUSED_BITS = SP_CELL_BITS - SP_USED_BITS
# The forest's hash types.
SP_TW_ENC = SP_TW_ENC_PLACEHOLDER
SP_TW_FCHAIN = SP_TW_FCHAIN_PLACEHOLDER
SP_TW_FKEY_LEAF = SP_TW_FKEY_LEAF_PLACEHOLDER
SP_TW_FSUBNODE = SP_TW_FSUBNODE_PLACEHOLDER
SP_TW_FTREE_LEAF = SP_TW_FTREE_LEAF_PLACEHOLDER
SP_TW_FNODE = SP_TW_FNODE_PLACEHOLDER
# Where a forest position sits in `hi`: tree c | leaf s | subtree j | key a | chain i,
# a subtree node's level and index in place of the key, a tree node's in place of
# the leaf.
SP_LEAF_MUL = 2 ** 3 * HI_MUL
SP_SUBTREE_MUL = 2 ** 7 * HI_MUL
SP_KEY_MUL = 2 ** 8 * HI_MUL
SP_FCHAIN_MUL = 2 ** 11 * HI_MUL
SP_SUBNODE_LEVEL_MUL = 2 ** 8 * HI_MUL
SP_SUBNODE_MUL = 2 ** 10 * HI_MUL
SP_FNODE_LEVEL_MUL = 2 ** 3 * HI_MUL
SP_FNODE_MUL = 2 ** 6 * HI_MUL
# Values bounded a byte at a time: each byte hinted in the exponent, range checked,
# and read as the bits it spells off a table of the SP_BYTE_VALUES bytes.
SP_BYTE_VALUES = 256
# The encoding counter, LE_32 in the low four bytes of its lane: bounded by
# rebuilding it from exactly that many bytes, so the guest accepts no preimage the
# native verifier cannot parse.
SP_COUNTER_BYTES = 4
# The bits past the second cell's fields, likewise: a byte at a time, the last one
# holding the rest.
SP_UNUSED_BYTES = (SP_UNUSED_BITS + 7) // 8
SP_UNUSED_TOP = 2 ** (SP_UNUSED_BITS - 8 * (SP_UNUSED_BYTES - 1))

# --------------------------------------------------------------- node capacities
# MAX_KEYS caps the coverage table's slots, both schemes' declared claims and their
# duplicates, which is what the coverage range check needs below 2^MIN_LOG_MEM;
# MAX_RECURSIONS is the arity of an aggregation tree.
MAX_KEYS = MAX_KEYS_PLACEHOLDER
MAX_DA_ROOTS = MAX_DA_ROOTS_PLACEHOLDER
DA_ROOT_COUNTS = DA_ROOT_COUNTS_PLACEHOLDER
MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER


# ---------------------------------- LeanDA ------------------------------------------
# Blob and cell widths are fixed. The row count is hinted and bounded by DA_MAX_ROWS;
# the Merkle trees dispatch on the checked log of its padded value.
DA_LOG_K = DA_LOG_K_PLACEHOLDER
DA_LOG_CELL = DA_LOG_CELL_PLACEHOLDER
DA_MAX_ROWS = DA_MAX_ROWS_PLACEHOLDER
DA_LOG_MAX_ROWS = DA_LOG_MAX_ROWS_PLACEHOLDER
DA_PAD_CELL_0 = DA_PAD_CELL_0_PLACEHOLDER
DA_PAD_CELL_1 = DA_PAD_CELL_1_PLACEHOLDER
DA_PAD_ROW_0 = DA_PAD_ROW_0_PLACEHOLDER
DA_PAD_ROW_1 = DA_PAD_ROW_1_PLACEHOLDER

DA_CELL = 2 ** DA_LOG_CELL                      # symbols in a cell
DA_BLOCK_BITS = DA_LOG_K + 1 - DA_LOG_CELL      # log of the cells per row
DA_CELLS = 2 ** DA_BLOCK_BITS                   # cells per row
DA_PREFIX_CELLS = 2 ** (DA_LOG_K - DA_LOG_CELL)    # cells in the first half
DA_PACKED = DA_CELL // 2                        # packed 128-bit cells in one cell
DA_WEIGHT_CELLS = 3 * DA_CELL // 2              # packed cells of one cell's weights
DA_TREE_ARMS = DA_LOG_MAX_ROWS + 1              # tree depths the row count can dispatch to

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
def canonical_limbs(word):
    # assert_canonical, keeping the two limbs it binds.
    lo = StackBuf(1)
    hint_f192_limbs(lo, word)
    hi = (word + lo[0]) * Y_INV
    assert_in_k(lo[0], hi)
    return lo[0], hi


@inline
def challenge_from_state(state):
    # Both words are hash outputs with zero top limbs.
    # Hint d2 and derive d3 = (state[1] + d2)/Y.
    # Requiring both in K binds d2 by the tower representation.
    # The challenge uses d2; d3 is checked and discarded.
    d2 = StackBuf(1)
    hint_f192_limbs(d2, state[1])
    d3 = (state[1] + d2[0]) * Y_INV
    assert_in_k(d2[0], d3)
    return state[0] + Y_TOWER * Y_TOWER * d2[0]


# ==================================== Fiat-Shamir ===================================
# A duplex sponge over the SHA3 step in overwrite mode (fiat_shamir::FiatShamirState). The
# sponge is the 13-cell output `sp` of its last permutation, whose last FS_CELLS cells, the
# capacity, are all the next permutation keeps: between functions and loop frames those
# cells are all that travels, `fs0 .. fs4`. Scalars absorbed since wait in an eight-cell
# `rate` run, two cells a scalar, at most four. How many wait is a compile-time count at
# every call site, `k`. A fifth scalar, or a challenge, permutes; every challenge is a
# permutation of its own.


@inline
def fs_pack(rate, k: Const, x, tag):
    # Scalar x as lanes (c0, c1, c2, tag) over rate cells 2k and 2k + 1. SHA3 requires
    # both cells' top limbs to be zero, which binds the hinted c2.
    limbs = StackBuf(3)
    hint_f192_limbs(limbs, x)
    assert_in_k(limbs[2], tag)
    rate[2 * k] = x + Y_TOWER * Y_TOWER * limbs[2]
    rate[2 * k + 1] = limbs[2] + Y_TOWER * tag
    return


@inline
def fs_perm(sp, rate, k: Const):
    # The permutation taking the k waiting scalars: they overwrite the rate, zero past them.
    nxt = StackBuf(SHA3_STATE)
    if k == 0:
        sha3([0, 0], [0, 0], nxt, cap=sp)
    if k == 1:
        sha3(rate[0:2], [0, 0], nxt, cap=sp)
    if k == 2:
        sha3(rate[0:2], rate[2:4], nxt, cap=sp)
    if k == 3:
        rate[6] = 0
        rate[7] = 0
        sha3(rate[0:2], rate[2:4], nxt, tail=rate[4:8], cap=sp)
    if k == 4:
        sha3(rate[0:2], rate[2:4], nxt, tail=rate[4:8], cap=sp)
    return nxt


@inline
def fs_perm4(sp, r0, r1, r2, r3):
    # The permutation whose rate is r0..r3 then zero: up to two waiting scalars, held as
    # cells rather than in a rate run.
    nxt = StackBuf(SHA3_STATE)
    sha3([r0, r1], [r2, r3], nxt, cap=sp)
    return nxt


@inline
def fs_absorb_nonce(sp, rate, k: Const, nonce):
    # A grinding nonce as waiting scalar k (k < 4), with its own tag, then the
    # permutation its challenge comes from.
    fs_pack(rate, k, nonce, DS_POW_NONCE)
    nxt = fs_perm(sp, rate, k + 1)
    return nxt


@inline
def fs_perm_pending(cap, rec, at: Const):
    # The permutation taking a full rate held in the record cells at..at+8.
    nxt = StackBuf(SHA3_STATE)
    sha3([rec[GEN ** at], rec[GEN ** (at + 1)]], [rec[GEN ** (at + 2)], rec[GEN ** (at + 3)]], nxt, tail=[rec[GEN ** (at + 4)], rec[GEN ** (at + 5)], rec[GEN ** (at + 6)], rec[GEN ** (at + 7)]], cap=cap)
    return nxt


@inline
def fs_cap(fs0, fs1, fs2, fs3, fs4):
    # A carried capacity as the run a permutation reads.
    sp = [fs0, fs1, fs2, fs3, fs4]
    return sp


@inline
def fs_load(rec, field: Const, stride: Const):
    # A record's carried capacity, its cells `stride` fields apart from `field` on.
    sp = [rec[GEN ** (field * stride)], rec[GEN ** ((field + 1) * stride)], rec[GEN ** ((field + 2) * stride)], rec[GEN ** ((field + 3) * stride)], rec[GEN ** ((field + 4) * stride)]]
    return sp


@inline
def fs_store(rec, field: Const, stride: Const, sp):
    # Store the capacity of permutation output `sp` as fs_load reads it.
    for j in unroll(0, FS_CELLS):
        rec[GEN ** ((field + j) * stride)] = sp[SHA3_STATE - FS_CELLS + j]
    return


@inline
def fs_next(rate, k: Const, cursor):
    # Fetch and absorb in one act: the word under `cursor` becomes waiting scalar k
    # (k < 4), and the cursor steps one word on. Reading and absorbing are inseparable,
    # so no proof-stream word can enter the computation unbound: the soundness
    # invariant the whole guest rests on.
    x = cursor[GEN ** 0]
    fs_pack(rate, k, x, DS_OBSERVE)
    return x, cursor * GEN


@inline
def squeeze(sp, rate, k: Const):
    # A challenge: the permutation taking the k waiting scalars, read off its first three
    # lanes. Returns the new sponge and the challenge.
    nxt = fs_perm(sp, rate, k)
    challenge = challenge_from_state(nxt)
    return nxt, challenge


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


def g_power_of_word(value):
    # g^value for a concrete integer `value` < 2^LOG_WORD_BITS: advice-decompose its
    # bits, tie them back to the word, and assemble Π g^(bit_j·2^j).
    bits = StackBuf(LOG_WORD_BITS)
    hint_decompose_bits(bits, value, LOG_WORD_BITS)
    word = 0
    g_value = GEN ** 0
    for j in unroll(0, LOG_WORD_BITS):
        bit = bits[j]
        bits[j] = bit * bit
        word += bit * (2 ** j)
        g_value *= 1 + bit * (1 + GEN ** (2 ** j))
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
    psum_buf = HeapBuf(SIZE_BITS + 1)  # psum_buf[g^j] = value of bits [0, j)
    psum_buf[GEN ** 0] = 0
    word = 0
    exp_prod = GEN ** 0
    for j in unroll(0, nbits):
        bit = bits_buf[GEN ** j]
        assert bit * bit == bit
        exp_prod *= (1 + bit * (g_squares[GEN ** j] + 1))
        word += bit * (2 ** j)
        psum_buf[GEN ** (j + 1)] = word
    for j in unroll(nbits + 1, SIZE_BITS + 1):
        psum_buf[GEN ** j] = word
    g_log = hint_log2_ceil(bits_buf, nbits, floor)  # prover advice; verified below
    assert log(g_log) < SIZE_BITS
    assert log(g_log / (GEN ** floor)) < SIZE_BITS
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


def grind_check(word, nbits: Const):
    # WHIR query grinding: the challenge drawn right after the nonce is absorbed must
    # have its low nbits zero (transcript::pow_bits_ok, nbits < 64). That window lives
    # in the challenge's FIRST 64-bit lane, the low limb of the permutation output's
    # first cell `word`: only that lane is advice-decomposed and verified. The honest
    # prover searches the deterministic u64 subset while verification permits the
    # full field: each candidate still costs one permutation and succeeds with
    # probability 2^-bits.
    lanes = StackBuf(1)
    hint_f192_limbs(lanes, word)
    high = (word + lanes[0]) * Y_INV
    assert_in_k(lanes[0], high)
    # The lane is rebuilt from its bits at and above nbits only, which IS the claim
    # that its low nbits coordinates are zero; the hinted low bits go unread.
    lane_bits = StackBuf(BASE_FIELD_BITS)
    hint_decompose_bits(lane_bits, lanes[0], BASE_FIELD_BITS)
    acc = 0
    for i in unroll(nbits, BASE_FIELD_BITS):
        b = lane_bits[i]
        lane_bits[i] = b * b  # booleanity, as a write-once pin
        acc += b * COORD_BASIS[i]
    assert acc == lanes[0]
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
def eqtree_frame(point_ptr, out, n_coords: Const, count: Const):
    # eqtree into frame cells, in the same layout, the last level cut at `count`
    # (which must exceed half of it).
    r0 = point_ptr[GEN ** 0]
    out[0] = 1 + r0
    out[1] = r0
    for t in unroll(1, n_coords):
        rt = point_ptr[GEN ** t]
        one_plus_rt = 1 + rt
        for i in unroll(0, 2 ** t):
            pw = out[2 ** t - 2 + i]
            out[2 ** (t + 1) - 2 + i] = pw * one_plus_rt
            if const(t + 1 == n_coords):
                if (2 ** t + i) // count == 0:
                    out[2 ** (t + 1) - 2 + 2 ** t + i] = pw * rt
            else:
                out[2 ** (t + 1) - 2 + 2 ** t + i] = pw * rt
    return


def eq_prefix_chain(chain, seed, a, b1, count_g):
    # Prefix products of eq(a_k, b_k) = a_k + b1_k, b1 = 1 + b, from `seed`, so a
    # reader picks the partial product up at its own certified length. Entry t is
    # written from inputs with index < t only, so a garbage tail past a buffer's
    # written extent cannot corrupt any shorter prefix.
    assert log(count_g) < EQ_CHAIN_ARMS
    done = match(log(count_g), range(0, EQ_CHAIN_ARMS), lambda n: eq_prefix_run(chain, seed, a, b1, n))  # a match needs a target
    return


def eq_prefix_run(chain, seed, a, b1, n: Const):
    chain[GEN ** 0] = seed
    v = seed
    for k in unroll(0, n):
        v = v * (a[GEN ** k] + b1[GEN ** k])
        chain[GEN ** (k + 1)] = v
    return 0


def plus_one_run(out, src, n: Const):
    for k in unroll(0, n):
        out[GEN ** k] = 1 + src[GEN ** k]
    return 0


def rs_eq_run(chain, z_vals, point1, count_g):
    # One run of the telescoped ring-switch product E = sum_k c_k * prod_j
    # (z_j^(2^k) + 1 + ris_j): coordinate x multiplies row k by (z^(2^k) + 1 +
    # point_x), z evolving by squaring per row. The runtime coordinates walk
    # OUTSIDE and the fixed Frobenius powers inside, so nothing stores a z-power
    # table. Coordinates go two an iteration, so a row is read and written once
    # per pair; count = 2 * half + odd is pinned from advice bits, and an odd
    # count's last coordinate runs after the loop. Returns the final row.
    bits = StackBuf(RS_COUNT_BITS)
    hint_decompose_bits_exponent(bits, count_g, RS_COUNT_BITS)
    odd = bits[0]
    bits[0] = odd * odd
    half_g = GEN ** 0
    for k in unroll(1, RS_COUNT_BITS):
        b = bits[k]
        bits[k] = b * b
        half_g *= 1 + b * (1 + GEN ** (2 ** (k - 1)))
    odd_g = 1 + odd * (1 + GEN)
    assert half_g * half_g * odd_g == count_g
    for xp in mul_range(1, half_g):
        pair = xp * xp
        zs = z_vals * pair
        ps = point1 * pair
        zv_0 = zs[GEN ** 0]
        zv_1 = zs[GEN ** 1]
        one_plus_0 = ps[GEN ** 0]
        one_plus_1 = ps[GEN ** 1]
        row = chain * xp ** BASE_FIELD_BITS
        nxt = row * GEN ** BASE_FIELD_BITS
        for k in unroll(0, BASE_FIELD_BITS):
            nxt[GEN ** k] = row[GEN ** k] * (zv_0 + one_plus_0) * (zv_1 + one_plus_1)
            if k != BASE_FIELD_BITS - 1:
                zv_0 *= zv_0
                zv_1 *= zv_1
    if odd == 1:
        last = half_g * half_g
        zv = z_vals[last]
        one_plus = point1[last]
        row = chain * half_g ** BASE_FIELD_BITS
        nxt = row * GEN ** BASE_FIELD_BITS
        for k in unroll(0, BASE_FIELD_BITS):
            nxt[GEN ** k] = row[GEN ** k] * (zv + one_plus)
            if k != BASE_FIELD_BITS - 1:
                zv *= zv
    return chain * (half_g * odd_g) ** BASE_FIELD_BITS


def fold_final_msg(msg, point, log_len: Const):
    weights = StackBuf(2 * YR_LOG_CAP)
    for j in unroll(0, log_len):
        weights[2 * j] = 1 + point[GEN ** j]
        weights[2 * j + 1] = point[GEN ** j]
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


def sumcheck_round4(rd, msg_cursor, claim):
    # One PLAIN sumcheck round, from the sponge of round record `rd` into the next
    # record's. The prover sends the round polynomial's coefficients bar the one the
    # split h(0) + h(1) == claim fixes, so the verifier derives that one and reads h
    # at the challenge by Horner. Nothing is reapplied: no eq factor, no separate
    # term for the tables still waiting, and the eq point is not read here at all.
    sp = fs_load(rd, ROUND_FS, 1)
    rate = StackBuf(8)
    c0, msg_cursor = fs_next(rate, 0, msg_cursor)
    c2, msg_cursor = fs_next(rate, 1, msg_cursor)
    c3, msg_cursor = fs_next(rate, 2, msg_cursor)
    # The split identity fixes c1 = claim + c2 + c3, so it is neither sent nor bound,
    # and h(y) = c0 + y (claim + (1 + y) (c2 + (1 + y) c3)).
    sp, y = squeeze(sp, rate, 3)
    fs_store(rd * GEN ** ROUND_SLOTS, ROUND_FS, 1, sp)
    y1 = 1 + y
    return msg_cursor, c0 + y * (claim + y1 * (c2 + y1 * c3)), y


def gkr_rounds(rd, pt, n: Const):
    # n GKR rounds, from the round record at `rd` (fields GKR_ROUNDS_CAP apart) to the
    # one n further. The prover sends every coefficient but c0, which the round's
    # pulled-out eq factor leaves fixed: c0 + r (c1 + ... + c4) == claim, r being the
    # previous point's coordinate pt[q]; the challenge goes to pt[MU_CAP + 2 + q].
    sp = fs_load(rd, ROUND_FS, GKR_ROUNDS_CAP)
    cur = rd[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)]
    claim = rd[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)]
    for q in unroll(0, n):
        rate = StackBuf(8)
        c1, cur = fs_next(rate, 0, cur)
        c2, cur = fs_next(rate, 1, cur)
        c3, cur = fs_next(rate, 2, cur)
        c4, cur = fs_next(rate, 3, cur)
        sp, rk = squeeze(sp, rate, 4)
        c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
        pt[GEN ** (MU_CAP + 2 + q)] = rk
        claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
    rd_next = rd * GEN ** n
    fs_store(rd_next, ROUND_FS, GKR_ROUNDS_CAP, sp)
    rd_next[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)] = cur
    rd_next[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)] = claim
    return


def batch_sumcheck(fs0, fs1, fs2, fs3, fs4, msgs, running, point, n_rounds: Const):
    # The rounds of a claim-batching sumcheck: two hinted values per round
    # (g(1) and g(inf)), the split fixing the third against the running claim, and
    # the challenges collected into `point`.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    for rd in unroll(0, n_rounds):
        rate = StackBuf(8)
        msg_g1, c = fs_next(rate, 0, msgs * GEN ** (2 * rd))
        msg_ginf, c = fs_next(rate, 1, c)
        sp, rv = squeeze(sp, rate, 2)
        point[GEN ** rd] = rv
        g_zero = running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        running = (msg_ginf * rv + c_one) * rv + g_zero  # fold the degree-2 round at rv
    return sp[8], sp[9], sp[10], sp[11], sp[12], running


# ==================================== Merkle paths ==================================


@inline
def verify_merkle_path(leaf, direction_bits, depth: Const):
    # Hinted child pairs are hashed in order; the boolean query bit selects the
    # child that must equal the running node, binding each link of the path.
    path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:4 * depth], "merkle_children")
    # The selected pair starts at path_ptr * g^(2*bit) = path_ptr + bit * path_step.
    path_ptr = addr(path)
    path_step = path_ptr * (1 + GEN ** 2)
    node = leaf
    for level in unroll(0, depth):
        selected = path_ptr + direction_bits[GEN ** level] * path_step
        selected[GEN ** (4 * level)] = node[0]
        selected[GEN ** (4 * level + 1)] = node[1]
        node = StackBuf(SHA3_STATE)
        sha3(path[4 * level:4 * level + 2], path[4 * level + 2:4 * level + 4], node)
    return node


def verify_merkle_cap(cap, flags, depth: Const):
    # Unrolled over the cap's nodes, so every address is an immediate. Every node's
    # hinted digest (node k at heap cells 2k, 2k+1) is read once into a frame run,
    # and an internal node's run is SHA3_STATE cells long so that its hash can
    # write its state there, the digest landing on (and so asserting) the hinted
    # value. An active (flagged) node is hashed; an inactive one pins its children's
    # flags to zero, so every active node's parent is active too, up to the root,
    # which is always hashed. The queries flag the parents of the cap leaves they
    # reach. The run is sized per depth, the cap depths a configuration reaches.
    if depth != 0:
        n_leaves = 2 ** depth
        if const(depth == 4):
            runs = StackBuf(15 * 16 - 13)
        elif const(depth == 5):
            runs = StackBuf(15 * 32 - 13)
        elif const(depth == 6):
            runs = StackBuf(15 * 64 - 13)
        elif const(depth == 7):
            runs = StackBuf(15 * 128 - 13)
        else:
            runs = StackBuf(15 * 256 - 13)
        # internal node k (1 <= k < n_leaves) at SHA3_STATE * (k - 1), leaf k after them
        for node in unroll(1, 2 * n_leaves):
            if const(node // n_leaves == 0):
                at = SHA3_STATE * (node - 1)
            else:
                at = SHA3_STATE * (n_leaves - 1) + 2 * (node - n_leaves)
            runs[at] = cap[GEN ** (2 * node)]
            runs[at + 1] = cap[GEN ** (2 * node + 1)]
        for node in unroll(1, n_leaves):
            if const(2 * node // n_leaves == 0):
                left = SHA3_STATE * (2 * node - 1)
                right = SHA3_STATE * (2 * node)
            else:
                left = SHA3_STATE * (n_leaves - 1) + 2 * (2 * node - n_leaves)
                right = left + 2
            at = SHA3_STATE * (node - 1)
            if const(node == 1):
                sha3(runs[left:left + 2], runs[right:right + 2], runs[at:at + SHA3_STATE])
            else:
                if flags[GEN ** node] != 0:
                    sha3(runs[left:left + 2], runs[right:right + 2], runs[at:at + SHA3_STATE])
                else:
                    if const(2 * node // n_leaves == 0):  # node has flagged children
                        flags[GEN ** (2 * node)] = 0
                        flags[GEN ** (2 * node + 1)] = 0
        root_0 = runs[0]
        root_1 = runs[1]
    else:
        root_0 = cap[GEN ** 2]
        root_1 = cap[GEN ** 3]
    return root_0, root_1


# ============================== the stacked WHIR opening ============================


def opening_fold(fs0, fs1, fs2, fs3, fs4, w0, w1, cursor, c0, c1, c2):
    # One fold round: its challenge takes the two scalars waiting in the sponge, w0 and
    # w1, and the next round's two coefficients, returned, wait in their place.
    cap = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    fs_pack(rate, 0, w0, DS_OBSERVE)
    fs_pack(rate, 1, w1, DS_OBSERVE)
    sp, r = squeeze(cap, rate, 2)
    claim = (c2 * r + c1) * r + c0
    rate = StackBuf(8)
    c0, cursor = fs_next(rate, 0, cursor)
    c2, cursor = fs_next(rate, 1, cursor)
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, claim, c0, c2, r


def opening_ood_point(fs0, fs1, fs2, fs3, fs4, r0, r1, r2, r3, r4, r5, r6, r7, point, n: Const):
    # One specialization per point dimension. The first coordinate's permutation takes
    # the rate r0..r7, the scalars waiting in the sponge and zero past them.
    cap = fs_cap(fs0, fs1, fs2, fs3, fs4)
    sp = StackBuf(SHA3_STATE)
    sha3([r0, r1], [r2, r3], sp, tail=[r4, r5, r6, r7], cap=cap)
    point[GEN ** 0] = challenge_from_state(sp)
    no_rate = StackBuf(8)
    for x in unroll(1, n):
        sp, r = squeeze(sp, no_rate, 0)
        point[GEN ** x] = r
    return sp[8], sp[9], sp[10], sp[11], sp[12]


def opening_final_message(fs0, fs1, fs2, fs3, fs4, w0, w1, cursor, out, n: Const):
    # The final message's n words, after the two scalars waiting in the sponge, w0 and
    # w1, then the grinding nonce and the permutation its challenge comes from. Returns
    # that output's first cell, its capacity, the cursor past the nonce, and the nonce.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    fs_pack(rate, 0, w0, DS_OBSERVE)
    fs_pack(rate, 1, w1, DS_OBSERVE)
    for pos in unroll(2, 2 + n):
        if pos % 4 == 0:
            sp = fs_perm(sp, rate, 4)
            rate = StackBuf(8)
        value, cursor = fs_next(rate, pos % 4, cursor)
        out[GEN ** (pos - 2)] = value
    nonce = cursor[GEN ** 0]
    if const((2 + n) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    sp = fs_absorb_nonce(sp, rate, (2 + n) % 4, nonce)
    return sp[0], sp[8], sp[9], sp[10], sp[11], sp[12], cursor * GEN, nonce


def opening_row_weights(point, out, folds: Const, reverse: Const):
    # The row's eq weights as their two tensor factors: weight i is
    # out[i % 2^lo] * out[2^lo + i // 2^lo], the low `lo` coordinates first. At
    # level 0 lane i is interleaving index 2^folds - 1 - i, which reverses both.
    if const(folds // 3 == 0):
        lo = folds
    else:
        lo = 3
    hi = folds - lo
    for i in unroll(0, 2 ** lo):
        if reverse == 1:
            slot = 2 ** lo - 1 - i
        else:
            slot = i
        out[GEN ** i] = eq_weight(point, lo, slot, 0)
    for i in unroll(0, 2 ** hi):
        if reverse == 1:
            slot = 2 ** hi - 1 - i
        else:
            slot = i
        out[GEN ** (2 ** lo + i)] = eq_weight(point * GEN ** lo, hi, slot, 0)
    return


@inline
def opening_query(cap, flags, row_eq_weights, direction_bits, base: Const, interleave: Const, leaf_cells: Const, depth: Const, cap_depth: Const):
    # One query: hash the hinted row up its Merkle path into the shared cap, and
    # return its dot product with the row's eq weights.
    if base == 1:
        row_len = interleave
    else:
        row_len = 3 * interleave
    row = StackBuf(LIG_ROW_CAP)
    hint_witness(row[0:row_len], "merkle_leaf_rows")
    row_dot = 0
    packed_row = StackBuf(LIG_PACKED_ROW_CAP)
    if base == 1:
        # Packing proves each hinted lane is in K before hashing or folding it.
        for jb in unroll(0, interleave // 2):
            packed_row[jb] = pack64x2(row[2 * jb], row[2 * jb + 1])
    else:
        # Pack the checked tower limbs into the leaf's contiguous byte image.
        for jb in unroll(0, 3 * interleave // 2):
            packed_row[jb] = pack64x2(row[2 * jb], row[2 * jb + 1])
    # The weights' tensor factors (opening_row_weights): a run of lo_len row
    # entries shares one hi factor.
    if const(interleave // 8 == 0):
        lo_len = interleave
    else:
        lo_len = 8
    for h in unroll(0, interleave // lo_len):
        part = 0
        for l in unroll(0, lo_len):
            jw = lo_len * h + l
            if base == 1:
                row_word = row[jw]
            elif 3 * jw % 2 == 0:
                # limbs (3w, 3w+1) are a pack; add Y^2 * limb(3w+2).
                row_word = packed_row[3 * jw // 2] + Y_TOWER * Y_TOWER * row[3 * jw + 2]
            else:
                # limbs (3w+1, 3w+2) are a pack; shift it by Y and add limb(3w).
                row_word = row[3 * jw] + Y_TOWER * packed_row[(3 * jw + 1) // 2]
            part += row_word * row_eq_weights[GEN ** l]
        row_dot += row_eq_weights[GEN ** (lo_len + h)] * part
    # Hash the packed row, eight cells a block.
    leaf_hash_state = StackBuf(SHA3_STATE)
    sha3_cells(packed_row[0:leaf_cells], leaf_hash_state)
    path_depth = depth - cap_depth
    node = verify_merkle_path(leaf_hash_state, direction_bits, path_depth)
    if cap_depth != 0:
        # The reached cap leaf is node 2*parent + bit at cells 2*node, 2*node + 1,
        # where parent = 2^(cap_depth-1) + q: q in the exponent, the constant
        # parts folded into the address immediates.
        if const(cap_depth == 1):
            flags[GEN] = 1
            leaf = cap * (1 + direction_bits[GEN ** path_depth] * (1 + GEN ** 2))
        else:
            q = 1 + direction_bits[GEN ** (path_depth + 1)] * (1 + GEN)
            for bit in unroll(1, cap_depth - 1):
                q *= 1 + direction_bits[GEN ** (path_depth + 1 + bit)] * (1 + GEN ** (2 ** bit))
            flags_q = flags * q
            flags_q[GEN ** (2 ** (cap_depth - 1))] = 1  # the cap check propagates this obligation to the root
            q2 = q * q
            leaf = cap * q2 * q2 * (1 + direction_bits[GEN ** path_depth] * (1 + GEN ** 2))
        leaf[GEN ** (2 ** (cap_depth + 1))] = node[0]
        leaf[GEN ** (2 ** (cap_depth + 1) + 1)] = node[1]
    else:
        cap[GEN ** 2] = node[0]
        cap[GEN ** 3] = node[1]
    return row_dot


def opening_queries(cap, flags, lam, lam_n, query_bit_ptrs, row_eq_weights, n_iters_g, odd: Const, base: Const, interleave: Const, leaf_cells: Const, depth: Const, cap_depth: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the weight reads; an odd count runs its first query alone,
    # ahead of the pairs. Extension rows run one query an iteration.
    # Query k is weighted lam^k: the chain runs h <- (h + dot_k) / lam, ending at
    # sum_k lam^(k - n) dot_k, and one product by lam_n = lam^n restores it.
    mu = 1 / lam
    chain = HeapBuf(n_iters_g * GEN)
    if odd == 1:
        chain[GEN ** 0] = opening_query(cap, flags, row_eq_weights, query_bit_ptrs[GEN ** 0], base, interleave, leaf_cells, depth, cap_depth) * mu
    else:
        chain[GEN ** 0] = 0
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            bit_ptrs = query_bit_ptrs * xi * xi
            d0 = opening_query(cap, flags, row_eq_weights, bit_ptrs[GEN ** odd], base, interleave, leaf_cells, depth, cap_depth)
            d1 = opening_query(cap, flags, row_eq_weights, bit_ptrs[GEN ** (odd + 1)], base, interleave, leaf_cells, depth, cap_depth)
            chain[xi * GEN] = ((chain[xi] + d0) * mu + d1) * mu
        else:
            d = opening_query(cap, flags, row_eq_weights, query_bit_ptrs[xi], base, interleave, leaf_cells, depth, cap_depth)
            chain[xi * GEN] = (chain[xi] + d) * mu
    return chain[n_iters_g] * lam_n


@inline
def residual_query(basis_chain, row_d, vanish: Const, n_cols: Const):
    # prod_t (d_t + chain_t) over one query's message-column coordinates, chain_0
    # being the query position.
    prefix_eq = row_d[GEN ** 0] + basis_chain
    for t in unroll(1, n_cols):
        # subspace-vanishing recurrence for the novel-basis point
        basis_chain *= basis_chain + LIG_VANISH_VALS[vanish + t - 1]
        prefix_eq *= row_d[GEN ** t] + basis_chain
    return prefix_eq


def open_stacked(m_idx: Const, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor):
    # The stacked WHIR opening, one specialization per (rate, committed log-size)
    # candidate: every LIG_* table reads row m_idx, per level row `ml`, and all
    # opening proof data is hinted here, so only the executed arm pops its streams.
    #
    # The returned point is in witness order. Round-order challenges stay local
    # for the induced weights, OOD claims, and residual evaluation.
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
    # Between rounds the sponge rides fs0..fs4, its capacity, and w0, w1, the two
    # scalars waiting in it: the last round polynomial's sent coefficients.
    msg_cursor = cursor
    round_quad_c = msg_cursor[GEN ** 0]  # the round polynomial in coefficients
    round_quad_a = msg_cursor[GEN ** 1]  # bar the linear one, which the split fixes
    msg_cursor = msg_cursor * GEN ** 2
    w0 = round_quad_c
    w1 = round_quad_a
    round_quad_b = target + round_quad_a
    sumcheck_target = target

    # Caps are shared across queries; rows and paths are hinted in each query's frame.
    merkle_caps = HeapBuf(GEN ** (4 * LIG_CAP_LEN[m_idx]))
    hint_witness(merkle_caps[0:4 * LIG_CAP_LEN[m_idx]], "merkle_caps")
    cap_flags = HeapBuf(GEN ** LIG_CAP_LEN[m_idx])
    hint_witness(cap_flags[0:LIG_CAP_LEN[m_idx]], "merkle_cap_active")
    final_msg = HeapBuf(GEN ** yr_len)  # filled from the stream at the last level
    # Each cap root is checked against its transcript-bound level root.
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
            fs0, fs1, fs2, fs3, fs4, msg_cursor, sumcheck_target, round_quad_c, round_quad_a, fold_challenge = opening_fold(fs0, fs1, fs2, fs3, fs4, w0, w1, msg_cursor, round_quad_c, round_quad_b, round_quad_a)
            w0 = round_quad_c
            w1 = round_quad_a
            fold_challenges[GEN ** (folds_off + j)] = fold_challenge
            round_quad_b = sumcheck_target + round_quad_a

        if lvl == yr_level:
            word0, fs0, fs1, fs2, fs3, fs4, msg_cursor, q_nonce = opening_final_message(fs0, fs1, fs2, fs3, fs4, w0, w1, msg_cursor, final_msg, yr_len)
        else:
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            fs_pack(rate, 0, w0, DS_OBSERVE)
            fs_pack(rate, 1, w1, DS_OBSERVE)
            next_root_a, msg_cursor = fs_next(rate, 2, msg_cursor)
            next_root_b, msg_cursor = fs_next(rate, 3, msg_cursor)
            # A non-canonical half is rejected (`Digest::from_halves` in `crates/verifier`), as
            # the commitment root was at its own read.
            canon = StackBuf(2)
            canon[0] = assert_canonical(next_root_a)
            canon[1] = assert_canonical(next_root_b)
            level_roots[GEN ** (2 * lvl + 2)] = next_root_a
            level_roots[GEN ** (2 * lvl + 3)] = next_root_b
            # OOD binding for the newly observed level-(lvl+1) commitment. The
            # random point has the just-folded witness dimension, namely this
            # level's message-column dimension.
            # The point's first permutation takes what waits: the fold's coefficients and
            # the root, four scalars, or the previous sample's three.
            for os in unroll(0, LIG_OOD_SAMPLES[ml + 1]):
                oz = ood_z * GEN ** (((lvl + 1) * LIG_MAX_OOD_SAMPLES + os) * LIG_LOG_MSG_COLS_CAP)
                if os == 0:
                    fs0, fs1, fs2, fs3, fs4 = opening_ood_point(fs0, fs1, fs2, fs3, fs4, rate[0], rate[1], rate[2], rate[3], rate[4], rate[5], rate[6], rate[7], oz, LIG_LOG_MSG_COLS[ml])
                else:
                    fs0, fs1, fs2, fs3, fs4 = opening_ood_point(fs0, fs1, fs2, fs3, fs4, rate[0], rate[1], rate[2], rate[3], rate[4], rate[5], 0, 0, oz, LIG_LOG_MSG_COLS[ml])
                sample = ood * GEN ** ((lvl + 1) * ood_stride + os * OOD_SLOTS)
                rate = StackBuf(8)
                ood_y, msg_cursor = fs_next(rate, 0, msg_cursor)
                ood_c0, msg_cursor = fs_next(rate, 1, msg_cursor)
                ood_c2, msg_cursor = fs_next(rate, 2, msg_cursor)
                sample[GEN ** OOD_Y] = ood_y
                sample[GEN ** OOD_C0] = ood_c0
                sample[GEN ** OOD_C2] = ood_c2  # the split fixes c1 = y + c2
            q_nonce = msg_cursor[GEN ** 0]
            msg_cursor = msg_cursor * GEN
            if LIG_OOD_SAMPLES[ml + 1] == 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
                sp = fs_absorb_nonce(sp, rate, 0, q_nonce)
            else:
                sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
                sp = fs_absorb_nonce(sp, rate, 3, q_nonce)
            word0 = sp[0]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above.
        if LIG_QUERY_GRIND_BITS[ml] != 0:
            grind_check(word0, LIG_QUERY_GRIND_BITS[ml])
        else:
            assert q_nonce == 0

        sqz = HeapBuf((GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1)) ** FS_CELLS)
        sqz[GEN ** 0] = fs0
        sqz[GEN ** 1] = fs1
        sqz[GEN ** 2] = fs2
        sqz[GEN ** 3] = fs3
        sqz[GEN ** 4] = fs4
        for xs in mul_range(1, GEN ** LIG_SQUEEZES[ml]):
            # a loop body captures free names BY VALUE, so the compile-time aliases
            # are rebound here (m_idx and lvl are substituted literals)
            depth = LIG_TREE_DEPTH[m_idx * LIG_MAX_LEVELS + lvl]
            pos_off = LIG_POSITIONS_OFF[m_idx * LIG_MAX_LEVELS + lvl]
            row = sqz * xs ** FS_CELLS
            row_cap = fs_load(row, 0, 1)
            no_rate = StackBuf(8)
            row_sp, packed_word = squeeze(row_cap, no_rate, 0)
            fs_store(row * GEN ** FS_CELLS, 0, 1, row_sp)
            query_ptr = xs ** (FIELD_BITS // depth)
            decode_query_bits(packed_word, query_positions * GEN ** pos_off * query_ptr, query_bit_ptrs * GEN ** pos_off * query_ptr, depth)
        sqz_end = sqz * (GEN ** LIG_SQUEEZES[ml]) ** FS_CELLS
        sp = fs_load(sqz_end, 0, 1)

        # One batching challenge for the level, drawn once every claim it batches is
        # fixed: its OOD claims above and these query positions. Claim tau of the
        # level is weighted lam^tau, the running claim keeping lam^0 (Annex B,
        # Protocol 1 step 1): query i is claim n_ood + 1 + i, so its weight splits
        # into lam^i here and the level scalar lam^(n_ood+1) below.
        no_rate = StackBuf(8)
        sp, lam = squeeze(sp, no_rate, 0)
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
        opening_row_weights(fold_challenges * GEN ** folds_off, row_eq_weights, LIG_FOLDS[ml], 1 // (lvl + 1))

        cap_depth = LIG_CAP_DEPTH[ml]
        cap = merkle_caps * GEN ** (4 * LIG_CAP_OFF[ml])
        flags = cap_flags * GEN ** LIG_CAP_OFF[ml]
        root_0, root_1 = verify_merkle_cap(cap, flags, cap_depth)
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        level_query_sum = opening_queries(cap, flags, lam, lam_pow, query_bit_ptrs * GEN ** pos_off, row_eq_weights, GEN ** (n_queries // (1 + 1 // (lvl + 1))), n_queries % 2 * (1 // (lvl + 1)), 1 // (lvl + 1), interleave, LIG_LEAF_CELLS[ml], depth, cap_depth)

        # Every level, including the last, ties its commitment in through an intro
        # message. The level's claims then enter the running one with powers of
        # `lam`: the OOD claims held above first, then this query batch.
        intro_c0 = msg_cursor[GEN ** 0]
        intro_c2 = msg_cursor[GEN ** 1]
        msg_cursor = msg_cursor * GEN ** 2
        fs0 = sp[8]
        fs1 = sp[9]
        fs2 = sp[10]
        fs3 = sp[11]
        fs4 = sp[12]
        w0 = intro_c0
        w1 = intro_c2
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
        fs0, fs1, fs2, fs3, fs4, msg_cursor, sumcheck_target, round_quad_c, round_quad_a, tail_c = opening_fold(fs0, fs1, fs2, fs3, fs4, w0, w1, msg_cursor, round_quad_c, round_quad_b, round_quad_a)
        w0 = round_quad_c
        w1 = round_quad_a
        tail_challenges[GEN ** j] = tail_c
        round_quad_b = sumcheck_target + round_quad_a
    # The closing round sends no following message.
    tail_cap = fs_cap(fs0, fs1, fs2, fs3, fs4)
    tail_rate = StackBuf(8)
    fs_pack(tail_rate, 0, w0, DS_OBSERVE)
    fs_pack(tail_rate, 1, w1, DS_OBSERVE)
    tail_sp, tail_last = squeeze(tail_cap, tail_rate, 2)
    tail_challenges[GEN ** (yr_log - 1)] = tail_last
    sumcheck_target = round_quad_c + tail_last * round_quad_b + tail_last * tail_last * round_quad_a
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The folds bind coordinates in ROUND order, and level 0's folds are the lane
    # fold, binding the witness's TOP k coordinates: lane l of the commitment is the
    # stack block q[l * 2^(mu-k) ...], which is what makes the witness's zero
    # padding whole lanes for the committer to leave out of the encode. Every
    # transparent weight downstream is written in witness coordinates, so rotate the
    # point left by those k rounds here, while the level shape is still
    # compile-time. Padding is zero so shared prefix chains may compute unused
    # entries above m without reading uninitialized cells.
    lane_folds = LIG_FOLDS[m_idx * LIG_MAX_LEVELS]
    fold_head = n_folds - lane_folds
    # point1 = 1 + point, the form every eq factor reads.
    point = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    point1 = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG)
    for j in unroll(0, fold_head):
        point[GEN ** j] = fold_challenges[GEN ** (lane_folds + j)]
        point1[GEN ** j] = 1 + fold_challenges[GEN ** (lane_folds + j)]
    for j in unroll(0, yr_log):
        point[GEN ** (fold_head + j)] = tail_challenges[GEN ** j]
        point1[GEN ** (fold_head + j)] = 1 + tail_challenges[GEN ** j]
    for j in unroll(0, lane_folds):
        point[GEN ** (fold_head + yr_log + j)] = fold_challenges[GEN ** j]
        point1[GEN ** (fold_head + yr_log + j)] = 1 + fold_challenges[GEN ** j]
    for j in unroll(n_folds + yr_log, SIZE_BITS + QKECCAK_SLOT_LOG):
        point[GEN ** j] = 0
        point1[GEN ** j] = 1

    # ---- per-level induced bases at the single terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates; only the novel-basis chain (the query position's
    # subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # fold coords then tail coords). Factoring b_t = c_t * inv_t out of every
    # coordinate leaves (a_t / b_t) + chain_t per query, so a query is one add and
    # one multiply a coordinate, and the level's product of the b_t scales its sum
    # once. A zero challenge makes b_t zero and the division unsatisfiable, which
    # rejects rather than accepts.
    basis_d = HeapBuf(GEN ** (n_levels * LIG_LOG_MSG_COLS_CAP))
    level_scale = HeapBuf(GEN ** n_levels)
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        scale = level_betas[GEN ** lvl]
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * LIG_VANISH_INVS[vanish + t]
            basis_d[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * LIG_VANISH_INVS[vanish + prefix_len + j]
            basis_d[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
        level_scale[GEN ** lvl] = scale
    inner_chain = HeapBuf(GEN ** (n_levels + 1))
    inner_chain[GEN ** 0] = 0
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        basis_row = lvl * LIG_LOG_MSG_COLS_CAP
        residual_chain = HeapBuf(GEN ** (max_q + 1))
        residual_chain[GEN ** 0] = 0
        # Two queries an iteration share the row's reads and constants.
        for xr in mul_range(1, GEN ** (LIG_QUERIES[ml] // 2)):
            ml = m_idx * LIG_MAX_LEVELS + lvl  # rebound: the body captures by value
            vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
            basis_row = lvl * LIG_LOG_MSG_COLS_CAP
            max_q = LIG_MAX_QUERIES[m_idx]
            pair = xr * xr
            positions = query_positions * GEN ** LIG_POSITIONS_OFF[ml] * pair
            weights = query_weights * GEN ** (lvl * max_q) * pair
            row_d = basis_d * GEN ** basis_row
            eq_0 = residual_query(positions[GEN ** 0], row_d, vanish, LIG_LOG_MSG_COLS[ml])
            eq_1 = residual_query(positions[GEN ** 1], row_d, vanish, LIG_LOG_MSG_COLS[ml])
            residual_chain[xr * GEN] = residual_chain[xr] + weights[GEN ** 0] * eq_0 + weights[GEN ** 1] * eq_1
        level_sum = residual_chain[GEN ** (LIG_QUERIES[ml] // 2)]
        if const(LIG_QUERIES[ml] % 2 == 1):
            last = LIG_QUERIES[ml] - 1
            eq_last = residual_query(query_positions[GEN ** (LIG_POSITIONS_OFF[ml] + last)], basis_d * GEN ** basis_row, vanish, LIG_LOG_MSG_COLS[ml])
            level_sum = level_sum + query_weights[GEN ** (lvl * max_q + last)] * eq_last
        # accumulate beta_lvl * prod_t b_t * (per-level residual sum) into the grand residual
        inner_chain[GEN ** (lvl + 1)] = inner_chain[GEN ** lvl] + level_scale[GEN ** lvl] * level_sum

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
    return sumcheck_target, point, point1, inner_chain[GEN ** n_levels] + ood_inner, yr_at_tail


# ============================== inner-proof verification ============================
# The phases of `verify_sub`, in the order it runs them. Each takes and returns the
# Fiat-Shamir state pair and the stream cursor, so the sequence is what binds them.


def verify_bus_gkr(fs0, fs1, fs2, fs3, fs4, cursor, g_bus_mu, zeta):
    # ONE GKR grand product over push, pull and count, RLC-batched. Push and pull
    # have equal depth (matched blocks) and the count tree is padded with identity
    # leaves up to it (product unchanged), so a single sumcheck serves all three.
    # Radix four contracts two binary levels per layer, each batched by a fresh λ
    # squeezed at its start. All three trees reduce to the one shared point `zeta`,
    # which this fills, returning their three leaf values with the walked
    # Fiat-Shamir state and stream cursor.
    layers = HeapBuf((g_bus_mu * GEN ** 2) ** LAYER_SLOTS)  # mu + 2 layers
    rounds = HeapBuf(GKR_ROUNDS_CAP * ROUND_SLOTS)
    gkr_pts = HeapBuf(GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    root_push, cursor = fs_next(rate, 0, cursor)
    root_pull = root_push
    root_count, cursor = fs_next(rate, 1, cursor)
    assert root_count != 0  # count-tree root nonzero: no read count self-cancels
    # The roots wait in the sponge until the first layer's challenge: a layer's first
    # permutation takes its LAYER_PEND cells, which are zero for every later layer.
    for j in unroll(0, FS_CELLS):
        layers[GEN ** (LAYER_FS + j)] = sp[j]
    for j in unroll(0, 4):
        layers[GEN ** (LAYER_PEND + j)] = rate[j]
    layers[GEN ** LAYER_CURSOR] = cursor
    layers[GEN ** LAYER_PUSH] = root_push
    layers[GEN ** LAYER_PULL] = root_pull
    layers[GEN ** LAYER_COUNT] = root_count
    layers[GEN ** LAYER_ROW] = gkr_pts
    layers[GEN ** LAYER_POS] = GEN ** 0
    layers[GEN ** LAYER_HALF] = GEN ** 0
    layers[GEN ** LAYER_PARITY] = 0

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
        layer_cap = fs_load(layers, LAYER_FS, 1)
        tail_sp = fs_perm4(layer_cap, layers[GEN ** LAYER_PEND], layers[GEN ** (LAYER_PEND + 1)], layers[GEN ** (LAYER_PEND + 2)], layers[GEN ** (LAYER_PEND + 3)])
        lam = challenge_from_state(tail_sp)
        rate = StackBuf(8)
        tcur = layers[GEN ** LAYER_CURSOR]
        tclaim = layers[GEN ** LAYER_PUSH] + lam * (layers[GEN ** LAYER_PULL] + lam * layers[GEN ** LAYER_COUNT])
        nextrow = layers[GEN ** LAYER_ROW] * GEN ** MU_CAP
        evals = StackBuf(2 * N_GKR_SIDES)  # the two children of each side, in side order
        for i in unroll(0, 2 * N_GKR_SIDES):
            if i % 4 == 0:
                if i != 0:
                    tail_sp = fs_perm(tail_sp, rate, 4)
                    rate = StackBuf(8)
            ev, tcur = fs_next(rate, i % 4, tcur)
            evals[i] = ev
        combined = 0
        for i in unroll(0, N_GKR_SIDES):
            side = N_GKR_SIDES - 1 - i  # Horner in lam, so the top side lands last
            combined = evals[2 * side] * evals[2 * side + 1] + lam * combined
        assert tclaim == combined
        tail_sp, c0 = squeeze(tail_sp, rate, (2 * N_GKR_SIDES + 3) % 4 + 1)
        nextrow[GEN ** 0] = c0
        nxt = layers * GEN ** LAYER_SLOTS
        fs_store(nxt, LAYER_FS, 1, tail_sp)
        for j in unroll(0, 4):
            nxt[GEN ** (LAYER_PEND + j)] = 0
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            nxt[GEN ** (LAYER_PUSH + side)] = evals[2 * side] + c0 * (evals[2 * side] + evals[2 * side + 1])
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN
        nxt[GEN ** LAYER_HALF] = GEN ** 0
        nxt[GEN ** LAYER_PARITY] = 0

    for x_pair in mul_range(1, pair_bounds[g_bus_mu]):
        sq = x_pair * x_pair
        x_layer = sq * depth_shift[g_bus_mu]
        layer = layers * x_layer ** LAYER_SLOTS
        layer_cap = fs_load(layer, LAYER_FS, 1)
        layer_sp = fs_perm4(layer_cap, layer[GEN ** LAYER_PEND], layer[GEN ** (LAYER_PEND + 1)], layer[GEN ** (LAYER_PEND + 2)], layer[GEN ** (LAYER_PEND + 3)])
        lam = challenge_from_state(layer_sp)
        point_row = layer[GEN ** LAYER_ROW]
        round_pos = layer[GEN ** LAYER_POS]
        nextrow = point_row * GEN ** MU_CAP
        # Round i's record keeps field k at rounds * g^(k GKR_ROUNDS_CAP + i), so a
        # round's record is one product away from the counter.
        head = rounds * round_pos
        fs_store(head, ROUND_FS, GKR_ROUNDS_CAP, layer_sp)
        head[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)] = layer[GEN ** LAYER_CURSOR]
        head[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)] = layer[GEN ** LAYER_PUSH] + lam * (layer[GEN ** LAYER_PULL] + lam * layer[GEN ** LAYER_COUNT])
        # 2k rounds, or 2k + 1 when the depth is odd: four a loop step, the state
        # between them staying in the frame, then two when k is odd, then the odd one.
        half = layer[GEN ** LAYER_HALF]
        parity = layer[GEN ** LAYER_PARITY]
        for x4 in mul_range(1, half):
            step = x4 ** 4
            rd = head * step
            pt = point_row * step
            round_sp = fs_load(rd, ROUND_FS, GKR_ROUNDS_CAP)
            cur = rd[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)]
            claim = rd[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)]
            for q in unroll(0, 4):
                # As in gkr_rounds.
                rate = StackBuf(8)
                c1, cur = fs_next(rate, 0, cur)
                c2, cur = fs_next(rate, 1, cur)
                c3, cur = fs_next(rate, 2, cur)
                c4, cur = fs_next(rate, 3, cur)
                round_sp, rk = squeeze(round_sp, rate, 4)
                c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
                pt[GEN ** (MU_CAP + 2 + q)] = rk  # nextrow[round * g^2]
                claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
            rd_next = rd * GEN ** 4
            fs_store(rd_next, ROUND_FS, GKR_ROUNDS_CAP, round_sp)
            rd_next[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)] = cur
            rd_next[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)] = claim
        if parity != 0:
            quad = half ** 4
            gkr_rounds(head * quad, point_row * quad, 2)
        if x_layer != sq:
            gkr_rounds(head * sq, point_row * sq, 1)
        tail = head * x_layer
        tail_sp = fs_load(tail, ROUND_FS, GKR_ROUNDS_CAP)
        rate = StackBuf(8)
        tcur = tail[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)]
        tclaim = tail[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)]
        evals = StackBuf(4 * N_GKR_SIDES)  # the four children of each side, in side order
        for i in unroll(0, 4 * N_GKR_SIDES):
            if i % 4 == 0:
                if i != 0:
                    tail_sp = fs_perm(tail_sp, rate, 4)
                    rate = StackBuf(8)
            ev, tcur = fs_next(rate, i % 4, tcur)
            evals[i] = ev
        combined = 0
        for i in unroll(0, N_GKR_SIDES):
            side = N_GKR_SIDES - 1 - i  # Horner in lam, so the top side lands last
            combined = evals[4 * side] * evals[4 * side + 1] * evals[4 * side + 2] * evals[4 * side + 3] + lam * combined
        assert tclaim == combined
        tail_sp, c0 = squeeze(tail_sp, rate, (4 * N_GKR_SIDES + 3) % 4 + 1)
        tail_sp, c1 = squeeze(tail_sp, rate, 0)
        nextrow[GEN ** 0] = c0
        nextrow[GEN ** 1] = c1
        nxt = layer * GEN ** (2 * LAYER_SLOTS)
        fs_store(nxt, LAYER_FS, 1, tail_sp)
        for j in unroll(0, 4):
            nxt[GEN ** (LAYER_PEND + j)] = 0
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            lo = evals[4 * side] + c0 * (evals[4 * side] + evals[4 * side + 1])
            hi = evals[4 * side + 2] + c0 * (evals[4 * side + 2] + evals[4 * side + 3])
            nxt[GEN ** (LAYER_PUSH + side)] = lo + c1 * (lo + hi)
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = round_pos * x_layer * GEN
        nxt[GEN ** LAYER_HALF] = half * (1 + parity * (1 + GEN))
        nxt[GEN ** LAYER_PARITY] = 1 + parity
    last = layers * g_bus_mu ** LAYER_SLOTS
    cursor = last[GEN ** LAYER_CURSOR]
    final_point_row = last[GEN ** LAYER_ROW]
    for xt in mul_range(1, g_bus_mu):
        zeta[xt] = final_point_row[xt]  # the ONE shared point
    return last[GEN ** LAYER_FS], last[GEN ** (LAYER_FS + 1)], last[GEN ** (LAYER_FS + 2)], last[GEN ** (LAYER_FS + 3)], last[GEN ** (LAYER_FS + 4)], cursor, last[GEN ** LAYER_PUSH], last[GEN ** LAYER_PULL], last[GEN ** LAYER_COUNT]


def index_mle(zeta, n: Const):
    # The Index coordinate's MLE over the block's n = κ low coords:
    # prod_t (1 + zeta_t * (1 + g^(2^t))).
    v = GEN ** 0
    for t in unroll(0, n):
        if t == 0:
            v = 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
        else:
            v *= 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
    return v


@inline
def sel_eq_nibble(out, z, z1, width: Const):
    # The eq tables over coordinates z[0..t] for t < width, level t at 2^(t+1) - 2,
    # coordinate t being index bit t; z1 = 1 + z.
    levels = StackBuf(SEL_EQ_STRIDE)
    levels[0] = z1[GEN ** 0]
    levels[1] = z[GEN ** 0]
    for t in unroll(1, width):
        r = z[GEN ** t]
        r1 = z1[GEN ** t]
        for i in unroll(0, 2 ** t):
            levels[2 ** (t + 1) - 2 + i] = levels[2 ** t - 2 + i] * r1
            levels[2 ** (t + 1) - 2 + 2 ** t + i] = levels[2 ** t - 2 + i] * r
    for i in unroll(0, 2 ** (width + 1) - 2):
        out[GEN ** i] = levels[i]
    return


@inline
def sel_g_nibble(out, gs, width: Const):
    # out[u] = prod_t gs[t]^(bit t of u) for u < 2^width.
    vals = StackBuf(16)
    vals[0] = 1
    vals[1] = gs[GEN ** 0]
    for t in unroll(1, width):
        g_t = gs[GEN ** t]
        for i in unroll(0, 2 ** t):
            vals[2 ** t + i] = vals[i] * g_t
    for i in unroll(0, 2 ** width):
        out[GEN ** i] = vals[i]
    return


def sel_partial_nibble(eq_out, g_out, z, z1, gs, width: Const):
    if const(width != 0):
        sel_eq_nibble(eq_out, z, z1, width)
        sel_g_nibble(g_out, gs, width)
    return 0


def shared_selector_tables(eq_tab, g_tab, zeta_hi, zeta1_hi, gsq_hi, len_g):
    # Per nibble j of a selector run of length n = 4q + r (coordinates 4j..4j+3
    # past κ, the last nibble r wide), the eq tables over its low 1..4
    # coordinates and the g-powers of its indices' offset shares. The split of n
    # is advice, each bit pinned and the whole tied back to len_g.
    nb = StackBuf(6)
    hint_decompose_bits_exponent(nb, len_g, 6)
    for k in unroll(0, 6):
        b = nb[k]
        nb[k] = b * b
    r_g = (1 + nb[0] * (1 + GEN)) * (1 + nb[1] * (1 + GEN ** 2))
    q_g = GEN ** 0
    for k in unroll(2, 6):
        q_g *= 1 + nb[k] * (1 + GEN ** (2 ** (k - 2)))
    q4 = q_g ** 4
    assert q4 * r_g == len_g
    for xq in mul_range(1, q_g):
        x4 = xq ** 4
        x16 = x4 ** 4
        sel_eq_nibble(eq_tab * x16 * x16, zeta_hi * x4, zeta1_hi * x4, 4)
        sel_g_nibble(g_tab * x16, gsq_hi * x4, 4)
    q16 = q4 ** 4
    done = match(log(r_g), range(0, 4), lambda w: sel_partial_nibble(eq_tab * q16 * q16, g_tab * q16, zeta_hi * q4, zeta1_hi * q4, gsq_hi * q4, w))  # a match needs a target
    return


def block_selector_tab(sel_bits, eq_tab, g_tab, n: Const):
    # block_selector off the shared tables: per nibble, the pinned bits fold into a
    # g-power index g^u, u below the nibble's table size, that reads its eq factor
    # and its share of g^offset.
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for j in unroll(0, (n + 3) // 4):
        width = 4
        if const(j == n // 4):
            width = n - 4 * j
        idx = GEN ** 0
        for t in unroll(0, width):
            sbit = sel_bits[GEN ** (4 * j + t)]
            sel_bits[GEN ** (4 * j + t)] = sbit * sbit  # booleanity as a write-once pin
            idx *= 1 + sbit * (1 + GEN ** (2 ** t))
        eq *= eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * idx]
        rebuilt *= g_tab[GEN ** (16 * j) * idx]
    return eq, rebuilt


def block_selector(sel_bits, zeta1_hi, idxc_hi, n: Const):
    # A bus block's eq over its n = mu - κ selector bits, the offset's bits above κ,
    # each boolean-pinned, and g^offset rebuilt from those bits alone (weights
    # g^(2^(κ+k)) = idxc_hi[k] + 1), which the caller pins to the certified offset.
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for k in unroll(0, n):
        sbit = sel_bits[GEN ** k]
        sel_bits[GEN ** k] = sbit * sbit  # booleanity as a write-once pin
        if k == 0:
            eq = sbit + zeta1_hi[GEN ** k]  # eq over GF(2) is 1 + b + z
            rebuilt = 1 + sbit * idxc_hi[GEN ** k]
        else:
            eq *= sbit + zeta1_hi[GEN ** k]
            rebuilt *= 1 + sbit * idxc_hi[GEN ** k]
    return eq, rebuilt


def padding_weight(rows, zeta, tau: Const):
    # pad_n(zeta[..tau]) for n = rows <= 2^tau (doc lem:suffix). The advice is the bits
    # of n + (2^tau - 1): the complements of n's low bits, as the step reads them, then
    # n's bit tau, set only alone.
    word = rows + const(2 ** tau - 1)
    bits = StackBuf(N_COLUMN_LOGS)
    hint_decompose_bits(bits, word, tau + 1)
    pad = 1
    for k in unroll(0, tau):
        c = bits[k]
        bits[k] = c * c
        z = zeta[GEN ** k]
        pad = c * z + (c + z) * pad
    top = bits[tau]
    bits[tau] = top * top
    # tau is the least height holding n iff lead == 1 and rest != 0: n's highest
    # bit is tau - 1 with more below it, or n = 2^tau.
    if tau == 0:
        low = 0
        lead = 1
        rest = 1
    else:
        # The bits below bit tau - 1, by Horner from their high end: one constant, 2.
        below = 0
        for k in unroll(1, tau):
            below = below * 2 + bits[tau - 1 - k]
        low = below + bits[tau - 1] * (2 ** (tau - 1))
        lead = top + 1 + bits[tau - 1]
        rest = top + below + const(2 ** (tau - 1) - 1)
    assert low + top * (2 ** tau) == word
    assert top * (low + const(2 ** tau - 1)) == 0
    return (1 + top) * pad, lead, rest


def verify_tables(fs0, fs1, fs2, fs3, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, block_kappa, g_squares, fp_w, beta, claim_pool, claim_cplen_g, chi, claim_push, claim_pull, claim_count):
    # Settle the bus against the six tables, in four steps: certify each side's
    # leaf-cube tiling, decompose the three GKR leaf values over it, run the ONE
    # table sumcheck they all reduce to, and bind the public input. Pooled claims
    # land in claim_pool/claim_cplen_g and the reduced point in `chi`; the batch's
    # round count g^n, the deferred bytecode share and the PI point come back.
    #
    # Bus-leaf packing offsets, for the selector certification. Each side's blocks
    # tile its leaf cube, block b at offset_b, and offsets accumulate as
    # g^offset = Π_{earlier} g^(2^κ). The hinted order is certified to be the
    # native one, as certify_placement does for the columns: descending κ, then
    # ascending block index, the guest's per-side block order being the native
    # verifier's (framework blocks, then each table's in table order). The
    # decompose below pins each block's selector bits against this offset, forcing
    # κ-alignment. Pull's blocks mirror push's and share zeta, so only push and
    # count need offsets (pull's slots go unread).
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
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
        prev_g = GEN ** 0
        prev_kappa = GEN ** 0
        for r in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            global_g = sort_order[GEN ** r]       # g^{global block index at this rank}
            assert log(global_g) < N_BLOCKS       # a valid block index
            assert block_side_tab[global_g] == s  # ...belonging to THIS side
            kappa_g = block_kappa[global_g]
            if r != SIDE_BLOCK_START[s]:
                assert log(prev_kappa / kappa_g) < SIZE_BITS  # κ non-increasing
                if prev_kappa == kappa_g:
                    # A side's blocks share one base, so ascending global index is
                    # the native ascending index.
                    assert log(global_g / prev_g) < N_BLOCKS
            # write-once: a repeat collides (g_off has grown since), so the side's
            # ranks name as many distinct blocks of the side as it has, omitting none
            block_off_g[global_g] = g_off
            g_off *= g_squares[kappa_g]
            prev_g = global_g
            prev_kappa = kappa_g

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
    # Each table's padding rows: their weight on a claim at zeta[..tau], dispatched on
    # its hinted log height tau, which this certifies: the least holding its rows, or
    # its floor. A table is at most the stack, so tau has an arm.
    pad_weight = StackBuf(N_TABLES)
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        assert log(tau_g) < N_COLUMN_LOGS
        rows = table_rows[GEN ** t]
        pad_weight[t], lead, rest = match(log(tau_g), range(0, N_COLUMN_LOGS), lambda tau: padding_weight(rows, zeta, tau))
        if FLOORS[t] == 0:
            assert lead == 1
            assert rest != 0
        else:
            assert log(tau_g / GEN ** FLOORS[t]) < N_COLUMN_LOGS
            if tau_g != GEN ** FLOORS[t]:
                assert lead == 1
                assert rest != 0
    idxc_tab = HeapBuf(SIZE_BITS)  # INDEX_MLE_FACTORS[t] = 1 + g^(2^t)
    for t in unroll(0, SIZE_BITS):
        idxc_tab[GEN ** t] = INDEX_MLE_FACTORS[t]
    zeta1 = HeapBuf(g_bus_mu)  # 1 + zeta, so an eq factor 1 + b + z is one XOR
    zeta1_done = match(log(g_bus_mu), range(0, SIZE_BITS), lambda n: plus_one_run(zeta1, zeta, n))  # a match needs a target
    # A block sized by table t's tau (kappa source 2 + t, unadjusted) has
    # block_kappa = kappa_base[2 + t] = dims_g[t + 1] (verify_sub), so all of one
    # table's blocks walk the same selector run and read the same tables.
    shared_len = StackBuf(N_TABLES)
    shared_eq = HeapBuf(N_TABLES * SEL_TAB_NIBBLES * SEL_TAB_EQ_STRIDE)
    shared_g = HeapBuf(N_TABLES * SEL_TAB_NIBBLES * 16)
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        shared_len[t] = g_bus_mu / tau_g
        assert log(shared_len[t]) < SIZE_BITS
        shared_selector_tables(shared_eq * GEN ** (t * SEL_TAB_NIBBLES * SEL_TAB_EQ_STRIDE), shared_g * GEN ** (t * SEL_TAB_NIBBLES * 16), zeta * tau_g, zeta1 * tau_g, g_squares * tau_g, shared_len[t])
    bus_table_total = StackBuf(N_GKR_SIDES)  # per side, what its tables' blocks owe
    block_eq_hi = StackBuf(N_BLOCKS)         # every block's eq_hi, reused below
    block_index_mle = HeapBuf(N_BLOCKS)      # per push block with an Index coord
    beta_1 = beta + 1
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
                offset_bits = HeapBuf(GEN ** SIZE_BITS)
                hint_decompose_bits_exponent(offset_bits, block_off_g[GEN ** b], SIZE_BITS)
                shared = 0
                if const(BLOCK_KAPPA_SRC[b] // 2 != 0):
                    if const(BLOCK_KAPPA_ADJ[b] == 0):
                        shared = 1
                if const(shared == 1):
                    t = BLOCK_KAPPA_SRC[b] - 2
                    sel_bits = offset_bits * dims_g[GEN ** (t + 1)]
                    len_g = shared_len[t]
                    tab_eq = shared_eq * GEN ** (t * SEL_TAB_NIBBLES * SEL_TAB_EQ_STRIDE)
                    tab_g = shared_g * GEN ** (t * SEL_TAB_NIBBLES * 16)
                    eq_hi, goff = match(log(len_g), range(0, SIZE_BITS), lambda n: block_selector_tab(sel_bits, tab_eq, tab_g, n))
                else:
                    sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                    assert log(sel_len_g) < SIZE_BITS
                    sel_bits = offset_bits * kappa_g
                    zeta1_hi = zeta1 * kappa_g
                    idxc_hi = idxc_tab * kappa_g
                    eq_hi, goff = match(log(sel_len_g), range(0, SIZE_BITS), lambda n: block_selector(sel_bits, zeta1_hi, idxc_hi, n))
                assert goff == block_off_g[GEN ** b]  # bits == offset >> κ, κ-aligned
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
                            if COORD_FRESH_POS[ci] % 4 == 0:
                                if COORD_FRESH_POS[ci] != 0:
                                    sp = fs_perm(sp, rate, 4)
                                    rate = StackBuf(8)
                            coord_val, cursor = fs_next(rate, COORD_FRESH_POS[ci] % 4, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = coord_val
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g  # cplen = block kappa
                        else:
                            coord_val = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                    if COORD_TYPE[ci] == COORD_KIND_GCOL:
                        if COORD_FRESH[ci] == 1:
                            if COORD_FRESH_POS[ci] % 4 == 0:
                                if COORD_FRESH_POS[ci] != 0:
                                    sp = fs_perm(sp, rate, 4)
                                    rate = StackBuf(8)
                            rawv, cursor = fs_next(rate, COORD_FRESH_POS[ci] % 4, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = rawv
                            claim_cplen_g[GEN ** COORD_CLAIM_SLOT[ci]] = kappa_g
                        else:
                            rawv = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                        coord_val = COORD_CONST[ci] * rawv
                    if COORD_TYPE[ci] == COORD_KIND_INDEX:
                        if s == PULL_SIDE:
                            coord_val = block_index_mle[GEN ** (b - SIDE_BLOCK_START[PULL_SIDE])]
                        else:
                            coord_val = match(log(kappa_g), range(0, SIZE_BITS), lambda n: index_mle(zeta, n))
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
        # The table sumcheck sums a table block's form phi over every row, padding
        # rows included, whose leaves are 1 instead: the difference, (1 - phi(p_j))
        # times the table's pad_weight, is public and joins the padding mass. A pull
        # block has its push twin's eq_hi and padding tuple, so pull owes what push does.
        if s == PULL_SIDE:
            acc += push_padding
        else:
            padding_sum = 0
            for t in unroll(0, N_TABLES):
                table_sum = 0
                for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
                    if BLOCK_TABLE[b] == t:
                        if s == COUNT_SIDE:
                            coeff = 1
                        else:
                            coeff = beta_1
                        for i in unroll(0, BLOCK_COORD_COUNT[b]):
                            ci = BLOCK_COORD_OFF[b] + i
                            if const(COORD_PADDING[ci] != 0):
                                if s == COUNT_SIDE:
                                    coeff += COORD_PADDING[ci]
                                else:
                                    coeff += fp_w[GEN ** i] * COORD_PADDING[ci]
                        table_sum += block_eq_hi[b] * coeff
                padding_sum += pad_weight[t] * table_sum
            acc += padding_sum
            if s == PUSH_SIDE:
                push_padding = padding_sum
        acc += 1 + selector_sum
        # What the tables' blocks owe this side: its GKR leaf value less the
        # framework decomposition. DERIVED, not read: a transmitted total would be a
        # free value in its own check. The table sumcheck's target pins it below.
        bus_table_total[s] = acc + gkr_claims[s]
    claim_idx = N_BUS_CLAIMS  # AIR/PI/pin claims pool after the deduped bus claims

    # ---- ONE table sumcheck for all six tables ----
    # Mirrors leanvm_core::constraints::verify. zc_xi ONCE, each table folding its own
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
    sp, zc_xi = squeeze(sp, rate, (N_FRESH + 3) % 4 + 1)
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
    fs_store(zc_rounds, ROUND_FS, 1, sp)
    zc_rounds[GEN ** ROUND_CURSOR] = cursor
    zc_rounds[GEN ** ROUND_CLAIM] = bus_target
    zc_cprod[GEN ** 0] = 1
    for xk in mul_range(1, g_zc_n):
        rd = zc_rounds * xk ** ROUND_SLOTS
        ncur, nclaim, rk = sumcheck_round4(rd, rd[GEN ** ROUND_CURSOR], rd[GEN ** ROUND_CLAIM])
        chi[g_zc_n * INV_GEN / xk] = rk  # g^(n-1-j): the variable round j binds
        nxt = rd * GEN ** ROUND_SLOTS
        nxt[GEN ** ROUND_CURSOR] = ncur
        nxt[GEN ** ROUND_CLAIM] = nclaim
        # cprod is the weight of a table that joins here; peq below is the rest
        zc_cprod[xk * GEN] = zc_cprod[xk] * rk
    zc_last = zc_rounds * g_zc_n ** ROUND_SLOTS
    sp = fs_load(zc_last, ROUND_FS, 1)
    rate = StackBuf(8)
    cursor = zc_last[GEN ** ROUND_CURSOR]
    claim = zc_last[GEN ** ROUND_CLAIM]
    # peq[g^tau] = eq(zeta[..tau], chi[..tau]), as a prefix chain.
    zc_peq = HeapBuf(g_zc_n * GEN)
    eq_prefix_chain(zc_peq, 1, chi, zeta1, g_zc_n)
    # Per table: every committed column's evaluation (pooled), its AIR constraint
    # at its own reduced point chi[..tau_t], weighted into the batch's final claim.
    air_acc = 0
    for t in unroll(0, N_TABLES):
        tau_g = dims_g[GEN ** (t + 1)]
        col_evals = StackBuf(TABLE_COLS_CAP)
        for pos in unroll(TABLE_COL_BASE[t], TABLE_COL_BASE[t] + N_TABLE_COLS[t]):
            if pos % 4 == 0:
                if pos != 0:
                    sp = fs_perm(sp, rate, 4)
                    rate = StackBuf(8)
            e, cursor = fs_next(rate, pos % 4, cursor)
            col_evals[pos - TABLE_COL_BASE[t]] = e
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

    # ---- public-input binding claim: one per MEM limb, read off no stream ----
    # The VM's bind_pi_claim claims each committed MEM limb at [rm, 0..] equals
    # that limb's line through the public words, lo_0 + rm*(lo_0 + lo_1) and so
    # on, which the statement alone determines. canonical_limbs binds each word's
    # limbs and proves its top limb zero, so the top claim is zero (doc sec:e2e-pi).
    sp, rm = squeeze(sp, rate, (N_COL_EVALS + 3) % 4 + 1)
    lo_0, hi_0 = canonical_limbs(pi_0)
    lo_1, hi_1 = canonical_limbs(pi_1)
    claim_pool[GEN ** claim_idx] = lo_0 + rm * (lo_0 + lo_1)
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = hi_0 + rm * (hi_0 + hi_1)
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = 0
    claim_idx += 1
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, g_zc_n, bc_share, rm


@inline
def carry_step(c0, c1, n0, n1, e_t, u_t, v_t, t: Const):
    # Extend every t-bit prefix p of r by bit t of r, to p and p + 2^t: c0[p], c1[p]
    # weigh the carry 0 and 1 into bit t, and e_t, u_t, v_t are bit t's weights for
    # (x, y) equal, (1, 0) and (0, 1). The zero prefix never carries.
    for p in unroll(0, 2 ** t):
        if p == 0:
            n0[0] = c0[0] * e_t
            n0[2 ** t] = c0[0] * u_t
            n1[2 ** t] = c0[0] * v_t
        else:
            n0[p] = c0[p] * e_t + c1[p] * u_t
            n1[p] = c1[p] * v_t
            n0[p + 2 ** t] = c0[p] * u_t
            n1[p + 2 ** t] = c0[p] * v_t + c1[p] * e_t
    return


@inline
def carry_wrap(c0, c1, out, e_t, s_t, t: Const):
    # carry_step's last bit, the carry out dropped: u_t + v_t = s_t weighs it either way.
    for p in unroll(0, 2 ** t):
        if p == 0:
            out[0] = c0[0] * e_t
            out[2 ** t] = c0[0] * s_t
        else:
            out[p] = c0[p] * e_t + c1[p] * s_t
            out[p + 2 ** t] = c0[p] * s_t + c1[p] * e_t
    return


@inline
def keccak_shifts_eq(a, b, shifts):
    # shifts[r] for every used r: the multilinear extension of "x = y + r mod 64" at
    # (a, b), a ripple of the carry over the six bits. Split r = rl + 8 rh: the low
    # three bits leave a carry c into the high three, which then add rh + c, so
    # shifts[r] = L0[rl] H[rh] + L1[rl] H[rh + 1] over tables of eight.
    w_eq = StackBuf(KECCAK_Z_BITS)
    w_sum = StackBuf(KECCAK_Z_BITS)
    w_up = StackBuf(KECCAK_Z_BITS)
    w_down = StackBuf(KECCAK_Z_BITS)
    # Bits 0 and 3 start the two tables: their weights are the first level itself.
    lo0 = StackBuf(2)
    lo1 = StackBuf(2)
    hi0 = StackBuf(2)
    hi1 = StackBuf(2)
    for t in unroll(0, KECCAK_Z_BITS):
        a_t = a[GEN ** t]
        b_t = b[GEN ** t]
        both = a_t * b_t
        w_sum[t] = a_t + b_t
        if t == 0:
            lo0[0] = 1 + w_sum[t]
            lo0[1] = a_t + both
            lo1[1] = b_t + both
        elif t == 3:
            hi0[0] = 1 + w_sum[t]
            hi0[1] = a_t + both
            hi1[1] = b_t + both
        else:
            w_eq[t] = 1 + w_sum[t]
            w_up[t] = a_t + both
            w_down[t] = b_t + both
    mid0 = StackBuf(4)
    mid1 = StackBuf(4)
    carry_step(lo0, lo1, mid0, mid1, w_eq[1], w_up[1], w_down[1], 1)
    low0 = StackBuf(8)
    low1 = StackBuf(8)
    carry_step(mid0, mid1, low0, low1, w_eq[2], w_up[2], w_down[2], 2)
    hmid0 = StackBuf(4)
    hmid1 = StackBuf(4)
    carry_step(hi0, hi1, hmid0, hmid1, w_eq[4], w_up[4], w_down[4], 1)
    high = StackBuf(8)
    carry_wrap(hmid0, hmid1, high, w_eq[5], w_sum[5], 2)
    for r in unroll(0, 64):
        if KECCAK_SHIFT_USED[r] == 1:
            if r % 8 == 0:
                shifts[r] = low0[0] * high[r // 8]
            else:
                shifts[r] = low0[r % 8] * high[r // 8] + low1[r % 8] * high[(r // 8 + 1) % 8]
    return


@inline
def fold_node(src, dst, a_t, p: Const, b: Const, t: Const):
    n = 2 ** (KECCAK_Z_BITS - t)
    for k in unroll(0, n // 2):
        x0 = src[p * n + (2 * k + (n - 1) * b) % n]
        x1 = src[p * n + (2 * k + 1 + (n - 1) * b) % n]
        dst[(p + 2 ** t * b) * (n // 2) + k] = x0 + a_t * (x0 + x1)
    return


@inline
def fold_shifts(src, dst, a_t, t: Const):
    # One level of sum_w eq(a, w) V[w - r] for every used r at once, LSB first: node
    # p of depth t is the vector for the residue p of r mod 2^t, 2^(6 - t) cells at
    # p 2^(6 - t). Folding bit t splits it by bit t of r, b: V[w - r] pairs the
    # parent's cells 2k - b and 2k + 1 - b.
    for p in unroll(0, 2 ** t):
        for b in unroll(0, 2):
            if const(t + 1 == KECCAK_Z_BITS):
                if KECCAK_SHIFT_USED[p + 2 ** t * b] == 1:
                    fold_node(src, dst, a_t, p, b, t)
            else:
                fold_node(src, dst, a_t, p, b, t)
    return


@inline
def keccak_form(lanes, shifts, f_lanes, f_off: Const):
    # <L^T(E), f> for theta, rho, pi's transpose L^T, on weights that factor as lane
    # times slice: E = lanes (x) eZ and f = f_lanes (x) fZ, the slices entering only
    # through shifts[r] = sum_z fZ[z] eZ[(z + r) % 64]. f_lanes are frame cells from
    # f_off.
    total = 0
    column = StackBuf(5)
    column_next = StackBuf(5)
    f_column = StackBuf(5)
    for x in unroll(0, 5):
        acc = 0
        acc_next = 0
        f_acc = 0
        for y in unroll(0, 5):
            lane_weight = lanes[GEN ** KECCAK_PI[x + 5 * y]]
            moved = lane_weight * shifts[KECCAK_RHO[x + 5 * y]]
            f_weight = f_lanes[f_off + x + 5 * y]
            total += f_weight * moved
            acc += moved
            acc_next += lane_weight * shifts[(KECCAK_RHO[x + 5 * y] + 1) % 64]
            f_acc += f_weight
        column[x] = acc
        column_next[x] = acc_next
        f_column[x] = f_acc
    for x in unroll(0, 5):
        total += f_column[x] * (column[(x + 1) % 5] + column_next[(x + 4) % 5])
    return total


def keccak_round(rd, pp, pt):
    # One round of a layer's pack and segment sumcheck, from the record at rd (fields
    # KR_CAP apart) to the next: q has degree two with the eq factor pulled out, and the prover
    # sends its coefficients c1 and c2 (g_1, g_2), c0 being fixed by the claim. With r = pp[1],
    # q(rho) = claim + (r + rho) c1 + (r + rho^2) c2, and the next claim is (1 + r + rho) q(rho).
    sp = fs_load(rd, KR_FS, KR_CAP)
    cur = rd[GEN ** (KR_CURSOR * KR_CAP)]
    r_eq = pp[1]
    rate = StackBuf(8)
    g_1, cur = fs_next(rate, 0, cur)
    g_2, cur = fs_next(rate, 1, cur)
    sp, rho = squeeze(sp, rate, 2)
    pt[1] = rho
    gap = r_eq + rho
    eq_factor = 1 + gap
    nxt = rd * GEN
    fs_store(nxt, KR_FS, KR_CAP, sp)
    nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur
    nxt[GEN ** (KR_CLAIM * KR_CAP)] = eq_factor * (rd[GEN ** (KR_CLAIM * KR_CAP)] + gap * g_1 + (r_eq + rho * rho) * g_2)
    nxt[GEN ** (KR_SCALE * KR_CAP)] = rd[GEN ** (KR_SCALE * KR_CAP)] * eq_factor
    return


def keccak_layer(fs0, fs1, fs2, fs3, fs4, p0, p1, cursor, y_g, half_g, y_last, claim, out, iota, first: Const, odd: Const):
    # One layer (keccak_gkr::protocol::verify_layer): the claim on the states after
    # a round becomes one on the states before it. A claim's position weights are
    # never written out: they are the transpose of the linear layer applied to a
    # lane table times the eq table of six slice coordinates, which is all the
    # record keeps, and what `keccak_form` evaluates them from.
    # The first layer starts with the committed outputs' value waiting in the sponge, its
    # two rate cells p0 and p1.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    if first == 1:
        rate[0] = p0
        rate[1] = p1
    mu = StackBuf(KECCAK_PACK)
    for i in unroll(0, KECCAK_PACK):
        mu[i] = claim[GEN ** (KC_MU + i)]
    # The product polynomial carries the claim.
    product = StackBuf(KECCAK_PROD_BITS)
    projected = 0
    for pos in unroll(first, first + KECCAK_PROD_BITS):
        # fs_next, the word read straight into its cell, k = pos - first.
        product[pos - first] = cursor[GEN ** (pos - first)]
        coefficient = product[pos - first]
        if pos % 4 == 0:
            if pos != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        fs_pack(rate, pos % 4, coefficient, DS_OBSERVE)
        reader = 0
        for t in unroll(KECCAK_PROJ_START[pos - first], KECCAK_PROJ_START[pos - first + 1]):
            reader += mu[KECCAK_PROJ_IDX[t]]
        projected += reader * coefficient
    cursor = cursor * GEN ** KECCAK_PROD_BITS
    assert projected + iota * claim[GEN ** KC_KAPPA] == claim[GEN ** KC_VALUE]
    # At a random point a pack is one field element.
    sp, s = squeeze(sp, rate, (first + KECCAK_PROD_BITS + 3) % 4 + 1)
    s_powers = StackBuf(KECCAK_EMBED_BITS)
    s_powers[0] = 1
    for b in unroll(1, KECCAK_EMBED_BITS):
        s_powers[b] = s_powers[b - 1] * s
    # mu[i] = emb_i(s), the embeddings being residues modulo the last one, the
    # modulus. Where an embedding is x times another, reduced modulo it, its weight
    # is s times that one's plus the modulus's when the reduction fires. A factor's
    # residues 1 + x, x, x + x^2 relate so: with A = emb_k + emb_(k+1) (the lift),
    # emb_(k+1) = x A and emb_(k+2) = x emb_k. Which rows relate is decided at
    # compile time from the embedding tables; any other row is summed directly.
    mu_new = StackBuf(KECCAK_PACK)
    modulus = 0
    for t in unroll(KECCAK_EMB_START[KECCAK_PACK - 1], KECCAK_EMB_START[KECCAK_PACK]):
        modulus += s_powers[KECCAK_EMB_IDX[t]]
    mu_new[KECCAK_PACK - 1] = modulus
    kappa = modulus  # the sum of the weights: a pair's is its lift's
    paired = 0
    for k in unroll(0, KECCAK_PACK - 1):
        if const(paired == 1):
            paired = 0
        else:
            # Is emb_(k+1) = x (emb_k + emb_(k+1)) mod the modulus?
            pair = 0
            pair_top = 0
            if const(k + 2 != KECCAK_PACK):
                pair = 1
                for t in unroll(KECCAK_EMB_START[k], KECCAK_EMB_START[k + 2]):
                    if const(KECCAK_EMB_IDX[t] == KECCAK_EMBED_BITS - 2):
                        if const(pair_top == 1):
                            pair_top = 0
                        else:
                            pair_top = 1
                for b in unroll(0, KECCAK_EMBED_BITS):
                    want = 0
                    for t in unroll(KECCAK_EMB_START[k], KECCAK_EMB_START[k + 2]):
                        if const(KECCAK_EMB_IDX[t] + 1 == b):
                            if const(want == 1):
                                want = 0
                            else:
                                want = 1
                    if const(pair_top == 1):
                        for t in unroll(KECCAK_EMB_START[KECCAK_PACK - 1], KECCAK_EMB_START[KECCAK_PACK]):
                            if const(KECCAK_EMB_IDX[t] == b):
                                if const(want == 1):
                                    want = 0
                                else:
                                    want = 1
                    have = 0
                    for t in unroll(KECCAK_EMB_START[k + 1], KECCAK_EMB_START[k + 2]):
                        if const(KECCAK_EMB_IDX[t] == b):
                            have = 1
                    if const(have != want):
                        pair = 0
            # Is emb_k = x emb_(k-2) mod the modulus?
            shifted = 0
            top = 0
            if const(k // 2 != 0):
                shifted = 1
                for t in unroll(KECCAK_EMB_START[k - 2], KECCAK_EMB_START[k - 1]):
                    if const(KECCAK_EMB_IDX[t] == KECCAK_EMBED_BITS - 2):
                        top = 1
                for b in unroll(0, KECCAK_EMBED_BITS):
                    want = 0
                    for t in unroll(KECCAK_EMB_START[k - 2], KECCAK_EMB_START[k - 1]):
                        if const(KECCAK_EMB_IDX[t] + 1 == b):
                            want = 1
                    if const(top == 1):
                        for t in unroll(KECCAK_EMB_START[KECCAK_PACK - 1], KECCAK_EMB_START[KECCAK_PACK]):
                            if const(KECCAK_EMB_IDX[t] == b):
                                if const(want == 1):
                                    want = 0
                                else:
                                    want = 1
                    have = 0
                    for t in unroll(KECCAK_EMB_START[k], KECCAK_EMB_START[k + 1]):
                        if const(KECCAK_EMB_IDX[t] == b):
                            have = 1
                    if const(have != want):
                        shifted = 0
            if const(pair == 1):
                lift = 0
                for b in unroll(0, KECCAK_EMBED_BITS):
                    in_lift = 0
                    for t in unroll(KECCAK_EMB_START[k], KECCAK_EMB_START[k + 2]):
                        if const(KECCAK_EMB_IDX[t] == b):
                            if const(in_lift == 1):
                                in_lift = 0
                            else:
                                in_lift = 1
                    if const(in_lift == 1):
                        lift += s_powers[b]
                if const(pair_top == 1):
                    mu_new[k + 1] = s * lift + modulus
                else:
                    mu_new[k + 1] = s * lift
                mu_new[k] = lift + mu_new[k + 1]
                kappa += lift
                paired = 1
            elif const(shifted == 1):
                if const(top == 1):
                    mu_new[k] = s * mu_new[k - 2] + modulus
                else:
                    mu_new[k] = s * mu_new[k - 2]
                kappa += mu_new[k]
            else:
                weight = 0
                for t in unroll(KECCAK_EMB_START[k], KECCAK_EMB_START[k + 1]):
                    weight += s_powers[KECCAK_EMB_IDX[t]]
                mu_new[k] = weight
                kappa += weight
    for i in unroll(0, KECCAK_PACK):
        out[GEN ** (KC_MU + i)] = mu_new[i]
    out[GEN ** KC_KAPPA] = kappa
    value = product[KECCAK_PROD_BITS - 1]
    for k in unroll(1, KECCAK_PROD_BITS):
        value = value * s + product[KECCAK_PROD_BITS - 1 - k]
    # The pack and the segment, a runtime number of rounds: 2 half_g, plus one when
    # odd, two a loop step; y_last = half_g g^odd.
    prev_point = claim[GEN ** KC_POINT]
    point = HeapBuf(y_g)
    rounds = HeapBuf(KR_SLOTS * KR_CAP)
    fs_store(rounds, KR_FS, KR_CAP, sp)
    rounds[GEN ** (KR_CURSOR * KR_CAP)] = cursor
    rounds[GEN ** (KR_CLAIM * KR_CAP)] = value
    rounds[GEN ** (KR_SCALE * KR_CAP)] = 1
    for x2 in mul_range(1, half_g):
        rd = rounds * x2
        sq = x2 * x2
        pp = prev_point * sq
        pt = point * sq
        round_sp = fs_load(rd, KR_FS, KR_CAP)
        cur_i = rd[GEN ** (KR_CURSOR * KR_CAP)]
        run = rd[GEN ** (KR_CLAIM * KR_CAP)]
        scale = rd[GEN ** (KR_SCALE * KR_CAP)]
        for q in unroll(0, 2):
            # As in keccak_round.
            r_eq = pp[GEN ** q]
            rate = StackBuf(8)
            g_1, cur_i = fs_next(rate, 0, cur_i)
            g_2, cur_i = fs_next(rate, 1, cur_i)
            round_sp, rho = squeeze(round_sp, rate, 2)
            pt[GEN ** q] = rho
            gap = r_eq + rho
            eq_factor = 1 + gap
            run = eq_factor * (run + gap * g_1 + (r_eq + rho * rho) * g_2)
            scale = scale * eq_factor
        nxt = rd * GEN
        fs_store(nxt, KR_FS, KR_CAP, round_sp)
        nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur_i
        nxt[GEN ** (KR_CLAIM * KR_CAP)] = run
        nxt[GEN ** (KR_SCALE * KR_CAP)] = scale
    if odd == 1:
        sq = half_g * half_g
        keccak_round(rounds * half_g, prev_point * sq, point * sq)
    last = rounds * y_last
    sp = fs_load(last, KR_FS, KR_CAP)
    cursor = last[GEN ** (KR_CURSOR * KR_CAP)]
    value = last[GEN ** (KR_CLAIM * KR_CAP)]
    # The bit position: degree three, the weights being one more multilinear factor.
    local = HeapBuf(KECCAK_LOCAL_BITS)
    for i in unroll(0, KECCAK_LOCAL_BITS):
        rate = StackBuf(8)
        c0, cursor = fs_next(rate, 0, cursor)
        c2, cursor = fs_next(rate, 1, cursor)
        c3, cursor = fs_next(rate, 2, cursor)
        sp, rho = squeeze(sp, rate, 3)
        local[GEN ** i] = rho
        # c1 = value + c2 + c3, so h(rho) = c0 + rho (value + (1 + rho) (c2 + (1 + rho) c3)).
        rho1 = 1 + rho
        value = c0 + rho * (value + rho1 * (c2 + rho1 * c3))
    rate = StackBuf(8)
    t0, cursor = fs_next(rate, 0, cursor)
    t1, cursor = fs_next(rate, 1, cursor)
    t2, cursor = fs_next(rate, 2, cursor)
    # The claim's weights at the local point.
    f_lanes = StackBuf(2 ** (KECCAK_LANE_BITS + 1) - 2)
    eqtree_frame(local * GEN ** KECCAK_Z_BITS, f_lanes, KECCAK_LANE_BITS, KECCAK_LANES)
    prev_lanes = claim[GEN ** KC_LANES]
    weight_at_local = StackBuf(1)
    if first == 1:
        # The first claim weighs a lane table times the bits of a word, x^z.
        lanes_eq = 0
        for lane in unroll(0, KECCAK_LANES):
            lanes_eq += f_lanes[LANE_OFF + lane] * prev_lanes[GEN ** lane]
        for t in unroll(0, KECCAK_Z_BITS):
            lanes_eq *= 1 + local[GEN ** t] * (1 + GEN ** (2 ** t))
        weight_at_local[0] = lanes_eq
    else:
        shifts = StackBuf(64)
        keccak_shifts_eq(claim[GEN ** KC_LOCAL], local, shifts)
        weight_at_local[0] = keccak_form(prev_lanes, shifts, f_lanes, LANE_OFF)
    assert last[GEN ** (KR_SCALE * KR_CAP)] * weight_at_local[0] * (kappa * t0 + (kappa + t1) * t2) == value
    # t[k] = sum_j eq[j] T[j + k]: one claim on the state before chi.
    sp, beta = squeeze(sp, rate, 3)
    out[GEN ** KC_VALUE] = t0 + beta * (t1 + beta * t2)
    out[GEN ** KC_POINT] = point
    out[GEN ** KC_LOCAL] = local
    lanes = HeapBuf(KECCAK_LANES)
    for y in unroll(0, 5):
        for x in unroll(0, 5):
            lanes[GEN ** (x + 5 * y)] = f_lanes[LANE_OFF + x + 5 * y] + beta * (f_lanes[LANE_OFF + (x + 4) % 5 + 5 * y] + beta * f_lanes[LANE_OFF + (x + 3) % 5 + 5 * y])
    out[GEN ** KC_LANES] = lanes
    slices = StackBuf(2 ** (KECCAK_Z_BITS + 1) - 2)
    eqtree_frame(local, slices, KECCAK_Z_BITS, 64)
    # The slice weights, for the next layer's iota term.
    slices_out = HeapBuf(BASE_FIELD_BITS)
    for z in unroll(0, BASE_FIELD_BITS):
        slices_out[GEN ** z] = slices[SLICE_OFF + z]
    out[GEN ** KC_SLICES] = slices_out
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor


def keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, p0, p1, cursor, value, point, n: Const, k0: Const):
    # n rounds of a degree-2 sumcheck with no equality factor. With k0 = 1 one scalar
    # already waits in the sponge, rate cells p0 and p1, and the first round's words
    # join it.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    for i in unroll(0, n):
        rate = StackBuf(8)
        if i == 0:
            if k0 == 1:
                rate[0] = p0
                rate[1] = p1
                c0, cursor = fs_next(rate, 1, cursor)
                c2, cursor = fs_next(rate, 2, cursor)
                sp, rho = squeeze(sp, rate, 3)
            else:
                c0, cursor = fs_next(rate, 0, cursor)
                c2, cursor = fs_next(rate, 1, cursor)
                sp, rho = squeeze(sp, rate, 2)
        else:
            c0, cursor = fs_next(rate, 0, cursor)
            c2, cursor = fs_next(rate, 1, cursor)
            sp, rho = squeeze(sp, rate, 2)
        c1 = value + c2
        point[GEN ** i] = rho
        value = c0 + rho * (c1 + rho * c2)
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, value


@inline
def keccak_slot_lanes(slot, segment_point, out, first: Const, count: Const):
    # The weight an opening's slot point puts on each lane, into the frame cells
    # out[0..25): the states it speaks of start at `first`, one per segment, for the
    # first `count` segments.
    slot_weights = StackBuf(2 ** (QKECCAK_SLOT_LOG + 1) - 2)
    eqtree_frame(slot, slot_weights, QKECCAK_SLOT_LOG, KECCAK_LANES * KECCAK_SEGMENTS)
    seg_weights = StackBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
    eqtree_frame(segment_point, seg_weights, KECCAK_SEG_LOG, 2 ** KECCAK_SEG_LOG)
    for lane in unroll(0, KECCAK_LANES):
        lane_acc = 0
        for m in unroll(0, count):
            lane_acc += seg_weights[2 ** KECCAK_SEG_LOG - 2 + m] * slot_weights[2 ** QKECCAK_SLOT_LOG - 2 + KECCAK_LANES * (first + m) + lane]
        out[lane] = lane_acc
    return


def verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, tau_g, chi, output_lanes, z_vals, slices):
    # SHA3 validity (keccak_gkr::verify): a random claim on every segment's output,
    # KECCAK_DEPTH layers down to the committed inputs, every segment at once. The
    # last segment's output is the permutation's: the table's claims on its output
    # lanes, `output_lanes`, at the table's point chi[..tau], give that part of the
    # claim, and the prover sends the committed outputs' part. It leaves two
    # openings of q_keccak, at the two points written to `z_vals` (tau +
    # QKECCAK_SLOT_LOG coordinates each, QKECCAK_VARS_CAP apart): the committed
    # outputs as words at the first, returned, and the 64 `slices` at the second.
    # tau >= FLOORS[TABLE_SHA3] is certified, so the pack count is a real count. It
    # also draws the ring-switching map's first challenge, which the last slices wait
    # for, and returns it.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    no_rate = StackBuf(8)
    pack_g = tau_g * INV_GEN ** KECCAK_PACK_LOG
    y_g = pack_g * GEN ** KECCAK_SEG_LOG
    # A layer runs y = log(y_g) rounds two at a time: y_g = half_g^2 g^odd, from y's
    # bits, pinned boolean and tied back (y = tau - 3 < 2^5 as tau < COUNT_BITS).
    y_bits = StackBuf(5)
    hint_decompose_bits_exponent(y_bits, y_g, 5)
    half_g = GEN ** 0
    for j in unroll(0, 5):
        bit = y_bits[j]
        y_bits[j] = bit * bit
        if j != 0:
            half_g *= 1 + bit * (1 + GEN ** (2 ** j // 2))
    odd_g = 1 + y_bits[0] * (1 + GEN)
    y_last = half_g * odd_g
    assert half_g * y_last == y_g
    out_point = z_vals
    in_point = z_vals * GEN ** QKECCAK_VARS_CAP
    for i in unroll(0, KECCAK_PACK_LOG):
        out_point[GEN ** i] = chi[GEN ** i]
    # The claim's point: chi's pack coordinates, then a fresh segment.
    point = HeapBuf(y_g)
    chi_pack = chi * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        point[xt] = chi_pack[xt]
    segment = point * pack_g
    for i in unroll(0, KECCAK_SEG_LOG):
        sp, r = squeeze(sp, no_rate, 0)
        segment[GEN ** i] = r
    r_lane = HeapBuf(KECCAK_LANE_BITS)
    for i in unroll(0, KECCAK_LANE_BITS):
        sp, r = squeeze(sp, no_rate, 0)
        r_lane[GEN ** i] = r
    # The committed outputs' value waits in the sponge until the first layer's words.
    value_rate = StackBuf(8)
    value, cursor = fs_next(value_rate, 0, cursor)
    fs0 = sp[8]
    fs1 = sp[9]
    fs2 = sp[10]
    fs3 = sp[11]
    fs4 = sp[12]

    # The first claim combines the output lanes as words: instance weights
    # eq(chi_low), position weights eq(r_lane) on the lane times x^z on the bit.
    claims = HeapBuf((KECCAK_DEPTH + 1) * KC_SIZE)
    claims[GEN ** KC_KAPPA] = 1
    claims[GEN ** KC_POINT] = point
    mu_tree = HeapBuf(2 ** (KECCAK_PACK_LOG + 1) - 2)
    eqtree(out_point, mu_tree, KECCAK_PACK_LOG)
    for i in unroll(0, KECCAK_PACK):
        claims[GEN ** (KC_MU + i)] = mu_tree[GEN ** (2 ** KECCAK_PACK_LOG - 2 + i)]
    lane_tree = HeapBuf(2 ** (KECCAK_LANE_BITS + 1) - 2)
    eqtree(r_lane, lane_tree, KECCAK_LANE_BITS)
    first_lanes = lane_tree * GEN ** (2 ** KECCAK_LANE_BITS - 2)
    claims[GEN ** KC_LANES] = first_lanes
    # `value` is the committed outputs' part; the last segment's is the table's.
    segment_tree = HeapBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
    eqtree(segment, segment_tree, KECCAK_SEG_LOG)
    output = 0
    for lane in unroll(0, KECCAK_LANES):
        output += first_lanes[GEN ** lane] * output_lanes[GEN ** lane]
    claims[GEN ** KC_VALUE] = value + segment_tree[GEN ** (2 ** KECCAK_SEG_LOG - 2 + KECCAK_SEGMENTS - 1)] * output

    for step in unroll(0, KECCAK_DEPTH):
        claim = claims * GEN ** (step * KC_SIZE)
        # iota flips known positions of lane 0, per segment a different round's.
        claim_point = claim[GEN ** KC_POINT]
        segment_tree = HeapBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
        eqtree(claim_point * pack_g, segment_tree, KECCAK_SEG_LOG)
        # The claim's weights where iota can flip, slice 2^i - 1 of lane 0, for the
        # i this step's round constants set: the first claim's are a word's,
        # x^(2^i - 1) on lane 0; a later claim's come from its lane and slice
        # weights through the linear layer's transpose.
        flips = StackBuf(KECCAK_IOTA_BITS)
        for i in unroll(0, KECCAK_IOTA_BITS):
            used = 0
            for t in unroll(KECCAK_IOTA_START[KECCAK_SEGMENTS * step], KECCAK_IOTA_START[KECCAK_SEGMENTS * step + KECCAK_SEGMENTS]):
                if const(KECCAK_IOTA_IDX[t] == i):
                    used = 1
            if const(used == 1):
                if step == 0:
                    flips[i] = first_lanes[GEN ** 0] * GEN ** (2 ** i - 1)
                else:
                    claim_lanes = claim[GEN ** KC_LANES]
                    claim_slices = claim[GEN ** KC_SLICES]
                    flipped = claim_lanes[GEN ** KECCAK_PI[0]] * claim_slices[GEN ** ((2 ** i - 1 + KECCAK_RHO[0]) % 64)]
                    for y in unroll(0, 5):
                        flipped += claim_lanes[GEN ** KECCAK_PI[1 + 5 * y]] * claim_slices[GEN ** ((2 ** i - 1 + KECCAK_RHO[1 + 5 * y]) % 64)]
                        flipped += claim_lanes[GEN ** KECCAK_PI[4 + 5 * y]] * claim_slices[GEN ** ((2 ** i + KECCAK_RHO[4 + 5 * y]) % 64)]
                    flips[i] = flipped
        iota = 0
        for m in unroll(0, KECCAK_SEGMENTS):
            flipped = 0
            for t in unroll(KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m], KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m + 1]):
                flipped += flips[KECCAK_IOTA_IDX[t]]
            iota += segment_tree[GEN ** (2 ** KECCAK_SEG_LOG - 2 + m)] * flipped
        # odd_g is g^0 or g^1, its exponent a pinned bit.
        if step == 0:
            fs0, fs1, fs2, fs3, fs4, cursor = match(log(odd_g), range(0, 2), lambda odd: keccak_layer(fs0, fs1, fs2, fs3, fs4, value_rate[0], value_rate[1], cursor, y_g, half_g, y_last, claim, claim * GEN ** KC_SIZE, iota, 1, odd))
        else:
            fs0, fs1, fs2, fs3, fs4, cursor = match(log(odd_g), range(0, 2), lambda odd: keccak_layer(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, y_g, half_g, y_last, claim, claim * GEN ** KC_SIZE, iota, 0, odd))

    # ---- the outputs, whose instance weights are an eq already ----
    # Their position weights are a word's, so the 64 slices are only needed as
    # the word they add up to: q_keccak itself at the point.
    out_slot = out_point * tau_g
    fs0, fs1, fs2, fs3, fs4, cursor, out_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, value, out_slot, QKECCAK_SLOT_LOG, 0)
    word_rate = StackBuf(8)
    word, cursor = fs_next(word_rate, 0, cursor)
    out_lanes = StackBuf(KECCAK_LANES)
    keccak_slot_lanes(out_slot, point * pack_g, out_lanes, 1, KECCAK_SEGMENTS - 1)
    lanes_sum = 0
    for lane in unroll(0, KECCAK_LANES):
        lanes_sum += out_lanes[lane] * first_lanes[GEN ** lane]
    assert lanes_sum * word == out_value
    out_pack = out_point * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        out_pack[xt] = point[xt]

    # ---- the inputs: the instances of a pack first, then the slot ----
    last = claims * GEN ** (KECCAK_DEPTH * KC_SIZE)
    fs0, fs1, fs2, fs3, fs4, cursor, low_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, word_rate[0], word_rate[1], cursor, last[GEN ** KC_VALUE], in_point, KECCAK_PACK_LOG, 1)
    low_tree = HeapBuf(2 ** (KECCAK_PACK_LOG + 1) - 2)
    eqtree(in_point, low_tree, KECCAK_PACK_LOG)
    mu_at_low = 0
    for i in unroll(0, KECCAK_PACK):
        mu_at_low += low_tree[GEN ** (2 ** KECCAK_PACK_LOG - 2 + i)] * last[GEN ** (KC_MU + i)]
    in_slot = in_point * tau_g
    fs0, fs1, fs2, fs3, fs4, cursor, in_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, low_value, in_slot, QKECCAK_SLOT_LOG, 0)
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    for z in unroll(0, BASE_FIELD_BITS):
        if z % 4 == 0:
            if z != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        w, cursor = fs_next(rate, z % 4, cursor)
        slices[GEN ** z] = w
    sp, map_0 = squeeze(sp, rate, 4)
    last_point = last[GEN ** KC_POINT]
    in_lanes = StackBuf(KECCAK_LANES)
    keccak_slot_lanes(in_slot, last_point * pack_g, in_lanes, 0, KECCAK_SEGMENTS)
    # shifts[r] = sum_z slices[z] eq(a, z + r), a the last layer's slice point:
    # folded a bit at a time for every r at once.
    last_local = last[GEN ** KC_LOCAL]
    level = StackBuf(64)
    for z in unroll(0, BASE_FIELD_BITS):
        level[z] = slices[GEN ** z]
    for t in unroll(0, KECCAK_Z_BITS):
        folded = StackBuf(64)
        fold_shifts(level, folded, last_local[GEN ** t], t)
        level = folded
    shifts = level
    last_lanes = last[GEN ** KC_LANES]
    assert mu_at_low * keccak_form(last_lanes, shifts, in_lanes, 0) == in_value
    in_pack = in_point * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        in_pack[xt] = last_point[xt]
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, word, map_0


@inline
def ring_map(lin_eval, map_challenges):
    for stage in unroll(0, len(RING_MAP_SHIFTS)):
        frobenius = lin_eval
        for k in unroll(0, RING_MAP_SHIFTS[stage]):
            frobenius *= frobenius
        lin_eval += map_challenges[GEN ** stage] * frobenius
    return lin_eval


def ring_switch_target(slices, map_challenges):
    # Evaluate the claim and combine its 64 packing rows, sum_i x^i L(slice_i),
    # RS_CHUNK rows an iteration in Horner form: the running x-power and the
    # running sum ride one two-slot chain.
    rs_chain = HeapBuf((BASE_FIELD_BITS // RS_CHUNK + 1) * PAIR_SLOTS)
    rs_chain[GEN ** 0] = GEN ** 0  # x^(RS_CHUNK j)
    rs_chain[GEN ** 1] = 0         # the running sum
    for x_round in mul_range(1, GEN ** (BASE_FIELD_BITS // RS_CHUNK)):
        rows = slices * x_round ** RS_CHUNK
        chunk = ring_map(rows[GEN ** (RS_CHUNK - 1)], map_challenges)
        for r in unroll(1, RS_CHUNK):
            chunk = chunk * 2 + ring_map(rows[GEN ** (RS_CHUNK - 1 - r)], map_challenges)
        row = rs_chain * x_round ** PAIR_SLOTS
        x_pow = row[GEN ** 0]
        row[GEN ** PAIR_SLOTS] = x_pow * const(2 ** RS_CHUNK)
        row[GEN ** (PAIR_SLOTS + 1)] = row[GEN ** 1] + x_pow * chunk
    rs_end = rs_chain * (GEN ** (BASE_FIELD_BITS // RS_CHUNK)) ** PAIR_SLOTS
    return rs_end[GEN ** 1]


def ring_switch_weight(z_vals, point1, c_table, qkeccakv_g):
    # One ring-switched claim's transparent weight at the opening point.
    prod_chains = HeapBuf((qkeccakv_g * GEN) ** BASE_FIELD_BITS)
    for k in unroll(0, BASE_FIELD_BITS):
        prod_chains[GEN ** k] = 1
    prod_final = rs_eq_run(prod_chains, z_vals, point1, qkeccakv_g)
    rs_weight = 0
    for k in unroll(0, BASE_FIELD_BITS):
        rs_weight += c_table[GEN ** k] * prod_final[GEN ** k]
    return rs_weight


def certify_placement(kappa_base, g_squares):
    # Certify the native order: descending kappa, then ascending column index.
    # Accumulate g^offset, with each column advancing it by g^(2^kappa).
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
        # <= 32 (log_mem or a tau), the baked bytecode log, or q_keccak's tau_5 + QKECCAK_SLOT_LOG.
        # Bound it before the lookup, independently of m derived from this product.
        assert log(kappa_g) < SIZE_BITS
        g_total *= g_squares[kappa_g]
        prev_col = col
        prev_kappa = kappa_g

    return g_total, col_off_g, col_kappa_g


def column_selector(offset, sel_eq, sel_g, kappa: Const):
    # Rebuild the offset using only bits above the column's kappa, certifying its
    # alignment. The same bits select the column at the complete opening point.
    # Both offset and point are zero above m, so extending to 4 * SEL_NIBBLES adds
    # only factors eq(0, 0) = 1. The bits go a nibble at a time, top bit first:
    # their g-power index u (bit 4j+3-t weighing 2^t) reads the nibble's eq over
    # its coordinates and its g^offset share off the tables of selector_tables.
    bits = StackBuf(4 * SEL_NIBBLES)
    hint_decompose_bits_exponent(bits, offset, 4 * SEL_NIBBLES)
    rebuilt = GEN ** 0
    selector = GEN ** 0
    for j in unroll(kappa // 4, SEL_NIBBLES):
        width = 4
        if const(j == kappa // 4):
            width = 4 * j + 4 - kappa
        idx = GEN ** 0
        for t in unroll(0, width):
            bit = bits[4 * j + 3 - t]
            bits[4 * j + 3 - t] = bit * bit
            idx *= 1 + bit * (1 + GEN ** (2 ** t))
        selector *= sel_eq[GEN ** (SEL_EQ_STRIDE * j + 2 ** width - 2) * idx]
        rebuilt *= sel_g[GEN ** (16 * j) * idx]
    assert rebuilt == offset
    return selector


def selector_tables(point, point1):
    # Per nibble j of the selector bits, the eq tables over its top 1..4
    # coordinates (coordinate 4j+3-t is index bit t; the top w form the level-w
    # table at 2^w - 2), and the g-powers g^(sum_t u_t 2^(4j+3-t)) of its indices.
    sel_eq = HeapBuf(SEL_NIBBLES * SEL_EQ_STRIDE)
    sel_g = HeapBuf(SEL_NIBBLES * 16)
    for j in unroll(0, SEL_NIBBLES):
        levels = StackBuf(SEL_EQ_STRIDE)
        levels[0] = point1[GEN ** (4 * j + 3)]
        levels[1] = point[GEN ** (4 * j + 3)]
        for t in unroll(1, 4):
            r = point[GEN ** (4 * j + 3 - t)]
            r1 = point1[GEN ** (4 * j + 3 - t)]
            for i in unroll(0, 2 ** t):
                levels[2 ** (t + 1) - 2 + i] = levels[2 ** t - 2 + i] * r1
                levels[2 ** (t + 1) - 2 + 2 ** t + i] = levels[2 ** t - 2 + i] * r
        for i in unroll(0, SEL_EQ_STRIDE):
            sel_eq[GEN ** (SEL_EQ_STRIDE * j + i)] = levels[i]
        for u in unroll(0, 16):
            g_share = GEN ** 0
            for t in unroll(0, 4):
                if (u // 2 ** t) % 2 == 1:
                    g_share *= GEN ** (2 ** (4 * j + 3 - t))
            sel_g[GEN ** (16 * j + u)] = g_share
    return sel_eq, sel_g


def check_opening_terminal(zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_sha3_g, claim_cplen_g, lam_out, lam_pool, col_offsets, col_kappas, z_vals, c_table, point, point1, inner_total, yr_at_tail, sumcheck_target):
    # Evaluate each transparent weight at the complete point in witness order.
    # A claim is its low point followed by the certified column's selector bits;
    # a q_keccak lane puts its slot's bits between the two.
    # point1 = 1 + point holds each coordinate's eq factor against a zero bit.
    zeta_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(zeta_eq_chain, 1, zeta, point1, g_bus_mu)
    chi_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(chi_eq_chain, 1, chi, point1, g_zc_n)
    slot_point = point * tau_sha3_g
    slot_point1 = point1 * tau_sha3_g
    pi_chain = HeapBuf(SIZE_BITS + 1)
    pi_chain[GEN ** 0] = 1
    pi_chain[GEN ** 1] = rm + point1[GEN ** 0]
    for xk in mul_range(GEN, g_log_mem):
        pi_chain[xk * GEN] = pi_chain[xk] * point1[xk]
    pi_eq = pi_chain[g_log_mem]

    sel_eq, sel_g = selector_tables(point, point1)
    selectors = StackBuf(N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        offset = col_offsets[GEN ** c]
        kappa_g = col_kappas[GEN ** c]
        selectors[c] = match(log(kappa_g), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, sel_eq, sel_g, kappa))

    inner_sum = inner_total
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] != POINT_BUF_KECCAK_OUT:
            if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
                cplen_g = g_log_mem
                low_eq = pi_eq
            else:
                cplen_g = claim_cplen_g[GEN ** j]
            nlow = cplen_g
            if CLAIM_POINT_BUF[j] == POINT_BUF_ZETA:
                low_eq = zeta_eq_chain[cplen_g]
            if CLAIM_POINT_BUF[j] == POINT_BUF_RHO:
                low_eq = chi_eq_chain[cplen_g]
            if CLAIM_POINT_BUF[j] == POINT_BUF_QKECCAK_RHO:
                # Top bit first, so claims sharing high slot bits share partial products.
                slot_eq = GEN ** 0
                for kk in unroll(0, QKECCAK_SLOT_LOG):
                    k = QKECCAK_SLOT_LOG - 1 - kk
                    if CLAIM_QKECCAK_SLOT_BITS[QKECCAK_SLOT_LOG * j + k] == 1:
                        slot_factor = slot_point[GEN ** k]
                    else:
                        slot_factor = slot_point1[GEN ** k]
                    if kk == 0:
                        slot_eq = slot_factor
                    else:
                        slot_eq *= slot_factor
                low_eq = slot_eq * chi_eq_chain[cplen_g]
                nlow = cplen_g * GEN ** QKECCAK_SLOT_LOG
            assert nlow == col_kappas[GEN ** CLAIM_COMMITTED_COL[j]]
            inner_sum += lam_pool[GEN ** j] * low_eq * selectors[CLAIM_COMMITTED_COL[j]]

    # The Keccak reduction's two claims on q_keccak, each over the whole column:
    # the ring-switched one leads the batch at lam_cl^0, the plain one closes it.
    # A lane claim's low point is tau_sha3 long, the kappa check above holding it
    # to this column.
    qkeccakv_g = tau_sha3_g * GEN ** QKECCAK_SLOT_LOG
    assert qkeccakv_g == col_kappas[GEN ** QKECCAK_COMMITTED_COL]
    out_eq_chain = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG + 1)
    eq_prefix_chain(out_eq_chain, 1, z_vals, point1, qkeccakv_g)
    rs_weight = ring_switch_weight(z_vals * GEN ** QKECCAK_VARS_CAP, point1, c_table, qkeccakv_g)
    inner_sum += (rs_weight + lam_out * out_eq_chain[qkeccakv_g]) * selectors[QKECCAK_COMMITTED_COL]
    assert inner_sum * yr_at_tail == sumcheck_target


def verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement (pi_0, pi_1),
    # mirroring `crates/verifier` step for step; the `# ---- ... ----` headers below run
    # in that order. All proof data is hinted HERE, so each call pops the next
    # sub-proof's entry of every witness stream and the body lowers once. The
    # exponent tables are shared read-only; the deferred claim goes to `defer_out`.
    #
    # The pool holds every committed-coordinate claim's value in decompose order
    # (the points are the GKR zetas, resolvable from the baked block structure) and
    # its certified low dimension, which the terminal pins its lengths against.
    claim_pool = HeapBuf(N_CLAIMS)
    claim_cplen_g = HeapBuf(N_CLAIMS)

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    # The sponge's first permutation takes the program digest and the statement as
    # its rate, from the zero state.
    sp = StackBuf(SHA3_STATE)
    sha3([seed_0, seed_1], [pi_0, pi_1], sp, final=0)
    stream = HeapBuf(STREAM_CAP)
    hint_witness(stream[0:STREAM_CAP], "stream")
    cursor = stream  # the proof stream, replayed word by word (advance = * g)

    # ---- announced layout and PCS rate (observed, then certified) ----
    # The stream announces the memory's log size and each table's row count as
    # integer WORDS; the shape-generic phases need logs as G-POWERS (loop bounds,
    # match scrutinees). log_mem is reassembled from its advice-decomposed bits, with
    # no hint and no g^j -> j lookup. A table's log height is advice, which
    # verify_tables certifies to be the least holding its rows, above its floor.
    table_rows = HeapBuf(N_TABLES)
    rate = StackBuf(8)
    for i in unroll(0, N_TABLES + 1):
        if i % 4 == 0:
            if i != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        x, cursor = fs_next(rate, i % 4, cursor)
        if i == 0:
            log_mem_word = x
        else:
            table_rows[GEN ** (i - 1)] = x
    if const((N_TABLES + 1) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    log_inv_rate, cursor = fs_next(rate, (N_TABLES + 1) % 4, cursor)
    rate_sel = g_power_of_word(log_inv_rate) / GEN
    assert log(rate_sel) < LIG_N_RATES
    dims_g = HeapBuf(N_TABLES + 1)  # [g^log_mem, g^tau_0 .. g^tau_{N_TABLES-1}]
    g_log_mem = g_power_of_word(log_mem_word)
    assert log(g_log_mem) < COUNT_BITS
    assert log(g_log_mem / GEN ** MIN_LOG_MEM) < COUNT_BITS  # native MIN_LOG_MEM <= log_mem
    dims_g[GEN ** 0] = g_log_mem
    hint_witness(dims_g[1:1 + N_TABLES], "table_logs")  # certified in verify_tables
    # kappa_base maps a kappa source index to its certified log (source 0
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
    # The announcement's N_TABLES + 2 words, then the root's two, wait as one run.
    if const((N_TABLES + 2) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    commit_root_0, cursor = fs_next(rate, (N_TABLES + 2) % 4, cursor)
    if const((N_TABLES + 3) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    commit_root_1, cursor = fs_next(rate, (N_TABLES + 3) % 4, cursor)
    # A non-canonical half is rejected here (`Digest::from_halves` in `crates/verifier`); the level
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
        if t == 0:
            sp, av = squeeze(sp, rate, (N_TABLES + 3) % 4 + 1)
        else:
            sp, av = squeeze(sp, rate, 0)
        bus_alpha[GEN ** t] = av
    fp_w = HeapBuf(N_TUPLE_SLOTS)
    for x in unroll(0, N_TUPLE_SLOTS):
        fp_w[GEN ** x] = eq_weight(bus_alpha, N_TUPLE_BITS, x, 0)
    sp, beta = squeeze(sp, rate, 0)

    # ---- ONE GKR grand product: push, pull, and count RLC-batched ----
    fs0, fs1, fs2, fs3, fs4, cursor, claim_push, claim_pull, claim_count = verify_bus_gkr(sp[8], sp[9], sp[10], sp[11], sp[12], cursor, g_bus_mu, zeta)

    # ---- the bus leaves, the table sumcheck, and the public-input claim ----
    chi = HeapBuf(SIZE_BITS)  # chi[i] = the challenge that bound variable i
    fs0, fs1, fs2, fs3, fs4, cursor, g_zc_n, bc_share, rm = verify_tables(fs0, fs1, fs2, fs3, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, block_kappa, g_squares, fp_w, beta, claim_pool, claim_cplen_g, chi, claim_push, claim_pull, claim_count)

    # ---- SHA3 validity, by GKR over the rounds ----
    tau_sha3_g = dims_g[GEN ** (TABLE_SHA3 + 1)]  # the SHA3 table's certified tau
    z_vals = HeapBuf(2 * QKECCAK_VARS_CAP)
    slices = HeapBuf(BASE_FIELD_BITS)
    fs0, fs1, fs2, fs3, fs4, cursor, keccak_word, map_0 = verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, tau_sha3_g, chi, claim_pool * GEN ** KECCAK_OUT_POOL, z_vals, slices)
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)

    # ---- stacked mixed opening: ring-switch front + claim combination ----
    # The input opening's slices were read and bound above; this block only binds
    # them to the commitment. Compose six two-term F2-linear maps with shifts
    # 32,16,8,4,2,1: their expansion has all 64 Frobenius terms soundness needs,
    # while direct application costs 63 squarings and only six general
    # multiplications.
    map_challenges = HeapBuf(6)  # len(RING_MAP_SHIFTS)
    c_table = HeapBuf(BASE_FIELD_BITS)
    # verify_keccak drew the first, which the last slices waited for.
    map_challenges[GEN ** 0] = map_0
    for stage in unroll(1, len(RING_MAP_SHIFTS)):
        sp, map_challenge = squeeze(sp, rate, 0)
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
    target_in = ring_switch_target(slices, map_challenges)
    # ONE batching challenge for the whole pool: N_CLAIMS - 1 fewer Fiat-Shamir
    # hashes than a challenge per claim, and none for the values themselves,
    # `fs_next` having bound every one it read and the public-input ones deriving
    # from the seeded statement and rm, so `lam_cl` already depends on all of
    # them. Disjoint power ranges, as for the zc_xi-powers above:
    # the ring-switch claim takes lam_cl^0, the pool lam_cl^1 onward (bar the output
    # lanes' claims, which the Keccak reduction consumed), and the Keccak reduction's
    # claim on its committed outputs the power after the pool's last.
    # The committed lane of a step's input holds the padding bit the VM reads
    # without, a constant apart.
    sp, lam_cl = squeeze(sp, rate, 0)
    target = target_in
    lam_pool = HeapBuf(N_CLAIMS)
    lam_pow = lam_cl
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] != POINT_BUF_KECCAK_OUT:
            lam_pool[GEN ** j] = lam_pow
            if CLAIM_END_LANE[j] == 1:
                target += lam_pow * (claim_pool[GEN ** j] + KECCAK_END_BIT)
            else:
                target += lam_pow * claim_pool[GEN ** j]
            lam_pow *= lam_cl
    target += lam_pow * keccak_word

    g_total, col_offsets, col_kappas = certify_placement(kappa_base, g_squares)

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
    sumcheck_target, point, point1, inner_total, yr_at_tail = match(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, sp[8], sp[9], sp[10], sp[11], sp[12], target, commit_root_0, commit_root_1, cursor))
    # `stream` is a fixed-capacity witness transport. The shape fixes the exact
    # consumed prefix, whose every word is transcript-bound; the unused suffix
    # is outside the recursively verified proof and intentionally unconstrained.

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    check_opening_terminal(zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_sha3_g, claim_cplen_g, lam_pow, lam_pool, col_offsets, col_kappas, z_vals, c_table, point, point1, inner_total, yr_at_tail, sumcheck_target)

    # ---- export this sub-proof's deferred-claim data to the caller (FRESH_*) ----
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = zeta[GEN ** k]
    for k in unroll(0, LOG2_BYTECODE_COLS):
        defer_out[GEN ** (BYTECODE_LOG + k)] = bus_alpha[GEN ** k]
    defer_out[GEN ** FRESH_BC_VALUE] = bc_share
    return


# =============================== WOTS+C, both schemes ===============================
# Every hash input is P | A | M with P, A and each value of M 16 bytes, so each is
# one cell: a hash's output feeds the next hash where it lands, and a hinted value
# needs no check of its own, the SHA3 table reading only canonical cells. A chain's
# steps land in fixed slots of a `walks` run, so its tip is one cell whatever the
# digit, read there by the leaf's hash.


@inline
def shifts(bits, off: Const, n: Const, out):
    # The integer in the pinned bits [off, off+n) and its right shifts, out[l] the
    # one by l: a field's value, and the node indices above a leaf.
    out[n - 1] = bits[off + n - 1]
    for r in unroll(1, n):
        out[n - 1 - r] = bits[off + n - 1 - r] + GEN * out[n - r]
    return


@inline
def is_child(node, kids, k: Const, bit):
    # A node is not ordered against its sibling: the two children are hinted in
    # order, at kids[k] and kids[k + 1], and `node` is checked to be the one `bit`
    # names, the left one at 0, the right one at 1. One product, stored where the
    # left child's difference already is, which is the assert.
    check = StackBuf(1)
    check[0] = node + kids[k]
    check[0] = bit * (kids[k] + kids[k + 1])
    return


@inline
def chain_tip(walks, i: Const):
    # Chain i's tip, in the last of its CHAIN_STEPS slots of `walks`.
    tip = walks[((i + 1) * CHAIN_STEPS - 1) * SHA3_STATE]
    return tip


@inline
def walk(at, pp, walks, i: Const, k: Const, lx: Const):
    # Walk chain i from position k to its end, the step leaving position s landing in
    # chain i's slot s of `walks`, so the tip is chain_tip(walks, i) whatever k is. A
    # leanSPHINCS step's address carries i and s, its input ending after the value; a
    # leanXMSS one only s, at[s] computed once per key, i riding after the value.
    if const(k == CHAIN_STEPS):
        hint_witness(walks[((i + 1) * CHAIN_STEPS - 1) * SHA3_STATE:((i + 1) * CHAIN_STEPS - 1) * SHA3_STATE + 1], "chain_starts")
    else:
        value = hint_witness("chain_starts")
        for s in unroll(k, CHAIN_STEPS):
            o = (CHAIN_STEPS * i + s) * SHA3_STATE
            if const(lx == 1):
                sha3([pp, at[s]], [value, i], walks[o:o + SHA3_STATE])
            else:
                sha3([pp, at + const(TW_CHAIN + i * HI_MUL + s * STEP_MUL)], [value, 0], walks[o:o + SHA3_STATE], len=48)
            value = walks[o]
    return


@inline
def walk_group(at, pp, walks, first: Const, n: Const, k: Const, lx: Const, powers, product, encoded):
    # The n <= DIGIT_GROUP chains from `first` on, at the digits of k, one
    # dispatch for all of them. Folds the digits' sum into `product`, in the
    # exponent (`powers[s]` is GEN ** s), and the digits into `encoded`, where the
    # encoding digest holds them.
    for r in unroll(0, n):
        walk(at, pp, walks, first + r, (k // CHAIN_LENGTH ** r) % CHAIN_LENGTH, lx)
    return product * powers[DIGIT_SUMS[k]], encoded + const(k * CHAIN_LENGTH ** first)


@inline
def wots_leaf(p0, p1, walks, n: Const, leaf):
    # The hash of the prefix (p0, p1) and the n chain tips, eight cells a block. A block
    # takes its first four cells from anywhere, and a later one all eight, its message
    # being XORed into the state, so the tips are read where their walks left them. The
    # last block holds one to four cells (asserted host-side).
    st = StackBuf(SHA3_STATE)
    sha3([p0, p1], [chain_tip(walks, 0), chain_tip(walks, 1)], st, tail=[chain_tip(walks, 2), chain_tip(walks, 3), chain_tip(walks, 4), chain_tip(walks, 5)], final=0)
    for b in unroll(1, (n + 1) // 8):
        t = 8 * b - 2  # the block's first tip
        nxt = StackBuf(SHA3_STATE)
        sha3([chain_tip(walks, t), chain_tip(walks, t + 1)], [chain_tip(walks, t + 2), chain_tip(walks, t + 3)], nxt, tail=[chain_tip(walks, t + 4), chain_tip(walks, t + 5), chain_tip(walks, t + 6), chain_tip(walks, t + 7)], state=st, final=0)
        st = nxt
    # The last block's one to four cells.
    t = 8 * ((n + 1) // 8) - 2
    last = n - t
    if const(last == 1):
        sha3([chain_tip(walks, t), 0], [0, 0], leaf, state=st, len=16)
    elif const(last == 2):
        sha3([chain_tip(walks, t), chain_tip(walks, t + 1)], [0, 0], leaf, state=st, len=32)
    elif const(last == 3):
        sha3([chain_tip(walks, t), chain_tip(walks, t + 1)], [chain_tip(walks, t + 2), 0], leaf, state=st, len=48)
    else:
        sha3([chain_tip(walks, t), chain_tip(walks, t + 1)], [chain_tip(walks, t + 2), chain_tip(walks, t + 3)], leaf, state=st, len=64)
    return


@inline
def merkle_path(node, pp, bits, nodes, out, off: Const, height: Const, end: Const, top: Const):
    # The path from `node` up `height` levels into out, the two children of each
    # node hinted in order. Level l's bit is bits[off + l] and its parent's index
    # nodes[off + l + 1], the one at `end` being a root, at index 0. `top` flags
    # leanXMSS's top layer.
    cur = node
    for level in unroll(0, height):
        kids = StackBuf(2)
        hint_witness(kids, "siblings")
        is_child(cur, kids, 0, bits[off + level])
        if const(level + 1 == height):
            parent = out
        else:
            parent = StackBuf(SHA3_STATE)
        if const(off + level + 1 == end):
            sha3([pp, const(TW_NODE + (level + 1) * HI_MUL + top * LX_TOP)], kids, parent)
        else:
            sha3([pp, const(TW_NODE + (level + 1) * HI_MUL + top * LX_TOP) + nodes[off + level + 1]], kids, parent)
        cur = parent[0]
    return


# ========================= leanXMSS signature verification ========================


def verify_lean_xmss(signer):
    # `signer` is one 4-cell entry of the leanXMSS coverage table: the pubkey's
    # merkle root and public parameter, then the message that pubkey signed. The
    # bottom layer signs the message, the top layer the bottom root.
    pp = signer[GEN]

    # The leaf index rides the signature, so every address is derived here from its
    # bits, which are advice pinned Boolean: any index is one some signature may
    # carry, so no outside value pins them, and the digests and the root this
    # signature must reach bind them. nodes[l] is `leaf_index >> l`: the bottom
    # layer's key and node indices, then from LX_HEIGHT on the top layer's.
    bits = StackBuf(2 * LX_HEIGHT)
    hint_witness(bits, "leaf_index_bits")
    for b in unroll(0, 2 * LX_HEIGHT):
        bits[b] = bits[b] * bits[b]
    nodes = StackBuf(2 * LX_HEIGHT)
    shifts(bits, 0, 2 * LX_HEIGHT, nodes)
    powers = StackBuf(DIGIT_GROUP * CHAIN_STEPS + 1)
    for s in unroll(0, DIGIT_GROUP * CHAIN_STEPS + 1):
        powers[s] = GEN ** s

    for layer in unroll(0, 2):
        if const(layer == 0):
            idx = nodes[0]
        else:
            idx = nodes[LX_HEIGHT] + LX_TOP
        # D = Th(P, A, M | R), one block: 80 bytes at the bottom, and 64 at the top,
        # where M is the bottom root.
        rho = hint_witness("randomizer")
        digest = StackBuf(SHA3_STATE)
        if const(layer == 0):
            sha3([pp, idx + TW_MSG], [signer[GEN ** 2], signer[GEN ** 3]], digest, tail=[rho, 0, 0, 0], len=80)
        else:
            sha3([pp, idx + TW_MSG], [root[0], rho], digest)

        # The codeword: DIGIT_GROUP digits at a time, hinted in the exponent, range
        # checked and dispatched once, the arm walking every chain's remaining steps
        # and folding its digits in: their sums into a product that must be the
        # target sum, and the digits, each where the digest holds it, into D, which
        # also checks the digits past LX_V are zero.
        steps = StackBuf(CHAIN_STEPS)
        for st in unroll(0, CHAIN_STEPS):
            steps[st] = idx + const(TW_CHAIN + st * STEP_MUL)
        walks = StackBuf(LX_V * CHAIN_STEPS * SHA3_STATE)
        digit_product = 1
        encoded = 0
        for p in unroll(0, LX_V // DIGIT_GROUP):
            group = hint_witness("digits")
            assert log(group) < DIGIT_GROUPS
            digit_product, encoded = match(log(group), range(0, DIGIT_GROUPS), lambda k: walk_group(steps, pp, walks, DIGIT_GROUP * p, DIGIT_GROUP, k, 1, powers, digit_product, encoded))
        group = hint_witness("digits")
        assert log(group) < CHAIN_LENGTH
        digit_product, encoded = match(log(group), range(0, CHAIN_LENGTH), lambda k: walk_group(steps, pp, walks, LX_V - 1, 1, k, 1, powers, digit_product, encoded))
        digest[0] = encoded  # the digits, stored where D already is
        assert digit_product == GEN ** LX_TARGET_SUM

        # The one-time leaf, then the path to the layer's root.
        leaf = StackBuf(SHA3_STATE)
        wots_leaf(pp, idx + TW_LEAF, walks, LX_V, leaf)
        root = StackBuf(SHA3_STATE)
        merkle_path(leaf[0], pp, bits, nodes, root, LX_HEIGHT * layer, LX_HEIGHT, 2 * LX_HEIGHT, layer)
    assert root[0] == signer[1]
    return


# ======================== leanSPHINCS signature verification ======================


@inline
def sp_from_bytes(byte_bits, marks, n: Const, top: Const):
    # The integer whose n bytes, low first, are hinted in the exponent at marks[k]:
    # each range checked (the top one below `top`, SP_BYTE_VALUES or SP_UNUSED_TOP)
    # and read off `byte_bits` as the bits it spells, so the integer is below
    # top * 2^(8 (n - 1)).
    for t in unroll(0, n):
        k = n - 1 - t
        if const(t == 0):
            if const(top == SP_BYTE_VALUES):
                assert log(marks[k]) < SP_BYTE_VALUES
            else:
                assert log(marks[k]) < SP_UNUSED_TOP
            value = byte_bits[marks[k]]
        else:
            assert log(marks[k]) < SP_BYTE_VALUES
            value = byte_bits[marks[k]] + value * GEN ** 8
    return value


@inline
def sp_forest_top(at, pp, tws, tops, t: Const, i: Const):
    # Chain i of the forest key at codeword t, walked its digit's steps up to the top,
    # the step leaving position s at address at + tws[SP_FTOP * i + s]. A top past the
    # block's first four cells lands in the tail run `tops`, the others are read where
    # the walk left them.
    if const(SP_CODEWORDS[SP_FCHAINS * t + i] == 0):
        if const(i // 2 == 0):
            value = hint_witness("sp_forest_values")
        else:
            hint_witness(tops[i - 2:i - 1], "sp_forest_values")
            value = tops[i - 2]
    else:
        value = hint_witness("sp_forest_values")
        for s in unroll(SP_FTOP - SP_CODEWORDS[SP_FCHAINS * t + i], SP_FTOP):
            out = StackBuf(SHA3_STATE)
            sha3([pp, at + tws[SP_FTOP * i + s]], [value, 0], out, len=48)
            value = out[0]
        if const(i // 2 != 0):
            tops[i - 2] = value
    return value


@inline
def sp_forest_key(at, pp, tws, t: Const, w: Const):
    # One opened WOTS key of the forest, at the codeword of table index t, walked in
    # the arm itself: each chain its digit's steps up to the top, and the subtree leaf
    # the tops hash to. Returns that leaf and t where the digest holds it, codeword w's
    # byte, which is how a dispatch that came from a hint is bound.
    tops = StackBuf(4)
    top_0 = sp_forest_top(at, pp, tws, tops, t, 0)
    top_1 = sp_forest_top(at, pp, tws, tops, t, 1)
    for i in unroll(2, SP_FCHAINS):
        top = sp_forest_top(at, pp, tws, tops, t, i)  # in `tops`
    # P, A and the six tops: 128 bytes, one block.
    leaf = StackBuf(SHA3_STATE)
    sha3([pp, at + tws[SP_FCHAINS * SP_FTOP]], [top_0, top_1], leaf, tail=tops)
    if const(w // 8 == 0):
        weight = const(t * 2 ** (8 * w))
    else:
        weight = const(t * 2 ** (8 * (w - 8))) * Y_TOWER
    return leaf[0], weight


@inline
def sp_fold(node, at, pp, out, tws, slot: Const, index: Const, height: Const, tw: Const, level_mul: Const, node_mul: Const, own_mul: Const, preset: Const):
    # Fold leaf `index` of a tree of the forest up its hinted path, into the
    # tree's two top nodes, out[slot] and out[slot + 1]. No hash joins them: the
    # path's last element is the top node the fold does not reach. The index is
    # the arm's constant, so the order of each pair and every node's address are
    # the program's. `at` is the leaf's own address, own_mul its field's unit: a
    # node's level and index take that field's place. With `preset`, what a node's
    # address adds is tws[(height - 1) * index + level], set once for every arm.
    cur = node
    for level in unroll(0, height - 1):
        sibling = hint_witness("sp_forest_nodes")
        parent = StackBuf(SHA3_STATE)
        if const(preset == 1):
            address = at + tws[(height - 1) * index + level]
        else:
            address = at + (const(index * own_mul) + const(tw + (level + 1) * level_mul + (index // 2 ** (level + 1)) * node_mul))
        if const((index // 2 ** level) % 2 == 0):
            sha3([pp, address], [cur, sibling], parent)
        else:
            sha3([pp, address], [sibling, cur], parent)
        cur = parent[0]
    out[slot + index // 2 ** (height - 1)] = cur
    hint_witness(out[slot + 1 - index // 2 ** (height - 1):slot + 2 - index // 2 ** (height - 1)], "sp_forest_nodes")
    return


@inline
def sp_subtree_arm(node, key_at, pp, subtops, sub_tws, c: Const, j: Const, a: Const):
    # The path of WOTS key `a` in subtree j, from the key's address. Returns the
    # subtree and `a` as its addresses hold them, and `a` as the digest does, which
    # is what binds the dispatch.
    sp_fold(node, key_at, pp, subtops, sub_tws, 2 + 2 * j, a, SP_SUBTREE_HEIGHT, SP_TW_FSUBNODE, SP_SUBNODE_LEVEL_MUL, SP_SUBNODE_MUL, SP_KEY_MUL, 1)
    return const(j * SP_SUBTREE_MUL + a * SP_KEY_MUL), const(a) * COORD_BASIS[SP_KEY_OFF + (2 * c + j) * SP_SUBTREE_HEIGHT]


@inline
def sp_tree_arm(node, leaf_at, pp, tops, sub_tws, c: Const, s: Const):
    # The path of leaf `s` in tree c, from the leaf's address, likewise.
    sp_fold(node, leaf_at, pp, tops, sub_tws, 2 + 2 * c, s, SP_TREE_HEIGHT, SP_TW_FNODE, SP_FNODE_LEVEL_MUL, SP_FNODE_MUL, SP_LEAF_MUL, 0)
    return const(c * HI_MUL + s * SP_LEAF_MUL), const(s) * COORD_BASIS[SP_LEAF_OFF + c * SP_TREE_HEIGHT]


def verify_sig_lean_sphincs(signer, byte_bits):
    # `signer` is one 4-cell entry of the leanSPHINCS coverage table: the pubkey's root and
    # public parameter, then the message THAT signer signed, the two bound together
    # by the signer-set digest, as for leanXMSS.
    pp = signer[GEN]

    # ---- the message digest, which chooses the few-time key and what it opens ----
    # D = H(P | A | m | rho), 80 bytes in one block.
    rho = hint_witness("sp_rand")
    digest = StackBuf(SHA3_STATE)
    sha3([pp, TW_MSG], [signer[GEN ** 2], signer[GEN ** 3]], digest, tail=[rho, 0, 0, 0], len=80)

    # The digest's first cell is the sixteen codewords and its second is bit
    # fields. A field a dispatch takes (a codeword, a tree's leaf, a subtree's
    # WOTS key) is hinted in the exponent and bound by what its arm returns, the
    # field as the digest holds it. The index is advice bits, pinned Boolean, and
    # the unused bits hinted bytes (sp_from_bytes). `bound` gathers what the second
    # cell's fields weigh.
    bits = StackBuf(SP_H)
    hint_decompose_bits(bits, digest[1], SP_H)
    for i in unroll(0, SP_H):
        bits[i] = bits[i] * bits[i]
    # nodes[l] is idx >> l: the index, then the node above it on each level.
    nodes = StackBuf(SP_H)
    shifts(bits, 0, SP_H, nodes)
    idx = nodes[0]
    unused_bytes = StackBuf(SP_UNUSED_BYTES)
    hint_witness(unused_bytes, "sp_unused")
    unused = sp_from_bytes(byte_bits, unused_bytes, SP_UNUSED_BYTES, SP_UNUSED_TOP)
    bound = idx + unused * COORD_BASIS[SP_USED_BITS]

    # ---- the few-time signature: two opened WOTS keys per tree of the forest ----
    # The encoding's input: P, A, then tree c's top nodes at tops[2 + 2c], the
    # few-time key, which no hash folds.
    tops = StackBuf(2 + 2 * SP_TREES)
    tops[0] = pp
    tops[1] = idx + SP_TW_ENC
    encoded_words = 0
    # What a forest key's addresses add to the key's own, the same for every key: its
    # chains' steps, then its leaf. Set once here, where each arm would set its own.
    tws = StackBuf(SP_FCHAINS * SP_FTOP + 1)
    for i in unroll(0, SP_FCHAINS):
        for s in unroll(0, SP_FTOP):
            tws[SP_FTOP * i + s] = const(SP_TW_FCHAIN + i * SP_FCHAIN_MUL + s * STEP_MUL)
    tws[SP_FCHAINS * SP_FTOP] = SP_TW_FKEY_LEAF
    # Likewise what a subtree node's address adds to its key's, by key and level.
    sub_tws = StackBuf(SP_KEYS * (SP_SUBTREE_HEIGHT - 1))
    for a in unroll(0, SP_KEYS):
        for level in unroll(0, SP_SUBTREE_HEIGHT - 1):
            sub_tws[(SP_SUBTREE_HEIGHT - 1) * a + level] = const(a * SP_KEY_MUL) + const(SP_TW_FSUBNODE + (level + 1) * SP_SUBNODE_LEVEL_MUL + (a // 2 ** (level + 1)) * SP_SUBNODE_MUL)
    for c in unroll(0, SP_TREES):
        # The tree's leaf: g^s, and the tree and s where an address holds them,
        # which the dispatch on the first writes again.
        leaf_mark = StackBuf(2)
        hint_witness(leaf_mark, "sp_leaves")
        assert log(leaf_mark[0]) < SP_LEAVES
        leaf_at = idx + leaf_mark[1]
        # The tree leaf's input: P, A, then subtree j's top nodes at subtops[2 + 2j].
        subtops = StackBuf(6)
        subtops[0] = pp
        subtops[1] = leaf_at + SP_TW_FTREE_LEAF
        for j in unroll(0, 2):
            # Likewise the subtree and its WOTS key.
            key_mark = StackBuf(2)
            hint_witness(key_mark, "sp_keys")
            assert log(key_mark[0]) < SP_KEYS
            word = hint_witness("sp_words")
            assert log(word) < SP_WORDS
            key_at = leaf_at + key_mark[1]
            node, weight = match(log(word), range(0, SP_WORDS), lambda t: sp_forest_key(key_at, pp, tws, t, 2 * c + j))
            if const(2 * c + j + 1 == 2 * SP_TREES):
                # The last codeword: the sum stored where the digest's first cell
                # already is, which is the assert that the codewords are that cell.
                digest[0] = encoded_words + weight
            else:
                encoded_words = encoded_words + weight
            key_mark[1], key_weight = match(log(key_mark[0]), range(0, SP_KEYS), lambda a: sp_subtree_arm(node, key_at, pp, subtops, sub_tws, c, j, a))
            bound = bound + key_weight
        leaf = StackBuf(SHA3_STATE)
        sha3_cells(subtops, leaf)
        leaf_mark[1], leaf_weight = match(log(leaf_mark[0]), range(0, SP_LEAVES), lambda s: sp_tree_arm(leaf[0], leaf_at, pp, tops, sub_tws, c, s))
        if const(c + 1 == SP_TREES):
            digest[1] = bound + leaf_weight  # likewise, the second cell's fields
        else:
            bound = bound + leaf_weight
    # ---- the one-time signature of the few-time key ----
    # D = Th(P, A, key | LE_32(c)), the sixteen top nodes then the counter: 292
    # bytes, three blocks. The counter is rebuilt from its four bytes, so the guest
    # accepts no preimage the native verifier cannot parse.
    ctr_bytes = StackBuf(SP_COUNTER_BYTES)
    hint_witness(ctr_bytes, "sp_counter")
    ctr = sp_from_bytes(byte_bits, ctr_bytes, SP_COUNTER_BYTES, SP_BYTE_VALUES)
    first = StackBuf(SHA3_STATE)
    sha3(tops[0:2], tops[2:4], first, tail=tops[4:8], final=0)
    second = StackBuf(SHA3_STATE)
    sha3(tops[8:10], tops[10:12], second, tail=tops[12:16], state=first, final=0)
    encoding = StackBuf(SHA3_STATE)
    sha3(tops[16:18], [ctr, 0], encoding, state=second, len=36)

    # The codeword: DIGIT_GROUP digits at a time, hinted in the exponent, range
    # checked and dispatched once, the arm walking every chain's remaining steps
    # and folding its digits in: their sums into a product that must be the target
    # sum, and the digits, each group where the digest holds it, into D. The
    # one-time leaf's input is P, A, then the chains' tips.
    walks = StackBuf(SP_V * CHAIN_STEPS * SHA3_STATE)
    powers = StackBuf(DIGIT_GROUP * CHAIN_STEPS + 1)
    for s in unroll(0, DIGIT_GROUP * CHAIN_STEPS + 1):
        powers[s] = GEN ** s
    digit_product = 1
    encoded = 0
    for p in unroll(0, SP_V // DIGIT_GROUP):
        group = hint_witness("digits")
        assert log(group) < DIGIT_GROUPS
        digit_product, encoded = match(log(group), range(0, DIGIT_GROUPS), lambda k: walk_group(idx, pp, walks, DIGIT_GROUP * p, DIGIT_GROUP, k, 0, powers, digit_product, encoded))
    # The chain the groups leave over.
    group = hint_witness("digits")
    assert log(group) < CHAIN_LENGTH
    digit_product, encoded = match(log(group), range(0, CHAIN_LENGTH), lambda k: walk_group(idx, pp, walks, SP_V - 1, 1, k, 0, powers, digit_product, encoded))
    encoding[0] = encoded  # the digits, stored where D already is
    assert digit_product == GEN ** SP_TARGET_SUM

    # ---- the tree: the path from that one-time key to the public key's root ----
    leaf = StackBuf(SHA3_STATE)
    wots_leaf(pp, idx + TW_LEAF, walks, SP_V, leaf)
    root = StackBuf(SHA3_STATE)
    merkle_path(leaf[0], pp, bits, nodes, root, 0, SP_H, SP_H, 0)
    assert root[0] == signer[1]
    return


# =========================== statements and the signer set ==========================


def statement_digest(seed_0, seed_1, signers_hash, da_0, da_1, defer):
    # A node's statement, hashed to the two words the VM publishes, over the
    # proving environment's Fiat-Shamir seed (the Keccak relation and this bytecode), the
    # two-cell signer-set digest, the digest of its possibly empty DA root list,
    # and the DEFER_STMT_CELLS deferred-claim cells. A
    # parent rebuilds a child's statement with this same call, over a signer-set
    # digest it re-absorbed itself, which forces the child to be a proof of THIS
    # bytecode over claims read out of the parent's own tables.
    #
    # The preimage is fixed-length, so a plain hash beats the Fiat-Shamir chain.
    # A header value is a canonical cell and needs no check, the SHA3 table
    # reading only cells whose top limb is zero. A deferred cell is a full field
    # element, so two fill three cells as (s0,s1) (s2,t0) (t1,t2), each top limb
    # derived from the two hinted below it and each pack proving its lanes in K.
    cells = StackBuf(STMT_CELLS)
    cells[0] = seed_0  # the STMT_HEADER header cells
    cells[1] = seed_1
    cells[2] = signers_hash[1]
    cells[3] = signers_hash[GEN]
    cells[4] = da_0
    cells[5] = da_1
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
    st = StackBuf(SHA3_STATE)
    sha3_cells(cells, st)
    return st[0], st[1]


# The declared claim lists are hashed as flat runs of cells, eight a block, two
# claims of four cells, the sponge state carried between loop frames through a heap
# chain of STATE_SLOTS cells a step. A chain starts from the zero state, which a
# later block's XOR turns into a first block's message. A list's length is runtime,
# but every block before the last is full, so only the last block's shape depends
# on it, and that is a small `match`.


@inline
def zero_state(chain):
    for k in unroll(0, SHA3_STATE):
        chain[GEN ** k] = 0
    return


def list_split(n_g, per_block: Const):
    # A list of n items, per_block to a block, as (g^body, g^rest): body blocks
    # before the last, and rest + 1 items in the last. The range check and the
    # product identity leave that split the only solution.
    split = StackBuf(2)
    hint_witness(split, "signers_split")
    body = split[0]
    rest = split[1]
    # rest < per_block, which must hold before the caller dispatches on it: the
    # first check rules out a negative exponent, the second, shifted so its bound
    # is a literal, cuts the range down to per_block <= 4.
    assert log(rest) < 4
    assert log(rest * GEN ** (4 - per_block)) < 4
    assert log(body) < MAX_KEYS
    # Both exponents are small and nonnegative, so this is an identity over the
    # integers: per_block * body + rest + 1 == n.
    assert body ** per_block * rest * GEN == n_g
    return body, rest



def claim_list_digest(entries_ptr, n_g):
    # The hash of one scheme's declared claims: 64 bytes a claim, the claimed pubkey
    # then the message it signed, so two claims a block. An empty list hashes the
    # empty string, and the padding binds the length.
    digest = StackBuf(SHA3_STATE)
    if n_g == 1:
        sha3([0, 0], [0, 0], digest, len=0)
    else:
        body, rest = list_split(n_g, 2)
        chain = HeapBuf((body * GEN) ** STATE_SLOTS)
        zero_state(chain)
        for xq in mul_range(1, body):
            st = chain * xq ** STATE_SLOTS
            nxt = st * GEN ** STATE_SLOTS
            blk = entries_ptr * xq ** 8
            hint_witness(blk[0:4], "claims")
            hint_witness(blk[4:8], "claims")
            sha3(blk[0:2], blk[2:4], nxt[0:SHA3_STATE], tail=blk[4:8], state=st[0:SHA3_STATE], final=0)
        last = chain * body ** STATE_SLOTS
        d0, d1 = match(log(rest), range(0, 2), lambda k: claim_list_last(last, entries_ptr * body ** 8, k))
        digest[0] = d0
        digest[1] = d1
    return digest[0], digest[1]


def claim_list_last(state, blk, k: Const):
    hint_witness(blk[0:4], "claims")
    digest = StackBuf(SHA3_STATE)
    if k == 0:
        sha3(blk[0:2], blk[2:4], digest, state=state[0:SHA3_STATE], len=64)
    else:
        hint_witness(blk[4:8], "claims")
        sha3(blk[0:2], blk[2:4], digest, tail=blk[4:8], state=state[0:SHA3_STATE])
    return digest[0], digest[1]


@inline
def child_claim_entries(entries_ptr, cover, marks, origin_g, limit_g, blk, n: Const):
    # n of a child's claims, each read at a hinted index into THIS node's table and
    # marked in the coverage table. The index is an offset into the scheme's region
    # and bounded by that region's size, so a child's claim can only ever land on a
    # slot of its own scheme.
    for j in unroll(0, n):
        off_hint = hint_witness("child_claim_index")
        assert log(off_hint) < log(limit_g)  # precondition as in the raw loops
        cover[origin_g * off_hint] = marks * (GEN ** j)
        entry = entries_ptr * (off_hint ** 4)
        for c in unroll(0, 4):
            blk[4 * j + c] = entry[GEN ** c]
    return


def child_claim_list_digest(entries_ptr, cover, base, origin_g, limit_g, n_g):
    # The hash of one of a child's declared claim lists, over the same 64n bytes the
    # child hashed (`claim_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. The chain threads the coverage write value, which
    # counts the claims off as they are marked, from `base`.
    digest = StackBuf(SHA3_STATE)
    if n_g == 1:
        sha3([0, 0], [0, 0], digest, len=0)
    else:
        body, rest = list_split(n_g, 2)
        chain = HeapBuf((body * GEN) ** STATE_SLOTS)
        zero_state(chain)
        chain[GEN ** SHA3_STATE] = base
        for xq in mul_range(1, body):
            st = chain * xq ** STATE_SLOTS
            nxt = st * GEN ** STATE_SLOTS
            marks = st[GEN ** SHA3_STATE]
            blk = StackBuf(8)
            child_claim_entries(entries_ptr, cover, marks, origin_g, limit_g, blk, 2)
            sha3(blk[0:2], blk[2:4], nxt[0:SHA3_STATE], tail=blk[4:8], state=st[0:SHA3_STATE], final=0)
            nxt[GEN ** SHA3_STATE] = marks * GEN ** 2
        last = chain * body ** STATE_SLOTS
        d0, d1 = match(log(rest), range(0, 2), lambda k: child_claim_list_last(last, entries_ptr, cover, origin_g, limit_g, k))
        digest[0] = d0
        digest[1] = d1
    return digest[0], digest[1]


def child_claim_list_last(state, entries_ptr, cover, origin_g, limit_g, k: Const):
    blk = StackBuf(8)
    child_claim_entries(entries_ptr, cover, state[GEN ** SHA3_STATE], origin_g, limit_g, blk, k + 1)
    digest = StackBuf(SHA3_STATE)
    if k == 0:
        sha3(blk[0:2], blk[2:4], digest, state=state[0:SHA3_STATE], len=64)
    else:
        sha3(blk[0:2], blk[2:4], digest, tail=blk[4:8], state=state[0:SHA3_STATE])
    return digest[0], digest[1]



# ================================ LeanDA ===============================
# Hash the encoded rows and the hinted membership vector, then check their inner products.
# The external verifier derives the vector hash from the root; recursion preserves both.


def da_verify(g_squares):
    # Returns the matrix root and membership-vector hash, two canonical cells each.
    # The row count is a run-time parameter. The trees need a compile-time depth,
    # so the rows are padded to a power of two and the two `match`es below dispatch
    # on its log; everything else walks the real rows only. A padding row is the
    # zero codeword, so its cell digest and its row digest are constants, and the
    # gap loop writes them without hashing anything.
    shape = StackBuf(2)
    hint_witness(shape, "da_shape")  # n_blob, then log2 of the padded count
    n_blob_g = shape[0]
    g_log_pad = shape[1]
    n_pad_g, gap_g = da_row_shape(n_blob_g, g_log_pad, g_squares)

    prefix_digests = HeapBuf(n_pad_g ** (2 * DA_PREFIX_CELLS))
    prefix_bases = HeapBuf(n_blob_g)
    for xi in mul_range(1, n_blob_g):
        prefix_bases[xi] = prefix_digests * (xi ** (2 * DA_PREFIX_CELLS))

    # The membership vector's hash, one column's weights at a time: every column's
    # weights are whole blocks, so the sponge state rides the chain between columns
    # and only the last block of the last column is final.
    hashes = HeapBuf(SHA3_STATE * (DA_CELLS + 1))
    zero_state(hashes)

    # Each row's running sum uses a fresh write-once cell per column.
    acc = HeapBuf(n_blob_g ** (DA_CELLS + 1))
    rowbase = HeapBuf(n_blob_g)
    for xi in mul_range(1, n_blob_g):
        chain = acc * (xi ** (DA_CELLS + 1))
        rowbase[xi] = chain
        chain[1] = 0

    # Prefix blocks first, so the digests the row branch needs are stored by a
    # loop that knows it is inside the prefix, with no per-block branch.
    coltree = HeapBuf(4 * DA_CELLS)
    for xb in mul_range(1, GEN ** DA_PREFIX_CELLS):
        da_verify_column(xb, n_blob_g, n_pad_g, gap_g, g_log_pad, prefix_bases, coltree, rowbase, hashes, 1)
    for xb in mul_range(GEN ** DA_PREFIX_CELLS, GEN ** DA_CELLS):
        da_verify_column(xb, n_blob_g, n_pad_g, gap_g, g_log_pad, prefix_bases, coltree, rowbase, hashes, 0)

    for xi in mul_range(1, n_blob_g):
        chain = rowbase[xi]
        assert chain[GEN ** DA_CELLS] == 0
    rc0, rc1 = da_levels(coltree, DA_CELLS, DA_BLOCK_BITS)

    # The row branch: each row's prefix digests, hashed as one string.
    rowtree = HeapBuf(n_pad_g ** 4)
    for xi in mul_range(1, n_blob_g):
        run = prefix_bases[xi]
        st = StackBuf(SHA3_STATE)
        sha3_cells(run[0:2 * DA_PREFIX_CELLS], st)
        slot = rowtree * (xi ** 2)
        slot[1] = st[0]
        slot[GEN] = st[1]
    for xd in mul_range(1, gap_g):
        pad = rowtree * (n_blob_g ** 2) * (xd ** 2)
        pad[1] = DA_PAD_ROW_0
        pad[GEN] = DA_PAD_ROW_1
    rr0, rr1 = match(log(g_log_pad), range(0, DA_TREE_ARMS), lambda k: da_levels(rowtree, 2 ** k, k))

    root = StackBuf(SHA3_STATE)
    sha3([rr0, rr1], [rc0, rc1], root)
    return root[0], root[1], hashes[GEN ** (SHA3_STATE * DA_CELLS)], hashes[GEN ** (SHA3_STATE * DA_CELLS + 1)]


def da_row_shape(n_blob_g, g_log_pad, g_squares):
    assert n_blob_g != 1
    assert log(n_blob_g) < DA_MAX_ROWS + 1
    assert log(g_log_pad) < DA_LOG_MAX_ROWS + 1
    n_pad_g = g_squares[g_log_pad]
    # n_blob <= n_pad < 2*n_blob: both differences must be nonnegative.
    gap_g = n_pad_g / n_blob_g
    assert log(gap_g) < DA_MAX_ROWS + 1
    assert log(n_blob_g * n_blob_g / (n_pad_g * GEN)) < DA_MAX_ROWS
    return n_pad_g, gap_g


def da_verify_column(xb, n_blob_g, n_pad_g, gap_g, g_log_pad, prefix_bases, coltree, rowbase, hashes, store: Const):
    st = hashes * (xb ** SHA3_STATE)
    lvals = da_vector_dispatch(xb, st, st * GEN ** SHA3_STATE)
    node = HeapBuf(n_pad_g ** 4)
    for xi in mul_range(1, n_blob_g):
        d0, d1, s = da_verify_cell(lvals)
        chain = rowbase[xi] * xb
        chain[GEN] = chain[1] + s
        leaf = node * (xi ** 2)
        leaf[1] = d0
        leaf[GEN] = d1
        if const(store == 1):
            slot = prefix_bases[xi] * (xb * xb)
            slot[1] = d0
            slot[GEN] = d1
    for xd in mul_range(1, gap_g):
        pad = node * (n_blob_g ** 2) * (xd ** 2)
        pad[1] = DA_PAD_CELL_0
        pad[GEN] = DA_PAD_CELL_1
    c0, c1 = match(log(g_log_pad), range(0, DA_TREE_ARMS), lambda k: da_levels(node, 2 ** k, k))
    out = coltree * (xb * xb)
    out[1] = c0
    out[GEN] = c1
    return


def da_verify_cell(lvals):
    # Packing checks that each symbol used by both the hash and dot product is in K.
    sym = StackBuf(DA_CELL)
    hint_witness(sym, "da_symbols")
    packed = StackBuf(DA_PACKED)
    s = 0
    for e in unroll(0, DA_PACKED):
        packed[e] = pack64x2(sym[2 * e], sym[2 * e + 1])
        s = s + lvals[GEN ** (2 * e)] * sym[2 * e]
        s = s + lvals[GEN ** (2 * e + 1)] * sym[2 * e + 1]
    st = StackBuf(SHA3_STATE)
    sha3_cells(packed, st)
    return st[0], st[1], s


def da_levels(tree, n: Const, log_n: Const):
    # The internal levels of a Merkle tree whose leaves already sit at level 0 of
    # `tree` (2 cells a node, level lvl at 4n - 4n//2**lvl). Returns the root pair.
    for lvl in unroll(0, log_n):
        for xp in mul_range(1, GEN ** (n // 2 ** (lvl + 1))):
            a = tree * (GEN ** (4 * n - 4 * n // 2 ** lvl)) * (xp ** 4)
            b = tree * (GEN ** (4 * n - 4 * n // 2 ** (lvl + 1))) * (xp * xp)
            sha3(a[0:2], a[2:4], b[0:2])
    return tree[GEN ** (4 * n - 4)], tree[GEN ** (4 * n - 3)]


def da_vector_dispatch(xb, state, next_state):
    # The last column's last block ends the vector's hash.
    out = StackBuf(1)
    if xb == GEN ** (DA_CELLS - 1):
        out[0] = da_vector_cell(state, next_state, 1)
    else:
        out[0] = da_vector_cell(state, next_state, 0)
    return out[0]


def da_vector_cell(state, next_state, final: Const):
    # One column's weights, absorbed into the vector's hash from `state`, the
    # result written to `next_state`. Two extension-field entries become three
    # canonical 128-bit cells, without padding.
    weights = StackBuf(DA_CELL)
    hint_witness(weights[0:DA_CELL], "da_weights")
    packed = StackBuf(DA_WEIGHT_CELLS)
    for p in unroll(0, DA_CELL // 2):
        s = weights[2 * p]
        t = weights[2 * p + 1]
        slo = StackBuf(2)
        tlo = StackBuf(2)
        hint_f192_limbs(slo, s)
        hint_f192_limbs(tlo, t)
        packed[3 * p] = pack64x2(slo[0], slo[1])
        packed[3 * p + 1] = pack64x2(((s + slo[0]) * Y_INV + slo[1]) * Y_INV, tlo[0])
        packed[3 * p + 2] = pack64x2(tlo[1], ((t + tlo[0]) * Y_INV + tlo[1]) * Y_INV)
    st = StackBuf(SHA3_STATE)
    sha3(packed[0:2], packed[2:4], st, tail=packed[4:8], state=state[0:SHA3_STATE], final=0)
    for b in unroll(1, DA_WEIGHT_CELLS // 8 - 1):
        nxt = StackBuf(SHA3_STATE)
        sha3(packed[8 * b:8 * b + 2], packed[8 * b + 2:8 * b + 4], nxt, tail=packed[8 * b + 4:8 * b + 8], state=st, final=0)
        st = nxt
    b = DA_WEIGHT_CELLS // 8 - 1
    if const(final == 1):
        sha3(packed[8 * b:8 * b + 2], packed[8 * b + 2:8 * b + 4], next_state[0:SHA3_STATE], tail=packed[8 * b + 4:8 * b + 8], state=st)
    else:
        sha3(packed[8 * b:8 * b + 2], packed[8 * b + 2:8 * b + 4], next_state[0:SHA3_STATE], tail=packed[8 * b + 4:8 * b + 8], state=st, final=0)
    weights_ptr = addr(weights)
    return weights_ptr

# ================================ the aggregation node ==============================


def da_list_digest(roots, n_g):
    # At most 16 roots, so the count dispatches to a compile-time length.
    a, b = match(log(n_g), range(0, DA_ROOT_COUNTS), lambda n: da_hash_roots(roots, n))
    return a, b


def da_hash_roots(roots, n: Const):
    digest = StackBuf(SHA3_STATE)
    if const(n == 0):
        sha3([0, 0], [0, 0], digest, len=0)
    else:
        sha3_cells(roots[0:4 * n], digest)
    return digest[0], digest[1]


def cover_da_root(roots, cover, n_slots_g, mark):
    index = hint_witness("da_index")
    assert log(index) < log(n_slots_g)
    cover[index] = mark
    root = roots * (index ** 4)
    return root[1], root[GEN], root[GEN ** 2], root[GEN ** 3]


def main():
    # One node of an aggregation tree: n_raw_lean_xmss leanXMSS signatures, n_raw_lean_sphincs
    # leanSPHINCS signatures and n_children sub-proofs OF THIS SAME BYTECODE. A claim of
    # either scheme is a pubkey and the message it signed, and each signature is
    # verified against the claim in its own coverage slot; a leanXMSS signature carries
    # its own leaf index. DA roots occupy a separate region of the same table.
    #
    # The declared lists are the signer set; the duplicate slots absorb claims a
    # child covers that the set does not declare. The coverage table is one region
    # per scheme, each its declared claims then its own duplicates, then DA shaped
    # the same way:
    #
    #   [leanXMSS: declared | dup][leanSPHINCS: declared | dup][DA: declared | dup]
    #
    # so one range check per write keeps each writer inside its own region: that is
    # what makes the statement's split mean which scheme verified which claim. A
    # signature slot is four cells, a pubkey and the message that pubkey signed; a DA root
    # occupies two cells.
    meta = StackBuf(8)
    hint_witness(meta, "meta")  # every count in the exponent
    n_lx_g = meta[0]
    n_xdup_g = meta[1]
    n_raw_x_g = meta[2]
    n_lean_sphincs_g = meta[3]
    n_sdup_g = meta[4]
    n_raw_s_g = meta[5]
    n_children_g = meta[6]
    n_direct_da_g = meta[7]
    assert log(n_lx_g) < MAX_KEYS
    assert log(n_xdup_g) < MAX_KEYS
    assert log(n_raw_x_g) < MAX_KEYS
    assert log(n_lean_sphincs_g) < MAX_KEYS
    assert log(n_sdup_g) < MAX_KEYS
    assert log(n_raw_s_g) < MAX_KEYS
    assert log(n_children_g) < MAX_RECURSIONS + 1
    assert log(n_direct_da_g) < 2
    da_meta = StackBuf(2)
    hint_witness(da_meta, "da_meta")
    n_da_g = da_meta[0]
    n_da_dup_g = da_meta[1]
    assert log(n_da_g) < MAX_DA_ROOTS + 1
    assert log(n_da_dup_g) < MAX_RECURSIONS * MAX_DA_ROOTS + 2
    da_slots_g = n_da_g * n_da_dup_g
    assert log(da_slots_g) < MAX_RECURSIONS * MAX_DA_ROOTS + 2
    lx_slots_g = n_lx_g * n_xdup_g
    lean_sphincs_slots_g = n_lean_sphincs_g * n_sdup_g
    # The sum of every region bounds the coverage indices, so it is what has to sit
    # below the minimum memory size.
    da_base_g = lx_slots_g * lean_sphincs_slots_g
    n_total_g = da_base_g * da_slots_g
    assert log(n_total_g) < MAX_KEYS

    # The proving environment (the Keccak relation and this bytecode) as one digest. It
    # rides the statement rather than the bytecode, so nothing here has to know its
    # own hash; the outer verifier pins it, and every child statement rebuilt below
    # copies it, which is what keeps a whole tree on one bytecode.
    fs_seed = StackBuf(2)
    hint_witness(fs_seed, "fs_seed")
    seed_0 = fs_seed[0]
    seed_1 = fs_seed[1]

    # ---- the signer set ----
    g_logs_pow2, g_squares = exponent_tables()

    # ---- data availability ----
    da_roots = HeapBuf(da_slots_g ** 4)
    for xd in mul_range(1, da_slots_g):
        root = da_roots * (xd ** 4)
        hint_witness(root[0:4], "da_roots")
    da_0, da_1 = da_list_digest(da_roots, n_da_g)
    # One table per scheme: its declared list (strictly sorted, checked by the outer
    # verifier, which holds it) followed by its own duplicate slots. The coverage
    # indices below run over one space: leanXMSS, then leanSPHINCS, then DA.
    #
    # Each list's digest is a plain hash of its claims, 64 bytes a claim, its padding
    # binding its length; the signer set is one permutation over the two digests.
    lx_table = HeapBuf(lx_slots_g ** 4)
    lean_sphincs_table = HeapBuf(lean_sphincs_slots_g ** 4)
    xd_0, xd_1 = claim_list_digest(lx_table, n_lx_g)
    sd_0, sd_1 = claim_list_digest(lean_sphincs_table, n_lean_sphincs_g)
    # The duplicate slots ride the same tables but outside the hashed prefixes.
    for xd in mul_range(1, n_xdup_g):
        dup = lx_table * ((n_lx_g * xd) ** 4)
        hint_witness(dup[0:4], "dup_claims")
    for xd in mul_range(1, n_sdup_g):
        dup = lean_sphincs_table * ((n_lean_sphincs_g * xd) ** 4)
        hint_witness(dup[0:4], "dup_claims")
    # At least one published signature claim or DA root also ensures a nonempty coverage table.
    assert n_lx_g * n_lean_sphincs_g * n_da_g != 1
    signers = StackBuf(SHA3_STATE)
    sha3([xd_0, xd_1], [sd_0, sd_1], signers)
    signers_hash = HeapBuf(DIGEST_CELLS)
    signers_hash[1] = signers[0]
    signers_hash[GEN] = signers[1]

    # ---- coverage ----
    # Every one of the n_total slots is written exactly once: write-once memory
    # rejects a second write (the value written is the running count, so two writes
    # to one slot disagree), and the count below rejects a missed one. So every
    # declared claim is covered by a direct check of its own kind or by a verified
    # child. Each writer is confined to its own region, including DA roots.
    cover = HeapBuf(n_total_g)
    da_cover = cover * da_base_g
    # byte_bits[g^v] = v, read at a hinted byte's exponent (sp_from_bytes).
    byte_bits = HeapBuf(SP_BYTE_VALUES)
    for v in unroll(0, SP_BYTE_VALUES):
        byte_bits[GEN ** v] = v
    for xi in mul_range(1, n_raw_x_g):
        idx = hint_witness("raw_index")
        # A runtime bound, whose `n_total < 2^MIN_LOG_MEM` precondition is
        # discharged by `assert log(n_total_g) < MAX_KEYS` above. Without it this
        # degenerates to what DEREF alone gives and an index could reach past
        # `cover`, which is the whole bijection. The bound is the leanXMSS region, so
        # a raw leanXMSS signature covers no leanSPHINCS claim.
        assert log(idx) < log(lx_slots_g)
        cover[idx] = xi
        verify_lean_xmss(lx_table * (idx ** 4))
    for xj in mul_range(1, n_raw_s_g):
        off_hint = hint_witness("sp_raw_index")
        assert log(off_hint) < log(lean_sphincs_slots_g)
        cover[lx_slots_g * off_hint] = n_raw_x_g * xj
        verify_sig_lean_sphincs(lean_sphincs_table * (off_hint ** 4), byte_bits)

    if n_direct_da_g == GEN:
        root_0, root_1, vector_0, vector_1 = da_verify(g_squares)
        expected_0, expected_1, expected_v0, expected_v1 = cover_da_root(da_roots, da_cover, da_slots_g, n_raw_x_g * n_raw_s_g)
        assert root_0 == expected_0
        assert root_1 == expected_1
        assert vector_0 == expected_v0
        assert vector_1 == expected_v1

    # ---- children ----
    child_pi = HeapBuf(n_children_g * n_children_g)
    child_fresh = HeapBuf(n_children_g ** DEFER_SIZE)
    child_carried = HeapBuf(n_children_g ** DEFER_STMT_CELLS)
    written = HeapBuf(n_children_g * GEN)  # loop-carried write count, one per child
    written[GEN ** 0] = n_raw_x_g * n_raw_s_g * n_direct_da_g
    for xc in mul_range(1, n_children_g):
        base = written[xc]
        # The child's two list lengths, then its two lists, rebuilt from THIS node's
        # tables through hinted indices: everything hinted there is pinned by the
        # list digests, which the child's statement carries, so a lie about any of it
        # changes the public input its proof has to satisfy.
        child_meta = StackBuf(2)
        hint_witness(child_meta, "child_meta")  # n_lean_xmss, n_lean_sphincs
        nsub_x_g = child_meta[0]
        nsub_s_g = child_meta[1]
        assert log(nsub_x_g) < MAX_KEYS
        assert log(nsub_s_g) < MAX_KEYS
        nsub_g = nsub_x_g * nsub_s_g
        cx_0, cx_1 = child_claim_list_digest(lx_table, cover, base, 1, lx_slots_g, nsub_x_g)
        cs_0, cs_1 = child_claim_list_digest(lean_sphincs_table, cover, base * nsub_x_g, lx_slots_g, lean_sphincs_slots_g, nsub_s_g)
        sub_signers = StackBuf(SHA3_STATE)
        sha3([cx_0, cx_1], [cs_0, cs_1], sub_signers)
        sub_hash = HeapBuf(DIGEST_CELLS)
        sub_hash[1] = sub_signers[0]
        sub_hash[GEN] = sub_signers[1]
        carried = child_carried * xc ** DEFER_STMT_CELLS
        hint_witness(carried[0:DEFER_STMT_CELLS], "child_defer")
        nsub_da_g = hint_witness("child_da_count")
        assert log(nsub_da_g) < MAX_DA_ROOTS + 1
        child_da = HeapBuf(nsub_da_g ** 4)
        for xd in mul_range(1, nsub_da_g):
            root = child_da * (xd ** 4)
            root_0, root_1, vector_0, vector_1 = cover_da_root(da_roots, da_cover, da_slots_g, base * nsub_g * xd)
            root[1] = root_0
            root[GEN] = root_1
            root[GEN ** 2] = vector_0
            root[GEN ** 3] = vector_1
        child_da_0, child_da_1 = da_list_digest(child_da, nsub_da_g)
        pi_0, pi_1 = statement_digest(seed_0, seed_1, sub_hash, child_da_0, child_da_1, carried)
        pi = xc * xc
        child_pi[pi] = pi_0
        child_pi[pi * GEN] = pi_1
        verify_sub(pi_0, pi_1, seed_0, seed_1, g_logs_pow2, g_squares, child_fresh * xc ** DEFER_SIZE)
        written[xc * GEN] = base * nsub_g * nsub_da_g
    assert written[n_children_g] == n_total_g

    # ---- this node's own deferred claim ----
    defer_stmt = HeapBuf(DEFER_STMT_CELLS)
    if n_children_g == 1:
        # A leaf has nothing to batch, so it defers the bytecode at the all-zeros
        # point. The value rides a hint and is checked nowhere here: the outer
        # verifier recomputes it and rebuilds the statement, so a lie changes the
        # public input rather than the claim.
        leaf_value = hint_witness("leaf_defer")
        for k in unroll(0, BYTECODE_VARS):
            defer_stmt[GEN ** k] = 0
        defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = leaf_value
    else:
        aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt)

    own_0, own_1 = statement_digest(seed_0, seed_1, signers_hash, da_0, da_1, defer_stmt)
    pub_ptr = GEN ** 0
    assert pub_ptr[1] == own_0
    assert pub_ptr[GEN] == own_1
    return


def aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt):
    # Every child contributes two claims on the stacked bytecode: the one IT
    # deferred (carried in its statement) and the fresh one raised by verifying its
    # proof. A fresh transcript binds all of them, samples the batching
    # coefficients, and one sumcheck reduces the lot to one claim, which is what the
    # node then defers in its own statement.
    bc_msgs = HeapBuf(2 * BYTECODE_VARS)
    hint_witness(bc_msgs[0:2 * BYTECODE_VARS], "bc_sumcheck_msgs")
    bytecode_star = hint_witness("bc_star_hint")

    # ---- one transcript over every child's statement and both its claim sets ----
    # The count, padded to a full rate, then each child's words, padded likewise: a
    # child starts by permuting the full rate the previous one left waiting, which
    # every record carries (PEND_SLOTS) beside its capacity.
    fresh_row = HeapBuf(n_children_g)
    carried_row = HeapBuf(n_children_g)
    seed = [AGG_SEED_0, AGG_SEED_1, AGG_SEED_2, AGG_SEED_3, AGG_SEED_4]
    rate = StackBuf(8)
    fs_pack(rate, 0, n_children_g, DS_OBSERVE)
    for j in unroll(1, 4):
        fs_pack(rate, j, 0, DS_OBSERVE)
    absorb = HeapBuf((n_children_g * GEN) ** PEND_SLOTS)
    for j in unroll(0, FS_CELLS):
        absorb[GEN ** j] = seed[j]
    for j in unroll(0, 8):
        absorb[GEN ** (FS_CELLS + j)] = rate[j]
    for xc in mul_range(1, n_children_g):
        row = absorb * xc ** PEND_SLOTS
        row_cap = fs_load(row, 0, 1)
        st = fs_perm_pending(row_cap, row, FS_CELLS)
        rate = StackBuf(8)
        pi = xc * xc
        fresh = child_fresh * xc ** DEFER_SIZE
        fresh_row[xc] = fresh
        carried = child_carried * xc ** DEFER_STMT_CELLS
        carried_row[xc] = carried
        for pos in unroll(0, AGG_CHILD_WORDS + AGG_CHILD_PAD):
            if pos % 4 == 0:
                if pos != 0:
                    st = fs_perm(st, rate, 4)
                    rate = StackBuf(8)
            if const(pos // 2 == 0):
                fs_pack(rate, pos % 4, child_pi[pi * GEN ** pos], DS_OBSERVE)
            if const(pos // 2 != 0):
                if const((pos - 2) // DEFER_SIZE == 0):
                    fs_pack(rate, pos % 4, fresh[GEN ** (pos - 2)], DS_OBSERVE)
                if const((pos - 2) // DEFER_SIZE != 0):
                    if const((pos - 2 - DEFER_SIZE) // DEFER_STMT_CELLS == 0):
                        fs_pack(rate, pos % 4, carried[GEN ** (pos - 2 - DEFER_SIZE)], DS_OBSERVE)
                    if const((pos - 2 - DEFER_SIZE) // DEFER_STMT_CELLS != 0):
                        fs_pack(rate, pos % 4, 0, DS_OBSERVE)
        nxt = row * GEN ** PEND_SLOTS
        fs_store(nxt, 0, 1, st)
        for j in unroll(0, 8):
            nxt[GEN ** (FS_CELLS + j)] = rate[j]
    absorbed = absorb * n_children_g ** PEND_SLOTS

    # ---- the batching sumcheck (BYTECODE_VARS variables, 2 claims per child) ----
    # Fresh and carried share one layout (point, then value), so the two differ
    # only in which buffer they come from. The first child's first challenge takes
    # the last full rate; every later record's pending cells are zero.
    lam_bc = HeapBuf(n_children_g * n_children_g)
    bc_chain = HeapBuf((n_children_g * GEN) ** ACC_SLOTS)
    for j in unroll(0, FS_CELLS):
        bc_chain[GEN ** (ACC_FS + j)] = absorbed[GEN ** j]
    for j in unroll(0, 8):
        bc_chain[GEN ** (ACC_PEND + j)] = absorbed[GEN ** (FS_CELLS + j)]
    bc_chain[GEN ** ACC_VALUE] = 0
    for xc in mul_range(1, n_children_g):
        row = bc_chain * xc ** ACC_SLOTS
        row_cap = fs_load(row, ACC_FS, 1)
        st = fs_perm_pending(row_cap, row, ACC_PEND)
        lam_fresh = challenge_from_state(st)
        no_rate = StackBuf(8)
        st, lam_carried = squeeze(st, no_rate, 0)
        pair = xc * xc
        lam_bc[pair] = lam_fresh
        lam_bc[pair * GEN] = lam_carried
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        nxt = row * GEN ** ACC_SLOTS
        fs_store(nxt, ACC_FS, 1, st)
        for j in unroll(0, 8):
            nxt[GEN ** (ACC_PEND + j)] = 0
        nxt[GEN ** ACC_VALUE] = row[GEN ** ACC_VALUE] + lam_fresh * fresh[GEN ** FRESH_BC_VALUE] + lam_carried * carried[GEN ** DEFER_STMT_BC_VALUE]
    bc_end = bc_chain * n_children_g ** ACC_SLOTS
    bc_running = bc_end[GEN ** ACC_VALUE]
    bc_point = HeapBuf(BYTECODE_VARS)
    fs0, fs1, fs2, fs3, fs4, bc_running = batch_sumcheck(bc_end[GEN ** ACC_FS], bc_end[GEN ** (ACC_FS + 1)], bc_end[GEN ** (ACC_FS + 2)], bc_end[GEN ** (ACC_FS + 3)], bc_end[GEN ** (ACC_FS + 4)], bc_msgs, bc_running, bc_point, BYTECODE_VARS)
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

    for k in unroll(0, BYTECODE_VARS):
        defer_stmt[GEN ** k] = bc_point[GEN ** k]
    defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = bytecode_star
    return
