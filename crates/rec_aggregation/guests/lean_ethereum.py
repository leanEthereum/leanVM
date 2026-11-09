# The recursive aggregation guest: zkDSL, not runnable Python (see
# crates/lean_compiler/zkDSL.md). One node of an aggregation tree verifies raw leanXMSS
# and leanSPHINCS signatures and sub-proofs OF THIS SAME BYTECODE, and publishes the
# statement digest binding its signature claims and at most one LeanDA root: that of a
# blob matrix it checks directly, or one of its children's, passed on.
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

# ------------------------------------------------------------- the field, GF(2^128)
# Tower F128 = F64[Y]/(Y^2+x*Y+1). Y_TOWER embeds Y for reassembling a word
# lo + hi*Y, and Y_INV = Y + x splits a word into its limbs once the low one is
# hinted. COORD_BASIS is the coordinate basis e_i of F128 (which spans the WHOLE
# field, unlike the g-power basis GEN**i, which spans only F64): hint_decompose_bits
# emits a word's coordinate bits, so a value reconstructs as Σ b_i·COORD_BASIS[i].
FIELD_BITS = 128
# A query position's path bits are dispatched on QW at a time (`walk_path`), and the windows one
# squeezed word's positions take fill at most QUERY_WINDOWS_CAP cells (`decode_query_windows`).
QW = 6
QUERY_WINDOWS_CAP = 36
BASE_FIELD_BITS = 64
Y_TOWER = Y_TOWER_PLACEHOLDER
Y_INV = Y_INV_PLACEHOLDER
COORD_BASIS = COORD_BASIS_PLACEHOLDER
# Phi, the F2-linear map that batches the 128 transposed ring-switch coordinates, is
# drawn as two rows of RING_MAP_WIDTH challenges, f_p then g_b. RING_W[p] = x^(-2^(64 - 8p)),
# the inverse of the target's Horner point z_p.
RING_MAP_WIDTH = 8
RING_W = RING_W_PLACEHOLDER
RS_CHUNK = 8  # ring-switch rows (target) or coordinates (weight) per loop iteration
RS_CHUNK_BITS = 3
RES_BATCH = 8  # residual queries per loop iteration
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
LAYER_VALS = 6  # the trees' claims, N_GKR_TREES of them
LAYER_ROW = 9
LAYER_POS = 10
LAYER_HALF = 11  # g^(k // 4) at radix-four layer k
LAYER_PARITY = 12  # g^(k % 4)
LAYER_SLOTS = 13

# ---------------------------------------------------- the bus: sides and blocks
# Bus sides, whose blocks the layout gives, and the GKR's trees, one a side: push and
# pull under the fingerprint (alphas, beta), then count, whose tuples are read at
# alpha = beta = 0. GKR_ROUNDS_CAP caps the round positions (triangle rounds plus one
# slot per layer) and GKR_POINTS_CAP the point triangle (rows x MU_CAP).
PUSH_SIDE = 0
PULL_SIDE = 1
COUNT_SIDE = 2
N_GKR_SIDES = 3
N_GKR_TREES = N_GKR_SIDES
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
N_COORDS = N_COORDS_PLACEHOLDER
BLOCK_KAPPA_SRC = BLOCK_KAPPA_SRC_PLACEHOLDER
BLOCK_KAPPA_ADJ = BLOCK_KAPPA_ADJ_PLACEHOLDER
BLOCK_TABLE = BLOCK_TABLE_PLACEHOLDER
BLOCK_SIDE = BLOCK_SIDE_PLACEHOLDER
N_BLOCK_GROUPS = N_BLOCK_GROUPS_PLACEHOLDER
BLOCK_GROUP_START = BLOCK_GROUP_START_PLACEHOLDER  # a block group's first block, then N_BLOCKS
SIDE_GROUP_START = SIDE_GROUP_START_PLACEHOLDER    # a side's first block group, then N_BLOCK_GROUPS
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
COORD_DIFF_OFF = COORD_DIFF_OFF_PLACEHOLDER  # a pull coordinate less its push twin's, as terms
COORD_DIFF_COUNT = COORD_DIFF_COUNT_PLACEHOLDER
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
# powers; the bus forms take ETA_FORM_BASE + tree, the SAME N_GKR_TREES powers for
# every table, and that sharing is what makes the batch's target derivable from the
# trees' leaf claims. FLOORS[t] is the table's least log height (the Keccak reduction
# is sized for at least one block of 2^9 steps).
TABLE_JUMP = 4
TABLE_KECCAK = 5
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
KECCAK_PROJ_A = KECCAK_PROJ_A_PLACEHOLDER
KECCAK_PROJ_B = KECCAK_PROJ_B_PLACEHOLDER
KECCAK_PROJ_OUT = KECCAK_PROJ_OUT_PLACEHOLDER
KECCAK_PROJ_CELLS = KECCAK_PROJ_CELLS_PLACEHOLDER
KECCAK_FAC_START = KECCAK_FAC_START_PLACEHOLDER
KECCAK_FAC_IDX = KECCAK_FAC_IDX_PLACEHOLDER
KECCAK_FAC_DEG = KECCAK_FAC_DEG_PLACEHOLDER
KECCAK_EMB_A = KECCAK_EMB_A_PLACEHOLDER
KECCAK_EMB_B = KECCAK_EMB_B_PLACEHOLDER
KECCAK_EMB_OUT = KECCAK_EMB_OUT_PLACEHOLDER
KECCAK_FAC_N = KECCAK_FAC_N_PLACEHOLDER
KECCAK_EMB_CELLS = KECCAK_EMB_CELLS_PLACEHOLDER
KECCAK_IOTA_START = KECCAK_IOTA_START_PLACEHOLDER
KECCAK_IOTA_IDX = KECCAK_IOTA_IDX_PLACEHOLDER
KECCAK_PI = KECCAK_PI_PLACEHOLDER
KECCAK_RHO = KECCAK_RHO_PLACEHOLDER
KECCAK_SHIFT_USED = KECCAK_SHIFT_USED_PLACEHOLDER
KECCAK_LANES = 25
KECCAK_Z_BITS = 6      # a bit position is z + 64 * lane
KECCAK_LANE_BITS = 5
KECCAK_LOCAL_BITS = KECCAK_Z_BITS + KECCAK_LANE_BITS
LANE_OFF = 2 ** KECCAK_LANE_BITS - 2  # where a frame eqtree's last level starts
KECCAK_IOTA_BITS = 7   # iota flips slices 2^i - 1 of lane 0 only
QKECCAK_SLOT_LOG = QKECCAK_SLOT_LOG_PLACEHOLDER
# A claim's record: its value, the sum of its instance weights, pointers to its
# point, its lane table, the local point whose slice coordinates' eq is its slice
# table, and its weight on each position iota can flip (slice 2^i - 1 of lane 0),
# then the instance weights.
KC_VALUE = 0
KC_KAPPA = 1
KC_POINT = 2
KC_LANES = 3
KC_LOCAL = 4
KC_FLIPS = 5
KC_MU = 6
KC_SIZE = KC_MU + KECCAK_PACK
# One round of a layer's sumcheck over packs and segments.
KR_FS = 0
KR_CURSOR = 5
KR_CLAIM = 6
KR_SCALE = 7
KR_SLOTS = 8
# A layer's round records lie field by field, KR_CAP apart, one per KR_STEP rounds
# and one per round of the remainder: a layer has tau - 3 < 32 rounds, so at most
# 3 + 7 of them.
KR_STEP_LOG = 3
KR_STEP = 2 ** KR_STEP_LOG
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
N_COL_GROUPS = N_COL_GROUPS_PLACEHOLDER
COL_GROUP_START = COL_GROUP_START_PLACEHOLDER  # a column group's first column, then N_COMMITTED_COLS
PCS_MIN_MU = PCS_MIN_MU_PLACEHOLDER
# Global maxima; StackBuf frame sizes are parse-time, so they must be baked.
LIG_MAX_LEVELS = LIG_MAX_LEVELS_PLACEHOLDER
LIG_MAX_VANISH_LEN = LIG_MAX_VANISH_LEN_PLACEHOLDER
LIG_LOG_MSG_COLS_CAP = LIG_LOG_MSG_COLS_CAP_PLACEHOLDER
YR_LOG_CAP = YR_LOG_CAP_PLACEHOLDER
# The opening's grinding (pcs::whir_config): before each round's theta and again before its
# (gamma, alpha, beta), before every level's queries, before each batching challenge, the
# ring switch's map included, and before the level-0 OOD sample. A non-final level draws
# OOD_SAMPLES points with no grind.
FOLD_GRIND_BITS = FOLD_GRIND_BITS_PLACEHOLDER
OOD_GRIND_BITS = OOD_GRIND_BITS_PLACEHOLDER
QUERY_GRIND_BITS = QUERY_GRIND_BITS_PLACEHOLDER
BATCH_GRIND_BITS = BATCH_GRIND_BITS_PLACEHOLDER
OOD_SAMPLES = OOD_SAMPLES_PLACEHOLDER
# Every other challenge grinds for its numerator (fiat_shamir::grinding_bits), zero
# bits being no nonce at all: the bus fingerprint by the push depth mu, BUS_GRIND_BITS[mu],
# never zero at an admitted depth; a sumcheck round for its degree d, eq factor
# included, as ROUNDd (the opening's tail and a Keccak opening's are degree 2, the
# table sumcheck's and a Keccak layer's degree 3, a bus GKR round degree 5); the GKR's
# combiner, its y (a binary layer's, a radix-four one's, the last layer's, read by the
# zerocheck too); the table sumcheck's xi; and the Keccak reduction's first message
# (its segment and lane), its s and its beta.
BUS_GRIND_BITS = BUS_GRIND_BITS_PLACEHOLDER
BUS_GRIND_ARMS = SIZE_BITS - MIN_LOG_MEM  # the bus depths from MIN_LOG_MEM, below SIZE_BITS
ROUND2_GRIND_BITS = ROUND2_GRIND_BITS_PLACEHOLDER
ROUND3_GRIND_BITS = ROUND3_GRIND_BITS_PLACEHOLDER
ROUND5_GRIND_BITS = ROUND5_GRIND_BITS_PLACEHOLDER
GKR_COMBINER_GRIND_BITS = GKR_COMBINER_GRIND_BITS_PLACEHOLDER
GKR_Y1_GRIND_BITS = GKR_Y1_GRIND_BITS_PLACEHOLDER
GKR_Y_GRIND_BITS = GKR_Y_GRIND_BITS_PLACEHOLDER
GKR_Y_LAST_GRIND_BITS = GKR_Y_LAST_GRIND_BITS_PLACEHOLDER
XI_GRIND_BITS = XI_GRIND_BITS_PLACEHOLDER
KECCAK_SEG_GRIND_BITS = KECCAK_SEG_GRIND_BITS_PLACEHOLDER
KECCAK_S_GRIND_BITS = KECCAK_S_GRIND_BITS_PLACEHOLDER
KECCAK_BETA_GRIND_BITS = KECCAK_BETA_GRIND_BITS_PLACEHOLDER
BATCH_LAM_GRIND_BITS = BATCH_LAM_GRIND_BITS_PLACEHOLDER
BC_LAM_WORDS = BC_LAM_WORDS_PLACEHOLDER  # the batching challenge's nonce, if it grinds
BC_ROUND_WORDS = BC_ROUND_WORDS_PLACEHOLDER  # a batching round's (g1, g_inf), then its nonce, if it grinds
# A level's high part has at most 2^HIGH_BITS_CAP coefficients, one per fold.
HIGH_BITS_CAP = 3
MAX_STACK_LOG = LIG_MIN_LOG_SIZE + LIG_N_LOG_SIZES - 1
SEL_NIBBLES = (MAX_STACK_LOG + 3) // 4  # four selector bits share one table lookup
SEL_EQ_STRIDE = 64                      # a nibble's eq tables over its top 1..4 coords, strided
EQ_CHAIN_ARMS = SIZE_BITS + QKECCAK_SLOT_LOG + 1  # eq prefix chain lengths
SEL_TAB_NIBBLES = (SIZE_BITS + 3) // 4  # nibbles of a bus selector run
SEL_TAB_EQ_STRIDE = 32                  # a nibble's eq tables over its low 1..4 coords, padded
RANK_KEYS_AT = SIZE_BITS + 16 * SEL_TAB_NIBBLES  # where exponent_tables keeps the rank keys
RANK_STRIDE = N_BLOCKS + N_COMMITTED_COLS  # above any block or column index
RANK_KEY_BOUND = SIZE_BITS * RANK_STRIDE   # above any step between two rank keys
SIDE_TAB_AT = RANK_KEYS_AT + SIZE_BITS
WIN_TAB_AT = SIDE_TAB_AT + N_BLOCK_GROUPS  # a bit window's pattern by its g-power: [g^n] = n
WIN_TAB_BITS = 11
WIN_TAB_LEN = 2 ** WIN_TAB_BITS
LIG_N_LEVELS = LIG_N_LEVELS_PLACEHOLDER
LIG_YR_LEVEL = LIG_YR_LEVEL_PLACEHOLDER
LIG_YR_LOG_LEN = LIG_YR_LOG_LEN_PLACEHOLDER
LIG_YR_LEN = LIG_YR_LEN_PLACEHOLDER
LIG_TOTAL_FOLDS = LIG_TOTAL_FOLDS_PLACEHOLDER
LIG_MAX_SQUEEZES = LIG_MAX_SQUEEZES_PLACEHOLDER
LIG_MAX_INTERLEAVE = LIG_MAX_INTERLEAVE_PLACEHOLDER
LIG_POSITIONS_LEN = LIG_POSITIONS_LEN_PLACEHOLDER
LIG_CAP_DEPTH = LIG_CAP_DEPTH_PLACEHOLDER
LIG_CAP_OFF = LIG_CAP_OFF_PLACEHOLDER
LIG_CAP_LEN = LIG_CAP_LEN_PLACEHOLDER
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
LIG_HIGH_BITS = LIG_HIGH_BITS_PLACEHOLDER  # the bits of a level's high-part index, j < folds
LIG_FOLDS_OFF = LIG_FOLDS_OFF_PLACEHOLDER
LIG_VANISH_OFF = LIG_VANISH_OFF_PLACEHOLDER
LIG_VANISH_VALS = LIG_VANISH_VALS_PLACEHOLDER
LIG_VANISH_INVS = LIG_VANISH_INVS_PLACEHOLDER
LIG_N_CANDIDATES = LIG_N_CANDIDATES_PLACEHOLDER
LIG_MIN_SHIFT_INV = LIG_MIN_SHIFT_INV_PLACEHOLDER
# eval_b claim descriptors. CLAIM_POINT_BUF says which point buffer a pooled
# claim's x-part lives in, CLAIM_COMMITTED_COL maps it to the compact index of the
# committed column it must open (a virtual KECCAK value claim maps to QKECCAK),
# CLAIM_QKECCAK_SLOT_BITS holds the bits of the q_keccak slot a virtual claim reads
# (zero for a non-virtual one), and QKECCAK_COMMITTED_COL is the ring-switch target.
# A KECCAK output lane's claim is POINT_BUF_KECCAK_OUT: never opened, the 25 of them,
# from KECCAK_OUT_POOL on, are the Keccak reduction's claim on the output.
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QKECCAK_RHO = 3
POINT_BUF_KECCAK_OUT = 4
KECCAK_OUT_POOL = KECCAK_OUT_POOL_PLACEHOLDER
CLAIM_POINT_BUF = CLAIM_POINT_BUF_PLACEHOLDER
CLAIM_COMMITTED_COL = CLAIM_COMMITTED_COL_PLACEHOLDER
CLAIM_KAPPA_SRC = CLAIM_KAPPA_SRC_PLACEHOLDER  # a claim's low dimension, as a kappa source
CLAIM_KAPPA_ADJ = CLAIM_KAPPA_ADJ_PLACEHOLDER
CLAIM_QKECCAK_SLOT_BITS = CLAIM_QKECCAK_SLOT_BITS_PLACEHOLDER
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
# The statement digest's preimage: the STMT_HEADER header cells (the seed, then the
# leanXMSS and leanSPHINCS claim-list digests and the DA one), then the deferred
# cells. No domain tag: every field has a fixed width, and the seed leads, binding
# this bytecode and the proof system's version.
STMT_HEADER = STMT_HEADER_PLACEHOLDER
STMT_DEFER_OFF = STMT_HEADER
STMT_CELLS = STMT_DEFER_OFF + DEFER_STMT_CELLS

# ------------------------------------------------------------------ the hash
# Every hash is Keccak-256 (primitives::hash::hash): a block is 136 bytes, eight and a
# half cells, XORed into the previous KECCAK_STATE-cell sponge state before a KECCAK,
# and the last output's first two cells are the digest. A hash of runtime length
# carries that state through a heap run between loop frames, KECCAK_STATE cells a
# step (`claim_list_digest`).
KECCAK_STATE = KECCAK_STATE_PLACEHOLDER
# Claims a declared claim list absorbs a loop frame: 68 cells, four block pairs. The
# list's bulk goes CLAIM_BIG claims a frame, BIG_GROUPS of those groups, so that the
# sponge state's trip through the heap is paid once per CLAIM_BIG claims; the rest
# CLAIM_GROUP a frame, then a `match` on the last group's count.
CLAIM_GROUP = CLAIM_GROUP_PLACEHOLDER
BIG_GROUPS = BIG_GROUPS_PLACEHOLDER
CLAIM_BIG = CLAIM_GROUP * BIG_GROUPS
# A child list's walk record: the sponge state, then a coverage slot and a table entry.
MONO_REC = KECCAK_STATE + 2

# --------------------------------------------------------- WOTS+C (host-supplied)
# Both schemes' one-time keys: chains of CHAIN_LENGTH positions, whose digits are
# dispatched a group at a time (leanSPHINCS DIGIT_GROUP and the last chain alone,
# leanXMSS LX_DIGIT_GROUP and the rest), and the leanXMSS address, a cell whose low
# lane is lo:32 | hi:24 | type:5 | step:3; TW_* hold the type. Every 16-byte native
# value is one cell.
W = W_PLACEHOLDER
CHAIN_LENGTH = 2 ** W
CHAIN_STEPS = CHAIN_LENGTH - 1
DIGIT_GROUP = DIGIT_GROUP_PLACEHOLDER
DIGIT_GROUPS = CHAIN_LENGTH ** DIGIT_GROUP
# The digit sum of group k, at k.
DIGIT_SUMS = DIGIT_SUMS_PLACEHOLDER

# ----------------------------------------------------- leanXMSS (host-supplied)
# Two layers of trees of height LX_HEIGHT over keys of LX_V chains. A layer's digest
# is a codeword when its first LX_V digits sum to LX_TARGET_SUM and the rest are
# zero. An address is a cell whose low lane is lo:32 | hi:24 | type:5 | step:3, TW_*
# holding the type; LX_TOP is the top layer's flag where an address holds it.
TW_CHAIN = TW_CHAIN_PLACEHOLDER
TW_LEAF = TW_LEAF_PLACEHOLDER
TW_NODE = TW_NODE_PLACEHOLDER
TW_MSG = TW_MSG_PLACEHOLDER
HI_MUL = 2 ** 32
STEP_MUL = 2 ** 61
LX_V = LX_V_PLACEHOLDER
LX_TARGET_SUM = LX_TARGET_SUM_PLACEHOLDER
LX_HEIGHT = LX_HEIGHT_PLACEHOLDER
LX_TOP = LX_TOP_PLACEHOLDER
# The path is dispatched LX_WINDOW index bits at a time (`lx_window`), LX_LAYER_WINDOWS a layer.
LX_WINDOW = LX_WINDOW_PLACEHOLDER
LX_LAYER_WINDOWS = LX_HEIGHT // LX_WINDOW
LX_WINDOWS = 2 * LX_LAYER_WINDOWS
LX_WINDOW_ARMS = 2 ** LX_WINDOW
# A layer's codeword digits are dispatched LX_DIGIT_GROUP at a time, then the LX_DIGIT_TAIL left.
LX_DIGIT_GROUP = LX_DIGIT_GROUP_PLACEHOLDER
LX_DIGIT_GROUPS = CHAIN_LENGTH ** LX_DIGIT_GROUP
LX_DIGIT_TAIL = LX_V % LX_DIGIT_GROUP
LX_TAIL_GROUPS = CHAIN_LENGTH ** LX_DIGIT_TAIL
LX_DIGIT_DISPATCHES = LX_V // LX_DIGIT_GROUP + 1
LX_GROUP_SIZES = LX_GROUP_SIZES_PLACEHOLDER
# Where a chain index lives (`walk`): the zero cell for 0, powers[LX_TAG_LOG[i]] for a power
# of two (slot 0), else LX_TAG_SLOT[i] - 1 of the LX_N_TAGS carried tags.
LX_TAG_SLOT = LX_TAG_SLOT_PLACEHOLDER
LX_TAG_LOG = LX_TAG_LOG_PLACEHOLDER
LX_N_TAGS = LX_N_TAGS_PLACEHOLDER

# -------------------------------------------------- leanSPHINCS (host-supplied)
# The scheme's own letters, prefixed SP_: under each bottom leaf a FORS instance of
# SP_FORS_TREES trees of height SP_FORS_HEIGHT, and above them three layers of trees
# over WOTS+C keys of SP_V chains, of heights SP_HEIGHT_0, SP_HEIGHT_1 and SP_HEIGHT_2
# from the bottom. An addressed hash is PK.seed, FIPS 205's 32-byte address (two
# cells), then the payload.
SP_V = SP_V_PLACEHOLDER
SP_TARGET_SUM = SP_TARGET_SUM_PLACEHOLDER
SP_HEIGHT_0 = SP_HEIGHT_0_PLACEHOLDER
SP_HEIGHT_1 = SP_HEIGHT_1_PLACEHOLDER
SP_HEIGHT_2 = SP_HEIGHT_2_PLACEHOLDER
SP_H = SP_HEIGHT_0 + SP_HEIGHT_1 + SP_HEIGHT_2
SP_FORS_TREES = SP_FORS_TREES_PLACEHOLDER
SP_FORS_HEIGHT = SP_FORS_HEIGHT_PLACEHOLDER
# The message digest is H_msg's two calls: the first call's two cells, then the low
# two bytes of the second call's first cell. Its first SP_MD_BYTES bytes are the
# FORS leaves, SP_FORS_HEIGHT bits each, most significant first; then the tree index,
# three bytes big endian of which the low SP_H - SP_HEIGHT_0 bits count, the high byte
# holding the 2 bits the others leave; then the bottom leaf, one byte.
SP_CELL_BITS = 2 * BASE_FIELD_BITS
SP_MD_BYTES = SP_FORS_TREES * SP_FORS_HEIGHT // 8
SP_DIGEST_BYTES = SP_DIGEST_BYTES_PLACEHOLDER
# The digest's bytes in the second call's first cell: the middle leaf, then the bottom
# leaf, one byte each.
SP_TAIL_BYTES = SP_DIGEST_BYTES - 32
# The layers' leaves one after the other, bottom first: the middle leaf's first bit,
# the top leaf's, and the top leaf's bits in the tree index's high byte, whose other
# bits are unused.
SP_MID = SP_HEIGHT_0
SP_TOP = SP_HEIGHT_0 + SP_HEIGHT_1
SP_TOP_HIGH_BITS = SP_HEIGHT_2 - 8
SP_PAD_BITS = 8 - SP_TOP_HIGH_BITS
# The cell bits of the first call's second cell where the tree index's high byte
# (digest byte SP_MD_BYTES) and middle byte (the next) start.
SP_TREE_HI_BIT = 8 * (SP_MD_BYTES - 16)
SP_TREE_MID_BIT = SP_TREE_HI_BIT + 8
# A codeword's digits in each byte of its encoding digest, base_2b.
SP_DIGITS_PER_BYTE = 8 // W
# Each H_msg call's input: R, PK.seed, PK.root and the 32-byte M, five cells, then
# the counter BE_32(i), a cell of its own whose byte 3 is i.
SP_HMSG_LEN = 5 * 16 + 4
SP_COUNTER_ONE = 2 ** 24
# FIPS 205's address is two cells, A0 the layer and the tree words and A1 the type
# and the three words after it, each word big endian, so a value's low byte is its
# word's last. The cell bit each such byte starts at:
SP_LAYER_MUL = SP_LAYER_MUL_PLACEHOLDER  # A0's byte 3: the layer
SP_TREE_MUL_0 = SP_TREE_MUL_0_PLACEHOLDER  # A0's bytes 15, 14 and 13: the tree's three low bytes
SP_TREE_MUL_1 = SP_TREE_MUL_1_PLACEHOLDER
SP_TREE_MUL_2 = SP_TREE_MUL_2_PLACEHOLDER
SP_KEY_MUL_0 = SP_KEY_MUL_0_PLACEHOLDER  # A1's bytes 23 and 22: the key pair's two low bytes
SP_KEY_MUL_1 = SP_KEY_MUL_1_PLACEHOLDER
SP_WORD2_MUL = SP_WORD2_MUL_PLACEHOLDER  # A1's byte 27: a chain index or a tree height
SP_WORD3_MUL_0 = SP_WORD3_MUL_0_PLACEHOLDER  # A1's bytes 31 and 30: a hash address or a tree index
SP_WORD3_MUL_1 = SP_WORD3_MUL_1_PLACEHOLDER
# The address types as A1 holds them; WOTS_HASH is zero.
SP_WOTS_PK = SP_WOTS_PK_PLACEHOLDER
SP_TREE = SP_TREE_PLACEHOLDER
SP_FORS_TREE = SP_FORS_TREE_PLACEHOLDER
SP_FORS_ROOTS = SP_FORS_ROOTS_PLACEHOLDER
SP_WOTS_ENC = SP_WOTS_ENC_PLACEHOLDER
# Values bounded a byte at a time: each byte hinted in the exponent, range checked,
# and read as the bits it spells off a table of the SP_BYTE_VALUES bytes.
SP_BYTE_VALUES = 256
# The encoding counter, BE_32 in the low four bytes of its cell: bounded by
# rebuilding it from exactly that many bytes, so the guest accepts no preimage the
# native verifier cannot parse.
SP_COUNTER_BYTES = 4
# An encoding's input: PK.seed, the address, the value it signs, then the counter.
SP_ENCODING_BYTES = 16 * 4 + SP_COUNTER_BYTES
# The second call's low lane past the digest: bytes, likewise.
SP_UNUSED_BYTES = 8 - SP_TAIL_BYTES

# --------------------------------------------------------------- node capacities
# MAX_KEYS caps the coverage table's slots, both schemes' declared claims and their
# duplicates, which is what the coverage range check needs below 2^MIN_LOG_MEM;
# MAX_RECURSIONS is the arity of an aggregation tree.
MAX_KEYS = MAX_KEYS_PLACEHOLDER
MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER


# ---------------------------------- LeanDA ------------------------------------------
# Blob and cell widths are fixed. The row count is hinted and bounded by DA_MAX_ROWS;
# the tree over the blob roots dispatches on the checked log of its padded value.
DA_LOG_K = DA_LOG_K_PLACEHOLDER
DA_LOG_CELL = DA_LOG_CELL_PLACEHOLDER
DA_MAX_ROWS = DA_MAX_ROWS_PLACEHOLDER
DA_LOG_MAX_ROWS = DA_LOG_MAX_ROWS_PLACEHOLDER
DA_PAD_BLOB_0 = DA_PAD_BLOB_0_PLACEHOLDER
DA_PAD_BLOB_1 = DA_PAD_BLOB_1_PLACEHOLDER
# Vhat_j at the points the membership vector's product tree needs (da_factors): each
# parent node of the tree over a cell index, then of the tree inside a cell, at the bit
# j it splits; and Vhat_j(beta_(DA_LOG_CELL + b)) at DA_LOG_CELL * b + j, for each factor
# j inside a cell and bit b of the cell index.
DA_VHAT = DA_VHAT_PLACEHOLDER
DA_VHAT_COLUMN = DA_VHAT_COLUMN_PLACEHOLDER

DA_LOG_M = DA_LOG_K + 1                         # log of the symbols per encoded row
DA_CELL = 2 ** DA_LOG_CELL                      # symbols in a cell
DA_BLOCK_BITS = DA_LOG_M - DA_LOG_CELL          # log of the cells per row
DA_CELLS = 2 ** DA_BLOCK_BITS                   # cells per row
DA_PACKED = DA_CELL // 2                        # packed 128-bit cells in one cell
DA_TREE_ARMS = DA_LOG_MAX_ROWS + 1              # tree depths the row count can dispatch to
DA_SUM = 4 * DA_CELLS                           # where a blob's running sum starts, past its tree
DA_REGION = DA_SUM + DA_CELLS + 1               # cells of one blob's tree and running sum

# =================================== field packing ==================================
# A word is a cell, so a value a KECCAK hashes or a transcript absorbs needs no check
# of its own. Exposing a word's two K limbs is the one thing that does: the tower
# representation is unique, so proving that the exposed lanes are in K and weight
# back to the word is the whole check, no equality to make, one less hint to distrust.


@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + Y_TOWER * b


@inline
def split_limbs(word):
    # Hint the low limb and derive the quotient by Y. Requiring both in K proves
    # `word = lo + Y*hi`, which binds them.
    lo = StackBuf(1)
    hint_f128_limbs(lo, word)
    hi = (word + lo[0]) * Y_INV
    assert_in_k(lo[0], hi)
    return lo[0], hi


@inline
def challenge_from_state(state):
    # A challenge is the sponge's first two lanes, its first cell.
    return state[0]


# ==================================== Fiat-Shamir ===================================
# A duplex sponge over Keccak-f in overwrite mode (fiat_shamir::FiatShamirState). The
# sponge is the 13-cell output `sp` of its last permutation, whose last FS_CELLS cells, the
# capacity, are all the next permutation keeps: between functions and loop frames those
# cells are all that travels, `fs0 .. fs4`. Scalars absorbed since wait in an eight-cell
# `rate` run, two cells a scalar, at most four. How many wait is a compile-time count at
# every call site, `k`. A fifth scalar, or a challenge, permutes; every challenge is a
# permutation of its own.


@inline
def fs_pack(rate, k: Const, x, tag: Const):
    # Scalar x as lanes (c0, c1, 0, tag) over rate cells 2k and 2k + 1: x itself, then a constant.
    rate[2 * k] = x
    rate[2 * k + 1] = Y_TOWER * tag
    return


@inline
def fs_perm(sp, rate, k: Const):
    # The permutation taking the k waiting scalars: they overwrite the rate, zero past them.
    nxt = StackBuf(KECCAK_STATE)
    if k == 0:
        keccak([0, 0], [0, 0], nxt, cap=sp)
    if k == 1:
        keccak(rate[0:2], [0, 0], nxt, cap=sp)
    if k == 2:
        keccak(rate[0:2], rate[2:4], nxt, cap=sp)
    if k == 3:
        rate[6] = 0
        rate[7] = 0
        keccak(rate[0:2], rate[2:4], nxt, tail=rate[4:8], cap=sp)
    if k == 4:
        keccak(rate[0:2], rate[2:4], nxt, tail=rate[4:8], cap=sp)
    return nxt


@inline
def fs_perm4(sp, r0, r1, r2, r3):
    # The permutation whose rate is r0..r3 then zero: up to two waiting scalars, held as
    # cells rather than in a rate run.
    nxt = StackBuf(KECCAK_STATE)
    keccak([r0, r1], [r2, r3], nxt, cap=sp)
    return nxt


@inline
def fs_absorb_nonce(sp, rate, k: Const, nonce):
    # A grinding nonce as waiting scalar k (k < 4), with its own tag, then the
    # permutation that draws the next challenge, its first cell, and carries the
    # proof of work, the first lane of its second cell (`grind_check`).
    fs_pack(rate, k, nonce, DS_POW_NONCE)
    nxt = fs_perm(sp, rate, k + 1)
    return nxt


@inline
def fs_grind_squeeze(sp, rate, k: Const, cursor, tabs, bits: Const):
    # A challenge after a grind of `bits`, k scalars waiting (k <= 4): the nonce under
    # `cursor` joins them, a fifth permuting the four first, and its permutation draws
    # the challenge. A grind of zero bits is no nonce, a plain squeeze. Returns the new
    # sponge, the challenge and the cursor.
    if const(bits == 0):
        nxt = fs_perm(sp, rate, k)
        cur = cursor
    elif const(k == 4):
        full = fs_perm(sp, rate, 4)
        nonce_rate = StackBuf(8)
        nxt = fs_absorb_nonce(full, nonce_rate, 0, cursor[GEN ** 0])
        grind_check(nxt[1], tabs, bits)
        cur = cursor * GEN
    else:
        nxt = fs_absorb_nonce(sp, rate, k, cursor[GEN ** 0])
        grind_check(nxt[1], tabs, bits)
        cur = cursor * GEN
    return nxt, nxt[0], cur


@inline
def fs_perm_pending(cap, rec, at: Const):
    # The permutation taking a full rate held in the record cells at..at+8.
    nxt = StackBuf(KECCAK_STATE)
    keccak([rec[GEN ** at], rec[GEN ** (at + 1)]], [rec[GEN ** (at + 2)], rec[GEN ** (at + 3)]], nxt, tail=[rec[GEN ** (at + 4)], rec[GEN ** (at + 5)], rec[GEN ** (at + 6)], rec[GEN ** (at + 7)]], cap=cap)
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
        rec[GEN ** ((field + j) * stride)] = sp[KECCAK_STATE - FS_CELLS + j]
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
    # A challenge: the permutation taking the k waiting scalars, read off its first two
    # lanes. Returns the new sponge and the challenge.
    nxt = fs_perm(sp, rate, k)
    challenge = challenge_from_state(nxt)
    return nxt, challenge


# ============================ bits, logs, and the exponent ==========================


def exponent_tables():
    # A read-only lookup table over the exponent domain, indexed at runtime g-powers
    # (so it must be heap, not stack): g_squares[g^j] = g^(2^j) turns integer sums of
    # powers of two into field products. It spans SIZE_BITS because
    # `log2_ceil_in_the_exponent` bounds its result there and indexes it at g^L.
    # Past them, the opening selector's nibble shares: g^(u 2^(4j)) at SIZE_BITS + 16j + u.
    g_squares = HeapBuf(WIN_TAB_AT + WIN_TAB_LEN)
    sq_run = GEN
    for j in unroll(0, SIZE_BITS):
        g_squares[GEN ** j] = sq_run
        sq_run *= sq_run
    # Then the rank keys g^(kappa RANK_STRIDE) of the placement orders.
    for k in unroll(0, SIZE_BITS):
        g_squares[GEN ** (RANK_KEYS_AT + k)] = GEN ** (k * RANK_STRIDE)
    # Then each bus block group's side.
    for s in unroll(0, N_GKR_SIDES):
        for gi in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            g_squares[GEN ** (SIDE_TAB_AT + gi)] = s
    base = GEN
    for j in unroll(0, SEL_TAB_NIBBLES):
        share = GEN ** 0
        for u in unroll(0, 16):
            g_squares[GEN ** (SIZE_BITS + 16 * j + u)] = share
            share *= base
        base = share
    # Last, a bit window's pattern by its g-power, for `query_window`.
    for n in unroll(0, WIN_TAB_LEN):
        g_squares[GEN ** (WIN_TAB_AT + n)] = const(n)
    return g_squares


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


def assert_small_g_power(x, g_squares):
    # x = g^e with e < 2^(4 SEL_TAB_NIBBLES): hinted g-power digits, each range-checked
    # below 16, whose weighted product is x. A g-power past that, a "negative"
    # difference of two small exponents above all, has no such digits.
    digits = StackBuf(SEL_TAB_NIBBLES)
    hint_decompose_digits_exponent(digits, x, 4 * SEL_TAB_NIBBLES, SEL_TAB_NIBBLES, 4, 0)
    shares = g_squares * GEN ** SIZE_BITS
    for j in unroll(0, SEL_TAB_NIBBLES):
        d = digits[j]
        assert log(d) < 16
        if const(j == 0):
            rebuilt = shares[d]
        else:
            rebuilt *= shares[GEN ** (16 * j) * d]
    assert rebuilt == x
    return


def log2_ceil_in_the_exponent(g_N, g_squares, floor: Const, nbits: Const):
    # g^L, L = max(log2_ceil(N), floor), given g_N = g^N. L is advice, pinned by
    # 2^L - N >= 0 and, above the floor, N - 2^(L-1) - 1 >= 0, each a g-power with a
    # small exponent (a negative one wraps around the order of g). The first bounds
    # N below 2^nbits, as L < SIZE_BITS = nbits. N must be known nonnegative: at the
    # floor only 2^floor - N is checked, which a small negative N passes too. Both
    # callers build g_N as a product of certified powers g^(2^kappa).
    bits = HeapBuf(GEN ** nbits)
    hint_decompose_bits_exponent(bits, g_N, nbits)
    g_log = hint_log2_ceil(bits, nbits, floor)
    assert log(g_log) < SIZE_BITS
    assert log(g_log / GEN ** floor) < SIZE_BITS
    assert_small_g_power(g_squares[g_log] / g_N, g_squares)
    if g_log != GEN ** floor:
        assert_small_g_power(g_N * INV_GEN / g_squares[g_log * INV_GEN], g_squares)
    return g_log


@inline
def assert_window(w, width: Const):
    # log(w) < 2^width, the bound spelled out per width (a range check takes a literal bound).
    if const(width == 1):
        assert log(w) < 2
    elif const(width == 2):
        assert log(w) < 4
    elif const(width == 3):
        assert log(w) < 8
    elif const(width == 4):
        assert log(w) < 16
    elif const(width == 5):
        assert log(w) < 32
    elif const(width == 6):
        assert log(w) < 64
    elif const(width == 7):
        assert log(w) < 128
    elif const(width == 8):
        assert log(w) < 256
    elif const(width == 9):
        assert log(w) < 512
    elif const(width == 10):
        assert log(w) < 1024
    elif const(width == 11):
        assert log(w) < 2048
    else:
        assert 0 == 1  # no window is wider than the window table covers
    return


@inline
def query_window(word, wins, tabs, at: Const, start: Const, width: Const):
    # Bits start..start+width of `word` into wins[at] as g^n, n the integer they spell, range checked below
    # 2^width. Returns n's bit pattern, `tabs[g^n]` (`query_tables`).
    hint_windows_exponent(wins, word, start, width, 1, at)
    w = wins[at]
    assert_window(w, width)
    return tabs[w]


@inline
def query_window_split(word, wins, tabs, parts, at: Const, start: Const, width: Const, cut: Const):
    # A window whose bits cross a limb boundary `cut` bits in: its two runs hinted and range checked apart,
    # each read as its bit pattern into parts[0], parts[1], and joined in the exponent into wins[at].
    hint_windows_exponent(parts, word, start, cut, 1, 2)
    hint_windows_exponent(parts, word, start + cut, width - cut, 1, 3)
    lo = parts[2]
    hi = parts[3]
    assert_window(lo, cut)
    assert_window(hi, width - cut)
    hp = hi
    for s in unroll(0, cut):
        hp = hp * hp
    wins[at] = lo * hp
    parts[0] = tabs[lo]
    parts[1] = tabs[hi]
    return


def decode_query_windows(squeezed_word, positions_out, win_ptrs_out, tabs, depth: Const, cap_depth: Const):
    # The squeezed word's bits are advice HERE, in windows: a window of w bits is hinted as g^n, n the integer
    # they spell, range checked below 2^w and read back as n's bit pattern. Each depth-bit group is a query
    # position (little-endian), whose windows are its path bits QW at a time from the bottom, then the cap
    # child bit, then the cap parent index: `opening_query` dispatches on them, and query j's run of windows
    # is at win_ptrs_out[g^j]. The bits above the last position are windows too, and the windows' patterns,
    # shifted to their places, must rebuild the word. A position whose bits cross a 64-bit limb splits there,
    # the polynomial basis shifting a run as a whole only inside one limb.
    per_word = FIELD_BITS // depth
    path = depth - cap_depth
    n_pw = (path + QW - 1) // QW
    n_win = n_pw + 2
    wins = StackBuf(QUERY_WINDOWS_CAP)
    wins_ptr = addr(wins)
    reconstructed = 0
    for j in unroll(0, per_word):
        base = j * depth
        at0 = j * n_win
        # bits of this position below the next limb; at least `depth` when it does not cross one
        cut = 64 - base % 64
        p_lo = 0
        p_hi = 0
        for i in unroll(0, n_win):
            # window i: QW path bits, the last path window's remainder, the cap child bit, the cap index
            if const(i + 2 == n_win):
                off = path
                width = 1
            elif const(i + 1 == n_win):
                off = path + 1
                width = cap_depth - 1
            elif const(i + 3 == n_win):
                off = QW * i
                width = path - QW * i
            else:
                off = QW * i
                width = QW
            if const((off + width) // (cut + 1) == 0):
                p_lo += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off]
            elif const(off // cut == 0):
                parts = StackBuf(4)
                query_window_split(squeezed_word, wins, tabs, parts, at0 + i, base + off, width, cut - off)
                p_lo += parts[0] * COORD_BASIS[off]
                p_hi += parts[1]
            else:
                p_hi += query_window(squeezed_word, wins, tabs, at0 + i, base + off, width) * COORD_BASIS[off - cut]
        if const(cut // depth == 0):
            positions_out[GEN ** j] = p_lo + COORD_BASIS[cut] * p_hi
            reconstructed += COORD_BASIS[base] * p_lo + COORD_BASIS[base + cut] * p_hi
        else:
            positions_out[GEN ** j] = p_lo
            reconstructed += COORD_BASIS[base] * p_lo
        win_ptrs_out[GEN ** j] = wins_ptr * GEN ** at0
    rest = StackBuf(4)
    for i in unroll(0, (FIELD_BITS - per_word * depth + 6) // 7):
        start = per_word * depth + 7 * i
        if const((start + 7) // (FIELD_BITS + 1) == 0):
            width = 7
        else:
            width = FIELD_BITS - start
        reconstructed += query_window(squeezed_word, rest, tabs, i, start, width) * COORD_BASIS[start]
    assert reconstructed == squeezed_word
    return


def grind_check(word, tabs, nbits: Const):
    # The permutation that absorbs a grinding nonce must leave its third lane, the first
    # of `word`, its second cell, with the low nbits zero (transcript::grind_check,
    # 0 < nbits < 64). That lane is rebuilt from windows of its bits at and above nbits
    # only, which IS the claim, and the word less it must be Y times a K element, which
    # pins the rebuilt lane as its first. The windows are WIN_TAB_BITS wide but the top
    # one, each range checked and read as its bit pattern, then joined by Horner in x,
    # which is GEN: no shift leaves the limb. The honest prover searches the u64 nonces
    # while verification permits the full field: each candidate still costs one
    # permutation and passes with probability 2^-nbits.
    n_win = (BASE_FIELD_BITS - nbits + WIN_TAB_BITS - 1) // WIN_TAB_BITS
    top = BASE_FIELD_BITS - nbits - WIN_TAB_BITS * (n_win - 1)
    wins = StackBuf(BASE_FIELD_BITS // WIN_TAB_BITS + 1)
    hint_windows_exponent(wins, word, nbits, WIN_TAB_BITS, n_win - 1, 0)
    hint_windows_exponent(wins, word, nbits + WIN_TAB_BITS * (n_win - 1), top, 1, n_win - 1)
    w = wins[n_win - 1]
    assert_window(w, top)
    lane = tabs[w]
    for i in unroll(1, n_win):
        w = wins[n_win - 1 - i]
        assert_window(w, WIN_TAB_BITS)
        lane = lane * GEN ** WIN_TAB_BITS + tabs[w]
    lane = lane * GEN ** nbits
    high = (word + lane) * Y_INV
    assert_in_k(high, lane)
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


def rs_eq_rows(row, zs, ps, n: Const):
    # Coordinates 0..n of zs/ps multiply rows 0..64 of `row` into the next row, row k
    # by prod_i (zs_i^(2^k) + ps_i), the Frobenius powers walked inside.
    nxt = row * GEN ** BASE_FIELD_BITS
    if const(n == 0):
        nxt = row
    else:
        zv = StackBuf(RS_CHUNK * BASE_FIELD_BITS)  # zv[64 i + k] = zs_i^(2^k)
        a = StackBuf(RS_CHUNK)
        for i in unroll(0, n):
            zv[BASE_FIELD_BITS * i] = zs[GEN ** i]
            a[i] = ps[GEN ** i]
        for k in unroll(0, BASE_FIELD_BITS):
            acc = row[GEN ** k]
            for i in unroll(0, n):
                acc *= zv[BASE_FIELD_BITS * i + k] + a[i]
                if const(k != BASE_FIELD_BITS - 1):
                    zv[BASE_FIELD_BITS * i + k + 1] = zv[BASE_FIELD_BITS * i + k] * zv[BASE_FIELD_BITS * i + k]
            nxt[GEN ** k] = acc
    return nxt


def rs_eq_run(chain, z_vals, point1, count_g):
    # One run of the telescoped ring-switch product E = sum_k c_k * prod_j
    # (z_j^(2^k) + 1 + ris_j): coordinate x multiplies row k by (z^(2^k) + 1 +
    # point_x), z evolving by squaring per row. The runtime coordinates walk
    # OUTSIDE and the fixed Frobenius powers inside, so nothing stores a z-power
    # table. Coordinates go RS_CHUNK an iteration, so a row is read and written once
    # per chunk; count = RS_CHUNK q + r is pinned from advice bits, and the r left
    # over run after the loop. Returns the final row.
    bits = StackBuf(RS_COUNT_BITS)
    hint_decompose_bits_exponent(bits, count_g, RS_COUNT_BITS)
    r_g = GEN ** 0
    q_g = GEN ** 0
    for k in unroll(0, RS_COUNT_BITS):
        b = bits[k]
        bits[k] = b * b
        if const(k // RS_CHUNK_BITS == 0):
            r_g *= 1 + b * (1 + GEN ** (2 ** k))
        else:
            q_g *= 1 + b * (1 + GEN ** (2 ** (k - RS_CHUNK_BITS)))
    assert q_g ** RS_CHUNK * r_g == count_g
    for xq in mul_range(1, q_g):
        base = xq ** RS_CHUNK
        done = rs_eq_rows(chain * xq ** BASE_FIELD_BITS, z_vals * base, point1 * base, RS_CHUNK)
    base = q_g ** RS_CHUNK
    row = chain * q_g ** BASE_FIELD_BITS
    last = match(log(r_g), range(0, RS_CHUNK), lambda n: rs_eq_rows(row, z_vals * base, point1 * base, n))
    return last


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


def sumcheck_round4(rd, msg_cursor, claim, tabs):
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
    # and h(y) = c0 + y (claim + (1 + y) (c2 + (1 + y) c3)). Then the round's grind.
    sp, y, msg_cursor = fs_grind_squeeze(sp, rate, 3, msg_cursor, tabs, ROUND3_GRIND_BITS)
    fs_store(rd * GEN ** ROUND_SLOTS, ROUND_FS, 1, sp)
    y1 = 1 + y
    return msg_cursor, c0 + y * (claim + y1 * (c2 + y1 * c3)), y


def gkr_rounds(rd, pt, tabs, n: Const):
    # n GKR rounds, from the round record at `rd` (fields GKR_ROUNDS_CAP apart) to the
    # one n further. The prover sends every coefficient but c0, which the round's
    # pulled-out eq factor leaves fixed: c0 + r (c1 + ... + c4) == claim, r being the
    # previous point's coordinate pt[q], then the round's grind; the challenge goes to
    # pt[MU_CAP + 2 + q].
    if const(n != 0):
        sp = fs_load(rd, ROUND_FS, GKR_ROUNDS_CAP)
        cur = rd[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)]
        claim = rd[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)]
        for q in unroll(0, n):
            rate = StackBuf(8)
            c1, cur = fs_next(rate, 0, cur)
            c2, cur = fs_next(rate, 1, cur)
            c3, cur = fs_next(rate, 2, cur)
            c4, cur = fs_next(rate, 3, cur)
            sp, rk, cur = fs_grind_squeeze(sp, rate, 4, cur, tabs, ROUND5_GRIND_BITS)
            c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
            pt[GEN ** (MU_CAP + 2 + q)] = rk
            claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
        rd_next = rd * GEN ** n
        fs_store(rd_next, ROUND_FS, GKR_ROUNDS_CAP, sp)
        rd_next[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)] = cur
        rd_next[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)] = claim
    return 0


def batch_sumcheck(fs0, fs1, fs2, fs3, fs4, msgs, running, point, tabs, n_rounds: Const):
    # The rounds of a claim-batching sumcheck: two hinted values per round
    # (g(1) and g(inf)) and the degree-two round's nonce, if any, the split fixing the
    # third against the running claim, and the challenges collected into `point`.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    for rd in unroll(0, n_rounds):
        rate = StackBuf(8)
        msg_g1, c = fs_next(rate, 0, msgs * GEN ** (BC_ROUND_WORDS * rd))
        msg_ginf, c = fs_next(rate, 1, c)
        sp, rv, c = fs_grind_squeeze(sp, rate, 2, c, tabs, ROUND2_GRIND_BITS)
        point[GEN ** rd] = rv
        g_zero = running + msg_g1
        c_one = g_zero + msg_g1 + msg_ginf
        running = (msg_ginf * rv + c_one) * rv + g_zero  # fold the degree-2 round at rv
    return sp[8], sp[9], sp[10], sp[11], sp[12], running


# ==================================== Merkle paths ==================================


def verify_merkle_cap(cap, flags, depth: Const):
    # Unrolled over the cap's nodes, so every address is an immediate. Every node's
    # hinted digest (node k at heap cells 2k, 2k+1) is read once into a frame run,
    # node k at cells 2(k - 1) and 2k - 1, where an internal node's hash writes its
    # digest, landing on (and so asserting) the hinted value. An active (flagged)
    # node is hashed; an inactive one pins its children's flags to zero, so every
    # active node's parent is active too, up to the root, which is always hashed.
    # The queries flag the parents of the cap leaves they reach. The run is sized
    # per depth, the cap depths a configuration reaches.
    if depth != 0:
        n_leaves = 2 ** depth
        if const(depth == 4):
            runs = StackBuf(4 * 16 - 2)
        elif const(depth == 5):
            runs = StackBuf(4 * 32 - 2)
        elif const(depth == 6):
            runs = StackBuf(4 * 64 - 2)
        elif const(depth == 7):
            runs = StackBuf(4 * 128 - 2)
        else:
            runs = StackBuf(4 * 256 - 2)
        for node in unroll(1, 2 * n_leaves):
            at = 2 * (node - 1)
            runs[at] = cap[GEN ** (2 * node)]
            runs[at + 1] = cap[GEN ** (2 * node + 1)]
        for node in unroll(1, n_leaves):
            left = 2 * (2 * node - 1)
            right = left + 2
            at = 2 * (node - 1)
            if const(node == 1):
                keccak(runs[left:left + 2], runs[right:right + 2], runs[at:at + 2])
            else:
                if flags[GEN ** node] != 0:
                    keccak(runs[left:left + 2], runs[right:right + 2], runs[at:at + 2])
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
# A level's rounds fold its lanes by the affine combiner G + (alpha + beta X)(F + theta G)
# of [CYWZ26, preprint], the claim carried by five scalars a round and the weight folded
# by gamma, so the gammas are the weight's point (verifier::whir::verify_whir). A
# non-final level then commits the folded lane's low part, sends its high part, and glues
# its OOD claims and its queries, each opened row folded as the lanes were and corrected by
# the high part. The final level sends the whole folded lane, checks the queries against
# it, and closes with a sumcheck over the low part.


def opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, gammas, coefs):
    # One fold round: grind, theta, the five scalars [u0, v0, c0, v1, c1], grind, then
    # gamma, alpha, beta. The G lanes' share u1 = claim + v0 + theta u0 is derived. The
    # row folds read alpha, beta, theta at coefs[0..3]; gamma is the point's coordinate.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    sp, theta, cursor = fs_grind_squeeze(sp, rate, 0, cursor, tabs, FOLD_GRIND_BITS)
    msg = StackBuf(8)
    u0, cursor = fs_next(msg, 0, cursor)
    v0, cursor = fs_next(msg, 1, cursor)
    c0, cursor = fs_next(msg, 2, cursor)
    v1, cursor = fs_next(msg, 3, cursor)
    sp = fs_perm(sp, msg, 4)
    last = StackBuf(8)
    c1, cursor = fs_next(last, 0, cursor)
    sp, gamma, cursor = fs_grind_squeeze(sp, last, 1, cursor, tabs, FOLD_GRIND_BITS)
    sp, alpha = squeeze(sp, rate, 0)
    sp, beta = squeeze(sp, rate, 0)
    gammas[GEN ** 0] = gamma
    coefs[GEN ** 0] = alpha
    coefs[GEN ** 1] = beta
    coefs[GEN ** 2] = theta
    side0 = u0 + alpha * v0 + beta * c0
    side1 = claim + v0 + theta * u0 + alpha * v1 + beta * c1
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, side0 + gamma * (side0 + side1)


def opening_message(fs0, fs1, fs2, fs3, fs4, cursor, out, n: Const, nonce: Const):
    # n stream words into out, then, with `nonce`, a grinding nonce, then the
    # permutation the next challenge comes from. Returns that output's first cell (the
    # challenge), its second (where the proof of work is), its capacity and the cursor.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    for pos in unroll(0, n):
        if pos % 4 == 0:
            if pos != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        value, cursor = fs_next(rate, pos % 4, cursor)
        out[GEN ** pos] = value
    if const(nonce == 1):
        if const(n % 4 == 0):
            if const(n != 0):
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        sp = fs_absorb_nonce(sp, rate, n % 4, cursor[GEN ** 0])
        cursor = cursor * GEN
    elif const(n == 0):
        sp = fs_perm(sp, rate, 0)
    else:
        sp = fs_perm(sp, rate, (n + 3) % 4 + 1)
    return sp[0], sp[1], sp[8], sp[9], sp[10], sp[11], sp[12], cursor


def squeeze_point(fs0, fs1, fs2, fs3, fs4, point, n: Const):
    # n challenges, nothing waiting in the sponge.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    no_rate = StackBuf(8)
    for x in unroll(0, n):
        sp, r = squeeze(sp, no_rate, 0)
        point[GEN ** x] = r
    if const(n == 0):
        out = sp
    else:
        out = [sp[8], sp[9], sp[10], sp[11], sp[12]]
    return out[0], out[1], out[2], out[3], out[4]


def squeeze_point_from(fs0, fs1, fs2, fs3, fs4, first, point, n: Const):
    # n challenges whose first, `first`, a permutation already drew, the sponge its
    # capacity: the other n - 1 are fresh squeezes.
    point[GEN ** 0] = first
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    if const(n // 2 == 0):
        out = sp
    else:
        no_rate = StackBuf(8)
        for x in unroll(1, n):
            sp, r = squeeze(sp, no_rate, 0)
            point[GEN ** x] = r
        out = [sp[8], sp[9], sp[10], sp[11], sp[12]]
    return out[0], out[1], out[2], out[3], out[4]


def opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs):
    # One round of the closing sumcheck: h(0) + h(1) == claim fixes h's linear
    # coefficient, so c0 and c2 are sent and h(r) = c0 + r (claim + (1 + r) c2). Then
    # the round's grind.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    c0, cursor = fs_next(rate, 0, cursor)
    c2, cursor = fs_next(rate, 1, cursor)
    sp, r, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, ROUND2_GRIND_BITS)
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, c0 + r * (claim + (1 + r) * c2), r


@inline
def walk_window(n0, n1, path, lvl0: Const, width: Const, k: Const):
    # Levels lvl0..lvl0+width of a Merkle path, whose order bits are k's: each hashes the running
    # node with the sibling on the other side of its hinted pair, which binds the link.
    for r in unroll(0, width):
        lvl = lvl0 + r
        nxt = StackBuf(2)
        if const((k // 2 ** r) % 2 == 0):
            keccak([n0, n1], path[4 * lvl + 2:4 * lvl + 4], nxt)
        else:
            keccak(path[4 * lvl:4 * lvl + 2], [n0, n1], nxt)
        n0 = nxt[0]
        n1 = nxt[1]
    return n0, n1


def walk_path(n0, n1, wins, cap, flags, path_depth: Const, cap_depth: Const):
    # The path, a window of QW levels a dispatch (`decode_query_windows`): each arm knows its
    # levels' order bits, so it hashes the running node against the sibling its hinted pair holds.
    path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:4 * path_depth], "merkle_children")
    for i in unroll(0, (path_depth + QW - 1) // QW):
        if const(QW * i + QW == QW * ((path_depth + QW - 1) // QW)):
            width = path_depth - QW * i
        else:
            width = QW
        w = wins[GEN ** i]
        if const(width == 6):
            n0, n1 = match(log(w), range(0, 64), lambda k: walk_window(n0, n1, path, QW * i, 6, k))
        elif const(width == 5):
            n0, n1 = match(log(w), range(0, 32), lambda k: walk_window(n0, n1, path, QW * i, 5, k))
        elif const(width == 4):
            n0, n1 = match(log(w), range(0, 16), lambda k: walk_window(n0, n1, path, QW * i, 4, k))
        elif const(width == 3):
            n0, n1 = match(log(w), range(0, 8), lambda k: walk_window(n0, n1, path, QW * i, 3, k))
        elif const(width == 2):
            n0, n1 = match(log(w), range(0, 4), lambda k: walk_window(n0, n1, path, QW * i, 2, k))
        else:
            n0, n1 = match(log(w), range(0, 2), lambda k: walk_window(n0, n1, path, QW * i, 1, k))
    # The reached cap leaf is node 2*parent + bit at cells 2*node, 2*node + 1, where
    # parent = 2^(cap_depth-1) + q: the child bit and q are the last two windows, g^bit
    # and g^q, the constant parts folded into the address immediates. Every cap is at
    # least two levels deep (`decode_query_windows` gives q cap_depth - 1 bits).
    wb = wins[GEN ** ((path_depth + QW - 1) // QW)]
    q = wins[GEN ** ((path_depth + QW - 1) // QW + 1)]
    flags_q = flags * q
    flags_q[GEN ** (2 ** (cap_depth - 1))] = 1  # the cap check propagates this obligation to the root
    q2 = q * q
    leaf = cap * q2 * q2 * (wb * wb)
    leaf[GEN ** (2 ** (cap_depth + 1))] = n0
    leaf[GEN ** (2 ** (cap_depth + 1) + 1)] = n1
    return


@inline
def novel_eval(coefs, ws, n: Const, nbits: Const):
    # sum_(c < n) coefs[c] prod_(i: c_i = 1) ws[i], the novel basis at a point whose
    # What_i normalizers the coefficients already carry: folded the lowest bit first,
    # out[m] = in[2m] + ws[i] in[2m + 1], level i of `buf` at 2^(nbits+1) - 2^(nbits+1-i).
    if const(nbits // 4 == 0):
        buf = StackBuf(16)
    elif const(nbits == 4):
        buf = StackBuf(32)
    elif const(nbits == 5):
        buf = StackBuf(64)
    else:
        buf = StackBuf(128)
    if const(nbits == 0):
        out = coefs[GEN ** 0]
    else:
        for i in unroll(0, nbits):
            n_in = const((n + 2 ** i - 1) // 2 ** i)
            at = const(2 ** (nbits + 1) - 2 ** (nbits + 1 - i))
            for m in unroll(0, (n_in + 1) // 2):
                if const(i == 0):
                    lo = coefs[GEN ** (2 * m)]
                    if const((2 * m + 1) // n_in == 0):
                        hi = coefs[GEN ** (2 * m + 1)]
                else:
                    src = const(2 ** (nbits + 1) - 2 ** (nbits + 2 - i))
                    lo = buf[src + 2 * m]
                    if const((2 * m + 1) // n_in == 0):
                        hi = buf[src + 2 * m + 1]
                if const((2 * m + 1) // n_in == 0):
                    buf[at + m] = lo + ws[i] * hi
                else:
                    buf[at + m] = lo
        out = buf[2 ** (nbits + 1) - 4]
    return out


@inline
def opening_query(cap, flags, coefs, hs, x, wins, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # One query: hash the hinted row up its Merkle path into the shared cap, then fold
    # it at its point x round by round as the prover folded the lanes. A row is one
    # hinted word a lane: a K lane at level 0, whose leaf image lists the lanes from the
    # top down, an E word deeper, which is already the leaf's cell. At a non-final level
    # the fold is returned (its high part's share is taken out in open_stacked's
    # residual pass); at the final level it must be P_final(x).
    interleave = const(2 ** folds)
    if const(folds // 5 == 0):
        row = StackBuf(16)
        acc = StackBuf(16)
    else:
        row = StackBuf(LIG_ROW_CAP)
        acc = StackBuf(LIG_ROW_CAP)
    hint_witness(row[0:interleave], "merkle_leaf_rows")
    leaf_hash_state = StackBuf(2)
    if base == 1:
        # Packing proves each hinted lane is in K before hashing or folding it.
        packed_row = StackBuf(LIG_PACKED_ROW_CAP)
        for jb in unroll(0, interleave // 2):
            packed_row[jb] = pack64x2(row[2 * jb], row[2 * jb + 1])
        keccak_cells(packed_row[0:leaf_cells], leaf_hash_state)
    else:
        keccak_cells(row[0:leaf_cells], leaf_hash_state)
    walk_path(leaf_hash_state[0], leaf_hash_state[1], wins, cap, flags, depth - cap_depth, cap_depth)
    # Round j takes the lane pairs (F, G) to t F + s G, t = alpha + beta x and
    # s = 1 + theta t. As t (F + (s / t) G) every output of a round shares the factor
    # t, so the pairs fold by r = theta + 1 / t and the t's multiply back once.
    for j in unroll(0, folds):
        t = coefs[GEN ** (3 * j)] + coefs[GEN ** (3 * j + 1)] * x
        r = coefs[GEN ** (3 * j + 2)] + 1 / t
        if const(j == 0):
            scale = t
        else:
            scale = scale * t
        n_out = const(2 ** (folds - 1 - j))
        for m in unroll(0, n_out):
            if const(j == 0):
                if const(base == 1):
                    acc[m] = row[interleave - 1 - 2 * m] + r * row[interleave - 2 - 2 * m]
                else:
                    acc[m] = row[2 * m] + r * row[2 * m + 1]
            else:
                src = const(interleave - 4 * n_out)
                acc[interleave - 2 * n_out + m] = acc[src + 2 * m] + r * acc[src + 2 * m + 1]
    value = scale * acc[interleave - 2]
    if const(final == 1):
        # The unnormalized W_i(x) for i <= mu, W_(i+1) = W_i (W_i + W_i(beta_i)).
        ws = StackBuf(YR_LOG_CAP + 1)
        ws[0] = x
        for i in unroll(1, mu + 1):
            ws[i] = ws[i - 1] * (ws[i - 1] + LIG_VANISH_VALS[vanish + i - 1])
        assert value == novel_eval(hs, ws, n_hs, hs_bits)
        out = 0
    else:
        out = value
    return out


def opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the challenge reads; an odd count runs its first query alone,
    # ahead of the pairs. Extension rows run one query an iteration.
    # Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at
    # sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's
    # queries are checks, with nothing to sum.
    chain = HeapBuf(n_iters_g * GEN)
    if odd == 1:
        chain[GEN ** 0] = opening_query(cap, flags, coefs, hs, positions[GEN ** 0], query_win_ptrs[GEN ** 0], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final) * lam_inv
    else:
        chain[GEN ** 0] = 0
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            pair_pos = positions * xi * xi
            pair_wins = query_win_ptrs * xi * xi
            d0 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** odd], pair_wins[GEN ** odd], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            d1 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** (odd + 1)], pair_wins[GEN ** (odd + 1)], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = ((chain[xi] + d0) * lam_inv + d1) * lam_inv
        else:
            d = opening_query(cap, flags, coefs, hs, positions[xi], query_win_ptrs[xi], base, folds, leaf_cells, depth, cap_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = (chain[xi] + d) * lam_inv
    if final == 0:
        total = chain[n_iters_g]
    else:
        total = 0
    return total


@inline
def residual_query(basis_chain, row_d, hs, vanish: Const, n_cols: Const, n_hs: Const, hs_bits: Const):
    # prod_t (d_t + chain_t) over one query's message-column coordinates, chain_t =
    # W_t(x), x the query position; then the high part's share of the query's fold,
    # What_mu(x) sum_j p_(2^mu + j) X_j(x), its normalizers in hs.
    ws = StackBuf(HIGH_BITS_CAP)
    ws[0] = basis_chain
    prefix_eq = row_d[GEN ** 0] + basis_chain
    for t in unroll(1, n_cols + 1):
        # subspace-vanishing recurrence for the novel-basis point
        if const(t // HIGH_BITS_CAP == 0):
            ws[t] = basis_chain * (basis_chain + LIG_VANISH_VALS[vanish + t - 1])
            basis_chain = ws[t]
        else:
            basis_chain *= basis_chain + LIG_VANISH_VALS[vanish + t - 1]
        if const(t != n_cols):
            prefix_eq *= row_d[GEN ** t] + basis_chain
    return prefix_eq, basis_chain * novel_eval(hs, ws, n_hs, hs_bits)


def open_stacked(m_idx: Const, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per (rate, committed log-size)
    # candidate: every LIG_* table reads row m_idx, per level row `ml`, and all
    # opening proof data is hinted here, so only the executed arm pops its streams.
    # The opening's scalars (round tables, level roots, high parts, OOD values,
    # nonces, the final lane, the closing rounds) ride the SHARED stream, walked on in
    # protocol order. A Merkle root is its two F128 scalars, exactly the root's two cells.
    #
    # Returns the closing claim, the point in witness order (and 1 + it), the glued
    # claims' weights at it, and the final lane's low part at the closing point.
    n_levels = LIG_N_LEVELS[m_idx]
    last = LIG_YR_LEVEL[m_idx]  # the final level, n_levels - 1
    yr_log = LIG_YR_LOG_LEN[m_idx]
    yr_len = LIG_YR_LEN[m_idx]
    n_folds = LIG_TOTAL_FOLDS[m_idx]

    # Caps are shared across queries; rows and paths are hinted in each query's frame.
    merkle_caps = HeapBuf(GEN ** (4 * LIG_CAP_LEN[m_idx]))
    hint_witness(merkle_caps[0:4 * LIG_CAP_LEN[m_idx]], "merkle_caps")
    cap_flags = HeapBuf(GEN ** LIG_CAP_LEN[m_idx])
    hint_witness(cap_flags[0:LIG_CAP_LEN[m_idx]], "merkle_cap_active")
    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The gammas in round order, and each round's alpha, beta, theta.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (3 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^(OOD_SAMPLES + 1) times
    # lam^n (the inverse chains' correction), 1/lam, and its OOD claims' points and
    # scalars lam^(s + 1), claim s at row OOD_SAMPLES (lvl + 1) + s.
    level_betas = HeapBuf(GEN ** n_levels)
    level_mus = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** (n_levels * 2 ** HIGH_BITS_CAP))  # each high part, normalizers in
    ood_z = HeapBuf(GEN ** (OOD_SAMPLES * n_levels * LIG_LOG_MSG_COLS_CAP))
    ood_scalars = HeapBuf(GEN ** (OOD_SAMPLES * n_levels))
    query_positions = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))
    query_win_ptrs = HeapBuf(GEN ** (LIG_POSITIONS_LEN[m_idx]))

    claim = target
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        n_queries = LIG_QUERIES[ml]
        depth = LIG_TREE_DEPTH[ml]
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        pos_off = LIG_POSITIONS_OFF[ml]
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (3 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD points,
            # one message with no grind, the first drawn by the permutation taking
            # those words, then their values and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, unused, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 0)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** (OOD_SAMPLES * (lvl + 1) * LIG_LOG_MSG_COLS_CAP)
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            for s in unroll(1, OOD_SAMPLES):
                fs0, fs1, fs2, fs3, fs4 = squeeze_point(fs0, fs1, fs2, fs3, fs4, ood_row * GEN ** (s * LIG_LOG_MSG_COLS_CAP), mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_ys = StackBuf(OOD_SAMPLES)
            for s in unroll(0, OOD_SAMPLES):
                ood_y, cursor = fs_next(rate, s, cursor)
                ood_ys[s] = ood_y
            sp = fs_absorb_nonce(sp, rate, OOD_SAMPLES, cursor[GEN ** 0])
            cursor = cursor * GEN
            word0 = sp[0]
            pow0 = sp[1]
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        # The nonce, a raw transport word, is bound by its DS_POW_NONCE absorb above;
        # its permutation draws the first query word, word0.
        grind_check(pow0, tabs, QUERY_GRIND_BITS)

        # Row k of sqz is the capacity of the permutation that drew query word k - 1.
        sqz = HeapBuf((GEN ** (LIG_MAX_SQUEEZES[m_idx] + 1)) ** FS_CELLS)
        sqz[GEN ** FS_CELLS] = fs0
        sqz[GEN ** (FS_CELLS + 1)] = fs1
        sqz[GEN ** (FS_CELLS + 2)] = fs2
        sqz[GEN ** (FS_CELLS + 3)] = fs3
        sqz[GEN ** (FS_CELLS + 4)] = fs4
        decode_query_windows(word0, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, tabs, depth, LIG_CAP_DEPTH[ml])
        for xs in mul_range(GEN, GEN ** LIG_SQUEEZES[ml]):
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
            cap_depth = LIG_CAP_DEPTH[m_idx * LIG_MAX_LEVELS + lvl]
            decode_query_windows(packed_word, query_positions * GEN ** pos_off * query_ptr, query_win_ptrs * GEN ** pos_off * query_ptr, tabs, depth, cap_depth)
        sqz_end = sqz * (GEN ** LIG_SQUEEZES[ml]) ** FS_CELLS
        sp = fs_load(sqz_end, 0, 1)
        if const(lvl != last):
            # One batching challenge for the level's glued claims, ground first.
            rate = StackBuf(8)
            sp, lam, cursor = fs_grind_squeeze(sp, rate, 0, cursor, tabs, BATCH_GRIND_BITS)
            lam_inv = 1 / lam
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam_inv = 0
            fs0 = sp[0]
            fs1 = sp[1]
            fs2 = sp[2]
            fs3 = sp[3]
            fs4 = sp[4]

        cap_depth = LIG_CAP_DEPTH[ml]
        cap = merkle_caps * GEN ** (4 * LIG_CAP_OFF[ml])
        flags = cap_flags * GEN ** LIG_CAP_OFF[ml]
        root_0, root_1 = verify_merkle_cap(cap, flags, cap_depth)
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        # The sent coefficients scaled by the What_i normalizers of their basis
        # elements, so a query evaluates them at the unnormalized W_i(x): at the final
        # level the whole lane, its high part X_(2^mu + j) = What_mu X_j; deeper, the
        # high part alone, What_mu folded in, for the residual pass.
        if const(lvl == last):
            n_hs = const(yr_len + folds)
            hs_bits = const(yr_log + 1)
            hs = HeapBuf(GEN ** n_hs)
            for c in unroll(0, n_hs):
                sc = 1
                for i in unroll(0, hs_bits):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * LIG_VANISH_INVS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** (lvl * 2 ** HIGH_BITS_CAP)
            for c in unroll(0, folds):
                sc = LIG_VANISH_INVS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * LIG_VANISH_INVS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        # At level 0 a leaf image lists its lanes from the top down: the lanes a
        # padding-free commitment leaves out are its LEADING words, whose whole blocks
        # the committer hashes once for all leaves. The flip is a compile-time index.
        if const(lvl == 0):
            pairs = n_queries // 2
            odd = n_queries % 2
        else:
            pairs = n_queries
            odd = 0
        if const(lvl == last):
            batched = opening_queries(cap, flags, lam_inv, round_coefs * GEN ** (3 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, GEN ** pairs, odd, 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], depth, cap_depth, mu, vanish, n_hs, hs_bits, 1)
        else:
            batched = opening_queries(cap, flags, lam_inv, round_coefs * GEN ** (3 * folds_off), hs, query_positions * GEN ** pos_off, query_win_ptrs * GEN ** pos_off, GEN ** pairs, odd, 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], depth, cap_depth, 0, 0, 0, 0, 0)

        if const(lvl != last):
            # OOD claim s takes lam^(s + 1), the query batch lam^(OOD_SAMPLES + 1) times
            # its own powers of lam. A query's value is its fold plus the high part's
            # share, which enters the claim linearly: the residual pass adds it, scaled
            # by every gamma and tail challenge drawn after this level, the claim's
            # factor from here on.
            lam_s = lam
            for s in unroll(0, OOD_SAMPLES):
                ood_scalars[GEN ** (OOD_SAMPLES * (lvl + 1) + s)] = lam_s
                claim = claim + lam_s * ood_ys[s]
                lam_s = lam_s * lam
            scale = lam_s * lam ** n_queries
            claim = claim + scale * batched
            level_betas[GEN ** lvl] = scale
            level_mus[GEN ** lvl] = lam_inv

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The gammas bind coordinates in ROUND order, and level 0's are the lane fold,
    # binding the witness's TOP k coordinates: lane l of the commitment is the stack
    # block q[l * 2^(mu-k) ...], which is what makes the witness's zero padding whole
    # lanes for the committer to leave out of the encode. Every transparent weight
    # downstream is written in witness coordinates, so rotate the point left by those
    # k rounds here, while the level shape is still compile-time. Padding is zero so
    # shared prefix chains may compute unused entries above m without reading
    # uninitialized cells.
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

    # ---- each non-final level's glued query batch, at the terminal point ----
    # Every query of a level runs the SAME product shape over its message-column
    # coordinates, the column weight prod_t (1 + c_t (1 + What_t(x))); only the
    # novel-basis chain (the query position's subspace-vanishing walk) differs. Since
    #     1 + c_t * (1 + chain_t * inv_t) == (1 + c_t) + (c_t * inv_t) * chain_t
    # a coordinate's two coefficients depend on the challenge and the baked
    # vanishing inverse alone, so they hoist out of the query loop (one row a level,
    # gammas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once. A zero
    # challenge makes b_t zero and the division unsatisfiable, which rejects rather
    # than accepts.
    basis_d = HeapBuf(GEN ** (n_levels * LIG_LOG_MSG_COLS_CAP))
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        scale = level_betas[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * LIG_VANISH_INVS[vanish + t]
            basis_d[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] = (1 + fold_c) / coef_b
            scale *= coef_b
            after *= fold_c
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * LIG_VANISH_INVS[vanish + prefix_len + j]
            basis_d[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + prefix_len + j)] = (1 + tail_c) / coef_b
            scale *= coef_b
            after *= tail_c
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        n_queries = LIG_QUERIES[ml]
        vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
        basis_row = lvl * LIG_LOG_MSG_COLS_CAP
        n_hs = LIG_FOLDS[ml]
        hs_bits = LIG_HIGH_BITS[ml]
        hs = level_hs * GEN ** (lvl * 2 ** HIGH_BITS_CAP)
        # Query q is weighted lam^q: each chain runs h <- (h + term_q) * mu with mu = 1/lam,
        # ending at lam^-n * sum_q lam^q term_q, and level_betas carries lam^(n + OOD_SAMPLES + 1).
        mu = level_mus[GEN ** lvl]
        residual_chain = HeapBuf(GEN ** (2 * (n_queries // RES_BATCH + 1)))
        residual_chain[GEN ** 0] = 0
        residual_chain[GEN ** 1] = 0
        # RES_BATCH queries an iteration share the row's reads and constants.
        for xr in mul_range(1, GEN ** (LIG_QUERIES[ml] // RES_BATCH)):
            ml = m_idx * LIG_MAX_LEVELS + lvl  # rebound: the body captures by value
            vanish = m_idx * LIG_MAX_VANISH_LEN + LIG_VANISH_OFF[ml]
            basis_row = lvl * LIG_LOG_MSG_COLS_CAP
            positions = query_positions * GEN ** LIG_POSITIONS_OFF[ml] * xr ** RES_BATCH
            row_d = basis_d * GEN ** basis_row
            hs = level_hs * GEN ** (lvl * 2 ** HIGH_BITS_CAP)
            rec = residual_chain * xr * xr
            h = rec[GEN ** 0]
            h_high = rec[GEN ** 1]
            for k in unroll(0, RES_BATCH):
                eq_q, high_q = residual_query(positions[GEN ** k], row_d, hs, vanish, LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml])
                h = (h + eq_q) * mu
                h_high = (h_high + high_q) * mu
            rec[GEN ** 2] = h
            rec[GEN ** 3] = h_high
        rec = residual_chain * GEN ** (2 * (n_queries // RES_BATCH))
        h = rec[GEN ** 0]
        h_high = rec[GEN ** 1]
        for q in unroll(n_queries - n_queries % RES_BATCH, n_queries):
            eq_q, high_q = residual_query(query_positions[GEN ** (LIG_POSITIONS_OFF[ml] + q)], basis_d * GEN ** basis_row, hs, vanish, LIG_LOG_MSG_COLS[ml], n_hs, hs_bits)
            h = (h + eq_q) * mu
            h_high = (h_high + high_q) * mu
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain) into the total,
        # and lam^(n+2) * (the challenges after the level) * (its high chain) into the claim
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h
        acc[GEN ** 3] = acc[GEN ** 1] + level_betas[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its power of
    # its level's lam.
    ood_inner = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        for s in unroll(0, OOD_SAMPLES):
            oz = ood_z * GEN ** ((OOD_SAMPLES * ood_lvl + s) * LIG_LOG_MSG_COLS_CAP)
            scalar = ood_scalars[GEN ** (OOD_SAMPLES * ood_lvl + s)]
            for t in unroll(0, z_folded):
                scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
            for t in unroll(0, yr_log):
                scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
            ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail


# ============================== inner-proof verification ============================
# The phases of `verify_sub`, in the order it runs them. Each takes and returns the
# Fiat-Shamir state pair and the stream cursor, so the sequence is what binds them.


@inline
def gkr_combine(vals, lam):
    # The trees' claims batched by powers of the combiner, tree t at lam^t.
    claim = vals[N_GKR_TREES - 1]
    for i in unroll(1, N_GKR_TREES):
        claim = vals[N_GKR_TREES - 1 - i] + lam * claim
    return claim


@inline
def gkr_children(sp, cursor, evals, n: Const):
    # Every tree's n children, tree by tree, nothing waiting before them. Returns the
    # sponge, the rate left waiting (its last one to four scalars) and the cursor.
    rate = StackBuf(8)
    for i in unroll(0, N_GKR_TREES * n):
        if i % 4 == 0:
            if i != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        ev, cursor = fs_next(rate, i % 4, cursor)
        evals[i] = ev
    return sp, rate, cursor


@inline
def gkr_product_check(evals, lam, claim, n: Const):
    # The layer's sumcheck claim is the combined product of each tree's n children.
    combined = 0
    for i in unroll(0, N_GKR_TREES):
        tree = N_GKR_TREES - 1 - i  # Horner in lam, so the top tree lands last
        product = evals[n * tree]
        for j in unroll(1, n):
            product = product * evals[n * tree + j]
        combined = product + lam * combined
    assert claim == combined
    return


@inline
def gkr_y_grind(out, cur_out, sp, rate, cursor, tabs, last: Const):
    # A radix-four layer's first y challenge, its children waiting, after the grind
    # for y, the last layer's if `last`: the permutation drawing it into `out`, the
    # cursor into `cur_out`.
    if const(last == 1):
        nxt, c, cur = fs_grind_squeeze(sp, rate, (4 * N_GKR_TREES + 3) % 4 + 1, cursor, tabs, GKR_Y_LAST_GRIND_BITS)
    else:
        nxt, c, cur = fs_grind_squeeze(sp, rate, (4 * N_GKR_TREES + 3) % 4 + 1, cursor, tabs, GKR_Y_GRIND_BITS)
    for j in unroll(0, KECCAK_STATE):
        out[j] = nxt[j]
    cur_out[0] = cur
    return 0


def verify_bus_gkr(fs0, fs1, fs2, fs3, fs4, cursor, g_bus_mu, zeta, tabs):
    # ONE GKR grand product over the N_GKR_TREES trees (push, pull, then count), batched by powers of a combiner. Push and pull have
    # equal depth (matched blocks) and the count tree is padded with identity leaves
    # up to it (product unchanged), so a single sumcheck serves them all. Radix four
    # contracts two binary levels per layer, each batched by a fresh combiner drawn
    # after a grind. All the trees reduce to the one shared point `zeta`, which this
    # fills, returning their leaf values with the walked Fiat-Shamir state and stream
    # cursor. The root-most layer, which has no rounds and finds the roots waiting in
    # the sponge, runs on its own: a binary layer for an odd depth, else a radix-four
    # one. It is never the last, the depth being at least the memory block's MIN_LOG_MEM.
    layers = HeapBuf((g_bus_mu * GEN ** 2) ** LAYER_SLOTS)
    rounds = HeapBuf(GKR_ROUNDS_CAP * ROUND_SLOTS)
    gkr_pts = HeapBuf(GKR_POINTS_CAP)
    assert log(g_bus_mu) < COUNT_BITS
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    # Push and pull's one root, then the count's.
    vals = StackBuf(N_GKR_TREES)
    root, cursor = fs_next(rate, 0, cursor)
    vals[PUSH_SIDE] = root
    vals[PULL_SIDE] = root
    root_count, cursor = fs_next(rate, 1, cursor)
    vals[COUNT_SIDE] = root_count
    assert root_count != 0  # count-tree root nonzero: no read count self-cancels
    sp, lam, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, GKR_COMBINER_GRIND_BITS)
    claim = gkr_combine(vals, lam)
    # k % 4 and its carry into k // 4 as layer k becomes k + 1, by g^(k % 4).
    k_mod_next = HeapBuf(8)
    for r in unroll(0, 4):
        k_mod_next[GEN ** r] = GEN ** ((r + 1) % 4)
        k_mod_next[GEN ** (4 + r)] = GEN ** ((r + 1) // 4)
    # Past the root-most layer, (depth - 1) // 2 radix-four layers; and g exactly when
    # the depth is odd.
    loop_bounds = HeapBuf(COUNT_BITS)
    depth_odd = HeapBuf(COUNT_BITS)
    loop_bounds[GEN ** 0] = GEN ** 0
    depth_odd[GEN ** 0] = GEN ** 0
    for depth in unroll(1, COUNT_BITS):
        loop_bounds[GEN ** depth] = GEN ** ((depth - 1) // 2)
        depth_odd[GEN ** depth] = GEN ** (depth % 2)
    odd_g = depth_odd[g_bus_mu]
    if const(GKR_Y_GRIND_BITS != GKR_Y_LAST_GRIND_BITS):
        # g^1 at the last layer, whose start leaves two binary levels, else g^0.
        last_layer = HeapBuf(COUNT_BITS)
        for depth in unroll(0, COUNT_BITS):
            if const(depth == 2):
                last_layer[GEN ** depth] = GEN
            else:
                last_layer[GEN ** depth] = GEN ** 0
    nextrow = gkr_pts * GEN ** MU_CAP
    if odd_g != 1:
        # The binary root layer: two children a tree, y one coordinate.
        evals = StackBuf(2 * N_GKR_TREES)
        sp, rate, cursor = gkr_children(sp, cursor, evals, 2)
        gkr_product_check(evals, lam, claim, 2)
        sp, c0, cursor = fs_grind_squeeze(sp, rate, (2 * N_GKR_TREES + 3) % 4 + 1, cursor, tabs, GKR_Y1_GRIND_BITS)
        nextrow[GEN ** 0] = c0
        nxt = layers * GEN ** LAYER_SLOTS
        fs_store(nxt, LAYER_FS, 1, sp)
        nxt[GEN ** LAYER_CURSOR] = cursor
        for t in unroll(0, N_GKR_TREES):
            nxt[GEN ** (LAYER_VALS + t)] = evals[2 * t] + c0 * (evals[2 * t] + evals[2 * t + 1])
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN
        nxt[GEN ** LAYER_HALF] = GEN ** 0
        nxt[GEN ** LAYER_PARITY] = GEN ** 0
    else:
        # The radix-four root layer: four children a tree, y two coordinates.
        evals = StackBuf(4 * N_GKR_TREES)
        sp, rate, cursor = gkr_children(sp, cursor, evals, 4)
        gkr_product_check(evals, lam, claim, 4)
        sp, c0, cursor = fs_grind_squeeze(sp, rate, (4 * N_GKR_TREES + 3) % 4 + 1, cursor, tabs, GKR_Y_GRIND_BITS)
        no_rate = StackBuf(8)
        sp, c1 = squeeze(sp, no_rate, 0)
        nextrow[GEN ** 0] = c0
        nextrow[GEN ** 1] = c1
        nxt = layers * GEN ** (2 * LAYER_SLOTS)
        fs_store(nxt, LAYER_FS, 1, sp)
        nxt[GEN ** LAYER_CURSOR] = cursor
        for t in unroll(0, N_GKR_TREES):
            lo = evals[4 * t] + c0 * (evals[4 * t] + evals[4 * t + 1])
            hi = evals[4 * t + 2] + c0 * (evals[4 * t + 2] + evals[4 * t + 3])
            nxt[GEN ** (LAYER_VALS + t)] = lo + c1 * (lo + hi)
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN
        nxt[GEN ** LAYER_HALF] = GEN ** 0
        nxt[GEN ** LAYER_PARITY] = GEN
    # Radix-four layer k (from 1 for an even depth) sits at binary layer 2k + odd, its
    # record's index, and runs that many rounds.
    start_g = GEN ** 2 / odd_g
    for x_pair in mul_range(1, loop_bounds[g_bus_mu]):
        sq = x_pair * x_pair
        x_layer = sq * start_g
        layer = layers * x_layer ** LAYER_SLOTS
        layer_cap = fs_load(layer, LAYER_FS, 1)
        layer_rate = StackBuf(8)
        layer_sp, layer_lam, layer_cur = fs_grind_squeeze(layer_cap, layer_rate, 0, layer[GEN ** LAYER_CURSOR], tabs, GKR_COMBINER_GRIND_BITS)
        layer_vals = StackBuf(N_GKR_TREES)
        for t in unroll(0, N_GKR_TREES):
            layer_vals[t] = layer[GEN ** (LAYER_VALS + t)]
        point_row = layer[GEN ** LAYER_ROW]
        round_pos = layer[GEN ** LAYER_POS]
        nextrow = point_row * GEN ** MU_CAP
        # Round i's record keeps field k at rounds * g^(k GKR_ROUNDS_CAP + i), so a
        # round's record is one product away from the counter.
        head = rounds * round_pos
        fs_store(head, ROUND_FS, GKR_ROUNDS_CAP, layer_sp)
        head[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)] = layer_cur
        head[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)] = gkr_combine(layer_vals, layer_lam)
        # 2k rounds, or 2k + 1 when the depth is odd: eight a loop step, the state
        # between them staying in the frame, then 2 (k % 4), then the odd one.
        half = layer[GEN ** LAYER_HALF]
        parity = layer[GEN ** LAYER_PARITY]
        for x8 in mul_range(1, half):
            step = x8 ** 8
            rd = head * step
            pt = point_row * step
            round_sp = fs_load(rd, ROUND_FS, GKR_ROUNDS_CAP)
            cur = rd[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)]
            claim = rd[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)]
            for q in unroll(0, 8):
                # As in gkr_rounds.
                rate = StackBuf(8)
                c1, cur = fs_next(rate, 0, cur)
                c2, cur = fs_next(rate, 1, cur)
                c3, cur = fs_next(rate, 2, cur)
                c4, cur = fs_next(rate, 3, cur)
                round_sp, rk, cur = fs_grind_squeeze(round_sp, rate, 4, cur, tabs, ROUND5_GRIND_BITS)
                c0 = claim + pt[GEN ** q] * (c1 + c2 + c3 + c4)
                pt[GEN ** (MU_CAP + 2 + q)] = rk  # nextrow[round * g^2]
                claim = c0 + rk * (c1 + rk * (c2 + rk * (c3 + rk * c4)))
            rd_next = rd * GEN ** 8
            fs_store(rd_next, ROUND_FS, GKR_ROUNDS_CAP, round_sp)
            rd_next[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)] = cur
            rd_next[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)] = claim
        octet = half ** 8
        rem_head = head * octet
        rem_row = point_row * octet
        done = match(log(parity), range(0, 4), lambda r: gkr_rounds(rem_head, rem_row, tabs, 2 * r))
        if odd_g != 1:
            done = gkr_rounds(head * sq, point_row * sq, tabs, 1)
        tail = head * x_layer
        tail_sp = fs_load(tail, ROUND_FS, GKR_ROUNDS_CAP)
        tcur = tail[GEN ** (ROUND_CURSOR * GKR_ROUNDS_CAP)]
        evals = StackBuf(4 * N_GKR_TREES)  # the four children of each tree, in tree order
        tail_sp, rate, tcur = gkr_children(tail_sp, tcur, evals, 4)
        gkr_product_check(evals, layer_lam, tail[GEN ** (ROUND_CLAIM * GKR_ROUNDS_CAP)], 4)
        # y's grind: the last layer's coordinates are also zeta's, which the table
        # sumcheck's zerocheck reads, so its numerator doubles.
        if const(GKR_Y_GRIND_BITS == GKR_Y_LAST_GRIND_BITS):
            tail_sp, c0, tcur = fs_grind_squeeze(tail_sp, rate, (4 * N_GKR_TREES + 3) % 4 + 1, tcur, tabs, GKR_Y_GRIND_BITS)
        else:
            y_sp = StackBuf(KECCAK_STATE)
            y_cur = StackBuf(1)
            done = match(log(last_layer[g_bus_mu / x_layer]), range(0, 2), lambda last: gkr_y_grind(y_sp, y_cur, tail_sp, rate, tcur, tabs, last))  # a match needs a target
            tail_sp = y_sp
            c0 = y_sp[0]
            tcur = y_cur[0]
        no_rate = StackBuf(8)
        tail_sp, c1 = squeeze(tail_sp, no_rate, 0)
        nextrow[GEN ** 0] = c0
        nextrow[GEN ** 1] = c1
        nxt = layer * GEN ** (2 * LAYER_SLOTS)
        fs_store(nxt, LAYER_FS, 1, tail_sp)
        nxt[GEN ** LAYER_CURSOR] = tcur
        for t in unroll(0, N_GKR_TREES):
            lo = evals[4 * t] + c0 * (evals[4 * t] + evals[4 * t + 1])
            hi = evals[4 * t + 2] + c0 * (evals[4 * t + 2] + evals[4 * t + 3])
            nxt[GEN ** (LAYER_VALS + t)] = lo + c1 * (lo + hi)
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = round_pos * x_layer * GEN
        nxt[GEN ** LAYER_HALF] = half * k_mod_next[GEN ** 4 * parity]
        nxt[GEN ** LAYER_PARITY] = k_mod_next[parity]
    last = layers * g_bus_mu ** LAYER_SLOTS
    cursor = last[GEN ** LAYER_CURSOR]
    final_point_row = last[GEN ** LAYER_ROW]
    for xt in mul_range(1, g_bus_mu):
        zeta[xt] = final_point_row[xt]  # the ONE shared point
    leaves = HeapBuf(N_GKR_TREES)
    for t in unroll(0, N_GKR_TREES):
        leaves[GEN ** t] = last[GEN ** (LAYER_VALS + t)]
    return last[GEN ** LAYER_FS], last[GEN ** (LAYER_FS + 1)], last[GEN ** (LAYER_FS + 2)], last[GEN ** (LAYER_FS + 3)], last[GEN ** (LAYER_FS + 4)], cursor, leaves


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


@inline
def assert_digit(d, width: Const):
    # d = g^u with u < 2^width: three cycles, no XOR.
    if const(width == 1):
        assert log(d) < 2
    if const(width == 2):
        assert log(d) < 4
    if const(width == 3):
        assert log(d) < 8
    if const(width == 4):
        assert log(d) < 16
    return


def block_selector_tab(digits, eq_tab, g_tab, n: Const):
    # block_selector off the shared tables: per nibble, a hinted g-power digit g^u,
    # range-checked below the nibble's table size, reads its eq factor and its share
    # of g^offset. The caller pins the shares' product to the certified offset, which
    # makes every digit the offset's own (a base-16 representation is unique).
    eq = GEN ** 0
    rebuilt = GEN ** 0
    for j in unroll(0, (n + 3) // 4):
        width = 4
        if const(j == n // 4):
            width = n - 4 * j
        d = digits[GEN ** j]
        assert_digit(d, width)
        if const(j == 0):
            eq = eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt = g_tab[GEN ** (16 * j) * d]
        else:
            eq *= eq_tab[GEN ** (SEL_TAB_EQ_STRIDE * j + 2 ** width - 2) * d]
            rebuilt *= g_tab[GEN ** (16 * j) * d]
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


def verify_tables(fs0, fs1, fs2, fs3, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, g_squares, fp_w, beta, claim_pool, chi, gkr_leaves, tabs):
    # Settle the bus against the six tables, in four steps: certify each side's
    # leaf-cube tiling, decompose the sides' GKR leaf values over it, run the ONE
    # table sumcheck they all reduce to, and bind the public input. Pooled claims land
    # in claim_pool and the reduced point in `chi`; the batch's round count g^n, the
    # bytecode value (the deferred claim) and the PI point come back.
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
    kb = StackBuf(N_TABLES + 2)  # kappa_base, in the frame
    kb[0] = 1
    for t in unroll(0, N_TABLES + 1):
        kb[1 + t] = dims_g[GEN ** t]
    # A block group, a run of a side's blocks sharing one kappa source, is consecutive
    # in its side's order, so a hinted order of the groups, certified strictly
    # descending in its rank key (descending κ, then ascending first index: a side's
    # blocks share one base, so the native ascending index), places every block.
    group_side_tab = g_squares * GEN ** SIDE_TAB_AT  # group -> its side (exponent_tables)
    rank_keys = g_squares * GEN ** RANK_KEYS_AT
    group_key = HeapBuf(N_BLOCK_GROUPS)
    group_size = HeapBuf(N_BLOCK_GROUPS)
    group_base = HeapBuf(N_BLOCK_GROUPS)
    group_order = HeapBuf(N_BLOCK_GROUPS)
    hint_witness(group_order[0:N_BLOCK_GROUPS], "block_group_order")
    block_off = StackBuf(N_BLOCKS)  # g^offset per push and count block
    for cert in unroll(0, 2):
        s = COUNT_SIDE * cert  # PUSH_SIDE (0), then COUNT_SIDE (2)
        for gi in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            b0 = BLOCK_GROUP_START[gi]
            kappa_g = kb[BLOCK_KAPPA_SRC[b0]] * GEN ** BLOCK_KAPPA_ADJ[b0]
            group_key[GEN ** gi] = rank_keys[kappa_g] * INV_GEN ** b0
            group_size[GEN ** gi] = g_squares[kappa_g] ** (BLOCK_GROUP_START[gi + 1] - b0)
        g_off = GEN ** 0
        for r in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            gi = group_order[GEN ** r]
            assert log(gi) < N_BLOCK_GROUPS  # a valid group...
            group_side_tab[gi] = s           # ...of THIS side
            key = group_key[gi]
            if r != SIDE_GROUP_START[s]:
                assert log(prev_key / key * INV_GEN) < RANK_KEY_BOUND
            # write-once: a repeat collides (g_off has grown since), so the side's
            # ranks name as many distinct groups of the side as it has, omitting none
            group_base[gi] = g_off
            g_off *= group_size[gi]
            prev_key = key
        for gi in unroll(SIDE_GROUP_START[s], SIDE_GROUP_START[s + 1]):
            b0 = BLOCK_GROUP_START[gi]
            step = g_squares[kb[BLOCK_KAPPA_SRC[b0]] * GEN ** BLOCK_KAPPA_ADJ[b0]]
            block_off[b0] = group_base[GEN ** gi]
            for b in unroll(b0 + 1, BLOCK_GROUP_START[gi + 1]):
                block_off[b] = block_off[b - 1] * step

    # ---- the leaf decomposition (claims pooled; bytecode Public DEFERRED) ----
    # Reconstruct Ṽ₀(ζ) per side and assert it equals the GKR leaf value. The
    # committed-coordinate values ride the stream (observed, pooled); Index
    # coordinates use the factored index MLE; and the program's whole share of a
    # bytecode leaf is ONE evaluation of the stacked polynomial, since its slots are
    # aligned with the tuple and the weights are eq(α⃗, ·), so the share IS that
    # polynomial at (ζ_lo, α⃗) (doc sec:e2e-bc): one hinted value, exported as a
    # deferred claim, which pins it, with no per-coordinate values and no selector
    # challenge.
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
        tau_g = kb[2 + t]
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
        tau_g = kb[2 + t]
        shared_len[t] = g_bus_mu / tau_g
        assert log(shared_len[t]) < SIZE_BITS
        shared_selector_tables(shared_eq * GEN ** (t * SEL_TAB_NIBBLES * SEL_TAB_EQ_STRIDE), shared_g * GEN ** (t * SEL_TAB_NIBBLES * 16), zeta * tau_g, zeta1 * tau_g, g_squares * tau_g, shared_len[t])
    block_eq_hi = StackBuf(N_BLOCKS)         # every block's eq_hi, reused below
    block_index_mle = HeapBuf(N_BLOCKS)      # per push block with an Index coord
    # A framework coordinate's value at zeta, and a table coordinate's at the table
    # sumcheck's point (a pull one's less its push twin's), by coordinate index.
    coord_vals = StackBuf(N_COORDS)
    selector_sums = StackBuf(N_GKR_SIDES)    # per side, its blocks' eq_hi summed
    public_eqs = StackBuf(N_GKR_SIDES)       # per side, the eq_hi of its blocks with public slots
    for s in unroll(0, N_GKR_SIDES):
        selector_sum = 0
        public_eq = 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            block_has_public = 0
            kappa_g = kb[BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]
            # Every certified log is under SIZE_BITS (log_mem below COUNT_BITS, a tau
            # below N_COLUMN_LOGS), so only an adjusted one needs bounding.
            if const(BLOCK_KAPPA_SRC[b] != 0):
                if const(BLOCK_KAPPA_ADJ[b] != 0):
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
                shared = 0
                if const(BLOCK_KAPPA_SRC[b] // 2 != 0):
                    if const(BLOCK_KAPPA_ADJ[b] == 0):
                        shared = 1
                if const(shared == 1):
                    t = BLOCK_KAPPA_SRC[b] - 2
                    digits = HeapBuf(SEL_TAB_NIBBLES)
                    hint_decompose_digits_exponent(digits, block_off[b], SIZE_BITS, SEL_TAB_NIBBLES, 4, kb[2 + t])
                    len_g = shared_len[t]
                    tab_eq = shared_eq * GEN ** (t * SEL_TAB_NIBBLES * SEL_TAB_EQ_STRIDE)
                    tab_g = shared_g * GEN ** (t * SEL_TAB_NIBBLES * 16)
                    eq_hi, goff = match(log(len_g), range(0, SIZE_BITS), lambda n: block_selector_tab(digits, tab_eq, tab_g, n))
                else:
                    sel_len_g = g_bus_mu / kappa_g  # g^(mu - κ)
                    assert log(sel_len_g) < SIZE_BITS
                    offset_bits = HeapBuf(GEN ** SIZE_BITS)
                    hint_decompose_bits_exponent(offset_bits, block_off[b], SIZE_BITS)
                    sel_bits = offset_bits * kappa_g
                    zeta1_hi = zeta1 * kappa_g
                    idxc_hi = idxc_tab * kappa_g
                    eq_hi, goff = match(log(sel_len_g), range(0, SIZE_BITS), lambda n: block_selector(sel_bits, zeta1_hi, idxc_hi, n))
                assert goff == block_off[b]  # bits == offset >> κ, κ-aligned
            selector_sum += eq_hi
            block_eq_hi[b] = eq_hi
            # A TABLE's block streams no value here: the table sumcheck settles its
            # fingerprint from that table's column evaluations. Only the framework
            # blocks (boundary, memory, bytecode) still decompose.
            if BLOCK_TABLE[b] == NO_TABLE:
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                    if COORD_TYPE[ci] == COORD_KIND_CONST:
                        coord_vals[ci] = COORD_CONST[ci]
                    if COORD_TYPE[ci] == COORD_KIND_COL:
                        if COORD_FRESH[ci] == 1:
                            if COORD_FRESH_POS[ci] % 4 == 0:
                                if COORD_FRESH_POS[ci] != 0:
                                    sp = fs_perm(sp, rate, 4)
                                    rate = StackBuf(8)
                            coord_val, cursor = fs_next(rate, COORD_FRESH_POS[ci] % 4, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = coord_val
                        else:
                            coord_val = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                        coord_vals[ci] = coord_val
                    if COORD_TYPE[ci] == COORD_KIND_GCOL:
                        if COORD_FRESH[ci] == 1:
                            if COORD_FRESH_POS[ci] % 4 == 0:
                                if COORD_FRESH_POS[ci] != 0:
                                    sp = fs_perm(sp, rate, 4)
                                    rate = StackBuf(8)
                            rawv, cursor = fs_next(rate, COORD_FRESH_POS[ci] % 4, cursor)
                            claim_pool[GEN ** COORD_CLAIM_SLOT[ci]] = rawv
                        else:
                            rawv = claim_pool[GEN ** COORD_CLAIM_SLOT[ci]]
                        coord_vals[ci] = COORD_CONST[ci] * rawv
                    if COORD_TYPE[ci] == COORD_KIND_INDEX:
                        if s == PULL_SIDE:
                            coord_vals[ci] = block_index_mle[GEN ** (b - SIDE_BLOCK_START[PULL_SIDE])]
                        else:
                            coord_val = match(log(kappa_g), range(0, SIZE_BITS), lambda n: index_mle(zeta, n))
                            coord_vals[ci] = coord_val
                            if s == PUSH_SIDE:
                                block_index_mle[GEN ** b] = coord_val
                    if COORD_TYPE[ci] == COORD_KIND_PUBLIC:
                        # The public slots carry no value of their own here: their
                        # alpha-weighted sum IS bc_share, added once per block below
                        # (push and pull share zeta, so both get the same one).
                        coord_vals[ci] = 0
                        block_has_public = 1
                if const(block_has_public == 1):
                    public_eq += eq_hi
        selector_sums[s] = selector_sum
        public_eqs[s] = public_eq

    # ---- the sides' framework decomposition ----
    # Per side, what its tables' blocks owe: its GKR leaf value less the framework
    # blocks' fingerprints and the padding mass. DERIVED, not read: a transmitted
    # total would be a free value in its own check. The table sumcheck's target pins
    # it below. Pull's padding is push's (same blocks, same padding tuples), and the
    # count side reads its tuples at alpha = beta = 0.
    bus_table_total = StackBuf(N_GKR_SIDES)
    beta_1 = beta + 1
    for s in unroll(0, N_GKR_SIDES):
        acc = 0
        for b in unroll(SIDE_BLOCK_START[s], SIDE_BLOCK_START[s + 1]):
            if BLOCK_TABLE[b] == NO_TABLE:
                inner_sum = 0
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i
                    if const(COORD_TYPE[ci] != COORD_KIND_PUBLIC):
                        if s == COUNT_SIDE:
                            inner_sum += coord_vals[ci]
                        else:
                            inner_sum += fp_w[GEN ** i] * coord_vals[ci]
                if s == COUNT_SIDE:
                    acc += block_eq_hi[b] * inner_sum
                else:
                    acc += block_eq_hi[b] * (beta + inner_sum)
        if const(s != COUNT_SIDE):
            acc += public_eqs[s] * bc_share
        # The table sumcheck sums a table block's form phi over every row, padding
        # rows included, whose leaves are 1 instead: the difference, (1 - phi(p_j))
        # times the table's pad_weight, is public and joins the padding mass.
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
        acc += 1 + selector_sums[s]
        bus_table_total[s] = acc + gkr_leaves[GEN ** s]
    claim_idx = N_BUS_CLAIMS  # the table and public-input claims follow the deduped bus claims

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
        tau_g = kb[2 + t]
        assert log(g_zc_n / tau_g) < COUNT_BITS
        zc_is_a_tau *= g_zc_n + tau_g
    assert zc_is_a_tau == 0
    # n <= mu, the `Error::Truncated` of constraints.rs. Every table pushes at
    # kappa = tau, so it holds structurally, but zc_peq below reads zeta[..n] and
    # zeta only holds mu coords: unwritten heap there is prover-chosen.
    assert log(g_bus_mu / g_zc_n) < COUNT_BITS
    # xi, after its grind, the framework blocks' fresh values waiting: the batch is of
    # degree N_ETA_POWS - 1 in it.
    sp, zc_xi, cursor = fs_grind_squeeze(sp, rate, (N_FRESH + 3) % 4 + 1, cursor, tabs, XI_GRIND_BITS)
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
        ncur, nclaim, rk = sumcheck_round4(rd, rd[GEN ** ROUND_CURSOR], rd[GEN ** ROUND_CLAIM], tabs)
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
    # The column evaluations stay where the stream holds them, N_COL_EVALS
    # consecutive words that fs_next bound: the pool's slots from N_BUS_CLAIMS on are
    # read there rather than copied.
    col_eval_words = cursor
    for t in unroll(0, N_TABLES):
        tau_g = kb[2 + t]
        col_evals = StackBuf(TABLE_COLS_CAP)
        for pos in unroll(TABLE_COL_BASE[t], TABLE_COL_BASE[t] + N_TABLE_COLS[t]):
            if pos % 4 == 0:
                if pos != 0:
                    sp = fs_perm(sp, rate, 4)
                    rate = StackBuf(8)
            e, cursor = fs_next(rate, pos % 4, cursor)
            col_evals[pos - TABLE_COL_BASE[t]] = e
            claim_idx += 1
        # The table's AIR constraint at the final point (col_evals is indexed by
        # local column index; the formulas mirror tables.rs Table::constraint). Every
        # value relation now rides the bus as a degree-2 coordinate, so only JUMP's
        # is-nonzero indicator is left with an identity of its own.
        constraint_eval = 0
        if t == TABLE_JUMP:
            # `b = c*w` and `c*(b+1) = 0`. The condition is K-valued, its memory read
            # carrying literal zeros above the low limb, so both identities are
            # single-lane (tables.rs JumpTable::constraint). Local columns: v_cond at 5, w at
            # 12, the indicator b at 13.
            c = col_evals[5]
            b = col_evals[13]
            constraint_eval = zc_xi_pows[ETA_OFFSET[t] + 0] * (b + c * col_evals[12])
            constraint_eval += zc_xi_pows[ETA_OFFSET[t] + 1] * (c * (b + 1))
        # The table's bus coordinates, evaluated at the SAME column evaluations, each
        # the sum of its terms over this table's column evaluations (a product term, an
        # address or an arithmetic result, is degree 2, which the batch's round
        # polynomial already allows); a pull coordinate as its difference from its push
        # twin's, where the two differ. This is what replaces opening those columns at ζ.
        for b in unroll(0, N_BLOCKS):
            if BLOCK_TABLE[b] == t:
                for i in unroll(0, BLOCK_COORD_COUNT[b]):
                    ci = BLOCK_COORD_OFF[b] + i  # a compile-time index, so `ci` costs nothing
                    if const(BLOCK_SIDE[b] == PULL_SIDE):
                        n_terms = COORD_DIFF_COUNT[ci]
                        first = COORD_DIFF_OFF[ci]
                    else:
                        n_terms = COORD_TERM_COUNT[ci]
                        first = COORD_TERM_OFF[ci]
                    if const(n_terms != 0):
                        cv = 0
                        for j in unroll(0, n_terms):
                            tj = first + j
                            if TERM_TYPE[tj] == COORD_KIND_CONST:
                                cv += TERM_CONST[tj]
                            if TERM_TYPE[tj] == COORD_KIND_COL:
                                cv += col_evals[TERM_COL_A[tj]]
                            if TERM_TYPE[tj] == COORD_KIND_GCOL:
                                cv += TERM_CONST[tj] * col_evals[TERM_COL_A[tj]]
                            if TERM_TYPE[tj] == COORD_KIND_PROD:
                                cv += TERM_CONST[tj] * (col_evals[TERM_COL_A[tj]] * col_evals[TERM_COL_B[tj]])
                        coord_vals[ci] = cv
        # Its forms, one a side: Σ_b eq_hi(b) · (β + Σ_i w(i) · coord_i). A pull
        # block shares its push twin's eq_hi, so a pull form is push's plus the
        # coordinates where the two differ.
        for sd in unroll(0, N_GKR_SIDES):
            form = 0
            for b in unroll(SIDE_BLOCK_START[sd], SIDE_BLOCK_START[sd + 1]):
                if BLOCK_TABLE[b] == t:
                    inner = 0
                    for i in unroll(0, BLOCK_COORD_COUNT[b]):
                        ci = BLOCK_COORD_OFF[b] + i
                        if const(sd == PULL_SIDE):
                            n_terms = COORD_DIFF_COUNT[ci]
                        else:
                            n_terms = COORD_TERM_COUNT[ci]
                        if const(n_terms != 0):
                            if sd == COUNT_SIDE:
                                inner += coord_vals[ci]
                            else:
                                inner += fp_w[GEN ** i] * coord_vals[ci]
                    if sd == PUSH_SIDE:
                        form += block_eq_hi[b] * (beta + inner)
                    else:
                        form += block_eq_hi[b] * inner
            if const(sd == PUSH_SIDE):
                push_form = form
            if const(sd == PULL_SIDE):
                form = push_form + form
            constraint_eval += zc_xi_pows[ETA_FORM_BASE + sd] * form
        air_acc += zc_cprod[g_zc_n / tau_g] * zc_peq[tau_g] * constraint_eval  # cprod[n - tau] * peq[tau]
    assert air_acc == claim

    # ---- public-input binding claim: one per MEM limb, read off no stream ----
    # The VM's bind_pi_claim claims each committed MEM limb at [rm, 0..] equals
    # that limb's line through the public words, lo_0 + rm*(lo_0 + lo_1) and so
    # on, which the statement alone determines. split_limbs binds each word's
    # limbs (doc sec:e2e-pi).
    sp, rm = squeeze(sp, rate, (N_COL_EVALS + 3) % 4 + 1)
    lo_0, hi_0 = split_limbs(pi_0)
    lo_1, hi_1 = split_limbs(pi_1)
    claim_pool[GEN ** claim_idx] = lo_0 + rm * (lo_0 + lo_1)
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = hi_0 + rm * (hi_0 + hi_1)
    claim_idx += 1
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, g_zc_n, bc_share, rm, col_eval_words


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
    # As products, (1 + a)(1 + b) + ab, a(1 + b) and (1 + a)b, trading XORs for MULs;
    # b's 1 + b_t is the local sumcheck's, already in the frame.
    for t in unroll(0, KECCAK_Z_BITS):
        a_t = a[GEN ** t]
        b_t = b[GEN ** t]
        a_t1 = 1 + a_t
        b_t1 = 1 + b_t
        if t == 0:
            lo0[0] = a_t1 * b_t1 + a_t * b_t
            lo0[1] = a_t * b_t1
            lo1[1] = a_t1 * b_t
        elif t == 3:
            hi0[0] = a_t1 * b_t1 + a_t * b_t
            hi0[1] = a_t * b_t1
            hi1[1] = a_t1 * b_t
        elif const(t + 1 == KECCAK_Z_BITS):
            w_eq[t] = a_t1 * b_t1 + a_t * b_t
            w_sum[t] = a_t + b_t
        else:
            w_eq[t] = a_t1 * b_t1 + a_t * b_t
            w_up[t] = a_t * b_t1
            w_down[t] = a_t1 * b_t
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
def fold_node(src, dst, a_t, a_t1, p: Const, b: Const, t: Const):
    # x0 + a (x0 + x1) as (1 + a) x0 + a x1: a MUL for an XOR, the scarcer row.
    n = 2 ** (KECCAK_Z_BITS - t)
    for k in unroll(0, n // 2):
        x0 = src[p * n + (2 * k + (n - 1) * b) % n]
        x1 = src[p * n + (2 * k + 1 + (n - 1) * b) % n]
        dst[(p + 2 ** t * b) * (n // 2) + k] = a_t1 * x0 + a_t * x1
    return


@inline
def fold_shifts(src, dst, a_t, t: Const):
    # One level of sum_w eq(a, w) V[w - r] for every used r at once, LSB first: node
    # p of depth t is the vector for the residue p of r mod 2^t, 2^(6 - t) cells at
    # p 2^(6 - t). Folding bit t splits it by bit t of r, b: V[w - r] pairs the
    # parent's cells 2k - b and 2k + 1 - b.
    a_t1 = 1 + a_t
    for p in unroll(0, 2 ** t):
        for b in unroll(0, 2):
            if const(t + 1 == KECCAK_Z_BITS):
                if KECCAK_SHIFT_USED[p + 2 ** t * b] == 1:
                    fold_node(src, dst, a_t, a_t1, p, b, t)
            else:
                fold_node(src, dst, a_t, a_t1, p, b, t)
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


@inline
def slice_weight(slices, top, top1, z: Const):
    # eq(local, z) from the five-coordinate tree `slices` and the top coordinate.
    if const(z // 32 == 1):
        w = slices[2 ** (KECCAK_Z_BITS - 1) - 2 + z % 32] * top
    else:
        w = slices[2 ** (KECCAK_Z_BITS - 1) - 2 + z % 32] * top1
    return w


def keccak_layer(fs0, fs1, fs2, fs3, fs4, p0, p1, cursor, y_g, step_g, rem_g, claim, out, iota, tabs, first: Const):
    # One layer (verifier::keccak::verify_layer): the claim on the states after
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
    # Each product coefficient's reader, a straight line of sums over the instance weights.
    readers = StackBuf(KECCAK_PROJ_CELLS)
    for i in unroll(0, KECCAK_PACK):
        readers[i] = claim[GEN ** (KC_MU + i)]
    for t in unroll(0, len(KECCAK_PROJ_A)):
        readers[KECCAK_PACK + t] = readers[KECCAK_PROJ_A[t]] + readers[KECCAK_PROJ_B[t]]
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
        projected += readers[KECCAK_PROJ_OUT[pos - first]] * coefficient
    cursor = cursor * GEN ** KECCAK_PROD_BITS
    assert projected + iota * claim[GEN ** KC_KAPPA] == claim[GEN ** KC_VALUE]
    # At a random point a pack is one field element, after a grind: the polynomial has
    # degree KECCAK_PROD_BITS - 1.
    sp, s, cursor = fs_grind_squeeze(sp, rate, (first + KECCAK_PROD_BITS + 3) % 4 + 1, cursor, tabs, KECCAK_S_GRIND_BITS)
    # mu[i] = emb_i(s), each embedding a product of small irreducible factors.
    s_powers = StackBuf(KECCAK_FAC_DEG)
    s_powers[0] = 1
    s_powers[1] = s
    for b in unroll(2, KECCAK_FAC_DEG):
        s_powers[b] = s_powers[b - 1] * s
    factors = StackBuf(KECCAK_EMB_CELLS)
    for f in unroll(0, KECCAK_FAC_N):
        acc = 0
        for t in unroll(KECCAK_FAC_START[f], KECCAK_FAC_START[f + 1]):
            acc += s_powers[KECCAK_FAC_IDX[t]]
        factors[f] = acc
    for t in unroll(0, len(KECCAK_EMB_A)):
        factors[KECCAK_FAC_N + t] = factors[KECCAK_EMB_A[t]] * factors[KECCAK_EMB_B[t]]
    kappa = 0  # the sum of the weights
    for i in unroll(0, KECCAK_PACK):
        out[GEN ** (KC_MU + i)] = factors[KECCAK_EMB_OUT[i]]
        kappa += factors[KECCAK_EMB_OUT[i]]
    out[GEN ** KC_KAPPA] = kappa
    value = product[KECCAK_PROD_BITS - 1]
    for k in unroll(1, KECCAK_PROD_BITS):
        value = value * s + product[KECCAK_PROD_BITS - 1 - k]
    # The pack and the segment, a runtime number of rounds: KR_STEP step_g, KR_STEP a
    # loop step, then rem_g, one a loop step (a loop rather than an unrolled arm per remainder,
    # whose shared frame would grow every layer's).
    prev_point = claim[GEN ** KC_POINT]
    point = HeapBuf(y_g)
    rounds = HeapBuf(KR_SLOTS * KR_CAP)
    fs_store(rounds, KR_FS, KR_CAP, sp)
    rounds[GEN ** (KR_CURSOR * KR_CAP)] = cursor
    rounds[GEN ** (KR_CLAIM * KR_CAP)] = value
    rounds[GEN ** (KR_SCALE * KR_CAP)] = 1
    for xs in mul_range(1, step_g):
        rd = rounds * xs
        pp = prev_point * xs ** KR_STEP
        pt = point * xs ** KR_STEP
        round_sp = fs_load(rd, KR_FS, KR_CAP)
        cur_i = rd[GEN ** (KR_CURSOR * KR_CAP)]
        run = rd[GEN ** (KR_CLAIM * KR_CAP)]
        scale = rd[GEN ** (KR_SCALE * KR_CAP)]
        for q in unroll(0, KR_STEP):
            # q has degree two with the eq factor pulled out, and the prover sends its
            # coefficients c1 and c2 (g_1, g_2), c0 being fixed by the claim. With r the
            # round's coordinate and c its challenge, q(c) = claim + (r + c) c1 +
            # (r + c^2) c2, and the next claim is (1 + r + c) q(c). The round grinds for
            # degree three, the eq factor included.
            r_eq = pp[GEN ** q]
            rate = StackBuf(8)
            g_1, cur_i = fs_next(rate, 0, cur_i)
            g_2, cur_i = fs_next(rate, 1, cur_i)
            round_sp, challenge, cur_i = fs_grind_squeeze(round_sp, rate, 2, cur_i, tabs, ROUND3_GRIND_BITS)
            pt[GEN ** q] = challenge
            gap = r_eq + challenge
            eq_factor = 1 + gap
            run = eq_factor * (run + gap * g_1 + (r_eq + challenge * challenge) * g_2)
            scale = scale * eq_factor
        nxt = rd * GEN
        fs_store(nxt, KR_FS, KR_CAP, round_sp)
        nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur_i
        nxt[GEN ** (KR_CLAIM * KR_CAP)] = run
        nxt[GEN ** (KR_SCALE * KR_CAP)] = scale
    rem_rounds = rounds * step_g
    rem_prev = prev_point * step_g ** KR_STEP
    rem_point = point * step_g ** KR_STEP
    for x1 in mul_range(1, rem_g):
        rd = rem_rounds * x1
        r_eq = rem_prev[x1]
        round_sp = fs_load(rd, KR_FS, KR_CAP)
        cur_i = rd[GEN ** (KR_CURSOR * KR_CAP)]
        rate = StackBuf(8)
        g_1, cur_i = fs_next(rate, 0, cur_i)
        g_2, cur_i = fs_next(rate, 1, cur_i)
        round_sp, challenge, cur_i = fs_grind_squeeze(round_sp, rate, 2, cur_i, tabs, ROUND3_GRIND_BITS)
        rem_point[x1] = challenge
        gap = r_eq + challenge
        eq_factor = 1 + gap
        nxt = rd * GEN
        fs_store(nxt, KR_FS, KR_CAP, round_sp)
        nxt[GEN ** (KR_CURSOR * KR_CAP)] = cur_i
        nxt[GEN ** (KR_CLAIM * KR_CAP)] = eq_factor * (rd[GEN ** (KR_CLAIM * KR_CAP)] + gap * g_1 + (r_eq + challenge * challenge) * g_2)
        nxt[GEN ** (KR_SCALE * KR_CAP)] = rd[GEN ** (KR_SCALE * KR_CAP)] * eq_factor
    last = rem_rounds * rem_g
    sp = fs_load(last, KR_FS, KR_CAP)
    cursor = last[GEN ** (KR_CURSOR * KR_CAP)]
    value = last[GEN ** (KR_CLAIM * KR_CAP)]
    scale = last[GEN ** (KR_SCALE * KR_CAP)]
    # The bit position: degree three, the weights being one more multilinear factor.
    local = HeapBuf(KECCAK_LOCAL_BITS)
    for i in unroll(0, KECCAK_LOCAL_BITS):
        rate = StackBuf(8)
        c0, cursor = fs_next(rate, 0, cursor)
        c2, cursor = fs_next(rate, 1, cursor)
        c3, cursor = fs_next(rate, 2, cursor)
        sp, challenge, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, ROUND3_GRIND_BITS)
        local[GEN ** i] = challenge
        # c1 = value + c2 + c3, so h(c) = c0 + c (value + (1 + c) (c2 + (1 + c) c3)).
        challenge1 = 1 + challenge
        value = c0 + challenge * (value + challenge1 * (c2 + challenge1 * c3))
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
    assert scale * weight_at_local[0] * (kappa * t0 + (kappa + t1) * t2) == value
    # t[k] = sum_j eq[j] T[j + k]: one claim on the state before chi, quadratic in beta.
    sp, beta, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, KECCAK_BETA_GRIND_BITS)
    out[GEN ** KC_VALUE] = t0 + beta * (t1 + beta * t2)
    out[GEN ** KC_POINT] = point
    out[GEN ** KC_LOCAL] = local
    lanes = HeapBuf(KECCAK_LANES)
    for y in unroll(0, 5):
        for x in unroll(0, 5):
            lanes[GEN ** (x + 5 * y)] = f_lanes[LANE_OFF + x + 5 * y] + beta * (f_lanes[LANE_OFF + (x + 4) % 5 + 5 * y] + beta * f_lanes[LANE_OFF + (x + 3) % 5 + 5 * y])
    out[GEN ** KC_LANES] = lanes
    # The next layer's iota term: for every i, the new claim's weight on slice 2^i - 1
    # of lane 0, through the linear layer's transpose, from its lane and slice weights.
    # The slice weights are an eq tree on the low five coordinates, times the top
    # one's factor where a weight is read.
    slices = StackBuf(2 ** KECCAK_Z_BITS - 2)
    eqtree_frame(local, slices, KECCAK_Z_BITS - 1, 2 ** (KECCAK_Z_BITS - 1))
    top = local[GEN ** (KECCAK_Z_BITS - 1)]
    top1 = 1 + top
    flips = HeapBuf(KECCAK_IOTA_BITS)
    for i in unroll(0, KECCAK_IOTA_BITS):
        flipped = lanes[GEN ** KECCAK_PI[0]] * slice_weight(slices, top, top1, (2 ** i - 1 + KECCAK_RHO[0]) % 64)
        for y in unroll(0, 5):
            flipped += lanes[GEN ** KECCAK_PI[1 + 5 * y]] * slice_weight(slices, top, top1, (2 ** i - 1 + KECCAK_RHO[1 + 5 * y]) % 64)
            flipped += lanes[GEN ** KECCAK_PI[4 + 5 * y]] * slice_weight(slices, top, top1, (2 ** i + KECCAK_RHO[4 + 5 * y]) % 64)
        flips[GEN ** i] = flipped
    out[GEN ** KC_FLIPS] = flips
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor


def keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, p0, p1, cursor, value, point, tabs, n: Const, k0: Const):
    # n rounds of a degree-2 sumcheck with no equality factor, each grinding for its
    # degree. With k0 = 1 one scalar already waits in the sponge, rate cells p0 and p1,
    # and the first round's words join it.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    for i in unroll(0, n):
        rate = StackBuf(8)
        if i == 0:
            if k0 == 1:
                rate[0] = p0
                rate[1] = p1
                c0, cursor = fs_next(rate, 1, cursor)
                c2, cursor = fs_next(rate, 2, cursor)
                sp, challenge, cursor = fs_grind_squeeze(sp, rate, 3, cursor, tabs, ROUND2_GRIND_BITS)
            else:
                c0, cursor = fs_next(rate, 0, cursor)
                c2, cursor = fs_next(rate, 1, cursor)
                sp, challenge, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, ROUND2_GRIND_BITS)
        else:
            c0, cursor = fs_next(rate, 0, cursor)
            c2, cursor = fs_next(rate, 1, cursor)
            sp, challenge, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, ROUND2_GRIND_BITS)
        c1 = value + c2
        point[GEN ** i] = challenge
        value = c0 + challenge * (c1 + challenge * c2)
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


def verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, tau_g, chi, output_lanes, z_vals, slices, tabs):
    # KECCAK validity (verifier::keccak::verify_keccak): a random claim on every segment's output,
    # KECCAK_DEPTH layers down to the committed inputs, every segment at once. The
    # last segment's output is the permutation's: the table's claims on its output
    # lanes, `output_lanes`, at the table's point chi[..tau], give that part of the
    # claim, and the prover sends the committed outputs' part. It leaves two
    # openings of q_keccak, at the two points written to `z_vals` (tau +
    # QKECCAK_SLOT_LOG coordinates each, QKECCAK_VARS_CAP apart): the committed
    # outputs as words at the first, returned, and the 64 `slices` at the second.
    # tau >= FLOORS[TABLE_KECCAK] is certified, so the pack count is a real count. It
    # also draws the ring-switching map's first challenge, which the last slices wait
    # for, and returns it.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    no_rate = StackBuf(8)
    pack_g = tau_g * INV_GEN ** KECCAK_PACK_LOG
    y_g = pack_g * GEN ** KECCAK_SEG_LOG
    # A layer runs y = log(y_g) rounds KR_STEP at a time: y_g = step_g^KR_STEP rem_g,
    # from y's bits, pinned boolean and tied back (y = tau - 3 < 2^5 as tau < COUNT_BITS).
    y_bits = StackBuf(5)
    hint_decompose_bits_exponent(y_bits, y_g, 5)
    for j in unroll(0, 5):
        bit = y_bits[j]
        y_bits[j] = bit * bit
    step_g = GEN ** 0
    for j in unroll(KR_STEP_LOG, 5):
        step_g *= 1 + y_bits[j] * (1 + GEN ** (2 ** (j - KR_STEP_LOG)))
    rem_g = GEN ** 0
    for j in unroll(0, KR_STEP_LOG):
        rem_g *= 1 + y_bits[j] * (1 + GEN ** (2 ** j))
    assert step_g ** KR_STEP * rem_g == y_g
    out_point = z_vals
    in_point = z_vals * GEN ** QKECCAK_VARS_CAP
    for i in unroll(0, KECCAK_PACK_LOG):
        out_point[GEN ** i] = chi[GEN ** i]
    # The claim's point: chi's pack coordinates, then a fresh segment.
    point = HeapBuf(y_g)
    chi_pack = chi * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        point[xt] = chi_pack[xt]
    # One message, the segment then the lane, after its grind: the first claim is
    # multilinear in them.
    segment = point * pack_g
    sp, r, cursor = fs_grind_squeeze(sp, no_rate, 0, cursor, tabs, KECCAK_SEG_GRIND_BITS)
    segment[GEN ** 0] = r
    for i in unroll(1, KECCAK_SEG_LOG):
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
        segment_tree = StackBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
        eqtree_frame(claim_point * pack_g, segment_tree, KECCAK_SEG_LOG, 2 ** KECCAK_SEG_LOG)
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
                    claim_flips = claim[GEN ** KC_FLIPS]
                    flips[i] = claim_flips[GEN ** i]
        iota = 0
        for m in unroll(0, KECCAK_SEGMENTS):
            flipped = 0
            for t in unroll(KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m], KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m + 1]):
                flipped += flips[KECCAK_IOTA_IDX[t]]
            iota += segment_tree[2 ** KECCAK_SEG_LOG - 2 + m] * flipped
        if step == 0:
            fs0, fs1, fs2, fs3, fs4, cursor = keccak_layer(fs0, fs1, fs2, fs3, fs4, value_rate[0], value_rate[1], cursor, y_g, step_g, rem_g, claim, claim * GEN ** KC_SIZE, iota, tabs, 1)
        else:
            fs0, fs1, fs2, fs3, fs4, cursor = keccak_layer(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, y_g, step_g, rem_g, claim, claim * GEN ** KC_SIZE, iota, tabs, 0)

    # ---- the outputs, whose instance weights are an eq already ----
    # Their position weights are a word's, so the 64 slices are only needed as
    # the word they add up to: q_keccak itself at the point.
    out_slot = out_point * tau_g
    fs0, fs1, fs2, fs3, fs4, cursor, out_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, value, out_slot, tabs, QKECCAK_SLOT_LOG, 0)
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
    fs0, fs1, fs2, fs3, fs4, cursor, low_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, word_rate[0], word_rate[1], cursor, last[GEN ** KC_VALUE], in_point, tabs, KECCAK_PACK_LOG, 1)
    low_tree = HeapBuf(2 ** (KECCAK_PACK_LOG + 1) - 2)
    eqtree(in_point, low_tree, KECCAK_PACK_LOG)
    mu_at_low = 0
    for i in unroll(0, KECCAK_PACK):
        mu_at_low += low_tree[GEN ** (2 ** KECCAK_PACK_LOG - 2 + i)] * last[GEN ** (KC_MU + i)]
    in_slot = in_point * tau_g
    fs0, fs1, fs2, fs3, fs4, cursor, in_value = keccak_plain_rounds(fs0, fs1, fs2, fs3, fs4, 0, 0, cursor, low_value, in_slot, tabs, QKECCAK_SLOT_LOG, 0)
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    for z in unroll(0, BASE_FIELD_BITS):
        if z % 4 == 0:
            if z != 0:
                sp = fs_perm(sp, rate, 4)
                rate = StackBuf(8)
        w, cursor = fs_next(rate, z % 4, cursor)
        slices[GEN ** z] = w
    sp = fs_perm(sp, rate, 4)
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
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, word


@inline
def ring_psi(out, r: Const, v, g):
    # out[r] = Psi(v) = sum_b g_b v^(2^b), the inner stage: 7 squarings and 8 products.
    psi = g[0] * v
    for b in unroll(1, RING_MAP_WIDTH - 1):
        v = v * v
        psi += g[b] * v
    v = v * v
    out[r] = psi + g[RING_MAP_WIDTH - 1] * v
    return


def ring_switch_target(slices, map_challenges):
    # T = sum_i x^i Phi(s_i) = sum_p f_p (sum_i z_p^i Psi(s_i))^(2^(8p)), z_p = x^(2^(64 - 8p))
    # in K, so a slice takes Psi alone. The eight sums run Horner over the slices from
    # the bottom, RS_CHUNK an iteration, in w_p = 1/z_p: they come out as
    # sum_i w_p^(63 - i) Psi(s_i), and the final x^63 = (z_p^63)^(2^(8p)) restores them all.
    rs_chain = HeapBuf((BASE_FIELD_BITS // RS_CHUNK + 1) * RING_MAP_WIDTH)
    for p in unroll(0, RING_MAP_WIDTH):
        rs_chain[GEN ** p] = 0
    for x_round in mul_range(1, GEN ** (BASE_FIELD_BITS // RS_CHUNK)):
        g = StackBuf(RING_MAP_WIDTH)  # read once an iteration, not once a row
        for b in unroll(0, RING_MAP_WIDTH):
            g[b] = map_challenges[GEN ** (RING_MAP_WIDTH + b)]
        rows = slices * x_round ** RS_CHUNK
        psi = StackBuf(RS_CHUNK)
        for r in unroll(0, RS_CHUNK):
            ring_psi(psi, r, rows[GEN ** r], g)
        row = rs_chain * x_round ** RING_MAP_WIDTH
        for p in unroll(0, RING_MAP_WIDTH):
            acc = row[GEN ** p]
            for r in unroll(0, RS_CHUNK):
                acc = acc * RING_W[p] + psi[r]
            row[GEN ** (RING_MAP_WIDTH + p)] = acc
    sums = rs_chain * (GEN ** (BASE_FIELD_BITS // RS_CHUNK)) ** RING_MAP_WIDTH
    total = map_challenges[GEN ** 0] * sums[GEN ** 0]
    for p in unroll(1, RING_MAP_WIDTH):
        h = sums[GEN ** p]
        for t in unroll(0, RING_MAP_WIDTH * p):
            h = h * h
        total += map_challenges[GEN ** p] * h
    return total * GEN ** (BASE_FIELD_BITS - 1)


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
    # Certify the native order (descending kappa, then ascending column index) group
    # by group: a column group, a run of columns sharing one kappa source, is
    # consecutive in it, so a hinted order of the groups, certified strictly
    # descending in its rank key, places every column. Returns g^(sum 2^kappa) and
    # each column's g^offset.
    kb = StackBuf(N_TABLES + 2)
    for i in unroll(0, N_TABLES + 2):
        kb[i] = kappa_base[GEN ** i]
    rank_keys = g_squares * GEN ** RANK_KEYS_AT
    group_key = HeapBuf(N_COL_GROUPS)
    group_size = HeapBuf(N_COL_GROUPS)
    for gi in unroll(0, N_COL_GROUPS):
        c0 = COL_GROUP_START[gi]
        kappa_g = kb[COL_KAPPA_SRC[c0]] * GEN ** COL_KAPPA_ADJ[c0]
        # g_squares spans SIZE_BITS, and every kappa is under it: a certified log
        # <= 32 (log_mem or a tau), the baked bytecode log, or q_keccak's tau_5 + QKECCAK_SLOT_LOG.
        assert log(kappa_g) < SIZE_BITS
        # Descending kappa, then the group's first (compact, native-order) index ascending.
        group_key[GEN ** gi] = rank_keys[kappa_g] * INV_GEN ** c0
        group_size[GEN ** gi] = g_squares[kappa_g] ** (COL_GROUP_START[gi + 1] - c0)
    group_order = HeapBuf(N_COL_GROUPS)
    hint_witness(group_order[0:N_COL_GROUPS], "col_group_order")
    group_base = HeapBuf(N_COL_GROUPS)
    g_total = GEN ** 0
    for rank in unroll(0, N_COL_GROUPS):
        gi = group_order[GEN ** rank]
        assert log(gi) < N_COL_GROUPS
        key = group_key[gi]
        # A negative step wraps around the order of GEN and cannot pass this check.
        if rank != 0:
            assert log(prev_key / key * INV_GEN) < RANK_KEY_BOUND
        group_base[gi] = g_total  # write-once: a repeated group collides
        g_total *= group_size[gi]
        prev_key = key
    col_off_g = HeapBuf(N_COMMITTED_COLS)
    for gi in unroll(0, N_COL_GROUPS):
        c0 = COL_GROUP_START[gi]
        step = g_squares[kb[COL_KAPPA_SRC[c0]] * GEN ** COL_KAPPA_ADJ[c0]]
        off = group_base[GEN ** gi]
        for c in unroll(c0, COL_GROUP_START[gi + 1]):
            col_off_g[GEN ** c] = off
            if const(c + 1 != COL_GROUP_START[gi + 1]):
                off *= step
    return g_total, col_off_g


def column_selector(offset, sel_eq, sel_g, kappa: Const):
    # The column's selector at the complete opening point, from hinted g-power digits
    # of its offset's nibbles at and above kappa // 4, each range-checked below 16.
    # Pinning their weighted product to the certified offset makes them its own
    # nibbles (a base-16 representation is unique), and that offset is 2^kappa-aligned
    # (certify_placement orders kappa descending), so the lowest digit, kappa's own
    # nibble, is a multiple of 2^(4 - width): the strided level-width table holds it.
    # Both offset and point are zero above m, so extending to 4 * SEL_NIBBLES adds
    # only factors eq(0, 0) = 1.
    digits = StackBuf(SEL_NIBBLES)
    hint_decompose_digits_exponent(digits, offset, 4 * SEL_NIBBLES, SEL_NIBBLES - kappa // 4, 4, 4 * (kappa // 4))
    if const(kappa // 4 == SEL_NIBBLES):
        selector = GEN ** 0
        rebuilt = GEN ** 0
    for j in unroll(kappa // 4, SEL_NIBBLES):
        width = 4
        if const(j == kappa // 4):
            width = 4 * j + 4 - kappa
        d = digits[j - kappa // 4]
        assert log(d) < 16
        if const(j == kappa // 4):
            selector = sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d]
            rebuilt = sel_g[GEN ** (16 * j) * d]
        else:
            selector *= sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * (width - 1)) * d]
            rebuilt *= sel_g[GEN ** (16 * j) * d]
    assert rebuilt == offset
    return selector


def selector_tables(point, point1):
    # Per nibble j of the selector bits, the eq tables over its top 1..4 coordinates,
    # the level-w one at 16 (w - 1), strided: entry u, a multiple of 2^(4 - w), holds
    # the eq of bit t of u against coordinate 4j + t for t >= 4 - w.
    sel_eq = HeapBuf(SEL_NIBBLES * SEL_EQ_STRIDE)
    for j in unroll(0, SEL_NIBBLES):
        levels = StackBuf(64)
        levels[0] = point1[GEN ** (4 * j + 3)]
        levels[8] = point[GEN ** (4 * j + 3)]
        for w in unroll(1, 4):
            r = point[GEN ** (4 * j + 3 - w)]
            r1 = point1[GEN ** (4 * j + 3 - w)]
            for i in unroll(0, 2 ** w):
                e = i * 2 ** (4 - w)
                levels[16 * w + e] = levels[16 * (w - 1) + e] * r1
                levels[16 * w + e + 2 ** (3 - w)] = levels[16 * (w - 1) + e] * r
        for w in unroll(0, 4):
            for i in unroll(0, 2 ** (w + 1)):
                e = i * 2 ** (3 - w)
                sel_eq[GEN ** (SEL_EQ_STRIDE * j + 16 * w + e)] = levels[16 * w + e]
    return sel_eq


def check_opening_terminal(g_squares, zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_keccak_g, kappa_base, lam_cl, col_offsets, z_vals, c_table, point, point1, inner_total, yr_at_tail, sumcheck_target, ood_z, gmv):
    # Evaluate each transparent weight at the complete point in witness order.
    # A claim is its low point followed by the certified column's selector bits;
    # a q_keccak lane puts its slot's bits between the two.
    # point1 = 1 + point holds each coordinate's eq factor against a zero bit.
    zeta_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(zeta_eq_chain, 1, zeta, point1, g_bus_mu)
    chi_eq_chain = HeapBuf(SIZE_BITS + 1)
    eq_prefix_chain(chi_eq_chain, 1, chi, point1, g_zc_n)
    slot_point = point * tau_keccak_g
    slot_point1 = point1 * tau_keccak_g
    pi_chain = HeapBuf(SIZE_BITS + 1)
    pi_chain[GEN ** 0] = 1
    pi_chain[GEN ** 1] = rm + point1[GEN ** 0]
    for xk in mul_range(GEN, g_log_mem):
        pi_chain[xk * GEN] = pi_chain[xk] * point1[xk]
    pi_eq = pi_chain[g_log_mem]

    # Every low dimension here is a certified log at a baked kappa source, as
    # certify_placement derives the columns'.
    kb = StackBuf(N_TABLES + 2)
    for i in unroll(0, N_TABLES + 2):
        kb[i] = kappa_base[GEN ** i]
    sel_eq = selector_tables(point, point1)
    sel_g = g_squares * GEN ** SIZE_BITS  # exponent_tables' constant nibble shares
    selectors = StackBuf(N_COMMITTED_COLS)
    for c in unroll(0, N_COMMITTED_COLS):
        offset = col_offsets[GEN ** c]
        kappa_g = kb[COL_KAPPA_SRC[c]] * GEN ** COL_KAPPA_ADJ[c]
        selectors[c] = match(log(kappa_g), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, sel_eq, sel_g, kappa))

    inner_sum = inner_total
    lam_pow = lam_cl  # the pool's powers, as verify_sub batched it
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] != POINT_BUF_KECCAK_OUT:
            col = CLAIM_COMMITTED_COL[j]
            cplen_g = kb[CLAIM_KAPPA_SRC[j]] * GEN ** CLAIM_KAPPA_ADJ[j]
            nlow_adj = CLAIM_KAPPA_ADJ[j]
            if CLAIM_POINT_BUF[j] == POINT_BUF_PI:
                low_eq = pi_eq
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
                nlow_adj = CLAIM_KAPPA_ADJ[j] + QKECCAK_SLOT_LOG
            # The claim's low dimension is its column's kappa: by construction when
            # the two share a kappa source, else checked.
            if const(CLAIM_KAPPA_SRC[j] != COL_KAPPA_SRC[col]):
                assert kb[CLAIM_KAPPA_SRC[j]] * GEN ** nlow_adj == kb[COL_KAPPA_SRC[col]] * GEN ** COL_KAPPA_ADJ[col]
            else:
                if const(nlow_adj != COL_KAPPA_ADJ[col]):
                    assert kb[CLAIM_KAPPA_SRC[j]] * GEN ** nlow_adj == kb[COL_KAPPA_SRC[col]] * GEN ** COL_KAPPA_ADJ[col]
            inner_sum += lam_pow * low_eq * selectors[col]
            lam_pow *= lam_cl
    lam_out = lam_pow

    # The Keccak reduction's two claims on q_keccak, each over the whole column:
    # the ring-switched one leads the batch at lam_cl^0, the plain one closes it.
    # A lane claim's low point is tau_keccak long, the kappa check above holding it
    # to this column.
    qkeccakv_g = tau_keccak_g * GEN ** QKECCAK_SLOT_LOG
    if const(COL_KAPPA_SRC[QKECCAK_COMMITTED_COL] != TABLE_KECCAK + 2):
        assert qkeccakv_g == kb[COL_KAPPA_SRC[QKECCAK_COMMITTED_COL]] * GEN ** COL_KAPPA_ADJ[QKECCAK_COMMITTED_COL]
    else:
        if const(COL_KAPPA_ADJ[QKECCAK_COMMITTED_COL] != QKECCAK_SLOT_LOG):
            assert qkeccakv_g == kb[COL_KAPPA_SRC[QKECCAK_COMMITTED_COL]] * GEN ** COL_KAPPA_ADJ[QKECCAK_COMMITTED_COL]
    out_eq_chain = HeapBuf(SIZE_BITS + QKECCAK_SLOT_LOG + 1)
    eq_prefix_chain(out_eq_chain, 1, z_vals, point1, qkeccakv_g)
    rs_weight = ring_switch_weight(z_vals * GEN ** QKECCAK_VARS_CAP, point1, c_table, qkeccakv_g)
    inner_sum += (rs_weight + lam_out * out_eq_chain[qkeccakv_g]) * selectors[QKECCAK_COMMITTED_COL]
    # The OOD sample's claim, after the output word's: eq(z, .) over the stack's m variables.
    ood_chain = HeapBuf(MAX_STACK_LOG + 1)
    eq_prefix_chain(ood_chain, lam_out * lam_cl, ood_z, point1, gmv)
    assert (inner_sum + ood_chain[gmv]) * yr_at_tail == sumcheck_target


def bus_grind_check(word, tabs, d: Const):
    # The bus's grind at a push depth of MIN_LOG_MEM + d.
    grind_check(word, tabs, BUS_GRIND_BITS[MIN_LOG_MEM + d])
    return 0


def verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, defer_out):
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
    tabs = g_squares * GEN ** WIN_TAB_AT

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    # The sponge's first permutation takes the program digest and the statement as
    # its rate, from the zero state.
    sp = StackBuf(KECCAK_STATE)
    keccak_cells([seed_0, seed_1, pi_0, pi_1], sp, final=0)
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
    kb = StackBuf(N_TABLES + 2)  # the same, in the frame
    kb[0] = 1
    kb[1] = g_log_mem
    for t in unroll(0, N_TABLES):
        kb[2 + t] = dims_g[GEN ** (t + 1)]
    for i in unroll(0, N_TABLES + 2):
        kappa_base[GEN ** i] = kb[i]
    # The ONE bus depth, COMPUTED (not hinted): mu = log2_ceil(Σ_b 2^κ_b) over
    # PUSH's blocks; pull matches by pairing, the count tree is padded to it.
    push_total = GEN ** 0
    for b in unroll(SIDE_BLOCK_START[PUSH_SIDE], SIDE_BLOCK_START[PUSH_SIDE + 1]):
        push_total *= g_squares[kb[BLOCK_KAPPA_SRC[b]] * GEN ** BLOCK_KAPPA_ADJ[b]]  # g^(sum of 2^kappa)
    g_bus_mu = log2_ceil_in_the_exponent(push_total, g_squares, 0, SIZE_BITS)
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

    # ---- the committed size: placement, then g^m, m = max(log2_ceil(sum_cols 2^kappa), PCS_MIN_MU) ----
    # g_total is g^(sum 2^kappa) from the certified placement walk.
    g_total, col_offsets = certify_placement(kappa_base, g_squares)
    gmv = log2_ceil_in_the_exponent(g_total, g_squares, PCS_MIN_MU, SIZE_BITS)  # g^m
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES

    # ---- the level-0 OOD sample (verifier read_ood) ----
    # A grind, then z of the stack's m variables, the first drawn by the grind's
    # permutation, then the stack's value at z.
    sp, z_first, cursor = fs_grind_squeeze(sp, rate, (N_TABLES + 3) % 4 + 1, cursor, tabs, OOD_GRIND_BITS)
    ood_z = HeapBuf(MAX_STACK_LOG)
    fs0, fs1, fs2, fs3, fs4 = match(log(size_sel), range(0, LIG_N_LOG_SIZES), lambda s: squeeze_point_from(sp[8], sp[9], sp[10], sp[11], sp[12], z_first, ood_z, LIG_MIN_LOG_SIZE + s))
    ood_value = HeapBuf(1)
    # The bus's grind nonce joins the value: its permutation draws the first alpha.
    word0, pow_word, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, ood_value, 1, 1)

    # ---- bus challenges ----
    # They fail with probability at most 4 * 2^mu / |E| (verifier::bus), so a grind of
    # BUS_GRIND_BITS[mu] comes first, mu the push side's depth: at least MIN_LOG_MEM,
    # the memory block's. A tuple is fingerprinted multilinearly: slot x weighs
    # eq(alphas, x), so a leaf factor has total degree N_TUPLE_BITS in the challenges
    # and the aligned bytecode polynomial is read off at the challenge vector itself
    # (doc sec:gp, sec:e2e-bc).
    bus_grind = g_bus_mu * INV_GEN ** MIN_LOG_MEM
    assert log(bus_grind) < BUS_GRIND_ARMS
    done = match(log(bus_grind), range(0, BUS_GRIND_ARMS), lambda d: bus_grind_check(pow_word, tabs, d))  # a match needs a target
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    no_rate = StackBuf(8)
    bus_alpha = HeapBuf(N_TUPLE_BITS)
    bus_alpha[GEN ** 0] = word0
    for t in unroll(1, N_TUPLE_BITS):
        sp, av = squeeze(sp, no_rate, 0)
        bus_alpha[GEN ** t] = av
    fp_w = HeapBuf(N_TUPLE_SLOTS)
    for x in unroll(0, N_TUPLE_SLOTS):
        fp_w[GEN ** x] = eq_weight(bus_alpha, N_TUPLE_BITS, x, 0)
    sp, beta = squeeze(sp, no_rate, 0)

    # ---- ONE GKR grand product: every tree batched ----
    fs0, fs1, fs2, fs3, fs4, cursor, gkr_leaves = verify_bus_gkr(sp[8], sp[9], sp[10], sp[11], sp[12], cursor, g_bus_mu, zeta, tabs)

    # ---- the bus leaves, the table sumcheck, and the public-input claim ----
    chi = HeapBuf(SIZE_BITS)  # chi[i] = the challenge that bound variable i
    fs0, fs1, fs2, fs3, fs4, cursor, g_zc_n, bc_share, rm, col_eval_words = verify_tables(fs0, fs1, fs2, fs3, fs4, cursor, pi_0, pi_1, zeta, g_bus_mu, dims_g, table_rows, g_squares, fp_w, beta, claim_pool, chi, gkr_leaves, tabs)

    # ---- KECCAK validity, by GKR over the rounds ----
    tau_keccak_g = dims_g[GEN ** (TABLE_KECCAK + 1)]  # the KECCAK table's certified tau
    z_vals = HeapBuf(2 * QKECCAK_VARS_CAP)
    slices = HeapBuf(BASE_FIELD_BITS)
    fs0, fs1, fs2, fs3, fs4, cursor, keccak_word = verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, tau_keccak_g, chi, col_eval_words * GEN ** (KECCAK_OUT_POOL - N_BUS_CLAIMS), z_vals, slices, tabs)
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)

    # ---- stacked mixed opening: ring-switch front + claim combination ----
    # The input opening's slices were read and bound above; this block only binds
    # them to the commitment. Phi(v) = sum_p f_p Psi(v)^(2^(8p)), Psi(v) = sum_b g_b v^(2^b):
    # its expansion has all 64 Frobenius terms soundness needs.
    # One grind covers the map's challenges and the batching challenge lam_cl, drawn
    # next: one verifier message.
    rate = StackBuf(8)
    ch = StackBuf(2 * RING_MAP_WIDTH)  # f_0 .. f_7, then g_0 .. g_7
    sp, map_first, cursor = fs_grind_squeeze(sp, rate, 0, cursor, tabs, BATCH_GRIND_BITS)
    ch[0] = map_first
    for i in unroll(1, 2 * RING_MAP_WIDTH):
        sp, map_challenge = squeeze(sp, rate, 0)
        ch[i] = map_challenge
    map_challenges = HeapBuf(2 * RING_MAP_WIDTH)
    for i in unroll(0, 2 * RING_MAP_WIDTH):
        map_challenges[GEN ** i] = ch[i]
    # The same map as a Frobenius sum, for the transparent weight: c_(8p+b) = f_p g_b^(2^(8p)).
    c_table = HeapBuf(BASE_FIELD_BITS)
    for b in unroll(0, RING_MAP_WIDTH):
        power = ch[RING_MAP_WIDTH + b]
        for p in unroll(0, RING_MAP_WIDTH):
            c_table[GEN ** (RING_MAP_WIDTH * p + b)] = ch[p] * power
            if const(p + 1 != RING_MAP_WIDTH):
                for t in unroll(0, RING_MAP_WIDTH):
                    power = power * power
    target_in = ring_switch_target(slices, map_challenges)
    # ONE batching challenge for the whole pool: N_CLAIMS - 1 fewer Fiat-Shamir
    # hashes than a challenge per claim, and none for the values themselves,
    # `fs_next` having bound every one it read and the public-input ones deriving
    # from the seeded statement and rm, so `lam_cl` already depends on all of
    # them. Disjoint power ranges, as for the zc_xi-powers above:
    # the ring-switch claim takes lam_cl^0, the pool lam_cl^1 onward (bar the output
    # lanes' claims, which the Keccak reduction consumed), and the Keccak reduction's
    # claim on its committed outputs the power after the pool's last.
    sp, lam_cl = squeeze(sp, rate, 0)
    target = target_in
    lam_pow = lam_cl
    for j in unroll(0, N_CLAIMS):
        if CLAIM_POINT_BUF[j] != POINT_BUF_KECCAK_OUT:
            if const(j // N_BUS_CLAIMS == 0):
                target += lam_pow * claim_pool[GEN ** j]
            else:
                if const((j - N_BUS_CLAIMS) // N_COL_EVALS == 0):
                    target += lam_pow * col_eval_words[GEN ** (j - N_BUS_CLAIMS)]
                else:
                    target += lam_pow * claim_pool[GEN ** j]
            lam_pow *= lam_cl
    target += lam_pow * keccak_word
    # The OOD sample's claim closes the batch.
    target += lam_pow * lam_cl * ood_value[1]
    # Flatten (rate-1, m-MIN) in rate-major order. Both coordinates are
    # transcript-bound and range-checked above, so a single compiled guest can
    # dispatch independently for every inner proof in a mixed-rate batch.
    config_sel = size_sel * rate_sel ** LIG_N_LOG_SIZES
    assert log(config_sel) < LIG_N_CANDIDATES
    sumcheck_target, point, point1, inner_total, yr_at_tail = match(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, sp[8], sp[9], sp[10], sp[11], sp[12], target, commit_root_0, commit_root_1, cursor, tabs))
    # `stream` is a fixed-capacity witness transport. The shape fixes the exact
    # consumed prefix, whose every word is transcript-bound; the unused suffix
    # is outside the recursively verified proof and intentionally unconstrained.

    # ---- generalized eval_b terminal (runtime claim shapes) ----
    check_opening_terminal(g_squares, zeta, chi, rm, g_bus_mu, g_zc_n, g_log_mem, tau_keccak_g, kappa_base, lam_cl, col_offsets, z_vals, c_table, point, point1, inner_total, yr_at_tail, sumcheck_target, ood_z, gmv)

    # ---- export this sub-proof's deferred-claim data to the caller (FRESH_*) ----
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = zeta[GEN ** k]
    for k in unroll(0, LOG2_BYTECODE_COLS):
        defer_out[GEN ** (BYTECODE_LOG + k)] = bus_alpha[GEN ** k]
    defer_out[GEN ** FRESH_BC_VALUE] = bc_share
    return


# =============================== WOTS+C, both schemes ===============================
# Every addressed hash input is P | A | M with P, each value of M and each half of A
# 16 bytes (A is one cell in leanXMSS, two in leanSPHINCS), so each is one cell: a
# hash's output feeds the next hash where it lands, and a hinted value needs no check
# of its own, every cell being a 16-byte value. A chain's steps land in
# fixed slots of a `walks` run, so its tip is one cell whatever the digit, read there
# by the leaf's hash.


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
    tip = walks[(i + 1) * CHAIN_STEPS - 1]
    return tip


@inline
def walk(at, pp, walks, tags, powers, i: Const, k: Const, lx: Const):
    # Walk chain i from position k to its end, the step leaving position s landing in
    # chain i's slot s of `walks`, so the tip is chain_tip(walks, i) whatever k is. A
    # leanSPHINCS step's address is at[0] and at[1] with i and s added, the value last;
    # a leanXMSS one carries only s, at[s] computed once per key, i riding after the
    # value, read off a cell set outside the dispatch (the zero cell, `powers` or
    # `tags`), so an arm names it rather than setting it again.
    if const(lx == 1):
        if const(i == 0):
            tag = 0
        elif const(LX_TAG_SLOT[i] == 0):
            tag = powers[LX_TAG_LOG[i]]
        else:
            tag = tags[LX_TAG_SLOT[i] - 1]
    if const(k == CHAIN_STEPS):
        hint_witness(walks[(i + 1) * CHAIN_STEPS - 1:(i + 1) * CHAIN_STEPS], "chain_starts")
    else:
        value = hint_witness("chain_starts")
        for s in unroll(k, CHAIN_STEPS):
            o = CHAIN_STEPS * i + s
            if const(lx == 1):
                keccak([pp, at[s]], [value, tag], walks[o:o + 1])
            else:
                keccak([pp, at[0]], [at[1] + const(i * SP_WORD2_MUL + s * SP_WORD3_MUL_0), value], walks[o:o + 1])
            value = walks[o]
    return


@inline
def walk_group(at, pp, walks, tags, first: Const, n: Const, k: Const, lx: Const, powers, product, encoded):
    # The n chains from `first` on, at the digits of k (its low n), one dispatch for
    # all of them. Folds the digits' sum into `product`, in the exponent (`powers[s]` is
    # GEN ** s), and the digits into `encoded`, where the encoding digest holds them:
    # leanXMSS's low first, leanSPHINCS's most significant first in each byte (base_2b).
    for r in unroll(0, n):
        walk(at, pp, walks, tags, powers, first + r, (k // CHAIN_LENGTH ** r) % CHAIN_LENGTH, lx)
    if const(lx == 1):
        digits = const(k % CHAIN_LENGTH ** n * CHAIN_LENGTH ** first)
    else:
        digits = 0
        for r in unroll(0, n):
            digits = digits + const(((k // CHAIN_LENGTH ** r) % CHAIN_LENGTH) * 2 ** (8 * ((first + r) // SP_DIGITS_PER_BYTE) + W * (SP_DIGITS_PER_BYTE - 1 - (first + r) % SP_DIGITS_PER_BYTE)))
    return product * powers[DIGIT_SUMS[k % CHAIN_LENGTH ** n]], encoded + digits


@inline
def leaf_word(p0, p1, walks, j: Const):
    # Word j of a one-time leaf's input: the prefix (p0, p1), then the chain tips.
    w = p0
    if const(j == 1):
        w = p1
    if const(j != 0):
        if const(j != 1):
            w = chain_tip(walks, j - 2)
    return w


@inline
def wots_leaf(p0, p1, walks, n: Const, leaf):
    # The hash of the prefix (p0, p1) and the n chain tips, each read where its walk left it.
    keccak_cells([leaf_word(p0, p1, walks, j) for j in unroll(0, n + 2)], leaf)
    return


# ========================= leanXMSS signature verification ========================


@inline
def lx_levels(cur, pp, powers, his, out, w: Const, k: Const):
    # The LX_WINDOW path levels from LX_WINDOW * w, whose index bits are k's, from `cur`
    # into out. A node's order against its hinted sibling is k's bit, and a parent's
    # address holds `leaf_index >> (level + 1)`: his[w + 1] shifted up by what is left of
    # the window, k's higher bits added. Nothing is above the top window.
    for r in unroll(0, LX_WINDOW):
        tag = const(TW_NODE + ((LX_WINDOW * w + r) % LX_HEIGHT + 1) * HI_MUL + (LX_WINDOW * w + r) // LX_HEIGHT * LX_TOP + k // 2 ** (r + 1))
        if const(w + 1 == LX_WINDOWS):
            at = tag
        elif const(r + 1 == LX_WINDOW):
            at = his[w + 1] + tag
        else:
            at = his[w + 1] * powers[LX_WINDOW - 1 - r] + tag
        if const(r + 1 == LX_WINDOW):
            parent = out
        else:
            parent = StackBuf(1)
        sibling = hint_witness("lx_path")
        if const((k // 2 ** r) % 2 == 0):
            keccak([pp, at], [cur, sibling], parent)
        else:
            keccak([pp, at], [sibling, cur], parent)
        cur = parent[0]
    return


@inline
def lx_window(cur, pp, powers, his, out, w: Const, k: Const):
    # Window w of the path (`lx_levels`). Returns his[w] as his[w + 1] and k spell it,
    # which the dispatch writes where the hinted his[w] already is: so the index the
    # signature's addresses use is the one its path takes.
    lx_levels(cur, pp, powers, his, out, w, k)
    return his[w + 1] * powers[LX_WINDOW] + const(k)


@inline
def lx_top_window(cur, pp, powers, his, out, w: Const, k: Const):
    # The top window, nothing above it: his[w] is k alone.
    lx_levels(cur, pp, powers, his, out, w, k)
    return const(k)


@inline
def verify_lean_xmss(signer, tags):
    # `signer` is one 4-cell entry of the leanXMSS coverage table: the pubkey's
    # merkle root and public parameter, then the message that pubkey signed. The
    # bottom layer signs the message, the top layer the bottom root.
    pp = signer[GEN]

    # The leaf index rides the signature, so every address is derived here from it. It
    # is advice: his[v] is `leaf_index >> (LX_WINDOW * v)`, a field's value, and each window
    # of LX_WINDOW bits is hinted again in the exponent, range checked and dispatched on
    # by the path (`lx_window`). Each arm pins his[w] to his[w + 1] and its own bits, and
    # the top one has nothing above it, so his[0] is the index the windows spell. Any
    # index is one some signature may carry; the digests and the root this signature
    # must reach bind it.
    his = StackBuf(LX_WINDOWS)
    hint_witness(his, "lx_index")
    windows = StackBuf(LX_WINDOWS)
    hint_witness(windows, "lx_windows")
    powers = StackBuf(LX_DIGIT_GROUP * CHAIN_STEPS + 1)
    for s in unroll(0, LX_DIGIT_GROUP * CHAIN_STEPS + 1):
        powers[s] = GEN ** s
    for layer in unroll(0, 2):
        if const(layer == 0):
            idx = his[0]
        else:
            idx = his[LX_LAYER_WINDOWS] + LX_TOP
        # D = Th(P, A, M | R), one block: 80 bytes at the bottom, and 64 at the top,
        # where M is the bottom root.
        rho = hint_witness("randomizer")
        digest = StackBuf(1)
        if const(layer == 0):
            keccak([pp, idx + TW_MSG], [signer[GEN ** 2], signer[GEN ** 3]], digest, tail=[rho, 0, 0, 0], len=80)
        else:
            keccak([pp, idx + TW_MSG], [root, rho], digest)

        # The codeword: LX_DIGIT_GROUP digits at a time, hinted in the exponent, range
        # checked and dispatched once, the arm walking every chain's remaining steps
        # and folding its digits in: their sums into a product that must be the
        # target sum, and the digits, each where the digest holds it, into D, which
        # also checks the digits past LX_V are zero.
        steps = StackBuf(CHAIN_STEPS)
        for st in unroll(0, CHAIN_STEPS):
            steps[st] = idx + const(TW_CHAIN + st * STEP_MUL)
        walks = StackBuf(LX_V * CHAIN_STEPS)
        digit_product = 1
        encoded = 0
        groups = StackBuf(LX_DIGIT_DISPATCHES)
        hint_witness(groups, "lx_digits")
        for p in unroll(0, LX_DIGIT_DISPATCHES - 1):
            assert log(groups[p]) < LX_DIGIT_GROUPS
        assert log(groups[LX_DIGIT_DISPATCHES - 1]) < LX_TAIL_GROUPS
        # Back to back, each arm entering the next dispatch. The last group's table is as
        # wide as the others, its range check what keeps it to LX_DIGIT_TAIL digits.
        for p in unroll(0, LX_DIGIT_DISPATCHES):
            digit_product, encoded = match(log(groups[p]), range(0, LX_DIGIT_GROUPS), lambda k: walk_group(steps, pp, walks, tags, LX_DIGIT_GROUP * p, LX_GROUP_SIZES[p], k, 1, powers, digit_product, encoded))
        digest[0] = encoded  # the digits, stored where D already is
        assert digit_product == GEN ** LX_TARGET_SUM

        # The one-time leaf, then the path to the layer's root, a window at a time.
        leaf = StackBuf(1)
        wots_leaf(pp, idx + TW_LEAF, walks, LX_V, leaf)
        cur = leaf[0]
        for v in unroll(0, LX_LAYER_WINDOWS):
            w = layer * LX_LAYER_WINDOWS + v
            out = StackBuf(1)
            assert log(windows[w]) < LX_WINDOW_ARMS
            if const(w + 1 == LX_WINDOWS):
                his[w] = match(log(windows[w]), range(0, LX_WINDOW_ARMS), lambda k: lx_top_window(cur, pp, powers, his, out, w, k))
            else:
                his[w] = match(log(windows[w]), range(0, LX_WINDOW_ARMS), lambda k: lx_window(cur, pp, powers, his, out, w, k))
            cur = out[0]
        root = cur
    assert root == signer[1]
    return


# ======================== leanSPHINCS signature verification ======================


@inline
def sp_from_bytes(byte_bits, marks, n: Const):
    # The integer whose n bytes, low first, are hinted in the exponent at marks[k]: each
    # range checked and read off `byte_bits` as the bits it spells.
    for t in unroll(0, n):
        k = n - 1 - t
        assert log(marks[k]) < SP_BYTE_VALUES
        if const(t == 0):
            value = byte_bits[marks[k]]
        else:
            value = byte_bits[marks[k]] + value * GEN ** 8
    return value


@inline
def sp_md_bit(bits0, bits1, p: Const):
    # Bit p of the digest read most significant first, as base_2b reads it: bit
    # 7 - p % 8 of byte p // 8, from the bit runs of the first call's two cells.
    b = bits0[(8 * (p // 8) + 7 - p % 8) % SP_CELL_BITS]
    if const(p // SP_CELL_BITS == 1):
        b = bits1[8 * (p // 8) + 7 - p % 8 - SP_CELL_BITS]
    return b


@inline
def sp_fors_field(bits0, bits1, vals, c: Const):
    # FORS tree c's leaf, the digest's SP_FORS_HEIGHT bits from bit SP_FORS_HEIGHT c,
    # and its right shifts, each with tree c's place across the trees: vals[SP_FORS_HEIGHT
    # c + z] is the FIPS 205 tree index of the leaf's ancestor at height z, c 2^(height - z)
    # plus its index in tree c.
    vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1] = sp_md_bit(bits0, bits1, SP_FORS_HEIGHT * c) + const(2 * c)
    for r in unroll(1, SP_FORS_HEIGHT):
        vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1 - r] = sp_md_bit(bits0, bits1, SP_FORS_HEIGHT * c + r) + GEN * vals[SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - r]
    return


@inline
def sp_md_byte(vals, i: Const):
    # Digest byte i < SP_MD_BYTES where its cell holds it, from the shifts of field c,
    # the one its first bit is in, and of c + 1 if it reaches it. A byte inside c is c
    # shifted past the bits after the byte, masked to eight bits; a byte across both is
    # c's low bits raised past c + 1's high ones. It keeps the trees' places vals carries,
    # which the caller takes out.
    c = 8 * i // SP_FORS_HEIGHT
    if const(c == (8 * i + 7) // SP_FORS_HEIGHT):
        v = vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i - 8]
        if const(8 * i != SP_FORS_HEIGHT * c):
            v = v + vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i] * GEN ** 8
        v = v * const(2 ** (8 * (i % 16)))
    else:
        v = (vals[SP_FORS_HEIGHT * c] + vals[SP_FORS_HEIGHT * (2 * c + 1) - 8 * i] * GEN ** (SP_FORS_HEIGHT * (c + 1) - 8 * i)) * const(2 ** (8 * (i % 16) + 8 * i + 8 - SP_FORS_HEIGHT * (c + 1)))
        v = v + vals[SP_FORS_HEIGHT * (2 * c + 3) - 8 * i - 8] * const(2 ** (8 * (i % 16)))
    return v


@inline
def sp_leaf_bit(bits1, bits2, b: Const):
    # Bit b of the three layers' leaves one after the other, bottom first, which the
    # digest's last four bytes hold: the bottom leaf the last byte (the second call's
    # byte 1), the middle one the byte before (its byte 0), and the top one the tree
    # index's high bits (the first call's byte 31, then the low two bits of 30).
    x = bits2[(b + SP_MID) % (8 * SP_TAIL_BYTES)]
    if const(b // 8 == SP_TOP // 8):
        x = bits1[b - SP_TOP + SP_TREE_MID_BIT]
    if const(b // 8 == SP_TOP // 8 + 1):
        x = bits1[b - SP_TOP - 8 + SP_TREE_HI_BIT]
    return x


@inline
def sp_leaf_shifts(bits1, bits2, lvals, off: Const, n: Const):
    # The leaf of n bits from leaf bit `off` and its right shifts: lvals[off + z] is the
    # index of its ancestor at height z.
    lvals[off + n - 1] = sp_leaf_bit(bits1, bits2, off + n - 1)
    for r in unroll(1, n):
        lvals[off + n - 1 - r] = sp_leaf_bit(bits1, bits2, off + n - 1 - r) + GEN * lvals[off + n - r]
    return


@inline
def sp_be16(vals, at: Const, n: Const):
    # The n-bit value vals[at] as the last two bytes of an A1 word, big endian: its low
    # byte masked and placed last, its high bits before it.
    if const((n + 7) // 8 == 2):
        v = vals[at] * const(SP_WORD3_MUL_0) + vals[at + 8] * (GEN ** 8 * const(SP_WORD3_MUL_0) + const(SP_WORD3_MUL_1))
    else:
        v = vals[at] * const(SP_WORD3_MUL_0)
    return v


@inline
def sp_fors_at(a1, vals, c: Const, z: Const):
    # The A1 of tree c's node at height z on the opened leaf's path, `a1` being the
    # trees' with neither: z, then the node's tree index across the trees in the word's
    # last two bytes, big endian. vals holds the index below the root, whose high byte is
    # c's part alone from height SP_FORS_HEIGHT - 8 on, a constant added first so that trees
    # sharing it share the sum; at the root the index is c.
    at = a1 + const(z * SP_WORD2_MUL)
    if const(z == SP_FORS_HEIGHT):
        at = at + const(c * SP_WORD3_MUL_0)
    elif const(z // (SP_FORS_HEIGHT - 8) == 0):
        at = at + sp_be16(vals, SP_FORS_HEIGHT * c + z, 16)
    else:
        at = at + const(c // 2 ** (z - (SP_FORS_HEIGHT - 8))) * (GEN ** 8 * const(SP_WORD3_MUL_0) + const(SP_WORD3_MUL_1))
        at = at + sp_be16(vals, SP_FORS_HEIGHT * c + z, 8)
    return at


@inline
def sp_fors_tree(pp, a0, a1, bits0, bits1, vals, roots, c: Const):
    # FORS tree c: its leaf, hashed from the hinted secret, then climbed up the hinted
    # ordered pairs to its root, into roots[c].
    secret = hint_witness("sp_fors_secrets")
    held = StackBuf(1)
    keccak([pp, a0], [sp_fors_at(a1, vals, c, 0), secret], held)
    cur = held[0]
    for z in unroll(0, SP_FORS_HEIGHT):
        # The two children, then three cells the compiler sets to the padding, so the
        # node's hash reads the right child in place (`pad_tail=1`).
        kids = StackBuf(5)
        hint_witness(kids[0:2], "sp_fors_nodes")
        is_child(cur, kids, 0, sp_md_bit(bits0, bits1, SP_FORS_HEIGHT * c + SP_FORS_HEIGHT - 1 - z))
        node_at = sp_fors_at(a1, vals, c, z + 1)
        if const(z + 1 == SP_FORS_HEIGHT):
            keccak([pp, a0], [node_at, kids[0]], roots[c:c + 1], tail=kids[1:5], len=80, pad_tail=1)
        else:
            parent = StackBuf(1)
            keccak([pp, a0], [node_at, kids[0]], parent, tail=kids[1:5], len=80, pad_tail=1)
            cur = parent[0]
    return


@inline
def sp_word(pp, a0, a1, run, first: Const, stride: Const, j: Const):
    # Word j of a T_l input: PK.seed, the address, then the values, value i at
    # run[first + stride i] (the FORS roots, or a one-time key's chain tips).
    w = pp
    if const(j == 1):
        w = a0
    if const(j == 2):
        w = a1
    if const(j // 3 != 0):
        w = run[first + stride * (j - 3)]
    return w


def sp_wots(pp, a0, a1, encoding):
    # The leaf of the one-time key whose address is (a0, a1), a1 of type WOTS_HASH and
    # so its key pair alone, and whose encoding digest is `encoding`. The codeword:
    # DIGIT_GROUP digits at a time, hinted in the exponent, range checked and
    # dispatched once, the arm walking every chain's remaining steps and folding its
    # digits in: their sums into a product that must be the target sum, and the
    # digits, each group where the digest holds it, into the digest. One function for
    # the three layers.
    at = [a0, a1]
    walks = StackBuf(SP_V * CHAIN_STEPS)
    powers = StackBuf(DIGIT_GROUP * CHAIN_STEPS + 1)
    for s in unroll(0, DIGIT_GROUP * CHAIN_STEPS + 1):
        powers[s] = GEN ** s
    digit_product = 1
    encoded = 0
    # A leanSPHINCS chain index rides its step's address, so the chain-index table a
    # leanXMSS walk reads is unused here and `powers` stands in for it.
    for p in unroll(0, SP_V // DIGIT_GROUP):
        group = hint_witness("digits")
        assert log(group) < DIGIT_GROUPS
        digit_product, encoded = match(log(group), range(0, DIGIT_GROUPS), lambda k: walk_group(at, pp, walks, powers, DIGIT_GROUP * p, DIGIT_GROUP, k, 0, powers, digit_product, encoded))
    # The chain the groups leave over.
    group = hint_witness("digits")
    assert log(group) < CHAIN_LENGTH
    digit_product, encoded = match(log(group), range(0, CHAIN_LENGTH), lambda k: walk_group(at, pp, walks, powers, SP_V - 1, 1, k, 0, powers, digit_product, encoded))
    assert encoded == encoding
    assert digit_product == GEN ** SP_TARGET_SUM
    leaf = StackBuf(1)
    pk_at = a1 + const(SP_WOTS_PK)
    keccak_cells([sp_word(pp, a0, pk_at, walks, CHAIN_STEPS - 1, CHAIN_STEPS, j) for j in unroll(0, SP_V + 3)], leaf)
    return leaf[0]


@inline
def sp_path(node, pp, a0, bits1, bits2, lvals, out, off: Const, height: Const):
    # The path from `node` up the tree whose address is a0, the leaf's bits from leaf bit
    # `off` and its ancestors' indices in lvals, the two children of each node hinted in
    # order, the root into out.
    cur = node
    for z in unroll(0, height):
        # The two children, then three cells the compiler pads (as in sp_fors_tree).
        kids = StackBuf(5)
        hint_witness(kids[0:2], "siblings")
        is_child(cur, kids, 0, sp_leaf_bit(bits1, bits2, off + z))
        # The parent's height, then its index, none at the root.
        node_at = const(SP_TREE + (z + 1) * SP_WORD2_MUL)
        if const(z + 1 == height):
            parent = out
        else:
            node_at = sp_be16(lvals, off + z + 1, height - z - 1) + node_at
            parent = StackBuf(1)
        keccak([pp, a0], [node_at, kids[0]], parent, tail=kids[1:5], len=80, pad_tail=1)
        cur = parent[0]
    return


@inline
def sp_layer(pp, a0, key, signed, byte_bits, bits1, bits2, lvals, out, off: Const, height: Const):
    # One layer: the key at (a0, key), `key` its key pair as A1 holds it, signs `signed`,
    # its counter rebuilt from four bytes, then the path to its tree's root into out.
    ctr = StackBuf(SP_COUNTER_BYTES)
    hint_witness(ctr, "sp_counter")
    counter = sp_from_bytes(byte_bits, ctr, SP_COUNTER_BYTES)
    enc = StackBuf(1)
    enc_at = key + const(SP_WOTS_ENC)
    keccak([pp, a0], [enc_at, signed], enc, tail=[counter, 0, 0, 0], len=SP_ENCODING_BYTES)
    leaf = sp_wots(pp, a0, key, enc[0])
    sp_path(leaf, pp, a0, bits1, bits2, lvals, out, off, height)
    return


def verify_sig_lean_sphincs(signer, byte_bits):
    # `signer` is one 4-cell entry of the leanSPHINCS coverage table: the pubkey's PK.seed
    # and PK.root, then the message THAT signer signed, the two bound together by the
    # scheme's claim-list digest, as for leanXMSS.
    pp = signer[1]
    pk_root = signer[GEN]

    # ---- H_msg, which picks the index and every FORS leaf ----
    # H(R | PK.seed | PK.root | M | BE_32(i)) for i = 0, 1, M the claim's two cells.
    m0 = signer[GEN ** 2]
    m1 = signer[GEN ** 3]
    rho = hint_witness("sp_rand")
    d0 = StackBuf(2)
    d1 = StackBuf(1)
    keccak([rho, pp], [pk_root, m0], d0, tail=[m1, 0, 0, 0], len=SP_HMSG_LEN)
    keccak([rho, pp], [pk_root, m0], d1, tail=[m1, SP_COUNTER_ONE, 0, 0], len=SP_HMSG_LEN)

    # The digest's bits are advice pinned Boolean, and the digest is rebuilt from them:
    # byte by byte from the FORS leaves' values, which their shifts give, then the tree
    # index and the bottom leaf from the layers' leaves, the six bits the tree index
    # leaves from their own bits, and the second call's unused bytes as hinted bytes
    # (sp_from_bytes). Its high lane is what the rest leaves, checked to be a lane.
    bits0 = StackBuf(SP_CELL_BITS)
    bits1 = StackBuf(SP_CELL_BITS)
    bits2 = StackBuf(8 * SP_TAIL_BYTES)
    hint_decompose_bits(bits0, d0[0], SP_CELL_BITS)
    hint_decompose_bits(bits1, d0[1], SP_CELL_BITS)
    hint_decompose_bits(bits2, d1[0], 8 * SP_TAIL_BYTES)
    for b in unroll(0, SP_CELL_BITS):
        bits0[b] = bits0[b] * bits0[b]
        bits1[b] = bits1[b] * bits1[b]
    for b in unroll(0, 8 * SP_TAIL_BYTES):
        bits2[b] = bits2[b] * bits2[b]
    vals = StackBuf(SP_FORS_TREES * SP_FORS_HEIGHT)
    for c in unroll(0, SP_FORS_TREES):
        sp_fors_field(bits0, bits1, vals, c)
    lvals = StackBuf(SP_H)
    sp_leaf_shifts(bits1, bits2, lvals, 0, SP_HEIGHT_0)
    sp_leaf_shifts(bits1, bits2, lvals, SP_MID, SP_HEIGHT_1)
    sp_leaf_shifts(bits1, bits2, lvals, SP_TOP, SP_HEIGHT_2)
    md0 = sp_md_byte(vals, 0)
    for i in unroll(1, 16):
        md0 = md0 + sp_md_byte(vals, i)
    md1 = sp_md_byte(vals, 16)
    for i in unroll(17, SP_MD_BYTES):
        md1 = md1 + sp_md_byte(vals, i)
    # vals carries each tree's place across the trees (sp_fors_field), which the digest's
    # bytes do not: take it out again, a constant per byte.
    corr0 = 0
    corr1 = 0
    for i in unroll(0, SP_MD_BYTES):
        fc = 8 * i // SP_FORS_HEIGHT
        pc = 0
        if const(fc != (8 * i + 7) // SP_FORS_HEIGHT):
            pc = const((fc + 1) * 2 ** (8 * i + 8 - SP_FORS_HEIGHT * (fc + 1))) * const(2 ** (8 * (i % 16)))
        elif const(8 * i == SP_FORS_HEIGHT * fc):
            pc = const(fc * 256) * const(2 ** (8 * (i % 16)))
        if const(i // 16 == 0):
            corr0 = corr0 + pc
        else:
            corr1 = corr1 + pc
    # The tree index's middle byte, the top leaf's low byte; its high byte holds the top
    # leaf's two high bits, then six unused ones.
    tree_mid = lvals[SP_TOP] + lvals[SP_TOP + 8] * GEN ** 8
    pad = bits1[SP_TREE_HI_BIT + 7]
    for b in unroll(1, SP_PAD_BITS):
        pad = bits1[SP_TREE_HI_BIT + 7 - b] + GEN * pad
    d0[0] = md0 + corr0
    d0[1] = md1 + corr1 + (lvals[SP_TOP + 8] + pad * GEN ** SP_TOP_HIGH_BITS) * const(2 ** SP_TREE_HI_BIT) + tree_mid * const(2 ** SP_TREE_MID_BIT)
    unused_bytes = StackBuf(SP_UNUSED_BYTES)
    hint_witness(unused_bytes, "sp_unused")
    unused = sp_from_bytes(byte_bits, unused_bytes, SP_UNUSED_BYTES)
    high = (d1[0] + lvals[SP_MID] + lvals[0] * GEN ** 8 + unused * GEN ** (8 * SP_TAIL_BYTES)) * Y_INV
    assert_in_k(high, unused)

    # ---- FORS: each tree's opening climbed to its root, then T_k over the roots ----
    # The FORS addresses are the bottom key's: its layer and tree, its leaf the key pair.
    a0_b = lvals[SP_MID] * const(SP_TREE_MUL_0) + tree_mid * const(SP_TREE_MUL_1) + lvals[SP_TOP + 8] * const(SP_TREE_MUL_2)
    key_b = lvals[0] * const(SP_KEY_MUL_0)
    roots = StackBuf(SP_FORS_TREES)
    fors_at = key_b + const(SP_FORS_TREE)
    for c in unroll(0, SP_FORS_TREES):
        sp_fors_tree(pp, a0_b, fors_at, bits0, bits1, vals, roots, c)
    fors_pk = StackBuf(1)
    roots_at = key_b + const(SP_FORS_ROOTS)
    keccak_cells([sp_word(pp, a0_b, roots_at, roots, 0, 1, j) for j in unroll(0, 3 + SP_FORS_TREES)], fors_pk)

    # ---- the hypertree: each layer's one-time key signs what the layer below gives ----
    # The bottom key is in the digest's tree at its leaf; the middle key in that tree's
    # top bits at its low byte; the top key in tree zero at the tree's top bits.
    root_b = StackBuf(1)
    sp_layer(pp, a0_b, key_b, fors_pk[0], byte_bits, bits1, bits2, lvals, root_b, 0, SP_HEIGHT_0)
    a0_m = const(SP_LAYER_MUL) + tree_mid * const(SP_TREE_MUL_0) + lvals[SP_TOP + 8] * const(SP_TREE_MUL_1)
    key_m = lvals[SP_MID] * const(SP_KEY_MUL_0)
    root_m = StackBuf(1)
    sp_layer(pp, a0_m, key_m, root_b[0], byte_bits, bits1, bits2, lvals, root_m, SP_HEIGHT_0, SP_HEIGHT_1)
    a0_t = const(2 * SP_LAYER_MUL)
    key_t = tree_mid * const(SP_KEY_MUL_0) + lvals[SP_TOP + 8] * const(SP_KEY_MUL_1)
    root = StackBuf(1)
    sp_layer(pp, a0_t, key_t, root_m[0], byte_bits, bits1, bits2, lvals, root, SP_HEIGHT_0 + SP_HEIGHT_1, SP_HEIGHT_2)
    assert root[0] == pk_root
    return


# ========================== statements and the claim lists ==========================


def statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer):
    # A node's statement, hashed to the two words the VM publishes, over the
    # proving environment's Fiat-Shamir seed (the proof system's version and this
    # bytecode), the leanXMSS and leanSPHINCS claim-list digests, its DA digest (zeros
    # without a root), and the DEFER_STMT_CELLS deferred-claim cells. A
    # parent rebuilds a child's statement with this same call, over list digests it
    # re-absorbed itself, which forces the child to be a proof of THIS bytecode over
    # claims read out of the parent's own tables.
    #
    # The preimage is fixed-length, so a plain hash beats the Fiat-Shamir chain.
    # Every value is one cell, hashed as its two lanes.
    cells = StackBuf(STMT_CELLS)
    cells[0] = seed_0  # the STMT_HEADER header cells
    cells[1] = seed_1
    cells[2] = xd_0
    cells[3] = xd_1
    cells[4] = sd_0
    cells[5] = sd_1
    cells[6] = da_0
    cells[7] = da_1
    for i in unroll(0, DEFER_STMT_CELLS):
        cells[STMT_DEFER_OFF + i] = defer[GEN ** i]
    st = StackBuf(2)
    keccak_cells(cells, st)
    return st[0], st[1]


# A declared claim list is hashed CLAIM_GROUP claims a loop frame: a claim is 64 bytes,
# four cells, so a group is 68 cells, four block pairs, and the sponge state is carried
# between frames through a heap chain of KECCAK_STATE cells a step, from the zero state.
# Only the claims after the last whole group depend on the length: a `match` on their
# count.


@inline
def zero_state(chain):
    for k in unroll(0, KECCAK_STATE):
        chain[GEN ** k] = 0
    return


def list_split(n_g):
    # A list of n claims as (g^bigs, g^groups, g^rest), n = CLAIM_BIG * bigs +
    # CLAIM_GROUP * groups + rest with groups < BIG_GROUPS. The range checks and the
    # product identity leave that split the only solution.
    split = StackBuf(3)
    hint_witness(split, "signers_split")
    bigs = split[0]
    groups = split[1]
    rest = split[2]
    assert log(rest) < CLAIM_GROUP
    assert log(groups) < BIG_GROUPS
    assert log(bigs) < MAX_KEYS
    # Every exponent is small and nonnegative, so this is an identity over the
    # integers: CLAIM_BIG * bigs + CLAIM_GROUP * groups + rest == n.
    assert bigs ** CLAIM_BIG * groups ** CLAIM_GROUP * rest == n_g
    return bigs, groups, rest


def claim_list_digest(entries_ptr, n_g):
    # The hash of one scheme's declared claims: 64 bytes a claim, the claimed pubkey
    # then the message it signed. An empty list hashes the empty string, and the
    # padding binds the length.
    digest = StackBuf(2)
    if n_g == 1:
        keccak([0, 0], [0, 0], digest, len=0)
    else:
        bigs, groups, rest = list_split(n_g)
        chain = HeapBuf((bigs * groups * GEN) ** KECCAK_STATE)
        zero_state(chain)
        for xq in mul_range(1, bigs):
            st = chain * xq ** KECCAK_STATE
            nxt = st * GEN ** KECCAK_STATE
            blk = entries_ptr * xq ** (4 * CLAIM_BIG)
            for j in unroll(0, CLAIM_BIG):
                hint_witness(blk[4 * j:4 * j + 4], "claims")
            keccak_cells(blk[0:4 * CLAIM_BIG], nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
        mid = chain * bigs ** KECCAK_STATE
        mid_entries = entries_ptr * bigs ** (4 * CLAIM_BIG)
        for xq in mul_range(1, groups):
            st = mid * xq ** KECCAK_STATE
            nxt = st * GEN ** KECCAK_STATE
            blk = mid_entries * xq ** (4 * CLAIM_GROUP)
            for j in unroll(0, CLAIM_GROUP):
                hint_witness(blk[4 * j:4 * j + 4], "claims")
            keccak_cells(blk[0:4 * CLAIM_GROUP], nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
        last = mid * groups ** KECCAK_STATE
        d0, d1 = match(log(rest), range(0, CLAIM_GROUP), lambda k: claim_list_last(last, mid_entries * groups ** (4 * CLAIM_GROUP), k))
        digest[0] = d0
        digest[1] = d1
    return digest[0], digest[1]


def claim_list_last(state, blk, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=state[0:KECCAK_STATE], len=0)
    else:
        for j in unroll(0, k):
            hint_witness(blk[4 * j:4 * j + 4], "claims")
        keccak_cells(blk[0:4 * k], digest, state=state[0:KECCAK_STATE])
    return digest[0], digest[1]


@inline
def child_claims(entries_ptr, region, marks, last_g, blk, n: Const):
    # n of a child's claims, each read at a hinted index into THIS node's table and
    # marked in the coverage table. The index is an offset into the scheme's region
    # (`region`, the coverage table from the scheme's origin) and bounded by that
    # region's size, last_g * GEN, so a child's claim can only ever land on a slot of
    # its own scheme. The bound so written is its own range-check target, last_g.
    for j in unroll(0, n):
        off_hint = hint_witness("child_claim_index")
        assert log(off_hint) < log(last_g * GEN)  # precondition as in the raw loops
        region[off_hint] = marks * (GEN ** j)
        entry = entries_ptr * (off_hint ** 4)
        for c in unroll(0, 4):
            blk[4 * j + c] = entry[GEN ** c]
    return


def child_claim_list_digest(entries_ptr, region, base, limit_g, n_g):
    # The hash of one of a child's declared claim lists, over the same 64n bytes the
    # child hashed (`claim_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. The coverage marks lie in [base, base + n): the claims'
    # running count, or `base` alone along a strictly increasing gap walk.
    # A list whose slots strictly increase (no duplicate slot among them) takes the
    # cheaper walk; either walk is sound on its own, so the choice is the prover's.
    digest = StackBuf(2)
    if n_g == 1:
        keccak([0, 0], [0, 0], digest, len=0)
    else:
        bigs, groups, rest = list_split(n_g)
        mono = hint_witness("child_mono")
        if mono == GEN:
            d0, d1 = child_claim_list_mono(entries_ptr, region, base, limit_g, bigs, groups, rest)
            digest[0] = d0
            digest[1] = d1
        else:
            d0, d1 = child_claim_list_any(entries_ptr, region, base, limit_g, bigs, groups, rest)
            digest[0] = d0
            digest[1] = d1
    return digest[0], digest[1]


def child_claim_list_any(entries_ptr, region, base, limit_g, bigs, groups, rest):
    last_g = limit_g / GEN
    chain = HeapBuf((bigs * groups * GEN) ** KECCAK_STATE)
    zero_state(chain)
    for xq in mul_range(1, bigs):
        st = chain * xq ** KECCAK_STATE
        nxt = st * GEN ** KECCAK_STATE
        blk = StackBuf(4 * CLAIM_BIG)
        child_claims(entries_ptr, region, base * xq ** CLAIM_BIG, last_g, blk, CLAIM_BIG)
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
    mid = chain * bigs ** KECCAK_STATE
    mid_base = base * bigs ** CLAIM_BIG
    for xq in mul_range(1, groups):
        st = mid * xq ** KECCAK_STATE
        nxt = st * GEN ** KECCAK_STATE
        blk = StackBuf(4 * CLAIM_GROUP)
        child_claims(entries_ptr, region, mid_base * xq ** CLAIM_GROUP, last_g, blk, CLAIM_GROUP)
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=st[0:KECCAK_STATE], final=0)
    last = mid * groups ** KECCAK_STATE
    d0, d1 = match(log(rest), range(0, CLAIM_GROUP), lambda k: child_claim_list_last(last, entries_ptr, region, mid_base * groups ** CLAIM_GROUP, last_g, k))
    return d0, d1


@inline
def child_claims_mono(cov, ent, mark, blk, out, n: Const):
    # n of a child's claims at strictly increasing offsets into THIS node's table: each
    # hinted gap g^e, e >= 0 by the DEREF through it, moves the offset on by e + 1.
    # cov and ent are the coverage slot and the table entry the next claim takes at
    # gap zero; out receives them for the claim after the last. Every claim of the list
    # writes the same mark, its first count: the walk cannot revisit a slot, and any
    # other writer's value differs, so a slot written twice still conflicts.
    for j in unroll(0, n):
        gap = hint_witness("child_claim_gap")
        assert_gpow(gap)
        cov = cov * gap
        gap2 = gap * gap
        ent = ent * (gap2 * gap2)
        cov[GEN ** j] = mark
        for c in unroll(0, 4):
            blk[4 * j + c] = ent[GEN ** (4 * j + c)]
    out[0] = cov * GEN ** n
    out[1] = ent * GEN ** (4 * n)
    return


def child_claim_list_mono(entries_ptr, region, base, limit_g, bigs, groups, rest):
    # The walk of a list at strictly increasing offsets o_j = e_0 + ... + e_j + j, every
    # e_j in [0, 2^h): its first offset is at least zero, and the count of claims keeps
    # the sum far from wrapping, so bounding its last offset below the region's size
    # (child_claim_list_mono_last) bounds them all. A record carries the sponge state,
    # then the walk's coverage slot and table entry.
    chain = HeapBuf((bigs * groups * GEN) ** MONO_REC)
    zero_state(chain)
    chain[GEN ** KECCAK_STATE] = region
    chain[GEN ** (KECCAK_STATE + 1)] = entries_ptr
    for xq in mul_range(1, bigs):
        rec = chain * xq ** MONO_REC
        nxt = rec * GEN ** MONO_REC
        blk = StackBuf(4 * CLAIM_BIG)
        walk = StackBuf(2)
        child_claims_mono(rec[GEN ** KECCAK_STATE], rec[GEN ** (KECCAK_STATE + 1)], base, blk, walk, CLAIM_BIG)
        nxt[GEN ** KECCAK_STATE] = walk[0]
        nxt[GEN ** (KECCAK_STATE + 1)] = walk[1]
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=rec[0:KECCAK_STATE], final=0)
    mid = chain * bigs ** MONO_REC
    for xq in mul_range(1, groups):
        rec = mid * xq ** MONO_REC
        nxt = rec * GEN ** MONO_REC
        blk = StackBuf(4 * CLAIM_GROUP)
        walk = StackBuf(2)
        child_claims_mono(rec[GEN ** KECCAK_STATE], rec[GEN ** (KECCAK_STATE + 1)], base, blk, walk, CLAIM_GROUP)
        nxt[GEN ** KECCAK_STATE] = walk[0]
        nxt[GEN ** (KECCAK_STATE + 1)] = walk[1]
        keccak_cells(blk, nxt[0:KECCAK_STATE], state=rec[0:KECCAK_STATE], final=0)
    last = mid * groups ** MONO_REC
    d0, d1 = match(log(rest), range(0, CLAIM_GROUP), lambda k: child_claim_list_mono_last(last, region, base, limit_g, k))
    return d0, d1


def child_claim_list_mono_last(rec, region, mark, limit_g, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=rec[0:KECCAK_STATE], len=0)
        cov_end = rec[GEN ** KECCAK_STATE]
    else:
        blk = StackBuf(4 * CLAIM_GROUP)
        walk = StackBuf(2)
        child_claims_mono(rec[GEN ** KECCAK_STATE], rec[GEN ** (KECCAK_STATE + 1)], mark, blk, walk, k)
        keccak_cells(blk[0:4 * k], digest, state=rec[0:KECCAK_STATE])
        cov_end = walk[0]
    # The offset after the last claim is at most the region's size.
    assert log(cov_end / region) < log(limit_g * GEN)
    return digest[0], digest[1]


def child_claim_list_last(state, entries_ptr, region, marks, last_g, k: Const):
    digest = StackBuf(2)
    if const(k == 0):
        keccak_cells([0], digest, state=state[0:KECCAK_STATE], len=0)
    else:
        blk = StackBuf(4 * CLAIM_GROUP)
        child_claims(entries_ptr, region, marks, last_g, blk, k)
        keccak_cells(blk[0:4 * k], digest, state=state[0:KECCAK_STATE])
    return digest[0], digest[1]



# ================================ LeanDA ===============================
# Hash the encoded rows and build the membership vector from the challenge, then check
# their inner products. The external verifier derives the challenge from the root;
# recursion preserves both.


def da_verify(g_squares):
    # Returns the commitment root, two cells, and the membership challenge, one.
    # Only the tree over the blob roots walks the padded count; a padding blob's root
    # is a constant, which the gap loop writes without hashing anything.
    shape = StackBuf(2)
    hint_witness(shape, "da_shape")  # n_blob, then log2 of the padded count
    n_blob_g = shape[0]
    g_log_pad = shape[1]
    n_pad_g, gap_g = da_row_shape(n_blob_g, g_log_pad, g_squares)

    # The challenge, hashed below as its two lanes and two zero ones.
    z = hint_witness("da_challenge")
    zs, top_leaves, cell_factors, offsets = da_vector(z)

    # A blob's region: its tree, then its running sum, a fresh write-once cell per column.
    blobs = HeapBuf(n_blob_g ** DA_REGION)
    rowbase = HeapBuf(n_blob_g)
    for xi in mul_range(1, n_blob_g):
        base = blobs * (xi ** DA_REGION)
        rowbase[xi] = base
        base[GEN ** DA_SUM] = 0

    for xb in mul_range(1, GEN ** DA_CELLS):
        da_verify_column(xb, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets)

    roots = HeapBuf(n_pad_g ** 4)
    for xi in mul_range(1, n_blob_g):
        base = rowbase[xi]
        assert base[GEN ** (DA_SUM + DA_CELLS)] == 0
        b0, b1 = da_levels(base, DA_CELLS, DA_BLOCK_BITS)
        slot = roots * (xi ** 2)
        slot[1] = b0
        slot[GEN] = b1
    for xd in mul_range(1, gap_g):
        pad = roots * (n_blob_g ** 2) * (xd ** 2)
        pad[1] = DA_PAD_BLOB_0
        pad[GEN] = DA_PAD_BLOB_1
    r0, r1 = match(log(g_log_pad), range(0, DA_TREE_ARMS), lambda k: da_levels(roots, 2 ** k, k))
    return r0, r1, z


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


def da_verify_column(xb, n_blob_g, rowbase, zs, top_leaves, cell_factors, offsets):
    # Column log(xb) of every blob: its weights expand the tree inside a cell from the
    # column's leaf of the tree above; a cell's digest is leaf log(xb) of its blob's tree,
    # and its inner product with the weights joins its blob's running sum.
    lvals = da_expand(top_leaves[xb], cell_factors, zs, offsets * xb ** DA_LOG_CELL, DA_LOG_CELL - 1, DA_LOG_CELL)
    xb2 = xb * xb
    for xi in mul_range(1, n_blob_g):
        d0, d1, s = da_verify_cell(lvals)
        base = rowbase[xi]
        chain = base * xb
        chain[GEN ** (DA_SUM + 1)] = chain[GEN ** DA_SUM] + s
        leaf = base * xb2
        leaf[1] = d0
        leaf[GEN] = d1
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
    st = StackBuf(2)
    keccak_cells(packed, st)
    return st[0], st[1], s


def da_levels(tree, n: Const, log_n: Const):
    # The internal levels of a Merkle tree whose leaves already sit at level 0 of
    # `tree` (2 cells a node, level lvl at 4n - 4n//2**lvl). Returns the root pair.
    for lvl in unroll(0, log_n):
        for xp in mul_range(1, GEN ** (n // 2 ** (lvl + 1))):
            a = tree * (GEN ** (4 * n - 4 * n // 2 ** lvl)) * (xp ** 4)
            b = tree * (GEN ** (4 * n - 4 * n // 2 ** (lvl + 1))) * (xp * xp)
            keccak(a[0:2], a[2:4], b[0:2])
    return tree[GEN ** (4 * n - 4)], tree[GEN ** (4 * n - 3)]


def da_vector(z):
    # L(x) = prod_(j < DA_LOG_K) (1 + z_j Vhat_j(x)), z_j = z^(2^j), as a binary tree over
    # x's bits from the top down: factor j depends only on the bits from j up, so a node
    # is its parent times one factor. The tree over the cell index runs once; each column
    # expands the tree inside a cell from its leaf, its factors shifted by the cell
    # index's part of each Vhat_j (da_column_offsets).
    zs = HeapBuf(DA_LOG_M)
    zj = z
    for j in unroll(0, DA_LOG_K):
        zs[GEN ** j] = zj
        zj = zj * zj
    zs[GEN ** DA_LOG_K] = 0  # the top bit splits without a factor: the degree bound
    above_top = HeapBuf(DA_LOG_M)  # nothing sits above the tree over the cell index
    for j in unroll(DA_LOG_CELL, DA_LOG_M):
        above_top[GEN ** j] = 0
    top_factors = da_factors(zs, DA_LOG_K, DA_BLOCK_BITS, 0)
    top_leaves = da_expand(1, top_factors, zs, above_top, DA_LOG_K, DA_BLOCK_BITS)
    cell_factors = da_factors(zs, DA_LOG_CELL - 1, DA_LOG_CELL, DA_CELLS)
    offsets = da_column_offsets(zs)
    return zs, top_leaves, cell_factors, offsets


def da_factors(zs, top: Const, depth: Const, at: Const):
    # 1 + z_j Vhat_j(x) for each parent node n of a product tree over bits top, top - 1, ...,
    # in heap order: j the bit n splits and x the point its path's bits make, DA_VHAT[at + n].
    factors = HeapBuf(DA_CELL)  # the deepest tree's parents, the one inside a cell
    for d in unroll(0, depth):
        z = zs[GEN ** (top - d)]
        for y in unroll(0, 2 ** d):
            factors[GEN ** (2 ** d + y)] = z * DA_VHAT[at + 2 ** d + y] + 1
    return factors


def da_expand(root, factors, zs, shifts, top: Const, depth: Const):
    # The product tree below `root` over bits top, top - 1, ..., in heap order: node n's
    # children 2n and 2n + 1 are n times its factor at the two values of the bit j it
    # splits, factors[n] + shifts[j] and that plus z_j. Returns a pointer to its leaves.
    nodes = StackBuf(2 * DA_CELL)  # the deepest tree's, the one inside a cell
    nodes[1] = root
    for d in unroll(0, depth):
        z = zs[GEN ** (top - d)]
        shift = shifts[GEN ** (top - d)]
        for y in unroll(0, 2 ** d):
            nodes[2 ** (d + 1) + 2 * y] = nodes[2 ** d + y] * (factors[GEN ** (2 ** d + y)] + shift)
            nodes[2 ** (d + 1) + 2 * y + 1] = nodes[2 ** (d + 1) + 2 * y] + nodes[2 ** d + y] * z
    leaves = addr(nodes)
    return leaves * GEN ** (2 ** depth)


def da_column_offsets(zs):
    # offsets[DA_LOG_CELL * h + j] = z_j Vhat_j at the cell index h's bits, for each factor
    # j inside a cell: zero at h = 0, then one doubling per bit of h.
    offsets = HeapBuf(DA_LOG_CELL * DA_CELLS)
    for j in unroll(0, DA_LOG_CELL):
        offsets[GEN ** j] = 0
    for b in unroll(0, DA_BLOCK_BITS):
        steps = HeapBuf(DA_LOG_CELL)
        for j in unroll(0, DA_LOG_CELL):
            steps[GEN ** j] = zs[GEN ** j] * DA_VHAT_COLUMN[DA_LOG_CELL * b + j]
        for xh in mul_range(1, GEN ** (2 ** b)):
            src = offsets * xh ** DA_LOG_CELL
            dst = src * GEN ** (DA_LOG_CELL * 2 ** b)
            for j in unroll(0, DA_LOG_CELL):
                dst[GEN ** j] = src[GEN ** j] + steps[GEN ** j]
    return offsets


# ================================ the aggregation node ==============================


def main():
    # One node of an aggregation tree: n_raw_lean_xmss leanXMSS signatures, n_raw_lean_sphincs
    # leanSPHINCS signatures and n_children sub-proofs OF THIS SAME BYTECODE. A claim of
    # either scheme is a pubkey and the message it signed, and each signature is
    # verified against the claim in its own coverage slot; a leanXMSS signature carries
    # its own leaf index. It publishes at most one DA digest: that of the blob matrix it
    # checks, or one of its children's, or none.
    #
    # The declared lists are what the node publishes; the duplicate slots absorb claims a
    # child covers that the set does not declare. The coverage table is one region
    # per scheme, each its declared claims then its own duplicates:
    #
    #   [leanXMSS: declared | dup][leanSPHINCS: declared | dup]
    #
    # so one range check per write keeps each writer inside its own region: that is
    # what makes the statement's split mean which scheme verified which claim. A
    # slot is four cells, a pubkey and the message that pubkey signed.
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
    lx_slots_g = n_lx_g * n_xdup_g
    lean_sphincs_slots_g = n_lean_sphincs_g * n_sdup_g
    # The sum of both regions bounds the coverage indices, so it is what has to sit
    # below the minimum memory size.
    n_total_g = lx_slots_g * lean_sphincs_slots_g
    assert log(n_total_g) < MAX_KEYS

    # The proving environment (the proof system's version and this bytecode) as one
    # digest. It rides the statement rather than the bytecode, so nothing here has to
    # know its own hash; the outer verifier pins it, and every child statement rebuilt
    # below copies it, which is what keeps a whole tree on one bytecode.
    fs_seed = StackBuf(2)
    hint_witness(fs_seed, "fs_seed")
    seed_0 = fs_seed[0]
    seed_1 = fs_seed[1]

    # ---- the claim lists ----
    g_squares = exponent_tables()

    # One table per scheme: its declared list (strictly sorted, checked by the outer
    # verifier, which holds it) followed by its own duplicate slots. The coverage
    # indices below run over one space: leanXMSS, then leanSPHINCS.
    #
    # Each list's digest is a plain hash of its claims, 64 bytes a claim, its padding
    # binding its length; the statement carries the two digests side by side.
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

    # ---- coverage ----
    # Every one of the n_total slots is written exactly once: write-once memory
    # rejects a second write (each writer's marks lie in its own range of counts, and a
    # gap-walked child list never revisits a slot, so two writes to one slot disagree),
    # and the count below rejects a missed one. So every
    # declared claim is covered by a direct check of its own kind or by a verified
    # child. Each writer is confined to its own region.
    cover = HeapBuf(n_total_g)
    sp_cover = cover * lx_slots_g  # the leanSPHINCS region
    # byte_bits[g^v] = v, read at a hinted byte's exponent (sp_from_bytes).
    byte_bits = HeapBuf(SP_BYTE_VALUES)
    for v in unroll(0, SP_BYTE_VALUES):
        byte_bits[GEN ** v] = v
    # The chain indices a leanXMSS chain step hashes after its value, those no other
    # cell holds (`walk`), set once here and carried through the signature loop.
    lx_tags = StackBuf(LX_N_TAGS)
    for i in unroll(1, LX_V):
        if const(LX_TAG_SLOT[i] != 0):
            lx_tags[LX_TAG_SLOT[i] - 1] = i
    for xi in mul_range(1, n_raw_x_g):
        idx = hint_witness("raw_index")
        # A runtime bound, whose `n_total < 2^MIN_LOG_MEM` precondition is
        # discharged by `assert log(n_total_g) < MAX_KEYS` above. Without it this
        # degenerates to what DEREF alone gives and an index could reach past
        # `cover`, which is the whole bijection. The bound is the leanXMSS region, so
        # a raw leanXMSS signature covers no leanSPHINCS claim.
        assert log(idx) < log(lx_slots_g)
        cover[idx] = xi
        verify_lean_xmss(lx_table * (idx ** 4), lx_tags)
    for xj in mul_range(1, n_raw_s_g):
        off_hint = hint_witness("sp_raw_index")
        assert log(off_hint) < log(lean_sphincs_slots_g)
        sp_cover[off_hint] = n_raw_x_g * xj
        verify_sig_lean_sphincs(lean_sphincs_table * (off_hint ** 4), byte_bits)

    # ---- data availability ----
    # One DA digest per child, read off its statement below, then the node's own:
    # H(root, challenge) of its blob matrix, or zeros without blobs.
    da_digests = HeapBuf((n_children_g * GEN) ** 2)
    own_da = da_digests * n_children_g ** 2
    if n_direct_da_g == GEN:
        root_0, root_1, z = da_verify(g_squares)
        keccak([root_0, root_1], [z, 0], own_da[0:2])
    else:
        own_da[1] = 0
        own_da[GEN] = 0

    # ---- children ----
    child_pi = HeapBuf(n_children_g * n_children_g)
    child_fresh = HeapBuf(n_children_g ** DEFER_SIZE)
    child_carried = HeapBuf(n_children_g ** DEFER_STMT_CELLS)
    written = HeapBuf(n_children_g * GEN)  # loop-carried write count, one per child
    written[GEN ** 0] = n_raw_x_g * n_raw_s_g
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
        cx_0, cx_1 = child_claim_list_digest(lx_table, cover, base, lx_slots_g, nsub_x_g)
        cs_0, cs_1 = child_claim_list_digest(lean_sphincs_table, sp_cover, base * nsub_x_g, lean_sphincs_slots_g, nsub_s_g)
        carried = child_carried * xc ** DEFER_STMT_CELLS
        hint_witness(carried[0:DEFER_STMT_CELLS], "child_defer")
        child_da = da_digests * xc ** 2
        hint_witness(child_da[0:2], "child_da")
        pi_0, pi_1 = statement_digest(seed_0, seed_1, cx_0, cx_1, cs_0, cs_1, child_da[1], child_da[GEN], carried)
        pi = xc * xc
        child_pi[pi] = pi_0
        child_pi[pi * GEN] = pi_1
        verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, child_fresh * xc ** DEFER_SIZE)
        written[xc * GEN] = base * nsub_g
    assert written[n_children_g] == n_total_g

    # The published DA digest: a child's or the node's own, its own if it has blobs.
    da_pick = hint_witness("da_pick")
    assert log(da_pick) < log(n_children_g * GEN)
    assert (da_pick + n_children_g) * (n_direct_da_g + 1) == 0
    da = da_digests * da_pick ** 2

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
        aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, g_squares * GEN ** WIN_TAB_AT)

    own_0, own_1 = statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da[1], da[GEN], defer_stmt)
    pub_ptr = GEN ** 0
    assert pub_ptr[1] == own_0
    assert pub_ptr[GEN] == own_1
    return


def aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, tabs):
    # Every child contributes two claims on the stacked bytecode: the one IT
    # deferred (carried in its statement) and the fresh one raised by verifying its
    # proof. A fresh transcript binds all of them, samples the batching
    # coefficient, and one sumcheck reduces the lot to one claim, which is what the
    # node then defers in its own statement.
    bc_msgs = HeapBuf(BC_LAM_WORDS + BC_ROUND_WORDS * BYTECODE_VARS)  # the batching challenge's nonce, then a round's words
    hint_witness(bc_msgs[0:BC_LAM_WORDS + BC_ROUND_WORDS * BYTECODE_VARS], "bc_sumcheck_msgs")
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
    # One challenge lam, after a grind whose nonce follows the last full rate: child i's fresh
    # claim takes lam^(2i), its carried one lam^(2i+1). Fresh and carried share one
    # layout (point, then value), so the two differ only in which buffer they come
    # from. Each record holds the child's power of lam^2, then the running value.
    absorbed_cap = fs_load(absorbed, 0, 1)
    full = fs_perm_pending(absorbed_cap, absorbed, FS_CELLS)
    if const(BATCH_LAM_GRIND_BITS == 0):
        st = full
    else:
        nonce_rate = StackBuf(8)
        st = fs_absorb_nonce(full, nonce_rate, 0, bc_msgs[GEN ** 0])
        grind_check(st[1], tabs, BATCH_LAM_GRIND_BITS)
    lam = st[0]
    lam_sq = lam * lam
    bc_chain = HeapBuf((n_children_g * GEN) ** PAIR_SLOTS)
    bc_chain[GEN ** 0] = 1
    bc_chain[GEN ** 1] = 0
    for xc in mul_range(1, n_children_g):
        row = bc_chain * xc ** PAIR_SLOTS
        lam_pow = row[GEN ** 0]
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        nxt = row * GEN ** PAIR_SLOTS
        nxt[GEN ** 0] = lam_pow * lam_sq
        nxt[GEN ** 1] = row[GEN ** 1] + lam_pow * (fresh[GEN ** FRESH_BC_VALUE] + lam * carried[GEN ** DEFER_STMT_BC_VALUE])
    bc_end = bc_chain * n_children_g ** PAIR_SLOTS
    bc_running = bc_end[GEN ** 1]
    bc_point = HeapBuf(BYTECODE_VARS)
    fs0, fs1, fs2, fs3, fs4, bc_running = batch_sumcheck(st[8], st[9], st[10], st[11], st[12], bc_msgs * GEN ** BC_LAM_WORDS, bc_running, bc_point, tabs, BYTECODE_VARS)
    bc_point1 = HeapBuf(BYTECODE_VARS)  # 1 + bc_point, so an eq factor is one XOR
    for k in unroll(0, BYTECODE_VARS):
        bc_point1[GEN ** k] = 1 + bc_point[GEN ** k]
    bc_wsum = HeapBuf(n_children_g * GEN)
    bc_wsum[GEN ** 0] = 0
    for xc in mul_range(1, n_children_g):
        fresh = fresh_row[xc]
        carried = carried_row[xc]
        for k in unroll(0, BYTECODE_VARS):
            rk1 = bc_point1[GEN ** k]
            if const(k == 0):
                eq_fresh = fresh[GEN ** k] + rk1
                eq_carried = carried[GEN ** k] + rk1
            else:
                eq_fresh *= fresh[GEN ** k] + rk1
                eq_carried *= carried[GEN ** k] + rk1
        row = bc_chain * xc ** PAIR_SLOTS
        bc_wsum[xc * GEN] = bc_wsum[xc] + row[GEN ** 0] * (eq_fresh + lam * eq_carried)
    assert bc_running == bytecode_star * bc_wsum[n_children_g]

    for k in unroll(0, BYTECODE_VARS):
        defer_stmt[GEN ** k] = bc_point[GEN ** k]
    defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = bytecode_star
    return
