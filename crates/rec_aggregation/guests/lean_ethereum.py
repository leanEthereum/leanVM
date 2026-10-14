# The recursive aggregation guest: zkDSL, not runnable Python (see
# crates/lean_compiler/zkDSL.md). One node of an aggregation tree verifies raw XMSS
# and SPHINCS+ signatures and sub-proofs OF THIS SAME BYTECODE, and publishes the
# statement digest binding its signature claims and a possibly empty list of LeanDA roots.
# It may check a blob matrix directly and retain any roots proved by its children.
# Reading order: `main` is the
# node, `verify_sub` the in-circuit copy of `leanvm_core::cpu::verify`, and
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
# One sumcheck round of the bus GKR or the table batch.
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
LAYER_ROW = 6
LAYER_POS = 7
LAYER_SLOTS = 8
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
# three leaf claims. FLOORS[t] is the table's tau floor (the Keccak reduction is
# sized for at least one block of 2^9 steps).
TABLE_XOR = 0
TABLE_MUL = 1
TABLE_SET = 2
TABLE_DEREF = 3
TABLE_JUMP = 4
TABLE_SHA3 = 5
N_TABLES = N_TABLES_PLACEHOLDER
KECCAK_MIN_STEPS_LOG = 9
FLOORS = [0, 0, 0, 0, 0, KECCAK_MIN_STEPS_LOG]
N_TABLE_COLS = N_TABLE_COLS_PLACEHOLDER
TABLE_COLS_CAP = TABLE_COLS_CAP_PLACEHOLDER
ETA_OFFSET = ETA_OFFSET_PLACEHOLDER
ETA_FORM_BASE = ETA_FORM_BASE_PLACEHOLDER
N_ETA_POWS = N_ETA_POWS_PLACEHOLDER

# ------------------------------------------------- Keccak, by GKR over its rounds
# q_keccak holds a step's state every KECCAK_DEPTH rounds, a lane per slot and a word
# per step; a pack is KECCAK_PACK consecutive steps, embedded in a polynomial of
# degree under KECCAK_EMBED_BITS whose products have KECCAK_PROD_BITS coefficients.
# The *_START / *_IDX pairs are index lists: row i is IDX[START[i] .. START[i + 1]].
KECCAK_DEPTH = KECCAK_DEPTH_PLACEHOLDER
KECCAK_SEGMENTS = KECCAK_SEGMENTS_PLACEHOLDER
KECCAK_SEG_LOG = 2
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
KECCAK_IOTA_BITS = 7   # iota flips slices 2^i - 1 of lane 0 only
QKECCAK_SLOT_LOG = QKECCAK_SLOT_LOG_PLACEHOLDER
# A claim's record: its value, the sum of its instance weights, pointers to its
# point, its lane table, its slice table and the local point that table is the eq
# of, then the instance weights and its position weights where iota flips.
KC_VALUE = 0
KC_KAPPA = 1
KC_POINT = 2
KC_LANES = 3
KC_SLICES = 4
KC_LOCAL = 5
KC_MU = 6
KC_IOTA = KC_MU + KECCAK_PACK
KC_SIZE = KC_IOTA + KECCAK_IOTA_BITS
# One round of a layer's sumcheck over packs and segments.
KR_FS0 = 0
KR_FS1 = 1
KR_CURSOR = 2
KR_CLAIM = 3
KR_SCALE = 4
KR_SLOTS = 5

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
SEL_SHARED_SRC = 2 + TABLE_SHA3         # the kappa source whose bus blocks share selector tables
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
POINT_BUF_ZETA = 0
POINT_BUF_RHO = 1
POINT_BUF_PI = 2
POINT_BUF_QKECCAK_RHO = 3
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
AGG_SEED_0 = AGG_SEED_0_PLACEHOLDER
AGG_SEED_1 = AGG_SEED_1_PLACEHOLDER
# The statement digest's preimage: the STMT_HEADER header values as the 16-byte
# cells they already are (the seed and the signer-set digest, which itself binds
# the leaf index groups and every count), then the deferred cells' tower limbs, two to
# a cell. No domain tag: the seed leads, and it binds this bytecode and the
# Keccak relation.
STMT_HEADER = STMT_HEADER_PLACEHOLDER
STMT_DEFER_OFF = STMT_HEADER
STMT_ODD = STMT_ODD_PLACEHOLDER
STMT_PAIRS = STMT_PAIRS_PLACEHOLDER
STMT_CELLS = STMT_DEFER_OFF + 3 * STMT_PAIRS

# ------------------------------------------------------------------ the hash
# Every hash is SHA3-256 in the cell encoding (primitives::hash::hash): a `sha3`
# block absorbs eight cells, and its output is the SHA3_STATE-cell sponge state,
# whose first two cells are the digest. A hash of runtime length carries that
# state through a heap run between loop frames, SHA3_STATE cells a step.
SHA3_STATE = SHA3_STATE_PLACEHOLDER
# One step of such a chain: the state, then whatever count the loop threads with it.
STATE_SLOTS = SHA3_STATE + 1

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
DIGEST_CELLS = 2
# Tweak table (one 1-cell tweak per index): encoding | V·CHAIN_STEPS chain |
# wots-pk | merkle. Derived in-circuit, once per leaf index group the statement carries.
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
SP_N_FTS = SP_K - 1                   # the forest drops the last index's tree
# The message digest is h + k*a bits of a hash output: the whole low cell and
# the low 48 bits of the high one. Decomposing the high cell's low lane covers
# them, so the buffer holds three lanes and the top 16 are never read.
SP_BIT_LANES = 3
SP_BIT_CELLS = SP_BIT_LANES * BASE_FIELD_BITS
# Native tweak prefixes, including the protocol domain separator and type.
SP_TW_CHAIN = SP_TW_CHAIN_PLACEHOLDER
SP_TW_LEAF = SP_TW_LEAF_PLACEHOLDER
SP_TW_NODE = SP_TW_NODE_PLACEHOLDER
SP_TW_ENC = SP_TW_ENC_PLACEHOLDER
SP_TW_FTS_LEAF = SP_TW_FTS_LEAF_PLACEHOLDER
SP_TW_FTS_NODE = SP_TW_FTS_NODE_PLACEHOLDER
SP_TW_FTS_ROOTS = SP_TW_FTS_ROOTS_PLACEHOLDER
SP_TW_MSG = SP_TW_MSG_PLACEHOLDER
# Tweak layout: protocol_domain_sep | type | layer | zero | p | tree | index.
# Each 32-bit field stays within one 64-bit lane.
SP_LAY_MUL = 2 ** 16
SP_P_MUL = 2 ** 32
SP_TAU_POS = BASE_FIELD_BITS
SP_J_POS = BASE_FIELD_BITS + 32
SP_CHAIN_MUL = SP_CHAIN_LENGTH * SP_P_MUL   # chain i's tweaks start at p = 2^w * i
# The encoding counter, LE_32 in the low four bytes of its cell: bounded by
# decomposing exactly that many bits, so the guest accepts no preimage the native
# verifier cannot parse.
SP_COUNTER_BITS = 32

# --------------------------------------------------------------- node capacities
# MAX_KEYS caps the coverage table's slots, both schemes' declared keys and their
# duplicates, which is what the coverage range check needs below 2^MIN_LOG_MEM;
# MAX_RECURSIONS is the arity of an aggregation tree; MAX_LEAF_INDICES caps the runtime
# number of XMSS leaf index groups.
MAX_KEYS = MAX_KEYS_PLACEHOLDER
MAX_DA_ROOTS = MAX_DA_ROOTS_PLACEHOLDER
DA_ROOT_COUNTS = DA_ROOT_COUNTS_PLACEHOLDER
MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER
MAX_LEAF_INDICES = MAX_LEAF_INDICES_PLACEHOLDER


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


@inline
def fs_compress(state, scalar, tail, out):
    # SHA3 requires block[0] to have zero top limb, binding the hinted top.
    limbs = StackBuf(3)
    hint_f192_limbs(limbs, scalar)
    assert_in_k(limbs[2], tail)
    block = StackBuf(2)
    block[0] = scalar + Y_TOWER * Y_TOWER * limbs[2]
    block[1] = limbs[2] + Y_TOWER * tail
    sha3(state[0:2], block, out)
    return


@inline
def obs(state, x):
    # Bind one scalar into the chain: state <- compress(state, (x, DS_OBSERVE)).
    # Returns the successor StackBuf; the call site aliases it (zero copies).
    nb = StackBuf(SHA3_STATE)
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
def squeeze_state(state):
    nb = StackBuf(SHA3_STATE)
    sha3(state[0:2], [0, Y_TOWER * DS_SQ], nb)
    return nb


@inline
def squeeze(state):
    # Ratchet: the canonical 128+128 digest is the new state; its first three K
    # lanes are reassembled as the F192 challenge.
    nb = squeeze_state(state)
    challenge = challenge_from_state(nb)
    return nb, challenge


@inline
def absorb_nonce(state, x):
    # Full-field grinding nonce absorb: [x.c0, x.c1, x.c2, DS_POW_NONCE].
    nb = StackBuf(SHA3_STATE)
    fs_compress(state, x, DS_POW_NONCE, nb)
    return nb


@inline
def squeeze_step(state_0, state_1):
    # `squeeze` exposing BOTH output words, so a query-squeeze loop can chain the
    # state through a heap buffer. Returns (challenge, next_state_0, next_state_1).
    state = [state_0, state_1]
    next_state = squeeze_state(state)
    challenge = challenge_from_state(next_state)
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
    base = StackBuf(SHA3_STATE)
    sha3(st, [0, Y_TOWER * DS_POW_BASE], base)
    out = StackBuf(SHA3_STATE)
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
    # The rounds of a claim-batching sumcheck: two hinted values per round
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
def verify_merkle_path(leaf_0, leaf_1, direction_bits, depth: Const):
    # Hinted child pairs are hashed in order; the boolean query bit selects the
    # child that must equal the running node, binding each link of the path.
    path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:4 * depth], "merkle_children")
    path_ptr = addr(path)
    node_0 = leaf_0
    node_1 = leaf_1
    for level in unroll(0, depth):
        dir_bit = direction_bits[GEN ** level]
        selected = path_ptr * GEN ** (4 * level) * (1 + dir_bit * (1 + GEN ** 2))
        selected[1] = node_0
        selected[GEN] = node_1
        parent = StackBuf(SHA3_STATE)
        sha3(path[4 * level:4 * level + 2], path[4 * level + 2:4 * level + 4], parent)
        node_0 = parent[0]
        node_1 = parent[1]
    return node_0, node_1


@inline
def hash_cap_node(cap, index):
    children = cap * index ** 4
    parent = StackBuf(SHA3_STATE)
    sha3([children[1], children[GEN]], [children[GEN ** 2], children[GEN ** 3]], parent)
    cap[index * index] = parent[0]
    cap[GEN * index * index] = parent[1]
    return


def verify_merkle_cap(cap, flags, depth: Const):
    if depth != 0:
        hash_cap_node(cap, GEN)
        flags[GEN] = 1
        for parent in mul_range(GEN, GEN ** (2 ** (depth - 1))):
            for side in unroll(0, 2):
                child = parent * parent * GEN ** side
                if flags[child] != 0:
                    flags[parent] = 1  # every active node forces its parent to be hashed
                    hash_cap_node(cap, child)
    return cap[GEN ** 2], cap[GEN ** 3]


# ============================== the stacked WHIR opening ============================


def opening_fold(fs0, fs1, cursor, c0, c1, c2):
    fs = [fs0, fs1]
    fs, r = squeeze(fs)
    claim = (c2 * r + c1) * r + c0
    fs, c0, cursor = fs_next(fs, cursor)
    fs, c2, cursor = fs_next(fs, cursor)
    return fs[0], fs[1], cursor, claim, c0, c2, r


def opening_ood_point(fs0, fs1, point, n: Const):
    # One specialization per point dimension, the state riding frame cells.
    fs = [fs0, fs1]
    for x in unroll(0, n):
        fs, r = squeeze(fs)
        point[GEN ** x] = r
    return fs[0], fs[1]


def opening_final_message(fs0, fs1, cursor, out, n: Const):
    fs = [fs0, fs1]
    for i in unroll(0, n):
        fs, value, cursor = fs_next(fs, cursor)
        out[GEN ** i] = value
    return fs[0], fs[1], cursor


def opening_row_weights(point, out, folds: Const, reverse: Const):
    for i in unroll(0, 2 ** folds):
        if reverse == 1:
            slot = 2 ** folds - 1 - i
        else:
            slot = i
        out[GEN ** i] = eq_weight(point, folds, slot, 0)
    return


def opening_queries(cap, flags, query_weights, query_bit_ptrs, row_eq_weights, n_queries_g, base: Const, interleave: Const, leaf_cells: Const, depth: Const, cap_depth: Const):
    # Specialize by row and path shape so opening configurations share query code.
    query_sum_chain = HeapBuf(n_queries_g * GEN)
    query_sum_chain[GEN ** 0] = 0
    for xe in mul_range(1, n_queries_g):
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
            for jb in unroll(0, interleave // 4):
                e0 = row[4 * jb]
                e1 = row[4 * jb + 1]
                e2 = row[4 * jb + 2]
                e3 = row[4 * jb + 3]
                packed_row[2 * jb] = pack64x2(e0, e1)
                packed_row[2 * jb + 1] = pack64x2(e2, e3)
                row_dot += e0 * row_eq_weights[GEN ** (4 * jb)] + e1 * row_eq_weights[GEN ** (4 * jb + 1)] + e2 * row_eq_weights[GEN ** (4 * jb + 2)] + e3 * row_eq_weights[GEN ** (4 * jb + 3)]
        else:
            # Pack the checked tower limbs into the leaf's contiguous byte image.
            for jb in unroll(0, 3 * interleave // 4):
                packed_row[2 * jb] = pack64x2(row[4 * jb], row[4 * jb + 1])
                packed_row[2 * jb + 1] = pack64x2(row[4 * jb + 2], row[4 * jb + 3])
            for jw in unroll(0, interleave):
                if 3 * jw % 2 == 0:
                    # limbs (3w, 3w+1) are a pack; add Y^2 * limb(3w+2).
                    row_word = packed_row[3 * jw // 2] + Y_TOWER * Y_TOWER * row[3 * jw + 2]
                else:
                    # limbs (3w+1, 3w+2) are a pack; shift it by Y and add limb(3w).
                    row_word = row[3 * jw] + Y_TOWER * packed_row[(3 * jw + 1) // 2]
                row_dot += row_word * row_eq_weights[GEN ** jw]
        # Hash the packed row, eight cells a block.
        leaf_hash_state = StackBuf(SHA3_STATE)
        sha3_cells(packed_row[0:leaf_cells], leaf_hash_state)
        query_sum_chain[xe * GEN] = query_sum_chain[xe] + query_weights[xe] * row_dot
        direction_bits = query_bit_ptrs[xe]
        path_depth = depth - cap_depth
        node_0, node_1 = verify_merkle_path(leaf_hash_state[0], leaf_hash_state[1], direction_bits, path_depth)
        if cap_depth != 0:
            parent = GEN ** (2 ** (cap_depth - 1))
            for bit in unroll(0, cap_depth - 1):
                parent *= 1 + direction_bits[GEN ** (path_depth + 1 + bit)] * (1 + GEN ** (2 ** bit))
            flags[parent] = 1  # the cap check propagates this obligation to the root
            cap_index = parent * parent * (1 + direction_bits[GEN ** path_depth] * (1 + GEN))
        else:
            cap_index = GEN
        cap[cap_index * cap_index] = node_0
        cap[GEN * cap_index * cap_index] = node_1
    return query_sum_chain[n_queries_g]


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


def open_stacked(m_idx: Const, fs0, fs1, target, commit_root_0, commit_root_1, cursor):
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
    fs = [fs0, fs1]
    msg_cursor = cursor
    fs, round_quad_c, msg_cursor = fs_next(fs, msg_cursor)  # the round polynomial in coefficients
    fs, round_quad_a, msg_cursor = fs_next(fs, msg_cursor)  # bar the linear one, which the split fixes
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
            f0, f1, msg_cursor, sumcheck_target, round_quad_c, round_quad_a, fold_challenge = opening_fold(fs[0], fs[1], msg_cursor, round_quad_c, round_quad_b, round_quad_a)
            fs = [f0, f1]
            fold_challenges[GEN ** (folds_off + j)] = fold_challenge
            round_quad_b = sumcheck_target + round_quad_a

        if lvl == yr_level:
            f0, f1, msg_cursor = opening_final_message(fs[0], fs[1], msg_cursor, final_msg, yr_len)
            fs = [f0, f1]
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
                f0, f1 = opening_ood_point(fs[0], fs[1], oz, LIG_LOG_MSG_COLS[ml])
                fs = [f0, f1]
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
        opening_row_weights(fold_challenges * GEN ** folds_off, row_eq_weights, LIG_FOLDS[ml], 1 // (lvl + 1))

        cap_depth = LIG_CAP_DEPTH[ml]
        cap = merkle_caps * GEN ** (4 * LIG_CAP_OFF[ml])
        flags = cap_flags * GEN ** LIG_CAP_OFF[ml]
        root_0, root_1 = verify_merkle_cap(cap, flags, cap_depth)
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        level_query_sum = opening_queries(cap, flags, query_weights * GEN ** (lvl * max_q), query_bit_ptrs * GEN ** pos_off, row_eq_weights, GEN ** n_queries, 1 // (lvl + 1), interleave, LIG_LEAF_CELLS[ml], depth, cap_depth)

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
        f0, f1, msg_cursor, sumcheck_target, round_quad_c, round_quad_a, tail_c = opening_fold(fs[0], fs[1], msg_cursor, round_quad_c, round_quad_b, round_quad_a)
        fs = [f0, f1]
        tail_challenges[GEN ** j] = tail_c
        round_quad_b = sumcheck_target + round_quad_a
    # The closing round sends no following message.
    fs, tail_last = squeeze(fs)
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


def verify_bus_gkr(fs0, fs1, cursor, g_bus_mu, zeta):
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
    fs = [fs0, fs1]
    fs, root_push, cursor = fs_next(fs, cursor)
    root_pull = root_push
    fs, root_count, cursor = fs_next(fs, cursor)
    assert root_count != 0  # count-tree root nonzero: no read count self-cancels
    layers[GEN ** LAYER_FS0] = fs[0]
    layers[GEN ** LAYER_FS1] = fs[1]
    layers[GEN ** LAYER_CURSOR] = cursor
    layers[GEN ** LAYER_PUSH] = root_push
    layers[GEN ** LAYER_PULL] = root_pull
    layers[GEN ** LAYER_COUNT] = root_count
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
        tail_fs = [layers[GEN ** LAYER_FS0], layers[GEN ** LAYER_FS1]]
        tail_fs, lam = squeeze(tail_fs)
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
        nxt = layers * GEN ** LAYER_SLOTS
        nxt[GEN ** LAYER_FS0] = tail_fs[0]
        nxt[GEN ** LAYER_FS1] = tail_fs[1]
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            nxt[GEN ** (LAYER_PUSH + side)] = evals[2 * side] + c0 * (evals[2 * side] + evals[2 * side + 1])
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = GEN

    for x_pair in mul_range(1, pair_bounds[g_bus_mu]):
        x_layer = x_pair * x_pair * depth_shift[g_bus_mu]
        layer = layers * x_layer ** LAYER_SLOTS
        layer_fs = [layer[GEN ** LAYER_FS0], layer[GEN ** LAYER_FS1]]
        layer_fs, lam = squeeze(layer_fs)
        point_row = layer[GEN ** LAYER_ROW]
        round_pos = layer[GEN ** LAYER_POS]
        nextrow = point_row * GEN ** MU_CAP
        head = rounds * round_pos ** ROUND_SLOTS
        head[GEN ** ROUND_FS0] = layer_fs[0]
        head[GEN ** ROUND_FS1] = layer_fs[1]
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
        nxt = layer * GEN ** (2 * LAYER_SLOTS)
        nxt[GEN ** LAYER_FS0] = tail_fs[0]
        nxt[GEN ** LAYER_FS1] = tail_fs[1]
        nxt[GEN ** LAYER_CURSOR] = tcur
        for side in unroll(0, N_GKR_SIDES):
            lo = evals[4 * side] + c0 * (evals[4 * side] + evals[4 * side + 1])
            hi = evals[4 * side + 2] + c0 * (evals[4 * side + 2] + evals[4 * side + 3])
            nxt[GEN ** (LAYER_PUSH + side)] = lo + c1 * (lo + hi)
        nxt[GEN ** LAYER_ROW] = nextrow
        nxt[GEN ** LAYER_POS] = round_pos * x_layer * GEN
    last = layers * g_bus_mu ** LAYER_SLOTS
    fs = [last[GEN ** LAYER_FS0], last[GEN ** LAYER_FS1]]
    cursor = last[GEN ** LAYER_CURSOR]
    final_point_row = last[GEN ** LAYER_ROW]
    for xt in mul_range(1, g_bus_mu):
        zeta[xt] = final_point_row[xt]  # the ONE shared point
    return fs[0], fs[1], cursor, last[GEN ** LAYER_PUSH], last[GEN ** LAYER_PULL], last[GEN ** LAYER_COUNT]


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
    zeta1 = HeapBuf(g_bus_mu)  # 1 + zeta, so an eq factor 1 + b + z is one XOR
    zeta1_done = match(log(g_bus_mu), range(0, SIZE_BITS), lambda n: plus_one_run(zeta1, zeta, n))  # a match needs a target
    # The blocks sized by SEL_SHARED_SRC share one κ, block_kappa being
    # kappa_base[src] = dims_g[src - 1] for them (verify_sub), so their selector
    # runs read shared tables.
    shared_kappa_g = dims_g[GEN ** (SEL_SHARED_SRC - 1)]
    shared_len_g = g_bus_mu / shared_kappa_g
    assert log(shared_len_g) < SIZE_BITS
    shared_eq = HeapBuf(SEL_TAB_NIBBLES * SEL_TAB_EQ_STRIDE)
    shared_g = HeapBuf(SEL_TAB_NIBBLES * 16)
    shared_selector_tables(shared_eq, shared_g, zeta * shared_kappa_g, zeta1 * shared_kappa_g, g_squares * shared_kappa_g, shared_len_g)
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
                offset_bits = HeapBuf(GEN ** SIZE_BITS)
                hint_decompose_bits_exponent(offset_bits, block_off_g[GEN ** b], SIZE_BITS)
                shared = 0
                if const(BLOCK_KAPPA_SRC[b] == SEL_SHARED_SRC):
                    if const(BLOCK_KAPPA_ADJ[b] == 0):
                        shared = 1
                if const(shared == 1):
                    sel_bits = offset_bits * shared_kappa_g
                    eq_hi, goff = match(log(shared_len_g), range(0, SIZE_BITS), lambda n: block_selector_tab(sel_bits, shared_eq, shared_g, n))
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
    eq_prefix_chain(zc_peq, 1, chi, zeta1, g_zc_n)
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

    # ---- public-input binding claim: one per MEM limb, read off no stream ----
    # The VM's bind_pi_claim claims each committed MEM limb at [rm, 0..] equals
    # that limb's line through the public words, lo_0 + rm*(lo_0 + lo_1) and so
    # on, which the statement alone determines. canonical_limbs binds each word's
    # limbs and proves its top limb zero, so the top claim is zero (doc sec:e2e-pi).
    fs, rm = squeeze(fs)
    lo_0, hi_0 = canonical_limbs(pi_0)
    lo_1, hi_1 = canonical_limbs(pi_1)
    claim_pool[GEN ** claim_idx] = lo_0 + rm * (lo_0 + lo_1)
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = hi_0 + rm * (hi_0 + hi_1)
    claim_idx += 1
    claim_pool[GEN ** claim_idx] = 0
    claim_idx += 1
    return fs[0], fs[1], cursor, g_zc_n, bc_share, rm


@inline
def keccak_shift_eq(e, u, v, r: Const):
    # The multilinear extension of "x = y + r mod 64" at (a, b), a ripple of the carry
    # over the six bits: e[t], u[t], v[t] are bit t's weights for (x, y) equal, (1, 0)
    # and (0, 1). c[2t], c[2t + 1] carry the weight of each carry into bit t, the
    # second absent until r's lowest set bit.
    c = StackBuf(2 * KECCAK_Z_BITS + 2)
    if r % 2 == 0:
        c[2] = e[0]
    else:
        c[2] = u[0]
        c[3] = v[0]
    for t in unroll(1, KECCAK_Z_BITS):
        if (r // 2 ** t) % 2 == 0:
            if r % 2 ** t == 0:
                c[2 * t + 2] = c[2 * t] * e[t]
            else:
                c[2 * t + 2] = c[2 * t] * e[t] + c[2 * t + 1] * u[t]
                c[2 * t + 3] = c[2 * t + 1] * v[t]
        else:
            if r % 2 ** t == 0:
                c[2 * t + 2] = c[2 * t] * u[t]
                c[2 * t + 3] = c[2 * t] * v[t]
            else:
                c[2 * t + 2] = c[2 * t] * u[t]
                c[2 * t + 3] = c[2 * t] * v[t] + c[2 * t + 1] * e[t]
    out = StackBuf(1)
    if r == 0:
        out[0] = c[2 * KECCAK_Z_BITS]
    else:
        out[0] = c[2 * KECCAK_Z_BITS] + c[2 * KECCAK_Z_BITS + 1]
    return out[0]


@inline
def keccak_form(lanes, shifts, f_lanes):
    # <L^T(E), f> for theta, rho, pi's transpose L^T, on weights that factor as lane
    # times slice: E = lanes (x) eZ and f = f_lanes (x) fZ, the slices entering only
    # through shifts[r] = sum_z fZ[z] eZ[(z + r) % 64].
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
            f_weight = f_lanes[GEN ** (x + 5 * y)]
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


def keccak_layer(fs0, fs1, cursor, y_g, claim, out, iota, first: Const):
    # One layer (keccak_gkr::protocol::verify_layer): the claim on the states after
    # a round becomes one on the states before it. A claim's position weights are
    # never written out: they are the transpose of the linear layer applied to a
    # lane table times the eq table of six slice coordinates, which is all the
    # record keeps, and what `keccak_form` evaluates them from.
    fs = [fs0, fs1]
    mu = StackBuf(KECCAK_PACK)
    for i in unroll(0, KECCAK_PACK):
        mu[i] = claim[GEN ** (KC_MU + i)]
    # The product polynomial carries the claim.
    product = StackBuf(KECCAK_PROD_BITS)
    projected = 0
    for k in unroll(0, KECCAK_PROD_BITS):
        fs, coefficient, cursor = fs_next(fs, cursor)
        product[k] = coefficient
        reader = 0
        for t in unroll(KECCAK_PROJ_START[k], KECCAK_PROJ_START[k + 1]):
            reader += mu[KECCAK_PROJ_IDX[t]]
        projected += reader * coefficient
    assert projected + iota * claim[GEN ** KC_KAPPA] == claim[GEN ** KC_VALUE]
    # At a random point a pack is one field element.
    fs, s = squeeze(fs)
    s_powers = StackBuf(KECCAK_EMBED_BITS)
    s_powers[0] = 1
    for b in unroll(1, KECCAK_EMBED_BITS):
        s_powers[b] = s_powers[b - 1] * s
    kappa = 0
    for i in unroll(0, KECCAK_PACK):
        weight = 0
        for t in unroll(KECCAK_EMB_START[i], KECCAK_EMB_START[i + 1]):
            weight += s_powers[KECCAK_EMB_IDX[t]]
        out[GEN ** (KC_MU + i)] = weight
        kappa += weight
    out[GEN ** KC_KAPPA] = kappa
    value = product[KECCAK_PROD_BITS - 1]
    for k in unroll(1, KECCAK_PROD_BITS):
        value = value * s + product[KECCAK_PROD_BITS - 1 - k]
    # The pack and the segment, a runtime number of rounds.
    prev_point = claim[GEN ** KC_POINT]
    point = HeapBuf(y_g)
    rounds = HeapBuf((y_g * GEN) ** KR_SLOTS)
    rounds[GEN ** KR_FS0] = fs[0]
    rounds[GEN ** KR_FS1] = fs[1]
    rounds[GEN ** KR_CURSOR] = cursor
    rounds[GEN ** KR_CLAIM] = value
    rounds[GEN ** KR_SCALE] = 1
    for xi in mul_range(1, y_g):
        rd = rounds * xi ** KR_SLOTS
        round_fs = [rd[GEN ** KR_FS0], rd[GEN ** KR_FS1]]
        r_eq = prev_point[xi]
        cur_i = rd[GEN ** KR_CURSOR]
        round_fs, g_1, cur_i = fs_next(round_fs, cur_i)
        round_fs, g_2, cur_i = fs_next(round_fs, cur_i)
        g_0 = rd[GEN ** KR_CLAIM] + r_eq * (g_1 + g_2)
        round_fs, rho = squeeze(round_fs)
        point[xi] = rho
        eq_factor = 1 + r_eq + rho
        nxt = rd * GEN ** KR_SLOTS
        nxt[GEN ** KR_FS0] = round_fs[0]
        nxt[GEN ** KR_FS1] = round_fs[1]
        nxt[GEN ** KR_CURSOR] = cur_i
        nxt[GEN ** KR_CLAIM] = eq_factor * (g_0 + rho * (g_1 + rho * g_2))
        nxt[GEN ** KR_SCALE] = rd[GEN ** KR_SCALE] * eq_factor
    last = rounds * y_g ** KR_SLOTS
    fs = [last[GEN ** KR_FS0], last[GEN ** KR_FS1]]
    cursor = last[GEN ** KR_CURSOR]
    value = last[GEN ** KR_CLAIM]
    # The bit position: degree three, the weights being one more multilinear factor.
    local = HeapBuf(KECCAK_LOCAL_BITS)
    for i in unroll(0, KECCAK_LOCAL_BITS):
        fs, c0, cursor = fs_next(fs, cursor)
        fs, c2, cursor = fs_next(fs, cursor)
        fs, c3, cursor = fs_next(fs, cursor)
        c1 = value + c2 + c3
        fs, rho = squeeze(fs)
        local[GEN ** i] = rho
        value = c0 + rho * (c1 + rho * (c2 + rho * c3))
    fs, t0, cursor = fs_next(fs, cursor)
    fs, t1, cursor = fs_next(fs, cursor)
    fs, t2, cursor = fs_next(fs, cursor)
    # The claim's weights at the local point.
    lane_tree = HeapBuf(2 ** (KECCAK_LANE_BITS + 1) - 2)
    eqtree(local * GEN ** KECCAK_Z_BITS, lane_tree, KECCAK_LANE_BITS)
    f_lanes = lane_tree * GEN ** (2 ** KECCAK_LANE_BITS - 2)
    prev_lanes = claim[GEN ** KC_LANES]
    weight_at_local = StackBuf(1)
    if first == 1:
        # The first claim weighs a lane table times the bits of a word, x^z.
        lanes_eq = 0
        for lane in unroll(0, KECCAK_LANES):
            lanes_eq += f_lanes[GEN ** lane] * prev_lanes[GEN ** lane]
        for t in unroll(0, KECCAK_Z_BITS):
            lanes_eq *= 1 + local[GEN ** t] * (1 + GEN ** (2 ** t))
        weight_at_local[0] = lanes_eq
    else:
        prev_local = claim[GEN ** KC_LOCAL]
        bit_eq = StackBuf(KECCAK_Z_BITS)
        bit_up = StackBuf(KECCAK_Z_BITS)
        bit_down = StackBuf(KECCAK_Z_BITS)
        for t in unroll(0, KECCAK_Z_BITS):
            a_t = prev_local[GEN ** t]
            b_t = local[GEN ** t]
            both = a_t * b_t
            bit_eq[t] = 1 + a_t + b_t
            bit_up[t] = a_t + both
            bit_down[t] = b_t + both
        shifts = StackBuf(64)
        for r in unroll(0, 64):
            if KECCAK_SHIFT_USED[r] == 1:
                shifts[r] = keccak_shift_eq(bit_eq, bit_up, bit_down, r)
        weight_at_local[0] = keccak_form(prev_lanes, shifts, f_lanes)
    assert last[GEN ** KR_SCALE] * weight_at_local[0] * (kappa * t0 + (kappa + t1) * t2) == value
    # t[k] = sum_j eq[j] T[j + k]: one claim on the state before chi.
    fs, beta = squeeze(fs)
    out[GEN ** KC_VALUE] = t0 + beta * (t1 + beta * t2)
    out[GEN ** KC_POINT] = point
    out[GEN ** KC_LOCAL] = local
    lanes = HeapBuf(KECCAK_LANES)
    for y in unroll(0, 5):
        for x in unroll(0, 5):
            lanes[GEN ** (x + 5 * y)] = f_lanes[GEN ** (x + 5 * y)] + beta * (f_lanes[GEN ** ((x + 4) % 5 + 5 * y)] + beta * f_lanes[GEN ** ((x + 3) % 5 + 5 * y)])
    out[GEN ** KC_LANES] = lanes
    slice_tree = HeapBuf(2 ** (KECCAK_Z_BITS + 1) - 2)
    eqtree(local, slice_tree, KECCAK_Z_BITS)
    slices = slice_tree * GEN ** (2 ** KECCAK_Z_BITS - 2)
    out[GEN ** KC_SLICES] = slices
    # The new weights where iota can flip: slice 2^i - 1 of lane 0.
    for i in unroll(0, KECCAK_IOTA_BITS):
        flipped = lanes[GEN ** KECCAK_PI[0]] * slices[GEN ** ((2 ** i - 1 + KECCAK_RHO[0]) % 64)]
        for y in unroll(0, 5):
            flipped += lanes[GEN ** KECCAK_PI[1 + 5 * y]] * slices[GEN ** ((2 ** i - 1 + KECCAK_RHO[1 + 5 * y]) % 64)]
            flipped += lanes[GEN ** KECCAK_PI[4 + 5 * y]] * slices[GEN ** ((2 ** i + KECCAK_RHO[4 + 5 * y]) % 64)]
        out[GEN ** (KC_IOTA + i)] = flipped
    return fs[0], fs[1], cursor


def keccak_plain_rounds(fs0, fs1, cursor, value, point, n: Const):
    # n rounds of a degree-2 sumcheck with no equality factor.
    fs = [fs0, fs1]
    for i in unroll(0, n):
        fs, c0, cursor = fs_next(fs, cursor)
        fs, c2, cursor = fs_next(fs, cursor)
        c1 = value + c2
        fs, rho = squeeze(fs)
        point[GEN ** i] = rho
        value = c0 + rho * (c1 + rho * c2)
    return fs[0], fs[1], cursor, value


def keccak_read_slices(fs0, fs1, cursor, out):
    fs = [fs0, fs1]
    for z in unroll(0, BASE_FIELD_BITS):
        fs, w, cursor = fs_next(fs, cursor)
        out[GEN ** z] = w
    return fs[0], fs[1], cursor


def keccak_slot_lanes(slot, segment_point, first: Const):
    # The weight an opening's slot point puts on each lane: the states it speaks of
    # start at `first`, one per segment.
    slot_tree = HeapBuf(2 ** (QKECCAK_SLOT_LOG + 1) - 2)
    eqtree(slot, slot_tree, QKECCAK_SLOT_LOG)
    segment_tree = HeapBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
    eqtree(segment_point, segment_tree, KECCAK_SEG_LOG)
    out = HeapBuf(KECCAK_LANES)
    for lane in unroll(0, KECCAK_LANES):
        acc = 0
        for m in unroll(0, KECCAK_SEGMENTS):
            acc += segment_tree[GEN ** (2 ** KECCAK_SEG_LOG - 2 + m)] * slot_tree[GEN ** (2 ** QKECCAK_SLOT_LOG - 2 + KECCAK_LANES * (first + m) + lane)]
        out[GEN ** lane] = acc
    return out


def verify_keccak(fs0, fs1, cursor, tau_g, z_vals, slices):
    # SHA3 validity (keccak_gkr::verify): a random claim on the committed outputs,
    # KECCAK_DEPTH layers down to the committed inputs, every segment at once. It
    # leaves two openings of q_keccak, at the two points written to `z_vals` (tau +
    # QKECCAK_SLOT_LOG coordinates each, QKECCAK_VARS_CAP apart): the column itself
    # at the first, returned, and its 64 `slices` at the second.
    # tau >= KECCAK_MIN_STEPS_LOG is certified, so the pack count is a real count.
    fs = [fs0, fs1]
    pack_g = tau_g * INV_GEN ** KECCAK_PACK_LOG
    y_g = pack_g * GEN ** KECCAK_SEG_LOG
    out_point = z_vals
    in_point = z_vals * GEN ** QKECCAK_VARS_CAP
    for i in unroll(0, KECCAK_PACK_LOG):
        fs, r = squeeze(fs)
        out_point[GEN ** i] = r
    point = HeapBuf(y_g)
    points = HeapBuf((y_g * GEN) ** PAIR_SLOTS)
    points[GEN ** 0] = fs[0]
    points[GEN ** 1] = fs[1]
    for xi in mul_range(1, y_g):
        row = points * xi ** PAIR_SLOTS
        point_fs = [row[GEN ** 0], row[GEN ** 1]]
        point_fs, r = squeeze(point_fs)
        point[xi] = r
        row[GEN ** PAIR_SLOTS] = point_fs[0]
        row[GEN ** (PAIR_SLOTS + 1)] = point_fs[1]
    points_last = points * y_g ** PAIR_SLOTS
    fs = [points_last[GEN ** 0], points_last[GEN ** 1]]
    r_lane = HeapBuf(KECCAK_LANE_BITS)
    for i in unroll(0, KECCAK_LANE_BITS):
        fs, r = squeeze(fs)
        r_lane[GEN ** i] = r
    fs, value, cursor = fs_next(fs, cursor)

    # The first claim combines the output lanes as words: instance weights
    # eq(r_low), position weights eq(r_lane) on the lane times x^z on the bit.
    claims = HeapBuf((KECCAK_DEPTH + 1) * KC_SIZE)
    claims[GEN ** KC_VALUE] = value
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
    for i in unroll(0, KECCAK_IOTA_BITS):
        claims[GEN ** (KC_IOTA + i)] = first_lanes[GEN ** 0] * GEN ** (2 ** i - 1)

    for step in unroll(0, KECCAK_DEPTH):
        claim = claims * GEN ** (step * KC_SIZE)
        # iota flips known positions of lane 0, per segment a different round's.
        claim_point = claim[GEN ** KC_POINT]
        segment_tree = HeapBuf(2 ** (KECCAK_SEG_LOG + 1) - 2)
        eqtree(claim_point * pack_g, segment_tree, KECCAK_SEG_LOG)
        iota = 0
        for m in unroll(0, KECCAK_SEGMENTS):
            flipped = 0
            for t in unroll(KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m], KECCAK_IOTA_START[KECCAK_SEGMENTS * step + m + 1]):
                flipped += claim[GEN ** (KC_IOTA + KECCAK_IOTA_IDX[t])]
            iota += segment_tree[GEN ** (2 ** KECCAK_SEG_LOG - 2 + m)] * flipped
        if step == 0:
            fs0, fs1, cursor = keccak_layer(fs[0], fs[1], cursor, y_g, claim, claim * GEN ** KC_SIZE, iota, 1)
        else:
            fs0, fs1, cursor = keccak_layer(fs[0], fs[1], cursor, y_g, claim, claim * GEN ** KC_SIZE, iota, 0)
        fs = [fs0, fs1]

    # ---- the outputs, whose instance weights are an eq already ----
    # Their position weights are a word's, so the 64 slices are only needed as
    # the word they add up to: q_keccak itself at the point.
    out_slot = out_point * tau_g
    fs0, fs1, cursor, out_value = keccak_plain_rounds(fs[0], fs[1], cursor, value, out_slot, QKECCAK_SLOT_LOG)
    fs = [fs0, fs1]
    fs, word, cursor = fs_next(fs, cursor)
    out_lanes = keccak_slot_lanes(out_slot, point * pack_g, 1)
    lanes_sum = 0
    for lane in unroll(0, KECCAK_LANES):
        lanes_sum += out_lanes[GEN ** lane] * first_lanes[GEN ** lane]
    assert lanes_sum * word == out_value
    out_pack = out_point * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        out_pack[xt] = point[xt]

    # ---- the inputs: the instances of a pack first, then the slot ----
    last = claims * GEN ** (KECCAK_DEPTH * KC_SIZE)
    fs0, fs1, cursor, low_value = keccak_plain_rounds(fs[0], fs[1], cursor, last[GEN ** KC_VALUE], in_point, KECCAK_PACK_LOG)
    low_tree = HeapBuf(2 ** (KECCAK_PACK_LOG + 1) - 2)
    eqtree(in_point, low_tree, KECCAK_PACK_LOG)
    mu_at_low = 0
    for i in unroll(0, KECCAK_PACK):
        mu_at_low += low_tree[GEN ** (2 ** KECCAK_PACK_LOG - 2 + i)] * last[GEN ** (KC_MU + i)]
    in_slot = in_point * tau_g
    fs0, fs1, cursor, in_value = keccak_plain_rounds(fs0, fs1, cursor, low_value, in_slot, QKECCAK_SLOT_LOG)
    fs0, fs1, cursor = keccak_read_slices(fs0, fs1, cursor, slices)
    last_point = last[GEN ** KC_POINT]
    in_lanes = keccak_slot_lanes(in_slot, last_point * pack_g, 0)
    last_slices = last[GEN ** KC_SLICES]
    shifts = StackBuf(64)
    for r in unroll(0, 64):
        if KECCAK_SHIFT_USED[r] == 1:
            acc = 0
            for z in unroll(0, BASE_FIELD_BITS):
                acc += slices[GEN ** z] * last_slices[GEN ** ((z + r) % 64)]
            shifts[r] = acc
    last_lanes = last[GEN ** KC_LANES]
    assert mu_at_low * keccak_form(last_lanes, shifts, in_lanes) == in_value
    in_pack = in_point * GEN ** KECCAK_PACK_LOG
    for xt in mul_range(1, pack_g):
        in_pack[xt] = last_point[xt]
    return fs0, fs1, cursor, word


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
        # <= 32 (log_mem or a tau), the baked bytecode log, or q_keccak's tau_5 + QFLOCK_SLOT_LOG.
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
    # mirroring cpu::verify step for step; the `# ---- ... ----` headers below run
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
    fs = StackBuf(SHA3_STATE)
    sha3([seed_0, seed_1], [pi_0, pi_1], fs)
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
        # A table's floor: the Keccak reduction is sized for at least 2^9 steps.
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

    # ---- SHA3 validity, by GKR over the rounds ----
    tau_sha3_g = dims_g[GEN ** (TABLE_SHA3 + 1)]  # the SHA3 table's certified tau
    z_vals = HeapBuf(2 * QKECCAK_VARS_CAP)
    slices = HeapBuf(BASE_FIELD_BITS)
    fs0, fs1, cursor, keccak_word = verify_keccak(fs[0], fs[1], cursor, tau_sha3_g, z_vals, slices)
    fs = [fs0, fs1]

    # ---- stacked mixed opening: ring-switch front + claim combination ----
    # The input opening's slices were read and bound above; this block only binds
    # them to the commitment. Compose six two-term F2-linear maps with shifts
    # 32,16,8,4,2,1: their expansion has all 64 Frobenius terms soundness needs,
    # while direct application costs 63 squarings and only six general
    # multiplications.
    map_challenges = HeapBuf(6)  # len(RING_MAP_SHIFTS)
    c_table = HeapBuf(BASE_FIELD_BITS)
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
    target_in = ring_switch_target(slices, map_challenges)
    # ONE batching challenge for the whole pool: N_CLAIMS - 1 fewer Fiat-Shamir
    # hashes than a challenge per claim, and none for the values themselves,
    # `fs_next` having bound every one it read and the public-input ones deriving
    # from the seeded statement and rm, so `lam_cl` already depends on all of
    # them. Disjoint power ranges, as for the zc_xi-powers above:
    # the ring-switch claim takes lam_cl^0, the pool lam_cl^1 onward, and the
    # Keccak reduction's claim on its outputs the power after the pool's last.
    # The committed lane of a step's input holds the padding bit the VM reads
    # without, a constant apart.
    fs, lam_cl = squeeze(fs)
    target = target_in
    lam_pool = HeapBuf(N_CLAIMS)
    lam_pow = lam_cl
    for j in unroll(0, N_CLAIMS):
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
    sumcheck_target, point, point1, inner_total, yr_at_tail = match(log(config_sel), range(0, LIG_N_CANDIDATES), lambda m_idx: open_stacked(m_idx, fs[0], fs[1], target, commit_root_0, commit_root_1, cursor))
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


# ============================ XMSS signature verification ===========================
# One signature of its leaf index group's (leaf index, message), against the signer's public
# key at `pk_ptr[g^0..g^1]` = (merkle_root, public_param). Every 16-byte native
# value (tweak, digest, chain tip, sibling, pp) is one canonical 128-bit cell.
# Tweak table layout (tweak index t at cell g^t):
#     0                        : encoding tweak
#     1 + CHAIN_STEPS·i + s    : chain tweak, chain i < V, step s < CHAIN_STEPS
#     WOTS_PK_TWEAK_IDX        : wots-pk tweak
#     MERKLE_TWEAK_IDX + l     : merkle tweak, level l < LOG_LIFETIME


def fill_xmss_leaf_index_tables(leaf_index, merkle_bits, tweak_table):
    # The tweak table and the Merkle direction bits at `leaf_index`, shared by every XMSS
    # signature this node verifies at it. One bit decomposition gives all three uses:
    # a tweak's index field is the leaf index (encoding, chain, wots-pk) or the parent
    # index `leaf_index >> lvl` at Merkle level lvl - 1, and the direction bit at that
    # level IS bit lvl - 1. Booleanity is a write-once pin and the reconstruction
    # ties the bits back to the leaf index, which also bounds it to LOG_LIFETIME bits.
    # SPHINCS shares none of this, deriving every tweak from the index its own
    # digest picks, which is neither public nor shared between signers.
    hint_decompose_bits(merkle_bits, leaf_index, LOG_LIFETIME)
    bits = StackBuf(LOG_LIFETIME)
    reconstructed = 0
    index = 0
    for b in unroll(0, LOG_LIFETIME):
        bit = merkle_bits[GEN ** b]
        merkle_bits[GEN ** b] = bit * bit
        bits[b] = bit
        reconstructed += bit * COORD_BASIS[b]
        index += bit * XM_INDEX_WEIGHT[b]
    assert reconstructed == leaf_index
    tweak_table[1] = index + XM_ENC_TWEAK
    for i in unroll(0, V):
        for s in unroll(0, CHAIN_STEPS):
            tweak_table[GEN ** (1 + CHAIN_STEPS * i + s)] = index + XM_CHAIN_TWEAKS[CHAIN_STEPS * i + s]
    tweak_table[GEN ** WOTS_PK_TWEAK_IDX] = index + XM_PK_TWEAK
    # Merkle level lvl - 1 hashes the parent at `leaf_index >> lvl`: the leaf_index's bits from
    # lvl up, each weighed lvl places down. The top level gets the empty sum.
    for lvl in unroll(1, LOG_LIFETIME + 1):
        parent = 0
        for b in unroll(lvl, LOG_LIFETIME):
            parent += bits[b] * XM_INDEX_WEIGHT[b - lvl]
        tweak_table[GEN ** (MERKLE_TWEAK_IDX + lvl - 1)] = parent + XM_MERKLE_TWEAKS[lvl - 1]
    return


def verify_sig(message, tweak_table, merkle_bits, pk_ptr):
    pp = pk_ptr[GEN]

    # Encoding digest D = H(tweak | pp | msg | randomness | zero-pad), 96 bytes in
    # one block: 24 bytes of randomness and the specified 8-byte zero pad. A packing
    # helper source is read as (lo, 0, 0) where SHA3 reads (lo, hi, 0), which is
    # what pins that pad.
    rand_block = StackBuf(DIGEST_CELLS)
    hint_witness(rand_block, "rand")
    assert_in_k(rand_block[1], 0)
    digest = StackBuf(SHA3_STATE)
    sha3([tweak_table[1], pp], [message[1], message[GEN]], digest, tail=[rand_block[0], rand_block[1], 0, 0], len=96)

    # V WOTS chains. Per chain the digit is hinted in the exponent (g^{e_i}), range
    # checked and dispatched once into this frame; arm k walks the remaining
    # CHAIN_STEPS-k steps into `tips` and returns e_i = k weighted by CHAIN_LENGTH^i
    # inside its own 64-bit lane (DIGITS_PER_WORD digits a lane, GF(2^64)'s monomial
    # budget, each lane's leftover top bits ground to zero by the signer). The product
    # of the digits is the target sum (g^{Σe_i}), and the weighted digits reconstruct
    # D's first cell as `acc_lo + acc_hi·Y`.
    # The leaf's preimage: the prefix (tweak, pp), then the V tips.
    tips = StackBuf(2 + TIP_CELLS)
    tips[0] = tweak_table[GEN ** (WORDS_PER_VALUE * WOTS_PK_TWEAK_IDX)]
    tips[1] = pp
    chain_tweaks = tweak_table * GEN ** WORDS_PER_VALUE  # chain i at cell 1 + CHAIN_STEPS·i
    digit_product = 1
    acc_lo = 0
    acc_hi = 0
    for i in unroll(0, V):
        digit = hint_witness("digits")
        assert log(digit) < CHAIN_LENGTH
        chain_start = hint_witness("chain_starts")
        term = match(log(digit), range(0, CHAIN_LENGTH), lambda k: walk(chain_start, chain_tweaks, pp, tips, i, k))
        digit_product = digit_product * digit
        if i // DIGITS_PER_WORD == 0:
            acc_lo = acc_lo + term
        else:
            acc_hi = acc_hi + term
        chain_tweaks = chain_tweaks * GEN ** (WORDS_PER_VALUE * CHAIN_STEPS)
    assert digit_product == GEN ** TARGET_SUM
    assert acc_lo + acc_hi * Y_TOWER == digest[0]

    # WOTS public-key leaf = the hash of the prefix and the V tips, eight cells a
    # block.
    leaf = StackBuf(SHA3_STATE)
    sha3_cells(tips, leaf)

    # Merkle path from the leaf to the root: the leaf index bit orders the two children at
    # each level, and the tweak carries that level's parent index.
    node = leaf[0]
    for lvl in unroll(0, LOG_LIFETIME):
        sibling = hint_witness("siblings")
        children = order_children(node, sibling, merkle_bits[GEN ** (WORDS_PER_VALUE * lvl)])
        parent = StackBuf(SHA3_STATE)
        sha3([tweak_table[GEN ** (WORDS_PER_VALUE * (MERKLE_TWEAK_IDX + lvl))], pp], children, parent)
        node = parent[0]
    assert node == pk_ptr[1]
    return


@inline
def walk(value, chain_tweaks, pp, tips, i: Const, k: Const):
    # Walk chain i's steps k..CHAIN_STEPS-1, value' = H(tweak|pp, value|0), the tip
    # landing in tips[2 + i]. Step s reads its tweak at cell s off the chain's
    # subtable, a compile-time offset.
    word = value
    for s in unroll(k, CHAIN_STEPS):
        out = StackBuf(SHA3_STATE)
        sha3([chain_tweaks[GEN ** (WORDS_PER_VALUE * s)], pp], [word, 0], out, len=48)
        word = out[0]
    tips[2 + i] = word
    return const(k * CHAIN_LENGTH ** (i % DIGITS_PER_WORD))


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
        out = StackBuf(SHA3_STATE)
        sha3([tw_base + s * SP_P_MUL, pp], [word, 0], out, len=48)
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
    digest = StackBuf(SHA3_STATE)
    sha3([tw_pos + SP_TW_ENC, pp], [msg, ctr], digest, len=52)

    # The codeword, as in XMSS: each digit hinted in the exponent, range checked and
    # dispatched once, arm k walking the remaining steps; the product of the digits
    # is the target sum, and the digits weighted by 2^w within each 64-bit lane
    # reconstruct D, which pins each lane's leftover top bits to zero.
    # The leaf's preimage: the prefix (tweak, pp), then the V tips.
    tips = StackBuf(2 + SP_TIP_CELLS)
    tips[0] = tw_pos + SP_TW_LEAF
    tips[1] = pp
    digit_product = 1
    acc_lo = 0
    acc_hi = 0
    for i in unroll(0, SP_V):
        digit = hint_witness("sp_digits")
        assert log(digit) < SP_CHAIN_LENGTH
        chain_start = hint_witness("sp_chain_starts")
        tw_chain = tw_pos + SP_TW_CHAIN + i * SP_CHAIN_MUL
        tips[2 + i], e = match(log(digit), range(0, SP_CHAIN_LENGTH), lambda k: sp_walk(chain_start, tw_chain, pp, k))
        digit_product = digit_product * digit
        term = e * SP_CHAIN_LENGTH ** (i % SP_DIGITS_PER_WORD)
        if i // SP_DIGITS_PER_WORD == 0:
            acc_lo = acc_lo + term
        else:
            acc_hi = acc_hi + term
    assert digit_product == GEN ** SP_TARGET_SUM
    assert acc_lo + acc_hi * Y_TOWER == digest[0]

    leaf = StackBuf(SHA3_STATE)
    sha3_cells(tips, leaf)
    return leaf[0]


def verify_sig_sphincs(signer):
    # `signer` is one 4-cell entry of the SPHINCS coverage table: the key's root and
    # public parameter, then the message THAT signer signed. Where XMSS's message is
    # one statement field for the whole node, a SPHINCS message rides its own slot,
    # and the signer-set digest binds the two together.
    pp = signer[GEN]

    # ---- the message digest, which chooses the few-time key ----
    # D = Truncate(H(tw_msg | P | rho | root | m)), 96 bytes in one block.
    rho_root = StackBuf(DIGEST_CELLS)
    hint_witness(rho_root[0:1], "sp_rand")
    rho_root[1] = signer[1]
    digest = StackBuf(SHA3_STATE)
    sha3([SP_TW_MSG, pp], rho_root, digest, tail=[signer[GEN ** 2], signer[GEN ** 3], 0, 0], len=96)

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
    # The few-time key's preimage: the prefix (tweak, pp), then the roots.
    roots = StackBuf(2 + SP_N_FTS)
    roots[0] = SP_TW_FTS_ROOTS + idx_tau
    roots[1] = pp
    for kappa in unroll(0, SP_N_FTS):
        leaf_off = SP_H + kappa * SP_A
        secret = StackBuf(DIGEST_CELLS)
        hint_witness(secret[0:1], "sp_fts_secrets")
        fts_leaf = StackBuf(SHA3_STATE)
        node_index = sp_bit_field(bits, leaf_off, SP_A, SP_J_POS)
        sha3([SP_TW_FTS_LEAF + kappa * SP_LAY_MUL + idx_tau + node_index, pp], [secret[0], 0], fts_leaf, len=48)
        node = fts_leaf[0]
        for level in unroll(0, SP_A):
            sibling = hint_witness("sp_fts_paths")
            children = order_children(node, sibling, bits[GEN ** (leaf_off + level)])
            parent = StackBuf(SHA3_STATE)
            if const(level + 1 == SP_A):
                node_index = 0
            else:
                # The index fits in one lane; clearing its low bit makes division by GEN a right shift.
                node_index = (node_index + bits[GEN ** (leaf_off + level)] * COORD_BASIS[SP_J_POS]) / GEN
            sha3([SP_TW_FTS_NODE + kappa * SP_LAY_MUL + const((level + 1) * SP_P_MUL) + idx_tau + node_index, pp], children, parent)
            node = parent[0]
        roots[2 + kappa] = node
    fts_key = StackBuf(SHA3_STATE)
    sha3_cells(roots, fts_key)
    signed = fts_key[0]

    # ---- the hypertree, bottom layer first ----
    # Layer lay signs what the layer below produced: the few-time key at the bottom,
    # that layer's root above it, and the public key's root at the top.
    for step in unroll(0, SP_D):
        lay = SP_D - 1 - step
        leaf_index_off = SP_SUFFIX[lay + 1]
        tau_field = sp_bit_field(bits, SP_SUFFIX[lay], SP_H - SP_SUFFIX[lay], SP_TAU_POS)
        node_index = sp_bit_field(bits, leaf_index_off, SP_HEIGHTS[lay], SP_J_POS)
        tw_pos = tau_field + node_index + lay * SP_LAY_MUL
        node = sp_ots_leaf(tw_pos, pp, signed)
        for level in unroll(0, SP_HEIGHTS[lay]):
            sibling = hint_witness("sp_siblings")
            children = order_children(node, sibling, bits[GEN ** (leaf_index_off + level)])
            parent = StackBuf(SHA3_STATE)
            if const(level + 1 == SP_HEIGHTS[lay]):
                node_index = 0
            else:
                node_index = (node_index + bits[GEN ** (leaf_index_off + level)] * COORD_BASIS[SP_J_POS]) / GEN
            sha3([SP_TW_NODE + lay * SP_LAY_MUL + const((level + 1) * SP_P_MUL) + tau_field + node_index, pp], children, parent)
            node = parent[0]
        signed = node
    assert signed == signer[1]
    return


# =========================== statements and the signer set ==========================


def statement_digest(seed_0, seed_1, signers_hash, da_0, da_1, defer):
    # A node's statement, hashed to the two words the VM publishes, over the
    # proving environment's Fiat-Shamir seed (the Keccak relation and this bytecode), the
    # two-cell signer-set digest, the digest of its possibly empty DA root list,
    # and the DEFER_STMT_CELLS deferred-claim cells. A
    # parent rebuilds a child's statement with this same call, over a signer-set
    # digest it re-absorbed itself, which forces the child to be a proof of THIS
    # bytecode over groups checked against the parent's own.
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


# The declared lists are hashed as flat runs of cells, eight a block, the sponge
# state carried between loop frames through a heap chain of STATE_SLOTS cells a step
# (see STATE_SLOTS). A chain starts from the zero state, which a later block's XOR
# turns into a first block's message. A list's length is runtime, but every block
# before the last is full, so only the last block's shape depends on it, and that is
# a small `match`.


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


def key_list_digest(keys_ptr, n_keys_g):
    # The hash of one leaf index group's declared key list, 32 bytes a key and so four
    # keys a block. The keys are hinted into the group's declared slots of the table,
    # a block at a time.
    body, rest = list_split(n_keys_g, 4)
    chain = HeapBuf((body * GEN) ** STATE_SLOTS)
    zero_state(chain)
    for xq in mul_range(1, body):
        st = chain * xq ** STATE_SLOTS
        nxt = st * GEN ** STATE_SLOTS
        blk = keys_ptr * xq ** 8
        hint_witness(blk[0:8], "pubkeys")
        sha3(blk[0:2], blk[2:4], nxt[0:SHA3_STATE], tail=blk[4:8], state=st[0:SHA3_STATE], final=0)
    last = chain * body ** STATE_SLOTS
    d0, d1 = match(log(rest), range(0, 4), lambda k: key_list_last(last, keys_ptr * body ** 8, k))
    return d0, d1


def key_list_last(state, blk, k: Const):
    # The last block of a key list: k + 1 keys, then the padding.
    hint_witness(blk[0:2 * k + 2], "pubkeys")
    digest = StackBuf(SHA3_STATE)
    if k == 0:
        sha3(blk[0:2], [0, 0], digest, state=state[0:SHA3_STATE], len=32)
    if k == 1:
        sha3(blk[0:2], blk[2:4], digest, state=state[0:SHA3_STATE], len=64)
    if k == 2:
        sha3(blk[0:2], blk[2:4], digest, tail=[blk[GEN ** 4], blk[GEN ** 5], 0, 0], state=state[0:SHA3_STATE], len=96)
    if k == 3:
        sha3(blk[0:2], blk[2:4], digest, tail=blk[4:8], state=state[0:SHA3_STATE])
    return digest[0], digest[1]


@inline
def child_keys(keys_ptr, cover, marks, origin_g, limit_g, blk, n: Const):
    # n of a child's keys, read at hinted indices into THIS node's table and marked
    # in the coverage table, copied into the block `blk`. Each index is an offset
    # into the parent group the caller mapped this child group to, bounded by that
    # group's size, so a child's key can only ever land on an XMSS slot of the right
    # leaf index.
    idx = StackBuf(4)
    hint_witness(idx[0:n], "child_index")
    for j in unroll(0, n):
        assert log(idx[j]) < log(limit_g)  # precondition as in the raw loops
        cover[origin_g * idx[j]] = marks * (GEN ** j)
        key = keys_ptr * (idx[j] * idx[j])
        blk[2 * j] = key[1]
        blk[2 * j + 1] = key[GEN]
    return


def child_key_list_digest(keys_ptr, cover, base, origin_g, limit_g, n_keys_g):
    # The hash of one leaf index group of a child's keys, over the same 32·n bytes the
    # child hashed (`key_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. The chain threads the coverage write value, which
    # counts the keys off as they are marked, from `base`.
    body, rest = list_split(n_keys_g, 4)
    chain = HeapBuf((body * GEN) ** STATE_SLOTS)
    zero_state(chain)
    chain[GEN ** SHA3_STATE] = base
    for xq in mul_range(1, body):
        st = chain * xq ** STATE_SLOTS
        nxt = st * GEN ** STATE_SLOTS
        marks = st[GEN ** SHA3_STATE]
        blk = StackBuf(8)
        child_keys(keys_ptr, cover, marks, origin_g, limit_g, blk, 4)
        sha3(blk[0:2], blk[2:4], nxt[0:SHA3_STATE], tail=blk[4:8], state=st[0:SHA3_STATE], final=0)
        nxt[GEN ** SHA3_STATE] = marks * GEN ** 4
    last = chain * body ** STATE_SLOTS
    d0, d1 = match(log(rest), range(0, 4), lambda k: child_key_list_last(last, keys_ptr, cover, origin_g, limit_g, k))
    return d0, d1


def child_key_list_last(state, keys_ptr, cover, origin_g, limit_g, k: Const):
    blk = StackBuf(8)
    child_keys(keys_ptr, cover, state[GEN ** SHA3_STATE], origin_g, limit_g, blk, k + 1)
    digest = StackBuf(SHA3_STATE)
    if k == 0:
        sha3(blk[0:2], [0, 0], digest, state=state[0:SHA3_STATE], len=32)
    if k == 1:
        sha3(blk[0:2], blk[2:4], digest, state=state[0:SHA3_STATE], len=64)
    if k == 2:
        sha3(blk[0:2], blk[2:4], digest, tail=[blk[4], blk[5], 0, 0], state=state[0:SHA3_STATE], len=96)
    if k == 3:
        sha3(blk[0:2], blk[2:4], digest, tail=blk[4:8], state=state[0:SHA3_STATE])
    return digest[0], digest[1]


def sphincs_list_digest(entries_ptr, n_g):
    # The hash of the declared SPHINCS claims: 64 bytes a claim, the claimed key
    # then the message it signed, so two claims a block. An empty list hashes the
    # empty string.
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
            hint_witness(blk[0:4], "sphincs_signers")
            hint_witness(blk[4:8], "sphincs_signers")
            sha3(blk[0:2], blk[2:4], nxt[0:SHA3_STATE], tail=blk[4:8], state=st[0:SHA3_STATE], final=0)
        last = chain * body ** STATE_SLOTS
        d0, d1 = match(log(rest), range(0, 2), lambda k: sphincs_list_last(last, entries_ptr * body ** 8, k))
        digest[0] = d0
        digest[1] = d1
    return digest[0], digest[1]


def sphincs_list_last(state, blk, k: Const):
    hint_witness(blk[0:4], "sphincs_signers")
    digest = StackBuf(SHA3_STATE)
    if k == 0:
        sha3(blk[0:2], blk[2:4], digest, state=state[0:SHA3_STATE], len=64)
    else:
        hint_witness(blk[4:8], "sphincs_signers")
        sha3(blk[0:2], blk[2:4], digest, tail=blk[4:8], state=state[0:SHA3_STATE])
    return digest[0], digest[1]


@inline
def child_sphincs_entries(entries_ptr, cover, marks, origin_g, limit_g, blk, n: Const):
    # n of a child's SPHINCS claims, each read at a hinted index into THIS node's
    # table and marked in the coverage table. The index is an offset into the
    # SPHINCS region and bounded by that region's size, so a child's claim can only
    # ever land on a SPHINCS slot.
    for j in unroll(0, n):
        off_hint = hint_witness("child_sphincs_index")
        assert log(off_hint) < log(limit_g)  # precondition as in the raw loops
        cover[origin_g * off_hint] = marks * (GEN ** j)
        entry = entries_ptr * (off_hint ** 4)
        for c in unroll(0, 4):
            blk[4 * j + c] = entry[GEN ** c]
    return


def child_sphincs_list_digest(entries_ptr, cover, base, origin_g, limit_g, n_g):
    # The hash of a child's declared SPHINCS claims, over the same 64n bytes the
    # child hashed (`sphincs_list_digest`), so the digest it rebuilds is the one the
    # child's statement carries. The chain threads the coverage write value from
    # `base`, as `child_key_list_digest` does.
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
            child_sphincs_entries(entries_ptr, cover, marks, origin_g, limit_g, blk, 2)
            sha3(blk[0:2], blk[2:4], nxt[0:SHA3_STATE], tail=blk[4:8], state=st[0:SHA3_STATE], final=0)
            nxt[GEN ** SHA3_STATE] = marks * GEN ** 2
        last = chain * body ** STATE_SLOTS
        d0, d1 = match(log(rest), range(0, 2), lambda k: child_sphincs_list_last(last, entries_ptr, cover, origin_g, limit_g, k))
        digest[0] = d0
        digest[1] = d1
    return digest[0], digest[1]


def child_sphincs_list_last(state, entries_ptr, cover, origin_g, limit_g, k: Const):
    blk = StackBuf(8)
    child_sphincs_entries(entries_ptr, cover, state[GEN ** SHA3_STATE], origin_g, limit_g, blk, k + 1)
    digest = StackBuf(SHA3_STATE)
    if k == 0:
        sha3(blk[0:2], blk[2:4], digest, state=state[0:SHA3_STATE], len=64)
    else:
        sha3(blk[0:2], blk[2:4], digest, tail=blk[4:8], state=state[0:SHA3_STATE])
    return digest[0], digest[1]


def signer_set_digest(run_ptr, n_leaf_indices_g):
    # The hash of the signer set: both list lengths and the SPHINCS list's digest,
    # then eight cells a group, its (leaf index, count, message) and its key list's
    # digest. That is 4 + 8·n_leaf_indices cells, so every block before the last is full
    # and the last holds four cells whatever the count: n_leaf_indices blocks in the loop,
    # then that one. Leading with both lengths makes the encoding prefix-free: no
    # set's string is a prefix of another's.
    chain = HeapBuf((n_leaf_indices_g * GEN) ** STATE_SLOTS)
    zero_state(chain)
    for xq in mul_range(1, n_leaf_indices_g):
        st = chain * xq ** STATE_SLOTS
        nxt = st * GEN ** STATE_SLOTS
        blk = run_ptr * xq ** 8
        sha3(blk[0:2], blk[2:4], nxt[0:SHA3_STATE], tail=blk[4:8], state=st[0:SHA3_STATE], final=0)
    last = chain * n_leaf_indices_g ** STATE_SLOTS
    blk = run_ptr * n_leaf_indices_g ** 8
    digest = StackBuf(SHA3_STATE)
    sha3(blk[0:2], blk[2:4], digest, state=last[0:SHA3_STATE], len=64)
    return digest[0], digest[1]


def rebuild_child_groups(nsub_e_g, run_ptr, base, leaf_indices, msgs, group_base, group_slots, n_leaf_indices_g, xmss_table, cover):
    # The child's leaf index groups, written into the run its own signer-set hash covers,
    # two blocks a group exactly as the child laid them out: its (leaf index, count,
    # message), then the digest of its keys, read from THIS node's table through
    # hinted indices. A hinted map ties each group to the parent group holding the
    # same leaf index AND message, whose region its keys land in. Everything hinted here
    # is pinned by the digest, which the child's statement carries. The running
    # product of the group counts prefixes each group's coverage writes and ends as
    # the child's XMSS claim count.
    counts = HeapBuf(nsub_e_g * GEN)
    counts[GEN ** 0] = 1
    for xj in mul_range(1, nsub_e_g):
        grp = StackBuf(4)
        hint_witness(grp, "child_group")  # leaf index, msg_lo, msg_hi, count
        n_keys = grp[3]
        assert log(n_keys) < MAX_KEYS
        parent = hint_witness("child_group_map")
        assert log(parent) < log(n_leaf_indices_g)
        assert leaf_indices[parent] == grp[0]
        parent_msg = msgs * (parent * parent)
        assert parent_msg[1] == grp[1]
        assert parent_msg[GEN] == grp[2]
        gb = group_base[parent]
        prefix = counts[xj]
        kd_0, kd_1 = child_key_list_digest(xmss_table * (gb * gb), cover, base * prefix, gb, group_slots[parent], n_keys)
        slot = run_ptr * (xj ** 8) * (GEN ** 4)
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
    # One node of an aggregation tree: raw XMSS signatures grouped by the (leaf index,
    # message) they claim (a RUNTIME number of groups), n_raw_sphincs SPHINCS signatures
    # and n_children sub-proofs OF THIS SAME BYTECODE. Each XMSS group carries its
    # own (leaf index, message) pair, and each SPHINCS signature is against the message
    # in its own coverage slot. DA roots occupy a separate region of the same table.
    #
    # The declared lists are the signer set; the duplicate slots absorb keys a child
    # covers that the set does not declare. The coverage table is one region per
    # leaf index group, each its declared keys then its own duplicates, then SPHINCS
    # and DA regions shaped the same way:
    #
    #   [group 0: declared | dup]...[group n_leaf_indices-1: declared | dup][SPHINCS: declared | dup][DA: declared | dup]
    #
    # The first n_decl groups are the signer set's; the n_drop after them declare
    # nothing, holding a child group's (leaf index, message) without publishing it.
    #
    # so one range check per write keeps each writer inside its own region: that is
    # what makes the statement's split mean which scheme verified which key against
    # which (leaf index, message). An XMSS slot is two cells, a SPHINCS slot four: a key
    # and the message that key signed. A DA root occupies two cells.
    meta = StackBuf(7)
    hint_witness(meta, "meta")  # every count in the exponent
    n_decl_g = meta[0]
    n_drop_g = meta[1]
    n_sphincs_g = meta[2]
    n_sdup_g = meta[3]
    n_raw_s_g = meta[4]
    n_children_g = meta[5]
    n_direct_da_g = meta[6]
    # Declared plus dropped, so bounding each side pins n_decl <= n_leaf_indices.
    assert log(n_decl_g) < MAX_LEAF_INDICES + 1
    assert log(n_drop_g) < MAX_LEAF_INDICES + 1
    n_leaf_indices_g = n_decl_g * n_drop_g
    assert log(n_leaf_indices_g) < MAX_LEAF_INDICES + 1
    assert log(n_sphincs_g) < MAX_KEYS
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

    # ---- the leaf index groups: geometry pass ----
    # Per group: its leaf index, its two message cells, and its declared, duplicate and
    # raw-signature counts, each count bounded before it enters a product (up to
    # 2^16 factors of exponent < 2^17 stay far from the order 2^64 - 1, so nothing
    # wraps). Region bases and the three totals ride a stride-4 chain; the per-group
    # values land in heap buffers the later passes and the children's hinted group
    # maps read back at runtime.
    leaf_indices = HeapBuf(n_leaf_indices_g)
    msgs = HeapBuf(n_leaf_indices_g * n_leaf_indices_g)
    group_n_keys = HeapBuf(n_leaf_indices_g)
    group_n_dups = HeapBuf(n_leaf_indices_g)
    group_n_raw = HeapBuf(n_leaf_indices_g)
    group_base = HeapBuf(n_leaf_indices_g)
    group_slots = HeapBuf(n_leaf_indices_g)
    geo = HeapBuf((n_leaf_indices_g * GEN) ** 4)  # [base, n_xmss product, n_raw product]
    geo[1] = 1
    geo[GEN] = 1
    geo[GEN ** 2] = 1
    for xe in mul_range(1, n_leaf_indices_g):
        grp = StackBuf(6)
        hint_witness(grp, "group")  # leaf index, msg_lo, msg_hi, n, n_dup, n_raw
        assert log(grp[3]) < MAX_KEYS
        assert log(grp[4]) < MAX_KEYS
        assert log(grp[5]) < MAX_KEYS
        leaf_indices[xe] = grp[0]
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
    geo_end = geo * (n_leaf_indices_g ** 4)
    xmss_slots_g = geo_end[1]
    n_raw_x_g = geo_end[GEN ** 2]
    sphincs_slots_g = n_sphincs_g * n_sdup_g
    # The sum of every region bounds the coverage indices, so it is what has to sit
    # below the minimum memory size.
    da_base_g = xmss_slots_g * sphincs_slots_g
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
    # One table per scheme, the XMSS one a leaf index group at a time: each group its
    # declared list (strictly sorted, checked by the outer verifier, which holds it)
    # followed by its own duplicate slots. The coverage indices below run over one
    # space: the group regions in order, then SPHINCS, then DA.
    #
    # The digest is a plain hash of one string: both lengths and the SPHINCS list's
    # digest, then per group its (leaf index, count, message) and its key list's digest,
    # each list hashed plainly in turn. Leading with both lengths makes the encoding
    # prefix-free, so no set's string is a prefix of another's and the digest binds
    # its own lengths.
    xmss_table = HeapBuf(xmss_slots_g * xmss_slots_g)
    sphincs_table = HeapBuf(sphincs_slots_g ** 4)
    # The run the set's hash covers: both lengths and the SPHINCS list's digest,
    # then eight cells a group, its header and its key digest.
    signers_run = HeapBuf(n_decl_g ** 8 * GEN ** 4)
    signers_run[1] = n_decl_g
    signers_run[GEN] = n_sphincs_g
    decl_keys = HeapBuf(n_decl_g * GEN)
    decl_keys[GEN ** 0] = 1
    for xe in mul_range(1, n_decl_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        decl_keys[xe * GEN] = decl_keys[xe] * n_keys
        kd_0, kd_1 = key_list_digest(xmss_table * (base * base), n_keys)
        group_msg = msgs * (xe * xe)
        slot = signers_run * (xe ** 8) * (GEN ** 4)
        slot[1] = leaf_indices[xe]
        slot[GEN] = n_keys
        slot[GEN ** 2] = group_msg[1]
        slot[GEN ** 3] = group_msg[GEN]
        slot[GEN ** 4] = kd_0
        slot[GEN ** 5] = kd_1
        slot[GEN ** 6] = 0
        slot[GEN ** 7] = 0
    # The duplicate slots ride the same table but outside the hashed prefix, past
    # each group's declared keys. Over the whole table: a dropped group has only these.
    for xe in mul_range(1, n_leaf_indices_g):
        n_keys = group_n_keys[xe]
        base = group_base[xe]
        dup_ptr = xmss_table * (base * base * n_keys * n_keys)
        for xd in mul_range(1, group_n_dups[xe]):
            dup = dup_ptr * (xd * xd)
            hint_witness(dup[0:2], "dup_pubkeys")
    sp_0, sp_1 = sphincs_list_digest(sphincs_table, n_sphincs_g)
    signers_run[GEN ** 2] = sp_0
    signers_run[GEN ** 3] = sp_1
    # At least one published signature claim or DA root also ensures a nonempty coverage table.
    assert decl_keys[n_decl_g] * n_sphincs_g * n_da_g != 1
    set_0, set_1 = signer_set_digest(signers_run, n_decl_g)
    signers_hash = HeapBuf(DIGEST_CELLS)
    signers_hash[1] = set_0
    signers_hash[GEN] = set_1
    for xd in mul_range(1, n_sdup_g):
        dup = sphincs_table * ((n_sphincs_g * xd) ** 4)
        hint_witness(dup[0:4], "dup_sphincs")

    # ---- coverage ----
    # Every one of the n_total slots is written exactly once: write-once memory
    # rejects a second write (the value written is the running count, so two writes
    # to one slot disagree), and the count below rejects a missed one. So every
    # declared claim is covered by a direct check of its own kind or by a verified
    # child. Each writer is confined to its own region, including DA roots.
    # The raw XMSS walk runs one loop per leaf index group, each signature verified
    # against that group's tables (built here, only for a group that holds raw
    # signatures); a stride-1 chain threads the running count across the groups.
    cover = HeapBuf(n_total_g)
    da_cover = cover * da_base_g
    merkle_bits = HeapBuf(n_leaf_indices_g ** MERKLE_BIT_CELLS)
    tweak_tables = HeapBuf(n_leaf_indices_g ** N_TWEAK_CELLS)
    raw_count = HeapBuf(n_leaf_indices_g * GEN)
    raw_count[GEN ** 0] = 1
    for xe in mul_range(1, n_leaf_indices_g):
        n_raw = group_n_raw[xe]
        prefix = raw_count[xe]
        if n_raw != 1:
            tweak_table = tweak_tables * (xe ** N_TWEAK_CELLS)
            group_bits = merkle_bits * (xe ** MERKLE_BIT_CELLS)
            fill_xmss_leaf_index_tables(leaf_indices[xe], group_bits, tweak_table)
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
                # this GROUP's region, so a signature verified at this (leaf index,
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
        # The child's two list lengths, then its groups, rebuilt into its signer-set
        # chain by rebuild_child_groups: everything hinted there is pinned by the
        # chain, which the child's statement digest carries, so a lie about any of
        # it changes the public input its proof has to satisfy. Nothing demands a
        # mid-tree statement be canonical (sorted, distinct groups); it still binds
        # every claim to its (leaf index, message), which is all the group map relies on.
        child_meta = StackBuf(2)
        hint_witness(child_meta, "child_meta")  # n_leaf_indices, n_sphincs
        nsub_e_g = child_meta[0]
        nsub_s_g = child_meta[1]
        assert log(nsub_e_g) < MAX_LEAF_INDICES + 1
        assert log(nsub_s_g) < MAX_KEYS
        sub_run = HeapBuf(nsub_e_g ** 8 * GEN ** 4)
        sub_run[1] = nsub_e_g
        sub_run[GEN] = nsub_s_g
        nsub_x_g = rebuild_child_groups(nsub_e_g, sub_run, base, leaf_indices, msgs, group_base, group_slots, n_leaf_indices_g, xmss_table, cover)
        # Implied by the per-group bounds and the child's own n_total assert; stands
        # as documentation.
        assert log(nsub_x_g) < MAX_KEYS
        nsub_g = nsub_x_g * nsub_s_g
        csp_0, csp_1 = child_sphincs_list_digest(sphincs_table, cover, base * nsub_x_g, xmss_slots_g, sphincs_slots_g, nsub_s_g)
        sub_run[GEN ** 2] = csp_0
        sub_run[GEN ** 3] = csp_1
        sub_set_0, sub_set_1 = signer_set_digest(sub_run, nsub_e_g)
        sub_hash = HeapBuf(DIGEST_CELLS)
        sub_hash[1] = sub_set_0
        sub_hash[GEN] = sub_set_1
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

    # ---- the batching sumcheck (BYTECODE_VARS variables, 2 claims per child) ----
    # Fresh and carried share one layout (point, then value), so the two differ
    # only in which buffer they come from.
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
