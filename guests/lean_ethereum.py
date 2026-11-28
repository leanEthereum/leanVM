# The recursive aggregation guest: zkDSL, not runnable Python (see
# crates/zkdsl_compiler/zkDSL.md). One node of an aggregation tree verifies raw leanXMSS
# and leanSPHINCS signatures and sub-proofs OF THIS SAME BYTECODE, and publishes the
# statement digest binding its signature claims and at most one LeanDA root: that of a
# blob matrix it checks directly, or one of its children's, passed on.
# Reading order: `main` is the
# node, `verify_sub` the in-circuit copy of `verifier::verify_execution`, and
# `open_stacked` the WHIR opening it dispatches into.
#
# Every `*_PLACEHOLDER` below is filled by the host at compile time
# (the `aggregation` crate's `placeholder_map`), so one source serves every inner
# shape. Names follow doc/leanvm/preamble/macros.tex.
from snark_lib import *

# ---------------------------------------------------------------- proof stream
# The proof stream rides witness hints of STREAM_CHUNK words, as many as it fills, at
# most STREAM_CAP words; binding always comes from the per-word absorbs.
STREAM_CAP = STREAM_CAP_PLACEHOLDER
STREAM_CHUNK = STREAM_CHUNK_PLACEHOLDER
MIN_LOG_MEM = MIN_LOG_MEM_PLACEHOLDER
MAX_LOG_MEM = MAX_LOG_MEM_PLACEHOLDER
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
QW = QW_PLACEHOLDER
QUERY_WINDOWS_CAP = QUERY_WINDOWS_CAP_PLACEHOLDER
BASE_FIELD_BITS = 64
Y_TOWER = Y_TOWER_PLACEHOLDER
Y_INV = Y_INV_PLACEHOLDER
COORD_BASIS = COORD_BASIS_PLACEHOLDER
# Phi, the F2-linear map that batches the 64 ring-switch slice claims, is
# drawn as two rows of RING_MAP_WIDTH challenges, f_p then g_b. RING_W[p] = x^(-2^(64 - 8p)),
# the inverse of the target's Horner point z_p.
RING_MAP_WIDTH = 8
RING_W = RING_W_PLACEHOLDER
RS_CHUNK = 8  # ring-switch rows (target) or coordinates (weight) per loop iteration
RS_CHUNK_BITS = 3
RES_BATCH = 8  # residual queries per loop iteration
SPLIT_COUNT_BITS = 6  # split_count takes a count below 2^SPLIT_COUNT_BITS
# Exponent bit-widths, wider than the 2^30 caps need: a count's log is below
# COUNT_BITS; a structural size (sums of 2^kappa, packing offsets) fits SIZE_BITS
# bits; and a structural LOG announced as an integer word (log_mem, log_inv_rate),
# raised to a g-power by g_power_of_word, is below SIZE_BITS, so LOG_WORD_BITS bits
# make the reconstruction the bound (a larger log cannot reproduce itself from them).
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

INDEX_MLE_FACTORS = INDEX_MLE_FACTORS_PLACEHOLDER  # 1 + g^(2^i)
# An instruction's 16 slots, indexed by LOG2_BYTECODE_COLS bits: the link weighs slot s by eq(alpha, s).
LOG2_BYTECODE_COLS = LOG2_BYTECODE_COLS_PLACEHOLDER

# --------------------------------------------------------------- the six tables
# FLOORS[t] is the table's least log height (the Keccak reduction is sized for at least
# one block of 2^9 steps).
TABLE_KECCAK = 5
N_TABLES = N_TABLES_PLACEHOLDER
FLOORS = FLOORS_PLACEHOLDER

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
# A layer's sumcheck over packs and segments runs tau - 3 < 32 rounds, KR_STEP and a remainder.
KR_STEP_LOG = 4
KR_STEP = 2 ** KR_STEP_LOG

# ------------------------------------------------- the stacked WHIR opening
# The opening is dispatched by the certified committed log-size m through `match`,
# one arm per m, and by the announced rate inside it. The LIG_* tables carry one row
# per (rate, m), emitted from the same level_shapes the prover uses: scalars index as
# TBL[m_idx], per-level values as TBL[m_idx * LIG_MAX_LEVELS + lvl], where m_idx is
# the rate-major candidate index rate * LIG_N_LOG_SIZES + m - LIG_MIN_LOG_SIZE.
LIG_MIN_LOG_SIZE = LIG_MIN_LOG_SIZE_PLACEHOLDER
LIG_N_LOG_SIZES = LIG_N_LOG_SIZES_PLACEHOLDER
LIG_N_RATES = LIG_N_RATES_PLACEHOLDER
# A column's possible logs, 0 through MAX_STACKED_LOG: the arms of its selector's match.
N_COLUMN_LOGS = N_COLUMN_LOGS_PLACEHOLDER
# The stack's blocks (verifier::layout::stack_blocks): each one's kappa source and adjustment. A block group is a
# run of blocks sharing both.
N_STK_BLOCKS = N_STK_BLOCKS_PLACEHOLDER
STK_SRC = STK_SRC_PLACEHOLDER
STK_ADJ = STK_ADJ_PLACEHOLDER
N_STK_GROUPS = N_STK_GROUPS_PLACEHOLDER
STK_GROUP_START = STK_GROUP_START_PLACEHOLDER  # a block group's first block, then N_STK_BLOCKS
STK_STRIDE = STK_STRIDE_PLACEHOLDER  # above the block count: a rank key's size step
STK_KEY_BOUND = SIZE_BITS * STK_STRIDE  # above any step between two rank keys
STK_MIN_LOG = STK_MIN_LOG_PLACEHOLDER
# Global maxima; StackBuf frame sizes are parse-time, so they must be baked.
LIG_MAX_LEVELS = LIG_MAX_LEVELS_PLACEHOLDER
# A rate's tables follow the previous rate's, every size and level of it.
LIG_RATE_STRIDE = LIG_N_LOG_SIZES * LIG_MAX_LEVELS
LIG_LOG_MSG_COLS_CAP = LIG_LOG_MSG_COLS_CAP_PLACEHOLDER
YR_LOG_CAP = YR_LOG_CAP_PLACEHOLDER
# The opening's grinding (pcs::whir_config): before each fold round's (alpha, beta),
# before every commitment's OOD point, before every level's queries (a non-final level's
# lambda rides that message), and before level 0's batching, the ring switch's map.
FOLD_GRIND_BITS = FOLD_GRIND_BITS_PLACEHOLDER
OOD_GRIND_BITS = OOD_GRIND_BITS_PLACEHOLDER
QUERY_GRIND_BITS = QUERY_GRIND_BITS_PLACEHOLDER
BATCH_GRIND_BITS = BATCH_GRIND_BITS_PLACEHOLDER
# Every other challenge grinds for its numerator (fiat_shamir::grinding_bits), zero
# bits being no nonce at all: a sumcheck round for its degree d, eq factor included, as
# ROUNDd (the opening's tail and a Keccak opening's are degree 2, a Keccak layer's
# degree 3); the batching challenge; and the Keccak reduction's first message (its
# segment and lane), its s and its beta.
ROUND2_GRIND_BITS = ROUND2_GRIND_BITS_PLACEHOLDER
ROUND3_GRIND_BITS = ROUND3_GRIND_BITS_PLACEHOLDER
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
SEL_EQ_STRIDE = 32                      # a nibble's eq tables over its top 1..4 coords, strided
# Where a nibble's level-w table starts: levels 0..2 interleaved in one 16-cell row, each
# shifted into the others' gaps (their entries are multiples of 8, 4 and 2), level 3 a row.
SEL_EQ_OFF = [4, 2, 1, 16]
EQ_CHAIN_ARMS = SIZE_BITS + QKECCAK_SLOT_LOG + 1  # eq prefix chain lengths
SEL_TAB_NIBBLES = (SIZE_BITS + 3) // 4  # nibbles of a small exponent (assert_small_g_power)
WIN_TAB_AT = SIZE_BITS + 16 * SEL_TAB_NIBBLES  # a bit window's pattern by its g-power: [g^n] = n
WIN_TAB_BITS = 11
WIN_TAB_LEN = 2 ** WIN_TAB_BITS

# The Hotwire link (verifier::link, verifier::layout::tables): the tables' non-pointer columns arrive
# in one sent run, in table then column order; a form is TERM_COEF * a * b over that run, a missing factor
# LINK_NO_POS. A sent column's claim lands on its stack block, on a q_keccak slot (N_STK_BLOCKS + slot)
# or nowhere (LINK_NO_POS). A pointer w bits wide splits into CHUNK_D[w] chunks, row w of the CHUNK_*
# tables, CHUNK_CAP entries each.
LINK_N_SENT = LINK_N_SENT_PLACEHOLDER
LINK_NO_POS = LINK_NO_POS_PLACEHOLDER
SENT_TARGET = SENT_TARGET_PLACEHOLDER
SENT_OUT_LANES = SENT_OUT_LANES_PLACEHOLDER
FORM_START = FORM_START_PLACEHOLDER
TERM_COEF = TERM_COEF_PLACEHOLDER
TERM_A = TERM_A_PLACEHOLDER
TERM_B = TERM_B_PLACEHOLDER
STATE_PC = STATE_PC_PLACEHOLDER
STATE_FP = STATE_FP_PLACEHOLDER
STATE_NEXT0 = STATE_NEXT0_PLACEHOLDER
STATE_NEXT1 = STATE_NEXT1_PLACEHOLDER
BC_OP_START = BC_OP_START_PLACEHOLDER
BC_OP_FORM = BC_OP_FORM_PLACEHOLDER
BC_OP_SLOT = BC_OP_SLOT_PLACEHOLDER  # an operand equation's first slot, whose challenge weighs it
ACC_START = ACC_START_PLACEHOLDER
ACC_ADDR = ACC_ADDR_PLACEHOLDER
ACC_VALUE = ACC_VALUE_PLACEHOLDER
ACC_GATE = ACC_GATE_PLACEHOLDER
ACC_SHIFT = ACC_SHIFT_PLACEHOLDER
N_ACCESSES = N_ACCESSES_PLACEHOLDER
ACC_PTR = ACC_PTR_PLACEHOLDER
# The word reads: the word at pointer WR_PTR, under access WR_ACC's mu, scaled by form WR_SCALE.
N_WORD_READS = N_WORD_READS_PLACEHOLDER
WR_PTR = WR_PTR_PLACEHOLDER
WR_ACC = WR_ACC_PLACEHOLDER
WR_SCALE = WR_SCALE_PLACEHOLDER
PTR_START = PTR_START_PLACEHOLDER
PTR_BLOCK = PTR_BLOCK_PLACEHOLDER
N_POINTERS = N_POINTERS_PLACEHOLDER
LINK_Q_VARS = LINK_Q_VARS_PLACEHOLDER
LINK_MAX_SHIFT = LINK_MAX_SHIFT_PLACEHOLDER
LINK_GRIND_BITS = LINK_GRIND_BITS_PLACEHOLDER
JUMP_IDS = JUMP_IDS_PLACEHOLDER
MAX_PTR_WIDTH = MAX_PTR_WIDTH_PLACEHOLDER
CHUNK_CAP = CHUNK_CAP_PLACEHOLDER
CHUNK_D = CHUNK_D_PLACEHOLDER
CHUNK_WIDTH = CHUNK_WIDTH_PLACEHOLDER
CHUNK_IDX = CHUNK_IDX_PLACEHOLDER
CHUNK_WORD = CHUNK_WORD_PLACEHOLDER
LINK_ROW_GRIND = LINK_ROW_GRIND_PLACEHOLDER  # a row round's grind, by d
LINK_PTR_GRIND = LINK_PTR_GRIND_PLACEHOLDER  # a pointer round's grind, by d
LINK_D_MIN = LINK_D_MIN_PLACEHOLDER  # the chunks of the narrowest pointer, BYTECODE_LOG bits
LINK_JUMP_TABLE = LINK_JUMP_TABLE_PLACEHOLDER
LIG_N_LEVELS = LIG_N_LEVELS_PLACEHOLDER
LIG_YR_LEVEL = LIG_YR_LEVEL_PLACEHOLDER
LIG_YR_LOG_LEN = LIG_YR_LOG_LEN_PLACEHOLDER
LIG_YR_LEN = LIG_YR_LEN_PLACEHOLDER
LIG_TOTAL_FOLDS = LIG_TOTAL_FOLDS_PLACEHOLDER
LIG_CAP_DEPTH = LIG_CAP_DEPTH_PLACEHOLDER
LIG_POS_OFF = LIG_POS_OFF_PLACEHOLDER  # a level's first query position, at its rate
LIG_POS_TOTAL = LIG_POS_TOTAL_PLACEHOLDER  # every level's, a candidate's one entry
VANISH_BY_COLS = VANISH_BY_COLS_PLACEHOLDER  # the subspace-vanishing values of n columns at n(n+1)/2
VANISH_INVS_BY_COLS = VANISH_INVS_BY_COLS_PLACEHOLDER  # and their inverses
LIG_QUERIES = LIG_QUERIES_PLACEHOLDER
LIG_FOLDS = LIG_FOLDS_PLACEHOLDER
LIG_LEAF_CELLS = LIG_LEAF_CELLS_PLACEHOLDER
LIG_PACKED_ROW_CAP = LIG_PACKED_ROW_CAP_PLACEHOLDER
LIG_ROW_CAP = LIG_ROW_CAP_PLACEHOLDER
LIG_PATH_CAP = LIG_PATH_CAP_PLACEHOLDER
LIG_TREE_DEPTH = LIG_TREE_DEPTH_PLACEHOLDER
LIG_SQUEEZES = LIG_SQUEEZES_PLACEHOLDER
LIG_LOG_MSG_COLS = LIG_LOG_MSG_COLS_PLACEHOLDER
LIG_RESIDUAL_FOLD_OFF = LIG_RESIDUAL_FOLD_OFF_PLACEHOLDER
LIG_RESIDUAL_PREFIX_LEN = LIG_RESIDUAL_PREFIX_LEN_PLACEHOLDER
LIG_HIGH_BITS = LIG_HIGH_BITS_PLACEHOLDER  # the bits of a level's high-part index, j < folds
LIG_FOLDS_OFF = LIG_FOLDS_OFF_PLACEHOLDER
LIG_MIN_SHIFT_INV = LIG_MIN_SHIFT_INV_PLACEHOLDER
# The most coordinates of a q_keccak opening point, its row's and its slot's: the stride of z_vals.
QKECCAK_VARS_CAP = QKECCAK_VARS_CAP_PLACEHOLDER

# ------------------------------------------------------ statements and deferral
# A node defers one claim on the program split by opcode (the link's columns, N_SPLIT
# of them padded to 2^SPLIT_LOG). DEFER_SIZE is the region one sub-proof's verification
# exports: the link point's BYTECODE_LOG instruction coordinates, then the split columns'
# values there. DEFER_STMT_* index the batched claim a node's OWN statement carries: its
# point (instructions, then columns), then its value. The Fiat-Shamir seed rides the public input rather than being baked,
# so one compiled guest verifies proofs of any inner program.
BYTECODE_LOG = BYTECODE_LOG_PLACEHOLDER  # log rows of the bytecode blocks
DEFER_SIZE = DEFER_SIZE_PLACEHOLDER
BYTECODE_VARS = BYTECODE_VARS_PLACEHOLDER  # = BYTECODE_LOG + SPLIT_LOG
N_SPLIT = N_SPLIT_PLACEHOLDER
SPLIT_LOG = SPLIT_LOG_PLACEHOLDER
# The program side (verifier::link::slot_weights): term i adds PW_COEF * factor * split
# column PW_COL to X_omega, or to P_fp when PW_FRAME. The factor is eta_bc * slot[PW_ARG]
# (kind 0), eta_mem * gm0 * mu[PW_ARG] (kind 1) or eta_mem * gm1 * mu[PW_ARG] (kind 2).
N_SPLIT_TERMS = N_SPLIT_TERMS_PLACEHOLDER
PW_COL = PW_COL_PLACEHOLDER
PW_FRAME = PW_FRAME_PLACEHOLDER
PW_KIND = PW_KIND_PLACEHOLDER
PW_ARG = PW_ARG_PLACEHOLDER
PW_COEF = PW_COEF_PLACEHOLDER
N_ROW_LOGS = MAX_PTR_WIDTH + 1  # a table's log height is at most the pointer width
ROW_BITS = N_ROW_LOGS + 1  # a row count's bits, a table's stride in the row-bit buffer
LINK_W_ARMS = MAX_PTR_WIDTH + 1 - BYTECODE_LOG  # the pointer widths from BYTECODE_LOG
LINK_D_ARMS = CHUNK_CAP + 1 - LINK_D_MIN
LINK_REC = FS_CELLS + 2  # a round's record: the sponge, the cursor, the claim
LINK_TAIL_CAP = CHUNK_CAP + 1  # a row round's coefficients past c1
# The link's challenges after theta_0 whose count is fixed (verifier::link::packed_challenges):
# theta's rest, gamma, mu, alpha, eta and eps. tau, zeta and nu follow, then the last
# permutation's unused cells.
LINK_FIXED = N_TABLES - 1 + 5 + N_ACCESSES + LOG2_BYTECODE_COLS + 2 + N_POINTERS
LINK_CHAL_CAP = 1 + LINK_FIXED + MAX_PTR_WIDTH + MAX_PTR_WIDTH + CHUNK_CAP + 7
LINK_VALS_CAP = 2 * CHUNK_CAP  # D_i at r and at 1 + r, at the widest chunking
EQ_Q_AT = 2 ** LINK_Q_VARS - 2  # eq(q_point, .) in its eqtree
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
# The coverage table's slots, both schemes' declared claims and their duplicates, are
# bounded by the memory itself: each count is a g-power address (`assert_gpow`), so its
# log is below the announced memory size, at most 2^30, and sums of a few never wrap.
# MAX_RECURSIONS is the arity of an aggregation tree.
MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER


# ---------------------------------- LeanDA ------------------------------------------
# Blob and cell widths are fixed. The blob count is hinted and bounded by DA_MAX_ROWS;
# zero rows pad the matrix to DA_MAX_ROWS.
LOG_BLOB_SYMBOLS = LOG_BLOB_SYMBOLS_PLACEHOLDER
LOG_CELL_SYMBOLS = LOG_CELL_SYMBOLS_PLACEHOLDER
DA_MAX_ROWS = DA_MAX_ROWS_PLACEHOLDER
DA_LOG_MAX_ROWS = DA_LOG_MAX_ROWS_PLACEHOLDER
DA_PAD_BLOB_0 = DA_PAD_BLOB_0_PLACEHOLDER
DA_PAD_BLOB_1 = DA_PAD_BLOB_1_PLACEHOLDER
# Vhat_j at the points the membership vector's product tree needs (da_factors): each
# parent node of the tree over a cell index, then of the tree inside a cell, at the bit
# j it splits; and Vhat_j(beta_(LOG_CELL_SYMBOLS + b)) at LOG_CELL_SYMBOLS * b + j, for
# each factor j inside a cell and bit b of the cell index.
DA_VHAT = DA_VHAT_PLACEHOLDER
DA_VHAT_COLUMN = DA_VHAT_COLUMN_PLACEHOLDER

DA_LOG_M = LOG_BLOB_SYMBOLS + 1              # log of the symbols per encoded row
DA_CELL = 2 ** LOG_CELL_SYMBOLS              # symbols in a cell
DA_BLOCK_BITS = DA_LOG_M - LOG_CELL_SYMBOLS  # log of the cells per row
DA_CELLS = 2 ** DA_BLOCK_BITS                # cells per row
DA_SUM = 4 * DA_CELLS                        # where a blob's running sum starts, past its tree
DA_REGION = DA_SUM + DA_CELLS + 1            # cells of one blob's tree and running sum

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


def is_zero(word):
    # 1 if the word is zero, else 0: its norm lo^2 + x lo hi + hi^2 is in K and zero only at zero
    # (y^2 + x y + 1 is irreducible over K).
    lo, hi = split_limbs(word)
    z = StackBuf(1)
    if lo * lo + GEN * lo * hi + hi * hi == 0:
        z[0] = 1
    else:
        z[0] = 0
    return z[0]


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
# every call site, `k`. A fifth scalar, or a challenge, permutes; every challenge outside
# a packed draw is a permutation of its own.


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
    bits = StackBuf(SIZE_BITS)  # nbits = SIZE_BITS at both callers
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
    # 2^width. Returns n's bit pattern, `tabs[g^n]` (`exponent_tables`).
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
    # Sized to the windows, a StackBuf taking a parse-time size.
    if const(per_word * n_win == 24):
        wins = StackBuf(24)
    elif const(per_word * n_win == 28):
        wins = StackBuf(28)
    elif const(per_word * n_win == 30):
        wins = StackBuf(30)
    else:
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


@inline
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


def one_plus_suffixes(chain, a, n: Const):
    # chain[k] = prod_{k <= i < n} (1 + a_i), for k <= n.
    chain[GEN ** n] = 1
    v = 1
    for kk in unroll(0, n):
        k = n - 1 - kk
        v = v * (1 + a[GEN ** k])
        chain[GEN ** k] = v
    return 0


def eq_prefix_run(chain, seed, a, b1, n: Const):
    chain[GEN ** 0] = seed
    v = seed
    for k in unroll(0, n):
        v = v * (a[GEN ** k] + b1[GEN ** k])
        chain[GEN ** (k + 1)] = v
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


@inline
def split_count(count_g, low: Const):
    # count = 2^low q + r, r < 2^low, from count's SPLIT_COUNT_BITS advice bits: g^q and g^r.
    bits = StackBuf(SPLIT_COUNT_BITS)
    hint_decompose_bits_exponent(bits, count_g, SPLIT_COUNT_BITS)
    r_g = GEN ** 0
    q_g = GEN ** 0
    for k in unroll(0, SPLIT_COUNT_BITS):
        b = bits[k]
        bits[k] = b * b
        if const(k // low == 0):
            r_g *= 1 + b * (1 + GEN ** (2 ** k))
        else:
            q_g *= 1 + b * (1 + GEN ** (2 ** (k - low)))
    assert q_g ** const(2 ** low) * r_g == count_g
    return q_g, r_g


def rs_eq_run(z_vals, point1, count_g, seed):
    # One run of the telescoped ring-switch product E = sum_k c_k * prod_j
    # (z_j^(2^k) + 1 + ris_j): coordinate x multiplies row k by (z^(2^k) + 1 +
    # point_x), z evolving by squaring per row. The runtime coordinates walk
    # OUTSIDE and the fixed Frobenius powers inside, so nothing stores a z-power
    # table. Coordinates go RS_CHUNK an iteration, so a row is read and written once
    # per chunk; count = RS_CHUNK q + r is pinned from advice bits, and the r left
    # over run after the loop, on q + 2 rows from the first, `seed`. Returns the final row.
    q_g, r_g = split_count(count_g, RS_CHUNK_BITS)
    chain = HeapBuf((q_g * GEN ** 2) ** BASE_FIELD_BITS)
    for k in unroll(0, BASE_FIELD_BITS):
        chain[GEN ** k] = seed[GEN ** k]
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
# A level's rounds fold its lanes by the affine combiner G + (alpha + beta X) F of
# [CWYZ26], the claim carried by four scalars a round and the weight folded
# at alpha, so the alphas are the weight's point (verifier::whir::verify_whir). A
# non-final level then commits the folded lane's low part, sends its high part, and glues
# its OOD claim and its queries, each opened row folded as the lanes were and corrected by
# the high part. The final level sends the whole folded lane, checks the queries against
# it, and closes with a sumcheck over the low part.


@inline
def opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, alphas, coefs):
    # One fold round: the four scalars [u0, w, c0, c1], grind, then alpha, beta. The
    # row folds read alpha, beta at coefs[0..2]; alpha is also the point's coordinate.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    msg = StackBuf(8)
    u0, cursor = fs_next(msg, 0, cursor)
    w, cursor = fs_next(msg, 1, cursor)
    c0, cursor = fs_next(msg, 2, cursor)
    c1, cursor = fs_next(msg, 3, cursor)
    sp, alpha, cursor = fs_grind_squeeze(sp, msg, 4, cursor, tabs, FOLD_GRIND_BITS)
    rate = StackBuf(8)
    sp, beta = squeeze(sp, rate, 0)
    alphas[GEN ** 0] = alpha
    coefs[GEN ** 0] = alpha
    coefs[GEN ** 1] = beta
    # u0 + alpha (u0 + claim) + alpha^2 w + beta c0 + alpha beta (c0 + c1)
    out = u0 + beta * c0 + alpha * (u0 + claim + alpha * w + beta * (c0 + c1))
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, out


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


def packed_message(fs0, fs1, fs2, fs3, fs4, msg, n: Const):
    # The n words at msg absorbed eight a permutation (transcript::observe_packed), the last one's rate zero past
    # them, then the permutation the next challenge comes from. Returns the challenge and the capacity.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    for i in unroll(0, n // 8):
        nxt = StackBuf(KECCAK_STATE)
        keccak(msg[8 * i:8 * i + 2], msg[8 * i + 2:8 * i + 4], nxt, tail=msg[8 * i + 4:8 * i + 8], cap=sp)
        sp = nxt
    if const(n % 8 != 0):
        rest = StackBuf(8)
        for j in unroll(0, n % 8):
            rest[j] = msg[GEN ** (n - n % 8 + j)]
        for j in unroll(n % 8, 8):
            rest[j] = 0
        nxt = StackBuf(KECCAK_STATE)
        keccak(rest[0:2], rest[2:4], nxt, tail=rest[4:8], cap=sp)
        sp = nxt
    out = StackBuf(KECCAK_STATE)
    keccak([0, 0], [0, 0], out, cap=sp)
    return out[0], out[8], out[9], out[10], out[11], out[12]


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
    # node with its hinted sibling, on the side the bit names.
    for r in unroll(0, width):
        lvl = lvl0 + r
        nxt = StackBuf(2)
        if const((k // 2 ** r) % 2 == 0):
            keccak([n0, n1], path[2 * lvl:2 * lvl + 2], nxt)
        else:
            keccak(path[2 * lvl:2 * lvl + 2], [n0, n1], nxt)
        n0 = nxt[0]
        n1 = nxt[1]
    return n0, n1


@inline
def walk_path(n0, n1, wins, cap, flags, path_depth: Const):
    # The path, a window of QW levels a dispatch (`decode_query_windows`): each arm knows its
    # levels' order bits, so it hashes the running node against its hinted sibling.
    # Sized to the depth, a multiple of QW but where the depth caps the cap.
    if const(path_depth == 6):
        path = StackBuf(12)
    elif const(path_depth == 12):
        path = StackBuf(24)
    elif const(path_depth == 18):
        path = StackBuf(36)
    elif const(path_depth == 24):
        path = StackBuf(48)
    else:
        path = StackBuf(LIG_PATH_CAP)
    hint_witness(path[0:2 * path_depth], "merkle_children")
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
    # and g^q, the constant parts folded into `cap` and `flags` by `level_queries`, so
    # one copy serves every cap depth. Every cap is at least two levels deep
    # (`decode_query_windows` gives q cap_depth - 1 bits).
    wb = wins[GEN ** ((path_depth + QW - 1) // QW)]
    q = wins[GEN ** ((path_depth + QW - 1) // QW + 1)]
    flags_q = flags * q
    flags_q[GEN ** 0] = 1  # the cap check propagates this obligation to the root
    q2 = q * q
    leaf = cap * q2 * q2 * (wb * wb)
    leaf[GEN ** 0] = n0
    leaf[GEN ** 1] = n1
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
def opening_query(cap, flags, coefs, hs, x, wins, base: Const, folds: Const, leaf_cells: Const, path_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
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
    walk_path(leaf_hash_state[0], leaf_hash_state[1], wins, cap, flags, path_depth)
    # Round j takes the lane pairs (F, G) to G + t F, t = alpha + beta x.
    for j in unroll(0, folds):
        t = coefs[GEN ** (2 * j)] + coefs[GEN ** (2 * j + 1)] * x
        n_out = const(2 ** (folds - 1 - j))
        for m in unroll(0, n_out):
            if const(j == 0):
                if const(base == 1):
                    acc[m] = row[interleave - 2 - 2 * m] + t * row[interleave - 1 - 2 * m]
                else:
                    acc[m] = row[2 * m + 1] + t * row[2 * m]
            else:
                src = const(interleave - 4 * n_out)
                acc[interleave - 2 * n_out + m] = acc[src + 2 * m + 1] + t * acc[src + 2 * m]
    value = acc[interleave - 2]
    if const(final == 1):
        # The unnormalized W_i(x) for i <= mu, W_(i+1) = W_i (W_i + W_i(beta_i)).
        ws = StackBuf(YR_LOG_CAP + 1)
        ws[0] = x
        for i in unroll(1, mu + 1):
            ws[i] = ws[i - 1] * (ws[i - 1] + VANISH_BY_COLS[vanish + i - 1])
        assert value == novel_eval(hs, ws, n_hs, hs_bits)
        out = 0
    else:
        out = value
    return out


def opening_queries(cap, flags, lam_inv, coefs, hs, positions, query_win_ptrs, n_iters_g, odd_g, base: Const, folds: Const, leaf_cells: Const, path_depth: Const, mu: Const, vanish: Const, n_hs: Const, hs_bits: Const, final: Const):
    # Specialize by row and path shape so opening configurations share query code.
    # Base-field rows (level 0) run two queries an iteration, sharing the loop
    # overhead and the challenge reads; an odd count, odd_g = g, runs its first query
    # alone, ahead of the pairs, the parity runtime so both share this code. Extension
    # rows run one query an iteration, odd_g = 1.
    # Query k is weighted lam^k: the chain runs h <- (h + v_k) / lam, ending at
    # sum_k lam^(k - n) v_k, which the caller scales by lam^n. The final level's
    # queries are checks, with nothing to sum.
    chain = HeapBuf(n_iters_g * GEN)
    # The loop's positions and window pointers, past a base row's odd first query: one pair, so
    # an iteration carries no pointer it does not read.
    if const(base == 1):
        if odd_g != 1:
            chain[GEN ** 0] = opening_query(cap, flags, coefs, hs, positions[GEN ** 0], query_win_ptrs[GEN ** 0], base, folds, leaf_cells, path_depth, mu, vanish, n_hs, hs_bits, final) * lam_inv
        else:
            chain[GEN ** 0] = 0
        loop_pos = positions * odd_g
        loop_wins = query_win_ptrs * odd_g
    else:
        chain[GEN ** 0] = 0
        loop_pos = positions
        loop_wins = query_win_ptrs
    for xi in mul_range(1, n_iters_g):
        if base == 1:
            sq = xi * xi
            pair_pos = loop_pos * sq
            pair_wins = loop_wins * sq
            d0 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** 0], pair_wins[GEN ** 0], base, folds, leaf_cells, path_depth, mu, vanish, n_hs, hs_bits, final)
            d1 = opening_query(cap, flags, coefs, hs, pair_pos[GEN ** 1], pair_wins[GEN ** 1], base, folds, leaf_cells, path_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = ((chain[xi] + d0) * lam_inv + d1) * lam_inv
        else:
            d = opening_query(cap, flags, coefs, hs, loop_pos[xi], loop_wins[xi], base, folds, leaf_cells, path_depth, mu, vanish, n_hs, hs_bits, final)
            if final == 0:
                chain[xi * GEN] = (chain[xi] + d) * lam_inv
    if final == 0:
        total = chain[n_iters_g]
    else:
        total = 0
    return total


@inline
def residual_query(basis_chain, row_d, hs, n_cols: Const, n_hs: Const, hs_bits: Const):
    # prod_t (d_t + chain_t) over one query's message-column coordinates, chain_t =
    # W_t(x), x the query position; then the high part's share of the query's fold,
    # What_mu(x) sum_j p_(2^mu + j) X_j(x), its normalizers in hs.
    ws = StackBuf(HIGH_BITS_CAP)
    ws[0] = basis_chain
    prefix_eq = row_d[GEN ** 0] + basis_chain
    for t in unroll(1, n_cols + 1):
        # subspace-vanishing recurrence for the novel-basis point, a function of n_cols alone
        if const(t // HIGH_BITS_CAP == 0):
            ws[t] = basis_chain * (basis_chain + VANISH_BY_COLS[n_cols * (n_cols + 1) // 2 + t - 1])
            basis_chain = ws[t]
        else:
            basis_chain *= basis_chain + VANISH_BY_COLS[n_cols * (n_cols + 1) // 2 + t - 1]
        if const(t != n_cols):
            prefix_eq *= row_d[GEN ** t] + basis_chain
    return prefix_eq, basis_chain * novel_eval(hs, ws, n_hs, hs_bits)


def level_residual(positions, row_d, hs, lam_inv, batches_g, rest_g, n_cols: Const, n_hs: Const, hs_bits: Const):
    # A non-final level's residual chains at the terminal point, over n = RES_BATCH b + r
    # queries, batches_g = g^b and rest_g = g^r: RES_BATCH queries an iteration sharing the
    # row's reads and constants, then the r left one at a time. The counts are runtime, so
    # levels of one column shape share this code. Query q is weighted lam^q: each chain
    # runs h <- (h + term_q) * lam_inv, ending at lam^-n * sum_q lam^q term_q.
    chain = HeapBuf((batches_g * rest_g * GEN) ** 2)
    chain[GEN ** 0] = 0
    chain[GEN ** 1] = 0
    for xr in mul_range(1, batches_g):
        batch = positions * xr ** RES_BATCH
        rec = chain * xr * xr
        h = rec[GEN ** 0]
        h_high = rec[GEN ** 1]
        for k in unroll(0, RES_BATCH):
            eq_q, high_q = residual_query(batch[GEN ** k], row_d, hs, n_cols, n_hs, hs_bits)
            h = (h + eq_q) * lam_inv
            h_high = (h_high + high_q) * lam_inv
        rec[GEN ** 2] = h
        rec[GEN ** 3] = h_high
    rest = chain * batches_g ** 2
    tail = positions * batches_g ** RES_BATCH
    for xq in mul_range(1, rest_g):
        rq = rest * xq * xq
        eq_q, high_q = residual_query(tail[xq], row_d, hs, n_cols, n_hs, hs_bits)
        rq[GEN ** 2] = (rq[GEN ** 0] + eq_q) * lam_inv
        rq[GEN ** 3] = (rq[GEN ** 1] + high_q) * lam_inv
    end = rest * rest_g ** 2
    return end[GEN ** 0], end[GEN ** 1]


def residual_query_slow(x, fold_cs, tail_cs, prefix_len: Const, yr_log: Const, vanish: Const):
    # prod_t (a_t + b_t chain_t) at the query position x, unfactored, the challenges read at
    # runtime: residual_query's weight for a level with a zero challenge.
    chain = x
    prod = 1
    for t in unroll(0, prefix_len):
        c = fold_cs[GEN ** t]
        prod *= 1 + c + c * VANISH_INVS_BY_COLS[vanish + t] * chain
        chain *= chain + VANISH_BY_COLS[vanish + t]
    for j in unroll(0, yr_log):
        c = tail_cs[GEN ** j]
        prod *= 1 + c + c * VANISH_INVS_BY_COLS[vanish + prefix_len + j] * chain
        chain *= chain + VANISH_BY_COLS[vanish + prefix_len + j]
    return prod


def level_residual_slow(positions, fold_cs, tail_cs, lam, zero, n_queries: Const, prefix_len: Const, yr_log: Const, vanish: Const):
    # On a level with a zero challenge (zero = 1), where b_t = 0 leaves the factored chains
    # nothing to divide by: lam^2 sum_q lam^q (the query's unfactored weight); 0 otherwise.
    out = StackBuf(1)
    if zero == 0:
        out[0] = zero
    else:
        out[0] = level_residual_sum(positions, fold_cs, tail_cs, lam, n_queries, prefix_len, yr_log, vanish)
    return out[0]


def level_residual_sum(positions, fold_cs, tail_cs, lam, n_queries: Const, prefix_len: Const, yr_log: Const, vanish: Const):
    # lam^2 sum_q lam^q (the query's unfactored weight), over g^n_queries queries.
    acc = HeapBuf(GEN ** (n_queries + 1))
    pw = HeapBuf(GEN ** (n_queries + 1))
    acc[GEN ** 0] = 0
    pw[GEN ** 0] = lam * lam
    for xq in mul_range(1, GEN ** n_queries):
        acc[xq * GEN] = acc[xq] + pw[xq] * residual_query_slow(positions[xq], fold_cs, tail_cs, prefix_len, yr_log, vanish)
        pw[xq * GEN] = pw[xq] * lam
    return acc[GEN ** n_queries]


def level_positions(word0, fs0, fs1, fs2, fs3, fs4, positions, win_ptrs, tabs, squeezes_g, depth: Const, cap_depth: Const):
    # A level's query positions, FIELD_BITS // depth a word: the first word, word0, drawn
    # by the query nonce's permutation, the rest one squeeze each. Row k of sqz is the
    # capacity of the permutation that drew word k - 1; returns the last one. The count of
    # squeezes, squeezes_g = g^count, is runtime, so levels of one path shape share this code.
    sqz = HeapBuf((squeezes_g * GEN) ** FS_CELLS)
    sqz[GEN ** FS_CELLS] = fs0
    sqz[GEN ** (FS_CELLS + 1)] = fs1
    sqz[GEN ** (FS_CELLS + 2)] = fs2
    sqz[GEN ** (FS_CELLS + 3)] = fs3
    sqz[GEN ** (FS_CELLS + 4)] = fs4
    decode_query_windows(word0, positions, win_ptrs, tabs, depth, cap_depth)
    for xs in mul_range(GEN, squeezes_g):
        row = sqz * xs ** FS_CELLS
        row_cap = fs_load(row, 0, 1)
        no_rate = StackBuf(8)
        row_sp, packed_word = squeeze(row_cap, no_rate, 0)
        fs_store(row * GEN ** FS_CELLS, 0, 1, row_sp)
        query_ptr = xs ** (FIELD_BITS // depth)
        decode_query_windows(packed_word, positions * query_ptr, win_ptrs * query_ptr, tabs, depth, cap_depth)
    sp = fs_load(sqz * squeezes_g ** FS_CELLS, 0, 1)
    return sp[0], sp[1], sp[2], sp[3], sp[4]


def level_queries(lam, lam_inv, coefs, hs, positions, win_ptrs, n_queries: Const, base: Const, folds: Const, leaf_cells: Const, depth: Const, cap_depth: Const, mu: Const, n_hs: Const, hs_bits: Const, final: Const):
    # A level's Merkle cap, hinted and checked up to its root, and the level's query batch
    # walked into it. Returns the root, the batch's sum, and lam^n_queries. At level 0 a
    # leaf image lists its lanes from the top down: the lanes a padding-free commitment
    # leaves out are its LEADING words, whose whole blocks the committer hashes once for
    # all leaves. The flip is a compile-time index.
    cap = HeapBuf(GEN ** (4 * 2 ** cap_depth))
    hint_witness(cap[0:4 * 2 ** cap_depth], "merkle_caps")
    flags = HeapBuf(GEN ** (2 ** cap_depth))
    hint_witness(flags[0:2 ** cap_depth], "merkle_cap_active")
    root_0, root_1 = verify_merkle_cap(cap, flags, cap_depth)
    if const(base == 1):
        pairs = n_queries // 2
        odd = n_queries % 2
    else:
        pairs = n_queries
        odd = 0
    # The cap leaf and flag a query reaches, offset past the levels above it.
    batched = opening_queries(cap * GEN ** (2 ** (cap_depth + 1)), flags * GEN ** (2 ** (cap_depth - 1)), lam_inv, coefs, hs, positions, win_ptrs, GEN ** pairs, GEN ** odd, base, folds, leaf_cells, depth - cap_depth, mu, mu * (mu + 1) // 2, n_hs, hs_bits, final)
    return root_0, root_1, batched, lam ** n_queries


@inline
def level_rate(ml: Const, r: Const):
    # A level's values that its rate sets, as g-powers: where its query positions start, its
    # squeezes, its queries in residual batches and the rest. Bound once, they leave the level's
    # rate dispatches the same runtime arguments in every arm, which fuses them.
    q = LIG_QUERIES[ml + r * LIG_RATE_STRIDE]
    return GEN ** LIG_POS_OFF[ml + r * LIG_RATE_STRIDE], GEN ** LIG_SQUEEZES[ml + r * LIG_RATE_STRIDE], GEN ** (q // RES_BATCH), GEN ** (q % RES_BATCH)


@inline
def positions_total(m_idx: Const, r: Const):
    # Every level's query positions at rate r, as the g-power a HeapBuf takes.
    return GEN ** LIG_POS_TOTAL[m_idx + r * LIG_N_LOG_SIZES]


def open_stacked(m_idx: Const, rate_sel, fs0, fs1, fs2, fs3, fs4, target, commit_root_0, commit_root_1, cursor, tabs):
    # The stacked WHIR opening, one specialization per committed log-size m_idx, the
    # rate g^rate_sel dispatched per level by a `match` into `level_rate` (query positions'
    # offsets, squeezes, query counts), `level_positions` and `level_queries` (tree and cap
    # depths, query counts), which read the tables a rate changes at `ml + r *
    # LIG_RATE_STRIDE`, and once into `positions_total` (LIG_POS_TOTAL). Every other LIG_*
    # table is read at the size's first-rate row `ml`, which `opening_placeholders` checks
    # does not vary by rate. Only the executed arm pops the opening's hint streams.
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

    # The final lane, its low part then its high part, read from the stream.
    final_msg = HeapBuf(GEN ** (yr_len + LIG_FOLDS[m_idx * LIG_MAX_LEVELS + last]))
    # Each cap root is checked against its transcript-bound level root.
    level_roots = HeapBuf(GEN ** (2 * n_levels))
    level_roots[GEN ** 0] = commit_root_0
    level_roots[GEN ** 1] = commit_root_1
    # The alphas in round order, the point's fold coordinates, and each round's
    # alpha, beta for the row folds.
    fold_challenges = HeapBuf(GEN ** n_folds)
    round_coefs = HeapBuf(GEN ** (2 * n_folds))
    # Per non-final level: its glued query batch's scalar lam^2 times lam^n (the inverse
    # chains' correction), 1/lam, and its OOD claim's point and scalar lam, at row lvl + 1.
    level_scales = HeapBuf(GEN ** n_levels)
    level_lam_invs = HeapBuf(GEN ** n_levels)
    level_hs = HeapBuf(GEN ** (n_levels * 2 ** HIGH_BITS_CAP))  # each high part, normalizers in
    ood_z = HeapBuf(GEN ** (n_levels * LIG_LOG_MSG_COLS_CAP))
    ood_scalars = HeapBuf(GEN ** n_levels)
    # A level's query positions, as many as its rate squeezes, start at LIG_POS_OFF.
    # Read from a table, not a `match`: no branch before a `HeapBuf`.
    pos_totals = HeapBuf(LIG_N_RATES)
    for r in unroll(0, LIG_N_RATES):
        pos_totals[GEN ** r] = positions_total(m_idx, r)
    pos_total = pos_totals[rate_sel]
    query_positions = HeapBuf(pos_total)
    query_win_ptrs = HeapBuf(pos_total)

    claim = target
    rates = StackBuf(4 * LIG_MAX_LEVELS)  # each level's `level_rate`
    for lvl in unroll(0, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        folds = LIG_FOLDS[ml]
        mu = LIG_LOG_MSG_COLS[ml]
        folds_off = LIG_FOLDS_OFF[ml]
        vanish = mu * (mu + 1) // 2
        rates[4 * lvl], rates[4 * lvl + 1], rates[4 * lvl + 2], rates[4 * lvl + 3] = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_rate(ml, r))
        squeezes_g = rates[4 * lvl + 1]
        level_pos = query_positions * rates[4 * lvl]
        level_wins = query_win_ptrs * rates[4 * lvl]
        for j in unroll(0, folds):
            fs0, fs1, fs2, fs3, fs4, cursor, claim = opening_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs, fold_challenges * GEN ** (folds_off + j), round_coefs * GEN ** (2 * (folds_off + j)))

        if const(lvl == last):
            word0, pow0, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, final_msg, const(yr_len + folds), 1)
        else:
            # The next level's root and this level's high part, then the OOD nonce,
            # whose permutation draws the OOD point's first coordinate, then its value
            # and the query nonce.
            sent = HeapBuf(GEN ** (2 + folds))
            z_first, pow_ood, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, sent, 2 + folds, 1)
            grind_check(pow_ood, tabs, OOD_GRIND_BITS)
            level_roots[GEN ** (2 * lvl + 2)] = sent[GEN ** 0]
            level_roots[GEN ** (2 * lvl + 3)] = sent[GEN ** 1]
            ood_row = ood_z * GEN ** ((lvl + 1) * LIG_LOG_MSG_COLS_CAP)
            fs0, fs1, fs2, fs3, fs4 = squeeze_point_from(fs0, fs1, fs2, fs3, fs4, z_first, ood_row, mu)
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            rate = StackBuf(8)
            ood_y, cursor = fs_next(rate, 0, cursor)
            sp = fs_absorb_nonce(sp, rate, 1, cursor[GEN ** 0])
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
        fs0, fs1, fs2, fs3, fs4 = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_positions(word0, fs0, fs1, fs2, fs3, fs4, level_pos, level_wins, tabs, squeezes_g, LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE]))
        if const(lvl != last):
            # The level's batching challenge, the query message's last squeeze.
            sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
            no_rate = StackBuf(8)
            sp, lam = squeeze(sp, no_rate, 0)
            lam_inv = 1 / (lam + is_zero(lam))  # any value at lam = 0, which scales every use
            fs0 = sp[8]
            fs1 = sp[9]
            fs2 = sp[10]
            fs3 = sp[11]
            fs4 = sp[12]
        else:
            lam = 0
            lam_inv = 0

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
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = final_msg[GEN ** c] * sc
        else:
            n_hs = 0  # the queries take no high part here
            hs_bits = 0
            hs = level_hs * GEN ** (lvl * 2 ** HIGH_BITS_CAP)
            for c in unroll(0, folds):
                sc = VANISH_INVS_BY_COLS[vanish + mu]
                for i in unroll(0, LIG_HIGH_BITS[ml]):
                    if const((c // 2 ** i) % 2 == 1):
                        sc = sc * VANISH_INVS_BY_COLS[vanish + i]
                hs[GEN ** c] = sent[GEN ** (2 + c)] * sc

        fin = (lvl + 1) // (last + 1)  # 1 at the final level, whose queries are checks
        root_0, root_1, batched, lam_pow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_queries(lam, lam_inv, round_coefs * GEN ** (2 * folds_off), hs, level_pos, level_wins, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], 1 // (lvl + 1), folds, LIG_LEAF_CELLS[ml], LIG_TREE_DEPTH[ml + r * LIG_RATE_STRIDE], LIG_CAP_DEPTH[ml + r * LIG_RATE_STRIDE], mu * fin, n_hs, hs_bits, fin))
        level_roots[GEN ** (2 * lvl)] = root_0
        level_roots[GEN ** (2 * lvl + 1)] = root_1

        if const(lvl != last):
            # The OOD claim takes lam, the query batch lam^2 times its own powers of
            # lam. A query's value is its fold plus the high part's share, which enters
            # the claim linearly: the residual pass adds it, scaled by every alpha and
            # tail challenge drawn after this level, the claim's factor from here on.
            ood_scalars[GEN ** (lvl + 1)] = lam
            claim = claim + lam * ood_y
            scale = lam * lam * lam_pow
            claim = claim + scale * batched
            level_scales[GEN ** lvl] = scale
            level_lam_invs[GEN ** lvl] = lam_inv

    # ---- the closing sumcheck over the final lane's low part ----
    tail_challenges = HeapBuf(GEN ** YR_LOG_CAP)
    for j in unroll(0, yr_log):
        fs0, fs1, fs2, fs3, fs4, cursor, claim, tail_c = opening_tail_round(fs0, fs1, fs2, fs3, fs4, cursor, claim, tabs)
        tail_challenges[GEN ** j] = tail_c
    for j in unroll(yr_log, YR_LOG_CAP):
        tail_challenges[GEN ** j] = 0

    yr_at_tail = fold_final_msg(final_msg, tail_challenges, yr_log)

    # ---- the same point, indexed by committed-witness coordinate ----
    # The alphas bind coordinates in ROUND order, and level 0's are the lane fold,
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
    # alphas then tail coords). Factoring b_t = c_t * inv_t out of every coordinate
    # leaves (a_t / b_t) + chain_t per query, so a query is one add and one multiply
    # a coordinate, and the level's product of the b_t scales its sum once.
    basis_d = HeapBuf(GEN ** (n_levels * LIG_LOG_MSG_COLS_CAP))
    level_scale = HeapBuf(GEN ** n_levels)
    level_after = HeapBuf(GEN ** n_levels)  # the product of the challenges after the level
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        prefix_len = LIG_RESIDUAL_PREFIX_LEN[ml]
        vanish = LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2
        scale = level_scales[GEN ** lvl]
        after = GEN ** 0
        for t in unroll(0, prefix_len):
            after *= fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
        for j in unroll(0, yr_log):
            after *= tail_challenges[GEN ** j]
        # On a level with a zero challenge every division takes 1, and the scale, from the
        # true coef_b, is zero: level_residual_slow sums that level.
        zero = is_zero(after)
        nonzero = 1 + zero
        for t in unroll(0, prefix_len):
            fold_c = fold_challenges[GEN ** (LIG_RESIDUAL_FOLD_OFF[ml] + t)]
            coef_b = fold_c * VANISH_INVS_BY_COLS[vanish + t]
            basis_d[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + t)] = (1 + fold_c) * (1 / (coef_b * nonzero + zero))
            scale *= coef_b
        for j in unroll(0, yr_log):
            tail_c = tail_challenges[GEN ** j]
            coef_b = tail_c * VANISH_INVS_BY_COLS[vanish + prefix_len + j]
            basis_d[GEN ** (lvl * LIG_LOG_MSG_COLS_CAP + prefix_len + j)] = (1 + tail_c) * (1 / (coef_b * nonzero + zero))
            scale *= coef_b
        level_scale[GEN ** lvl] = scale
        level_after[GEN ** lvl] = after
    # Per level: the glued weights' sum, then the claim's correction.
    inner_chain = HeapBuf(GEN ** (2 * n_levels))
    inner_chain[GEN ** 0] = 0
    inner_chain[GEN ** 1] = claim
    for lvl in unroll(0, last):
        ml = m_idx * LIG_MAX_LEVELS + lvl
        # level_scales carries the lam^(n + 2) that the chains' 1/lam steps leave out.
        level_pos = query_positions * rates[4 * lvl]
        h, h_high = level_residual(level_pos, basis_d * GEN ** (lvl * LIG_LOG_MSG_COLS_CAP), level_hs * GEN ** (lvl * 2 ** HIGH_BITS_CAP), level_lam_invs[GEN ** lvl], rates[4 * lvl + 2], rates[4 * lvl + 3], LIG_LOG_MSG_COLS[ml], LIG_FOLDS[ml], LIG_HIGH_BITS[ml])
        # accumulate lam^(n+2) * prod_t b_t * (the level's residual chain), or on a level with
        # a zero challenge its slow sum, into the total, and lam^(n+2) * (the challenges after
        # the level) * (its high chain) into the claim
        zero = is_zero(level_after[GEN ** lvl])
        slow = match(log(rate_sel), range(0, LIG_N_RATES), lambda r: level_residual_slow(level_pos, fold_challenges * GEN ** LIG_RESIDUAL_FOLD_OFF[ml], tail_challenges, ood_scalars[GEN ** (lvl + 1)], zero, LIG_QUERIES[ml + r * LIG_RATE_STRIDE], LIG_RESIDUAL_PREFIX_LEN[ml], yr_log, LIG_LOG_MSG_COLS[ml] * (LIG_LOG_MSG_COLS[ml] + 1) // 2))
        acc = inner_chain * GEN ** (2 * lvl)
        acc[GEN ** 2] = acc[GEN ** 0] + level_scale[GEN ** lvl] * h + slow
        acc[GEN ** 3] = acc[GEN ** 1] + level_scales[GEN ** lvl] * level_after[GEN ** lvl] * h_high

    # The OOD claims' eq weights at the same terminal point, each glued with its level's
    # lam.
    ood_inner = 0
    for ood_lvl in unroll(1, n_levels):
        ml = m_idx * LIG_MAX_LEVELS + ood_lvl
        z_folded = LIG_LOG_MSG_COLS[ml - 1] - yr_log
        ris_start = LIG_FOLDS_OFF[ml]
        oz = ood_z * GEN ** (ood_lvl * LIG_LOG_MSG_COLS_CAP)
        scalar = ood_scalars[GEN ** ood_lvl]
        for t in unroll(0, z_folded):
            scalar *= (1 + oz[GEN ** t] + fold_challenges[GEN ** (ris_start + t)])
        for t in unroll(0, yr_log):
            scalar *= (1 + oz[GEN ** (z_folded + t)] + tail_challenges[GEN ** t])
        ood_inner += scalar
    total = inner_chain * GEN ** (2 * last)
    return total[GEN ** 1], point, point1, total[GEN ** 0] + ood_inner, yr_at_tail, cursor


# ============================== inner-proof verification ============================
# The phases of `verify_sub` and their helpers. A phase takes and returns the sponge's
# five words and the stream cursor, so the sequence is what binds them.


def index_mle(zeta, n: Const):
    # The MLE of [1, g, g^2, ...] at zeta[..n] (multilinear::index_mle):
    # prod_t (1 + zeta_t * (1 + g^(2^t))).
    v = GEN ** 0
    for t in unroll(0, n):
        if t == 0:
            v = 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
        else:
            v *= 1 + zeta[GEN ** t] * INDEX_MLE_FACTORS[t]
    return v


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
    # The pack and the segment, a runtime number of rounds y = KR_STEP log(step_g) + log(rem_g), each run
    # straight in a frame its count sizes: a dispatch on step_g (zero or KR_STEP rounds), then one on rem_g.
    prev_point = claim[GEN ** KC_POINT]
    point = HeapBuf(y_g)
    f0, f1, f2, f3, f4, cursor, value = match(log(step_g), range(0, 2), lambda k: layer_rounds(sp[8], sp[9], sp[10], sp[11], sp[12], cursor, value, prev_point, point, tabs, KR_STEP * k))
    shift = step_g ** KR_STEP
    f0, f1, f2, f3, f4, cursor, value = match(log(rem_g), range(0, KR_STEP), lambda k: layer_rounds(f0, f1, f2, f3, f4, cursor, value, prev_point * shift, point * shift, tabs, k))
    sp = fs_cap(f0, f1, f2, f3, f4)
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
    assert weight_at_local[0] * (kappa * t0 + (kappa + t1) * t2) == value
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


def layer_rounds(fs0, fs1, fs2, fs3, fs4, cursor, run, prev_point, point, tabs, n: Const):
    # n rounds of a layer's sumcheck (keccak_layer). Round q has degree two with the eq factor
    # pulled out, and the prover sends its coefficients c1 and c2 (g_1, g_2), c0 being fixed by
    # the claim. With r the round's coordinate and c its challenge, q(c) = claim + (r + c) c1 +
    # (r + c^2) c2, which is the next normalized claim. The round grinds for degree three, the
    # eq factor included.
    # A 13-cell output's view of the carried capacity, its last five cells.
    sp = [0, 0, 0, 0, 0, 0, 0, 0, fs0, fs1, fs2, fs3, fs4]
    for q in unroll(0, n):
        r_eq = prev_point[GEN ** q]
        rate = StackBuf(8)
        g_1, cursor = fs_next(rate, 0, cursor)
        g_2, cursor = fs_next(rate, 1, cursor)
        sp, challenge, cursor = fs_grind_squeeze(sp, rate, 2, cursor, tabs, ROUND3_GRIND_BITS)
        point[GEN ** q] = challenge
        run = run + (r_eq + challenge) * g_1 + (r_eq + challenge * challenge) * g_2
    return sp[8], sp[9], sp[10], sp[11], sp[12], cursor, run


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
    # tau >= FLOORS[TABLE_KECCAK] is certified, so the pack count is a real count.
    # The ring-switching map's challenges are drawn after it, by the caller, under
    # the batch grind.
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


def certify_stack(kappa_base, g_squares):
    # Certify the stack's layout (multilinear::stack_offsets): every block whole, 2^kappa words at an offset
    # aligned to its size, the blocks end to end sorted by kappa down, then by index. A block group is consecutive
    # in that order, so a hinted order of the groups, certified strictly descending in its rank key, places every
    # block at a running sum. Returns the stack's log as a g-power, and per block g^offset and g^kappa.
    kb = StackBuf(N_TABLES + 2)
    for i in unroll(0, N_TABLES + 2):
        kb[i] = kappa_base[GEN ** i]
    group_key = HeapBuf(N_STK_GROUPS)
    group_size = HeapBuf(N_STK_GROUPS)
    for gi in unroll(0, N_STK_GROUPS):
        b0 = STK_GROUP_START[gi]
        kappa_g = kb[STK_SRC[b0]] * GEN ** STK_ADJ[b0]
        assert log(kappa_g) < SIZE_BITS
        # The key's exponent: kappa STK_STRIDE - first block.
        group_key[GEN ** gi] = kappa_g ** STK_STRIDE * INV_GEN ** b0
        group_size[GEN ** gi] = g_squares[kappa_g] ** (STK_GROUP_START[gi + 1] - b0)
    group_order = HeapBuf(N_STK_GROUPS)
    hint_witness(group_order[0:N_STK_GROUPS], "stk_group_order")
    group_at = HeapBuf(N_STK_GROUPS)
    g_total = GEN ** 0
    for rank in unroll(0, N_STK_GROUPS):
        gi = group_order[GEN ** rank]
        assert log(gi) < N_STK_GROUPS
        key = group_key[gi]
        # A negative step wraps around the order of GEN and cannot pass this check.
        if rank != 0:
            assert log(prev_key / key * INV_GEN) < STK_KEY_BOUND
        group_at[gi] = g_total  # write-once: a repeated group collides
        g_total *= group_size[gi]
        prev_key = key
    gmv = log2_ceil_in_the_exponent(g_total, g_squares, STK_MIN_LOG, SIZE_BITS)
    # Per block, N_STK_BLOCKS apart: g^offset, then g^kappa.
    outs = HeapBuf(2 * N_STK_BLOCKS)
    for gi in unroll(0, N_STK_GROUPS):
        b0 = STK_GROUP_START[gi]
        kappa_g = kb[STK_SRC[b0]] * GEN ** STK_ADJ[b0]
        step = g_squares[kappa_g]
        at_g = group_at[GEN ** gi]
        for b in unroll(b0, STK_GROUP_START[gi + 1]):
            outs[GEN ** b] = at_g
            outs[GEN ** (N_STK_BLOCKS + b)] = kappa_g
            if const(b + 1 != STK_GROUP_START[gi + 1]):
                at_g *= step
    return gmv, outs, outs * GEN ** N_STK_BLOCKS


def column_selector(offset, sel_eq, sel_g, n_nib: Const, kappa: Const):
    # The column's selector at the complete opening point, from hinted g-power digits
    # of its offset's nibbles at and above kappa // 4, each range-checked below 16.
    # Pinning their weighted product to the certified offset makes them its own
    # nibbles (a base-16 representation is unique), and that offset is 2^kappa-aligned
    # (certify_stack places blocks largest first), so the lowest digit, kappa's own
    # nibble, is a multiple of 2^(4 - width): the strided level-width table holds it.
    # The digits run to `n_nib` nibbles, the stack's: its offsets and the point are zero
    # above, where every factor is eq(0, 0) = 1, and rebuilding the offset from them
    # bounds it there.
    digits = StackBuf(SEL_NIBBLES)
    # max(n_nib - kappa // 4, 0) digits, from nibble kappa // 4 on.
    hint_decompose_digits_exponent(digits, offset, 4 * n_nib, (kappa // 4) // (n_nib + 1) * (kappa // 4) + (1 - (kappa // 4) // (n_nib + 1)) * n_nib - kappa // 4, 4, 4 * (kappa // 4))
    if const((kappa // 4) // n_nib != 0):
        selector = GEN ** 0
        rebuilt = GEN ** 0
    for j in unroll(kappa // 4, SEL_NIBBLES):
        if const(j // n_nib == 0):
            width = 4
            if const(j == kappa // 4):
                width = 4 * j + 4 - kappa
            d = digits[j - kappa // 4]
            assert log(d) < 16
            if const(j == kappa // 4):
                selector = sel_eq[GEN ** (SEL_EQ_STRIDE * j + SEL_EQ_OFF[width - 1]) * d]
                rebuilt = sel_g[GEN ** (16 * j) * d]
            else:
                selector *= sel_eq[GEN ** (SEL_EQ_STRIDE * j + SEL_EQ_OFF[width - 1]) * d]
                rebuilt *= sel_g[GEN ** (16 * j) * d]
    assert rebuilt == offset
    return selector


def selector_tables(point, point1, n_nib: Const):
    # Per nibble j of the selector bits, the eq tables over its top 1..4 coordinates,
    # the level-w one at SEL_EQ_OFF[w - 1], strided: entry u, a multiple of 2^(4 - w),
    # holds the eq of bit t of u against coordinate 4j + t for t >= 4 - w.
    sel_eq = HeapBuf(GEN ** (n_nib * SEL_EQ_STRIDE))
    for j in unroll(0, n_nib):
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
                sel_eq[GEN ** (SEL_EQ_STRIDE * j + SEL_EQ_OFF[w] + e)] = levels[16 * w + e]
    return sel_eq


def squeeze_packed(fs0, fs1, fs2, fs3, fs4, out, count_g):
    # count = log(count_g) permutations of the capacity alone, each writing its eight
    # rate cells to out, in order: four a loop frame, count = 4 h + r, then the r left. A
    # record per frame carries the capacity.
    h_g, r_g = split_count(count_g, 2)
    recs = HeapBuf((h_g * GEN * GEN) ** FS_CELLS)
    recs[GEN ** 0] = fs0
    recs[GEN ** 1] = fs1
    recs[GEN ** 2] = fs2
    recs[GEN ** 3] = fs3
    recs[GEN ** 4] = fs4
    for xk in mul_range(1, h_g):
        rec = recs * xk ** FS_CELLS
        cells = out * xk ** 32
        last = squeeze_cells(rec, cells, 4)
        fs_store(rec * GEN ** FS_CELLS, 0, 1, last)
    tail = recs * h_g ** FS_CELLS
    end = tail * GEN ** FS_CELLS
    done = match(log(r_g), range(0, 4), lambda k: squeeze_packed_last(tail, end, out * h_g ** 32, k))
    return end[GEN ** 0], end[GEN ** 1], end[GEN ** 2], end[GEN ** 3], end[GEN ** 4]


@inline
def squeeze_cells(rec, cells, n: Const):
    # n permutations of the capacity alone from the one at rec, each writing its eight rate
    # cells to cells, in order. Returns the last output.
    nxt = StackBuf(KECCAK_STATE)
    keccak([0, 0], [0, 0], nxt, cap=rec[0:FS_CELLS])
    for j in unroll(0, 8):
        cells[GEN ** j] = nxt[j]
    for i in unroll(1, n):
        nx = StackBuf(KECCAK_STATE)
        keccak([0, 0], [0, 0], nx, cap=nxt)
        for j in unroll(0, 8):
            cells[GEN ** (8 * i + j)] = nx[j]
        nxt = nx
    return nxt


def squeeze_packed_last(rec, end, cells, k: Const):
    # squeeze_packed's last k < 4 permutations, from record rec into record end.
    if const(k == 0):
        for j in unroll(0, FS_CELLS):
            end[GEN ** j] = rec[GEN ** j]
    else:
        last = squeeze_cells(rec, cells, k)
        fs_store(end, 0, 1, last)
    return 0


@inline
def link_round(sp, cur, cl, out, tabs, n_tail: Const, bits: Const):
    # One plain sum-check round (transcript::sumcheck_round_poly with no eq factor): c0
    # and the n_tail coefficients from c2 on are sent, c1 = claim + their sum, then a
    # grind of `bits` and the challenge y. Returns the sponge; out takes y, the cursor
    # and the claim.
    rate = StackBuf(8)
    tail = StackBuf(LINK_TAIL_CAP)
    c0, cur = fs_next(rate, 0, cur)
    for j in unroll(0, n_tail):
        if const((j + 1) % 4 == 0):
            sp = fs_perm(sp, rate, 4)
            rate = StackBuf(8)
        x, cur = fs_next(rate, (j + 1) % 4, cur)
        tail[j] = x
    sp, y, cur = fs_grind_squeeze(sp, rate, n_tail % 4 + 1, cur, tabs, bits)
    acc = tail[n_tail - 1]
    tsum = tail[n_tail - 1]
    for j in unroll(1, n_tail):
        acc = acc * y + tail[n_tail - 1 - j]
        tsum = tsum + tail[n_tail - 1 - j]
    acc = acc * y + (cl + tsum)
    out[0] = y
    out[1] = cur
    out[2] = acc * y + c0
    return sp


def link_rounds(fs0, fs1, fs2, fs3, fs4, cursor, claim, point, count_g, tabs, n_tail: Const, bits: Const):
    # count = log(count_g) link_round's, into point[0..count): four a loop frame, count =
    # 4 h + r, then the r left, their record after the last frame's. A record carries
    # the sponge, the cursor and the claim between loop frames.
    h_g, r_g = split_count(count_g, 2)
    recs = HeapBuf((h_g * GEN * GEN) ** LINK_REC)
    recs[GEN ** 0] = fs0
    recs[GEN ** 1] = fs1
    recs[GEN ** 2] = fs2
    recs[GEN ** 3] = fs3
    recs[GEN ** 4] = fs4
    recs[GEN ** 5] = cursor
    recs[GEN ** 6] = claim
    for xk in mul_range(1, h_g):
        rd = recs * xk ** LINK_REC
        pts = point * xk ** 4
        sp_in = fs_load(rd, 0, 1)
        o0 = StackBuf(3)
        sp0 = link_round(sp_in, rd[GEN ** 5], rd[GEN ** 6], o0, tabs, n_tail, bits)
        pts[GEN ** 0] = o0[0]
        o1 = StackBuf(3)
        sp1 = link_round(sp0, o0[1], o0[2], o1, tabs, n_tail, bits)
        pts[GEN ** 1] = o1[0]
        o2 = StackBuf(3)
        sp2 = link_round(sp1, o1[1], o1[2], o2, tabs, n_tail, bits)
        pts[GEN ** 2] = o2[0]
        o3 = StackBuf(3)
        sp3 = link_round(sp2, o2[1], o2[2], o3, tabs, n_tail, bits)
        pts[GEN ** 3] = o3[0]
        nxt = rd * GEN ** LINK_REC
        fs_store(nxt, 0, 1, sp3)
        nxt[GEN ** 5] = o3[1]
        nxt[GEN ** 6] = o3[2]
    last = recs * h_g ** LINK_REC
    out = last * GEN ** LINK_REC
    done = match(log(r_g), range(0, 4), lambda k: link_rounds_last(last, out, point * h_g ** 4, tabs, n_tail, bits, k))
    return out[GEN ** 0], out[GEN ** 1], out[GEN ** 2], out[GEN ** 3], out[GEN ** 4], out[GEN ** 5], out[GEN ** 6]


def link_rounds_last(rd, out, pts, tabs, n_tail: Const, bits: Const, k: Const):
    # link_rounds' last k < 4 rounds, from record rd into record out, their challenges at pts[0..k).
    sp_in = fs_load(rd, 0, 1)
    if const(k == 0):
        fs_store_cap(out, sp_in)
        out[GEN ** 5] = rd[GEN ** 5]
        out[GEN ** 6] = rd[GEN ** 6]
    else:
        o0 = StackBuf(3)
        sp0 = link_round(sp_in, rd[GEN ** 5], rd[GEN ** 6], o0, tabs, n_tail, bits)
        pts[GEN ** 0] = o0[0]
        if const(k == 1):
            fs_store(out, 0, 1, sp0)
            out[GEN ** 5] = o0[1]
            out[GEN ** 6] = o0[2]
        else:
            o1 = StackBuf(3)
            sp1 = link_round(sp0, o0[1], o0[2], o1, tabs, n_tail, bits)
            pts[GEN ** 1] = o1[0]
            if const(k == 2):
                fs_store(out, 0, 1, sp1)
                out[GEN ** 5] = o1[1]
                out[GEN ** 6] = o1[2]
            else:
                o2 = StackBuf(3)
                sp2 = link_round(sp1, o1[1], o1[2], o2, tabs, n_tail, bits)
                pts[GEN ** 2] = o2[0]
                fs_store(out, 0, 1, sp2)
                out[GEN ** 5] = o2[1]
                out[GEN ** 6] = o2[2]
    return 0


@inline
def fs_store_cap(rec, sp):
    # A five-cell capacity run into a record's first FS_CELLS cells.
    for j in unroll(0, FS_CELLS):
        rec[GEN ** j] = sp[j]
    return


def link_row_side(fs0, fs1, fs2, fs3, fs4, cursor, claim, chi, q_point, g_n, tabs, d: Const):
    # The row rounds, then the pointer-column rounds, at d chunks a pointer
    # (link::round_coefficients): d + 1 and d coefficients past c1, each round's grind
    # grinding_bits of its count less one.
    fs0, fs1, fs2, fs3, fs4, cursor, claim = link_rounds(fs0, fs1, fs2, fs3, fs4, cursor, claim, chi, g_n, tabs, d + 1, LINK_ROW_GRIND[d])
    fs0, fs1, fs2, fs3, fs4, cursor, claim = link_rounds(fs0, fs1, fs2, fs3, fs4, cursor, claim, q_point, GEN ** LINK_Q_VARS, tabs, d, LINK_PTR_GRIND[d])
    return fs0, fs1, fs2, fs3, fs4, cursor, claim


def chunk_d(w: Const):
    # g^d, d the chunks of a w-bit pointer (link::Chunks).
    return GEN ** CHUNK_D[w]


def table_size(rows, bits, h: Const):
    # Certify h against the table's row count and keep its bits: the advice is the bits
    # of rows + (2^h - 1), the complements of the row count's low bits, then its bit h,
    # set only alone. Returns g^rows and the least-height test's terms.
    word = rows + const(2 ** h - 1)
    hint_decompose_bits(bits, word, h + 1)
    g_rows = GEN ** 0
    for k in unroll(0, h):
        c = bits[GEN ** k]
        bits[GEN ** k] = c * c
        g_rows *= 1 + (1 + c) * (1 + GEN ** (2 ** k))
    top = bits[GEN ** h]
    bits[GEN ** h] = top * top
    g_rows *= 1 + top * (1 + GEN ** (2 ** h))
    if const(h == 0):
        low = 0
        lead = 1
        rest = 1
    else:
        below = 0
        for k in unroll(1, h):
            below = below * 2 + bits[GEN ** (h - 1 - k)]
        low = below + bits[GEN ** (h - 1)] * (2 ** (h - 1))
        lead = top + 1 + bits[GEN ** (h - 1)]
        rest = top + below + const(2 ** (h - 1) - 1)
    assert low + top * (2 ** h) == word
    assert top * (low + const(2 ** h - 1)) == 0
    return g_rows, lead, rest


def table_point(theta, tau, chi, bits, h: Const):
    # A table at its row point chi[..h], from its row count's complement bits: its row
    # weight theta sum_{u < rows} eq(tau, u) eq(chi, u) (link::omega_at, by prefix_sum's
    # walk from the top), LT_rows(chi) and eq(tau, chi).
    full = StackBuf(N_ROW_LOGS + 1)
    low = StackBuf(N_ROW_LOGS)
    high = StackBuf(N_ROW_LOGS)
    full[0] = 1
    pad = 1
    for k in unroll(0, h):
        t = tau[GEN ** k]
        x = chi[GEN ** k]
        hi = t * x
        e = 1 + t + x
        low[k] = hi + e
        high[k] = hi
        full[k + 1] = full[k] * e
        c = bits[GEN ** k]
        pad = c * x + (c + x) * pad
    top = bits[GEN ** h]
    total = top * full[h]
    prefix = 1
    for jj in unroll(0, h):
        j = h - 1 - jj
        bit = 1 + bits[GEN ** j]
        total = total + bit * prefix * low[j] * full[j]
        prefix = prefix * (low[j] + bit * (high[j] + low[j]))
    return theta * total, 1 + (1 + top) * pad, full[h]


def state_ends(zeta, cbits, w: Const):
    # eq(zeta[..w], 0) and eq(zeta[..w], cycles), the state identity's ends.
    e0 = 1
    ec = 1
    for k in unroll(0, w):
        z = zeta[GEN ** k]
        e0 = e0 * (1 + z)
        ec = ec * (1 + cbits[GEN ** k] + z)
    return e0, ec


def index_side(r, zeta, below, w: Const):
    # At the index point r[..w]: index_mle, eq(zeta, r), its shift by one (link::shift_eq),
    # and below[k] = prod_{k <= i < w} (1 + r_i) for k <= w (link's `below`).
    idx = index_mle(r, w)
    eqzr = 1
    shz = 0
    carry = 1
    for k in unroll(0, w):
        x = r[GEN ** k]
        z = zeta[GEN ** k]
        e = 1 + z + x
        shz = shz * e + carry * (1 + x) * z
        carry = carry * x * (1 + z)
        eqzr = eqzr * e
    below[GEN ** w] = 1
    acc = 1
    for kk in unroll(0, w):
        k = w - 1 - kk
        acc = acc * (1 + r[GEN ** k])
        below[GEN ** k] = acc
    return idx, eqzr, shz


@inline
def link_form(sent, f: Const):
    # Form f over the sent values: its terms TERM_COEF * a * b, a missing factor one.
    acc = 0
    for j in unroll(FORM_START[f], FORM_START[f + 1]):
        if const(TERM_A[j] == LINK_NO_POS):
            term = TERM_COEF[j]
        elif const(TERM_B[j] == LINK_NO_POS):
            term = TERM_COEF[j] * sent[GEN ** TERM_A[j]]
        else:
            term = TERM_COEF[j] * sent[GEN ** TERM_A[j]] * sent[GEN ** TERM_B[j]]
        acc = acc + term
    return acc


def link_terminal(r, sent, coef, shifts, cert_w, nu, rest, claim, w: Const):
    # The summand at the end point (link::Functionals::summand) from the pointer words'
    # 64 bit-slices, at the w-bit chunking: (coef D_0 + sum_s c_s T_s) prod_{i >= 1} D_i,
    # T_s chunk 0 read s further inside its window (zero past it), and the mirror
    # certificate, chunk i under cert_w nu_i. `rest` is eq0(q) times the base terms.
    d = CHUNK_D[w]
    # Chunk i's eq table at stride `step`, twice the widest chunk's (chunk 0's) size.
    step = const(2 ** (CHUNK_WIDTH[CHUNK_CAP * w] + 1))
    eqs = HeapBuf(GEN ** (CHUNK_D[w] * step))
    for i in unroll(0, d):
        eqtree(r * GEN ** CHUNK_IDX[CHUNK_CAP * w + i], eqs * GEN ** (step * i), CHUNK_WIDTH[CHUNK_CAP * w + i])
    sl = sent * GEN ** LINK_N_SENT
    vals = StackBuf(LINK_VALS_CAP)
    # D_i at r_i and at 1 + r_i.
    for i in unroll(0, d):
        n = 2 ** CHUNK_WIDTH[CHUNK_CAP * w + i]
        ws = CHUNK_WORD[CHUNK_CAP * w + i]
        at = step * i + n - 2
        acc = 0
        accr = 0
        for v in unroll(0, n):
            s_v = sl[GEN ** (ws + v)]
            acc = acc + eqs[GEN ** (at + v)] * s_v
            accr = accr + eqs[GEN ** (at + n - 1 - v)] * s_v
        vals[i] = acc
        vals[d + i] = accr
    # Chunk 0's factor: coef D_0 and each shift s's T_s under c_s.
    n0 = 2 ** CHUNK_WIDTH[CHUNK_CAP * w]
    low = coef * vals[0]
    for s in unroll(1, LINK_MAX_SHIFT + 1):
        acc = 0
        for v in unroll(0, n0):
            if const((v + s) // n0 == 0):
                acc = acc + eqs[GEN ** (n0 - 2 + v + s)] * sl[GEN ** v]
        low = low + shifts[GEN ** (s - 1)] * acc
    for i in unroll(1, d):
        low = low * vals[i]
    cert = 0
    for i in unroll(0, d):
        ci = cert_w * nu[GEN ** i]
        mirror = 1
        for k in unroll(CHUNK_IDX[CHUNK_CAP * w + i], CHUNK_IDX[CHUNK_CAP * w + i] + CHUNK_WIDTH[CHUNK_CAP * w + i]):
            x = r[GEN ** k]
            mirror = mirror * (x * x + x)
        cert = cert + ci * (vals[i] * vals[d + i] + mirror)
    assert low + cert + rest == claim
    return 0


# ============================ the stack opening's weights ==========================


def stack_selectors(offs, kaps, point, point1, g_squares, n_nib: Const):
    # Each block's selector at the opening point, the eq of its offset's bits above its kappa, over the nibbles a
    # stack of 2^m words has: its offsets and the point are zero above them. A kappa is at most the stack's log, the
    # block lying inside the stack.
    sel_eq = selector_tables(point, point1, n_nib)
    sel_g = g_squares * GEN ** SIZE_BITS
    sel = HeapBuf(N_STK_BLOCKS)
    for b in unroll(0, N_STK_BLOCKS):
        offset = offs[GEN ** b]
        s = match(log(kaps[GEN ** b]), range(0, N_COLUMN_LOGS), lambda kappa: column_selector(offset, sel_eq, sel_g, n_nib, kappa))
        sel[GEN ** b] = s
    return sel


def rs_eq_rows_all(row, zs, ps, n: Const):
    # rs_eq_rows keeping every row: rows 1..n past `row`, 64 cells apart, row i + 1 being
    # row i times (zs_i^(2^k) + ps_i) at k.
    if const(n != 0):
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
                row[GEN ** (BASE_FIELD_BITS * (i + 1) + k)] = acc
    return 0


def ring_rows(chain, zs, ps, c_table, count_g):
    # Rows 0..count of 64 cells (row m at chain g^(64 m)): c_k prod_{n < m} (zs_n^(2^k) + ps_n),
    # RS_CHUNK coordinates an iteration, count = RS_CHUNK q + r pinned from advice bits.
    for k in unroll(0, BASE_FIELD_BITS):
        chain[GEN ** k] = c_table[GEN ** k]
    q_g, r_g = split_count(count_g, RS_CHUNK_BITS)
    for xq in mul_range(1, q_g):
        base = xq ** RS_CHUNK
        done = rs_eq_rows_all(chain * base ** BASE_FIELD_BITS, zs * base, ps * base, RS_CHUNK)
    base = q_g ** RS_CHUNK
    done = match(log(r_g), range(0, RS_CHUNK), lambda n: rs_eq_rows_all(chain * base ** BASE_FIELD_BITS, zs * base, ps * base, n))
    return


def ring_cols(row, scl, msk, n: Const):
    # sum_q msk_q sum_k row_k scl_q^(2^k) over n columns sharing `row`: a ring piece's weight
    # (ring_switch::ring_weight) from its point's row, its scale and its selector.
    rs = StackBuf(BASE_FIELD_BITS)
    for k in unroll(0, BASE_FIELD_BITS):
        rs[k] = row[GEN ** k]
    total = 0
    for q in unroll(0, n):
        acc = 0
        sv = scl[GEN ** q]
        for k in unroll(0, BASE_FIELD_BITS):
            acc = acc + rs[k] * sv
            if const(k != BASE_FIELD_BITS - 1):
                sv = sv * sv
        total = total + acc * msk[GEN ** q]
    return total


def check_stack_terminal(g_squares, kappa_base, offs, kaps, gmv, chi, g_n, r_pt, g_log_mem, rm, z_vals, eq_q, c_table, rho, lam, gm1b, gm2b, point, point1, inner_total, yr_at_tail, sumcheck_target, ood_z):
    # Every stack claim's weight at the opening point, batched by the powers of lam in the native order: the ring
    # claim (the Keccak inputs', then the pointer columns' as rho times theirs, rho in each column's scale), the
    # memory term, the sent columns, the public input's two, the Keccak outputs, the OOD sample. A claim at row point
    # p on a column of 2^kappa words is eq(p, x[..kappa]) times the column's selector.
    rchi = HeapBuf((g_n * GEN) ** BASE_FIELD_BITS)
    pmask = HeapBuf(N_POINTERS)
    rq = HeapBuf(N_POINTERS)
    chain_chi = HeapBuf(EQ_CHAIN_ARMS + 1)
    chain_out = HeapBuf(EQ_CHAIN_ARMS + 1)
    chain_r = HeapBuf(EQ_CHAIN_ARMS + 1)
    chain_pi = HeapBuf(EQ_CHAIN_ARMS + 1)
    pi_pt = HeapBuf(MAX_LOG_MEM + 1)
    tq = HeapBuf(2 ** (QKECCAK_SLOT_LOG + 1) - 2)
    ood_chain = HeapBuf(MAX_STACK_LOG + 1)
    sel = match(log(gmv * INV_GEN ** LIG_MIN_LOG_SIZE), range(0, LIG_N_LOG_SIZES), lambda s: stack_selectors(offs, kaps, point, point1, g_squares, (LIG_MIN_LOG_SIZE + s + 3) // 4))
    kb = StackBuf(N_TABLES + 2)
    for i in unroll(0, N_TABLES + 2):
        kb[i] = kappa_base[GEN ** i]
    h5_g = kb[2 + TABLE_KECCAK]
    kq_g = h5_g * GEN ** QKECCAK_SLOT_LOG
    sel_qk = sel[GEN ** 2]
    sel_m0 = sel[GEN ** 0]
    sel_m1 = sel[GEN ** 1]

    # q_keccak's ring claim at the Keccak input point, its scale one.
    row_k = rs_eq_run(z_vals * GEN ** QKECCAK_VARS_CAP, point1, kq_g, c_table)
    w_kring = 0
    for k in unroll(0, BASE_FIELD_BITS):
        w_kring = w_kring + row_k[GEN ** k]
    w_total = w_kring * sel_qk

    # The pointer columns' ring claim, column q scaled by rho eq(q_point, q): their map is v -> Phi(rho v), so rho
    # joins each column's scale and the rows take the map's c_k. A table's columns share its row point chi[..h_t],
    # hence one row, Frobenius being additive; a column on a q_keccak slot sits in KECCAK, at h5.
    for q in unroll(0, N_POINTERS):
        rq[GEN ** q] = rho * eq_q[GEN ** (EQ_Q_AT + q)]
    ring_rows(rchi, chi, point1, c_table, g_n)
    # A slot's bits sit right above h5, q_keccak being aligned to its size.
    tpt = point * h5_g
    eqtree(tpt, tq, QKECCAK_SLOT_LOG)
    w_link = 0
    for t in unroll(0, N_TABLES):
        if const(PTR_START[t + 1] != PTR_START[t]):
            for q in unroll(PTR_START[t], PTR_START[t + 1]):
                b = PTR_BLOCK[q]
                if const(b // N_STK_BLOCKS == 0):
                    pmask[GEN ** q] = sel[GEN ** b]
                else:
                    pmask[GEN ** q] = tq[GEN ** (2 ** QKECCAK_SLOT_LOG - 2 + b - N_STK_BLOCKS)] * sel_qk
            row = rchi * kb[2 + t] ** BASE_FIELD_BITS
            w_link = w_link + ring_cols(row, rq * GEN ** PTR_START[t], pmask * GEN ** PTR_START[t], const(PTR_START[t + 1] - PTR_START[t]))
    w_total = w_total + w_link

    # The memory term at r[..log_mem], on both limbs.
    eq_prefix_chain(chain_r, 1, r_pt, point1, g_log_mem)
    w_mem = chain_r[g_log_mem] * (gm1b * sel_m0 + gm2b * sel_m1)

    # The public input's claims at [rm, 0, ..].
    pi_pt[GEN ** 0] = rm
    for i in unroll(1, MAX_LOG_MEM + 1):
        pi_pt[GEN ** i] = 0
    eq_prefix_chain(chain_pi, 1, pi_pt, point1, g_log_mem)
    pi_eq = chain_pi[g_log_mem]

    # The Keccak reduction's claim on the committed outputs, over the whole column.
    eq_prefix_chain(chain_out, 1, z_vals, point1, kq_g)

    # The OOD sample's claim closes the batch.
    eq_prefix_chain(ood_chain, 1, ood_z, point1, gmv)

    # The claims after the ring claim by Horner in lam, from the last: the OOD sample, the Keccak outputs, the public
    # input's two, the sent columns (each at its table's row point, on its own block or a slot of q_keccak), the
    # memory term.
    eq_prefix_chain(chain_chi, 1, chi, point1, g_n)
    acc = ood_chain[gmv]
    acc = acc * lam + chain_out[kq_g] * sel_qk
    acc = acc * lam + pi_eq * sel_m1
    acc = acc * lam + pi_eq * sel_m0
    slot_eq = chain_chi[h5_g] * sel_qk
    for jj in unroll(0, LINK_N_SENT):
        j = LINK_N_SENT - 1 - jj
        if const(SENT_TARGET[j] != LINK_NO_POS):
            if const(SENT_TARGET[j] // N_STK_BLOCKS == 0):
                b = SENT_TARGET[j]
                wgt = chain_chi[kaps[GEN ** b]] * sel[GEN ** b]
            else:
                wgt = slot_eq * tq[GEN ** (2 ** QKECCAK_SLOT_LOG - 2 + SENT_TARGET[j] - N_STK_BLOCKS)]
            acc = acc * lam + wgt
    acc = acc * lam + w_mem
    w_total = w_total + acc * lam
    assert (inner_total + w_total) * yr_at_tail == sumcheck_target
    return


def hint_stream(stream, n_g):
    # The proof stream's n chunks into `stream`.
    for xc in mul_range(1, n_g):
        at = stream * xc ** STREAM_CHUNK
        hint_witness(at[0:STREAM_CHUNK], "stream")
    return


def verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, defer_out):
    # In-circuit verification of ONE inner proof for the statement (pi_0, pi_1),
    # mirroring `crates/verifier`'s walk step for step. All proof data is hinted HERE, so
    # each call pops the next sub-proof's entry of every witness stream and the body
    # lowers once. The deferred claim goes to `defer_out`.
    tabs = g_squares * GEN ** WIN_TAB_AT
    h_logs = HeapBuf(N_TABLES)
    rows_bits = HeapBuf(N_TABLES * ROW_BITS)
    cbits = HeapBuf(MAX_PTR_WIDTH)
    shape = HeapBuf(4)
    chal = HeapBuf(LINK_CHAL_CAP)
    slot = HeapBuf(30)
    r_pt = HeapBuf(MAX_PTR_WIDTH)
    below = HeapBuf(MAX_PTR_WIDTH + 1)
    splitv = HeapBuf(N_SPLIT)
    chi = HeapBuf(MAX_PTR_WIDTH)
    q_point = HeapBuf(LINK_Q_VARS)
    eq_q = HeapBuf(2 ** (LINK_Q_VARS + 1) - 2)
    corners = HeapBuf(MAX_PTR_WIDTH + 1)  # entry h: prod_{h <= i < n} (1 + chi_i), a table of 2^h rows
    shifts = HeapBuf(LINK_MAX_SHIFT)
    z_vals = HeapBuf(2 * QKECCAK_VARS_CAP)
    kslices = HeapBuf(BASE_FIELD_BITS)
    ood_z = HeapBuf(MAX_STACK_LOG)
    ood_value = HeapBuf(1)

    # ---- seed (statement pre-bound: hinted sub pi + baked program digest) ----
    sp = StackBuf(KECCAK_STATE)
    keccak_cells([seed_0, seed_1, pi_0, pi_1], sp, final=0)
    # The stream, STREAM_CHUNK words a hint, as many chunks as it fills: the opening checks it read no further.
    stream_chunks = hint_witness("stream_chunks")
    assert log(stream_chunks) < STREAM_CAP // STREAM_CHUNK + 1
    stream = HeapBuf(stream_chunks ** STREAM_CHUNK)
    hint_stream(stream, stream_chunks)
    cursor = stream  # the proof stream, replayed word by word (advance = * g)

    # ---- announced layout and PCS rate (observed, then certified) ----
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
    g_log_mem = g_power_of_word(log_mem_word)
    assert log(g_log_mem) < MAX_LOG_MEM + 1  # native log_mem <= MAX_LOG_MEM
    assert log(g_log_mem / GEN ** MIN_LOG_MEM) < COUNT_BITS  # native MIN_LOG_MEM <= log_mem
    # Each table's log height h_t = max(log2_ceil(rows), floor), advice certified below.
    hint_witness(h_logs[0:N_TABLES], "table_logs")
    kappa_base = HeapBuf(N_TABLES + 2)
    kb = StackBuf(N_TABLES + 2)  # the same, in the frame
    kb[0] = 1
    kb[1] = g_log_mem
    for t in unroll(0, N_TABLES):
        kb[2 + t] = h_logs[GEN ** t]
    for i in unroll(0, N_TABLES + 2):
        kappa_base[GEN ** i] = kb[i]

    # ---- commitment root (2 words), kept for the opening phase ----
    if const((N_TABLES + 2) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    commit_root_0, cursor = fs_next(rate, (N_TABLES + 2) % 4, cursor)
    if const((N_TABLES + 3) % 4 == 0):
        sp = fs_perm(sp, rate, 4)
        rate = StackBuf(8)
    commit_root_1, cursor = fs_next(rate, (N_TABLES + 3) % 4, cursor)

    # ---- the shape: heights, cycles, rounds, pointer width ----
    # A table's height is the least power of two holding its rows, or its floor; the
    # cycles are the rows' sum; the pointer width w = max(bitlen(cycles), log_mem, kbc)
    # is at most MAX_PTR_WIDTH (link::Chunks). Then every log height is at most w too.
    g_cycles = GEN ** 0
    for t in unroll(0, N_TABLES):
        hh = kb[2 + t]
        assert log(hh) < N_ROW_LOGS
        rows = table_rows[GEN ** t]
        bits_t = rows_bits * GEN ** (ROW_BITS * t)
        g_rows, lead, rest = match(log(hh), range(0, N_ROW_LOGS), lambda h: table_size(rows, bits_t, h))
        if FLOORS[t] == 0:
            assert lead == 1
            assert rest != 0
        else:
            assert log(hh / GEN ** FLOORS[t]) < N_ROW_LOGS
            if hh != GEN ** FLOORS[t]:
                assert lead == 1
                assert rest != 0
        g_cycles *= g_rows
    hint_decompose_bits_exponent(cbits, g_cycles, MAX_PTR_WIDTH)
    rebuilt = GEN ** 0
    for k in unroll(0, MAX_PTR_WIDTH):
        b = cbits[GEN ** k]
        cbits[GEN ** k] = b * b
        rebuilt *= 1 + b * (1 + GEN ** (2 ** k))
    assert rebuilt == g_cycles
    # g^n_rows (the tallest height), g^w, whether w is the cycles' bit length, and g^p for
    # the p permutations that draw the link's packed challenges.
    hint_witness(shape[0:4], "link_shape")
    g_n = shape[GEN ** 0]
    g_w = shape[GEN ** 1]
    flag = shape[GEN ** 2]
    tallest = 1
    for t in unroll(0, N_TABLES):
        assert log(g_n / kb[2 + t]) < N_ROW_LOGS
        tallest = tallest * (g_n + kb[2 + t])
    assert tallest == 0
    assert log(g_w * INV_GEN ** BYTECODE_LOG) < LINK_W_ARMS
    assert log(g_w / g_log_mem) < N_ROW_LOGS
    assert_small_g_power(g_squares[g_w] * INV_GEN / g_cycles, g_squares)  # cycles < 2^w
    assert flag * flag == flag
    if flag == 1:
        assert_small_g_power(g_cycles / g_squares[g_w * INV_GEN], g_squares)  # 2^(w - 1) <= cycles
    else:
        assert (g_w + g_log_mem) * (g_w + GEN ** BYTECODE_LOG) == 0
    g_d = match(log(g_w * INV_GEN ** BYTECODE_LOG), range(0, LINK_W_ARMS), lambda k: chunk_d(k + BYTECODE_LOG))

    # ---- the stack: placement and its size ----
    gmv, offs, kaps = certify_stack(kappa_base, g_squares)
    size_sel = gmv * LIG_MIN_SHIFT_INV  # g^(m - MIN)
    assert log(size_sel) < LIG_N_LOG_SIZES

    # ---- the level-0 OOD sample (verifier read_ood) ----
    sp, z_first, cursor = fs_grind_squeeze(sp, rate, (N_TABLES + 3) % 4 + 1, cursor, tabs, OOD_GRIND_BITS)
    fs0, fs1, fs2, fs3, fs4 = match(log(size_sel), range(0, LIG_N_LOG_SIZES), lambda s: squeeze_point_from(sp[8], sp[9], sp[10], sp[11], sp[12], z_first, ood_z, LIG_MIN_LOG_SIZE + s))
    # The link's grind nonce joins the value: its permutation draws theta_0.
    theta0, pow_word, fs0, fs1, fs2, fs3, fs4, cursor = opening_message(fs0, fs1, fs2, fs3, fs4, cursor, ood_value, 1, 1)
    grind_check(pow_word, tabs, LINK_GRIND_BITS)

    # ---- the link's challenges ----
    # The grind's permutation drew theta_0; the rest come eight to a permutation of the
    # capacity alone, the fixed-count ones first. The hinted count p is the one with
    # 8 p - 8 < count <= 8 p.
    g_p = shape[GEN ** 3]
    over = g_p ** 8 / (GEN ** LINK_FIXED * g_n * g_w * g_d)
    vanish = 1
    for j in unroll(0, 8):
        vanish = vanish * (over + GEN ** j)
    assert vanish == 0
    chal[GEN ** 0] = theta0
    fs0, fs1, fs2, fs3, fs4 = squeeze_packed(fs0, fs1, fs2, fs3, fs4, chal * GEN, g_p)
    theta = chal
    gam = theta * GEN ** N_TABLES
    gs0 = gam[GEN ** 0]
    gs1 = gam[GEN ** 1]
    # On the address, the word and the presence; a word lo + Y hi takes gm1 Y on its high limb.
    gm0 = gam[GEN ** 2]
    gm1 = gam[GEN ** 3]
    gm3 = gam[GEN ** 4]
    mu = gam * GEN ** 5
    alpha = mu * GEN ** N_ACCESSES
    etas = alpha * GEN ** LOG2_BYTECODE_COLS
    eta_mem = etas[GEN ** 0]
    eta_bc = etas[GEN ** 1]
    # The mirror certificates' coefficients: pointer column q's chunk c takes eps_q nu_c.
    eps = etas * GEN ** 2
    tau = eps * GEN ** N_POINTERS
    zeta = tau * g_n
    nu = zeta * g_w
    eqtree(alpha, slot, LOG2_BYTECODE_COLS)
    slot = slot * GEN ** (2 ** LOG2_BYTECODE_COLS - 2)  # eq(alpha, .) over the 16 tuple slots

    # ---- the index side ----
    # The state identity: sum_j eq(zeta, j) A(j) + eq(zeta, j + 1) B(j) = eq(zeta, 0) s_init + eq(zeta, cycles) s_fin,
    # a state s being 1 + gs0 pc + gs1 fp.
    e0, ec = match(log(g_w * INV_GEN ** BYTECODE_LOG), range(0, LINK_W_ARMS), lambda k: state_ends(zeta, cbits, k + BYTECODE_LOG))
    claim = e0 * (1 + gs0 + gs1) + ec * (1 + gs0 * GEN ** (2 ** BYTECODE_LOG - 1) + gs1)
    fs0, fs1, fs2, fs3, fs4, cursor, claim = link_rounds(fs0, fs1, fs2, fs3, fs4, cursor, claim, r_pt, g_w, tabs, 1, 0)
    # The memory term at r, then the five fresh coefficients from the one permutation taking it.
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)
    rate = StackBuf(8)
    m1, cursor = fs_next(rate, 0, cursor)
    sp = fs_perm(sp, rate, 1)
    cert = sp[0]
    jump_0 = sp[1]
    jump_1 = sp[2]
    jump_2 = sp[3]
    jump_3 = sp[4]
    idx, eqzr, shz = match(log(g_w * INV_GEN ** BYTECODE_LOG), range(0, LINK_W_ARMS), lambda k: index_side(r_pt, zeta, below, k + BYTECODE_LOG))
    eq0_r = below[GEN ** 0]
    below_mem = below[g_log_mem]
    below_bc = below[GEN ** BYTECODE_LOG]
    # The split program at r[..kbc]: advice, the claim this proof raises. The program side
    # weighs it into X_omega (on the rows' weight) and P_fp (on omega fp).
    hint_witness(splitv[0:N_SPLIT], "split_values")
    em_g0 = eta_mem * gm0
    em_g1 = eta_mem * gm1
    program = 0
    frame_program = 0
    for i in unroll(0, N_SPLIT_TERMS):
        if const(PW_KIND[i] == 0):
            pw_f = eta_bc * slot[GEN ** PW_ARG[i]]
        elif const(PW_KIND[i] == 1):
            pw_f = em_g0 * mu[GEN ** PW_ARG[i]]
        else:
            pw_f = em_g1 * mu[GEN ** PW_ARG[i]]
        pw_t = PW_COEF[i] * pw_f * splitv[GEN ** PW_COL[i]]
        if const(PW_FRAME[i] == 0):
            program = program + pw_t
        else:
            frame_program = frame_program + pw_t
    y_mem = gm0 * idx + gm3 * below_mem + gm1 * m1
    x_bc = eta_bc * slot[GEN ** 1] * idx + below_bc * (eta_bc * slot[GEN ** 2] + program)
    p_fp = below_bc * frame_program

    # ---- the row side ----
    assert log(g_d * INV_GEN ** LINK_D_MIN) < LINK_D_ARMS
    fs0, fs1, fs2, fs3, fs4, cursor, claim = match(log(g_d * INV_GEN ** LINK_D_MIN), range(0, LINK_D_ARMS), lambda k: link_row_side(sp[8], sp[9], sp[10], sp[11], sp[12], cursor, claim, chi, q_point, g_n, tabs, k + LINK_D_MIN))
    eqtree(q_point, eq_q, LINK_Q_VARS)
    assert log(g_n) < EQ_CHAIN_ARMS
    done = match(log(g_n), range(0, EQ_CHAIN_ARMS), lambda n: one_plus_suffixes(corners, chi, n))
    # The tables' sent columns, then the pointer words' 64 bit-slices; rm follows.
    # One message, read where it lies in the stream, eight words a permutation.
    sent = cursor
    rm, fs0, fs1, fs2, fs3, fs4 = packed_message(fs0, fs1, fs2, fs3, fs4, sent, LINK_N_SENT + BASE_FIELD_BITS)
    cursor = cursor * GEN ** (LINK_N_SENT + BASE_FIELD_BITS)

    # ---- the summand at the end point ----
    coef = 0
    base = 0
    cert_w = 0
    fq = StackBuf(N_POINTERS)  # eq(q_point, q) * corner * omega, per pointer
    acc_gm = StackBuf(N_ACCESSES)  # mu * gate, per access
    for t in unroll(0, N_TABLES):
        hh = kb[2 + t]
        bits_t = rows_bits * GEN ** (ROW_BITS * t)
        th = theta[GEN ** t]
        omega, act, eq_tau = match(log(hh), range(0, N_ROW_LOGS), lambda h: table_point(th, tau, chi, bits_t, h))
        corner = corners[hh]
        pc_t = sent[GEN ** STATE_PC[t]]
        fp_t = sent[GEN ** STATE_FP[t]]
        nx0 = link_form(sent, STATE_NEXT0[t])
        nx1 = link_form(sent, STATE_NEXT1[t])
        # The cycle pointer's weight: its row's state and successor under eq(zeta, r) and its shift.
        s_weight = eqzr * (1 + gs0 * pc_t + gs1 * fp_t) + shz * (1 + gs0 * nx0 + gs1 * nx1)
        r_bc = slot[GEN ** 1] * sent[GEN ** STATE_PC[t]] + slot[GEN ** 2] + slot[GEN ** 3] * GEN ** t
        for i in unroll(0, BC_OP_START[t + 1] - BC_OP_START[t]):
            r_bc = r_bc + slot[GEN ** BC_OP_SLOT[BC_OP_START[t] + i]] * link_form(sent, BC_OP_FORM[BC_OP_START[t] + i])
        memory = 0
        for a in unroll(ACC_START[t], ACC_START[t + 1]):
            if const(ACC_GATE[a] == LINK_NO_POS):
                gm_a = mu[GEN ** a]
            else:
                gm_a = mu[GEN ** a] * sent[GEN ** ACC_GATE[a]]
            acc_gm[a] = gm_a
            access = gm0 * link_form(sent, ACC_ADDR[a]) + gm3 + gm1 * link_form(sent, ACC_VALUE[a])
            memory = memory + gm_a * access
        table_base = omega * eq0_r * (eta_mem * memory + eta_bc * r_bc)
        if const(t == LINK_JUMP_TABLE):
            cnd = sent[GEN ** JUMP_IDS[0]]
            inv = sent[GEN ** JUMP_IDS[1]]
            flg = sent[GEN ** JUMP_IDS[2]]
            dst = sent[GEN ** JUMP_IDS[3]]
            frm = sent[GEN ** JUMP_IDS[4]]
            ids = jump_0 * (flg + cnd * inv) + jump_1 * cnd * (flg + 1)
            # The successor: b (v_pc, v_fp) + (b + 1) (g pc, fp).
            gpc = GEN * pc_t
            ids = ids + jump_2 * (nx0 + gpc + flg * (dst + gpc)) + jump_3 * (nx1 + fp_t + flg * (frm + fp_t))
            table_base = table_base + eq_tau * ids
        base = base + corner * table_base
        for q in unroll(PTR_START[t], PTR_START[t + 1]):
            e = eq_q[GEN ** (EQ_Q_AT + q)] * corner
            eo = e * omega
            fq[q] = eo
            cert_w = cert_w + eo * eps[GEN ** q]
            if const(q == PTR_START[t]):
                coef = coef + e * act * s_weight
            elif const(q == PTR_START[t] + 1):
                coef = coef + eo * (x_bc + sent[GEN ** STATE_FP[t]] * p_fp)
    ey = eta_mem * y_mem
    # The word reads weigh word(r) = m1 at their pointer.
    wm = em_g1 * m1
    for w in unroll(0, N_WORD_READS):
        coef = coef + fq[WR_PTR[w]] * mu[GEN ** WR_ACC[w]] * link_form(sent, WR_SCALE[w]) * wm
    for a in unroll(0, N_ACCESSES):
        if const(ACC_SHIFT[a] == 0):
            coef = coef + fq[ACC_PTR[a]] * acc_gm[a] * ey
    for s in unroll(0, LINK_MAX_SHIFT):
        sh = 0
        for a in unroll(0, N_ACCESSES):
            if const(ACC_SHIFT[a] == s + 1):
                sh = sh + fq[ACC_PTR[a]] * acc_gm[a] * ey
        shifts[GEN ** s] = sh
    rest = eq_q[GEN ** EQ_Q_AT] * base
    done = match(log(g_w * INV_GEN ** BYTECODE_LOG), range(0, LINK_W_ARMS), lambda k: link_terminal(r_pt, sent, coef, shifts, cert_w * cert, nu, rest, claim, k + BYTECODE_LOG))

    # ---- public-input binding: each memory limb's line through the public words ----
    lo_0, hi_0 = split_limbs(pi_0)
    lo_1, hi_1 = split_limbs(pi_1)
    pi_m0 = lo_0 + rm * (lo_0 + lo_1)
    pi_m1 = hi_0 + rm * (hi_0 + hi_1)

    # ---- KECCAK validity, by GKR over the rounds ----
    h5 = kb[2 + TABLE_KECCAK]
    fs0, fs1, fs2, fs3, fs4, cursor, keccak_word = verify_keccak(fs0, fs1, fs2, fs3, fs4, cursor, h5, chi, sent * GEN ** SENT_OUT_LANES, z_vals, kslices, tabs)
    sp = fs_cap(fs0, fs1, fs2, fs3, fs4)

    # ---- stacked opening: ring switch, then the claims' batch ----
    # One grind covers the map's challenges, rho and the batching challenge lam, one
    # packed draw: the grind's permutation gives seven, every cell but the proof of
    # work's, then two of the capacity alone eight and three.
    rate = StackBuf(8)
    ch = StackBuf(2 * RING_MAP_WIDTH)  # f_0 .. f_7, then g_0 .. g_7
    sp, map_first, cursor = fs_grind_squeeze(sp, rate, 0, cursor, tabs, BATCH_GRIND_BITS)
    ch[0] = map_first
    for i in unroll(1, 7):
        ch[i] = sp[i + 1]
    sp = fs_perm(sp, rate, 0)
    for i in unroll(0, 8):
        ch[7 + i] = sp[i]
    sp = fs_perm(sp, rate, 0)
    ch[15] = sp[0]
    rho = sp[1]
    lam = sp[2]
    map_challenges = HeapBuf(2 * RING_MAP_WIDTH)
    for i in unroll(0, 2 * RING_MAP_WIDTH):
        map_challenges[GEN ** i] = ch[i]
    # The same map as a Frobenius sum, for the transparent weights: c_(8p+b) = f_p g_b^(2^(8p)).
    c_table = HeapBuf(BASE_FIELD_BITS)
    for b in unroll(0, RING_MAP_WIDTH):
        power = ch[RING_MAP_WIDTH + b]
        for p in unroll(0, RING_MAP_WIDTH):
            c_table[GEN ** (RING_MAP_WIDTH * p + b)] = ch[p] * power
            if const(p + 1 != RING_MAP_WIDTH):
                for t in unroll(0, RING_MAP_WIDTH):
                    power = power * power
    # The two ring claims as one, the pointer columns' as rho times theirs: rho scales
    # inside the map, so their slices take it, and so do their columns' scales
    # (check_stack_terminal).
    merged = HeapBuf(BASE_FIELD_BITS)
    link_slices = sent * GEN ** LINK_N_SENT
    for i in unroll(0, BASE_FIELD_BITS):
        merged[GEN ** i] = kslices[GEN ** i] + rho * link_slices[GEN ** i]
    target = ring_switch_target(merged, map_challenges)
    # The claims after the ring claim by Horner in lam, from the last: the OOD value, the
    # Keccak word, the public input's two, the sent values, the memory word m1.
    acc = ood_value[GEN ** 0]
    acc = acc * lam + keccak_word
    acc = acc * lam + pi_m1
    acc = acc * lam + pi_m0
    for jj in unroll(0, LINK_N_SENT):
        j = LINK_N_SENT - 1 - jj
        if const(SENT_TARGET[j] != LINK_NO_POS):
            acc = acc * lam + sent[GEN ** j]
    acc = acc * lam + m1
    target = target + acc * lam
    sumcheck_target, point, point1, inner_total, yr_at_tail, cursor = match(log(size_sel), range(0, LIG_N_LOG_SIZES), lambda m_idx: open_stacked(m_idx, rate_sel, sp[8], sp[9], sp[10], sp[11], sp[12], target, commit_root_0, commit_root_1, cursor, tabs))
    # Every word the proof was read from lies in the hinted chunks. The shape fixes that
    # prefix, every word of it transcript-bound; the words past it are outside the
    # verified proof and unconstrained.
    assert log(cursor / stream) < log(stream_chunks ** STREAM_CHUNK * GEN)

    check_stack_terminal(g_squares, kappa_base, offs, kaps, gmv, chi, g_n, r_pt, g_log_mem, rm, z_vals, eq_q, c_table, rho, lam, below_mem, Y_TOWER * below_mem, point, point1, inner_total, yr_at_tail, sumcheck_target, ood_z)

    # ---- export this sub-proof's claim: the split program at r[..kbc] ----
    for k in unroll(0, BYTECODE_LOG):
        defer_out[GEN ** k] = r_pt[GEN ** k]
    for j in unroll(0, N_SPLIT):
        defer_out[GEN ** (BYTECODE_LOG + j)] = splitv[GEN ** j]
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
    assert_gpow(bigs)
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
        d0, d1 = claim_list_chain(entries_ptr, n_g, bigs, groups, rest)
        digest[0] = d0
        digest[1] = d1
    # n_g a g-power below the memory size: the bound of the claims' cells written above. claim_list_chain checks it
    # too, for its own contract; this one bounds this function's, which the core route checks on its body alone.
    assert_gpow(n_g)
    return digest[0], digest[1]


def claim_list_chain(entries_ptr, n_g, bigs, groups, rest):
    # A non-empty list's hash, in a function of its own so that its buffer precedes its first call.
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
    d0, d1 = claim_list_tail(last, mid_entries * groups ** (4 * CLAIM_GROUP), rest)
    # list_split's split checked again here, where the claims' cells are written: bigs, groups and
    # rest g-powers below the memory size, and its identity, so those cells tile [0, n).
    assert_gpow(bigs)
    assert_gpow(groups)
    assert_gpow(rest)
    assert bigs ** CLAIM_BIG * groups ** CLAIM_GROUP * rest == n_g
    # n_g a g-power below the memory size: the bound of the claims' cells written above.
    assert_gpow(n_g)
    return d0, d1


def claim_list_tail(state, blk, rest):
    # The last block's hash: the dispatch on the rest, at the top of a body.
    d0, d1 = match(log(rest), range(0, CLAIM_GROUP), lambda k: claim_list_last(state, blk, k))
    return d0, d1


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
    # list_split's bounds on bigs and groups, checked again here, where their exponents are formed.
    assert_gpow(bigs)
    assert_gpow(groups)
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
    # e_j in [0, 2^h): its first offset is at least zero, and the count of claims, a
    # memory address (`assert_gpow`, below 2^30), keeps the sum below 2^60, short
    # of wrapping, so bounding its last offset below the region's size
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
    # list_split's bounds on bigs and groups, checked again here, where their exponents are formed.
    assert_gpow(bigs)
    assert_gpow(groups)
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


def da_verify(byte_bits):
    # Returns the commitment H(tree root, n), two cells, and the membership challenge, one.
    # The matrix always has DA_MAX_ROWS rows: a padding row's root is a constant, which
    # the gap loop writes without hashing anything.
    n_blob_g = hint_witness("da_n_blobs")
    gap_g = da_padding(n_blob_g)

    # The challenge, hashed below as its two lanes and two zero ones.
    z = hint_witness("da_challenge")
    zs, top_leaves, cell_factors, offsets = da_vector(z)

    weights = da_weights(top_leaves, cell_factors, zs, offsets)

    roots = HeapBuf(GEN ** (4 * DA_MAX_ROWS))
    for xi in mul_range(1, n_blob_g):
        b0, b1 = da_verify_blob(weights)
        slot = roots * (xi ** 2)
        slot[1] = b0
        slot[GEN] = b1
    da_pad(roots, n_blob_g, gap_g)
    r0, r1 = da_levels(roots, DA_MAX_ROWS, DA_LOG_MAX_ROWS)
    commitment = StackBuf(2)
    keccak([r0, r1], [byte_bits[n_blob_g], 0], commitment)
    return commitment[0], commitment[1], z


def da_weights(top_leaves, cell_factors, zs, offsets):
    # Column h's weights, once for every blob: the tree inside a cell expanded from the
    # column's leaf of the tree above, its factors shifted by the column's offsets. Unrolled,
    # so each pointer is into a callee's frame placed by this function.
    weights = HeapBuf(DA_CELLS)
    for h in unroll(0, DA_CELLS):
        weights[GEN ** h] = da_expand(top_leaves[GEN ** h], cell_factors, zs, offsets * GEN ** (LOG_CELL_SYMBOLS * h), LOG_CELL_SYMBOLS - 1, LOG_CELL_SYMBOLS)
    return weights


def da_pad(roots, n_blob_g, gap_g):
    # The padding rows' roots, past the n blobs' own.
    for xd in mul_range(1, gap_g):
        pad = roots * (n_blob_g ** 2) * (xd ** 2)
        pad[1] = DA_PAD_BLOB_0
        pad[GEN] = DA_PAD_BLOB_1
    return


def da_padding(n_blob_g):
    # g^(DA_MAX_ROWS - n) padding rows, for n_blob_g = g^n with 1 <= n <= DA_MAX_ROWS.
    assert n_blob_g != 1
    assert log(n_blob_g) < DA_MAX_ROWS + 1
    return GEN ** DA_MAX_ROWS / n_blob_g


def da_verify_blob(weights):
    # One blob, cell by cell: cell log(xb)'s digest is leaf log(xb) of the blob's tree, and
    # its inner product with the column's weights joins the running sum. Returns the blob's
    # root. Its region: its tree, then its running sum, a fresh write-once cell per column.
    base = HeapBuf(DA_REGION)
    base[GEN ** DA_SUM] = 0
    for xb in mul_range(1, GEN ** DA_CELLS):
        d0, d1, s = da_verify_cell(weights[xb])
        chain = base * xb
        chain[GEN ** (DA_SUM + 1)] = chain[GEN ** DA_SUM] + s
        leaf = base * (xb * xb)
        leaf[1] = d0
        leaf[GEN] = d1
    assert base[GEN ** (DA_SUM + DA_CELLS)] == 0
    b0, b1 = da_levels(base, DA_CELLS, DA_BLOCK_BITS)
    return b0, b1


def da_verify_cell(lvals):
    # A symbol is a word of E, so the hash and the inner product read the hinted cell as is.
    sym = StackBuf(DA_CELL)
    hint_witness(sym, "da_symbols")
    s = 0
    for e in unroll(0, DA_CELL):
        s = s + lvals[GEN ** e] * sym[e]
    st = StackBuf(2)
    keccak_cells(sym, st)
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
    # L(x) = prod_(j < LOG_BLOB_SYMBOLS) (1 + z_j Vhat_j(x)), z_j = z^(2^j), as a binary tree over
    # x's bits from the top down: factor j depends only on the bits from j up, so a node
    # is its parent times one factor. The tree over the cell index runs once; each column
    # expands the tree inside a cell from its leaf, its factors shifted by the cell
    # index's part of each Vhat_j (da_column_offsets).
    zs = HeapBuf(DA_LOG_M)
    zj = z
    for j in unroll(0, LOG_BLOB_SYMBOLS):
        zs[GEN ** j] = zj
        zj = zj * zj
    zs[GEN ** LOG_BLOB_SYMBOLS] = 0  # the top bit splits without a factor: the degree bound
    above_top = HeapBuf(DA_LOG_M)  # nothing sits above the tree over the cell index
    for j in unroll(LOG_CELL_SYMBOLS, DA_LOG_M):
        above_top[GEN ** j] = 0
    top_factors = da_factors(zs, LOG_BLOB_SYMBOLS, DA_BLOCK_BITS, 0)
    top_leaves = da_expand(1, top_factors, zs, above_top, LOG_BLOB_SYMBOLS, DA_BLOCK_BITS)
    cell_factors = da_factors(zs, LOG_CELL_SYMBOLS - 1, LOG_CELL_SYMBOLS, DA_CELLS)
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
    # offsets[LOG_CELL_SYMBOLS * h + j] = z_j Vhat_j at the cell index h's bits, for each factor
    # j inside a cell: zero at h = 0, then one doubling per bit of h.
    offsets = HeapBuf(LOG_CELL_SYMBOLS * DA_CELLS)
    for j in unroll(0, LOG_CELL_SYMBOLS):
        offsets[GEN ** j] = 0
    for b in unroll(0, DA_BLOCK_BITS):
        steps = HeapBuf(LOG_CELL_SYMBOLS)
        for j in unroll(0, LOG_CELL_SYMBOLS):
            steps[GEN ** j] = zs[GEN ** j] * DA_VHAT_COLUMN[LOG_CELL_SYMBOLS * b + j]
        for xh in mul_range(1, GEN ** (2 ** b)):
            src = offsets * xh ** LOG_CELL_SYMBOLS
            dst = src * GEN ** (LOG_CELL_SYMBOLS * 2 ** b)
            for j in unroll(0, LOG_CELL_SYMBOLS):
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
    assert_gpow(n_lx_g)
    assert_gpow(n_xdup_g)
    assert_gpow(n_raw_x_g)
    assert_gpow(n_lean_sphincs_g)
    assert_gpow(n_sdup_g)
    assert_gpow(n_raw_s_g)
    assert log(n_children_g) < MAX_RECURSIONS + 1
    assert log(n_direct_da_g) < 2
    lx_slots_g = n_lx_g * n_xdup_g
    lean_sphincs_slots_g = n_lean_sphincs_g * n_sdup_g
    # The sum of both regions bounds the coverage indices, so it is what has to be a
    # memory address: its log is then below 2^30 and the runtime bounds below mean
    # what they say. An honest node holds its coverage table in memory, so it fits.
    n_total_g = lx_slots_g * lean_sphincs_slots_g
    assert_gpow(n_total_g)

    # The proving environment (the proof system's version and this bytecode) as one
    # digest. It rides the statement rather than the bytecode, so nothing here has to
    # know its own hash; the outer verifier pins it, and every child statement rebuilt
    # below copies it, which is what keeps a whole tree on one bytecode.
    fs_seed = StackBuf(2)
    hint_witness(fs_seed, "fs_seed")
    seed_0 = fs_seed[0]
    seed_1 = fs_seed[1]

    # Every HeapBuf's size is computed before the first call (zkDSL.md, where a buffer is reserved).
    lx_table_size = lx_slots_g ** 4
    lean_sphincs_table_size = lean_sphincs_slots_g ** 4
    da_digests_size = (n_children_g * GEN) ** 2
    child_pi_size = n_children_g * n_children_g
    child_fresh_size = n_children_g ** DEFER_SIZE
    child_carried_size = n_children_g ** DEFER_STMT_CELLS
    written_size = n_children_g * GEN

    # ---- the claim lists ----
    g_squares = exponent_tables()

    # One table per scheme: its declared list (strictly sorted, checked by the outer
    # verifier, which holds it) followed by its own duplicate slots. The coverage
    # indices below run over one space: leanXMSS, then leanSPHINCS.
    #
    # Each list's digest is a plain hash of its claims, 64 bytes a claim, its padding
    # binding its length; the statement carries the two digests side by side.
    lx_table = HeapBuf(lx_table_size)
    lean_sphincs_table = HeapBuf(lean_sphincs_table_size)
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
    # byte_bits[g^v] = v, read at a hinted byte's exponent (sp_from_bytes, da_verify).
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
        # The runtime bound is small by `assert_gpow(n_total_g)` above (its log below
        # the memory size). Without it this degenerates to what DEREF alone gives and an
        # index could reach past `cover`, which is the whole bijection. The bound is the
        # leanXMSS region, so a raw leanXMSS signature covers no leanSPHINCS claim.
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
    da_digests = HeapBuf(da_digests_size)
    own_da = da_digests * n_children_g ** 2
    if n_direct_da_g == GEN:
        root_0, root_1, z = da_verify(byte_bits)
        keccak([root_0, root_1], [z, 0], own_da[0:2])
    else:
        own_da[1] = 0
        own_da[GEN] = 0

    # ---- children ----
    child_pi = HeapBuf(child_pi_size)
    child_fresh = HeapBuf(child_fresh_size)
    child_carried = HeapBuf(child_carried_size)
    written = HeapBuf(written_size)  # loop-carried write count, one per child
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
        assert_gpow(nsub_x_g)
        assert_gpow(nsub_s_g)
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
    assert GEN[1] == own_1
    return


def aggregate_claims(n_children_g, child_pi, child_fresh, child_carried, defer_stmt, tabs):
    # Every child contributes two claims on the split program: the one IT
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
    # The column challenges fold each fresh claim's values into one at (r, col).
    col = HeapBuf(SPLIT_LOG)
    no_rate = StackBuf(8)
    for k in unroll(0, SPLIT_LOG):
        st, col_k = squeeze(st, no_rate, 0)
        col[GEN ** k] = col_k
    eq_col_tree = HeapBuf(2 ** (SPLIT_LOG + 1) - 2)
    eqtree(col, eq_col_tree, SPLIT_LOG)
    eq_col = eq_col_tree * GEN ** (2 ** SPLIT_LOG - 2)
    fresh_val = HeapBuf(n_children_g)
    for xc in mul_range(1, n_children_g):
        fresh = fresh_row[xc]
        fv = 0
        for j in unroll(0, N_SPLIT):
            fv = fv + eq_col[GEN ** j] * fresh[GEN ** (BYTECODE_LOG + j)]
        fresh_val[xc] = fv
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
        nxt[GEN ** 1] = row[GEN ** 1] + lam_pow * (fresh_val[xc] + lam * carried[GEN ** DEFER_STMT_BC_VALUE])
    bc_end = bc_chain * n_children_g ** PAIR_SLOTS
    bc_running = bc_end[GEN ** 1]
    bc_point = HeapBuf(BYTECODE_VARS)
    fs0, fs1, fs2, fs3, fs4, bc_running = batch_sumcheck(st[8], st[9], st[10], st[11], st[12], bc_msgs * GEN ** BC_LAM_WORDS, bc_running, bc_point, tabs, BYTECODE_VARS)
    bc_point1 = HeapBuf(BYTECODE_VARS)  # 1 + bc_point, so an eq factor is one XOR
    for k in unroll(0, BYTECODE_VARS):
        bc_point1[GEN ** k] = 1 + bc_point[GEN ** k]
    # A fresh claim's point is (r, col): its column factor is common to every child.
    for k in unroll(0, SPLIT_LOG):
        if const(k == 0):
            eq_cols = col[GEN ** k] + bc_point1[GEN ** (BYTECODE_LOG + k)]
        else:
            eq_cols *= col[GEN ** k] + bc_point1[GEN ** (BYTECODE_LOG + k)]
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
            elif const(k // BYTECODE_LOG == 0):
                eq_fresh *= fresh[GEN ** k] + rk1
                eq_carried *= carried[GEN ** k] + rk1
            else:
                eq_carried *= carried[GEN ** k] + rk1
        row = bc_chain * xc ** PAIR_SLOTS
        bc_wsum[xc * GEN] = bc_wsum[xc] + row[GEN ** 0] * (eq_fresh * eq_cols + lam * eq_carried)
    assert bc_running == bytecode_star * bc_wsum[n_children_g]

    for k in unroll(0, BYTECODE_VARS):
        defer_stmt[GEN ** k] = bc_point[GEN ** k]
    defer_stmt[GEN ** DEFER_STMT_BC_VALUE] = bytecode_star
    return
