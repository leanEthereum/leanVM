from __future__ import annotations
import math
from dataclasses import dataclass
from enum import IntEnum
from pathlib import Path
from typing import Sequence
from primitives import *


PUBLIC_INPUT_SIZE = DIGEST_ELEMS
SNARK_DOMAIN_SEP = [Fp(v) for v in (130704175, 1303721200, 493664240, 1035493700, 2063844858, 1410214009, 1938905908, 1696767928)]  # fmt: skip

WHIR_INITIAL_FOLDING_FACTOR, WHIR_SUBSEQUENT_FOLDING_FACTOR, WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS = 7, 5, 8
MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE, RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 1, 4, 5
_WHIR_CONFIGS = WHIR_CONFIGS = [(1,7,1,10,220,16,[]), (1,8,1,11,220,16,[]), (1,9,1,12,220,16,[]), (1,10,1,13,220,16,[]), (1,11,1,14,220,16,[]), (1,12,1,15,220,16,[]), (1,13,1,16,220,16,[]), (1,14,1,15,221,16,[]), (1,15,1,16,221,16,[]), (1,16,1,11,73,16,[(222,1,16,16), ]), (1,17,1,12,73,16,[(223,1,16,16), ]), (1,18,1,13,73,16,[(224,1,16,16), ]), (1,19,1,14,73,16,[(225,1,16,16), ]), (1,20,1,15,73,16,[(227,1,16,16), ]), (1,21,2,9,32,16,[(229,1,16,16), (73,1,16,16)]), (1,22,2,10,32,16,[(230,1,16,16), (74,1,16,12)]), (1,23,2,11,32,16,[(234,1,16,16), (74,1,16,13)]), (1,24,2,12,32,16,[(235,1,16,16), (74,1,16,14)]), (1,25,2,13,32,16,[(241,2,16,16), (74,2,16,15)]), (1,26,2,14,21,14,[(243,2,16,16), (74,2,16,16), (32,2,16,14)]), (1,27,2,15,21,14,[(248,2,16,16), (75,2,16,15), (32,2,16,15)]), (1,28,2,16,21,14,[(256,2,16,16), (75,2,16,16), (32,2,16,16)]), (1,29,2,17,21,14,[(262,2,16,16), (76,2,16,15), (33,2,16,12)]), (1,30,2,18,21,14,[(270,2,16,16), (76,2,16,16), (33,2,16,13)]), (2,7,1,13,109,16,[]), (2,8,1,14,109,16,[]), (2,9,1,15,109,16,[]), (2,10,1,16,109,16,[]), (2,11,1,12,110,16,[]), (2,12,1,13,110,16,[]), (2,13,1,14,110,16,[]), (2,14,1,15,110,16,[]), (2,15,1,16,110,16,[]), (2,16,1,10,55,16,[(111,1,16,14), ]), (2,17,1,11,55,16,[(111,1,16,15), ]), (2,18,1,12,55,16,[(111,1,16,16), ]), (2,19,1,13,55,16,[(112,1,16,15), ]), (2,20,2,14,55,16,[(112,1,16,16), ]), (2,21,2,10,28,16,[(113,1,16,16), (55,1,16,15)]), (2,22,2,11,28,16,[(114,1,16,15), (55,1,16,16)]), (2,23,2,12,28,16,[(114,1,16,16), (56,1,16,13)]), (2,24,2,13,28,16,[(115,1,16,16), (56,2,16,14)]), (2,25,2,14,28,16,[(118,2,16,15), (56,2,16,15)]), (2,26,2,17,19,15,[(118,2,16,16), (56,2,16,16), (28,2,16,15)]), (2,27,2,18,19,15,[(119,2,16,16), (57,2,16,13), (28,2,16,16)]), (2,28,2,19,19,15,[(120,2,16,16), (57,2,16,14), (29,2,15,14)]), (2,29,2,20,19,15,[(123,2,16,16), (57,2,16,15), (29,2,15,15)]), (3,7,1,9,73,16,[]), (3,8,1,10,73,16,[]), (3,9,1,11,73,16,[]), (3,10,1,12,73,16,[]), (3,11,1,13,73,16,[]), (3,12,1,14,73,16,[]), (3,13,1,15,73,16,[]), (3,14,1,16,73,16,[]), (3,15,1,12,74,16,[]), (3,16,1,11,44,16,[(74,1,16,13), ]), (3,17,1,12,44,16,[(74,1,16,14), ]), (3,18,2,13,44,16,[(74,1,16,15), ]), (3,19,2,14,44,16,[(74,1,16,16), ]), (3,20,2,15,44,16,[(75,1,16,15), ]), (3,21,2,11,25,16,[(75,1,16,16), (44,1,16,16)]), (3,22,2,12,25,16,[(76,1,16,15), (45,1,16,11)]), (3,23,2,13,25,16,[(76,1,16,16), (45,2,16,12)]), (3,24,2,14,25,16,[(77,2,16,16), (45,2,16,13)]), (3,25,2,15,25,16,[(78,2,15,16), (45,2,16,14)]), (3,26,2,19,18,12,[(79,2,15,16), (45,2,16,15), (25,2,16,16)]), (3,27,2,20,18,12,[(80,2,16,16), (45,2,16,16), (26,2,13,15)]), (3,28,2,21,18,12,[(82,2,15,15), (46,2,16,15), (26,2,13,16)]), (4,7,1,8,55,16,[]), (4,8,1,9,55,16,[]), (4,9,1,10,55,16,[]), (4,10,1,11,55,16,[]), (4,11,1,12,55,16,[]), (4,12,1,13,55,16,[]), (4,13,1,14,55,16,[]), (4,14,1,15,55,16,[]), (4,15,1,16,55,16,[]), (4,16,1,9,37,16,[(56,1,16,13), ]), (4,17,1,10,37,16,[(56,1,16,14), ]), (4,18,2,11,37,16,[(56,1,16,15), ]), (4,19,2,12,37,16,[(56,1,16,16), ]), (4,20,2,13,37,16,[(57,1,16,13), ]), (4,21,2,12,23,15,[(57,2,16,14), (37,2,16,14)]), (4,22,2,13,23,15,[(57,2,16,15), (37,2,16,15)]), (4,23,2,14,23,15,[(57,2,16,16), (37,2,16,16)]), (4,24,2,15,23,15,[(58,2,16,15), (38,2,16,13)]), (4,25,2,16,23,15,[(58,2,16,16), (38,2,16,14)]), (4,26,2,22,16,16,[(60,2,15,16), (38,2,16,15), (23,2,15,17)]), (4,27,2,23,16,16,[(61,2,16,15), (38,2,16,16), (23,2,15,18)])]  # fmt: skip
WHIR_CONFIGS = {
    (c[0], c[1]): {
        "log_inv_rate": c[0],
        "num_variables": c[1],
        "commitment_ood_samples": c[2],
        "rounds": [{"num_queries": r[0], "ood_samples": r[1], "query_pow_bits": r[2], "folding_pow_bits": r[3]} for r in c[6]]
        + [{"num_queries": c[4], "query_pow_bits": c[5], "folding_pow_bits": c[3]}],
    }
    for c in _WHIR_CONFIGS
}

MIN_LOG_MEMORY_SIZE, MAX_LOG_MEMORY_SIZE = 16, 26
MIN_LOG_HEIGHT_PER_TABLE, MIN_BYTECODE_LOG_SIZE, MAX_BYTECODE_LOG_SIZE = 8, 8, 22
N_VARS_TO_SEND_GKR_COEFFS = 5

N_RUNTIME_COLUMNS, N_INSTRUCTION_COLUMNS = 8, 12

LOGUP_MEMORY_DOMAINSEP, LOGUP_BYTECODE_DOMAINSEP = 1, 2
POSEIDON_DOMAINSEP_BASE = 3  # odd ≥ 3
POSEIDON_FLAG_PERMUTE_SHIFT, POSEIDON_FLAG_OUT8_SHIFT = 1 << 1, 1 << 2
POSEIDON_FLAG_LEFT_SHIFT, POSEIDON_OFFSET_LEFT_SHIFT = 1 << 3, 1 << 4
EXT_OP_FLAG_BE, EXT_OP_FLAG_ADD, EXT_OP_FLAG_DOT_PRODUCT, EXT_OP_FLAG_EQ, EXT_OP_LEN_MULTIPLIER = 4, 8, 16, 32, 64

STARTING_PC = 0  # every program starts at PC = 0, and ends at PC = len(bytecode) - 1


class BusDirection(IntEnum):
    PUSH = 1
    PULL = -1


@dataclass(frozen=True)
class BusInteraction:
    direction: BusDirection
    domain_sep: int = 0
    cols: tuple[str, ...] = ()  # committed columns forming σ (address column first, for memory)
    n_terms: int = 1  # number of logup terms (memory groups: consecutive cells sharing cols[0])


@dataclass(frozen=True)
class Table:
    name: str
    columns: tuple[str, ...]
    buses: tuple[BusInteraction, ...]
    air_degree: int
    n_constraints: int
    n_shift: int  # shift (next-row) columns are always the first ones
    max_log_height: int
    air_constraints_fn: object  # (constraint_evaluator, logup_beta_eq) -> None

    @property
    def n_columns(self) -> int:
        return len(self.columns)

    @property
    def n_bus_interactions(self) -> int:
        return sum(b.n_terms for b in self.buses)

    @property
    def precompile_bus_interaction_sign(self) -> EF:
        return EF(self.buses[0].direction)  # precompile interaction is the first, by convention

    def col(self, name: str) -> int:
        return self.columns.index(name)

    def eval_air(self, col_evals: Sequence[EF], alpha_powers: Sequence[EF], logup_beta_eq: list[EF]) -> EF:
        constraint_evaluator = ConstraintEvaluator(col_evals[: self.n_columns], col_evals[self.n_columns :], alpha_powers, self.columns)
        self.air_constraints_fn(constraint_evaluator, logup_beta_eq)
        return constraint_evaluator.accumulator

    def boundary_statements(self, stacked_n_vars: int, offset: int, log_height: int, ending_pc: int) -> list["SparseStatements"]:
        if self.name != "execution":
            return []
        pc_col_offset = offset + (self.col("pc") << log_height)
        return [
            SparseStatements(stacked_n_vars, [], [(pc_col_offset + idx, EF(pc))])
            for idx, pc in [(0, STARTING_PC), ((1 << log_height) - 1, ending_pc)]
        ]


# Overwrite-sponge
def sponge_hash(data: Sequence[Fp]) -> list[Fp]:
    assert len(data) % SPONGE_RATE == 0 and len(data) > 0
    capacity = [Fp(len(data))] + [Fp(0)] * (SPONGE_CAPACITY - 1)
    full = list(capacity) + [Fp(0)] * SPONGE_RATE
    for k in range(len(data) // SPONGE_RATE):
        chunk = data[k * SPONGE_RATE : (k + 1) * SPONGE_RATE]
        full = POSEIDON16.permute(list(capacity) + list(chunk))
        capacity = full[:SPONGE_CAPACITY]
    return full[SPONGE_CAPACITY:]


class DuplexSpongeChallenger:  # https://eprint.iacr.org/2025/536.pdf
    def __init__(self, initial_capacity: Sequence[Fp]) -> None:
        self.state: list[Fp] = list(initial_capacity) + [Fp(0)] * SPONGE_RATE
        self.rate_fresh: bool = False

    def observe(self, chunk: Sequence[Fp]) -> None:
        assert len(chunk) == SPONGE_RATE
        self.state = POSEIDON16.permute(self.state[:SPONGE_CAPACITY] + list(chunk))
        self.rate_fresh = True

    def observe_many(self, scalars: Sequence[Fp]) -> None:
        for i in range(0, len(scalars), SPONGE_RATE):
            chunk = list(scalars[i : i + SPONGE_RATE])
            chunk += [Fp(0)] * (SPONGE_RATE - len(chunk))
            self.observe(chunk)

    def duplex(self) -> None:
        self.observe([Fp(0)] * SPONGE_RATE)

    def _sample_rate(self) -> list[Fp]:
        assert self.rate_fresh, "stale rate: insert duplex() before sampling"  # unreachable
        self.rate_fresh = False
        return self.state[SPONGE_CAPACITY:]

    def _sample_many(self, n: int) -> list[Fp]:
        out: list[Fp] = []
        for i in range(n):
            if i:
                self.duplex()
            out.extend(self._sample_rate())
        return out

    def sample_many_ef(self, n: int) -> list[EF]:
        flat = self._sample_many(div_ceil(n * EF.DIMENSION, SPONGE_RATE))[: n * EF.DIMENSION]
        return embed_ef(flat)

    def sample_ef(self) -> EF:
        return self.sample_many_ef(1)[0]

    def sample_in_range(self, bits: int, n_samples: int) -> list[int]:
        assert bits < 31
        flat = self._sample_many(div_ceil(n_samples, SPONGE_RATE))[:n_samples]
        return [int(x.value) & ((1 << bits) - 1) for x in flat]


@dataclass
class MerkleOpening:
    leaf_data: list[Fp]
    path: list[list[Fp]]


@dataclass
class Proof:
    transcript: list[Fp]
    merkle_openings: list[MerkleOpening]


class FiatShamir(DuplexSpongeChallenger):
    def __init__(self, proof: Proof, initial_capacity: Sequence[Fp]) -> None:
        super().__init__(initial_capacity)
        self.transcript = list(proof.transcript)
        self.openings = list(reversed(proof.merkle_openings))
        self.offset = 0

    def _read_padded(self, n: int) -> list[Fp]:
        n_pad = next_multiple_of(n, SPONGE_RATE)
        assert self.offset + n_pad <= len(self.transcript), "Exceeded Transcript"
        chunk = self.transcript[self.offset : self.offset + n_pad]
        self.offset += n_pad
        assert all(int(chunk[i].value) == 0 for i in range(n, n_pad)), "InvalidTranscript: non-zero padding"
        self.observe_many(chunk)
        return chunk

    def observe_scalars(self, scalars: Sequence[Fp]) -> None:
        self.observe_many(list(scalars))

    def next_base_scalars(self, n: int) -> list[Fp]:
        return self._read_padded(n)[:n]

    def next_extension_scalars_vec(self, n: int) -> list[EF]:
        flat = self.next_base_scalars(n * EF.DIMENSION)
        return embed_ef(flat)

    def next_extension_scalar(self) -> EF:
        return self.next_extension_scalars_vec(1)[0]

    def next_merkle_opening(self) -> MerkleOpening:
        assert self.openings, "Exceeded Transcript: no more Merkle openings"
        return self.openings.pop()

    def check_pow_grinding(self, bits: int) -> None:
        if bits == 0:
            return
        self._read_padded(SPONGE_RATE)
        assert int(self.state[SPONGE_CAPACITY].value) & ((1 << bits) - 1) == 0, "Invalid Grinding Witness"


def merkle_verify_path(
    root: list[Fp],
    log_height: int,
    index: int,
    opened_values: Sequence[Fp],
    opening_proof: Sequence[list[Fp]],
) -> None:
    assert len(opening_proof) == log_height, "Merkle verification failed: opening proof has wrong length"
    chunks = [list(opened_values[i : i + SPONGE_RATE]) for i in range(0, len(opened_values), SPONGE_RATE)]
    current = sponge_hash([x for c in reversed(chunks) for x in c])
    for sibling in opening_proof:
        current = poseidon16_compress(current, sibling) if index & 1 == 0 else poseidon16_compress(sibling, current)
        index >>= 1
    assert root == current, "Merkle verification failed: root mismatch"


def expand_from_univariate(x: EF, num_variables: int) -> list[EF]:
    return list(accumulate(repeat(x, num_variables), lambda a, _: a * a))  # [x, x², x⁴, …, x^(2^(n−1))]


def eq_poly(a: Sequence[EF], b: Sequence[EF]) -> EF:
    assert len(a) == len(b)
    return math.prod(x * y + (ONE - x) * (ONE - y) for x, y in zip(a, b))


def eq_at_index(point: Sequence[EF], idx: int, n: int) -> EF:
    """eq(point, big-endian-bits(idx, n)). Specialization of eq_poly for boolean points."""
    return math.prod(point[j] if (idx >> (n - 1 - j)) & 1 else ONE - point[j] for j in range(n))


def dot_product(a: Sequence, b: Sequence):
    return sum(x * y for x, y in zip(a, b))


def next_mle(x: Sequence[EF], y: Sequence[EF]) -> EF:
    assert len(x) == len(y)
    s, eq_prefix = ZERO, ONE
    for xi, yi in zip(x, y):
        s = xi * (ONE - yi) * s + eq_prefix * (ONE - xi) * yi
        eq_prefix *= xi * yi + (ONE - xi) * (ONE - yi)
    return s + math.prod([*x, *y])


def eval_multilinear_by_evals(evals: Sequence[Fp | EF], point: Sequence[EF]) -> EF:
    """Evaluate a multilinear in evaluation form at `point`."""
    assert len(evals) == 1 << len(point)
    cur: Sequence = evals
    for r in reversed(point):
        cur = [cur[j] + (cur[j + 1] - cur[j]) * r for j in range(0, len(cur), 2)]
    return cur[0]


def eval_multilinear_by_coeffs(coeffs: Sequence[EF], point: Sequence[EF]) -> EF:
    """Evaluate a multilinear in coefficient form at `point`."""
    assert len(coeffs) == 1 << len(point)
    if not point:
        return coeffs[0]
    half = len(coeffs) // 2
    lo = eval_multilinear_by_coeffs(coeffs[:half], point[1:])
    hi = eval_multilinear_by_coeffs(coeffs[half:], point[1:])
    return lo + hi * point[0]


def eval_univariate_polynomial(coeffs: list[EF], x: EF) -> EF:
    acc = ZERO
    for c in reversed(coeffs):
        acc = acc * x + c
    return acc


def mle_of_01234567_etc(point: Sequence[EF]) -> EF:
    """evaluate the MLE of `f(i) = i` (big-endian) at `point`."""
    n = len(point)
    return sum(p * (1 << (n - 1 - i)) for i, p in enumerate(point))


def mle_of_zeros_then_ones(n_zeros: int, point: Sequence[EF]) -> EF:
    """evaluate the MLE of `[0]*n_zeros ++ [1]*(2^len(point) - n_zeros)` at `point`."""
    n_values = 1 << len(point)
    assert n_zeros <= n_values
    if n_zeros == 0:
        return ONE
    if n_zeros == n_values:
        return ZERO
    half, tail = n_values >> 1, point[1:]
    if n_zeros < half:
        return (ONE - point[0]) * mle_of_zeros_then_ones(n_zeros, tail) + point[0]
    return point[0] * mle_of_zeros_then_ones(n_zeros - half, tail)


def eval_eq(point: Sequence[EF]) -> list[EF]:
    out = [ONE]
    for p in point:
        out = [w for v in out for w in (v * (ONE - p), v * p)]
    return out


@dataclass
class SparseStatements:
    total_num_variables: int
    point: list[EF]  # low-bits variables (suffix), shared by every entry in `values`
    values: list[tuple[int, EF]]  # (selector_index, eval): poly(high bits = selector_index, low bits = point) == eval
    is_next: bool = False  # if set, the low-variable part uses the shifted "next-row" MLE instead of plain eq

    @property
    def selector_num_variables(self) -> int:
        return self.total_num_variables - len(self.point)  # count of high/selector bits that selector_index spans


def whir_folding_factor_at_round(round: int) -> int:
    return WHIR_INITIAL_FOLDING_FACTOR if round == 0 else WHIR_SUBSEQUENT_FOLDING_FACTOR


@dataclass
class WhirCommitment:
    num_variables: int
    root: list[Fp]
    ood_points: list[EF]
    ood_answers: list[EF]

    @classmethod
    def parse(cls, fs: "FiatShamir", num_variables: int, n_ood: int) -> "WhirCommitment":
        return cls(
            num_variables,
            fs.next_base_scalars(DIGEST_ELEMS),
            fs.sample_many_ef(n_ood),
            fs.next_extension_scalars_vec(n_ood),
        )

    def oods_constraints(self) -> list[SparseStatements]:
        return [
            SparseStatements(self.num_variables, expand_from_univariate(p, self.num_variables), [(0, ev)])
            for p, ev in zip(self.ood_points, self.ood_answers)
        ]


def verify_sumcheck(fiat_shamir: FiatShamir, target: EF, n_rounds: int, degree: int, pow_bits: int = 0) -> tuple[list[EF], EF]:
    point: list[EF] = []
    for _ in range(n_rounds):
        coeffs = fiat_shamir.next_extension_scalars_vec(degree + 1)
        s = coeffs[0] + sum(coeffs)  # s = h(0) + h(1)
        assert s == target, "Sumcheck identity failed: h(0) + h(1) != target"
        fiat_shamir.check_pow_grinding(pow_bits)
        challenge = fiat_shamir.sample_ef()
        point.append(challenge)
        target = eval_univariate_polynomial(coeffs, challenge)
    return point, target


def verify_whir(
    fiat_shamir: FiatShamir,
    cfg: dict,
    commitment: WhirCommitment,
    statements: list[SparseStatements],
):
    current_vars = cfg["num_variables"]
    num_vars_after_1_round = current_vars - WHIR_INITIAL_FOLDING_FACTOR
    assert num_vars_after_1_round >= WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS
    n_rounds = div_ceil(num_vars_after_1_round - WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS, WHIR_SUBSEQUENT_FOLDING_FACTOR)
    round_constraints: list[tuple[EF, list[SparseStatements]]] = []
    folding_challenges: list[EF] = []
    log_domain = current_vars + cfg["log_inv_rate"]
    target = ZERO
    constraints = commitment.oods_constraints() + statements
    for round in range(n_rounds + 1):
        round_params = cfg["rounds"][round]
        fold_pow_bits = round_params["folding_pow_bits"]
        folding_factor = whir_folding_factor_at_round(round)
        fiat_shamir.duplex()
        gamma = fiat_shamir.sample_ef()
        gamma_power = ONE
        for smt in constraints:
            for _, value in smt.values:
                target += gamma_power * value
                gamma_power *= gamma
        round_constraints.append((gamma, constraints))
        sc_point, target = verify_sumcheck(fiat_shamir, target, folding_factor, 2, fold_pow_bits)
        folding_challenges += sc_point
        current_vars -= folding_factor
        is_final = round == n_rounds
        if is_final:
            final_coeffs = fiat_shamir.next_extension_scalars_vec(1 << current_vars)
        else:
            new_commitment = WhirCommitment.parse(fiat_shamir, current_vars, round_params["ood_samples"])

        log_height = log_domain - folding_factor
        gen = Fp(KB_TWO_ADIC_GENERATORS[log_height])
        fiat_shamir.check_pow_grinding(round_params["query_pow_bits"])
        indices = fiat_shamir.sample_in_range(log_height, round_params["num_queries"])
        stir_constraints: list[SparseStatements] = []
        for idx in indices:
            op = fiat_shamir.next_merkle_opening()
            merkle_verify_path(commitment.root, log_height, idx, op.leaf_data, op.path)
            # Round 0 leaves are raw base-field elements; later rounds embed DIM Fp values per EF element.
            leaf = op.leaf_data if round == 0 else embed_ef(op.leaf_data)
            leaf_eval = eval_multilinear_by_evals(leaf, folding_challenges[-folding_factor:])
            point = expand_from_univariate(EF(pow(int(gen.value), idx, P)), current_vars)
            stir_constraints.append(SparseStatements(current_vars, point, [(0, leaf_eval)]))

        if is_final:
            final_stir_constraints = stir_constraints
            break
        constraints = new_commitment.oods_constraints() + stir_constraints
        log_domain -= RS_DOMAIN_INITIAL_REDUCTION_FACTOR if round == 0 else 1
        commitment = new_commitment
    for smt in final_stir_constraints:
        univ_eval = eval_univariate_polynomial(final_coeffs, smt.point[0])
        assert all(univ_eval == v[1] for v in smt.values), "Final STIR constraint mismatch"

    final_sc_point, final_sc_value = verify_sumcheck(fiat_shamir, target, current_vars, 2)
    folding_challenges += final_sc_point

    eval_weights = ZERO
    for round, (gamma, smts) in enumerate(round_constraints):
        if round > 0:
            folding_challenges = folding_challenges[whir_folding_factor_at_round(round - 1) :]
        gamma_power = ONE
        for smt in smts:
            point_suffix = folding_challenges[len(folding_challenges) - len(smt.point) :]  # dense part of the point
            eval_suffix = next_mle(smt.point, point_suffix) if smt.is_next else eq_poly(smt.point, point_suffix)
            sel_n = smt.selector_num_variables
            for v in smt.values:
                eval_prefix = eq_at_index(folding_challenges, v[0], sel_n)  # sparse part of the point
                eval_weights += eval_prefix * eval_suffix * gamma_power
                gamma_power *= gamma
    final_value = eval_multilinear_by_coeffs(final_coeffs, list(reversed(final_sc_point)))
    assert final_sc_value == eval_weights * final_value, "WHIR final sumcheck check failed"


def verify_gkr_quotient(fiat_shamir: FiatShamir, n_vars: int) -> tuple[EF, list[EF], EF, EF]:
    assert n_vars > N_VARS_TO_SEND_GKR_COEFFS

    nums = fiat_shamir.next_extension_scalars_vec(1 << N_VARS_TO_SEND_GKR_COEFFS)
    dens = fiat_shamir.next_extension_scalars_vec(1 << N_VARS_TO_SEND_GKR_COEFFS)
    quotient = sum(n * d.inv() for n, d in zip(nums, dens))

    point = fiat_shamir.sample_many_ef(N_VARS_TO_SEND_GKR_COEFFS)
    claim_num = eval_multilinear_by_evals(nums, point)
    claim_den = eval_multilinear_by_evals(dens, point)

    for layer_n_vars in range(N_VARS_TO_SEND_GKR_COEFFS, n_vars):
        fiat_shamir.duplex()
        alpha = fiat_shamir.sample_ef()
        sc_point, sc_value = verify_sumcheck(fiat_shamir, claim_num + alpha * claim_den, layer_n_vars, 3)
        sc_point = list(reversed(sc_point))
        nl, nr, dl, dr = fiat_shamir.next_extension_scalars_vec(4)
        assert sc_value == eq_poly(point, sc_point) * (alpha * dl * dr + nl * dr + nr * dl), "GKR step: postponed value mismatch"  # fmt: skip
        beta = fiat_shamir.sample_ef()
        one_minus = ONE - beta
        claim_num = one_minus * nl + beta * nr
        claim_den = one_minus * dl + beta * dr
        point = sc_point + [beta]

    return quotient, point, claim_num, claim_den


def finger_print(domainsep: Fp | EF, data: Sequence[EF], beta_eq: Sequence[EF]) -> EF:
    assert len(beta_eq) > len(data)
    return dot_product(beta_eq, data) + beta_eq[-1] * domainsep


def sort_tables_by_height(tables: Sequence[Table], heights: dict[str, int]) -> list[tuple[Table, int]]:
    """Descending by height, alphabetical on ties"""
    return sorted([(t, heights[t.name]) for t in tables], key=lambda x: (-x[1], x[0].name))


def verify_logup(
    fiat_shamir: FiatShamir,
    gamma: EF,  # quotient denominator challenge
    beta: list[EF],  # bus-tuple hashing seed
    beta_eq: list[EF],  # eq(beta, ·) evaluation table
    log_memory: int,
    bytecode_multilinear: list[int],
    tables: Sequence[Table],
    table_heights: dict[str, int],
) -> dict:
    log_instr = log2_ceil(N_INSTRUCTION_COLUMNS)
    log_bytecode = log2_strict(len(bytecode_multilinear)) - log_instr

    tables_sorted = sort_tables_by_height(tables, table_heights)
    tallest_h = tables_sorted[0][1]

    total_active_len = (1 << log_memory) + max(1 << log_bytecode, 1 << tallest_h) + sum(t.n_bus_interactions << h for t, h in tables_sorted)
    logup_n_vars = log2_ceil(total_active_len)

    quotient, gkr_point, claim_num, claim_den = verify_gkr_quotient(fiat_shamir, logup_n_vars)
    assert quotient == ZERO, "imbalanced logup bus"

    def pref_at(offset: int, log_height: int) -> EF:
        n_missing = logup_n_vars - log_height
        return eq_at_index(gkr_point, offset >> log_height, n_missing)

    num = den = ZERO

    # Memory section
    mem_pt = gkr_point[-log_memory:]
    pref = pref_at(0, log_memory)
    memory_acc_eval = fiat_shamir.next_extension_scalar()
    memory_eval = fiat_shamir.next_extension_scalar()
    num -= pref * memory_acc_eval
    den += pref * (gamma - finger_print(Fp(LOGUP_MEMORY_DOMAINSEP), [mle_of_01234567_etc(mem_pt), memory_eval], beta_eq))
    offset = 1 << log_memory

    # Bytecode section (padded to the tallest table)
    log_bytecode_padded = max(log_bytecode, tallest_h)
    bytecode_point = gkr_point[-log_bytecode:]
    pref = pref_at(offset, log_bytecode)
    pref_padded = pref_at(offset, log_bytecode_padded)
    value_bytecode_acc = fiat_shamir.next_extension_scalar()
    bytecode_eval = eval_multilinear_by_evals([Fp(v) for v in bytecode_multilinear], bytecode_point + beta[-log_instr:])
    correction = math.prod(ONE - a for a in beta[: len(beta) - log_instr])
    fingerprint_bytecode = (
        bytecode_eval * correction + mle_of_01234567_etc(bytecode_point) * beta_eq[N_INSTRUCTION_COLUMNS] + beta_eq[-1] * Fp(LOGUP_BYTECODE_DOMAINSEP)
    )
    num -= pref * value_bytecode_acc
    den += pref * (gamma - fingerprint_bytecode) + pref_padded * mle_of_zeros_then_ones(1 << log_bytecode, gkr_point[-log_bytecode_padded:])
    offset += 1 << log_bytecode_padded

    # Per-table section
    table_offsets: dict[str, int] = {}
    for table, log_height in tables_sorted:
        table_offsets[table.name] = offset
        offset += table.n_bus_interactions << log_height
    final_offset = offset

    precompile_nums: dict[str, EF] = {}
    precompile_dens: dict[str, EF] = {}
    columns_evals: dict[str, dict[int, EF]] = {}

    for table in tables:
        offset = table_offsets[table.name]
        columns_evals[table.name] = {}

        def request_column_evals_dedup(cols: Sequence[int]) -> list[EF]:
            missing = [c for c in cols if c not in columns_evals[table.name]]
            for c, e in zip(missing, fiat_shamir.next_extension_scalars_vec(len(missing))):
                columns_evals[table.name][c] = e
            return [columns_evals[table.name][c] for c in cols]

        for bus in table.buses:
            if bus.cols:
                # memory / bytecode interraction
                base = [table.col(c) for c in bus.cols]
                for i in range(bus.n_terms):  # term i: σ = (m[base[0]] + i, m[base[1:] + i])
                    pref = pref_at(offset, table_heights[table.name])
                    d = request_column_evals_dedup([base[0], *(c + i for c in base[1:])])
                    num += pref  # always multiplicity 1
                    den += pref * (gamma - finger_print(Fp(bus.domain_sep), [d[0] + i, *d[1:]], beta_eq))
                    offset += 1 << table_heights[table.name]
            else:
                # precompile interraction
                pref = pref_at(offset, table_heights[table.name])
                precompile_nums[table.name] = fiat_shamir.next_extension_scalar()
                precompile_dens[table.name] = fiat_shamir.next_extension_scalar()
                num += pref * precompile_nums[table.name]
                den += pref * precompile_dens[table.name]
                offset += 1 << table_heights[table.name]

    den += mle_of_zeros_then_ones(final_offset, gkr_point)
    assert num == claim_num, "logup: numerators value mismatch"
    assert den == claim_den, "logup: denominators value mismatch"

    return memory_eval, memory_acc_eval, value_bytecode_acc, precompile_nums, precompile_dens, gkr_point, columns_evals


class Cols(dict):
    def arr(self, prefix: str, n: int) -> list:
        return [self[f"{prefix}_{i}"] for i in range(n)]


class ConstraintEvaluator:
    def __init__(self, flat: Sequence[EF], shift: Sequence[EF], alpha_powers: Sequence[EF], columns: Sequence[str]) -> None:
        self.flat = flat
        self.shift = shift
        self.alpha_powers = alpha_powers
        # Shift columns are always the first `n_shift` columns of the table.
        self.flat = Cols(zip(columns, self.flat))
        self.next = Cols(zip(columns[: len(self.shift)], self.shift))
        self.accumulator: EF = ZERO
        self.i = 0

    def assert_zero(self, x: EF) -> None:
        self.accumulator = self.accumulator + self.alpha_powers[self.i] * x
        self.i += 1

    def assert_eq(self, x: EF, y: EF) -> None:
        self.assert_zero(x - y)

    def assert_bool(self, x: EF) -> None:
        self.assert_zero(x * (ONE - x))


def eval_precompile_bus_in_air(
    evaluator: "ConstraintEvaluator",
    logup_beta_eq: list[EF],
    multiplicity: EF,
    domainsep: EF,
    data: Sequence[EF],
) -> None:
    evaluator.assert_zero(multiplicity)
    evaluator.assert_zero(finger_print(domainsep, data, logup_beta_eq))


def eval_air_execution_table(evaluator: ConstraintEvaluator, logup_beta_eq: list[EF]) -> None:
    (pc, fp, addr_a, addr_b, addr_c, value_a, value_b, value_c, operand_a, operand_b, operand_c,
        flag_a, flag_b, flag_c, flag_c_fp, flag_ab_fp, flag_mul, flag_jump, aux_1, aux_2) = (evaluator.flat[k] for k in EXECUTION_COLUMNS)  # fmt: skip
    next_pc, next_fp = evaluator.next["pc"], evaluator.next["fp"]

    # nu_x = flag·operand + (1 − flag − flag_ab_fp)·value + flag_ab_fp·(fp + operand)
    nfa = ONE - flag_a - flag_ab_fp
    nfb = ONE - flag_b - flag_ab_fp
    nfc = ONE - flag_c - flag_c_fp
    nu_a = flag_a * operand_a + nfa * value_a + flag_ab_fp * (fp + operand_a)
    nu_b = flag_b * operand_b + nfb * value_b + flag_ab_fp * (fp + operand_b)
    nu_c = flag_c * operand_c + nfc * value_c + flag_c_fp * (fp + operand_c)

    # aux_1 ∈ {0,1,2}: 0=nothing, 1=add, 2=deref.
    flag_add = aux_1 * 2 - aux_1 * aux_1
    flag_deref = aux_1 * (aux_1 - ONE) * ((P + 1) // 2)  # (P+1)/2 is the inverse of 2 mod P
    flag_precompile = ONE - flag_add - flag_mul - flag_deref - flag_jump

    eval_precompile_bus_in_air(evaluator, logup_beta_eq, flag_precompile, aux_2, [nu_a, nu_b, nu_c])
    evaluator.assert_zero(nfa * (addr_a - (fp + operand_a)))
    evaluator.assert_zero(nfb * (addr_b - (fp + operand_b)))
    evaluator.assert_zero(nfc * (addr_c - (fp + operand_c)))
    evaluator.assert_zero(flag_add * (nu_b - (nu_a + nu_c)))
    evaluator.assert_zero(flag_mul * (nu_b - nu_a * nu_c))
    evaluator.assert_zero(flag_deref * (addr_b - (value_a + operand_b)))
    evaluator.assert_zero(flag_deref * (value_b - nu_c))
    jumping = flag_jump * nu_a
    evaluator.assert_zero(jumping * (nu_a - ONE))  # nu_a (condition) should be boolean in case of JUMP instruction
    evaluator.assert_zero(jumping * (next_pc - nu_b))
    evaluator.assert_zero(jumping * (next_fp - nu_c))
    not_jumping = ONE - jumping
    evaluator.assert_zero(not_jumping * (next_pc - (pc + ONE)))
    evaluator.assert_zero(not_jumping * (next_fp - fp))


def eval_air_extension_table(evaluator: ConstraintEvaluator, logup_beta_eq: list[EF]) -> None:
    (flag_be, flag_start, len_col, flag_add, flag_dot_product, flag_eq, idx_a, idx_b) = (evaluator.flat[k] for k in EXTENSION_COLUMNS[:8])  # fmt: skip
    idx_r, acc, v_a, v_b, res = evaluator.flat["idx_r"], evaluator.flat.arr("acc", EF.DIMENSION), evaluator.flat.arr("v_a", EF.DIMENSION), evaluator.flat.arr("v_b", EF.DIMENSION), evaluator.flat.arr("res", EF.DIMENSION)  # fmt: skip
    flag_be_next, flag_start_next, len_next, flag_add_next, flag_dot_product_next, flag_eq_next, idx_a_next, idx_b_next = (evaluator.next[k] for k in EXTENSION_COLUMNS[:8])  # fmt: skip
    acc_next = evaluator.next.arr("acc", EF.DIMENSION)

    aux_2 = flag_be * EXT_OP_FLAG_BE + flag_add * EXT_OP_FLAG_ADD + flag_dot_product * EXT_OP_FLAG_DOT_PRODUCT + flag_eq * EXT_OP_FLAG_EQ + len_col * EXT_OP_LEN_MULTIPLIER  # fmt: skip
    eval_precompile_bus_in_air(evaluator, logup_beta_eq, flag_start * (flag_add + flag_dot_product + flag_eq), aux_2, [idx_a, idx_b, idx_r])  # fmt: skip

    for x in (flag_be, flag_start, flag_add, flag_dot_product, flag_eq):
        evaluator.assert_bool(x)

    is_ee, not_start_next = ONE - flag_be, ONE - flag_start_next
    v_a_tilde = [v_a[0]] + [v_a[k] * is_ee for k in range(1, EF.DIMENSION)]
    acc_tail = [acc_next[k] * not_start_next for k in range(EF.DIMENSION)]
    v_a_v_b = quintic_mul(v_a_tilde, v_b, ZERO)

    for k in range(EF.DIMENSION):
        evaluator.assert_zero((acc[k] - (v_a_tilde[k] + v_b[k] + acc_tail[k])) * flag_add)
    for k in range(EF.DIMENSION):
        evaluator.assert_zero((acc[k] - (v_a_v_b[k] + acc_tail[k])) * flag_dot_product)
    # eq: acc ← (2·v_a·v_b − v_a − v_b + 1) · (acc_tail or 1 at group end).
    e_eq = [2 * v_a_v_b[k] - v_a_tilde[k] - v_b[k] + (ONE if k == 0 else ZERO) for k in range(EF.DIMENSION)]
    acc_tail_or_one = [acc_next[0] * not_start_next + flag_start_next] + [acc_next[k] * not_start_next for k in range(1, EF.DIMENSION)]
    eq_result = quintic_mul(e_eq, acc_tail_or_one, ZERO)
    for k in range(EF.DIMENSION):
        evaluator.assert_zero((acc[k] - eq_result[k]) * flag_eq)

    for k in range(EF.DIMENSION):
        evaluator.assert_zero((acc[k] - res[k]) * flag_start)

    for x, y in [(len_col, len_next + ONE), (flag_be, flag_be_next), (flag_add, flag_add_next), (flag_dot_product, flag_dot_product_next), (flag_eq, flag_eq_next)]:  # fmt: skip
        evaluator.assert_zero(not_start_next * (x - y))

    evaluator.assert_zero(not_start_next * (idx_a_next - idx_a - (flag_be + is_ee * EF.DIMENSION)))
    evaluator.assert_zero(not_start_next * (idx_b_next - idx_b - EF.DIMENSION))
    evaluator.assert_zero(flag_start_next * (len_col - ONE))


def eval_air_poseidon16_table(evaluator: ConstraintEvaluator, logup_beta_eq: list[EF]) -> None:
    multiplicity, nu_b, nu_c , flag_out4, flag_out8, flag_left, offset_left, addr_left_lo, addr_left_hi, flag_permute = (evaluator.flat[k] for k in POSEIDON_COLUMNS[:10])  # fmt: skip
    inputs = evaluator.flat.arr("input", POSEIDON_WIDTH)
    beginning_full_rounds = [evaluator.flat.arr(f"begin_r{r}", POSEIDON_WIDTH) for r in range(POSEIDON_QUARTER_FULL_ROUNDS)]  # fmt: skip
    partial_cols = evaluator.flat.arr("partial", POSEIDON_PARTIAL_ROUNDS)
    ending_full_rounds = [evaluator.flat.arr(f"end_r{r}", POSEIDON_WIDTH) for r in range(POSEIDON_QUARTER_FULL_ROUNDS - 1)]  # fmt: skip
    out_lo, out_hi = evaluator.flat.arr("out_lo", POSEIDON_WIDTH // 2), evaluator.flat.arr("out_hi", POSEIDON_WIDTH // 2)  # fmt: skip

    domainsep = POSEIDON_DOMAINSEP_BASE + flag_permute * POSEIDON_FLAG_PERMUTE_SHIFT + flag_out8 * POSEIDON_FLAG_OUT8_SHIFT + flag_left * POSEIDON_FLAG_LEFT_SHIFT + flag_left * offset_left * POSEIDON_OFFSET_LEFT_SHIFT  # fmt: skip
    not_flag_left = ONE - flag_left
    nu_a = addr_left_hi - not_flag_left * (DIGEST_ELEMS // 2)
    eval_precompile_bus_in_air(evaluator, logup_beta_eq, multiplicity, domainsep, [nu_a, nu_b, nu_c])
    for f in (multiplicity, flag_out4, flag_out8, flag_left, flag_permute):
        evaluator.assert_bool(f)
    evaluator.assert_zero(flag_permute * flag_out4)
    evaluator.assert_zero(flag_out8 * flag_out4)
    evaluator.assert_zero((ONE - flag_permute) * (ONE - flag_out8) * (ONE - flag_out4))
    evaluator.assert_zero(flag_left * (offset_left - addr_left_lo))
    evaluator.assert_zero(not_flag_left * (nu_a - addr_left_lo))
    state = list(inputs)

    def do_2_full_round(state: list[EF], rc1: list[Fp], rc2: list[Fp]) -> list[EF]:
        for rc in (rc1, rc2):
            sbox = [(s + c).cube() for s, c in zip(state, rc)]
            state = [dot_product(sbox, row) for row in POSEIDON_AIR_MDS_DENSE]
        return state

    # 2-by-2 initial full rounds
    for r in range(POSEIDON_QUARTER_FULL_ROUNDS):
        state = do_2_full_round(state, POSEIDON_AIR_INITIAL_CONSTANTS[2 * r], POSEIDON_AIR_INITIAL_CONSTANTS[2 * r + 1])
        for i, post in enumerate(beginning_full_rounds[r]):
            evaluator.assert_eq(state[i], post)
            state[i] = post
    # partial-rounds (using the sparse decomposition, see Appendix of [Poseidon1](https://eprint.iacr.org/2019/458))
    state = [s + rc for s, rc in zip(state, POSEIDON_AIR_SPARSE_FIRST_RC)]
    state = [dot_product(state, row) for row in POSEIDON_AIR_SPARSE_M_I]
    for r in range(POSEIDON_PARTIAL_ROUNDS):
        evaluator.assert_eq(state[0].cube(), partial_cols[r])
        state[0] = partial_cols[r]
        if r < POSEIDON_PARTIAL_ROUNDS - 1:
            state[0] += POSEIDON_AIR_SPARSE_SCALAR_RC[r]
        old_s0 = state[0]
        state[0] = dot_product(state, POSEIDON_AIR_SPARSE_FIRST_ROW[r])
        for i in range(1, POSEIDON_WIDTH):
            state[i] += old_s0 * POSEIDON_AIR_SPARSE_V[r][i - 1]
    # 2-by-2 final full rounds
    for r in range(POSEIDON_QUARTER_FULL_ROUNDS - 1):
        state = do_2_full_round(state, POSEIDON_AIR_FINAL_CONSTANTS[2 * r], POSEIDON_AIR_FINAL_CONSTANTS[2 * r + 1])
        for i, post in enumerate(ending_full_rounds[r]):
            evaluator.assert_eq(state[i], post)
            state[i] = post
    # Last full round
    state = do_2_full_round(state, POSEIDON_AIR_FINAL_CONSTANTS[-2], POSEIDON_AIR_FINAL_CONSTANTS[-1])
    not_permute, gate_out_4_to_8, gate_hi = ONE - flag_permute, ONE - flag_out4, ONE - flag_out8 - flag_out4
    for i in range(POSEIDON_WIDTH // 2):
        value = state[i] + not_permute * inputs[i]  # when it's not permutation -> it's a compression (feedforward)
        if i < (DIGEST_ELEMS // 2):
            evaluator.assert_zero(value - out_lo[i])
        else:
            evaluator.assert_zero(gate_out_4_to_8 * (value - out_lo[i]))
        evaluator.assert_zero(gate_hi * (state[i + POSEIDON_WIDTH // 2] - out_hi[i]))


EXECUTION_COLUMNS = (
    "pc", "fp", # 'next' columns (the rest are 'flat')
    "addr_a", "addr_b", "addr_c", "value_a", "value_b", "value_c", # 8 runtime cols
    "operand_a", "operand_b", "operand_c", "flag_a", "flag_b", "flag_c", "flag_c_fp", "flag_ab_fp", "flag_mul", "flag_jump", "aux_1", "aux_2", # 12 instruction cols.
)  # fmt: skip

EXTENSION_COLUMNS = (
    "flag_be", "flag_start", "len", "flag_add", "flag_dot_product", "flag_eq", "idx_a", "idx_b", *(f"acc_{i}" for i in range(EF.DIMENSION)), # 'next' columns
    "idx_r", *(f"v_a_{i}" for i in range(EF.DIMENSION)), *(f"v_b_{i}" for i in range(EF.DIMENSION)), *(f"res_{i}" for i in range(EF.DIMENSION)), # # 'flat' columns
)  # fmt: skip

POSEIDON_COLUMNS = ( # all 'flat' columns
    "multiplicity", "nu_b", "nu_c", "flag_out4", "flag_out8", "flag_left", "offset_left", "addr_left_lo", "addr_left_hi", "flag_permute",
    *(f"input_{i}" for i in range(POSEIDON_WIDTH)),
    *(f"begin_r{r}_{i}" for r in range(POSEIDON_HALF_FULL_ROUNDS // 2) for i in range(POSEIDON_WIDTH)),
    *(f"partial_{i}" for i in range(POSEIDON_PARTIAL_ROUNDS)),
    *(f"end_r{r}_{i}" for r in range(POSEIDON_HALF_FULL_ROUNDS // 2 - 1) for i in range(POSEIDON_WIDTH)),
    *(f"out_lo_{i}" for i in range(POSEIDON_WIDTH // 2)), *(f"out_hi_{i}" for i in range(POSEIDON_WIDTH // 2)), # lo: [0:8], hi: [8:16]
)  # fmt: skip

TABLES = [
    Table(
        name="execution",
        columns=EXECUTION_COLUMNS,
        buses=(
            BusInteraction(BusDirection.PUSH),
            BusInteraction(BusDirection.PULL, LOGUP_BYTECODE_DOMAINSEP, (*EXECUTION_COLUMNS[N_RUNTIME_COLUMNS:], "pc")),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("addr_a", "value_a")),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("addr_b", "value_b")),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("addr_c", "value_c")),
        ),
        air_degree=5,
        n_constraints=14,
        n_shift=2,
        max_log_height=24,
        air_constraints_fn=eval_air_execution_table,
    ),
    Table(
        name="extension",
        columns=EXTENSION_COLUMNS,
        buses=(
            BusInteraction(BusDirection.PULL),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("idx_a", "v_a_0"), EF.DIMENSION),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("idx_b", "v_b_0"), EF.DIMENSION),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("idx_r", "res_0"), EF.DIMENSION),
        ),
        air_degree=6,
        n_constraints=35,
        n_shift=13,
        max_log_height=21,
        air_constraints_fn=eval_air_extension_table,
    ),
    Table(
        name="poseidon",
        columns=POSEIDON_COLUMNS,
        buses=(
            BusInteraction(BusDirection.PULL),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("addr_left_lo", "input_0"), 4),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("addr_left_hi", "input_4"), 4),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("nu_b", "input_8"), 8),
            BusInteraction(BusDirection.PULL, LOGUP_MEMORY_DOMAINSEP, ("nu_c", "out_lo_0"), 16),
        ),
        air_degree=10,
        n_constraints=101,
        n_shift=0,
        max_log_height=21,
        air_constraints_fn=eval_air_poseidon16_table,
    ),
]


def verify_execution(
    bytecode_multilinear: list[int],  # trusted-source (and thus contains only valid instructions)
    public_input: Sequence[Fp],
    proof: Proof,
) -> None:
    bytecode_log_size = log2_strict(len(bytecode_multilinear)) - log2_ceil(N_INSTRUCTION_COLUMNS)
    ending_pc = (1 << bytecode_log_size) - 1
    bytecode_hash = sponge_hash([Fp(v) for v in bytecode_multilinear])
    assert len(public_input) == PUBLIC_INPUT_SIZE, "public_input length mismatch"

    fiat_shamir = FiatShamir(proof, poseidon16_compress(bytecode_hash, SNARK_DOMAIN_SEP))  # domain separator across bytecodes
    fiat_shamir.observe_scalars(public_input)
    log_inv_rate, log_memory, *table_log_heights = [int(x.value) for x in fiat_shamir.next_base_scalars(2 + len(TABLES))]
    assert MIN_WHIR_LOG_INV_RATE <= log_inv_rate <= MAX_WHIR_LOG_INV_RATE, "InvalidRate"
    assert MIN_LOG_MEMORY_SIZE <= log_memory <= MAX_LOG_MEMORY_SIZE, "log_memory out of range"
    assert MIN_BYTECODE_LOG_SIZE <= bytecode_log_size <= MAX_BYTECODE_LOG_SIZE, "bytecode log_size out of range"
    assert log_memory >= max(max(table_log_heights, default=0), bytecode_log_size), "memory smaller than tables/bytecode"
    for table, log_height in zip(TABLES, table_log_heights):
        assert MIN_LOG_HEIGHT_PER_TABLE <= log_height <= table.max_log_height, f"table {table.name}: invalid height"

    table_log_heights = {t.name: h for t, h in zip(TABLES, table_log_heights)}
    tables_sorted = sort_tables_by_height(TABLES, table_log_heights)
    n_max = tables_sorted[0][1]

    total_stacked = (
        (2 << log_memory) + (1 << max(bytecode_log_size, n_max)) + sum(t.n_columns << table_log_heights[t.name] for t in TABLES)
    )  # memory + memory_acc + bytecode_acc + biggest_table + second_biggest_table + etc + smallest_table
    stacked_n_vars = log2_ceil(total_stacked)
    assert stacked_n_vars <= TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate, "tacked_n_vars exceeds WHIR domain bound"
    cfg = WHIR_CONFIGS[(log_inv_rate, stacked_n_vars)]

    # 1] Parse WHIR commitment
    parsed_commitment = WhirCommitment.parse(fiat_shamir, stacked_n_vars, cfg["commitment_ood_samples"])

    logup_gamma = fiat_shamir.sample_ef()  # the quotient denominator
    fiat_shamir.duplex()
    logup_beta = fiat_shamir.sample_many_ef(log2_ceil(N_INSTRUCTION_COLUMNS + 2))  # the bus-tuple hashing seeds
    logup_beta_eq = eval_eq(logup_beta)

    # 2] Verify logup bus interractions
    memory_eval, memory_acc_eval, value_bytecode_acc, precompile_nums, precompile_dens, gkr_point, columns_evals = verify_logup(
        fiat_shamir,
        logup_gamma,
        logup_beta,
        logup_beta_eq,
        log_memory,
        bytecode_multilinear,
        TABLES,
        table_log_heights,
    )

    alpha = fiat_shamir.sample_ef()
    alpha_powers = ef_powers(alpha, sum(t.n_constraints for t in TABLES))

    initial_sum, offset = ZERO, 0
    for table in TABLES:
        initial_sum += alpha_powers[offset] * (precompile_nums[table.name] * table.precompile_bus_interaction_sign)
        initial_sum += alpha_powers[offset + 1] * (logup_gamma - precompile_dens[table.name])
        offset += table.n_constraints

    # 3] verify batched AIR sumcheck
    sc_point, sc_value = verify_sumcheck(fiat_shamir, initial_sum, n_max, max(t.air_degree + 1 for t in TABLES))

    committed_column_evals = {t.name: [(gkr_point[-table_log_heights[t.name] :], columns_evals[t.name], {})] for t in TABLES}
    air_final_value, offset = ZERO, 0
    for table in TABLES:
        log_height = table_log_heights[table.name]
        col_evals = fiat_shamir.next_extension_scalars_vec(table.n_shift + table.n_columns)
        alphas = alpha_powers[offset : offset + table.n_constraints]
        offset += table.n_constraints
        constraint_eval = table.eval_air(col_evals, alphas, logup_beta_eq)
        natural_point = list(reversed(sc_point[-log_height:]))
        air_final_value += math.prod(sc_point[:-log_height]) * eq_poly(gkr_point[-log_height:], natural_point) * constraint_eval
        eq_vals = {i: col_evals[i] for i in range(table.n_columns)}
        next_vals = {j: col_evals[table.n_columns + j] for j in range(table.n_shift)}
        committed_column_evals[table.name].append((natural_point, eq_vals, next_vals))
    assert air_final_value == sc_value, "AIR sumcheck: claimed value mismatch"

    public_memory_point = fiat_shamir.sample_many_ef(log2_strict(PUBLIC_INPUT_SIZE))
    public_memory_eval = eval_multilinear_by_evals(public_input, public_memory_point)

    bytecode_acc_offset = (2 << log_memory) >> bytecode_log_size  # offset within the stacked polynomial
    pcs_statements = [
        SparseStatements(
            stacked_n_vars,
            gkr_point[-log_memory:],
            [(0, memory_eval), (1, memory_acc_eval)],
        ),
        SparseStatements(stacked_n_vars, public_memory_point, [(0, public_memory_eval)]),
        SparseStatements(stacked_n_vars, gkr_point[-bytecode_log_size:], [(bytecode_acc_offset, value_bytecode_acc)]),
    ]
    table_offsets: dict[str, int] = {}
    layout_offset = (2 << log_memory) + (1 << max(bytecode_log_size, tables_sorted[0][1]))
    for table, log_height in tables_sorted:
        table_offsets[table.name] = layout_offset
        layout_offset += table.n_columns << log_height

    def values_at(d: dict[int, EF], col_base: int) -> list[tuple[int, EF]]:
        return [(col_base + i, v) for i, v in sorted(d.items())]

    for table in TABLES:
        log_height = table_log_heights[table.name]
        offset = table_offsets[table.name]
        col_base = offset >> log_height
        pcs_statements.extend(table.boundary_statements(stacked_n_vars, offset, log_height, ending_pc))
        for point, eq_values, next_values in committed_column_evals[table.name]:
            if next_values:
                pcs_statements.append(SparseStatements(stacked_n_vars, point, values_at(next_values, col_base), True))
            pcs_statements.append(SparseStatements(stacked_n_vars, point, values_at(eq_values, col_base)))

    # 4] Open the PCS
    verify_whir(fiat_shamir, cfg, parsed_commitment, pcs_statements)

    assert fiat_shamir.offset == len(fiat_shamir.transcript), f"transcript not fully consumed ({fiat_shamir.offset}/{len(fiat_shamir.transcript)})"
    assert not fiat_shamir.openings, f"{len(fiat_shamir.openings)} Merkle openings unused"
