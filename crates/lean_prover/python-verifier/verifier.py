"""Pure-Python verifier for leanVM proofs.
Setup the test vector (one-time):
    cargo test --release --package lean_prover --lib -- test_zkvm::dump_test_vector_for_python_verifier --include-ignored
Run:
    python3 crates/lean_prover/python-verifier/verifier.py
Format:
    ruff format --line-length 120 crates/lean_prover/python-verifier
"""

from __future__ import annotations
import array
import json
import math
import sys
from dataclasses import dataclass
from enum import IntEnum
from pathlib import Path
from typing import Sequence
from primitives import *


PUBLIC_INPUT_SIZE = DIGEST_ELEMS
SNARK_DOMAIN_SEP = [Fp(v) for v in (130704175, 1303721200, 493664240, 1035493700, 2063844858, 1410214009, 1938905908, 1696767928)]  # fmt: skip

WHIR_INITIAL_FOLDING_FACTOR, WHIR_SUBSEQUENT_FOLDING_FACTOR, WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS = 7, 5, 8
MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE, RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 1, 4, 5
_WHIR_CONFIGS = ((1,7,1,10,220,16,()),(1,8,1,11,220,16,()),(1,9,1,12,220,16,()),(1,10,1,13,220,16,()),(1,11,1,14,220,16,()),(1,12,1,15,220,16,()),(1,13,1,16,220,16,()),(1,14,1,15,221,16,()),(1,15,1,16,221,16,()),(1,16,1,16,73,16,((222,1,16,11),)),(1,17,1,16,73,16,((223,1,16,12),)),(1,18,1,16,73,16,((224,1,16,13),)),(1,19,1,16,73,16,((225,1,16,14),)),(1,20,1,16,73,16,((227,1,16,15),)),(1,21,2,16,32,16,((229,1,16,16),(73,1,16,9))),(1,22,2,16,32,16,((230,1,16,12),(74,1,16,10))),(1,23,2,16,32,16,((234,1,16,13),(74,1,16,11))),(1,24,2,16,32,16,((235,1,16,14),(74,1,16,12))),(1,25,2,16,32,16,((241,2,16,15),(74,2,16,13))),(1,26,2,16,21,14,((243,2,16,16),(74,2,16,14),(32,2,16,14))),(1,27,2,16,21,14,((248,2,16,15),(75,2,16,15),(32,2,16,15))),(1,28,2,16,21,14,((256,2,16,16),(75,2,16,16),(32,2,16,16))),(1,29,2,16,21,14,((262,2,16,15),(76,2,16,12),(33,2,16,17))),(1,30,2,16,21,14,((270,2,16,16),(76,2,16,13),(33,2,16,18))),(2,7,1,13,109,16,()),(2,8,1,14,109,16,()),(2,9,1,15,109,16,()),(2,10,1,16,109,16,()),(2,11,1,12,110,16,()),(2,12,1,13,110,16,()),(2,13,1,14,110,16,()),(2,14,1,15,110,16,()),(2,15,1,16,110,16,()),(2,16,1,14,55,16,((111,1,16,10),)),(2,17,1,15,55,16,((111,1,16,11),)),(2,18,1,16,55,16,((111,1,16,12),)),(2,19,1,15,55,16,((112,1,16,13),)),(2,20,2,16,55,16,((112,1,16,14),)),(2,21,2,16,28,16,((113,1,16,15),(55,1,16,10))),(2,22,2,15,28,16,((114,1,16,16),(55,1,16,11))),(2,23,2,16,28,16,((114,1,16,13),(56,1,16,12))),(2,24,2,16,28,16,((115,1,16,14),(56,2,16,13))),(2,25,2,15,28,16,((118,2,16,15),(56,2,16,14))),(2,26,2,16,19,15,((118,2,16,16),(56,2,16,15),(28,2,16,17))),(2,27,2,16,19,15,((119,2,16,13),(57,2,16,16),(28,2,16,18))),(2,28,2,16,19,15,((120,2,16,14),(57,2,16,14),(29,2,15,19))),(2,29,2,16,19,15,((123,2,16,15),(57,2,16,15),(29,2,15,20))),(3,7,1,9,73,16,()),(3,8,1,10,73,16,()),(3,9,1,11,73,16,()),(3,10,1,12,73,16,()),(3,11,1,13,73,16,()),(3,12,1,14,73,16,()),(3,13,1,15,73,16,()),(3,14,1,16,73,16,()),(3,15,1,12,74,16,()),(3,16,1,13,44,16,((74,1,16,11),)),(3,17,1,14,44,16,((74,1,16,12),)),(3,18,2,15,44,16,((74,1,16,13),)),(3,19,2,16,44,16,((74,1,16,14),)),(3,20,2,15,44,16,((75,1,16,15),)),(3,21,2,16,25,16,((75,1,16,16),(44,1,16,11))),(3,22,2,15,25,16,((76,1,16,11),(45,1,16,12))),(3,23,2,16,25,16,((76,1,16,12),(45,2,16,13))),(3,24,2,16,25,16,((77,2,16,13),(45,2,16,14))),(3,25,2,16,25,16,((78,2,15,14),(45,2,16,15))),(3,26,2,16,18,12,((79,2,15,15),(45,2,16,16),(25,2,16,19))),(3,27,2,16,18,12,((80,2,16,16),(45,2,16,15),(26,2,13,20))),(3,28,2,15,18,12,((82,2,15,15),(46,2,16,16),(26,2,13,21))),(4,7,1,8,55,16,()),(4,8,1,9,55,16,()),(4,9,1,10,55,16,()),(4,10,1,11,55,16,()),(4,11,1,12,55,16,()),(4,12,1,13,55,16,()),(4,13,1,14,55,16,()),(4,14,1,15,55,16,()),(4,15,1,16,55,16,()),(4,16,1,13,37,16,((56,1,16,9),)),(4,17,1,14,37,16,((56,1,16,10),)),(4,18,2,15,37,16,((56,1,16,11),)),(4,19,2,16,37,16,((56,1,16,12),)),(4,20,2,13,37,16,((57,1,16,13),)),(4,21,2,14,23,15,((57,2,16,14),(37,2,16,12))),(4,22,2,15,23,15,((57,2,16,15),(37,2,16,13))),(4,23,2,16,23,15,((57,2,16,16),(37,2,16,14))),(4,24,2,15,23,15,((58,2,16,13),(38,2,16,15))),(4,25,2,16,23,15,((58,2,16,14),(38,2,16,16))),(4,26,2,16,16,16,((60,2,15,15),(38,2,16,17),(23,2,15,22))),(4,27,2,15,16,16,((61,2,16,16),(38,2,16,18),(23,2,15,23))))  # fmt: skip
WHIR_CONFIGS = {
    (c[0], c[1]): {
        "log_inv_rate": c[0],
        "num_variables": c[1],
        "commitment_ood_samples": c[2],
        "starting_folding_pow_bits": c[3],
        "final_queries": c[4],
        "final_query_pow_bits": c[5],
        "rounds": [
            {"num_queries": r[0], "ood_samples": r[1], "query_pow_bits": r[2], "folding_pow_bits": r[3]} for r in c[6]
        ],
    }
    for c in _WHIR_CONFIGS
}

MIN_LOG_MEMORY_SIZE, MAX_LOG_MEMORY_SIZE = 16, 26
MIN_LOG_N_ROWS_PER_TABLE, MIN_BYTECODE_LOG_SIZE, MAX_BYTECODE_LOG_SIZE = 8, 8, 22
N_VARS_TO_SEND_GKR_COEFFS = 5

N_RUNTIME_COLUMNS, N_INSTRUCTION_COLUMNS = 8, 12

LOGUP_MEMORY_DOMAINSEP, LOGUP_BYTECODE_DOMAINSEP = 1, 2
POSEIDON_DISCRIMINATOR_BASE = 3  # odd ≥ 3
POSEIDON_PERMUTE_SHIFT, POSEIDON_HALF_OUTPUT_SHIFT = 1 << 1, 1 << 2
POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT, POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT = 1 << 3, 1 << 4
EXT_OP_FLAG_IS_BE, EXT_OP_FLAG_ADD, EXT_OP_FLAG_MUL, EXT_OP_FLAG_POLY_EQ, EXT_OP_LEN_MULTIPLIER = 4, 8, 16, 32, 64

STARTING_PC = 0  # every program starts at PC = 0, and ends at PC = len(bytecode) - 1


class ProofError(Exception):
    pass


class BusDirection(IntEnum):
    PUSH = 1
    PULL = -1


class BusInteraction(IntEnum):
    PRECOMPILE = 0
    BYTECODE = 1
    MEMORY = 2


@dataclass(frozen=True)
class Table:
    name: str
    columns: tuple[str, ...]
    buses: tuple
    air_degree: int
    n_constraints: int
    n_shift: int  # shift (next-row) columns are always the first ones
    max_log_height: int
    air_constraints_fn: object  # (folder, logup_beta_eq) -> None

    @property
    def n_columns(self) -> int:
        return len(self.columns)

    @property
    def n_buses(self) -> int:
        return sum(b[3] if b[0] == BusInteraction.MEMORY else 1 for b in self.buses)

    @property
    def precompile_bus_interraction_sign(self) -> EF:
        return EF(self.buses[0][1])  # precompile interraction is the first, by convention

    def col(self, name: str) -> int:
        return self.columns.index(name)

    def eval_air(self, col_evals: Sequence[EF], alpha_powers: Sequence[EF], logup_beta_eq: list[EF]) -> EF:
        folder = ConstraintFolder(col_evals[: self.n_columns], col_evals[self.n_columns :], alpha_powers, self.columns)
        self.air_constraints_fn(folder, logup_beta_eq)
        return folder.accumulator

    def boundary_statements(
        self, stacked_n_vars: int, offset: int, n_vars: int, ending_pc: int
    ) -> list["SparseStatements"]:
        if self.name != "execution":
            return []
        pc_col_offset = offset + (self.col("pc") << n_vars)
        return [
            SparseStatements(stacked_n_vars, [], [(pc_col_offset + idx, EF(pc))])
            for idx, pc in [(0, STARTING_PC), ((1 << n_vars) - 1, ending_pc)]
        ]


# T-Sponge (compression instead of permutation) with replacement (instead of xoring / adding the ingested data).
def sponge_hash(data: Sequence[Fp]) -> list[Fp]:
    assert len(data) % SPONGE_RATE == 0 and len(data) > 0
    state = [Fp(len(data))] + [Fp(0)] * (SPONGE_CAPACITY - 1)
    for k in range(len(data) // SPONGE_RATE):
        state = poseidon16_compress(state, data[k * SPONGE_RATE : (k + 1) * SPONGE_RATE])
    return state


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
        assert self.rate_fresh, "stale rate — insert duplex() before sampling"
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
        return pack_ef(flat)

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
        if self.offset + n_pad > len(self.transcript):
            raise ProofError("ExceededTranscript")
        chunk = self.transcript[self.offset : self.offset + n_pad]
        self.offset += n_pad
        if any(int(chunk[i].value) for i in range(n, n_pad)):
            raise ProofError("InvalidTranscript: non-zero padding")
        self.observe_many(chunk)
        return chunk

    def observe_scalars(self, scalars: Sequence[Fp]) -> None:
        self.observe_many(list(scalars))

    def next_base_scalars_vec(self, n: int) -> list[Fp]:
        return self._read_padded(n)[:n]

    def next_extension_scalars_vec(self, n: int) -> list[EF]:
        flat = self.next_base_scalars_vec(n * EF.DIMENSION)
        return pack_ef(flat)

    def next_extension_scalar(self) -> EF:
        return self.next_extension_scalars_vec(1)[0]

    def next_merkle_opening(self) -> MerkleOpening:
        if not self.openings:
            raise ProofError("ExceededTranscript: no more Merkle openings")
        return self.openings.pop()

    def check_pow_grinding(self, bits: int) -> None:
        if bits == 0:
            return
        self._read_padded(1)
        if int(self.state[SPONGE_CAPACITY].value) & ((1 << bits) - 1) != 0:
            raise ProofError("InvalidGrindingWitness")


def merkle_verify_path(
    root: list[Fp],
    log_height: int,
    index: int,
    opened_values: Sequence[Fp],
    opening_proof: Sequence[list[Fp]],
) -> None:
    if len(opening_proof) != log_height:
        raise ProofError("Merkle verification failed: opening proof has wrong length")
    chunks = [list(opened_values[i : i + SPONGE_RATE]) for i in range(0, len(opened_values), SPONGE_RATE)]
    current = sponge_hash([x for c in reversed(chunks) for x in c])
    for sibling in opening_proof:
        current = poseidon16_compress(current, sibling) if index & 1 == 0 else poseidon16_compress(sibling, current)
        index >>= 1
    if root != current:
        raise ProofError("Merkle verification failed: root mismatch")


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


def eval_multilinear_evals(evals: Sequence[Fp | EF], point: Sequence[EF]) -> EF:
    """Evaluate a multilinear in evaluation form at `point`."""
    assert len(evals) == 1 << len(point)
    cur: Sequence = evals
    for r in reversed(point):
        cur = [cur[j] + (cur[j + 1] - cur[j]) * r for j in range(0, len(cur), 2)]
    return cur[0]


def eval_multilinear_coeffs(coeffs: Sequence[EF], point: Sequence[EF]) -> EF:
    """Evaluate a multilinear in coefficient form at `point`."""
    assert len(coeffs) == 1 << len(point)
    if not point:
        return coeffs[0]
    half = len(coeffs) // 2
    lo = eval_multilinear_coeffs(coeffs[:half], point[1:])
    hi = eval_multilinear_coeffs(coeffs[half:], point[1:])
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
    point: list[EF]
    values: list[tuple[int, EF]]
    is_next: bool = False

    @property
    def selector_num_variables(self) -> int:
        return self.total_num_variables - len(self.point)


def whir_folding_factor_at_round(r: int) -> int:
    return WHIR_INITIAL_FOLDING_FACTOR if r == 0 else WHIR_SUBSEQUENT_FOLDING_FACTOR


def whir_n_rounds_and_final_sumcheck(num_variables: int) -> tuple[int, int]:
    nv = num_variables - WHIR_INITIAL_FOLDING_FACTOR
    if nv < WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS:
        return 0, nv
    n = div_ceil(nv - WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS, WHIR_SUBSEQUENT_FOLDING_FACTOR)
    return n, nv - n * WHIR_SUBSEQUENT_FOLDING_FACTOR


@dataclass
class ParsedCommitment:
    num_variables: int
    root: list[Fp]
    ood_points: list[EF]
    ood_answers: list[EF]

    def oods_constraints(self) -> list[SparseStatements]:
        return [
            SparseStatements(self.num_variables, expand_from_univariate(p, self.num_variables), [(0, ev)])
            for p, ev in zip(self.ood_points, self.ood_answers)
        ]


def verify_sumcheck(
    fiat_shamir: FiatShamir, target: EF, n_rounds: int, degree: int, pow_bits: int = 0
) -> tuple[list[EF], EF]:
    point: list[EF] = []
    for _ in range(n_rounds):
        coeffs = fiat_shamir.next_extension_scalars_vec(degree + 1)
        s = coeffs[0] + sum(coeffs)
        if s != target:
            raise ProofError("Sumcheck identity failed: h(0) + h(1) != target")
        fiat_shamir.check_pow_grinding(pow_bits)
        r = fiat_shamir.sample_ef()
        point.append(r)
        target = eval_univariate_polynomial(coeffs, r)
    return point, target


def verify_stir_challenges(
    fiat_shamir: FiatShamir,
    round_index: int,
    log_height: int,
    num_variables: int,
    num_queries: int,
    query_pow_bits: int,
    commitment: ParsedCommitment,
    folding_randomness: list[EF],
) -> list[SparseStatements]:
    gen = Fp(KB_TWO_ADIC_GENERATORS[log_height])
    fiat_shamir.check_pow_grinding(query_pow_bits)
    indices = fiat_shamir.sample_in_range(log_height, num_queries)
    constraints: list[SparseStatements] = []
    for idx in indices:
        op = fiat_shamir.next_merkle_opening()
        merkle_verify_path(commitment.root, log_height, idx, op.leaf_data, op.path)
        # Round 0 leaves are raw base-field elements; later rounds pack DIM Fp values per EF element.
        leaf = op.leaf_data
        if round_index == 0:
            packed = leaf
        else:
            packed = pack_ef(leaf)
        fold = eval_multilinear_evals(packed, folding_randomness)
        ef_pt = EF(pow(int(gen.value), idx, P))
        pt = expand_from_univariate(ef_pt, num_variables)
        constraints.append(SparseStatements(num_variables, pt, [(0, fold)]))
    return constraints


def whir_verify(
    fiat_shamir: FiatShamir,
    cfg: dict,
    parsed_commitment: ParsedCommitment,
    statements: list[SparseStatements],
) -> list[EF]:
    n_rounds, final_sumcheck_rounds = whir_n_rounds_and_final_sumcheck(cfg["num_variables"])
    round_constraints: list[tuple[list[EF], list[SparseStatements]]] = []
    round_folding: list[list[EF]] = []
    target = ZERO

    def step(constraints: list[SparseStatements], n_fold: int, pow_bits: int) -> None:
        nonlocal target
        fiat_shamir.duplex()
        gamma = fiat_shamir.sample_ef()
        combo: list[EF] = []
        g = ONE
        for smt in constraints:
            for _, value in smt.values:
                target += g * value
                combo.append(g)
                g *= gamma
        round_constraints.append((combo, constraints))
        sc_point, target = verify_sumcheck(fiat_shamir, target, n_fold, 2, pow_bits)
        round_folding.append(sc_point)

    step(
        parsed_commitment.oods_constraints() + statements,
        whir_folding_factor_at_round(0),
        cfg["starting_folding_pow_bits"],
    )

    prev_commitment = parsed_commitment
    current_vars = cfg["num_variables"]
    log_domain = cfg["num_variables"] + cfg["log_inv_rate"]
    for r in range(n_rounds):
        round_params = cfg["rounds"][r]
        current_vars -= whir_folding_factor_at_round(r)
        n_ood_samples = round_params["ood_samples"]
        new_commitment = ParsedCommitment(
            current_vars,
            fiat_shamir.next_base_scalars_vec(DIGEST_ELEMS),
            fiat_shamir.sample_many_ef(n_ood_samples),
            fiat_shamir.next_extension_scalars_vec(n_ood_samples),
        )
        stir = verify_stir_challenges(
            fiat_shamir,
            r,
            log_domain - whir_folding_factor_at_round(r),
            current_vars,
            round_params["num_queries"],
            round_params["query_pow_bits"],
            prev_commitment,
            round_folding[-1],
        )
        step(
            new_commitment.oods_constraints() + stir,
            whir_folding_factor_at_round(r + 1),
            round_params["folding_pow_bits"],
        )
        log_domain -= RS_DOMAIN_INITIAL_REDUCTION_FACTOR if r == 0 else 1
        prev_commitment = new_commitment

    n_vars_final = current_vars - whir_folding_factor_at_round(n_rounds)
    final_coeffs = fiat_shamir.next_extension_scalars_vec(1 << n_vars_final)
    final_stir = verify_stir_challenges(
        fiat_shamir,
        n_rounds,
        log_domain - whir_folding_factor_at_round(n_rounds),
        n_vars_final,
        cfg["final_queries"],
        cfg["final_query_pow_bits"],
        prev_commitment,
        round_folding[-1],
    )
    # Each STIR constraint's point is `expand_from_univariate(α, n)` = [α, α², α⁴, …]. We check that `Σ coeffs[i]·α^i == value` for each smt
    for smt in final_stir:
        univ_eval = eval_univariate_polynomial(final_coeffs, smt.point[0])
        if any(univ_eval != v[1] for v in smt.values):
            raise ProofError("Final STIR constraint mismatch")

    final_sc_point, final_sc_value = verify_sumcheck(fiat_shamir, target, final_sumcheck_rounds, 2)
    round_folding.append(final_sc_point)

    folding_flat = [r for chunk in round_folding for r in chunk]

    eval_weights = ZERO
    pt = folding_flat
    for round_idx, (randomness, smts) in enumerate(round_constraints):
        if round_idx > 0:
            pt = pt[whir_folding_factor_at_round(round_idx - 1) :]
        i = 0
        for smt in smts:
            inner_pt = pt[len(pt) - len(smt.point) :]
            common = next_mle(smt.point, inner_pt) if smt.is_next else eq_poly(smt.point, inner_pt)
            sel_n = smt.selector_num_variables
            for v in smt.values:
                lagrange = eq_at_index(pt, v[0], sel_n)
                eval_weights += lagrange * common * randomness[i]
                i += 1
    final_value = eval_multilinear_coeffs(final_coeffs, list(reversed(final_sc_point)))
    if final_sc_value != eval_weights * final_value:
        raise ProofError("WHIR final sumcheck check failed")

    return folding_flat


def stacked_pcs_global_statements(
    stacked_n_vars: int,
    memory_n_vars: int,
    bytecode_n_vars: int,
    previous_statements: list[SparseStatements],
    tables: Sequence[Table],
    heights: dict[str, int],
    committed_statements: dict[str, list[tuple[list[EF], dict[int, EF], dict[int, EF]]]],
    ending_pc: int,
) -> list[SparseStatements]:
    tables_sorted = sort_tables_by_height(tables, heights)
    table_offsets: dict[str, int] = {}
    layout_offset = (2 << memory_n_vars) + (1 << max(bytecode_n_vars, tables_sorted[0][1]))
    for table, n_vars in tables_sorted:
        table_offsets[table.name] = layout_offset
        layout_offset += table.n_columns << n_vars

    out = list(previous_statements)

    def values_at(d: dict[int, EF], col_base: int) -> list[tuple[int, EF]]:
        return [(col_base + i, v) for i, v in sorted(d.items())]

    for table in tables:
        n_vars = heights[table.name]
        offset = table_offsets[table.name]
        col_base = offset >> n_vars
        out.extend(table.boundary_statements(stacked_n_vars, offset, n_vars, ending_pc))
        for point, eq_values, next_values in committed_statements[table.name]:
            if next_values:
                out.append(SparseStatements(stacked_n_vars, list(point), values_at(next_values, col_base), True))
            out.append(SparseStatements(stacked_n_vars, list(point), values_at(eq_values, col_base)))

    return out


def verify_gkr_quotient(fiat_shamir: FiatShamir, n_vars: int) -> tuple[EF, list[EF], EF, EF]:
    assert n_vars > N_VARS_TO_SEND_GKR_COEFFS

    nums = fiat_shamir.next_extension_scalars_vec(1 << N_VARS_TO_SEND_GKR_COEFFS)
    dens = fiat_shamir.next_extension_scalars_vec(1 << N_VARS_TO_SEND_GKR_COEFFS)
    quotient = sum(n * d.inv() for n, d in zip(nums, dens))

    point = fiat_shamir.sample_many_ef(N_VARS_TO_SEND_GKR_COEFFS)
    claim_num = eval_multilinear_evals(nums, point)
    claim_den = eval_multilinear_evals(dens, point)

    for layer_n_vars in range(N_VARS_TO_SEND_GKR_COEFFS, n_vars):
        fiat_shamir.duplex()
        alpha = fiat_shamir.sample_ef()
        raw_pt, sc_value = verify_sumcheck(fiat_shamir, claim_num + alpha * claim_den, layer_n_vars, 3)
        sc_point = list(reversed(raw_pt))
        nl, nr, dl, dr = fiat_shamir.next_extension_scalars_vec(4)
        if sc_value != eq_poly(point, sc_point) * (alpha * dl * dr + nl * dr + nr * dl):
            raise ProofError("GKR step: postponed value mismatch")
        beta = fiat_shamir.sample_ef()
        one_minus = ONE - beta
        claim_num = one_minus * nl + beta * nr
        claim_den = one_minus * dl + beta * dr
        point = sc_point + [beta]

    return quotient, point, claim_num, claim_den


def finger_print(discriminator: Fp | EF, data: Sequence[EF], beta_eq: Sequence[EF]) -> EF:
    assert len(beta_eq) > len(data)
    return dot_product(beta_eq, data) + beta_eq[-1] * discriminator


def sort_tables_by_height(tables: Sequence[Table], heights: dict[str, int]) -> list[tuple[Table, int]]:
    """Descending by height, alphabetical on ties"""
    return sorted([(t, heights[t.name]) for t in tables], key=lambda x: (-x[1], x[0].name))


def verify_generic_logup(
    fiat_shamir: FiatShamir,
    gamma: EF,  # quotient denominator challenge
    beta: list[EF],  # bus-tuple hashing seeds
    beta_eq: list[EF],  # eq(beta, ·) evaluation table
    log_memory: int,
    bytecode_multilinear: list[int],
    tables: Sequence[Table],
    heights: dict[str, int],
) -> dict:
    ds_mem = Fp(LOGUP_MEMORY_DOMAINSEP)
    ds_byte = Fp(LOGUP_BYTECODE_DOMAINSEP)
    log_instr = log2_ceil(N_INSTRUCTION_COLUMNS)
    log_bytecode = log2_strict(len(bytecode_multilinear)) - log_instr

    tables_sorted = sort_tables_by_height(tables, heights)
    tallest_h = tables_sorted[0][1]

    total_active_len = (
        (1 << log_memory) + max(1 << log_bytecode, 1 << tallest_h) + sum(t.n_buses << h for t, h in tables_sorted)
    )
    total_gkr_n_vars = log2_ceil(total_active_len)

    quotient, point_gkr, claim_num, claim_den = verify_gkr_quotient(fiat_shamir, total_gkr_n_vars)
    if quotient != ZERO:
        raise ProofError("logup: GKR sum != 0")

    def pref_at(offset: int, log_height: int) -> EF:
        """Lagrange weight for the layout-offset of a section of height 2^log_height."""
        n_missing = total_gkr_n_vars - log_height
        return eq_at_index(point_gkr, offset >> log_height, n_missing)

    num = den = ZERO

    # Memory section
    mem_pt = point_gkr[-log_memory:]
    pref = pref_at(0, log_memory)
    value_memory_acc = fiat_shamir.next_extension_scalar()
    value_memory = fiat_shamir.next_extension_scalar()
    fp_mem = finger_print(ds_mem, [mle_of_01234567_etc(mem_pt), value_memory], beta_eq)
    num -= pref * value_memory_acc
    den += pref * (gamma - fp_mem)
    offset = 1 << log_memory

    # Bytecode section (padded to the tallest table)
    log_byte_pad = max(log_bytecode, tallest_h)
    byte_pt = point_gkr[-log_bytecode:]
    pref = pref_at(offset, log_bytecode)
    pref_pad = pref_at(offset, log_byte_pad)
    value_bytecode_acc = fiat_shamir.next_extension_scalar()
    bytecode_value = eval_multilinear_evals([Fp(v) for v in bytecode_multilinear], byte_pt + beta[-log_instr:])
    correction = math.prod(ONE - a for a in beta[: len(beta) - log_instr])
    fp_byte = (
        bytecode_value * correction
        + mle_of_01234567_etc(byte_pt) * beta_eq[N_INSTRUCTION_COLUMNS]
        + beta_eq[-1] * ds_byte
    )
    num -= pref * value_bytecode_acc
    den += pref * (gamma - fp_byte) + pref_pad * mle_of_zeros_then_ones(1 << log_bytecode, point_gkr[-log_byte_pad:])
    offset += 1 << log_byte_pad

    # Per-table section
    table_offsets: dict[str, int] = {}
    for table, log_n_rows in tables_sorted:
        table_offsets[table.name] = offset
        offset += table.n_buses << log_n_rows
    final_offset = offset

    bus_num_vals: dict[str, EF] = {}
    bus_den_vals: dict[str, EF] = {}
    columns_values: dict[str, dict[int, EF]] = {}

    for table in tables:
        name = table.name
        log_n_rows = heights[name]
        row_stride = 1 << log_n_rows
        offset_within_table = table_offsets[name]
        table_values: dict[int, EF] = {}

        def read_fresh(cols: list[int]) -> None:
            """Read one extension scalar per column not yet in `table_values`, in order."""
            missing = [c for c in cols if c not in table_values]
            for c, e in zip(missing, fiat_shamir.next_extension_scalars_vec(len(missing))):
                table_values[c] = e

        for bus in table.buses:
            pref = pref_at(offset_within_table, log_n_rows)
            kind = bus[0]
            if kind == BusInteraction.PRECOMPILE:
                bus_num_vals[name] = fiat_shamir.next_extension_scalar()
                bus_den_vals[name] = fiat_shamir.next_extension_scalar()
                num += pref * bus_num_vals[name]
                den += pref * bus_den_vals[name]
                n_sub = 1
            elif kind == BusInteraction.BYTECODE:
                cols = list(range(N_RUNTIME_COLUMNS, N_RUNTIME_COLUMNS + N_INSTRUCTION_COLUMNS)) + [table.col("pc")]
                read_fresh(cols)
                evals = [table_values[c] for c in cols]
                num += pref
                den += pref * (gamma - finger_print(ds_byte, evals, beta_eq))
                n_sub = 1
            elif kind == BusInteraction.MEMORY:
                _, idx_ref, vals_ref, n_sub = bus
                idx_col, vals_start = table.col(idx_ref), table.col(vals_ref)
                # One sub-bus per cell in the group; the prover sends only the not-yet-seen
                # columns per row (idx_col is shared across all n_sub rows).
                for i in range(n_sub):
                    val_col = vals_start + i
                    read_fresh([idx_col, val_col])
                    pref = pref_at(offset_within_table + i * row_stride, log_n_rows)
                    fp = finger_print(ds_mem, [table_values[idx_col] + i, table_values[val_col]], beta_eq)
                    num += pref
                    den += pref * (gamma - fp)
            else:
                raise ProofError(f"unknown bus kind: {kind}")
            offset_within_table += n_sub * row_stride

        columns_values[name] = table_values

    den += mle_of_zeros_then_ones(final_offset, point_gkr)
    if num != claim_num:
        raise ProofError("logup: numerators value mismatch")
    if den != claim_den:
        raise ProofError("logup: denominators value mismatch")

    return {
        "value_memory": value_memory, "value_memory_acc": value_memory_acc,
        "value_bytecode_acc": value_bytecode_acc, "bus_num": bus_num_vals, "bus_den": bus_den_vals,
        "gkr_point": point_gkr, "columns_values": columns_values,
    }  # fmt: skip


class Cols(dict):
    def arr(self, prefix: str, n: int) -> list:
        return [self[f"{prefix}_{i}"] for i in range(n)]


class ConstraintFolder:
    def __init__(
        self, flat: Sequence[EF], shift: Sequence[EF], alpha_powers: Sequence[EF], columns: Sequence[str]
    ) -> None:
        self.flat = list(flat)
        self.shift = list(shift)
        self.alpha_powers = list(alpha_powers)
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


def eval_precompile_bus_virtual_columns(
    folder: "ConstraintFolder",
    logup_beta_eq: list[EF],
    multiplicity: EF,
    discriminator: EF,
    data: Sequence[EF],
) -> None:
    folder.assert_zero(multiplicity)
    folder.assert_zero(finger_print(discriminator, data, logup_beta_eq))


def eval_air_execution(folder: ConstraintFolder, logup_beta_eq: list[EF]) -> None:
    c, n = folder.flat, folder.next
    (pc, fp, addr_a, addr_b, addr_c, value_a, value_b, value_c, operand_a, operand_b, operand_c,
     flag_a, flag_b, flag_c, flag_c_fp, flag_ab_fp, mul, jump, aux, discriminator) = (c[k] for k in (
        "pc", "fp", "addr_a", "addr_b", "addr_c", "value_a", "value_b", "value_c",
        "operand_a", "operand_b", "operand_c", "flag_a", "flag_b", "flag_c", "flag_c_fp",
        "flag_ab_fp", "mul", "jump", "aux", "discriminator"))  # fmt: skip
    pc_shift, fp_shift = n["pc"], n["fp"]

    # nu_x = flag·operand + (1 − flag − flag_ab_fp)·value + flag_ab_fp·(fp + operand)
    nfa = ONE - flag_a - flag_ab_fp
    nfb = ONE - flag_b - flag_ab_fp
    nfc = ONE - flag_c - flag_c_fp
    nu_a = flag_a * operand_a + nfa * value_a + flag_ab_fp * (fp + operand_a)
    nu_b = flag_b * operand_b + nfb * value_b + flag_ab_fp * (fp + operand_b)
    nu_c = flag_c * operand_c + nfc * value_c + flag_c_fp * (fp + operand_c)

    # aux ∈ {0,1,2}: 0=nothing, 1=add, 2=deref.
    add = aux * 2 - aux * aux
    deref = aux * (aux - ONE) * ((P + 1) // 2)  # (P+1)/2 is the inverse of 2 mod P
    is_precompile = ONE - add - mul - deref - jump

    eval_precompile_bus_virtual_columns(folder, logup_beta_eq, is_precompile, discriminator, [nu_a, nu_b, nu_c])
    folder.assert_zero(nfa * (addr_a - (fp + operand_a)))
    folder.assert_zero(nfb * (addr_b - (fp + operand_b)))
    folder.assert_zero(nfc * (addr_c - (fp + operand_c)))
    folder.assert_zero(add * (nu_b - (nu_a + nu_c)))
    folder.assert_zero(mul * (nu_b - nu_a * nu_c))
    folder.assert_zero(deref * (addr_b - (value_a + operand_b)))
    folder.assert_zero(deref * (value_b - nu_c))
    jc = jump * nu_a
    folder.assert_zero(jc * (nu_a - ONE))
    folder.assert_zero(jc * (pc_shift - nu_b))
    folder.assert_zero(jc * (fp_shift - nu_c))
    not_jc = ONE - jc
    folder.assert_zero(not_jc * (pc_shift - (pc + ONE)))
    folder.assert_zero(not_jc * (fp_shift - fp))


def eval_air_extension(folder: ConstraintFolder, logup_beta_eq: list[EF]) -> None:
    c, n = folder.flat, folder.next
    is_be, start, len_col = c["is_be"], c["start"], c["len"]
    flag_add, flag_mul, flag_poly_eq = c["flag_add"], c["flag_mul"], c["flag_poly_eq"]
    idx_a, idx_b, idx_res = c["idx_a"], c["idx_b"], c["idx_res"]
    comp, va, vb, vres = c.arr("comp", 5), c.arr("va", 5), c.arr("vb", 5), c.arr("vres", 5)
    is_be_sh, start_sh, len_sh = n["is_be"], n["start"], n["len"]
    flag_add_sh, flag_mul_sh, flag_poly_eq_sh = n["flag_add"], n["flag_mul"], n["flag_poly_eq"]
    idx_a_sh, idx_b_sh = n["idx_a"], n["idx_b"]
    comp_sh = n.arr("comp", 5)

    aux = (
        is_be * EXT_OP_FLAG_IS_BE
        + flag_add * EXT_OP_FLAG_ADD
        + flag_mul * EXT_OP_FLAG_MUL
        + flag_poly_eq * EXT_OP_FLAG_POLY_EQ
        + len_col * EXT_OP_LEN_MULTIPLIER
    )
    eval_precompile_bus_virtual_columns(
        folder, logup_beta_eq, start * (flag_add + flag_mul + flag_poly_eq), aux, [idx_a, idx_b, idx_res]
    )

    for x in (is_be, start, flag_add, flag_mul, flag_poly_eq):
        folder.assert_bool(x)

    is_ee, not_start_sh = ONE - is_be, ONE - start_sh
    va_x = [va[0]] + [va[k] * is_ee for k in range(1, 5)]
    comp_tail = [comp_sh[k] * not_start_sh for k in range(5)]
    va_vb = quintic_mul(va_x, vb, ZERO)

    for k in range(5):
        folder.assert_zero((comp[k] - (va_x[k] + vb[k] + comp_tail[k])) * flag_add)
    for k in range(5):
        folder.assert_zero((comp[k] - (va_vb[k] + comp_tail[k])) * flag_mul)

    # poly_eq: comp ← (2·va·vb − va − vb + 1) · comp_sh_or_one.
    poly_eq_val = [2 * va_vb[k] - va_x[k] - vb[k] + (ONE if k == 0 else ZERO) for k in range(5)]
    comp_sh_or_one = [comp_sh[0] * not_start_sh + start_sh] + [comp_sh[k] * not_start_sh for k in range(1, 5)]
    poly_eq_result = quintic_mul(poly_eq_val, comp_sh_or_one, ZERO)
    for k in range(5):
        folder.assert_zero((comp[k] - poly_eq_result[k]) * flag_poly_eq)
    for k in range(5):
        folder.assert_zero((comp[k] - vres[k]) * start)

    for x, y in [
        (len_col, len_sh + ONE),
        (is_be, is_be_sh),
        (flag_add, flag_add_sh),
        (flag_mul, flag_mul_sh),
        (flag_poly_eq, flag_poly_eq_sh),
    ]:
        folder.assert_zero(not_start_sh * (x - y))

    folder.assert_zero(not_start_sh * (idx_a_sh - idx_a - (is_be + is_ee * 5)))
    folder.assert_zero(not_start_sh * (idx_b_sh - idx_b - 5))
    folder.assert_zero(start_sh * (len_col - ONE))


def _full_round(state: list[EF], rc1: list[Fp], rc2: list[Fp]) -> list[EF]:
    """Two consecutive Poseidon full rounds, fused as one AIR step."""
    for rc in (rc1, rc2):
        sbox = [(s + c).cube() for s, c in zip(state, rc)]
        state = [dot_product(sbox, row) for row in POSEIDON_AIR_MDS_DENSE]
    return state


def eval_air_poseidon16(folder: ConstraintFolder, logup_beta_eq: list[EF]) -> None:
    c = folder.flat
    half_pairs = POSEIDON_HALF_FULL_ROUNDS // 2

    multiplicity = c["multiplicity"]
    index_b, index_res = c["index_b"], c["index_res"]
    flag_half_output, flag_hardcoded_left = c["flag_half_output"], c["flag_hardcoded_left"]
    offset_hardcoded_left = c["offset_hardcoded_left"]
    eff_idx_left_first, eff_idx_left_second = c["eff_idx_left_first"], c["eff_idx_left_second"]
    flag_permute = c["flag_permute"]
    inputs = c.arr("input", POSEIDON_WIDTH)
    beginning_full_rounds = [c.arr(f"begin_r{r}", POSEIDON_WIDTH) for r in range(half_pairs)]
    partial_cols = c.arr("partial", POSEIDON_PARTIAL_ROUNDS)
    ending_full_rounds = [c.arr(f"end_r{r}", POSEIDON_WIDTH) for r in range(half_pairs - 1)]
    outputs_left = c.arr("out_left", POSEIDON_WIDTH // 2)
    outputs_right = c.arr("out_right", POSEIDON_WIDTH // 2)

    discriminator = (
        POSEIDON_DISCRIMINATOR_BASE
        + flag_permute * POSEIDON_PERMUTE_SHIFT
        + flag_half_output * POSEIDON_HALF_OUTPUT_SHIFT
        + flag_hardcoded_left * POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT
        + flag_hardcoded_left * offset_hardcoded_left * POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT
    )
    not_hcl = ONE - flag_hardcoded_left
    index_a = eff_idx_left_second - not_hcl * (DIGEST_ELEMS // 2)

    eval_precompile_bus_virtual_columns(
        folder, logup_beta_eq, multiplicity, discriminator, [index_a, index_b, index_res]
    )
    for f in (multiplicity, flag_half_output, flag_hardcoded_left, flag_permute):
        folder.assert_bool(f)
    folder.assert_zero(flag_permute * (flag_half_output + flag_hardcoded_left))
    folder.assert_zero(flag_hardcoded_left * (offset_hardcoded_left - eff_idx_left_first))
    folder.assert_zero(not_hcl * (index_a - eff_idx_left_first))

    # --- Poseidon1-16 permutation AIR: each committed `post` row pins the intermediate
    # state then re-binds it, capping polynomial degree across the long round sequence.
    state = list(inputs)

    # Beginning full rounds, paired up.
    for r in range(half_pairs):
        state = _full_round(state, POSEIDON_AIR_INITIAL_CONSTANTS[2 * r], POSEIDON_AIR_INITIAL_CONSTANTS[2 * r + 1])
        for i, post in enumerate(beginning_full_rounds[r]):
            folder.assert_eq(state[i], post)
            state[i] = post

    # Transition into sparse partial-round form.
    state = [s + rc for s, rc in zip(state, POSEIDON_AIR_SPARSE_FIRST_RC)]
    state = [dot_product(state, row) for row in POSEIDON_AIR_SPARSE_M_I]

    # Partial rounds: one sbox on lane 0, then sparse mat-vec.
    for r in range(POSEIDON_PARTIAL_ROUNDS):
        folder.assert_eq(state[0].cube(), partial_cols[r])
        state[0] = partial_cols[r]
        if r < POSEIDON_PARTIAL_ROUNDS - 1:
            state[0] += POSEIDON_AIR_SPARSE_SCALAR_RC[r]
        old_s0 = state[0]
        state[0] = dot_product(state, POSEIDON_AIR_SPARSE_FIRST_ROW[r])
        for i in range(1, POSEIDON_WIDTH):
            state[i] += old_s0 * POSEIDON_AIR_SPARSE_V[r][i - 1]

    # Ending full rounds (all but the last pair) commit intermediate state.
    for r in range(half_pairs - 1):
        state = _full_round(state, POSEIDON_AIR_FINAL_CONSTANTS[2 * r], POSEIDON_AIR_FINAL_CONSTANTS[2 * r + 1])
        for i, post in enumerate(ending_full_rounds[r]):
            folder.assert_eq(state[i], post)
            state[i] = post

    # Last full round: compression mode adds `inputs` back (gated by flag_half_output for lanes 4..8);
    # permute mode (flag_permute=1) outputs raw state.
    last = 2 * (half_pairs - 1)
    state = _full_round(state, POSEIDON_AIR_FINAL_CONSTANTS[last], POSEIDON_AIR_FINAL_CONSTANTS[last + 1])
    not_permute = ONE - flag_permute
    compression_last4 = not_permute - flag_half_output
    for i in range(POSEIDON_WIDTH // 2):
        gate = not_permute if i < (DIGEST_ELEMS // 2) else compression_last4
        folder.assert_zero(gate * (state[i] + inputs[i] - outputs_left[i]))
        folder.assert_zero(flag_permute * (state[i] - outputs_left[i]))
        folder.assert_zero(flag_permute * (state[i + POSEIDON_WIDTH // 2] - outputs_right[i]))


EXECUTION_COLUMNS = (
    "pc", "fp", "addr_a", "addr_b", "addr_c", "value_a", "value_b", "value_c", # 8 runtime cols
    "operand_a", "operand_b", "operand_c", "flag_a", "flag_b", "flag_c", "flag_c_fp", "flag_ab_fp", "mul", "jump", "aux", "discriminator", # 12 instruction cols.
)  # fmt: skip

EXTENSION_COLUMNS = (
    "is_be", "start", "len", "flag_add", "flag_mul", "flag_poly_eq", "idx_a", "idx_b",
    *(f"comp_{i}" for i in range(5)),
    "idx_res",
    *(f"va_{i}" for i in range(5)),
    *(f"vb_{i}" for i in range(5)),
    *(f"vres_{i}" for i in range(5)),
)  # fmt: skip

POSEIDON_COLUMNS = (
    "multiplicity", "index_b", "index_res", "flag_half_output", "flag_hardcoded_left", "offset_hardcoded_left", "eff_idx_left_first", "eff_idx_left_second", "flag_permute",
    *(f"input_{i}" for i in range(POSEIDON_WIDTH)),
    *(f"begin_r{r}_{i}" for r in range(POSEIDON_HALF_FULL_ROUNDS // 2) for i in range(POSEIDON_WIDTH)),
    *(f"partial_{i}" for i in range(POSEIDON_PARTIAL_ROUNDS)),
    *(f"end_r{r}_{i}" for r in range(POSEIDON_HALF_FULL_ROUNDS // 2 - 1) for i in range(POSEIDON_WIDTH)),
    *(f"out_left_{i}" for i in range(POSEIDON_WIDTH // 2)),
    *(f"out_right_{i}" for i in range(POSEIDON_WIDTH // 2)),
)  # fmt: skip

TABLES = [
    Table(
        name="execution",
        columns=EXECUTION_COLUMNS,
        buses=(
            (BusInteraction.PRECOMPILE, BusDirection.PUSH),
            (BusInteraction.BYTECODE,),
            (BusInteraction.MEMORY, "addr_a", "value_a", 1),
            (BusInteraction.MEMORY, "addr_b", "value_b", 1),
            (BusInteraction.MEMORY, "addr_c", "value_c", 1),
        ),
        air_degree=5,
        n_constraints=14,
        n_shift=2,
        max_log_height=24,
        air_constraints_fn=eval_air_execution,
    ),
    Table(
        name="extension",
        columns=EXTENSION_COLUMNS,
        buses=(
            (BusInteraction.PRECOMPILE, BusDirection.PULL),
            (BusInteraction.MEMORY, "idx_a", "va_0", 5),
            (BusInteraction.MEMORY, "idx_b", "vb_0", 5),
            (BusInteraction.MEMORY, "idx_res", "vres_0", 5),
        ),
        air_degree=6,
        n_constraints=35,
        n_shift=13,
        max_log_height=21,
        air_constraints_fn=eval_air_extension,
    ),
    Table(
        name="poseidon",
        columns=POSEIDON_COLUMNS,
        buses=(
            (BusInteraction.PRECOMPILE, BusDirection.PULL),
            (BusInteraction.MEMORY, "eff_idx_left_first", "input_0", 4),
            (BusInteraction.MEMORY, "eff_idx_left_second", "input_4", 4),
            (BusInteraction.MEMORY, "index_b", "input_8", 8),
            (BusInteraction.MEMORY, "index_res", "out_left_0", 16),
        ),
        air_degree=10,
        n_constraints=101,
        n_shift=0,
        max_log_height=21,
        air_constraints_fn=eval_air_poseidon16,
    ),
]


def verify_execution(
    public_input: Sequence[Fp],
    proof: Proof,
    bytecode_multilinear: list[int],
):
    bytecode_log_size = log2_strict(len(bytecode_multilinear)) - log2_ceil(N_INSTRUCTION_COLUMNS)
    ending_pc = (1 << bytecode_log_size) - 1
    bytecode_hash = sponge_hash([Fp(v) for v in bytecode_multilinear])
    if len(public_input) != PUBLIC_INPUT_SIZE:
        raise ProofError("InvalidProof: public_input length mismatch")

    state = FiatShamir(proof, poseidon16_compress(bytecode_hash, SNARK_DOMAIN_SEP))  # domain separator across bytecodes
    state.observe_scalars(public_input)
    dims = [int(x.value) for x in state.next_base_scalars_vec(2 + len(TABLES))]
    log_inv_rate, log_memory, *table_log_n_rows = dims
    if not MIN_WHIR_LOG_INV_RATE <= log_inv_rate <= MAX_WHIR_LOG_INV_RATE:
        raise ProofError("InvalidRate")
    if not MIN_LOG_MEMORY_SIZE <= log_memory <= MAX_LOG_MEMORY_SIZE:
        raise ProofError("InvalidProof: log_memory out of range")
    if not MIN_BYTECODE_LOG_SIZE <= bytecode_log_size <= MAX_BYTECODE_LOG_SIZE:
        raise ProofError("InvalidProof: bytecode log_size out of range")
    if log_memory < max(max(table_log_n_rows, default=0), bytecode_log_size):
        raise ProofError("InvalidProof: memory smaller than tables/bytecode")
    for table, log_height in zip(TABLES, table_log_n_rows):
        if not MIN_LOG_N_ROWS_PER_TABLE <= log_height <= table.max_log_height:
            raise ProofError(
                f"InvalidProof: table {table.name} log_n_rows={log_height} not in [{MIN_LOG_N_ROWS_PER_TABLE}, {table.max_log_height}]"
            )

    log_heights = {t.name: h for t, h in zip(TABLES, table_log_n_rows)}
    n_max = sort_tables_by_height(TABLES, log_heights)[0][1]

    total_stacked = (
        (2 << log_memory)
        + (1 << max(bytecode_log_size, n_max))
        + sum(t.n_columns << log_heights[t.name] for t in TABLES)
    )

    stacked_n_vars = log2_ceil(total_stacked)
    if stacked_n_vars > TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate:
        raise ProofError("InvalidProof: stacked_n_vars exceeds WHIR domain bound")
    cfg = WHIR_CONFIGS[(log_inv_rate, stacked_n_vars)]
    nood = cfg["commitment_ood_samples"]
    parsed_commitment = ParsedCommitment(
        stacked_n_vars,
        state.next_base_scalars_vec(DIGEST_ELEMS),
        state.sample_many_ef(nood),
        state.next_extension_scalars_vec(nood),
    )

    logup_gamma = state.sample_ef()  # the quotient denominator
    state.duplex()
    logup_beta = state.sample_many_ef(log2_ceil(N_INSTRUCTION_COLUMNS + 2))  # the bus-tuple hashing seeds
    logup_beta_eq = eval_eq(logup_beta)
    logup = verify_generic_logup(
        state,
        logup_gamma,
        logup_beta,
        logup_beta_eq,
        log_memory,
        bytecode_multilinear,
        TABLES,
        log_heights,
    )
    gkr_point = logup["gkr_point"]

    air_alpha = state.sample_ef()
    alpha_powers = ef_powers(air_alpha, sum(t.n_constraints for t in TABLES))

    initial_sum, offset = ZERO, 0
    for table in TABLES:
        initial_sum += alpha_powers[offset] * (logup["bus_num"][table.name] * table.precompile_bus_interraction_sign)
        initial_sum += alpha_powers[offset + 1] * (logup_gamma - logup["bus_den"][table.name])
        offset += table.n_constraints
    sc_point, sc_value = verify_sumcheck(state, initial_sum, n_max, max(t.air_degree + 1 for t in TABLES))

    committed = {t.name: [(gkr_point[-log_heights[t.name] :], logup["columns_values"][t.name], {})] for t in TABLES}
    my_air_final, offset = ZERO, 0
    for table in TABLES:
        log_n_rows = log_heights[table.name]
        col_evals = state.next_extension_scalars_vec(table.n_columns + table.n_shift)
        alphas = alpha_powers[offset : offset + table.n_constraints]
        offset += table.n_constraints
        constraint_eval = table.eval_air(col_evals, alphas, logup_beta_eq)

        natural_pt = list(reversed(sc_point[-log_n_rows:])) if log_n_rows else []
        k_t = math.prod(sc_point[: n_max - log_n_rows])
        my_air_final += k_t * eq_poly(gkr_point[-log_n_rows:], natural_pt) * constraint_eval

        eq_vals = {i: col_evals[i] for i in range(table.n_columns)}
        next_vals = {j: col_evals[table.n_columns + j] for j in range(table.n_shift)}
        committed[table.name].append((natural_pt, eq_vals, next_vals))
    if my_air_final != sc_value:
        raise ProofError("AIR sumcheck: claimed value mismatch")

    pm_point = state.sample_many_ef(log2_strict(PUBLIC_INPUT_SIZE))
    pm_eval = eval_multilinear_evals(public_input, pm_point)

    bytecode_acc_idx = (2 << log_memory) >> bytecode_log_size
    previous_statements = [
        SparseStatements(
            stacked_n_vars,
            gkr_point[-log_memory:],
            [(0, logup["value_memory"]), (1, logup["value_memory_acc"])],
        ),
        SparseStatements(stacked_n_vars, pm_point, [(0, pm_eval)]),
        SparseStatements(
            stacked_n_vars, gkr_point[-bytecode_log_size:], [(bytecode_acc_idx, logup["value_bytecode_acc"])]
        ),
    ]
    global_statements = stacked_pcs_global_statements(
        stacked_n_vars,
        log_memory,
        bytecode_log_size,
        previous_statements,
        TABLES,
        log_heights,
        committed,
        ending_pc,
    )
    whir_verify(state, cfg, parsed_commitment, global_statements)

    if state.offset != len(state.transcript):
        raise ProofError(
            f"InvalidProof: transcript not fully consumed ({state.offset}/{len(state.transcript)} scalars read)"
        )
    if state.openings:
        raise ProofError(f"InvalidProof: {len(state.openings)} Merkle openings unused")


def main() -> int:
    vector_path = Path(__file__).resolve().parents[3] / "target" / "zkvm_test_vectors" / "proof.json"
    if not vector_path.exists():
        print(
            f"Test vector not found at {vector_path}. Please follow the instructions at the beginning of verifier.py file."
        )
        return 1

    print(f"Loading {vector_path.name}...")
    raw = json.loads(vector_path.read_text())
    print("... done")

    arr = array.array("I")
    arr.frombytes((vector_path.parent / raw["bytecode_multilinear_path"]).read_bytes())
    bytecode_multilinear: list[int] = list(arr)

    fp_list = lambda xs: [Fp(v) for v in xs]
    public_input = fp_list(raw["public_input"])
    proof = Proof(
        transcript=fp_list(raw["proof"]["transcript"]),
        merkle_openings=[
            MerkleOpening(leaf_data=fp_list(o["leaf_data"]), path=[fp_list(d) for d in o["path"]])
            for o in raw["proof"]["merkle_openings"]
        ],
    )

    try:
        verify_execution(public_input, proof, bytecode_multilinear)
    except ProofError as e:
        print(f"FAIL: {e}")
        return 1

    print(f"Proof successfully verified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
