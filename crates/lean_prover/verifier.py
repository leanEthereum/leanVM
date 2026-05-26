"""Pure-Python verifier for leanVM proofs.
Setup the test vector (one-time):
    cargo test --release -p lean_prover dump_test_vector_for_python_verifier -- --nocapture
Run:
    python3 crates/lean_prover/verifier.py
Format:
    ruff format --line-length 120 crates/lean_prover
"""

from __future__ import annotations
import array
import json
import math
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence
from primitives import *


PUBLIC_INPUT_SIZE = DIGEST_ELEMS
SNARK_DOMAIN_SEP = [Fp(v) for v in (130704175, 1303721200, 493664240, 1035493700, 2063844858, 1410214009, 1938905908, 1696767928)]  # fmt: skip

WHIR_INITIAL_FOLDING_FACTOR, WHIR_SUBSEQUENT_FOLDING_FACTOR, WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS = 7, 5, 8
MIN_WHIR_LOG_INV_RATE, MAX_WHIR_LOG_INV_RATE, RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 1, 4, 5
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
    for c in ((1,7,1,10,220,16,()),(1,8,1,11,220,16,()),(1,9,1,12,220,16,()),(1,10,1,13,220,16,()),(1,11,1,14,220,16,()),(1,12,1,15,220,16,()),(1,13,1,16,220,16,()),(1,14,1,15,221,16,()),(1,15,1,16,221,16,()),(1,16,1,16,73,16,((222,1,16,11),)),(1,17,1,16,73,16,((223,1,16,12),)),(1,18,1,16,73,16,((224,1,16,13),)),(1,19,1,16,73,16,((225,1,16,14),)),(1,20,1,16,73,16,((227,1,16,15),)),(1,21,2,16,32,16,((229,1,16,16),(73,1,16,9))),(1,22,2,16,32,16,((230,1,16,12),(74,1,16,10))),(1,23,2,16,32,16,((234,1,16,13),(74,1,16,11))),(1,24,2,16,32,16,((235,1,16,14),(74,1,16,12))),(1,25,2,16,32,16,((241,2,16,15),(74,2,16,13))),(1,26,2,16,21,14,((243,2,16,16),(74,2,16,14),(32,2,16,14))),(1,27,2,16,21,14,((248,2,16,15),(75,2,16,15),(32,2,16,15))),(1,28,2,16,21,14,((256,2,16,16),(75,2,16,16),(32,2,16,16))),(1,29,2,16,21,14,((262,2,16,15),(76,2,16,12),(33,2,16,17))),(1,30,2,16,21,14,((270,2,16,16),(76,2,16,13),(33,2,16,18))),(2,7,1,13,109,16,()),(2,8,1,14,109,16,()),(2,9,1,15,109,16,()),(2,10,1,16,109,16,()),(2,11,1,12,110,16,()),(2,12,1,13,110,16,()),(2,13,1,14,110,16,()),(2,14,1,15,110,16,()),(2,15,1,16,110,16,()),(2,16,1,14,55,16,((111,1,16,10),)),(2,17,1,15,55,16,((111,1,16,11),)),(2,18,1,16,55,16,((111,1,16,12),)),(2,19,1,15,55,16,((112,1,16,13),)),(2,20,2,16,55,16,((112,1,16,14),)),(2,21,2,16,28,16,((113,1,16,15),(55,1,16,10))),(2,22,2,15,28,16,((114,1,16,16),(55,1,16,11))),(2,23,2,16,28,16,((114,1,16,13),(56,1,16,12))),(2,24,2,16,28,16,((115,1,16,14),(56,2,16,13))),(2,25,2,15,28,16,((118,2,16,15),(56,2,16,14))),(2,26,2,16,19,15,((118,2,16,16),(56,2,16,15),(28,2,16,17))),(2,27,2,16,19,15,((119,2,16,13),(57,2,16,16),(28,2,16,18))),(2,28,2,16,19,15,((120,2,16,14),(57,2,16,14),(29,2,15,19))),(2,29,2,16,19,15,((123,2,16,15),(57,2,16,15),(29,2,15,20))),(3,7,1,9,73,16,()),(3,8,1,10,73,16,()),(3,9,1,11,73,16,()),(3,10,1,12,73,16,()),(3,11,1,13,73,16,()),(3,12,1,14,73,16,()),(3,13,1,15,73,16,()),(3,14,1,16,73,16,()),(3,15,1,12,74,16,()),(3,16,1,13,44,16,((74,1,16,11),)),(3,17,1,14,44,16,((74,1,16,12),)),(3,18,2,15,44,16,((74,1,16,13),)),(3,19,2,16,44,16,((74,1,16,14),)),(3,20,2,15,44,16,((75,1,16,15),)),(3,21,2,16,25,16,((75,1,16,16),(44,1,16,11))),(3,22,2,15,25,16,((76,1,16,11),(45,1,16,12))),(3,23,2,16,25,16,((76,1,16,12),(45,2,16,13))),(3,24,2,16,25,16,((77,2,16,13),(45,2,16,14))),(3,25,2,16,25,16,((78,2,15,14),(45,2,16,15))),(3,26,2,16,18,12,((79,2,15,15),(45,2,16,16),(25,2,16,19))),(3,27,2,16,18,12,((80,2,16,16),(45,2,16,15),(26,2,13,20))),(3,28,2,15,18,12,((82,2,15,15),(46,2,16,16),(26,2,13,21))),(4,7,1,8,55,16,()),(4,8,1,9,55,16,()),(4,9,1,10,55,16,()),(4,10,1,11,55,16,()),(4,11,1,12,55,16,()),(4,12,1,13,55,16,()),(4,13,1,14,55,16,()),(4,14,1,15,55,16,()),(4,15,1,16,55,16,()),(4,16,1,13,37,16,((56,1,16,9),)),(4,17,1,14,37,16,((56,1,16,10),)),(4,18,2,15,37,16,((56,1,16,11),)),(4,19,2,16,37,16,((56,1,16,12),)),(4,20,2,13,37,16,((57,1,16,13),)),(4,21,2,14,23,15,((57,2,16,14),(37,2,16,12))),(4,22,2,15,23,15,((57,2,16,15),(37,2,16,13))),(4,23,2,16,23,15,((57,2,16,16),(37,2,16,14))),(4,24,2,15,23,15,((58,2,16,13),(38,2,16,15))),(4,25,2,16,23,15,((58,2,16,14),(38,2,16,16))),(4,26,2,16,16,16,((60,2,15,15),(38,2,16,17),(23,2,15,22))),(4,27,2,15,16,16,((61,2,16,16),(38,2,16,18),(23,2,15,23))))
}  # fmt: skip

MIN_LOG_MEMORY_SIZE, MAX_LOG_MEMORY_SIZE = 16, 26
MIN_LOG_N_ROWS_PER_TABLE, MIN_BYTECODE_LOG_SIZE, MAX_BYTECODE_LOG_SIZE = 8, 8, 22
MAX_LOG_N_ROWS_PER_TABLE = {"execution": 24, "extension": 21, "poseidon": 21}
ALL_TABLES_ORDER = ("execution", "extension", "poseidon")
N_VARS_TO_SEND_GKR_COEFFS = 5

N_RUNTIME_COLUMNS, N_INSTRUCTION_COLUMNS, PC_COL_INDEX = 8, 12, 0

LOGUP_MEMORY_DOMAINSEP, LOGUP_BYTECODE_DOMAINSEP = 1, 2
POSEIDON_DISCRIMINATOR_BASE = 3  # odd ≥ 3
POSEIDON_PERMUTE_SHIFT, POSEIDON_HALF_OUTPUT_SHIFT = 1 << 1, 1 << 2
POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT, POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT = (
    1 << 3,
    1 << 4,
)


STARTING_PC = 0  # every program starts at PC = 0, and ends at PC = len(bytecode) - 1

POSEIDON_WIDTH, POSEIDON_FULL_ROUNDS, POSEIDON_PARTIAL_ROUNDS = 16, 8, 20


class ProofError(Exception):
    pass


# T-Sponge (compression instead of permutation) with replacement (instead of xoring / adding the ingested data).
def sponge_hash(data: Sequence[Fp]) -> list[Fp]:
    assert len(data) % SPONGE_RATE == 0 and len(data) > 0
    state = [Fp(len(data))] + [Fp(0)] * (SPONGE_CAPACITY - 1)  # IV = [size, 0, 0, 0, ..., 0]
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
        return list(self.state[SPONGE_CAPACITY:])

    def _sample_many(self, n: int) -> list[Fp]:
        out: list[Fp] = []
        for i in range(n):
            if i:
                self.duplex()
            out.extend(self._sample_rate())
        return out

    def sample_many_ef(self, n: int) -> list[EF]:
        flat = self._sample_many((n * EF.DIMENSION + SPONGE_RATE - 1) // SPONGE_RATE)[: n * EF.DIMENSION]
        return [EF(flat[i : i + EF.DIMENSION]) for i in range(0, len(flat), EF.DIMENSION)]

    def sample_ef(self) -> EF:
        return self.sample_many_ef(1)[0]

    def sample_in_range(self, bits: int, n_samples: int) -> list[int]:
        assert bits < 31
        flat = self._sample_many((n_samples + SPONGE_RATE - 1) // SPONGE_RATE)[:n_samples]
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
        return [EF(flat[i : i + EF.DIMENSION]) for i in range(0, len(flat), EF.DIMENSION)]

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


def dot_product(a: Sequence, b: Sequence):
    return sum(x * y for x, y in zip(a, b))


def next_mle(x: Sequence[EF], y: Sequence[EF]) -> EF:
    assert len(x) == len(y)
    s, eq_prefix = ZERO, ONE
    for xi, yi in zip(x, y):
        s = xi * (ONE - yi) * s + eq_prefix * (ONE - xi) * yi
        eq_prefix *= xi * yi + (ONE - xi) * (ONE - yi)
    return s + math.prod([*x, *y])


def eval_multilinear_evals(evals: Sequence[EF], point: Sequence[EF]) -> EF:
    """Evaluate a multilinear in evaluation form at `point`."""
    assert len(evals) == 1 << len(point)
    cur = list(evals)
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


@dataclass
class SparseStatements:
    total_num_variables: int
    point: list[EF]
    values: list[tuple[int, EF]]
    is_next: bool = False

    @property
    def selector_num_variables(self) -> int:
        return self.total_num_variables - len(self.point)

    @staticmethod
    def dense(point: list[EF], value: EF) -> "SparseStatements":
        return SparseStatements(len(point), point, [(0, value)])

    @staticmethod
    def unique_value(total: int, index: int, value: EF) -> "SparseStatements":
        return SparseStatements(total, [], [(index, value)])

    @staticmethod
    def new_next(total: int, point: list[EF], values: list[tuple[int, EF]]) -> "SparseStatements":
        return SparseStatements(total, point, values, is_next=True)


def whir_folding_factor_at_round(r: int) -> int:
    return WHIR_INITIAL_FOLDING_FACTOR if r == 0 else WHIR_SUBSEQUENT_FOLDING_FACTOR


def whir_n_rounds_and_final_sumcheck(num_variables: int) -> tuple[int, int]:
    nv = num_variables - WHIR_INITIAL_FOLDING_FACTOR
    if nv < WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS:
        return 0, nv
    n = -(-(nv - WHIR_MAX_NUM_VARIABLES_TO_SEND_COEFFS) // WHIR_SUBSEQUENT_FOLDING_FACTOR)
    return n, nv - n * WHIR_SUBSEQUENT_FOLDING_FACTOR


@dataclass
class ParsedCommitment:
    num_variables: int
    root: list[Fp]
    ood_points: list[EF]
    ood_answers: list[EF]

    def oods_constraints(self) -> list[SparseStatements]:
        return [
            SparseStatements.dense(expand_from_univariate(p, self.num_variables), ev)
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
        leaf = op.leaf_data
        if round_index == 0:
            packed = [EF(f) for f in leaf]
        else:
            packed = [EF(leaf[i : i + EF.DIMENSION]) for i in range(0, len(leaf), EF.DIMENSION)]
        fold = eval_multilinear_evals(packed, folding_randomness)
        ef_pt = EF(pow(int(gen.value), idx, P))
        constraints.append(SparseStatements.dense(expand_from_univariate(ef_pt, num_variables), fold))
    return constraints


def eval_constraints_poly(constraints: list[tuple[list[EF], list[SparseStatements]]], point: list[EF]) -> EF:
    value = ZERO
    pt = list(point)
    for round_idx, (randomness, smts) in enumerate(constraints):
        if round_idx > 0:
            pt = pt[whir_folding_factor_at_round(round_idx - 1) :]
        i = 0
        for smt in smts:
            inner_pt = pt[len(pt) - len(smt.point) :]
            common = next_mle(smt.point, inner_pt) if smt.is_next else eq_poly(smt.point, inner_pt)
            sel_n = smt.selector_num_variables
            for v in smt.values:
                lagrange = math.prod(pt[j] if (v[0] >> (sel_n - 1 - j)) & 1 else ONE - pt[j] for j in range(sel_n))
                value = value + lagrange * common * randomness[i]
                i += 1
        assert i == len(randomness)
    return value


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
        # Fold each constraint value into `target` via successive powers of γ.
        gamma = fiat_shamir.sample_ef()
        combo: list[EF] = []
        g = ONE
        for smt in constraints:
            for _, value in smt.values:
                target = target + g * value
                combo.append(g)
                g = g * gamma
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
    # Each STIR constraint's point is `expand_from_univariate(α, n)` = [α, α², α⁴, …]; check that `Σ coeffs[i]·α^i == value`.
    for smt in final_stir:
        assert smt.selector_num_variables == 0
        univ_eval = eval_univariate_polynomial(final_coeffs, smt.point[0])
        if any(univ_eval != v[1] for v in smt.values):
            raise ProofError("Final STIR constraint mismatch")

    final_sc_point, final_sc_value = verify_sumcheck(fiat_shamir, target, final_sumcheck_rounds, 2)
    round_folding.append(final_sc_point)

    folding_flat = [r for chunk in round_folding for r in chunk]
    eval_weights = eval_constraints_poly(round_constraints, folding_flat)
    final_value = eval_multilinear_coeffs(final_coeffs, list(reversed(final_sc_point)))
    if final_sc_value != eval_weights * final_value:
        raise ProofError("WHIR final sumcheck check failed")

    return folding_flat


# poseidon16_compress: 9 scalars + WIDTH inputs + (ROUNDS_F/2) pairs of WIDTH cols (begin + end-1 + outputs) + partial.
_POSEIDON_N_COLS = 9 + POSEIDON_WIDTH + POSEIDON_WIDTH * (POSEIDON_FULL_ROUNDS // 2) + POSEIDON_PARTIAL_ROUNDS
TABLE_BUSES = {
    "execution": (
        ("col_mult", "Push"),
        ("byte_lookup",),
        ("mem_group", 2, 5, 1),  # addr_a, value_a
        ("mem_group", 3, 6, 1),  # addr_b, value_b
        ("mem_group", 4, 7, 1),  # addr_c, value_c
    ),
    "extension": (
        ("col_mult", "Pull"),
        ("mem_group", 6, 14, 5),  # idx_a,   va
        ("mem_group", 7, 19, 5),  # idx_b,   vb
        ("mem_group", 13, 24, 5),  # idx_res, vres
    ),
    "poseidon": (
        ("col_mult", "Pull"),
        ("mem_group", 6, 9, 4),
        ("mem_group", 7, 13, 4),
        ("mem_group", 1, 17, 8),
        ("mem_group", 2, _POSEIDON_N_COLS - 16, 16),
    ),
}


@dataclass(frozen=True)
class TableMeta:
    name: str
    n_columns: int
    buses: tuple
    air_degree: int  # max degree of AIR transition constraints
    n_constraints: int
    n_shift: int  # number of shift (next-row) columns
    air_fn: object  # (folder, extra_data) -> None, fills folder with AIR constraints

    @property
    def n_buses(self) -> int:
        # mem_group entries expand to `n` individual buses.
        return sum(b[3] if b[0] == "mem_group" else 1 for b in self.buses)


def stacked_pcs_global_statements(
    stacked_n_vars: int,
    memory_n_vars: int,
    bytecode_n_vars: int,
    previous_statements: list[SparseStatements],
    table_log_heights: dict[str, int],
    committed_statements: dict[str, list[tuple[list[EF], dict[int, EF], dict[int, EF]]]],
    tables: dict[str, TableMeta],
    ending_pc: int,
) -> list[SparseStatements]:
    assert len(table_log_heights) == len(committed_statements)
    tables_sorted = sort_tables_by_height(table_log_heights)

    # Layout offsets are assigned in sorted-by-height order (taller tables come first
    # in the stacked polynomial), but statements are emitted in canonical ALL_TABLES order.
    table_offsets: dict[str, int] = {}
    layout_offset = (2 << memory_n_vars) + (1 << max(bytecode_n_vars, tables_sorted[0][1]))
    for name, n_vars in tables_sorted:
        table_offsets[name] = layout_offset
        layout_offset += tables[name].n_columns << n_vars

    out = list(previous_statements)

    # Rust uses BTreeMap (sorted by key); Python dicts are insertion-ordered, sort here.
    def values_at(d: dict[int, EF], col_base: int) -> list[tuple[int, EF]]:
        return [(col_base + i, v) for i, v in sorted(d.items())]

    for name in ALL_TABLES_ORDER:
        n_vars = table_log_heights[name]
        offset = table_offsets[name]
        col_base = offset >> n_vars
        if name == "execution":
            # PC column: pin first row to STARTING_PC, last row to ending_pc.
            for idx, pc in [(0, STARTING_PC), ((1 << n_vars) - 1, ending_pc)]:
                out.append(
                    SparseStatements.unique_value(stacked_n_vars, offset + (PC_COL_INDEX << n_vars) + idx, EF(pc))
                )
        for point, eq_values, next_values in committed_statements[name]:
            if next_values:
                out.append(SparseStatements.new_next(stacked_n_vars, list(point), values_at(next_values, col_base)))
            out.append(SparseStatements(stacked_n_vars, list(point), values_at(eq_values, col_base)))

    return out


def verify_gkr_quotient(fiat_shamir: FiatShamir, n_vars: int) -> tuple[EF, list[EF], EF, EF]:
    """Layered sumcheck for `Σ nᵢ/dᵢ`. Returns `(quotient, point, claim_num, claim_den)`."""
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


def mle_of_01234567_etc(point: Sequence[EF]) -> EF:
    """MLE of `f(i) = i` (big-endian) at `point`."""
    n = len(point)
    return sum(p * EF(1 << (n - 1 - i)) for i, p in enumerate(point))


def mle_of_zeros_then_ones(n_zeros: int, point: Sequence[EF]) -> EF:
    """MLE of `[0]*n_zeros ++ [1]*(2^len(point) − n_zeros)` at `point`."""
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


def finger_print(discriminator: Fp, data: Sequence[EF], alphas_eq_poly: Sequence[EF]) -> EF:
    """`Σᵢ αᵢ · dataᵢ + α_last · discriminator`."""
    assert len(alphas_eq_poly) > len(data)
    return dot_product(alphas_eq_poly, data) + alphas_eq_poly[-1] * EF(discriminator)


def sort_tables_by_height(table_log_heights: dict[str, int]) -> list[tuple[str, int]]:
    """Descending by height, alphabetical on ties (matches Rust `BTreeMap`)."""
    return sorted(sorted(table_log_heights.items()), key=lambda kv: -kv[1])


def eval_eq(point: Sequence[EF]) -> list[EF]:
    """Length-`2^n` evaluation table of `eq(point, ·)`."""
    out = [ONE]
    for p in point:
        out = [w for v in out for w in (v * (ONE - p), v * p)]
    return out


def verify_generic_logup(
    fiat_shamir: FiatShamir,
    c: EF,
    alphas: list[EF],
    alphas_eq_poly: list[EF],
    log_memory: int,
    bytecode_multilinear: list[int],
    table_log_heights: dict[str, int],
    tables: dict[str, TableMeta],
) -> dict:
    """GKR-quotient + section-by-section (memory/bytecode/per-table) reconstruction."""
    n_instr_cols = N_INSTRUCTION_COLUMNS
    n_runtime_cols = N_RUNTIME_COLUMNS
    col_pc = PC_COL_INDEX
    ds_mem = Fp(LOGUP_MEMORY_DOMAINSEP)
    ds_byte = Fp(LOGUP_BYTECODE_DOMAINSEP)

    tables_sorted = sort_tables_by_height(table_log_heights)
    log_bytecode = log2_strict(len(bytecode_multilinear) // (1 << log2_ceil(n_instr_cols)))
    log_instr = log2_ceil(n_instr_cols)

    total_active_len = (
        (1 << log_memory)
        + max(1 << log_bytecode, 1 << tables_sorted[0][1])
        + sum(tables[n].n_buses << h for n, h in tables_sorted)
    )
    total_gkr_n_vars = log2_ceil(total_active_len)

    quotient, point_gkr, claim_num, claim_den = verify_gkr_quotient(fiat_shamir, total_gkr_n_vars)
    if quotient != ZERO:
        raise ProofError("logup: GKR sum != 0")

    num, den = ZERO, ZERO

    def pref_at(offset: int, log_height: int) -> EF:
        n_missing = total_gkr_n_vars - log_height
        idx = offset >> log_height
        bits = [ONE if (idx >> (n_missing - 1 - i)) & 1 else ZERO for i in range(n_missing)]
        return eq_poly(bits, point_gkr[:n_missing])

    # Memory (data order: [value_index, value_memory] mirrors `crates/sub_protocols/src/logup.rs`).
    mem_pt = point_gkr[-log_memory:]
    pref = pref_at(0, log_memory)
    value_memory_acc = fiat_shamir.next_extension_scalar()
    num = num - pref * value_memory_acc
    value_memory = fiat_shamir.next_extension_scalar()
    fp_mem = finger_print(ds_mem, [mle_of_01234567_etc(mem_pt), value_memory], alphas_eq_poly)
    den = den + pref * (c - fp_mem)
    offset = 1 << log_memory

    # Bytecode (padded to the tallest table).
    log_byte_pad = max(log_bytecode, tables_sorted[0][1])
    byte_pt = point_gkr[-log_bytecode:]
    pref = pref_at(offset, log_bytecode)
    pref_pad = pref_at(offset, log_byte_pad)
    value_bytecode_acc = fiat_shamir.next_extension_scalar()
    bytecode_value = eval_multilinear_evals([EF(v) for v in bytecode_multilinear], byte_pt + alphas[-log_instr:])
    correction = math.prod(ONE - a for a in alphas[: len(alphas) - log_instr])
    fp_byte = (
        bytecode_value * correction
        + mle_of_01234567_etc(byte_pt) * alphas_eq_poly[n_instr_cols]
        + alphas_eq_poly[-1] * EF(ds_byte)
    )
    num = num - pref * value_bytecode_acc
    den = den + pref * (c - fp_byte) + pref_pad * mle_of_zeros_then_ones(1 << log_bytecode, point_gkr[-log_byte_pad:])
    offset += 1 << log_byte_pad

    # Per-table base offsets in the GKR layout are assigned in sorted-by-height order
    # (mirrors `layout_offsets` in sub_protocols/src/logup.rs).
    table_offsets: dict[str, int] = {}
    for name, log_n_rows in tables_sorted:
        table_offsets[name] = offset
        offset += tables[name].n_buses << log_n_rows
    final_offset = offset

    # Per-table: walk the bus spec in the same order as the Rust prover. The prover
    # writes col_evals for new (uncached) columns in `bus.data` order via a single
    # `add_extension_scalars` chunk per bus — the verifier must read in the same chunks.
    # Iterate tables in canonical ALL_TABLES order (matches the new prover scalar layout).
    bus_num_vals: dict[str, EF] = {}
    bus_den_vals: dict[str, EF] = {}
    columns_values: dict[str, dict[int, EF]] = {}

    for name in ALL_TABLES_ORDER:
        log_n_rows = table_log_heights[name]
        meta = tables[name]
        table_values: dict[int, EF] = {}
        row_stride = 1 << log_n_rows
        offset_within_table = table_offsets[name]

        for bus in meta.buses:
            pref = pref_at(offset_within_table, log_n_rows)
            if bus[0] == "col_mult":
                bus_num_vals[name] = fiat_shamir.next_extension_scalar()
                bus_den_vals[name] = fiat_shamir.next_extension_scalar()
                num = num + pref * bus_num_vals[name]
                den = den + pref * bus_den_vals[name]
                offset_within_table += row_stride
            elif bus[0] == "byte_lookup":
                cols = list(range(n_runtime_cols, n_runtime_cols + n_instr_cols)) + [col_pc]
                evals = fiat_shamir.next_extension_scalars_vec(len(cols))
                for c_idx, e in zip(cols, evals):
                    table_values[c_idx] = e
                num = num + pref  # Push direction
                den = den + pref * (c - finger_print(ds_byte, evals, alphas_eq_poly))
                offset_within_table += row_stride
            elif bus[0] == "mem_group":
                _, idx_col, vals_start, n = bus
                # One bus per row in the group; first sees idx_col fresh, the rest
                # see only val_col fresh (mirrors the Rust prover's dedup logic).
                for i in range(n):
                    val_col = vals_start + i
                    idx_fresh = idx_col not in table_values
                    val_fresh = val_col not in table_values
                    evals = iter(fiat_shamir.next_extension_scalars_vec(idx_fresh + val_fresh))
                    if idx_fresh:
                        table_values[idx_col] = next(evals)
                    if val_fresh:
                        table_values[val_col] = next(evals)
                    pref = pref_at(offset_within_table, log_n_rows)
                    fp = finger_print(ds_mem, [table_values[idx_col] + EF(i), table_values[val_col]], alphas_eq_poly)
                    num = num + pref  # Push direction
                    den = den + pref * (c - fp)
                    offset_within_table += row_stride
            else:
                raise ProofError(f"unknown bus kind: {bus[0]}")

        columns_values[name] = table_values

    den = den + mle_of_zeros_then_ones(final_offset, point_gkr)
    if num != claim_num:
        raise ProofError("logup: numerators value mismatch")
    if den != claim_den:
        raise ProofError("logup: denominators value mismatch")

    return {
        "value_memory": value_memory,
        "value_memory_acc": value_memory_acc,
        "value_bytecode_acc": value_bytecode_acc,
        "bus_num": bus_num_vals,
        "bus_den": bus_den_vals,
        "gkr_point": list(point_gkr),
        "columns_values": columns_values,
    }


class ConstraintFolder:
    """`flat`/`shift` = current-row / next-row column evals. Each `assert_zero(x)`
    adds `alpha_powers[i]·x` to the accumulator."""

    def __init__(self, flat: Sequence[EF], shift: Sequence[EF], alpha_powers: Sequence[EF]) -> None:
        self.flat, self.shift, self.alpha_powers = (
            list(flat),
            list(shift),
            list(alpha_powers),
        )
        self.accumulator: EF = ZERO
        self.i = 0

    def assert_zero(self, x: EF) -> None:
        self.accumulator = self.accumulator + self.alpha_powers[self.i] * x
        self.i += 1

    def assert_eq(self, x: EF, y: EF) -> None:
        self.assert_zero(x - y)

    def assert_bool(self, x: EF) -> None:
        self.assert_zero(x * (ONE - x))


def _eval_bus_virtual(
    folder: "ConstraintFolder", extra_data: dict, multiplicity: EF, discriminator: EF, data: Sequence[EF]
) -> None:
    alphas: list[EF] = extra_data["logup_alphas_eq"]
    assert len(data) < len(alphas)
    folder.assert_zero(multiplicity)
    encoded = dot_product(alphas, data) + alphas[-1] * discriminator
    folder.assert_zero(encoded)


def air_constraint_eval(
    table: TableMeta,
    col_evals: Sequence[EF],
    alpha_powers: Sequence[EF],
    extra_data: dict,
) -> EF:
    folder = ConstraintFolder(col_evals[: table.n_columns], col_evals[table.n_columns :], alpha_powers)
    table.air_fn(folder, extra_data)
    return folder.accumulator


def _eval_air_execution(folder: ConstraintFolder, extra_data: dict) -> None:
    # fmt: off
    (pc, fp, addr_a, addr_b, addr_c, value_a, value_b, value_c,
     operand_a, operand_b, operand_c, flag_a, flag_b, flag_c, flag_c_fp,
     flag_ab_fp, mul, jump, aux, discriminator) = folder.flat[:20]
    # fmt: on
    pc_shift, fp_shift = folder.shift[0], folder.shift[1]

    # nu_x = flag·operand + (1 − flag − flag_ab_fp)·value + flag_ab_fp·(fp + operand)
    nfa = ONE - flag_a - flag_ab_fp
    nfb = ONE - flag_b - flag_ab_fp
    nfc = ONE - flag_c - flag_c_fp
    nu_a = flag_a * operand_a + nfa * value_a + flag_ab_fp * (fp + operand_a)
    nu_b = flag_b * operand_b + nfb * value_b + flag_ab_fp * (fp + operand_b)
    nu_c = flag_c * operand_c + nfc * value_c + flag_c_fp * (fp + operand_c)

    # aux ∈ {0,1,2}: 0=nothing, 1=add, 2=deref.
    add = aux * EF(2) - aux * aux
    deref = aux * (aux - ONE) * EF((P + 1) // 2)  # (P+1)/2 is the inverse of 2 mod P
    is_precompile = ONE - add - mul - deref - jump

    az = folder.assert_zero
    _eval_bus_virtual(folder, extra_data, is_precompile, discriminator, [nu_a, nu_b, nu_c])
    az(nfa * (addr_a - (fp + operand_a)))
    az(nfb * (addr_b - (fp + operand_b)))
    az(nfc * (addr_c - (fp + operand_c)))
    az(add * (nu_b - (nu_a + nu_c)))
    az(mul * (nu_b - nu_a * nu_c))
    az(deref * (addr_b - (value_a + operand_b)))
    az(deref * (value_b - nu_c))
    jc = jump * nu_a
    az(jc * (nu_a - ONE))
    az(jc * (pc_shift - nu_b))
    az(jc * (fp_shift - nu_c))
    not_jc = ONE - jc
    az(not_jc * (pc_shift - (pc + ONE)))
    az(not_jc * (fp_shift - fp))


# extension_op/air.rs precompile-data layout.
_EXT_OP_FLAG_IS_BE = 4
_EXT_OP_FLAG_ADD = 8
_EXT_OP_FLAG_MUL = 16
_EXT_OP_FLAG_POLY_EQ = 32
_EXT_OP_LEN_MULTIPLIER = 64


def _quintic_mul_ef(a: Sequence[EF], b: Sequence[EF]) -> list[EF]:
    """Multiply two quintic-extension elements whose coefficients are themselves `EF`."""
    assert len(a) == 5 and len(b) == 5
    return quintic_mul(a, b, ZERO)


def _eval_air_extension_op(folder: ConstraintFolder, extra_data: dict) -> None:
    # Layout: shift columns 0..13 = (is_be, start, len, flag_{add,mul,poly_eq},
    # idx_{a,b}, comp[0..5]); then idx_res, va, vb, vres (5 each).
    f = folder.flat
    is_be, start, len_col, flag_add, flag_mul, flag_poly_eq, idx_a, idx_b = f[:8]
    comp, idx_res = f[8:13], f[13]
    va, vb, vres = f[14:19], f[19:24], f[24:29]
    s = folder.shift
    is_be_sh, start_sh, len_sh, flag_add_sh, flag_mul_sh, flag_poly_eq_sh, idx_a_sh, idx_b_sh = s[:8]
    comp_sh = s[8:13]

    aux = (
        is_be * EF(_EXT_OP_FLAG_IS_BE)
        + flag_add * EF(_EXT_OP_FLAG_ADD)
        + flag_mul * EF(_EXT_OP_FLAG_MUL)
        + flag_poly_eq * EF(_EXT_OP_FLAG_POLY_EQ)
        + len_col * EF(_EXT_OP_LEN_MULTIPLIER)
    )
    _eval_bus_virtual(folder, extra_data, start * (flag_add + flag_mul + flag_poly_eq), aux, [idx_a, idx_b, idx_res])

    for x in (is_be, start, flag_add, flag_mul, flag_poly_eq):
        folder.assert_bool(x)

    is_ee, not_start_sh = ONE - is_be, ONE - start_sh
    va_x = [va[0]] + [va[k] * is_ee for k in range(1, 5)]
    comp_tail = [comp_sh[k] * not_start_sh for k in range(5)]
    va_vb = _quintic_mul_ef(va_x, vb)

    for k in range(5):
        folder.assert_zero((comp[k] - (va_x[k] + vb[k] + comp_tail[k])) * flag_add)
    for k in range(5):
        folder.assert_zero((comp[k] - (va_vb[k] + comp_tail[k])) * flag_mul)

    # poly_eq: comp ← (2·va·vb − va − vb + 1) · comp_sh_or_one.
    poly_eq_val = [va_vb[k] + va_vb[k] - va_x[k] - vb[k] + (ONE if k == 0 else ZERO) for k in range(5)]
    comp_sh_or_one = [comp_sh[0] * not_start_sh + start_sh] + [comp_sh[k] * not_start_sh for k in range(1, 5)]
    poly_eq_result = _quintic_mul_ef(poly_eq_val, comp_sh_or_one)
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

    folder.assert_zero(not_start_sh * (idx_a_sh - idx_a - (is_be + is_ee * EF(5))))
    folder.assert_zero(not_start_sh * (idx_b_sh - idx_b - EF(5)))
    folder.assert_zero(start_sh * (len_col - ONE))


def _build_p1c() -> dict:
    raw = POSEIDON1_AIR_CONSTANTS
    fp_mat = lambda m: [[Fp(v) for v in row] for row in m]
    fp_vec = lambda v: [Fp(x) for x in v]
    n = len(MDS_FIRST_ROW_16)
    mds_dense = [[Fp(MDS_FIRST_ROW_16[(j - i) % n]) for j in range(n)] for i in range(n)]
    # External full-round RCs: first and last `(ROUNDS_F/2) * WIDTH` entries of the
    # raw round-constant table that drives the actual Poseidon permutation.
    hf, t = POSEIDON_FULL_ROUNDS // 2, POSEIDON_WIDTH
    rcs = PARAMS_16.round_constants
    initial_constants = [[Fp(x) for x in rcs[i * t : (i + 1) * t]] for i in range(hf)]
    tail_start = (hf + POSEIDON_PARTIAL_ROUNDS) * t
    final_constants = [[Fp(x) for x in rcs[tail_start + i * t : tail_start + (i + 1) * t]] for i in range(hf)]
    return {
        "initial_constants": initial_constants,
        "final_constants": final_constants,
        "sparse_m_i": fp_mat(raw["sparse_m_i"]),
        "sparse_first_row": fp_mat(raw["sparse_first_row"]),
        "sparse_v": fp_mat(raw["sparse_v"]),
        "sparse_first_rc": fp_vec(raw["sparse_first_round_constants"]),
        "sparse_scalar_rc": fp_vec(raw["sparse_scalar_round_constants"]),
        "mds_dense": mds_dense,
    }


P1C = _build_p1c()


def _matvec_kb(mat: list[list[Fp]], state: list[EF]) -> list[EF]:
    return [dot_product(state, row) for row in mat]


def _full_round(state: list[EF], rc1: list[Fp], rc2: list[Fp]) -> list[EF]:
    for rc in (rc1, rc2):
        sbox = [(t := s + c) * t * t for s, c in zip(state, rc)]
        state = _matvec_kb(P1C["mds_dense"], sbox)
    return state


def _eval_poseidon1_16(folder: ConstraintFolder, cols: dict) -> None:
    """AIR for Poseidon1-16. Each `post` column commits an intermediate state, which we
    constrain against the local computation, then adopt to bound polynomial degree."""
    const = P1C
    state = list(cols["inputs"])
    initial = list(cols["inputs"])
    half_initial = half_final = POSEIDON_FULL_ROUNDS // 4

    for r in range(half_initial):
        state = _full_round(state, const["initial_constants"][2 * r], const["initial_constants"][2 * r + 1])
        for i, post in enumerate(cols["beginning_full_rounds"][r]):
            folder.assert_eq(state[i], post)
            state[i] = post

    state = [s + c for s, c in zip(state, const["sparse_first_rc"])]
    state = _matvec_kb(const["sparse_m_i"], state)

    n_partial = POSEIDON_PARTIAL_ROUNDS
    for r in range(n_partial):
        folder.assert_eq(state[0] * state[0] * state[0], cols["partial_rounds"][r])
        state[0] = cols["partial_rounds"][r]
        if r < n_partial - 1:
            state[0] = state[0] + const["sparse_scalar_rc"][r]
        old_s0 = state[0]
        state[0] = dot_product(state, const["sparse_first_row"][r])
        for i in range(1, POSEIDON_WIDTH):
            state[i] = state[i] + old_s0 * const["sparse_v"][r][i - 1]

    for r in range(half_final - 1):
        state = _full_round(state, const["final_constants"][2 * r], const["final_constants"][2 * r + 1])
        for i, post in enumerate(cols["ending_full_rounds"][r]):
            folder.assert_eq(state[i], post)
            state[i] = post

    # Last full round: compression mode adds `initial` (gated by flag_half_output for lanes 4..8);
    # permute mode (flag_permute=1) outputs raw state.
    last = 2 * (half_final - 1)
    state = _full_round(state, const["final_constants"][last], const["final_constants"][last + 1])
    flag_permute = cols["flag_permute"]
    not_permute = ONE - flag_permute
    compression_last4 = not_permute - cols["flag_half_output"]
    for i in range(POSEIDON_WIDTH // 2):
        gate = not_permute if i < (DIGEST_ELEMS // 2) else compression_last4
        folder.assert_zero(gate * (state[i] + initial[i] - cols["outputs_left"][i]))
        folder.assert_zero(flag_permute * (state[i] - cols["outputs_left"][i]))
        folder.assert_zero(flag_permute * (state[i + POSEIDON_WIDTH // 2] - cols["outputs_right"][i]))


def _eval_air_poseidon16(folder: ConstraintFolder, extra_data: dict) -> None:
    flat, W = folder.flat, POSEIDON_WIDTH
    half_initial = half_final = POSEIDON_FULL_ROUNDS // 4

    o = 0

    def take(n: int) -> list[EF]:
        nonlocal o
        chunk, o = flat[o : o + n], o + n
        return list(chunk)

    # fmt: off
    [multiplicity, index_b, index_res, flag_half_output, flag_hardcoded_left,
     offset_hardcoded_left, eff_idx_left_first, eff_idx_left_second, flag_permute] = take(9)
    # fmt: on
    inputs = take(W)
    beginning_full_rounds = [take(W) for _ in range(half_initial)]
    partial_cols = take(POSEIDON_PARTIAL_ROUNDS)
    ending_full_rounds = [take(W) for _ in range(half_final - 1)]
    outputs_left, outputs_right = take(W // 2), take(W // 2)

    discriminator = (
        EF(POSEIDON_DISCRIMINATOR_BASE)
        + flag_permute * EF(POSEIDON_PERMUTE_SHIFT)
        + flag_half_output * EF(POSEIDON_HALF_OUTPUT_SHIFT)
        + flag_hardcoded_left * EF(POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT)
        + flag_hardcoded_left * offset_hardcoded_left * EF(POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT)
    )
    not_hcl = ONE - flag_hardcoded_left
    index_a = eff_idx_left_second - not_hcl * EF(DIGEST_ELEMS // 2)

    _eval_bus_virtual(folder, extra_data, multiplicity, discriminator, [index_a, index_b, index_res])
    for f in (multiplicity, flag_half_output, flag_hardcoded_left, flag_permute):
        folder.assert_bool(f)
    folder.assert_zero(flag_permute * (flag_half_output + flag_hardcoded_left))
    folder.assert_zero(flag_hardcoded_left * (offset_hardcoded_left - eff_idx_left_first))
    folder.assert_zero(not_hcl * (index_a - eff_idx_left_first))

    _eval_poseidon1_16(
        folder,
        {
            "inputs": inputs,
            "beginning_full_rounds": beginning_full_rounds,
            "partial_rounds": partial_cols,
            "ending_full_rounds": ending_full_rounds,
            "outputs_left": outputs_left,
            "outputs_right": outputs_right,
            "flag_half_output": flag_half_output,
            "flag_permute": flag_permute,
        },
    )


# (n_columns, air_degree, n_constraints, n_shift, air_fn) per table — all constants.
DEFAULT_TABLES = [
    TableMeta(name, n, TABLE_BUSES[name], d, k, s, fn)
    for name, n, d, k, s, fn in (
        ("execution", N_INSTRUCTION_COLUMNS + N_RUNTIME_COLUMNS, 5, 14, 2, _eval_air_execution),
        ("extension", 29, 6, 35, 13, _eval_air_extension_op),
        ("poseidon", _POSEIDON_N_COLS, 10, 101, 0, _eval_air_poseidon16),
    )
]


def verify_execution(
    public_input: Sequence[Fp],
    proof: Proof,
    bytecode_multilinear: list[int],
):
    tables = DEFAULT_TABLES
    bytecode_log_size = log2_strict(len(bytecode_multilinear)) - log2_ceil(N_INSTRUCTION_COLUMNS)
    ending_pc = (1 << bytecode_log_size) - 1
    bytecode_hash = sponge_hash([Fp(v) for v in bytecode_multilinear])
    if len(public_input) != PUBLIC_INPUT_SIZE:
        raise ProofError("InvalidProof: public_input length mismatch")

    state = FiatShamir(proof, poseidon16_compress(bytecode_hash, SNARK_DOMAIN_SEP))  # domain separator accross bytecode
    state.observe_scalars(public_input)

    dims = [int(x.value) for x in state.next_base_scalars_vec(2 + len(tables))]
    log_inv_rate, log_memory, *table_log_n_rows = dims
    if not MIN_WHIR_LOG_INV_RATE <= log_inv_rate <= MAX_WHIR_LOG_INV_RATE:
        raise ProofError("InvalidRate")
    if not MIN_LOG_MEMORY_SIZE <= log_memory <= MAX_LOG_MEMORY_SIZE:
        raise ProofError("InvalidProof: log_memory out of range")
    if not MIN_BYTECODE_LOG_SIZE <= bytecode_log_size <= MAX_BYTECODE_LOG_SIZE:
        raise ProofError("InvalidProof: bytecode log_size out of range")
    if log_memory < max(max(table_log_n_rows, default=0), bytecode_log_size):
        raise ProofError("InvalidProof: memory smaller than tables/bytecode")
    for t, h in zip(tables, table_log_n_rows):
        limit = MAX_LOG_N_ROWS_PER_TABLE[t.name]
        if not MIN_LOG_N_ROWS_PER_TABLE <= h <= limit:
            raise ProofError(
                f"InvalidProof: table {t.name} log_n_rows={h} not in [{MIN_LOG_N_ROWS_PER_TABLE}, {limit}]"
            )

    table_log_heights = {t.name: h for t, h in zip(tables, table_log_n_rows)}
    tables_by_name = {t.name: t for t in tables}
    tables_sorted = sort_tables_by_height(table_log_heights)
    n_max = tables_sorted[0][1]

    total_stacked = (
        (2 << log_memory)
        + (1 << max(bytecode_log_size, n_max))
        + sum(t.n_columns << table_log_heights[t.name] for t in tables)
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

    logup_c = state.sample_ef()
    state.duplex()
    logup_alphas = state.sample_many_ef(log2_ceil(N_INSTRUCTION_COLUMNS + 2))
    logup_alphas_eq = eval_eq(logup_alphas)
    logup = verify_generic_logup(
        state,
        logup_c,
        logup_alphas,
        logup_alphas_eq,
        log_memory,
        bytecode_multilinear,
        table_log_heights,
        tables_by_name,
    )
    gkr_point = logup["gkr_point"]

    air_alpha = state.sample_ef()

    # AIR alpha powers/offsets are laid out in canonical ALL_TABLES order
    # (mirrors `for table in ALL_TABLES { alpha_offset += n_constraints }` in verify_execution.rs).
    alpha_offsets: dict[str, int] = {}
    cumulative = 0
    for name in ALL_TABLES_ORDER:
        alpha_offsets[name] = cumulative
        cumulative += tables_by_name[name].n_constraints
    alpha_powers = ef_powers(air_alpha, cumulative)

    extra_data = {"logup_alphas_eq": logup_alphas_eq}

    # Initial AIR sum: Σ_table (α^o · signed_num + α^(o+1) · (c − bus_den)). The
    # sign is the direction of each table's unique Column-multiplicity bus.
    initial_sum = ZERO
    for name in ALL_TABLES_ORDER:
        offset = alpha_offsets[name]
        sign = -ONE if tables_by_name[name].buses[0][1] == "Pull" else ONE
        initial_sum = initial_sum + alpha_powers[offset] * (logup["bus_num"][name] * sign)
        initial_sum = initial_sum + alpha_powers[offset + 1] * (logup_c - logup["bus_den"][name])
    sc_point, sc_value = verify_sumcheck(state, initial_sum, n_max, max(t.air_degree + 1 for t in tables))

    committed = {
        name: [(gkr_point[-table_log_heights[name] :], logup["columns_values"][name], {})] for name in ALL_TABLES_ORDER
    }
    my_air_final = ZERO
    for name in ALL_TABLES_ORDER:
        meta = tables_by_name[name]
        log_n_rows = table_log_heights[name]
        col_evals = state.next_extension_scalars_vec(meta.n_columns + meta.n_shift)
        offset = alpha_offsets[name]
        alpha_slice = alpha_powers[offset : offset + meta.n_constraints]
        constraint_eval = air_constraint_eval(meta, col_evals, alpha_slice, extra_data)

        natural_pt = list(reversed(sc_point[-log_n_rows:])) if log_n_rows else []
        k_t = math.prod(sc_point[: n_max - log_n_rows])
        my_air_final = my_air_final + k_t * eq_poly(gkr_point[-log_n_rows:], natural_pt) * constraint_eval

        eq_vals = {i: col_evals[i] for i in range(meta.n_columns)}
        next_vals = {j: col_evals[meta.n_columns + j] for j in range(meta.n_shift)}
        committed[name].append((natural_pt, eq_vals, next_vals))
    if my_air_final != sc_value:
        raise ProofError("AIR sumcheck: claimed value mismatch")

    assert len(public_input) % DIGEST_ELEMS == 0
    pm_point = state.sample_many_ef(log2_strict(len(public_input)))
    pm_eval = eval_multilinear_evals([EF(f) for f in public_input], pm_point)

    bytecode_acc_idx = (2 << log_memory) >> bytecode_log_size
    previous = [
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
        previous,
        table_log_heights,
        committed,
        tables_by_name,
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
    vector_path = Path(__file__).resolve().parents[2] / "target" / "zkvm_test_vectors" / "proof.json"
    if not vector_path.exists():
        print(
            f"Test vector not found at {vector_path}. Generate it first with:\n"
            "    cargo test --release -p lean_prover dump_test_vector_for_python_verifier -- --nocapture"
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
