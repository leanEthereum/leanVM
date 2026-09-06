"""Joint prefix/boundary reduction and the residual outside SET/JUMP bytecode."""

from fractions import Fraction
from functools import reduce
from operator import mul
from random import Random

from zk_bus_boundary_audit import error_bound
from zk_bus_packet_audit import table_packets
from zk_bytecode_frontier_audit import BANKS, CODE_BASES, code_frontier
from zk_bytecode_public_library_audit import FRAME_BASE, set_library
from zk_column_count_audit import Library
from zk_count_children_audit import EDGES
from zk_gkr_coarse_audit import check_first_packet, cycles
from zk_gkr_first_packet_audit import fingerprint
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import table_products
from zk_set_payload_products_audit import BITS


def jump_controls(v, library, e, beta):
    return tuple(value for side in ("push", "pull") for value in table_products(v, library, v.OP_JUMP, side, e, beta))


def outside_ratio(v, library, e, beta):
    return reduce(
        mul,
        (
            table_products(v, library, opcode, "push", e, beta)[1] / table_products(v, library, opcode, "pull", e, beta)[1]
            for opcode in range(len(v.TABLES))
            if opcode not in (v.OP_SET, v.OP_JUMP)
        ),
        v.ONE,
    )


def trade_invariance(v, e, beta, rng):
    library, positions, switches = Library(v), {}, []
    library.frame = 65536
    columns = [v.JUMP_COLUMNS.index(name) for name in ("cnt_f", "cnt_bc")]
    for bank, (first, second) in enumerate(EDGES):
        template = library.templates(library.block(v.OP_JUMP), library.fresh_frame())
        rows = [library.append(template)[0] for _ in range(4)]
        ordered = rows[0], rows[3], rows[1], rows[2]
        base = 8 * (bank << 12)
        positions.update(zip(ordered, (base + first, base + second, base + 4 + first, base + 4 + second), strict=True))
        switches.extend(tuple((row, column) for row in ordered) for column in columns)
    library.verify()
    layout = v.build_layout(range(16 << 20), 20, (4, 18, 15, 4, 17, 3))
    bus = v.bus_layout((0, 20, 20), layout.push)
    point = [v.E(*(rng.getrandbits(64) for _ in range(3))) for _ in range(bus.depth - 2)]
    initial = jump_controls(v, library, e, beta)
    initial_packet = table_packets(v, library, positions, bus, layout, point, e)
    exponents, reads = dict(library.exponents), dict(library.reads)

    def quartet_products():
        result = {}
        for row_id, (_, row) in enumerate(library.rows):
            for column in columns:
                key = column, positions[row_id] >> 2
                result[key] = result.get(key, v.ONE) * row[column]
        return result

    quartets = quartet_products()
    for choice in [1 << bit for bit in range(8)] + [0xA5, 0xFF]:
        for bit, switch in enumerate(switches):
            library.set_labels(switch, (1, 2, 0, 3) if choice >> bit & 1 else (0, 3, 1, 2))
        library.verify()
        assert jump_controls(v, library, e, beta) == initial
        assert quartet_products() == quartets
        assert dict(library.exponents) == exponents and dict(library.reads) == reads
        assert table_packets(v, library, positions, bus, layout, point, e) != initial_packet
    print(
        "Actual frame/bytecode label trades change final packet evaluations while preserving all ten whole JUMP products and count quartets",
        flush=True,
    )


def payload_invariance(v, e, beta, rng):
    libraries = [cycles(v, 1, payloads)[0] for payloads in ([[0] * 3] * 48, [[rng.getrandbits(64) for _ in range(3)] for _ in range(48)])]
    assert jump_controls(v, libraries[0], e, beta) == jump_controls(v, libraries[1], e, beta)
    assert outside_ratio(v, libraries[0], e, beta) == outside_ratio(v, libraries[1], e, beta)
    xor_libraries = []
    for values in ([0] * 8, [rng.getrandbits(64) for _ in range(8)]):
        library = Library(v)
        library.pc, library.frame = 2048, 1 << 17
        block = library.block(v.OP_XOR)
        for value in values:
            templates = library.templates(block, library.fresh_frame())
            templates[0][1][v.ARITH_COLUMNS.index("va_0")] = v.E(value)
            library.append(templates)
        library.verify()
        xor_libraries.append(library)
    assert jump_controls(v, xor_libraries[0], e, beta) == jump_controls(v, xor_libraries[1], e, beta)
    assert outside_ratio(v, xor_libraries[0], e, beta) == outside_ratio(v, xor_libraries[1], e, beta)
    for left, right in (libraries, xor_libraries):
        assert dict(left.reads) == dict(right.reads) and left.images["code"] == right.images["code"]
    print("The actual MUL and XOR payload masks preserve the retained JUMP products, final counts and outside bytecode ratio", flush=True)


def add_library(target, source):
    for kind in target.images:
        assert target.images[kind].keys().isdisjoint(source.images[kind])
        target.images[kind].update(source.images[kind])
    target.append(source.rows)


def residual_and_reconstruction(v, e, beta, rng):
    support = (0, 64)
    words = [[[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in support] for _ in range(BANKS)]
    real_pc, real_frame = 900000, 32

    def build(choice, bits):
        library, code_indices, alternatives = Library(v), set(), []
        for alternative in (0, 1):
            pc = real_pc + 2 * alternative
            template = library.templates((v.OP_MUL, pc, [], True), v.GEN ** (real_frame + 128 * alternative))
            library.register(template)
            alternatives.append(template)
            code_indices.update((pc, pc + 1))
        library.append(alternatives[choice])
        library.append(alternatives[choice])
        for bank in range(BANKS):
            local, indices = set_library(
                v,
                support,
                words[bank],
                bits[bank * len(support) : (bank + 1) * len(support)],
                code_base=CODE_BASES[bank],
                frame_base=FRAME_BASE + 8 * BITS * bank,
                compact=True,
            )
            add_library(library, local)
            code_indices.update(indices["code"])
        library.verify()
        return library, code_indices

    ratios, reference = [], None
    for choice in (0, 1):
        for bits in ([0] * 8, [1] * 8, [i % 2 for i in range(8)]):
            library, indices = build(choice, bits)
            if reference is None:
                reference = library
            assert library.images == reference.images and dict(library.exponents) == dict(reference.exponents)
            d = code_frontier(v, library, indices, e, beta)
            seed = reduce(
                mul,
                (fingerprint(v, e, beta, v.SEP_BYTECODE, address, v.ONE, payload) for address, payload in library.images["code"].items()),
                v.ONE,
            )
            set_push, set_pull = [table_products(v, library, v.OP_SET, side, e, beta) for side in ("push", "pull")]
            controls = jump_controls(v, library, e, beta)
            omega = outside_ratio(v, library, e, beta)
            jump_ratio = controls[1] / controls[6]
            recovered = reduce(mul, d, v.ONE) / seed * set_pull[1] / set_push[1] / jump_ratio
            assert recovered == omega
            assert set_push[1] == reduce(mul, d, v.ONE) / (seed * omega * jump_ratio) * set_pull[1]
            ratios.append(omega)

            sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
            free_d, free_set = [sample() for _ in range(4)], [sample() for _ in range(3)]
            free_packet = [sample() for _ in range(5)]
            set_plus = reduce(mul, free_d, v.ONE) * free_set[0] / (seed * omega * jump_ratio)
            assert reduce(mul, free_d, v.ONE) / seed * free_set[0] / set_plus / jump_ratio == omega
            p0, p2, p3, q2, q3 = free_packet
            d_total = reduce(mul, free_d, v.ONE)
            push = [p0, seed, p2, p3]
            pull = [seed * p0 * p2 * p3 / (d_total * q2 * q3), d_total, q2, q3]
            check_first_packet(v, push, pull, [v.GEN**19, v.ONE, v.ONE, v.ONE])
    assert ratios[:3] == [ratios[0]] * 3 and ratios[3:] == [ratios[3]] * 3 and ratios[0] != ratios[3]
    fingerprints = [
        fingerprint(v, e, beta, v.SEP_BYTECODE, int(v.GEN ** (real_pc + 2 * a)), v.ONE, reference.images["code"][int(v.GEN ** (real_pc + 2 * a))])
        for a in (0, 1)
    ]
    delta = e[2] * (v.ONE + v.GEN**2)
    assert fingerprints[0] + fingerprints[1] == e[1] * (v.GEN**real_pc + v.GEN ** (real_pc + 2)) != v.ZERO
    assert ratios[0] + ratios[3] == delta * (fingerprints[0] + fingerprints[1]) / (fingerprints[0] * fingerprints[1]) != v.ZERO
    print("A common-image/count-product MUL occupancy pair changes the recovered outside ratio, which all SET choices leave fixed", flush=True)
    print(
        "Seven product coordinates and five packet coordinates reconstruct consistently with that ratio; the actual first-packet reader accepts",
        flush=True,
    )
    print("This is a strengthened-view residual, not a distinguisher for the mixed second GKR layer", flush=True)


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    rank = Fraction(base**2, (size - 2) ** 2)
    mul_error = Fraction((1 << 23) + 8 * 48 + 8, size) + rank + Fraction(1, 1 << 384)
    unused_error = Fraction((1 << 23) + 40, size) + rank + Fraction(1, 1 << 256)
    boundary_error, _ = error_bound()
    assert mul_error + unused_error + boundary_error + Fraction(1, 1 << 159) < Fraction(1, 1 << 155)
    print(
        "Joint enlarged-view reduction error below 2^-155, retaining the actual thirteen-field residual and excluding intervening messages",
        flush=True,
    )


if __name__ == "__main__":
    verifier, random = verifier_module(), Random(177)
    sample = lambda: verifier.E(*(random.getrandbits(64) for _ in range(3)))
    weights, shift = verifier.eq_kernel([sample() for _ in range(4)]), sample()
    trade_invariance(verifier, weights, shift, random)
    payload_invariance(verifier, weights, shift, random)
    residual_and_reconstruction(verifier, weights, shift, random)
    concrete_bound()
