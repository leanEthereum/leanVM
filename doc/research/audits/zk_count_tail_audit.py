"""A nonlinear endpoint test on the anchored count-only GKR layer."""

from functools import reduce
from operator import mul
from random import Random

from zk_count_children_audit import gkr_replay, polynomial_product
from zk_count_mixed_audit import evaluate, source_library, symbolic_leaves
from zk_pcs_audit import verifier_module


def endpoint_test(verifier, details, guess):
    _, challenge, packet, wire = details["view"]
    coin, scale = challenge[-1], details["combiner"] ** 2
    assert scale != verifier.ZERO
    tail = [coefficient / scale for coefficient in wire[-16:-12]]
    constant = reduce(mul, packet) + verifier.E.sum(coefficient * coin**degree for degree, coefficient in enumerate(tail, 1))
    numerator, denominator = coin * guess + packet[1], guess + packet[1]
    return verifier.E.sum(coefficient * numerator**degree * denominator ** (4 - degree) for degree, coefficient in enumerate([constant, *tail]))


def upper_children(verifier, leaves, point):
    half = len(leaves) // 2
    return [verifier.multilinear_eval(leaves[half + child :: 4], point) for child in range(4)]


def audit(verifier, sparse_bits=2):
    library, positions, masks, real_switches = source_library(verifier, sparse_bits, anchors=True)
    baseline = []
    for secret in (0, 1):
        for switch in real_switches:
            library.set_labels(switch, (1, 2, 0, 3) if secret else (0, 3, 1, 2))
        library.verify()
        baseline.append(symbolic_leaves(verifier, library, positions, masks))
    half, rng = len(positions) // 2, Random(139)
    assert all(set(leaf) == {0} for system in baseline for leaf in system[half + 1 :: 4])
    changed = next(index for index in range(half + 1, len(positions), 4) if baseline[0][index][0] != baseline[1][index][0])
    assert all(set(baseline[secret][index]) == {0} for secret in (0, 1) for index in range(changed - 1, changed + 3))
    count = 0
    for seed in (128, 140, 141):
        prefix = None
        for bits in (0, (1 << len(masks)) - 1, rng.getrandbits(len(masks))):
            for secret in (0, 1):
                leaves = [evaluate(verifier, polynomial, bits) for polynomial in baseline[secret]]
                for switch in real_switches:
                    library.set_labels(switch, (1, 2, 0, 3) if secret else (0, 3, 1, 2))
                for bit, switch in enumerate(masks):
                    library.set_labels(switch, (1, 2, 3, 0) if bits >> bit & 1 else (0, 3, 2, 1))
                library.verify()
                column = verifier.JUMP_COLUMNS.index("cnt_c")
                assert leaves == [library.rows[positions[position]][1][column] for position in range(len(positions))]
                details = gkr_replay(verifier, leaves, seed=seed, details=True)
                view = details["view"]
                if prefix is None:
                    prefix = view[0]
                assert view[0] == prefix
                point, packet = view[1][:-1], view[2]
                upper = upper_children(verifier, leaves, point)
                guesses = [upper_children(verifier, [polynomial[0] for polynomial in system], point)[1] for system in baseline]
                assert upper[1] == guesses[secret] != guesses[1 - secret]
                for candidate, guess in enumerate(guesses):
                    value = endpoint_test(verifier, details, guess)
                    assert value == reduce(mul, (guess * terminal + packet[1] * endpoint for terminal, endpoint in zip(packet, upper)))
                    assert (value == verifier.ZERO) == (candidate == secret)
                count += 1

    rounds = verifier.log2_strict(len(positions)) - 2
    index = (changed - half) // 4
    point = [verifier.ONE if index >> bit & 1 else verifier.ZERO for bit in range(rounds - 1)]
    for secret in (0, 1):
        bits = rng.getrandbits(len(masks))
        leaves = [evaluate(verifier, polynomial, bits) for polynomial in baseline[secret]]
        upper = upper_children(verifier, leaves, point)
        wrong = upper_children(verifier, [polynomial[0] for polynomial in baseline[1 - secret]], point)[1]
        value = reduce(mul, (wrong * endpoint + upper[1] * endpoint for endpoint in upper))
        assert value == reduce(mul, upper) * (wrong + upper[1]) ** 4 != verifier.ZERO

    for coin, guess in ((verifier.E(7), verifier.E(11)), (verifier.ONE, verifier.E(11))):
        lines = [(verifier.E(3), verifier.E(5)), (guess, verifier.ZERO), (verifier.E(13), verifier.E(17)), (verifier.E(19), verifier.E(23))]
        polynomial = polynomial_product(verifier, lines)
        packet = tuple(constant + coin * slope for constant, slope in lines)
        details = {"view": ((), (coin,), packet, (*polynomial[1:], *([verifier.ONE] * 8), *packet)), "combiner": verifier.ONE}
        assert packet[1] == guess and endpoint_test(verifier, details, guess) == verifier.ZERO
    print(
        f"Anchored {len(positions)}-row valid-cycle library: {count} accepted GKR replays, correct endpoint guesses accepted, wrong guesses rejected"
    )
    print(f"Boolean specialization certifies nonzero false-test polynomials for every mask assignment; total degree at most {8 * rounds - 4}")
    print("Scope: count-only channel with identity fingerprint trees; no full-VM leakage claim")


if __name__ == "__main__":
    audit(verifier_module())
