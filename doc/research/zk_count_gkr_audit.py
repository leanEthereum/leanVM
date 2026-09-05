"""A count-GKR prefix exposes the non-JUMP product despite a fixed total root."""

from random import Random

from zk_pcs_audit import verifier_module


def prefix(verifier, total, non_jump, coins):
    _, _, second_batch, query = coins
    jump = total / non_jump
    tail = (second_batch**2 * (jump + non_jump), second_batch**2 * (verifier.ONE + jump) * (verifier.ONE + non_jump), verifier.ZERO, verifier.ZERO)
    children = (jump + query * (verifier.ONE + jump), non_jump + query * (verifier.ONE + non_jump), verifier.ONE, verifier.ONE)

    class EndOfPrefix(Exception):
        pass

    class Stream:
        def __init__(self):
            self.values = iter([verifier.ONE, total, *([verifier.ONE] * 4), total, verifier.ONE, *tail, *([verifier.ONE] * 8), *children])
            self.coins = iter(coins)

        def next_scalar(self):
            return next(self.values)

        def next_scalars(self, count):
            return [self.next_scalar() for _ in range(count)]

        def sample(self):
            try:
                return next(self.coins)
            except StopIteration as error:
                raise EndOfPrefix from error

        def samples(self, count):
            return [self.sample() for _ in range(count)]

        sumcheck_round_poly = verifier.Transcript.sumcheck_round_poly

    checks, original = [], verifier.require

    def require(condition, message):
        if message.startswith("GKR layer"):
            checks.append((condition, message))
        original(condition, message)

    verifier.require = require
    stream = Stream()
    try:
        verifier.verify_gkr_grand_products(25, stream)
        raise AssertionError("the intentionally incomplete prefix returned a proof")
    except EndOfPrefix:
        assert len(checks) == 2 and all(condition for condition, _ in checks)
        assert next(stream.values, None) is None
    finally:
        verifier.require = original
    recovered = (children[1] + query) / (verifier.ONE + query)
    assert recovered == non_jump
    return recovered


if __name__ == "__main__":
    verifier, rng = verifier_module(), Random(126)
    heights = (0, 1, 0, 0, 20, 3)
    layout = verifier.build_layout([verifier.K(0)] * (16 << 12), 24, heights)
    push = verifier.bus_layout((0, 24, 12), layout.push)
    count = verifier.bus_layout((), layout.count)
    assert push.depth == 25 and count.depth == 23
    boundary = 4 << 20
    for block, placement in zip(layout.count, count.tables):
        if block.owner == verifier.OP_JUMP:
            assert placement.index + (1 << placement.variables) <= boundary
        else:
            assert boundary <= placement.index < placement.index + (1 << placement.variables) <= 2 * boundary
    coins = [verifier.E(*(rng.getrandbits(64) for _ in range(3))) for _ in range(4)]
    values = [prefix(verifier, verifier.GEN**1000, factor, coins) for factor in (verifier.ONE, verifier.GEN**3)]
    assert values[0] != values[1]
    print(
        "Actual layout and two accepted GKR layers: the same total count root admits visibly different non-JUMP products, recovered exactly from the second child packet",
        flush=True,
    )
