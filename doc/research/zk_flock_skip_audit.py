"""Valid-compression directions for Flock's first message, not joint Flock ZK."""

from fractions import Fraction
from functools import reduce
from hashlib import blake2s
from operator import xor
from random import Random
from struct import pack, unpack

from zk_column_count_audit import Library
from zk_count_mixed_audit import echelon
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module


def witness(verifier, message):
    mask = (1 << 32) - 1
    h = list(verifier.BLAKE2S_IV)
    h[0] ^= 0x01010020
    z = a = b = 1 << 512

    def write(position, width, left, right, value):
        nonlocal z, a, b
        bound = (1 << width) - 1
        assert left & ~bound == right & ~bound == value & ~bound == 0
        z |= value << position
        a |= left << position
        b |= right << position

    def linear(position, value):
        write(position, 32, value, mask, value)

    def add(x, y, position):
        result = (x + y) & mask
        carry = result ^ x ^ y
        left, right = (x ^ carry) & (mask >> 1), (y ^ carry) & (mask >> 1)
        write(position, 31, left, right, left & right)
        return result

    def add3(x, y, third, position):
        left, right = (x ^ third) & (mask >> 1), (y ^ third) & (mask >> 1)
        product = left & right
        write(position, 31, left, right, product)
        p, q = x ^ y ^ third, (product ^ (third & (mask >> 1))) << 1
        result = (p + q) & mask
        carry = result ^ p ^ q
        left, right = ((p ^ carry) >> 1) & (mask >> 2), ((q ^ carry) >> 1) & (mask >> 2)
        write(position + 31, 30, left, right, left & right)
        return result

    rotate = lambda value, shift: ((value >> shift) | (value << (32 - shift))) & mask
    for word, value in enumerate(h):
        linear(32 * word, value)
    for word, value in enumerate(message):
        linear(640 + 32 * word, value)
    for position, value in zip((1152, 1184, 1216, 1248), (64, 0, mask, 0)):
        linear(position, value)
    state = h + list(verifier.BLAKE2S_IV)
    state[12] ^= 64
    state[14] ^= mask
    for round_index, sigma in enumerate(verifier.BLAKE2S_SIGMA):
        for number, (ia, ib, ic, id_) in enumerate(verifier.BLAKE2S_G_LANES):
            position = 1280 + 184 * (8 * round_index + number)
            aa, bb, cc, dd = (state[index] for index in (ia, ib, ic, id_))
            aa = add3(aa, bb, message[sigma[2 * number]], position)
            dd = rotate(dd ^ aa, 16)
            cc = add(cc, dd, position + 61)
            bb = rotate(bb ^ cc, 12)
            aa = add3(aa, bb, message[sigma[2 * number + 1]], position + 92)
            dd = rotate(dd ^ aa, 8)
            cc = add(cc, dd, position + 153)
            bb = rotate(bb ^ cc, 7)
            for index, value in zip((ia, ib, ic, id_), (aa, bb, cc, dd)):
                state[index] = value
    output = [h[word] ^ state[word] ^ state[word + 8] for word in range(8)]
    for word, value in enumerate(output):
        linear(256 + 32 * word, value)
    assert pack("<8I", *output) == blake2s(pack("<16I", *message)).digest()
    assert a & b == z
    return z, a, b


def check_rows(verifier, triple):
    z, a, b = triple
    left, right = verifier.blake2s_row_values([verifier.ONE if z >> bit & 1 else verifier.ZERO for bit in range(1 << 14)])
    assert all(value == (verifier.ONE if a >> bit & 1 else verifier.ZERO) for bit, value in enumerate(left))
    assert all(value == (verifier.ONE if b >> bit & 1 else verifier.ZERO) for bit, value in enumerate(right))


def tables(verifier):
    field = Field(8, 0x11B)
    assert all(verifier.PHI[field.mul[2][value]] == verifier.PHI[2] * verifier.PHI[value] for value in range(256))
    inverse_phi = {value: index for index, value in enumerate(verifier.PHI)}
    extensions = []
    for point in verifier.PHI[64:128]:
        coefficients = [inverse_phi[value] for value in verifier.lagrange_weights(64, point)]
        chunks = []
        for chunk in range(8):
            chunks.append([reduce(xor, (coefficients[8 * chunk + bit] for bit in range(8) if byte >> bit & 1), 0) for byte in range(256)])
        extensions.append(chunks)
    weights = verifier.eq_kernel(verifier.FIXED_CHALLENGES)
    weighted = [[int(weight * value) for value in verifier.PHI] for weight in weights]
    return field, extensions, weighted


def skip_halves(verifier, triple, lookup):
    field, extensions, weighted = lookup
    result = [[], []]
    words = [[(value >> (64 * row)) & ((1 << 64) - 1) for value in triple] for row in range(256)]
    for chunks in extensions:
        sums = [0, 0]
        for row, packed_words in enumerate(words):
            z, a, b = [reduce(xor, (chunks[chunk][word >> (8 * chunk) & 255] for chunk in range(8)), 0) for word in packed_words]
            sums[row // 128] ^= weighted[row % 128][field.mul[a][b] ^ z]
        for half, value in zip(result, sums):
            half.append(verifier.E(*(value >> (64 * limb) & ((1 << 64) - 1) for limb in range(3))))
    assert all(verifier.E.sum(half) == verifier.ZERO for half in result)
    return result


def cycle_certificate(verifier, messages):
    libraries = []
    for chosen in (messages, [[0] * 16 for _ in messages]):
        library = Library(verifier)
        block = library.block(verifier.OP_BLAKE2S)
        for message in chosen:
            templates = library.templates(block, library.fresh_frame())
            opcode, row = templates[0]
            assert opcode == verifier.OP_BLAKE2S
            encoded = pack("<16I", *message)
            output = blake2s(encoded).digest()
            cells = [(f"m{cell}", encoded[16 * cell : 16 * (cell + 1)]) for cell in range(4)]
            cells += [("out0", output[:16]), ("out1", output[16:])]
            for name, data in cells:
                for limb, value in zip(("lo", "hi"), unpack("<2Q", data)):
                    row[verifier.BLAKE2S_COLUMNS.index(f"{name}_{limb}")] = verifier.E(value)
            library.append(templates)
        library.verify()
        libraries.append(library)
    first, second = libraries
    assert first.images["code"] == second.images["code"]
    assert first.reads == second.reads and first.exponents == second.exponents
    assert first.images["memory"].keys() == second.images["memory"].keys()
    print("Compression choices fit closed BLAKE2S/JUMP cycles with fixed bytecode, addresses, and counter exponents", flush=True)


def bound_certificate():
    size = 1 << 192
    delta = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    delta += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    assert delta + Fraction(12 + 12 + 63, size) < Fraction(1, 1 << 157)
    print("First-message statistical bound: sparse-span error plus 87/2^192, below 2^-157", flush=True)


def interpolation_certificate(verifier, triple, halves, rng):
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    coin, point = sample(), sample()
    lagrange = verifier.lagrange_weights(64, point)
    direct = verifier.ZERO
    for row, scale in enumerate(verifier.eq_kernel([*verifier.FIXED_CHALLENGES, coin])):
        z, a, b = [verifier.E.sum(weight for bit, weight in enumerate(lagrange) if packed >> (64 * row + bit) & 1) for packed in triple]
        direct += scale * (a * b + z)
    wire = [left + coin * (left + right) for left, right in zip(*halves)]
    assert verifier.lagrange_interpolate(128, [verifier.ZERO] * 64 + wire, point) == direct
    print("Coset-message interpolation agrees with direct quirky R1CS evaluation at independent field coins", flush=True)


def audit(verifier):
    rng = Random(151)
    lookup = tables(verifier)
    baseline = witness(verifier, [0] * 16)
    check_rows(verifier, baseline)
    base = skip_halves(verifier, baseline, lookup)
    differences, messages = [], []
    for index in range(64):
        message = [rng.getrandbits(32) for _ in range(16)]
        messages.append(message)
        triple = witness(verifier, message)
        check_rows(verifier, triple)
        halves = skip_halves(verifier, triple, lookup)
        differences.append([a + b for a, b in zip(halves[0], base[0])])
        if index % 8 == 7:
            print(f"Verified {index + 1} compression witnesses and their two skip-message halves", flush=True)
    rank = len(echelon(verifier, differences))
    print(f"Valid-compression skip differences at the remaining within-block equality coin zero: rank {rank}/63", flush=True)
    assert rank == 63
    interpolation_certificate(verifier, triple, halves, rng)
    cycle_certificate(verifier, messages)
    bound_certificate()


if __name__ == "__main__":
    audit(verifier_module())
