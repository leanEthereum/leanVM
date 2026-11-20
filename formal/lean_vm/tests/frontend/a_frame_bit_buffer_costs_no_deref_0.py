def main():
    bits = HeapBuf(GEN ** 8)
    hint_decompose_bits(bits, 182, 8)
    acc = 0
    for i in unroll(0, 8):
        b = bits[GEN ** i]
        bits[GEN ** i] = b * b
        acc += b * (2 ** i)
    assert acc == 182
    p = 1
    p[1] = acc
    p[GEN] = 1
    return
