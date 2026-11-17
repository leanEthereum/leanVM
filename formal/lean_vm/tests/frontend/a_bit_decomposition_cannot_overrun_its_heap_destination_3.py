def main():
    hb = HeapBuf(16)
    v = GEN ** 5
    hint_decompose_bits_exponent(hb * GEN ** 4, v, 8)
    p = GEN ** 0
    p[1] = hb[1]
    p[GEN] = GEN ** 0
    return
