def main():
    hb = HeapBuf(2)
    v = GEN ** 5
    hint_decompose_bits_exponent(hb, v, 8)
    p = GEN ** 0
    p[1] = hb[1]
    p[GEN] = GEN ** 0
    return
