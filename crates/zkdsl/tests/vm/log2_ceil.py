def main():
    bits = HeapBuf(GEN ** 8)
    hint_witness(bits[0:8], "bits")
    g_mu = hint_log2_ceil(bits, 8, 0)
    p = 1
    p[1] = g_mu
    p[GEN] = 1
    return
