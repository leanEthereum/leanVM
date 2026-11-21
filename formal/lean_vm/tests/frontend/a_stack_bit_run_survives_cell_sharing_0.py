def main():
    src = StackBuf(4)
    hint_witness(src, "bits")
    bits = StackBuf(4)
    for i in unroll(0, 4):
        dup = src[i] * src[i]
        bits[i] = src[i] * src[i]
        assert dup == bits[i]
    g_mu = hint_log2_ceil(bits, 4, 0)
    p = 1
    p[1] = g_mu
    p[GEN] = 1
    return
