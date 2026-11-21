def main():
    hb = HeapBuf(2)
    w = [GEN ** 3, 7]
    for i in mul_range(1, GEN ** 2):
        for k in unroll(0, 0):
            w = [GEN, 9]
        hb[i] = w[0]
    assert hb[GEN] == GEN ** 3
    return
