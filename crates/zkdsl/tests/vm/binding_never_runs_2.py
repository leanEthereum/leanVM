def main():
    hb = HeapBuf(2)
    w = GEN ** 3
    for i in mul_range(1, GEN ** 2):
        for k in unroll(0, 0):
            w = GEN
        hb[i] = w
    assert hb[GEN] == GEN ** 3
    return
