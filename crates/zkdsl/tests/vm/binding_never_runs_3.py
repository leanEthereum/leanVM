def main():
    hb = HeapBuf(2)
    w = [GEN ** 3, 7]
    for i in mul_range(1, GEN ** 2):
        if const(1 == 2):
            w = [GEN, 9]
        hb[i] = w[0]
    assert hb[GEN] == GEN ** 3
    return
