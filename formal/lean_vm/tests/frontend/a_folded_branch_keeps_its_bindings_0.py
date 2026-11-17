def main():
    hb = HeapBuf(64)
    w = HeapBuf(16)
    for i in mul_range(1, GEN ** 3):
        if 1 == 1:
            w = StackBuf(2)
            w[0] = i
            w[1] = i * GEN
        hb[i] = w[1]
    assert hb[1] == GEN
    return
