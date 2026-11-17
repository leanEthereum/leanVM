def main():
    sa = StackBuf(2)
    sa[0] = GEN
    sa[1] = GEN ** 2
    hb = HeapBuf(8)
    for i in mul_range(1, GEN ** 3):
        if i == GEN:
            sa = StackBuf(2)
            sa[0] = GEN ** 5
            assert sa[0] == GEN ** 5
        else:
            hb[i] = GEN ** 7
    assert sa[0] == GEN
    return
