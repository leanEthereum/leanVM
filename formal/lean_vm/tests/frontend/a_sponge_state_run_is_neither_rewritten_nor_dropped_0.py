def main():
    hb = HeapBuf(4)
    hb[1] = GEN ** 11
    hb[GEN] = GEN ** 22
    hb[GEN ** 2] = GEN ** 33
    hb[GEN ** 3] = GEN ** 44
    x = hb[1]
    y = hb[GEN]
    z = hb[GEN ** 2]
    w = hb[GEN ** 3]
    t = StackBuf(13)
    s = StackBuf(13)
    for k in unroll(0, 12):
        t[k] = x
        s[k] = x
    t[12] = z
    s[12] = w
    o1 = StackBuf(2)
    keccak_cells([y, y, y, y], o1, state=t)
    o2 = StackBuf(2)
    keccak_cells([y, y, y, y], o2, state=s)
    assert o1[0] != o2[0]
    p = 1
    p[1] = x
    p[GEN] = y
    return
