def main():
    hb = HeapBuf(2)
    hb[1] = GEN ** 9
    hb[GEN] = GEN ** 9
    a = hb[1]
    b = hb[GEN]
    # The same XOR the assert needs, as a live value.
    diff = a + b
    assert a == b
    p = 1
    p[1] = diff
    p[GEN] = a
    return
