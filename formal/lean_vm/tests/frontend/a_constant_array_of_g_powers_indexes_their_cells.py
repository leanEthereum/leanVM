OFFS = [GEN ** 2, GEN ** 5]

def main():
    hb = HeapBuf(8)
    for k in unroll(0, len(OFFS)):
        hb[OFFS[k]] = 7 + k
    assert hb[GEN ** 2] == 7
    assert hb[GEN ** 5] == 6
    return
